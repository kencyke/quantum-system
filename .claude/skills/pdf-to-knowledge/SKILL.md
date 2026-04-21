---
name: pdf-to-knowledge
description: Convert a PDF document (paper, RFC, spec, manual, datasheet) into agent-friendly Markdown with extracted image assets, saved under `references/<slug>/` so coding agents can consult it across sessions. Use this skill whenever the user includes a PDF URL (links ending in `.pdf`, `arxiv.org/pdf/...`, `arxiv.org/abs/...`, ACM/IEEE/Nature/bioRxiv links, or similar) or asks to "read", "reference", "import", "ingest", "use as knowledge", or "make available" a PDF, even when they do not explicitly say "convert". Also trigger when the user points at a local `.pdf` file path and wants it turned into durable reference material.
---

# pdf-to-knowledge

Turn a PDF into Markdown + images that a coding agent can navigate efficiently.

## When to invoke

- The user's message contains a URL ending in `.pdf` or a well-known PDF host
  (`arxiv.org/pdf/...`, `arxiv.org/abs/...`, `dl.acm.org/...`, publisher DOIs that
  resolve to PDFs).
- The user asks to "use this paper/spec/manual as reference", "add this to
  knowledge", "ingest this doc", etc.
- The user gives a local path to a `.pdf` file and wants it made available for
  future reference.

Do **not** invoke when the user only wants a one-shot summary of a PDF without
persisting it; just answer from `Read` in that case.

## Output contract

Everything lands under `<cwd>/references/<slug>/`. Coding agents can then
`Read` any file in that tree without re-running the conversion. Layout:

```
references/<slug>/
├── INDEX.md         # metadata + Summary + Key concepts + ToC (you fill 2 sections)
├── content.md       # present when page count <= 20
├── sections/        # present when page count > 20 and the PDF has H1 headings
│   ├── 01-<slug>.md
│   └── ...
├── assets/          # image files referenced from Markdown as "assets/..."
│   └── image_000001_<hex>.jpg
└── mineru-raw/      # optional; only written when the user passes --keep-raw
    ├── <name>_middle.json
    ├── <name>_layout.pdf
    └── ...
```

Full format spec: `references/output-format.md` (read it when the user asks
about the layout or you need to tweak it).

## Workflow

1. **Extract the source.** Pull the PDF URL or local path out of the user's
   message. If multiple are present, ask which one to process unless the user
   clearly meant all of them (then loop).

2. **Decide on the output root.** Default to `references/` in the current
   working directory. This project has `references/` in `.gitignore`, and the
   convention generalises well — only override if the user specifies a path.

3. **Run the converter.** Invoke the bundled script via `uv run` so
   dependencies install on demand into a cached virtualenv:

   ```bash
   uv run .claude/skills/pdf-to-knowledge/scripts/convert.py "<pdf-url-or-path>"
   ```

   The path above assumes the current working directory is the project root
   (where `.claude/` lives). If the skill was installed somewhere else, use
   the absolute path of `scripts/convert.py` next to this `SKILL.md`.

   Useful flags (pass only when needed):
   - `--output-dir <dir>` — override the `references/` root.
   - `--slug <name>` — override the auto-derived slug (arXiv IDs are
     preserved; other sources slugify the filename).
   - `--max-pages-per-section N` — split threshold (default 20; do not change
     unless the user asks).
   - `--ocr` — switch MinerU to OCR mode (for scanned PDFs). Default is
     `auto`, which picks text extraction when the PDF has a text layer.
   - `--keep-raw` — keep MinerU's auxiliary outputs (middle.json, layout.pdf,
     span.pdf, model.json, content_list_v2.json) under
     `<output-dir>/<slug>/mineru-raw/`. Off by default — debugging artefacts
     only; they add several MB and are unsuitable for agents.

   The script prints a JSON summary with `slug`, `output_dir`, `page_count`,
   `image_count`, and `sectioned` — read it to plan the next step.

4. **Fill in the INDEX.md scaffold.** The script leaves two sections as
   `<!-- TODO -->` and an incomplete frontmatter. Your job:

   a. **Extract authors into the frontmatter.** Read the first ~30 lines of
      `content.md` (or the first `sections/*.md`) to find the author list —
      usually between the title and the abstract. Add an `authors` field to
      the YAML frontmatter as a list of display names:
      ```yaml
      authors: ["Huzihiro Araki", "Masanao Ozawa"]
      ```
      If authors cannot be identified, omit the field (do not invent names).
      The authors list enables author-name-based search later on
      (see the *Searching related work* section below).

   b. **Write Summary.** 3–5 sentences that answer "what is this doc and
      why would a coding agent care?". Base it on the actual content, not
      the title alone.

   c. **Write Key concepts.** Bullet list of identifiers an agent would
      grep for. **Each bullet must start with a backtick-quoted identifier
      name**, followed by a short description. This is a hard format
      requirement — `scripts/update_concepts.py` keys its cross-document
      index off this leading identifier, and bullets without one collapse
      into a `Unnamed concepts` bucket.

      Required shape:
      ```markdown
      - `<concept name>` — <one-line description>  → mathlib: Mathlib.X.y
      - `<concept name>` — <one-line description>  → needs formalization
      ```

      Contents of the bullets:
      - For **code-adjacent papers**: function/type names, CLI flags,
        config keys, environment variables, error messages, protocol fields.
      - For **math papers**: named definitions, canonical theorems, operator
        or functor names (e.g. `modular automorphism group`, `relative
        modular operator`, `KMS condition`).

      Skip this section entirely (delete the TODO block) if the doc has
      genuinely no greppable terminology — do not fabricate identifiers.

   d. **Cross-reference against mathlib** (only if the Lean MCP toolchain is
      available in this session — i.e. `lean_local_search`,
      `lean_leansearch` are callable). For each Key concept bullet:

      - Run `lean_local_search <concept term>` first. If it returns a
        declaration that matches, annotate the bullet with
        `→ mathlib: Mathlib.Namespace.name`.
      - If nothing comes back, **also try an author-name search**:
        `lean_local_search <last-name>` for each author extracted in 4a,
        plus any canonical author cited repeatedly in the text (e.g.
        "Takesaki", "Araki", "Connes"). This surfaces modules that cite
        the author in docstrings or comments, which often reveal
        adjacent formalisations even when the term itself is not in
        mathlib. See *Searching related work* below for rationale.
      - If both searches miss, annotate the bullet with
        `→ needs formalization` so the gap is explicit.
      - If the session has no Lean MCP tools, skip this step — do not
        invent annotations.

      **Never trust search results blindly.** After annotating, pass
      each proposed `→ mathlib: <path>` through the verification loop
      in step 4g — silent mismatches undermine every downstream agent.

   e. **Extract the bibliography into the frontmatter.** Read the end of
      `content.md` (or the final `sections/*.md`) for the `## References`
      section. Parse each numbered / keyed entry into a YAML list and add
      it to the frontmatter as `bibliography`:
      ```yaml
      bibliography:
        - key: Ara76             # short citation key; invented if absent
          title: "Relative entropy of states of von Neumann algebras"
          authors: ["Huzihiro Araki"]
          venue: "Publ. RIMS Kyoto Univ. 11"
          year: 1976
          arxiv: null            # arXiv ID if present in the entry
          doi: null              # DOI if present
          ingested: false        # true only if already inside references/
      ```
      Rules:
      - Preserve the entry order from the paper so `key` matches the
        in-text citation numbering when possible.
      - If the paper uses author-year keys ("Kos85", "TV20"), keep them;
        otherwise generate `refNN` using the 1-based index.
      - `authors` is always a list, even for a single author. Omit fields
        (set to `null`) rather than invent data.
      - Skip the section entirely if the paper has no References — do not
        fabricate entries.
      - `ingested: true` is reserved for the `update_concepts.py` helper
        to set later; leave it `false` while writing.

   f. **Refresh the concept index (strict mode).** After INDEX.md is
      fully populated, run

      ```bash
      python3 .claude/skills/pdf-to-knowledge/scripts/update_concepts.py \
          --strict <references-root>
      ```

      The `--strict` flag fails with exit 1 if any Key concepts bullet
      does not start with a `` `backtick-quoted` `` identifier — this
      is what the cross-document index keys off (step 4c contract). If
      it fails, fix the offending bullets and re-run; never commit a
      tree in which the validator complains.

      **This project auto-runs `update_concepts.py` via a
      `PostToolUse` hook** (`.claude/settings.json`) whenever an
      INDEX.md under a `references/` tree is edited. The `--strict`
      invocation above is still required — the hook runs the
      non-strict form, so format-drift checks need to happen
      explicitly. If you want to confirm nothing drifted silently,
      append `--check-fresh` on its own invocation; it exits 1 when
      any INDEX.md is newer than CONCEPTS.md.

   g. **Verify every mathlib annotation** (only when Lean MCP tools are
      available; skip otherwise). Run

      ```bash
      python3 .claude/skills/pdf-to-knowledge/scripts/verify_mathlib_refs.py \
          extract <references-root> --output /tmp/mathlib-worklist.json
      ```

      For each item in the worklist, call `mcp__lean-lsp__lean_verify`
      on the candidates in the order listed. The **first candidate that
      `lean_verify` accepts as a valid declaration counts as verified**.
      If every candidate for an item fails, the annotation is a silent
      false positive — record the failure as
      `{"slug": "...", "line": NN, "reason": "..."}` and append it to a
      `failed.json` list.

      After the loop, patch the offending bullets with

      ```bash
      python3 .claude/skills/pdf-to-knowledge/scripts/verify_mathlib_refs.py \
          mark-unverified <references-root> --from /tmp/failed.json
      ```

      The script appends ` [UNVERIFIED] (reason)` to each annotation
      so `gap-filler`'s `detect_gaps.py` treats the concept as
      `suspect` rather than resolved. It **also stamps every INDEX.md**
      with a `mathlib_verified: <timestamp>` frontmatter field so the
      verification cycle is provable. Re-run step 4f after patching so
      `CONCEPTS.md` picks up the markers.

      **Always run `mark-unverified`, even if `failed.json` is an empty
      list.** The empty-list case is the "happy path" where every
      annotation passed; the script still needs to stamp the tree so
      `check-done` (step 4h) recognises the cycle as complete.

   h. **Prove the cycle ran.** Run

      ```bash
      python3 .claude/skills/pdf-to-knowledge/scripts/verify_mathlib_refs.py \
          check-done <references-root>
      ```

      It exits 0 only when every INDEX.md carries a fresh
      `mathlib_verified` timestamp and no INDEX.md has been edited
      after being stamped. Treat a non-zero exit as a hard failure —
      the ingestion is not finished until this check passes. If you
      edit an INDEX.md after stamping, re-run step 4g with an updated
      `failed.json` (even empty) to re-stamp.

   Keep `INDEX.md` concise (under ~80 lines, including the bibliography).
   The point is navigation, not summarisation; the body lives in
   `content.md` / `sections/`.

5. **Report back to the user.** Tell them the `INDEX.md` path, any notable
   caveats (OCR was skipped, large doc was split, no images found), a
   one-line count of how many concepts had a mathlib match vs needed
   formalization, and how many bibliography entries were extracted.
   Mention `CONCEPTS.md` if it was refreshed. Do not paste the full
   summary into chat — they can read the file.

## Searching related work

When annotating concepts against mathlib (step 4d) or — in future — against
external sources, two search axes should be used together:

1. **Term-based search.** The mathematical term or identifier itself
   (`"relative entropy"`, `"modular automorphism"`, `"scaled dot-product
   attention"`). This finds definitions and direct restatements.

2. **Author-name search.** The surname(s) of the paper's authors plus the
   canonical author of the concept being formalised (often different —
   e.g. Araki wrote about *relative entropy* building on *Takesaki's*
   modular theory; both names should be tried). Rationale: mathlib
   developers routinely cite sources in docstrings and section comments,
   so `lean_local_search "Takesaki"` surfaces declarations that invoke
   Takesaki-style theory even when the user's exact term is absent. This
   is how neighbouring formalisations get discovered.

Examples:

- Concept "modular automorphism group" → `lean_local_search "modular
  automorphism"` (term) + `lean_local_search "Takesaki"` (author).
- Concept "Araki's relative entropy" → `lean_local_search "relative
  entropy"` + `lean_local_search "Araki"` + `lean_local_search "Connes"`
  (Connes-Radon-Nikodym cocycle underlies the construction).

The same two-axis pattern applies to future web / textbook search skills:
looking up the author's publication list often yields introductions that
fill prerequisite gaps which the primary paper assumes.

## Why this design

- **MinerU over Docling for math papers.** Earlier iterations used Docling
  as a library; it handled layout / figures well but emitted
  `<!-- formula-not-decoded -->` for every equation by default, and the
  opt-in formula VLM was GPU-tuned and failed to make meaningful progress
  in 10 minutes on an 18-page paper on CPU. MinerU's `pipeline` backend
  decodes the same paper end-to-end in ~7 minutes on CPU, with LaTeX for
  every formula (display and inline) and no placeholders. MinerU also
  preserves equation numbers via `\tag{...}` and provides a straight JSON
  page index. The gain for math formalisation work is qualitative, not
  just quantitative.
- **CLI subprocess, not library import.** MinerU's Python API exists but
  is less stable than the CLI and pulls in a heavier dependency graph
  (vLLM, xformers) when imported directly. Shelling out to `mineru` via
  `subprocess.run` sidesteps the Python version churn and lets us install
  the tool once per machine with `uv tool install "mineru[all]"`.
- **GPL-free dependencies.** MinerU 3.1+ is Apache 2.0 with commercial
  thresholds (100M MAU / $20M monthly revenue) that do not apply here.
  `pymupdf`/`poppler`/`marker-pdf` remain off-limits for license reasons.
- **Claude writes Summary / Key concepts, not the script.** Summarisation
  and identifier extraction are judgement calls; a scripted heuristic
  would be wrong often enough to be harmful. The script handles the
  mechanical work (download, convert, chunk, save images, scaffold); the
  agent handles the semantic work.

## Runtime prerequisites

- **`uv`** must be on `PATH`. The script itself declares no Python deps
  (stdlib only) but uses `uv run` for invocation hygiene.
- **`mineru` CLI must be on `PATH`**. One-off install:
  `uv tool install "mineru[all]"` (≈ 4 GB of Python packages + model weights
  on first run). Subsequent runs reuse the cache and start in a second.
- **Disk space.** MinerU's models plus the `mineru[all]` environment live
  in the uv tool directory; budget ~4 GB. Per-paper runtime memory peaks
  at 3–4 GB on the Araki-size paper.
- **GPU (optional).** If `nvidia-smi` reports a working GPU the converter
  switches MinerU to its `hybrid-auto-engine` backend, which is
  dramatically faster on the formula-recognition stage. Otherwise it
  silently uses the CPU-only `pipeline` backend. No flag needed.

## Failure modes to watch for

- **Network errors on download.** The script exits non-zero; forward the
  error and ask the user for a local path.
- **Scanned PDFs (no text layer).** Output Markdown will be nearly empty. Re-run
  with `--ocr` after asking the user, since OCR adds minutes.
- **No H1 headings despite >20 pages.** The script falls back to a single
  `content.md` — that is intentional, do not try to hand-split.
- **Very large docs (>100 pages).** First-run conversion can take several
  minutes on CPU; warn the user before starting so they do not cancel.
