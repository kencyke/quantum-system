---
name: web-to-knowledge
description: Convert an HTML web page (Wikipedia article, nLab page, textbook chapter, blog post, documentation page) into agent-friendly Markdown with preserved LaTeX math and downloaded image assets, saved under `references/<slug>/` so coding agents can consult it across sessions. Use this skill whenever the user includes a URL that points at a human-readable HTML page (links like `en.wikipedia.org/wiki/...`, `ncatlab.org/nlab/show/...`, textbook TOC pages, software docs) or asks to "read", "reference", "import", "ingest", "use as knowledge", or "make available" a web page, even when they do not explicitly say "convert". Also trigger when the user wants to expand their existing `references/` with related articles that cite-or-are-cited-by a paper already under `references/`. Do NOT trigger for PDF URLs — those belong to the `pdf-to-knowledge` skill.
---

# web-to-knowledge

Turn a web page into Markdown + images that a coding agent can navigate
efficiently. Output is shape-compatible with `pdf-to-knowledge` so the
shared `scripts/update_concepts.py` (lives in `pdf-to-knowledge`) indexes
concepts across both skills.

## When to invoke

- The user's message contains a URL ending in `/wiki/...`, `ncatlab.org/...`,
  a documentation host, or anything that clearly resolves to an HTML page
  (not `.pdf`).
- The user asks to "use this wiki/article/page as reference", "add this to
  knowledge", "ingest this doc", etc.
- A previous `pdf-to-knowledge` ingestion referenced a Wikipedia or
  textbook page as prerequisite knowledge and the user wants to pull it in
  too — e.g. "also grab the Wikipedia article on modular automorphism group
  from the references I just ingested".

Do **not** invoke for:
- **PDF URLs** — use `pdf-to-knowledge` instead. This skill's parser assumes
  HTML and will fail on `application/pdf`.
- One-shot "summarise this page" requests where the user does not want
  persistent reference material — `WebFetch` is sufficient.

## Output contract

Everything lands under `<cwd>/references/<slug>/`, matching the
`pdf-to-knowledge` layout so `update_concepts.py` aggregates both.

```
references/<slug>/
├── INDEX.md        # metadata + Summary + Key concepts + External links + ToC (you fill 3 sections)
├── content.md      # page Markdown with preserved LaTeX math and relative image links
└── assets/         # downloaded images referenced from content.md
```

Slug conventions:
- Wikipedia → `wiki-<kebab-title>` (e.g. `wiki-tomita-takesaki-theory`).
- nLab → `nlab-<kebab-title>` (e.g. `nlab-relative-entropy`).
- Other hosts → `web-<basehost>-<basename>`.

Full format spec: `references/output-format.md`.

## Workflow

1. **Extract the URL.** Pull the web-page URL out of the user's message.
   If multiple are present, ask which one to process unless the user
   clearly meant all of them (then loop).

2. **Decide on the output root.** Default to `references/` in the current
   working directory (same convention as `pdf-to-knowledge` — already
   gitignored in this project).

3. **Run the fetcher.** Invoke the bundled script via `uv run` so the HTML
   parsing dependencies install on demand into a cached virtualenv:

   ```bash
   uv run .claude/skills/web-to-knowledge/scripts/fetch.py "<url>"
   ```

   Useful flags:
   - `--output-dir <dir>` — override the `references/` root.
   - `--slug <name>` — override the auto-derived slug.

   The script prints a JSON summary with `slug`, `output_dir`, `image_count`,
   `formula_count`, and `final_url` (after redirects).

4. **Fill in the INDEX.md scaffold.** The script leaves three sections as
   `<!-- TODO -->`:

   a. **Summary** — 3–5 sentences answering "what does this page cover and
      why would a coding agent consult it?". Base it on the actual content,
      not the title alone. Read `content.md` first.

   b. **Key concepts** — bullet list of identifiers an agent would grep
      for. **Each bullet must start with a `` `backtick-quoted` ``
      identifier** — this is a hard format requirement so that
      `scripts/update_concepts.py` (in `pdf-to-knowledge`) can aggregate
      concepts across web and PDF sources under unified headers. Skip the
      section entirely if the page has no greppable terminology.

   c. **External links** — optional free-form list of adjacent references
      the page links to. Especially useful for Wikipedia / nLab articles
      that contain "See also" sections pointing at related concepts: list
      them here so a future agent knows what to ingest next. Two formats
      are acceptable:
      ```
      - [Modular conjugation](https://en.wikipedia.org/wiki/Modular_conjugation) — J operator on standard form
      - [KMS state](https://ncatlab.org/nlab/show/KMS+state) — companion thermodynamic condition
      ```
      or a single paragraph. Skip if the page has no meaningful outbound links.

   d. **Mathlib cross-reference** — same technique as `pdf-to-knowledge`
      step 4d. For each Key concepts bullet, run
      `lean_local_search <term>` plus `lean_local_search <author-name>` for
      names that appear prominently in the page. Annotate matches with
      `→ mathlib: Mathlib.X.y`, misses with `→ needs formalization`. Skip
      entirely if the Lean MCP toolchain is unavailable.

      **Every annotation must pass through the step-6 verification
      loop** — do not trust `lean_local_search` hits at face value.

   Keep `INDEX.md` concise (under ~80 lines).

5. **Refresh the concept index (strict mode).** Call

   ```bash
   python3 .claude/skills/pdf-to-knowledge/scripts/update_concepts.py \
       --strict <references-root>
   ```

   (The script lives in `pdf-to-knowledge` — it is source-agnostic and
   indexes any `<slug>/INDEX.md` under the root.) `--strict` fails with
   exit 1 if any Key concepts bullet does not start with a
   `` `backtick-quoted` `` identifier. Fix the offending bullets and
   re-run; never leave format drift unfixed.

6. **Verify every mathlib annotation** (only when Lean MCP tools are
   available). Run

   ```bash
   python3 .claude/skills/pdf-to-knowledge/scripts/verify_mathlib_refs.py \
       extract <references-root> --output /tmp/mathlib-worklist.json
   ```

   Feed each candidate symbol to `mcp__lean-lsp__lean_verify`. Record
   every item whose candidates all fail into a `failed.json`, then:

   ```bash
   python3 .claude/skills/pdf-to-knowledge/scripts/verify_mathlib_refs.py \
       mark-unverified <references-root> --from /tmp/failed.json
   ```

   This appends `[UNVERIFIED]` markers so `gap-filler` treats the
   concepts as `suspect` rather than trusting the raw search hit, and
   stamps every INDEX.md with a `mathlib_verified` timestamp in its
   frontmatter. **Always run `mark-unverified`, even with an empty
   `failed.json`** — the empty case is the happy path but still needs
   to stamp the tree. Finish with

   ```bash
   python3 .claude/skills/pdf-to-knowledge/scripts/verify_mathlib_refs.py \
       check-done <references-root>
   ```

   It exits 0 only when every INDEX.md carries a fresh stamp; treat
   a non-zero exit as a hard failure. Re-run step 5 after patching so
   `CONCEPTS.md` reflects the markers.

7. **Report back to the user.** Tell them the `INDEX.md` path, the
   formula/image counts, and whether any mathlib matches surfaced
   (and how many were downgraded to `[UNVERIFIED]` in step 6). Do not
   paste the full summary into chat — they can read the file.

## Why this design

- **Share the output shape with `pdf-to-knowledge`.** A single
  `references/<slug>/` convention and a single `CONCEPTS.md` across both
  skills means an agent does not have to know whether a concept came from
  a paper or a wiki — only that it was ingested.
- **Preserve LaTeX from HTML.** BeautifulSoup lets us surgically unwrap
  MediaWiki's `<span class="mwe-math-element">` (which bundles MathML +
  fallback image + `{\displaystyle ...}` annotation) into plain
  `$...$`/`$$...$$` LaTeX. MathJax `<script>` tags and nLab's iTeX-rendered
  `<math>` are handled similarly. A single-pass approach with
  `trafilatura` silently drops every math element, so we skip it.
- **No full-text summarisation in the script.** Same rationale as
  `pdf-to-knowledge`: Claude fills Summary / Key concepts / Mathlib
  annotations because those are judgement calls that a regex cannot make
  correctly.
- **GPL-free dependencies.** `beautifulsoup4`, `markdownify`, `lxml` are
  all MIT/BSD.

## Runtime prerequisites

- **`uv`** on `PATH`. First invocation installs `beautifulsoup4`,
  `markdownify`, `lxml` into a cached environment (~50 MB).
- **Network access** for both the page fetch and downloaded images.
- No external binaries or OS-level packages are required.

## Failure modes to watch for

- **Paywalled / login-gated pages.** The fetcher sends no cookies. If the
  page returns HTML that omits the real content (common on Elsevier,
  Springer, IEEE), the resulting `content.md` will be mostly nav / abstract.
  Prefer the open-access version, or hand the user the paywall URL back.
- **JS-rendered pages.** MathJax rendered purely at client side (with no
  `<math>` tag and no `<script type="math/tex">`) will lose formulas.
  Wikipedia pages are safe; nLab is safe; some personal blogs and MkDocs
  sites are not. Warn the user if `formula_count: 0` on a page you expected
  to contain math.
- **arxiv.org URLs.** Route the user to `pdf-to-knowledge` — the arXiv
  abstract page is low-signal and the companion PDF is much richer.
- **Image hotlinking failures.** Some CDNs block non-browser user agents.
  Individual image failures are logged but the conversion still succeeds
  with the original `<img src>` URL left in place for the affected image.
