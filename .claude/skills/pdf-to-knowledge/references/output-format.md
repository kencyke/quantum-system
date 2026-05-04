# Output format: `references/<slug>/`

Detailed specification of what the skill writes to disk. Read this when you
need to tweak the converter or answer a user question about where something
lives.

## Directory layout

```
references/<slug>/
├── INDEX.md
├── content.md          (page count <= 20, OR > 20 but no H1 headings to split on)
├── sections/           (page count > 20 and the PDF has H1 headings)
│   ├── 01-<heading-slug>.md
│   └── 02-<heading-slug>.md
├── assets/
│   ├── image_000001_<hex>.jpg
│   └── image_000002_<hex>.jpg
└── mineru-raw/        (only with --keep-raw; see the last section for contents)
```

Exactly one of `content.md` or `sections/` exists — never both. Keeps the
agent's mental model simple.

## Slug derivation

- arXiv URLs (`arxiv.org/abs/2501.12345v1`, `arxiv.org/pdf/2501.12345`) →
  `arxiv-2501.12345`. Version suffix is stripped so re-fetching v2 lands in
  the same directory.
- Other URLs → slugified filename from the URL path (`.pdf` stripped).
- Local paths → slugified basename.
- `--slug` flag always wins.

## `INDEX.md` structure

```markdown
---
title: "..."
source: "<original-url-or-path>"
pages: <int>
slug: <str>
assets: <int>                  # number of extracted image files
authors: ["Name1", "Name2"]    # populated by Claude in step 4a; omitted if unknown
bibliography:                  # populated by Claude in step 4e; empty list if the paper has no References
  - key: "<citation-key>"
    title: "<entry title>"
    authors: ["Name1", ...]
    venue: "<journal/conf>"
    year: <int or null>
    arxiv: "<id or null>"
    doi: "<doi or null>"
    ingested: false            # true when the referenced paper is already under references/; used by the concept index
---

# <title>

## Summary
<!-- 3-5 sentences, filled in by Claude after conversion -->

## Key concepts
<!-- bullet list of identifiers; deleted entirely if not applicable.
     Each bullet may end with a tier annotation:
     - `<term>` — definition/description  → formalized: `QuantumSystem.A.b`
     - `<term>` — definition/description  → mathlib: `Mathlib.A.B.c`
     - `<term>` — definition/description  → needs formalization
-->

## Contents
- [<section title>](sections/NN-<slug>.md)
- ...
```

Frontmatter is plain YAML — machine-readable. The body is human/agent-readable
navigation. Summary and Key concepts are scaffolded as `<!-- TODO -->` blocks;
Claude replaces them. `authors` is filled by Claude after scanning the first
page of `content.md`; when present it powers author-name-based related-work
search in step 4d. `bibliography` is populated in step 4e and drives the
cross-document "next papers to ingest" suggestions (currently manual,
automated in a future iteration).

### Concept annotations

Cross-references live inline on each Key concepts bullet as a trailing
arrow annotation. Three forms are recognised by `update_concepts.py`,
`detect_gaps.py`, and `verify_mathlib_refs.py`:

- `→ formalized: QuantumSystem.X.y` — locally proven in this repository.
  Strongest tier; outranks `resolved` for prioritisation.
- `→ mathlib: Mathlib.X.y` — present in mathlib (term or author search hit
  that passed `lean_verify`). Tier `resolved`.
- `→ needs formalization` — no match in either search axis. Tier `gap`.

A `[UNVERIFIED] (reason)` suffix is appended by
`verify_mathlib_refs.py mark-unverified` when the candidate failed
`lean_verify`; both `mathlib` and `formalized` annotations participate in
that loop.

They are plain Markdown — agents can `grep -n "→ formalized:"`,
`grep -n "→ mathlib:"`, `grep -n "→ needs formalization"`, or
`grep -n "[UNVERIFIED]"` to slice an INDEX.md by tier. The annotation is
added only when the session has Lean MCP tooling; otherwise it is
omitted.

### ToC detail

- **Split mode (sections/)**: one entry per section file in document order.
- **Monolith mode (content.md)**: the "Full content" link, followed by
  indented child links for each H2/H3 heading (up to 20) with GitHub-style
  anchor fragments — e.g. ``[3 Model Architecture](content.md#3-model-architecture)``.
  This lets an agent jump straight to the relevant section without scanning
  the whole file.

## Section splitting rules

Trigger: `page_count > --max-pages-per-section` (default 20).

Algorithm:
1. Walk the raw Markdown line by line.
2. Each `# ` line starts a new section. `## `, `### `, etc. are body.
3. Content before the first `# ` (if non-empty) becomes a `front-matter`
   section, numbered first.
4. If only one real section is produced, fall back to a single `content.md`
   (no splitting, ToC points at the monolith).

Section filenames are `NN-<heading-slug>.md` where `NN` is a zero-padded
1-based index and the slug is derived the same way as the top-level slug
(lowercase, ASCII-ish, max 60 chars).

## Image handling

- MinerU writes extracted images into `<scratch>/<name>/auto/images/` with
  hash-named JPG files and references them from the Markdown as
  `images/<hash>.jpg`. The post-processor in `scripts/convert.py` rewrites
  these references to `assets/<hash>.jpg`, copies **only the referenced**
  images into `assets/`, and drops any orphan clips MinerU may have left
  behind (mostly per-formula crops MinerU keeps as debugging spare data).
- For pure math papers with no figures MinerU's `images/` directory still
  gets populated with formula clips. None of them are referenced from the
  Markdown (LaTeX handles the equations), so `assets/` ends up empty — the
  converter does not create it in that case.

## Formulas

Always on. MinerU emits LaTeX for both inline (`$...$`) and display (`$$...$$`)
math. Equation numbering is preserved via `\tag{...}`. No opt-in flag is
needed; the formula recogniser runs as part of the `pipeline` backend at
modest additional CPU cost (~2 minutes on an 18-page paper).

## OCR

Off by default (`--ocr` to enable). Running OCR on a text-native PDF is slow
and often introduces transcription errors. Switch MinerU's method to `ocr`
only when the user confirms the PDF is scanned or when the initial
conversion returned near-empty Markdown.

## `CONCEPTS.md` (cross-document index)

Sibling of the per-slug subdirs under `references/`. Regenerated by
`scripts/update_concepts.py` at the end of step 4f in the workflow.

```
references/
├── CONCEPTS.md                 # this file
├── arxiv-2202.03357/
│   └── INDEX.md
├── arxiv-1706.03762/
│   └── INDEX.md
└── ...
```

Content:

```markdown
# Concepts index

Auto-generated from references/*/INDEX.md. Do not edit by hand — rerun
`.claude/skills/pdf-to-knowledge/scripts/update_concepts.py references/`.

## <Concept title>

- [<slug>](<slug>/INDEX.md) — <description from Key concepts bullet>  → mathlib: Mathlib.A.B.c
- [<another slug>](<another slug>/INDEX.md) — <description>  → needs formalization
```

Each section header is a concept title (the backtick-quoted identifier at
the head of a `Key concepts` bullet). Entries are grouped by concept so a
glance reveals which papers cover each term and whether any of them gives
a mathlib mapping. The file is fully derived — editing it by hand is
overwritten on the next rebuild.

Implementation note: concept keys are normalised to lowercase for
deduplication but displayed in their original case. Bullets with no
backtick-quoted lead identifier fall under a synthetic
"`Unnamed concepts`" heading to avoid silent loss.

## `mineru-raw/` (optional debug artefacts)

- **Off by default** since iteration-6; pass `--keep-raw` to the converter
  to retain them. When enabled, `<slug>/mineru-raw/` holds MinerU's
  auxiliary outputs:
  - `<name>_middle.json` — raw DocumentAnalysis JSON (2+ MB)
  - `<name>_content_list.json` and `_v2` — per-span structured content
  - `<name>_model.json` — layout model outputs
  - `<name>_layout.pdf`, `_span.pdf`, `_origin.pdf` — annotated PDFs useful
    when triaging a conversion bug
- Not intended for agents to `Read`; the useful signal is already in
  `content.md` / `INDEX.md`. Safe to delete.
