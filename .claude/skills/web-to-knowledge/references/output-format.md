# Output format: `references/<slug>/`

Per-page layout produced by `scripts/fetch.py`. Matches the
`pdf-to-knowledge` output contract so `update_concepts.py` can treat PDF
and web sources uniformly.

## Directory layout

```
references/<slug>/
├── INDEX.md        # metadata + scaffolded Summary / Key concepts / External links + ToC
├── content.md      # full page Markdown with preserved LaTeX math
└── assets/         # downloaded images referenced from content.md (only present when the page has images)
```

Exactly `INDEX.md` and `content.md` always exist. `assets/` is created
only when at least one image was downloaded.

## Slug derivation

- Wikipedia (`en.wikipedia.org/wiki/<Title>`) →
  `wiki-<kebab-title>`. Hyphens and underscores unify, en-dashes collapse
  (e.g. `Tomita–Takesaki_theory` → `wiki-tomita-takesaki-theory`).
- nLab (`ncatlab.org/nlab/show/<title>`) → `nlab-<kebab-title>`
  (e.g. `relative+entropy` → `nlab-relative-entropy`).
- Everything else → `web-<basehost>-<path-basename>`
  (e.g. `docs.python.org/3/library/pathlib.html` →
  `web-python-pathlib`).
- `--slug` flag always wins.

## `INDEX.md` structure

```markdown
---
title: "Page title"
source: "<original-url-given-to-the-tool>"
final_url: "<final-url-after-redirects>"
slug: <str>
assets: <int>
formulas: <int>   # count of LaTeX math spans recovered from the HTML
---

# <title>

## Summary
<!-- 3-5 sentences, filled in by Claude -->

## Key concepts
<!-- bullet list; each bullet MUST start with `backtick-quoted` identifier -->

## External links
<!-- optional: adjacent articles / related pages an agent may want to ingest next -->

## Contents
- [Full content](content.md)
  - [<H2 title>](content.md#<anchor>)
  - ...
```

Frontmatter is plain YAML — machine-readable. The body is
human/agent-readable navigation. `Summary`, `Key concepts`, and
`External links` are scaffolded as `<!-- TODO -->` blocks; Claude replaces
them when filling in the workflow step 4.

### ToC

Always `- [Full content](content.md)` followed by indented entries for the
page's `##`/`###` headings (up to 30) with GitHub-style anchor fragments
(`content.md#foo-bar`).

## Math handling

- `<span class="mwe-math-element">` (Wikipedia wrapper): the MathML child
  is parsed for `<annotation encoding="application/x-tex">TeX</annotation>`
  or `alttext="TeX"`. The whole span — including the fallback `<img>` —
  collapses to a single `$...$` / `$$...$$`.
- `<math display="block">` and plain `<math>` (nLab, some pages): same
  parsing.
- `<img class="mwe-math-fallback-image-{inline,display}" alt="TeX">`:
  handled as a last resort (for pages that do not inline MathML).
- MathJax `<script type="math/tex">...</script>` and
  `<script type="math/tex; mode=display">...</script>`: extracted.
- `{\displaystyle ... }` wrappers injected by Wikipedia's MathML renderer
  are unwrapped so the emitted LaTeX reads naturally.

If a page appears to render math entirely client-side (no `<math>` / no
`math/tex` scripts), the `formulas` count drops to 0; the conversion still
succeeds for the prose but formulae are lost.

## Image handling

- Every `![alt](src)` in the generated Markdown triggers a fetch. `src` is
  URL-joined to the page's final URL to resolve relative links.
- Images save to `assets/<slugified-stem>.<ext>` (max 60 chars). Collisions
  are disambiguated with `-1`, `-2`, etc.
- Inline `data:` URIs are dropped — they usually represent small icons
  (bullets, separators) that agents do not care about.
- Supported extensions: `.png`, `.jpg`, `.jpeg`, `.gif`, `.svg`, `.webp`.
  Anything else is written with `.img` extension and still referenced,
  but agents should check content-type manually.

Image download failures log a warning and leave the original `src` URL in
place, so the conversion never aborts mid-run because of a dead CDN.

## Cross-document concept index

`web-to-knowledge` does **not** ship its own `update_concepts.py`. The
`pdf-to-knowledge` script is source-agnostic — it scans every
`<slug>/INDEX.md` under the references root regardless of whether the
slug originated from a PDF or a web page. Run it once after any new
ingestion:

```bash
python3 .claude/skills/pdf-to-knowledge/scripts/update_concepts.py references/
```

The resulting `references/CONCEPTS.md` groups bullets from papers and
wikis under unified concept headers, which is the whole point of the
shared output shape.
