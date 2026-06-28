---
name: ingest-paper
description: Convert a paper or lecture-note PDF into agent-navigable Markdown under references/<slug>/, as the groundwork for grilling its formalization plan.
disable-model-invocation: true
---

# ingest-paper

Turn a PDF (paper, lecture notes) into Markdown + extracted images + a filled
`INDEX.md` that an agent can navigate across sessions — the durable substrate a
formalization plan gets grilled against afterwards.

This skill stops at a navigable document. It does **not** plan or formalize; the
last step hands off to `/grilling`.

## Steps

1. **Resolve the source.** Pull the PDF URL or local path from the request. If
   several are present, process the one the user names; ask only when ambiguous.
   *Done when:* you hold exactly one URL or existing local `.pdf` path.

2. **Run the converter.** From the project root:

   ```bash
   uv run .claude/skills/ingest-paper/scripts/convert.py "<pdf-url-or-path>"
   ```

   Add a flag only when the default fails: `--ocr` (scanned PDF, output came out
   nearly empty), `--slug <name>` (override the derived slug), `--output-dir
   <dir>` (override the `references/` root). Other flags and runtime
   prerequisites live in `references/conversion.md` — read it only if the
   command errors or the layout needs tweaking.
   *Done when:* the script prints its JSON summary (`slug`, `output_dir`,
   `index_path`, `page_count`, `image_count`, `sectioned`) and exits 0.

3. **Fill the INDEX.md scaffold.** The script leaves two `<!-- TODO -->` blocks.
   Read `content.md` (or the `sections/*.md` files) and replace **both**:
   - **Summary** — 3–5 sentences: what this document is and why a formalization
     agent would consult it. From the actual content, not the title.
   - **Key concepts** — bullet list an agent would grep for. **Every bullet
     starts with a `` `backtick-identifier` ``** naming the concept, then a short
     gloss. Omit the section only for pure-prose documents with no greppable
     terminology.
   *Done when:* no `<!-- TODO -->` marker remains anywhere in `INDEX.md`, and
   every Key-concepts bullet begins with a backtick identifier.

4. **Hand off to planning.** Report the `INDEX.md` path and any caveats (OCR
   skipped, document split into `sections/`, no images found) — do not paste the
   summary into chat. Then tell the user the substrate is ready and the next move
   is `/grilling` to stress-test the formalization plan against it.
   *Done when:* the user has the INDEX path and the `/grilling` pointer.
