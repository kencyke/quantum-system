---
name: ingest-paper
description: Convert a paper or lecture-note PDF into agent-navigable Markdown under references/<slug>/, as the groundwork for interrogating its formalization plan.
disable-model-invocation: true
---

# ingest-paper

Turn a PDF (paper, lecture notes) into Markdown + extracted images + a filled
`INDEX.md` that an agent can navigate across sessions — the durable substrate a
formalization plan gets grilled against afterwards.

This skill stops at a navigable document. It does **not** plan or formalize; the
last step hands off to `/grill-formalization`. The structured sections it fills
(Main results, Load-bearing assumptions) **record** what the paper states — they
never judge formalizability or classify hypotheses; that judgement belongs to
`/grill-formalization`.

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

3. **Fill the INDEX.md scaffold.** The script leaves four `<!-- TODO -->` blocks.
   Read `content.md` (or the `sections/*.md` files) and replace **all four**:
   - **Summary** — 3–5 sentences: what this document is and why a formalization
     agent would consult it. From the actual content, not the title.
   - **Key concepts** — bullet list an agent would grep for. **Every bullet
     starts with a `` `backtick-identifier` ``** naming the concept, then a short
     gloss. Omit the section only for pure-prose documents with no greppable
     terminology.
   - **Main results** — the results this document targets for formalization,
     recorded as a **dependency DAG** so the proof skeleton survives. List the
     headline theorems **and** the intermediate lemmas/propositions they rest on,
     so every edge resolves. **Every bullet starts with a
     `` `backtick-identifier` ``** (the candidate Lean name), then a one-line
     *mathematical* statement and a pointer to where it lives (`sections/NN-*.md`
     or `content.md#anchor`), followed by a `depends on:` line referencing other
     nodes, `` `assumption-id` ``s, and external results as `[cited: ...]` (Mathlib
     reuse candidates). Drop the `depends on:` line for a leaf with no stated
     dependencies. Record what the paper states; do **not** judge formalizability
     or proof order.
   - **Load-bearing assumptions** — the hypotheses the Main results depend on,
     recorded **neutrally** from the paper. **Every bullet starts with a
     `` `backtick-identifier` ``** (referenced from the Main-results `depends on:`
     lines), then the assumption and which result(s) rely on it. Do **not**
     classify model-dependent vs provable — that is `/grill-formalization`'s call.
     Omit only if the document states no explicit hypotheses.
   *Done when:* no `<!-- TODO -->` marker remains anywhere in `INDEX.md`, every
   Key-concepts, Main-results, and Load-bearing-assumptions bullet (in the
   sections that are present) begins with a backtick identifier, and every
   Main-results `depends on:` reference resolves to a node/assumption id in the
   document or a `[cited: ...]` external result.

4. **Hand off to planning.** Report the `INDEX.md` path and any caveats (OCR
   skipped, document split into `sections/`, no images found) — do not paste the
   summary into chat. Then tell the user the substrate is ready and the next move
   is `/grill-formalization`, which reads Main results and Load-bearing
   assumptions to stress-test the formalization plan against the paper.
   *Done when:* the user has the INDEX path and the `/grill-formalization` pointer.
