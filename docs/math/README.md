# Extraction notes

One note per mathematical object, recording what the literature says about it —
the definitional variants and the conventions behind them, the results and their
dependencies, each hypothesis sorted into provable / model-dependent / open, the
degenerate cases, and the formulations that were rejected together with the
object that rules each one out.

These notes are written **before** the corresponding Lean, by the `math-extract`
skill. They contain mathematics only: no Lean types, no declaration names, no
docstring drafts. How the object is eventually formalized is decided when it is
formalized, and a note that guessed in advance would only add noise.

The format is specified in
`.claude/skills/math-extract/references/note-format.md`. The retrieval history
and locator adjudications for the sources these notes cite live in
`.claude/skills/math-extract/sources.md`. Fetched source texts are cached under
`references/`, which is gitignored — the cache is navigation, these notes are
the product.

## Index

| Object | Note | Implemented as |
|---|---|---|

<!-- One row per note. "Implemented as" is a fact recorded after the object is
     formalized — the module or declaration that ended up carrying it, or
     "none" while it is still only a note. It is a back-link, not a plan. -->
