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

They are read twice afterwards: when the object is designed (AGENTS.md *Think
before coding*), and by `/math-review`, which compares the elaborated Lean back
against the note's adopted general form, hypothesis classification and
degeneracy table — and which maintains the `Implemented as` column below.

The format is specified in
`.claude/skills/math-extract/references/note-format.md`. The retrieval history
and locator adjudications for the sources these notes cite live in
`.claude/skills/math-extract/sources.md`. Fetched source texts are cached under
`references/`, which is gitignored — the cache is navigation, these notes are
the product.

## Index

| Object | Note | Implemented as |
|---|---|---|
| Causal index set of a Haag–Kastler net | [causal-index-set.md](causal-index-set.md) | `CausalIndexSet` |
| Split inclusion of von Neumann algebras | [split-inclusion.md](split-inclusion.md) | `VonNeumannAlgebra.IsSplitInclusion` |
| Faithful representation of a separable C\*-algebra on a separable Hilbert space | [separable-faithful-representation.md](separable-faithful-representation.md) | `CStarRep.exists_isometric_separable` |
| Von Neumann bicommutant theorem | [bicommutant-theorem.md](bicommutant-theorem.md) | `DoubleCommutant.bicommutant_tfae` |

<!-- One row per note. "Implemented as" is a fact recorded after the object is
     formalized — the fully-qualified declaration that ended up carrying it, or
     "none" while it is still only a note. It is a back-link, not a plan.
     /math-review writes it, and resets it to "none" when the declaration is
     gone; it must agree with the note's own `implemented-as:` frontmatter. -->
