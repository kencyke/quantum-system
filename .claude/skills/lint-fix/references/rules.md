# Project Lint Rules

The authoritative statement of this repository's editing hygiene, prohibited
tokens, commit style, and style guidelines. `AGENTS.md` points here rather than
restating them, and the `lint-fix` skill detects and fixes violations of them —
so this file is the one place to edit when a rule changes.

Each rule carries the reason it exists where the reason is not self-evident. The
reasons are load-bearing: they are what lets you judge an edge case the bullet
does not literally cover, instead of guessing.

## Editing Hygiene

- Spaces only, never tabs.
  **Why:** Mathlib style; mixed whitespace breaks `lake exe runLinter`.
- Never modify `lakefile.toml`, `lean-toolchain`, or `lake-manifest.json`.
  **Why:** the toolchain and manifest are pinned intentionally; accidental edits cascade into reproducibility failures.
- Write comments in English.
- Never create namespaces or sections named `QuantumSystem`.
  **Why:** the module path already prefixes every declaration; an extra namespace would produce `QuantumSystem.QuantumSystem.Foo`.

## Prohibited Tokens

The following tokens are strictly prohibited in Lean sources, grouped by reason.

- *Unsound or deferred proofs:* `sorry`, `admit`, `axiom`.
  **Why:** the project targets a fully axiom-free formalization; assumptions smuggled into structure fields count as axioms too.
- *Global configuration and unsafe code:* `set_option`, `unsafe`.
  **Why:** these mutate kernel or elaborator behavior project-wide, or bypass soundness.
- *Compiler and metaprogramming internals:* `System`, `open System`, `Lean.Elab`, `Lean.Meta`, `Lean.Compiler`.
  **Why:** this is a mathematics repository, not a tactic-library repository; depending on internals creates brittle code.

## Commit Style

`lefthook` + `commitizen` (`cz check`, configured in `pyproject.toml`) enforce this; the accepted
vocabulary is:

- Conventional Commits: `feat` / `fix` / `chore` / `docs` / `refactor` / `test` / `perf`.
- Lowercase type, colon, imperative subject. Example: `feat: add GNS faithfulness lemma`.
- One logical change per commit.

The hook runs the stock `cz_conventional_commits` schema, which also accepts `build` / `ci` /
`style` / `revert` / `bump`; the list above is the deliberately narrower project convention.

## Style Guidelines

The Mathlib contribute templates are authoritative; the bullets below distill what actually comes up during edits.

**Naming.**
- `lowerCamelCase` for terms and definitions (`gnsRepresentation`, `isPureState`).
- `UpperCamelCase` for types, structures, and propositions (`CStarAlgebra`, `IsState`).
- Theorem names use `_` as word separator (`norm_add_le`, `inner_self_nonneg`).
- Prefer the `_of_` pattern for implications (`continuous_of_lipschitz`); `iff` joins equivalences; `not_` prefixes negations.

**Layout.**
- 120-column line limit.
- 2-space indentation; `by` stays on the same line as the goal it opens unless the resulting line would exceed the limit.
- Hoist shared hypotheses into `variable` blocks; keep explicit/implicit arity consistent with sibling lemmas.
- Align `calc` steps on the relation; use `·` (centered dot) for focused goals, not `case _ =>`.

**Docstrings.**
- Every public declaration gets a `/-- ... -/` docstring whose first sentence is a self-contained summary.
- Module docs (`/-! # Title ... -/`) at the top of each file describe the content and any non-obvious conventions.

**References** (fetch when a rule above is ambiguous):

- https://github.com/leanprover-community/leanprover-community.github.io/blob/lean4/templates/contribute/doc.md
- https://github.com/leanprover-community/leanprover-community.github.io/blob/lean4/templates/contribute/naming.md
- https://github.com/leanprover-community/leanprover-community.github.io/blob/lean4/templates/contribute/style.md
