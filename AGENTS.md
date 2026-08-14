# AGENTS.md

## Project Layout

- `QuantumSystem/ForMathlib/` — only Mathlib imports allowed; candidates for upstreaming.
- `QuantumSystem.lean` — aggregate root that re-exports every module.
- `scripts/mk_all.lean` — regenerates the aggregate.
- `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` — pinned toolchain and manifest.

## Working Principles

**Think before coding.**
- Read the target file and its importers before editing.
- State your assumptions about the goal, the existing lemmas, and the proof
  skeleton before typing tactics. Capture the goal with `lean_goal` rather
  than guessing the shape from the file context.
- Prefer `lean-lsp` MCP tools over shelling out: `lean_goal`,
  `lean_local_search`, `lean_leansearch`, `lean_loogle`. If you do not know
  whether a lemma exists, say so and search; do not invent plausible-looking
  names.
- When stuck on a goal, search closing lemmas with `lean_state_search` /
  `lean_hammer_premise`, then verify with `lean_multi_attempt` before
  editing.

**Abstraction first.**
- Build the general interface before the concrete model — even when the source
  literature treats only a specific case. Introduce the abstract structure and
  the mathematically conventional form from the *first* commit, not as a later
  refactor, then instantiate the concrete model the task needs.
- Do not specialise to a concrete model because the
  immediate task uses only that case, and do not weaken hypotheses to
  match whatever fragment Mathlib currently has the most lemmas for —
  follow the literature, even when it forces you to build supporting
  API that Mathlib does not yet provide.

**Prove what is provable; do not *defer* it.**
- Do not introduce a `class` / `structure` field (or a `def … : Prop`
  hypothesis) that stands in for a theorem when that theorem has a known
  mathematical proof — *even when Mathlib lacks the supporting lemmas, and
  even when proving it is out of scope for the current change.*
- A hypothesis class is acceptable **only** for genuinely model-dependent
  inputs that are false for some objects in the class *and* for which no known
  universal proof exists.
  **Why:** deferred hypotheses became permanent here. Once a
  `Has…` field is wired in, discharging it later costs far more than proving it
  up front and the trusted base grows silently.  Restricting hypotheses to the
  irreducible (a) inputs — and proving or descoping everything else — is what
  keeps that base bounded.

**Match the code to the docs, not the docs to the code.**
- When a docstring or module comment claims more than the code actually
  establishes, raise the code to meet the claim — strengthen the statement,
  discharge the missing hypothesis, or generalise the definition. Do not
  weaken the documentation to match a thinner implementation.
  **Why:** the documentation records the *intended* theorem; trimming it to
  match a shortfall silently shrinks the goal and hides the gap instead of
  closing it.

**Goal-driven verification (Definition of Done).**
- A change is done only when `lake build` completes with no new errors or
  warnings on the edited modules and their downstream importers.
- After adding imports, run `lean_build` via MCP to restart the LSP;
  otherwise `lean_diagnostic_messages` suffices.
- If a new top-level module is introduced, regenerate `QuantumSystem.lean`
  via `scripts/mk_all.lean`.
- When a tactic fails to close a goal, do not stack `try` / `<;>` to silence
  the error — re-inspect the goal with `lean_goal` and address the actual
  mismatch.

## Editing Hygiene

- Spaces only, never tabs.
  **Why:** Mathlib style; mixed whitespace breaks `lake exe runLinter`.
- Never modify `lakefile.toml`, `lean-toolchain`, or `lake-manifest.json`.
  **Why:** the toolchain and manifest are pinned intentionally; accidental edits cascade into reproducibility failures.
- Write comments in English.
- Never create namespaces or sections named `QuantumSystem`.
  **Why:** the module path already prefixes every declaration; an extra namespace would produce `QuantumSystem.QuantumSystem.Foo`.

## Prohibited Tokens

The following tokens are strictly prohibited, grouped by reason.

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

## Source of Truth

`AGENTS.md` is the single source of truth; `CLAUDE.md` is a symlink to it. Edit only this file.
