# AGENTS.md

## Project Layout

- `QuantumSystem/ForMathlib/` — only Mathlib imports allowed; candidates for upstreaming.
- `QuantumSystem.lean` — aggregate root that re-exports every module.
- `scripts/mk_all.lean` — regenerates the aggregate.
- `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` — pinned toolchain and manifest.
- `docs/math/` — extraction notes: what the literature says about an object, written
  before its Lean. Mathematics only, no Lean. Produced by `/math-extract`.

## Working Principles

**Think before coding.**
- Read the target file and its importers before editing.
- Before designing a new object, check `docs/math/README.md` for an extraction
  note on it and read the note if one exists — its adopted general form is the
  statement the Lean is meant to realise, and its `## Hypotheses` table already
  separates the provable from the genuinely model-dependent. A note is
  mathematics, not a design: it never says how to define anything in Lean, and
  no note is a normal state, not a blocker.
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

**Do not bridge what should be unified.**
- When Mathlib already provides an object — a type copy, a topology, a
  structure — use it. Do not reimplement it locally and then paper over the
  mismatch with a conversion lemma, an `Equiv`, or a `Homeomorph` between the
  two copies.
- If such a local reimplementation already exists, migrate to the Mathlib
  object and delete the local one. Do not add a bridge to keep both alive.
- The same applies to two local spellings of one notion (image vs preimage
  form, bundled vs unbundled): pick one and state every result in it.
- A conversion lemma is acceptable only when both sides are genuinely outside
  your control — both already in Mathlib, or the local object carries structure
  the Mathlib one cannot.
  **Why:** a bridge makes the duplication permanent. Every later lemma must
  then pick a side and be transported across, and a `ForMathlib/` copy of
  something Mathlib already has can never be upstreamed — which is the only
  reason that directory exists.

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

## Plan Mode & Responses

**In plan mode, a question deserves an answer — not a plan.**
- When the user asks a question under plan mode, reply with the
  AskUserQuestion tool and answer *only* what was asked. Do not invent a
  problem statement or start drafting a plan the user never requested.

**Numbered steps first, prose second.**
- Do not narrate a whole plan in prose. Lead with the concrete steps as a
  numbered list, then add brief supplementary notes after it.
  **Why:** the reader has ADHD; a response that demands sustained attention
  to parse is a response that does not get read. Keep it scannable.

**Do not force a plan that does not fit.**
- If the request is judged infeasible or inappropriate to turn into an
  implementation plan, do not force one. State the grounds for that
  judgement, then offer alternative approaches that are viable for the
  current codebase, or point to references worth investigating further.

## Lint Rules

Editing hygiene, prohibited tokens, commit style, and style guidelines live in
`.claude/skills/lint-fix/references/rules.md`. Read that file when a hygiene or
style question arises while editing — it is the authoritative statement of the
rules and stands on its own.

To fix a change rather than consult the rules, run `/lint-fix`: it applies the
safe fixes, verifies with `lake build`, and reports what it deliberately left
alone. It writes to the working tree, so it runs only when you ask for it by
name.

## Source of Truth

`AGENTS.md` is the single source of truth; `CLAUDE.md` is a symlink to it. Edit only this file.
