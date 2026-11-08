# AGENTS.md

## Project Layout

- `QuantumSystem/ForMathlib/` — candidates for upstreaming, each file on its own: it imports Mathlib
  only, never another `ForMathlib/` file. A candidate that needs another local result takes it into the
  same file, or moves under `QuantumSystem/Analysis/`, which may import `ForMathlib/` freely.
  **Why:** a chain of local imports cannot be upstreamed as one pull request.
- `QuantumSystem.lean` — aggregate root that re-exports every module.
- `lake exe mk_all --lib QuantumSystem` (Mathlib's script) — regenerates the aggregate.
- `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` — pinned toolchain and manifest.
- `plugins/lean-formalization/` — a Claude Code plugin published from here through
  `.claude-plugin/marketplace.json`; its `README.md` describes it. Each entry of `.claude/skills` and
  `.claude/agents` is a symbolic link to the plugin's skill or agent of that name, so this repository
  uses the plugin without installing it. A skill or agent for this repository alone goes there as a
  regular entry and is not published; the repository's own rules stay outside the plugin, in `docs/`
  and here. Two rules hold for every edit under `plugins/lean-formalization/`:
  - **Nothing of this repository's domain goes in.** The plugin serves any Lean project: no name,
    convention, degenerate model or citation of this repository (C⋆-algebras, the trace
    normalisation, `QuantumSystem`, `docs/lint-rules.md`) in a skill, agent, script or the plugin's
    README. Such content belongs here or in `docs/`, where the skills read it through the
    instruction file. An example in the plugin's docs is drawn from another field (a measure space,
    a group). Before finishing, grep the plugin for this repository's terms.
  - **The citation script's politeness is not weakened.** `cite.py`'s module docstring is the one
    statement of how it treats the sources (robots.txt for its own product token and `Claude-User`,
    one connection and an interval per host, `Retry-After` and backoff, redirects checked hop by
    hop, no retry of a refusal, no caching of negative answers). An edit that touches a request
    keeps every one of those and the test in `plugins/lean-formalization/tests/test_cite.py` that
    covers it, and changes an interval or the user agent only against the source's own published
    terms, cited in the comment next to the constant. No skill or agent fetches a source by another
    route (curl, WebFetch, another identity) to get around a refusal or a `retry-later`.
- `formalization.yaml` — project metadata in the mathlib-initiative format (v0.4); its `sources`, with
  the `checked` key that the plugin's `citation-check` skill writes, are the ledger of citations
  checked against their source.
- `.github/workflows/` — `lean_action_ci.yml` runs `lake build`, `lake lint`, the `mk_all` check and an
  axiom audit that fails on any axiom other than `propext`, `Classical.choice` and `Quot.sound`;
  `plugin_ci.yml` runs the citation script's tests on a change under `plugins/`; `release.yml` tags and
  releases a head of `main` that switches `lean-toolchain` to a Lean release; `update_mathlib.yml` opens
  the weekly pull request that bumps Mathlib and the other pinned dependencies. CI catches mistakes, not a
  malicious contributor: pull request review is the trust boundary.

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
- When stuck on a goal, search closing lemmas with `lean_hammer_premise`,
  then verify with `lean_multi_attempt` before editing.

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
- A new abstraction — a `class`, a `structure`, a definition stated over a
  general interface — lands in the same pull request as an instance of it other
  than a degenerate one (the trivial type, the zero object) and at least one
  theorem that uses it.
  **Why:** an interface with no instance cannot be applied and no proof can
  contradict it, so nothing stated over it is ever tested; one that no theorem
  uses is a guess at what a later proof will need. Declarations that nothing
  used have already had to be deleted here after the fact.

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
- The one exception is the draft of an upstream generalisation: a Mathlib
  definition restated in `ForMathlib/` in a wider setting, with its complete API
  and agreeing with Mathlib's by `rfl` in Mathlib's setting, may stand beside it
  with a single conversion between the two. Its module doc's TODO names the
  upstream change that retires both the copy and the conversion
  (`CompletelyPositiveMap'` in `ForMathlib/Analysis/OperatorSystem/Basic.lean`).

**Declare names in their own namespace.**
- Avoid `_root_` as far as possible: do not escape the current namespace with `_root_.X.y` to
  declare a name; open `namespace X` and declare `y` there, with the helpers that do not belong to it
  in their own namespace. Keep `_root_` for the cases where splitting the namespaces would break the
  order of the file, as when declarations of two namespaces depend on each other in alternation. The
  rule binds new and edited code; existing uses are not rewritten for it.
  **Why:** a `_root_` declaration's name differs from the namespace it sits in, so a reader cannot tell
  where a name is declared from the `namespace` lines alone.

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

**Cite only what you have checked against the source.**
- A citation (an author, a work, a theorem / section / equation number, or a
  claim attached to it) goes into a docstring, module comment or the README
  only after you have read the cited passage itself and confirmed that it
  states what the text attributes to it, hypotheses included.
- If the source cannot be accessed, or it matches only loosely (a special
  case, a different setting, another edition's numbering), leave the citation
  out rather than hedging it. Do not cite from memory, and do not cite a
  secondary source's account as the primary one.
- Do not add comparisons with the literature ("X proves only …", "Y leaves
  this open", "already in Z") unless each side has been checked in this way.
  **Why:** a wrong locator or attribution looks authoritative and is rarely
  rechecked; an audit of this repository found dozens of them, nearly all in
  citations written without the source at hand.
- Record each checked citation in `formalization.yaml` (`sources[].checked`: the URL read and, per
  locator, the page, the date, the version of the work that page number belongs to (optional) and —
  when that locator was read in another copy — its URL), with
  `uv run plugins/lean-formalization/skills/citation-check/scripts/cite.py ledger add`. Citations
  that cannot be checked against their source are removed: `/citation-check` deletes a citation that
  it can neither find in that ledger nor check against an open copy of the source.

**Goal-driven verification (Definition of Done).**
- A change is done only when `lake build` completes with no new errors or
  warnings on the edited modules and their downstream importers.
- After adding imports, run `lean_build` via MCP to restart the LSP;
  otherwise `lean_diagnostic_messages` suffices.
- If a new top-level module is introduced, regenerate `QuantumSystem.lean`
  via `lake exe mk_all --lib QuantumSystem`.
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
`docs/lint-rules.md`, on top of the generic Lean rules in
`plugins/lean-formalization/skills/lint-fix/references/rules.md`. Read both when a hygiene or style
question arises while editing — together they are the authoritative statement of
the rules, and the project file wins where the two differ.

To fix a change rather than consult the rules, run `/lint-fix`: it applies the
safe fixes, verifies with `lake build`, and reports what it deliberately left
alone. It writes to the working tree, so it runs only when you ask for it by
name.

## Mathematical Review

`/math-review` checks the following on top of its generic models and conventions:

- Degenerate models: a system carrying only pure states.
- Conventions to pin in the module doc: whether `Tr` is the normalised or the unnormalised trace, and
  whether ℏ = 1 is in force.

## Source of Truth

`AGENTS.md` is the single source of truth; `CLAUDE.md` is a symlink to it. Edit only this file.
