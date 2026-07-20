---
name: grill-formalization
description: Grill a formalization plan against the paper and AGENTS.md before any Lean is written — statement fidelity, abstraction level, deferred hypotheses, Mathlib reuse, proof order.
disable-model-invocation: true
---

# grill-formalization

Interview the user relentlessly about a formalization plan until every decision
that would become permanent sediment in the Lean development is settled —
*before* any tactic is typed. This is a relentless interview aimed at one target:
the plan to formalize an ingested paper.

Run this after `ingest-paper` has left a navigable `references/<slug>/INDEX.md`.
Read that substrate and `AGENTS.md` first; every recommendation you make is
grounded in the paper's actual content and the project's working principles, not
in what Mathlib happens to make easy.

## Survey first

Before any question, map the ground you will plan on — a phase that only
understands the architecture, never decides. Read the Lean sources the plan will
touch and write down the existing **structures, typeclasses, and interfaces**
already in play: what each provides, what it assumes, how a new development must
fit them. The grill runs against this written map.

Ground every line in the **Lean source and mathematical fact** — never in
comments, docstrings, or `.md` notes, which drift. Label each as **fact** (read
off the code, or a proven/standard result) or **inference** (suspected, not yet
verified), and keep the two visibly apart. This discipline holds for the whole
skill.

*Done when:* the architecture map is written and every line is tagged fact or
inference.

## The grill loop

Walk down the design tree below, one axis at a time, resolving dependencies in
order. For each question:

- Ask **one** question and wait for the answer — multiple at once is bewildering.
- Provide your **recommended** answer, grounded and labelled per *Survey first*.
- If the codebase or the paper answers it, **explore instead of asking** — read
  `references/<slug>/`, grep the Lean sources, and use lean-lsp search
  (`lean_leansearch`, `lean_loogle`, `lean_local_search`) to check whether an API
  already exists. Never invent a plausible-looking lemma name; search, then
  report what you found.

## The design tree

Grill these decisions in order — later axes depend on earlier ones. Each rule
lives in `AGENTS.md`; read it there, never restate it here.

1. **Statement fidelity** → *Abstraction first*
2. **Abstraction first** → *Abstraction first*
3. **Deferred hypotheses** → *Prove what is provable; do not defer it*
4. **Mathlib reuse vs. build** → *Project Layout*
5. **Proof skeleton & dependency order** → *Think before coding*
6. **Definition of done** → *Goal-driven verification*, *Prohibited Tokens*

## Output

When every axis is settled, write the plan in this format:

- **Mathematical statement** — the result to formalize, stated in mathematics.
- **Lean statement** — the `theorem` planned for it: the abstract interface, then
  its concrete instantiation.
- **Data structures** — the structures / typeclasses the statement and proof need.
- **Hypotheses** — each hypothesis required, justified as model-dependent vs
  proven-in-plan (axis 3).
- **Equivalence check** — the points to confirm the Lean statement says *exactly*
  the mathematical one. Name where the two could silently diverge — implicit
  coercions, hidden finiteness / nonemptiness, quantifier order, hypotheses
  weakened to fit Mathlib — and how each is settled, separating what is verified
  from what is still inference.

*Done when:* the plan follows the format above, the Lean statement is argued
equivalent to the mathematical one, and no hypothesis survives axis 3 without
being either proven-in-plan or justified as a model-dependent input.
