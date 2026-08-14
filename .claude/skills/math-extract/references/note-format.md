# Extraction note format

The authoritative specification of `docs/math/<slug>.md` — the tracked artefact
the `math-extract` skill produces. `SKILL.md` points here rather than restating
it, so this file is the one place to edit when the format changes.

Each rule carries the reason it exists where the reason is not self-evident. The
reasons are load-bearing: they are what lets you judge a case the rule does not
literally cover.

**The note records mathematics.** No Lean types, no `def`/`structure`/`class`
sketches, no candidate declaration names, no docstring drafts, no ` ```lean `
fences anywhere in the file. A statement that Mathlib contains a declaration is
a fact and is allowed; a suggestion about how this project should define
something is not.

**One note per object, not per source.** The cache under `references/<slug>/` is
indexed by source; the note is indexed by object; the `## Sources` table is where
the two indices cross. Reconciling several sources into one account is the note's
reason to exist.

The note is written in **English**, including prose. Verbatim quotes stay in the
source's own language.

## Skeleton

````markdown
---
object: Split inclusion of von Neumann algebras
slug: split-inclusion
status: draft
worst-tier: c
mathlib-rev: <Mathlib rev from lake-manifest.json>
implemented-as: none
revisions:
  - 2026-08-14 · <short commit> · initial extraction · sources: DL84, BU74
---

# <Object, as a mathematician names it>

## What this object is for

<1–3 sentences: what the object does in the theory, and why its generality
 matters. No history essay, no motivation essay, nothing about formalization.>

## Definition

### Variants as the sources write them

**(D1) [DL84] §1** — tier (a)

> <verbatim quote, in the source's language, unmodified, formulas in the
>  source's own notation>

[tr.] <optional translation, outside the quote, tier (b)>

**(D2) [BU74]** — tier (b)

<paraphrase; a locator is permitted at this tier>

`differs from (D1) by:` <one sentence naming the difference>
`sources claim equivalence:` yes / no / not addressed — <the citation, if yes>

### Adopted general form

<Written by the orchestrator at merge time, not by a lane. States the form this
 note takes forward and cites the discriminators that justify it — e.g. "(D1),
 because (X3) shows (D2) drops the non-σ-finite case that [DL84] §1 covers".>

## Notation and conventions

| (C#) | Axis | This note | Per source | Translation |
|---|---|---|---|---|
| (C1) | trace normalisation | unnormalised | [DL84] unnormalised; [BU74] implicit, inferred from §2 eq. (4) | — |

## Results and dependencies

### (R1) <short name>

<the statement, written out in this note's adopted conventions>

- Source: [DL84] Thm 3.2 · tier (a) · **proved in source**
- Depends on: (R2), (A1), [ext: …]
- Conventions: (C1)
- Verbatim:
  > <quote — tier (a) only; must survive the quote check>

### (R2) …

## Hypotheses

| (A#) | Statement | Class | Evidence | Witness | Scope | Tier | Used by |
|---|---|---|---|---|---|---|---|
| (A1) | the net is nuclear | model-dependent | — | <named object where it fails> | local | b | (R1) |
| (A2) | H is separable | provable | [BU74] §1 | — | standing | b | (R1), (R3) |
| (A3) | … | open | could not separate | — | local | c | (R4) |

## Degeneracies and boundary cases

| Case | Effect on the adopted form | Tier |
|---|---|---|
| zero object / scalars | … | — |
| finite-dimensional | … | — |
| commutative | … | — |
| non-separable / non-σ-finite | … | — |
| type III | … | — |
| non-unital / degenerate representation | … | — |
| universally orthogonal index element | … | — |
| quantifier swap: ∀…∃… ↦ ∃…∀… | … | — |
| hypothesis dropped: (A1) | … | — |

## Rejected formulations and refuted claims

**Append-only.**

| id | Candidate or claim | Disposition | Discriminator | Tier | Date |
|---|---|---|---|---|---|
| (X1) | <candidate> | rejected | **(X3) generality loss** — <what falls out> | a | 2026-08-14 |
| (X2) | <candidate> | equivalent | — ([BU74] Prop 1.1 proves it under (A2)) | b | 2026-08-14 |
| (X3) | <candidate> | open — could not separate; tried … | — | c | 2026-08-14 |
| (X4) | <candidate> | preference-only — no discriminator found | — | d | 2026-08-14 |
| (X5) | *claim*: <a claim about the literature> | refuted | <the evidence that killed it> | a | 2026-08-14 |

## Prior art

| System | Found | Relation to variants | How searched | Measured at |
|---|---|---|---|---|
| Mathlib | `Mathlib.…` | same as (D2) | lean_local_search "…", lean_loogle "…" | mathlib rev `<sha>` |
| Mathlib | could not find <X> | — | <the queries> | mathlib rev `<sha>` |
| Isabelle AFP | — | — | AFP index search "…" | 2026-08-14 |

## Open questions

<One line each, pointing at its row. Only what the extraction could not settle.>

## Sources

**Append-only.**

| Key | Work | Status | Cache | Version | Tier reached | Retrieved |
|---|---|---|---|---|---|---|
| DL84 | Doplicher, Longo, *Standard and split inclusions of von Neumann algebras*, Invent. Math. 75 (1984) | retrieved | `references/dl-1984-split/` | published | a | 2026-08-14 |
| TAK-I | Takesaki, *Theory of Operator Algebras I* | not retrieved — tried arXiv, DOI, publisher, zbMATH | — | — | d | 2026-08-14 |

## Not investigated

<Never omitted.>
````

## Section rules

### Frontmatter

- `worst-tier` is the **minimum tier over load-bearing rows** — the rows the
  adopted general form and the main results actually rest on. It is the first
  thing a reader sees, and it is an honesty indicator: a note whose conclusions
  ride on recollection says so at the top.
- `implemented-as` is a **fact-only back-link**, `none` until the object is
  implemented and a declaration name afterwards. Writing the name is this
  skill's job; checking that the declaration still matches the note is
  `math-review`'s job.
- `mathlib-rev` is the Mathlib revision from `lake-manifest.json` at extraction
  time. It is what expires the `## Prior art` rows.
- `revisions` carries the history. **The body never does** — a note is the
  current best account, not a changelog.

### What this object is for

Written by lane 1. Enough for a reader to decide whether this is the object they
mean, and why the generality is the one under discussion. Not a survey.

### Definition

- Every variant carries a source, a tier, and a locator where the tier allows
  one. **A variant with no source is not a variant** — it belongs under
  `## Rejected formulations` as a candidate.
- Never merge two sources' formulations into one row because they look alike,
  and never renumber a source's own labels.
- `differs from:` states the difference in one sentence. "Slightly different" is
  not a difference.
- `sources claim equivalence:` distinguishes an equivalence the literature
  asserts (a citation) from one the note asserts (an argument that must be
  written out).
- **Adopted general form** is written by the orchestrator at merge, because the
  justification comes from lane 4's discriminators and lane 1 cannot see them
  while running in parallel. It may never be justified by formalization
  convenience.
- No proposed notation, no identifiers.

### Notation and conventions

One row per axis the corpus actually touches; an irrelevant convention pinned
here is noise. The axes that bite in this domain: trace normalisation, the base
of the logarithm, which inner-product argument is conjugate-linear, ℏ = 1,
the range of a summation, unitality, nondegeneracy of representations, and
whether an order symbol is the Löwner order or containment of algebras.

A convention a source leaves implicit is recorded as implicit, with the passage
the inference came from. That inference is tier (b) at best.

### Results and dependencies

- `proof status` ∈ proved in source / sketched / cited elsewhere / asserted.
  Cheap to record and it tells the implementer where the real work is.
- Every dependency a source does not prove in the corpus is marked `[ext: …]`.
  At tier (c)/(d) it carries no locator and instead carries a one-line statement
  of what the external result says — see the substitution rule below.
- One row per result. The same result under two conventions is one row with a
  `Conventions:` flag; genuinely different results sharing a name are two rows
  plus a lane 1 note.

### Hypotheses

- `Class` ∈ `provable` / `model-dependent` / `open`.
- `provable` requires a pointer to a proof — a source and locator, or an
  argument written out. A library lacking the supporting lemmas is irrelevant.
- **`model-dependent` requires a named witness object where the hypothesis
  fails.** No witness ⇒ the row is `open`, never `model-dependent`.
  **Why:** this is the class a later hypothesis field would be justified by, and
  AGENTS.md *Prove what is provable; do not defer it* records what happens when
  that justification is never demanded: the deferred hypothesis becomes
  permanent and the trusted base grows in silence. Demanding a witness at
  extraction time is the cheapest place to stop it.
- `Scope` is `standing` (assumed throughout a source) or `local`. Standing
  hypotheses receive no dependency edge.
- `Used by` lists the results that need it. A standing hypothesis no result
  needs is a finding — say so in the report.

### Degeneracies and boundary cases

Every checklist item gets a row, including the ones where nothing happens: "no
effect" is a result, and an unlisted case is an unchecked one. One row per
quantifier swap and per dropped hypothesis. This is coverage, not a quota.

### Rejected formulations and refuted claims

- **Append-only. Rows are never deleted.** A changed disposition is edited in
  place with a dated note appended:
  `rejected → adopted (2026-09-01: the (X1) separating object was mis-stated)`.
  **Why:** the record of what was tried and discarded is the part of an
  extraction that a later reader cannot reconstruct, and a revision that
  silently drops it destroys exactly the thing that makes re-visiting the design
  cheap.
- `Disposition` ∈ `adopted` / `equivalent` / `rejected` / `preference-only` /
  `open` / `refuted`.
- `rejected` requires a typed discriminator: **(X1) separating object** (named,
  not "some algebra") / **(X2) degeneracy** / **(X3) generality loss** /
  **(X4) source disagreement** (a fetched source discards it, with a quote) /
  **(X5) conditional equivalence**.
- **"Harder to formalize" is never a discriminator**, nor is "not standard"
  (that needs a source and belongs under `## Definition`), nor "equivalent
  anyway" (that is the `equivalent` disposition).
- `preference-only` rows are weightless and **may not be cited from any other
  section**. They exist only so the next run does not re-explore them.
- A formulation some source actually adopts may not be `rejected` here; it is a
  variant under `## Definition`, and the most this table may hold is a
  discriminator showing the two are inequivalent.

### Prior art

- **Facts only.** What exists, and how it relates to the note's variants. No
  proposals about how this project should define, name, or structure anything.
- A search miss is recorded as "could not find X, having searched …" — never
  "Mathlib has no X".
- Every row carries the Mathlib revision it was measured against. The row is
  void once `lake-manifest.json`'s Mathlib revision moves.

### Sources

**Append-only.** A source that was attempted and not obtained gets a row anyway,
recording what was tried — "not cited" and "could not be obtained" are different
facts. The cross-object retrieval ledger and the locator adjudications live in
`../sources.md`; this table is the per-note view.

### Not investigated

**Never omitted, even when empty.** State:

- the `[ext: …]` edges from `## Results` that lane 5 never reached;
- the sources listed as not retrieved, and which rows depend on them;
- the degeneracy checklist items skipped, and why;
- the variants sighted during scoping and not pursued;
- and always, **the unexamined base**: the tier (c)/(d) rows that everything
  above stands on.

The risk lives here, not in what was extracted.

## The three cross-cutting rules

### Evidence tiers

| Tier | What the writer had | What the row may contain |
|---|---|---|
| **(a) quoted** | the source in the cache, opened at the passage | a verbatim quote, a full locator, the cache path |
| **(b) read** | the same, passage read | a paraphrase and a full locator |
| **(c) attested** | another fetched source attributes the claim to this one | the claim and the attester's locator |
| **(d) recalled** | nothing | the claim, plus author and title |

A row's tier is the **minimum** over what it rests on.

### The locator substitution rule

> A full locator — theorem number, section, page, equation number — appears only
> at tier (a) or (b). At (c) only the attesting source's locator. At (d) none.
> **A row forbidden a locator must instead state, in one line, what the cited
> result says.**

**Why:** a number is cheap to fabricate and expensive to check; a statement is
expensive to fabricate and cheap to check. This repository already carries
locators written without the source in hand; the rule exists so the note does
not add more, and so the substituted sentence becomes something a later reader
can actually falsify.

### The quote check

> Every blockquote in the note must survive `grep -F` against the corpus cache
> under `references/`. What fails is downgraded to (b) or deleted.

**Why:** it makes tier (a) mechanically decidable instead of self-reported, at a
cost of seconds. Converted PDFs are model output, not text, so a quote taken
from converted Markdown is (b) with `mineru-unchecked` until compared against
the page image; an arXiv LaTeX source is the original and needs no such check.
