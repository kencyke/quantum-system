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

<!--
Macros the quotes below need, copied from each source's own preamble:
  \lok  DL84, references/<slug-of-source>/raw/<file>.tex:144
Omit this block and the comment when no quote carries a source macro.
-->

$$
\newcommand{\lok}[1]{{\mathcal #1}}
$$

# <Object, as a mathematician names it>

## What this object is for

<1–3 sentences: what the object does in the theory, and why its generality
 matters. No history essay, no motivation essay, nothing about formalization.>

## Definition

### Variants as the sources write them

| (D#) | Source | <axis> | <axis> | <axis> | Tier |
|---|---|---|---|---|---|
| (D1) | [DL84] | pair of algebras | second algebra arbitrary | no vector | a |
| (D2) | [BU74] | net-level | second algebra a commutant | vector required | b |

**(D1) [DL84] §1** — tier (a)

> <verbatim quote, in the source's language, unmodified, formulas in the
>  source's own notation>

[tr.] <optional translation, outside the quote, tier (b)>

**(D2) [BU74]** — tier (b)

<paraphrase; a locator is permitted at this tier>

`differs from (D1) by:` <one sentence naming the difference>
`sources claim equivalence:` yes / no / not addressed — <the citation, if yes>

### Adopted general form

<Written by the orchestrator at merge time, not by a lane. Two parts, in this
 order.

 First the statement itself, written out in this note's conventions: the
 ambient objects and their standing assumptions, the quantifiers in order, and
 the (A#) rows it carries. Complete enough to be compared against an elaborated
 Lean type without opening a source.

 Then the justification, one sentence citing the (D#) followed and the (X#)
 that discriminates — e.g. "This is (D1); (X3) shows (D2) drops the non-σ-finite
 case that [DL84] §1 covers." If no discriminator justifies the choice, write
 "provisional — no discriminator separates (D1) from (D2)" and stop; do not
 manufacture a reason.

 When the literature has a canonical display for the object — an inclusion
 chain, a commuting diagram — it may follow the written-out statement as
 display math; it supplements the statement and never replaces it.>

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
- Proof route: <proved-in-source rows only, optional — one reason per step;
  each step names its justification and the (R#)/(A#)/[ext] edge it consumes>
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
| intended case is nonvacuous | <named instance, or "none found — <what was searched>"> | — |
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

<Never omitted, and never empty.>
````

## Section rules

### Macro preamble

Verbatim quotes carry the source's own LaTeX, and sources define their own
macros — `\lok`, `\A`, `\bC`. Any renderer that parses `$…$` (KaTeX in VS Code's
Markdown preview, MathJax elsewhere) raises a parse error on every one of them,
and **the fix is never to edit the quote**: those bytes are the evidence the
quote check verifies. Transcribe the definitions instead, into a `$$` block
between the frontmatter and the H1 — it must precede the first quote that uses
them — with an HTML comment naming the file and line each was copied from.

- **Copy the definition; do not paraphrase it.** `\newcommand{\lok}[1]{{\mathcal
  #1}}` lifted from the paper's preamble can be audited against that preamble.
  An equivalent written from scratch cannot, and a wrong transcription
  mis-renders a quote that the quote check will still pass — it checks the
  source bytes, not what they display as.
- **Only the macros the note actually uses.**
- **`\renewcommand` where the renderer already defines the name.** `\H` is the
  Hungarian-umlaut accent in KaTeX's own macro table, so `\newcommand{\H}` is an
  error; sources redefining it hit the same wall and write `\renewcommand`, so
  copying them is both correct and faithful.
- **The definitions are per-note, and that is the point.** Renderers reset the
  macro table per document, so two notes may transcribe one name differently —
  which is what the sources do. Defining the macros once in an editor or
  workspace setting instead would put every note into a single namespace, and
  the first collision would render one source's quote in another source's
  notation **without raising an error**. A silently mis-rendered verbatim quote
  is worse than a visible parse error, which is why this block belongs in the
  note and not in a configuration file.
- A renderer that does not share macro state across a document simply ignores
  the block, and the quotes show as source LaTeX — which is what they are.
  Nothing downstream depends on it, and no editor configuration is required.

The block is presentation, not mathematics: it carries no claim, so it needs no
tier and no locator beyond the file:line provenance in the comment.

### Frontmatter

- `worst-tier` is the **minimum tier over load-bearing rows** — the rows the
  adopted general form and the main results actually rest on. It is the first
  thing a reader sees, and it is an honesty indicator: a note whose conclusions
  ride on recollection says so at the top.
- `implemented-as` is a **fact-only back-link**, `none` until the object is
  implemented and a fully-qualified declaration name afterwards. This skill
  writes `none`, because it runs *before* the Lean exists and has nothing to
  point at. `math-review` fills the name in — and resets it to `none` when the
  declaration is gone — as part of checking that the declaration still matches
  the note; those two fields (here and in the `docs/math/README.md` index row)
  are the only thing it may write in this file. A re-extraction carries the
  field forward unchanged rather than resetting it.
  **Why:** a back-link nobody is obliged to maintain decays into a claim that
  the object was formalized as something it no longer is, which is worse than
  the honest `none` it started as.
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
- **The comparison grid is a derived index, not a claim.** The orchestrator
  writes it at merge from the (D#) blocks below it, choosing as columns the
  axes along which the corpus actually splits (quantification level, what the
  second object is, extra data such as a distinguished vector — whatever the
  variants genuinely differ on). Like the macro preamble it carries no tier and
  no locator, and when grid and (D#) block disagree, the grid is wrong. The
  verbatim blocks and `differs from:` lines are unchanged by its presence.
  **Why:** filling one column per axis is what makes a variant axis visible at
  merge time — the adopted general form's generality decisions are made along
  exactly these axes, and an axis nobody wrote down is an axis silently
  dropped.
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
- **The adopted form is written out, not merely named.** State the definition
  as a complete sentence in this note's own conventions — the ambient objects
  and their standing assumptions, the quantifiers in order, and the `(A#)` rows
  it carries — and only then cite the `(D#)` it follows and the `(X#)` that
  justifies it. "(D1), because (X3) shows (D2) drops the non-σ-finite case" is
  the *justification*; it is not the definition, and a reader who stops there
  has to reconstruct the mathematics from a verbatim quote in some source's own
  notation.
  **Why:** this paragraph is what the eventual formalization is written
  against, and it is what `math-review` compares an elaborated type to. Both
  need a statement whose quantifier order and hypotheses are unambiguous in
  *one* place; a pointer to a quote in another notation is not that.
- **A canonical display supplements the statement; it never replaces it.**
  When the literature writes the object as a standard display — an inclusion
  chain, a commuting diagram — transcribing it after the written-out statement
  is welcome, but the written-out sentence remains mandatory: a display-only
  adopted form is the pointer-only failure the previous rule forbids, in
  prettier clothes.
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
- **`Proof route:` — one reason per step.** Optional, and only on rows whose
  proof status is `proved in source`. Each step names its justification — a
  definition unfolded, a dependency invoked, a substitution, an approximation —
  and the (R#)/(A#)/[ext] edge it consumes. **Every edge named in the route
  must appear in `Depends on:`, and every `Depends on:` edge of a routed row
  must be consumed by some step** — that cross-check is the field's point.
  **Why:** a hypothesis the proof uses but the row never lists is the most
  expensive omission a formalization inherits, and per-step naming is the
  cheapest audit of the dependency list. It also keeps proof status honest: a
  route cannot be written for a proof that was only skimmed, so a row that
  claims `proved in source` and cannot state its route was read as a sketch.
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

The `intended case is nonvacuous` row is never omitted: it names an instance —
from the corpus, at that attestation's tier — where the adopted form holds
non-trivially, or records "none found — <what was searched>". A corpus with no
non-trivial instance is a finding about the adopted form, in the same
discipline as `## Prior art`'s "could not find X, having searched …".
**Why:** the failure witnesses in `## Hypotheses` guard one direction — a
statement that proves too much — and this row guards the other: a definition
nothing satisfies formalizes cleanly and says nothing, and vacuity is cheapest
to catch before the Lean exists.

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
  void once `lake-manifest.json`'s Mathlib revision moves. Nothing enforces this
  automatically: expiry is decided by a reader comparing the row's revision to
  the manifest, which is why the revision is written into the row rather than
  left implicit in the note's date. A void row is not wrong — it is unmeasured,
  and a claim resting on it drops to (c).

### Sources

**Append-only.** A source that was attempted and not obtained gets a row anyway,
recording what was tried — "not cited" and "could not be obtained" are different
facts. The cross-object retrieval ledger and the locator adjudications live in
`../sources.md`; this table is the per-note view.

### Not investigated

**Never omitted, and never empty.** The last item below always has content, so
an empty section means it was not written rather than that nothing was left
unexamined. State:

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

> Every blockquote in the note must survive `grep -F` against
> `source.flat.txt` of **the source that row cites** — not against the cache at
> large. What fails is downgraded to (b) or deleted.

Matching some other file in the cache proves the sentence exists somewhere,
which is not the claim the row makes. `source.flat.txt` rather than `source.txt`
because a quotation crossing a line break matches only there; see
`ingestion.md`.

A quote that will not *render* is still a quote. Fix it with the macro preamble
above, never by touching the bytes: normalising a formula so a previewer stops
complaining destroys the only thing that makes the row checkable.

**Why:** it makes tier (a) mechanically decidable instead of self-reported, at a
cost of seconds. Converted PDFs are model output, not text, so a quote taken
from converted Markdown is (b) with `mineru-unchecked` until compared against
the page image; an arXiv LaTeX source is the original and needs no such check.

**Known limitation.** The check is decidable only while the cache exists, and
the cache under `references/<slug>/` is untracked and disposable. Once it is
deleted, a tier (a) row is re-checkable only by re-ingesting the source — the
`## Sources` table records the path and enough bibliographic detail to do that,
which is why that table is append-only. A downstream reader who cannot re-ingest
treats an (a) row as an (a) row: the check was run when the row was written, and
the row's locator is what makes the claim falsifiable against a physical copy.
