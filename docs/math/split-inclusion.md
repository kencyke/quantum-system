---
object: Split inclusion of von Neumann algebras
slug: split-inclusion
status: draft
worst-tier: c
mathlib-rev: 5450b53e5ddc75d46418fabb605edbf36bd0beb6
implemented-as: VonNeumannAlgebra.IsSplitInclusion
revisions:
  - 2026-08-14 · 4d8a21b · initial extraction · sources: KOE03, HS17, dB74, DL84
  - 2026-08-15 · 4ec09ec · format migration: variant grid, nonvacuity row, adopted-form display · no new claims
  - 2026-08-15 · 4ec09ec (working tree) · prior-art locator refresh after rename/refactor (`exists_tensor_decomposition`, `VonNeumannNet`) · no new claims
  - 2026-08-15 · <working tree, uncommitted> · prior-art refresh after the diagonal-algebra non-split witness · no new claims
---

<!--
Macros used by the verbatim quotes below, transcribed from each source's own
preamble so that the quotes render as their authors wrote them:
  \lok  KOE03, references/arxiv-math-ph-0308031/raw/mathphkoediss.tex:144
  \A    HS17,  references/arxiv-1702.04924/raw/main.tex:151
  \H    HS17,  main.tex:196 — \renewcommand, not \newcommand: \H is the
        Hungarian-umlaut accent in KaTeX's own macro table, which is why the
        source redefines it too
  \bC   HS17,  main.tex:97
The definitions are scoped to this file: the renderer resets its macro table
per document, so a later note may transcribe the same names differently.
-->

$$
\newcommand{\lok}[1]{{\mathcal #1}}
\newcommand{\A}{\mathfrak{A}}
\renewcommand{\H}{\mathcal{H}}
\def\bC{{\mathbb C}}
$$

# Split inclusion of von Neumann algebras

## What this object is for

A split inclusion upgrades mere commutation of two von Neumann algebras to
*statistical independence*: an intermediate type I factor lets states be
prescribed independently on the two sides, as if the pair acted on a tensor
product. In local quantum physics the split property of a net (split inclusions
for all suitably separated region pairs) is the standing regularity hypothesis
behind the type III₁ structure of local algebras, the quantum Noether theorem,
and the finiteness/positivity theory of entanglement measures. The general
two-algebra form matters because the literature proves its structure theory
(canonical interpolating factor, product states, tensor decompositions) at that
level and only then specialises to nets.

## Definition

### Variants as the sources write them

| (D#) | Source | Level | Interpolating 𝔑 squeezed against | Extra data | Tier |
|---|---|---|---|---|---|
| (D1) | [KOE03] | net (chiral) | larger local algebra 𝔅(I₂) | — | a |
| (D2) | [HS17] | pair | — (abstract isomorphism 𝔄_A ∨ 𝔄_B ≅ 𝔄_A ⊗ 𝔄_B, no interpolating factor) | — | a |
| (D3) | [HS17] | pair | commutant 𝔄_B′ | vector \|Ψ⟩ cyclic for each, separating for the join | a |
| (D4) | [dB74] | net (QFT regions) | commutant ℛ(O₂)′ | normal product state | b |
| (D5) | [HS17] | pair | undefined ("intermediate" never pinned) | — | a |
| (D6) | [DL84] | pair | arbitrary second algebra B | — | b |
| (D7) | [DL84] | pair | — (split after tensoring with an auxiliary type I factor M) | auxiliary type I factor M | b |

**(D1) [KOE03] §2.2 ("Split property for chiral subnets"), eq. `eq:splitprop`, source.txt 1697–1707** — tier (a) — net-level, nested form

> a chiral net $\lok{B}$ has the split property, if for any pair $I_{1,2}$ of proper intervals satisfying $\overline{I_1}\subset I_2$ there is a type $I$ factor $\lok{M}$ interpolating between $\lok{B}(I_1)$ and $\lok{B}(I_2)$

with the display Λ: 𝔅(I₁) ⊂ 𝔐 ⊂ 𝔅(I₂), Ī₁ ⊂ I₂ ⋐ S¹. A net-level property,
quantified over all pairs of proper intervals with closure containment,
demanding a type I **factor** squeezed against the **local algebra of the
larger region**. KOE03 presents it as "the usual definition (adapted to our
context; cf FG93 definition 2.11)" — the wording is KOE03's adaptation, and the
FG93 locator is KOE03's citation (tier (c) toward FG93, not retrieved). KOE03
also asserts, without listing them: "There are equivalent formulations of this
property."

**(D2) [HS17] §2, displayed definition, source.txt 985–993** — tier (a) — statistical independence

> The algebras $\A_A$ and $\A_B$ are said to be statistically independent iff there is an isomorphism of the v. Neumann algebras $\A_A\vee\A_B \simeq \A_A\otimes\A_B$.

For two commuting von Neumann algebras on a common ℋ, with ∨ and ⊗ defined at
the definition site and the notion pinned as "$W^*$-independence in the product
sense" (citation florig, not retrieved).

`differs from (D1) by:` single-pair, no net, abstract isomorphism instead of an interpolating factor.
`sources claim equivalence:` no — HS17 says only that statistical independence "is closely related" to the split property. (X4) shows it strictly weaker in general; DL84 identifies it with **quasi-split** (D7), equivalent to split under a semi-standard state.

**(D3) [HS17] §2, "Split property" paragraph, source.txt 995–1005** — tier (a) — the split, commutant form

Given statistical independence and a vector |Ψ⟩ cyclic for 𝔄_A and 𝔄_B and
separating for 𝔄_A ∨ 𝔄_B (written inside the definitional paragraph as "there
is typically a vector…"), there is a unitary W: ℋ → ℋ⊗ℋ with WaW\* = π_A(a)⊗1,
WbW\* = 1⊗π_B(b); setting 𝔑 = W\*(𝔅(ℋ_A)⊗1)W gives 𝔄_A ⊂ 𝔑 ⊂ 𝔄_B′,

> which is also called the ``split''. The split and the unitary $W$ are unique (for given $|\Psi \rangle \in\H$) if we require that

W\*(|Ψ⟩⊗|Ψ⟩) lies in the natural cone of |Ψ⟩ for 𝔄_A ⊗ 𝔄_B. 𝔑 depends on the
chosen |Ψ⟩.

`differs from (D1) by:` the type I factor is squeezed against the **commutant** 𝔄_B′, not the larger local algebra; no regions. In the chiral dictionary the two agree iff Haag duality 𝔅(I₂) = 𝔅(I₂′)′ holds — neither source invokes duality at its definition site.
`sources claim equivalence:` HS17 presents (D2) + |Ψ⟩ ⇒ (D3) as an entailment ("entails"), no proof, citing DL84 and BW86. The machinery is proved in [DL84] Thm 2.1 (tier (b), mineru-unchecked; see (R7)).

**(D4) product-state formulation [dB74], attested through [KOE03] and now read in [dB74] pp. 1–8** — tier (b), mineru-unchecked

[dB74] Cor. 2.4: in its QFT standing structure (local rings with Reeh–Schlieder
vacuum, "almost factor" property, regions with slack), a normal product state
for the pair yields interpolating type I factors realizing Borchers' display
ℛ(O₁) ⊂ 𝔐₁ ⊂ 𝔐₂′ ⊂ ℛ(O₂)′. The converse is asserted:

> It is obvious, but still worth mentioning, that the existence of factors $M_{1}$ and $M_{2}$ with the properties specified above implies the existence of normal product states.

**Caution (refutation finding):** "split ⇔ faithful normal product state" is
**false for abstract commuting pairs** — the (X4) witness carries a faithful
normal product state yet is not split. The abstract relation is [DL84] §1:
normal product state / product isomorphism ⇔ **quasi-split** (D7), and

> Under very general circumstances, for example if there exists a semi-standard state, the split and quasi-split properties are equivalent

dB74's equivalence is honest because its QFT standing structure supplies the
standardness; KOE03's use of the criterion in (R1) is inside that structure and
is sound.

`sources claim equivalence:` KOE03 attests both directions of (D1) ⇔ (D4) to dB74 (proof of `prop:subsplit`, source.txt 1765–1769, and source.txt 9753–9758) — for local algebras in the QFT setting, now grounded at (b) by the dB74 fetch, with the standardness proviso above.

**(D5) [HS17] "intermediate type I subfactors", source.txt 2293–2300** — tier (a) usage row; notion undefined in the corpus

Thm `Thm:dominance` quantifies over "intermediate type I subfactors"
𝔑_A ⊂ 𝔄_A, 𝔑_B ⊂ 𝔄_B; "intermediate" (between which algebras) and "exhausting
𝔄" in the following remark are never defined in HS17. Recorded as a gap, not
filled. Partially grounded by [DL84]'s dyadic interpolation chain (see (R9)).

**(D6) [DL84] Definition 1.4 (p. 497 of Invent. Math. 75)** — tier (b), mineru-unchecked — the bare two-algebra form

> 1.4. Definition. A $W^*$ -inclusion $(A, B)$ is split if there exists a type I factor $N$ such that $A \subset N \subset B$ .

where a W*-inclusion is a pair A ⊆ B of von Neumann algebras,

> (of course $A$ and $B$ have the same identity)

No vector, no separability, no factoriality of the endpoints. Standardness
(a vector cyclic and separating for A, B and A′∧B — Def. 1.1) is a separate
refinement layer; for a non-trivial **standard** split inclusion, separability
of the GNS space and proper infiniteness of A, B, A′∧B are *theorems*
([DL84] Prop. 1.6, tier (b), mineru-unchecked).

`differs from (D1)/(D3) by:` no net, no commutant: the second algebra is arbitrary. Both (D1) and (D3) are instances (take B := 𝔅(I₂), resp. B := 𝔄_B′).

**(D7) [DL84] §1, quasi-split** — tier (b), mineru-unchecked

> We shall also say that $(A,B)$ is quasi-split if there exists a type I factor $M$ such that $(A\otimes \mathbb{1},B\otimes M)$ is split.

DL84 (citing its ref. [12]) states: (A,B) is quasi-split iff there is an
isomorphism A∨B′ → A⊗B′ with ab′ ↦ a⊗b′ — i.e. exactly the (D2) shape for the
pair (A, B′). Split ⇒ quasi-split; equivalence under a semi-standard state
(quote under (D4)). The (X4) witness is quasi-split but not split.

### Adopted general form

Fix a complex Hilbert space ℋ, of arbitrary dimension. All von Neumann algebras
act on ℋ and contain 1_ℋ; that the interpolating factor shares the unit is
*derived* from Λ(1) ⊆ 𝔑, not assumed (degeneracy table, "non-unital" row).
A **W*-inclusion** is a pair (Λ(1), Λ(2)) of von Neumann algebras on ℋ with
Λ(1) ⊆ Λ(2). The inclusion is **split** iff there exists a type I factor 𝔑 on
ℋ with Λ(1) ⊆ 𝔑 ⊆ Λ(2). There are no further hypotheses: no factoriality or
type restriction on the endpoints, no separability of ℋ, no distinguished
vector, and no non-triviality clause (the inclusion is trivially split whenever
either endpoint is a type I factor).

$$
\Lambda(1) \;\subseteq\; \mathfrak{N} \;\subseteq\; \Lambda(2),
\qquad \mathfrak{N} \text{ a type I factor on } \mathcal{H}.
$$

At net level: a local net O ↦ 𝓡(O) has the **split property** iff for every
suitably separated pair of regions — Ī₁ ⊂ I₂ in the chiral/interval case,
a positive-distance corridor in the Minkowski case — the inclusion
𝓡(O₁) ⊆ 𝓡(O₂) is split (the *nested* form). The *commutant* form — for each
admissible disjoint pair, 𝓡(O_A) ⊆ 𝔑 ⊆ 𝓡(O_B)′ is split — is the historical
original (Borchers' conjecture as displayed in [dB74]); the nested form implies
it via locality (𝓡(O₂) ⊆ 𝓡(O₂′)′), and the converse holds under Haag duality,
which no fetched source assumes at its definition site. This note adopts the
nested form at net level and treats the commutant form as a conditionally
equivalent variant, so that every net-level row below says which of the two its
source states.

Justification: the single-inclusion core is (D6) — up to notation verbatim
[DL84] Definition 1.4 — and subsumes (D1) and (D3) as instances. (X1) and (X2)
discriminate both clauses of "type I factor": an interpolating factor of
arbitrary type is strictly weaker ((X1), hyperfinite III₁ identity inclusion),
and an interpolating type I *algebra* is strictly weaker ((X2), ℂ⊕ℂ ⊆ ℂ⊕ℂ).
(X4) shows the statistical-independence/quasi-split candidate (D2)/(D7)
strictly weaker in general (a 5-dimensional separating object), with
equivalence restored exactly under a semi-standard state ([DL84] §1). The
net-level choice resolves the refutation's hole H1 by picking one quantified
property and recording the conditional equivalence instead of an ambiguous
disjunction.

## Notation and conventions

| (C#) | Axis | This note | Per source | Translation |
|---|---|---|---|---|
| (C1) | standing setting, chiral | — | [KOE03] def:chcotheo, source.txt 953–982: chiral net on **explicitly separable** ℋ; proper interval I ⋐ S¹ open, connected, non-dense; I′ := S¹∖Ī. tier (a) | — |
| (C2) | separation of the region pair | nested closure containment | [KOE03] Ī₁ ⊂ I₂ (inside the definition); [HS17] dist(A,B) > 0 ("finite safety-corridor"). tier (a) both | on S¹ they agree (Ī₁ ⊂ I₂ ⇔ disjoint closures with two open arcs between); on a non-compact Cauchy surface dist > 0 is strictly stronger than disjoint closures; the corpus never confronts the two |
| (C3) | HS17 standing conventions | — | "Hilbert spaces are always assumed (or manifestly) separable."; inner products anti-linear in the **first** entry; ∨, ⊗ defined at the (D2) site. tier (a) | — |
| (C4) | which "statistical independence" | W*-independence in the product sense | [HS17] pins by citation (florig); [KOE03] footnote flags the family of inequivalent notions (sS90). Both citations unfetched | none available in corpus |
| (C5) | factor vs type I subalgebra | factor (definitional) | definitions in all sources demand type I **factors**; [HS17]'s proofs use type I subalgebras merely "chosen to be" factors (source.txt 4360). tier (a) | (X2): the algebra form is strictly weaker |
| (C6) | net-level property vs single inclusion | both; single inclusion is primary | [KOE03] net-level (D1); [HS17] per-pair object (D3); [DL84] abstract pair (D6). tier (a)/(b) | net-level = ∀ admissible pairs, single-inclusion form |
| (C7) | meaning of ≅ in (D2) | abstract *-isomorphism | [HS17] displayed definition: isomorphism of von Neumann algebras; its intro glosses ≅ as "up to unitary equivalence" (spatial). Internal wobble, unremarked in the source. tier (a) | under the spatial reading the candidate becomes the (X7) tensor form, which *is* equivalent to split |

## Results and dependencies

### (R1) Heredity: chiral subnets inherit the split property and nuclearity

Let 𝔄 ⊂ 𝔅 be a chiral subnet. If 𝔅 has the split property (is nuclear), then 𝔄
has the split property (is nuclear).

- Source: [KOE03] `prop:subsplit`, source.txt 1748–1782 · tier (a) · **proved in source**
- Verbatim:
  > Let $\lok{A}\subset\lok{B}$ be a chiral subnet. If $\lok{B}$ has the split property (is nuclear), then $\lok{A}$ has the split property (is nuclear).
- Proof route: restrict 𝔄 to its vacuum subrepresentation; by the dB74
  criterion it suffices to produce a faithful normal product state on
  𝔄(I₁)e_𝔄 ∨ 𝔄(I₂′)e_𝔄; modular covariance (A15) makes A ↦ Ae_𝔄 an
  isomorphism on 𝔄(I₃), I₃ ⊇ I₁ ∪ I₂′; pull back a product state from 𝔅.
- Depends on: (D4)/[dB74] criterion (tier (b), mineru-unchecked, with the
  standardness proviso under (D4)); (A15) modular covariance; hypothesis (A13).
- Note: KOE03 demands a *faithful* normal product state where dB74 Cor. 2.4
  needs only a normal one (faithfulness is manufactured in dB74 Thm 2.2) —
  a harmlessly stronger input.

### (R2) Nuclearity ⇒ split

BW-nuclearity (a5): Θ_{β,r}: a ↦ e^{−βH}π₀(a)|0⟩ nuclear with
‖Θ_{β,r}‖₁ ≤ e^{(c/β)ⁿ}) implies the split property for pairs with
dist(A,B) > 0; chiral version with L₀ in place of H.

- Source: [HS17] source.txt 1199 (cites BDF87); [KOE03] source.txt 1709–1716
  and 9174–9278 (nuclearity formulated by BW86; chiral implication via FG93,
  its lemma 2.12 — locator is KOE03's citation) · tier (a) attestations, result
  **(c)** · cited elsewhere
- Conventions: one result under two conventions (H-form and L₀-form).
- Attribution note (refutation-verified): KOE03 attaches no citation to the
  implication itself — BW86 is credited with the nuclearity condition and the
  free-field case, FG93 with the chiral implication; HS17 credits BDF87. Not a
  contradiction; the unfetched originals would adjudicate.
- Depends on: [ext: Buchholz–Wichmann (BW86) — formulates energy nuclearity and
  establishes it for the free scalar field, deriving causal/statistical
  independence of sufficiently separated local algebras. tier (c), no locator,
  not retrieved]; [ext: Buchholz–D'Antoni–Fredenhagen (BDF87) — HS17's citation
  target for nuclearity ⇒ split. tier (c), no locator, not retrieved];
  [ext: Gabbiani–Fröhlich (FG93) — translates the implication to chiral nets on
  S¹. tier (c), not retrieved].

### (R3) Modular nuclearity a5′) ⇒ statistical independence; a5′) ⇒ a5)

- Source: [HS17] source.txt 2337–2349 · tier (a) attestation, results (c) ·
  asserted / cited elsewhere
- Depends on: [ext: Buchholz–D'Antoni–Longo, *Nuclear maps and modular
  structures I* — modular nuclearity implies energy nuclearity in Minkowski
  space without the quantitative bounds. tier (c), no locator, not retrieved];
  edge to (R2).

### (R4) Split ⇒ local algebras ≅ centre ⊗ hyperfinite type III₁ factor

- Source: attested in [KOE03] source.txt 1718–1731 · tier (c) · cited elsewhere
- Depends on: [ext: BDF87 — under the split property (plus its standing
  assumptions, for nets in 3+1-dimensional Minkowski space) local von Neumann
  algebras factorise as centre ⊗ hyperfinite type III₁ factor. tier (c), no
  locator, not retrieved]; [ext: Haagerup — uniqueness of the injective type
  III₁ factor. tier (c), not retrieved]; [ext: FG93 — chiral translation.
  tier (c), not retrieved].
- Flag (refutation): KOE03 and HS17 attribute *different hypothesis-sets* to
  BDF87 (split alone, here, vs nuclearity + scale invariance in (R5)); read
  this row as KOE03's compression, not as a theorem shape.

### (R5) Nuclearity + asymptotic scale invariance ⇒ direct sums of type III₁ factors

- Source: attested in [HS17] source.txt 1201 · tier (c) · cited elsewhere
  ([ext: BDF87, as in (R4)])
- Depends on: a5) (A8) and (A14). Kept distinct from (R4): different
  hypotheses, different conclusion.

### (R6) No purity / failure of statistical independence for touching regions (HS17 `thm_split`)

(a) The restriction of a locally normal state to a local algebra is never pure.
(b) A pure normal state on a local algebra extends to no larger local algebra
normally. (c) For disjoint A, B with Ā ∩ B̄ ≠ ∅ there is no normal separable
state on 𝔄(O_A) ∨ 𝔄(O_B); in particular the pair is not statistically
independent (hence not split).

- Source: [HS17] `thm_split`, source.txt 1202–1210 · tier (a) for (a), (c);
  (b) inherits (c) · (a), (c) proved in source; (b) cited elsewhere
- Depends on: [ext: Fewster–Verch, *The necessity of the Hadamard condition* —
  its corollary 3.3 (locator as HS17 cites it): a pure normal state on a local
  algebra cannot be extended to a normal state on any larger local algebra.
  tier (c), not retrieved]; setting of (R5); hypotheses (A10), (A14).
- Independent grounding (refutation fetch): [dB74] Ch. II conclusion asserts
  the same failure for the free field —
  > one runs into contradictions if one postulates the existence of normal product states for such regions
  (tier (b), mineru-unchecked).

### (R7) Canonical split: implementing unitary, canonical 𝔑, natural-cone uniqueness

For a semi-standard split W*-inclusion, there is a standard-implementation
unitary U_Λ: ℋ_Λ → ℋ₁⊗ℋ₂ with U_Λ ab′U_Λ\* = a_e⊗b′_f and
U_Λ P^♮_Ω(A′∧B) = P^♮_{Ω⊗Ω}; the canonical interpolating type I factor is
N_Λ = U_Λ\*(𝔅(ℋ₁)⊗1)U_Λ, unique per standard vector by unicity of the standard
implementation. When the vector is cyclic for both algebras (HS17's hypotheses)
this is exactly (D3)'s W: ℋ → ℋ⊗ℋ.

- Source: [DL84] Thm 2.1, Def. 2.2, Cor. 2.4 (pp. 1–14 of the conversion) ·
  tier (b), mineru-unchecked · proved in source (promoted from (c) by the
  refutation fetch); [HS17] source.txt 995–1005 asserts it · tier (a)
- Precisions: DL84 normalises via the natural cone of the **relative
  commutant** A′∧B (equivalent to HS17's phrasing under the identification by
  W); Cor. 2.4 shows every interpolating type I factor with properly infinite
  relative commutants is vN_Λv\* for a unitary v ∈ A′∧B — uniqueness is
  strictly *per vector*.
- Depends on: (D6); standardness layer; [ext: DL84's ref. [12] for the
  quasi-split equivalences. tier (c), not retrieved].

### (R8) Entanglement-measure dominance on intermediate type I subfactors

E(ω) ≥ E_D(ω|_𝔑) for entanglement measures with (e2), (e4), (e5) and the
normalisation, 𝔑 = 𝔑_A ⊗ 𝔑_B an intermediate type I subfactor pair.

- Source: [HS17] `Thm:dominance`, source.txt 2292–2307 · tier (a) statement ·
  cited elsewhere + sketched (finite-dimensional case in [ext: Donald–
  Horodecki–Rudolph — entanglement measures with the stated properties dominate
  distillable entanglement in finite-dimensional type I algebras. tier (c), not
  retrieved]; approximation sketch in source)
- Depends on: (R9); (D5) gap; measure axioms (out of this object's scope).

### (R9) Split ⇒ many intermediate type I subfactors "exhausting" the pair

- Source: [HS17] remark after `Thm:dominance` · tier (a) for the assertion ·
  **asserted, no proof, no citation in HS17**
- Verbatim:
  > The existence of many such intermediate type I subfactors exhausting $\A$ is guaranteed by the split property.
- Refutation status: half-grounded. [DL84]'s introduction states
  > the interpolation by a chain of type I factors $N_{d}$ , $d$ a diadic rational
  (Th. 8.3; that section not converted) — "many" in a precise sense, tier (b),
  mineru-unchecked. "Exhausting 𝔄" remains undefined in every fetched text;
  this row must not be cited as a theorem shape until it is pinned.

### (R10) Split ⇒ the decoupled state is well-defined; lower bounds on E_I, E_R (HS17 `corI`)

For dist(A,B) > 0 and ω faithful normal on 𝔄_A ∨ 𝔄_B, the decoupled state
ω′(ab) = ω(a)ω(b) is well-defined by the split property, and E_I, E_R admit the
lower bounds of HS17 corI.

- Source: [HS17] `corI` and preceding paragraph, source.txt 4648–4676 ·
  tier (a) · proved in source
- Depends on: split property for the pair ((R2) route); statistical
  independence (split ⇒ quasi-split, [DL84] §1, tier (b)); hypotheses (A7),
  (A11). Consequence noted in source: E_R diverges as the corridor shrinks.

### (R11) E_R(ω) > 0 across a corridor (HS17 `cor1`)

- Source: [HS17] `cor1`, source.txt 4347–4386 · tier (a) · proved in source
  (split-chosen type I "Cbit" subalgebras + near-maximal Bell violation +
  Fell's theorem + Reeh–Schlieder)
- Depends on: (R10); split property; Reeh–Schlieder (A5, proved in HS17);
  [ext: Fell's theorem — normal states of a representation approximate any
  state weakly; HS17 points at Haag's book. tier (c)/(d), not retrieved];
  technique attributed to [ext: Narnhofer; Summers–Werner — maximal Bell
  violation is generic in QFT. tier (c), not retrieved].

### (R12) Quantum Noether theorem: split ⇒ local implementers via universal localisation maps

- Source: [KOE03] source.txt 9751–9773 (detailed summary), 1724–1726 ·
  tier (c) · cited elsewhere
- Depends on: (R1); [ext: Buchholz–Doplicher–Longo (BDL86) — under the split
  property, spacetime symmetries admit local implementers built from universal
  localisation maps: for Ī ⊂ J a norm-one *-homomorphism onto the algebra of J
  acting trivially on the algebra of I carries global symmetry unitaries to
  locally supported implementers. tier (c), no locator, not retrieved];
  (D4)/[dB74] supplies the product state; local normality of the embedding.

### (R13) Localisation maps → identity as regions exhaust spacetime

- Source: attested in [KOE03] source.txt 9812–9818 · tier (c) · cited elsewhere
- Depends on: (R12); [ext: D'Antoni–Doplicher–Fredenhagen–Longo (ADF87) — for
  suitable enlarged regions the universal localisation maps converge pointwise
  strongly to the identity, given irreducibility of the quasi-local algebra.
  tier (c), no locator, not retrieved]; irreducibility hypothesis.

### (R14) Trace-class estimate on e^{−βL₀} ⇒ nuclearity ⇒ split for the U(1)-current derivative models

- Source: [KOE03] source.txt 9174–9278, estimate `eq:nuclcond` · tier (a) for
  the estimate, proved in source; the final split step inherits (c) (FG93's
  own lemma 2.12, locator as KOE03 cites it)
- Depends on: (R2); [ext: FG93 as in (R2)]; [ext: Schoeneberg III.§3 — Dedekind
  η transformation law, locator as KOE03 cites it. tier (c), not retrieved];
  trace-class hypothesis (A8 witnesses).

### (R15) The chiral nets LSU(n)_k are split, hence completely rational

- Source: attested in [KOE03] source.txt 4175–4180 · tier (c) · cited elsewhere
- Depends on: [ext: FG93 — split property for chiral current algebra models.
  tier (c), not retrieved]; [ext: Loke thesis — strong additivity. tier (c),
  not retrieved]; [ext: Xu — μ-index computation. tier (c), not retrieved];
  [ext: Kawahigashi–Longo–Müger — complete rationality (split + strong
  additivity + finite μ-index) implies finitely many sectors of finite
  statistical dimension. tier (c), not retrieved]. Split is a defining
  constituent of complete rationality (KOE03 source.txt 7913–7920).

### (R16) Joint cyclic-separating vectors — corrected statement

**As quoted by KOE03 (source.txt 6666–6669) the sentence is refuted** — see
(X9) in the rejected/refuted table. Corrected statement, now read in the
fetched DL84: under the hypotheses of [DL84] Prop. 1.2 (properly infinite
algebras *acting standardly* / with properly infinite commutants, separable
predual), each of A, B, A′∧B admits a dense G_δ set of cyclic separating
vectors, hence standard vectors for (A, B) form a dense set.

- Source: [DL84] Prop. 1.2 · tier (b), mineru-unchecked · proved in source,
  via [ext: Dixmier–Maréchal — the cyclic separating vectors of a von Neumann
  algebra with separable predual and properly infinite commutant form a dense
  G_δ. tier (c), not retrieved]
- KOE03's *application* (type III subfactor inclusions on the vacuum space) is
  sound; only its freestanding sentence drops the hypotheses.

### (R17) Finite-dimensional statistical independence — refuted as stated

HS17 asserts (source.txt 991, tier (a)):

> When $\A_A$ and $\A_B$ are finite dimensional and $\A_A\cap\A_B=\bC 1$, then the algebras are always statistically independent.

**Refuted as literally stated** — see (X10) in the rejected/refuted table. It
holds for commuting finite-dimensional *factors* (then the join is naturally
the tensor product); the corpus's uses of the remark are unaffected because
they concern factors.

### (R18) Diffeomorphism covariance ⇒ split for chiral nets

- Source: attested in [HS17] footnote, source.txt 1493 · tier (c) · cited
  elsewhere ([ext: Morinelli–Tanimoto–Weiner, *Conformal covariance and the
  split property* — a chiral net containing the Virasoro subnet automatically
  satisfies the split property. tier (c), no locator, not retrieved])

### (R19) Model inputs: free fields satisfy BW-nuclearity

- Source: attested in [HS17] source.txt 2375, 1220 · tier (c) · cited elsewhere
- Depends on: [ext: BW86 — nuclearity for the free scalar field. tier (c), not
  retrieved]; [ext: D'Antoni–Hollands — nuclearity and split for free Dirac
  fields, also in curved spacetime. tier (c), not retrieved]. These supply the
  nonvacuous instances of the split property in the corpus.

## Hypotheses

| (A#) | Statement | Class | Evidence | Witness | Scope | Tier | Used by |
|---|---|---|---|---|---|---|---|
| (A1) | ℋ separable | open | explicit in both sources (KOE03 source.txt 956; HS17 conventions); **no fetched result visibly uses it**; for *standard* split inclusions separability is a theorem ([DL84] Prop. 1.6) | — | standing | a/b | none exhibited |
| (A2) | chiral-net axiom bundle (isotony, locality, covariance, spectrum, unique cyclic vacuum) | — (definitional bundle) | KOE03 def:chcotheo; HS17 a1)–a4) | — | standing | a | (A5), (R1)–(R6) |
| (A3) | subnet conformal covariance | model-dependent | KOE03 source.txt 1006–1020, 1484–1496 | fails: light-ray inclusion of the U(1)-current derivatives in their dual net (KOE03 names it, GLW98 leg tier (c)); holds: coset/current subalgebras | standing | b/c | (A15), (R1) |
| (A4) | uniqueness of the vacuum | — (axiom) | KOE03 source.txt 1221–1223; HS17 a4) | — | standing | a/c | type III₁ factoriality |
| (A5) | vacuum cyclic and separating for local algebras (Reeh–Schlieder) | provable | HS17 proves in-source, source.txt 1141–1167; KOE03 attests RS61 et al. | — | standing (derived) | b | (A11), (A12), (R1), (R11) |
| (A6) | weak additivity | provable (chiral) / open (general nets) | KOE03 derives for chiral nets (LRT78/FJ96 legs (c)); HS17 assumes it as Araki's axiom | — | standing | a/c | (A5) |
| (A7) | corridor dist(A,B) > 0 | model-dependent | HS17 source.txt 451, 1199, 2345, 4649 | fails: free Klein–Gordon net with touching bases ((R6)(c); fewster_2 leg (c); split ⇒ statistical independence now (b) via dB74/DL84); holds: same net with corridor | local | a/c | (R2), (R10), (R11) |
| (A8) | BW-nuclearity a5) | open | sufficient for split (attested); no converse claimed; no net satisfying a1)–a4) but failing a5) named in any fetched source | satisfiers named: free KG, free spin-½, U(1)-current derivative and stress-energy models (KOE03 proves the chiral estimate in-source) | local | a/c | (R2), (R5), (R14), (R19) |
| (A9) | modular nuclearity a5′) | open | a5′) ⇒ a5) attested (tier (c)); satisfiers: integrable models with factorizing S-matrix | — | local | a/c | (R3) |
| (A10) | local normality of ω | model-dependent | HS17 source.txt 1201 | fails: pure state on 𝔄(O_A) Hahn–Banach-extended (argument written out in extraction; non-constructive step flagged); holds: vacuum and density-matrix states | local | a/b | (R6) |
| (A11) | ω faithful + normal on 𝔄_A ∨ 𝔄_B | provable for the vacuum (corridor + Reeh–Schlieder argument written out; faithfulness *consumes* the corridor); model-dependent for general normal states | HS17 source.txt 4649 | fails (general case): normal state with support projection p < 1; holds: vacuum | local | a/b | (R10), (R11) |
| (A12) | vector Ψ cyclic for 𝔄_A, 𝔄_B, separating for the join | provable for the vacuum (discharges HS17's "typically"); open beyond it | HS17 source.txt 995 | — | local | a/b | (R7), (D3) |
| (A13) | ambient net 𝔅 has the split property | open | satisfiers: LSU(n)_k, U(1)-current models; **no non-split net named in the fetched pages** — [DL84] announces non-split field theories in its §9–10, not converted | — | local | a | (R1), (R12), complete rationality |
| (A14) | asymptotic scale invariance at small scales | open | undefined in fetched text; grounding lives in BDF87 (unfetched) | — | local | a/c | (R5), (R6) |
| (A15) | modular covariance of subnet inclusions | provable | derived from (A3) + geometric modular action; KOE03 source.txt 1508–1523 (Takesaki/Jones legs (c)) | — | standing (derived) | b/c | (R1) |
| (A16) | faithful normal product state on 𝔄(I₁)e_𝔄 ∨ 𝔄(I₂′)e_𝔄 | provable given (A13) + (A15) | proof written out in KOE03 prop:subsplit; criterion now read in dB74 (tier (b), mineru-unchecked) | — | local | b | (R1), (R12) |

## Degeneracies and boundary cases

| Case | Effect on the adopted form | Tier |
|---|---|---|
| intended case is nonvacuous | named instances exist in the corpus, at attestation level only: the (A8) satisfiers (free KG, free spin-½, U(1)-current derivative and stress-energy models) and (R15)'s LSU(n)_k — every leg rests on tier (c) attestations ((R2)'s BW86/FG93 route); the type III row below records where the bare definition is non-vacuous | c |
| zero object / scalars | Λ(1) = ℂ1: always split (ℂ1 is a type I factor). Either endpoint a type I factor (incl. Λ(2) = 𝔅(ℋ)): trivially split — the definition has no non-triviality clause, matching [DL84] (its Cor. 2.3(d) handles N = ℂ1 and N = 𝔅(ℋ) explicitly) | b |
| identity inclusion Λ(1) = Λ(2) = 𝔐 | split iff 𝔐 is a type I factor; fails for the hyperfinite III₁ factor (existence attested via KOE03/BDF87, (c)) | a/c |
| finite-dimensional | **not trivial**: split ⇒ Λ(1) ∩ Λ(2)′ = ℂ1 (one-line proof), but not conversely — 5-dimensional witness (ℋ = ℂ⁵, Λ(2) = M₂⊕M₃, Λ(1) = {p, 1−p}″, p = diag(1,0)⊕diag(1,1,0)): trivial relative intersection, statistically independent, yet no interpolating type I factor (unital subfactor of M₂⊕M₃ forces r ∣ 2 and r ∣ 3 ⇒ r = 1). Minimal witness: ℂ⊕ℂ ⊆ ℂ⊕ℂ, now formalized as `VonNeumannAlgebra.not_isSplitInclusion_diagonalAlgebra` (Prior art) | — (verified computation) |
| commutative | Λ(1) commutative harmless; Λ(2) commutative ⇒ split iff Λ(1) = ℂ1 (only commutative factor is ℂ1). Witnesses: ℂ⊕ℂ ⊆ ℂ⊕ℂ (formalized, see Prior art); L∞[0,1] ⊆ L∞[0,1] | — |
| non-separable / non-σ-finite | no effect on the bare form (ℂ1 ⊆ 𝔅(ℋ) splits on any ℋ); separability enters only with the standardness refinement, where it becomes a **theorem** ([DL84] Prop. 1.6) | b |
| type III | intended case; the definition is non-vacuous exactly when neither endpoint is type I | a |
| non-unital / degenerate representation | dissolves: 1 ∈ Λ(1) ⊆ 𝔑 forces unit-sharing — a derived fact, not a hypothesis (refutation hole H2); no fetched source entertains a non-unital variant | — |
| universally orthogonal index element | net level: touching pairs are excluded by the definition's typography (Ī₁ ⊂ I₂), and the exclusion is essential ((R6)(c)); empty pair-index ⇒ vacuously split, no effect | a |
| quantifier swap: ∀ pairs ∃ 𝔑 ↦ ∃ 𝔑 ∀ pairs | contradictory in any net with factorial local algebras: 𝔐 ⊆ 𝔅(I₂) for all I₂ plus locality forces 𝔐 ⊆ Z(𝔅(I₂)) = ℂ1, then 𝔅(I₁) ⊆ ℂ1 — see (X8) | a |
| hypothesis dropped: "type I" | strictly weaker — (X1) | a/c |
| hypothesis dropped: "factor" | strictly weaker — (X2) | — |
| hypothesis dropped: Λ(1) ⊆ 𝔑 | vacuous — (X3) | — |

## Rejected formulations and refuted claims

**Append-only.**

| id | Candidate or claim | Disposition | Discriminator | Tier | Date |
|---|---|---|---|---|---|
| (X1) | interpolating *factor* of arbitrary type | rejected | **(X1) separating object** — identity inclusion of the hyperfinite type III₁ factor: interpolates itself, split fails (identity-inclusion row) | a/c | 2026-08-14 |
| (X2) | interpolating type I *algebra* instead of factor | rejected | **(X1) separating object** — ℂ⊕ℂ ⊆ ℂ⊕ℂ on ℂ²: the only interpolating algebra is ℂ⊕ℂ, type I but not a factor | — | 2026-08-14 |
| (X3) | "Λ(1)′ ∩ Λ(2) contains a type I factor" | rejected | **(X2) degeneracy/vacuity** — ℂ1 always qualifies; satisfied by every unital inclusion, incl. the non-split (X2) witness | — | 2026-08-14 |
| (X4) | statistical independence of (Λ(1), Λ(2)′) as the definition (≡ quasi-split, (D7)) | rejected | **(X1) separating object** — the 5-dimensional witness (degeneracy table): quasi-split and W*-independent yet not split; it has no semi-standard vector, exactly threading [DL84]'s gap. **(X5) conditional equivalence** — split ⇔ quasi-split under a semi-standard state ([DL84] §1, tier (b)); the standard-position sub-question is thereby settled affirmatively. Under HS17's spatial gloss of ≅ ((C7)) the candidate becomes (X7) and is equivalent | b | 2026-08-14 |
| (X5) | uniqueness of the interpolating 𝔑 required | rejected | **(X1) separating object** — ℂ1 ⊆ M₂(ℂ): both ℂ1 and M₂ interpolate. [DL84] Cor. 2.4 confirms structurally: uniqueness only per standard vector | a/b | 2026-08-14 |
| (X6) | strict intermediacy (𝔑 ∉ {Λ(1), Λ(2)}) | rejected | **(X1) separating object** — ℂ1 ⊆ M₂(ℂ) is split, but the only unital subfactors of M₂ are the endpoints | — | 2026-08-14 |
| (X7) | tensor/unitary form: ∃ W: ℋ → ℋ_A ⊗ ℋ_B with WΛ(1)W* ⊆ 𝔅(ℋ_A)⊗1, WΛ(2)′W* ⊆ 1⊗𝔅(ℋ_B) | equivalent | — ((⇐) is HS17's construction, tier (a); (⇒) via the type I structure theorem, used verbatim in [DL84] Prop. 1.5, tier (b), mineru-unchecked — promoted from (d) by the refutation fetch). HS17's literal ℋ⊗ℋ form is conditionally equivalent (needs the cyclicity hypotheses making both legs ℋ) | b | 2026-08-14 |
| (X8) | net-level ∃ 𝔑 ∀ pairs | rejected | **(X2) degeneracy** — forces 𝔐 = ℂ1 in any net with factorial local algebras (corpus-only argument via locality + factoriality, no irreducibility needed); named case: free scalar field / any III₁ net | a | 2026-08-14 |
| (X9) | *claim* [KOE03 source.txt 6666–6669]: properly infinite von Neumann algebras on a separable ℋ admit joint cyclic-separating vectors | refuted | counterexample 𝔑 = 𝔐 = 𝔅(ℓ²): properly infinite, separable, **no separating vector at all**. Corrected statement = [DL84] Prop. 1.2 (needs standard action / properly infinite commutants); KOE03's application is sound, its freestanding sentence is not | b | 2026-08-14 |
| (X10) | *claim* [HS17 source.txt 991]: finite-dimensional commuting pair with trivial intersection is always statistically independent | refuted | counterexample: 𝔄_A = {1, p}″, 𝔄_B = {1, q}″ with p, q nonzero orthogonal projections, p + q < 1 (e.g. on ℂ³): commuting, 𝔄_A ∩ 𝔄_B = ℂ1, but 𝔄_A ∨ 𝔄_B ≅ ℂ³ ≇ ℂ⁴ ≅ 𝔄_A ⊗ 𝔄_B, and the product state with φ(p) = ψ(q) = 1 admits no extension (ω(1−p−q) = −1). True for commuting finite-dimensional *factors* | — (written-out argument) | 2026-08-14 |

## Prior art

| System | Found | Relation to variants | How searched | Measured at |
|---|---|---|---|---|
| this repository | `VonNeumannAlgebra.IsSplitInclusion` (`QuantumSystem/Algebra/VonNeumannAlgebra/SplitInclusion.lean`) — interpolating type I factor, containment derived; monotonicity, sandwich and self constructors; `IsSplitInclusion.exists_tensor_decomposition` (spatial split of the interpolating factor and its commutant) | same as (D6)/adopted form; the tensor decomposition is the (X7)(⇒) direction | find/grep over QuantumSystem/ | working tree, 2026-08-15 |
| this repository | `VonNeumannAlgebra.not_isSplitInclusion_diagonalAlgebra` (`QuantumSystem/Algebra/LocalNet/Examples.lean`) — identity inclusion of `diagonalAlgebra := commutantSet {diagonalProjection}` on `EuclideanSpace ℂ (Fin 2)` (concretely ℂ⊕ℂ, the diagonal operators) is **not** split, via `not_isTypeIFactor_diagonalAlgebra`/`not_isFactor_diagonalAlgebra` and `IsSplitInclusion.isTypeIFactor_of_self`; axiom-checked (`#print axioms`), rests only on `propext`, `Classical.choice`, `Quot.sound` | **negative witness** — realizes the degeneracy table's minimal witness ℂ⊕ℂ ⊆ ℂ⊕ℂ (also the object underlying (X2)'s discriminator); distinct in kind from the positive rows above (`IsSplitInclusion` itself, `exists_tensor_decomposition`, `VonNeumannNet.SplitProperty`), which inhabit the predicate rather than refute it | `lean_local_search`, `lean_declaration_file`, axiom check via `#print axioms` | working tree, 2026-08-15 |
| this repository | `LocalNet.SplitProperty` (`QuantumSystem/Algebra/LocalNet/SplitProperty.lean`) — nested form over `ProperContainment` pairs, stated as `VonNeumannNet.SplitProperty` at the representation instance | same as (D1) at net level (nested form, as adopted) | same | working tree, 2026-08-15 |
| this repository | type classification substrate: `IsFactor`, `IsTypeI`, `IsTypeIFactor`, `IsTypeIInfinite`, Murray–von Neumann equivalence, `IsTypeIFactor.exists_starAlgEquiv`, type I structure theorem, `vnTensorLeft/Right` commutant theorems, double commutant theorem (both halves) | supports the adopted form; (X7)(⇒)'s external is proved here | same | working tree, 2026-08-14 |
| this repository | could not find: statistical independence (D2), split unitary W (D3), product-state form (D4), standard split inclusion, quasi-split (D7), W*-independence, funnel property, hyperfinite III₁, normal states | — | grep for product state / independence / standard split / funnel / hyperfinite / cyclic | working tree, 2026-08-14 |
| Mathlib | `VonNeumannAlgebra`, `WStarAlgebra`, `commutant`, `commutant_commutant`, WOT files — substrate only | can phrase an inclusion and commutants; nothing more | grep over `.lake/packages/mathlib`, `lean_leansearch` | mathlib rev `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |
| Mathlib | could not find: split inclusion, type I factor, factor (vN sense), MvN equivalence, hyperfinite, normal state, statistical independence, vN double commutant theorem (the structure's field is an axiom, not the theorem) | no Mathlib declaration can state any variant | grep sweeps + `lean_leansearch` | mathlib rev `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |
| Lean ecosystem | vN double commutant TFAE is a Lean AI leaderboard benchmark (solved by AI systems, May–July 2026) — corroborates absence from Mathlib | substrate | leaderboard page fetched | 2026-08-14 |
| Isabelle AFP | substrate only (Complex_Bounded_Operators, Hilbert tensor products, Kraus Maps, GNS 2026, Registers); no vN algebra structure, factors, or split found | Hilbert tensor product is substrate (D2) would need | topic index + entry pages; **search.isa-afp.org unreachable (TLS)** | 2026-08-14 |
| Coq/Rocq (CoqQ/mathcomp) | finite-dimensional only; no vN algebra structure | trivialised setting for every variant | web searches, paper summaries | 2026-08-14 |
| Lean Zulip | could not find indexed threads, having searched site-scoped and archive-scoped web queries — a statement about the searches run, not about absence | — | web searches | 2026-08-14 |
| any system, AQFT level | could not find any other formalization of Haag–Kastler nets or the net-level split property | this repository's `LocalNet.SplitProperty` is the only one located | web searches | 2026-08-14 |

## Open questions

- A concrete non-split net, named at a checkable tier: [DL84] announces
  > In particular we give examples of field theories which do not fulfill the split property.
  (§9–10, pages not converted). Converting DL84 pp. 15–44 would likely move (A13) from `open`.
- "Exhausting 𝔄" and "intermediate" in (D5)/(R9): undefined in every fetched text.
- (A14) asymptotic scale invariance: formulation lives in BDF87 (unfetched).
- (R4) vs (R5): which hypothesis-set BDF87 actually uses — needs the paper.
- Whether the free KG field satisfies (A14) (needed to run (A7)'s witness fully inside HS17's own hypotheses).
- KOE03's stated open problem (source.txt 2750–2752): a split-based triviality argument for certain coset representations is "out of reach to date".
- (A1): does any result in this circle actually need separability at the bare-form layer? (For standard split inclusions it is a theorem; no fetched result visibly consumes the standing assumption.)

## Sources

**Append-only.**

| Key | Work | Status | Cache | Version | Tier reached | Retrieved |
|---|---|---|---|---|---|---|
| KOE03 | S. Köster, *Structure of Coset Models*, dissertation, arXiv math-ph/0308031 | retrieved (arXiv LaTeX, verbatim) | `references/arxiv-math-ph-0308031/` | arXiv v1 | a | 2026-08-14 |
| HS17 | S. Hollands, K. Sanders, *Entanglement measures and their properties in quantum field theory*, arXiv 1702.04924 | retrieved (arXiv LaTeX, verbatim) | `references/arxiv-1702.04924/` | arXiv | a | 2026-08-14 |
| dB74 | D. Buchholz, *Product states for local algebras*, Comm. Math. Phys. 36 (1974) | retrieved **partial** — pp. 1–8 of 18, Project Euclid PDF via MinerU hybrid-engine | `references/buchholz-1974-product-states/` | published | b (mineru-unchecked) | 2026-08-14 |
| DL84 | S. Doplicher, R. Longo, *Standard and split inclusions of von Neumann algebras*, Invent. Math. 75 (1984) 493–536 | retrieved **partial** — pp. 1–14 of 44 (§0–§4), GDZ digitization via MinerU hybrid-engine | `references/doplicher-longo-1984-standard-split/` | published | b (mineru-unchecked) | 2026-08-14 |
| FG93 | Gabbiani, Fröhlich, *Operator algebras and conformal field theory* | not retrieved — not attempted this run | — | — | c | 2026-08-14 |
| BDF87 | Buchholz, D'Antoni, Fredenhagen, *The universal structure of local algebras*, CMP 111 (1987) | not retrieved — not attempted this run | — | — | c | 2026-08-14 |
| BW86 | Buchholz, Wichmann, *Causal independence and the energy-level density of states…* | not retrieved — not attempted this run | — | — | c | 2026-08-14 |
| BDL86 | Buchholz, Doplicher, Longo, *On Noether's theorem in quantum field theory* | not retrieved — not attempted this run | — | — | c | 2026-08-14 |
| ADF87 | D'Antoni, Doplicher, Fredenhagen, Longo, *Convergence of local charges…* | not retrieved — not attempted this run | — | — | c | 2026-08-14 |
| FV13 | Fewster, Verch, *The necessity of the Hadamard condition* (HS17's fewster_2) | not retrieved — not attempted this run | — | — | c | 2026-08-14 |
| DHR02 | Donald, Horodecki, Rudolph (HS17's donald_2) | not retrieved — not attempted this run | — | — | c | 2026-08-14 |
| MTW | Morinelli, Tanimoto, Weiner, *Conformal covariance and the split property* | not retrieved — not attempted this run | — | — | c | 2026-08-14 |
| SS90 | Summers, independence-notions survey (KOE03's sS90) | not retrieved — not attempted this run | — | — | d | 2026-08-14 |
| GLW98 | Guido, Longo, Wiesbrock (KOE03's GLW98) | not retrieved — not attempted this run | — | — | c | 2026-08-14 |
| DM | Dixmier, Maréchal (DL84's ref. [14]) | not retrieved — not attempted this run | — | — | c | 2026-08-14 |

Further works cited by the corpus and not retrieved (uH87, CC01, KLM01, vL97,
fX00a, florig, narnhofer_1, summers_1/2, haag_2, dantoni, buchholz_3,
buchholz_5, LRT78, FJ96, mT72, vJ83, wD75, RS61, hjB68, bS74): every claim
through them carries a substitution sentence, no locators beyond the attesting
sources' own citations.

## Not investigated

- **The [ext] gap.** Lane 5 swept only the formalization landscape; **no lane
  checked any of the external mathematical results** lane 2 marked. The
  refutation pass fetched exactly two (dB74 pp. 1–8, DL84 pp. 1–14); all other
  [ext] edges — BW86, BDF87, FG93, BDL86, ADF87, uH87, fewster_2, donald_2,
  MTW/weiner, CC01, KLM01, vL97, fX00a, sS90, florig, GLW98, Dixmier–Maréchal,
  narnhofer_1, summers_1/2, haag_2, dantoni, buchholz_3, buchholz_5 — remain
  unexamined; (R2), (R4), (R5), (R12), (R13), (R15), (R18), (R19) and the
  GLW98/fewster_2 witness legs rest entirely on attestations.
- **Unconverted pages.** dB74 pp. 9–18; DL84 pp. 15–44, including Th. 8.3's
  dyadic-chain proof ((R9)), §6 standard-vector structure, and the §9–10
  non-split field theories that would unblock (A13).
- **MinerU output was not compared against page images**: every dB74/DL84 quote
  and locator stays (b) with `mineru-unchecked`.
- Degeneracy probes skipped: type II endpoints as separate witnesses; whether
  split inclusions of type III algebras force 𝔑 type I_∞; the repaired
  candidate "Λ(1)′ ∩ Λ(2) is a type I factor"; σ-finiteness separately from
  separability.
- Variants sighted, not pursued: the C*-independence side of the sS90 taxonomy;
  HS17's curved-spacetime axiom variants a3′), a4′); the funnel property
  (searched only by lane 5 as a keyword).
- AFP full-text search (site unreachable); Lean Zulip content; CoqQ source.
- KOE03's finite-index chapters beyond the grep hits; HS17's Thm_m>0, Thm_KMS,
  Thm_ER<EN, Thm_EN<Em and the N-Cbit construction (iterate (R11)'s mechanism).
- **The unexamined base**: the tier (c) rows everything above stands on — (R2),
  (R4), (R5) and the external legs of (A3), (A7), (A15), (R6)(b), (R8), (R11)
  — plus the mineru-unchecked (b) layer of dB74/DL84.
