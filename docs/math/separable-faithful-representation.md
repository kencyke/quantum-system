---
object: Faithful representation of a separable C*-algebra on a separable Hilbert space
slug: separable-faithful-representation
status: draft
worst-tier: c
mathlib-rev: 5450b53e5ddc75d46418fabb605edbf36bd0beb6
implemented-as: CStarRep.exists_isometric_separable
revisions:
  - 2026-08-16 · 2e21b4b · initial extraction · sources: BF26, LAN98, SHI12, VER25
---

<!--
Macros the quotes below need, copied from each source's own preamble:
  \cB, \cH   BF26,  references/arxiv-2602.15812/raw/measpreambleu.tex:63, :79
  \cstar     BF26,  references/arxiv-2602.15812/raw/measpreambleu.tex:292
  \sfS       BF26,  references/arxiv-2602.15812/raw/25-Cstar-choice.tex:76
  \ca        LAN98, references/arxiv-math-ph-9807030/raw/*.tex:53
  \rep       LAN98, :56
  \Hs        LAN98, :58
  \om        LAN98, :233
  \A         LAN98, :238
  \H         LAN98, :269  (the source itself uses \renewcommand — KaTeX defines \H)
  \cs, \ss   SHI12, references/arxiv-1211.3404/raw/main.tex:65, :66  (\def, not \newcommand)
-->

$$
\newcommand{\cB}{{\mathcal B}}
\newcommand{\cH}{{\mathcal H}}
\newcommand{\cstar}{$\mathrm{C}^*$}
\newcommand{\sfS}{\mathsf S}
\newcommand{\ca}{$C^*$-algebra}
\newcommand{\rep}{representation}
\newcommand{\Hs}{Hilbert space}
\newcommand{\om}{\omega}
\newcommand{\A}{{\frak A}}
\renewcommand{\H}{{\cal H}}
\def\cs{{$C^{\ast}$}}
\def\ss{{$\ast$}}
$$

# Faithful representation of a separable C\*-algebra on a separable Hilbert space

## What this object is for

The Gelfand–Naimark theorem places every C\*-algebra inside the bounded operators
on *some* Hilbert space, but the Hilbert space its standard proof produces is
indexed by the whole state space and is enormous. This object is the refinement
that bounds the size of the Hilbert space by the size of the algebra: a
countable dense subset of the algebra buys a countable dense subset of the
Hilbert space. The generality that matters is that nothing beyond separability
is assumed — not unitality, not commutativity, not nuclearity — and that the
bound is one-directional: it is a sufficient condition on the algebra, never a
characterisation.

## Definition

### Variants as the sources write them

| (D#) | Source | What is asserted | "faithful" reads as | "separable H" reads as | unitality | ambient theory | Tier |
|---|---|---|---|---|---|---|---|
| (D1) | [BF26] `SepRepThm` | the object | undefined in the source | undefined in the source | none assumed | ZF | a |
| (D2) | [BF26] `RepCAlg` | *representable*: no separability of H at all | isomorphism onto a **closed** \*-algebra of operators | — (H unrestricted) | none assumed | ZF | a |
| (D3) | [LAN98] `injmor` context | ingredient definition | **injective**; isometry derived | — | — | ZFC | a |
| (D4) | [VER25] Operator Algebra Basics | ingredient definition | **injective** (π(A)=0 ⟹ A=0); faithful *state*: ω(A\*A)=0 ⟹ A=0 | — | unital throughout | ZFC | a |
| (D5) | [SHI12] Approximate units | ingredient: separable **algebra** | — | — | — | ZFC | a |
| (D6) | [SHI12] Hilbert spaces | ingredient: separable **Hilbert space** | — | **countable orthonormal basis** | — | ZFC | a |
| (D7) | [SHI12], [LAN98] `GNSconstruction` | ingredient: H_φ as an explicit completion | — | — | LAN98 unital only | ZFC | a |

**(D1) [BF26] Theorem `SepRepThm`** — tier (a)

> `Every separable C*-algebra has a faithful representation as a concrete C*-algebra of operators on a separable Hilbert space.`

BF26 nowhere defines "faithful representation": the word occurs six times in the
whole paper and never in a definition environment. The meaning has to be
imported, which is what (D3) and (D4) supply.

**(D2) [BF26] Definition `RepCAlg`** — tier (a)

> `A \cstar-algebra $A$ is {\em representable} if it is isomorphic to a closed *-algebra of bounded operators on a Hilbert space.`

`differs from (D1) by:` (D2) demands an isomorphism onto a norm-**closed**
\*-subalgebra and says nothing about the Hilbert space, where (D1) demands a
faithful map and a **separable** Hilbert space.
`sources claim equivalence:` not addressed — BF26 uses both in one subsection
without remarking on the difference.

**(D3) [LAN98] Lemma `injmor` and its use** — tier (a)

> `An injective morphism between \ca s is isometric. In particular, its range is closed.`

used in the sentence "‖π(A)‖ = ‖A‖

> `when $\pi$ is faithful by Lemma \ref{injmor}`

`differs from (D1) by:` fixes faithful = injective and derives the other two
readings.
`sources claim equivalence:` yes — this lemma, together with [SHI12]
`cor:firstiso`, *is* the equivalence; see (R5).

**(D4) [VER25] §Operator Algebra Basics** — tier (a)

> `A state on a unital $*$-algebra $\mathbfcal{A}$ is called \textbf{faithful} if, for any $\Att \in \mathbfcal{A}$,`

followed by the displayed ω(A\*A) = 0 ⟹ A = 0; faithfulness of a representation
is defined in the same passage by π(A) = 0 ⟹ A = 0.

`differs from (D3) by:` nothing for representations; (D4) additionally defines
the *faithful state*, which (D3) does not and which (D1)'s justification
consumes.
`sources claim equivalence:` not addressed.

**(D5) [SHI12] §Approximate units** — tier (a)

> `A \cs-algebra $A$ is called {\bf separable} if it possesses a countable and dense subset.`

BF26 uses the same notion without a definition environment, speaking throughout
of a countable dense subset and, in `L.states`, of "a countable dense sequence".

**(D6) [SHI12] §Hilbert spaces** — tier (a)

> `A Hilbert space is called {\bf separable} if it has a countable orthonormal basis.`

immediately followed by

> `\begin{exercise} Let $H$ be a Hilbert space. Show that $H$ is a separable Hilbert space if and only if $H$ is a separable topological space. \end{exercise}`

`differs from (D5) by:` (D6) is basis-theoretic where (D5) is topological, and
the source relegates their equivalence to an exercise rather than proving it.
`sources claim equivalence:` yes, as an exercise — but see (X3): the two are
**provably inequivalent** in ZF, which is the ambient theory of the source that
states (D1).

**(D7) [LAN98] Construction `GNSconstruction`, [SHI12] §Hilbert spaces** — tier (a)

> `The \Hs\ $\H_{\om}$ is the closure of $\A/{\cal N}_{\om}$ in this inner product.`

SHI12 builds the same object as `The completion of $A/N_\ff$ with respect to the norm defined by $\inner_\ff$`, and VER25 instead postulates the triple abstractly
with a cyclic vector. Only the completion form makes separability of H_ω
visible, which is why the corpus's failure to prove (R7) is a failure to compose
two of its own definitions.

### Adopted general form

Let `A` be a C\*-algebra over ℂ — an involutive Banach algebra with
‖x\*x‖ = ‖x‖² — **not** assumed unital and **not** assumed commutative, and
suppose `A` is separable as a metric space, that is, `A` has a countable dense
subset in the norm topology (D5). Then there exist a complex Hilbert space `H`
and a map `π` such that

1. `H` has a countable dense subset in the norm topology;
2. `π : A → B(H)` is a \*-homomorphism — linear, multiplicative, and
   star-preserving — into the bounded linear operators on `H`;
3. `π` is injective.

Nothing further is assumed of `A`, and nothing further is asserted of `π`: in
particular the adopted form does **not** claim that `π` is nondegenerate, does
**not** claim `π(1) = 1` when `A` is unital, and does **not** claim that `H` may
be taken to be ℓ²(ℕ). The hypotheses carried are (A1) alone. Three consequences
follow from 1–3 with no extra input and are therefore not extra content (R5):
`π` is isometric, its range is norm-closed, and `π` corestricts to a
\*-isomorphism of `A` onto a C\*-subalgebra of `B(H)` — which is what makes the
phrase "concrete C\*-algebra of operators" in (D1) legitimate.

*Justification.* This is (D1), the only formulation in the corpus that states
the object, with its two undefined phrases fixed. "Faithful" is read as
injective, following (D3) and (D4), the only sources in the corpus that define
the word; (X5) and (X6) record that injective, isometric, and "isomorphic onto a
norm-closed \*-subalgebra" coincide for C\*-algebras, so this reading costs no
generality and (D2) is not a competing variant. "Separable Hilbert space" is
read topologically rather than basis-theoretically, following (X3)'s
**(X5) conditional equivalence**: the two readings agree under the axiom of
countable choice and come apart without it, and BF26 — the source that states
(D1) — works in ZF and says so explicitly, so the topological reading is the
only one available to it. Under ZFC, the ambient theory of every other source in
the corpus, the choice is inert.

## Notation and conventions

| (C#) | Axis | This note | Per source | Translation |
|---|---|---|---|---|
| (C1) | what "faithful" means | injective | [LAN98] injective, isometry derived; [VER25] injective; [BF26] undefined, glossed parenthetically as isometric; [SHI12] no notion of faithful representation | the three readings coincide, by (R5) |
| (C2) | unitality | not assumed | every source does its state/GNS work in the unital case and defers the rest to unitisation; [BF26] `RepThm` says "separable (unital)" with the parenthesis, `SepRepThm` says nothing; none of the three writes the unitisation argument | (A2) |
| (C3) | what "separable Hilbert space" means | countable dense subset | [SHI12] countable orthonormal basis, equivalence set as an exercise; [BF26] topological, forced by its ZF setting | equivalent under countable choice only — (X3) |
| (C4) | ℓ²(ℕ) as the canonical space | not used in the statement | [SHI12] is careful — `When $H$ is an infinite dimensional separable Hilbert space, or equivalently $H\simeq \ell^2$`; the ℓ²(ℕ) phrasing appears in BF26 only in commented-out source | a formulation naming ℓ²(ℕ) silently excludes the finite-dimensional case unless ℓ² is read as allowing finite dimension |
| (C5) | conjugate-linearity of the inner product | first argument | [LAN98] `(A,B)_0:=\om(A^* B)`, first argument; [VER25] first argument; [SHI12] not determined | — |
| (C6) | nondegeneracy | not asserted | [LAN98] defines it and uses it elsewhere; 0 occurrences in [BF26] and [VER25]; no source attaches it to this object | (A9) |
| (C7) | ambient set theory | ZFC assumed, ZF tracked | [BF26] ZF throughout; [LAN98] [SHI12] [VER25] ZFC | the ZF/ZFC split is what makes (C3) a live axis and (R5) an edge rather than a triviality |

## Results and dependencies

### (R1) The object

Every separable C\*-algebra has a faithful representation as a concrete
C\*-algebra of operators on a separable Hilbert space.

- Source: [BF26] Theorem `SepRepThm` · tier (a) · **asserted**
- Depends on: (R2), (R6), (R7), (R5)
- Conventions: (C1), (C3), (C7)
- Verbatim:
  > `Every separable C*-algebra has a faithful representation as a concrete C*-algebra of operators on a separable Hilbert space.`

**No `Proof route:` field, because there is no proof.** There is no proof
environment after the theorem in BF26's source; the entire justification is the
single sentence preceding it:

> `In fact, using \ref{FaithfulStateThm} we can do better, since the GNS representation from a faithful state is faithful:`

That sentence supplies (R2) and asserts (R6). It says nothing about separability
of the GNS Hilbert space — the adjective that distinguishes this theorem from
the unrefined Gelfand–Naimark theorem (R8) — and nothing about the image being
norm-closed. Of the four things (R1) needs: one is proved in the stating source,
one is asserted twice and proved nowhere in the corpus, one is absent from the
corpus entirely, and one is proved only in ZFC sources while the stating source
works in ZF.

### (R2) A separable C\*-algebra has a faithful state

- Source: [BF26] Proposition `FaithfulStateThm` · tier (a) · **proved in source**
- Depends on: (R3), (R4), (A2), [ext: a countable convex combination of states is a state — used in step 3 and stated nowhere in the corpus]
- Conventions: (C2)
- Proof route:
  1. Reduce to the unital case — asserted, not argued, consuming (A2);
  2. `S(A)` is weak\*-separable — consumes (R3);
  3. take a weak\*-dense sequence (φₙ) in `S(A)` and set φ = Σ 2⁻ⁿ φₙ, a state
     because a countable convex combination of states is a state;
  4. for positive `a` of norm 1 there is a state ψ with ψ(a) = 1 — consumes (R4);
  5. approximate ψ by some φₙ, giving φₙ(a) > ½, hence φ(a) ≥ 2⁻ⁿφₙ(a) > 0.
- Verbatim:
  > `A separable \cstar-algebra has a faithful state.`

Note which faithfulness is produced: step 5 yields φ(a) > 0 for positive `a`,
the order-theoretic form, where (D4) defines faithfulness of a state by
ω(A\*A) = 0 ⟹ A = 0. These are interchangeable, but BF26 neither says so nor
defines the term.

### (R3) The state space of a separable unital C\*-algebra is separable, compact and metrizable in the weak\* topology

- Source: [BF26] Lemma `L.S(A)` · tier (a) · **proved in source**
- Depends on: (R4), [ext: BF26's own separable Hahn–Banach / Banach–Alaoglu package], [ext: BF26's separable Krein–Milman], [ext: Blackadar, *Real Analysis* — the pure state space of a separable unital C\*-algebra is a G_δ subset of the state space]
- Conventions: (C2), (C7)
- Verbatim:
  > `Suppose that $A$ is a separable unital \cstar-algebra. Then the state space $\sfS(A)$ with respect to the weak*-topology is a separable compact metrizable space.`

Only the weak\*-separability clause is consumed by (R2). The Krein–Milman step
inside this proof supports the pure-state clause, which nothing on the route to
(R1) cites — see (A7).

### (R4) Every separable C\*-algebra has sufficiently many states

- Source: [BF26] Lemma `L.states` · tier (a) · **proved in source**
- Depends on: (A2), [ext: BF26's own positivity proposition — `x*x` is a positive element], [ext: BF26's separable Hahn–Banach extension], [ext: BF26's continuous functional calculus], [ext: Blackadar, *Operator Algebras* — a linear functional on a unital C\*-algebra is a state iff it has norm 1 and value 1 at the unit]
- Conventions: (C2), (C7)
- Proof route:
  1. reduce to `A` unital — asserted, consuming (A2);
  2. `x*x` is positive;
  3. ‖λ1 + x\*x‖ = λ + ‖x\*x‖ for λ ≥ 0, by functional calculus — consumes the
     functional-calculus edge;
  4. on the two-dimensional span of 1 and `x*x`, the functional sending 1 ↦ 1
     and `x*x` ↦ ‖x‖² has norm 1;
  5. extend by Hahn–Banach for separable Banach spaces, choice-free — consumes
     the Hahn–Banach edge;
  6. a norm-1 functional taking value 1 at the unit is a state — consumes the
     Blackadar edge.
- Verbatim:
  > `Every separable \cstar-algebra, and more generally every \cstar-algebra with a well-ordered dense subset, has sufficiently many states.`

BF26 defines "sufficiently many states" as: for every `x` there is a state φ
with ‖π_φ(x)‖ = ‖x‖. The proof produces φ(x\*x) = ‖x‖²; the one-line bridge
between the two is **not written down in BF26**.

### (R5) An injective \*-homomorphism of C\*-algebras is isometric, and its range is norm-closed

- Source: [LAN98] Lemma `injmor`; [SHI12] Corollary `cor:csinjection` together with Corollary `cor:firstiso` · tier (a) · **proved in source** (SHI12), **sketched** as read by this extraction (LAN98)
- Depends on: [LAN98] its ideal theory
- Conventions: (C1), (C7) — both sources are ZFC
- Verbatim:
  > `An injective morphism between \ca s is isometric. In particular, its range is closed.`

  > `Every injective \ss-homomorphism between two \cs-algebras is an isometry.`

This is one result with two locators, kept as one row. It is what makes (C1)
inert and (D2) not a competing variant. It is also the edge that BF26 uses
parenthetically — `a direct sum of GNS representations is faithful (isometric)` —
without citing any lemma, which in a ZF paper is not free; see `## Open questions`.

### (R6) The GNS representation of a faithful state is faithful

- Source: [VER25] §Operator Algebra Basics · tier (a) · **asserted**
- Depends on: [VER25]'s GNS theorem, for the existence of the triple
- Conventions: (C2) — stated for unital algebras
- Verbatim:
  > `For a unital $C^*$-algebra, if a state $\omega$ is faithful, then $(\pi_\omega,\mathcal{H}_\omega)$ is faithful.`

This is exactly the step (R1)'s one-sentence justification consumes. The corpus
states it twice — here and inside BF26's sentence — and proves it zero times.
[LAN98] has the only *proved* proposition in this direction, and it is about the
compact operators specifically, not a general C\*-algebra.

### (R7) The GNS Hilbert space of a state on a separable C\*-algebra is separable

**Absent from the corpus.** No source states, proves or cites it.

- Source: none · tier — · **not in corpus**
- Depends on: (D7) plus the general facts that a continuous image of a separable
  space is separable and that the closure of a separable subset is separable
- Conventions: (C3)

Both ingredients are present, in different sources: [VER25] gives cyclicity of
Ω_ω, and [LAN98]/[SHI12] give H_ω as the closure of a quotient of `A` (D7).
Either yields H_ω as the closure of a continuous image of `A`, hence separable
when `A` is, with no choice used because the dense sequence in H_ω is the
*image* of a fixed dense sequence in `A`. **No source performs the
composition.** This is the entire content of the refinement over (R8), and it is
the one step the literature in this corpus leaves unwritten.

### (R8) The unrefined Gelfand–Naimark representation theorem

- Source: [LAN98] Theorem `GNT` · tier (a) · **proved in source**; announced without proof by [SHI12]
- Depends on: [LAN98] `defunivrep`, `gnscor`, `lots`, the C\*-identity, (R5)
- Conventions: (C1)
- Proof route:
  1. take `H` to be the universal representation's space ⊕_{ω∈S(A)} H_ω —
     consumes `defunivrep`;
  2. π_u(A) = 0 forces π_ω(A) = 0 for every state — by definition of direct sum;
  3. hence ω(A\*A) = 0 for every state — consumes `gnscor`;
  4. hence ‖A\*A‖ = 0 — consumes `lots`, "there are lots of states";
  5. hence A = 0 by the C\*-identity;
  6. injective ⟹ isometric — consumes (R5).
- Verbatim:
  > `A \ca\ is isomorphic to a subalgebra of $\B(\H)$, for some Hilbert space $\H$.`

### (R9) The universal Hilbert space is too large, and the pure-state reduction does not fix it

- Source: [LAN98], the paragraph after the proof of `GNT` · tier (a) · **remark (asserted)**, with a **proved** reduction to pure states
- Depends on: (R8), [LAN98] `lotsp`, [ext: Krein–Milman, which LAN98 states without proof]
- Verbatim:
  > `While the universal \rep\ leads to a nice proof of \ref{GNT}, the \Hs\ $\H_{\mbox{\tiny u}}$ is absurdly large; in practical examples a better way of obtaining a faithful \rep\ always exists.`

This is the corpus's own statement that (R8) does not deliver a separable
Hilbert space. LAN98's remedy is to sum over pure states, and then over one pure
state per unitary-equivalence class — a reduction that for a separable algebra
still leaves an uncountable index set. See (X1) and (X2).

### (R10) `B(H)` is norm-separable if and only if `H` is finite-dimensional

- Source: [BF26] Theorem `BHNormSepThm` · tier (a) · **proved in source** (read as a sketch by this extraction)
- Depends on: [BF26] `OrthProjSeqProp`, and its choice-free replacement for the orthonormal-sequence argument
- Verbatim:
  > `Let $\cH$ be a Hilbert space. Then $\cB(\cH)$ is norm-separable if and only if $\cH$ is finite-dimensional.`

No step of (R1) consumes this, so it is not an edge. It is the boundary object:
it shows that "faithful representation on a separable Hilbert space" must not be
confused with "faithful representation into a separable `B(H)`", which would
force finite dimension and trivialise the object. [LAN98] makes the same
observation from the other side: `Another argument against $\BH$ is that it is non-separable in the nom-topology even when $\H$ is separable.` (the typo `nom-` is
in the original).

### (R11) Every closed subspace of a separable Banach space is separable

- Source: [BF26] Proposition `ClosedSubspaceProp` · tier (a) · **cited elsewhere**
- Depends on: [ext: Blackadar, *Real Analysis* — every closed subset of a separable metric space is separable]

Not an edge of (R1). With (R1) it gives that the image π(A) is itself a
separable concrete C\*-algebra.

### (R12) Two Hilbert spaces are unitarily equivalent iff their orthonormal bases are equinumerous

- Source: [SHI12] Corollary `cor:Hilbertcardinality` · tier (a) · **proved in source**
- Depends on: [SHI12]'s theorem that any two orthonormal bases are equinumerous
- Conventions: (C3), (C4), (C7)

This is what would licence replacing "separable Hilbert space" by ℓ²(ℕ) in the
infinite-dimensional case. It is unusable in BF26's ZF setting (C3), and SHI12's
equinumerosity proof makes an unflagged simultaneous choice.

### (R13) Every separable commutative C\*-algebra is C₀(X) for a locally compact metrizable X

- Source: [BF26], the separable commutative Gelfand theorem · tier (a) · **proved in source**
- Depends on: (R4), (A7) Krein–Milman, Stone–Weierstrass
- Conventions: (C7)

Recorded because it gives a second, independent route to (R1) in the commutative
case, and because that route is **strictly more expensive** in ZF than the
general one: it consumes Krein–Milman, which the general route does not (A7).

## Hypotheses

| (A#) | Statement | Class | Evidence | Witness | Scope | Tier | Used by |
|---|---|---|---|---|---|---|---|
| (A1) | `A` is norm-separable | antecedent — the hypothesis of the theorem, not a side condition | [BF26] `SepRepThm`; [SHI12] definition | — | standing | a | (R1)–(R4) |
| (A1b) | separability of `A` is **not necessary** for the conclusion | — (a finding: the hypothesis cannot be made an iff) | [BF26] `BHNormSepThm`; [LAN98] | **B(ℓ²)**, non-separable yet faithfully represented on ℓ² by its identity representation; likewise ℓ^∞(ℕ) | — | a | — |
| (A2) | `A` is unital | provable — removable by unitisation | [BF26] `L.states`, `FaithfulStateThm` both open "We may assume `A` is unital", unargued; [LAN98] defers to `extstate` | — (non-unital instance C₀(ℝ) is covered) | local | a | (R2), (R4) |
| (A3) | `A` is σ-unital | provable from (A1) | [SHI12] "Every separable C\*-algebra is σ-unital"; [LAN98] `exau` | — | local | a | — (consumed by no step of the adopted route) |
| (A4) | `A` has sufficiently many states / is representable | provable under (A1); **model-dependent** without it | [BF26] `L.states`, `P.Representable`, `P.ExistenceOfStates` | **ℓ^∞(ℕ)/c₀(ℕ)** and the **Calkin algebra**, which have no states at all in ZF models where every set of reals has the Property of Baire | local | a | (R2) |
| (A5) | `A` has a faithful state | provable from (A1) | [BF26] `FaithfulStateThm` | — | local | a | (R1) |
| (A6) | `S(A)` is weak\*-separable | provable from (A1)+(A2); model-dependent without (A1) | [BF26] `L.S(A)`, `P.Russel.example` | the **Russell-set algebra** — concretely representable, unital, commutative, AF, non-separable, with a state space that is not compact and has no extreme points | local | a | (R2) |
| (A7) | Krein–Milman / nonemptiness of the pure state space | **not a hypothesis of this theorem** | [BF26]: the route `SepRepThm ← FaithfulStateThm ← L.S(A)` cites only weak\*-separability, itself from Banach–Alaoglu plus metrizability, both proved outright in ZF | — | — | a | (R13) only |
| (A8) | `H_φ` is separable when `A` is | provable from (A1) — **and no source in the corpus proves it** | the argument is written out at (R7); the corpus supplies only the ingredients | — | local | a | (R1) |
| (A9) | the representation is nondegenerate | provable for `A ≠ 0`; fails at `A = 0` | [LAN98] defines nondegeneracy; the GNS representation of a state on a unital algebra is cyclic, and cyclic ⟹ nondegenerate | `A = 0` | local | a | — (not asserted by the adopted form) |

Hypotheses searched for and found attached nowhere in this corpus: nuclearity,
exactness, simplicity, stable rank, existence of a tracial state, σ-finiteness,
type classification, amenability. The theorem rests on separability alone.

## Degeneracies and boundary cases

| Case | Effect on the adopted form | Tier |
|---|---|---|
| intended case is nonvacuous | **C([0,1])** — separable by Stone–Weierstrass over ℚ+iℚ, infinite-dimensional, and faithfully represented by multiplication operators on the separable space L²([0,1], m); second instance, the compacts 𝒦 = K(ℓ²) with their defining representation | a |
| zero object / scalars | `A = 0` is separable and the unique map into any `B(H)` is injective, so the adopted form holds trivially. It breaks two natural strengthenings: "π is nondegenerate on a nonzero H" and "π is unital" — see (X7) | a |
| finite-dimensional | no effect; conclusion automatic, since a finite-dimensional C\*-algebra is a direct sum of matrix algebras and sits in `B(ℂⁿ)`. By (R10) this is the **only** case where the ambient `B(H)` is itself norm-separable | a |
| commutative | no effect on truth; a second route exists via (R13) and multiplication operators on L²(X,μ), and that route is strictly more expensive in ZF because it consumes Krein–Milman (A7) | a |
| non-separable / non-σ-finite | **conclusion false.** Witness **c₀(ω₁)**: its ℵ₁ many singleton characteristic functions are nonzero mutually orthogonal projections, whose images under a faithful π are nonzero mutually orthogonal projections; the least-index argument BF26 uses for ε-discrete sets then injects ω₁ into ℕ. Non-σ-unital cannot arise at all, by (A3) | a |
| type III | outside the scope, provably: no infinite-dimensional von Neumann algebra is norm-separable, by BF26's 2^ℵ⁰-sized 1-discrete family of projections. Witnesses: the hyperfinite II₁ factor, L^∞([0,1]) — both act on separable Hilbert spaces and neither is a separable C\*-algebra | a |
| non-unital / degenerate representation | no effect; (A2) discharges unitality by unitisation and the adopted form asserts no nondegeneracy. Named non-unital separable instance: C₀(ℝ) | a |
| universally orthogonal index element | no effect on the adopted form. In the direct-sum formulations the index set is the state space; its degenerate extreme `A = ℂ` gives a one-dimensional sum, harmless, and its opposite extreme — uncountable state space — is what destroys those formulations (X1) | a |
| quantifier swap: ∀…∃… ↦ ∃…∀… | swapping to "for every `a ≠ 0` there is a representation on a separable H not killing `a`" gives BF26's weaker `RepThm`. Under (A1) the two are **equivalent**, by a route no source states: index by a dense sequence (aₙ) of the algebra, take the state norming each aₙ from (R4), and form the countable direct sum ⊕ₙ π_{ψₙ}. Each summand is separable by (A8), so the countable sum is separable in ZF, and the representation is isometric on a dense set | a |
| quantifier swap: ∃ separable H ↦ ∀ separable H | **false.** `A = M₂(ℂ)`, `H = ℂ`: `B(ℂ) = ℂ` admits no injective \*-homomorphism from M₂(ℂ) | a |
| hypothesis dropped: (A1) | nothing survives — false, witness c₀(ω₁) above | a |
| hypothesis dropped: (A2) | everything survives — discharged by unitisation | a |
| hypothesis dropped: (A5) | everything survives, via the quantifier-swap route above, which avoids the faithful state entirely | a |
| hypothesis dropped: (A7) | everything survives for this theorem; the *commutative* Gelfand theorem (R13) falls | a |
| hypothesis dropped: (A9) | everything survives, except at `A = 0` | a |

## Rejected formulations and refuted claims

**Append-only.**

| id | Candidate or claim | Disposition | Discriminator | Tier | Date |
|---|---|---|---|---|---|
| (X1) | take the direct sum of the GNS representations of **all** states — the universal representation | rejected | **(X1) separating object** — **ℂ²**: the cyclic vectors Ω_ω lie in mutually orthogonal summands and form an orthonormal family of cardinality \|S(A)\|, uncountable for every algebra of dimension ≥ 2, while ℂ² is separable. [LAN98] flags the defect (`absurdly large`) but adopts the construction, so this is not an (X4) | a | 2026-08-16 |
| (X2) | take one pure state from each unitary-equivalence class, and sum over those — [LAN98]'s own refinement | rejected | **(X1) separating object** — **C([0,1])**: its pure states are exactly the point evaluations (`The pure state space of the commutative \ca\ $C_0(X)$ (equipped with the relative $w^*$-topology) is homeomorphic to $X$.`), each with a one-dimensional GNS space and a distinct kernel, so the classes are still continuum many. C₀(ℝ) works identically | a | 2026-08-16 |
| (X3) | read "separable Hilbert space" as "has a countable orthonormal basis" | **(X5) conditional equivalence** | assumption named: the axiom of countable choice. [BF26], in ZF: `an infinite-dimensional Hilbert space need not contain an orthonormal sequence, or even an infinite orthonormal set`, and in the other direction there is a nonseparable Hilbert space carrying a sequence of mutually orthogonal rank-one projections. [SHI12] *adopts* the basis reading, so this is a definitional variant (D6), not a rejection | a | 2026-08-16 |
| (X4) | state the conclusion as "on ℓ²(ℕ)" | equivalent | for `A ≠ 0`, by amplification and (R12); only the *nondegenerate*-on-ℓ² variant dies at `A = 0`. Caveat (C4): the phrasing silently excludes finite dimension unless ℓ² is read loosely | a | 2026-08-16 |
| (X5) | demand "faithful **and** isometric" as two separate conditions | equivalent | (R5) — injective ⟹ isometric for C\*-algebras, so the second demand is empty | a | 2026-08-16 |
| (X6) | state it as "`A` is \*-isomorphic to a norm-closed \*-subalgebra of `B(H)`" rather than as an injective homomorphism | equivalent | (R5) — the image of an injective \*-homomorphism is automatically norm-closed. This is [BF26]'s own (D2) phrasing | a | 2026-08-16 |
| (X7) | strengthen the conclusion by demanding the representation be nondegenerate, or unital when `A` is | rejected | **(X2) degeneracy** — `A = 0`: no nondegenerate representation on a nonzero Hilbert space exists, and no unital \*-homomorphism `0 → B(H)` exists for `H ≠ 0` | a | 2026-08-16 |
| (X8) | strengthen "separable" to a characterisation — "`A` is separable **iff** it has a faithful representation on a separable Hilbert space" | refuted | **B(ℓ²)** is not norm-separable (R10) yet its identity representation on the separable space ℓ² is faithful. The hypothesis is sufficient and never necessary | a | 2026-08-16 |
| (X9) | strengthen the conclusion to "on ℓ² with π(A) containing no nonzero compact operator", or any similar structural normalisation of the image | open — could not separate; searched all three sources for `compact`, `essential`, `Calkin` and read [LAN98]'s compact-operator section | — | c | 2026-08-16 |
| (X10) | weaken "separable" to "has a well-ordered dense subset" in the conclusion as well as the hypothesis | open — could not separate. [BF26] pairs the two hypotheses systematically elsewhere (`Every separable \cstar-algebra, and more generally every \cstar-algebra with a well-ordered dense subset, has sufficiently many states.`) but stops short of the analogue for the representation theorem | — | c | 2026-08-16 |
| (X11) | *claim*: [BF26] proves `SepRepThm` | refuted | there is **no proof environment after the theorem** in BF26's LaTeX source: `\begin{Theorem}\label{SepRepThm}` is followed by the statement, `\end{Theorem}`, a commented-out paragraph, and then the commutative Gelfand theorem. The whole justification is the one preceding sentence, which never mentions separability of the Hilbert space | a | 2026-08-16 |
| (X12) | *claim*: the separable refinement is obtained by trimming the pure-state direct sum to a countable subfamily of pure states | refuted | (X2)'s separating object. The trimming that does work indexes by a dense sequence **of the algebra**, not by states — see the quantifier-swap row in `## Degeneracies` | a | 2026-08-16 |

## Prior art

| System | Found | Relation to variants | How searched | Measured at |
|---|---|---|---|---|
| Mathlib | `PositiveLinearMap.PreGNS`, `.GNS` (a `UniformSpace.Completion`), `.gnsNonUnitalStarAlgHom`, `.gnsStarAlgHom` in `Mathlib/Analysis/CStarAlgebra/GelfandNaimarkSegal.lean` | partial — supplies the GNS construction of (D7) for a positive linear functional, with **no** cyclic vector (its own TODO asks for one), no faithfulness, no isometry, no nondegeneracy, no separability | `find` for `*GelfandNaimark*`; full read of the file; `lean_leanfinder "faithful representation of a C*-algebra on a Hilbert space; injective star algebra homomorphism into bounded operators"` | `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |
| Mathlib | `NonUnitalStarAlgHom.norm_map`, `.isometry` in `Mathlib/Analysis/CStarAlgebra/Hom.lean` | same as (R5) — an injective non-unital \*-homomorphism of complex C\*-algebras is isometric, already a theorem | `lean_leansearch "C*-algebra embeds isometrically into bounded operators on a Hilbert space"`; read of the file | `5450b53e…` |
| Mathlib | `gelfandTransform_isometry`, `gelfandTransform_bijective`, `gelfandStarTransform` in `GelfandDuality.lean` | unrelated — the **commutative** Gelfand–Naimark theorem, a different statement under a stronger hypothesis; it shares only the name | file read | `5450b53e…` |
| Mathlib | could not find a **noncommutative** Gelfand–Naimark theorem in any form | — | `grep -rni "gelfand.naimark" Mathlib/ --include=*.lean -l` (one file, the GNS one); `lean_leansearch "C*-algebra embeds isometrically into bounded operators on a Hilbert space"`; GitHub PR search `repo:leanprover-community/mathlib4 Gelfand Naimark is:pr` (one PR, #33116, the GNS construction) | `5450b53e…` |
| Mathlib | could not find a notion of a **state** on a C\*-algebra, nor of a **faithful** state or representation | — the GNS input is `PositiveLinearMap`, with no normalisation and no faithfulness predicate | `grep -rn "faithful" Mathlib/Analysis/CStarAlgebra/ Mathlib/Analysis/InnerProductSpace/ -i`; `grep -rni "\bstate\b" Mathlib/Analysis/CStarAlgebra/*.lean`; `grep -rln "QuasiState\|StateSpace\|IsState\b" Mathlib/` | `5450b53e…` |
| Mathlib | `TopologicalSpace.SeparableSpace` (the `@[mk_iff]` class), `DenseRange.separableSpace`, `SeparableSpace.of_denseRange`, `IsSeparable.image`, `isSeparable_range`, `IsSeparable.span`, countable products, `UniformSpace.separableSpace_completion` | supplies (C3)'s topological reading and, composed, supplies the corpus's missing (R7): the GNS space is a completion of a type synonym of the algebra, so dense-range transfer followed by separability of completions covers it | `grep`/read of `Topology/Bases.lean`, `UniformSpace/{Cauchy,Completion}.lean`, `Topology/Algebra/Module/Basic.lean` | `5450b53e…` |
| Mathlib | `IsHilbertSum`, `IsHilbertSum.linearIsometryEquiv`, `HilbertBasis`, `exists_hilbertBasis` in `InnerProductSpace/l2Space.lean` | partial — "every Hilbert space is unitarily an ℓ²" in unindexed Zorn generality, i.e. (R12) without the cardinality bookkeeping | file read | `5450b53e…` |
| Mathlib | could not find separability of `lp` over a countable index, nor "separable iff countable Hilbert basis", nor "a separable Hilbert space is unitarily ℓ²(ℕ)" | — this is where (C4)/(R12) have no counterpart | `grep -rni "separab" Mathlib/Analysis/InnerProductSpace/ Mathlib/Analysis/Normed/Lp/`; `lean_leansearch "separable Hilbert space has a countable orthonormal basis"`; `lean_leansearch "lp space is separable when the index type is countable"`; `lean_loogle "TopologicalSpace.SeparableSpace (lp _ _)"` (empty) | `5450b53e…` |
| Mathlib | `WeakDual.isCompact_closedBall`, `WeakDual.isCompact_polar`, `WeakDual.exists_countable_separating`, `WeakDual.metrizable_of_isCompact`, sequential Banach–Alaoglu | supplies both halves of (R3)'s analytic input — Banach–Alaoglu and metrizability of weak\*-compact subsets for a separable normed space. Could not find the composed statement that the dual ball is weak\*-separable | `grep -rni "alaoglu"`; `grep -rni "metrizab" Mathlib/Analysis/Normed/Module/WeakDual.lean`; `lean_leansearch "separable normed space dual unit ball weak-star separable"` | `5450b53e…` |
| Mathlib | could not find "`B(H)` is norm-separable iff `H` is finite-dimensional" (R10) | — | `grep -rni "separab" Mathlib/Analysis/Normed/Operator/*.lean Mathlib/Analysis/Normed/Module/Dual.lean`; `grep -rn "SeparableSpace (.*→L\[" Mathlib/ --include=*.lean` | `5450b53e…` |
| Isabelle AFP | `Complex_Bounded_Operators` — complex normed/Banach/Hilbert spaces, `cblinfun`, unitaries, projectors, BLT, adjoints, Loewner order | unrelated — supplies the ambient `B(H)`, not the object. The abstract names no C\*-algebras, no Gelfand–Naimark, no GNS, no separability; only the abstract was read | WebSearch for the AFP entry and for `arXiv:2512.05878`; the AFP search page itself is client-side rendered and returned nothing — an instrument failure, not an absence | 2026-08-16 |
| Coq/Rocq | could not find any formalization of Gelfand–Naimark in either form, or of C\*-algebras as a structure | — | one WebSearch, `Coq mathcomp-analysis Gelfand-Naimark C*-algebra formalization`; a thin measurement | 2026-08-16 |
| Lean Zulip | could not find a thread on the noncommutative theorem or on faithful representations | — the archive indexes poorly, so this is a weak negative. One community artefact found: a blog post on the merged GNS work, with no future-work items | WebSearch restricted to `leanprover.zulipchat.com` | 2026-08-16 |

## Open questions

- Whether the equivalence "injective ⟹ isometric ⟹ closed range" (R5), which
  [BF26] uses parenthetically, survives in [BF26]'s ambient ZF. Both corpus
  proofs of it are ZFC and go through the continuous functional calculus; [BF26]
  cites no lemma at that point. This is the fourth of (R1)'s four dependencies
  and the only one whose *scope* rather than existence is in doubt.
- (X9) — whether the image can be structurally normalised.
- (X10) — whether the well-ordered-dense-subset generalisation has a matching
  conclusion about the Hilbert space.
- Whether the unitisation reduction (A2) preserves faithfulness of the state as
  well as of the representation: every source in the corpus asserts the
  reduction and none writes it out.
- Whether [SHI12] takes the inner product conjugate-linear in the first or the
  second argument (C5) — not determined.

## Sources

**Append-only.**

| Key | Work | Status | Cache | Version | Tier reached | Retrieved |
|---|---|---|---|---|---|---|
| BF26 | B. Blackadar, I. Farah, *Separable C\*-algebras Without the Countable Axiom of Choice*, arXiv:2602.15812 | retrieved | `references/arxiv-2602.15812/` | arXiv | a | 2026-08-16 |
| LAN98 | N. P. Landsman, *Lecture Notes on C\*-algebras, Hilbert C\*-modules and Quantum Mechanics*, arXiv math-ph/9807030 | retrieved | `references/arxiv-math-ph-9807030/` | arXiv | a | 2026-08-16 |
| SHI12 | V. Shirbisheh, *Lectures on C\*-algebras*, arXiv:1211.3404 | retrieved | `references/arxiv-1211.3404/` | arXiv | a | 2026-08-16 |
| VER25 | R. Verch, *Lecture Notes on Operator Algebras and Quantum Field Theory*, arXiv:2507.00900 | retrieved | `references/arxiv-2507.00900/` | arXiv | a | 2026-08-16 |
| MUR90 | G. J. Murphy, *C\*-algebras and Operator Theory*, Academic Press 1990 — reported to state the Gelfand–Naimark theorem together with the refinement that a separable algebra may be represented on a separable Hilbert space; no locator, the work was not opened | not retrieved — no legitimate free copy found; only a web search was attempted | — | — | d | 2026-08-16 |
| PED79 | G. K. Pedersen, *C\*-algebras and their Automorphism Groups*, Academic Press 1979 | not retrieved — same | — | — | d | 2026-08-16 |
| DIX77 | J. Dixmier, *C\*-algebras*, North-Holland 1977 | not retrieved — same | — | — | d | 2026-08-16 |
| BLA06 | B. Blackadar, *Operator Algebras: Theory of C\*-Algebras and von Neumann Algebras*, Springer 2006 — cited by BF26 for the definition of a C\*-algebra and for "norm 1 and φ(1)=1 ⟹ state" | not retrieved | — | — | c (through BF26) | 2026-08-16 |
| BLA-R | B. Blackadar, *Real Analysis* — cited by BF26 for "closed subsets of separable metric spaces are separable" and for the pure state space being G_δ | not retrieved | — | — | c (through BF26) | 2026-08-16 |
| BLA-H | B. Blackadar, *Hilbert spaces* (2023) — cited by BF26 for the ZF pathologies: a Hilbert space with no orthonormal basis, Russell and Cohen-finite sets | not retrieved | — | — | c (through BF26) | 2026-08-16 |
| TAK79 | M. Takesaki, *Theory of Operator Algebras I*, Springer 1979 | not retrieved — same | — | — | d | 2026-08-16 |

## Not investigated

- **The `[ext]` gap.** Lane 2 marked five external edges; lane 5 reached none of
  them, because all five point into books nobody obtained. They are: Blackadar,
  *Operator Algebras* — a linear functional on a unital C\*-algebra is a state
  iff it has norm 1 and value 1 at the unit (consumed by (R4)); Blackadar,
  *Real Analysis* — closed subsets of separable metric spaces are separable
  (consumed by (R11)) and the pure state space of a separable unital
  C\*-algebra is G_δ (consumed by the clause of (R3) that nothing on the route
  to (R1) uses); Blackadar, *Hilbert spaces* — the ZF pathologies underwriting
  (X3); and Krein–Milman as [LAN98] states it, without proof (consumed by (R9),
  not by (R1)). **(R4) is on the route to (R1), so the load-bearing chain does
  pass through a tier (c) edge** — this is what sets `worst-tier: c`.
- **BF26's own internal edges** were read as statements only, not chased: its
  separable Hahn–Banach / Banach–Alaoglu package, its separable Krein–Milman,
  its continuous functional calculus, and its positivity proposition.
- **(R7) is absent from the corpus and the argument in this note is the note's
  own**, not any source's. Anyone relying on (R1) is relying on a step no source
  in this corpus writes down.
- **(R5)'s scope in ZF** is unresolved — see `## Open questions`. Every claim
  that BF26's `SepRepThm` delivers a *concrete* C\*-algebra of operators, rather
  than merely an injective homomorphism, rests on it.
- **The five textbooks were never opened**, so the attributions that motivated
  this extraction — that Murphy, Pedersen, Dixmier, Blackadar and Takesaki each
  state the refinement alongside the Gelfand–Naimark theorem — are unverified.
  No row in this note carries a locator into any of them. Whether the refinement
  sits in the body of a numbered result or in a following remark is therefore
  still unknown, and that was one of the questions the extraction set out to
  answer.
- **Proof reading depth.** (R5) as LAN98 states it, (R10), and [LAN98]'s
  compact-operator proposition were skimmed rather than read through, and are
  recorded as sketched. [LAN98]'s `spc`/`spc5` and its ideal theory were not
  opened.
- **[VER25] was mis-scoped by the orchestrator** and only partly recovered: it
  contains no occurrence of "separable" or "Gelfand", but it is the corpus's
  only source for (D4) and (R6). Lanes 3 and 4 accepted the mis-scoping and did
  not open it, so its degeneracy and hypothesis content is unmeasured.
- **Not searched**: HOL Light, Metamath, Mizar, and Lean's `Mathlib/Archive`.
  The Isabelle AFP entry was measured from its abstract only, and the Coq/Rocq
  and Zulip negatives rest on one search each.
- **The unexamined base.** Everything above stands on the tier (c) rows in
  `## Sources` — the three Blackadar works reached only through BF26's
  citations — and on the two tier (c) `open` rows (X9) and (X10).
