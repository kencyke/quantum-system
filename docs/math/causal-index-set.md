---
object: Causal index set of a Haag–Kastler net
slug: causal-index-set
status: draft
worst-tier: b
mathlib-rev: 5450b53e5ddc75d46418fabb605edbf36bd0beb6
implemented-as: CausalIndexSet
revisions:
  - 2026-08-15 · 4ec09ec · initial extraction · sources: HM06, GLRV99, NAA13, BGL93, BFV01, KOE03, dB74, DL84
  - 2026-08-15 · <working tree, uncommitted> · prior-art refresh after CausalIndexSet mixin addition · no new claims
---

<!--
No document-level macro preamble: measured through
@vscode/markdown-it-katex (the plugin VS Code's own Markdown preview uses),
no macro definition form -- \newcommand, \gdef, \global\def -- survives
from one math span to the next, so a preamble here would leave every quote
using it broken (see check_render.py / render_check.js). Instead, every
verbatim-quote math span that needs a source's own macro carries a local,
self-contained \gdef of exactly that macro, e.g.
`$\gdef\lok#1{{\mathcal #1}}\lok{B}$` -- defined and used inside the same
$...$ pair, so it renders correctly without any state surviving to the next
span. The \gdef prefix is presentation, not content: strip it before
comparing a quote's tex against source.flat.txt for the quote check, and
audit it against the source's own definition below.

Source macro catalogue (name[arity] = body, source, file:line):
  \2[1] = {{\mathcal #1}}   (provenance: see prior revision / sources.md)
  \7[1] = {{\mathbb #1}}   (provenance: see prior revision / sources.md)
  \A = {{\cal A}}   BGL93,  references/arxiv-funct-an-9302008/raw/main.tex:58,64,72,77,81
  \C = {{\cal C}}   BGL93,  references/arxiv-funct-an-9302008/raw/main.tex:58,64,72,77,81
  \K = {{\cal K}}   BGL93,  references/arxiv-funct-an-9302008/raw/main.tex:58,64,72,77,81
  \O = {{\cal O}}   BGL93,  references/arxiv-funct-an-9302008/raw/main.tex:58,64,72,77,81
  \Om = {\Omega}   (provenance: see prior revision / sources.md)
  \R = {{\cal R}}   BGL93,  references/arxiv-funct-an-9302008/raw/main.tex:58,64,72,77,81
  \Seins = {\mathsf{S}^1}   KOE03,  references/arxiv-math-ph-0308031/raw/mathphkoediss.tex:144,135
  \al[1] = {{\mathfrak #1}}   (provenance: see prior revision / sources.md)
  \alg[1] = {\mathfrak{#1}}   (provenance: see prior revision / sources.md)
  \cA = {{\cal A}}   GLRV99, references/arxiv-math-ph-9906019/raw/main.tex:69,70,76,79,80,83,85,88,92,93
  \cB = {{\cal B}}   GLRV99, references/arxiv-math-ph-9906019/raw/main.tex:69,70,76,79,80,83,85,88,92,93
  \cH = {{\cal H}}   GLRV99, references/arxiv-math-ph-9906019/raw/main.tex:69,70,76,79,80,83,85,88,92,93
  \cK = {{\cal K}}   GLRV99, references/arxiv-math-ph-9906019/raw/main.tex:69,70,76,79,80,83,85,88,92,93
  \cL = {{\cal L}}   GLRV99, references/arxiv-math-ph-9906019/raw/main.tex:69,70,76,79,80,83,85,88,92,93
  \cO = {{\cal O}}   GLRV99, references/arxiv-math-ph-9906019/raw/main.tex:69,70,76,79,80,83,85,88,92,93
  \cP = {{\cal P}}   GLRV99, references/arxiv-math-ph-9906019/raw/main.tex:69,70,76,79,80,83,85,88,92,93
  \cS = {{\cal S}}   GLRV99, references/arxiv-math-ph-9906019/raw/main.tex:69,70,76,79,80,83,85,88,92,93
  \cW = {{\cal W}}   GLRV99, references/arxiv-math-ph-9906019/raw/main.tex:69,70,76,79,80,83,85,88,92,93
  \cX = {{\cal X}}   GLRV99, references/arxiv-math-ph-9906019/raw/main.tex:69,70,76,79,80,83,85,88,92,93
  \calA = {{\mathcal A}}   BFV01,  references/arxiv-math-ph-0112041/raw/main.tex:7,26,31,89,82 (FIRST document body)
  \calK = {{\mathcal K}}   BFV01,  references/arxiv-math-ph-0112041/raw/main.tex:7,26,31,89,82 (FIRST document body)
  \frakM = {{\mathfrak{Man}}}   BFV01,  references/arxiv-math-ph-0112041/raw/main.tex:7,26,31,89,82 (FIRST document body)
  \gb = {\boldsymbol{g}}   BFV01,  references/arxiv-math-ph-0112041/raw/main.tex:7,26,31,89,82 (FIRST document body)
  \lok[1] = {{\mathcal #1}}   KOE03,  references/arxiv-math-ph-0308031/raw/mathphkoediss.tex:144,135
  \mc[1] = {\mathcal{#1}}   NAA13,  references/arxiv-1311.2717/raw/qlattice.tex:73
  \norm[1] = {\| #1\|}   (provenance: see prior revision / sources.md)
  \obj = {\mbox{\rm Obj}}   BFV01,  references/arxiv-math-ph-0112041/raw/main.tex:7,26,31,89,82 (FIRST document body)
  \ol[1] = {{\overline #1}}   (provenance: see prior revision / sources.md)
  \p = {\pi}   GLRV99, main.tex:127
  \wt[1] = {{\tilde #1}}   (provenance: see prior revision / sources.md)
-->

# Causal index set of a Haag–Kastler net

## What this object is for

A Haag–Kastler net assigns algebras to spacetime regions, and every axiom that
makes the assignment physics rather than bookkeeping — locality, duality, the
DHR selection criterion, the split property — is a statement about *which
regions stand in which relation to which*. The index set is where that
information lives: a partially ordered set of regions carried with a relation of
causal disjointness, and, for the independence properties, one or more
strengthenings of that relation. Its generality matters because the corpus's
main structural results split precisely along its axes — whether the order is
directed decides whether a quasi-local algebra exists at all, and which
strengthening of causal disjointness is in force decides whether an
independence theorem applies to a given pair of regions.

## Definition

### Variants as the sources write them

| (D#) | Source | Level | Primitive | Membership conditions | Directed | ∅ ∈ 𝒦 | Tier |
|---|---|---|---|---|---|---|---|
| (D1) | [GLRV99] | abstract | relation ⊥ on a poset | a), b), c) | not required | not excluded | a |
| (D2) | [GLRV99] | concrete | ⊥ on subsets of M | regular diamond; `𝒪^⊥ ≠ ∅` | not in general; never if the Cauchy surface is compact | no | a |
| (D3) | [GLRV99] | pointwise | ⊥ on points of M | — (neighbourhood-buffer definition) | — | — | a |
| (D4) | [GLRV99] | operation | `Q^⊥ := M ∖ J̄(Q)` | — | — | — | a |
| (D5) | [GLRV99] | derived relations | ⊥̃, ⊥̂ from ⊥ | — | — | — | a |
| (D6) | [HM06] | concrete | "spacelike separated", primitive | open double cone in Minkowski | yes (Minkowski) | no | a |
| (D7) | [HM06] | strengthened relation | translation buffer | — | — | — | a |
| (D8) | [HM06] | strengthened relation | closures + enlargement | — | — | — | a |
| (D9) | [HM06] | separation for split | `Ō₁ ⊆ O₂` | — | — | — | a |
| (D10) | [NAA13] | concrete | "spacelike separated", primitive | double cone; records `𝒪 = 𝒪″` | yes | no | a |
| (D11) | [NAA13] | concrete, discrete | disjointness | finite subset of a countable Γ | yes | **yes** | a |
| (D12) | [BGL93] | concrete ×2 | causal complement | `𝒦̃`: open contractible precompact, closed under `′`; `𝒦`: double cones | `𝒦̃` no, `𝒦` yes | no | a |
| (D13) | [BGL93] | operation on S¹ | `I′ =` interior of the complement | — | — | — | a |
| (D14) | [KOE03] | concrete | operation `I ↦ I′` | connected, open, non-dense; `I′ ≠ ∅` | **no** | no | a |
| (D15) | [KOE03] | separation for split | `Ī₁ ⊂ I₂` | — | — | — | a |
| (D16) | [BFV01] | concrete | closure-based ⊥ | relatively compact, causally convex | not addressed | yes, read literally | a/b |
| (D17) | [BFV01] | operation | `O^⊥ =` largest causally separated open set | — | — | — | a |
| (D18) | [dB74] | separation ×3 | translation buffer / closure / positive distance | open, `𝒪′ ≠ ∅` | — | no | b |
| (D19) | [GLRV99] | concrete, net-dependent | ⊥ on sieves | causally closed, `𝒮^⊥ ≠ ∅`, ⊥̃-duality for `𝒮` or `𝒮^⊥` | — | no | a |
| (D20) | [GLRV99] | concrete, mixed | ⊥ across two families | regular diamonds ∪ wedges | — | no | a |

**(D1) [GLRV99] §3.1, `source.txt` 1214–1226** — tier (a) — the abstract form

> The causal structure enters in the form of the relation $\perp$ of causal disjointness, defined in Ch.\ 2, and here to be considered as a relation on the ordered set $\cal{K}$, satisfying \begin{description} \item{$a)$} $\gdef\cO{{\cal O}}\cO_1\perp\cO_2\Rightarrow\cO_2\perp\cO_1$. \item{$b)$} $\gdef\cO{{\cal O}}\cO_1\subset\cO_2$ and $\gdef\cO{{\cal O}}\cO_2\perp\cO_3 \Rightarrow\cO_1\perp\cO_3$. \item{$c)$} Given $\gdef\cO{{\cal O}}\gdef\cK{{\cal K}}\cO_1\in\cK$, there exists an $\gdef\cO{{\cal O}}\gdef\cK{{\cal K}}\cO_2\in\cK$ such that $\gdef\cO{{\cal O}}\cO_1\perp\cO_2$. \end{description} We write $\gdef\cO{{\cal O}}\gdef\cK{{\cal K}}\cO^\perp:=\{\cO_1\in\cK:\cO_1\perp\cO\}$.

Restated at the head of the Appendix to Ch. 3 with the gloss that b) says
`$\cal{O}^\perp$ is a sieve of $\cal{K}$`. Here `𝒪^⊥` is a **subset of 𝒦**, not
a region — the opposite convention from (D4); see (C4). The abstraction is
deliberate:

> Our discussion of superselection theory in this and in subsequent sections is in terms of a partially ordered set $\cal{K}$ together with a binary relation $\perp$. The necessary properties will be introduced as needed and there will be no specific reference to spacetime.

**The list is therefore a floor, not a ceiling, and the source says so.** A
fourth condition appears later in the same chapter and is recorded as (D5′).

**(D2) [GLRV99] §2.1 and §3.1** — tier (a) — regular diamonds

> A set of the form $\gdef\cO{{\cal O}}\cO = {\rm int}\,D(G)$ is a regular diamond provided $\gdef\cO{{\cal O}}\cO^\perp$ is non-void and

with (i) `Ḡ` compact and contractible to a point in `G`, `G` open in an acausal
Cauchy surface `C`; (ii) `∂G` a locally flat, two-sided topological
submanifold of `C`, smooth near points of each connected component. Then
`We let $\gdef\cK{{\cal K}}\cK$ denote the set of regular diamonds in $M$, ordered under inclusion.`
Non-void causal complement is **in the definition**, which is how axiom c) is
secured. GLRV99 declines double cones and says why:

> For these reasons, we have chosen to use the collection $\gdef\cK{{\cal K}}\cK$ of regular diamonds rather than the collection of double cones whose causal complement has non-empty interior as an index set in a globally hyperbolic spacetime.

`differs from (D6)/(D10) by:` a Cauchy-surface base with compactness,
contractibility and a two-sidedness condition, plus `𝒪^⊥ ≠ ∅`. Note the source
uses two different provisos in one sentence — `𝒪^⊥` **non-void** for diamonds,
**non-empty interior** for the declined double cones — and does not reconcile
them.

**(D3) [GLRV99] §2.1** — tier (a) — causal disjointness of points, with a buffer

> One says that two points $p$ and $q$ in $M$ are {\it causally disjoint}, in symbols $p \perp q$, if there are open neighbourhoods $U$ of $p$ and $V$ of $q$ such that there is no causal curve connecting $U$ and $V$ (i.e.\ $U \cap J(V) = \emptyset = V \cap J(U)$). Correspondingly one calls two subsets $P$ and $Q$ of $M$ causally disjoint if $p \perp q$ holds for all pairs $p \in P$ and $q \in Q$; this will be abbreviated as $P \perp Q$.

The **open-neighbourhood buffer** makes this strictly stronger than "no causal
curve joins `p` and `q`", and (R4)'s proof consumes exactly that strength. As
defined, `p ⊥ p` is impossible, so `P ⊥ P` fails for every non-empty `P` and
holds vacuously for `P = ∅`.

`differs from (D17) by:` GLRV99 buffers with neighbourhoods and quantifies over
points of `P`, `Q`; BFV01 uses no buffer and quantifies over points of the
**closures**. **The corpus contains two inequivalent ⊥'s and no source compares
them.**

**(D4) [GLRV99] §2.1** — tier (a) — the causal complement as an operation on subsets

> It is moreover worth mentioning that for any two subsets $P$ and $Q$ of a globally hyperbolic spacetime $(M,g)$ we have $P \perp Q$ if and only if $P \subset Q^{\perp}$, where the causal complement $Q^{\perp}$ of $Q \subset M$ is defined by $Q^{\perp} := M \backslash \overline{J(Q)}$

Complement of the **closure** of the causal hull, hence automatically open.

**(D5) [GLRV99] Appendix to Ch. 3** — tier (a) — the two derived relations

> There are two derived binary relations $\tilde\perp$ and $\hat\perp$ defined by supplementing $\gdef\cO{{\cal O}}\cO_1\perp\cO_2$ by requiring that there exists an $\gdef\cO{{\cal O}}\cO_3\in\cal{K}$ such that $$\gdef\cO{{\cal O}}\cO_1\perp\cO_3,\,\,\cO_2\perp\cO_3$$ or such that $$\gdef\cO{{\cal O}}\cO_1,\,\,\cO_2\subset\cO_3,$$ respectively. These relations automatically satisfy a) and b) but c) remains to be checked and will not prove to be a problem in our applications to curved spacetime. The operation of passing from $\perp$ to $\tilde\perp$ or $\hat\perp$ is idempotent and if $\cal{K}$ is directed, all three relations coincide.

So `O₁ ⊥̃ O₂` demands a common ⊥-partner and `O₁ ⊥̂ O₂` a common upper bound.
Both are **purely order/⊥-theoretic**: neither mentions closures or distance.
The whole ⊥/⊥̃/⊥̂ distinction is the price of dropping directedness — see (R9).

**(D5′) [GLRV99] Ch. 3, before Theorem 3.13, `source.txt` 1878–1882** — tier (a)
— the corpus's only collar-shaped condition on 𝒦 itself

> In fact, the following result is valid for a directed set $\cal{K}$ with a binary relation $\perp$ such that given $\cal{O}\in\cal{K}$, there exists $\gdef\cO{{\cal O}}\cO_1,\cO_2\in\cal{K}$ with $\gdef\cO{{\cal O}}\cO,\cO_1\subset\cO_2$ and $\gdef\cO{{\cal O}}\cO\perp\cO_1$. This condition is related to our use of the Borchers Property.

For every `O` there are `O₁, O₂` with `O ⊆ O₂`, `O₁ ⊆ O₂` and `O ⊥ O₁` — in the
vocabulary of (D5), **every `O` has an `O₁` with `O ⊥̂ O₁`**, i.e. axiom c)
strengthened from ⊥ to ⊥̂. Stated as a hypothesis of one theorem alongside
directedness, not as a standing axiom.

`differs from (D5) by:` (D5) is a relation *between two given regions*; this is
a **∀∃ statement about 𝒦**. Every other collar in the corpus is of the former
kind or is topological ((D8), (D9)). **No source compares the two shapes.**

**(D6) [HM06] §2.1** — tier (a) — open double cones in Minkowski

> An open \emph{double cone} in Minkowski spacetime is the intersection of the causal future of a point $x$ with the causal past of a point $y$ to the future of $x$. Let $\gdef\2#1{{\mathcal #1}}\2K$ be the set of open double cones in Minkowski spacetime

No poset axioms are stated; the order is inclusion, used silently. **HM06 never
defines "spacelike separated"** — it is an undefined primitive from the
Microcausality assumption onward, and the causal complement is written `O'` with
no formula. See (C1).

`differs from (D2) by:` no Cauchy-surface base, no regularity, and **no
requirement that the causal complement be non-void**.

**(D7) [HM06] §3.3** — tier (a) — strictly spacelike separated

> Two double cones $O_1,O_2$ are said to be \emph{strictly spacelike separated} just in case there is a neighborhood $N$ of zero such that $O_1+x$ is spacelike separated from $O_2$ for all $x\in N$.

A translation-buffer condition; **requires a translation group**.

**(D8) [HM06] §3.3** — tier (a) — strongly spacelike separated

> Two double cones $O_1$ and $O_2$ are said to be \emph{strongly spacelike separated} just in case there are double cones $\gdef\wt#1{{\tilde #1}}\wt O_i$ such that $\gdef\ol#1{{\overline #1}}\gdef\wt#1{{\tilde #1}}\ol O_i\subseteq \wt O_i$, and $\gdef\wt#1{{\tilde #1}}\wt O_1,\wt O_2$ are spacelike.

with the ordering claim

> In terms of logical strength, the following concept lies between spacelike separation and strict spacelike separation; furthermore, this concept makes sense for spacetimes without a translation group.

`differs from (D5) by:` the shapes are not the same. (D5)'s clauses ask for
**one** further region related to both by ⊥ or by ≤; (D8) asks for **two**
enlargements, one per region, each containing the region's **closure**. (D8)
uses the topological closure, **which is not available in (D1)'s data**, so
"strongly spacelike separated" is not expressible in GLRV99's abstract language.
`sources claim equivalence:` no — no source in the corpus mentions the other's
relation.

**(D9) [HM06] §2.4** — tier (a) — the separation carrying the split property

> the \emph{funnel property} if for any double cones $O_1,O_2$ with $\gdef\ol#1{{\overline #1}}\ol O_1$ contained in $O_2$, the pair $\gdef\al#1{{\mathfrak #1}}(\al R(O_1),\al R(O_2))$ is a split inclusion.

The relation is `closure(O₁) ⊆ O₂`. **HM06 gives it no name and no symbol.**
Purely topological: no causal structure, no metric, no positive distance.

**(D10) [NAA13] §1.2** — tier (a) — double cones, recorded as causally complete

> As the basic regions we consider \emph{double cones}\index{double cone} $\gdef\mc#1{\mathcal{#1}}\mc{O}$, defined as the intersection of (the interior of) a forward and backward light-cone. Note that a double cone is causally complete: $\gdef\mc#1{\mathcal{#1}}\mc{O} = \mc{O}''$, where a prime $'$ denotes taking the causal complement.

`differs from (D6) by:` the same family, presented as an intersection of cones
rather than through two points, **plus the causal-completeness observation HM06
never makes**. NAA13 is the corpus's only source stating `𝒪 = 𝒪″`, and states it
as an observation, not as a membership condition — contrast (D19).

**(D11) [NAA13] §2.4** — tier (a) — the lattice index set, with `∅` a member

> Let $\Gamma$ be as above. We will write $\gdef\mc#1{\mathcal{#1}}\mc{P}(\Gamma)$ for the set of all subsets of $\Gamma$. Similarly, $\gdef\mc#1{\mathcal{#1}}\mc{P}_f(\Gamma)$ is the subset of all \emph{finite} subsets of $\Gamma$.

> For convenience we will set $\gdef\alg#1{\mathfrak{#1}}\alg{A}(\emptyset) = \mathbb{C} I$, since multiples of the identity are contained in $\gdef\alg#1{\mathfrak{#1}}\alg{A}(\Lambda)$ for all $\gdef\mc#1{\mathcal{#1}}\Lambda \in \mc{P}_f(\Gamma)$.

Finite subsets of a countable Γ, ordered by inclusion, ⊥ = plain disjointness.
**Directed**, with a **least element ∅**, a distributive lattice, and its
complement operation `Λ^c` leaves 𝒦. GLRV99 licenses exactly this replacement of
causal disjointness by "its Euclidean counterpart, disjointness". Because
`∅ ∈ 𝒦`, **⊥ is reflexive at ∅** and axiom c) holds for free — see (C11), (H1).

**(D12) [BGL93] §1, Prop. 1.3** — tier (a) — two index sets in one paper

> In the following we shall consider the family $\gdef\K{{\cal K}}\tilde\K$ of the subregions of $\tilde M$ which are images of double cones in $M$ under conformal transformations in $\gdef\C{{\cal C}}\tilde\C$.

> All elements of $\gdef\K{{\cal K}}\tilde\K$ are open contractible precompact submanifolds of $\tilde M$. They are a fundamental set of neighborhoods for $\tilde M$.

> The space-like complement $\gdef\O{{\cal O}}\O'$ of a region $\gdef\O{{\cal O}}\gdef\K{{\cal K}}\O\in\tilde\K$ belong to $\gdef\K{{\cal K}}\tilde\K$.

> The family $\gdef\K{{\cal K}}\tilde\K$ is not a net, in fact the union of a region and of its causal complement is not contained in any region of $\gdef\K{{\cal K}}\tilde\K$.

and, for the same paper's other index set,

> Since the family $\gdef\K{{\cal K}}\K$ is a direct set, the map $\gdef\O{{\cal O}}\gdef\A{{\cal A}}\O\to\A(\O)$ is indeed a net and the quasilocal $C^*$-algebra $\gdef\A{{\cal A}}\A_0$ is defined as the direct limit of the local algebras.

**`𝒦̃` is the corpus's only index set literally closed under the causal
complement**, so on it `𝒪 ↦ 𝒪′` is an *operation*; on every other index set it
is only a relation. One paper, two index sets, opposite on directedness and
opposite on closure under `′`.

**(D13) [BGL93] §2** — tier (a): `where $I'$ is the interior of the complement of $I$.`
`differs from (D14) by:` presentation only — interior-of-complement versus
complement-of-closure. The two sources write different formulas for the same set
and neither remarks on it.

**(D14) [KOE03] §2** — tier (a) — proper intervals of the circle

> The localisation regions are open, non-dense intervals contained in the circle, called the {\em proper intervals}. A connected, open subset $I$ of $\gdef\Seins{\mathsf{S}^1}\Seins$ is a proper interval, denoted by $\gdef\Seins{\mathsf{S}^1}I\Subset\Seins$, if its {\em causal complement} $\gdef\Seins{\mathsf{S}^1}I':= \Seins\setminus\overline{I}$ is not the empty set.

Membership requires connected, open, non-dense, and `I′ ≠ ∅` — as in (D2) and
unlike (D6)/(D10). Locality is stated as `{\em Locality\label{ax:loc}:} For $I_1\subset I_2'$,`
so **the primitive is the operation `I ↦ I′`** and ⊥ is derived, the reverse of
(D1). Interchangeable only because 𝒦 is closed under `′` here. The index set is
not directed and the source draws the terminological consequence:

> The set of proper intervals in $\gdef\Seins{\mathsf{S}^1}\Seins$ is not directed with respect to the partial order defined by inclusion and thus is not a net in the proper sense of the word.

**(D15) [KOE03] §1.3** — tier (a) — the chiral split separation

> a chiral net $\gdef\lok#1{{\mathcal #1}}\lok{B}$ has the split property, if for any pair $I_{1,2}$ of proper intervals satisfying $\overline{I_1}\subset I_2$ there is a type $I$ factor $\gdef\lok#1{{\mathcal #1}}\lok{M}$ interpolating between $\gdef\lok#1{{\mathcal #1}}\lok{B}(I_1)$ and $\gdef\lok#1{{\mathcal #1}}\lok{B}(I_2)$

`differs from (D9) by:` **nothing mathematical** — two traditions, one relation,
and neither names it or gives it a symbol. KOE03 also takes the one step in the
corpus connecting the topological and order-theoretic collar families:

> we conclude that there is $\gdef\Seins{\mathsf{S}^1}I_3\Subset\Seins$ satisfying $I_1\cup I_2' \subset I_3$

i.e. `Ī₁ ⊂ I₂` yields a common upper bound for `I₁` and `I₂′`, which with
`I₁ ∩ I₂′ = ∅` says exactly `I₁ ⊥̂ I₂′`.

**(D16) [BFV01] §2.4, first document body** — tier (a) literal / (b) as intended

> We denote by $\gdef\calK{{\mathcal K}}\gdef\gb{\boldsymbol{g}}\calK(M,\gb)$ the set of all subsets in $M$ which are relatively compact and contain with each pair of points $x$ and $y$ also all $\gdef\gb{\boldsymbol{g}}\gb$-causal curves in $M$ connecting $x$ and $y$ (cf.\ condition $(ii)$ in the definition of $\gdef\frakM{{\mathfrak{Man}}}\frakM$).

Two conditions only: **relatively compact** and **causally convex**. Read
literally, `∅`, singletons and spacelike point-pairs are members. The next
sentence silently demands far more — each `(O, ḡ_O)` must lie in `obj(𝔐)`, whose
manifolds are `Hausdorff, paracompact, and connected` — so the intended index set
is open, connected, non-empty and globally hyperbolic. **The two readings give
different index sets**, and the inference to the second is tier (b).

**(D17) [BFV01] §2.1, first document body** — tier (a) — closure-based ⊥

> Two subsets $O_1$ and $O_2$ in $M$ are called causally separated if they cannot be connected by a causal curve, i.e.\ if for all $x \in \overline{O_1}$, $J^{\pm}(x)$ has empty intersection with $\overline{O_2}$. By $O^{\perp}$ we denote the causal complement of $O$, i.e.\ the largest open set in $M$ which is causally separated from $O$.

**BFV01's plain "causally separated" already excludes touching regions**, unlike
(D3) and (D14). `O^⊥` is given by a maximality characterisation with **no
set-theoretic formula**, unlike (D4) and (D14).

**(D18) [dB74] Ch. II–III** — tier (b), `mineru-unchecked` except where noted —
three separation shapes in one paper

- *translation buffer*, Thm 2.2:
  > Let $\hat{O}_{1}$ and $\hat{O}_{2}$ be two spacelike separated regions such that $O_{1} + N \subset \hat{O}_{1}$ and $O_{2} + N \subset \hat{O}_{2}$ .
- *closure*, Ch. II item a), **p. 292** (tier (b),
  `mineru-cross-checked-against-PDF-text-layer`):
  > If the closures of the regions $O_{1}$ and $O_{2}$ are not spacelike separated, then, at least for the free field, it is easy to show that one runs into contradictions if one postulates the existence of normal product states for such regions.
  **The corpus's only statement that the closure relation is *necessary*.**
- *positive distance*, Ch. III:
  > Both regions shall have smooth boundaries and the distance between $O_{1}$ and $O_{2}$ is supposed to be greater than zero.

dB74's index set carries openness and `𝒪′ ≠ ∅`, stated as the scope of its
Reeh–Schlieder assumption rather than as a definition.

`differs from (D7) by:` HM06 translates one region and asks it stay spacelike to
the other; dB74 translates a region and asks it stay **inside a larger region**.
Same buffer idea, two different relations.

**(D19) [GLRV99] Appendix Ch. 3 and §4.2** — tier (a) — an index set that depends on the net

> We choose $\gdef\cL{{\cal L}}\cL$ to be the set of non-empty causally closed subsets $\gdef\cS{{\cal S}}\cS$ of $M$ with non-empty causal complements such that for the given net $\gdef\cA{{\cal A}}\cA$ $\tilde\perp$--duality holds either for $\gdef\cS{{\cal S}}\cS$ or for $\gdef\cS{{\cal S}}\cS^\perp$.

> This choice has the disadvantage of depending on the theory under consideration but it allows a smooth treatment of endomorphisms.

`differs from every other (D#) by:` **the index set is a function of the net.**
Causal closedness `𝒮 = 𝒮^⊥⊥` is here a *membership condition*, where (D10)
records it as an observation.

**(D20) [GLRV99] Ch. 5** — tier (a) — diamonds together with wedges

> Now we consider a net $\gdef\cO{{\cal O}}\gdef\cA{{\cal A}}\cO \mapsto\cA(\cO)$ of von~Neumann algebras indexed by elements $\gdef\cO{{\cal O}}\gdef\cK{{\cal K}}\gdef\cW{{\cal W}}\cO \in \cK \cup \cW$ where $\gdef\cK{{\cal K}}\cK$ is the set of regular diamonds and $\gdef\cW{{\cal W}}\cW$ is a set of wedges with the properties discussed in the previous section

The corpus's only index set containing **unbounded** elements as first-class
members, and the only one that is not a single geometric family. A form that
builds boundedness into 𝒦 cannot state GLRV99's Ch. 5 hypotheses.

### Adopted general form

Fix a partially ordered set `𝒦`, whose elements are called *regions*, and a
binary relation `⊥` on `𝒦`, read *causally disjoint*. The pair `(𝒦, ⊥)` is a
**causal index set** when

1. `O₁ ⊥ O₂` implies `O₂ ⊥ O₁`;
2. `O₁ ≤ O₂` and `O₂ ⊥ O₃` imply `O₁ ⊥ O₃` — equivalently, `O^⊥ := {O₁ ∈ 𝒦 : O₁ ⊥ O}` is downward closed in `𝒦` for every `O`;
3. for every `O₁ ∈ 𝒦` there exists `O₂ ∈ 𝒦` with `O₁ ⊥ O₂`.

There are no further hypotheses: the order is **not** assumed directed, `⊥` is
**not** assumed irreflexive, `𝒦` carries **no topology** and no
causal-complement operation into itself, no element is assumed causally complete,
no region is assumed open, bounded or non-empty, and `𝒦` may be empty. Standing
hypotheses of the sources that this form deliberately does not carry are (A1)
directedness, (A7) openness and path-connectedness, (A10) causal completeness and
(A11) global hyperbolicity of an ambient spacetime, each of which is a row in
`## Hypotheses` rather than part of the definition.

$$
\text{(a) } O_1 \perp O_2 \Rightarrow O_2 \perp O_1,\qquad
\text{(b) } O_1 \le O_2,\ O_2 \perp O_3 \Rightarrow O_1 \perp O_3,\qquad
\text{(c) } \forall O_1\, \exists O_2,\ O_1 \perp O_2 .
$$

This is (D1), verbatim [GLRV99] §3.1 up to notation. It is the corpus's only
abstract axiomatisation, it is stated twice and with a declared motive, and every
concrete index set in the corpus is an instance of it — double cones, regular
diamonds, proper intervals of `S¹`, `𝒦̃`, `𝓛`, `𝒦 ∪ 𝒲`, wedges and `𝒫_f(Γ)` were
each checked against a), b), c). (X18) rejects the alternative of taking the
causal complement as an **operation into 𝒦**: the separating object is a double
cone in Minkowski, whose ⊥-partners have no maximum, while `𝒦̃` and the proper
intervals do support the operation; the sieve-valued operation
`O ↦ O^⊥ ⊆ 𝒦` is `equivalent` and is GLRV99's own notation. (X19) rejects adding
causal completeness as an axiom: a three-element antichain satisfies a), b), c)
with `B^⊥⊥ ⊋ ↓B`. (X25)–(X27) reject the quantifier and heredity variants.

**Three costs of this choice, recorded rather than left to be rediscovered.**

- **(H1)** Axiom c) does not deliver what the corpus uses it for. Adjoin a least
  element `0` to *any* poset and set `⊥ := {(0,O),(O,0)}`; a), b), c) all hold.
  So every poset underlies a causal index set and the form has **no
  order-theoretic content**. In particular a form omitting irreflexivity may not
  be credited with (X3)'s consequence that comparable regions are never ⊥, nor
  with (X6)'s that `𝒦` is not a chain — both need irreflexivity, which is
  independent of a), b), c). GLRV99's own text warns that the list is a floor.
- **(H2)** [BFV01]'s primary object is a **category** of spacetimes with
  isometric embeddings, whose causality condition quantifies over pairs of
  morphisms into a common spacetime. This form covers BFV01's *derived* net over
  `𝒦(M,ḡ)` and not BFV01's theory.
- **(T) is not expressible.** The hypothesis under which the two candidate
  separation relations for the split property are ordered — see below — is
  topological, and a bare poset with ⊥ cannot state it. This is the same
  obstruction as (D8)'s.

**The separation relation for the split property is not adopted as a single
relation.** The corpus carries at least six phrasings — (D5)'s ⊥̃ and ⊥̂, (D5′),
(D7), (D8), (D9)/(D15), and (D18)'s three — and states exactly one implication
between any two of them ([HM06]'s `fact`, (R25), asserted there and proved in
this note). What can be said is:

**(T) — the causal complement abuts the region.** `Ō ∩ cl(O^⊥) ≠ ∅` for every
`O ∈ 𝒦`; equivalently `dist(Ō, O^⊥) = 0`; equivalently, there is no buffer
between a region and its causal complement. *No source states (T); it is this
note's, extracted from the case analysis below.*

**Ordering theorem** (this note's, not any source's). Let `𝒦` be a base of
**non-empty open** subsets of a topological space `M`, let ⊥ be induced by an
operation `O ↦ O^⊥` into the open sets by `O₃ ⊥ O₁ ⟺ O₃ ⊆ O₁^⊥`, and let
`O ∩ O^⊥ = ∅`. If **(T)** holds then `Ō₁ ⊆ O₂` implies the collar clause
`∃O₃ ∈ 𝒦 : O₃ ≤ O₂, O₃ ⊥ O₁, O₃ ⊄ O₁`.

*Proof.* By (T) pick `x ∈ Ō₁ ∩ cl(O₁^⊥)`. Since `Ō₁ ⊆ O₂` with `O₂` open, `O₂`
is a neighbourhood of `x`, so meets `O₁^⊥`; hence `O₂ ∩ O₁^⊥` is non-empty open
and, `𝒦` being a base, contains some `O₃ ∈ 𝒦`. Then `O₃ ≤ O₂`; `O₃ ⊆ O₁^⊥`
gives `O₃ ⊥ O₁`; and `O₃ ⊄ O₁` because `O₃ ⊆ O₁^⊥`, `O₁ ∩ O₁^⊥ = ∅` and
`O₃ ≠ ∅`. ∎

Compactness of `Ō₁` is not used; openness of `O₂` is. The implication is
**strict**: (X15) direction 2 gives internally tangent double cones satisfying
the collar clause and failing `Ō₁ ⊆ O₂`. (T) holds for double cones (the
intersection is the waist sphere), for regular diamonds (secured by GLRV99's
two-sidedness clause), for the proper intervals of `S¹` (the two endpoints) and
for `𝒦̃` (tier (b), by transporting the Minkowski computation along a conformal
map); it **fails** for `𝒫_f(Γ)`, where discreteness puts a buffer of width 1
between a set and its complement, and for any index set containing a region with
empty causal complement. So the two forms are `ordered-under-(T)`, neither
`incomparable` nor `ordered`.

## Notation and conventions

| (C#) | Axis | This note | Per source | Translation |
|---|---|---|---|---|
| (C1) | is "spacelike separated" defined? | ⊥ is primitive, axiomatised | [GLRV99] (D3) and [BFV01] (D17) define it; **[HM06] and [NAA13] leave it undefined** and write the complement `O'` with no formula. tier (a)/(b) | none available: the two definitions that exist are inequivalent |
| (C2) | directedness of 𝒦 | not assumed | [HM06] and [GLRV99] both remark it may fail and say what is lost; [BGL93] and [KOE03] make it a terminological matter. tier (a) | (R1), (R19), (R16), (R40) |
| (C3) | causal vs plain disjointness | ⊥ abstract | [GLRV99] licenses replacing causal disjointness by "its Euclidean counterpart, disjointness" on the circle; [NAA13] (D11) does it on a lattice. tier (a) | on a discrete Γ the two coincide by fiat |
| (C4) | what `O^⊥` denotes | a subset of 𝒦 | [GLRV99] uses `𝒪^⊥` for **both** the sieve `{𝒪₁ ∈ 𝒦 : 𝒪₁ ⊥ 𝒪}` (D1) and the point set `M ∖ J̄(𝒪)` (D4), in one paper; [BFV01], [KOE03], [BGL93] use the point-set reading only. tier (a) | (R13): `μ`, `ν` are mutually inverse on causally closed sets and sieves, which is the precise sense in which the two readings agree |
| (C5) | openness of regions | not assumed | open in [GLRV99], [BGL93], [KOE03], [dB74]; unstated but automatic in [HM06], [NAA13]; **absent from [BFV01]'s literal definition** and forced by its next sentence. tier (a)/(b) | — |
| (C6) | irreflexivity of ⊥ | not assumed | **no source states it as an axiom**; forced for non-empty regions by (D3)'s pointwise definition; permitted by a), b), c); holds at `∅` in (D11). tier (a)/(b) | (H1); (X3) |
| (C7) | **[KOE03]'s `⋐` is a membership predicate, not containment** | — | `I ⋐ S¹` abbreviates "`I` is a proper interval of `S¹`"; the separation is written `\overline{I_1}\subset I_2`. tier (a) | **a reader who takes `I₁ ⋐ I₂` to mean `Ī₁ ⊆ I₂` reads the wrong relation into every axiom of that source**; the two symbols appear side by side in (D15) |
| (C8) | the word "net" | the map `O ↦ 𝒜(O)` | = **directed family** in [BGL93] and [KOE03], who therefore say `𝒦̃` and the proper intervals "are not a net"; = the map in [HM06], [NAA13], [GLRV99], [BFV01]. tier (a) | under the first reading, [BGL93] Prop. 1.3(v) is a statement about the *index set*, not the algebras |
| (C9) | extending the net outside 𝒦 | not adopted | three devices for `𝒜(𝒮)`: norm closure of the algebras inside `𝒮` ([NAA13], explicit); smallest C\*-algebra generated by them ([BFV01], for `S^⊥⊥`); additivity plus enlarging the index set ([GLRV99]); **undefined** ([HM06] writes `\al A(O')` with no definition). tier (a) | a *choice*, not a theorem; nothing in the corpus shows two devices agree |
| (C10) | boundedness | not assumed | compact base ([GLRV99]), precompact ([BGL93]), relatively compact ([BFV01]), finite ([NAA13]), **non-dense** ([KOE03]), automatic ([HM06]), **dropped** ([GLRV99] (D20)). tier (a) | non-dense on `S¹` is **not** a compactness condition — every subset of `S¹` is relatively compact — but is what makes the complement non-empty |
| (C11) | is `∅ ∈ 𝒦`? | not excluded | **in**: [NAA13]'s `𝒫_f(Γ)` with `𝒜(∅) = ℂI` (tier (a)); [BFV01] read literally (tier (b)). **out**: [GLRV99], [BGL93], [KOE03], [HM06], [dB74] — in every case as a by-product of the construction, never as a stated condition. tier (a)/(b) | `∅` is ⊥ to everything **including itself**, so admitting it makes ⊥ reflexive and satisfies c) for free — this is (H1)'s concrete form |

## Results and dependencies

### (R1) Directedness ⇒ the quasi-local algebra exists; without it the construction is unavailable

- Source: [GLRV99] §1.1 · tier (a) · **asserted**
- Verbatim:
  > If $\gdef\cK{{\cal K}}\cK$ is directed, then one can form the ``quasilocal algebra'', i.e.\ the smallest $C^*$-algebra containing all the local algebras $\gdef\cA{{\cal A}}\gdef\cO{{\cal O}}\cA(\cO)$. It is the norm closure of the union of the local algebras, $\gdef\cO{{\cal O}}\gdef\cA{{\cal A}}\overline{\bigcup_{\cO}\cA(\cO)}$. In the generic case where $\gdef\cK{{\cal K}}\cK$ is not directed, this possibility is denied to us.
- Depends on: (A1); [ext: the C\*-inductive-limit construction — the norm closure of an upward-directed union of C\*-subalgebras of a common ambient algebra is a C\*-algebra and is the smallest one containing them all. tier (d), not retrieved]
- This is why GLRV99's superselection apparatus is cohomological rather than algebraic.

### (R2) Essential duality lies strictly between locality and Haag duality

For a representation family, the dual net is `𝒜_π^d(𝒪) := ⋂_{𝒪₁ ⊥ 𝒪} π_{𝒪₁}(𝒜(𝒪₁))′`;
*essential duality* asks that it be local, *Haag duality* that it equal
`π_𝒪(𝒜(𝒪))″`.

- Source: [GLRV99] §1.1 · tier (a) · **asserted**
- Verbatim:
  > This property is stronger than locality but not as strong as Haag duality which demands that $\gdef\p{\pi}\gdef\cO{{\cal O}}\gdef\cA{{\cal A}}\p_{\cO}(\cA(\cO))'' = \cA_{\p}^d(\cO)$ for all $\gdef\cO{{\cal O}}\gdef\cK{{\cal K}}\cO \in \cK$.
- Depends on: (R7); the availability of `𝒪^⊥` as an index set, i.e. (D1)

### (R3) [GLRV99] Lemma 2.1 — the regular diamonds absorb any point of the causal complement

Let `𝒪` be a regular diamond and `p ∈ 𝒪^⊥`. Then some regular diamond `𝒪₁`
satisfies `𝒪 ∪ {p} ⊂ 𝒪₁`.

- Source: [GLRV99] Lemma 2.1 · tier (a) · **sketched in source**, full proof cited elsewhere
- Depends on: (D2)'s regularity conditions; (A11); [ext: Brown — a compact, locally flatly embedded, two-sided topological submanifold boundary admits a collar neighbourhood, so the base of a regular diamond has an open neighbourhood in the same Cauchy surface with the same regularity. tier (d), not retrieved]; [ext: Verch — the detailed proof, and the existence of an acausal Cauchy surface through `p` meeting `J(Ḡ)` inside a regularity-preserving neighbourhood. tier (d), not retrieved]
- Proof route: (1) fix a smooth foliation into acausal Cauchy surfaces [global hyperbolicity, (A11)]; (2) enlarge `Ḡ` to a neighbourhood that is again a regular base [ext: Brown]; (3) find an acausal Cauchy surface through `p` with `J(Ḡ)` inside the transported neighbourhood [ext: Verch]; (4) attach a tubular neighbourhood of a curve to `p` [the two-sidedness clause of (D2)].
- Step 3 is load-bearing and rests entirely on the unfetched reference.

### (R4) [GLRV99] Lemma 2.2 — the causally disjoint pairs of points are pathwise connected, with one exception

- Source: [GLRV99] Lemma 2.2 · tier (a) · **proved in source**
- Verbatim:
  > ${\cal X}_{M,g}$ is pathwise connected except when its Cauchy surfaces are noncompact and 1--dimensional in which case there are precisely two path--components corresponding to $x$ being causally to the left or to the right of $y$.
- Depends on: (A11); (A2a); (D3) — the *neighbourhood-buffered* form of ⊥, consumed in step 2 and not replaceable by the naive reading; [ext: elementary homotopy theory — a strong deformation retract induces a bijection of path components. tier (d), not retrieved]
- Proof route: (1) build a homotopy retracting onto pairs in one Cauchy surface [the foliation, (A11)]; (2) check the image stays in `𝒳_{M,g}` — **this step consumes exactly (D3)'s open-neighbourhood buffer and fails for the naive reading of ⊥**; (3) conclude a bijection on path components [ext: homotopy theory]; (4) split by the topology of the Cauchy surface [(A2a)].
- GLRV99 records `It may be known to experts, but as we have not found it in the literature, we put it on record here.`, so the corpus is this row's primary source.

### (R5) [GLRV99] Lemma 3A.1 / Cor. 3A.2 — connectedness transported from the space to the poset

- Source: [GLRV99] Lemma 3A.1, Cor. 3A.2 · tier (a) · **proved in source** (3A.1); **asserted** (3A.2)
- Verbatim:
  > Let $\cal{P}$ be a base for the topology of a space $M$ and ordered under inclusion and suppose the elements of $\cal{P}$ are open, (non-empty) and path--connected. Then an open subset $X$ of $M$ is path--connected if and only if $\gdef\cP{{\cal P}}\cP_X$:=$\gdef\cO{{\cal O}}\gdef\cP{{\cal P}}\{\cO\in\cP:\cO\subset X\}$ is connected.
- Depends on: (A6); (A7)
- The bridge lemma of the whole apparatus: every connectedness claim GLRV99 makes about the *poset* is obtained by applying this to a topological one.

### (R6) The poset of regular diamonds is connected, each `𝒪^⊥` is connected, and the graph of ⊥ is connected — except in two dimensions

- Source: [GLRV99] §3.1 · tier (a) · **proved in source** as a two-step derivation
- Verbatim:
  > By virtue of Lemma 3A.1, we know that $\cal{K}$ is connected and, see Lemma 2.2, that $\gdef\cO{{\cal O}}\cO^\perp$ is connected except when $M$ is two dimensional with a non--compact Cauchy surface.
- Depends on: (R4); (R5); (A6); (A2a)

### (R7) The dual-net operation is an antitone Galois-type map

`𝒜 ⊂ 𝒜^dd`; `𝒜 ⊂ ℬ` implies `ℬ^d ⊂ 𝒜^d`; hence `𝒜^d = 𝒜^ddd`; and `𝒜` local
implies `𝒜^dd` local.

- Source: [GLRV99] §3.2 · tier (a) · **proved in source**
- Verbatim:
  > is the largest net local relative to $\gdef\cA{{\cal A}}\cA^d$, $\gdef\cA{{\cal A}}\cA\subset\cA^{dd}$. However $\gdef\cA{{\cal A}}\gdef\cB{{\cal B}}\cA\subset\cB$ implies $\gdef\cB{{\cal B}}\gdef\cA{{\cal A}}\cB^d\subset\cA^d$, so that $\gdef\cA{{\cal A}}\cA^d=\cA^{ddd}$. A net $\gdef\cA{{\cal A}}\cA$ is said to be {\it local} if $\gdef\cA{{\cal A}}\cA\subset\cA^d$ and then $\gdef\cA{{\cal A}}\cA^{dd}\subset\cA^d=\cA^{ddd}$ so that $\gdef\cA{{\cal A}}\cA^{dd}$ is local, too.
- Depends on: (D1) a), b), c) — GLRV99 notes relative locality satisfies their analogues
- Proof route: (1) `𝒜^d` is the largest net relatively local to `𝒜` [the formula]; (2) `𝒜 ⊂ 𝒜^dd` [step 1]; (3) `d` is order reversing, so `𝒜^d = 𝒜^ddd` [steps 1–2]; (4) locality propagates [step 3].
- The algebra-side shadow of the ⊥-Galois connection on 𝒦; the index-set version is (R9).

### (R8) The Extension Theorem — connectedness of each `𝒪^⊥` lets essential duality replace Haag duality

- Source: [GLRV99] Thm 3A.7 · tier (a) · **proved in source**
- Verbatim:
  > If each $\cal{O}^\perp$ is connected, every object $\pi$ of {\rm Rep}$\gdef\cA{{\cal A}}^\perp\cA$ admits a unique extension to an object of {\rm Rep}$\gdef\cA{{\cal A}}^\perp\cA^{dd}$. Furthermore there is a canonical isomorphism of $W^*$--categories {\rm Rep}$\gdef\cA{{\cal A}}^\perp\cA$ and {\rm Rep}$\gdef\cA{{\cal A}}^\perp\cA^{dd}$.
- Depends on: (A3); (R7); [GLRV99] Lemma 3A.5; [GLRV99] Thm 3A.6
- The printed proof cites "Lemma 3.A.4" where Lemma 3A.5 is needed — see `## Not investigated`.

### (R9) ⊥̃ and ⊥̂ inherit a) and b) but not c); both operations are idempotent; all three relations coincide when 𝒦 is directed

- Source: [GLRV99] Appendix Ch. 3 · tier (a) · **asserted in source; proved in this note**
- Verbatim: the quote under (D5).
- Depends on: (D1) a), b), c); (A1) for the coincidence clause
- Proof (coincidence): `⊥ ⊆ ⊥̂` — directedness supplies a common upper bound, and uses **no axiom**. `⊥ ⊆ ⊥̃` — given `O₁ ⊥ O₂`, directedness supplies `O₄ ≥ O₁, O₂`, c) supplies `O₃` with `O₄ ⊥ O₃`, and b) applied twice gives `O₁ ⊥ O₃` and `O₂ ⊥ O₃`; this uses **b), c) and directedness, but not a)**.
- Proof (idempotence): `⊥̂` is idempotent with **no axiom** — its defining clause is already carried by `⊥̂`. `⊥̃` is idempotent **using a)**: if `O₃` witnesses `O₁ ⊥̃ O₂`, then `O₂` witnesses `O₁ ⊥̃ O₃`, which needs `O₃ ⊥ O₂` obtained from `O₂ ⊥ O₃` by symmetry.
- So **a) is load-bearing for idempotence of ⊥̃ and for nothing else in this cluster, while b) and c) are load-bearing for the coincidence.** No source locates this.

### (R10) For regular diamonds the gap between ⊥ and ⊥̃ is a boundary effect

- Source: [GLRV99] Appendix Ch. 3 · tier (a) · **proved in source** for the implication, **asserted** for the exhaustion
- Verbatim:
  > the difference between the relations $\perp$ and $\tilde\perp$ is, in this sense, a boundary effect.
- Depends on: (D2); (R9)

### (R11) On the sieves with non-trivial causal complement, ⊥̃ = ⊥̂

- Source: [GLRV99] Appendix Ch. 3 · tier (b) read · **proved in source** (one line)
- Depends on: (R9); sieves closed under union
- GLRV99's diagnosis of why the two differ on regular diamonds: `The difference between $\tilde\perp$ and $\hat\perp$ merely reflects the potential difficulty of finding suitably large regular diamonds.` — i.e. exactly a failure of directedness.

### (R12) [GLRV99] Lemma 3A.3 — components of a poset from components of a covering family of sieves

- Source: [GLRV99] Lemma 3A.3 · tier (a) · **proved in source**
- Depends on: each member of the covering family is a sieve; `I` connected for the second clause

### (R13) [GLRV99] Lemma 3.A4 — `μ` and `ν` are mutually inverse on causally closed open sets and sieves

With `μ(X) := {𝒪 ∈ 𝒦 : 𝒪 ⊂ X}` and `ν(𝒮) := ⋃{𝒪 : 𝒪 ∈ 𝒮}`.

- Source: [GLRV99] Lemma 3.A4 · tier (a) · **proved in source**
- Verbatim:
  > When restricted to causally closed open sets and sieves, the maps $\mu$ and $\nu$ are inverses of one another.
- Depends on: (A6); (A9); (A10)
- **This is the result most directly about the object of this note**: it is the precise sense in which the poset `(𝒦, ⊥)` loses no information relative to the causally closed open sets of `M`, and it is what reconciles (C4)'s two readings of `𝒪^⊥`.

### (R14) [GLRV99] Lemma 3.6 and its dimensional case analysis — the components of `Σ^⊥₁` determine the braiding

In dimension `> 2` the relevant poset of 1-simplices is connected; in dimension
two with non-compact Cauchy surfaces it has exactly two components; in dimension
two with compact Cauchy surfaces the graph of ⊥ is connected but the simplex
poset still has two components.

- Source: [GLRV99] Lemma 3.6 and the discussion following · tier (a) · **proved in source**
- Depends on: (R4); (R6); (R12); (D2)
- **This is where the index set alone decides whether the statistics is symmetric or braided.**

### (R15) A net tending spacelike to infinity exists when 𝒦 is directed and when the Cauchy surface is non-compact; the compact case is open

- Source: [GLRV99] §3.1 · tier (a) · **asserted**
- Verbatim:
  > Such a net obviously exists whenever $\cal{K}$ is directed but it continues to exist for an arbitrary globally hyperbolic spacetime with a noncompact Cauchy surface. The question of whether one can find a suitable substitute for globally hyperbolic spacetimes with compact Cauchy surfaces is still open,
- Depends on: (A1); (A11)
- The geometric input to the construction of a left inverse, hence to the classification of statistics and charge conjugation. GLRV99's own mitigation is (A19).

### (R16) The regular diamonds are not directed in general and are **never** directed when the Cauchy surface is compact

- Source: [GLRV99] §3.1 · tier (a) · **asserted**
- Verbatim:
  > may not be directed although it will be in cases of interest. However, when $M$ is globally hyperbolic with a compact Cauchy surface, $\gdef\cK{{\cal K}}\cK$ will never be directed and we shall meet problems akin to those on the circle.
- Depends on: (D2)'s `𝒪^⊥ ≠ ∅` clause — the unstated reason is that a diamond over the whole compact Cauchy surface would have empty causal complement
- This makes (R1)'s negative half bite, and is why (R15)'s compact case is open.

### (R17) [GLRV99] — duality for ⊥̂ follows from duality for ⊥ plus additivity, via Lemma 2.1

- Source: [GLRV99] §5.2 · tier (a) · **proved in source**
- Verbatim:
  > Under the above assumptions, the net satisfies duality for the relation $\hat\perp$, namely $$\gdef\cA{{\cal A}}\gdef\cO{{\cal O}} \cA(\cO)=\cap_{\cO_1\hat\perp\cO}\cA(\cO_1)' $$
- Depends on: (R3); additivity of the net; (A17)
- Proof route: (1) Lemma 2.1 gives, for each point of `𝒪₁`, regions witnessing `𝒪 ⊥̂ 𝒪_x` [(R3)]; (2) additivity and duality collapse the two intersections [additivity, (A17)].
- **The only place in the corpus where (R3) does real work in the main line**, and the justification for GLRV99's remark that the two notions of duality coincide for additive nets over regular diamonds.

### (R18) [GLRV99] — closed-form causal complement on a wedge index set

`W(E,t)^⊥ = W(E′,t)`, with `E′` the interior of the complement of the hemisphere `E`.

- Source: [GLRV99] §5.1 · tier (a) · **asserted** (`The following proposition immediately follows.`)
- Verbatim:
  > {$(i)$} $W(E,t)^{\perp} =\hat{r}_{\partial E,t}W(E,t)=W(E',t)$, where $E'$ denotes the interior of the complement of $E$.
- Depends on: (D20)
- The corpus's only closed-form computation of `^⊥` outside Minkowski and conformal settings; the source also records that each wedge here is a diamond, so the two families are not disjoint.

### (R19) [HM06]'s account of directedness — and it disagrees with (R1)

HM06 derives the inductive limit from isotony alone and then notes that
non-directedness can in many cases be circumvented.

- Source: [HM06] §2.1 · tier (a) · **cited elsewhere**
- Verbatim:
  > In some spacetimes, the set of double cones is not directed. In many such cases, it is still possible to define the quasilocal algebra by means of more sophisticated techniques \cite{glob}.
- Depends on: [ext: Fredenhagen, *Global observables in local quantum physics* — a construction of a global observable algebra for a net over a non-directed index set, so that failure of directedness does not by itself obstruct the passage to a single ambient C\*-algebra. tier (d), not retrieved]
- **The corpus's most important unreconciled disagreement.** (R1) says the construction is *denied*; this says it can often be circumvented. The two are not formally contradictory — GLRV99 denies the naive norm closure, which HM06 does not claim — but the reconciliation lives in an unfetched article.

### (R20) Reeh–Schlieder plus `Ō₁ ⊂ 𝒪₂` gives a standard inclusion

- Source: [HM06] §2.4 · tier (a) · **asserted**
- Verbatim:
  > Then if $O_1,O_2$ are double cones such that the closure $\gdef\ol#1{{\overline #1}}\ol{O}_1$ of $O_1$ is contained in $O_2$, then the pair $\gdef\alg#1{\mathfrak{#1}}(\alg{R}(O_1),\alg{R}(O_2))$ is a standard inclusion of von Neumann algebras.
- Depends on: (A5); (D9)
- **The clearest instance in the corpus of a theorem whose only geometric content is a relation on 𝒦.** The unstated intermediate step — that `Ō₁ ⊂ 𝒪₂` makes `𝒪₁′ ∩ 𝒪₂` contain a region — is itself a claim about 𝒦 that no source proves; it is exactly the collar clause, and the Ordering theorem above is its proof under (T).

### (R21) The funnel property implies the Hilbert space is separable

- Source: [HM06] Prop. `separable` · tier (a) · **proved in source**
- Depends on: (A13); (A5); [DL84] Prop. 1.6 as an independent route (tier (b), `mineru-unchecked`)
- HM06 records that this is the only place in its chapter where separability is needed, and is openly sceptical of its physical warrant.

### (R22) Concrete models exist in which the funnel property fails

- Source: [HM06] §2.4 · tier (a) *for HM06 making the claim*; the claim itself **cited elsewhere**
- Depends on: [ext: Horuzhy, *Introduction to Algebraic Quantum Field Theory* — exhibits models of a net of local algebras in which no type I factor interpolates between the algebras of a region and of a larger region containing its closure. tier (c), no locator, not retrieved]
- No such model is named in any fetched source; (R39) supplies a named one by a different route.

### (R23) The funnel property holds for free fields

- Source: [HM06] §2.4 · tier (a) for the claim · **cited elsewhere** — and the cited source is [dB74], in this corpus
- Depends on: (R57); (R60)

### (R24) Schlieder from microcausality, weak additivity and the spectrum condition, for strictly spacelike separated pairs

- Source: [HM06] Prop. `schlieder` · tier (a) · **cited elsewhere**
- Depends on: (D7); [ext: Schlieder — for a pair of commuting von Neumann algebras arising from spacelike separated regions of a net with weak additivity and positive energy, the product of two non-zero elements, one from each, is non-zero. tier (d), not retrieved]

### (R25) "Strongly spacelike separated" lies strictly between spacelike and strictly spacelike separated

- Source: [HM06] §3.3 · tier (a) · **asserted in source; proved in this note**
- Verbatim:
  > \begin{fact} If $O_1$ and $O_2$ are strictly spacelike separated, then they are strongly spacelike separated. \end{fact}
- Depends on: (D7); (D8); (A: 𝒦 contains, for each region, an enlargement containing its closure)
- Proof: from a neighbourhood `N` of `0` with `O₁ + x` spacelike to `O₂` for all `x ∈ N`, pick `ε` with `B(0,ε) ⊆ N`; translation covariance gives `O₁ + x` spacelike to `O₂ + y` for `|x|,|y| < ε/2`, and the unions over those translates are the required enlargements. **The proof is model-specific**: it needs 𝒦 closed under small enlargements, which (D2) records that double cones in a curved spacetime lack.

### (R26) Schlieder from microcausality and property B, for strongly spacelike separated pairs

- Source: [HM06] Prop. `frees` · tier (a) · **proved in source**
- Depends on: (A20); (D8)
- The printed proof opens "Let `O₁` and `O₂` be **strictly** spacelike separated" where the statement says **strongly**; the proof's second sentence is the definition of *strongly* unpacked, so the proposition as stated is proved and the first line is a typo.

### (R27) The split property fails for a wedge and its causal complement

- Source: [HM06] §3.3 · tier (a) · **proved in source**
- Depends on: `ℛ(W)` and `ℛ(W′)` being type III₁ factors; HM06's remark that a factor and its commutant have the same type
- HM06's own type III₁ proposition carries the escape clause `Then either $\gdef\al#1{{\mathfrak #1}}\gdef\7#1{{\mathbb #1}}\al R=\7C I$ or $\gdef\al#1{{\mathfrak #1}}\al R$ is a type III$_1$ factor.`, so every argument of the shape "split for all pairs ⇒ type I ⇒ contradiction" silently assumes the local algebras are not the scalars.

### (R28) The funnel property upgrades to the split property for strictly spacelike separated pairs

- Source: [HM06] §3.3 · tier (a) · **asserted**
- Depends on: (A13); (D7)

### (R29) The implication chain among independence notions

- Source: [HM06] §3.2 · tier (b) read · **cited elsewhere**
- Depends on: [ext: Summers — a survey ordering the independence conditions for a pair of commuting von Neumann algebras by logical strength. tier (c), no locator, not retrieved]

### (R30) [BGL93] Prop. 1.3 — five index-set properties of `𝒦̃`, including that it is closed under `′` and is not directed

- Source: [BGL93] Prop. 1.3 · tier (a) · **asserted** (`\proof Immediate.`)
- Verbatim: the three clauses quoted under (D12).
- Depends on: `M̃` the universal covering of compactified Minkowski space and `𝒞̃` its conformal group
- Clause (v) is `proved` on inspection, but the proof needs `𝒪″ = 𝒪`, which BGL93 never states.

### (R31) For the double cones of Minkowski space, directedness is what makes the quasilocal algebra a direct limit

- Source: [BGL93] §1 · tier (a) · **asserted**
- Verbatim: the `direct set` quote under (D12).

### (R32) The conformal net extends uniquely to the covering

- Source: [BGL93] Lemma 1.9, Prop. 1.10 · tier (a) · **proved in source**
- Depends on: (R30)(ii) — transitivity of the conformal action on `𝒦̃`

### (R33) Essential duality holds automatically for a conformally covariant pre-cosheaf

- Source: [BGL93] Thm 2.3 · tier (a) · **proved in source**
- Depends on: (R32); [BGL93] Prop. 2.1

### (R34) Duality on `S¹` holds with no assumption beyond positivity of the energy

- Source: [BGL93] §2 · tier (a) · **asserted** for the models
- Depends on: (R33); [ext: Hislop–Longo — for the free massless scalar field the modular group of the algebra of a double cone acts geometrically, giving duality. tier (c), no locator, not retrieved]
- (R42) identifies by name what this describes: duality on the light-ray is equivalent to **strong additivity**, and fails because the complement of an interval of `ℝ` is disconnected while on `S¹` it is a single proper interval.

### (R35) [BGL93] Cor. 2.7 — under conformal invariance plus a spectral condition, every local algebra is the hyperfinite type III₁ factor

- Source: [BGL93] Remark 2.6, Cor. 2.7 · tier (a) for the statement; the result **cited elsewhere** (`\proof Immediate, see [\ref(Long1)].`) · **survives at (c), `unverified`**
- Depends on: (R36); conformal invariance; exponential eigenvalue growth; [ext: Longo — the interpolating type I factor structure forces the hyperfinite type III₁ factor. tier (c), no locator, not retrieved]
- **How much weight this can carry:** it is conditional on Remark 2.6's spectral hypothesis and on an unretrieved citation, so an argument needing "local algebras are not type I" should hang on [HM06]'s type III₁ proposition instead, carrying its `ℂ𝟙` escape clause.

### (R36) The "distal split property" is an existential over a single pair of regions

- Source: [BGL93] §3 assumption (b) · tier (a) · it is an **assumption**, not a result
- Verbatim:
  > \item{$(b)$} Distal split property holds, i.e there exist two regions $\gdef\O{{\cal O}}\O_1\subset \O'_2$ in $M$ such that $\gdef\R{{\cal R}}\gdef\O{{\cal O}}\R(\O_1)$ and $\gdef\R{{\cal R}}\gdef\O{{\cal O}}\R(\O_2)$ generates a $W^*$-tensor product.
- **It imposes no relation on 𝒦 at all** — one split pair anywhere suffices — and is therefore strictly weaker than the funnel property, not a metric strengthening of the separation relation. It upgrades to the universal form under a **transitively acting symmetry group and `d > 2`**.

### (R37) The distal split property forces uniqueness of the covariant representation

- Source: [BGL93] Thm 3.1 · tier (a) · **proved in source**
- Depends on: (R36)

### (R38) Essential duality for wedges from geometric modular action

- Source: [BGL93] Thm 3.3 · tier (a) · **proved in source** by reference to earlier proofs
- Depends on: (R33)
- The printed proof cites a "Lemma 3.4" that does not exist; Lemma 3.2 is meant.

### (R39) A named non-split net: `ℬ(𝒪) = 𝒜(π⁻¹𝒪)`

Let `𝒜` be a Poincaré covariant net on `(d+1)`-dimensional Minkowski space and
`π` the projection onto `d` dimensions; then `𝒪 ↦ 𝒜(π⁻¹𝒪)` is a net on `d`
dimensions which BGL93 labels non-split.

- Source: [BGL93] §3, closing paragraph · tier (a) for the construction; the attribution is to a **private remark** of Buchholz, so **no locator can ever exist** · **proved in source** as a short verification
- Depends on: (R38)
- **The corpus's only concrete non-split example.** BGL93 only *labels* it non-split and leaves unwritten both that `ℬ` satisfies its assumption (a) and the contraposition; and the argument needs `d > 2`. (R59)(b) reaches the same conclusion by a route with fewer external edges.

### (R40) The proper intervals of `S¹` are not directed

- Source: [KOE03] §1.2 · tier (a) · **asserted**
- Verbatim: the quote under (D14).
- Depends on: `I′ ≠ ∅` as a membership condition
- **The corpus's load-bearing non-directed index set.**

### (R41) What the failure of directedness costs: DHR must be replaced, and Doplicher–Roberts reconstruction is lost

- Source: [KOE03] §1.3 · tier (a) · **cited elsewhere**
- Depends on: (R40)

### (R42) Haag duality on `S¹` follows from the general assumptions but may fail on the light-ray

- Source: [KOE03] §1.3 · tier (a) · **asserted** (`S¹` half)
- Depends on: (R40)
- The mechanism is the index set's topology: the complement of an interval of `ℝ` is disconnected, of an interval of `S¹` is a single proper interval.

### (R43) Strong additivity of a subnet removes the isotony problem for local relative commutants

- Source: [KOE03] §1.2–1.3 · tier (a) · **proved in source**
- Depends on: (R42); locality; the `⋐` relation

### (R44) The dual net on the light-ray makes any chiral theory strongly additive

- Source: [KOE03] §1.3 · tier (a) · **cited elsewhere**
- Depends on: (R42)

### (R45) Inner and outer continuity of the local algebras along the `⋐` relation

- Source: [KOE03] §1.3 · tier (a) · **cited elsewhere**
- Depends on: scale invariance

### (R46) The split property for chiral nets is stated over the `Ī₁ ⊂ I₂` relation

- Source: [KOE03] §1.3 · tier (a) · **definition** plus an **asserted/cited** implication from nuclearity
- Verbatim: the quote under (D15).
- Depends on: [ext: Buchholz–Wichmann — a nuclearity condition on the energy-level density implies the split property for sufficiently separated regions. tier (d), no locator, not retrieved]

### (R47) Double cones are causally complete

- Source: [NAA13] §1 · tier (a) · **asserted**
- Verbatim: the quote under (D10).

### (R48) The lattice index set is directed, ⊥ is disjointness, and the quasi-local algebra is the inductive limit

- Source: [NAA13] §2.4 · tier (a) · **proved in source** at the level of the construction
- Depends on: Γ countable; (A1), used silently

### (R49) C\*-level duality `𝒜(Λ)^c = 𝒜(Λ^c)` for finite Λ

- Source: [NAA13] §2.4 · tier (a) · **proved in source** for the finite case
- Depends on: (R48); [ext: NAA13's cited text — the relative commutant of a finite-region algebra inside the quasi-local algebra of a spin system is the algebra of the complementary region. tier (c), no locator, not retrieved]

### (R50) Haag duality for cones: one inclusion is free from locality, the other is an assumption

- Source: [NAA13] §3 · tier (a) · the easy inclusion **proved in source**
- Depends on: (R48)

### (R51) The superselection criterion quantifies over the cone index set

- Source: [NAA13] §3 · tier (a) · **sketched**
- Depends on: (R50)
- Cones are named as an index set here and by [GLRV99] and are **defined by neither**; the definition lives on the unfetchable list.

### (R52) [BFV01] — the index set of a locally covariant theory

- Source: [BFV01] §2.4, first document body · tier (a) · **definition**
- Verbatim: the quote under (D16).
- Depends on: `(M,ḡ)` an object of `𝔐`

### (R53) [BFV01] — the causal complement as a largest open set

- Source: [BFV01] §2.1, first document body · tier (a) · **definition**
- Verbatim: the quote under (D17).
- The existence of a *largest* such open set is not argued.

### (R54) [BFV01] Prop. `localnet` — a locally covariant theory yields a Haag–Kastler net over `𝒦(M,ḡ)`

- Source: [BFV01] Prop. `localnet`, first document body · tier (a) · **proved in source**, all four clauses
- Depends on: (R52); (R53); the functor axioms
- **The corpus's only derivation of the Haag–Kastler index-set structure from a categorical datum**, and the reason (H2) is a scope limit rather than a defect.

### (R55) [BFV01] — the fattening lemma: causally separated regions can be enlarged while staying causally separated

- Source: [BFV01], inside the proof of Prop. `localnet`, first document body · tier (a) · **asserted**
- Depends on: (R52); (R53); (A11)
- BFV01 asserts in one sentence what [GLRV99] (R3) sketches over a page.

### (R56) [BFV01] — the inductive limit attributed to isotony alone

- Source: [BFV01] §2.4 footnote, first document body · tier (a) · **asserted**
- Depends on: isotony; and, unstated, that the bounded open subsets of Minkowski space are directed

### (R57) [dB74] — the `𝒩`-thickened separation relation and the "almost factors" standing hypothesis

- Source: [dB74] §II · tier (b), `mineru-unchecked` · **cited elsewhere**
- Verbatim: the shape-1 and standing-hypothesis quotes under (D18).
- Depends on: (A5) in dB74's form — Ω cyclic and separating for open regions with non-empty spacelike complement

### (R58) [dB74] Cor. 2.4 — a normal product state yields interpolating type I factors, and conversely

- Source: [dB74] Cor. 2.4 · tier (b), `mineru-unchecked` · **proved in source**; the converse **asserted**
- Depends on: (R57)

### (R59) [dB74] — two classes of configurations admitting **no** normal product state

(a) regions whose closures are not spacelike separated (asserted, free field);
(b) any two spacelike separated regions each mapped into itself by a common
translation.

- Source: [dB74] §II, items a) and b), **p. 292** · tier (b), `mineru-cross-checked-against-PDF-text-layer` · (a) **asserted**, (b) **proved in source**
- Depends on: isotony; clustering; (A5)
- **(b) is the corpus's most economical non-example**: it needs no type classification, and it covers both (R27)'s wedge pair (**in `d ≥ 3` only** — in 1+1 no translation fixes both `W` and `W′`, so the two routes are incomparable rather than nested) and every region of (R39)'s net. Neither source cites dB74 for it. The footnote on item b) reads *This example is due to Araki*.

### (R60) [dB74] — the positive result for the free neutral massive scalar field

- Source: [dB74] §III · tier (b), `mineru-unchecked` · **proved in source** (the proof runs past the converted pages, so no route)
- Depends on: (D18) shape 3 — smooth boundaries and positive distance

### (R61) [DL84] — the split property expresses independence of regions separated by non-zero distance

- Source: [DL84] §0 · tier (b), `mineru-unchecked` · **asserted**
- Verbatim:
  > expresses the statistical independence of any bounded region in space-time from any other region space-like separated by non-zero distance
- Depends on: (D18) shape 3, which DL84 echoes from dB74 — and dB74's cached scope (R60) is narrower than either DL84's or HM06's paraphrase.

### (R62) [DL84] — the split property is stated with **no separation relation at all**

- Source: [DL84] §1 · tier (b), `mineru-unchecked` · **definition**
- **The cleanest evidence in the corpus that the separation relation belongs to the index set and not to the algebras**: at the two-algebra level it simply is not present.

### (R63) [DL84] announces field theories that do not satisfy the split property

- Source: [DL84] §§9–10, **not converted** · tier (b) for the announcement
- Would supply further concrete non-split examples; the highest-value extension available to a later run.

## Hypotheses

| (A#) | Statement | Class | Evidence | Witness | Scope | Tier | Used by |
|---|---|---|---|---|---|---|---|
| (A1) | 𝒦 is directed under inclusion | model-dependent | [GLRV99] §3.1; [KOE03] §1.2; [HM06] §2.1 | fails: the proper intervals of `S¹` ([KOE03], stated outright); also the regular diamonds of any globally hyperbolic spacetime with compact Cauchy surface ([GLRV99], class fact, no spacetime named). holds: the open double cones of Minkowski | local | a | (R1), (R9), (R15), (R16), (R19), (R31), (R40), (R48) |
| (A2) | 𝒦 is connected as a poset | provable | [GLRV99] Lemma 3A.1 applied to (A2a) | — | local | a | (R6), (R14) |
| (A2a) | `M` is path-connected | model-dependent | implicit in [GLRV99] §2.1, explicit in [BFV01] §2 (`connected`) | fails: the disjoint union of two copies of Minkowski space (tier (b) — the ingredients are quoted, the assembly is mine). holds: 4-dimensional Minkowski | standing, **implicit** in [GLRV99] | a/b | (R2), (R4), (R6) |
| (A3) | each `𝒪^⊥` is connected | model-dependent | [GLRV99] §3.1, §3.2 | fails: regular diamonds in 2-dimensional Minkowski space, where the complement splits into a left and a right part. holds: 4-dimensional Minkowski | local | a | (R6), (R8), (R14) |
| (A4) | the graph of ⊥ is connected | model-dependent | [GLRV99] Lemma 2.2, proof read | fails: 2-dimensional Minkowski (Cauchy surface `ℝ`). holds: dimension `> 2` | local | a | (R14) |
| (A5) | the vacuum is cyclic and separating for local algebras | provable / assumed | [HM06] §2.3; [dB74] §II as a standing assumption | — | standing in [dB74] | a/b | (R20), (R21), (R57), (R59) |
| (A6) | 𝒦 is a base for the topology of `M` | provable | [GLRV99] Lemma 3A.1 and `Both sets have in common that they form a base for the topology of $M$` | — | local | a | (R5), (R6), (R13), and the Ordering theorem |
| (A7) | members of 𝒦 are open, non-empty, path-connected | provable | [GLRV99] §2.1 regularity conditions | — | local | a | (R5), (R6) |
| (A8) | condition c) for ⊥, ⊥̃, ⊥̂ | definitional for ⊥; provable for ⊥̃, ⊥̂ in the applications | [GLRV99] §3.1 and Appendix Ch. 3 (`c) remains to be checked`) | — | standing / local | a | (R7), (R9) |
| (A9) | ⊥ on `Open(M)` is *local*: `X ⊆ ⋃𝒪ᵢ` with every `𝒪ᵢ ⊥ 𝒪` gives `X ⊥ 𝒪` | provable | [GLRV99] Appendix Ch. 3, asserted as obvious | — | local | a | (R13) |
| (A10) | members of 𝒦 are causally complete, `𝒪 = 𝒪^⊥⊥` | provable for the index sets used | [NAA13] §1 and [GLRV99] §2.1 both assert it without proof; **independent of a),b),c)** by (X19) | — | mixed: membership condition in (D19), observation in (D10) | a | (R13), (R30) |
| (A11) | `(M,g)` is globally hyperbolic | model-dependent | [GLRV99] §2.1; [BFV01] §2, both standing | no failing spacetime is named in the corpus; the classical examples rest on recall, so this row is at best (d) on the failing side | standing | a/d | (R3), (R4), (R15), (R55) |
| (A12) | the vacuum Hilbert space is separable | provable relative to (A13) | [HM06] Prop. `separable`; [KOE03] builds it into its axioms; [DL84] Prop. 1.6 independently (tier (b), `mineru-unchecked`) | — | standing in [HM06], [KOE03] | a/b | (R21) |
| (A13) | the funnel / split property | model-dependent | [HM06] §2.4; [BGL93] §3; [KOE03] §1.3 | fails: [BGL93]'s dimensional-reduction net (R39), and every configuration of (R59)(b). holds: the free neutral massive scalar field (R60); conformal nets under (R35) | local | a | (R21), (R23), (R28), (R35), (R37) |
| (A14) | how much separation the independence results need | model-dependent | [HM06] §3.3; [dB74] §II–III; [DL84] §0; [BGL93] §3 | fails: two double cones in 4-dimensional Minkowski whose closures touch (R59)(a). holds: the same pair pushed apart | local | a/b | (R20), (R24), (R25), (R26), (R28), (R59), (R61) |
| (A15) | every region has non-empty causal complement | model-dependent | [dB74] §II standing; membership condition in (D2), (D14), (D19) | fails: a time-slab around a compact Cauchy surface in [BFV01]'s `𝒦(M,ḡ)`. holds: every open double cone in Minkowski | standing in [dB74] | a/b | (R16), and axiom c) |
| (A16) | members of [BFV01]'s `𝒦(M,ḡ)` are open and connected | model-dependent | [BFV01] §2.4 — **not in the definition, forced by the next sentence** | fails on the literal reading: `∅`, `{x}`, and `{x,y}` for `x`, `y` spacelike. holds: any relatively compact causally convex open connected set | standing, **implicit** | a/b | (R52), (R54), and (X15) direction 1 |
| (A17) | Haag duality, or essential duality, for a given index set | model-dependent — **and dependent on which index set** | [BGL93] Thm 2.3; [KOE03] §1.3; [GLRV99] §1.1; [HM06]; [NAA13] §3 | fails: [BGL93]'s net `𝒜ₙ` on the light-ray, i.e. a non-strongly-additive chiral theory. holds: conformally covariant pre-cosheaves (R33); the free massless scalar (R34) | standing / local | a | (R2), (R8), (R17), (R42), (R50) |
| (A18) | surjectivity of the projection from the graph of ⊥ onto 𝒦 | provable | [GLRV99] §3.1, asserted | — | local | a | (R14) |
| (A19) | local intertwiners equal global intertwiners | provable for Minkowski; open in general | [GLRV99] Ch. 5, postulated | — | local | a | (R15)'s mitigation |
| (A20) | property B | provable from microcausality, the spectrum condition and weak additivity | [HM06] Prop. `prop-B`; [GLRV99] §3.2 | — | standing in [HM06] | a | (R26) |
| (A21) | the time-slice axiom | provable for a named model | [BFV01] §4 — the CCR/Weyl algebra of the Klein–Gordon equation on any globally hyperbolic spacetime | — | local | a | — |
| (A22) | the wedges separate spacelike points, i.e. regular diamonds are intersections of wedges | open | [GLRV99] Ch. 5, assumed | neither a proof nor a failing spacetime could be produced | local | a | (R18), (R20)'s wedge analogue |

## Degeneracies and boundary cases

| Case | Effect on the adopted form | Tier |
|---|---|---|
| intended case is nonvacuous | named instances abound and were checked one by one against a), b), c): open double cones in Minkowski ([HM06], [NAA13]); regular diamonds in a globally hyperbolic spacetime ([GLRV99]); proper intervals of `S¹` ([KOE03]); `𝒦̃` ([BGL93], c) via Prop. 1.3(iv)); `𝓛` and `𝒦 ∪ 𝒲` ([GLRV99]); wedges in Minkowski (c) via the opposite wedge); `𝒫_f(Γ)` ([NAA13]) | a |
| zero object / scalars | `𝒦 = ∅`: a), b), c) hold vacuously; no effect. `𝒦` a single element: c) fails unless that element is self-orthogonal | — |
| finite-dimensional | not a meaningful axis for an index set; the discrete analogue is `𝒫_f(Γ)` with `Γ` finite, which still satisfies c) via `∅` | — |
| commutative | not a meaningful axis; the order-theoretic analogue is `𝒦` a chain, which is **not** excluded by the adopted form (it is excluded only under irreflexivity — (X6), (H1)) | — |
| non-separable / non-σ-finite | no effect: these are conditions on the Hilbert space, and (A12) makes separability a *consequence* of (A13) rather than an input | b |
| type III | the intended case: the local algebras of an interesting net are type III₁, and (X32) turns that into the reason the collar clause cannot be dropped — subject to [HM06]'s `ℂ𝟙` escape clause | a/c |
| non-unital / degenerate representation | no effect at index-set level; [NAA13] fixes `𝒜(∅) = ℂI` explicitly rather than allowing a degenerate algebra | a |
| universally orthogonal index element | **admitted**: `∅ ∈ 𝒦` is ⊥ to everything including itself in (D11), and a bottom element ⊥ to everything is exactly (H1)'s construction. It satisfies c) while making c)'s intended guarantee empty | a |
| everything ⊥ everything | a), b), c) all hold; the *net* over such an index set collapses to a commutative one by locality, but the form itself is not contradicted | — |
| quantifier swap in c): `∀O₁ ∃O₂` ↦ `∃O₂ ∀O₁` | meaning changes: taking `O₁ := O₂` forces `O₂ ⊥ O₂`. False on double cones, true on `𝒫_f(Γ)` via `∅` — (X25) | — |
| quantifier swap: "∃ one region ⊥ to all *others*" | genuinely different from both, separated by the 2-element antichain — (X26) | — |
| quantifier swap inside the collar clause | `∃ one collar ∀ nested pairs` is false for double cones (the collar must fit inside arbitrarily small outer regions) and, under the strict collar clause, false for `𝒫_f(Γ)` too — (X28) | — |
| hypothesis dropped: a) symmetry | independent — witness: a 3-cycle on a 3-element antichain satisfies b), c) and fails a). Consequence: idempotence of ⊥̃ fails, by (R9) | — |
| hypothesis dropped: b) heredity | independent — witness: `{A ≤ B, C, D}` with `⊥ = {(B,C),(A,D)}` symmetrised. Consequence: `𝒪^⊥` is no longer a sieve, so (R13) and (R7) fail | — |
| hypothesis dropped: c) | independent — witness: a single element with `⊥ = ∅`. Consequence: `⊥ ⊆ ⊥̃` fails even under directedness, by (R9) | — |
| hypothesis reversed: b) anti-heredity | false in every geometric model; with a top element it produces a *top* orthogonal to everything including itself, **not** the everything-⊥-everything model — (X27) | — |
| hypothesis added: irreflexivity | strictly stronger — not derivable from a), b), c) (witness: (H1)'s bottom-element model). It is what would buy "comparable regions are never ⊥" and "𝒦 is not a chain" | — |
| hypothesis added: causal completeness | strictly stronger — 3-element antichain witness, (X19) | — |
| collar clause dropped from the separation relation | the split property degenerates to `𝒜(O) ⊆ 𝒩 ⊆ 𝒜(O)`, forcing every local algebra to be type I — (X32) | a/c |

## Rejected formulations and refuted claims

**Append-only.**

| id | Candidate or claim | Disposition | Discriminator | Tier | Date |
|---|---|---|---|---|---|
| (X15) | the collar clause and the closure form `Ō₁ ⊆ O₂` as *the* separation relation for the split property | rejected (both, as the single adopted relation) | **(X1) separating object**, both directions — collar without closure: internally tangent double cones `O₂ = {|x₀|+\|x⃗\| < 1}`, `O₁ = {|x₀|+\|x⃗−c\| < 1/2}`, `c = (1/2,0,0)`, with collar `O₃ = {|x₀|+\|x⃗+c\| < 1/8}`, using the verified criterion that `D(B(a,r))` and `D(B(b,s))` are spacelike iff `\|a−b\| ≥ r+s`; closure without collar: `Λ₁ = Λ₂ = {0}` in `𝒫_f(ℤ)`, and (non-degenerately) `O = (−ε,ε)×Σ ⊂ O₂ = (−2ε,2ε)×Σ` over a compact Cauchy surface Σ. **(X5) conditional equivalence** — under (T) the closure form is strictly stronger; see the Ordering theorem | a/b | 2026-08-15 |
| (X18) | the causal complement as an **operation into 𝒦**, `O₁ ⊥ O₂ ⟺ O₂ ≤ O₁^⊥` | rejected | **(X1) separating object** — a double cone in Minkowski: the double cones spacelike to it have no maximum (translate away, then dilate inside `O′`). `𝒦̃` and the proper intervals of `S¹` do support the operation | a | 2026-08-15 |
| (X18′) | the complement as a **sieve-valued** operation `O ↦ {O₁ : O₁ ⊥ O}` | equivalent | — ([GLRV99] writes exactly this: `We write $\gdef\cO{{\cal O}}\gdef\cK{{\cal K}}\cO^\perp:=\{\cO_1\in\cK:\cO_1\perp\cO\}$.`) | a | 2026-08-15 |
| (X19) | causal completeness `O = O″` as an axiom | rejected | **(X1) separating object** — the 3-element antichain `{A,B,C}` with `⊥ = {(A,B),(B,A),(A,C),(C,A)}` satisfies a), b), c) while `B^⊥⊥ = {B,C} ⊋ ↓B`. Geometric realisation: a spacelike disc and its domain of dependence share a causal complement | — | 2026-08-15 |
| (X24) | [BGL93]'s *distal split property* as a phrasing of the separation relation | rejected | **(X5) conditional equivalence** — as written it is an existential over one pair of regions and constrains 𝒦 not at all; it upgrades to the universal form only under a transitively acting symmetry group **and** `d > 2` | a | 2026-08-15 |
| (X25) | c) with the quantifiers swapped | rejected | **(X2) degeneracy** — forces a self-orthogonal element; false on double cones, true on `𝒫_f(Γ)` via `∅` | — | 2026-08-15 |
| (X26) | "∃ one region ⊥ to all *others*" | rejected | **(X1) separating object** — the 2-element antichain `{A,B}` with `A ⊥ B`: the `≠`-form holds, the `∀`-including-self form fails | — | 2026-08-15 |
| (X27) | b) with the inclusion reversed (anti-heredity) | rejected | **(X1) separating object** — false in every geometric model. *The parenthetical claim that with a top element it collapses to everything-⊥-everything is itself refuted*: witness `{A, B ≤ T}` with `⊥ = {(A,B),(B,A)} ∪ {(T,X),(X,T)} ∪ {(T,T)}`, where `A ⊥̸ A` | — | 2026-08-15 |
| (X28) | one collar for all nested pairs | rejected | **(X1) separating object** — double cones: the collar must lie inside arbitrarily small outer regions | — | 2026-08-15 |
| (X32) | dropping the collar clause, leaving `O₁ ≤ O₂` | rejected | **(X2) degeneracy** — the split property becomes `𝒜(O) ⊆ 𝒩 ⊆ 𝒜(O)`, forcing every local algebra type I, contradicting the type III₁ structure — with [HM06]'s escape clause `Then either $\gdef\al#1{{\mathfrak #1}}\gdef\7#1{{\mathbb #1}}\al R=\7C I$ or $\gdef\al#1{{\mathfrak #1}}\al R$ is a type III$_1$ factor.` attached | a/c | 2026-08-15 |
| (X9) | *claim*: [BFV01]'s `𝒦(M,ḡ)` is not an instance of the adopted form, witnessed by `∅`, `{x}`, `{x,y}` and a time-slab | refuted as stated | read literally `∅ ∈ 𝒦(M,ḡ)`, and BFV01's ⊥ is vacuously true against `∅`, so **c) holds everywhere via `∅`** and three of the four witnesses show only that BFV01's regions need not be open or connected. What survives: under the reading forced by BFV01's own `obj(𝔐)` sentence, c) fails at a time-slab around a compact Cauchy surface — **one witness, conditional on a reading BFV01 never states** | a | 2026-08-15 |
| (X7) | *claim*: the lattice index set is excluded by c) | refuted as stated — re-scoped | **[NAA13]'s own `𝒫_f(Γ)` contains `∅`** and fixes `𝒜(∅) = ℂI`, so c) holds even for finite Γ. The claim is about a variant with `∅` removed, not about the corpus's lattice index set | a | 2026-08-15 |
| (X6) | *claim*: the adopted form excludes chains | refuted as applied | the derivation uses **irreflexivity**, which is independent of a), b), c) — witness (H1)'s bottom-element model. The form is not credited with it | — | 2026-08-15 |
| (H1) | *claim about the adopted form*: axiom c) delivers "every region has somewhere spacelike to it" | refuted | adjoin a least element `0` to any poset and set `⊥ = {(0,O),(O,0)}`; a), b), c) hold, so **every poset underlies a causal index set**. Concretely, with `𝒜(0) = ℂ𝟙` the dual net is `B(ℋ)` everywhere and Haag duality forces `𝒜(O) = B(ℋ)` | — | 2026-08-15 |
| (H2) | *scope*: the adopted form expresses [BFV01]'s theory | refuted | BFV01's primary object is a category whose causality condition quantifies over **pairs of morphisms into a common spacetime**; `𝒦(M,ḡ)` is a derived poset obtained by fixing one object. The form covers the derived net, not the theory | a | 2026-08-15 |
| (X-R25) | *claim* [HM06] `fact`: strictly spacelike separated ⇒ strongly spacelike separated, asserted with no proof and no citation | promoted to proved | proof written out at (R25); **not trivial** — it needs 𝒦 closed under small enlargements, which [GLRV99] records that double cones in a curved spacetime lack | a | 2026-08-15 |
| (X-R9) | *claim* [GLRV99]: passing to ⊥̃ or ⊥̂ is idempotent, and all three coincide when 𝒦 is directed, asserted with no proof | promoted to proved | proofs written out at (R9), locating which axiom does which work | a | 2026-08-15 |
| (X-frees) | *claim*: [HM06] Prop. `frees` is proved for a different hypothesis than it states | refuted | the proof's second sentence is the definition of *strongly* unpacked; `strictly` in its first line is a typo and the proposition as stated is proved | a | 2026-08-15 |
| (X-Cor2.7) | *claim*: [BGL93] Cor. 2.7 establishes type III₁ for local algebras | survives at (c), `unverified` | discharged by `\proof Immediate, see [\ref(Long1)].` and conditional on Remark 2.6's spectral hypothesis; the cited work is not retrieved. **The locator is into BGL93, which was retrieved at tier (a), so it is a permitted locator; the `c` in the tier column is the verification status of the *result*, whose proof lies in an unretrieved work** | c | 2026-08-15 |
| (X-1.3v) | *claim*: [BGL93] Prop. 1.3(v) (that `𝒦̃` is not directed) is immediate | promoted to proved | the verification is immediate **given `𝒪″ = 𝒪`**, which BGL93 never states | a | 2026-08-15 |

## Prior art

| System | Found | Relation to variants | How searched | Measured at |
|---|---|---|---|---|
| this repository | `CausalOrthogonality` (`QuantumSystem/Algebra/LocalNet/Net.lean`) — a class over a `Preorder` with fields `Orthogonal`, `orthogonal_symm`, `orthogonal_mono_left` | **still weaker than (D1) alone**: a) and b) present, **c) absent from this class specifically** — c) has since been split off into the separate mixin `CausalIndexSet` (see below), so `CausalOrthogonality` by itself remains a strict sub-axiomatisation, exactly as before this revision. The docstring now names the split explicitly and gives three ways the corpus secures c) (membership condition, admitting `∅`, or not at all — citing (D2)/(D14), (D11), (D16)). Irreflexivity still absent, deliberately; no causal-complement operation, no causal completeness, no directedness in the class | `Grep` for `Causal\|complement\|Haag\|duality\|DHR\|superselection` over `QuantumSystem/`; full read of `Net.lean`; `lean_local_search "CausalIndexSet"`; `lean_hover_info` on both classes | working tree, 2026-08-15 |
| this repository | `CausalIndexSet` (`QuantumSystem/Algebra/LocalNet/Net.lean`) — a new `Prop`-valued mixin class over `[Preorder K] [CausalOrthogonality K]` with the single field `exists_orthogonal : ∀ O₁, ∃ O₂, O₁ ⟂ O₂` | **the combination `CausalOrthogonality K` + `CausalIndexSet K` realizes (D1) exactly** — a), b), c) together, with no further hypotheses: no irreflexivity, no directedness, no causal-complement operation into `K`, no causal completeness. The docstring states this identification in so many words (`An ordered K with [CausalOrthogonality K] and this mixin is exactly the adopted general form of the extraction note`). Previously (X18) and (X19) were rejections of *additional* axioms this class still correctly does not carry — a causal-complement operation into `K` and causal completeness respectively — and that remains true: `CausalIndexSet` adds only c), nothing from (X18)/(X19)'s rejected strengthenings | `lean_hover_info` and `lean_declaration_file` on `CausalIndexSet`; `lean_references` (no consumers found); full read of `Net.lean` | working tree, 2026-08-15 |
| this repository | `instance : CausalOrthogonality (Finset α)` with `Orthogonal := Disjoint`, and `instance : CausalIndexSet (Finset α)` proved by `⟨fun Λ => ⟨∅, Finset.disjoint_empty_right Λ⟩⟩` | **same as (D11)**, and the `CausalIndexSet (Finset α)` instance is the Lean realization of exactly the route (X7)/(D11) already document for the concrete lattice case: `∅` is disjoint from every finite set, so `∅` is the witness for `exists_orthogonal`, matching NAA13's `𝒫_f(Γ) ∋ ∅` device that (X7) identifies as how axiom c) is secured for the lattice index set (the docstring of the instance states this explicitly: "the empty region is disjoint from every region, so causal complements exist for free"). The other (D-concrete) branches — double cones, regular diamonds, `S¹` intervals — have no instance anywhere | greps for `Minkowski`, `Lorentz`, `double cone`, `diamond`, `spacetime`, `wedge` return only docstring prose; full read of the `CausalIndexSet (Finset α)` instance and its docstring | working tree, 2026-08-15 |
| this repository | `ProperContainment` (`QuantumSystem/Algebra/LocalNet/SplitProperty.lean`) with the collar field `∃ O₃, O₃ ≤ O₂ ∧ O₁ ⟂ O₃ ∧ ¬ O₃ ≤ O₁` | **the collar branch of the separation family** — closest to (D5′) among the literature forms, though (D5′) quantifies over all regions rather than relativising to a given outer region. Weaker than (D8)/(D9)/(D15): no closure, no distance. The repository proves the exact strength of its own clause (`exists_orthogonal_iff_not_subset`), namely that on `Finset α` it is equivalent to strict inclusion — which is (X15) direction 1 rediscovered | same | working tree, 2026-08-15 |
| this repository | `ProperContainment.ofThicken` and the `Finset ℤ` 1-neighbourhood instance | **stronger than the class** — the literature's separation is recovered by a buffer layer, at model level | same | working tree, 2026-08-15 |
| this repository | `LocalNet`, `VonNeumannNet`, `LocalNet.Covariance` | consuming structures; `Covariance` is an automorphism group of a fixed index set, **unrelated to (D-categorical)** — no functor from a category of spacetimes exists here | same | working tree, 2026-08-15 |
| this repository | could not find: a causal-complement operation, causal completeness, Haag duality, additivity, spacelike cones, or any DHR material at index-set level | — | same | working tree, 2026-08-15 |
| Mathlib | order-theoretic substrate only: `Disjoint`, `SetRel`, `SimpleGraph`, `Metric.AreSeparated`, `Metric.thickening`, `closure`/`interior` | **substrate**; nothing expresses a causal-disjointness relation on a poset | `lean_local_search`, `Grep` over `.lake/packages/mathlib`, `lean_leansearch`, `lean_loogle`, `lean_leanfinder` | mathlib rev `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |
| Mathlib | could not find: an abstract orthogonality relation on an order with the heredity axiom, causal structure, Lorentzian geometry, or anything AQFT-shaped | — | same queries | mathlib rev `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |
| Lean, outside Mathlib | `physlib`: `Lorentz.Vector.causallyUnrelated`, `causalDiamond`, `CausalCharacter` | **substrate at event level** for (D-concrete); no regions, no index set, no AQFT net | web and repository search | 2026-08-15 |
| Lean, outside Mathlib | an orthomodular-lattice development was reported but not retrieved | (D-complement)-shaped, tier (d) | web search | 2026-08-15 |
| Isabelle AFP | Schutz's Minkowski axioms; GNS; no-faster-than-light entries | **event-level substrate**; the index set is absent | AFP topic index and entry pages | 2026-08-15 |
| Coq/Rocq | could not find any causal index set or AQFT net, having searched the mathcomp and CoqQ indices and general web queries | — | web searches | 2026-08-15 |
| any system | could not find a formalization of Haag–Kastler nets over a causal index set, nor of causal-set structure carrying a *disjointness* rather than a causal *order* | — | web searches, Lean Zulip site-scoped queries | 2026-08-15 |

## Open questions

- (R19) versus (R1): does the failure of directedness deny the quasi-local algebra, or can it be circumvented? The reconciliation lives in an unfetched Fredenhagen article. **This is the corpus's most consequential unresolved disagreement.**
- (A5)/(R15): whether a substitute for a net tending spacelike to infinity exists over a compact Cauchy surface — [GLRV99]'s own stated open problem.
- (A22): whether the wedges of a spherically symmetric spacetime separate spacelike points; neither a proof nor a failing spacetime could be produced.
- Whether (D3)'s neighbourhood-buffered ⊥ and (D17)'s closure-based ⊥ are equivalent; no source in the corpus compares them, and (R4)'s proof consumes the buffer.
- Whether the ordering theorem's hypothesis (T) is the weakest such condition, and whether it has a purely order-theoretic surrogate — the adopted form cannot state (T).
- (R63): which field theories [DL84] §§9–10 exhibits as non-split; those pages were not converted.
- (R22): a funnel-property counterexample at a checkable tier; the corpus's only pointer is unfetchable, and (R39)'s alternative rests on a private communication.

## Sources

**Append-only.**

| Key | Work | Status | Cache | Version | Tier reached | Retrieved |
|---|---|---|---|---|---|---|
| HM06 | H. Halvorson, M. Müger, *Algebraic Quantum Field Theory*, in *Handbook of the Philosophy of Physics*, arXiv math-ph/0602036 | retrieved (arXiv LaTeX, verbatim) | `references/arxiv-math-ph-0602036/` | arXiv | a | 2026-08-15 |
| GLRV99 | D. Guido, R. Longo, J. E. Roberts, R. Verch, *Charged sectors, spin and statistics in quantum field theory on curved spacetimes*, arXiv math-ph/9906019 | retrieved (arXiv LaTeX, verbatim) | `references/arxiv-math-ph-9906019/` | arXiv | a | 2026-08-15 |
| NAA13 | P. Naaijkens, *Quantum spin systems on infinite lattices*, arXiv 1311.2717 | retrieved (arXiv LaTeX, verbatim) | `references/arxiv-1311.2717/` | arXiv | a | 2026-08-15 |
| BGL93 | R. Brunetti, D. Guido, R. Longo, *Modular structure and duality in conformal quantum field theory*, arXiv funct-an/9302008 | retrieved (arXiv LaTeX, verbatim) | `references/arxiv-funct-an-9302008/` | arXiv | a | 2026-08-15 |
| BFV01 | R. Brunetti, K. Fredenhagen, R. Verch, *The generally covariant locality principle*, arXiv math-ph/0112041 | retrieved (arXiv LaTeX, verbatim) — **the cache holds two complete document bodies; all locators here are from the first** | `references/arxiv-math-ph-0112041/` | arXiv | a | 2026-08-15 |
| KOE03 | S. Köster, *Structure of Coset Models*, dissertation, arXiv math-ph/0308031 | retrieved (arXiv LaTeX, verbatim) | `references/arxiv-math-ph-0308031/` | arXiv | a | 2026-08-14 |
| dB74 | D. Buchholz, *Product states for local algebras*, Comm. Math. Phys. 36 (1974) 287–304 | retrieved **partial** — pp. 1–8 of 18 via MinerU; p. 292 additionally cross-checked against the PDF's own text layer with `pypdf`, independently of MinerU | `references/buchholz-1974-product-states/` | published | b | 2026-08-14 |
| DL84 | S. Doplicher, R. Longo, *Standard and split inclusions of von Neumann algebras*, Invent. Math. 75 (1984) 493–536 | retrieved **partial** — pp. 1–14 of 44 (§0–§4) via MinerU | `references/doplicher-longo-1984-standard-split/` | published | b | 2026-08-14 |
| HAAG | R. Haag, *Local Quantum Physics* | not retrieved — not attempted this run | — | — | d | 2026-08-15 |
| ROB76 | J. E. Roberts, *Local cohomology and superselection structure*, Comm. Math. Phys. 51 (1976) | not retrieved — not attempted this run | — | — | d | 2026-08-15 |
| BW-NETS | H. Baumgärtel, M. Wollenberg, *Causal Nets of Operator Algebras* — [GLRV99]'s cited treatment of nets over posets with a causal-disjointness relation | not retrieved — not attempted this run | — | — | d | 2026-08-15 |
| BF82 | D. Buchholz, K. Fredenhagen, *Locality and the structure of particle states*, Comm. Math. Phys. 84 (1982) — the source of the spacelike-cone index set | not retrieved — not attempted this run | — | — | d | 2026-08-15 |
| HOR | S. S. Horuzhy, *Introduction to Algebraic Quantum Field Theory* — [HM06]'s pointer to funnel-property counterexamples | not retrieved — not attempted this run | — | — | c | 2026-08-15 |
| FRED93 | K. Fredenhagen, *Global observables in local quantum physics* — the reconciliation of (R1) with (R19) | not retrieved — not attempted this run | — | — | d | 2026-08-15 |
| DHR | S. Doplicher, R. Haag, J. E. Roberts, *Local observables and particle statistics* I, II | not retrieved — not attempted this run | — | — | d | 2026-08-15 |

Further works cited by the corpus and not retrieved (Schlieder, Brown, Verch, Keyl, Borchers, Hislop–Longo, Dimock, Longo, Buchholz–Schulz-Mirbach, Buchholz–Wichmann, Buchholz–D'Antoni, Yngvason, Guido–Longo–Wiesbrock, Fredenhagen–Gabbiani, Fredenhagen–Jörß, Summers, Araki, Sakai, Kay–Wald): every claim through them carries a substitution sentence and no locator. One of them — [BGL93]'s attribution of (R39) to Buchholz — is a *private communication*, so no locator can ever exist for it.

## Not investigated

- **The `[ext]` gap.** Lane 5 swept only the formalization landscape; **no lane checked any external mathematical result**. The refutation pass fetched none. Every one of the external edges above — Fredenhagen's global-observables construction (which decides the (R1)/(R19) disagreement), Horuzhy's funnel counterexamples, Schlieder, Brown, Verch, Keyl, Hislop–Longo, Longo, Buchholz–Wichmann, Summers, and the DHR papers — remains unexamined, so (R19), (R22), (R24), (R29), (R34), (R35), (R46), (R49) and the external legs of (R3) rest entirely on attestations.
- **Unconverted pages.** dB74 pp. 9–18, including the proof underlying (R60); DL84 pp. 15–44, including the §§9–10 non-split field theories of (R63).
- **No page-image comparison was possible** — `pdftoppm`, `pdftotext`, `mutool` and `gs` are all absent from this container — so **no MinerU quote reaches tier (a)**. dB74's p. 292 was cross-checked against the PDF's own text layer, which removes the MinerU-inference risk for that passage only; DL84 was not cross-checked at all.
- **Spacelike cones** are named as an index set by [GLRV99] and [NAA13] and **defined by neither**; [HM06] defers to an unfetchable source. No (D#) row exists for them and none can be written from this corpus, so whether the cone index set is an instance of the adopted form is **unverified**, not covered.
- **[GLRV99] Ch. 5's labelled geometric assumptions** (a), (b), (c), (c′) were read only as far as (A19) and (A22) required — the single largest gap in the hypothesis lane. [KOE03]'s coset and subnet machinery and [NAA13]'s lattice chapters were swept only for index-set statements.
- **Degeneracy probes skipped**: whether (T) is preserved under passing to `𝒦̃`-style conformal orbits in general; whether ⊥̃ and ⊥̂ can be separated on a *corpus* index set (they coincide on `S¹` and fail together on the sieve poset — the only separating object found was constructed for the purpose); closure-separation versus positive distance for unbounded regions.
- **Errata found but not chased**: [GLRV99]'s Extension-Theorem proof cites Lemma 3.A.4 where 3A.5 is needed, and prints three spellings of one label; its Lemma 3.6 says `dimension $\geq 2$` and then treats dimension two as the remaining case; [BGL93] Thm 3.3's proof cites a Lemma 3.4 that does not exist; [BFV01]'s `cf.\ condition $(ii)$` points at orientation-preservation where causal convexity is condition (i), **in both document bodies, so authorial rather than a conversion artefact**.
- **Not opened**: HS17 (`references/arxiv-1702.04924/`), cached from a previous run and outside this corpus.
