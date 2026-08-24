---
object: Lieb's concavity theorems for trace functions, and the triple-matrix trace inequality
slug: lieb-concavity-inequality
status: draft
worst-tier: b
mathlib-rev: 5450b53e5ddc75d46418fabb605edbf36bd0beb6
implemented-as: Matrix.lieb_joint_concavity_general
revisions:
  - 2026-08-23 · eb92563 · initial extraction · sources: LIE73, LR73, TRO11, RUS02, RUS04, CL08, EFF09, NP05, CFL14, HIA13, ZHA18, HIA18, KW20
  - 2026-08-23 · working tree · implemented-as set to Matrix.lieb_joint_concavity_general after the general-region formalization and its math review; prior-art row for this repository annotated
---

<!--
No document-level macro preamble: no definition form survives from one math span
to the next in the renderers this note has to work in. Everything the note says
in its own voice is plain KaTeX.

Every verbatim quote below is in a fenced block or backticks rather than a
`\gdef`-carrying math span, and the reason is not a macro this note declined to
define. Two reasons, both of which put the quotes in the "cannot be \gdef'd at
all" case of the format spec:

  * LIE73 and LR73 quotes are 1973-typescript **OCR output** (`£` for `≤`,
    Cyrillic `К` for `K`, `p` for `ρ`, `c9^(H)` for `S_1(H)`). They are not
    LaTeX at all, so there is no macro to define; typesetting them is
    impossible without editing the bytes, which the quote check forbids.
  * The arXiv quotes are clipped **fragments** of LaTeX — trailing commas,
    half-open `\begin{eqnarray}`, line-broken displays. A substitution macro
    cannot close an unbalanced environment.

Source macro catalogue (name[arity] = body, source, file:line) — recorded for a
reader reconstructing a quote, not injected anywhere:
  \tr      = \mathrm{tr}          RUS02, references/arxiv-quant-ph-0205064/raw/main.tex
  \dg      = \dagger              RUS02, raw/main.tex:36
  \raw     = \rightarrow          RUS02, raw/main.tex
  \mtx[1]  = {\bm{#1}}            TRO11, references/arxiv-1101.1070/raw/macro-file.tex:194
  \trace   = \operatorname{tr}    TRO11, raw/macro-file.tex:210
  \coll[1] = {\mathscr{#1}}       TRO11, raw/macro-file.tex:139
  \Tr      = \mathrm{Tr}          ZHA18 / HIA13 (by \def), reconstructed
  \Tr, \supp, \ket, \bra          KW20 — unrecoverable (private \documentclass), reconstructed
  \hnp, \Pn, \phx                 CL08 / CFL14 / ZHA18 — positive-matrix cones, reconstructed
-->

# Lieb's concavity theorems for trace functions, and the triple-matrix trace inequality

## What this object is for

Lieb's 1973 paper proves that certain traces built from powers of positive
operators are concave, and derives from them a three-operator substitute for the
Golden–Thompson inequality. The concavity statements are what make the quantum
relative entropy jointly convex and the von Neumann entropy strongly
subadditive; the trace inequality is the step that converts Klein's inequality
into strong subadditivity. The generality that matters is threefold: the
exponents are two free parameters constrained only by their sum, the operator
$K$ conjugating the two arguments is arbitrary (and in the 1973 statement need
not even be bounded), and the ambient space is a Hilbert space rather than a
matrix algebra.

## Definition

### Variants as the sources write them

The corpus splits along five axes. The grid is a derived index — it carries no
tier and no locator, and where it disagrees with a block below, the grid is
wrong.

| (D#) | Source | variables | exponent constraint | where $K$ sits / what is assumed of it | domain cone | dimension |
|---|---|---|---|---|---|---|
| (D1) | [LIE73] Thm 1 | one | $p+r\le 1$ | inner, **unbounded allowed** | positive | any |
| (D2) | [LIE73] Cor 1.1 | two | $p+r\le 1$ | inner, bounded | positive | any |
| (D3) | [LIE73] Cor 1.2 | two, outer power $q$ | $p+r\le 1$, $0<q\le 1/s$ | inner, bounded | positive | any |
| (D8) | [RUS02] `eq:WYD` | two | $=1$, open interval | inner | strictly positive | finite by fiat |
| (D11) | [EFF09] Cor 2.4 | two | $=1$, $0<s<1$ | inner | strictly positive | finite |
| (D12) | [EFF09] Cor 3.3 | two | $p+q\le 1$ | inner | positive | finite |
| (D13) | [CL08] Lem `al` | two, **tensor, no trace, no $K$** | $0\le p\le r\le 1$ | absent | semidefinite | finite |
| (D14) | [CL08] Rem `requiv`, Lem `equiv` | two | any real $s,t$ | all-$K$ ⟺ $K=I$ ⟺ tensor | semidefinite | finite |
| (D15) | [CFL14] $\Phi_{p,q,s}$, Thm `conc` | two, outer power $s$ | **iff** $0\le p,q\le 1$, $0\le s\le 1/(p+q)$ | inner; $q$ on the **outer** argument | positive definite | finite |
| (D15a) | [CFL14] Lem `equiv` | one ⟺ two | any $p,q,s$ | all-$K$ / unitary / $K=I$ | positive definite | finite |
| (D16) | [ZHA18] $\Psi_{p,q,s}$, Thm A | two, outer power $s$ | complete region, $p\ge q$ | inner, **invertible**; $p$ on the outer argument | positive definite | finite |
| (D16a) | [ZHA18] Lem `Lieb-Ando` | two | $=1$, $0<p\le 1$ | inner, invertible | positive definite | finite |
| (D17) | [KW20] Thm `thm:lieb-concavity` | two | $=1$, $t\in(0,1)$ | **outermost**, arbitrary | semidefinite | finite by fiat |
| (D4) | [LIE73] Thm 6 | one, logarithm | — | $L$ self-adjoint, additive | strictly positive | finite (§IV extends) |
| (D4a) | [LR73] §III(B) | one, logarithm | — | $K$ additive | positive, by continuity | any |
| (D9) | [RUS02] Thm `exp.conc` | one, logarithm | — | $K$ self-adjoint matrix, additive | strictly positive | finite by fiat |
| (D10) | [TRO11] Thm `thm:lieb` | one, logarithm | — | $H$ self-adjoint matrix, additive | positive definite | finite |
| (D5) | [LIE73] Thm 7 | three | — | — | self-adjoint exponents | finite |
| (D5a) | [LIE73] Rem after Thm 7 | three | — | — | self-adjoint exponents | finite |
| (D6) | [LR73] (2.4) | three | — | — | positive, hypotheses **unstated** | any |
| (D7) | [RUS02] Thm `cor:trip.gold` | three | — | — | $R,S,T>0$ stated | finite by fiat |
| (D18)–(D21) | [LIE73] WYD, Thm 8, Cor 6.1/Thm 9, the Conjecture | companions | see blocks | — | — | — |

#### The WYD-type trace concavity

**(D1) [LIE73] Theorem 1, RCP25 preprint printed p. `III - 5 -`** — tier (b),
`mineru-cross-checked-against-PDF-text-layer`

Let $K$ be a linear operator on $H$, not necessarily bounded; let $A, B$ be
positive; let $0<\lambda<1$ and $C = \lambda A + (1-\lambda)B$; let $p, r > 0$
with $p + r \equiv s \le 1$. If $M \equiv C^{p/2} K C^{r/2}$ has an extension to
the Hilbert–Schmidt class, then $A^{p/2} K A^{r/2}$ and $B^{p/2} K B^{r/2}$ do
too, and
$\lambda \operatorname{Tr} A^{r/2} K^{\dagger} A^{p} K A^{r/2} + (1-\lambda) \operatorname{Tr} B^{r/2} K^{\dagger} B^{p} K B^{r/2} \le \operatorname{Tr} C^{r/2} K^{\dagger} C^{p} K C^{r/2}$.

```
positive real numbers with p + r s s £ 1 .If M = CP^2 К СГ^2 has
```

```
A € fi+(H) н Tr Ar/2  Kt Ap KA r/2 is  concave.
```

[tr.] "`A` positive $\mapsto \operatorname{Tr} A^{r/2}K^{\dagger}A^{p}KA^{r/2}$
is concave"; `s s £ 1` is $\equiv s \le 1$, and the OCR has substituted a
Cyrillic `К` for `K` throughout. Note
$\operatorname{Tr} A^{r/2} K^{\dagger} A^{p} K A^{r/2} = \lVert A^{p/2}KA^{r/2}\rVert_2^2$,
which is how the hypothesis on $M$ and the displayed trace are made consistent.

**(D2) [LIE73] Corollary 1.1, printed p. `III - 8 -`** — tier (b),
cross-checked

With $p, r$ as in Theorem 1, the map
$(A,B,K) \mapsto F(A,B,K) = \operatorname{Tr} A^{r/2} K^{\dagger} B^{p} K A^{r/2}$
on positive $\times$ positive $\times$ bounded is jointly concave in $(A,B)$ and
convex in $K$.

```
(1) is jointly concave in (A,B)
```

`differs from (D1) by:` $A^p$ becomes $B^p$, one variable becomes two, and $K$
is now required bounded. LIE73 proves it from (D1) by a direct-sum construction
on $H \oplus H$.
`sources claim equivalence:` yes — [CFL14]'s Lemma `equiv` lists the
one-variable diagonal form and the two-variable form as equivalent for every
$s$, and credits the $s=1$ case of that equivalence to Lieb 1973. **The joint
two-variable form is therefore not a modern reformulation; it is one corollary
after Theorem 1 in the 1973 paper**, and it is what [CL08], [ZHA18] and [KW20]
cite when they say "Lieb's concavity theorem".

**(D3) [LIE73] Corollary 1.2, printed p. `III - 8 -`** — tier (b),
`mineru-unchecked`

$F_q(A,B,K) = \{\operatorname{Tr} A^{r/2}K^{\dagger}B^{p}KA^{r/2}\}^{q}$ with
$p+r \equiv s \le 1$ is jointly concave in $(A,B)$ for $0 < q \le 1/s$, jointly
convex for $q<0$, and convex in $K$ for $q \ge 1/2$.
`differs from (D2) by:` an outer power. This is LIE73's own anticipation of the
$s$ parameter of (D15)/(D16) — but note the symbol collision recorded at (C6):
LIE73's $s$ is the **sum** and its outer power is $q$, while [CFL14] and [ZHA18]
call the **outer power** $s$.

**(D8) [RUS02] §"Lieb's convex trace functions", display `eq:WYD`** — tier (a)

```
(A,B) \raw \tr \, A^s K^{\dg} B^{(1-s)} K
```

with $0 < s < 1$. `differs from (D2) by:` the exponents sum to exactly $1$; $s$
is confined to the open interval; the domain is strictly positive.
`sources claim equivalence:` not addressed — RUS02 introduces it as what the
WYD conjecture "is equivalent to", and states that equivalence without proof.

**(D11) [EFF09] the corollary after Corollary 2.4** — tier (a)

```
F(A,B)=\mathrm{Trace}\,A^{s}K^{*}B^{1-s}K
```

```
is jointly concave on the strictly positive $n\times n$ matrices $A,B$.
```

`differs from (D8) by:` nothing mathematical — the same statement in $*$ rather
than $\dagger$ notation, over matrices.

**(D12) [EFF09] Corollary 3.3, "Lieb's extension of Corollary 2.4"** — tier (a)

```
(A,B)\mapsto \mathrm{Trace}\,A^{q}X^{*}B^{p}X
```

```
is jointly concave on the positive $n\times n$ matrices.
```

for $0 < p, q$ with $p + q \le 1$. `differs from (D11) by:` two independent
exponents with sum $\le 1$, and the domain relaxed to positive.
`sources claim equivalence:` yes, and constructively — EFF09 is the only corpus
source that *derives* the $\le 1$ form from the $=1$ form, and it needs extra
machinery (its Maréchal-perspective Theorem 3.2) to do it. So the two are
inter-derivable in finite dimensions, at a cost.

**(D13) [CL08] the lemma labelled `al` in §2** — tier (a)

```
\medskip \begin{lm}\label{al} The map $$(A,B) \mapsto A^p\otimes B^{1-r}$$
```

```
(Lieb's concavity theorem).
```

The full statement: this map on semidefinite pairs is jointly convex for
$1 \le r \le p \le 2$ (Ando's convexity theorem) and jointly concave for
$0 \le p \le r \le 1$ (Lieb's concavity theorem).
`differs from (D2) by:` it is a statement of **operator** concavity of a tensor
product, with no trace and no $K$. Exponent translation: CL08's $(p, 1-r)$ with
$0 \le p \le r \le 1$ is LIE73's $(p, r)$ with $p + r \le 1$.

**(D14) [CL08] Remark `requiv` and Lemma `equiv`** — tier (a)

CL08 asserts, and argues, that the convexity/concavity of
$(A,B) \mapsto \operatorname{tr} A^{p}K^{*}B^{1-r}K$ for all $K$ is equivalent
to (D13), the difference being

```
merely notational.
```

by vectorising $K$, so that
$\operatorname{tr} A^{p}K^{*}B^{1-r}K = \langle K^{\mathrm{vec}}, (A^{p}\otimes B^{1-r})K^{\mathrm{vec}}\rangle$;
and Lemma `equiv` extends this to $\operatorname{tr}(A^{s}B^{t})$ for **any**
real $s,t$. `sources claim equivalence:` yes, proved — but by a
finite-dimensional argument. CL08's own release of the dimension restriction is
an assertion with no proof (see (C10)).

**(D15) [CFL14] $\Phi_{p,q,s}$, $\Psi_{K,p,q,s}$ and Theorem `conc`** — tier (a)

```
\Phi_{p,q,s}(A,B) = \tr[ (A^{q/2}B^p A^{q/2})^s]\ .
```

```
\tr[ (A^{q/2}K^* B^p
```

```
K A^{q/2})^s]\ ,
```

(the definition is quoted in two spans because the flattener the quote check
greps collapses runs of spaces, and the source writes `B^p  K` with two)

```
The trace function $\Phi_{p,q,s}(A,B)$ is jointly concave if and only if
```

```
$0\leq p,q \leq 1$ and $0\leq s \leq 1/(p+q)$.
```

`differs from (D2)/(D3) by:` a three-parameter family with an **iff** region on
the interior of the cone. The $s = 1$ slice of the concavity region is
$p + q \le 1$, which is exactly (D2), and CFL14 credits that slice to Lieb.

**(D15a) [CFL14] Lemma `equiv`, "Equivalent formulations"** — tier (a)

Five statements are equivalent for fixed $p,q,s$: joint convexity of
$\Psi_{K,p,q,s}$ for all $K$ and all $n$; the same for unitary $K$; the $K=I$
case $\Phi_{p,q,s}$; and

```
{\rm(4)} The map $ A\mapsto \Psi_{K ,p,q,s}(A,A) $ is
```

convex for all $K$ and all $n$; and the same for unitary $K$. "The same is true
if convex is replaced by concave in all statements."

```
equivalence of (1) and (4) is in \cite{Lieb73} and
```

`sources claim equivalence:` yes, proved. **This is the decisive definitional
fact of the note**: the one-variable/two-variable axis is a *phrasing* axis, not
a strength axis. The caveat is dimensional — see (X6) and (O3): CFL14's proof
runs the reductions through a $2n \times 2n$ embedding, so at fixed $n$ only the
trivial implications are established.

**(D16) [ZHA18] $\Psi_{p,q,s}$ and Theorem A** — tier (a)

```
\Psi_{p,q,s}(A,B)=\Tr(B^{\frac{q}{2}}K^*A^{p}KB^{\frac{q}{2}})^s,~~p,q,s\in \mathbb{R},
```

for positive definite $A,B$ and any fixed **invertible** $K$. Theorem A: with
$p \ge q$ and $s>0$, jointly concave if $0 \le q \le p \le 1$ and
$0 < s \le 1/(p+q)$; jointly convex if $-1 \le q \le p \le 0$ and $s>0$; jointly
convex if $-1 \le q \le 0$, $1 \le p \le 2$, $(p,q) \ne (1,-1)$ and
$s \ge 1/(p+q)$.
`differs from (D15) by:` **$A$ and $B$ exchange which exponent they carry.**
CFL14 puts $q$ on the outer argument, ZHA18 puts $p$ on it. The concavity
regions are symmetric in $p,q$ so the swap is invisible there; it is *not*
invisible in the convexity regions. ZHA18 also requires $K$ invertible where
CFL14 allows any $K$.

```
which states that $\Psi_{p,q,1}$ is jointly concave for all $0\le p,q\le1,p+q\le 1$ and for all $K$
```

**(D16a) [ZHA18] Lemma `lem:Lieb-Ando`** — tier (a)

```
$$\Psi_{p,1-p,1}(A,B)=\Tr K^*A^p KB^{1-p},~~A,B\in\ph^{\times},$$
```

jointly concave for $0 < p \le 1$ (Lieb), jointly convex for $-1 \le p < 0$
(Ando). `differs from (D8) by:` the concavity range **includes** the endpoint
$p=1$, and the companion convexity range is stated in the same breath. ZHA18
makes this the reduction target: the whole $(p,q,s)$ family collapses onto it.

**(D17) [KW20] Theorem `thm:lieb-concavity`, "Lieb Concavity"** — tier (a)

```
The following function is jointly concave with respect to positive semi-definite operators $R$ and $S$ for arbitrary $t\in(0,1)$ and an arbitrary operator $K$
```

```
(R,S)\mapsto \Tr[KR^{t}K^{\dag}S^{1-t}].
```

`differs from (D8) by:` the domain is semidefinite; the adjoint has migrated so
that $K$ is leftmost and $K^{\dagger}$ innermost; finite dimensions are a
standing assumption by fiat. KW20 proves it.

#### The $\operatorname{Tr}\exp(L + \log A)$ concavity

**(D4) [LIE73] Theorem 6, printed p. `III - 22 -`** — tier (b), the frame
cross-checked, the display `mineru-unchecked`

```
Theorem 6 : Let L £ fi S(H) be fixed . Then the
```

Read: $L$ bounded self-adjoint fixed; $A \mapsto \operatorname{Tr}\exp(L + \ln A)$
is concave on the **strictly positive** operators. MinerU dropped the `s` and
`++` superscripts; the OCR text layer carries the `s`, and the two witnesses
jointly carry the `++`. Stated inside §III, which is finite-dimensional by
declaration, and extended to infinite dimensions in §IV — under a hypothesis
that is *incompatible* with bounded $L$ there; see (C5) and (R24).

**(D4a) [LR73] §III(B) and the second inequality of (2.3)** — tier (b),
cross-checked

```
C|—^Tr[exp (K 4- In C) ] for positive C applied to
```

`differs from (D4) by:` the domain is stated as **positive**, not strictly
positive, with a separate appeal to continuity. LR73 records the attribution
chain: Uhlmann showed strong subadditivity follows from this concavity, Lieb
proved the concavity, Epstein found an alternate proof.

**(D9) [RUS02] Theorem `exp.conc`** — tier (a)

```
$A \mapsto F(A) = \tr \, e^{K + \log A}$ is concave in $A > 0$.
```

for any fixed self-adjoint matrix $K$. `differs from (D4) by:` `ln` written
`log`, with no base stated — see (C4), where this is the one axis in the note
that changes a truth value.

**(D10) [TRO11] Theorem `thm:lieb`, "[Lieb]"** — tier (a)

```
\mtx{A} \longmapsto \trace \exp\left( \mtx{H} + \log \mtx{A} \right)
```

```
is concave on the positive-definite cone.
```

`differs from (D9) by:` letter names only. TRO11 cites this to Lieb's Theorem 6
and calls (D1) "Lieb's main concavity theorem" — the clearest instance of the
naming collision recorded at (C12).

#### The triple-matrix inequality

**(D5) [LIE73] Theorem 7, printed p. `III - 25 -`** — tier (b), cross-checked

```
Theorem 7 : Let A,B,C g JJ S(H) .
```

[tr.] "Let $A,B,C$ be bounded self-adjoint". Then
$\operatorname{Tr} e^{C}\, T_{\exp(-A)}(e^{B}) \ge \operatorname{Tr} e^{A+B+C}$,
where $T_{\alpha}(K) = \int_{0}^{\infty}(\alpha + x)^{-1} K (\alpha + x)^{-1}\,dx$;
and if $A$ commutes with $B$ this reduces to Golden–Thompson. MinerU rendered
the hypothesis without the self-adjointness superscript; the OCR layer restores
it, and **that restoration is what makes (D5), (D6) and (D7) one statement**
rather than three.

**(D5a) [LIE73] the Remark after Theorem 7** — tier (b), `mineru-unchecked` for
the display

For $A, C, D$ bounded self-adjoint,
$\operatorname{Tr} e^{C}e^{D} \ge \operatorname{Tr}\exp\bigl[C + A + \ln \int_{0}^{1} e^{-As} e^{D} e^{-A(1-s)}\,ds\bigr]$,
obtained from $T_{\exp(-A)}(e^{B}) \equiv e^{D}$ and the inversion formula
$T_{A}^{-1}: K \mapsto \int_{0}^{1} A^{x} K A^{1-x}\,dx$.

**(D6) [LR73] display (2.4), printed p. `III - 41 -`** — tier (b), quoted from
the OCR layer

```
Tr[exp(ln B -In C + In D) ] s Tr / B (C+xl)" 1 D(C+xH) _1 dx. (2.4)
```

[tr.] $\operatorname{Tr}\exp(\ln B - \ln C + \ln D) \le \operatorname{Tr}\int_{0}^{\infty} B (C+x)^{-1} D (C+x)^{-1}\,dx$.
`differs from (D5) by:` parametrised by positive operators under logarithms
instead of self-adjoint exponents, and written with $\le$. **LR73 prints no
hypotheses on $B, C, D$ at all.**

**(D7) [RUS02] Theorem `cor:trip.gold`, "(Lieb)"** — tier (a)

```
\tr \, e^{\log R - \log S + \log T} \leq
```

with the right-hand side
$\operatorname{tr}\int_{0}^{\infty} R (S+uI)^{-1} T (S+uI)^{-1}\,du$, "For any
$R, S, T > 0$". `differs from (D6) by:` the hypothesis is now stated
explicitly.
`sources claim equivalence:` no — **no corpus source performs the substitution
that identifies (D5) with (D6)/(D7)**. The identification is this note's, and
the argument is written out at (R20). It is legitimate only because LIE73's
$A,B,C$ are self-adjoint, which is exactly the fact the conversion destroyed.

#### Companion statements in the same 1973 paper

**(D18) [LIE73] the WYD section, printed pp. `III - 12/13 -`** — tier (b),
`mineru-unchecked`. For self-adjoint $K$ and $0<p<1$,
$S_p(\rho,K) \equiv \tfrac12 \operatorname{Tr}[\rho^{p},K][\rho^{1-p},K]$, whose
negative is Wigner–Yanase's skew information; the WYD conjecture is concavity of
$S_p(\cdot,K)$ in the state. Rewritten,
$S_p(\rho,K) = -\operatorname{Tr}\rho K^{2} + \operatorname{Tr}\rho^{1-p}K\rho^{p}K$,
whose second term is (D1). LIE73 remarks that Theorem 1 is *stronger than
necessary* because it allows $K$ non-self-adjoint, and that polarisation reduces
the non-self-adjoint case to the self-adjoint one **only at $p = 1/2$**. ZHA18
states the same object, tier (a):

```
S_p(\rho,K):=\frac{1}{2}\Tr[\rho^p,K][\rho^{1-p},K]=-\Tr\rho K^2+\Tr\rho^{p}K\rho^{1-p} K,
```

**Caution.** Both LIE73 extractions render $\rho$ as `p` through this passage,
so the sentence stating the conjecture reads "concave in p". The correct reading
— concave in $\rho$, for fixed $K$ and fixed $p$ — is confirmed by RUS02 and
ZHA18, not by LIE73's own bytes.

**(D19) [LIE73] Theorem 8** — tier (a) for the hypothesis line (clean ASCII
matching the prose), (b) for the display

```
Theorem 8 : Let K ∈ B(H) and 1 ≥ p > 0, 1 ≥ r > 0 be fixed. Then the
```

$F(A) = \operatorname{Tr} A^{-p} K^{\dagger} A^{-r} K$ is convex on the strictly
positive operators. `differs from (D1) by:` negative exponents, and **no
constraint on the sum** — each of $p,r$ is separately in $(0,1]$, so the sum may
reach $2$. LIE73 calls Theorems 8 and 9 "a side issue ... independent of and
simpler than Theorem 1"; CFL14 and ZHA18 both cite it as the source of the
region $-1 \le p,q < 0$.

**(D20) [LIE73] Corollary 6.1 and Theorem 9** — tier (b), `mineru-unchecked`.
$F_q(A_1,\dots,A_k) = \{\operatorname{Tr}\exp[L + \sum_j p_j \ln A_j]\}^{q}$ with
$\sum_j p_j \equiv s \le 1$, jointly concave for $0 < q \le 1/s$ and jointly
convex for $q \le 0$; and with a **minus** sign,
$F_q = \{\operatorname{Tr}\exp[L - \sum_j p_j \ln A_j]\}^{q}$ with $s$
unconstrained, jointly convex for $q \ge 0$ and jointly concave for
$-1/s \le q \le 0$. The sign difference is not a transcription slip: the
convexity pattern is the opposite one.

**(D21) [LIE73] the Conjecture after Corollary 6.2, printed p. `III - 24 -`** —
tier (b), quoted from the OCR layer

```
function Tr (B 1/n A 1/n ) n is  concave in A € Ô+(H) .
```

LIE73 arrives at it by noting $n=1$ is linear, $n=2$ is Theorem 1, and
$n=\infty$ is Theorem 6 by Trotter. **It is a conjecture in the source and it is
no longer open** — see (X9): it is Epstein's theorem in disguise, which the
refutation pass established by an explicit reduction. Anyone writing the
"obvious" common generalisation of (D2) and (D4) will be writing this statement,
so the reduction is worth having in front of them.

### Adopted general form

**The concavity half.** Let $H$ be a complex Hilbert space, $K$ a bounded
operator on $H$, and $p, r > 0$ real with $p + r \le 1$. Then the map
$$(A,B) \longmapsto \operatorname{Tr} A^{r/2} K^{\dagger} B^{p} K A^{r/2}$$
is jointly concave on pairs of positive operators, valued in $[0,+\infty]$ under
the convention that the trace of a positive non-trace-class operator is
$+\infty$ (C3). Equivalently — and this is an equivalence the literature
proves, not one this note asserts — the one-variable diagonal
$A \mapsto \operatorname{Tr} A^{r/2} K^{\dagger} A^{p} K A^{r/2}$ is concave,
and there $K$ need only be a densely defined linear operator, subject to (A5).
When one wants the *conclusion* that $A^{p/2}KA^{r/2}$ is Hilbert–Schmidt and
not merely the inequality, the hypothesis (A4) that $C^{p/2}KC^{r/2}$ extends to
a Hilbert–Schmidt operator is required and is not removable.

This is (D2), with (D1) as its equivalent one-variable phrasing. The choice of
$p + r \le 1$ over the $p + r = 1$ of (D8)/(D11)/(D16a)/(D17) is justified by
**(X5) generality loss**: the restricted form drops the whole region
$p + r < 1$, and although [EFF09] does derive the general case from the boundary
case, it needs machinery beyond the boundary statement to do it. The choice of
the two-variable phrasing over the tensor form (D13) is *not* a generality
decision — (X6) records that they are equivalent, and only in finite
dimensions is that equivalence proved. The choice of $s = 1$ (no outer power)
rather than the full $\Psi_{p,q,s}$ family costs no generality either: (R46)
shows the whole three-parameter family reduces back to this statement.

**The inequality half.** Let $A, B, C$ be bounded self-adjoint operators on a
**finite-dimensional** $H$. Then
$$\operatorname{Tr} e^{A+B+C} \;\le\; \operatorname{Tr} \int_{0}^{\infty} e^{C}\,(e^{-A}+u)^{-1}\, e^{B}\,(e^{-A}+u)^{-1}\,du ,$$
equivalently, for positive definite $R, S, T$,
$$\operatorname{Tr} e^{\log R - \log S + \log T} \;\le\; \operatorname{Tr}\int_{0}^{\infty} R\,(S+u)^{-1}\,T\,(S+u)^{-1}\,du ,$$
the two being one statement under $S = e^{-A}$, $T = e^{B}$, $R = e^{C}$.

This is (D5) = (D6) = (D7). **The finite-dimensionality is a hole, not a
choice.** §III of [LIE73] is finite-dimensional by declaration and its §IV
extends Theorem 6 and only Theorem 6; [RUS02], the only source that proves the
inequality in full, is finite-dimensional by fiat. In infinite dimensions with
bounded self-adjoint $A,B,C$ both sides are $+\infty$, so the statement is true
and empty, and for unbounded $A,B,C$ the corpus is silent. Recorded as (A8) and
(O2). The resolvent form is not cosmetic: (X1) exhibits an explicit
one-parameter family on $2\times 2$ matrices for which the naive
$\operatorname{Tr} e^{A+B+C} \le \operatorname{Tr} e^{A}e^{B}e^{C}$ fails, and
that is the whole reason the inequality is stated with an integral.

## Notation and conventions

| (C#) | Axis | This note | Per source | Translation |
|---|---|---|---|---|
| (C1) | conjugate-linear argument of the inner product | second argument linear | [LIE73] explicit: linear in the second, conjugate-linear in the first. No other source states it; [KW20] leaves it implicit in bra–ket notation and it is load-bearing in its proof | — |
| (C2) | adjoint symbol | $\dagger$ | $\dagger$: [LIE73], [LR73], [RUS02], [KW20]. $*$: [CL08], [CFL14], [ZHA18], [EFF09], [HIA13] | purely notational; recorded so no quote is silently normalised |
| (C3) | trace normalisation | unnormalised, valued in $[0,+\infty]$ | unnormalised in every source. **[LIE73] additionally fixes $\operatorname{Tr} A = \infty$ for positive non-trace-class $A$** | the convention is load-bearing for (A4), (A14), (A19) |
| (C4) | base of the logarithm | $e$ | [LIE73], [LR73] write `ln`. [RUS02], [TRO11], [CL08] write `log` with **no base stated**; a search of all arXiv sources for "natural logarithm", "base", `log_2`, `\log_` found nothing | **This bites.** $\operatorname{Tr}\exp(H + \log_b A)$ is concave in $A^{1/\ln b}$, not in $A$, so the (D4)/(D9)/(D10) family is false as written unless the base is $e$. It does **not** bite the WYD family, which has no logarithm |
| (C5) | positive vs strictly positive | positive for the WYD half, strictly positive for the logarithmic half | [LIE73] defines both pointwise, so its "strictly positive" is *weaker* than invertibility in infinite dimensions. Closed cone: [LIE73] Thm 1, [CL08], [KW20], [EFF09] Cor 3.3, [RUS04]. Open cone: [CFL14], [ZHA18], [RUS02], [EFF09] Cor 2.4. Third, strictly stronger: $\varepsilon \le A \le \omega$ in [LIE73] §IV Case 1 | the logarithmic and negative-power statements *require* the interior; the WYD ones do not, and LIE73 reaches the semidefinite case inside the proof by splitting off $\ker C$ |
| (C6) | the letter $s$, and which argument carries which exponent | $p, r$ for the two exponents, $s = p+r$; no outer power | $s$ is the **sum** in [LIE73] (which also writes $B^{s}(H)$ for the self-adjoint part); a single **exponent** in [RUS02], [EFF09]; the **outer power** in [CFL14], [ZHA18], [HIA13]. And [CFL14] and [ZHA18] **swap which argument carries $p$ and which $q$** | a cited "$s \le 1$" is meaningless without the paper it came from; the two exponent tables are transposes and must be transposed before comparison |
| (C7) | sum of exponents | $\le 1$ | $=1$: [RUS02], [EFF09] Cor 2.4, [KW20], [ZHA18]'s reduction lemma. $\le 1$: [LIE73], [EFF09] Cor 3.3, [CL08], and the $s=1$ slices of [CFL14], [ZHA18]. Endpoints differ: $0<s<1$ ([RUS02], [KW20]), $0<p\le1$ ([ZHA18]), $0\le p\le r\le1$ ([CL08]), $p,r>0$ ([LIE73]) | a strength difference, not a translation; [EFF09] Cor 3.3 is where the reduction lives |
| (C8) | what is assumed of $K$ | bounded in the two-variable form; densely defined in the one-variable form | unbounded allowed: [LIE73] Thm 1. Bounded: [LIE73] Cor 1.1/1.2, [CL08], [KW20]. Invertible: [ZHA18]. Any matrix, reduced to invertible by density: [CFL14]. Absent: [CL08]'s tensor form | LIE73's is the strongest form in the corpus; every matrix source is a specialisation |
| (C9) | the triple-matrix inequality's parametrisation and direction | positive operators under logarithms, written $\le$ | self-adjoint exponents with $\ge$: [LIE73]. Positive operators under logarithms with $\le$: [LR73], [RUS02] | $B = e^{C}$, $C = e^{-A}$, $D = e^{B}$; the resolvent integral is on the larger side in both. Sub-convention: the resolvent measure is $dx$ on $[0,\infty)$ in all three, with three different letters. [LIE73] additionally gives the spectral form $T_A : \{K_{ij}\} \mapsto \{K_{ij} f(A_i,A_j)\}$ with $f(x,y) = (x-y)^{-1}\ln(x/y)$, $f(x,x) = x^{-1}$, and the inversion $T_A^{-1}: K \mapsto \int_0^1 A^{x}KA^{1-x}dx$ |
| (C10) | dimension | stated per result | infinite from the start: [LIE73] §II, [LR73]. Finite by declaration then extended: [LIE73] §III with §IV. Finite by fiat, never extended: [RUS02], [KW20]. Finite with an unproved release: [CL08] — "as none of them refers to the dimension, it is easy to extend them ... and we take this for granted" | the release is an assertion; CL08 gives no proof, and the vectorisation equivalences (D14), (D15a) are proved only finite-dimensionally |
| (C11) | order symbols | Löwner order | $A>0$, $A \ge 0$ in [RUS02], [CFL14], [ZHA18], [LIE73]. [TRO11] introduces a dedicated $\succ$ for the positive-definite order. [CL08] uses set membership instead | no source uses an order symbol for containment of algebras, so that ambiguity does not arise here |
| (C12) | what "Lieb's concavity theorem" denotes | **nothing, uniquely** | the logarithmic statement (D4): [TRO11], which calls the WYD statement "Lieb's main concavity theorem". The WYD joint concavity: [CL08], [ZHA18], [KW20]. No name: [RUS02] (which names (D7) "Lieb's golden corollary"), [EFF09], [CFL14]. [HIA18] says "the Wigner-Yanase-Dyson-Lieb concavity" and states nothing | both attributions are historically correct — both statements are Lieb 1973. A reader who takes the name from one source and a locator from another assembles a false statement |
| (C13) | the relative entropy in the modern proofs | Umegaki's, no affine term | [TRO11] uses $D(X;Y) = \operatorname{trace}(X\log X - X\log Y - (X-Y))$, i.e. Umegaki **plus** $\operatorname{Tr}Y - \operatorname{Tr}X$ | recorded because this note sits next to [[umegaki-relative-entropy]] and the two differ by exactly that affine term; the $-(X-Y)$ is what makes TRO11's variational formula come out with a $+X$ on the right |

## Results and dependencies

### (R1) [LIE73] Theorem 1 — the main WYD concavity theorem

The statement of (D1). Source: [LIE73] Theorem 1, preprint p. `III - 5 -` ·
tier (b) `mineru-cross-checked-against-PDF-text-layer` · **proved in source**,
in full, for infinite-dimensional $H$.

- Depends on: `[ext: BS55/KR36]`, `[ext: MAXMOD]`.
- Conventions: (C3), (C5), (C6), (C8), (C10).
- Proof route:
  1. Reduce to $C > 0$ — operator concavity of $A \mapsto A^{p}$ for
     $0 < p \le 1$ gives $\lambda A^{p} \le C^{p}$, so
     $\alpha(q) \equiv A^{q/2}C^{-q/2}$ extends boundedly to $(\ker C)^{\perp}$
     with norm at most $\lambda^{-1/2}$, and traces computed in a basis adapted
     to $\ker C \oplus (\ker C)^{\perp}$ kill the $\ker C$ terms. Consumes
     `[ext: BS55/KR36]`.
  2. Rewrite the claim as an inequality between Hilbert–Schmidt pairings for
     every $M$ in the Hilbert–Schmidt class.
  3. Complexify: $\alpha(z) = A^{z/2}C^{-z/2}$ is uniformly bounded and regular
     on the strip $0 \le \operatorname{Re} z \le 1$ because $C^{iy/2}$ is
     unitary and $\lVert A^{iy/2}\rVert \le 1$; weak analyticity upgrades to
     norm analyticity.
  4. Apply the maximum modulus principle on the strip. Consumes
     `[ext: MAXMOD]`.
  5. On the boundary line, use cyclicity of the trace and
     $\lvert \operatorname{Tr} BC\rvert \le \tfrac12 \operatorname{Tr} B^{\dagger}B + \tfrac12\operatorname{Tr}C^{\dagger}C$.
  6. Close with $\lambda A^{s} + (1-\lambda)B^{s} \le C^{s}$. Consumes
     `[ext: BS55/KR36]` again.
- Restatements of the same result, one row with a `Conventions:` flag:
  [ZHA18] as $\Psi_{p,q,1}$ jointly concave (tier (a)); [EFF09] Corollary 3.3
  (tier (a)); [CL08] Lemma `al` in tensor form (tier (a)); [CFL14] §2, which
  records the sufficiency as `sufficient in \cite[Theorem 1]{Lieb73}` — a
  locator into the **published** paper, quoted from CFL14 and not checked here.
- The bound $p+r \le 1$ is sharp; see (R43), (R45), (R46) and (A2).

### (R2) The `exponents-sum-to-one` form

For $0 < t < 1$ and any $K$,
$(R,S) \mapsto \operatorname{Tr}[K R^{t} K^{\dagger} S^{1-t}]$ is jointly
concave. Filed separately from (R1) because it is strictly weaker and because
every source below states it in that restricted form and calls it *the* Lieb
concavity theorem.

- Sources, all tier (a): [RUS02] `eq:WYD` — **cited to [LIE73], not proved**,
  and attributing the conjecture to Baumann rather than Wigner–Yanase–Dyson;
  [ZHA18] Lemma 3.1 — **cited**, to Lieb for concavity and Ando for convexity;
  [EFF09] Corollary 2.4 — **proved in source**; [KW20] `thm:lieb-concavity` —
  **proved in source, in full**.
- Depends on: `[ext: BHA-OPCONV]`, `[ext: HPJ]` (the EFF09 route); nothing
  external for the KW20 route, which uses an operator Jensen inequality KW20
  proves itself.
- Proof route (EFF09, the shortest in the corpus):
  1. $f(t) = -t^{s}$ is operator convex for $0<s<1$. Consumes
     `[ext: BHA-OPCONV]`.
  2. Hence the perspective $g(L,R) = Rf(L/R) = -L^{s}R^{1-s}$ is jointly convex
     on commuting positive $L,R$ — EFF09's Theorem 2.2, from
     Hansen–Pedersen–Jensen. Consumes `[ext: HPJ]`.
  3. On matrices with the Hilbert–Schmidt pairing, take $L(X) = AX$ and
     $R(X) = XB$; these commute, and
     $-\operatorname{Tr} A^{s}K^{*}B^{1-s}K = \langle g(L,R)(K^{*}), K^{*}\rangle$.
- Proof route (KW20, independent): write the trace as a quadratic form in the
  vectorisation of $K$ against $g(S^{T}\otimes R^{-1})$ with
  $g(x) = x^{1-t}$ operator concave; choose $G_0, G_1$ with
  $G_0^{\dagger}G_0 + G_1^{\dagger}G_1 = 1$; apply the operator Jensen
  inequality (internal to KW20); compute the resulting argument; extend from
  positive definite to semidefinite by $R + \varepsilon$.
- (R1) implies (R2). The converse is not immediate: [EFF09] needs its
  Maréchal-perspective Theorem 3.2 to get from Corollary 2.4 to Corollary 3.3.

### (R3) Equivalence of the tensor form, the trace form, and the $K = I$ form

Two independent statements, both tier (a), both **proved in source**.
[CL08] Lemma `equiv` in §5: for any real $s,t$, concavity/convexity of
$(A,B) \mapsto \operatorname{Tr}(A^{s}B^{t})$ is equivalent to operator
concavity/convexity of $(A,B) \mapsto A^{s}\otimes B^{t}$.
[CFL14] Lemma `equiv`: the five formulations of (D15a) are equivalent for fixed
$p,q,s$.

- Depends on: nothing external — algebra plus a unitary dilation.
- Proof route: the $K = I$ direction is CL08's vectorisation remark; the
  converse reduces to unitary $K$, then dilates a contraction $K = U\lvert K\rvert$
  to a unitary on $H \oplus H$ and uses
  $\operatorname{Tr}(A^{s}KB^{t}K^{*})$ computed on the doubled space.
- CFL14 records the provenance: the one-variable/two-variable half is LIE73's
  own, and the $K = I$ half is Carlen–Lieb's.
- **This row is what licenses treating the one-variable, two-variable and
  tensor forms as one theorem** — in finite dimensions only.

### (R4) [LIE73] Corollary 1.1 — the $H \oplus H$ doubling device

The statement of (D2). Tier (b), `mineru-unchecked` for the display, structure
cross-checked. **Proved in source**, in four lines.

- Depends on: (R1).
- Proof route: on $H \oplus H$ define $k : (x,y) \mapsto (0,Kx)$ and
  $a : (x,y) \mapsto (Ax,By)$; apply (R1) to
  $\operatorname{Tr} a^{r/2}k^{\dagger}a^{p}k a^{r/2}$, which yields the joint
  concavity; convexity in $K$ follows from a Cauchy–Schwarz argument, $F$ being
  nonnegative and quadratic in $K$.

### (R5) [LIE73] Corollary 1.2 — powers of the WYD trace function

The statement of (D3). Tier (b), `mineru-unchecked`. **Proved in source.**

- Depends on: (R4).
- Proof route: (R4) supplies a nonnegative concave $F$, homogeneous of order
  $s$ on a convex cone; for such an $F$ the level sets are convex and $F^{q}$ is
  concave for $0 < q \le 1/s$.
- Cross-reference, not an edge: the same homogeneity device is reused at (R9),
  (R11), (R17) and (R23), and appears in [CL08]'s Remark `r1` with the level
  sets spelled out.

### (R6) [LIE73] Corollary 1.3 — the partial-trace / Haar-averaging form

Let $H^{2}$ have finite dimension $d_2$, $A_{12}$ positive trace class,
$A_1$ its partial trace, $p+r = s \le 1$, and $L = K \otimes 1$. Then an
inequality holds between $d_2^{1-s}$ times the trace over $H^{1}$ and the trace
over $H^{12}$. Tier (b), `mineru-unchecked` (the conversion of this statement is
heavily mangled). **Proved in source.**

- Depends on: (R1), `[ext: UHL72]`.
- Proof route: represent $A_1 \otimes 1 / d_2$ as a Haar average of unitary
  conjugations over the unitary group of $H^{2}$ (consumes `[ext: UHL72]`);
  apply (R1) to get $F$ of the average at least the average of $F$; note $F$ is
  independent of the unitary.
- The source records that **Theorem 1 is a special case of Corollary 1.3**, via
  $d_2 = 2$ and $A_{12} = \tfrac12 A \otimes P^{a} + \tfrac12 B \otimes P^{b}$.
  So (R1) and (R6) are mutually derivable — an early instance of (R25).

### (R7) [LIE73] display (2.5) — the WYD subadditivity conjecture

Subadditivity of the WYD skew information in a two-system form. Tier (b),
`mineru-unchecked`. **Proof status: asserted as an open conjecture.**

```
We do not have a proof of this, but when
```

- Depends on: (R6), for the special cases only.

### (R8) [LIE73] Theorem 2 — joint convexity of $\operatorname{Tr} A^{-r}K^{\dagger}A^{-p}K$

For $p, r \ge 0$ with $p + r \le 1$, $(A,K) \mapsto \operatorname{Tr} A^{-r}K^{\dagger}A^{-p}K$
is jointly convex on strictly positive $\times$ bounded. Tier (b),
`mineru-cross-checked` for the enclosing sentence, signs `mineru-unchecked`.
§III is finite-dimensional throughout. **Proved in source.**

- Depends on: (R1).
- Proof route: regard the bounded operators as a Hilbert space under
  $\langle K,K'\rangle = \operatorname{Tr}K^{\dagger}K'$; the map is a positive
  definite quadratic form in $K$; maximise the variational quotient between the
  convex combination and the value at the mean; invert the Euler equations to
  express the extremisers as $\gamma^{-1}A^{p}MA^{r}$; multiply by
  $M^{\dagger}$, trace, and read off $\gamma \le 1$ **from (R1)**.

### (R9) [LIE73] Corollary 2.1 — powers of (R8)

For $p,r \ge 0$, $p+r \equiv s \le 1$, $q \ne 0$:
$(A,B,K) \mapsto (\operatorname{Tr} A^{-p}K^{\dagger}B^{-r}K)^{q}$ is jointly
convex when $q \ge (2-s)^{-1}$. Tier (b), `mineru-unchecked`. **Proved in
source**, by the (R5) device, the function being homogeneous of order $2-s$.

- Depends on: (R8), (R5).
- **Consumer, 41 years later:** [CFL14]'s proof of its Theorem 4.2 uses exactly
  this, citing `Corollary 2.1` of the published paper — see (R44).

### (R10) [LIE73] Theorem 3 — joint convexity of the double-resolvent integral

$Q(A,K) = \operatorname{Tr}\int_0^{\infty}(A+x)^{-1}K^{\dagger}(A+x)^{-1}K\,dx$
is jointly convex on strictly positive $\times$ bounded. Tier (b),
`mineru-cross-checked` for the header, formula `mineru-unchecked`. **Proved in
source.**

- Depends on: (R1), (R8).
- Proof route: as for (R8) up to the eigenvalue equation, which becomes
  $\gamma T_A(K) = T_C(\lambda K + (1-\lambda)L)$; invert $T_A$ by the explicit
  formula $T_A^{-1}: K \mapsto \int_0^1 A^{x}KA^{1-x}dx$, verified in an
  eigenbasis; multiply by $M^{\dagger}$ and apply (R1) to get $\gamma \le 1$.
- Conventions: (C9). $T_A^{-1}$ is the Kubo–Mori operator.

### (R11) [LIE73] Corollary 3.1 — powers of (R10), all four sign regimes

$Q_q(A,B,K) = (\operatorname{Tr}\int_0^{\infty}(A+x)^{-1}K^{\dagger}(B+x)^{-1}K\,dx)^{q}$
is jointly convex in $(A,B,K)$ for $q \ge 1$; convex in $K$ for $q \ge 1/2$;
jointly convex in $(A,B)$ for $q>0$; jointly concave in $(A,B)$ for
$-1 \le q < 0$ and $K \ne 0$. Tier (b), `mineru-unchecked`. **Proved in
source.**

- Depends on: (R10), (R4), (R5).
- Proof route: (R10) supplies the convexity of $Q_1$; the $H \oplus H$ device of
  (R4) replaces $A$ by $(A,B)$; $Q_1$ is
  homogeneous of order $-1$ in $(A,B)$ by the change of variable $x \to \lambda x$
  and of order $1$ in $(A,B,K)$; the first two parts reuse the (R5) device, the
  last two use the reciprocal gauge, which is positive, concave and homogeneous
  of order one.

### (R12) [LIE73] identities (3.6)–(3.9) and Proposition 4 — the derivative calculus

All proved in source. Tier (b), `mineru-unchecked` for the formulas,
`mineru-cross-checked` for Proposition 4's header. In particular
$\log A = \int_0^{\infty}(1+x)^{-1}(A-1)(A+x)^{-1}dx$;
$\frac{d}{dx}\log(A+xK)\big|_{0} = T_A(K)$;
$\frac{d^{2}}{dx^{2}}\log(A+xK)\big|_{0} = -R_A(K)$ with $R_A(K)$ positive for
$K \ne 0$; and Proposition 4,
$0 \le R_A(\gamma K + A) = 1 + 2\gamma T_A(K) + \gamma^{2}R_A(K)$.

- Depends on: nothing beyond elementary calculus.
- **Recorded negative result**, stated and refuted in the source: the
  proposition $R_A(K) \ge T_A(K)^{2}$ is **false**, witnessed by
  $A = \operatorname{diag}(a,b)$ with $a>b>0$ and $K$ the $2\times2$ flip. The
  source adds that Theorem 6 would be trivial if it were true.

### (R13) [LIE73] Lemma 5 — the homogeneous-convex derivative inequality

Let $\mathcal{C}$ be a convex cone, $F$ convex on it, right-differentiable with
$G(A,B) = \lim_{x \downarrow 0} x^{-1}\{F(A+xB) - F(A)\}$, and homogeneous of
order $1$. Then $G(A,B) \le F(B)$; and conversely, under two-sided
differentiability, measurability of $x \mapsto G(A+xB,B)$, $G(A,B) \le F(B)$ and
homogeneity, $F$ is convex. Tier (b), `mineru-cross-checked`. **Proved in
source, both directions, in six lines.**

- Depends on: nothing.
- Proof route: forward, $F(A+xB) = (1+x)F(\frac{A + xB}{1+x}) \le F(A) + xF(B)$
  by convexity and homogeneity, then divide and let $x \downarrow 0$. Converse,
  integrate $G$ along the segment.
- **Provenance disagreement inside the corpus.** [LIE73] proves this itself and
  cites Rockafellar only as a pointer; [RUS02] credits Rockafellar alone;
  [CL08] cites Rockafellar for a *third*, different result. Restated by [LR73]
  §III E), attributed there to Lieb.

### (R14) [LIE73] display (3.12) — the mixed $T$/$R$ trace inequality

$-\operatorname{Tr} B\,R_A(K) + 2\operatorname{Tr} M\,T_A(K) \le \operatorname{Tr} M\,T_B(M)$.
Tier (b), `mineru-unchecked`. **Proved in source.**

- Depends on: (R10), (R12), (R13).
- Proof route: $Q(A,K) = \operatorname{Tr}K^{\dagger}T_A(K)$ is homogeneous of
  order $1$ and convex by (R10); its directional derivative is
  $-\operatorname{Tr}B R_A(K)$ by (R12); feed both into the forward half of
  (R13).

### (R15) Concavity of $A \mapsto \operatorname{Tr}\exp(L + \log A)$ — [LIE73] Theorem 6, the hub

The statement of (D4). Tier (b) for [LIE73],
`mineru-cross-checked-against-PDF-text-layer` for the self-adjointness of $L$.
**Proved in source.**

- Depends on: (R14). Transitively, through (R14): (R12) and (R1).
- Conventions: (C4) — the base must be $e$; (C5); (C10).
- Proof route (LIE73's own): fix $A$ strictly positive and $K$ self-adjoint and
  put $f(x) = \operatorname{Tr}\exp(L + \log(A+xK))$; concavity is equivalent to
  $f''(0) \le 0$; use
  $\frac{d}{dx}e^{F+xG}\big|_{0} = \int_0^1 e^{yF}Ge^{(1-y)F}dy = T_{\exp F}^{-1}(G)$;
  compute
  $f''(0) = -\operatorname{Tr}B R_A(K) + \operatorname{Tr}T_A(K)\,T_B^{-1}[T_A(K)]$
  with $B = \exp(L + \log A)$; apply (R14) with $M = T_B^{-1}[T_A(K)]$.
- Restatements, one row with a `Conventions:` flag: [RUS02] `exp.conc` (tier
  (a), **proved in its Appendix A** by Epstein's argument); [TRO11] `thm:lieb`
  (tier (a), **proved in source**); [LR73] uses it unnamed.
- Alternative proof route A — Epstein's, as reproduced in [RUS02] Appendix A,
  tier (a) for the reproduction: analytically continue $g(z) = \operatorname{tr}e^{K+\log(zA+B)}$;
  show it maps the upper half plane to itself (consumes `[ext: SPECMAP]`); use
  the Herglotz integral representation (consumes `[ext: HERGLOTZ]`); change
  variables and differentiate under the integral sign. **A strictness error in
  that appendix is recorded at (X10).**
- Alternative proof route B — [TRO11]'s, from joint convexity of the relative
  entropy: rearrange Klein's inequality into the variational formula
  $\operatorname{tr}Y = \max_{X>0}\operatorname{tr}(X\log Y - X\log X + X)$; put
  $Y = \exp(H + \log A)$; observe the bracket is jointly concave in $(A,X)$ by
  joint convexity of the relative entropy; apply (R16). Consumes (R16), (R38),
  (R36). **This route reverses the classical order**, consuming what was
  historically derived from this theorem. TRO11 adds that the same identity
  exhibits $H \mapsto \operatorname{tr}\exp(H+\log A)$ as a Fenchel conjugate,
  hence convex in $H$.

### (R16) Partial minimisation/maximisation preserves convexity/concavity

Three independent statements, one row, all tier (a) and all **proved in
source**. [CL08] Lemma `rock`: the infimum over $y$ of a jointly convex
$f(x,y)$ is convex, and dually. [ZHA18] Lemma 3.2: strictly stronger, in two
parts — a supremum of functions each convex in $x$ is convex, needing no joint
convexity, whereas the infimum statement does. [TRO11] `prop:partial-max`: the
concave/max half only, with the maximum assumed attained.

- Depends on: nothing.
- The asymmetry matters downstream: part (1) is cheap, part (2) is substantive,
  and [CFL14]'s Theorem 4.2 turns on exactly that distinction.

### (R17) [LIE73] Corollary 6.1 — the $k$-fold weighted-log form

The concavity/convexity statement of (D20)'s first half. Tier (b),
`mineru-unchecked`. **Proved in source**, with the source flagging the
surprise that joint concavity in $k$ variables "seems like a stronger result
than Theorem 6 but, surprisingly, it is not".

- Depends on: (R15), (R5), (R12).
- Proof route: reduce to $q = 1$ by the (R5) homogeneity device; show the
  $k \times k$ Hessian at $0$ is negative semidefinite, its off-diagonal terms
  controlled by Cauchy–Schwarz for the pairing $T_B^{-1}$, whose positivity and
  symmetry come from (R12), and its diagonal by (R15); assemble, using
  $s \le 1$ **only at the last step**.

### (R18) [LIE73] Corollary 6.2 — the rank-one limit

With $p_1,\dots,p_k$ as in (R17) and $\Psi$ a unit vector,
$(A_1,\dots,A_k) \mapsto \exp[\sum_j p_j (\Psi, \log A_j\, \Psi)]$ is concave.
Tier (b), `mineru-cross-checked` for the header. **Proved in source**, by taking
$e^{L}$ to the rank-one projection in (R17).

- Depends on: (R17).

### (R19) [LIE73] — the Trotter-limit statement $\operatorname{Tr}(B^{1/n}A^{1/n})^{n}$

The statement of (D21). Tier (b), `mineru-unchecked`. **Proof status in the
source: asserted as a conjecture.** The motivation is a genuine dependency:
writing $B = e^{L}$, Trotter gives $F_L(A) = \lim_n \operatorname{Tr}(B^{1/n}A^{1/n})^{n}$,
where $n=1$ is linear, $n=2$ is concave by (R1), and the limit is concave by
(R15).

- Depends on: (R1), (R15), `[ext: TROTTER]`.
- **No longer open.** (X9) records the reduction that identifies it with
  Epstein's theorem, which [CL08] states and [HIA13] proves.

### (R20) The triple-matrix inequality — [LIE73] Theorem 7 = [LR73] (2.4) = [RUS02] `cor:trip.gold`

**One row, three source displays**, because the three are the same statement
under an invertible change of variables. Statements as (D5), (D6), (D7).
[LIE73] tier (b) `mineru-cross-checked-against-PDF-text-layer` for the
self-adjointness hypothesis; [LR73] tier (b); [RUS02] tier (a) and **proved in
source**.

- Depends on: (R15), (R13), (R12), `[ext: LOGINT]`.
- Conventions: (C9).
- The translation is this note's own argument, tier inherited (b): put
  $S = e^{-A}$, $T = e^{B}$, $R = e^{C}$ — legitimate because [LIE73]'s
  $A,B,C$ are self-adjoint and $R,S,T$ are then positive. Then
  $\log R - \log S + \log T = A+B+C$, and [RUS02]'s right-hand side is
  $\operatorname{Tr} e^{C}T_{\exp(-A)}(e^{B})$. **[RUS02]'s "minus sign on the
  middle term" is exactly [LIE73]'s $\exp(-A)$ inside the resolvent**, and the
  minus-sign form is not modern: it is [LR73]'s (2.4) in the 1973 preprint.
- Proof route ([LIE73]'s): put $\alpha = e^{-A}$, $\beta = e^{B}$, $L = A+C$;
  the map $\alpha \mapsto -\operatorname{Tr}e^{L+\log\alpha}$ is homogeneous of
  order $1$ and convex, convex because (R15) says the un-negated map is
  concave; apply the forward half of (R13) at $\alpha$ in the direction $\beta$;
  identify the derivative as $\operatorname{Tr}e^{C}T_{\alpha}(\beta)$ using
  (R12); in the commuting case $T_{\alpha}(\beta) = e^{A}e^{B}$.
- Proof route ([RUS02]'s, more explicit at the derivative step): apply (R13) to
  (R15) with $K = \log R - \log S$; substitute the integral representation
  $\log(S+xT) - \log S = \int_0^{\infty}(S+u)^{-1}xT(S+xT+u)^{-1}du$, which
  RUS02 calls well known and does not cite (consumes `[ext: LOGINT]`, which is
  in fact [LIE73]'s own (3.7)/(3.8)); expand to first order in $x$.
- [LIE73] notes that Theorem 7 gives an alternative proof of Golden–Thompson,
  so (R20) implies (R21.1).

### (R21) Golden–Thompson, and the falsity of its naive three-operator analogue

**(R21.1)** $\operatorname{Tr}e^{A+B} \le \operatorname{Tr}e^{A}e^{B}$ for
self-adjoint $A,B$. [LIE73] display (3.14), tier (b), **cited elsewhere** — to
Golden, to Thompson, and for the infinite-dimensional extension to Ruskai 1972.
[RUS02] `thm:gold`, tier (a), **strictly stronger** and **proved in source in
outline**, adding equality iff $A$ and $B$ commute.

- Depends on, as **citation** edges of the statement rather than steps of any
  route read here: `[ext: GOL65]`, `[ext: THO65]`, `[ext: RUS72]` (what [LIE73]
  cites), and `[ext: PETZ88]` (a derivation [RUS02] mentions and does not carry
  out). The one route below consumes `[ext: SCHATTEN-MONOTONE]` and
  Cauchy–Schwarz.
- Proof route (RUS02's): $\operatorname{tr}[e^{A/2^{k}}e^{B/2^{k}}]^{2^{k}}$ is
  monotone decreasing in $k$ with limit $\operatorname{tr}e^{A+B}$ (consumes
  `[ext: SCHATTEN-MONOTONE]`); the $k=1$ step is Cauchy–Schwarz for the
  Hilbert–Schmidt pairing; the equality case of Cauchy–Schwarz forces the
  exponentials to commute.

**(R21.2)** The naive three-operator analogue is false. [LIE73], tier (b),
**asserted, no counterexample given**:

```
The obvious generalization of GT to three opera
```

[RUS02], tier (a), the same claim with an absolute value — a genuinely stronger
falsity claim — and a pointer to an unretrieved book:

```
fails; see, for example, Problem~20 on pages 512--513
```

- Depends on: `[ext: HJ91]`, tier (c).
- **This note supplies the missing witness** at (X1), which makes the external
  edge dispensable.

### (R22) [LIE73] Theorem 7, alternative formulation

The statement of (D5a). Tier (b), `mineru-unchecked`. **Proved in source**, in
one line, from the definition of $T$ and the inversion formula.

- Depends on: (R20), (R10).

### (R23) [LIE73] Theorem 8, Corollary 8.1 and Theorem 9 — the elementary branch

Theorem 8 is (D19). Corollary 8.1: for $1 \ge p, r > 0$, $p + r \equiv s$,
$q \ne 0$, $(A,B,K) \mapsto (\operatorname{Tr}A^{-p}K^{\dagger}B^{-r}K)^{q}$ is
convex in $K$ for $q \ge 1/2$, jointly convex in $(A,B)$ for $q>0$, jointly
concave for $-1/s \le q < 0$. Theorem 9 is (D20)'s second half. Tier (b),
`mineru-cross-checked` for all three headers. **Proved in source, and
explicitly independent of (R1)** — "a side issue ... independent of and simpler
than Theorem 1".

- Depends on: (R12), (R11), and an integral representation of $A^{p}$ for
  $0 < p < 1$.
- Proof route (Theorem 8): show $g(x) = F(A+xL)$ has $g''(0) \ge 0$; relate the
  first and second derivatives of $A(x)^{\pm p}$ through
  $A(x)^{p}A(x)^{-p} = 1$; every term is nonnegative once the second derivative
  of $A(x)^{p}$ is nonpositive, which follows from the integral representation
  together with (R12)'s (3.8).
- Proof route (Theorem 9): reduce to $k = q = 1$ by (R11)'s device; the second
  derivative is $-p\operatorname{Tr}BR_A(K) + p^{2}\operatorname{Tr}T_A(K)T_B^{-1}[T_A(K)]$
  with $B = \exp(L - p\log A)$; close with positivity of $R_A(K)$ and of the
  $T_B^{-1}$ pairing, both from (R12).
- Recorded remark: $A \mapsto A^{-p}$ is not convex for $p>1$, but
  $A \mapsto \operatorname{Tr}A^{-p}$ is convex for $2 \ge p > 0$.
- **Consumer:** [CFL14] §2 records that the sufficiency of its convexity
  condition at $s = 1$ was proved in Lieb's Theorem 8.

### (R24) [LIE73] §IV — Theorem 6 in infinite dimensions

With $L$ self-adjoint, $e^{L}$ trace class, and $C = \lambda A + (1-\lambda)B$,
the concavity inequality holds in three successive cases: $\varepsilon < A,B < \omega$
(**proved**); $0 < A, B \le \omega$ (**proved**, with the trace defined as a
decreasing limit); and $A,B$ positive and possibly unbounded with $\log A$,
$\log B$ form-bounded perturbations of $-L$ (**asserted, attributed to a private
communication from B. Simon, not proved**). Tier (b), `mineru-cross-checked` for
the section heading.

- Depends on: (R15), `[ext: MINIMAX]`, `[ext: DOMCONV]`.
- Proof route (Case 1): compress by the spectral projections of $L$, set
  $A_n = P_nAP_n + \varepsilon(1-P_n)$; the residual terms cancel from both
  sides, leaving a finite-dimensional inequality true by (R15); pass to the
  limit by dominated convergence for eigenvalues, using the min-max principle
  and compactness of the resolvent (consumes `[ext: MINIMAX]`,
  `[ext: DOMCONV]`).
- Hypotheses: (A10)–(A13). **§IV extends Theorem 6 and only Theorem 6**, which
  is the hole in the inequality half of the adopted form.

### (R25) [LIE73] §V — the mutual-implication claim among Theorems 1, 2, 3, 6, 7

A meta-result about the skeleton: if an independent proof of any of Theorems 2,
3, 6, 7 were found, the others could be derived from it, **when $H$ is
finite-dimensional**. Tier (b), `mineru-cross-checked`. **Proof status:
sketched** — the section calls itself "formally heuristic" and leaves details to
the reader. Note that **the conversion dropped the §V heading entirely**; only
the OCR layer carries it.

- Depends on: (R1), (R8), (R10), (R13), (R14), (R15), (R20).
- The edges claimed: $1 \Rightarrow 2$ and $1 \Rightarrow 3 \Rightarrow 6 \Rightarrow 7$
  already established; then $2 \Rightarrow 1$ by reading Theorem 2's proof
  backwards; $7 \Rightarrow 6$ by the **converse half of (R13)**;
  $6 \Rightarrow (3.12)$ by minimising over $M$; $(3.12) \Rightarrow 3$ as
  before; and $3 \Rightarrow 2$ by an integration in the parameters plus
  continuity at $p+r = 1$.
- The source's own caveat, which anyone quoting the equivalence is also
  quoting:

```
It is a truism of logic that two true theorems, however dis
```

- **Downstream endorsement**, tier (a): [TRO11] says many convexity and
  concavity theorems for trace functions are mutually derivable, citing §5 of
  [LIE73] and §5 of [CL08]. Both pointers check out — (R25) and (R41).

### (R26) [LR73] Theorem 1 — convexity of $\rho_{12} \mapsto S_1 - S_{12}$

On positive trace-class operators on a tensor product, $\rho_{12} \mapsto S(\rho_1) - S(\rho_{12})$
is convex. Tier (b), cross-checked against the OCR layer. **Proved in source**
(finite dimensions in §II; §IV extends).

- Depends on: (R15), `[ext: KLEIN]`.
- Proof route: reduce to strictly positive arguments by continuity; write the
  claim as nonnegativity of two symmetric terms; apply Klein's inequality with
  the second argument $\exp[\log\rho_1^{a} + \log\rho_{12} - \log\rho_1]$
  (consumes `[ext: KLEIN]`); close with (R15).

### (R27) [LR73] Theorem 2 — strong subadditivity, both forms

For $\rho_{123}$ positive trace class: (i) $S_{123} + S_2 - S_{12} - S_{23} \ge 0$;
(ii) $S_1 + S_3 - S_{12} - S_{23} \le 0$, the second additionally requiring
$\operatorname{Tr}\rho_{123} = 1$. Tier (b), cross-checked. **Proved in
source**, each part separately.

- Depends on: (i) (R20), `[ext: KLEIN]`; (ii) (R26), `[ext: AL70-L3]`.
- Proof route (i): Klein's inequality with the second argument
  $\exp[\log\rho_{12} - \log\rho_2 + \log\rho_{23}]$ (consumes
  `[ext: KLEIN]`); apply (R20) in the (D6) form to the right-hand side; the
  resolvent integral collapses to $\operatorname{Tr}\rho_2$, so the difference
  is at least $\operatorname{Tr}\rho_2 - \operatorname{Tr}\rho_{123} = 0$.
- Proof route (ii): the left side is convex by (R26) applied twice, the partial
  trace being linear; the extremal rays of the positive cone are multiples of
  one-dimensional projections; on those the expression vanishes because
  $S_1 = S_{23}$ and $S_3 = S_{12}$ (consumes `[ext: AL70-L3]`); conclude by
  convexity.
- The normalisation enters exactly once, at $\rho_2^{2} \le \rho_2$ — see (A18)
  and (R33).

### (R28) [LR73] §III — the equivalences, and their limits

Four claims. **A)** Theorem 2 implies Theorem 1, in one sentence, by a
two-dimensional third factor. **B)** Uhlmann's remark: strong subadditivity
follows from the concavity of $C \mapsto \operatorname{Tr}\exp(K+\ln C)$ —
**cited**, so (R15) implies (R27)(i) by a second route. **C)** Theorem 1
implies Theorem 2, and also implies (1.5) directly, via a chain LR73 spells out:
Baumann and Jost showed a special choice implies the joint convexity of the
double-resolvent integral — that is (R10)/(R11) — Lieb showed that implies
(R15), and (R15) was used to prove (R20). **D)** The limitation: the two forms
are **not** equivalent in other contexts, and (1.6) is asserted false in the
classical continuous case, **with no witness supplied**.

- Depends on: (R26), (R27), (R15), (R20), (R10), `[ext: UHL73]`, `[ext: BJ69]`.

### (R29) [LR73] §III D) — the left side of (1.5) is not convex

$\rho_{123} \mapsto S_{123} + S_2 - S_{12} - S_{23}$ is **not** convex, although
the left side of (1.6) is. Tier (b). **Proved in source, with an explicit
witness**: were it convex, a one-dimensional second factor would force
$S_{13} - S_1 - S_3$ to be convex; two orthogonal one-dimensional projections on
a $2 \times 2$ tensor product then give $-2\log 2 < 0$.

- Depends on: nothing. Self-contained.
- A named separating object, and it shows the asymmetry between the two forms of
  (R27) is essential rather than an artefact of the proof.

### (R30) [LR73] §III E) and its Corollary (3.2)

For $\gamma_{12}, \rho_{12}$ positive trace class,
$\operatorname{Tr}\gamma_{12}\log\rho_{12} - \operatorname{Tr}\gamma_1\log\rho_1 \le \operatorname{Tr}\gamma_{12}\log\gamma_{12} - \operatorname{Tr}\gamma_1\log\gamma_1$;
i.e. for fixed $\gamma_{12}$ the left side is maximised at
$\rho_{12} = \gamma_{12}$. Tier (b). **Proved in source.**

- Depends on: (R26), (R13).
- Proof route: the conditional entropy is convex by (R26) and homogeneous;
  apply (R13); compute the directional derivative of the entropy.
- This is monotonicity of relative entropy under partial trace in disguise —
  [RUS02] says Lieb and Ruskai obtained monotonicity *from* strong
  subadditivity by exactly this route.

### (R31) [LR73] §IV and the appendix by B. Simon — entropy convergence

Four statements, all **proved in source** (the appendix is separately
attributed to B. Simon): compressions are dominated in the eigenvalue order,
$PAP \prec A$, and monotonically so; a basic convergence theorem for the entropy
under eigenvalue convergence with a dominating operator of finite entropy; the
same under weak convergence with $A_n \prec A$; and a a dominated-convergence
result for the entropy under the operator order. An example shows the
eigenvalue order and not the operator order is what the second of these needs.
§IV then extends (R26) and (R27) to infinite dimensions by finite-dimensional
compression. Tier (b).

- Depends on: (R26), (R27), `[ext: RITZ]`, `[ext: MINIMAX]`.

### (R32) [RUS02] — the strong subadditivity equality condition

Equality holds in strong subadditivity if and only if
$\log\rho_{123} + \log\rho_2 = \log\rho_{12} + \log\rho_{23}$. Tier (a).
**Proved in source**: the first inequality of the derivation is Klein's, whose
equality condition is exactly this; and when it holds the second inequality
becomes an equality automatically because the traces agree. RUS02 notes the
equality conditions for (R20) itself are harder and are not needed.

- Depends on: (R27), (R38), (R20).

### (R33) [RUS02] — the Araki–Lieb subadditivity inequality

$S(\rho_{123}) \le S(\rho_{12}) + S(\rho_{23})$ under normalisation. Tier (a).
**Proved in source**, by the exact template of the strong subadditivity proof
with Golden–Thompson in place of the triple-matrix inequality.

- Depends on: (R38), (R21.1).
- Proof route: Klein's inequality (R38) with second argument
  $e^{\log\rho_{12}+\log\rho_{23}}$; then (R21.1); then $\rho_2^{2} \le \rho_2$, "which is the *only* place the
  normalization condition is needed".
- Plain subadditivity follows from Klein alone, with equality iff the state is a
  product.

### (R34) [RUS02] — equality in the triple-matrix inequality does not require commutativity

Tier (a). **Proved in source, with a named witness**:

```
One might expect that equality holds if and only if $R,S, T$
```

```
Although this is sufficient, it is not necessary.
```

The witness is $R = \rho_1 \otimes \rho_2 \otimes I$,
$S = I \otimes \rho_2 \otimes I$, $T = I \otimes \rho_{23}$, where both sides
equal $\operatorname{Tr}\rho_1 \otimes \rho_{23}$ even though $T$ commutes with
neither $R$ nor $S$.

- Depends on: (R20).

### (R35) [RUS02] — monotonicity of relative entropy under partial trace

For $\rho_{12}, \gamma_{12} > 0$ with equal traces,
$H(\rho_2,\gamma_2) \le H(\rho_{12},\gamma_{12})$, with equality iff
$\log\rho_{12} - \log\gamma_{12} = I \otimes [\log\gamma_2 - \log\rho_2]$.
Tier (a). **Proved in source.**

- Depends on: (R38), (R20).
- Proof route: Klein with $\log B = \log\gamma_{12} - \log\gamma_2 + \log\rho_2$
  (consumes (R38)); then (R20); the integral collapses by the same computation
  as in (R27)(i) — a cross-reference, not a further edge — and the result
  telescopes.

### (R36) [RUS02] — joint convexity of the relative entropy

$H(\sum_k \lambda_k \rho^{(k)}, \sum_k \lambda_k \gamma^{(k)}) \le \sum_k \lambda_k H(\rho^{(k)},\gamma^{(k)})$,
with equality iff the differences of logarithms agree across $k$. Tier (a).
**Proved in source, twice.**

- Depends on: (R35) for route 1; (R38), (R15) for route 2.
- Proof route 1 (one line): specialise (R35) to block-diagonal arguments,
  reading the partial trace as a sum over blocks.
- Proof route 2 (direct, chosen by RUS02 "since it demonstrates the central role
  of" the logarithmic concavity): Klein with
  $\log B = \log\rho - \log\gamma + \log\gamma^{(k)}$ (consumes (R38));
  multiply by $\lambda_k$ and sum; the second inequality is precisely (R15).
- Also stated tier (a) by [EFF09] as its Corollary 2.3 and **proved from the
  operator convexity of $x\log x$** via its perspective theorem — a third route
  touching none of the Lieb theorems; and by [TRO11] as a Fact attributed to
  Lindblad and *not proved there*, then **consumed by TRO11's proof of (R15)**.

### (R37) [RUS02] — the second equivalence class

With MONO = monotonicity of the relative entropy under stochastic maps,
MPT = (R35), SSA = (R27), JC = (R36): $\mathrm{MONO} \Rightarrow \mathrm{MPT}$
and $\mathrm{MPT} \Leftrightarrow \mathrm{SSA} \Leftrightarrow \mathrm{JC}$,
with Lindblad completing the circuit. Tier (a). **Proved in source edge by
edge, except two cited edges.**

- Depends on: (R27), (R30), (R35), (R36), (R13), `[ext: UHL73]`,
  `[ext: LIN75]`.
- Proof route: MONO to MPT (R35) to SSA (R27) is immediate from RUS02's
  restatement; MPT to JC is the block-diagonal specialisation of (R36); SSA to
  MPT goes through
  convexity of the conditional entropy and then (R13) — RUS02 attributes this
  observation to [LR73], i.e. to (R30); JC to MPT is **cited**, using
  Uhlmann's observation that the partial trace is a convex combination of
  unitary conjugations (consumes `[ext: UHL73]`); JC to SSA directly goes by
  purification and extremality of pure states; MPT to MONO is **cited** to
  Lindblad (consumes `[ext: LIN75]`), though RUS02 also gives the
  Stinespring-style derivation itself.

### (R38) [RUS02] — Klein's inequality with equality conditions

For $A,B > 0$,
$\operatorname{tr}A(\log A - \log B) \ge \operatorname{tr}(A-B)$, with equality
iff $A = B$. Tier (a). **Proof status: cited elsewhere** — RUS02 attributes it
to Klein and does not prove it, while stressing that the equality conditions are
critical downstream.

- Depends on: `[ext: KLEIN]`.
- Also present tier (a) as [TRO11]'s Fact, where it **is proved**, from strict
  convexity of $X \mapsto \operatorname{trace}(X\log X)$.
- **Convention trap:** [KW20]'s Klein inequality is conditional on
  $\operatorname{Tr}\sigma \le 1$, its second argument being only semidefinite.
  RUS02's and TRO11's are not so conditioned. Do not merge.

### (R39) [CL08] Theorem 1.1 — convexity/concavity of three families

With $\Phi_{p,q}$, $\Psi_{p,q}$, $\Upsilon_{p,q}$ as CL08 defines them: for
$1 \le p \le 2$ and $q \ge 1$ all three are convex (jointly, for $\Phi$); for
$0 \le p \le q \le 1$ all three are concave; and for $p > 2$ none is convex or
concave for any $q \ne p$. Tier (a). **Proved in source.**

- Depends on: (R1), (R2), (R3), (R16); and `[ext: AND79]` as a **citation** edge, carrying the convexity half, which no route here reads.
- Proof route: variational formulas for $\Upsilon_{p,q}$ (CL08's lemma `lem1`);
  joint convexity/concavity of an auxiliary two-variable trace (its lemma
  `jcc`), proved by a $2\times2$ block trick reducing to (R1)/(R2) via (R3);
  combine through (R16); transfer to $\Phi$ and $\Psi$; and for $p>2$ a Taylor
  expansion (its lemma `noncon`).
- Attribution recorded by CL08: at $q = 1$ and $0 \le p \le 1$ the concavity of
  $\Upsilon_{p,1}$ "is a theorem of Epstein".

### (R40) [CL08] the Minkowski-type trace inequality, and strong subadditivity from it

For $1 \le q \le p \le 2$ an inequality between iterated partial traces of
powers, reversing for $0 \le p \le 1$. Tier (a). **Proved in source**, from
(R39). Its printed number is **not** asserted here; see (X11).

- Depends on: (R39), (R31).
- Proof route: (R39) supplies the inequality for the relevant exponent range;
  at $q = p = 1$ it is an identity, so differentiating in $p$ there yields an
  inequality between entropies; CL08 supplies the
  expansion $A^{1+\varepsilon} = A + \varepsilon A\log A + O(\varepsilon^{2})$
  and obtains strong subadditivity in finite dimensions; the general case
  follows by finite-dimensional approximation, citing the appendix of [LR73],
  which is (R31). **A fourth, independent route to strong subadditivity.**

### (R41) [CL08] §5 — the second explicit equivalence cycle

The chain from the tensor form through $\Upsilon_{p,q}$ and $\Phi_{p,q}$ back to
the trace form and the tensor form closes, so **Ando's convexity theorem,
Lieb's concavity theorem and the convexity/concavity of the three families are
all equivalent**. Tier (a). **Proved in source, edge by edge.**

- Depends on: (R39) and (R3); transitively (R1), through (R39); and
  `[ext: AND79]`, `[ext: BEK04]` as **citation** edges naming the two theorems
  the cycle is asserted to be equivalent to and to follow.
- Proof route: the first two edges are (R39)'s steps, CL08's lemmas `upprop`
  and `phiprop`; the
  third follows Bekjan, by expanding $\Phi_{p,1}(tA,B)$ in $t$ so that the
  affine term drops out — "this is the reason for the restriction to $q=1$
  here"; then $q$ is restored using monotonicity and concavity of the
  appropriate powers; the last edge is (R3).
- CL08 records a historical judgement worth keeping: Bekjan knew his concavity
  result was equivalent to Lieb's, but was either unaware of Ando's theorem or
  unaware that his own was equivalent to it.

### (R42) [CFL14] Theorem 3.2 — joint operator convexity, a complete classification

For $p,q$ nonzero and fixed $n \ge 2$, $(A,B) \mapsto A^{q/2}B^{p}A^{q/2}$ is
jointly operator convex **if and only if** $q = 2$ and $-1 \le p < 0$, and there
are no other convex or concave cases. Tier (a). **Proved in source**, from two
internal lemmas.

- Depends on: nothing external.
- A hard negative result: joint operator convexity fails for
  $(A,B) \mapsto B^{p/2}A^{q}B^{p/2}$ for **every** $p<2$. See (X4).

### (R43) [CFL14] Theorem 4.4 — the concavity region, an iff

$\Phi_{p,q,s}$ is jointly concave if and only if $0 \le p,q \le 1$ and
$0 \le s \le 1/(p+q)$. Tier (a). **Proved in source, in three pieces**:
necessity **cited** to [HIA13]; sufficiency for $1/2 \le s \le 1/(p+q)$
**cited** to [HIA13]; sufficiency for $0 < s < 1/2$ **proved here**.

- Depends on: (R16), `[ext: HIAI13-T41]` (consumed by the route below), and
  `[ext: HIAI13-P51]`, `[ext: HIAI13-T21]` and (R1) as **citation** edges
  carrying the two pieces CFL14 does not prove.
- Proof route (the piece proved here): rewrite by the variational formula for
  $\operatorname{Tr}X^{s}$ with $0<s<1$, an infimum; change variables twice;
  use operator concavity of $B \mapsto B^{p}$ and, for the other factor, Hiai's
  extension of Epstein's theorem, `[ext: HIAI13-T41]`; conclude by (R16) part
  (1), an infimum of concave functions.
- **This row closes the gap for concavity.** With [HIA13] now in the corpus, its
  cited halves are tier (a) rather than (c) — but see (X8): Hiai may be cited
  for *necessity* without caveat, and for sufficiency only outside the range his
  own paper records as a gap.
- Internal inconsistency in CFL14, recorded at (X12).

### (R44) [CFL14] Theorems 4.1 and 4.2 — the convexity region for $p \in [1,2]$, $q \in [-1,0)$

Theorem 4.1: joint convexity for all $s \ge \min\{1/(p-1), 1/(1+q)\}$.
Theorem 4.2: at $p = 2$, joint convexity for all $-1 \le q < 0$ and
$s \ge 1/(2+q)$ — the optimal range. Tier (a). **Both proved in source.**

- Depends on: (R16), (R9), (R42), `[ext: HIAI13-T41]`, `[ext: CL08-L22]`.
- Proof route (4.1): use the $s>1$ variational formula, a supremum (consumes
  `[ext: CL08-L22]`); rewrite as a supremum of a convex-in-$B$ plus a
  concave-in-$A$ term, using operator convexity of $B \mapsto B^{p}$ for
  $1 \le p \le 2$ and Hiai's extension of Epstein's theorem (consumes
  `[ext: HIAI13-T41]`); conclude by (R16) part (1). The other half of the
  range runs the same way with the arguments swapped, invoking (R42).
- Proof route (4.2): for $1/(2+q) \le s < 1$ the variational formula gives an
  **infimum**, so (R16) part (1) no longer suffices and joint convexity in three
  variables is needed; that is supplied by (R9), LIE73's Corollary 2.1; then
  (R16) part (2) closes it.
- Recorded as open by CFL14 for $p \in (1,2)$, $q \in [-1,0)$ in two intervals
  of $s$ — closed later by (R46).

### (R45) [CFL14] §2 — Hiai's necessary conditions

As reported by CFL14: joint convexity forces either $1 \le p \le 2$,
$-1 \le q < 0$, $s \ge 1/(p+q)$ (or the same with $p,q$ interchanged), or
$-1 \le p,q < 0$; joint concavity forces $0 < p,q \le 1$ and
$0 < s \le 1/(p+q)$. Tier (a) for CFL14's report. **Proof status: cited
elsewhere** — and the cited source is now in the corpus, so the underlying
result is tier (a) too; see (X8).

- Depends on: `[ext: HIAI13]`, now retrieved.

### (R46) [ZHA18] Theorem 1.1 — the complete range for $\Psi_{p,q,s}$

The three-part statement of (D16). Tier (a). **Proved in source.** It confirms
the Audenaert–Datta conjecture and the stronger Carlen–Frank–Lieb conjecture.

- Depends on: (R2), (R47), (R16); and `[ext: AND79]`, `[ext: HIAI13]` as
  **citation** edges — Ando's half of the reduction's base case, and the
  necessity that makes the range sharp.
- Proof route: three reductions, each consuming (R16) part (1) only — the
  two-variable family reduces to a one-variable family by the variational
  identity (R47) applied to a suitable exponent triple; that reduces to three
  extreme cases the same way; and those reduce to $\Psi_{p,1-p,1}$, i.e. to
  (R2) for concavity and Ando for convexity.
- **The whole $(p,q,s)$ family collapses onto (R2)** — the strongest equivalence
  claim in the corpus, and the reason adopting the $s=1$ form costs no
  generality.

### (R47) [ZHA18] Theorem 3.3 — the Hölder/Young variational identity

For $r_i > 0$ with $1/r_0 = 1/r_1 + 1/r_2$ and invertible $X,Y$, two variational
expressions for $\operatorname{Tr}\lvert XY\rvert^{r_0}$ and
$\operatorname{Tr}\lvert XY\rvert^{r_1}$ as a minimum and a maximum over $Z$.
Tier (a). **Proved in source.**

- Depends on: `[ext: BHA-HOLDER]`.
- Proof route: Hölder's inequality for Schatten quasi-norms (consumes
  `[ext: BHA-HOLDER]`), then Young's inequality; the extremum is attained.
- ZHA18 attributes the method's origin to [CL08], so this row generalises CL08's
  variational lemma inside (R39).

### (R48) [NP05] — monotonicity of relative entropy without any Lieb theorem

Monotonicity of the relative entropy is **proved in source** with no edge to
(R1), (R2), (R15) or (R20), resting only on operator convexity of $-\ln x$ and a
compression inequality NP05 calls a variant of Hansen–Pedersen–Jensen, both
proved there. Tier (a).

- Depends on: nothing in the Lieb family; `[ext: PETZ86]` for the strategy's
  provenance only.
- **Consequence for the skeleton.** Combined with (R37) and with [TRO11]'s route
  from joint convexity to (R15), the whole graph is reachable from elementary
  operator convexity, so **no node in it is a genuine root**.

### The skeleton, as it came out

Not a spine. Five overlapping equivalence or reduction claims: (R25) over
LIE73's own Theorems 1, 2, 3, 6, 7, in finite dimensions; (R37) over MONO, MPT,
SSA, JC; (R41) over Ando, Lieb and the three Carlen–Lieb families; (R3) over the
five formulations of one convexity question; and (R46) reducing the whole
three-parameter family to (R2). The classes are joined at (R15), which belongs
to the first, implies strong subadditivity in the second by two routes, and is
*implied* by joint convexity in the second via [TRO11]. Adding (R48), the graph
has no root.

The genuinely ordered material is the negative results — (R12)'s refutation,
(R21.2), (R29), (R34), (R42), (R45) — and (R23), which [LIE73] places explicitly
outside the first class.

## Hypotheses

| (A#) | Statement | Class | Evidence | Witness | Scope | Tier | Used by |
|---|---|---|---|---|---|---|---|
| (A1) | $H$ separable | provable (dispensable) | a step-by-step read of [LIE73] Theorem 1's proof: the only candidate steps are density of finite-rank operators in the Hilbert–Schmidt norm and the existence of orthonormal bases for $\ker C$ and its complement, both true in any Hilbert space. In §IV it is *implied* by (A10) | — | standing ([LIE73] §II, [CL08]) | b | none — **a standing hypothesis no result needs** |
| (A2) | $p,r>0$ and $p+r \le 1$ | model-dependent | [LIE73] Theorem 1 states it; [CFL14] Theorem `conc` and [HIA13] show it is exactly sharp | fails at $H = \mathbb{C}$, $K=1$, $p=r=1$, $A = \varepsilon = 0.1$, $B=2$, $\lambda = \tfrac12$: $2.005 > 1.1025$. Holds at $p=r=\tfrac12$, the Wigner–Yanase case | local | b | (R1), (R4), (R5), (R6) |
| (A3) | $p \le 1$ and $q \le 1$ separately, in the generalised family | model-dependent | [HIA13] Proposition 4.1(2) **proves** necessity on $2\times2$ positive definite matrices | the degenerating family $A = \operatorname{diag}(a,b)$, $X_{\varepsilon} = \begin{pmatrix}1&0\\1&\varepsilon\end{pmatrix}$ with $\varepsilon \downarrow 0$, reducing to non-concavity of $(a^{p}+b^{p})^{s}$. Independently, this note's (X3) exhibits $(p,q,s) = (2,1,1/3)$ | local | a | (R43), (R45), (R46) |
| (A4) | $C^{p/2}KC^{r/2}$ extends to a Hilbert–Schmidt operator | provable | $\operatorname{Tr}C^{r/2}K^{\dagger}C^{p}KC^{r/2} = \lVert M\rVert_2^{2}$, so the hypothesis is **logically equivalent to finiteness of the right-hand side**; under (C3) the inequality then holds unconditionally in $[0,+\infty]$, which is why [LIE73] omits it from Corollary 1.1. It remains the antecedent of the *Hilbert–Schmidt conclusion*, which is false without it | — | local | b | (R1), (R6) |
| (A5) | the domain condition on an unbounded $K$: that $C^{r/2}$ maps enough vectors into the domain of $K$ | open | [LIE73] assumes it by fiat — `it is always correct to assume that` — with no proof and no argument for "always correct". No other corpus source can even state it, all taking $K$ a matrix | — | local | b | (R1) |
| (A6) | $0 < \lambda < 1$ | provable | at the endpoints the inequality reduces to $F(A) \le F(A)$. [KW20] and [TRO11] include an endpoint | — | local | a | all convexity rows |
| (A7) | $A$ strictly positive | provable | definedness only. [LIE73] §IV Case 2 removes it for (R15) by a decreasing limit; for the negative-power rows it is invertibility, which in finite dimensions coincides with strict positivity. Absent from the WYD rows, where [LIE73] splits off $\ker C$ instead | — | local / standing | b | (R8), (R10), (R15), (R17), (R23) |
| (A8) | $\dim H < \infty$ | provable for (R1) and (R15) — **both removals are already in the corpus**; **open** for (R20), for §V's implications, and for the (D14)/(D15a) equivalences | [LIE73] §II proves (R1) in infinite dimensions and §IV extends (R15). Nobody extends (R20): §IV extends Theorem 6 and only Theorem 6, and [RUS02] is finite-dimensional by fiat. [CL08]'s release of the restriction is an assertion with no proof | — | standing ([LIE73] §III, [RUS02], [CFL14], [ZHA18], [KW20]) | b | (R8)–(R23), (R25), (R43)–(R47) |
| (A9) | $L$ self-adjoint in Theorems 6 and 7 | provable | definedness: for non-self-adjoint $L$, $\exp(L+\ln A)$ need not be positive and its trace need not be real, so Theorem 6's own words "to the nonnegative reals" presuppose it. Read from the OCR layer, the conversion having dropped the superscript | — | local | b | (R15), (R20) |
| (A10) | $e^{L}$ is trace class | model-dependent | [LIE73] §IV standing hypothesis, which the source says forces $L$ to have purely discrete spectrum | fails at $H = \ell^{2}$, $L = 0$: $e^{L} = I$ is not trace class and §IV's proof has no eigenvalue enumeration to start from. Holds at $L = -N$, the number operator, where the trace is $1/(e-1)$ | standing ([LIE73] §IV) | b | (R24) |
| (A11) | $\varepsilon \le A, B \le \omega$ | provable | [LIE73] §IV Case 2 removes the lower bound by the monotone limit; the upper bound is implied by boundedness, which is standing | — | local | b | (R24) |
| (A12) | the domains of $\log A$ and $L$ intersect densely | open | asserted in [LIE73] §IV from a private communication, with the conclusion attached to it proved nowhere in the corpus. The intersection of two dense subspaces need not be dense, so it is not obviously vacuous either | — | local | b | (R24) |
| (A13) | $\log A$, $\log B$ are form-bounded perturbations of $-L$ | open | same private communication; the only place in the corpus where the logarithmic concavity is claimed for unbounded $A$ | — | local | b | (R24) |
| (A14) | $R,S,T > 0$ in the triple-matrix inequality | provable | definedness. There is no singular $S$ separating hypothesis from conclusion: on $\ker S$ the resolvent integrand is $O(u^{-2})$ and diverges while $-\log S$ is $+\infty$, so both sides are $+\infty$ and the statement is true-but-empty, discharged by (C3). **[LR73] prints no hypotheses at all** | — | local ([RUS02]); absent ([LR73]) | a | (R20), (R27), (R35) |
| (A15) | $K$ bounded, or invertible | provable | invertibility is discharged by density and continuity, and [CFL14] says so: `Since invertible $K$ are dense, it suffices to consider all invertible operators $K$.` Boundedness is not a hypothesis of the general form at all — [LIE73] Theorem 1 drops it in favour of (A4)/(A5) | — | local / standing ([ZHA18]) | a | (R2), (R46) |
| (A16) | the maximum in the variational formula is attained | provable | [TRO11]'s own application exhibits the maximiser, $X = \exp(H + \log A)$, which is positive definite hence admissible | — | local | a | (R15) route B |
| (A17) | the second factor is finite-dimensional in Corollary 1.3 | model-dependent | the source supplies the witness itself: `(iii) When d 2 » c» , Corollary 1.3 makes no sense except when s - 1, ` | fails at $H^{2} = \ell^{2}$ with any $s<1$ — the prefactor diverges. Holds at $d_2 = 2$, which is exactly what [LIE73]'s own Remark (i) uses to recover Theorem 1 | local | b | (R6) |
| (A18) | $K \ne 0$; $\lVert\Psi\rVert = 1$; $t \in (0,1)$; $\operatorname{Tr}\rho_{123} = 1$ | provable | degenerate or normalising side conditions. The normalisation enters exactly once, at $\rho_2^{2} \le \rho_2$, and [RUS02] says so in italics. Note that the corpus's most-used exponent case sits exactly on the boundary of (A2) | — | local | a | (R2), (R12), (R18), (R27)(ii), (R33) |
| (A19) | $A_{12}$ is trace class in Corollary 1.3 | provable | definedness of the partial trace; redundant given (A17), since the defining sum is then finite — a redundancy [LIE73] does not remark on | — | local | b | (R6) |
| (A20) | $p \le 2$ in the [CL08] family | model-dependent | [CL08]'s `Lemma \ref{noncon}` gives a recipe resting on the failure of operator convexity of $t \mapsto t^{p}$ for $p>2$; that failure is stated verbatim by both [CFL14] and [CL08] | at $p=3$, $A = \begin{pmatrix}1&1\\1&1\end{pmatrix}$, $B = \operatorname{diag}(0,10)$ the second-difference matrix is $\begin{pmatrix}1/4 & -59/4\\ -59/4 & 1331/4\end{pmatrix}$, of determinant $-2150/16 < 0$, with separating vector proportional to $(1,\,0.0442740)$ — this note's own construction, which supplies the three objects CL08's recipe leaves existential | local | a | (R39) |

## Degeneracies and boundary cases

| Case | Effect on the adopted form | Tier |
|---|---|---|
| intended case is nonvacuous | **Yes, strictly and non-commutingly.** $H = \mathbb{C}^{2}$, $p = r = 1/2$, $K$ the flip, $A_1 = \operatorname{diag}(2,1)$, $A_2 = \begin{pmatrix}1&1\\1&2\end{pmatrix}$, $B_1 = \operatorname{diag}(1,3)$, $B_2 = \begin{pmatrix}2&-1\\-1&1\end{pmatrix}$ — no two of which commute — give slacks $+0.219777$, $+0.247525$, $+0.165930$ at $\lambda = 0.25, 0.5, 0.75$ (recomputed independently to all nine digits). For the inequality half, on the (X1) trio at $t = 1/2$ the left side is $2.000000$ and the right $2.017528$, so the resolvent form holds with strict slack exactly where the naive product form fails. Corpus-named instances: [RUS02]'s non-commuting equality case (R34), and strong subadditivity itself | own computation; (a) for (R34) |
| zero object / scalars | Two effects. $A = 0$: the function vanishes and concavity extends to the closed cone by continuity for $p,r>0$; for the logarithmic half the zero object is *excluded* ($\log 0$ undefined) and [LIE73] §IV recovers it only as a decreasing limit. $H = \mathbb{C}$: **not degenerate** — it forces $p+r \le 1$ exactly, and it is where the operator-concavity rejection (X4) stops being valid. $K = 0$: both sides vanish, which is what makes the existential quantifier swap (X6) collapse | (a)/(b) |
| finite-dimensional | No effect on the truth of any adopted statement — this is the case in which everything in the corpus is *proved*. What is finite-dimension-only is the web of equivalences: (R25), (R3), (D14) | b |
| commutative | Bites, and is the exponent boundary. With $A,B$ simultaneously diagonal the trace becomes $\sum_{i,j} a_i^{r}\lvert K_{ji}\rvert^{2} b_j^{p}$, whose joint concavity is exactly that of $(a,b) \mapsto a^{r}b^{p}$, i.e. $p,r \ge 0$ and $p+r \le 1$. **Sharp for the adopted form; strictly too weak for the $s \ne 1$ generalisation** — see (X3) | own computation |
| non-separable / non-$\sigma$-finite | Non-separable: **excluded by hypothesis** rather than unaddressed. (A10) forces separability in §IV, and the Hilbert–Schmidt hypothesis (A4) forces the relevant part of $H$ to be separable. Non-$\sigma$-finite: **no natural instantiation** — the object is stated with the canonical trace on the bounded operators, and no corpus statement carries a measure or a weight for the condition to attach to | b |
| type III | **No natural instantiation.** Every corpus statement is a trace inequality and a type III factor has no semifinite normal trace, so the expressions have no meaning there. [RUS04] gestures at the relative-modular route for algebras "which might not even have a trace" but states no theorem. This is out of the object's scope on the corpus's own evidence, not a degeneracy of the adopted form | a |
| non-unital / degenerate representation | **No natural instantiation.** No corpus statement quantifies over an algebra or a representation | b |
| universally orthogonal index element | Reading (a), $A$ and $B$ with orthogonal supports ($A = P$, $B = 1-P$, $K = 1$): the function vanishes identically on that sub-cone, but concavity is *not* trivialised — a convex combination of two such pairs need not have orthogonal supports, and the inequality holds with strict slack. So this is a source of strictness, not of degeneracy. Reading (b), $K$ zero: as above | own computation |
| quantifier swap: $\forall K\,\forall A,B \mapsto \forall A,B\,\forall K$ | No change in meaning — commuting universals | — |
| quantifier swap: $\forall K \mapsto \forall\text{ unitary }K \mapsto K = 1$ | Equivalent, (X5a) — but only across all dimensions; at fixed $n$ the reduction is (O3), open | a |
| quantifier swap: $\forall K \mapsto \exists K$ | Collapses to vacuity via $K = 0$; rejected, (X6) | own computation |
| quantifier swap: two variables $\mapsto$ diagonal | Equivalent, (X5b) — the same dimension-doubling caveat | a |
| quantifier swap: self-adjoint exponents $\mapsto$ positive operators, in the inequality | A change of variables, no change in meaning; recorded as (C9) | b |
| hypothesis dropped: (A2), $p+r \le 1$ | **False.** Scalar witness: $H = \mathbb{C}$, $K=1$, $p=r=0.6$, where $a \mapsto a^{1.2}$ is strictly convex. Matrix confirmation on a validated harness: worst relative concavity violation $0.1760$ in dimension 3 and $0.0647$ in dimension 4 at $p=q=0.6$; $0.2384$ and $0.2225$ at $p=0.9$, $q=0.4$ | own computation |
| hypothesis dropped: (A4), the Hilbert–Schmidt condition | Not false — $+\infty \le +\infty$. Named witness for the divergence: $H = \ell^{2}$, $A = B = K = 1$, where the trace is $+\infty$ and concavity is meaningless. [RUS04] states the hypothesis verbatim as the weaker assumption Lieb uses. An attempted refutation could not produce a case with the left side infinite and the right side finite, monotonicity of $F$ in each argument (Löwner–Heinz) making it a supremum of finite-rank compressions — that argument is this note's, and is a sketch | (a) for RUS04; own sketch |
| hypothesis dropped: (A9), self-adjointness of $L$ | Ill-posed rather than false: $e^{L+\log A}$ is no longer positive and the trace is in general complex, so "concave" has no meaning | b |
| hypothesis dropped: $\ker A \subseteq \ker K$ in the resolvent form | **Divergent.** [RUS04] Theorem 2 states the condition verbatim; drop it and, at $H = \mathbb{C}^{2}$, $A = \lvert 0\rangle\langle 0\rvert$, $B = 1$, $K = 1$, the surviving diagonal contribution is $\int_0^{\infty} du/(u(1+u))$, divergent at $0$ | a |
| hypothesis dropped: positivity of $A,B$ | Ill-posed — $A^{p}$ is not defined (or not single-valued) for non-positive $A$ | — |
| hypothesis dropped: $p>0$ or $r>0$ | Harmless but contentless: the form loses its dependence on one argument. [CFL14] excises the case by fiat, calling the question trivial | a |
| boundary asymmetry: negative exponents | [LIE73] Theorem 8 requires only $1 \ge p > 0$ and $1 \ge r > 0$ **separately**, so the sum may reach $2$; [CFL14] notes the corresponding triple convexity needs $-1 \le p+r < 0$. **The negative-exponent convexity region is genuinely larger than the positive-exponent concavity region**, and the two must not be assumed mirror images | a |

## Rejected formulations and refuted claims

**Append-only.**

| id | Candidate or claim | Disposition | Discriminator | Tier | Date |
|---|---|---|---|---|---|
| (X1) | the naive three-matrix Golden–Thompson inequality, $\operatorname{Tr}e^{A+B+C} \le \operatorname{Tr}e^{A}e^{B}e^{C}$ (and with an absolute value) | rejected | **(X1) separating object** — three coplanar Bloch vectors at $120°$: $A = t\sigma_z$, $B = t(\tfrac{\sqrt3}{2}\sigma_x - \tfrac12\sigma_z)$, $C = t(-\tfrac{\sqrt3}{2}\sigma_x - \tfrac12\sigma_z)$, so $A+B+C = 0$ and the left side is $2$ for every $t$, while $\operatorname{Tr}e^{A}e^{B}e^{C} = \cosh t\,(3-\cosh^{2}t)$ — real for all $t$, since coplanarity kills the antisymmetric term. With $c = \cosh t$ the cubic $3c-c^{3}$ has value $2$ at $c=1$ and is strictly decreasing beyond, so the plain form fails for **every** $t>0$; the absolute-value form fails exactly for $0 < t < \log(2+\sqrt3)$; and at $t = \log(\sqrt3+\sqrt2)$ the product trace is exactly $0$ against $2$. All six orderings agree, so no reordering rescues it, and pairwise Golden–Thompson is untouched on the same data ($2\sqrt3 \le 4$). Verified symbolically from $e^{t\,n\cdot\sigma} = \cosh t + \sinh t\,(n\cdot\sigma)$ — the $\sinh^{2}$ is legitimately absorbed by $s^{2} = c^{2}-1$, no factor dropped — and against a matrix exponential to nine digits at five values of $t$. **This makes the unretrieved Horn–Johnson edge dispensable** | own construction, verified twice | 2026-08-23 |
| (X2) | the symmetrised three-matrix product, $\operatorname{Tr}e^{A+B+C} \le \operatorname{Tr}e^{A/2}e^{B/2}e^{C}e^{B/2}e^{A/2}$ | rejected | **(X1) separating object** — nobody's candidate (a grep of all six arXiv sources for the symmetrised form returns nothing), invented as the obvious repair of (X1): its right side is a trace of a positive operator, hence real and nonnegative, and it survives the (X1) trio. It fails at $A = 2\sigma_z$, $B = -\sqrt3\sigma_z+\sigma_x$, $C = \sigma_z-\sqrt3\sigma_x$: $4.554940$ against $2.723890$, a 67% violation, reproduced independently to five digits | own construction | 2026-08-23 |
| (X3) | the commutative (scalar) exponent condition as *the* exponent condition for $\Phi_{p,q,s}$ | rejected | **(X1) separating object** — at $(p,q,s) = (2,1,1/3)$ the scalar condition holds ($ps+qs = 1$) but $p = 2 > 1$. With $\Phi_{2,1,1/3}(A,B) = \operatorname{Tr}[(BAB)^{1/3}]$, rank-one $A_1 = \lvert 0\rangle\langle 0\rvert$, $A_2 = \lvert 1\rangle\langle 1\rvert$, $B_1 = \lvert u\rangle\langle u\rvert$ with $u = (2,1)/\sqrt5$, $B_2 = \lvert w\rangle\langle w\rvert$ with $w = (1,2)/\sqrt5$ and $\lambda = 1/2$: $(4/5)^{1/3} = 0.928317767 > \tfrac12[(9/5)^{2/3}+(1/5)^{2/3}] = 0.910861217$. The rank-one identity $\operatorname{Tr}[(BAB)^{1/3}] = \lvert\langle u\vert v\rangle\rvert^{2/3}$ needs no norm factor, and the convention matches [CFL14]'s via the identity CFL14 itself uses. Survives perturbation into the strictly positive interior ($+0.017435$ at $\varepsilon = 10^{-4}$, $+0.009309$ at $\varepsilon = 0.05$). **[HIA13] has his own, different witness** (see (A3)); both stand. **Boundary refinement:** at $s = 1$ the commutative condition *is* sharp, since $p,q>0$ with $p+q\le1$ already forces $p,q\le1$ | own construction, verified in two spellings | 2026-08-23 |
| (X4) | strengthening the adopted trace concavity to **operator** concavity of $(A,B) \mapsto A^{q/2}B^{p}A^{q/2}$ | rejected | **(X4) source disagreement**, reinforced by **(X2) degeneracy** — [CFL14] Theorem `opcon` part (2.) states verbatim `is {\rm not} jointly operator concave.` and its proof supplies the separating case, an $A$ with nontrivial kernel, contradiction by a homogeneity-degree mismatch. Its corollary kills the three-factor variant too, `never concave`. **The scalars are exactly where this rejection stops**: [CFL14] states `for some fixed $n\geq 2$` and states the one-dimensional case positively, so $H = \mathbb{C}$ genuinely separates the two candidates rather than trivialising both | a | 2026-08-23 |
| (X5a) | restricting the universal quantifier on $K$ to unitary $K$, or to $K = 1$ | equivalent | — ([CFL14] Lemma `equiv` proves the five-way equivalence; it credits the one-variable/two-variable half to Lieb 1973 and the $K=I$ half to Carlen–Lieb). **Not dimension-local**: both substantive directions go through a $2n\times2n$ block embedding, so at fixed $n$ only the trivial implications hold — see (O3) | a | 2026-08-23 |
| (X5b) | the one-variable diagonal form in place of the two-variable form | equivalent | — ([LIE73] Corollary 1.1 and [CFL14] Lemma `equiv`; the device is the block matrix with $K$ the flip, so the same dimension-doubling caveat applies) | a/b | 2026-08-23 |
| (X6) | swapping the quantifier on $K$ from universal to existential | rejected | **(X2) degeneracy** — $K = 0$ makes the trace vanish identically, so the existential statement is true on the whole region where concavity provably fails, and carries no information. $K=0$ is admissible in [LIE73]'s own Theorem 1, $K$ being an arbitrary linear operator. **Scope caveat:** under [ZHA18]'s standing invertibility of $K$ the discriminator vanishes, and that variant is `open` | a | 2026-08-23 |
| (X7) | every finite Trotter truncation, $\operatorname{Tr}e^{A+B+C} \le \operatorname{Tr}(e^{A/N}e^{B/N}e^{C/N})^{N}$ | rejected | **(X1) separating object** — for **each** $N$ there is a counterexample, and analytically so on the (X1) trio: each factor has determinant $1$, so the product $M_N$ does too, and its trace is $3c_N - c_N^{3} \in (-2,2)$ for $0 < t < \log(2+\sqrt3)$, whence its eigenvalues are $e^{\pm i\theta}$ and $\operatorname{Tr}M_N^{N} = 2\cos(N\theta) \le 2$ strictly. **The stronger reading is false**: a random search found a triple on which the $N=1$ truncation *holds* ($707.98 \le 1521.92$), so "every truncation fails for all data" is wrong and only the per-$N$ statement is right | own construction, corrected on review | 2026-08-23 |
| (X8) | *claim*: the sharp exponent region's necessity half is uncheckable in this corpus, being attested only through [CFL14] and [ZHA18] | refuted | [HIA13] was retrieved and read: its Proposition 4.1(2) proves the necessity of $p,q \le 1$ on $2\times2$ positive definite matrices, so (A3) moves from `open` to `model-dependent` with a locator. **Caveat, from the same source:** [HIA13] records a gap $0 < s < 1/2$ between its own necessary and sufficient conditions, so it may be cited for necessity without qualification and for sufficiency only outside that range | a | 2026-08-23 |
| (X9) | *claim*: [LIE73]'s conjecture that $A \mapsto \operatorname{Tr}(B^{1/n}A^{1/n})^{n}$ is concave is open | refuted | It is Epstein's theorem, settled in 1973. With $Y = B^{1/(2n)}$ one has $(YZY)^{n} = Y(ZY^{2})^{n-1}ZY$, so $\operatorname{Tr}[(B^{1/n}A^{1/n})^{n}] = \operatorname{Tr}[(X^{*}A^{p}X)^{1/p}]$ at $p = 1/n$ — which is [CL08]'s $\Upsilon_{p,1}$, of which CL08 says `the concavity of $\Upsilon_{p,1}$ is a theorem of Epstein`, and which [HIA13] Theorem 3.1(1) proves. A numerical search had found no counterexample (40000 complex Hermitian trials per $n$ in dimension 2, 8000 real symmetric per $n$ in dimensions 3–4, all reporting exactly zero violation) because there is none. Note the corpus never calls it "Lieb's conjecture"; it appears under other names | a | 2026-08-23 |
| (X9a) | the *joint* two-variable strengthening of (X9) | rejected | **(X2) degeneracy** — the map is homogeneous of degree $1$ in each argument, hence of degree $2$ jointly, and a nonnegative jointly concave function vanishing at the origin cannot be: concavity would give $f(X) \ge 2f(X)$. Recorded as a homogeneity triviality that carries **no** information about (X9) | own argument | 2026-08-23 |
| (X10) | *claim*: [RUS02]'s Appendix A establishes concavity from the strict inequality $f''(0) < 0$ | refuted | The strict form is false as printed: taking the direction equal to the point makes $f$ affine, so $f''(0) = 0$. What is needed, and what the integral representation gives, is $f''(0) \le 0$. The appendix says `$f^{\prime\prime}(0) < 0$ for all choices of $B = B^*$.` twice | a | 2026-08-23 |
| (X11) | *claim*: [CL08]'s printed theorem numbers can be recovered from the arXiv bytes | refuted | [TRO11] cites CL08's Theorem 1.1 for the main theorem and its Lemma 2.3 for the partial-maximisation lemma. Counting CL08's shared theorem counter — remark environments included, since they consume it — agrees on 1.1 but makes 2.3 *Ando's convexity theorem* and 2.2 the partial-maximisation lemma. Either the published version renumbers or one count is wrong; **this note therefore cites CL08 by section plus LaTeX label and prints no derived numbers for it** | a | 2026-08-23 |
| (X12) | *claim*: [CFL14] states its concavity region consistently | refuted | It states it **four** ways: $0 < p,q \le 1$ with $0 < s \le 1/(p+q)$; $0 < p,q \le 1$ with $0 \le s \le 1/(p+q)$; $0 \le p,q \le 1$ with $0 \le s \le 1/(p+q)$ (its Theorem `conc`); and the scalar version with a closed left endpoint. The discrepancies are at both the $p,q$ and the $s$ endpoints, and are reconciled only by the paper's separate declaration that zero exponents are excluded as trivial | a | 2026-08-23 |
| (X13) | *claim*: the two-variable joint concavity is a modern reformulation of Lieb's one-variable theorem | refuted | It is [LIE73] Corollary 1.1, one corollary after Theorem 1, printed p. `III - 8 -`, proved there from Theorem 1 by a direct-sum construction; and [CFL14] credits the equivalence of the two phrasings to Lieb 1973 | b | 2026-08-23 |
| (X14) | *claim*: [LIE73] Theorem 6's hypotheses and its §IV hypotheses are mutually exclusive, so the logarithmic concavity is two statements under one name | refuted | The incompatibility is real — bounded $L$ makes $e^{L}$ boundedly invertible, hence never trace class in infinite dimensions — but there is no defect, because **Theorem 6 is a finite-dimensional theorem**: [LIE73]'s introduction says its §III theorems are for finite-dimensional $H$ and that Theorem 6 alone is extended in §IV. Nothing is asserted with bounded $L$ on an infinite-dimensional space. The real gap is next door and is recorded as (A8)/(O2): §IV extends Theorem 6 and **only** Theorem 6, so the *inequality* half of the adopted form has no infinite-dimensional statement anywhere in the corpus | b | 2026-08-23 |

## Prior art

| System | Found | Relation to variants | How searched | Measured at |
|---|---|---|---|---|
| this repository | `Matrix.lieb_joint_concavity_general`, `Matrix.lieb_concavity_weighted`, `Matrix.lieb_concavity_sum`, `Matrix.hsInnerProduct` (the public API), plus the private chain `Matrix.liebJointFunction`, `Matrix.lieb_joint_concavity{,_semidef,_rect_semidef}` in `QuantumSystem/Analysis/Matrix/LiebConcavity.lean` (1019 lines) resting on `QuantumSystem/Analysis/Matrix/Effros.lean` (815 lines); no `sorry` and no `axiom` in either file. Already consumed by `relativeEntropy_jointly_convex` and `vonNeumannEntropy_SSA`. Its route is the [EFF09] one — matrix perspective, Löwner convexity, Hansen–Pedersen–Jensen | `same as` (D8)/(D11) — the $p+r = 1$ boundary, finite dimensions, semidefinite matrices, $K$ allowed rectangular. **`weaker` than (D1)/(D2)**: the region $p + r < 1$ is not covered and neither is the infinite-dimensional or unbounded-$K$ setting. `unrelated` to (D15)/(D16), there being no $s$ parameter. **Updated 2026-08-23, working tree**: `Matrix.lieb_joint_concavity_general` (in the same file) now covers the full $p + r \le 1$ region — rectangular $K$, semidefinite matrices, finite dimensions — via the reduction through the $s$-th powers, Mathlib's `CFC.rpow_le_rpow` (Löwner–Heinz) and a locally proved operator concavity of `rpow`; **its exponent hypotheses are $0 \le p$, $0 \le q$, $p + q \le 1$, so the endpoints are included and it subsumes the three narrower statements in the same file** (those are kept because each is the proof input to the next, and were made `private` on 2026-08-24 so that the public namespace carries one form of the theorem rather than three). The `weaker` verdict now applies only to the infinite-dimensional / unbounded-$K$ setting | `grep` over `QuantumSystem/` for the declaration names and for `sorry`/`axiom`; file listing | commit `eb92563` |
| this repository | could not find the $\operatorname{Tr}\exp(L+\log A)$ family or the triple-matrix inequality; `Matrix.exp`, `CFC.exp` and `CFC.log` do not occur in `QuantumSystem/` at all | — | `grep -rniE "golden\|thompson\|CFC.exp\|CFC.log\|triple"` over `QuantumSystem/`; every hit was scalar `Complex.exp` or an unrelated word | commit `eb92563` |
| Mathlib | could not find the names Lieb, Golden–Thompson, Wigner–Yanase–Dyson, Araki–Lieb or Peierls anywhere; nor von Neumann's trace inequality; nor the operator/matrix perspective, Hansen–Pedersen–Jensen, or Löwner–Heinz by name | — | a whole-library regex over declaration names, docstrings and bibliography keys; cross-checked with a natural-language search and a semantic search on all three families, and a separate search for the trace inequality | mathlib rev `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |
| Mathlib | operator **monotonicity** is proved — `CFC.monotone_rpow` and `CFC.monotone_nnrpow` on $[0,1]$, `CFC.log_monotoneOn`, `CStarAlgebra.convexOn_ringInverse` — via an integral-representation file and a functional-calculus integral file. Operator **concavity** is an explicit TODO in four separate file headers, verbatim `+ Show operator concavity of \`rpow\` over \`Icc 0 1\`` and `* Show that the log is operator concave` | `weaker`. Operator concavity of $A \mapsto A^{p}$ is step 1 of the [EFF09] route to the WYD family; Mathlib has the monotonicity and not the concavity, and it states nothing about operator concavity of $A^{p}\otimes B^{q}$, the object (D14)/(D15a) prove equivalent to the all-$K$ trace form | regexes for operator monotone/concave/convex and Löwner over the whole library; directory listings of the relevant subtrees | mathlib rev `5450b53e…` |
| Mathlib | "operator monotone" and "operator concave" exist **only in prose**: the statements use the generic `Monotone` and `ConvexOn` over the Löwner order (`instLoewnerPartialOrder`, `StarOrderedRing`), and there is no `OperatorMonotone`-style predicate | infrastructure fact. [CL08]'s and [CFL14]'s equivalences are phrased in operator-concavity language, which Mathlib expresses through the generic predicates | as above | mathlib rev `5450b53e…` |
| Mathlib | trace and functional-calculus infrastructure present (`Matrix.trace`, `LinearMap.trace`, `Matrix.PosDef`/`PosSemidef`, `Matrix.IsHermitian.cfc`, `Matrix.exp`, `CFC.exp`/`log`/`rpow`); **could not find any trace-class, Schatten or nuclear-operator notion** in the analysis tree. There is no `Matrix.PosSemidef.rpow` at this revision — matrix powers go through the generic `CFC.rpow` | bears on (A4) and (A10): the well-definedness conditions of the infinite-dimensional statements have no counterpart here | `grep` for `Schatten`, `IsTraceClass`, `nuclear` over the analysis tree; `grep` for `def rpow` | mathlib rev `5450b53e…` |
| Mathlib | the commutative shadows are present: `Real.concaveOn_rpow`, `NNReal.concaveOn_rpow`, `Real.strictConcaveOn_log_Ioi`, `Real.convexOn_mul_log`, `Real.concaveOn_negMulLog`, `ConcaveOn.le_map_sum`, and `klDiv` | `weaker` — `Real.concaveOn_rpow` is the commutative case of the WYD family's one-variable form, and `klDiv` is the commutative shadow of the relative entropy the theorem exists to serve | as above | mathlib rev `5450b53e…` |
| external Lean — `Hayata-Yamasaki-Group/lean-quantum` | `Quantum/TraceInequality/LiebAndoTrace.lean` (1460 lines) proves, on a finite-dimensional Hilbert space over the positive-definite cone: joint concavity of $\operatorname{Tr}(A^{s}K^{*}B^{1-s}K)$ for $0<s<1$; joint convexity for $1 \le s \le 2$; **joint concavity of $\operatorname{Tr}(A^{q}K^{*}B^{p}K)$ under $p,q>0$ and $p+q \le 1$**; Ando's convexity theorem; and a further convexity corollary. The library is sorry-free at the revision fetched. It also carries named operator-monotonicity predicates, Löwner–Heinz, Jensen's operator inequality, generalized perspectives and operator power means | the third is `same as` (D2)/(D12) restricted to finite dimensions, bounded $K$ and the open cone; the first is `same as` (D8); the convexity and Ando rows are the $s=1$ slice of the (D15)/(D16) region and are `stronger` than anything the WYD family of this note asserts. Nothing there corresponds to the logarithmic family or to the triple-matrix inequality | git-trees API listing, then all 21 files downloaded and grepped for the declaration names and for `sorry` | default-branch HEAD, 2026-08-23; **no commit SHA recorded, so this row expires on the next push** |
| external Lean — `leanprover-community/physlib` | the same trace-inequality development, vendored, plus a bridge from matrices to bounded operators on Euclidean space and a one-variable sandwiched concavity result $\sigma \mapsto \operatorname{Tr}[(\sigma^{s}H\sigma^{s})^{p}]$ for $1 < \alpha$. At this location `Rpow.lean` has **no** `sorry` and both Araki–Lieb–Thirring and the $p$-power trace subadditivity are proved | the sandwiched result is `weaker` than (D15)/(D16) — one variable, fixed $H$, one parameter slice — and downstream of the previous row rather than independent of it | git tree of 1069 entries fetched, including a 109-path `QuantumInfo/` subtree; `QuantumInfo`-path commits reach 2026-03-08, so the merge of the former `Timeroot/Lean-QuantumInfo` is real and not a snapshot. `sorry` counts are `grep`, **not** an axiom check | 2026-08-23; repository name lowercase `physlib` |
| Isabelle / AFP | could not find an entry stating Lieb's concavity theorem, Ando's convexity theorem, Golden–Thompson, or the triple-matrix inequality. Substantial *ambient* infrastructure exists: `Hilbert_Space_Tensor_Product` supplies trace-class and Hilbert–Schmidt operators, positive operators, partial trace and von Neumann algebras for **arbitrary** Hilbert spaces, and `Complex_Bounded_Operators` supplies the Löwner order | `unrelated` for the results. On trace class the AFP is *more general* than Mathlib — which is the infrastructure (A4) and (A10) would want | all 1019 entry slugs enumerated and filtered; abstracts of the three plausible operator-theory entries read. **The theory sources themselves were not grepped** | 2026-08-23 |
| Coq / Rocq — CoqQ | the Löwner order and positive-semidefinite predicates are present in quantity; `grep -i lieb` returns **zero** across the predicate, majorization, quantum and hermitian source files | `unrelated` | the CoqQ source tree fetched and grepped directly | 2026-08-23 |
| Lean Zulip | could not find a thread, **but the two searches never reached the archive domain**. This is a statement about a failed instrument, not about the archive's contents | — | two web searches, one domain-restricted, neither of which bound | 2026-08-23 |

<!-- `implemented-as` was set to `Matrix.lieb_joint_concavity_general` on
     2026-08-23 by the math review that accompanied the formalization of the
     general exponent region; it names the declaration carrying the adopted
     concavity form. The inequality half of the adopted form remains
     unformalized. -->

## Open questions

- (A5) — for a positive bounded $C$ and a densely defined $K$, is
  $\{\psi : C^{r/2}\psi \in D(K)\}$ dense? [LIE73] assumes it by fiat.
- (A12), (A13) — the two hypotheses [LIE73] §IV takes from a private
  communication, with conclusions proved nowhere in the corpus.
- (O2) — the triple-matrix inequality in infinite dimensions. With bounded
  self-adjoint exponents both sides are $+\infty$, so the statement is true and
  empty; for unbounded exponents the corpus is silent. Equivalently: is there a
  trace-class hypothesis under which it has content, and is that class
  non-empty?
- (O3) — does the reduction from all $K$ to $K = 1$ hold at **fixed**
  dimension? [CFL14]'s proof needs $2n$.
- (R7) — [LIE73]'s subadditivity conjecture for the skew information. No corpus
  source revisits it.
- Whether the $\exists$-quantifier variant of (X6) separates from the universal
  one when $K$ is restricted to invertibles.
- Whether [LIE73]'s Corollary 1.3 at $s = 1$ and infinite $d_2$ — asserted true
  with the proof explicitly withheld — has ever been written down.

## Sources

**Append-only.**

| Key | Work | Status | Cache | Version | Tier reached | Retrieved |
|---|---|---|---|---|---|---|
| LIE73 | E. H. Lieb, *Convex Trace Functions and the Wigner-Yanase-Dyson Conjecture*; the RCP25 Strasbourg preprint of Adv. Math. **11** (1973) 267–288 | retrieved (preprint only) | `references/lieb-rcp25/` | RCP25 preprint, Janvier 1973 | b | 2026-08-23 |
| LIE73-pub | the same, *published* in Adv. Math. 11 (1973) 267–288 | not retrieved — ScienceDirect returns HTTP 403 to this container | — | published | — | 2026-08-23 |
| LR73 | E. H. Lieb, M. B. Ruskai, *Proof of the Strong Subadditivity of Quantum-Mechanical Entropy*; the RCP25 preprint of J. Math. Phys. **14** (1973) 1938 | retrieved (preprint only) | `references/lr-rcp25/` | RCP25 preprint | b | 2026-08-23 |
| LR73-pub | the same, *published* in J. Math. Phys. 14 (1973) 1938 | not retrieved — AIP paywall, not pursued | — | published | — | 2026-08-23 |
| TRO11 | J. A. Tropp, *From joint convexity of quantum relative entropy to a concavity theorem of Lieb*, arXiv:1101.1070 | retrieved | `references/arxiv-1101.1070/` | arXiv | a | 2026-08-23 |
| RUS02 | M. B. Ruskai, *Inequalities for quantum entropy: a review with conditions for equality*, arXiv:quant-ph/0205064 | retrieved | `references/arxiv-quant-ph-0205064/` | arXiv | a | 2026-08-23 |
| RUS04 | M. B. Ruskai, *Lieb's simple proof of concavity of $\operatorname{tr}A^{p}K^{\dagger}B^{1-p}K$ and remarks on related inequalities*, arXiv:quant-ph/0404126 | retrieved | `references/arxiv-quant-ph-0404126/` | arXiv, a revised version — it footnotes a later preprint number | a | 2026-08-23 |
| CL08 | E. A. Carlen, E. H. Lieb, *A Minkowski Type Trace Inequality and Strong Subadditivity of Quantum Entropy II: Convexity and Concavity*, arXiv:0710.4167 | retrieved | `references/arxiv-0710.4167/` | arXiv | a | 2026-08-23 |
| EFF09 | E. G. Effros, *A Matrix Convexity Approach to Some Celebrated Quantum Inequalities*, arXiv:0802.1234 | retrieved | `references/arxiv-0802.1234/` | arXiv | a | 2026-08-23 |
| NP05 | M. A. Nielsen, D. Petz, *A simple proof of the strong subadditivity inequality*, arXiv:quant-ph/0408130 | retrieved | `references/arxiv-quant-ph-0408130/` | arXiv | a | 2026-08-23 |
| CFL14 | E. A. Carlen, R. L. Frank, E. H. Lieb, *Some Operator and Trace Function Convexity Theorems*, arXiv:1409.0564 | retrieved | `references/arxiv-1409.0564/` | arXiv | a | 2026-08-23 |
| HIA13 | F. Hiai, *Concavity of certain matrix trace and norm functions*, arXiv:1210.7524 | retrieved | `references/arxiv-1210.7524/` | arXiv | a | 2026-08-23 |
| ZHA18 | H. Zhang, *From Wigner-Yanase-Dyson conjecture to Carlen-Frank-Lieb conjecture*, arXiv:1811.01205 | retrieved | `references/arxiv-1811.01205/` | arXiv | a | 2026-08-23 |
| HIA18 | F. Hiai, *Quantum f-divergences in von Neumann algebras I*, arXiv:1805.02050 | retrieved (earlier run) | `references/arxiv-1805.02050/` | arXiv | — cleared, contributes nothing | 2026-08-16 |
| KW20 | S. Khatri, M. M. Wilde, *Principles of Quantum Communication Theory*, arXiv:2011.04672 | retrieved (earlier run) | `references/arxiv-2011.04672/` | arXiv | a | 2026-08-16 |
| EPS73 | H. Epstein, *Remarks on Two Theorems of E. Lieb*, Comm. Math. Phys. **31** (1973) 317–325 | not retrieved — not sought. The volume and page range are **not a locator into Epstein**: they are the bibliographic entry, printed identically in the bibliographies of [CL08], [ZHA18] and [HIA13], which is what tier (c) permits — an attesting source's own text. Nothing is claimed about what any page of it says | — | published | c | 2026-08-23 |
| HJ91 | R. A. Horn, C. R. Johnson, *Topics in Matrix Analysis*, CUP 1991 | not retrieved — the one place a needed counterexample was known to live. **(X1) makes it dispensable** | — | published | c | 2026-08-23 |
| BHA97 | R. Bhatia, *Matrix Analysis* | not retrieved — cited by [EFF09] for operator convexity of $x\log x$ and of $-x^{s}$, and by [ZHA18] for Hölder's inequality for Schatten quasi-norms | — | published | c | 2026-08-23 |
| CARLEN-NOTES | E. A. Carlen, *Trace inequalities and quantum entropies: an introductory course* | not retrieved — not sought. **This is the work Mathlib's `rpow` order files cite as their reference, and it is a different work from [CL08]**; do not merge the two keys | — | published | — | 2026-08-23 |
| CFL-SURVEY | E. A. Carlen, R. L. Frank, E. H. Lieb, the survey [ZHA18] cites | not retrieved — five [ZHA18] rows rest on statements quoted from it. The numbers involved (**[ZHA18]'s** Propositions 2.1–2.3, its Theorem 3.5, its Lemma 3.2) are locators into the *attester*, which is what tier (c) permits; no locator into the survey itself appears anywhere in this note | — | — | c | 2026-08-23 |
| RUS05-ERR | M. B. Ruskai, Erratum, J. Math. Phys. **46** (2005) 0199101 | not retrieved. **[TRO11] cites it every time it cites [RUS02]'s Appendix A**, and the [RUS02] cache contains the string "erratum" zero times, so what it corrected is unknown here — see `## Not investigated` | — | published | — | 2026-08-23 |
| AND79 / UHL / LIN74 / LIN75 / GOL65 / THO65 / RUS72 / WY63 / BAU71 / BEK04 / KLEIN / ROCK70 / AL70 / BJ69 / PETZ86 / PETZ88 | Ando 1979; Uhlmann; Lindblad 1974 and 1975; Golden 1965; Thompson 1965; Ruskai 1972; Wigner–Yanase 1963; Baumann 1971; Bekjan; Klein 1931; Rockafellar; Araki–Lieb 1970; Baumann–Jost 1969; Petz 1986 and 1988 | not retrieved — none sought | — | — | c/d | 2026-08-23 |

## Not investigated

- **The published versions of both 1973 papers.** Every [LIE73] and [LR73]
  locator in this note is a locator **into the RCP25 preprint**. Five later
  sources cite the published Adv. Math. paper by theorem number, and those
  numbers are consistent with what the preprint contains wherever it could be
  checked — Theorem 1 the WYD concavity, Theorem 6 the logarithmic concavity,
  Theorem 8 the negative-power convexity, Corollary 2.1 the power form. **That
  is corroboration of the numbering, not proof of it.** Two specific
  consequences: whether Theorem 8's hypothesis survived into print was not
  checked, and whether Corollary 1.2's part (3) prints $q \ge 1/2$ or $q \ge 1$
  could not be resolved against the proof text.
- **No [LIE73] or [LR73] quote was compared against a page image**, so every
  such row is tier (b): `mineru-cross-checked-against-PDF-text-layer` where the
  independent OCR extraction confirms it, `mineru-unchecked` otherwise. Every
  exponent range, sign and display below the level of the prose is in the
  weaker class. `pdftoppm`, `pdftotext`, `mutool` and `gs` are all absent from
  this container, so no page-image check is possible here at all.
- **The `[ext: …]` coverage gap.** 32 external edges were marked; six are
  discharged inside the corpus (`LOGINT`, `HPJ`, `CL08-L22`, `KLEIN`, `LIN74`,
  `EPS73`); the sharp-region edges into [HIA13] were closed by retrieving it;
  and prior art was measured for three of the rest (operator concavity of
  $A^{p}$, Hansen–Pedersen–Jensen, Golden–Thompson). **The remaining edges were
  never checked against any proof assistant**: `BS55/KR36` beyond the Mathlib
  TODO, `MAXMOD`, `UHL72`/`UHL73`, `ROCK70`, `TROTTER`, `THO65`, `RUS72`,
  `SCHATTEN-MONOTONE`, `HJ91`, `SPECMAP`, `HERGLOTZ`, `MINIMAX`, `DOMCONV`,
  `RITZ`, `AL70-L3`, `BJ69`, `LIN75`, `BHA-OPCONV`, `BHA-HOLDER`, `AND79`,
  `BEK04`, `PETZ86`, `PETZ88`, `WY63`, `BAU71`. Note that `BHA-HOLDER` is the
  one edge whose substitution sentence was incomplete when filed; it reads:
  Hölder's inequality for Schatten quasi-norms,
  $\lVert XY\rVert_{r_0} \le \lVert X\rVert_{r_1}\lVert Y\rVert_{r_2}$ when
  $1/r_0 = 1/r_1 + 1/r_2$, valid for all positive exponents.
- **[RUS02]'s erratum.** [TRO11] cites it alongside every citation of [RUS02]'s
  Appendix A — the appendix that carries the Epstein route recorded under
  (R15). What it corrected is unknown here, and (X10) identifies a strictness
  error in that appendix that an erratum would plausibly address. **This is the
  one gap that could invalidate a proof route filed as proved.**
- **Sources not sought at all**: Ando 1979, which [CL08] says contains proofs of
  *both* Ando's convexity theorem and Lieb's concavity theorem; the
  Carlen–Frank–Lieb survey, on which five [ZHA18] rows rest; Carlen's course
  notes, which Mathlib itself cites as the reference for its operator-order
  files; and Epstein, Bhatia, Horn–Johnson, Uhlmann, Lindblad, Rockafellar,
  Klein, Wigner–Yanase, Baumann, Bekjan, Petz.
- **Degeneracy checklist items disposed of by judgement rather than by a
  source**: non-$\sigma$-finiteness, type III, and non-unitality /
  degenerate representations are recorded as having no natural instantiation.
  That is defensible from the statements — every one is a trace inequality on a
  Hilbert space — but no source says so.
- **Prior art gaps**: no commit SHA was recorded for either external Lean
  repository, so those two rows expire on the next push; the `sorry` counts
  there are text greps and **not** axiom checks, so nothing is certified about
  the axiom set of any external declaration; the AFP theory sources were not
  grepped, only entry slugs and three abstracts; `mathcomp-analysis` was not
  searched directly; the Lean Zulip archive was never effectively reached; and
  `inQWIRE/LeanQuantum`, Metamath, HOL Light and Mizar were not swept.
- **Statements sighted and not pursued**: [LIE73]'s Corollaries 2.1, 3.1 and
  8.1 region tables were recorded but their four sign regimes not checked
  individually; [CL08]'s three families were recorded only where they name
  Lieb; [CFL14] §3's internal lemmas and [ZHA18] §2's Rényi background were
  read at statement level only, so (R42) and part of (R46) carry no proof
  route; and [LIE73]'s §V edge from Theorem 3 to Theorem 2 is recorded as the
  source sketches it, its conversion being too mangled to read the integration
  step.
- **The unexamined base.** The adopted concavity form rests on tier (b) rows
  ((D1), (D2), (R1)) whose only witnesses are a MinerU conversion and an
  independent OCR extraction of a 1973 typescript — corroborated by four tier
  (a) restatements, none of which covers the full $p+r \le 1$ region in infinite
  dimensions. The adopted inequality rests on tier (b) rows ((D5), (D6), (R20))
  plus one tier (a) source that proves it only in finite dimensions, and on a
  change of variables that **no source prints** and that this note argues for
  itself.
