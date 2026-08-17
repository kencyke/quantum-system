---
object: Umegaki relative entropy
slug: umegaki-relative-entropy
status: draft
worst-tier: c
mathlib-rev: 5450b53e5ddc75d46418fabb605edbf36bd0beb6
implemented-as: none
revisions:
  - 2026-08-16 · 2d7f460 · initial extraction · sources: UME62, HIA18, VED02, WIT18, HS17, KW20
---

<!--
No macro preamble. Every verbatim quote that carries a source's private macros
(\S, \U, \A, \a from WIT18; \Tr, \supp from KW20's unavailable Book_KW class)
is placed inside a fenced code block, so the bytes stay exactly as fetched and no
renderer tries to typeset them. Everything the note says in its own voice is
written in plain KaTeX.

Do not reintroduce a `$$\newcommand{...}$$` block here: measured against
katex 0.18.4, \newcommand does NOT survive from one math span to the next -- not
even when the renderer passes a shared `macros` object, because \newcommand is a
local definition. Such a block leaves every later use of the macro throwing
`Undefined control sequence`. Only \gdef carries, and only into renderers that
share macro state at all. `scripts/check_render.py` enforces this.
-->
# Umegaki relative entropy

## What this object is for

The Umegaki relative entropy is a two-argument, non-symmetric, jointly convex,
jointly lower semicontinuous functional on pairs of normal positive functionals
on an operator algebra, whose classical special case is the Kullback–Leibler
divergence and whose operational meaning is the optimal error exponent in
asymmetric quantum hypothesis testing. Its defining structural property is
*monotonicity* under the adjoints of well-behaved positive unital maps — the
data-processing inequality — from which the literature derives non-negativity,
subadditivity, strong subadditivity, sufficiency of a subalgebra and the
entanglement measures of quantum field theory.

Its generality is forced by a definitional obstruction, not by taste. The naive
formula $\mathrm{Tr}\,\rho(\log\rho-\log\sigma)$ needs a trace and needs $\log\sigma$, and
a type III von Neumann algebra — the case that actually occurs for the local
algebras of a quantum field — has neither. The object therefore has two lives: a
trace-based one (Umegaki 1962) and a relative-modular-operator one (Araki
1976/77), and the point of the modern treatment is that the second restricts to
the first where the first exists.

## Definition

### Variants as the sources write them

The columns are the axes along which this corpus actually splits. `Total?` asks
whether the definition assigns a value to *every* pair, or is a partial function
whose domain is a hypothesis. `Apparatus` is what the formula is built out of.

| (D#) | Source | Ambient algebra | Trace needed | Apparatus | Arguments | Total? | Tier |
|---|---|---|---|---|---|---|---|
| (D1) | [UME62] | finite class, σ-finite | **yes**, faithful normal finite | trace + Radon–Nikodym densities in $L^1(A)$ | both normalised | **no** — domain is $a\prec b$ | b |
| (D2) | [HIA18] §1 | semifinite | **yes**, semifinite | trace + density operators | both normal states | yes, case split | a / c |
| (D3) | [HIA18] §1 | arbitrary | no | relative modular operator | both normal states | yes, case split | a / c |
| (D4) | [HIA18] Def. 2.1 | arbitrary | no | standard $f$-divergence at $f(t)=t\log t$ | both in $M_*^+$, unnormalised | yes, boundary term | a |
| (D5) | [VED02] | none (matrices) | Tr | bare formula | both states | **no** — silent off the domain | a |
| (D6) | [WIT18] | arbitrary, with a cyclic separating vector | no | relative modular operator, vector form | $\Psi$ cyclic separating; $\Phi$ any | yes, $+\infty$ a consequence | a / c |
| (D7) | [HS17] | standard form, σ-finite | no | relative modular operator + Connes cocycle | both **faithful** normal states | partial, then stipulated | a / c |
| (D8) | [KW20] | $\mathcal B(\mathcal H)$, $\dim\mathcal H<\infty$ | Tr | bare formula, base 2 | first a state, second only PSD | yes, case split | a |
| (D9) | [HIA18] §3 / Kosaki | arbitrary | no | supremum over step-function paths | both in $M_*^+$ | yes | a / c |

**(D1) [UME62] §4, Definition 1 (journal pp. 68–69)** — tier (b),
`mineru-cross-checked-against-PDF-text-layer`

The cache is MinerU model output, so no blockquote is taken from it; the
following is a paraphrase, and every clause below was confirmed independently
against the PDF's own OCR text layer (`pdftextlayer.txt`, extracted with `pypdf`)
as well as against the MinerU conversion.

Standing setting (§1): $A$ is a von Neumann algebra **of finite class and
σ-finite**, carrying a fixed faithful normal (finite) trace $\tau$; $L^p(A)$ are
Segal's measurable-operator spaces; a normal state $\rho$ has a
Radon–Nikodym derivative $d\rho/d\tau\in L^1(A)$ with
$\rho(a)=\tau((d\rho/d\tau)a)$. For self-adjoint $a,b$, Umegaki writes $a\prec b$
to mean $s(a)\le s(b)$, $s(\cdot)$ the support projection.

Definition 1: for $a,b\in L^1(A)$ with $a,b\ge 0$, $a\prec b$ and
$\tau(a)=\tau(b)=1$,
$$I(a,b)=\tau(a\log a-a\log b),$$
called the **information** between $a$ and $b$; and for normal states with
$\sigma\prec\rho$, $I(\sigma,\rho):=I(d\sigma/d\tau,\,d\rho/d\tau)$. The singular
part is cut off inside the definition by $a\log b:=a\,s(b)\log b$.

Four points that are easy to get wrong:

1. **The name is *information*, not *relative entropy*.** See (X6): the string
   "relative entropy" occurs zero times in the paper. *Entropy* is reserved for
   the one-argument $H(a)=-\tau(a\log a)$, and §5 defines a separate symmetric
   *divergence* $J(a,b)=I(a,b)+I(b,a)$ on the stricter domain $a\sim b$.
2. **The support condition is a hypothesis of the definition, not a case.**
   Outside $a\prec b$, $I(a,b)$ receives no value at all. There is no $+\infty$
   branch anywhere in the paper.
3. **Finite entropy is *not* in Definition 1.** The class
   $\mathcal E=\{a\in L^1(A): a\ge0,\ |H(a)|<\infty,\ \tau(a)=1\}$ is defined
   separately at the end of §3 and is a hypothesis of the *theorems* (R7)–(R11).
   Proposition 4.1 gives two independent sufficient conditions for $I(a,b)$ to be
   unambiguous in $(-\infty,+\infty]$: $ab=ba$, or $H(a)$ finite with $b$ bounded.
4. **The setting is *finite*, not semifinite — but Umegaki descopes it himself.**
   §1 states that a faithful normal trace exists iff $A$ is of finite class and
   σ-finite, then says the assumption "is not necessarily essential" and that for
   semifinite $A$ with a semi-trace all theorems and propositions hold "by a
   little or simply modified proofs", subject to an unverified side condition on
   subalgebras. Footnote 5) goes further and *extends the definition itself* to
   the semifinite case for $0\le a\in L^1(A)$ and $0\le b\in A$ with $a\prec b$,
   where $b$ need not lie in $L^1(A)$ — so **Umegaki's own semifinite extension
   already drops the normalisation of the second argument**, which is (D8)'s
   asymmetric regime, in 1962. See (C4) and (X7).

`differs from (D2):` a finite trace rather than a semifinite one; a partial
function rather than a total one; both arguments normalised; and a different
name.
`sources claim equivalence:` [HIA18] presents (D2) *as* Umegaki's; no source in
the corpus remarks on the finite/semifinite difference.

**(D2) [HIA18] §1, eq. (F-1.1)** — tier (a) for HIA18's restatement, tier (c) as
a claim about what [UME62] says

> ```
> D(\rho\|\sigma):=\begin{cases}
> \tau(d_\rho(\log d_\rho-\log d_\sigma)) & \text{if $s(\rho)\le s(\sigma)$}, \\
> +\infty & \text{otherwise},
> \end{cases}
> ```

introduced by

> the relative entropy $D(\rho\|\sigma)$ was first
> introduced in 1962 by Umegaki \cite{Um} for normal states $\rho,\sigma$ on a semifinite von

and glossed

> where $\tau$ is a semifinite trace on $M$, $d_\rho$ is the density operator of $\rho$ with
> respect to $\tau$ and $s(\rho)$ is the support projection of $\rho$.

`differs from (D1):` semifinite versus finite trace; total versus partial; and
the **letters are swapped** — see (C1), under which
$D_{\mathrm{HIA}}(\rho\|\sigma)=I_{\mathrm{UME}}(\sigma,\rho)$.
`sources claim equivalence:` yes, by identification. See (X7) for the
adjudication: this is a defensible generalisation of a claim [UME62] makes about
itself, not a transcription of its standing hypothesis.

**(D3) [HIA18] §1, eq. (F-1.2)** — tier (a) for the restatement, tier (c) for the
attribution to Araki, whose papers were not obtained

> ```
> D(\rho\|\sigma):=\begin{cases}
> -\<\xi_\rho,(\log\Delta_{\sigma,\rho})\xi_\rho\>
> =\<\xi_\sigma,(\Delta_{\rho,\sigma}\log\Delta_{\rho,\sigma})\xi_\sigma\>
> & \text{if $s(\rho)\le s(\sigma)$}, \\
> +\infty & \text{otherwise},
> \end{cases}
> ```

preceded by

> Later in 1970's Araki
> \cite{Ar5,Ar2} extended Umegaki's relative entropy, by introducing the \emph{relative modular
> operator} $\Delta_{\rho,\sigma}$ for normal states $\rho,\sigma$, to general
> von Neumann algebras as

Supporting apparatus (HIA18 §2.1, tier (a) for HIA18's statements): every
$\sigma\in M_*^+$ has a unique vector representative $\xi_\sigma$ in the natural
cone with $\sigma(x)=\langle\xi_\sigma,x\xi_\sigma\rangle$;
$S_{\rho,\sigma}(x\xi_\sigma+\eta):=s_M(\sigma)x^*\xi_\rho$ for $x\in M$,
$\eta\in(1-s_{M'}(\sigma))\mathcal H$;
$\Delta_{\rho,\sigma}:=S_{\rho,\sigma}^*\overline{S_{\rho,\sigma}}$; the support
projection of $\Delta_{\rho,\sigma}$ is $s_M(\rho)s_{M'}(\sigma)$.

Note the **two equal expressions with opposite subscript orders** inside
(F-1.2). That is the notational trap; see (C2).

`differs from (D1)/(D2):` no trace, no density operators, no semifiniteness —
valid for an arbitrary von Neumann algebra, type III included.
`sources claim equivalence:` [HIA18] says Araki *extended* Umegaki's, by
citation, not by proof. The reduction is *proved* in this corpus only for
$\mathcal B(\mathcal H)$ ((R3)) and for finite-dimensional bipartite systems ((R13)). See
`## Open questions`.

**(D4) [HIA18] Definition 2.1, eqs. (F-2.4)–(F-2.6)** — tier (a)

For $\rho,\sigma\in M_*^+$ (arbitrary normal **positive functionals**, not
necessarily states) and $f$ convex on $(0,\infty)$:

> We then introduce the {\it standard $f$-divergence} $S_f(\rho\|\sigma)$ of $\rho,\sigma$ by

> ```
> S_f(\rho\|\sigma):=\<\xi_\sigma,f(\Delta_{\rho,\sigma})\xi_\sigma\>
> +f(0^+)\sigma(1-s_M(\rho))+f'(+\infty)\rho(1-s_M(\sigma)).
> ```

with $f(\Delta_{\rho,\sigma}):=\int_{(0,+\infty)}f(t)\,dE_{\rho,\sigma}(t)$ — the
spectral integral over the **open** interval, the endpoints carried by the two
boundary terms explicitly — and the scalar conventions $bf(0/b):=f(0^+)b$,
$0f(a/0):=f'(+\infty)a$, $(+\infty)\cdot0:=0$, $(+\infty)c:=+\infty$ for $c>0$.
The relative entropy is the case $f(t)=t\log t$, for which $f(0^+)=0$ and
$f'(+\infty)=+\infty$.

`differs from (D3):` **not in value** — (D4) *is* (D3) at $f=t\log t$, extended
off states to all of $M_*^+$. It differs in *mechanism*: the $+\infty$ on
non-dominated supports is not a case split but the boundary term
$f'(+\infty)\rho(1-s_M(\sigma))$, which is what makes (D4) automatically
homogeneous, additive over direct sums and jointly lower semicontinuous.
`sources claim equivalence:` yes — HIA18 Remark 2.7 and Example 3.12, proved in
source for $\mathcal B(\mathcal H)$ with $\dim\mathcal H<\infty$.

A near-miss recorded here rather than as its own variant: HIA18 Remark 2.7 also
displays Petz's *quasi-entropy* at $k=1$, which for $f=t\log t$ gives
$\mathrm{Tr}\, D_\rho(\log D_\rho-\log^+ D_\sigma)$ with $\log^+0:=0$ — finite for every
pair — and calls it improper. That is a formulation the literature exhibits and
discards; it is (X1).

**(D5) [VED02], the Definition following the von Neumann entropy, eq. (def8)** —
tier (a)

> {\bf Definition}. {\em The von Neumann relative entropy} between
> the two states $\sigma$ and $\rho$ is defined as

> ```
> S_N(\sigma ||\rho) = \mbox{Tr} \sigma (\ln \sigma - \ln \rho) \;\; .
> ```

Explicit natural logarithm. **No support condition and no $+\infty$ branch at
all**; the singular case is not discussed anywhere in the paper. The attribution
is in the same paragraph:

> this quantity was first considered by Umegaki (1962), but for
> consistency reasons I name it after von Neumann; I will also refer
> to it as the quantum relative entropy).

`differs from (D8):` no support condition, hence a partial function whose domain
the source never states; natural log; second argument a state.
`sources claim equivalence:` with Umegaki's, asserted. VED02 is internally
consistent in keeping $\sigma$ first throughout (F1–F3, Theorem 5, the Stein
exponent).

**(D6) [WIT18] §"Relative Entropy In Quantum Field Theory", eq. (onorf)** —
tier (a) for WIT18's statements, tier (c) as a claim about Araki

> \S_{\Psi|\Phi}(\U)= -\la\Psi|\log \Delta_{\Psi|\Phi}|\Psi\ra.

with $\Delta_{\Psi|\Phi}:=S^\dagger_{\Psi|\Phi}S_{\Psi|\Phi}$ and
$S_{\Psi|\Phi}\,a|\Psi\rangle=a^\dagger|\Phi\rangle$; $\Psi$ must be cyclic and
separating for $\mathcal A_{\mathcal U}$, while $\Phi$ may be any state. The singular case is a
consequence rather than a stipulation:

> ```
> For example, $\S_{\Psi|\Phi}(\U)$ may be $+\infty$ if $\Delta_{\Psi|\Phi}$ has a zero eigenvalue, which will occur if $\Phi$ is not separating for $\A_\U$.
> ```

`differs from (D3):` the subscript convention on $S$ and $\Delta$ is reversed
(C2), and the first argument must carry a cyclic separating vector.
`sources claim equivalence:` yes, and **proved in source** for the
finite-dimensional case — see (R13).

**(D7) [HS17], the Definition of the relative entropy, eq. (drel1)** — tier (a)
for HS17's statements, tier (c) as a claim about Araki

> H(\omega, \omega') = \langle \Omega | \log \Delta_{\omega, \omega'} \ \Omega\rangle

together with the Connes-cocycle expression
$\lim_{t\to0}\omega([D\omega:D\omega']_t-1)/(it)$ as part of the same
definition — a **third** equivalent expression, present in no other corpus
source. Standing hypotheses:

> ```
> One assumes to be given two faithful, normal states $\omega, \omega'$ on a v. Neumann algebra $\A$ in standard form.
> ```

and three stipulations the others do not make: an explicit two-parameter
rescaling rule
$H(\lambda\omega,\lambda'\omega')=\lambda H(\omega,\omega')+\lambda\log(\lambda/\lambda')$;
$H(\omega,\omega')=\infty$ when $\omega'$ is not normal; and the frank

> When $\omega$ or $\omega'$ are not faithful (such that
> $|\Omega\rangle,|\Omega'\rangle$ are not standard), the definition has to be somewhat modified~\cite{ohya_1}.

The **plus** sign here is not a disagreement with HIA18's minus: HS17 uses
HIA18's subscript order and inserts the index-reversed $\Delta$. See (C2).

`differs from (D3):` requires both states faithful; carries the cocycle formula
as part of the definition; and its domain is the positive functionals of a
**C\*-algebra**, not $M_*^+$ — see (C8).
`sources claim equivalence:` the $\mathcal B(\mathcal H)$ reduction is computed in source; the
general equality with Araki's is asserted by citation.

**(D8) [KW20], Definition (`def-rel_ent`)** — tier (a)

Stated for *every state* $\rho$ and *positive semi-definite operator* $\sigma$ —
the asymmetry is in the definition's own hypothesis, not a later remark:

> the \textit{quantum relative entropy of $\rho$ and $\sigma$}, denoted by $D(\rho\Vert\sigma)$, is defined as

> ```
> D(\rho\Vert\sigma)=\left\{\begin{array}{l l} \Tr[\rho(\log_2 \rho-\log_2\sigma)] & \text{if }\supp(\rho)\subseteq\supp(\sigma),\\ +\infty & \text{otherwise}. \end{array}\right.
> ```

with $0\log_2 0=0$, base 2 uniformly, finite dimensions throughout, and the
asymmetry stated deliberately:

> More generally, we could define the quantum relative entropy exactly as above, but with both arguments being positive semi-definite operators. For our purposes in this book, however, it suffices to restrict the first argument to be a state.

`differs from (D2):` base 2; finite dimensions; second argument merely positive
semi-definite.
`sources claim equivalence:` with Umegaki's, by citation; with the regularised
form $\lim_{\varepsilon\to0^+}D(\rho\|\sigma+\varepsilon\mathbb 1)$, **proved in
source** — see (R14).

**(D9) [HIA18] §3, Theorem 3.5 and Example 3.12; Kosaki 1986** — tier (a) for
HIA18's own expression, tier (c) for Kosaki's, whose paper was not obtained

HIA18's expression, obtained by specialising its Theorem 3.5 to $f=-\log t$, is a
supremum over $n\in\mathbb N$ and over $M$-valued step functions $x(\cdot)$ of an
explicit expression involving $\sigma(1)\log n$, a correction term
$(\sigma(1)-\rho(1))\tfrac{2}{n+1}$, and
$-\int_{[1/n,n]}\{\sigma((1-x(s))^*(1-x(s)))+s^{-1}\rho(x(s)x(s)^*)\}s^{-1}\,ds$.

Substitution sentence for Kosaki (tier (c), no locator into Kosaki's paper):
*Kosaki, "Relative entropy of states: a variational expression" (J. Operator
Theory 16 (1986) 335–348, per HIA18's bibliography) expresses the relative
entropy as a supremum over $n$ and over $M$-valued step functions $x(\cdot)$ of
$\sigma(1)\log n-\int_{[1/n,+\infty)}\{\sigma((1-x(s))^*(1-x(s)))+s^{-1}\rho(x(s)x(s)^*)\}s^{-1}\,ds$
— the integration range $[1/n,+\infty)$ being the only difference HIA18 names —
from which positivity, joint convexity, lower semicontinuity and monotonicity
follow directly. Whether Kosaki states it on $M_*^+$ or on states is not
recoverable from HIA18's reproduction.*

HIA18 on the relation:

> This expression is similar to but a bit different from the variational expression

`differs from (D4):` the same functional, presented as a supremum; the cut-off
interval is two-sided in HIA18 and one-sided in Kosaki, which HIA18 explains as
what makes its expression behave under the transpose
$\widetilde f(t)=tf(t^{-1})$.
`sources claim equivalence:` yes — HIA18 derives its own from Theorem 3.5,
proved in source, and reports Kosaki's as an alternative for the same quantity.

There is a **second, genuinely different** variational expression, Petz's, at
(R16); it is not a further (D#) because HIA18 states it for the relative entropy
already defined, not as a definition.

### Adopted general form

Let $M$ be a von Neumann algebra in standard form $(M,\mathcal H,J,\mathcal P)$, and let
$M_*^+$ be the positive cone of its predual — the normal positive linear
functionals on $M$, **not** required to be normalised, faithful, or nonzero. For
$\rho,\sigma\in M_*^+$ let $\xi_\rho,\xi_\sigma$ be their unique vector
representatives in the natural cone $\mathcal P$, let $s_M(\cdot)$ and
$s_{M'}(\cdot)$ denote the support projections in $M$ and in $M'$, let
$S_{\rho,\sigma}$ be the conjugate-linear operator determined on the dense
subspace $M\xi_\sigma+(1-s_{M'}(\sigma))\mathcal H$ by
$S_{\rho,\sigma}(x\xi_\sigma+\eta):=s_M(\sigma)x^*\xi_\rho$, and let
$\Delta_{\rho,\sigma}:=S_{\rho,\sigma}^*\overline{S_{\rho,\sigma}}$ be the
relative modular operator, with spectral measure $E_{\rho,\sigma}$ on
$s_M(\rho)s_{M'}(\sigma)\mathcal H$. Writing $f(t)=t\log t$ on $(0,\infty)$, so that
$f(0^+)=0$ and $f'(+\infty)=+\infty$, the **Umegaki relative entropy of $\rho$
with respect to $\sigma$** is
$$
D(\rho\|\sigma)\;:=\;\int_{(0,+\infty)}t\log t\;d\|E_{\rho,\sigma}(t)\xi_\sigma\|^2
\;+\;0\cdot\sigma(1-s_M(\rho))\;+\;(+\infty)\cdot\rho(1-s_M(\sigma)),
$$
the integral taken over the **open** interval, under the scalar conventions
$(+\infty)\cdot0:=0$ and $(+\infty)c:=+\infty$ for $c>0$. Its value lies in
$(-\infty,+\infty]$ for every pair; it is $+\infty$ exactly when
$s_M(\rho)\not\le s_M(\sigma)$ or the spectral integral diverges. Natural
logarithm (C3). The definition carries **no** hypothesis of semifiniteness,
σ-finiteness, separability, faithfulness, normalisation, or finite dimension —
(A1)–(A5) are all absent from it — and the only standing assumption is that $M$
is presented in a standard form, which is (A6) and is provable.

This is **(D4)**, i.e. **(D3) totalised**. The discriminator is **(X4) type III
generality loss**: on the local algebra $\mathcal A_{\mathcal U}$ of a wedge region there is no
trace at all, so (D1)/(D2)/(D8) have no referent there, while every ingredient
above exists for every von Neumann algebra — and (D4) loses nothing, because it
reproduces the trace expression on $\mathcal B(\mathcal H)$ ((R3)) and the classical
$f$-divergence on an abelian algebra ((R4)). **(X3)** shows the choice is forced
already one type earlier: the density-matrix form (D8) fails on any type II
factor, where a trace exists but $\mathrm{Tr}\,$-densities do not. Two further decisions
inside the modular family are settled by **(X5)**: the domain is $M_*^+$ rather
than the faithful states of (D7) or the cyclic-separating-vector states of (D6),
because the named pair $\rho=\mathrm{diag}(1,0)$,
$\sigma=\mathrm{diag}(\tfrac12,\tfrac12)$ on $M_2(\mathbb C)$ has relative
entropy $\log 2$ with $\rho$ not faithful, and neither (D6) nor (D7) reaches it.

Two limits of this choice, stated here rather than buried:

- **Nothing in this corpus proves that the adopted form agrees with (D1)/(D2) on
  a general semifinite algebra.** What is proved is agreement on $\mathcal B(\mathcal H)$ (R3) and
  in finite dimensions (R13); the nearest general statement, (R17), is restricted
  to pairs related by a *bounded* relative Hamiltonian, is written with the
  canonical trace on a crossed product rather than a trace on $M$, and is hedged
  by its own source as a "complete resemblance". See `## Open questions`.
- (D7)'s domain is strictly **larger**: HS17 defines $H$ on the positive
  functionals of a C\*-algebra, assigning $+\infty$ off the normal ones. That is
  a totalisation by stipulation, recorded as (C8); the adopted form does not
  include it.

## Notation and conventions

| (C#) | Axis | This note | Per source | Translation |
|---|---|---|---|---|
| (C1) | which argument is differentiated, and its letter | first argument, called $\rho$ | role order identical in **all six** sources: $(\text{first})(\log\text{first}-\log\text{second})$. Letters: [HIA18] [KW20] [WIT18] write $\rho$/$\Psi$ first; [UME62] [VED02] call that argument $\sigma$ | $D_{\mathrm{HIA}}(\rho\|\sigma)=I_{\mathrm{UME}}(\sigma,\rho)=S_{\mathrm{VED}}(\sigma\|\rho)$ after renaming |
| (C2) | subscript order on $S_{\cdot,\cdot}$, $\Delta_{\cdot,\cdot}$ | HIA18's: acts on the **second** index's vector | [HIA18] $S_{\rho,\sigma}(x\xi_\sigma+\eta)=s_M(\sigma)x^*\xi_\rho$; [HS17] $S_{\omega,\omega'}a\|\Omega'\rangle=a^*\|\Omega\rangle$; [WIT18] $S_{\Psi\|\Phi}a\|\Psi\rangle=a^\dagger\|\Phi\rangle$ — the **first** index | $\Delta^{\mathrm{WIT}}_{\Psi\|\Phi}=\Delta^{\mathrm{HIA}}_{\Phi,\Psi}$. HS17's $+$ with $\Delta_{\omega,\omega'}$ and HIA18's $-$ with $\Delta_{\sigma,\rho}$ are the same expression twice |
| (C3) | base of the logarithm | natural | explicit `\ln` [VED02]; explicit `\log_2` [KW20]; implicit natural [UME62] [HIA18] [WIT18] [HS17] | $D_{\mathrm{KW20}}=D/\ln 2$. Weightless for the definition ((X10)) but **two corpus statements are base-locked**: WIT18's positivity step $\log\lambda\le\lambda-1$ is false in base 2, and any pairing of $D$ with an exponential (Stein exponents) fixes the base |
| (C4) | normalisation of the arguments | none — both range over $M_*^+$ | both states: [UME62] main text, [VED02], [WIT18], [HS17] base case, [HIA18] (D2). First normalised / second free: [KW20], and **[UME62] footnote 5) in the semifinite case**. Both free: [HIA18] (D4), [HS17]'s extension | [HS17] gives the two-parameter rule $H(\lambda\omega,\lambda'\omega')=\lambda H+\lambda\log(\lambda/\lambda')$; [HIA18] states only joint homogeneity $S_f(\lambda\rho\|\lambda\sigma)=\lambda S_f(\rho\|\sigma)$. Consistent, but (R10)(h4) needs the former |
| (C5) | mechanism for the singular case | boundary term | hypothesis [UME62]; case split [HIA18](D2) [KW20]; boundary term [HIA18](D4); regularised limit [KW20]; consequence of a zero eigenvalue [WIT18]; silence [VED02] | all give $+\infty$ where all are defined; only the *shape* differs |
| (C6) | spelling of the support condition | $s_M(\rho)\le s_M(\sigma)$ | $s(\rho)\le s(\sigma)$ [HIA18]; $\operatorname{supp}(\rho)\subseteq\operatorname{supp}(\sigma)$ [KW20]; $\sigma\prec\rho$ [UME62], in its own letters | one condition, three spellings; always the dominated support is on the differentiated argument |
| (C7) | conjugate-linearity of the inner product | first slot | **no source in the corpus states it.** Inferred (tier (b)) from [HIA18] writing $\sigma(x)=\langle\xi_\sigma,x\xi_\sigma\rangle$ with $J$ a conjugate-linear involution, and [WIT18]'s Dirac notation | value-irrelevant for $\langle\xi,A\xi\rangle$ with $A$ self-adjoint |
| (C8) | domain of the functional | $M_*^+\times M_*^+$ | [HS17] extends to **all** positive functionals of a C\*-algebra, setting $H=\infty$ off the normal ones | a stipulated totalisation, not covered by the adopted form. **[HS17] is internally inconsistent**: its Definition totalises on the second argument only, while its (h1) reads as totalising on both |

## Results and dependencies

Grouped by source. Numbering is this note's.

### (R1) $S_f(\rho\|\sigma)$ is well defined in $(-\infty,+\infty]$

For every $\rho,\sigma\in M_*^+$ and convex $f$, the expression of the adopted
form is well defined with values in $(-\infty,+\infty]$; in particular the
relative entropy never takes the value $-\infty$.

- Source: [HIA18] Lemma 2.2 · tier (a) · **proved in source**
- Depends on: (A6), convexity of $f$ — which $t\log t$ satisfies, and which is
  strictly weaker than the (A7) needed later, [ext: HIA18 §2.1 cites
  [Ar2, Lemma 2.2] for the closability of $S_{\rho,\sigma}$ and
  $F_{\rho,\sigma}$ and the identity
  $S^*_{\rho,\sigma}=\overline{F_{\rho,\sigma}}$, which is what makes
  $\Delta_{\rho,\sigma}$ a positive self-adjoint operator]
- Conventions: (C4)
- Proof route: (i) convexity gives an affine minorant $f(t)\ge a+bt$; (ii)
  integrate it against $d\|E_{\rho,\sigma}(t)\xi_\sigma\|^2$; (iii) the constant
  term evaluates to $a\,\sigma(s_M(\rho))$ by the support identity of (A6); (iv)
  the linear term evaluates to $b\,\rho(s_M(\sigma))$, using
  $J\Delta^{1/2}\xi_\sigma=s_M(\sigma)\xi_\rho$ from the closability edge; (v)
  both are finite reals, so the integral exceeds $-\infty$.
- Verbatim:
  > For every $\rho,\sigma\in M_*^+$, $S_f(\rho\|\sigma)$ is well defined with values in $(-\infty,+\infty]$.

### (R2) Invariance, degenerate values, homogeneity, direct-sum additivity

(1) $S_f(\rho\circ\Phi\|\sigma\circ\Phi)=S_f(\rho\|\sigma)$ for a
\*-isomorphism $\Phi$. (2) $S_f(0\|\sigma)=f(0^+)\sigma(1)$,
$S_f(\rho\|0)=f'(+\infty)\rho(1)$, $S_f(\sigma\|\sigma)=f(1)\sigma(1)$.
(3) $S_f(\lambda\rho\|\lambda\sigma)=\lambda S_f(\rho\|\sigma)$ for
$\lambda\ge0$. (4) Additivity over a **direct sum** $M=M_1\oplus M_2$.

- Source: [HIA18] Proposition 2.3 · tier (a) · **proved in source**
- Depends on: (A6), [ext: Haagerup's uniqueness of the standard form up to a
  unitary intertwining the modular conjugations and natural cones — needed for
  (1) only]
- Conventions: (C4)
- Proof route: (1) uniqueness of the standard form; (2) directly from the
  definition; (3) substitute $\xi_{\lambda\sigma}=\sqrt\lambda\,\xi_\sigma$ and
  $\Delta_{\lambda\rho,\lambda\sigma}=\Delta_{\rho,\sigma}$, with $\lambda=0$
  from (2); (4) the standard form of a direct sum is the direct sum of the
  standard forms, so $\Delta$ decomposes and the definition reads off.
- **This is direct-sum, not tensor-product, additivity.** No tensor additivity
  statement appears in [HIA18]; the tensor statement is (R11), (R18), (R10)(h7),
  (R15)(3), and they must not be merged.

### (R3) The modular form reproduces the trace form on a type I factor

For $M=\mathcal B(\mathcal H)$ with $\mathcal H$ arbitrary,
$\Delta_{\rho,\sigma}=L_{D_\rho}R_{D_\sigma^{-1}}$ (generalised inverse), and
$S_f(\rho\|\sigma)$ evaluates to the double sum
$\sum_{a>0}\sum_{b>0}bf(a/b)\mathrm{Tr}\, P_aQ_b$ plus the two boundary terms. At
$f=t\log t$ this is $\mathrm{Tr}\, D_\rho(\log D_\rho-\log D_\sigma)$ when
$s_M(\rho)\le s_M(\sigma)$ and $+\infty$ otherwise.

- Source: [HIA18] Example 2.6 and Remark 2.7 · tier (a) · **proved in source**
- Depends on: (R1), the standard form of $\mathcal B(\mathcal H)$ on the Hilbert–Schmidt class with
  $J=\ {}^*$
- Conventions: (C5), (C6)
- **This is the corpus's cleanest statement that the adopted form restricts to
  the trace form — but it is for $\mathcal B(\mathcal H)$, not for a general semifinite algebra.**
- Verbatim:
  > On the other hand, $S_{t\log t}(\rho\|\sigma)$ in \eqref{F-2.6} coincides with the usual \emph{relative entropy}

### (R4) The commutative case is the classical $f$-divergence

For $M\cong L^\infty(\Omega,\mu)$ with $\mu$ σ-finite and $\rho,\sigma$ given by
densities $\phi,\psi$, $\Delta_{\rho,\sigma}$ is multiplication by the classical
Radon–Nikodym derivative and $S_f(\rho\|\sigma)$ equals
$\int_{\{\phi>0\}\cap\{\psi>0\}}\psi f(\phi/\psi)\,d\mu$ plus the two boundary
integrals — the classical $f$-divergence, hence at $f=t\log t$ the
Kullback–Leibler divergence.

- Source: [HIA18] Example 2.5 · tier (a) · **proved in source** (HIA18 calls the
  computation straightforward)
- Depends on: (R1)
- Conventions: (C6)
- The σ-finiteness here is the *example's*, needed to write $M_*\cong L^1$; it is
  not a hypothesis of the adopted form. Mutually singular measures give
  $+\infty$, the correct classical value.

### (R5) Transpose symmetry

$S_f(\rho\|\sigma)=S_{\widetilde f}(\sigma\|\rho)$ with
$\widetilde f(t):=tf(1/t)$. Since $t\log t$ and $-\log t$ are transposes,
$D(\sigma\|\rho)=S_{t\log t}(\sigma\|\rho)=S_{-\log t}(\rho\|\sigma)$.

- Source: [HIA18] Proposition 2.4 and Example 3.12 · tier (a) · **proved in
  source**
- Depends on: (R1), (A6) — for the support identity
  $s_M(\rho)s_{M'}(\sigma)=Js_M(\sigma)s_{M'}(\rho)J$ used at step (ii),
  [ext: HIA18 §2.2 cites [Ar2, Theorem 2.4] for
  $\Delta_{\rho,\sigma}=J\Delta_{\sigma,\rho}^{-1}J$]
- Proof route: (i) $\widetilde f(0^+)=f'(+\infty)$ and
  $\widetilde f{}'(+\infty)=f(0^+)$, so only the spectral term needs work;
  (ii) apply the $J$-conjugation identity together with
  $s_M(\rho)s_{M'}(\sigma)=Js_M(\sigma)s_{M'}(\rho)J$; (iii) convert the spectral
  measure of one pair into that of the other; (iv) change variables in the
  integral.

### (R6) Variational expression

For $f$ operator convex, $S_f(\rho\|\sigma)$ equals a supremum over $n$ and over
$M$-valued step functions of an explicit expression; see (D9).

- Source: [HIA18] Theorem 3.5 · tier (a) · **proved in source**
- Depends on: (R1), (A7), [ext: the Lesniewski–Ruskai integral representation of
  an operator convex function on $(0,\infty)$ as
  $a+b(t-1)+c(t-1)^2+\int(t-1)^2/(t+s)\,d\mu(s)$ with $c\ge0$, $\mu\ge0$
  and the data unique — HIA18 cites it as `\cite{LR}`, which is
  **Lesniewski**–Ruskai 1999, not Lieb–Ruskai]
- Conventions: (C4)
- Proof route: (i) rewrite $S_{f_n}$ using the truncated representation; (ii)
  HIA18 Lemma 3.4 turns the spectral integral into an infimum over $M$-valued
  step functions; (iii) take $\sup_n$ and apply HIA18 Lemma 3.2's monotone
  convergence $S_{f_n}\nearrow S_f$.
- **This is the engine of the whole theory**: (R7) and everything after it is
  read off from it.

### (R7) Joint lower semicontinuity, joint convexity, monotonicity, martingale convergence

For $f$ operator convex and $\rho,\sigma\in M_*^+$: (i) $(\rho,\sigma)\mapsto
S_f(\rho\|\sigma)$ is jointly lower semicontinuous in the $\sigma(M_*,M)$
topology; (ii) it is jointly convex and jointly subadditive; (iii) it is
monotone in each argument under the stated sign conditions on $f(0^+)$ and
$f'(+\infty)$; (iv) **data processing** — for $\Phi:N\to M$ **unital**, positive,
normal and a Schwarz map, $S_f(\rho\circ\Phi\|\sigma\circ\Phi)\le
S_f(\rho\|\sigma)$; (v) martingale convergence along an increasing net of unital
subalgebras generating $M$.

- Source: [HIA18] Theorem 4.1 · tier (a) · **proved in source**, all five parts
- Depends on: (R6), (R2)(3), (A7), (A11)
- Conventions: (C4). $\Phi$ acts on observables, so states pull back — the
  Heisenberg picture. **Schwarz is strictly weaker than 2-positive and much
  weaker than completely positive**, so this is a stronger theorem than the
  usual CPTP data-processing inequality.
- Proof route: (i)+(ii) the bracketed expression in the variational formula is
  affine and $\sigma(M_*,M)$-continuous in $(\rho,\sigma)$, and a supremum of
  such is jointly lsc and jointly convex — convexity and subadditivity being
  equivalent by the homogeneity of (R2)(3); (iii) read off the sign of the
  boundary coefficients in the same formula; (iv) push an $N$-valued step
  function $x(\cdot)$ to $y(s):=\Phi(x(s))$ and use unitality plus the Schwarz
  inequality to dominate each bracket, then take suprema; (v) take the dense
  subspace in (R6) to be $\bigcup_\alpha M_\alpha$, so that restricting the step
  functions recovers the restricted divergence.
- Verbatim:
  > \emph{Monotonicity:} Let $N$ be another von Neumann algebra and $\Phi:N\to M$ be a unital positive linear map that is normal

### (R8) Peierls–Bogoliubov and strict positivity

(1) $S_f(\rho\|\sigma)\ge\sigma(1)f(\rho(1)/\sigma(1))$, with equality (for
non-linear $f$, nonzero arguments) iff $\rho=(\rho(1)/\sigma(1))\sigma$.
(2) If $f$ is non-linear with $f(1)=0$ and $\rho(1)=\sigma(1)>0$ then
$S_f(\rho\|\sigma)\ge0$ with equality iff $\rho=\sigma$. At $f=t\log t$ this is
**non-negativity of the relative entropy with the equality case, on an arbitrary
von Neumann algebra**.

- Source: [HIA18] Corollary 4.2 · tier (a) · **proved in source**
- Depends on: (R7)(iv), (A3), (A7), (A8), and HIA18's own Lemma 4.3 — an
  elementary strict-convexity lemma it proves in source "since we find no
  suitable reference"
- Conventions: (C4) — the hypothesis $\rho(1)=\sigma(1)$ is not decorative; see
  the degeneracy row for dropped normalisation.
- Proof route: (i) apply (R7)(iv) to the subalgebra $\mathbb C1$, which is
  exactly the scalar computation and yields the Peierls–Bogoliubov bound;
  (ii) if $\rho=k\sigma$ then $\Delta_{\rho,\sigma}=k\Delta_\sigma$, the spectral
  measure is a point mass and equality holds; (iii) conversely apply (R7)(iv) to
  $\mathbb Ce+\mathbb Ce^\perp$ for each projection $e$; (iv) Lemma 4.3 forces
  proportionality on every projection, hence $\rho=(\rho(1)/\sigma(1))\sigma$;
  (v) part (2) is part (1) evaluated at $f(1)=0$ under the equal-mass hypothesis
  $\rho(1)=\sigma(1)>0$ of (A3), with (A8) supplying the strictness.
- **Dependency inversion worth recording**: here non-negativity is a *corollary
  of data processing*, not of Klein's inequality.
- Verbatim:
  > \emph{Strict positivity:} Assume that $f$ is non-linear with $f(1)=0$ and $\rho(1)=\sigma(1)>0$. Then $S_f(\rho\|\sigma)\ge0$, and $S_f(\rho\|\sigma)=0$ $\iff$ $\rho=\sigma$.

### (R9) Support reduction, orthogonal-support additivity, $\varepsilon$-regularisation

(1) If $s_M(\rho),s_M(\sigma)\le e$ then $S_f(\rho\|\sigma)=S_f(e\rho e\|e\sigma e)$
computed in $eMe$. (2) If the joins of the supports of two pairs are orthogonal,
$S_f$ is additive over the sum. (3) If $S_f(\omega_1\|\omega_2)<+\infty$ then
$S_f(\rho\|\sigma)=\lim_{\varepsilon\searrow0}S_f(\rho+\varepsilon\omega_1\|\sigma+\varepsilon\omega_2)$.

- Source: [HIA18] Corollary 4.4 · tier (a) · **proved in source**
- Depends on: (R6), (R7)(i), (R7)(ii), (R7)(iv), (R2)(3), (R2)(4)
- Proof route: (1) "$\le$" by (R7)(iv), "$\ge$" by pushing $x(s)\mapsto ex(s)e$
  through (R6); (2) "$\ge$" via the subalgebra $eMe\oplus e^\perp Me^\perp$ with
  (R7)(iv) and (R2)(4) and part (1), "$\le$" via the unital map
  $x\mapsto exe+e^\perp xe^\perp$ and (R7)(iv); (3) "$\le$" from (R7)(i),
  "$\ge$" from (R7)(ii) with (R2)(3).
- **(3) is the general-algebra analogue of (R14)**, and it is *conditional*: it
  needs a reference pair of finite divergence, which $\sigma+\varepsilon\mathbb1$
  supplies only where a trace does.

### (R10) The property list of the Araki relative entropy

[HS17] enumerates (h1) positivity with the equality case, and $H=\infty$ for
non-normal arguments; (h2) weak lower semicontinuity **on the positive
functionals of a C\*-algebra**; (h3) subadditivity, equivalently convexity; (h4)
superadditivity in the first argument; (h5) monotonicity in the arguments; (h6)
Uhlmann's monotonicity theorem for normalised completely positive maps, with
equality for a faithful normal conditional expectation preserving a faithful
normal state; (h7) the tensor **chain rule**
$H(\omega,\omega'_1\otimes\omega'_2)=H(\omega,\omega_1\otimes\omega_2)+H(\omega_1,\omega'_1)+H(\omega_2,\omega'_2)$.

- Source: [HS17], the (h1)–(h7) enumeration · tier (a) for the list, tier (c) for
  each claim · **asserted** — every item is cited to Ohya–Petz, none is proved
- Depends on: [ext: Ohya–Petz, *Quantum entropy and its use* — a monograph
  treatment of the Araki relative entropy establishing positivity with the
  equality case, joint lower semicontinuity, joint convexity, superadditivity in
  the first argument, monotonicity in both arguments and under normalised
  completely positive maps, and the tensor chain rule. HS17 gives no theorem
  numbers]; for (h6) additionally [ext: Lindblad 1973 and Uhlmann 1977 —
  monotonicity of the relative entropy under normalised completely positive maps
  between von Neumann algebras]
- Conventions: (C4) — (h4) needs HS17's two-parameter rescaling rule and is
  **not** derivable from the joint homogeneity of (R2)(3); (C8) for (h2).
- Independent corpus support: (h1) is (R8)(2), (R12), (R15); (h2) is (R7)(i) but
  only on $M_*^+$, a smaller domain; (h3) is (R7)(ii); (h5) is (R7)(iii);
  (h6) is (R7)(iv), (R13), (R14), (R19). **(h4) and (h7) rest on Ohya–Petz alone
  within this corpus.** Both were verified in finite dimensions during the
  refutation pass — (h4) reduces exactly to the Holevo bound
  $\chi\le H(\{\lambda_i\})$ via the compensation identity, with equality iff the
  states are mutually orthogonal; (h7) is an algebraic identity needing no
  product hypothesis on $\omega$.
- **(h5) is degenerate as printed**: for positive functionals on a unital
  algebra, $\phi\le\omega$ with $\|\phi\|=\|\omega\|$ forces $\phi=\omega$, so
  its first-argument clause is vacuous and (h5) states only monotonicity in the
  second argument.
- Verbatim:
  > (h1)] (positivity) $H(\omega, \omega') \ge 0$, and $H(\omega,\omega') = 0 \Rightarrow \omega=\omega'$ for states $\omega, \omega'$.

### (R11) Additivity over tensor products (Umegaki)

For $A_1,A_2$ **of finite class** with faithful normal traces, $A=A_1\otimes A_2$
with $\tau=\tau_1\otimes\tau_2$, and $a_i\prec b_i$ in $\mathcal E(A_i)$:
$I(a_1\otimes a_2,\,b_1\otimes b_2)=I(a_1,b_1)+I(a_2,b_2)$, and likewise for the
divergence $J$. Corollary: $H(a_1\otimes a_2)=H(a_1)+H(a_2)$.

- Source: [UME62] Theorem 3 and Corollary 3.1, §6 · tier (b),
  `mineru-unchecked` · **proved in source**
- Depends on: (R7'), (A2), (A3), [ext: the tensor product of two von Neumann
  algebras of finite class, with the tensor product of two faithful normal
  traces, is again of finite class with a faithful normal trace — UME62 cites
  Dixmier and Misonou by name for the direct-product construction]
- Conventions: (C1), (C4)
- Proof route: (i) split $\log(a_1\otimes a_2)$ into
  $\log(a_1\otimes1)+\log(1\otimes a_2)$, an identity UME62 uses without proof;
  (ii) regroup into the two bracketed differences, each of which is an
  information in its own factor and therefore defined by (R7') under (A2);
  (iii) factor $\tau=\tau_1\otimes\tau_2$ across elementary tensors, which is
  where the Dixmier–Misonou edge enters; (iv) use $\tau(a_i)=1$ from (A3) to
  kill the cross terms.
- Umegaki identifies this as the operator generalisation of the
  Kullback–Leibler form of the Shannon–Wiener theorem for independent events.
  It is **not** (R2)(4).

### (R7') Non-negativity of the information

For $a,b\in\mathcal E$ with $a\prec b$, $I(a,b)$ is uniquely determined and, when
finite, non-negative. Likewise for normal states of finite entropy.

- Source: [UME62] Theorem 1, Corollary 4.1, Theorem 1′, §4 · tier (b),
  `mineru-unchecked` · **proved in source**
- Depends on: (A2), (A3), and UME62's own Lemma 7.1 ($a\prec b$ implies
  $a^e\prec b^e$) and Corollary 2.1, both proved in source, [ext: the operator
  entropy $h(a)=-a\log a$ is operator concave and satisfies $h(E[a|B])\ge
  E[h(a)|B]$ for every von Neumann subalgebra $B$ — UME62 attributes this to
  Nakamura–Umegaki and independently to Davis, generalising Segal], [ext: the
  classical Kullback–Leibler inequality that the information of two probability
  densities is non-negative, with the second-order mean-value expansion of
  $-h(\lambda)$ — UME62 cites Kullback–Leibler]
  ((A1) is standing in [UME62] and so carries no edge, though the whole
  statement is written through its trace.)
- Proof route: (i) for bounded $b$, Proposition 4.1(ii) makes $I(a,b)$
  unambiguous; (ii) condition onto the **commutative** algebra generated by $b$
  and apply the operator Jensen inequality $a^e\log a^e\le(a\log a)^e$;
  (iii) Lemma 7.1 propagates $a\prec b$ to $a^e\prec b^e$, so by Corollary 2.1
  the cross term conditions cleanly;
  (iv) subtracting reduces the claim to $I(a^e,b)\ge0$, where the two
  operators commute; (v) expand $-h(\lambda)$ to second order and use
  $\tau(a)=\tau(b)=1$ to kill the linear part, leaving a manifestly non-negative
  trace; (vi) for unbounded $b$, approximate monotonically inside the algebra
  generated by $b$ and rule out two limits by a commutation argument.
- **The dependency order is the reverse of (R8)**: here non-negativity is
  primitive and monotonicity ((R12)) is derived from it.

### (R12) Monotonicity under a conditional expectation — **doubly conditional**

Theorem 4: for $a,b\in\mathcal E$ **affiliated with the commutant $B'$**,
$I(a^e,b^e)\le I(a,b)$ where $e=E[\cdot|B]$. Theorem 4′: for normal states of
finite entropy **in the $B$-tracelet space $T_B$** — i.e. $\sigma(xy)=\sigma(yx)$
for all $x\in A$, $y\in B$ — $I_B(\sigma,\rho)\le I(\sigma,\rho)$.

- Source: [UME62] Theorems 4 and 4′, §7 · tier (b), `mineru-unchecked` ·
  **proved in source**
- Depends on: (R7'), (A2), (A3), (A10), and UME62's Corollary 2.1 and Lemma 7.2,
  both proved in source
- Proof route: (i) expand $I(a,b)-I(a^e,b^e)$ using Corollary 2.1 to
  replace $\tau(a^eX)$ by $\tau(aX)$; (ii) invoke Lemma 7.2 — this is
  precisely where affiliation with $B'$ buys mutual commutation of the four
  operators — to combine the three logarithms; (iii) recognise the result as
  $I(a,\,b\,a^e(b^e+(I-q'))^{-1})$, whose second argument is positive with trace
  1 by (A3); (iv) apply (R7') to that residual pair, which needs (A2);
  (v) for Theorem 4′, transport
  $\sigma\prec\rho$ through the densities and identify $(d\sigma/d\tau)^e$ with
  $d\sigma_B/d\tau_B$.
- **[UME62] does not prove data processing in the modern sense.** Neither
  hypothesis appears in (R7)(iv); this is the note's sharpest correction to the
  standard story that "Umegaki proved monotonicity".

### (R13) Sufficiency of a subalgebra as the equality case

Under a commutativity hypothesis on the density system, $B$ is sufficient for a
family $S$ of faithful normal states iff $I_B=I$ on every pair of $S$, iff
$J_B=J$ on every pair.

- Source: [UME62] Theorem 5, §8 · tier (b), `mineru-unchecked` · **proved in
  source**, importing a criterion from Umegaki's own part III
- Depends on: (R12), (A2), (A10), UME62's Lemma 7.2, and UME62's Theorem 2 — the
  equality case $I(a,b)=0\iff a=b$ under $ab=ba$, proved in source, [ext:
  Umegaki, *Conditional expectation in an operator algebra III* — a von Neumann
  subalgebra $B$ is sufficient for a family $S$ of faithful normal states iff
  $d(\sigma)d(\rho)^{-1}=d(\sigma)^ed(\rho)^{e-1}$ for every pair in $S$]
- Proof route: (i) replace sufficiency by that criterion; (ii) Lemma 7.2 makes
  the four densities mutually commuting, which is what (A10) buys and what makes
  (R12) applicable to the family $S\subset T_M\subset T_B$; (iii) **the
  monotonicity defect is itself an information**,
  $I(\sigma,\rho)-I_B(\sigma,\rho)=I(d(\sigma),\,d(\rho)d(\sigma)^ed(\rho)^{e-1})$,
  which is defined because the pair lies in $\mathcal E$ by (A2); (iv) apply
  Theorem 2 to that commuting pair; (v) symmetrise for the $J$ version.
- Step (iii) is the mathematically interesting content and is worth carrying
  forward independently of the sufficiency statement.

### (R14) The finite-dimensional reduction of the Araki form (Witten)

For $\mathcal H_1\otimes\mathcal H_2$ with $\Psi$ cyclic separating, reduced density matrices
$\rho_1,\rho_2$, and a second vector $\Phi$ with reduced density matrices
$\sigma_1,\sigma_2$: $\Delta_{\Psi|\Phi}=\sigma_1\otimes\rho_2^{-1}$, hence
$\mathcal S_{\Psi|\Phi}=\mathrm{Tr}\,\rho_1(\log\rho_1-\log\sigma_1)$.

- Source: [WIT18] §"Monotonicity of Relative Entropy In The Finite-Dimensional
  Case" · tier (a) · **proved in source**
- Depends on: (A4), (A5), WIT18's earlier computation of $\Delta_{\Psi|\Phi}$,
  and the conjugacy of the two reduced density matrices of a pure state
- Conventions: (C2), (C3)
- Proof route: (i) substitute WIT18's $\Delta_{\Psi|\Phi}=\sigma_1\otimes\rho_2^{-1}$,
  available because (A4) makes $\Delta_{\Psi|\Phi}$ densely defined and (A5)
  makes $\rho_2^{-1}$ an honest inverse, and split the logarithm;
  (ii) trace out $\mathcal H_2$ in the first term; (iii) in the
  second, use conjugacy to rewrite $\mathrm{Tr}_2\rho_2\log\rho_2$ as
  $\mathrm{Tr}_1\rho_1\log\rho_1$; (iv) combine.
- Verbatim:
  > We have arrived at the usual definition of the relative entropy in nonrelativistic quantum mechanics.

### (R15) Non-negativity in the vector formulation, with a different equality case

$\mathcal S_{\Psi|\Phi}(\mathcal U)\ge0$, vanishing **precisely when $\Phi=a'\Psi$ for a unitary
$a'$ in the commutant $\mathcal A_{\mathcal U}'$** — equivalently, when $\Phi$ and $\Psi$ induce
the same state on $\mathcal A_{\mathcal U}$.

- Source: [WIT18] §"Relative Entropy In Quantum Field Theory" · tier (a) ·
  **proved in source**, for a general von Neumann algebra with a cyclic
  separating vector
- Depends on: (A3), (A4), [ext: WIT18 credits the scalar-inequality argument to
  Araki's 1976 paper]
- Conventions: (C3) — the step $\log\lambda\le\lambda-1$ is base-locked
- Proof route: (i) $\log\lambda\le\lambda-1$ lifts by functional calculus to
  $-\log\Delta_{\Psi|\Phi}\ge1-\Delta_{\Psi|\Phi}$; (ii) take the expectation in
  $\Psi$ and use the normalisation $\|\Psi\|=\|\Phi\|=1$ of (A3) to get $0$;
  (iii) equality saturates
  the scalar inequality only at $\lambda=1$, forcing
  $\Delta_{\Psi|\Phi}\Psi=\Psi$; (iv) this equates all matrix elements of
  $\mathcal A_{\mathcal U}$ in the two vectors; (v) cyclicity (A4) turns $a\Psi\mapsto a\Phi$ into
  a unitary in the commutant.
- **Do not merge this equality case with (R8)(2)'s $\rho=\sigma$.** They agree:
  $\Phi=a'\Psi$ is exactly the condition that the two vectors give the same state.
- Verbatim:
  > ```
  > An important elementary property is that $\S_{\Psi|\Phi}(\U)$ is always non-negative, and vanishes precisely if $\Phi=\a'\Psi$
  > ```

### (R16) Monotonicity under shrinking the region

If $\widetilde{\mathcal U}\subset\mathcal U$ then $\mathcal S_{\Psi|\Phi}(\mathcal U)\ge\mathcal S_{\Psi|\Phi}(\widetilde{\mathcal U})$,
reduced to the operator inequality
$\Delta_{\widetilde{\mathcal U}}\ge\Delta_{\mathcal U}$ in the resolvent sense.

- Source: [WIT18] §"Monotonicity of Relative Entropy" and §"The Proof" ·
  tier (a) · **proved in source**, self-containedly
- Depends on: (A4), (A9), [ext: the projection onto the graph of a closed densely
  defined operator $T$ is the explicit $2\times2$ matrix with entries built from
  $(1+T^*T)^{-1}$ — WIT18 attributes the computation to Stone and to Halmos],
  [ext: Borchers' argument that the modular operator increases as the region
  shrinks, from the ordering of graph projections]
- Proof route: (i) write the graph projection explicitly; (ii) if $T_1$ extends
  $T_0$ then the graphs nest and the projections are ordered; (iii) evaluate the
  projections on vectors of the form $(\psi,0)$ to get
  $\langle\psi,(1+T_0^*T_0)^{-1}\psi\rangle\le\langle\psi,(1+T_1^*T_1)^{-1}\psi\rangle$;
  (iv) rescale $T_i\mapsto T_i/\sqrt s$ to get the resolvent statement at every
  $s>0$; (v) take $T_0=S_{\widetilde{\mathcal U}}$, $T_1=S_{\mathcal U}$, legitimate because the
  larger algebra has more vectors $a|\Psi\rangle$; (vi) operator monotonicity of
  $\log$ (A9) from the resolvent integral representation; (vii) take the
  expectation in $\Psi$ and flip the sign.
- Verbatim:
  > The inequality (\ref{wonorf}) is a direct consequence of an operator inequality

### (R17) The Araki form in Haagerup $L^1$ — the closest thing to a general reduction

For $\varphi\in M_*^+$ faithful and $\omega=\varphi^h$ with $h\in M_{\mathrm{sa}}$, one has
$h_\omega=\exp(\log h_\varphi+h)$ in Haagerup's $L^1(M)$ and consequently
$D(\omega\|\varphi)=\mathrm{tr}(h_\omega(\log h_\omega-\log h_\varphi))$, with $\mathrm{tr}$ the
canonical trace on the crossed product.

- Source: [HIA18], Appendix B closing remark · tier (a) · **sketched** — the key
  identity is imported wholesale
- Depends on: HIA18's Proposition 5.3(3), that the relative entropy is the
  $\alpha\to1$ limit of the Petz–Rényi divergences, and its Theorem B.2, both
  proved in source, [ext: a Trotter-type product formula in the spatial
  $L^p$-spaces], [ext: Terp's isomorphism between spatial and Haagerup
  $L^p$-spaces], [ext: HIA18 cites Araki's 1973 relative-Hamiltonian paper for
  uniqueness of the relative Hamiltonian], [ext: HIA18 cites Donald's theorem
  that a finite infimum of $h(\rho)+D(\rho\|\varphi)$ over normal states is attained
  at a unique normal state]
- **The source's own hedge and its own limitation**: HIA18 calls this a
  "complete resemblance" to Umegaki's formula, and says explicitly that when the
  relative Hamiltonian is unbounded above it is problematic whether the formulas
  still make sense. The trace is on a crossed product, not on $M$. **This is not
  a reduction theorem.**
- Verbatim:
  > which has a complete resemblance to Umegaki's relative entropy in the semifinite case (see \eqref{F-1.1}).

### (R18) The support condition as an $\varepsilon$-limit

$D(\rho\|\sigma)=\lim_{\varepsilon\to0^+}\mathrm{Tr}\,[\rho(\log_2\rho-\log_2(\sigma+\varepsilon\mathbb1))]$,
hence $D(\rho\|\sigma)=\lim_{\varepsilon\to0^+}D(\rho\|\sigma+\varepsilon\mathbb1)$.

- Source: [KW20] Proposition (`prop-rel_ent_lim`) · tier (a) · **proved in
  source**
- Depends on: (A5)
- Conventions: (C3), (C5), (C6)
- Proof route: (i) $\sigma+\varepsilon\mathbb1$ has full support, so the
  expression is finite for each $\varepsilon>0$; (ii) block-decompose $\rho$ and
  $\sigma$ along $\operatorname{supp}\sigma\oplus\ker\sigma$; (iii) if supports nest, the
  off-support blocks vanish and the limit is the finite value; (iv) otherwise the
  $\log_2\varepsilon$ term diverges, giving $+\infty$.
- **This is what justifies the $+\infty$ branch as the right value rather than a
  convention.** Its general-algebra analogue is (R9)(3), which is conditional.

### (R19) Basic properties in finite dimensions

Isometric invariance; Klein's inequality $D(\rho\|\sigma)\ge0$ **under
$\mathrm{Tr}\,\sigma\le1$**; faithfulness; monotonicity in $\sigma$; tensor additivity with
the rescaling corollary $D(\rho\|\beta\sigma)=D(\rho\|\sigma)+\log_2(1/\beta)$;
and the direct-sum property for classical–quantum states.

- Source: [KW20] Proposition (`prop-rel_ent`) · tier (a) · **proved in source**
- Depends on: (R18), (A5)
- Conventions: (C3), (C4). **Note the shape of Klein's inequality here.** Because
  the second argument need only be positive semi-definite, non-negativity is
  conditional on $\mathrm{Tr}\,\sigma\le1$; (R8)(2) instead requires
  $\rho(1)=\sigma(1)>0$; (R10)(h1) assumes both are states. **Three different
  statements.**

### (R20) Data processing in finite dimensions, and the properties derived from it

$D(\rho\|\sigma)\ge D(\mathcal N(\rho)\|\mathcal N(\sigma))$ for every quantum
channel $\mathcal N$. Klein's inequality, isometric invariance and joint
convexity are then all corollaries.

- Source: [KW20] Theorem (`thm-monotone_rel_ent`), via the Petz–Rényi route, and
  the following Proposition · tier (a) · **proved in source**, with the operator
  Jensen inequality and Stinespring's theorem also proved in the book
- Depends on: (R19), (A5), (A11), and — proved in [KW20] itself, not cited —
  Stinespring's theorem, the operator Jensen inequality in the form
  $f(V^*XV)\le V^*f(X)V$ for isometric $V$, and the convergence
  $D_\alpha\to D$ as $\alpha\to1$, [ext: KW20 states the operator convexity
  of $x\mapsto x^\beta$ on $[-1,0)\cup[1,2]$ and operator concavity on $(0,1]$ as
  a numbered fact, deferring the proof to its bibliographic notes]
- Proof route: (i) Stinespring plus isometric invariance reduce a channel to a
  partial trace; (ii) reduce to invertible operators by a double limit;
  (iii) write the Petz–Rényi quantity as a vector expectation of
  $f(\rho^{-1}\otimes\sigma^{T})$ with $f(x)=x^{1-\alpha}$; (iv) construct the
  isometry $V$ carrying the smaller purification to the larger; (v) apply
  operator Jensen in the form $f(V^*XV)\le V^*f(X)V$; (vi) compute $V^*(\cdot)V$
  to be the reduced object; (vii) translate through $\log$, flipping direction
  where $\alpha<1$; (viii) take $\alpha\to1$.
- Verbatim:
  > One of the remarkable aspects of the data-processing inequality for the qua\-ntum relative entropy is that it alone can be used to prove many of the properties of the quantum relative entropy stated in Proposition~\ref{prop-rel_ent}.

### (R21) The operational meaning: quantum Stein's lemma

For all states $\rho,\sigma$, the optimal achievable rate and the strong converse
rate for asymmetric quantum hypothesis testing both equal $D(\rho\|\sigma)$; in
the singular case both are $+\infty$.

- Source: [KW20] Theorem (`thm-q_Stein_lemma`) · tier (a) · **proved in source**
  (the achievability and strong-converse halves were not read through here, so no
  proof route is filed)
- Depends on: (R18), (R20), (A5), [ext: Hiai–Petz 1991 — the relative entropy is
  the optimal type-II error exponent in asymmetric hypothesis testing between
  i.i.d. copies of two states], [ext: Ogawa–Nagaoka 2000 — the strong converse]
- **This is the answer to "why this quantity and not another."**
- Verbatim:
  > For all states $\rho$ and $\sigma$, the optimal achievable and strong converse rates are equal to the quantum relative entropy of $\rho$ and $\sigma$

### Three incompatible orders of derivation

Reading the corpus as one graph, the same properties are obtained three ways, and
none is the textbook order:

- **[UME62]**: operator concavity of $-a\log a$ → non-negativity (R7') → the
  equality case → *conditional* monotonicity (R12) → sufficiency (R13).
- **[HIA18]**: the Lesniewski–Ruskai integral representation → the variational
  expression (R6) → monotonicity, joint convexity and joint lower semicontinuity
  all at once (R7) → non-negativity (R8).
- **[WIT18] / [KW20]**: an operator-monotonicity fact → monotonicity
  (R16)/(R20) → non-negativity, isometric invariance, joint convexity,
  subadditivity and strong subadditivity.

In four of the six sources **monotonicity is primitive and non-negativity is its
corollary.** Only [UME62] goes the other way, and its monotonicity is the weak,
hypothesis-laden version.

## Hypotheses

| (A#) | Statement | Class | Evidence | Witness | Scope | Tier | Used by |
|---|---|---|---|---|---|---|---|
| (A1) | $M$ carries a faithful normal (semi)finite trace | model-dependent | — | the local algebra $\mathcal A_{\mathcal U}$ of a wedge region: [WIT18] states QFT local algebras are type III and "do not have a trace -- even one defined only on part of the algebra" | standing in [UME62]; **absent from the adopted form** | a | (R7'), (R11), (R12), (R13); (D1), (D2), (D8) |
| (A2) | finite entropy $\|H(a)\|<\infty$ ([UME62]'s class $\mathcal E$) | model-dependent | — | on $A=L^\infty([0,1],dx)$ with $\tau=\int dx$ — inside UME62's own setting — the density $C/(x\log^2 x)$ on $(0,\tfrac12)$ is integrable while $\int f\log f$ diverges, so $H(f)=-\infty$ | local to [UME62] | b | (R7'), (R11), (R12), (R13) |
| (A3) | both arguments normalised (equal mass, in the general form) | provable | [HS17] extends $H$ off normalised states by the explicit two-parameter rule, so the unnormalised value is *determined*, not assumed; [HIA18] defines $S_f$ on all of $M_*^+$; [KW20] says restricting the first argument to a state is expository | — | local | a | (R7'), (R8)(2), (R11), (R12), (R15); **and it is load-bearing inside them** — see the dropped-normalisation degeneracy row |
| (A4) | $\Psi$ cyclic and separating for the algebra | model-dependent | — | any Schmidt-rank-one product vector, e.g. $\|1\rangle\otimes\|1\rangle$ in $\mathbb C^2\otimes\mathbb C^2$: [WIT18] states $\Psi$ is cyclic and separating iff all Schmidt coefficients are nonzero | local to [WIT18]'s (D6) | a | (R14), (R15), (R16) |
| (A5) | finite dimension | model-dependent | — | every infinite-dimensional system; in particular every QFT local algebra | standing in [KW20], implicit in [VED02] | a | (R14), (R18), (R19), (R20), (R21) |
| (A6) | $M$ is presented in a standard form | **provable** | [HIA18] Appendix A **constructs** one unconditionally from an arbitrary faithful normal semifinite weight: `Then $(M,L^2(M),J=\,^*,L^2(M)_+)$ becomes a standard form of $M$` — existence is tier (a) *inside the corpus*; only uniqueness up to unitary equivalence remains cited to Haagerup | — | standing throughout the adopted form | a | (R1)–(R9), and the adopted form itself |
| (A7) | $f$ is operator convex | **provable** for the two functions this object needs | $t\log t=\int_0^\infty\bigl(\tfrac{t}{1+s}-\tfrac{t}{t+s}\bigr)ds$; writing the integrand as $\tfrac{t}{1+s}-1+s(t+s)^{-1}$ exhibits it as an affine function plus a positive multiple of the operator convex $t\mapsto(t+s)^{-1}$, and operator convexity survives positive combinations and pointwise limits. Independently, [KW20] states it outright: `The function $x\mapsto x\log_b(x)$, for every base $b>0$ and $x\in[0,\infty)$, is operator convex` | — | standing in [HIA18] §§3–4 | a | (R6), (R7), (R8), (R9) |
| (A8) | a non-affine operator convex function on $(0,\infty)$ is strictly convex | **provable** | from the integral representation of (R6): $\frac{d^2}{dt^2}\frac{(t-1)^2}{t+s}=\frac{2(1+s)^2}{(t+s)^3}>0$, so $f''(t)\ge 2c+\int\frac{2(1+s)^2}{(t+s)^3}d\mu(s)>0$ unless $c=0$ and $\mu=0$, i.e. unless $f$ is affine | — | local to [HIA18] Cor. 4.2 | b | (R8) |
| (A9) | $\log$ is operator monotone | provable | the resolvent integral representation $\log R=\int_0^\infty(\tfrac1{s+1}-\tfrac1{s+R})ds$, which [WIT18] derives in source | — | local | a | (R16) |
| (A10) | [UME62]'s operators are affiliated with $B'$ / its states lie in the tracelet space $T_B$ | model-dependent | — | any pair of normal states of a non-abelian $A$ failing $\sigma(xy)=\sigma(yx)$ for some $x\in A$, $y\in B$; $T_B$ is automatic only when $B$ lies in the centre | local to [UME62] §§7–8 | b | (R12), (R13) |
| (A11) | $\Phi$ is **unital** | model-dependent | — | $\Phi:\mathbb C\to M_2(\mathbb C)$, $\Phi(\lambda)=\lambda p$ with $p=\mathrm{diag}(0,1)$: CP, normal, sub-unital and Schwarz with equality, yet $D(\rho\circ\Phi\|\sigma\circ\Phi)=\tfrac12\log 5>\tfrac12\log(25/9)=D(\rho\|\sigma)$ for $\rho=\mathrm{diag}(\tfrac12,\tfrac12)$, $\sigma=\mathrm{diag}(\tfrac9{10},\tfrac1{10})$ | local to (R7)(iv) | b | (R7)(iv), (R20) |
| (A12) | $M$ is σ-finite | model-dependent | — | $\mathcal B(\mathcal H)$ for $\mathcal H=\ell^2(I)$ with $I$ uncountable: an uncountable orthogonal family of rank-one projections cannot all receive positive value under a normal state | standing in [HS17]; in [HIA18] a **proof convenience only** — it says σ-finiteness lets one "sometimes reduce arguments", offered after the theorems are proved without it | a | (R10) only |
| (A13) | Hilbert spaces are separable | model-dependent | — | same as (A12) | standing in [HS17] — and **used by no result about this object** | a | **none** |
| (A14) | both states faithful | model-dependent as stated, **removable** | [HIA18] §2.1 supplies the modification [HS17] defers to Ohya–Petz: extending the domain from $M\xi_\sigma$ to $M\xi_\sigma\oplus(1-s_{M'}(\sigma))\mathcal H$, dense for every $\sigma$, replaces cyclicity; inserting $s_M(\sigma)$ into the value replaces separatingness, since $x\xi_\sigma=0$ forces $s_M(\sigma)x^*=0$ | $\rho=\mathrm{diag}(1,0)$ on $M_2(\mathbb C)$ | local to [HS17]'s (D7) | a | (D7) only |
| (A15) | normality of the arguments | provable that it is not a hypothesis | [HS17] admits non-normal functionals and assigns $+\infty$; [HIA18] builds normality into the ambient $M_*^+$, a typing decision | — | — | a | none |

**(A13) is a standing hypothesis that no result about this object consumes.**
[HIA18] proves the same properties, in greater generality, with no separability
anywhere. It is presumably consumed elsewhere in [HS17] (nuclearity, modular
estimates), which is outside this object.

Checked and found **not** to be hypotheses of this object: statistical
independence of two subalgebras and nuclearity (both attach to [HS17]'s
entanglement measure $E_R$, not to $H$); hyperfiniteness (searched all six
caches); commutativity $\rho\sigma=\sigma\rho$ (a hypothesis of a
well-definedness lemma only, superseded exactly as (A2) is); the type of the
algebra, which is a hypothesis of the *trace* row (A1) and of nothing else.

## Degeneracies and boundary cases

| Case | Effect on the adopted form | Tier |
|---|---|---|
| intended case is nonvacuous | **Holds, with a construction.** (R17)'s underlying identity gives $D(\rho\|\omega)=-h(\rho)+D(\rho\|\varphi)$ for $\omega=\varphi^h$ on an **arbitrary** von Neumann algebra; at $\rho=\omega$ this reads $D(\omega\|\varphi)=\omega(h)$, which [HIA18] uses outright. Instantiate on a QFT local algebra $\mathcal A(O)$ with $\varphi$ the vacuum — faithful, the vacuum being cyclic and separating, which [HS17] states at theorem strength for Lechner's integrable models along with "each $\mathcal A(O)$ is of type III$_1$" — and $h$ any nonzero positive element of $M_{\mathrm{sa}}$: then $D(\omega\|\varphi)=\omega(h)\in(0,\infty)$, **finite and strictly non-zero on a type III₁ algebra with no trace anywhere**. Corroborated non-constructively by [HS17]'s $E_R(\omega_0)>0$ together with its finite upper bound for massive BW-nuclear theories. The scaling pair $\rho=k\sigma$ is *not* an acceptable witness here: [HIA18]'s own computation shows it sees only the point spectral measure at $k$, so it never probes the relative modular operator and holds on every algebra | b |
| zero object / scalars | No effect on definedness; the values are forced. $D(0\|\sigma)=0$, $D(\rho\|0)=+\infty$ for $\rho\ne0$, $D(0\|0)=0$, $D(\sigma\|\sigma)=0$. On $M=\mathbb C$: $D(p\|q)=p\log(p/q)$, hence $0$ on states — degenerate only because $\mathbb C$ has one state, and this case is *load-bearing*, since (R8) feeds it in as the subalgebra $\mathbb C1$. On $M=\{0\}$ the only pair is $(0,0)$ | a |
| finite-dimensional | No effect on definedness; the modular form **reproduces** the trace form (R3), (R14). But "finite-dimensional ⇒ finite value" is **false**: dimension 2 already gives $+\infty$ | a |
| commutative | Reduces to the classical $f$-divergence, hence to Kullback–Leibler — **proved** in the corpus (R4). The sanity check the object exists to pass | a |
| non-separable / non-σ-finite | **No effect.** [HIA18]'s Example 2.6 is stated for "an arbitrary Hilbert space", and σ-finiteness appears only as a proof convenience (A12). [UME62] needs σ-finiteness for its $L^1(A)$ machinery and disclaims even that | a |
| type III | **Decisive.** No trace, so (D1)/(D2)/(D8) have no referent: no $\tau$, no $d_\rho$, no $\mathrm{Tr}\,$-density. The adopted form is unaffected, because the standard form exists for every von Neumann algebra (A6). [HS17] states the obstruction from the other side: generalising the *von Neumann entropy* to arbitrary type is hard, while the *relative* entropy generalises | a |
| non-unital / degenerate representation | **Non-unital algebra**: outside the class — a von Neumann algebra is unital, and no source contemplates otherwise. **Non-unital map**: fatal, see (A11). **Degenerate/non-standard representation**: no effect on the adopted form, since (R2)(1) makes it a function of the algebra and the functionals only; but fatal to (D6)/(D7), which are stated for a *given* representation and a *given* vector | a |
| universally orthogonal index element ($\operatorname{supp}\rho\perp\operatorname{supp}\sigma$) | Value $+\infty$, and this is the *correct* value, not a convention (R18). Named separating pair, computed from [WIT18]'s own finite-dimensional formula: $\mathcal H=\mathbb C^2\otimes\mathbb C^2$, $\Psi=\tfrac1{\sqrt2}(\|1,1\rangle+\|2,2\rangle)$, $\Phi=\|1,1\rangle$, i.e. $\rho_1=\mathrm{diag}(\tfrac12,\tfrac12)$, $\sigma_1=\mathrm{diag}(1,0)$. This is the pair that kills (X1) | a |
| quantifier swap: $\forall\Phi$ ↦ $\exists\Phi$ in monotonicity | **Destroys the statement.** $\Phi=\mathrm{id}$ satisfies the existential with equality for *every* two-argument functional, so the $\exists$ form carries no information | b |
| quantifier swap: $\sup_n\sup_{x(\cdot)}$ in (R6) | No-op — two suprema over independent index sets commute. Nor does $\sup_n$ differ from $\lim_n$, the net being increasing by [HIA18] Lemma 3.2. A third, non-trivial invariance: the inner quantifier may range over $L$-valued step functions for **any** subspace $L\ni1$ dense in $M$ in the strong\* topology, which is what powers the martingale-convergence proof | a |
| hypothesis dropped: (A3) normalisation | **Non-negativity fails**, and this is the cleanest degeneracy in the note: $D(\rho\|2\rho)=-\log 2<0$. Confirmed four independent ways — [HIA18]'s Peierls–Bogoliubov equality case, [HS17]'s two-parameter rescaling rule, [KW20]'s $D(\rho\|\beta\sigma)=D(\rho\|\sigma)+\log_2(1/\beta)$, and [WIT18]'s positivity proof, whose final step is exactly $\|\Psi\|^2-\|\Phi\|^2=0$. Everything else — monotonicity, joint convexity, lower semicontinuity, additivity — survives; only the *sign* is lost | a |
| hypothesis dropped: (A11) unitality of $\Phi$ | **Data processing fails**, with the named counterexample in (A11). The mechanism: the predual of a sub-unital map is trace-*decreasing*, and $D$ is not jointly scale-invariant, so unequal shrinkage of the two arguments can increase the value | b |
| hypothesis dropped: support condition | Nothing is dropped from the adopted form — it is total and returns $+\infty$. Under (D1) the quantity becomes **undefined**, not $+\infty$; that total-versus-partial difference is (D1)'s only structural departure | a |
| hypothesis dropped: (A14) faithfulness | Splits asymmetrically. Second argument: faithfulness is what makes $S_{\omega,\omega'}$ well defined in (D7), and dropping it needs (A14)'s modification. First argument: not needed at all — $\rho=\mathrm{diag}(1,0)$, $\sigma=\mathrm{diag}(\tfrac12,\tfrac12)$ gives $\log 2$, one bit | a |
| hypothesis dropped: (A4) cyclicity of $\Psi$ | **Definedness** fails for (D6), not merely the value: [WIT18] says $S_{\Psi\|\Phi}$ makes sense as a densely defined operator only then. The adopted form needs nothing of the sort | a |
| hypothesis dropped: (A2) finite entropy | No effect on the adopted form, which never splits $\tau(a\log a)-\tau(a\log b)$ into two separately-finite terms. It is an artefact of (D1)'s difference-of-two-traces presentation | b |
| hypothesis dropped: (A7) operator convexity, keeping convexity | The *definition* survives — [HIA18] Definition 2.1 needs only convexity, and (R1) still gives well-definedness. What fails is (R6) and hence everything after it. The definition and the main theorem genuinely have different hypotheses | a |

## Rejected formulations and refuted claims

**Append-only.**

| id | Candidate or claim | Disposition | Discriminator | Tier | Date |
|---|---|---|---|---|---|
| (X1) | $\mathrm{Tr}\,\rho(\log\rho-\log^+\sigma)$ with $\log^+0:=0$ — the totalised no-branch formula (Petz's quasi-entropy at $k=1$) | rejected | **(X4) source disagreement** — [HIA18] Remark 2.7 states the candidate and calls it "improper as a standard $f$-divergence" (under its hypotheses $M=\mathcal B(\mathcal H)$, $\dim\mathcal H<\infty$, $f(0^+)<\infty$); **and (X2) degeneracy** — on $\rho=\mathrm{diag}(\tfrac12,\tfrac12)$, $\sigma=\mathrm{diag}(1,0)$ it returns $-\log2<0$ for two genuine states | a | 2026-08-16 |
| (X2) | $-S(\rho)-\mathrm{Tr}\,\rho\log\sigma$, splitting into two separately-defined terms | rejected | **(X2) degeneracy** — the split is $\infty-\infty$ already in type I, at any normal state of $\mathcal B(\mathcal H)$ with infinite von Neumann entropy, whereas the difference is defined. No type III algebra is needed; [HS17] frames the contrast as one of *definability*, not generality. [UME62] itself performs the split only under "the entropy $H(a)$ is finite and $b$ is bounded" | b | 2026-08-16 |
| (X3) | density matrices on $\mathcal B(\mathcal H)$ / finite dimensions as **the** definition | rejected | **(X3) generality loss** — witness the **hyperfinite type II₁ factor**, which [WIT18] constructs: a trace exists there, but $\mathrm{Tr}\,$-densities do not, so the formula has no referent while the adopted form does. [KW20] scopes itself explicitly to finite dimensions | a | 2026-08-16 |
| (X4) | the trace formula (D1)/(D2) taken as the **general** definition | rejected | **(X3) generality loss** — witness the local algebra $\mathcal A_{\mathcal U}$ of a wedge region, type III with no trace even on part of the algebra. **Not** a rejection of (D1)/(D2) in their own semifinite scope, where they are correct and agree with the adopted form on $\mathcal B(\mathcal H)$ (R3) | a | 2026-08-16 |
| (X5) | requiring both states faithful ([HS17]) or the first vector cyclic separating ([WIT18]) as the definition's domain | rejected as a *domain choice*; both remain variants under `## Definition` | **(X3) generality loss** — named pair $\rho=\mathrm{diag}(1,0)$, $\sigma=\mathrm{diag}(\tfrac12,\tfrac12)$ on $M_2(\mathbb C)$, relative entropy $\log 2$, $\rho$ not faithful; neither (D6) nor (D7) reaches it, and both sources concede the gap. Note the asymmetry: [WIT18] constrains only the first argument, [HS17] both | a | 2026-08-16 |
| (X6) | *claim*: [UME62] introduced the "relative entropy" | refuted **as a claim about the name**; upheld as a claim about the object | `grep -F "relative entropy"` returns **zero hits** in all three independent extractions of [UME62] (MinerU `source.txt`, `source.flat.txt`, and the pypdf PDF text layer); all occurrences of "relative" are the ordinary English adverbial. The paper's object is *information* $I(\cdot,\cdot)$; *entropy* is the one-argument $H(a)$. [VED02] says as much in the corpus: "this quantity was first considered by Umegaki (1962), but for consistency reasons I name it after von Neumann" | b | 2026-08-16 |
| (X7) | *claim*: [HIA18] misdescribes [UME62]'s hypothesis by attributing the definition to a **semifinite** algebra | refuted | [UME62]'s standing hypothesis is indeed finite class + σ-finite, so HIA18's sentence is not a transcription — but §1 asserts the semifinite extension of every theorem in the paper, and **footnote 5) extends the definition itself** to the semifinite case. Of the four semi-trace footnotes, three support the extension and only footnote 4) carves anything out, and that concerns the operator-entropy of $L^p$ elements, not $I(\cdot,\cdot)$. HIA18's sentence is a **defensible generalisation of a claim the source makes about itself**; the residual gap is *proof*, not scope, since UME62's extension is asserted ("can be shown by a little or simply modified proofs") with an unverified side condition on subalgebras | b | 2026-08-16 |
| (X8) | the regularised form $\lim_{\varepsilon\to0^+}D(\rho\|\sigma+\varepsilon\mathbb1)$ | equivalent | — ([KW20] proves it, (R18)) | a | 2026-08-16 |
| (X9) | monotonicity for sub-unital (non-unital) Schwarz maps | rejected | **(X1) separating object** — $\Phi:\mathbb C\to M_2(\mathbb C)$, $\Phi(\lambda)=\lambda\,\mathrm{diag}(0,1)$, with $\rho=\mathrm{diag}(\tfrac12,\tfrac12)$ and $\sigma=\mathrm{diag}(\tfrac9{10},\tfrac1{10})$: $D(\rho\circ\Phi\|\sigma\circ\Phi)=\tfrac12\log5\approx0.805>\tfrac12\log(25/9)\approx0.511=D(\rho\|\sigma)$. The statement is **false**, not open | b | 2026-08-16 |
| (X10) | base 2 versus natural logarithm | preference-only — no discriminator found | — | a | 2026-08-16 |
| (X11) | the symmetrised divergence $J(\sigma,\rho)=I(\sigma,\rho)+I(\rho,\sigma)$ | **not a candidate reading of this object** — [UME62] gives it a separate Definition 2 on a stricter domain ($a\sim b$) and it is symmetric | — | b | 2026-08-16 |

## Prior art

| System | Found | Relation to variants | How searched | Measured at |
|---|---|---|---|---|
| Mathlib | `InformationTheory.klDiv` on measures via `Measure.rnDeriv`/`llr`, valued in `ℝ≥0∞`, `⊤` unless absolutely continuous **and** the log-likelihood ratio is integrable, with a correction term for non-probability measures | the classical special case; shares the `+∞` convention of (D2)/(D8) and is incompatible with (D5); carries a *second* `⊤` branch (non-integrability) that no quantum variant has | directory listing, file read, two `lean_leansearch` queries | mathlib rev `5450b53e` |
| Mathlib | `InformationTheory.klFun x = x*log x + 1 - x`, `strictConvexOn_klFun`, `klDiv_eq_integral_klFun` | the commutative shadow of (D4) at $f(t)=t\log t$, affinely normalised so $f(1)=f'(1)=0$; a single instance, not a general $f$-divergence | file read | mathlib rev `5450b53e` |
| Mathlib | `Real.negMulLog`, `strictConcaveOn_negMulLog`, `strictConvexOn_mul_log`, `deriv2_mul_log`; `Real.binEntropy`, `Real.qaryEntropy` | the scalar backbone of every variant, real-variable only | grep, `lean_leanfinder` | mathlib rev `5450b53e` |
| Mathlib | `Analysis/InnerProductSpace/StandardSubspace.lean` — `StandardSubspace`, `IsCyclic`, `IsSeparating`, with a file TODO reading "Define the Tomita conjugation, prove Tomita's theorem, prove the KMS condition" | a precursor to the apparatus of (D3)/(D6)/(D7); the modular operator itself is absent | `grep "Tomita\|Takesaki\|Araki\|Umegaki"` — the only match in all of Mathlib | mathlib rev `5450b53e` |
| Mathlib | `CFC.log a := cfc Real.log a` with `log_exp`, `exp_log`, `log_pow` | the operator logarithm exists at C\*-generality. **The singular case is the point**: `cfc` returns a junk value when the function is not continuous on the spectrum, and `Real.log 0 = 0`, so `CFC.log` coincides with the support-restricted logarithm (D1)'s convention intends exactly when $0$ is *isolated* in the spectrum — always so in finite dimensions — and is junk when $0$ is non-isolated | read `ExpLog/Basic.lean` and the `cfc` definition | mathlib rev `5450b53e` |
| Mathlib | `CFC.log_monotoneOn` on strictly positive elements — (A9). Operator **concavity** of log appears only as a file TODO | (A9) present; (A7) not found | grep, file reads | mathlib rev `5450b53e` |
| Mathlib | `WStarAlgebra` (predual merely exists), `VonNeumannAlgebra H` with `commutant_commutant` — one file | the ambient object of (D1)–(D4) exists as a definition; could not find normal states, traces, $L^1(A)$, or the type classification, having searched `grep -rni "semifinite\|faithful normal\|normal state"` over Mathlib | grep, file read | mathlib rev `5450b53e` |
| Mathlib | `instLoewnerPartialOrder`, `Matrix.PosSemidef`/`PosDef`, `Matrix.trace`; positive linear maps `A →ₚ[ℂ] A₂`, `PositiveLinearMap.PreGNS`, completely positive maps `A₁ →CP A₂` | the order in which (C6) and the corpus's operator inequalities are stated, and the finite-dimensional data of (D8). Could not find a support-projection notion, a bundled `State`, or normality, having searched `grep -rn "IsState\|StateSpace"` and `lean_leansearch "state on a C-star algebra positive linear functional norm one"` | grep, `lean_leansearch` | mathlib rev `5450b53e` |
| Mathlib | could not find: any quantum or von Neumann relative entropy; von Neumann entropy; Shannon entropy of a distribution; Rényi/Hellinger/Pinsker/hypothesis testing; a general $f$-divergence; trace-class or Hilbert–Schmidt operators; non-commutative $L^p$, Haagerup $L^1$, standard form, or a Radon–Nikodym derivative for states; the modular or relative modular operator; support projections; Löwner's theorem; the operator Jensen inequality; Lieb concavity; Lieb–Ruskai/Uhlmann joint convexity; Kosaki's variational expression; Stinespring dilation; density matrices, channels or POVMs; an operator $x\log x$ | — | ~20 greps plus five `lean_leansearch`/`lean_leanfinder` queries, all recorded in the lane notes | mathlib rev `5450b53e` |
| this repository | `Matrix.relativeEntropy (ρ σ : DensityMatrix n) : EReal`, `QuantumSystem/Analysis/Entropy/RelativeEntropy.lean`, with the docstring citing Umegaki 1962; surrounding `relativeEntropy_nonneg`, `_eq_zero_iff`, `_channel_le`, `_channel_eq_iff_recoverable`, `_jointly_convex`, and `Analysis/Matrix/{LiebConcavity,Effros,Pinching}` | closest to **(D8)**, with two stated differences: the log base is $e$, not 2; and the second argument is a density matrix, not merely positive semi-definite. No regularised form (R18). Nothing for (D1)–(D4), (D6), (D7), (D9). **The `implemented-as` field of this note is `none` only because that field belongs to `math-review`, not to this skill; a declaration for the finite-dimensional case exists** | repository grep, file read | 2026-08-16 |
| Physlib (`leanprover-community/physlib`) | `QuantumInfo/Entropy/Relative.lean`: `qRelativeEnt (ρ σ : MState d) : ENNReal`, docstring "Also called the Umegaki quantum relative entropy", defined as the $\alpha=1$ case of a sandwiched Rényi family, natural log, `⊤` when supports fail to nest. Around it: `qRelativeEnt_joint_convexity`, `_additive`, `lowerSemicontinuous`, `Entropy/DPI.lean`, `Entropy/SSA.lean`, `Channels/Pinching.lean`, `ResourceTheory/SteinsLemma.lean`, and `TraceInequality/{LownerHeinzTheorem,JensenOperatorInequality,LiebAndoTrace,OperatorGeometricMean}` | **direct prior art**, (D8)-shaped and finite-dimensional. Its variational formula is for the *sandwiched Rényi* quantity, not Kosaki's (D9) for the Umegaki form. Covers, finite-dimensionally, the external edges Löwner–Heinz, operator Jensen, Lieb concavity, joint convexity, pinching, support projections | GitHub trees API, raw file reads | 2026-08-16 |
| Physlib | `PhyslibAlpha/QuantumMechanics/StinespringDilation.lean` — Kraus form and `QuantumChannel`, over a general ring; its own TODO notes a second, different Stinespring elsewhere in the repository | supplies (R20)'s Stinespring edge, finite-dimensional | trees API, raw file read | 2026-08-16 |
| Rocq — `infotheo` | `probability/divergence.v`: `div = \sum_(a in A) P a * log (P a / Q a)`, base 2, with `div_ge0`, `div0P` | the classical case on finite distributions; base 2 as in (D8), but **real-valued with no `+∞`** — dominance is a lemma hypothesis, not a case split. Could not find a quantum relative entropy in the library, having listed all 87 `.v` files and read the divergence file | trees API, raw reads | 2026-08-16 |
| Rocq — CoqQ | density matrices, quantum Hoare logic, `majorization.v`; the only entropy hits are `entropy_majority`/`majority_entropy_le` on real vectors | could not find a quantum relative entropy | trees API, greps of the three likeliest files | 2026-08-16 |
| Isabelle/HOL main library | `HOL-Probability.Information`: `KL_divergence b M N` via `entropy_density` and `RN_deriv`, parametric base | the classical case; **real-valued with no `+∞`**, absolute continuity as a lemma hypothesis | WebFetch of the library page | 2026-08-16 |
| Isabelle AFP | only *Source Coding Theorem* under probability theory; *Isabelle Marries Dirac* is matrix quantum computation. Could not find a quantum relative entropy | — | topic index page plus two web searches; **the AFP full-text search endpoint returned only the search form**, so this is not a full-text sweep | 2026-08-16 |
| Lean Zulip | **unreliable miss** — the domain-restricted search returned no pages from those domains at all, which indicts the search channel, not the archive | — | `WebSearch` with `allowed_domains` | 2026-08-16 |

## Open questions

- **Does the adopted form agree with (D1)/(D2) on a general semifinite von
  Neumann algebra?** Nothing in this corpus proves it. Proved: agreement on
  $\mathcal B(\mathcal H)$ (R3) and in finite dimensions (R14). Nearest general statement: (R17),
  restricted to bounded relative Hamiltonians, written with a crossed-product
  trace, and hedged by its own source. This sits exactly at the object's
  definition and is the note's principal limitation.
- Is [UME62]'s asserted semifinite extension (X7) actually valid, including its
  unverified side condition that $\tau$ restrict to a semi-trace on every
  subalgebra used?
- Is [UME62]'s $I(a,b)=0\Rightarrow a=b$ true without the commutativity
  hypothesis its Theorem 2 carries? (R8)(2) settles the *mathematics* — it is —
  so this is a proof-technique gap in the 1962 paper, not a truth gap.
- Do (R10)(h4) and (h7) have a source other than Ohya–Petz? Both were verified in
  finite dimensions during this extraction; neither is proved anywhere in the
  corpus.
- Is [UME62]'s footnote 7) polarity as read here? MinerU dropped all four
  footnotes, so the PDF text layer is the sole witness, its OCR is damaged, and
  no page-image check was possible in this container. The reading adopted is
  "**is** satisfied"; an earlier reading of the same line said "is not
  necessarily satisfied". Both come from the same OCR.

## Sources

**Append-only.**

| Key | Work | Status | Cache | Version | Tier reached | Retrieved |
|---|---|---|---|---|---|---|
| UME62 | H. Umegaki, *Conditional expectation in an operator algebra, IV (entropy and information)*, Kodai Math. Sem. Rep. **14** (1962) 59–85 | retrieved (converted) | `references/umegaki-1962-cond-exp-iv/` | published | b | 2026-08-16 |
| HIA18 | F. Hiai, *Quantum $f$-divergences in von Neumann algebras I. Standard $f$-divergences*, arXiv:1805.02050; J. Math. Phys. **59** (2018) 102202 | retrieved | `references/arxiv-1805.02050/` | arXiv | a | 2026-08-16 |
| VED02 | V. Vedral, *The role of relative entropy in quantum information theory*, arXiv:quant-ph/0102094; Rev. Mod. Phys. **74** (2002) 197 | retrieved | `references/arxiv-quant-ph-0102094/` | arXiv | a | 2026-08-16 |
| WIT18 | E. Witten, *Notes on some entanglement properties of quantum field theory*, arXiv:1803.04993 | retrieved | `references/arxiv-1803.04993/` | arXiv | a | 2026-08-16 |
| HS17 | S. Hollands, K. Sanders, *Entanglement measures and their properties in quantum field theory*, arXiv:1702.04924 | retrieved | `references/arxiv-1702.04924/` | arXiv | a | 2026-08-16 |
| KW20 | S. Khatri, M. M. Wilde, *Principles of Quantum Communication Theory: A Modern Approach*, arXiv:2011.04672 | retrieved | `references/arxiv-2011.04672/` | arXiv | a | 2026-08-16 |
| ARA76 | H. Araki, *Relative entropy of states of von Neumann algebras*, Publ. RIMS **11** (1976) 809–833 | not retrieved — tried Project Euclid's download endpoint (returns HTML), its `.full` article page (404), `kurims.kyoto-u.ac.jp/~prims/pdf/11-3/*.pdf` (404), the `ems.press` volume index (404) | — | — | c | 2026-08-16 |
| ARA77 | H. Araki, *Relative entropy for states of von Neumann algebras II*, Publ. RIMS **13** (1977) 173–192 | not retrieved — same routes as ARA76 | — | — | c | 2026-08-16 |
| KOS86 | H. Kosaki, *Relative entropy of states: a variational expression*, J. Operator Theory **16** (1986) 335–348 | not sought | — | — | c | 2026-08-16 |
| PET88 | D. Petz, *A variational expression for the relative entropy*, Comm. Math. Phys. **114** (1988) 345–349 | not sought | — | — | c | 2026-08-16 |
| OP93 | M. Ohya, D. Petz, *Quantum entropy and its use*, Springer 1993 | not sought | — | — | c | 2026-08-16 |
| LR99 | A. Lesniewski, M. B. Ruskai, *Monotone Riemannian metrics and relative entropy on noncommutative probability spaces*, J. Math. Phys. **40** (1999) 5702–5724 | not sought | — | — | c | 2026-08-16 |
| HAA75 | U. Haagerup, *The standard form of von Neumann algebras*, Math. Scand. **37** (1975) 271–283 | not sought | — | — | c | 2026-08-16 |

## Not investigated

- **The `[ext]` coverage gap.** These external edges appear in `## Results` and
  were **not** checked against any library or formalization: the strict-convexity
  fact (A8); the Lesniewski–Ruskai integral representation under (R6); Petz's
  variational expression (R16); the tensor product of two finite-class von
  Neumann algebras under (R11); Umegaki's own part III sufficiency criterion
  under (R13); Borchers' modular-operator ordering and the Stone/Halmos graph
  projection under (R16); Donald's and Araki's relative-Hamiltonian results under
  (R17); the classical Kullback–Leibler inputs of (R7'); the Peierls–Bogoliubov
  inequality as [VED02] imports it; the polar-decomposition lemma [VED02] takes
  from Reed–Simon; and — named as unchecked by the prior-art lane itself — the
  operator Schwarz inequality, the Gibbs variational principle, Klein's
  inequality, Petz recovery beyond this repository's own lemma, Araki's
  Radon–Nikodym cocycle, and the Connes cocycle of (D7).
- **Araki's own papers were never opened.** Every claim in this note about what
  Araki assumed, defined or proved is a claim about how [HIA18], [HS17] and
  [WIT18] *report* him. In particular, whether Araki's original definition
  assumed faithfulness is not settled here: [HS17] attributes the faithful
  version to him and [HIA18] attributes the total version to the same two papers.
- **No page-image check of [UME62] was possible.** `pdftoppm`, `pdftotext`,
  `mutool` and `gs` are all absent from this container, so the UME62 rows rest on
  a MinerU conversion cross-checked against the PDF's own OCR text layer — two
  extractions, no image. MinerU dropped the paper's footnotes entirely, so every
  footnote claim (including (X7)'s footnote 5) and the open question about
  footnote 7) rests on the text layer alone, uncross-checked.
- **[KW20] was searched, not read.** 4.3 million characters were grepped and
  jumped; its later chapters were not swept for further statements about this
  object. Likewise unread: [HIA18]'s Lemmas 3.1–3.4 and §5 Rényi proofs, its
  Appendix A/B derivations beyond the statements quoted, [WIT18]'s
  $\Delta_D\ge\Delta_N$ section, and the achievability and strong-converse halves
  of (R21).
- **Variants sighted and not pursued**: [UME62]'s $I(\cdot;B)$ relative to a
  subalgebra; [HIA18]'s Rényi and max-relative entropies and the $\alpha\to1$
  characterisation (R10's neighbour), where a further definitional variant could
  hide; [VED02]'s measured/asymptotic characterisation
  $S(\sigma\|\rho)=\lim_N S_N$, which is arguably a definition in its own right;
  the Haagerup $L^p$ route of (R17) as a source of further variants.
- **Prior art not swept**: Physlib's spectral-theory and unbounded-operator
  files were listed but not opened; the AFP was not full-text searched; Mizar,
  HOL Light, `QuantumLib`/SQIR and `mathcomp-analysis` were not searched at all;
  the Lean Zulip result is an unreliable miss.
- **The unexamined base.** Everything above rests on a tier-(c) floor: the
  closability of $S_{\rho,\sigma}$ and the identity
  $\Delta_{\rho,\sigma}=J\Delta_{\sigma,\rho}^{-1}J$ — the two facts that make the
  adopted form's relative modular operator exist and behave — are attested only
  through [HIA18]'s citations to Araki, whose papers could not be obtained. So
  is Haagerup's uniqueness of the standard form under (R2)(1), the
  Lesniewski–Ruskai representation under (R6), and the whole of (R10). The
  adopted form itself is therefore **(c)**, which is what `worst-tier` records.
