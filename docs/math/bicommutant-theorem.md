---
object: Von Neumann bicommutant theorem
slug: bicommutant-theorem
status: draft
worst-tier: b
mathlib-rev: 5450b53e5ddc75d46418fabb605edbf36bd0beb6
implemented-as: DoubleCommutant.bicommutant_tfae
revisions:
  - 2026-08-16 · 9b1810d · initial extraction · sources: SHI12, LAN98, HIA20, KOS13, SOR23, NAA13, HM06
  - 2026-08-16 · (working tree) · back-link set — the adopted general form (non-unital, non-degenerate) is now stated by `SOTClosedSubalgebra.doubleCommutant_eq_of_isSOTClosed` / `WOTClosedSubalgebra.doubleCommutant_eq_of_isWOTClosed`
  - 2026-08-16 · (working tree) · back-link moved to `DoubleCommutant.bicommutant_tfae`, which states the adopted general form in full (the three-way equivalence, non-unital and non-degenerate); the density form (R2) is `SOTClosedSubalgebra.sotClosure_eq_doubleCommutant` / `wotClosure_eq_doubleCommutant`
  - 2026-08-16 · (working tree) · (A2) — that $1 \in M$ is a conclusion, not a hypothesis — is now `WOTClosedSubalgebra.one_mem_of_isWOTClosed` / `DoubleCommutant.one_mem_of_isSOTClosed`, which is also the sharpened content of (X6); (X4)'s $F(H)' = \mathbb{C}1$ and the $F(H)'' = B(H)$ it yields are `InnerProductSpace.centralizer_finiteRankOperators` / `centralizer_centralizer_finiteRankOperators`, and the negative instance itself is `DoubleCommutant.not_isWOTClosed_finiteRankOperators` / `not_isSOTClosed_finiteRankOperators` / `centralizer_centralizer_ne_finiteRankOperators`
---

<!--
Macros the quotes below need, copied from each source's own preamble:
  \ra \c \s \cs \ss \sub \lan \ran \la \ep   SHI12, references/arxiv-1211.3404/raw/main.tex:46,52,62,65,66,70,72,73,96,98
  \ll \ca \Hs \sta \vNa \raw \n \BH \dl \ep \lm \Ph \Ps \M \GN \H \CO \C \I \su
                                             LAN98, references/arxiv-math-ph-9807030/raw/main.tex:34,53,58,62,66,78,86,113,211,213,221,228,232,246,247,269,276,288,291,28
  \cH \cA \Proj                              HIA20, references/arxiv-2004.02383/raw/main.tex:32,51,62
  \comps \A \H \B                            SOR23, references/arxiv-2302.01958/raw/type_classification.tex:26,30,32,38
  \idx \alg \mc                              NAA13, references/arxiv-1311.2717/raw/qlattice.tex:21,66,73
  \alg \norm \bh \2 \7 \al                   HM06, references/arxiv-math-ph-0602036/raw/reconstruction.tex:26,27,28,136,138,143
  KOS13's macros (\df \comm \N \C \BH \CC \II \zentr \limp \rpktarget) are defined
  in the author's private packages rpk.sty and motta.sty, which are NOT in the
  arXiv package (\usepackage lines at raw/wstarint-arxiv.tex:35-36). They cannot
  be transcribed, and no KOS13 quote below can be rendered from this note; see
  the tier note on (D9)/(D10).
  \H and \M are defined by more than one source below; LAN98's and SOR23's \H
  agree up to the spelling of the calligraphic alphabet, and only LAN98 uses \M
  inside a quote, so a single definition of each is faithful here.

  The bodies below are the sources' own; only the defining primitive is this
  note's, and it is forced by the renderer. KaTeX scopes \newcommand to the
  expression it appears in, so a preamble written with \newcommand defines
  nothing for the rest of the document; \gdef is the form that persists. \gdef
  also overwrites silently, which is what \c, \ss, \sub and \H need — KaTeX
  predefines all four (cedilla, sharp s, \subset, Hungarian umlaut) and rejects
  \newcommand on them outright, aborting the whole block and leaving every
  later macro undefined. That was the parse error this preamble first produced.
-->

$$
\gdef\ra{{\rightarrow}}
\gdef\c{{\mathbb{C}}}
\gdef\s{{^{\ast}}}
\gdef\cs{{C^{\ast}\text{-}}}
\gdef\ss{{\ast}}
\gdef\sub{{\subseteq }}
\gdef\lan{{\langle}}
\gdef\ran{{\rangle}}
\gdef\la{{\lambda}}
\gdef\ep{{\varepsilon}}
\gdef\sta{{\ast\text{-algebra}}}
\gdef\ca{{C^{\ast}\text{-algebra}}}
\gdef\Hs{{\text{Hilbert space}}}
\gdef\vNa{{\text{von Neumann algebra}}}
\gdef\raw{\rightarrow}
\gdef\BH{{\frak B}({\cal H})}
\gdef\dl{\delta}
\gdef\lm{\lambda}
\gdef\Ph{\Phi}
\gdef\Ps{\Psi}
\gdef\M{{\frak M}}
\gdef\GN{{\frak N}}
\gdef\H{{\cal H}}
\gdef\C{{\Bbb C}}
\gdef\I{{\Bbb I}}
\gdef\cH{\mathcal{H}}
\gdef\A{\mathcal{A}}
\gdef\B{\mathcal{B}}
\gdef\cA{\mathcal{A}}
\gdef\alg#1{\mathfrak{#1}}
\gdef\mc#1{\mathcal{#1}}
\gdef\bh{\mathfrak{B}(\mathcal{H})}
\gdef\2#1{{\mathcal #1}}
$$

# Von Neumann bicommutant theorem

## What this object is for

The bicommutant theorem identifies a purely algebraic condition on an operator
algebra $M \subseteq B(H)$ — that it is its own bicommutant — with a purely
topological one — that it is closed in the weak (equivalently strong) operator
topology. It is what makes the theory of von Neumann algebras possible at all:
it lets a definition be given algebraically and then used topologically, so that
weak limits, spectral projections and polar decompositions of elements of $M$
stay inside $M$. Its generality matters in exactly one direction: the algebra is
required to act non-degenerately (a condition strictly weaker than containing
$1$), and nothing about separability, σ-finiteness, type, or commutativity
enters anywhere.

## Definition

### Variants as the sources write them

Axes along which the corpus genuinely splits. The grid is a derived index and
carries no tier; where it disagrees with a block below, the grid is wrong.

| (D#) | Source | Assumption on $M$ | Norm-closed? | Closure conditions listed | Which side is the definition |
|---|---|---|---|---|---|
| (D1) | SHI12 | none (unitality derived) | — | $M = M''$ | algebraic |
| (D2) | SHI12 | acts non-degenerately | **yes** ($C^{*}$-subalgebra) | $M=M''$ / WOT / SOT | theorem, both sides |
| (D3) | LAN98 | $1 \in M$ | no | $M''=M$ / WOT / SOT | theorem, both sides |
| (D4) | LAN98 (reporting von Neumann) | none | no | **sequential** WOT-completeness | topological |
| (D5) | HIA20 | $1 \in M$ | no | WOT / SOT / $M''=M$ | topological |
| (D6) | HM06 | $1 \in M$ | no | WOT / $R''=R$ — **no SOT** | algebraic, by election |
| (D7) | NAA13 | unital | no | WOT — **no SOT** | algebraic ($M = A''$) |
| (D8) | SOR23 | folded into "$*$-subalgebra" | no | WOT $\Rightarrow$ vN algebra (one direction) | algebraic |
| (D9) | KOS13 | unital | no | $N=N''$ / σ-weak / σ-strong / σ-strong-⋆ — **no WOT, no SOT** | algebraic |
| (D10) | KOS13 | — ($W^*$-algebra, abstract) | — | possession of a predual | Hilbert-space-free |
| (D11) | all | — | — | the six sources' own topology definitions | — |

**(D1) [SHI12] — von Neumann algebra as $M = M''$, unitality derived** — tier (a)

> `Let $H$ be a Hilbert space. An involutive subalgebra $M$ of $B(H)$ is called a {\bf von Neumann algebra on $H$} if $M=M''$.`

> `One notes that every von Neumann algebra is necessarily unital.`

SHI12 also fixes $VN(S) := C^*(S)''$ for the generated von Neumann algebra, and
calls $A''$ the enveloping von Neumann algebra of a $C^{*}$-subalgebra $A$.

**(D2) [SHI12] — the theorem, non-degeneracy form** — tier (a)

> `We say a {\bf \cs-subalgebra $A$ of $B(H)$ acts non-degenerately on $H$} if $x\in H$ and $Tx=0$ for all $T\in A$ implies $x=0$.`

> `\label{thm:bicommutant} [The von Neumann bicommutant theorem] Let $M$ be a \cs-subalgebra of $B(H)$ acting non-degenerately on $H$. Then the following statements are equivalent:`

with the three equivalents `$M=M^{\prime \prime}$`, `$M$ is weakly closed`,
`$M$ is strongly closed`.

`differs from (D3) by:` SHI12 hypothesises non-degeneracy where every other
corpus source hypothesises $1 \in M$, and is the only source to require $M$
norm-closed.
`sources claim equivalence:` not addressed — no corpus source compares the two
hypothesis packages. They are not equivalent; see (X1) and (X6).

**(D3) [LAN98] — the double commutant theorem, unital $*$-algebra** — tier (a)

> `Let $\M$ be a \sta\ in $\BH$, containing $\I$. The following are`

equivalent: `$\M''=\M$`; `$\M$ is closed in the weak operator topology`;
`$\M$ is closed in the strong operator topology`.

`differs from (D2) by:` unitality in place of non-degeneracy, and no
norm-closedness.
`sources claim equivalence:` not addressed.

**(D4) [LAN98] — von Neumann's original definition, as LAN98 reports it** — tier (a)

> `defines a {\bf ring of operators} $\M$ (nowadays called a {\bf von Neumann algebra}) as a $\mbox{}^*$-subalgebra of the algebra $\BH$ of all bounded operators on a \Hs\ $\H$ (i.e, a subalgebra which is closed under the involution $A\raw A^*$) that is closed (i.e., sequentially complete) in the weak operator topology.`

LAN98 then changes its own definition mid-text:

> `from now on we add to the definition of a von`

> `Neumann algebra the condition that $\M$ contains $\I$.`

`differs from (D3) by:` no unit, and closure phrased **sequentially**. WOT is not
first countable, so this is not a notational difference; see (X7), which
separates the two on a non-separable space.
`sources claim equivalence:` not addressed; LAN98 does not flag its own switch.

**(D5) [HIA20] — von Neumann algebra defined topologically** — tier (a)

> `A *-subalgebra of $B(\cH)$ is called a \emph{von Neumann algebra} (also \emph{$W^*$-algebra})`

> `if it contains the identity operator $1$ and closed in the weak topology.`

and, for a $*$-subalgebra $M$ with $1 \in M$, the

> `commutation theorem} or \emph{von Neumann's density theorem} says that the following three conditions are equivalent:`

namely weakly closed / strongly closed / $M''=M$.

`differs from (D3) by:` the direction of definition is reversed — the definiens
is topological and $M''=M$ is derived. HIA20 also declares "von Neumann
algebra" and "$W^*$-algebra" synonyms, which (D10) refuses.
`sources claim equivalence:` yes, by its own statement of the theorem.

**(D6) [HM06] — algebraic condition taken as basic, two conditions only** — tier (a)

> `The standard definition of a von Neumann algebra involves reference to a topology, and it is then shown (by von Neumann's double commutant theorem) that this topological condition coincides with an algebraic condition (condition 2 in the Definition \ref{vNA}). But for present purposes, it will suffice to take the algebraic condition as basic.`

> `For a $*$-algebra $\alg{R}$ on $\2H$ that contains $I$, the following are equivalent: (i) $\alg{R}$ is weakly closed; (ii) $\alg{R}''=\alg{R}$. This is von Neumann's double commutant theorem.`

`differs from (D3) by:` the SOT clause is absent, though HM06 has defined SOT.
HM06 writes the commutant with a commutator, $[B,A]=0$.
`sources claim equivalence:` yes for its own two conditions.

**(D7) [NAA13] — unital $*$-subalgebra, WOT only** — tier (a)

> `a unital $*$-subalgebra of $\alg{B}(\mathcal{H})$ is a von Neumann algebra if and only if it is closed in the weak operator topology. This result, which is known as the \emph{bicommutant theorem}, relates the purely algebraic definition of von Neumann algebras given on page~\pageref{p:vna}, to a topological condition.`

`differs from (D6) by:` NAA13's "purely algebraic definition" is not $M = M''$
but the construction $M = A''$ from an ambient $*$-algebra $A$.
`sources claim equivalence:` yes, between its own two conditions.

**(D8) [SOR23] — $A = A''$, with unitality folded into "$*$-subalgebra"** — tier (a)

> `A subset of $\B(\H)$ is said to be a \textbf{$*$-subalgebra} if it is closed under scalar multiplication, operator multiplication, operator addition, and adjoints, and contains the identity operator.`

> `A $*$-subalgebra $\A \subseteq \B(\H)$ is a \textbf{von Neumann algebra} if it is equal to its own double commutant, i.e., $\A = \A''.$`

and the theorem, one-directional and stated inside a proof sketch:

> `It uses the double commutant theorem, which says that any $*$-subalgebra of $\B(\H)$ that is topologically closed with respect to the ``weak operator topology''\footnote{The weak operator topology is explained in appendix \ref{app:operator-topologies}.} is a von Neumann algebra.`

`differs from (D6) by:` unitality lives in the ambient notion, so SOR23's
"$*$-subalgebra" is not the standard one. **Read with the standard non-unital
meaning the statement is false**, witnesses $\{0\}$ and $\mathbb{C}p$ for a
proper projection $p$; read with SOR23's own definition it is the standard
unital statement and is true. See (X8).
`sources claim equivalence:` not addressed.

**(D9) [KOS13] — commutant relative to an ambient algebra, σ-topologies** — tier (b)
(byte-verbatim, but KOS13's macros are unavailable, so the mathematical reading
of the quote is inferred)

> `The \df{commutant} of a subalgebra $\N$ of any algebra $\C$ is defined as`

> `\N^\comm:=\{y\in\C\mid xy=yx\;\forall x\in\N\},`

> `A unital $*$-subalgebra $\N$ of an algebra $\BH$ is called the \df{von Neumann algebra} \cite{vonNeumann:1930:algebra,Murray:vonNeumann:1936} if{}f $\N=\N^\comm{}^\comm$. From von Neumann's double commutant theorem \cite{vonNeumann:1930:algebra} it follows that this is equivalent with any of the conditions: $\N$ is weakly-$\star$ closed, $\N$ is ultrastrongly closed, $\N$ is ultrastrongly-$\star$ closed. In particular, $\BH$ is a von Neumann algebra.`

`differs from (D3) by:` two independent things. The commutant is taken relative
to an arbitrary ambient algebra, not inside $B(H)$; and the closure conditions
are the σ-topologies, WOT and SOT occurring nowhere in KOS13. That these
topologies are the standard σ-topologies is fixed by KOS13 itself:

> `When considered in the context of $W^*$-algebras $\N\subseteq\BH$, these topologies are usually called \textit{$\sigma$-strong} and \textit{$\sigma$-strong-$\star$}, respectively.`

`sources claim equivalence:` KOS13 asserts its four conditions equivalent, citing
von Neumann; **no corpus source bridges its list to the WOT/SOT list**. The note
supplies that bridge itself as (X9), at tier (d).

**(D10) [KOS13] — $W^*$-algebra as the abstract notion, kept distinct** — tier (b)

> `If for a given $C^*$-algebra $\C$ there exists a predual $\C_\star$, then it is a unique predual of $\C$, and in such case $\C$ is called a \df{$W^*$-algebra} \cite{Sakai:1956}.`

> `An image $\pi(\N)$ of any representation $(\H,\pi)$ of a $W^*$-algebra $\N$ is a von Neumann algebra if{}f $\pi$ is normal and nondegenerate.`

`differs from (D5) by:` KOS13 keeps $W^*$-algebra and von Neumann algebra as two
notions related by a cited theorem, where HIA20 declares them synonyms. This is
a definitional disagreement in the corpus, not a notational one.
`sources claim equivalence:` yes, by citing Sakai — see the external edge in
(R14).

**(D11) — the operator topologies, per source** — tier (a)

Filed as a variant because the theorem's content is exactly which topology is
named. SHI12 defines SOT, WOT and strong-⋆ and **no** σ-topology; LAN98 defines
norm, strong and weak by nets; HIA20 names norm/SOT/WOT without defining them and
adds the σ-weak topology as $\sigma(B(\mathcal{H}),\mathcal{C}_1(\mathcal{H}))$; SOR23 defines
norm, strong and weak by seminorms and no σ-topology; HM06 defines uniform, weak,
strong and **ultraweak**, the last concretely via density operators; KOS13
defines only σ-topologies, on an abstract $W^*$-algebra via its predual. Three
mutually inequivalent ambient frameworks, therefore, and only (X9) connects the
third to the first.

**Notation trap.** SHI12's "strong-`\ss` operator topology" is defined by the
seminorms $T \mapsto \|Tx\| + \|T^{*}x\|$ — that is the **strong-⋆** topology,
not KOS13's σ-strong. Matching the two by their spelling is a mistake.

### Adopted general form

Let $H$ be a complex Hilbert space and let $M \subseteq B(H)$ be a
$*$-subalgebra — a linear subspace closed under products and under the adjoint,
**not assumed norm-closed and not assumed to contain $1$** — which acts
non-degenerately on $H$, meaning: for $x \in H$, if $Tx = 0$ for every
$T \in M$, then $x = 0$. Write $M' = \{S \in B(H) : ST = TS \text{ for all }
T \in M\}$ and $M'' = (M')'$. Then the following three conditions are
equivalent:

1. $M = M''$;
2. $M$ is closed in the weak operator topology of $B(H)$;
3. $M$ is closed in the strong operator topology of $B(H)$.

The standing assumptions are (A3) self-adjointness, (A5) the algebra structure
and (A10) that $H$ is a complex Hilbert space; the one local hypothesis is (A1)
non-degeneracy. No separability, σ-finiteness, type or commutativity assumption
is carried, and none is available to be dropped.

This is (D2) with SHI12's norm-closedness hypothesis deleted. The choice of
(D2) over the unital variants is justified by (X1): $K(H)$ for infinite
-dimensional $H$ acts non-degenerately and is not unital, so (D3), (D5), (D6),
(D7) and (D9) say nothing about it while (D2) does. The deletion of
norm-closedness is justified by (X4): no step of the corpus proof consumes it
and each of the three conditions implies it, so assuming it removes only
instances where all three fail — a class inhabited by the finite-rank operators
$F(H)$.

### The density form the equivalence hides

The corpus proof establishes more than the equivalence states, and the stronger
statement is the one a formalization is likely to want as the primary result:
for **every** non-degenerate $*$-subalgebra $M \subseteq B(H)$, with no closure
hypothesis at all,

$$M'' = \overline{M}^{\,\mathrm{SOT}} = \overline{M}^{\,\mathrm{WOT}}.$$

The three-way equivalence is a corollary. See (R2) for the tier.

## Notation and conventions

| (C#) | Axis | This note | Per source | Translation |
|---|---|---|---|---|
| (C1) | conjugate-linear argument of the inner product | irrelevant to every statement here, provided the WOT seminorms range over all pairs | SHI12 linear in the first; LAN98 conjugate-linear in the first, explicit; SOR23, HIA20, NAA13 conjugate-linear in the first, implicit (tier b); HM06 and KOS13 unresolved | SHI12's $\langle x,y\rangle$ is LAN98's $(y,x)$ |
| (C2) | status of $1 \in M$ | a conclusion, not a hypothesis | conclusion (SHI12); hypothesis (LAN98, HIA20, HM06, NAA13, KOS13); part of the ambient notion (SOR23); added mid-text (LAN98) | (A2) |
| (C3) | self-adjointness of the set whose commutant is taken | assumed throughout | isolated only by SHI12; stated informally by LAN98 and SOR23; omitted by HIA20, HM06, NAA13, KOS13 | without it $M'$ need not be a $*$-algebra — (X2) |
| (C4) | name of the theorem | bicommutant theorem | bicommutant (SHI12, NAA13, KOS13); double commutant (LAN98, SOR23, HM06, KOS13); double commutation **or** von Neumann's density theorem (HIA20) | HIA20's "density theorem" is a name collision with Kaplansky density, which HIA20 states separately — see (R11), (R12) |
| (C5) | which topologies enter the statement | WOT and SOT | three conditions (SHI12, LAN98, HIA20); two (HM06, NAA13); one direction (SOR23); four σ-conditions (KOS13) | (X9) |
| (C6) | "von Neumann algebra" vs "$W^*$-algebra" | kept distinct | synonyms (HIA20); distinct notions related by a cited theorem (KOS13) | Sakai's theorem, (R14) |
| (C7) | algebraic vs topological primacy | algebraic condition stated first, topological conditions as equivalents | explicit, self-aware disagreement across the corpus — HM06 and NAA13 elect the algebraic side, HIA20 the topological, SHI12 the algebraic with a remark | presentation only, no content |
| (C8) | commutant notation | $M'$, $M''$ | $X'$/$X''$ everywhere; SHI12 continues $X''', X''''$; KOS13 uses a macro, not a prime; HM06 defines it by $[B,A]=0$ | — |
| (C9) | nets vs sequences | nets | LAN98's report of von Neumann's original definition is sequential; HM06, SOR23 and SHI12 all warn that WOT is not first countable | not interchangeable — (X7) |

## Results and dependencies

### (R1) The bicommutant theorem, non-degeneracy form

For $M$ a norm-closed $*$-subalgebra of $B(H)$ acting non-degenerately:
$M = M''$ ⟺ $M$ WOT-closed ⟺ $M$ SOT-closed.

- Source: [SHI12] Theorem `thm:bicommutant` · tier (a) · **proved in source**
- Depends on: (R3), (R5), (R6), (R7), (R8), (A1), (A3), (A5)
- Conventions: (C2), (C3), (C5)
- Proof route:
  1. (i)⇒(ii) and (ii)⇔(iii) in one line, consuming (R7) [WOT coarser than SOT],
     (R5) [every commutant is WOT- and SOT-closed] and (R6) [for a convex set,
     SOT-closed ⟺ WOT-closed; $M$ is a subspace, hence convex — (A5)].
  2. One-vector case: fix $x_0$, put $X = \overline{Mx_0}$, $P = P_X$; then
     $PTP = TP$ for $T \in M$ because $MX \subseteq X$ — consumes (A5).
  3. Adjoint trick $TP = (PT^{*}P)^{*} = (T^{*}P)^{*} = PT$, so $P \in M'$ —
     consumes (A3), and consumes it **here only**.
  4. $T(1-P)x_0 = (1-P)Tx_0 = 0$ for all $T \in M$, so $(1-P)x_0 = 0$ —
     consumes (A1), and consumes it **here only**.
  5. For $S \in M''$: $SP = PS$, so $Sx_0 = PSx_0 \in X$, giving $T \in M$ with
     $\|(S-T)x_0\| < \varepsilon_0$.
  6. Amplify to $H^n$ and use $D(M)' = M_n(M')$ to place $D(S)$ in $D(M)''$ —
     consumes (R8).
  7. Re-run steps 2–5 on $(H^n, D(M), D(S))$ and estimate
     $\|(S-T)x_m\| \le \|(D(S)-D(T))x\| < \varepsilon$, so
     $M'' \subseteq \overline{M}^{\,\mathrm{SOT}} = M$.
  8. $M \subseteq M''$ is (R3)(iii) — consumes (R3).
- Note: step 7 re-uses the one-vector argument on $D(M)$ without checking that
  $D(M)$ acts non-degenerately on $H^n$. The check is one line and is written
  out at (A8); the mathematics is unaffected.
- Verbatim:
  > `The implications (i) $\Rightarrow$ (ii) $\Leftrightarrow$ (iii) follow from Proposition \ref{prop:strongweaktop}(i), Remark \ref{rem:continofoperations}(v), and Corollary \ref{cor:weakstrongconvexclosed}.`

  > `Since $M$ acts non-degenerately on $H$, $(1-P)x_0=0$.`

### (R2) The density form

For every non-degenerate $*$-subalgebra $M \subseteq B(H)$, with no closure
hypothesis, $M'' = \overline{M}^{\,\mathrm{SOT}} = \overline{M}^{\,\mathrm{WOT}}$.

- Source: [SHI12] — the same proof, read as establishing more than it states ·
  tier (b) · **proved in source, but not stated there**: the proof is (R1)'s and
  is quoted under it; the statement is this note's reading of that proof, which
  is why the row is (b)
- Depends on: (R1) steps 2–7, (R5), (R6), (A1), (A3), (A5)
- Conventions: (C5)
- Nothing in steps 2–7 uses any of (i),(ii),(iii); they are consumed only in
  step 1 and in the final identification $\overline{M}^{\,\mathrm{SOT}} = M$.
  The corpus does not state this form, which is why the row is (b) and not (a).

### (R3) Basic properties of the commutant, including $X''' = X'$

For subsets $X, X_1, X_2 \subseteq B(H)$: (i) $X_1 \subseteq X_2 \Rightarrow
X_2' \subseteq X_1'$; (ii) $X'$ is a norm-closed unital subalgebra; (iii)
$X \subseteq X'' = X'''' = \cdots$ and $X' = X''' = \cdots$; (iv) $X$
self-adjoint $\Rightarrow$ $X'$ self-adjoint; (v) $X'' = B(H)$ iff
$X' = \mathbb{C}1$.

- Source: [SHI12] Proposition `prop:basiccommutant` · tier (a) · **proved in source**
- Depends on: nothing, except (v) which consumes SHI12's Cauchy–Schwarz
  equality case
- Conventions: (C3), (C8)
- Verbatim:
  > `\item [(ii)] $X'$ is a closed unital subalgebra of $B(H)$.`

  > `\item [(iv)] If $X$ is a self adjoint subset of $B(H)$, then $X'$ is self adjoint, and consequently a unital \cs-subalgebra of $B(H)$.`

- (ii) is what makes (A2) a theorem rather than a hypothesis: $M = M''$ forces
  $1 \in M$.

### (R4) The projection lemma

For $M$ a $*$-algebra in $B(H)$ and $\Psi \in H$ non-zero, the orthogonal
projection onto $\overline{M\Psi}$ lies in $M'$.

- Source: [LAN98] Lemma `DCTlemma` · tier (a) · **proved in source**
- Depends on: LAN98's decomposition of an element into self-adjoint parts
- Proof route: $A \in M$ gives $ApH \subseteq pH$, hence $p^{\perp}Ap = 0$, i.e.
  $Ap = pAp$; for $A = A^{*}$ this yields $(Ap)^{*} = pA = pAp = Ap$; extend to
  all of $M$ by linearity.
- Verbatim:
  > `Let $\M$ be a \sta\ in $\BH$, take a nonzero vector $\Ps\in\H$, and`

  > `let $p$ be the projection onto the closure of $\M\Ps$. Then $p\in\M'$`

- This is the same content SHI12 inlines as (R1) steps 2–3. LAN98 isolates it and
  re-uses it in three further results; SHI12 never names it.

### (R5) Every commutant is WOT- and SOT-closed

- Source: [SHI12] Remark `rem:continofoperations`(v) · tier (a) · **asserted**
  (SHI12 sets the proof as an exercise); [LAN98] proves the WOT half inline
  inside its proof of (R9) · tier (a) · **proved in source**
- Depends on: separate continuity of multiplication
- The corpus therefore does contain a proof of this — in the other source than
  the one that states it as a remark.
- Verbatim (LAN98):
  > `the commutant $\GN'$ of a \sta\ $\GN$ is always weakly closed`

### (R6) A convex set is SOT-closed iff WOT-closed

- Source: [SHI12] Corollary `cor:weakstrongconvexclosed` · tier (a) · **proved in source**
- Depends on: Hahn–Banach separation in a locally convex space, and (R7)
- Conventions: (C5)
- Verbatim:
  > `Let $X$ be a convex set in $B(H)$. Then $X$ is strongly closed if and only if it is weakly closed.`

- This is the whole content of the (ii)⇔(iii) half of (R1); it consumes (A5)
  and none of (A1), (A2), (A3).

### (R7) WOT ⊆ SOT ⊆ norm topology

- Source: [SHI12] Proposition `prop:strongweaktop` · tier (a) · **proved in source**;
  the same two reasons appear unnumbered in [LAN98]
- Depends on: nothing
- This is what makes (A4) redundant: a WOT- or SOT-closed set is norm-closed.

### (R8) Amplification: $B(H^n) \cong M_n(B(H))$ and $D(M)' = M_n(M')$

- Source: [SHI12] Problem `e:5-22` · tier (a) · **asserted** (set as an exercise,
  no proof); [LAN98], inside its proof of (R10), proves the commutator half
  inline and asserts $M_n(M')' = M_n(M'')$ · tier (a) · **proved in source** (in
  part)
- Depends on: nothing
- Verbatim (LAN98):
  > `Hence $\dl(\M)'=\M^n(\M')$.`

- This is the one place where the two full proofs differ in rigour: SHI12 exiles
  it to an unproved exercise, LAN98 proves half of it and waves at the rest.

### (R9) The bicommutant theorem, unital form

For $M$ a $*$-algebra in $B(H)$ containing $1$: $M'' = M$ ⟺ WOT-closed ⟺
SOT-closed.

- Source: [LAN98] Theorem `DCT` · tier (a) · **proved in source**
- Depends on: (R4), (R5), (R7), (R8), (R10), (A2). Self-adjointness (A3) and the
  algebra structure (A5) enter this proof only through (R4), not through a step
  of its own
- Conventions: (C2), (C5)
- Proof route:
  1. 1⇒2 via (R5), proved inline by the net computation
     $(\Phi,[A,B]\Psi) = \lim_\alpha (\Phi,[A_\lambda,B]\Psi) = 0$.
  2. 2⇒3 trivially, WOT being coarser than SOT — consumes (R7).
  3. 3⇒1: $p = [\overline{M\Psi}] \in M'$ by (R4); $1 \in M$ gives
     $\Psi = 1\Psi \in M\Psi$, so $p\Psi = \Psi$ and $A\Psi \in
     \overline{M\Psi}$ for $A \in M''$ — consumes (A2), **and consumes it
     here only**, at exactly the point where (R1) consumes (A1).
  4. Amplify as in (R10), giving $A_\varepsilon \in M$ inside a basic SOT
     neighbourhood — consumes (R8).
  5. $M$ SOT-closed gives $M'' \subseteq M$.
- Not self-contained: LAN98 writes step 4 as a delta on the proof of (R10) and
  does not re-derive the amplification.
- Verbatim:
  > `Let $\M$ be a \sta\ in $\BH$, containing $\I$. The following are`

### (R10) The finite-dimensional case

For $M$ a $*$-algebra in $M_n(\mathbb{C})$ containing $1$, $n < \infty$:
$M'' = M$, with **no** topological hypothesis.

- Source: [LAN98] Proposition `DCT1` · tier (a) · **proved in source**
- Depends on: (R4), (R8), (A2), (A6), (A7)
- Proof route: $M\Psi$ is already closed in finite dimensions, so no closure is
  needed; $p = [M\Psi] \in M'$ by (R4); $1 \in M$ gives $p\Psi = \Psi$, hence
  $A\Psi = A_0\Psi$ for some $A_0 \in M$; amplify by (R8) and run the argument
  on $n$ spanning vectors to get $A = A_0$.
- Verbatim:
  > `Let $\M$ be a \sta\ (and hence a \ca) in $\M^n(\C)$ containing $\I$`

- LAN98 states the sharpness itself:
  > `As it stands, Proposition \ref{DCT1} is not valid when $\M^n(\C)$ is replaced by $\BH$, where $\dim(\H)=\infty$.`

### (R11) The theorem as the four other sources carry it

- Sources: [HIA20] §1.2 (three conditions), [HM06] its `fact` (two conditions,
  no SOT), [NAA13] (two conditions, no SOT), [SOR23] (one direction, inside a
  proof sketch) · tier (a) each · **asserted** — none of the four gives a proof
- Depends on: [ext: VN30 — a $*$-subalgebra of the bounded operators on a
  Hilbert space that contains the identity equals its own bicommutant if and
  only if it is closed in the weak operator topology. tier (c), no locator, not
  retrieved]; SOR23 additionally points its proof at a work of Conway, see
  (R15)
- Conventions: (C4), (C5)
- Five of the seven corpus sources carry the theorem with no proof at all.

### (R12) Kaplansky density — stated in the corpus, consumed by nothing in it

For a $*$-subalgebra $\mathcal{A}$ of $B(H)$ containing $1$, the unit ball of
$\mathcal{A}$ is SOT-dense in the unit ball of $\mathcal{A}''$.

- Source: [HIA20] §1.2 · tier (a) · **asserted** (no proof, no citation to one)
- Depends on: nothing stated
- Verbatim:
  > `$\{a\in\cA:\|a\|\le1\}$ is strongly dense in $\{a\in\cA'':\|a\|\le1\}$.`

- No result in any of the seven sources cites it. It becomes load-bearing only
  in (X7) and (X9), which are this note's own arguments.

### (R13) $K(H)'' = B(H)$

- Source: [SHI12] Proposition `prop:voncompact` · tier (a) · **proved in source**
- Depends on: (R3)(v)
- The corpus's own witness that the bicommutant operation is non-trivial on a
  non-unital algebra, and the separating object of (X1). SHI12 also records, as
  an exercise, that $K(H)$ is not unital for infinite-dimensional $H$.

### (R14) Downstream consumers, and one name collision

- [SHI12]: the Borel functional calculus of a normal $T \in M$ stays inside $M$ ·
  tier (a) · **asserted** ("an immediate consequence"), reconstructible from
  SHI12's own proof that the calculus is WOT-continuous.
- [HIA20]: polar and spectral decompositions are taken inside $M$ · tier (a) ·
  **asserted**.
- [KOS13]: the projections generate, $\mathrm{Proj}(N)'' = N$; and approximate
  finite-dimensionality reads $N = (\bigcup_i N_i)''$ · tier (b) · **asserted** —
  the corpus's only use of the theorem in the direction "density ⟹ bicommutant
  identity", which is the direction that matters downstream.
- [SOR23]: for any adjoint-closed $\mathcal{A} \subseteq B(H)$, $\mathcal{A}'$ is
  a von Neumann algebra · tier (a) · **sketched**. True with no unitality caveat,
  since $\mathcal{A}'$ always contains $1$, is a $*$-algebra when
  $\mathcal{A} = \mathcal{A}^{*}$, and is WOT-closed by (R5).
- [HIA20]: the **commutant theorem** $(M_1 \otimes M_2)' = M_1' \otimes M_2'$
  for tensor products · tier (a) · **asserted**. **A different theorem** sharing
  a similar name; recorded so it is never merged with this one.
- [ext: Sakai — a C\*-algebra is isomorphic to a von Neumann algebra if and only
  if it is the dual Banach space of some Banach space, and the predual is then
  unique. tier (c), no locator, not retrieved], attested by HIA20 and KOS13; it
  is the bridge (D10) uses.

### (R15) The single-generator theorem

On a separable Hilbert space, every abelian von Neumann algebra is $\{T\}''$ for
a single Hermitian $T$ in it.

- Source: [SOR23] · tier (a) for the statement · **cited elsewhere**
- Depends on: [ext: VN30 — on a separable Hilbert space every abelian von
  Neumann algebra is the bicommutant of a single self-adjoint operator it
  contains. tier (c), no locator, not retrieved]; SOR23 additionally claims the
  result appears as an exercise with hints in a work of Dixmier — that locator
  is **SOR23's claim**, reported here and not adopted
- Conventions: (A9)
- Carried because it is the only place in the corpus where separability is
  load-bearing; (A9) records the witness and (A11) what remains open.

## Hypotheses

| (A#) | Statement | Class | Evidence | Witness | Scope | Tier | Used by |
|---|---|---|---|---|---|---|---|
| (A1) | $M$ acts non-degenerately on $H$ | model-dependent | SHI12 states it as the hypothesis of the theorem | fails for $M = B(H_1) \oplus 0 \subseteq B(H_1 \oplus H_2)$, where (ii),(iii) hold and (i) fails; holds for $K(H)$ and $B(H)$ | local | a | (R1) step 4 only, i.e. (iii)⇒(i) only |
| (A2) | $1 \in M$ | provable | from (A1) plus any one of (i),(ii),(iii): (iii)⇒(i) gives $M = M''$, and $M''$ is unital by (R3)(ii). SHI12 records the conclusion in prose | — | local in LAN98/HIA20/HM06/NAA13/KOS13; standing in LAN98 after its mid-text change, and in SOR23 | a | (R9) step 3, (R10) — and nothing else in either proof |
| (A3) | $M$ is self-adjoint | model-dependent | every corpus source imposes it | fails for the upper-triangular $2\times2$ complex matrices: unital, closed in every topology, $M' = \mathbb{C}1$, $M'' = M_2(\mathbb{C}) \supsetneq M$; holds for every von Neumann algebra | local, and standing in SOR23 | a | (R1) step 3, (R4), (R3)(iv) |
| (A4) | $M$ is norm-closed | provable, **and used by no step** | each of (i),(ii),(iii) implies it via (R7); a step-by-step reading of (R1) finds no step consuming it | — | local, SHI12 only | a | nothing |
| (A5) | $M$ is a subalgebra, hence convex | provable (the convexity half is immediate) | a subalgebra is a linear subspace | fails for $V = \operatorname{span}\{1, e_{12}+e_{21}\} \subseteq M_3(\mathbb{C})$: self-adjoint, unital, closed, $\dim V = 2$ but $\dim V'' = 3$ | local, all sources | a | (R1) step 2, (R4), (R6) |
| (A6) | $\dim H < \infty$ | model-dependent | LAN98 imposes it on the finite-dimensional case and states its sharpness itself | fails for $M = K(H) + \mathbb{C}1$ on infinite-dimensional $H$: unital, norm-closed, $M' = \mathbb{C}1$, $M'' = B(H) \supsetneq M$; holds for $M_n(\mathbb{C})$ | local, (R10) only | a | (R10), to know $M\Psi$ is closed — it is what hypothesis (iii) is substituted for |
| (A7) | the vectors in (R10) span | provable | choose an orthonormal basis; nothing else in the argument constrains them | — | local, implicit — LAN98 says "arbitrary" | a | (R10)'s final step |
| (A8) | $D(M)$ acts non-degenerately on $H^n$ | provable, in one line | if $D(T)y = (Ty_1,\dots,Ty_n) = 0$ for all $T \in M$ then each $y_k$ is annihilated by all of $M$, so $y_k = 0$ by (A1) | — | local, implicit — SHI12 never checks it | a | (R1) step 7 |
| (A9) | $H$ separable | model-dependent | SOR23 declares it in its front matter | fails for $\ell^2(I)$, $I$ uncountable; holds for $L^2(\mathbb{R}^n)$ | standing in SOR23 | a | **not** the bicommutant theorem — no step of either full proof and no statement of the theorem uses it; used by (R15) and by the direct-integral decomposition |
| (A10) | $H$ is a complex Hilbert space | provable (it delimits the class rather than constraining members) | completeness is what gives the projection $P_X$ | — | standing | a | (R1) step 2, (R4) |
| (A11) | sharpness of (A9) below $2^{\aleph_0}$ | open | for $\lvert I \rvert > 2^{\aleph_0}$, $\ell^\infty(I)$ on $\ell^2(I)$ has no single Hermitian generator (argument written out in the lane notes); for $\lvert I \rvert \le 2^{\aleph_0}$ an injective $I \to \mathbb{R}$ exists and the obstruction vanishes | — | local | b | (R15) |

Cleared, after checking: irreducibility and factoriality; cyclic and separating
vectors; faithfulness and normality of representations; σ-finiteness,
hyperfiniteness, proper infiniteness and the type conditions; boundedness. None
is a hypothesis of this theorem in any corpus source.

## Degeneracies and boundary cases

| Case | Effect on the adopted form | Tier |
|---|---|---|
| intended case is nonvacuous | $B(H)$ for every $\dim H$ (HM06's type I$_\kappa$ factor); $\{T\}''$ for a single Hermitian $T$ (SOR23); $VN(S) = C^*(S)''$ (SHI12); hyperfinite $(\bigcup_a R_a)''$ (HM06); the type III local algebras of QFT (HM06) | a |
| zero object — $H = \{0\}$ | no effect. $B(\{0\}) = \{0\}$, non-degeneracy is vacuous, the identity is $0$ and lies in $M$, so **both** hypothesis packages hold and all three conditions are true. There is no edge case here | — |
| zero object — $M = \{0\}$, $H \ne \{0\}$ | excluded by every corpus variant. It is the minimal witness for dropping non-degeneracy: $M$ is WOT-closed but $M'' = \mathbb{C}1 \supsetneq M$ | — |
| scalars — $M = \mathbb{C}1$ | no effect; non-vacuous but trivial ($M' = B(H)$, $M'' = M$) | — |
| finite-dimensional | holds, and the topological content evaporates: LAN98 proves this case with no topological hypothesis, and HM06 states that the four topologies coincide iff $H$ is finite-dimensional. In finite dimensions non-degeneracy and unitality coincide for $*$-subalgebras — see (X5) | a |
| commutative | no effect; neither proof mentions commutativity, and the theorem keeps its content ($C[0,1]$ on $L^2[0,1]$ is neither WOT-closed nor its own bicommutant) | a |
| non-separable / non-σ-finite | no effect. Neither full proof assumes separability; $\ell^\infty(X)$ on $\ell^2(X)$ for uncountable $X$ is maximal abelian, hence satisfies the form and is not σ-finite | a |
| type III | no effect; the type classification is downstream of this theorem and never upstream of it | a |
| non-unital | **this is where the variants differ, and the difference is real.** $K(H)$ for infinite-dimensional $H$ is non-degenerate and non-unital, and satisfies the equivalence negatively: all three conditions fail together, since $K(H)'' = B(H)$ | a |
| degenerate representation | the hypothesis bites — see (X1) | — |
| universally orthogonal index element (here: large joint kernel or a reducing subspace) | a reducing subspace alone has no effect ($\mathbb{C}1$ on $\mathbb{C}^2$); a summand on which $M$ acts as zero breaks (i) and only (i). NAA13's failure of Haag duality for infinite regions is **not** a boundary of this theorem — it is the identification of $\pi(A(\Lambda))''$ with another algebra's commutant that fails, not the bicommutant construction | a |
| quantifier swap: non-degeneracy $\forall x \forall T \mapsto \forall T \forall x$ | meaning changes and the swapped form is wrong: it says every element of $M$ is injective, which fails for $M = B(\mathbb{C}^2)$, $T = e_{11}$ — the paradigm von Neumann algebra. See (X10) | — |
| quantifier swap: inside the commutant | degenerate probe. The two universals are separated by an implication and by different sorts; exchanging them is not type-correct. No row | — |
| hypothesis dropped: (A1) non-degeneracy | theorem false; (i)⇒(ii) and (ii)⇔(iii) survive, (iii)⇒(i) dies. See (X1) | — |
| hypothesis dropped: (A3) self-adjointness | theorem false. See (X2) | — |
| hypothesis dropped: (A5) algebra structure | theorem false. See (X3) | — |
| hypothesis dropped: (A4) norm-closedness | **droppable — this is what the adopted form does.** The enlarged class is inhabited by $F(H)$, for which all three conditions fail together. See (X4) | — |
| hypothesis dropped: (A9) separability | already dropped; no effect | a |
| hypothesis dropped: complex scalars | **open** — every corpus source works over $\mathbb{C}$, none states the real case, and neither a proof nor a counterexample was found | — |

## Rejected formulations and refuted claims

**Append-only.**

| id | Candidate or claim | Disposition | Discriminator | Tier | Date |
|---|---|---|---|---|---|
| (X1) | the theorem with (A1) dropped — equivalently, the unital variants (D3),(D5),(D6),(D7),(D9) as a *general* form | rejected | **(X1) separating object** — $M = \mathbb{C}e_{11} \subseteq M_2(\mathbb{C})$ is a closed self-adjoint algebra with $M' = $ the diagonal, so $M'' = \mathbb{C}e_{11} \oplus \mathbb{C}e_{22} \supsetneq M$ while (ii),(iii) hold; in infinite dimensions $B(H_0) \oplus 0$. Against the unital variants the separating object is $K(H)$, $\dim H = \infty$, which they do not cover | a | 2026-08-16 |
| (X2) | the theorem with (A3) dropped | rejected | **(X1) separating object** — the upper-triangular $2\times2$ complex matrices: unital, closed in every topology, $M' = \mathbb{C}1$, $M'' = M_2(\mathbb{C}) \supsetneq M$ | a | 2026-08-16 |
| (X3) | the theorem for a self-adjoint *subspace* rather than an algebra | rejected | **(X1) separating object** — $V = \operatorname{span}_{\mathbb{C}}\{1, e_{12}+e_{21}\} \subseteq M_3(\mathbb{C})$: $\dim V = 2$, and $e_{12}+e_{21}$ has three simple eigenvalues so $V''$ is a $3$-dimensional maximal abelian algebra. In $M_2$ the same construction gives no separation | a | 2026-08-16 |
| (X4) | keeping SHI12's norm-closedness hypothesis | rejected | **(X3) generality loss** — the finite-rank operators $F(H)$ on infinite-dimensional $H$ form a non-degenerate $*$-subalgebra that is not norm-closed, with $F(H)' = \mathbb{C}1$, so all three conditions fail together and the equivalence holds. Keeping the hypothesis drops that class and buys nothing: no proof step consumes it and each condition implies it | a | 2026-08-16 |
| (X5) | the unital form as a *distinct* theorem in finite dimensions | equivalent | — (in finite dimensions $M$ is automatically SOT-closed, so (iii)⇒(i) applies and delivers $M = M''$, which is unital; conditional equivalence with the assumption $\dim H < \infty$ named) | a | 2026-08-16 |
| (X6) | *claim*: the non-degenerate form is strictly more general than the unital form | adopted, sharpened | its entire extra content is the implication "non-degenerate and WOT-closed $\Rightarrow 1 \in M$": granted, it yields the adopted form; conversely the adopted form yields it because $X'$ is always unital. The extra scope contains only negative instances, and $K(H)$ inhabits it | a | 2026-08-16 |
| (X7) | von Neumann's original **sequential** WOT-completeness (D4) as a formulation of closedness | rejected | **(X1) separating object** — on a non-separable $H$ take $S = \{T : \operatorname{ran} T, \operatorname{ran} T^{*} \text{ separable}\}$ and $M = \mathbb{C}1 + S$: a unital $*$-subalgebra, sequentially WOT-closed, with $M' = \mathbb{C}1$ so $M'' = B(H)$, yet $M \ne B(H)$. For **separable** $H$ the two coincide, by Kaplansky density (R12) plus metrizability of SOT on the unit ball | b | 2026-08-16 |
| (X8) | *claim*: SOR23's statement of the theorem is false as written | refuted | SOR23's own definition of "$*$-subalgebra" includes the identity, so its statement is the standard unital one and is true. The witnesses $\{0\}$ and $\mathbb{C}p$ refute it only under the standard non-unital reading — they are a convention discriminator, recorded at (D8), not a defect | a | 2026-08-16 |
| (X9) | KOS13's σ-weak / σ-strong / σ-strong-⋆ form (D9) as a *different* theorem | equivalent | — (for a non-degenerate $*$-subalgebra all six closure conditions coincide; the argument runs SHI12's proof on the infinite ampliation $T \mapsto T \otimes 1$, whose seminorms pull back to the σ-topologies. **No corpus source states this**, and the ampliation identity it consumes is an unretrieved external, so the row is tier (d) as a whole. A bounded-set cross-check grounds the σ-weak and σ-strong branches for *unital* $M$ without that external; the σ-strong-⋆ branch does not survive the cross-check and keeps the (d) input) | d | 2026-08-16 |
| (X10) | non-degeneracy read as "every element of $M$ is injective" | rejected | **(X2) degeneracy** — the reading excludes $M = B(H)$ for $\dim H \ge 2$ (take $T = e_{11}$), i.e. the paradigm case the form must cover | a | 2026-08-16 |
| (X11) | non-degeneracy read as "$MH$ is dense in $H$" | equivalent | — (equivalent given (A3); the two come apart without it, separating object $\operatorname{span}\{e_{11}, e_{12}\} \subseteq M_2(\mathbb{C})$, an algebra with trivial joint kernel whose range is not dense. Conditional equivalence with the assumption $M = M^{*}$ named) | a | 2026-08-16 |
| (X12) | *claim*: HM06's fact that the weak, ultraweak and norm closures of a bounded convex set agree | refuted | the closed unit ball of $K(H)$, $\dim H = \infty$, is bounded and convex; its norm closure is itself and its weak closure is the unit ball of $B(H)$, by (R13) and (R12). Deleting "norm" makes the statement true | a | 2026-08-16 |

## Prior art

| System | Found | Relation to variants | How searched | Measured at |
|---|---|---|---|---|
| Mathlib | `VonNeumannAlgebra`, a structure extending `StarSubalgebra ℂ (H →L[ℂ] H)` whose defining field states that the centralizer of the centralizer of the carrier is the carrier | same as (D1)/(D8) — algebraic, and **unital by construction** since `StarSubalgebra` is; non-degeneracy is nowhere mentioned, so relative to (D2) it is stronger on hypotheses and $K(H)$ separates them | `grep -rn "VonNeumannAlgebra"` over `.lake/packages/mathlib`, whole file read; `lean_leansearch`; `lean_loogle` on the centralizer pattern | mathlib rev `5450b53e` |
| Mathlib | `WStarAlgebra`, a separate structure with a single field asserting a predual exists | same as (D10) — Mathlib follows KOS13's separation of the two notions, not HIA20's identification | same sweep | mathlib rev `5450b53e` |
| Mathlib | could not find any declaration equating WOT- or SOT-closedness with the bicommutant condition, having searched `grep -rni "bicommutant\|double.commutant\|doubleCommutant"`, `grep -rni "commutant"`, `lean_leansearch`, `lean_loogle` and `lean_leanfinder`. Mathlib's own module docstring says the equivalence and the theorem remain to be proved, and names a (D6)-shaped target | — | as listed | mathlib rev `5450b53e` |
| Mathlib | `Set.centralizer`, `Set.centralizer_centralizer_centralizer`, `StarSubalgebra.centralizer`, `VonNeumannAlgebra.commutant_commutant` (which holds by definition, not by a topological argument), `StarSubalgebra.topologicalClosure_adjoin_le_centralizer_centralizer` (an inclusion in the **norm** topology) | weaker than every corpus variant | same sweep | mathlib rev `5450b53e` |
| Mathlib | WOT is present (`→WOT[𝕜]`, `toWOT`); SOT is present under the name of the topology of pointwise convergence, with a docstring saying the term "strong operator topology" is deliberately avoided | — | `grep -rn "StrongOperatorTopology"` returned nothing, which prompted `grep -rni "strong operator topology"` | mathlib rev `5450b53e` |
| Mathlib | could not find Kaplansky density, a Borel/measurable functional calculus, spectral measures, direct integrals, σ-weak or σ-strong topologies, or normal states. The spectral theorem is present only in a finite-dimensional diagonalization form; the **continuous** functional calculus is present in full | — | `grep -rni` per term | mathlib rev `5450b53e` |
| This repository | `WOTClosedSubalgebra.doubleCommutant_eq_of_isWOTClosed`, `SOTClosedSubalgebra.doubleCommutant_eq_of_isSOTClosed`, and `SOTClosedSubalgebra.mem_sotClosure_of_mem_doubleCommutant` under `QuantumSystem/Algebra/Star/DoubleCommutant/`, with no `sorry` or `axiom` in that directory | same as (D3)/(D5) — all three take a `StarSubalgebra`, hence **unital**; none is stated for a non-unital or non-degenerate algebra. The third is the density statement (R2) in unital form, carrying no closedness hypothesis. The SOT theorem is derived from the WOT one, so the two are not independent proofs | file read; `grep -rn "sorry\|axiom "`; repo-wide grep for non-degeneracy finds it only in unrelated files. Statement-level measurement only — no `lake build` was run | repo `9b1810d` |
| This repository | could not find any equivalence (`iff`/TFAE) packaging the three conditions, nor any lemma constructing a `VonNeumannAlgebra` from a closed `StarSubalgebra`. Both main theorems are leaves: the WOT one is called only by the SOT one, and the SOT one is called nowhere | — | `grep -rn "TFAE\|IsWOTClosed.*↔\|↔ IsSOTClosed"`, call-site grep | repo `9b1810d` |
| mathlib4 GitHub | PR #35538, "feat(Analysis/VonNeumannAlgebra): double commutant theorem", opened 2026-02-19 and **closed unmerged** 2026-03-09. Its main statement is a two-condition WOT form for a unital `StarSubalgebra`, by the same diagonal-amplification route. Closed over a review disagreement; no mathematical obstruction appears in the thread | same as (D6) | unauthenticated GitHub REST search, then the PR, comments and files endpoints | 2026-08-16 |
| Lean AI leaderboard | the three-condition unital form is listed as a benchmark problem and is **solved**, first on 2026-05-09 and seven times since | same as (D3)/(D5) | fetched the problem page | 2026-08-16 |
| Isabelle AFP | `Complex_Bounded_Operators` provides complex Hilbert spaces, bounded operators, adjoints and projections; its abstract mentions no von Neumann algebra, commutant or operator topology | unrelated — substrate only | two web searches plus the entry abstract; the AFP search page returned only site chrome, so this negative rests on a weak instrument | 2026-08-16 |
| Coq / Rocq / mathcomp | could not find a von Neumann algebra or commutant development, having run **one** query. This is a single-query result, not an absence | — | one web search | 2026-08-16 |
| Lean Zulip | no archive page was retrieved by any of four searches; the archive appears poorly indexed and the Zulip API was not queried | — | four web searches | 2026-08-16 |

## Open questions

- Does the adopted form hold over a **real** Hilbert space? No corpus source
  treats it, and neither a proof nor a counterexample was found.
- (A11): for which density characters between $\aleph_1$ and $2^{\aleph_0}$ does
  (R15) fail? The argument on file settles only $> 2^{\aleph_0}$.
- (X9) is tier (d) as a whole because its σ-strong-⋆ branch consumes an
  unretrieved external (the infinite-ampliation commutant identity). Grounding
  it needs either that identity or a self-adjoint form of Kaplansky density,
  which HIA20 does not state.
- Whether von Neumann's paper is dated 1929 or 1930 cannot be settled here: the
  corpus's two dates attach to bibliographically identical data, so there is one
  paper in play, and only the original could say whether 1929 is a submission
  year against a 1930 issue.

## Sources

**Append-only.**

| Key | Work | Status | Cache | Version | Tier reached | Retrieved |
|---|---|---|---|---|---|---|
| SHI12 | V. Shirbisheh, *Lectures on C\*-algebras*, arXiv:1211.3404 | retrieved | `references/arxiv-1211.3404/` | arXiv | a | 2026-08-16 |
| LAN98 | N. P. Landsman, *Lecture Notes on C\*-algebras, Hilbert C\*-modules and Quantum Mechanics*, arXiv math-ph/9807030 | retrieved | `references/arxiv-math-ph-9807030/` | arXiv | a | 2026-08-16 |
| HIA20 | F. Hiai, *Concise lectures on selected topics of von Neumann algebras*, arXiv:2004.02383 | retrieved | `references/arxiv-2004.02383/` | arXiv | a | 2026-08-16 |
| KOS13 | R. P. Kostecki, *W\*-algebras and noncommutative integration*, arXiv:1307.4818 | retrieved | `references/arxiv-1307.4818/` | arXiv | b (macros unavailable) | 2026-08-16 |
| SOR23 | J. Sorce, *Notes on the type classification of von Neumann algebras*, arXiv:2302.01958 | retrieved | `references/arxiv-2302.01958/` | arXiv | a | 2026-08-16 |
| NAA13 | P. Naaijkens, *Quantum spin systems on infinite lattices*, arXiv:1311.2717 | retrieved | `references/arxiv-1311.2717/` | arXiv | a | 2026-08-16 |
| HM06 | H. Halvorson, M. Müger, *Algebraic Quantum Field Theory*, arXiv math-ph/0602036 | retrieved | `references/arxiv-math-ph-0602036/` | arXiv | a | 2026-08-16 |
| VN30 | J. von Neumann, *Zur Algebra der Funktionaloperationen und Theorie der normalen Operatoren*, Math. Ann. 102 (1930) 370–427 | not retrieved — tried the GDZ id and mets endpoints (JavaScript-only shell, no METS served) and EUDML doc/159384 (HTTP 403); Springer paywall not pursued | — | — | c | 2026-08-16 |
| CON00 | J. B. Conway, *A Course in Operator Theory*, American Mathematical Society, 2000 | not retrieved | — | — | d | 2026-08-16 |
| PED79 | G. K. Pedersen, *C\*-algebras and their Automorphism Groups* | not retrieved | — | — | b (method attribution only) | 2026-08-16 |
| MUR90 / DIX77 / TAK79 / BLA06 | the standard C\*-algebra and operator-algebra textbooks | not retrieved | — | — | c | 2026-08-16 |

## Not investigated

- **The `[ext: …]` edges lane 5 never reached.** Formalization status was
  measured for Kaplansky density, the spectral theorem, the Borel functional
  calculus, Sakai's characterisation, the reduction/direct-integral theorem and
  the σ-topologies. It was **not** measured for: the single-generator theorem;
  the Dixmier and Conway pointers; Pedersen's proof strategy; Wedderburn's
  decomposition result; Murray–von Neumann 1936; Bratteli–Robinson's
  infinite-region statement; the infinite-ampliation commutant identity that (X9) consumes; and
  the identification $C[0,1]'' = L^\infty[0,1]$ that the commutative-case row
  uses.
- **Sources listed as not retrieved, and what rests on them.** VN30 carries the
  attribution of the theorem itself and of (R15); every row citing it is (c) and
  carries a statement instead of a locator. CON00 carries SOR23's only proof
  pointer. PED79 carries SHI12's method attribution — nothing in SHI12's proof
  depends on it for correctness. The textbook row is why no note in this
  repository may carry a locator into any of them.
- **Degeneracy checklist items skipped:** none. The real-scalar case is filed
  `open` rather than skipped.
- **Variants sighted and not pursued.** KOS13's relative commutant inside an
  arbitrary ambient algebra is recorded at (D9) but not developed — the note
  treats only the case where the ambient algebra is $B(H)$. KOS13's later
  sections (spatial derivatives, Connes cocycles) and HIA20's later chapters
  were not swept for restatements of the theorem carrying different hypotheses.
- **Internal edges never opened**, so the floor of the proof readings is: SHI12's
  Hahn–Banach separation for locally convex spaces, its Riesz representation for
  bounded sesquilinear forms, its Cauchy–Schwarz equality case, and two of its
  remarks; LAN98's decomposition into self-adjoint parts and its refined
  Gelfand–Naimark decomposition. (R6), (R3)(v) and (R4) therefore have
  unverified floors.
- **The unexamined base.** Everything above stands on: the tier (c) attribution
  of the theorem to VN30, which no one here has opened; the tier (d) row (X9),
  which is the only bridge between the corpus's WOT/SOT framework and its
  σ-topology framework; the tier (b) reading (R2) that the corpus proof
  establishes the density form, which no source states; the tier (b) status of
  every mathematical reading of a KOS13 quote, whose macros cannot be
  reconstructed from the arXiv package; and, for the prior-art rows, a
  statement-level measurement of this repository that was never elaborated by
  `lake build`.
