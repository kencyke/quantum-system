# `InfiniteTensor/` ↔ von Neumann (1939) mapping

This document maps the seven Lean files in this directory onto the paper
**J. von Neumann, *On infinite direct products*, Compositio Mathematica **6**
(1939), pp. 1–77** (Numdam: `CM_1939__6__1_0`).

The paper is available locally at
[`references/cm-1939-6-1-0/`](../../../references/cm-1939-6-1-0/) — body
in `sections/02-on-infinite-direct-products.md`, summary and tier-annotated
key concepts in `INDEX.md`.

The Lean files cite Bratteli–Robinson Vol. 2 §2.7.2 and Naaijkens 2012 §3.5
as direct sources, but those are the modernised re-presentation; the
underlying mathematics is von Neumann 1939.  The most consequential
identifications established below are:

- `cRel`  ≡ vN's strong equivalence `≈` (Definition 3.3.2);
- `c0Rel` ≡ vN's **weak equivalence** `≈_w` (Definition 6.1.1 + Lemma 6.1.3);
- `ITPSector Ω` ≡ vN's incomplete direct product `Π⊗^C_{α∈I} H_α` for
  the class `C = [Ω]` (Definition 4.1.1 + Theorem III).

## Notation cheat sheet

| vN 1939 symbol | Lean identifier | Where defined |
| --- | --- | --- |
| `H_α` (unitary space at site `α`) | `H : ι → Type*` with `[InnerProductSpace ℂ (H i)]` | parameter throughout |
| unit-norm `C₀`-sequence representative (Lemma 3.3.7) | `InfiniteTensor.UnitFamily H` | `Product.lean` |
| finite tensor `Π⊗_{α∈S} H_α` (`S` finite) | `InfiniteTensor.regionTensor S` | `Extension.lean` |
| `f^0 ↦ ⊗ ξ_α^0 ↦ Π(f^0_α, ·)` (elementary product) | `PiTensorProduct.tprod ℂ` (from mathlib) on `regionTensor` | `Extension.lean` (used) |
| `Π'⊗_{α∈I} H_α` (algebraic pre-completion, Definition 3.1.4) | `InfiniteTensor.UnitFamily.preITPSector` | `Extension.lean` |
| `Π⊗^C_{α∈I} H_α` (incomplete direct product, Definition 4.1.1) | `InfiniteTensor.UnitFamily.ITPSector` | `Completion.lean` |
| `Π⊗_w^{C_w}_{α∈I} H_α` (weak-class incomplete direct product, Definition 6.1.3) | per-fibre of `InfiniteTensor.decomposableTensorProduct` | `SectorDecomp.lean` |
| `Π⊗_{α∈I} H_α` (vN's full complete direct product) | **not formalised** — `decomposableTensorProduct` is the *separable* `c0Equiv`-aggregate, not the non-separable continuum sum |
| `≈` (Definition 3.3.2: `Σ\|(f, g) − 1\| < ∞`) | `InfiniteTensor.UnitFamily.cRel` | `SectorEquiv.lean` |
| `≈_w` (Definition 6.1.1 / Lemma 6.1.3: `Σ\|\|(f, g)\| − 1\| < ∞`) | `InfiniteTensor.UnitFamily.c0Rel` | `SectorEquiv.lean` |
| (no direct vN name; finer than `≈`) | `InfiniteTensor.UnitFamily.referenceRel` (agreement off a finite set) | `SectorEquiv.lean` |
| (no direct vN name; intermediate) | `InfiniteTensor.UnitFamily.strongRel` (`Σ‖f − g‖² < ∞`) | `SectorEquiv.lean` |
| `T`  (set of `≈`-classes) | **not formalised as a Lean quotient**; `cRel` exists but no `cEquiv` `Setoid` is packaged | `SectorEquiv.lean` |
| `T_w` (set of `≈_w`-classes) | `Quotient c0Equiv` | `SectorEquiv.lean`; indexer of `decomposableTensorProduct` |
| extended operator `Ā_{α₀}` (Lemma 5.1.1) | **not formalised at the pure-ITP layer**; lattice-side analogue: `LocalNetLike.localEmbedRefSector` | `LatticeBridge.lean` |
| `U(z_α; α∈I)` (diagonal unitary, Definition 6.2.1) | **not formalised as a named scalar-diagonal operator**; abstract/non-canonical replacements: `noncanonicalSectorEquivAny`, `SectorEquivData` | `SectorIsometry.lean` |
| `P[C]`, `P_w[C_w]` (projection onto incomplete sector) | **not formalised** as a single decl; `embedRegion` provides per-region isometries | `Completion.lean` |
| `B^#` (ring of extended operators, Definition 6.3.1) | **not formalised**; lattice-side fragments: `localEmbedDecompRingHom`, and the stronger star-preserving `localEmbedDecompStarHom` | `LatticeBridge.lean` |

## File-by-file overview

### `Product.lean` (90 lines) — vN §3.3 unit-norm representative

Sets up the parameter shape.  `UnitFamily H` bundles a function
`vec : (i : ι) → H i` with a proof `‖vec i‖ = 1`, packaged with a
`DFunLike` instance so `Ω i` reads as the vector at site `i`.  This is
**vN's unit-norm `C₀`-sequence representative**, justified by Lemma 3.3.7
(every `≈`-class contains a sequence with `‖f_α‖ = 1` everywhere).

### `Extension.lean` (577 lines) — vN §3.1–3.4 construction of `Π'⊗`

Builds the directed system of finite tensor products and the algebraic
colimit:

- `regionTensor S` — finite tensor `⨂[ℂ] s : S, H s.val`.
- `extendVec Ω h ξ`, `extendMultilinear Ω h` — extension of
  a tuple on `S` to a tuple on `S' ⊇ S` by filling with `Ω`-components.
  This is the elementary-product step `f ⊗ Ω_α'` of vN §3.5.
- `regionEmbedLe Ω h` and `regionEmbedLeIsom Ω h` —
  the corresponding linear / isometric maps `regionTensor S → regionTensor S'`.
- `regionDirectedSystem` — instance proving the
  `regionEmbedLe` family is a `Module.DirectedSystem`.
- `preITPSector Ω` — the algebraic colimit
  `Module.DirectLimit … regionEmbedLe`, which **is** vN's `Π'⊗_{α∈I} H_α`
  (Definition 3.1.4 / Theorem II).  The conjugate-linear-functional
  presentation of vN is replaced by a colimit presentation; the two are
  mathematically equivalent for unit-norm representatives.
- `innerPreITPSector` plus `instInnerProductSpacePreITPSector`
  — gives `Π'⊗` its inner product (vN's Lemma 3.2.1 / Lemma 3.4.1
  / Theorem II).

### `SectorEquiv.lean` (311 lines) — vN §3.3, §6.1 equivalence relations

The four-relation hierarchy on `UnitFamily H`:

- `referenceRel` — agreement off a finite set; sufficient for `≈`
  (vN Lemma 3.3.5).
- `strongRel` — `Σ‖Ω − Ω'‖² < ∞`.  Real part of vN Lemma 3.3.4.
- `cRel` — `Σ|⟨Ω, Ω'⟩ − 1| < ∞`.  This is vN's `≈`
  (Definition 3.3.2).
- `c0Rel` — `Σ(1 − |⟨Ω, Ω'⟩|) < ∞`.  This is vN's `≈_w`
  (Definition 6.1.1 / Lemma 6.1.3); the Setoid `c0Equiv` exists.

Inclusions proved: `referenceRel ⊆ strongRel ⊆ c0Rel`,
`referenceRel ⊆ c0Rel`, `cRel ⊆ c0Rel`.  The chain `strongRel ⊆ cRel`
**does not hold** — see the design-divergences section below for the
counterexample and the connection to vN Lemma 3.3.4.

### `Completion.lean` (143 lines) — vN §3.5, Theorem III

`ITPSector Ω` is `UniformSpace.Completion (preITPSector Ω)`.
This realises the metric completion of vN's `Π'⊗` to the complete
incomplete-direct-product `Π⊗^[Ω]_{α∈I} H_α` (Theorem III).

- `fromPre`, `fromRegion S`, `embedRegion S`
  — the canonical isometric embeddings from each layer.
- `denseRange_fromPre`, `denseRange_iUnion_embedRegion` — finite-region
  images are dense (vN §3.5 / Lemma 3.5.8: `Π'⊗ ⊆ Π⊗` is dense).

### `SectorIsometry.lean` (1650 lines) — vN §6.2 unitary sector transport

Targets the **sector isometry theorem**:
`c0Rel Ω Ω' → ITPSector Ω ≃ₗᵢ[ℂ] ITPSector Ω'` (this is the abstract
content of vN's `U(z_α)` for `|z_α| = 1` combined with Lemma 6.2.3).

What is done:

- `sectorEquivOfEquivalent_refl` — trivial diagonal case.
- `referenceRel` case — `forwardFiber*`, `forwardPre*`,
  `preITPSectorEquivOfReferenceRel`, `sectorEquivOfReferenceRel`,
  `sectorEquivOfEquivalent_referenceRel`.  Handles finite-deviation
  identifications cleanly, no infinite-product machinery.
- General arbitrary-family case via `Classical.choice` —
  `chooseRotation`, `regionRot`, `forwardFiberAny`, …,
  `noncanonicalSectorEquivAny`.  Gives a Hilbert-space identification
  for **arbitrary** unit families, hence in particular for `c0Rel`-equivalent
  families, sacrificing canonicity and functoriality.
- `SectorEquivData` framework — abstracted data carrying
  per-site unitaries; proves `refl`/`symm`/`trans` laws
  (`sectorEquivOfData_refl/symm/trans`).  Designed to replace the
  ad-hoc `Any` constructions.  `FiniteSiteIsoData`
  specialises to finite support; `ofReferenceRel` bridges to
  the finite-deviation case.
- `C0SectorMorphism` bundles a `c0Rel` witness together with
  coherent transport data; `sectorEquivOfReindexedData`
  provides the corresponding reindexed transport API for group actions.
- `ReindexedSectorTransportData` — index-set reindexing
  variant, needed for group actions.

What is **not** done: the canonical `c0Rel`-only wrapper
`sectorEquivOfEquivalent : c0Rel Ω Ω' → ...` and the
`Complex.multipliable_of_summable_log`-based phase-normalised Route 1 from
the file's opening comment; that would realise vN's `U(z_α)` directly
rather than via non-canonical choices or externally supplied transport data.

### `SectorDecomp.lean` (119 lines) — vN §4.1 Lemma 4.1.1 / Theorem V (separable variant)

`decomposableTensorProduct H` is
`lp (Quotient c0Equiv ↦ ITPSector H q.out) 2`, an `ℓ²` direct sum over
weak-equivalence classes.  This is the **separable** Bratteli–Robinson
decomposition, *not* vN's non-separable complete direct product
(Theorem V's decomposition is uncountable; see "Design divergences"
below).

The file commentary still leaves pending the per-sector embedding
`sectorEmbed Ω : ITPSector H Ω →ₗᵢ[ℂ] decomposableTensorProduct H`.
The representative-case map is only described structurally as
`lp.lsingle 2 q`.  For general `Ω`, `SectorDecomp.lean` still lacks the
packaging step from a `c0Equiv` witness to the chosen representative fibre.
`SectorIsometry.lean` already provides non-canonical arbitrary-family
equivalences (`noncanonicalSectorEquivAny`) and coherent transport APIs
(`SectorEquivData`, `C0SectorMorphism`), but `sectorEmbed` itself is not
yet defined here.

### `LatticeBridge.lean` (2953 lines) — bridge to the lattice / quasi-local layer (no vN counterpart)

vN 1939 has **no lattice notion**; his index set `I` is an abstract set
(typically `ℕ` for the interesting cases).  This file is **extension
beyond vN scope** — specialisation of the pure ITP layer to
`H s := siteHilbert s` for `LocalNetLike L`, instantiating the abstract
`UnitFamily` with the canonical reference choice
`referenceUnitFamily L`.  Builds the chain

```
regionTensor (siteHilbert ·) Λ ≃ₗᵢ regionHilbert Λ ↪ referenceSectorHilbert L
```

(via `regionTensorBasis` and `regionTensorONB`) and
then the local-operator API (`localEmbedRefSector`,
`localEmbedSector`, `localEmbedDecomp`).  Closest to vN: the lattice-side
bundlings `localEmbedDecompRingHom` and
`localEmbedDecompStarHom` mirror part of vN Lemma 5.1.2 /
Theorem VIII at the lattice-restricted level, but the algebra `B^#` of
vN §6.3 is not formalised.

## Section-by-section correspondence

| vN ref | vN statement (paraphrase) | Lean status | Lean declaration |
| --- | --- | --- | --- |
| Def 2.2.1 | `Π z_α` / `Σ z_α` convergence over unordered finite sets | mathlib | `Multipliable`, `Summable` |
| Lemma 2.3.1 | `Σ z_α ≥ 0` converges ⇔ partial-sum set bounded | mathlib | `Summable.tsum_eq` etc. (general theory) |
| Lemma 2.3.3 | `Σ z_α` converges ⇔ `Σ\|z_α\|` converges (complex case) | mathlib | covers `summable_iff_abs_summable` for ℂ |
| Lemma 2.3.4 | `Σ z_α` converges ⇔ countable nonzero support + `Σ\|z_αₙ\| < ∞` | → needs formalization | (combines `Summable.countable_support` + abs summability; no single mathlib lemma) |
| Lemma 2.4.1 | `Π\|z_α\| ≥ 0` convergence criteria | → needs formalization |  |
| Lemma 2.4.2 | `Π z_α` converges ⇔ `Π\|z_α\| = 0` OR (`Π\|z_α\|` and `Σ\|arcus z_α\|` converge) | → needs formalization |  |
| Def 2.5.1 | `Π z_α` is **quasi-convergent** if `Π\|z_α\|` converges | → needs formalization |  |
| Lemma 2.5.1 | Quasi-conv. ≠ 0 ⇔ all `z_α ≠ 0` and `Σ\|z_α − 1\| < ∞` | mathlib | `Complex.multipliable_of_summable_log` |
| Lemma 2.5.2 | `Π‖f_α‖`, `Π‖g_α‖` quasi-conv. ⇒ `Π(f_α, g_α)` quasi-conv. | → needs formalization |  |
| Def 3.1.1 | `f_α ∈ H_α`, `Π‖f_α‖` converges → `C`-sequence | → needs formalization (folded into pure-`UnitFamily` ≡ `C₀`-rep.) |  |
| Lemma 3.1.1 | Two `C`-sequences ⇒ `Π(f, g)` quasi-conv. | → needs formalization |  |
| Def 3.1.2 | conjugate-linear functionals `Φ` on `C`-sequences | structurally different in Lean | `Module.DirectLimit` colimit instead — same UMP |
| Def 3.1.4 | `Π'⊗_{α∈I} H_α` = span of `Π⊗ f^0_α` | formalized | `InfiniteTensor.UnitFamily.preITPSector` (`Extension.lean`) |
| Lemma 3.2.1–3.2.3 | inner-product properties of `Π'⊗` | formalized | inner instance via `innerPreITPSector` + lemmas `inner_preITPSector_*` (`Extension.lean`) |
| Def 3.3.1 | `Σ\|‖f_α‖ − 1\| < ∞` → `C₀`-sequence | partially formalized | `UnitFamily.norm_vec` enforces `‖vec i‖ = 1`, i.e. the unit-norm representative of Lemma 3.3.7 |
| Lemma 3.3.1 | every `C₀`-seq is a `C`-seq; every `C`-seq with nonzero product is `C₀`. | → needs formalization (not needed at unit-norm level) |  |
| Lemma 3.3.2 | `Σ\|‖f‖ − 1\| < ∞` ⇔ `Σ\|‖f‖² − 1\| < ∞` | → needs formalization |  |
| Def 3.3.2 | `(f) ≈ (g)` ⇔ `Σ\|(f, g) − 1\| < ∞` | formalized | `InfiniteTensor.UnitFamily.cRel` (`SectorEquiv.lean`); the `Setoid` is **not** packaged (file note `SectorEquiv.lean`) |
| Lemma 3.3.3 | `≈` is a Setoid | partially formalized | `cRel` is defined and `cRel_le_c0Rel` is proved, but there is no `cEquiv : Setoid _`; transitivity for `cRel` is deferred (`SectorEquiv.lean`) |
| **Theorem I** | different `≈`-classes ⇒ orthogonal `Π⊗ f`, `Π⊗ g` | → needs formalization |  |
| Lemma 3.3.4 | `≈` ⇔ `Σ‖f − g‖² < ∞` **and** `Σ\|Im(f, g)\| < ∞` | → needs formalization | (key for the `strongRel ⊄ cRel` gap) |
| Lemma 3.3.5 | finite-disagreement ⇒ `≈` | partially formalized | only the weaker inclusion `referenceRel ⊆ c0Rel` appears as `referenceRel_le_c0Rel` (`SectorEquiv.lean`); `referenceRel_le_cRel` is absent |
| Lemma 3.3.6 | scaling and equivalence under `z_α` weights | → needs formalization | (key for §6.1 weak equivalence introduction) |
| Lemma 3.3.7 | every `≈`-class has unit-norm representative | formalized (by design) | `InfiniteTensor.UnitFamily` requires `‖vec i‖ = 1` (`Product.lean`) |
| Def 3.4.1 / Lemma 3.4.1–3.4.3 | norm and Schwarz on `Π'⊗` | formalized | `instInnerProductSpacePreITPSector` (`Extension.lean`) inherits Schwarz |
| **Theorem II** | `Π'⊗` is a unitary space (Hermitean + definite inner product) | formalized | `instInnerProductSpacePreITPSector` (`Extension.lean`) |
| Def 3.5.1 | `Π⊗_{α∈I} H_α` = limits of Cauchy sequences from `Π'⊗` | formalized | `InfiniteTensor.UnitFamily.ITPSector := UniformSpace.Completion preITPSector` (`Completion.lean`) |
| Lemma 3.5.2 / 3.5.7–3.5.9 | Cauchy sequences have unique limits; `Π'⊗` dense in `Π⊗`; `Π⊗` complete | formalized | `denseRange_fromPre` / `CompleteSpace` instance (`Completion.lean`) |
| **Theorem III** | `Π⊗` is a unitary (complete) space | formalized | `instInnerProductSpace`, `instCompleteSpace` on `ITPSector Ω` (`Completion.lean`) |
| **Theorem IV** | uniqueness of `Π⊗` up to isomorphism on `Π⊗ f^0` | → needs formalization | (used in `SectorIsometry.lean` proofs only implicitly via `UniformSpace.Completion`'s UMP) |
| Def 4.1.1 | `Π⊗^C_{α∈I} H_α` = closed span of `Π⊗ f` for `f ∈ C` | formalized as ITPSector per representative | `InfiniteTensor.UnitFamily.ITPSector` (`Completion.lean`) — one Hilbert space per `c0Equiv`-class representative |
| Lemma 4.1.1 | `Π⊗^C` are mutually orthogonal; span = `Π⊗` | → needs formalization | (sector orthogonality at the `cRel`-level; only `c0Equiv` direct-sum packaging at present in `decomposableTensorProduct`) |
| Lemma 4.1.2 | `Π⊗^C` is also generated by `f^0 + finite-deviation` sequences | partially formalized | `sectorEquivOfReferenceRel` provides the unitary identification (`SectorIsometry.lean`) |
| Lemma 4.1.3 | per-factor linearity / continuity of `Π⊗ f` | → needs formalization |  |
| Lemma 4.1.4 | explicit ONB construction from per-site `φ_{α,β}` | → needs formalization | (mathlib's `Basis.piTensorProduct` does this for *finite* `S` only — see `LatticeBridge.regionTensorBasis:124`) |
| **Theorem V** | bijection `Π⊗^C ↔ ℓ²(F)` for `F = finite-support β(α)`-functions | → needs formalization | (would give `ITPSector Ω` an explicit `OrthonormalBasis`) |
| **Theorem VI / VII** | associative law for `Π⊗` over a partition of `I` | → needs formalization |  |
| Lemma 5.1.1 / 5.1.2 | extension `A_{α₀} ↦ Ā_{α₀}`; `*`-isomorphism on each factor | → needs formalization at pure layer | lattice-side analogue: `LocalNetLike.localEmbedRefSector` (`LatticeBridge.lean`) and its compatibility lemmas |
| Lemma 5.2.1 | `B̄_{α₀}` is a ring containing `1` | partially via lattice analogue | `localEmbedRefSector_one` / `localEmbedRefSector_mul` give the reference-sector ring laws; `localEmbedRefSectorHom` is only the linear packaging (`LatticeBridge.lean`) |
| Lemma 5.2.2 / 5.2.3 | structure of `Π'⊗ f ⊗ g` and ring images under extension | → needs formalization |  |
| **Theorem VIII** | `A ↦ Ā` is a `*`-homomorphism (full version) | partially via lattice analogues | `localEmbedRefSector_*` covers the reference fibre, and `localEmbedDecompStarHom` packages the decomposable-space lattice analogue (`LatticeBridge.lean`) |
| Def 6.1.1 / Lemma 6.1.1 | weak equivalence: `∃ \|z_α\| = 1` with `z·f ≈ g` | formalized via Lemma 6.1.3 | `c0Rel` is defined directly in terms of Lemma 6.1.3's criterion |
| Lemma 6.1.2 | `≈_w` is a Setoid | formalized | `InfiniteTensor.UnitFamily.c0Equiv` (`SectorEquiv.lean`) |
| Def 6.1.2 / Def 6.1.3 | `T_w`, `Π⊗_w^{C_w}` | formalized as quotient + fibres | `Quotient c0Equiv` indexes `decomposableTensorProduct H` (`SectorDecomp.lean`) |
| Lemma 6.1.3 | `≈_w` ⇔ `Σ\|\|(f, g)\| − 1\| < ∞` | formalized **by definition** | this **is** the definition of `c0Rel` (`SectorEquiv.lean`) |
| Lemma 6.2.1 / Def 6.2.1 | diagonal unitary `U(z_α; α∈I)`, `\|z_α\| = 1`, with `U Π⊗ f = Π⊗ z_α f` | partially formalized | `noncanonicalSectorEquivAny` gives an arbitrary Hilbert equivalence, and `SectorEquivData` packages coherent per-site unitaries; the **specific** scalar-diagonal `U(z_α)` is not named (`SectorIsometry.lean`) |
| Lemma 6.2.2 / 6.2.3 | `U(z_α)` commutes with `P_w[C_w]`; commutes with `P[C]` iff `Π z_α` conv. | → needs formalization |  |
| Lemma 6.2.4 | `Ā_{α₀}` commutes with all `P[C]`, `P_w[C_w]`, `U(z_α)` | → needs formalization |  |
| Def 6.3.1 | `B^#` = ring generated by all `Ā_{α₀}` | → needs formalization |  |
| Def 6.3.2 / Lemma 6.3.2–6.3.5 | `M[Φ]`, `E[Φ]` and their `B^#`-membership properties | → needs formalization |  |
| **Theorem IX** | `A ∈ B^#` ⇔ `A` commutes with all `P[C]` and `U(z_α)` | → needs formalization |  |
| **Theorem X** | `B^# = B(Π⊗)` ⇔ `I` is finite; structure of `B^#` per sector | → needs formalization | (vN's deepest non-finite-`I` result; outright not in Lean) |
| Lemma 6.4.1 | `I` finite ⇔ `T` and `T_w` have one element | → needs formalization |  |
| §7.1 – 7.5 / Lemma 7.4.1 / 7.5.1 | type-`(II_1)` factor example | → needs formalization | (the type-classification work depends on having all of §5–6 above first) |

## Gap punch list (priority order for the InfiniteTensor rebuild)

1. **Blocking pending (at the API level):** a packaged
  `sectorEmbed Ω : ITPSector H Ω →ₗᵢ[ℂ] decomposableTensorProduct H`.
  The missing piece is no longer "some equivalence between sectors":
  `noncanonicalSectorEquivAny` already supplies arbitrary-family Hilbert
  equivalences, and `SectorEquivData` / `C0SectorMorphism` package
  coherent transport data.  What is still absent is a canonical wrapper
  from a bare `c0Rel` witness to the chosen representative fibre,
  ideally the phase-normalised
  `sectorEquivOfEquivalent : c0Rel Ω Ω' → ...` realising vN's
  `U(z_α)` route.

2. **Sector orthogonality (vN Theorem I + Lemma 4.1.1) at the `c0Rel` level.**
   Currently only the `c0Equiv` ℓ²-direct-sum *packaging* is available.
   The orthogonality of distinct `c0Equiv`-class subspaces inside a
   common ambient is not proved at the pure-ITP layer.

3. **Explicit ONB of `ITPSector Ω` (vN Lemma 4.1.4 / Theorem V).**
   Would give `ITPSector Ω` an `OrthonormalBasis` indexed by
   finite-support functions, mirroring the finite-case
   `regionTensorONB` (`LatticeBridge.lean`).  Needed before Lemma
   6.4.1's dimension counting can be ported.

4. **Pure-layer operator extension (vN Lemma 5.1.1 / Theorem VIII).**
   The lattice-side `localEmbedRefSector` etc. cover the
   reference-sector case but are scoped to `LocalNetLike L`.  A pure-layer
   `Ā_{α₀}` `*`-homomorphism on `ITPSector Ω` for arbitrary `Ω` is
   absent.

5. **`B^#` and Theorems IX–X.**  vN's deepest results; no Lean
   counterpart.  These are structurally absent rather than pending —
   the migration plan presumably targets the BR / Naaijkens reframing
   first.

## Design divergences (deliberate, not gaps)

**Non-separable `Π⊗` vs. separable `decomposableTensorProduct`.**
vN's Theorem V says `Π⊗_{α∈I} H_α` (over an infinite `I`, with each
`dim H_α ≥ 2`) has uncountably many `≈`-classes and is hence
non-separable.  The Lean side intentionally restricts to a **single**
`c0Equiv`-class quotient and packages those as an `ℓ²`-direct-sum.
This follows Bratteli–Robinson Vol. 2 §2.7.2 and Naaijkens 2012 §3.5;
each sector is separable, and most physical applications need only one
sector at a time.  This is **not** a formalisation gap — it is a
mathematically distinct (and easier) object.

**`strongRel ⊄ cRel`.**  The migration plan
`infinite-tensor-product.md` claimed `referenceRel ⊆ strongRel ⊆ cRel ⊆ c0Rel`.
The middle inclusion fails: the file's own counterexample (`SectorEquiv.lean`)
considers `Ω' i = exp(i · θ_i) · Ω i` with `θ_i = 1/i`:

- `Σ‖Ω i − Ω' i‖² ≍ Σ θ_i² = Σ 1/i² < ∞` so `strongRel` holds;
- `Σ|⟨Ω i, Ω' i⟩ − 1| ≍ Σ|θ_i| = Σ 1/i = ∞` so `cRel` fails.

This is **consistent with vN Lemma 3.3.4**, which says `≈` is equivalent
to `Σ‖f − g‖² < ∞` **and** `Σ|Im(f, g)| < ∞`.  The imaginary-part
summability is exactly what fails in the phase-rotation counterexample.
The Lean inclusions therefore form a non-linear DAG:
`referenceRel ⊆ strongRel ⊆ c0Rel`, `referenceRel ⊆ cRel ⊆ c0Rel`, with
no direct relation between `strongRel` and `cRel`.

**Colimit presentation vs. conjugate-linear-functional presentation of `Π'⊗`.**
vN realises `Π'⊗` (Definition 3.1.2 / 3.1.4) as conjugate-linear
functionals on `C`-sequences.  Lean realises it as a
`Module.DirectLimit` over the directed system
`{ regionTensor S | S : Finset ι }` under `regionEmbedLe`-extension.
The two are equivalent for unit-norm representatives by the universal
property of the algebraic colimit; the colimit presentation is more
mechanical to work with in Lean.

## Cross-references

- [`references/cm-1939-6-1-0/INDEX.md`](../../../references/cm-1939-6-1-0/INDEX.md)
  — ingested paper with tier-annotated key concepts (`mathlib_verified`).
- [`references/CONCEPTS.md`](../../../references/CONCEPTS.md) —
  cross-document concept index.
- `references/cm-1939-6-1-0/sections/02-on-infinite-direct-products.md` —
  full paper body with LaTeX-decoded equations.
