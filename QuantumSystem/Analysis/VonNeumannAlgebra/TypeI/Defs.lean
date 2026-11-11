/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.VonNeumannAlgebra.MinimalProjection
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.l2Space
public import QuantumSystem.ForMathlib.LinearAlgebra.Dimension.OrthogonalIdempotents

/-!
# Type I von Neumann algebras and factors

The general **type I** property:
every nonzero central projection dominates a nonzero abelian projection; a type I factor
(`IsTypeIFactor`) is a factor with this property. For a factor on a nonzero Hilbert space it is
equivalent to the existence of a minimal projection. The equivalence is proved in full: the easy
direction is minimal ⇒ abelian ⇒ type I; the converse is that a nonzero
abelian projection of a factor is minimal
(`isMinimalProjection_of_isAbelianProjection_of_isCentral`, in
`QuantumSystem.Analysis.VonNeumannAlgebra.MinimalProjection`).

This file is the root of the type I theory: it defines the factor-level predicates `IsTypeIFactor`
and `IsTypeIInfinite` (a type I factor of infinite multiplicity), proves their invariance under
spatial and abstract `⋆`-isomorphisms, and develops the **fundamental example** `B(H)`: the
algebra of *all* bounded operators, `𝓑(H) : VonNeumannAlgebra H`, is a factor
(`isCentral_boundedLinearOperators`, in `QuantumSystem.Analysis.VonNeumannAlgebra.Factor`) and
possesses a minimal projection, namely any rank-one orthogonal projection `|u⟩⟨u|` with `‖u‖ = 1`
(`exists_isMinimalProjection_boundedLinearOperators`, in
`QuantumSystem.Analysis.VonNeumannAlgebra.MinimalProjection`). Hence `B(H)` is a **type I
factor**, `⋆`-isomorphic to `B(ℓ²(ι))` for `ι` the index set of a Hilbert basis of `H`; when `H` is
infinite-dimensional this exhibits `B(H)` as a **type I_∞ factor**.

The structure theorems — a type I factor is `⋆`-isomorphic to `B(K)`, spatially `B(ℓ²(F)) ⊗̄ 1`,
and the type I_∞ factors are exactly the `B(K)` with `K` infinite-dimensional — are proved in
`QuantumSystem.Analysis.VonNeumannAlgebra.TypeI.Classification` on top of
`QuantumSystem.Analysis.VonNeumannAlgebra.TypeI.StructureTheorem`.

## Main definitions

* `VonNeumannAlgebra.IsTypeI N` — every nonzero central projection of `N` dominates a nonzero
  abelian projection.
* `VonNeumannAlgebra.IsTypeIFactor N` — a factor that is type I.
* `VonNeumannAlgebra.IsTypeIInfinite N` — a type I factor carrying an infinite orthogonal family
  of minimal projections (infinite multiplicity).

## Main results

* `VonNeumannAlgebra.isTypeI_iff_exists_isMinimalProjection_of_isCentral` — on a nonzero Hilbert
  space, a factor is type I iff it has a minimal projection.
* `VonNeumannAlgebra.IsTypeIFactor.exists_isMinimalProjection`,
  `VonNeumannAlgebra.IsMinimalProjection.isTypeIFactor_of_isCentral` — on a nonzero Hilbert space, a
  type I factor is a factor with a minimal projection.
* `VonNeumannAlgebra.IsTypeIInfinite.exists_injective` — the witnessing minimal projections of a
  type I_∞ factor may be chosen injectively.
* `VonNeumannAlgebra.isTypeIFactor_conj_iff` — type I factors are spatially invariant.
* `VonNeumannAlgebra.isTypeIFactor_iff_of_starAlgEquiv`,
  `VonNeumannAlgebra.isTypeIInfinite_iff_of_starAlgEquiv` — type I and type I_∞ factors are
  invariant under `⋆`-isomorphisms `N ≃⋆ₐ M` of von Neumann algebras on possibly different spaces.
* `VonNeumannAlgebra.isTypeIFactor_boundedLinearOperators` — `B(H)` is a type I factor.
* `VonNeumannAlgebra.exists_starAlgEquiv_boundedLinearOperators` — `B(H) ≃⋆ₐ B(ℓ²(ι))`, implemented
  as `x ↦ U x U⁻¹` by an isometry `U : H ≃ₗᵢ ℓ²(ι)`, for `ι` the index set of a Hilbert basis of `H`.
* `VonNeumannAlgebra.isTypeIInfinite_boundedLinearOperators` — for infinite-dimensional `H`, `B(H)`
  is a type I_∞ factor, packaged as the intrinsic predicate `IsTypeIInfinite 𝓑(H)`.
* `VonNeumannAlgebra.exists_starAlgEquiv_infiniteDimensional_boundedLinearOperators` — for
  infinite-dimensional `H`, the same with `ι` infinite, hence `ℓ²(ι)` infinite-dimensional.
* `VonNeumannAlgebra.isMinimalProjection_iff_of_starAlgEquiv_continuousLinearMap` — through `φ : N ≃⋆ₐ B(K)` the
  minimal projections of `N` are the rank-one projections `φ⁻¹ |u⟩⟨u|`, `‖u‖ = 1`.
* `VonNeumannAlgebra.isTypeIFactor_of_starAlgEquiv_continuousLinearMap` — `N ≃⋆ₐ B(K)` makes `N` a type I factor.
* `VonNeumannAlgebra.isTypeIInfinite_iff_of_starAlgEquiv_continuousLinearMap` — if `N ≃⋆ₐ B(K)`, then `N` is type I_∞
  iff `K` is infinite-dimensional.

## Notation

In the prose above `B(H)` names the mathematical object — the algebra of all bounded operators —
while `𝓑(H)` is the Lean notation for it. The two are used deliberately, not interchangeably:
`𝓑(H)` is the bundled von Neumann algebra `VonNeumannAlgebra.boundedLinearOperators H` (notation
introduced in `QuantumSystem.Analysis.VonNeumannAlgebra.BoundedOperators`), while the operator type
is written `H →L[ℂ] H`; the two are related by the canonical `⋆`-isomorphism
`boundedLinearOperators.starAlgEquiv`.
-/

@[expose] public section

namespace VonNeumannAlgebra

open scoped lp

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Type I von Neumann algebra**: every nonzero central projection dominates a nonzero abelian
projection, `p ≤ z` in the operator order. -/
def IsTypeI (N : VonNeumannAlgebra H) : Prop :=
  ∀ z : H →L[ℂ] H, IsCentralProjection N z → z ≠ 0 →
    ∃ p : H →L[ℂ] H, IsAbelianProjection N p ∧ p ≠ 0 ∧ p ≤ z

/-- A **type I factor**: a factor that is type I. On a nonzero Hilbert space this is a factor
possessing a minimal projection (`IsTypeIFactor.exists_isMinimalProjection`,
`IsMinimalProjection.isTypeIFactor_of_isCentral`); on the zero space every von Neumann algebra is a
type I factor (`isTypeIFactor_of_subsingleton`). The spatial decomposition `N ≅ B(H₁) ⊗̄ 1` is a
theorem, not part of the definition. -/
def IsTypeIFactor (N : VonNeumannAlgebra H) : Prop :=
  Algebra.IsCentral ℂ N ∧ IsTypeI N

/-- A type I factor is a factor. -/
lemma IsTypeIFactor.isCentral {N : VonNeumannAlgebra H} (hN : IsTypeIFactor N) :
    Algebra.IsCentral ℂ N :=
  hN.1

/-- A type I factor is type I. -/
lemma IsTypeIFactor.isTypeI {N : VonNeumannAlgebra H} (hN : IsTypeIFactor N) : IsTypeI N :=
  hN.2

/-- A factor with a minimal projection is type I: the only nonzero central projection of a factor
is `1` (`IsCentralProjection.eq_zero_or_eq_one`), and it dominates the minimal
projection, which is abelian and nonzero. -/
lemma isTypeI_of_exists_isMinimalProjection_of_isCentral {N : VonNeumannAlgebra H}
    [Algebra.IsCentral ℂ N] (h : ∃ e : H →L[ℂ] H, IsMinimalProjection N e) : IsTypeI N := by
  obtain ⟨e, he⟩ := h
  have : Nontrivial H := he.nontrivial
  intro z hz hz0
  rcases hz.eq_zero_or_eq_one with h0 | h1
  · exact absurd h0 hz0
  · exact ⟨e, he.isAbelianProjection, he.2.2.1, h1 ▸ he.1.le_one⟩

/-- **The abelian-projection characterisation of type I coincides with the minimal-projection one
on factors**: a factor is type I iff it has a minimal projection. Nontriviality of `H` is
essential for the forward direction only: on a subsingleton `H` the type I condition is vacuously
satisfied while no nonzero projection exists, so `IsTypeI N` cannot produce one. The converse
carries no such hypothesis (`isTypeI_of_exists_isMinimalProjection_of_isCentral`) — the minimal projection it
is handed is nonzero and so supplies the nontriviality itself. -/
theorem isTypeI_iff_exists_isMinimalProjection_of_isCentral [Nontrivial H] {N : VonNeumannAlgebra H}
    [Algebra.IsCentral ℂ N] : IsTypeI N ↔ ∃ e : H →L[ℂ] H, IsMinimalProjection N e := by
  constructor
  · intro h
    have hone : (1 : H →L[ℂ] H) ≠ 0 := by
      obtain ⟨v, hv⟩ := exists_ne (0 : H)
      intro h1
      apply hv
      have h2 := congrArg (fun T : H →L[ℂ] H => T v) h1
      simpa using h2
    obtain ⟨q, hab, hq0, -⟩ := h 1 (IsCentralProjection.one N) hone
    exact ⟨q, isMinimalProjection_of_isAbelianProjection_of_isCentral hab hq0⟩
  · exact isTypeI_of_exists_isMinimalProjection_of_isCentral

/-- A factor with a minimal projection is a type I factor. -/
lemma IsMinimalProjection.isTypeIFactor_of_isCentral {N : VonNeumannAlgebra H}
    [h : Algebra.IsCentral ℂ N] {e : H →L[ℂ] H} (he : IsMinimalProjection N e) : IsTypeIFactor N :=
  ⟨h, isTypeI_of_exists_isMinimalProjection_of_isCentral ⟨e, he⟩⟩

/-- A type I factor on a nonzero Hilbert space has a minimal projection. -/
lemma IsTypeIFactor.exists_isMinimalProjection [Nontrivial H] {N : VonNeumannAlgebra H}
    (hN : IsTypeIFactor N) : ∃ e : H →L[ℂ] H, IsMinimalProjection N e :=
  have := hN.isCentral
  isTypeI_iff_exists_isMinimalProjection_of_isCentral.mp hN.isTypeI

/-- On the zero Hilbert space every von Neumann algebra is type I: it has no nonzero central
projection. -/
lemma isTypeI_of_subsingleton [Subsingleton H] (N : VonNeumannAlgebra H) : IsTypeI N :=
  fun z _ hz => absurd (Subsingleton.elim z 0) hz

/-- On the zero Hilbert space every von Neumann algebra is a type I factor. -/
lemma isTypeIFactor_of_subsingleton [Subsingleton H] (N : VonNeumannAlgebra H) :
    IsTypeIFactor N :=
  ⟨isCentral_of_subsingleton N, isTypeI_of_subsingleton N⟩

/-! ### Type I_∞ factors

A **type I_∞ factor** is a type I factor of infinite multiplicity, recorded intrinsically as the
existence of an infinite orthogonal family of minimal projections. Its identification with `B(K)`
for an infinite-dimensional `K` is proved below (`isTypeIInfinite_iff_of_starAlgEquiv_continuousLinearMap`) and in
`QuantumSystem.Analysis.VonNeumannAlgebra.TypeI.Classification`. -/

/-- A **type I_∞ factor**: a type I factor carrying an infinite sequence of pairwise orthogonal
minimal projections. This is the intrinsic form of *infinite multiplicity*: through the structure
theorem `N ≃⋆ₐ B(K)` (`IsTypeIFactor.exists_starAlgEquiv`) the minimal projections are the rank-one
projections (`isMinimalProjection_iff_of_starAlgEquiv_continuousLinearMap`), and an infinite orthogonal family of them
exists exactly when `K` is infinite-dimensional (`isTypeIInfinite_iff_of_starAlgEquiv_continuousLinearMap`) — a type
`I_n` factor `B(ℂⁿ)` has at most `n` pairwise orthogonal nonzero projections
(`ContinuousLinearMap.natCard_le_finrank_of_orthogonalIdempotents`). As with `IsTypeIFactor`, the
spatial identification with an infinite-dimensional `B(K)` is then a theorem, not part of the
definition: abstractly `IsTypeIInfinite.exists_starAlgEquiv`, with converse
`isTypeIInfinite_iff_exists_starAlgEquiv`, and spatially
`IsTypeIInfinite.exists_spatial_tensor_decomposition` — `N` is `B(ℓ²(F)) ⊗̄ 1` for an infinite
covering family `F` (`OrthEquivFam.isTypeIInfinite_iff_infinite`). -/
def IsTypeIInfinite (N : VonNeumannAlgebra H) : Prop :=
  IsTypeIFactor N ∧
    ∃ e : ℕ → (H →L[ℂ] H),
      (∀ n, IsMinimalProjection N (e n)) ∧
      (∀ m n, m ≠ n → e m * e n = 0)

/-- An orthogonal sequence of minimal projections is injective. -/
lemma injective_of_isMinimalProjection_orthogonal {N : VonNeumannAlgebra H}
    {e : ℕ → (H →L[ℂ] H)} (hmin : ∀ n, IsMinimalProjection N (e n))
    (horth : ∀ m n, m ≠ n → e m * e n = 0) : Function.Injective e := by
  intro m n hmn
  by_contra hne
  have h0 := horth m n hne
  rw [hmn, (hmin n).1.isIdempotentElem] at h0
  exact (hmin n).2.2.1 h0

/-- The witnessing minimal projections of a type I_∞ factor may be chosen injectively. -/
lemma IsTypeIInfinite.exists_injective {N : VonNeumannAlgebra H} (hN : IsTypeIInfinite N) :
    ∃ e : ℕ → (H →L[ℂ] H), Function.Injective e ∧
      (∀ n, IsMinimalProjection N (e n)) ∧
      (∀ m n, m ≠ n → e m * e n = 0) := by
  obtain ⟨-, e, hmin, horth⟩ := hN
  exact ⟨e, injective_of_isMinimalProjection_orthogonal hmin horth, hmin, horth⟩

/-- A type I_∞ factor is in particular a type I factor. -/
lemma IsTypeIInfinite.isTypeIFactor {N : VonNeumannAlgebra H} (hN : IsTypeIInfinite N) :
    IsTypeIFactor N := hN.1

universe u

/-- The range of a minimal projection is a nonzero subspace, the projection being nonzero. -/
lemma IsMinimalProjection.nontrivial_range {N : VonNeumannAlgebra H} {e : H →L[ℂ] H}
    (he : IsMinimalProjection N e) : Nontrivial (e.range) := by
  rw [Submodule.nontrivial_iff_ne_bot, ne_eq, LinearMap.range_eq_bot]
  exact fun h => he.2.2.1 (ContinuousLinearMap.coe_injective
    (h.trans ContinuousLinearMap.toLinearMap_zero.symm))

section Conj

variable {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']

/-- **Type I factors are spatially invariant**: `U N U⋆` is a type I factor iff `N` is. -/
lemma isTypeIFactor_conj_iff {N : VonNeumannAlgebra H} (U : H ≃ₗᵢ[ℂ] H') :
    IsTypeIFactor (conj U N) ↔ IsTypeIFactor N := by
  rcases subsingleton_or_nontrivial H with _ | _
  · have : Subsingleton H' := U.symm.toLinearEquiv.toEquiv.subsingleton
    exact iff_of_true (isTypeIFactor_of_subsingleton _) (isTypeIFactor_of_subsingleton _)
  have : Nontrivial H' := U.symm.toLinearEquiv.toEquiv.nontrivial
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨e, he⟩ := h.exists_isMinimalProjection
    have := (isCentral_conj_iff U).mp h.isCentral
    refine IsMinimalProjection.isTypeIFactor_of_isCentral (e := U.conjStarAlgEquiv.symm e) ?_
    rw [← isMinimalProjection_conj_iff U, StarAlgEquiv.apply_symm_apply]
    exact he
  · obtain ⟨e, he⟩ := h.exists_isMinimalProjection
    have := h.isCentral
    exact (he.conj U).isTypeIFactor_of_isCentral

/-- If `N` is a type I factor, so is `U N U⋆`. -/
lemma IsTypeIFactor.conj {N : VonNeumannAlgebra H} (hN : IsTypeIFactor N) (U : H ≃ₗᵢ[ℂ] H') :
    IsTypeIFactor (conj U N) :=
  (isTypeIFactor_conj_iff U).mpr hN

end Conj

section StarAlgEquiv

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {N : VonNeumannAlgebra H} {M : VonNeumannAlgebra K}

/-- A von Neumann algebra on `H` is trivial only on the zero space: `1 = 0` in it forces `H = 0`. -/
private lemma subsingleton_of_subsingleton {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {A : VonNeumannAlgebra E} [Subsingleton A] : Subsingleton E := by
  have h : ((1 : A) : E →L[ℂ] E) = ((0 : A) : E →L[ℂ] E) :=
    congrArg Subtype.val (Subsingleton.elim _ _)
  exact ⟨fun x y => sub_eq_zero.mp (by simpa using congrArg (fun T : E →L[ℂ] E => T (x - y)) h)⟩

/-- A `⋆`-isomorphism `N ≃⋆ₐ M` of von Neumann algebras on a nonzero `K` forces `H ≠ 0`: on the
zero space `N`, hence `M`, is trivial, so `K = 0`. -/
private lemma nontrivial_of_starAlgEquiv [Nontrivial K] (φ : N ≃⋆ₐ[ℂ] M) : Nontrivial H := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have : Subsingleton N := ⟨fun a b => Subtype.ext (ContinuousLinearMap.ext fun _ => Subsingleton.elim _ _)⟩
  have : Subsingleton M := φ.symm.toEquiv.subsingleton
  exact not_subsingleton K (subsingleton_of_subsingleton (A := M))

/-- **Type I factors are invariant under `⋆`-isomorphisms**: if `N` is a type I factor and
`φ : N ≃⋆ₐ M`, so is `M`. Being a factor is carried by `Algebra.IsCentral.of_algEquiv'`, and a
minimal projection of `N` by `IsMinimalProjection.map_starAlgEquiv`. -/
lemma IsTypeIFactor.of_starAlgEquiv (hN : IsTypeIFactor N) (φ : N ≃⋆ₐ[ℂ] M) : IsTypeIFactor M := by
  rcases subsingleton_or_nontrivial K with _ | _
  · exact isTypeIFactor_of_subsingleton M
  have := nontrivial_of_starAlgEquiv φ
  obtain ⟨e, he⟩ := hN.exists_isMinimalProjection
  have := hN.isCentral
  have : Algebra.IsCentral ℂ M := .of_algEquiv' φ.toAlgEquiv
  exact (IsMinimalProjection.map_starAlgEquiv (x := ⟨e, he.2.1⟩) he φ).isTypeIFactor_of_isCentral

/-- Two `⋆`-isomorphic von Neumann algebras are type I factors together. -/
lemma isTypeIFactor_iff_of_starAlgEquiv (φ : N ≃⋆ₐ[ℂ] M) : IsTypeIFactor N ↔ IsTypeIFactor M :=
  ⟨fun h => h.of_starAlgEquiv φ, fun h => h.of_starAlgEquiv φ.symm⟩

/-- **Type I_∞ factors are invariant under `⋆`-isomorphisms**: `φ : N ≃⋆ₐ M` carries an orthogonal
sequence of minimal projections of `N` to one of `M`. -/
lemma IsTypeIInfinite.of_starAlgEquiv (hN : IsTypeIInfinite N) (φ : N ≃⋆ₐ[ℂ] M) :
    IsTypeIInfinite M := by
  obtain ⟨hI, e, hmin, horth⟩ := hN
  let x : ℕ → N := fun n => ⟨e n, (hmin n).2.1⟩
  refine ⟨hI.of_starAlgEquiv φ, fun n => φ (x n),
    fun n => IsMinimalProjection.map_starAlgEquiv (x := x n) (hmin n) φ, fun m n hmn => ?_⟩
  have h : φ (x m) * φ (x n) = 0 := by
    rw [← map_mul, show x m * x n = 0 from Subtype.ext (horth m n hmn), map_zero]
  exact congrArg Subtype.val h

/-- Two `⋆`-isomorphic von Neumann algebras are type I_∞ factors together. -/
lemma isTypeIInfinite_iff_of_starAlgEquiv (φ : N ≃⋆ₐ[ℂ] M) : IsTypeIInfinite N ↔ IsTypeIInfinite M :=
  ⟨fun h => h.of_starAlgEquiv φ, fun h => h.of_starAlgEquiv φ.symm⟩

end StarAlgEquiv

/-! ### The fundamental example: `B(H)` is a type I factor -/

open InnerProductSpace

/-- **`B(H)` is a type I factor**: for nonzero `H` a rank-one projection is minimal. -/
lemma isTypeIFactor_boundedLinearOperators : IsTypeIFactor 𝓑(H) := by
  rcases subsingleton_or_nontrivial H with _ | _
  · exact isTypeIFactor_of_subsingleton _
  obtain ⟨_, he⟩ := exists_isMinimalProjection_boundedLinearOperators (H := H)
  exact he.isTypeIFactor_of_isCentral

/-- **`B(H) ≃⋆ₐ B(ℓ²(ι))`, implemented by `U : H ≃ₗᵢ ℓ²(ι)`.** The full algebra is `⋆`-isomorphic
to the bounded operators on `ℓ²(ι)` for an index set `ι` — the index set of a Hilbert basis of
`H` — and the isomorphism is spatial: it is `x ↦ U x U⁻¹` for the corresponding isometry
`U : H ≃ₗᵢ ℓ²(ι)`, which is returned alongside it.

The `ℓ²` model is stated rather than hidden behind an unconstrained `∃ K`. With `K` unconstrained
the statement would be discharged by `K := H` and `boundedLinearOperators.starAlgEquiv`,
carrying none of the classification content: the content is exactly that `K` may be taken of the
form `ℓ²(ι)`, which is what `IsTypeIFactor.exists_starAlgEquiv` hides behind its existential and
what the type `I_{|ι|}` reading of `B(H)` needs. Nonzeroness of `H` is not required: for `H = 0`
the Hilbert basis is empty and both sides are trivial. -/
lemma exists_starAlgEquiv_boundedLinearOperators {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] :
    ∃ (ι : Type u) (U : H ≃ₗᵢ[ℂ] ℓ²(ι, ℂ))
      (e : (𝓑(H) : VonNeumannAlgebra H) ≃⋆ₐ[ℂ] (ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ))),
      ∀ (x : (𝓑(H) : VonNeumannAlgebra H)) (v : ℓ²(ι, ℂ)),
        e x v = U ((x : H →L[ℂ] H) (U.symm v)) := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ H
  exact ⟨w, b.repr, boundedLinearOperators.starAlgEquiv.trans b.repr.conjStarAlgEquiv,
    fun _ _ => rfl⟩

/-- **`B(H) ≃⋆ₐ B(ℓ²(ι))` with `ι` infinite, when `H` is infinite-dimensional.** The full algebra
is `⋆`-isomorphic to the bounded operators on `ℓ²(ι)` for an *infinite* index set `ι`, by
`x ↦ U x U⁻¹` for an isometry `U : H ≃ₗᵢ ℓ²(ι)` returned alongside; in particular `ℓ²(ι)` is itself
infinite-dimensional. Expressing type I_∞ this way is the standard reading: a type I_n factor is
`B(K)` with `dim K = n`, so I_∞ is exactly the infinite index set.

As in `exists_starAlgEquiv_boundedLinearOperators`, the `ℓ²` model is part of the statement: an
unconstrained `∃ K` with `¬FiniteDimensional ℂ K` would be discharged by `K := H`. -/
lemma exists_starAlgEquiv_infiniteDimensional_boundedLinearOperators {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (hinf : ¬FiniteDimensional ℂ H) :
    ∃ ι : Type u, Infinite ι ∧ ¬FiniteDimensional ℂ (ℓ²(ι, ℂ)) ∧
      ∃ (U : H ≃ₗᵢ[ℂ] ℓ²(ι, ℂ))
        (e : (𝓑(H) : VonNeumannAlgebra H) ≃⋆ₐ[ℂ] (ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ))),
        ∀ (x : (𝓑(H) : VonNeumannAlgebra H)) (v : ℓ²(ι, ℂ)),
          e x v = U ((x : H →L[ℂ] H) (U.symm v)) := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ H
  have hwinf : Infinite w := by rwa [← not_finite_iff_infinite, ← b.finiteDimensional_iff_finite]
  exact ⟨w, hwinf, by rwa [lp.finiteDimensional_iff_finite, not_finite_iff_infinite], b.repr,
    boundedLinearOperators.starAlgEquiv.trans b.repr.conjStarAlgEquiv, fun _ _ => rfl⟩

/-- **`B(H)` is a type I_∞ factor when `H` is infinite-dimensional.** Packaged as the intrinsic
predicate `IsTypeIInfinite`: `𝓑(H) = B(H)` is a type I factor (`isTypeIFactor_boundedLinearOperators`)
carrying an infinite orthogonal family of minimal projections — the rank-one projections
`|uₙ⟩⟨uₙ|` onto a countable orthonormal sequence `(uₙ)` extracted from a Hilbert basis of the
infinite-dimensional `H`. The `⋆`-isomorphism to an infinite-dimensional `B(K)` is
`exists_starAlgEquiv_infiniteDimensional_boundedLinearOperators`. -/
theorem isTypeIInfinite_boundedLinearOperators {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (hinf : ¬FiniteDimensional ℂ H) :
    IsTypeIInfinite 𝓑(H) := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ H
  have : Infinite w := by rwa [← not_finite_iff_infinite, ← b.finiteDimensional_iff_finite]
  let g : ℕ ↪ w := Infinite.natEmbedding w
  set u : ℕ → H := fun n => b (g n) with hu_def
  have hon : Orthonormal ℂ u := by
    rw [hu_def]; exact b.orthonormal.comp g g.injective
  have hnorm : ∀ n, ‖u n‖ = 1 := fun n => hon.1 n
  have hmin : ∀ n, IsMinimalProjection 𝓑(H) (rankOne ℂ (u n) (u n)) :=
    fun n => isMinimalProjection_rankOne_boundedLinearOperators (hnorm n)
  have horth : ∀ m n, m ≠ n → rankOne ℂ (u m) (u m) * rankOne ℂ (u n) (u n) = 0 := by
    intro m n hmn
    rw [ContinuousLinearMap.mul_def, rankOne_comp_rankOne, hon.2 hmn, zero_smul]
  have : Nontrivial H :=
    nontrivial_of_ne (u 0) 0 (by rw [← norm_ne_zero_iff, hnorm 0]; norm_num)
  exact ⟨isTypeIFactor_boundedLinearOperators, fun n => rankOne ℂ (u n) (u n), hmin, horth⟩

/-! ### Minimal projections and multiplicity through `N ≃⋆ₐ B(K)`

Through a `⋆`-isomorphism `φ : N ≃⋆ₐ B(K)` the minimal projections of `N` are the rank-one
projections of `B(K)` (`isMinimalProjection_iff_of_starAlgEquiv_continuousLinearMap`), and `N` carries an infinite
orthogonal family of them iff `K` is infinite-dimensional (`isTypeIInfinite_iff_of_starAlgEquiv_continuousLinearMap`):
on a finite-dimensional `K` a family of nonzero orthogonal projections has at most `dim K` members
(`ContinuousLinearMap.natCard_le_finrank_of_orthogonalIdempotents`), while an infinite-dimensional
`K` carries the rank-one projections onto an orthonormal sequence
(`isTypeIInfinite_boundedLinearOperators`). -/

section TypeIInfinite

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {N : VonNeumannAlgebra H}

/-- Minimality transported along a `⋆`-isomorphism onto the operator type `K →L[ℂ] K`, which
lands in `𝓑(K)` after composing with `boundedLinearOperators.starAlgEquiv.symm`. -/
private lemma isMinimalProjection_apply_iff (φ : N ≃⋆ₐ[ℂ] (K →L[ℂ] K)) {x : N} :
    IsMinimalProjection 𝓑(K) (φ x) ↔ IsMinimalProjection N (x : H →L[ℂ] H) :=
  isMinimalProjection_starAlgEquiv_iff (M := 𝓑(K))
    (φ.trans boundedLinearOperators.starAlgEquiv.symm)

/-- The preimage form of `isMinimalProjection_apply_iff`. -/
private lemma isMinimalProjection_symm_apply_iff (φ : N ≃⋆ₐ[ℂ] (K →L[ℂ] K)) {y : K →L[ℂ] K} :
    IsMinimalProjection N (φ.symm y : H →L[ℂ] H) ↔ IsMinimalProjection 𝓑(K) y := by
  rw [← isMinimalProjection_apply_iff φ, StarAlgEquiv.apply_symm_apply]

/-- **Through `N ≃⋆ₐ B(K)` the minimal projections are the rank-one projections.** For a
`⋆`-isomorphism `φ : N ≃⋆ₐ B(K)`, an element `x ∈ N` is a minimal projection iff `φ x = |u⟩⟨u|`
for a unit vector `u ∈ K`: minimality is invariant under `⋆`-isomorphisms
(`isMinimalProjection_starAlgEquiv_iff`), and the minimal projections of `B(K)` are the rank-one
projections (`isMinimalProjection_boundedLinearOperators_iff`). -/
lemma isMinimalProjection_iff_of_starAlgEquiv_continuousLinearMap (φ : N ≃⋆ₐ[ℂ] (K →L[ℂ] K)) {x : N} :
    IsMinimalProjection N (x : H →L[ℂ] H) ↔ ∃ u : K, ‖u‖ = 1 ∧ φ x = rankOne ℂ u u := by
  rw [← isMinimalProjection_apply_iff φ, isMinimalProjection_boundedLinearOperators_iff]

/-- **A von Neumann algebra `⋆`-isomorphic to `B(K)` is a type I factor** — the converse of
`IsTypeIFactor.exists_starAlgEquiv`. It is a factor, as `B(K)` is (`Algebra.IsCentral.of_algEquiv'`), and
the preimage of a rank-one projection of `B(K)` is a minimal projection
(`isMinimalProjection_starAlgEquiv_iff`); for `K = 0` the algebra `N` is zero, so `1 = 0` on `H`
and `H` is the zero space (`isTypeIFactor_of_subsingleton`). -/
lemma isTypeIFactor_of_starAlgEquiv_continuousLinearMap (φ : N ≃⋆ₐ[ℂ] (K →L[ℂ] K)) : IsTypeIFactor N := by
  rcases subsingleton_or_nontrivial K with _ | _
  · have : Subsingleton N := φ.toEquiv.subsingleton
    have h : ((1 : N) : H →L[ℂ] H) = ((0 : N) : H →L[ℂ] H) :=
      congrArg Subtype.val (Subsingleton.elim _ _)
    have : Subsingleton H :=
      ⟨fun x y => sub_eq_zero.mp (by simpa using congrArg (fun T : H →L[ℂ] H => T (x - y)) h)⟩
    exact isTypeIFactor_of_subsingleton N
  obtain ⟨_, he⟩ := exists_isMinimalProjection_boundedLinearOperators (H := K)
  have : Algebra.IsCentral ℂ N := .of_algEquiv' φ.toAlgEquiv.symm
  exact ((isMinimalProjection_symm_apply_iff φ).mpr he).isTypeIFactor_of_isCentral

/-- **Type I_∞ is infinite dimension of the model.** If `N ≃⋆ₐ B(K)`, then `N` is a type I_∞ factor
iff `K` is infinite-dimensional. Forward: an infinite orthogonal sequence of minimal projections of
`N` is carried to an infinite family of nonzero orthogonal idempotents of `B(K)`, which a
finite-dimensional `K` does not admit
(`ContinuousLinearMap.finite_of_orthogonalIdempotents`). Backward: an infinite-dimensional `K`
carries the rank-one projections onto an orthonormal sequence
(`isTypeIInfinite_boundedLinearOperators`), whose preimages are orthogonal minimal projections of
`N`; and `N` is a type I factor (`isTypeIFactor_of_starAlgEquiv_continuousLinearMap`). -/
theorem isTypeIInfinite_iff_of_starAlgEquiv_continuousLinearMap (φ : N ≃⋆ₐ[ℂ] (K →L[ℂ] K)) :
    IsTypeIInfinite N ↔ ¬FiniteDimensional ℂ K := by
  constructor
  · rintro ⟨-, e, hmin, horth⟩ _
    let x : ℕ → N := fun n => ⟨e n, (hmin n).2.1⟩
    have hmin' : ∀ n, IsMinimalProjection 𝓑(K) (φ (x n)) := fun n =>
      (isMinimalProjection_apply_iff φ).mpr (hmin n)
    have hp : OrthogonalIdempotents fun n => φ (x n) :=
      ⟨fun n => (hmin' n).1.isIdempotentElem, fun m n hmn => show φ (x m) * φ (x n) = 0 by
        rw [← map_mul, show x m * x n = 0 from Subtype.ext (horth m n hmn), map_zero]⟩
    exact not_finite_iff_infinite.mpr (inferInstance : Infinite ℕ)
      (ContinuousLinearMap.finite_of_orthogonalIdempotents hp fun n => (hmin' n).2.2.1)
  · intro hK
    have : Nontrivial K := by
      by_contra h
      rw [not_nontrivial_iff_subsingleton] at h
      exact hK inferInstance
    obtain ⟨-, f, hmin, horth⟩ := isTypeIInfinite_boundedLinearOperators hK
    refine ⟨isTypeIFactor_of_starAlgEquiv_continuousLinearMap φ, fun n => φ.symm (f n),
      fun n => (isMinimalProjection_symm_apply_iff φ).mpr (hmin n), fun m n hmn => ?_⟩
    have h : φ.symm (f m) * φ.symm (f n) = 0 := by rw [← map_mul, horth m n hmn, map_zero]
    exact congrArg Subtype.val h

end TypeIInfinite

end VonNeumannAlgebra
