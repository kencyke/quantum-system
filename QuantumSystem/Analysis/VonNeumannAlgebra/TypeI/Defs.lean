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

The general **type I** property, phrased as in the literature (Takesaki V.1, Blackadar III.1.5):
every nonzero central projection dominates a nonzero abelian projection. For a *factor* this is
equivalent to the existence of a minimal projection, i.e. to `IsTypeIFactor`. The equivalence is
proved in full: the easy direction is minimal ⇒ abelian ⇒ type I; the converse is that a nonzero
abelian projection of a factor is minimal
(`IsFactor.isMinimalProjection_of_isAbelianProjection`, in
`QuantumSystem.Analysis.VonNeumannAlgebra.MinimalProjection`).

This file is the root of the type I theory: it defines the factor-level predicates `IsTypeIFactor`
and `IsTypeIInfinite` (a type I factor of infinite multiplicity), proves their invariance under
spatial and abstract `⋆`-isomorphisms, and develops the **fundamental example** `B(H)`: the
algebra of *all* bounded operators, `𝓑(H) : VonNeumannAlgebra H`, is a factor
(`isFactor_boundedLinearOperators`, in `QuantumSystem.Analysis.VonNeumannAlgebra.Factor`) and
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
* `VonNeumannAlgebra.IsTypeIFactor N` — a factor possessing a minimal projection.
* `VonNeumannAlgebra.IsTypeIInfinite N` — a type I factor carrying an infinite orthogonal family
  of minimal projections (infinite multiplicity).

## Main results

* `VonNeumannAlgebra.IsFactor.isTypeI_iff_exists_isMinimalProjection` — a factor is type I iff
  it has a minimal projection.
* `VonNeumannAlgebra.isTypeIFactor_iff_isFactor_and_isTypeI` — `IsTypeIFactor N ↔ IsFactor N ∧
  IsTypeI N`.
* `VonNeumannAlgebra.IsTypeIInfinite.exists_injective` — the witnessing minimal projections of a
  type I_∞ factor may be chosen injectively.
* `VonNeumannAlgebra.isTypeIFactor_conj_iff` — type I factors are spatially invariant.
* `VonNeumannAlgebra.isTypeIFactor_boundedLinearOperators` — `B(H)` is a type I factor.
* `VonNeumannAlgebra.exists_starAlgEquiv_boundedLinearOperators` — `B(H) ≃⋆ₐ B(ℓ²(ι))`, implemented
  as `x ↦ U x U⁻¹` by an isometry `U : H ≃ₗᵢ ℓ²(ι)`, for `ι` the index set of a Hilbert basis of `H`.
* `VonNeumannAlgebra.isTypeIInfinite_boundedLinearOperators` — for infinite-dimensional `H`, `B(H)`
  is a type I_∞ factor, packaged as the intrinsic predicate `IsTypeIInfinite 𝓑(H)`.
* `VonNeumannAlgebra.exists_starAlgEquiv_infiniteDimensional_boundedLinearOperators` — for
  infinite-dimensional `H`, the same with `ι` infinite, hence `ℓ²(ι)` infinite-dimensional.
* `VonNeumannAlgebra.isMinimalProjection_iff_of_starAlgEquiv` — through `φ : N ≃⋆ₐ B(K)` the
  minimal projections of `N` are the rank-one projections `φ⁻¹ |u⟩⟨u|`, `‖u‖ = 1`.
* `VonNeumannAlgebra.isTypeIFactor_of_starAlgEquiv` — `N ≃⋆ₐ B(K)` with `K ≠ 0` makes `N` a type I
  factor.
* `VonNeumannAlgebra.isTypeIInfinite_iff_of_starAlgEquiv` — if `N ≃⋆ₐ B(K)`, then `N` is type I_∞
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

/-- A **type I factor**: a factor possessing a minimal projection. This is the mathematically
conventional, intrinsic definition; the spatial decomposition `N ≅ B(H₁) ⊗̄ 1` is then a theorem,
not part of the definition. The equivalence with the general abelian-projection definition
`IsTypeI` is `isTypeIFactor_iff_isFactor_and_isTypeI`. -/
def IsTypeIFactor (N : VonNeumannAlgebra H) : Prop :=
  IsFactor N ∧ ∃ e : H →L[ℂ] H, IsMinimalProjection N e

/-- A factor with a minimal projection is type I: the only nonzero central projection of a factor
is `1` (`central_projection_eq`), and it dominates the minimal projection, which is abelian and
nonzero. -/
lemma IsFactor.isTypeI_of_exists_isMinimalProjection {N : VonNeumannAlgebra H}
    (hN : IsFactor N) (h : ∃ e : H →L[ℂ] H, IsMinimalProjection N e) : IsTypeI N := by
  obtain ⟨e, he⟩ := h
  have : Nontrivial H := he.nontrivial
  intro z hz hz0
  rcases hN.central_projection_eq hz with h0 | h1
  · exact absurd h0 hz0
  · exact ⟨e, he.isAbelianProjection, he.2.2.1, h1 ▸ he.1.le_one⟩

/-- **The abelian-projection characterisation of type I coincides with the minimal-projection one
on factors**: a factor is type I iff it has a minimal projection. Nontriviality of `H` is
essential for the forward direction only: on a subsingleton `H` the type I condition is vacuously
satisfied while no nonzero projection exists, so `IsTypeI N` cannot produce one. The converse
carries no such hypothesis (`isTypeI_of_exists_isMinimalProjection`) — the minimal projection it
is handed is nonzero and so supplies the nontriviality itself. -/
theorem IsFactor.isTypeI_iff_exists_isMinimalProjection [Nontrivial H] {N : VonNeumannAlgebra H}
    (hN : IsFactor N) : IsTypeI N ↔ ∃ e : H →L[ℂ] H, IsMinimalProjection N e := by
  constructor
  · intro h
    have hone : (1 : H →L[ℂ] H) ≠ 0 := by
      obtain ⟨v, hv⟩ := exists_ne (0 : H)
      intro h1
      apply hv
      have h2 := congrArg (fun T : H →L[ℂ] H => T v) h1
      simpa using h2
    obtain ⟨q, hab, hq0, -⟩ := h 1 (isCentralProjection_one N) hone
    exact ⟨q, hN.isMinimalProjection_of_isAbelianProjection hab hq0⟩
  · exact hN.isTypeI_of_exists_isMinimalProjection

/-- The factor-specialised definition `IsTypeIFactor` agrees with the conjunction of the general
abelian-projection type I property and factor-ness. `[Nontrivial H]` is load-bearing here, not
decoration: on a subsingleton `H` *every* von Neumann algebra satisfies `IsFactor N ∧ IsTypeI N`
while *none* satisfies `IsTypeIFactor N`, since a minimal projection must be nonzero. -/
lemma isTypeIFactor_iff_isFactor_and_isTypeI [Nontrivial H] {N : VonNeumannAlgebra H} :
    IsTypeIFactor N ↔ IsFactor N ∧ IsTypeI N := by
  constructor
  · rintro ⟨hf, he⟩
    exact ⟨hf, hf.isTypeI_of_exists_isMinimalProjection he⟩
  · rintro ⟨hf, ht⟩
    exact ⟨hf, hf.isTypeI_iff_exists_isMinimalProjection.mp ht⟩

/-! ### Type I_∞ factors

A **type I_∞ factor** is a type I factor of infinite multiplicity, recorded intrinsically as the
existence of an infinite orthogonal family of minimal projections. Its identification with `B(K)`
for an infinite-dimensional `K` is proved below (`isTypeIInfinite_iff_of_starAlgEquiv`) and in
`QuantumSystem.Analysis.VonNeumannAlgebra.TypeI.Classification`. -/

/-- A **type I_∞ factor**: a type I factor carrying an infinite sequence of pairwise orthogonal
minimal projections. This is the intrinsic form of *infinite multiplicity*: through the structure
theorem `N ≃⋆ₐ B(K)` (`IsTypeIFactor.exists_starAlgEquiv`) the minimal projections are the rank-one
projections (`isMinimalProjection_iff_of_starAlgEquiv`), and an infinite orthogonal family of them
exists exactly when `K` is infinite-dimensional (`isTypeIInfinite_iff_of_starAlgEquiv`) — a type
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
  refine ⟨fun ⟨hf, e, he⟩ => ⟨(isFactor_conj_iff U).mp hf, U.conjStarAlgEquiv.symm e, ?_⟩,
    fun ⟨hf, e, he⟩ => ⟨hf.conj U, _, he.conj U⟩⟩
  rw [← isMinimalProjection_conj_iff U, StarAlgEquiv.apply_symm_apply]
  exact he

/-- If `N` is a type I factor, so is `U N U⋆`. -/
lemma IsTypeIFactor.conj {N : VonNeumannAlgebra H} (hN : IsTypeIFactor N) (U : H ≃ₗᵢ[ℂ] H') :
    IsTypeIFactor (conj U N) :=
  (isTypeIFactor_conj_iff U).mpr hN

end Conj

/-! ### The fundamental example: `B(H)` is a type I factor -/

open InnerProductSpace

/-- **`B(H)` is a type I factor** (for nonzero `H`). -/
lemma isTypeIFactor_boundedLinearOperators [Nontrivial H] :
    IsTypeIFactor 𝓑(H) :=
  ⟨isFactor_boundedLinearOperators, exists_isMinimalProjection_boundedLinearOperators⟩

/-- The commutant of `B(H)` consists of scalars: it is the centre of the factor `B(H)`. -/
lemma exists_eq_smul_one_of_mem_commutant_boundedLinearOperators {x : H →L[ℂ] H}
    (hx : x ∈ (𝓑(H))′) : ∃ c : ℂ, x = c • 1 :=
  isFactor_boundedLinearOperators x (mem_boundedLinearOperators x) hx

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
projections of `B(K)` (`isMinimalProjection_iff_of_starAlgEquiv`), and `N` carries an infinite
orthogonal family of them iff `K` is infinite-dimensional (`isTypeIInfinite_iff_of_starAlgEquiv`):
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
lemma isMinimalProjection_iff_of_starAlgEquiv (φ : N ≃⋆ₐ[ℂ] (K →L[ℂ] K)) {x : N} :
    IsMinimalProjection N (x : H →L[ℂ] H) ↔ ∃ u : K, ‖u‖ = 1 ∧ φ x = rankOne ℂ u u := by
  rw [← isMinimalProjection_apply_iff φ, isMinimalProjection_boundedLinearOperators_iff]

/-- A von Neumann algebra `⋆`-isomorphic to `B(K)` is a factor: being a factor is invariant under
`⋆`-isomorphisms (`isFactor_iff_of_starAlgEquiv`) and `B(K)` is a factor
(`isFactor_boundedLinearOperators`). -/
lemma isFactor_of_starAlgEquiv (φ : N ≃⋆ₐ[ℂ] (K →L[ℂ] K)) : IsFactor N :=
  (isFactor_iff_of_starAlgEquiv (M := 𝓑(K))
    (φ.trans boundedLinearOperators.starAlgEquiv.symm)).mp isFactor_boundedLinearOperators

/-- **A von Neumann algebra `⋆`-isomorphic to `B(K)`, `K ≠ 0`, is a type I factor** — the converse
of `IsTypeIFactor.exists_starAlgEquiv`. It is a factor (`isFactor_of_starAlgEquiv`), and the
preimage of a rank-one projection of `B(K)` is a minimal projection
(`isMinimalProjection_starAlgEquiv_iff`). -/
lemma isTypeIFactor_of_starAlgEquiv [Nontrivial K] (φ : N ≃⋆ₐ[ℂ] (K →L[ℂ] K)) :
    IsTypeIFactor N :=
  let ⟨_, he⟩ := exists_isMinimalProjection_boundedLinearOperators (H := K)
  ⟨isFactor_of_starAlgEquiv φ, _, (isMinimalProjection_symm_apply_iff φ).mpr he⟩

/-- **Type I_∞ is infinite dimension of the model.** If `N ≃⋆ₐ B(K)`, then `N` is a type I_∞ factor
iff `K` is infinite-dimensional. Forward: an infinite orthogonal sequence of minimal projections of
`N` is carried to an infinite family of nonzero orthogonal idempotents of `B(K)`, which a
finite-dimensional `K` does not admit
(`ContinuousLinearMap.finite_of_orthogonalIdempotents`). Backward: an infinite-dimensional `K`
carries the rank-one projections onto an orthonormal sequence
(`isTypeIInfinite_boundedLinearOperators`), whose preimages are orthogonal minimal projections of
`N`; and `N` is a type I factor (`isTypeIFactor_of_starAlgEquiv`). -/
theorem isTypeIInfinite_iff_of_starAlgEquiv (φ : N ≃⋆ₐ[ℂ] (K →L[ℂ] K)) :
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
    refine ⟨isTypeIFactor_of_starAlgEquiv φ, fun n => φ.symm (f n),
      fun n => (isMinimalProjection_symm_apply_iff φ).mpr (hmin n), fun m n hmn => ?_⟩
    have h : φ.symm (f m) * φ.symm (f n) = 0 := by rw [← map_mul, horth m n hmn, map_zero]
    exact congrArg Subtype.val h

end TypeIInfinite

end VonNeumannAlgebra
