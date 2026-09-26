/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Algebra.VonNeumannAlgebra.MinimalProjection
public import QuantumSystem.Algebra.VonNeumannAlgebra.TypeI.StructureTheorem

/-!
# Type I von Neumann algebras

The general **type I** property, phrased as in the literature (Takesaki V.1, Blackadar III.1.5):
every nonzero central projection dominates a nonzero abelian projection. For a *factor* this is
equivalent to the existence of a minimal projection, i.e. to `IsTypeIFactor`. The equivalence is
proved in full: the easy direction is minimal ⇒ abelian ⇒ type I; the converse is that a nonzero
abelian projection of a factor is minimal
(`IsFactor.isMinimalProjection_of_isAbelianProjection`, in
`QuantumSystem.Algebra.VonNeumannAlgebra.MinimalProjection`).

This file is also the home of the factor-level type I predicates `IsTypeIFactor` and
`IsTypeIInfinite`, and of the abstract structure theorem `IsTypeIFactor.exists_starAlgEquiv`
identifying a type I factor with `B(K)` for some Hilbert space `K` (whose spatial content lives in
`QuantumSystem.Algebra.VonNeumannAlgebra.TypeI.StructureTheorem`).

Finally, the file develops the **fundamental example** `B(H)`: the algebra of *all* bounded
operators, `𝓑(H) : VonNeumannAlgebra H`, is a factor (`isFactor_boundedLinearOperators`, in
`QuantumSystem.Algebra.VonNeumannAlgebra.Basic`) and possesses a minimal projection, namely any
rank-one orthogonal projection `|u⟩⟨u|` with `‖u‖ = 1`
(`exists_isMinimalProjection_boundedLinearOperators`, in
`QuantumSystem.Algebra.VonNeumannAlgebra.MinimalProjection`). Hence
`B(H)` is a **type I factor**, and by the abstract structure theorem it is `⋆`-isomorphic to
`B(K)` for some Hilbert space `K` (which is `ℓ²` of an orthonormal basis of `H`); when `H` is
infinite-dimensional this exhibits `B(H)` as a **type I_∞ factor**.

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
* `VonNeumannAlgebra.IsTypeIFactor.exists_spatial_tensor_decomposition`,
  `VonNeumannAlgebra.IsTypeIFactor.exists_split_tensor_decomposition` — the spatial and split
  tensor decompositions of `QuantumSystem.Algebra.VonNeumannAlgebra.TypeI.StructureTheorem`, stated
  for a type I factor with the minimal projection existentially quantified.
* `VonNeumannAlgebra.IsTypeIFactor.exists_starAlgEquiv` — a type I factor is `⋆`-isomorphic to
  `B(K)` for some complex Hilbert space `K`.
* `VonNeumannAlgebra.isTypeIFactor_boundedLinearOperators` — `B(H)` is a type I factor.
* `VonNeumannAlgebra.exists_starAlgEquiv_boundedLinearOperators` — `B(H) ≃⋆ₐ B(ℓ²(ι))` with the
  implementing isometry `H ≃ₗᵢ ℓ²(ι)`, for `ι` the index set of a Hilbert basis of `H`.
* `VonNeumannAlgebra.isTypeIInfinite_boundedLinearOperators` — for infinite-dimensional `H`, `B(H)`
  is a type I_∞ factor, packaged as the intrinsic predicate `IsTypeIInfinite 𝓑(H)`.
* `VonNeumannAlgebra.exists_starAlgEquiv_infiniteDimensional_boundedLinearOperators` — for
  infinite-dimensional `H`, the same with `ι` infinite, hence `ℓ²(ι)` infinite-dimensional.

## Notation

In the prose above `B(H)` names the mathematical object — the algebra of all bounded operators —
while `𝓑(H)` is the Lean notation for it. The two are used deliberately, not interchangeably:
`𝓑(H)` resolves to `VonNeumannAlgebra.boundedLinearOperators H` (bundled von Neumann algebra) or
to `H →L[ℂ] H` (operator type) according to the expected type, an overload tabled in
`QuantumSystem.Algebra.VonNeumannAlgebra.Basic` and bridged by
`boundedLinearOperators.starAlgEquiv`.

`⊗̄` is documentation shorthand for the von Neumann (spatial) tensor product of algebras; that
convention is stated in full in `QuantumSystem.Algebra.VonNeumannAlgebra.TensorFactor`, where the
algebras it names (`HilbertTensor.vnTensorLeft` / `vnTensorRight`) are defined.
-/

@[expose] public section

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Type I von Neumann algebra**: every nonzero central projection dominates a nonzero abelian
projection. The subprojection relation `p ≤ z` is written algebraically as `z * p = p`, as
everywhere in this development. -/
def IsTypeI (N : VonNeumannAlgebra H) : Prop :=
  ∀ z : H →L[ℂ] H, IsCentralProjection N z → z ≠ 0 →
    ∃ p : H →L[ℂ] H, IsAbelianProjection N p ∧ p ≠ 0 ∧ z * p = p

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
  · exact ⟨e, he.isAbelianProjection, he.2.2.1, by rw [h1, one_mul]⟩

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
theorem isTypeIFactor_iff_isFactor_and_isTypeI [Nontrivial H] {N : VonNeumannAlgebra H} :
    IsTypeIFactor N ↔ IsFactor N ∧ IsTypeI N := by
  constructor
  · rintro ⟨hf, he⟩
    exact ⟨hf, hf.isTypeI_of_exists_isMinimalProjection he⟩
  · rintro ⟨hf, ht⟩
    exact ⟨hf, hf.isTypeI_iff_exists_isMinimalProjection.mp ht⟩

/-! ### Type I_∞ factors

A **type I_∞ factor** is a type I factor of infinite multiplicity, recorded intrinsically as the
existence of an infinite orthogonal family of minimal projections. -/

/-- A **type I_∞ factor**: a type I factor carrying an infinite sequence of pairwise orthogonal
minimal projections. This is the intrinsic form of *infinite multiplicity*: through the structure
theorem `N ≃⋆ₐ B(K)` the minimal projections are the rank-one projections, and an infinite
orthogonal family of them exists exactly when `K` is infinite-dimensional — a type `I_n` factor
`B(ℂⁿ)` has at most `n` pairwise orthogonal nonzero projections. As with `IsTypeIFactor`, the
spatial identification with an infinite-dimensional `B(K)` is then a theorem, not part of the
definition. -/
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

/-! ### Abstract structure theorem

A type I factor is `⋆`-isomorphic to `B(K)` for some Hilbert space `K`. The spatial content — the
implementing unitary and the multiplicity model `K = ℓ²(F)` — is
`IsTypeIFactor.exists_spatial_tensor_decomposition` (the `IsTypeIFactor` form of
`IsFactor.exists_spatial_tensor_decomposition` in `Algebra.VonNeumannAlgebra.TypeI.StructureTheorem`);
here it is packaged as an abstract `⋆`-isomorphism. -/

universe u

section SpatialTensor

open HilbertTensor

/-- **Spatial structure theorem for a type I factor.** A type I factor `N ⊆ B(H)` is spatially the
tensor factor `B(ℓ²(F)) ⊗̄ 1`: for some minimal projection `e` of `N` there is
`U : H ≃ₗᵢ ℓ²(F) ⊗̂ (eH)` carrying `N` onto `vnTensorLeft` and `N′` onto `vnTensorRight`. This is
the `IsTypeIFactor` form of `IsFactor.exists_spatial_tensor_decomposition`, which gives the same
for *every* minimal projection `e` of a factor. -/
theorem IsTypeIFactor.exists_spatial_tensor_decomposition {N : VonNeumannAlgebra H}
    (hN : IsTypeIFactor N) :
    ∃ e : H →L[ℂ] H, IsMinimalProjection N e ∧ ∃ (F : Set (H →L[ℂ] H))
      (U : H ≃ₗᵢ[ℂ] lp (fun _ : F => ℂ) 2 ⊗̂ LinearMap.range (e : H →ₗ[ℂ] H)),
      VonNeumannAlgebra.conj U N = vnTensorLeft ∧
      VonNeumannAlgebra.conj U N′ = vnTensorRight :=
  let ⟨hf, e, he⟩ := hN
  ⟨e, he, hf.exists_spatial_tensor_decomposition he⟩

/-- **Split tensor decomposition through a type I factor.** If a type I factor `N` interpolates an
inclusion `A ≤ N ≤ B`, then for some minimal projection `e` of `N` there is
`U : H ≃ₗᵢ ℓ²(F) ⊗̂ (eH)` identifying `N` and `N′` with the tensor factors and sending `A` into
`vnTensorLeft` and `B′` into `vnTensorRight`. This is the `IsTypeIFactor` form of
`IsFactor.exists_split_tensor_decomposition`, which gives the same for *every* minimal projection
`e` of a factor. -/
theorem IsTypeIFactor.exists_split_tensor_decomposition {N : VonNeumannAlgebra H}
    (hN : IsTypeIFactor N) {A B : VonNeumannAlgebra H} (h₁ : A ≤ N) (h₂ : N ≤ B) :
    ∃ e : H →L[ℂ] H, IsMinimalProjection N e ∧ ∃ (F : Set (H →L[ℂ] H))
      (U : H ≃ₗᵢ[ℂ] lp (fun _ : F => ℂ) 2 ⊗̂ LinearMap.range (e : H →ₗ[ℂ] H)),
      Nonempty F ∧
      VonNeumannAlgebra.conj U N = vnTensorLeft ∧
      VonNeumannAlgebra.conj U N′ = vnTensorRight ∧
      VonNeumannAlgebra.conj U A ≤ vnTensorLeft ∧
      VonNeumannAlgebra.conj U B′ ≤ vnTensorRight :=
  let ⟨hf, e, he⟩ := hN
  ⟨e, he, hf.exists_split_tensor_decomposition he h₁ h₂⟩

end SpatialTensor

/-- **Type I factor abstract structure theorem.** A type I factor `N` (a factor with a minimal
projection, acting on a nonzero Hilbert space) is `⋆`-isomorphic to the algebra `B(K)` of all
bounded operators on *some* complex Hilbert space `K`. This is the model-independent form of the
classification of type I factors: `B(K)` for `K = ℓ²(F)` is exactly the type `I_{|F|}` factor, and
`K = H` recovers the full algebra `B(H)` as the type `I` factor `𝓑(H)`. The spatial content — that the
isomorphism is implemented by a unitary and that `K` is the multiplicity space of the minimal
projection — is `IsTypeIFactor.exists_spatial_tensor_decomposition`; here it is packaged as an abstract
`⋆`-isomorphism, hiding the specific model `K = ℓ²(F)` behind an existential. -/
theorem IsTypeIFactor.exists_starAlgEquiv {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {N : VonNeumannAlgebra H}
    (hN : IsTypeIFactor N) :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (_ : CompleteSpace K),
      Nonempty (N ≃⋆ₐ[ℂ] (K →L[ℂ] K)) := by
  obtain ⟨e, he, F, U, hU, -⟩ := hN.exists_spatial_tensor_decomposition
  have : CompleteSpace (LinearMap.range (e : H →ₗ[ℂ] H)) := he.1.completeSpace_range
  have : Nontrivial (LinearMap.range (e : H →ₗ[ℂ] H)) := by
    rw [Submodule.nontrivial_iff_ne_bot, ne_eq, LinearMap.range_eq_bot]
    exact fun h => he.2.2.1 (ContinuousLinearMap.coe_injective
      (h.trans ContinuousLinearMap.toLinearMap_zero.symm))
  exact ⟨lp (fun _ : F => ℂ) 2, inferInstance, inferInstance, inferInstance,
    ⟨(conjEquiv U N).trans ((equivOfEq hU).trans HilbertTensor.amplifyLeftStarAlgEquiv.symm)⟩⟩

/-! ### The fundamental example: `B(H)` is a type I factor -/

open InnerProductSpace

/-- **`B(H)` is a type I factor** (for nonzero `H`). -/
theorem isTypeIFactor_boundedLinearOperators [Nontrivial H] :
    IsTypeIFactor 𝓑(H) :=
  ⟨isFactor_boundedLinearOperators, exists_isMinimalProjection_boundedLinearOperators⟩

/-- **`B(H) ≃⋆ₐ B(ℓ²(ι))` with `H ≃ₗᵢ ℓ²(ι)`.** The full algebra is `⋆`-isomorphic to the bounded
operators on `ℓ²(ι)` for an index set `ι` — the index set of a Hilbert basis of `H` — and the
isomorphism is implemented by the corresponding isometry `H ≃ₗᵢ ℓ²(ι)`, which is returned
alongside it.

The `ℓ²` model is stated rather than hidden behind an unconstrained `∃ K`. With `K` unconstrained
the statement would be discharged by `K := H` and `boundedLinearOperators.starAlgEquiv`,
carrying none of the classification content: the content is exactly that `K` may be taken of the
form `ℓ²(ι)`, which is what `IsTypeIFactor.exists_starAlgEquiv` hides behind its existential and
what the type `I_{|ι|}` reading of `B(H)` needs. Nonzeroness of `H` is not required: for `H = 0`
the Hilbert basis is empty and both sides are trivial. -/
theorem exists_starAlgEquiv_boundedLinearOperators {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] :
    ∃ ι : Type u, Nonempty (H ≃ₗᵢ[ℂ] lp (fun _ : ι => ℂ) 2) ∧
      Nonempty ((𝓑(H) : VonNeumannAlgebra H) ≃⋆ₐ[ℂ]
        (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2)) := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ H
  exact ⟨w, ⟨b.repr⟩, ⟨boundedLinearOperators.starAlgEquiv.trans b.repr.conjStarAlgEquiv⟩⟩

/-- **`B(H) ≃⋆ₐ B(ℓ²(ι))` with `ι` infinite, when `H` is infinite-dimensional.** The full algebra
is `⋆`-isomorphic to the bounded operators on `ℓ²(ι)` for an *infinite* index set `ι`, with the
implementing isometry `H ≃ₗᵢ ℓ²(ι)` returned alongside; in particular `ℓ²(ι)` is itself
infinite-dimensional. Expressing type I_∞ this way is the standard reading: a type I_n factor is
`B(K)` with `dim K = n`, so I_∞ is exactly the infinite index set.

As in `exists_starAlgEquiv_boundedLinearOperators`, the `ℓ²` model is part of the statement: an
unconstrained `∃ K` with `¬FiniteDimensional ℂ K` would be discharged by `K := H`. -/
theorem exists_starAlgEquiv_infiniteDimensional_boundedLinearOperators {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (hinf : ¬FiniteDimensional ℂ H) :
    ∃ ι : Type u, Infinite ι ∧ ¬FiniteDimensional ℂ (lp (fun _ : ι => ℂ) 2) ∧
      Nonempty (H ≃ₗᵢ[ℂ] lp (fun _ : ι => ℂ) 2) ∧
      Nonempty ((𝓑(H) : VonNeumannAlgebra H) ≃⋆ₐ[ℂ]
        (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2)) := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ H
  have hwinf : Infinite w := by
    rw [← not_finite_iff_infinite]
    intro hfin
    have : Finite w := hfin
    have : Fintype w := Fintype.ofFinite w
    exact hinf b.toOrthonormalBasis.toBasis.finiteDimensional_of_finite
  have hnfd : ¬FiniteDimensional ℂ (lp (fun _ : w => ℂ) 2) := by
    intro hK
    have := hK
    exact hinf b.repr.symm.toLinearEquiv.finiteDimensional
  exact ⟨w, hwinf, hnfd, ⟨b.repr⟩,
    ⟨boundedLinearOperators.starAlgEquiv.trans b.repr.conjStarAlgEquiv⟩⟩

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
  have hwinf : Infinite w := by
    rw [← not_finite_iff_infinite]
    intro hfin
    have : Finite w := hfin
    have : Fintype w := Fintype.ofFinite w
    exact hinf b.toOrthonormalBasis.toBasis.finiteDimensional_of_finite
  have := hwinf
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

end VonNeumannAlgebra
