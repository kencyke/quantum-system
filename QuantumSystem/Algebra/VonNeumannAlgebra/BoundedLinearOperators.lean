module

public import QuantumSystem.Algebra.VonNeumannAlgebra.TensorIdentification
public import QuantumSystem.Algebra.VonNeumannAlgebra.TypeI
public import Mathlib.Analysis.VonNeumannAlgebra.Basic

/-!
# The algebra of all bounded operators is a type I factor

The algebra `B(H) = H →L[ℂ] H` of *all* bounded operators is realised as the greatest von Neumann
algebra `⊤ : VonNeumannAlgebra H`. The von Neumann subalgebras of `B(H)` form a bounded lattice
under inclusion, whose greatest element is `B(H)` itself; Mathlib's `VonNeumannAlgebra H` carries no
`Top` instance, so this file first supplies one (carrier `Set.univ`, double-commutant law from
`Set.subset_centralizer_centralizer` together with `Set.subset_univ`) before developing the factor
theory.

This `⊤` is a factor: its centre is the scalars, by the elementary fact
that an operator commuting with every rank-one operator is scalar. It possesses a minimal
projection, namely any rank-one orthogonal projection `|u⟩⟨u|` with `‖u‖ = 1`. Hence `B(H)` is a
**type I factor**, and by the abstract structure theorem `IsTypeIFactor.exists_starAlgEquiv` it is
`⋆`-isomorphic to `B(K)` for some Hilbert space `K` (which is `ℓ²` of an orthonormal basis of `H`);
when `H` is infinite-dimensional this exhibits `B(H)` as a **type I_∞ factor**.

## Main results

* `Top (VonNeumannAlgebra H)` — the greatest element `⊤`, the algebra of all bounded operators, with
  carrier `Set.univ` (`VonNeumannAlgebra.coe_top` / `VonNeumannAlgebra.mem_top`).
* `VonNeumannAlgebra.isFactor_boundedLinearOperators` — `B(H)` is a factor.
* `VonNeumannAlgebra.exists_isMinimalProjection_boundedLinearOperators` — `B(H)` has a minimal
  projection (rank-one).
* `VonNeumannAlgebra.isTypeIFactor_boundedLinearOperators` — `B(H)` is a type I factor.
* `VonNeumannAlgebra.exists_starAlgEquiv_boundedLinearOperators` — `B(H) ≃⋆ₐ B(K)` for some
  Hilbert space `K`.
* `VonNeumannAlgebra.isTypeIInfinite_boundedLinearOperators` — for infinite-dimensional `H`, `B(H)`
  is a type I_∞ factor, packaged as the intrinsic predicate `IsTypeIInfinite ⊤`.
* `VonNeumannAlgebra.exists_starAlgEquiv_infiniteDimensional_boundedLinearOperators` — for
  infinite-dimensional `H`, `B(H) ≃⋆ₐ B(K)` with `K` itself infinite-dimensional.
-/

@[expose] public section

namespace VonNeumannAlgebra

open InnerProductSpace

universe u

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The **algebra of all bounded operators** `B(H) = H →L[ℂ] H`, as the greatest element `⊤` of the
inclusion order on `VonNeumannAlgebra H`. Its carrier is `Set.univ`; the double-commutant property is
the bicommutant inclusion `s ⊆ s''` applied to `s = univ`, together with `univ` being the largest
set. -/
noncomputable instance : Top (VonNeumannAlgebra H) where
  top :=
    { toStarSubalgebra := ⊤
      centralizer_centralizer' :=
        Set.Subset.antisymm (Set.subset_univ _) Set.subset_centralizer_centralizer }

@[simp] lemma coe_top : ((⊤ : VonNeumannAlgebra H) : Set (H →L[ℂ] H)) = Set.univ := rfl

/-- Every bounded operator lies in the full algebra `⊤ = B(H)`. -/
@[simp] lemma mem_top (x : H →L[ℂ] H) : x ∈ (⊤ : VonNeumannAlgebra H) := Set.mem_univ x

/-- **`B(H)` is a factor.** The centre of the full algebra is trivial: an operator lying in the
commutant of `⊤` commutes with every operator, in particular with every rank-one operator, hence is
a scalar (`ContinuousLinearMap.exists_eq_smul_one_of_forall_rankOne_comm`). -/
theorem isFactor_boundedLinearOperators : IsFactor (⊤ : VonNeumannAlgebra H) := by
  intro x _ hxComm
  rw [VonNeumannAlgebra.mem_commutant_iff] at hxComm
  refine ContinuousLinearMap.exists_eq_smul_one_of_forall_rankOne_comm (fun a b => ?_)
  have hg := hxComm (rankOne ℂ a b) (mem_top _)
  rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def] at hg
  exact hg.symm

/-- **A rank-one projection is minimal in `B(H)`.** For a unit vector `u`, the rank-one orthogonal
projection `|u⟩⟨u|` is a minimal projection of `⊤`: it is a star projection, nonzero, and its corner
is trivial because `|u⟩⟨u| ∘ a ∘ |u⟩⟨u| = ⟪u, a u⟫ • |u⟩⟨u|`. -/
lemma isMinimalProjection_rankOne_boundedLinearOperators {u : H} (hu : ‖u‖ = 1) :
    IsMinimalProjection (⊤ : VonNeumannAlgebra H) (rankOne ℂ u u) := by
  have hu_ne : u ≠ 0 := by rw [← norm_pos_iff, hu]; norm_num
  refine ⟨⟨isIdempotentElem_rankOne_self hu, ?_⟩, mem_top _,
    rankOne_ne_zero hu_ne hu_ne, fun a _ => ?_⟩
  · rw [isSelfAdjoint_iff, ContinuousLinearMap.star_eq_adjoint, adjoint_rankOne]
  · exact ⟨inner ℂ u (a u), by
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.comp_assoc, comp_rankOne, rankOne_comp_rankOne]⟩

omit [CompleteSpace H] in
/-- A normalised nonzero vector of a nontrivial space, packaged as a unit vector. -/
private theorem exists_unit_vector [Nontrivial H] : ∃ u : H, ‖u‖ = 1 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  exact ⟨(‖v‖⁻¹ : ℂ) • v, by
    rw [norm_smul, norm_inv, Complex.norm_real, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]⟩

/-- **`B(H)` has a minimal projection** (a rank-one projection). Needs `H` nonzero. -/
theorem exists_isMinimalProjection_boundedLinearOperators [Nontrivial H] :
    ∃ e : H →L[ℂ] H, IsMinimalProjection (⊤ : VonNeumannAlgebra H) e :=
  let ⟨u, hu⟩ := exists_unit_vector (H := H)
  ⟨rankOne ℂ u u, isMinimalProjection_rankOne_boundedLinearOperators hu⟩

/-- **`B(H)` is a type I factor** (for nonzero `H`). -/
theorem isTypeIFactor_boundedLinearOperators [Nontrivial H] :
    IsTypeIFactor (⊤ : VonNeumannAlgebra H) :=
  ⟨isFactor_boundedLinearOperators, exists_isMinimalProjection_boundedLinearOperators⟩

/-- **`B(H)` is `⋆`-isomorphic to `B(K)`** for some complex Hilbert space `K`. This applies the
abstract type I factor structure theorem `IsTypeIFactor.exists_starAlgEquiv` to the full algebra;
`K` is `ℓ²` of an orthonormal basis of `H`. -/
theorem exists_starAlgEquiv_boundedLinearOperators {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H] :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (_ : CompleteSpace K),
      Nonempty ((⊤ : VonNeumannAlgebra H) ≃⋆ₐ[ℂ] (K →L[ℂ] K)) :=
  isTypeIFactor_boundedLinearOperators.exists_starAlgEquiv

/-- **`B(H) ≃⋆ₐ B(K)` with `K` infinite-dimensional, when `H` is infinite-dimensional.** The full
algebra is `⋆`-isomorphic to `B(K)` for a complex Hilbert space `K` that is itself
infinite-dimensional. Here `K = ℓ²(F)` for `F` an orthonormal basis of `H`; a finite `F` would,
through the spatial decomposition `H ≃ₗᵢ ℓ²(F) ⊗̂ (eH)` with one-dimensional multiplicity `eH` (the
range of the rank-one minimal projection), force `H` finite-dimensional. Expressing type I_∞ as
`¬FiniteDimensional ℂ K` is the standard reading: a type I_n factor is `B(K)` with `dim K = n`, so
I_∞ is exactly the infinite-dimensional `K`. -/
theorem exists_starAlgEquiv_infiniteDimensional_boundedLinearOperators {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (hinf : ¬FiniteDimensional ℂ H) :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (_ : CompleteSpace K),
      ¬FiniteDimensional ℂ K ∧
      Nonempty ((⊤ : VonNeumannAlgebra H) ≃⋆ₐ[ℂ] (K →L[ℂ] K)) := by
  haveI : Nontrivial H := by
    rcases subsingleton_or_nontrivial H with h | h
    · haveI := h
      exact absurd (inferInstance : FiniteDimensional ℂ H) hinf
    · exact h
  obtain ⟨u, hu⟩ := exists_unit_vector (H := H)
  have he : IsMinimalProjection (⊤ : VonNeumannAlgebra H) (rankOne ℂ u u) :=
    isMinimalProjection_rankOne_boundedLinearOperators hu
  obtain ⟨F, U, hU, -⟩ := isFactor_boundedLinearOperators.exists_spatial_tensorDecomposition he
  haveI : CompleteSpace (LinearMap.range ((rankOne ℂ u u : H →L[ℂ] H) : H →ₗ[ℂ] H)) :=
    he.1.completeSpace_range
  haveI hfd : FiniteDimensional ℂ (LinearMap.range ((rankOne ℂ u u : H →L[ℂ] H) : H →ₗ[ℂ] H)) :=
    finiteDimensional_range_rankOne u
  haveI : Nontrivial (LinearMap.range ((rankOne ℂ u u : H →L[ℂ] H) : H →ₗ[ℂ] H)) := by
    rw [Submodule.nontrivial_iff_ne_bot, ne_eq, LinearMap.range_eq_bot]
    exact fun h => he.2.2.1 (ContinuousLinearMap.coe_injective
      (h.trans ContinuousLinearMap.coe_zero.symm))
  refine ⟨lp (fun _ : F => ℂ) 2, inferInstance, inferInstance, inferInstance, ?_,
    ⟨(conjEquiv U ⊤).trans ((equivOfEq hU).trans HilbertTensor.amplifyLeftStarAlgEquiv.symm)⟩⟩
  intro hK
  haveI := hK
  exact hinf U.symm.toLinearEquiv.finiteDimensional

/-- **`B(H)` is a type I_∞ factor when `H` is infinite-dimensional.** Packaged as the intrinsic
predicate `IsTypeIInfinite`: `⊤ = B(H)` is a type I factor (`isTypeIFactor_boundedLinearOperators`)
carrying an infinite orthogonal family of minimal projections — the rank-one projections
`|uₙ⟩⟨uₙ|` onto a countable orthonormal sequence `(uₙ)` extracted from a Hilbert basis of the
infinite-dimensional `H`. The `⋆`-isomorphism to an infinite-dimensional `B(K)` is
`exists_starAlgEquiv_infiniteDimensional_boundedLinearOperators`. -/
theorem isTypeIInfinite_boundedLinearOperators {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (hinf : ¬FiniteDimensional ℂ H) :
    IsTypeIInfinite (⊤ : VonNeumannAlgebra H) := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ H
  have hwinf : Infinite w := by
    rw [← not_finite_iff_infinite]
    intro hfin
    haveI : Finite w := hfin
    haveI : Fintype w := Fintype.ofFinite w
    exact hinf b.toOrthonormalBasis.toBasis.finiteDimensional_of_finite
  haveI := hwinf
  let g : ℕ ↪ w := Infinite.natEmbedding w
  set u : ℕ → H := fun n => b (g n) with hu_def
  have hon : Orthonormal ℂ u := by
    rw [hu_def]; exact b.orthonormal.comp g g.injective
  have hnorm : ∀ n, ‖u n‖ = 1 := fun n => hon.1 n
  have hmin : ∀ n, IsMinimalProjection (⊤ : VonNeumannAlgebra H) (rankOne ℂ (u n) (u n)) :=
    fun n => isMinimalProjection_rankOne_boundedLinearOperators (hnorm n)
  have horth : ∀ m n, m ≠ n → rankOne ℂ (u m) (u m) * rankOne ℂ (u n) (u n) = 0 := by
    intro m n hmn
    rw [ContinuousLinearMap.mul_def, rankOne_comp_rankOne, hon.2 hmn, zero_smul]
  haveI : Nontrivial H :=
    nontrivial_of_ne (u 0) 0 (by rw [← norm_ne_zero_iff, hnorm 0]; norm_num)
  exact ⟨isTypeIFactor_boundedLinearOperators, fun n => rankOne ℂ (u n) (u n), hmin, horth⟩

end VonNeumannAlgebra
