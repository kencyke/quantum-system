module

public import QuantumSystem.Algebra.VonNeumannAlgebra.TensorIdentification
public import QuantumSystem.ForMathlib.Analysis.VonNeumannAlgebra.Lattice

/-!
# The algebra of all bounded operators is a type I factor

The algebra `B(H) = H →L[ℂ] H` of *all* bounded operators — realised as the greatest von Neumann
algebra `⊤ : VonNeumannAlgebra H` — is a factor: its centre is the scalars, by the elementary fact
that an operator commuting with every rank-one operator is scalar. It possesses a minimal
projection, namely any rank-one orthogonal projection `|u⟩⟨u|` with `‖u‖ = 1`. Hence `B(H)` is a
**type I factor**, and by the abstract structure theorem `IsTypeIFactor.exists_starAlgEquiv` it is
`⋆`-isomorphic to `B(K)` for some Hilbert space `K` (which is `ℓ²` of an orthonormal basis of `H`);
when `H` is infinite-dimensional this exhibits `B(H)` as a **type I_∞ factor**.

## Main results

* `VonNeumannAlgebra.isFactor_boundedLinearOperators` — `B(H)` is a factor.
* `VonNeumannAlgebra.exists_isMinimalProjection_boundedLinearOperators` — `B(H)` has a minimal
  projection (rank-one).
* `VonNeumannAlgebra.isTypeIFactor_boundedLinearOperators` — `B(H)` is a type I factor.
* `VonNeumannAlgebra.exists_starAlgEquiv_boundedLinearOperators` — `B(H) ≃⋆ₐ B(K)` for some
  Hilbert space `K`.
* `VonNeumannAlgebra.isTypeIInfinite_boundedLinearOperators` — for infinite-dimensional `H`, the
  space `K` is infinite-dimensional (`B(H)` is type I_∞).
-/

@[expose] public section

namespace VonNeumannAlgebra

open InnerProductSpace

universe u

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

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

/-- **`B(H)` is a type I_∞ factor when `H` is infinite-dimensional.** The full algebra is
`⋆`-isomorphic to `B(K)` for a complex Hilbert space `K` that is itself infinite-dimensional. Here
`K = ℓ²(F)` for `F` an orthonormal basis of `H`; a finite `F` would, through the spatial
decomposition `H ≃ₗᵢ ℓ²(F) ⊗̂ (eH)` with one-dimensional multiplicity `eH` (the range of the
rank-one minimal projection), force `H` finite-dimensional. Expressing type I_∞ as
`¬FiniteDimensional ℂ K` is the standard reading: a type I_n factor is `B(K)` with `dim K = n`, so
I_∞ is exactly the infinite-dimensional `K`. -/
theorem isTypeIInfinite_boundedLinearOperators {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H] (hinf : ¬FiniteDimensional ℂ H) :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (_ : CompleteSpace K),
      ¬FiniteDimensional ℂ K ∧
      Nonempty ((⊤ : VonNeumannAlgebra H) ≃⋆ₐ[ℂ] (K →L[ℂ] K)) := by
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

end VonNeumannAlgebra
