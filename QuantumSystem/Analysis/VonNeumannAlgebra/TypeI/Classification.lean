/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.VonNeumannAlgebra.TypeI.Defs
public import QuantumSystem.Analysis.VonNeumannAlgebra.TypeI.StructureTheorem

/-!
# Classification of type I factors

A type I factor (`IsTypeIFactor`, a factor that is type I, defined in
`QuantumSystem.Analysis.VonNeumannAlgebra.TypeI.Defs`; on a nonzero Hilbert space, a factor with a
minimal projection) is `⋆`-isomorphic to the algebra `B(K)` of
all bounded operators on some Hilbert space `K` (`IsTypeIFactor.exists_starAlgEquiv`); the spatial
content — the implementing unitary and the multiplicity model `K = ℓ²(F)` — is
`IsTypeIFactor.exists_spatial_tensor_decomposition`, the `IsTypeIFactor` form of the structure
theorem `IsFactor.exists_spatial_tensor_decomposition` of
`QuantumSystem.Analysis.VonNeumannAlgebra.TypeI.StructureTheorem`. The commutant of a type I factor
is again a type I factor (`IsTypeIFactor.commutant`).

For a type I_∞ factor the Hilbert space `K` is infinite-dimensional, and conversely
(`isTypeIInfinite_iff_exists_starAlgEquiv`): through `N ≃⋆ₐ B(K)` the minimal projections are the
rank-one projections, of which `B(K)` has an infinite orthogonal family exactly when `K` is
infinite-dimensional. Spatially, a factor is type I_∞ iff the covering family `F` of the structure
theorem `N ≅ B(ℓ²(F)) ⊗̄ 1` is infinite (`OrthEquivFam.isTypeIInfinite_iff_infinite`).

## Main results

* `VonNeumannAlgebra.IsTypeIFactor.exists_spatial_tensor_decomposition`,
  `VonNeumannAlgebra.IsTypeIFactor.exists_split_tensor_decomposition` — the spatial and split
  tensor decompositions of `QuantumSystem.Analysis.VonNeumannAlgebra.TypeI.StructureTheorem`, stated
  for a type I factor on a nonzero Hilbert space with the minimal projection existentially
  quantified.
* `VonNeumannAlgebra.IsTypeIFactor.commutant`, `VonNeumannAlgebra.isTypeIFactor_commutant_iff` —
  the commutant of a type I factor is a type I factor, via `isTypeIFactor_oneTensor_boundedLinearOperators`
  (`1 ⊗̄ B(H₂)` is a type I factor) and `isTypeIFactor_conj_iff` (spatial invariance).
* `VonNeumannAlgebra.IsTypeIFactor.exists_starAlgEquiv` — a type I factor is `⋆`-isomorphic to
  `B(K)` for some complex Hilbert space `K`.
* `VonNeumannAlgebra.isTypeIFactor_commutant_boundedLinearOperators` — the scalar algebra
  `ℂ1 = B(H)′` is a type I factor.
* `VonNeumannAlgebra.IsTypeIInfinite.exists_starAlgEquiv`,
  `VonNeumannAlgebra.isTypeIInfinite_iff_exists_starAlgEquiv` — the type I_∞ factors are exactly
  the von Neumann algebras `⋆`-isomorphic to `B(K)` for an infinite-dimensional `K`.
* `VonNeumannAlgebra.OrthEquivFam.isTypeIInfinite_iff_infinite`,
  `VonNeumannAlgebra.IsTypeIInfinite.exists_spatial_tensor_decomposition` — spatially, a factor is
  type I_∞ iff the covering family `F` of the structure theorem `N ≅ B(ℓ²(F)) ⊗̄ 1` is infinite.

## Notation

`⊗̄` is documentation shorthand for the von Neumann (spatial) tensor product of algebras; that
convention is stated in full in `QuantumSystem.Analysis.VonNeumannAlgebra.TensorFactor`, where the
algebras it names (`VonNeumannAlgebra.tensorOne` / `VonNeumannAlgebra.oneTensor`) are defined.
-/

@[expose] public section

namespace VonNeumannAlgebra

open scoped lp

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Spatial structure theorems for type I factors -/

universe u

section SpatialTensor

open HilbertTensor

/-- **Spatial structure theorem for a type I factor.** A type I factor `N ⊆ B(H)` on a nonzero
Hilbert space is spatially the tensor factor `B(ℓ²(F)) ⊗̄ 1`: for some minimal projection `e` of `N` there is
`U : H ≃ₗᵢ ℓ²(F) ⊗̂ (eH)` carrying `N` onto `𝓑(ℓ²(F)) ⊗ 𝟙[eH]` and `N′` onto `𝟙[ℓ²(F)] ⊗ 𝓑(eH)`. This is
the `IsTypeIFactor` form of `IsFactor.exists_spatial_tensor_decomposition`, which gives the same
for *every* minimal projection `e` of a factor. -/
theorem IsTypeIFactor.exists_spatial_tensor_decomposition [Nontrivial H] {N : VonNeumannAlgebra H}
    (hN : IsTypeIFactor N) :
    ∃ (e : H →L[ℂ] H) (he : IsMinimalProjection N e),
      haveI := he.1.completeSpace_range
      ∃ (F : Set (H →L[ℂ] H)) (U : H ≃ₗᵢ[ℂ] ℓ²(F, ℂ) ⊗̂ e.range),
        VonNeumannAlgebra.conj U N = 𝓑(ℓ²(F, ℂ)) ⊗ 𝟙[e.range] ∧
        VonNeumannAlgebra.conj U N′ = 𝟙[ℓ²(F, ℂ)] ⊗ 𝓑(e.range) :=
  let ⟨e, he⟩ := hN.exists_isMinimalProjection
  ⟨e, he, hN.1.exists_spatial_tensor_decomposition he⟩

/-- **Split tensor decomposition through a type I factor.** If a type I factor `N` on a nonzero
Hilbert space interpolates an inclusion `A ≤ N ≤ B`, then for some minimal projection `e` of `N` there is
`U : H ≃ₗᵢ ℓ²(F) ⊗̂ (eH)` identifying `N` and `N′` with the tensor factors and sending `A` into
`𝓑(ℓ²(F)) ⊗ 𝟙[eH]` and `B′` into `𝟙[ℓ²(F)] ⊗ 𝓑(eH)`. This is the `IsTypeIFactor` form of
`IsFactor.exists_split_tensor_decomposition`, which gives the same for *every* minimal projection
`e` of a factor. -/
lemma IsTypeIFactor.exists_split_tensor_decomposition [Nontrivial H] {N : VonNeumannAlgebra H}
    (hN : IsTypeIFactor N) {A B : VonNeumannAlgebra H} (h₁ : A ≤ N) (h₂ : N ≤ B) :
    ∃ (e : H →L[ℂ] H) (he : IsMinimalProjection N e),
      haveI := he.1.completeSpace_range
      ∃ (F : Set (H →L[ℂ] H)) (U : H ≃ₗᵢ[ℂ] ℓ²(F, ℂ) ⊗̂ e.range),
        Nonempty F ∧
        VonNeumannAlgebra.conj U N = 𝓑(ℓ²(F, ℂ)) ⊗ 𝟙[e.range] ∧
        VonNeumannAlgebra.conj U N′ = 𝟙[ℓ²(F, ℂ)] ⊗ 𝓑(e.range) ∧
        VonNeumannAlgebra.conj U A ≤ 𝓑(ℓ²(F, ℂ)) ⊗ 𝟙[e.range] ∧
        VonNeumannAlgebra.conj U B′ ≤ 𝟙[ℓ²(F, ℂ)] ⊗ 𝓑(e.range) :=
  let ⟨e, he⟩ := hN.exists_isMinimalProjection
  ⟨e, he, hN.1.exists_split_tensor_decomposition he h₁ h₂⟩

/-- **`1 ⊗̄ B(H₂)` is a type I factor**. If either leg is zero, so is `H₁ ⊗̂ H₂`
(`isTypeIFactor_of_subsingleton`). Otherwise it is a factor
(`VonNeumannAlgebra.isFactor_oneTensor_boundedLinearOperators`), and `1 ⊗̂ |u⟩⟨u|` is a minimal projection for a unit
vector `u ∈ H₂`: every element of `1 ⊗̄ B(H₂)` is a right amplification `1 ⊗̂ S`
(`VonNeumannAlgebra.mem_oneTensor_iff`), so the corner reduces to the corner of the
rank-one projection in `B(H₂)`. -/
lemma isTypeIFactor_oneTensor_boundedLinearOperators {H₁ H₂ : Type*} [NormedAddCommGroup H₁]
    [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
    [CompleteSpace H₂] : IsTypeIFactor (𝟙[H₁] ⊗ 𝓑(H₂)) := by
  have of_one_eq_zero (h : (1 : H₁ ⊗̂ H₂ →L[ℂ] H₁ ⊗̂ H₂) = 0) : IsTypeIFactor (𝟙[H₁] ⊗ 𝓑(H₂)) := by
    have : Subsingleton (H₁ ⊗̂ H₂) :=
      ⟨fun x y => sub_eq_zero.mp (by simpa using congrArg (fun T => T (x - y)) h)⟩
    exact isTypeIFactor_of_subsingleton _
  rcases subsingleton_or_nontrivial H₁ with _ | _
  · exact of_one_eq_zero (by
      rw [← amplifyLeft_one (H₂ := H₂), Subsingleton.elim (1 : H₁ →L[ℂ] H₁) 0, amplifyLeft_zero])
  rcases subsingleton_or_nontrivial H₂ with _ | _
  · exact of_one_eq_zero (by
      rw [← amplifyRight_one (H₁ := H₁), Subsingleton.elim (1 : H₂ →L[ℂ] H₂) 0, amplifyRight_zero])
  obtain ⟨p, hp⟩ := exists_isMinimalProjection_boundedLinearOperators (H := H₂)
  refine isFactor_oneTensor_boundedLinearOperators.isTypeIFactor_of_isMinimalProjection (e := 𝟙 ⊗ p)
    ⟨hp.1.map (amplifyRightₐ (H₁ := H₁)), amplifyRight_mem_oneTensor (mem_boundedLinearOperators p),
      fun h => hp.2.2.1 (amplifyRight_injective (H₁ := H₁) (h.trans amplifyRight_zero.symm)),
      fun T hT => ?_⟩
  obtain ⟨S, -, rfl⟩ := mem_oneTensor_iff.mp hT
  obtain ⟨c, hc⟩ := hp.2.2.2 S (mem_boundedLinearOperators S)
  exact ⟨c, by rw [← amplifyRight_mul, ← amplifyRight_mul, hc, amplifyRight_smul]⟩

end SpatialTensor

open HilbertTensor in
/-- **The commutant of a type I factor is a type I factor**. By the split tensor decomposition,
`N` and `N′` are spatially
`B(ℓ²(F)) ⊗̄ 1` and `1 ⊗̄ B(eH)` for a minimal projection `e` of `N`; the latter
is a type I factor (`isTypeIFactor_oneTensor_boundedLinearOperators`), and type I factors are spatially invariant
(`isTypeIFactor_conj_iff`). -/
theorem IsTypeIFactor.commutant {N : VonNeumannAlgebra H} (hN : IsTypeIFactor N) :
    IsTypeIFactor N′ := by
  rcases subsingleton_or_nontrivial H with _ | _
  · exact isTypeIFactor_of_subsingleton _
  obtain ⟨e, he, F, U, -, -, hU', -, -⟩ := hN.exists_split_tensor_decomposition le_rfl le_rfl
  have : CompleteSpace (e.range) := he.1.completeSpace_range
  rw [← isTypeIFactor_conj_iff U, hU']
  exact isTypeIFactor_oneTensor_boundedLinearOperators

/-- A von Neumann algebra is a type I factor iff its commutant is. -/
lemma isTypeIFactor_commutant_iff {N : VonNeumannAlgebra H} :
    IsTypeIFactor N′ ↔ IsTypeIFactor N :=
  ⟨fun h => VonNeumannAlgebra.commutant_commutant N ▸ h.commutant, IsTypeIFactor.commutant⟩

/-- **Type I factor abstract structure theorem.** A type I factor `N` is `⋆`-isomorphic to the
algebra `B(K)` of all bounded operators on *some* complex Hilbert space `K` (on the zero space,
`K = H`). This is the model-independent form of the
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
  rcases subsingleton_or_nontrivial H with _ | _
  · refine ⟨H, inferInstance, inferInstance, inferInstance,
      ⟨StarAlgEquiv.ofBijective N.toStarSubalgebra.subtype ⟨Subtype.val_injective, fun x => ?_⟩⟩⟩
    exact ⟨⟨x, Subsingleton.elim x 0 ▸ N.zero_mem⟩, rfl⟩
  obtain ⟨e, he, F, U, hU, -⟩ := hN.exists_spatial_tensor_decomposition
  have : CompleteSpace (e.range) := he.1.completeSpace_range
  have : Nontrivial (e.range) := he.nontrivial_range
  exact ⟨ℓ²(F, ℂ), inferInstance, inferInstance, inferInstance,
    ⟨(conjEquiv U N).trans ((equivOfEq hU).trans HilbertTensor.amplifyLeftStarAlgEquiv.symm)⟩⟩

/-- **The scalar algebra `ℂ1 = B(H)′` is a type I factor**, as the commutant of the type I factor
    `B(H)` (`IsTypeIFactor.commutant`); concretely its only elements are scalars, and on a nonzero
    space `1` is a minimal projection. This is the degenerate type I factor of the escape clause
    "either `𝓡 = ℂ1` or …" of the type III₁ literature. -/
lemma isTypeIFactor_commutant_boundedLinearOperators :
    IsTypeIFactor (𝓑(H))′ :=
  isTypeIFactor_boundedLinearOperators.commutant

/-! ### Type I_∞ factors are `B(K)` with `K` infinite-dimensional

Combining the structure theorem with `isTypeIInfinite_iff_of_starAlgEquiv` identifies the type I_∞
factors with the `B(K)` for infinite-dimensional `K`, abstractly
(`isTypeIInfinite_iff_exists_starAlgEquiv`) and spatially as `B(ℓ²(F)) ⊗̄ 1` for an infinite
covering family `F` (`IsTypeIInfinite.exists_spatial_tensor_decomposition`). -/

section TypeIInfinite

variable {N : VonNeumannAlgebra H}

/-- **A type I_∞ factor is `B(K)` for an infinite-dimensional `K`.** A type I_∞ factor is
`⋆`-isomorphic to the algebra `B(K)` of all bounded operators on an infinite-dimensional complex
Hilbert space `K`: the structure theorem `IsTypeIFactor.exists_starAlgEquiv` gives some `K`, and
`isTypeIInfinite_iff_of_starAlgEquiv` forces it to be infinite-dimensional. The converse is
`isTypeIInfinite_iff_exists_starAlgEquiv`; the spatial form is
`IsTypeIInfinite.exists_spatial_tensor_decomposition`. -/
theorem IsTypeIInfinite.exists_starAlgEquiv {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {N : VonNeumannAlgebra H}
    (hN : IsTypeIInfinite N) :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (_ : CompleteSpace K),
      ¬FiniteDimensional ℂ K ∧ Nonempty (N ≃⋆ₐ[ℂ] (K →L[ℂ] K)) := by
  obtain ⟨K, _, _, _, ⟨φ⟩⟩ := hN.isTypeIFactor.exists_starAlgEquiv
  exact ⟨K, _, _, _, (isTypeIInfinite_iff_of_starAlgEquiv φ).mp hN, ⟨φ⟩⟩

/-- **Type I_∞ factors are exactly the `B(K)` with `K` infinite-dimensional.** A von Neumann
algebra is a type I_∞ factor iff it is `⋆`-isomorphic to the algebra `B(K)` of all bounded operators
on an infinite-dimensional complex Hilbert space `K`. The forward direction is
`IsTypeIInfinite.exists_starAlgEquiv`, the backward one `isTypeIInfinite_iff_of_starAlgEquiv`. -/
theorem isTypeIInfinite_iff_exists_starAlgEquiv {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {N : VonNeumannAlgebra H} :
    IsTypeIInfinite N ↔
      ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (_ : CompleteSpace K),
        ¬FiniteDimensional ℂ K ∧ Nonempty (N ≃⋆ₐ[ℂ] (K →L[ℂ] K)) :=
  ⟨IsTypeIInfinite.exists_starAlgEquiv,
    fun ⟨_, _, _, _, hK, ⟨φ⟩⟩ => (isTypeIInfinite_iff_of_starAlgEquiv φ).mpr hK⟩

open HilbertTensor in
/-- **A factor is type I_∞ iff its covering family is infinite.** Let `e` be a minimal projection
of a factor `N` and `F` a covering family of pairwise orthogonal projections equivalent to `e`
(`IsFactor.exists_orthEquivFam_top`). Then `N` is type I_∞ iff `F` is infinite. Forward: the
spatial isomorphism `U : H ≃ₗᵢ ℓ²(F) ⊗̂ (eH)` of the structure theorem carries `N` onto
`B(ℓ²(F)) ⊗̄ 1` (`OrthEquivFam.conj_spatialEquiv_eq_tensorOne_boundedLinearOperators`), whence `N ≃⋆ₐ B(ℓ²(F))`; so
`ℓ²(F)` is infinite-dimensional (`isTypeIInfinite_iff_of_starAlgEquiv`), i.e. `F` is infinite
(`lp.finiteDimensional_iff_finite`). Backward: the members of an infinite `F` are themselves an
infinite orthogonal family of minimal projections (`OrthEquivFam.isMinimalProjection_of_mem`). -/
lemma OrthEquivFam.isTypeIInfinite_iff_infinite {e : H →L[ℂ] H} {F : Set (H →L[ℂ] H)}
    (hF : OrthEquivFam N e F) (hN : IsFactor N) (he : IsMinimalProjection N e)
    (htop : (⨆ f ∈ F, f.range).topologicalClosure = ⊤) :
    IsTypeIInfinite N ↔ Infinite F := by
  constructor
  · intro hI
    have : DecidableEq F := Classical.decEq _
    have : CompleteSpace (e.range) := he.1.completeSpace_range
    have : Nontrivial (e.range) := he.nontrivial_range
    have φ := (conjEquiv (hF.spatialEquiv htop) N).trans
      ((equivOfEq (hF.conj_spatialEquiv_eq_tensorOne_boundedLinearOperators he htop)).trans
        amplifyLeftStarAlgEquiv.symm)
    rw [← not_finite_iff_infinite, ← lp.finiteDimensional_iff_finite (𝕜 := ℂ)]
    exact (isTypeIInfinite_iff_of_starAlgEquiv φ).mp hI
  · intro _
    let g : ℕ ↪ F := Infinite.natEmbedding F
    exact ⟨hN.isTypeIFactor_of_isMinimalProjection he, fun n => g n, fun n => hF.isMinimalProjection_of_mem he (g n).2,
      fun m n hmn => hF.2 (g m).2 (g n).2 fun h => hmn (g.injective (Subtype.ext h))⟩

open HilbertTensor in
/-- **Spatial structure theorem for a type I_∞ factor.** A type I_∞ factor `N ⊆ B(H)` is spatially
`B(ℓ²(F)) ⊗̄ 1` for an *infinite* covering family `F`: for a minimal projection `e` of `N` and a
covering family `F` of pairwise orthogonal projections equivalent to `e`, `F` is infinite
(`OrthEquivFam.isTypeIInfinite_iff_infinite`), and the spatial isomorphism
`U : H ≃ₗᵢ ℓ²(F) ⊗̂ (eH)` carries `N` onto `𝓑(ℓ²(F)) ⊗ 𝟙[eH]` and `N′` onto `𝟙[ℓ²(F)] ⊗ 𝓑(eH)`
(`OrthEquivFam.conj_spatialEquiv_eq_tensorOne_boundedLinearOperators`). This is the type I_∞ refinement of
`IsTypeIFactor.exists_spatial_tensor_decomposition`. -/
theorem IsTypeIInfinite.exists_spatial_tensor_decomposition (hN : IsTypeIInfinite N) :
    ∃ (e : H →L[ℂ] H) (he : IsMinimalProjection N e),
      haveI := he.1.completeSpace_range
      ∃ F : Set (H →L[ℂ] H),
        OrthEquivFam N e F ∧ (⨆ f ∈ F, f.range).topologicalClosure = ⊤ ∧ Infinite F ∧
        ∃ U : H ≃ₗᵢ[ℂ] ℓ²(F, ℂ) ⊗̂ e.range,
          VonNeumannAlgebra.conj U N = 𝓑(ℓ²(F, ℂ)) ⊗ 𝟙[e.range] ∧
          VonNeumannAlgebra.conj U N′ = 𝟙[ℓ²(F, ℂ)] ⊗ 𝓑(e.range) := by
  obtain ⟨⟨hf, -⟩, e₀, hmin, -⟩ := id hN
  obtain ⟨e, he⟩ : ∃ e, IsMinimalProjection N e := ⟨e₀ 0, hmin 0⟩
  obtain ⟨F, hF, htop⟩ := hf.exists_orthEquivFam_top he
  have : DecidableEq F := Classical.decEq _
  have : CompleteSpace (e.range) := he.1.completeSpace_range
  exact ⟨e, he, F, hF, htop, (hF.isTypeIInfinite_iff_infinite hf he htop).mp hN,
    hF.spatialEquiv htop, hF.conj_spatialEquiv_eq_tensorOne_boundedLinearOperators he htop,
    hF.conj_spatialEquiv_commutant_eq_oneTensor_boundedLinearOperators he htop⟩

end TypeIInfinite

end VonNeumannAlgebra
