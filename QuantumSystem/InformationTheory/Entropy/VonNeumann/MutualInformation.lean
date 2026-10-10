/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.InnerProductSpace.PartialTrace
public import QuantumSystem.InformationTheory.Entropy.VonNeumann.Basic
public import QuantumSystem.Notation

/-!
# Quantum mutual information

Let `H` and `K` be finite-dimensional complex Hilbert spaces and `ω` a state on
`B(H ⊗ K) = B(H) ⊗ B(K)`. Its **marginals** are the restrictions `ω_A = ω(· ⊗ 1)` and
`ω_B = ω(1 ⊗ ·)` (`State.traceRight`, `State.traceLeft`); their densities are the partial traces
of `ρ_ω` (`State.density_traceRight`). The **quantum mutual information** is
`I(A:B) = S(ω_A) + S(ω_B) - S(ω)` (`State.mutualInformation`), and it is the relative entropy of
`ω` with respect to the product of its marginals:
`D(ω ‖ ω_A ⊗ ω_B) = I(A:B)` (`State.umegakiEntropy_eq_mutualInformation`). In particular
`I(A:B) ≥ 0`, i.e. the von Neumann entropy is subadditive (`State.mutualInformation_nonneg`).

The **product** `ψ ⊗ φ` of positive functionals on `B(H)` and `B(K)` is the functional on
`B(H ⊗ K)` with `(ψ ⊗ φ)(A ⊗ B) = ψ(A) φ(B)` (`PositiveLinearMap.tensorProduct`), through
`B(H) ⊗ B(K) ≅ B(H ⊗ K)` (`TensorProduct.mapLEquiv`); its density is `ρ_ψ ⊗ ρ_φ`.

## Main definitions

* `PositiveLinearMap.tensorProduct ψ φ` — the product functional `ψ ⊗ φ`;
  `State.tensorProduct ω₁ ω₂` — the product state.
* `State.traceRight ω`, `State.traceLeft ω` — the marginals `ω_A`, `ω_B` of a state on
  `B(H ⊗ K)`.
* `State.mutualInformation ω` — `I(A:B) = S(ω_A) + S(ω_B) - S(ω)`.

## Main results

* `PositiveLinearMap.tensorProduct_mapL`, `PositiveLinearMap.density_tensorProduct` — the product
  functional on elementary tensors, and its density.
* `State.density_traceRight`, `State.density_traceLeft` — the marginals have the partial traces
  of `ρ_ω` as densities.
* `State.umegakiEntropy_eq_mutualInformation` — `D(ω ‖ ω_A ⊗ ω_B) = I(A:B)`.
* `State.mutualInformation_nonneg` — `0 ≤ I(A:B)`, subadditivity `S(ω) ≤ S(ω_A) + S(ω_B)`.

## TODO

The product state and the marginals are stated on `B(H) ⊗ B(K) ≅ B(H ⊗ K)` (finite dimensions,
`TensorProduct.mapLEquiv`). For general C\*-algebras the product state lives on the minimal
C\*-tensor product, which Mathlib does not have yet; move them to `State` then. The marginals are
instances of the restriction `State.comp` along the ampliations.

## Proof

In the product `e_{ij} = aᵢ ⊗ fⱼ` of eigenbases of `ρ_A` and `ρ_B`, with eigenvalues `λᵢ`, `μⱼ`,
`log(ρ_A ⊗ ρ_B)` is diagonal with entries `log(λᵢ μⱼ)`. The weights `w_{ij} = ω(|e_{ij}⟩⟨e_{ij}|)`
have marginals `Σⱼ w_{ij} = λᵢ` and `Σᵢ w_{ij} = μⱼ` (`TensorProduct.rTensor_rankOne_eq_sum`), so
`w_{ij} = 0` unless `λᵢ μⱼ > 0`. This gives the support condition, and
`ω(log(ρ_A ⊗ ρ_B)) = Σᵢⱼ w_{ij} (log λᵢ + log μⱼ) = Σᵢ λᵢ log λᵢ + Σⱼ μⱼ log μⱼ`.
-/

@[expose] public section

open ContinuousLinearMap TensorProduct
open InnerProductSpace (rankOne)
open scoped InnerProductSpace ComplexOrder QuantumInfo TensorProduct

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]

/-! ### Product functionals -/

namespace ContinuousLinearMap

variable {G G' : Type*} [FunLike G (H →L[ℂ] H) ℂ] [LinearMapClass G ℂ (H →L[ℂ] H) ℂ]
  [FunLike G' (K →L[ℂ] K) ℂ] [LinearMapClass G' ℂ (K →L[ℂ] K) ℂ]

/-- The product `f ⊗ g` of functionals on `B(H)` and `B(K)`, read on `B(H ⊗ K)` through
`B(H) ⊗ B(K) ≅ B(H ⊗ K)`, is `Z ↦ tr((ρ_f ⊗ ρ_g) Z)`: both are linear and agree on the elementary
tensors `A ⊗ B` (`TensorProduct.ext_mapL`), where they are `f(A) g(B)`. -/
lemma mul'_map_mapLEquiv_symm_apply (f : G) (g : G') (Z : H ⊗[ℂ] K →L[ℂ] H ⊗[ℂ] K) :
    LinearMap.mul' ℂ ℂ (TensorProduct.map (f : (H →L[ℂ] H) →ₗ[ℂ] ℂ) (g : (K →L[ℂ] K) →ₗ[ℂ] ℂ)
      ((mapLEquiv ℂ H H K K).symm Z)) =
      Tr (mapL (density f) (density g) ∘L Z) := by
  have h := ext_mapL (𝕜 := ℂ) (E := H) (F := H) (G := K) (H := K) (M := ℂ)
    (u := LinearMap.mul' ℂ ℂ ∘ₗ TensorProduct.map (f : (H →L[ℂ] H) →ₗ[ℂ] ℂ)
      (g : (K →L[ℂ] K) →ₗ[ℂ] ℂ) ∘ₗ (mapLEquiv ℂ H H K K).symm.toLinearMap)
    (v := (LinearMap.trace ℂ (H ⊗[ℂ] K) ∘ₗ coeLM ℂ) ∘ₗ
      LinearMap.mulLeft ℂ (mapL (density f) (density g))) fun A B => by
    have hs : (mapLEquiv ℂ H H K K).symm (mapL A B) = A ⊗ₜ B :=
      (LinearEquiv.symm_apply_eq _).mpr (mapLEquiv_tmul A B).symm
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, hs,
      TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.mulLeft_apply, coeLM_apply,
      mul_def, ← mapL_comp, trace_mapL, trace_density_comp]
    rfl
  exact LinearMap.congr_fun h Z

end ContinuousLinearMap

namespace PositiveLinearMap

/-- The **product functional** `ψ ⊗ φ` on `B(H ⊗ K)` of positive functionals on `B(H)` and `B(K)`,
determined by `(ψ ⊗ φ)(A ⊗ B) = ψ(A) φ(B)` (`PositiveLinearMap.tensorProduct_mapL`) through
`B(H) ⊗ B(K) ≅ B(H ⊗ K)` (`TensorProduct.mapLEquiv`). It is positive since its density is
`ρ_ψ ⊗ ρ_φ ≥ 0` (`ContinuousLinearMap.mul'_map_mapLEquiv_symm_apply`,
`TensorProduct.mapL_nonneg`). For states it is the product state. -/
noncomputable def tensorProduct (ψ : (H →L[ℂ] H) →ₚ[ℂ] ℂ) (φ : (K →L[ℂ] K) →ₚ[ℂ] ℂ) :
    (H ⊗[ℂ] K →L[ℂ] H ⊗[ℂ] K) →ₚ[ℂ] ℂ :=
  .mk₀ (LinearMap.mul' ℂ ℂ ∘ₗ TensorProduct.map (ψ : (H →L[ℂ] H) →ₗ[ℂ] ℂ)
      (φ : (K →L[ℂ] K) →ₗ[ℂ] ℂ) ∘ₗ (mapLEquiv ℂ H H K K).symm.toLinearMap) fun Z hZ => by
    change 0 ≤ LinearMap.mul' ℂ ℂ (TensorProduct.map (ψ : (H →L[ℂ] H) →ₗ[ℂ] ℂ)
      (φ : (K →L[ℂ] K) →ₗ[ℂ] ℂ) ((mapLEquiv ℂ H H K K).symm Z))
    rw [mul'_map_mapLEquiv_symm_apply]
    exact trace_comp_nonneg (mapL_nonneg (density_nonneg ψ) (density_nonneg φ)) hZ

variable (ψ : (H →L[ℂ] H) →ₚ[ℂ] ℂ) (φ : (K →L[ℂ] K) →ₚ[ℂ] ℂ)

/-- The product functional is `Z ↦ tr((ρ_ψ ⊗ ρ_φ) Z)`. -/
lemma tensorProduct_apply (Z : H ⊗[ℂ] K →L[ℂ] H ⊗[ℂ] K) :
    ψ.tensorProduct φ Z = Tr (mapL (density ψ) (density φ) ∘L Z) :=
  mul'_map_mapLEquiv_symm_apply ψ φ Z

/-- **The product functional on elementary tensors**: `(ψ ⊗ φ)(A ⊗ B) = ψ(A) φ(B)`. -/
@[simp] lemma tensorProduct_mapL (A : H →L[ℂ] H) (B : K →L[ℂ] K) :
    ψ.tensorProduct φ (mapL A B) = ψ A * φ B := by
  rw [tensorProduct_apply, ← mapL_comp, trace_mapL, trace_density_comp, trace_density_comp]

/-- The density of the product functional is the tensor product of the densities. -/
lemma density_tensorProduct : density (ψ.tensorProduct φ) = mapL (density ψ) (density φ) := by
  rw [eq_comm, eq_density_iff]
  exact fun Z => (tensorProduct_apply ψ φ Z).symm

end PositiveLinearMap

namespace State

/-- The **product state** `ω₁ ⊗ ω₂` on `B(H ⊗ K)` of states on `B(H)` and `B(K)`:
`(ω₁ ⊗ ω₂)(A ⊗ B) = ω₁(A) ω₂(B)` (`PositiveLinearMap.tensorProduct`). -/
noncomputable def tensorProduct (ω₁ : State (H →L[ℂ] H)) (ω₂ : State (K →L[ℂ] K)) :
    State (H ⊗[ℂ] K →L[ℂ] H ⊗[ℂ] K) :=
  ofPositiveLinearMap (A := H ⊗[ℂ] K →L[ℂ] H ⊗[ℂ] K)
    ((PositiveLinearMap.ofClass ω₁).tensorProduct (PositiveLinearMap.ofClass ω₂)) (by
    rw [one_def, ← mapL_id_id, PositiveLinearMap.tensorProduct_mapL, ← one_def, ← one_def]
    simp)

/-- The positive functional underlying a product state is the product of the underlying
positive functionals. -/
@[simp] lemma ofClass_tensorProduct (ω₁ : State (H →L[ℂ] H)) (ω₂ : State (K →L[ℂ] K)) :
    PositiveLinearMap.ofClass (ω₁.tensorProduct ω₂) =
      (PositiveLinearMap.ofClass ω₁).tensorProduct (PositiveLinearMap.ofClass ω₂) :=
  rfl

/-- **The product state on elementary tensors**: `(ω₁ ⊗ ω₂)(A ⊗ B) = ω₁(A) ω₂(B)`. -/
@[simp] lemma tensorProduct_mapL (ω₁ : State (H →L[ℂ] H)) (ω₂ : State (K →L[ℂ] K))
    (A : H →L[ℂ] H) (B : K →L[ℂ] K) : ω₁.tensorProduct ω₂ (mapL A B) = ω₁ A * ω₂ B :=
  PositiveLinearMap.tensorProduct_mapL (PositiveLinearMap.ofClass ω₁) (PositiveLinearMap.ofClass ω₂) A B

/-- The density of the product state is the tensor product of the densities. -/
lemma density_tensorProduct (ω₁ : State (H →L[ℂ] H)) (ω₂ : State (K →L[ℂ] K)) :
    density (ω₁.tensorProduct ω₂) = mapL (density ω₁) (density ω₂) := by
  have h₁ : density (PositiveLinearMap.ofClass ω₁) = density ω₁ :=
    density_eq_density_iff.mpr fun _ => rfl
  have h₂ : density (PositiveLinearMap.ofClass ω₂) = density ω₂ :=
    density_eq_density_iff.mpr fun _ => rfl
  rw [← h₁, ← h₂, eq_comm, eq_density_iff]
  exact fun Z => (PositiveLinearMap.tensorProduct_apply (PositiveLinearMap.ofClass ω₁)
    (PositiveLinearMap.ofClass ω₂) Z).symm

end State

/-! ### Marginals and mutual information -/

namespace State

variable (ω : State (H ⊗[ℂ] K →L[ℂ] H ⊗[ℂ] K))

/-- The **marginal** `ω_A = ω(· ⊗ 1)` of a state on `B(H ⊗ K)` on the first factor: its restriction
along the ampliation `A ↦ A ⊗ 1`. Its density is the partial trace `tr_K ρ_ω`
(`State.density_traceRight`). -/
noncomputable def traceRight : State (H →L[ℂ] H) :=
  ω.comp (rTensorStarAlgHom ℂ H K) (map_one _)

/-- The **marginal** `ω_B = ω(1 ⊗ ·)` of a state on `B(H ⊗ K)` on the second factor: its
restriction along the ampliation `B ↦ 1 ⊗ B`. -/
noncomputable def traceLeft : State (K →L[ℂ] K) :=
  ω.comp (lTensorStarAlgHom ℂ K H) (map_one _)

/-- `traceRight` evaluates `ω` on the ampliation `A ↦ A ⊗ 1`. -/
@[simp] lemma traceRight_apply (A : H →L[ℂ] H) : ω.traceRight A = ω (A.rTensor K) :=
  rfl

/-- `traceLeft` evaluates `ω` on the ampliation `B ↦ 1 ⊗ B`. -/
@[simp] lemma traceLeft_apply (B : K →L[ℂ] K) : ω.traceLeft B = ω (B.lTensor H) :=
  rfl

/-- The density of the marginal `ω_A` is the partial trace `tr_K ρ_ω`. -/
lemma density_traceRight :
    density ω.traceRight = ContinuousLinearMap.traceRight H K (density ω) :=
  density_eq_traceDual (rTensorStarAlgHom ℂ H K) fun _ => rfl

/-- The density of the marginal `ω_B` is the partial trace `tr₁(ρ_ω)` of `ρ_ω` over the first
factor. -/
lemma density_traceLeft :
    density ω.traceLeft = ContinuousLinearMap.traceLeft H K (density ω) :=
  density_eq_traceDual (lTensorStarAlgHom ℂ K H) fun _ => rfl

/-- The **quantum mutual information** `I(A:B) = S(ω_A) + S(ω_B) - S(ω)` of a state on
`B(H ⊗ K)`. -/
noncomputable def mutualInformation : ℝ :=
  S(ω.traceRight) + S(ω.traceLeft) - S(ω)

/-- **The mutual information is a relative entropy**: `D(ω ‖ ω_A ⊗ ω_B) = I(A:B)`. -/
theorem umegakiEntropy_eq_mutualInformation :
    D(ω ∥ ω.traceRight.tensorProduct ω.traceLeft) = (ω.mutualInformation : EReal) := by
  obtain ⟨a, l, -, ha⟩ := exists_orthonormalBasis_density_apply ω.traceRight
  obtain ⟨f, m, -, hf⟩ := exists_orthonormalBasis_density_apply ω.traceLeft
  obtain ⟨e, he_def⟩ : ∃ e : OrthonormalBasis _ ℂ (H ⊗[ℂ] K), e = a.tensorProduct f := ⟨_, rfl⟩
  have hep : ∀ p, e p = a p.1 ⊗ₜ f p.2 := fun p => by
    rw [he_def, OrthonormalBasis.tensorProduct_apply']
  have he : ∀ p, density (ω.traceRight.tensorProduct ω.traceLeft) (e p) =
      ((l p.1 * m p.2 : ℝ) : ℂ) • e p := fun p => by
    rw [density_tensorProduct, hep, mapL_tmul, ha, hf, smul_tmul_smul, Complex.ofReal_mul]
  -- the weights `w p = ω(|e p⟩⟨e p|)` and their marginals
  obtain ⟨w, hw⟩ : ∃ w : _ → ℂ, ∀ p, w p = ω (rankOne ℂ (e p) (e p)) := ⟨_, fun _ => rfl⟩
  have hw0 : ∀ p, 0 ≤ w p := fun p => by
    rw [hw]
    exact ω.apply_nonneg (nonneg_iff_isPositive.2 (InnerProductSpace.isPositive_rankOne_self _))
  have hrow : ∀ i, ∑ j, w (i, j) = (l i : ℂ) := fun i => by
    have h := (inner_density_apply ω.traceRight (a i)).symm
    rw [ha, inner_smul_right, a.inner_eq_one, mul_one, traceRight_apply,
      rTensor_rankOne_eq_sum f, map_sum] at h
    simp only [hw, hep]
    exact h
  have hcol : ∀ j, ∑ i, w (i, j) = (m j : ℂ) := fun j => by
    have h := (inner_density_apply ω.traceLeft (f j)).symm
    rw [hf, inner_smul_right, f.inner_eq_one, mul_one, traceLeft_apply,
      lTensor_rankOne_eq_sum a, map_sum] at h
    simp only [hw, hep]
    exact h
  have hwl : ∀ i j, l i = 0 → w (i, j) = 0 := fun i j hi =>
    (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hw0 (i, j)).mp
      (by rw [hrow, hi, Complex.ofReal_zero]) j (Finset.mem_univ j)
  have hwm : ∀ i j, m j = 0 → w (i, j) = 0 := fun i j hj =>
    (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hw0 (i, j)).mp
      (by rw [hcol, hj, Complex.ofReal_zero]) i (Finset.mem_univ i)
  -- the support condition
  have hnull : ∀ Z : H ⊗[ℂ] K →L[ℂ] H ⊗[ℂ] K,
      ω.traceRight.tensorProduct ω.traceLeft (star Z * Z) = 0 → ω (star Z * Z) = 0 := by
    have hzero : ∀ p, l p.1 * m p.2 = 0 → ω (rankOne ℂ (e p) (e p)) = 0 := fun p hp => by
      rw [← hw]
      exact (mul_eq_zero.mp hp).elim (hwl p.1 p.2) (hwm p.1 p.2)
    exact apply_star_mul_self_eq_zero_of_apply_rankOne (ψ := ω)
      (φ := ω.traceRight.tensorProduct ω.traceLeft) (c := e) (s := fun p => l p.1 * m p.2) he hzero
  -- Umegaki's formula
  have hsa := IsSelfAdjoint.of_nonneg (density_nonneg (ω.traceRight.tensorProduct ω.traceLeft))
  rw [umegakiEntropy_eq_re_apply hnull, map_sub, Complex.sub_re, re_apply_log_density,
    ← trace_density_comp ω, CFC.log, trace_comp_cfc_eq_sum hsa e he]
  have hterm : ∀ p : _ × _, (Real.log (l p.1 * m p.2) : ℂ) * ⟪e p, density ω (e p)⟫_ℂ =
      (Real.log (l p.1) : ℂ) * w p + (Real.log (m p.2) : ℂ) * w p := fun p => by
    rw [inner_density_apply, ← hw]
    by_cases hp : w p = 0
    · simp [hp]
    · have hl0 : l p.1 ≠ 0 := fun h => hp (hwl p.1 p.2 h)
      have hm0 : m p.2 ≠ 0 := fun h => hp (hwm p.1 p.2 h)
      rw [Real.log_mul hl0 hm0, Complex.ofReal_add, add_mul]
  simp_rw [hterm, Finset.sum_add_distrib, Fintype.sum_prod_type]
  rw [Finset.sum_comm (f := fun i j => (Real.log (m j) : ℂ) * w (i, j))]
  simp_rw [← Finset.mul_sum, hrow, hcol]
  rw [mutualInformation, vonNeumannEntropy_eq_sum_negMulLog _ ha,
    vonNeumannEntropy_eq_sum_negMulLog _ hf]
  congr 1
  simp only [Complex.add_re, Complex.re_sum, ← Complex.ofReal_mul, Complex.ofReal_re,
    Real.negMulLog]
  simp only [neg_mul, Finset.sum_neg_distrib]
  simp_rw [mul_comm (Real.log _)]
  ring

/-- **Nonnegativity of the mutual information** (Klein's inequality for
`D(ω ‖ ω_A ⊗ ω_B)`), i.e. **subadditivity** `S(ω) ≤ S(ω_A) + S(ω_B)`. -/
theorem mutualInformation_nonneg : 0 ≤ ω.mutualInformation := by
  have h := umegakiEntropy_nonneg (ψ := ω) (φ := ω.traceRight.tensorProduct ω.traceLeft)
    (by simp)
  rw [umegakiEntropy_eq_mutualInformation] at h
  exact_mod_cast h

end State
