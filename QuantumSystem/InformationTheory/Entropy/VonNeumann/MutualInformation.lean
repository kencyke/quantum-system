/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.CStarAlgebra.State.TensorProduct
public import QuantumSystem.Analysis.InnerProductSpace.PartialTrace
public import QuantumSystem.InformationTheory.Entropy.VonNeumann.Basic
public import QuantumSystem.ForMathlib.LinearAlgebra.Trace

/-!
# Quantum mutual information

Let `H` and `K` be finite-dimensional complex Hilbert spaces and `ω` a state on
`B(H ⊗ K) = B(H) ⊗ B(K)`. Its **marginals** are the restrictions `ω_A = ω(· ⊗ 1)` and
`ω_B = ω(1 ⊗ ·)` (`State.traceRight`, `State.traceLeft`), the marginals `State.marginalLeft`,
`State.marginalRight` of `ω` as a state of `B(H) ⊗ₘᵢₙ B(K)`; their densities are the partial traces
of `ρ_ω` (`State.density_traceRight`). The **quantum mutual information** is
`I(A:B) = S(ω_A) + S(ω_B) - S(ω)` (`State.mutualInformation`), and it is the relative entropy of
`ω` with respect to the product of its marginals:
`D(ω ‖ ω_A ⊗ ω_B) = I(A:B)` (`State.umegakiEntropy_eq_mutualInformation`). In particular
`I(A:B) ≥ 0`, i.e. the von Neumann entropy is subadditive (`State.mutualInformation_nonneg`).

The **product** `ψ ⊗ φ` of positive functionals on `B(H)` and `B(K)` is the functional on
`B(H ⊗ K)` with `(ψ ⊗ φ)(A ⊗ B) = ψ(A) φ(B)` (`PositiveLinearMap.tensorProduct`): the product
functional `PositiveLinearMap.minTensorProduct` of the minimal tensor product, read through
`B(H) ⊗ₘᵢₙ B(K) ≃ B(H ⊗ K)` (`MinTensorProduct.continuousLinearMapEquiv`); its density is
`ρ_ψ ⊗ ρ_φ`.

## Conventions

`Tr` is the unnormalised trace `LinearMap.trace` (`Tr 1 = dim`), the trace of
`ContinuousLinearMap.density`: `ψ(A) = Tr(ρ_ψ A)`, so the density of a state has trace one.

## Main definitions

* `PositiveLinearMap.tensorProduct ψ φ` — the product functional `ψ ⊗ φ`;
  `State.tensorProduct ω₁ ω₂` — the product state. Both are the products of the minimal tensor
  product (`PositiveLinearMap.minTensorProduct`, `State.minTensorProduct`), read through
  `B(H) ⊗ₘᵢₙ B(K) ≃ B(H ⊗ K)`.
* `State.traceRight ω`, `State.traceLeft ω` — the marginals `ω_A`, `ω_B` of a state on
  `B(H ⊗ K)`, from `State.marginalLeft`, `State.marginalRight`.
* `State.mutualInformation ω` — `I(A:B) = S(ω_A) + S(ω_B) - S(ω)`.

## Main results

* `PositiveLinearMap.tensorProduct_mapL`, `PositiveLinearMap.density_tensorProduct` — the product
  functional on elementary tensors, and its density.
* `State.density_traceRight`, `State.density_traceLeft` — the marginals have the partial traces
  of `ρ_ω` as densities.
* `State.umegakiEntropy_eq_mutualInformation` — `D(ω ‖ ω_A ⊗ ω_B) = I(A:B)`.
* `State.mutualInformation_nonneg` — `0 ≤ I(A:B)`, subadditivity `S(ω) ≤ S(ω_A) + S(ω_B)`.

## TODO

The mutual information is stated on `B(H) ⊗ B(K) ≅ B(H ⊗ K)` (finite dimensions); the product
state and the marginals are already those of the minimal C\*-tensor product
(`State.minTensorProduct`, `State.marginalLeft`, `State.marginalRight`), read through
`MinTensorProduct.continuousLinearMapEquiv`. Still to do:

* Define the relative entropy of states of a C\*-algebra. It exists only for normal functionals of
  a von Neumann algebra (`VonNeumannAlgebra.arakiEntropy`), of which `umegakiEntropy` is the case
  `𝓑(H)`.
* Define the mutual information of a state `ω` of `A ⊗ₘᵢₙ B` as the relative entropy of `ω` with
  respect to `ω.marginalLeft.minTensorProduct ω.marginalRight`, and show that
  `State.mutualInformation` is the case `B(H) ⊗ₘᵢₙ B(K)`
  (`State.umegakiEntropy_eq_mutualInformation`).

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

namespace PositiveLinearMap

open scoped MinTensorProduct

/-- The **product functional** `ψ ⊗ φ` on `B(H ⊗ K)` of positive functionals on `B(H)` and `B(K)`:
the product functional `PositiveLinearMap.minTensorProduct` of the minimal tensor product, read on
`B(H ⊗ K)` through `B(H) ⊗ₘᵢₙ B(K) ≃ B(H ⊗ K)` (`MinTensorProduct.continuousLinearMapEquiv`). It
is determined by `(ψ ⊗ φ)(A ⊗ B) = ψ(A) φ(B)` (`PositiveLinearMap.tensorProduct_mapL`), and for
states it is the product state. -/
noncomputable def tensorProduct (ψ : (H →L[ℂ] H) →ₚ[ℂ] ℂ) (φ : (K →L[ℂ] K) →ₚ[ℂ] ℂ) :
    (H ⊗[ℂ] K →L[ℂ] H ⊗[ℂ] K) →ₚ[ℂ] ℂ :=
  (ψ.minTensorProduct φ).comp
    (PositiveLinearMap.ofClass (MinTensorProduct.continuousLinearMapEquiv H K).symm)

variable (ψ : (H →L[ℂ] H) →ₚ[ℂ] ℂ) (φ : (K →L[ℂ] K) →ₚ[ℂ] ℂ)

/-- The product functional on `B(H ⊗ K)` is `PositiveLinearMap.minTensorProduct` after the inverse
of `MinTensorProduct.continuousLinearMapEquiv`. -/
lemma tensorProduct_eq_minTensorProduct (Z : H ⊗[ℂ] K →L[ℂ] H ⊗[ℂ] K) :
    ψ.tensorProduct φ Z =
      ψ.minTensorProduct φ ((MinTensorProduct.continuousLinearMapEquiv H K).symm Z) := by
  simp only [tensorProduct, PositiveLinearMap.comp_apply, coe_toLinearMap, coe_ofClass]

/-- The product functional on `B(H ⊗ K)` is the product functional of the minimal tensor product,
under `B(H) ⊗ₘᵢₙ B(K) ≃ B(H ⊗ K)` (`MinTensorProduct.continuousLinearMapEquiv`). -/
lemma tensorProduct_continuousLinearMapEquiv (T : (H →L[ℂ] H) ⊗ₘᵢₙ (K →L[ℂ] K)) :
    ψ.tensorProduct φ (MinTensorProduct.continuousLinearMapEquiv H K T) =
      ψ.minTensorProduct φ T := by
  rw [tensorProduct_eq_minTensorProduct, StarAlgEquiv.symm_apply_apply]

/-- **The product functional on elementary tensors**: `(ψ ⊗ φ)(A ⊗ B) = ψ(A) φ(B)`. -/
@[simp] lemma tensorProduct_mapL (A : H →L[ℂ] H) (B : K →L[ℂ] K) :
    ψ.tensorProduct φ (mapL A B) = ψ A * φ B := by
  rw [← MinTensorProduct.continuousLinearMapEquiv_of_tmul, tensorProduct_continuousLinearMapEquiv,
    minTensorProduct_of_tmul]

/-- The product functional is `Z ↦ tr((ρ_ψ ⊗ ρ_φ) Z)`: both are linear and agree on the elementary
tensors `A ⊗ B` (`TensorProduct.ext_mapL`), where they are `ψ(A) φ(B)`. -/
lemma tensorProduct_apply (Z : H ⊗[ℂ] K →L[ℂ] H ⊗[ℂ] K) :
    ψ.tensorProduct φ Z = Tr (mapL (density ψ) (density φ) ∘L Z) := by
  have h := ext_mapL (𝕜 := ℂ) (E := H) (F := H) (G := K) (H := K) (M := ℂ)
    (u := (ψ.tensorProduct φ).toLinearMap)
    (v := (LinearMap.trace ℂ (H ⊗[ℂ] K) ∘ₗ coeLM ℂ) ∘ₗ
      LinearMap.mulLeft ℂ (mapL (density ψ) (density φ))) fun A B => by
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply, coeLM_apply,
      mul_def, ← mapL_comp, trace_mapL, trace_density_comp]
    exact tensorProduct_mapL ψ φ A B
  exact LinearMap.congr_fun h Z

/-- The density of the product functional is the tensor product of the densities. -/
lemma density_tensorProduct : density (ψ.tensorProduct φ) = mapL (density ψ) (density φ) := by
  rw [eq_comm, eq_density_iff]
  exact fun Z => (tensorProduct_apply ψ φ Z).symm

end PositiveLinearMap

namespace State

open scoped MinTensorProduct in
/-- The **product state** `ω₁ ⊗ ω₂` on `B(H ⊗ K)` of states on `B(H)` and `B(K)`: the product state
`State.minTensorProduct` of the minimal tensor product, read on `B(H ⊗ K)` through
`B(H) ⊗ₘᵢₙ B(K) ≃ B(H ⊗ K)` (`MinTensorProduct.continuousLinearMapEquiv`). It is determined by
`(ω₁ ⊗ ω₂)(A ⊗ B) = ω₁(A) ω₂(B)` (`State.tensorProduct_mapL`). -/
noncomputable def tensorProduct (ω₁ : State (H →L[ℂ] H)) (ω₂ : State (K →L[ℂ] K)) :
    State (H ⊗[ℂ] K →L[ℂ] H ⊗[ℂ] K) :=
  (ω₁.minTensorProduct ω₂).comp (MinTensorProduct.continuousLinearMapEquiv H K).symm (map_one _)

/-- The positive functional underlying a product state is the product of the underlying
positive functionals. -/
@[simp] lemma ofClass_tensorProduct (ω₁ : State (H →L[ℂ] H)) (ω₂ : State (K →L[ℂ] K)) :
    PositiveLinearMap.ofClass (ω₁.tensorProduct ω₂) =
      (PositiveLinearMap.ofClass ω₁).tensorProduct (PositiveLinearMap.ofClass ω₂) := by
  rw [tensorProduct, State.ofClass_comp, State.ofClass_minTensorProduct]
  rfl

open scoped MinTensorProduct in
/-- The product state on `B(H ⊗ K)` is the product state of the minimal tensor product, under
`B(H) ⊗ₘᵢₙ B(K) ≃ B(H ⊗ K)` (`MinTensorProduct.continuousLinearMapEquiv`). -/
lemma tensorProduct_continuousLinearMapEquiv (ω₁ : State (H →L[ℂ] H)) (ω₂ : State (K →L[ℂ] K))
    (T : (H →L[ℂ] H) ⊗ₘᵢₙ (K →L[ℂ] K)) :
    ω₁.tensorProduct ω₂ (MinTensorProduct.continuousLinearMapEquiv H K T) =
      ω₁.minTensorProduct ω₂ T := by
  rw [tensorProduct, State.comp_apply, StarAlgEquiv.symm_apply_apply]

/-- **The product state on elementary tensors**: `(ω₁ ⊗ ω₂)(A ⊗ B) = ω₁(A) ω₂(B)`. -/
@[simp] lemma tensorProduct_mapL (ω₁ : State (H →L[ℂ] H)) (ω₂ : State (K →L[ℂ] K))
    (A : H →L[ℂ] H) (B : K →L[ℂ] K) : ω₁.tensorProduct ω₂ (mapL A B) = ω₁ A * ω₂ B := by
  rw [← MinTensorProduct.continuousLinearMapEquiv_of_tmul, tensorProduct_continuousLinearMapEquiv,
    minTensorProduct_of_tmul]

/-- The density of the product state is the tensor product of the densities. -/
lemma density_tensorProduct (ω₁ : State (H →L[ℂ] H)) (ω₂ : State (K →L[ℂ] K)) :
    density (ω₁.tensorProduct ω₂) = mapL (density ω₁) (density ω₂) := by
  have h₁ : density (PositiveLinearMap.ofClass ω₁) = density ω₁ :=
    density_eq_density_iff.mpr fun _ => rfl
  have h₂ : density (PositiveLinearMap.ofClass ω₂) = density ω₂ :=
    density_eq_density_iff.mpr fun _ => rfl
  rw [← h₁, ← h₂, eq_comm, eq_density_iff]
  exact fun Z => ((DFunLike.congr_fun (ofClass_tensorProduct ω₁ ω₂) Z).trans
    (PositiveLinearMap.tensorProduct_apply (PositiveLinearMap.ofClass ω₁)
      (PositiveLinearMap.ofClass ω₂) Z)).symm

end State

/-! ### Marginals and mutual information -/

namespace State

variable (ω : State (H ⊗[ℂ] K →L[ℂ] H ⊗[ℂ] K))

open scoped MinTensorProduct in
/-- The **marginal** `ω_A = ω(· ⊗ 1)` of a state on `B(H ⊗ K)` on the first factor: the marginal
`State.marginalLeft` of `ω` read on `B(H) ⊗ₘᵢₙ B(K)` through
`MinTensorProduct.continuousLinearMapEquiv`. Its density is the partial trace `tr_K ρ_ω`
(`State.density_traceRight`). -/
noncomputable def traceRight : State (H →L[ℂ] H) :=
  (ω.comp (MinTensorProduct.continuousLinearMapEquiv H K) (map_one _)).marginalLeft

open scoped MinTensorProduct in
/-- The **marginal** `ω_B = ω(1 ⊗ ·)` of a state on `B(H ⊗ K)` on the second factor: the marginal
`State.marginalRight` of `ω` read on `B(H) ⊗ₘᵢₙ B(K)` through
`MinTensorProduct.continuousLinearMapEquiv`. -/
noncomputable def traceLeft : State (K →L[ℂ] K) :=
  (ω.comp (MinTensorProduct.continuousLinearMapEquiv H K) (map_one _)).marginalRight

/-- `traceRight` evaluates `ω` on the amplification `A ↦ A ⊗ 1`. -/
@[simp] lemma traceRight_apply (A : H →L[ℂ] H) : ω.traceRight A = ω (A.rTensor K) := by
  rw [traceRight, marginalLeft_apply, comp_apply, MinTensorProduct.continuousLinearMapEquiv_of_tmul,
    rTensor_eq_mapL]
  rfl

/-- `traceLeft` evaluates `ω` on the amplification `B ↦ 1 ⊗ B`. -/
@[simp] lemma traceLeft_apply (B : K →L[ℂ] K) : ω.traceLeft B = ω (B.lTensor H) := by
  rw [traceLeft, marginalRight_apply, comp_apply, MinTensorProduct.continuousLinearMapEquiv_of_tmul,
    lTensor_eq_mapL]
  rfl

/-- The marginals of the product state are its factors. -/
@[simp] lemma traceRight_tensorProduct (ω₁ : State (H →L[ℂ] H)) (ω₂ : State (K →L[ℂ] K)) :
    (ω₁.tensorProduct ω₂).traceRight = ω₁ := by
  ext A
  rw [traceRight_apply, rTensor_eq_mapL, tensorProduct_mapL]
  exact (congrArg (ω₁ A * ·) ω₂.apply_one).trans (mul_one _)

@[simp, inherit_doc traceRight_tensorProduct]
lemma traceLeft_tensorProduct (ω₁ : State (H →L[ℂ] H)) (ω₂ : State (K →L[ℂ] K)) :
    (ω₁.tensorProduct ω₂).traceLeft = ω₂ := by
  ext B
  rw [traceLeft_apply, lTensor_eq_mapL, tensorProduct_mapL]
  exact (congrArg (· * ω₂ B) ω₁.apply_one).trans (one_mul _)

/-- The density of the marginal `ω_A` is the partial trace `tr_K ρ_ω`. -/
lemma density_traceRight :
    density ω.traceRight = ContinuousLinearMap.traceRight H K (density ω) :=
  density_eq_traceDual (rTensorStarAlgHom ℂ H K) fun A => traceRight_apply ω A

/-- The density of the marginal `ω_B` is the partial trace `tr₁(ρ_ω)` of `ρ_ω` over the first
factor. -/
lemma density_traceLeft :
    density ω.traceLeft = ContinuousLinearMap.traceLeft H K (density ω) :=
  density_eq_traceDual (lTensorStarAlgHom ℂ K H) fun B => traceLeft_apply ω B

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
