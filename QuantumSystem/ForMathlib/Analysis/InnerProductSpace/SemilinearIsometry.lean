/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.StandardSubspace

/-!
# Inner products under semilinear isometries

The isometric ring endomorphisms of `ℂ` are the identity and the complex conjugation
(`Complex.ringHom_eq_id_or_conj_of_continuous`). A `σ`-semilinear isometry `V` between complex
inner product spaces, for such a `σ`, transforms inner products by `σ`:
`⟪V x, V y⟫ = σ ⟪x, y⟫`. For `σ = id` this is Mathlib's `LinearIsometry.inner_map_map`; for the
complex conjugation it is the defining property `⟪J x, J y⟫ = conj ⟪x, y⟫` of an antiunitary `J`.

## Main definitions

* `ContinuousLinearMap.toRealCLM` — a bounded `σ`-semilinear map as a bounded real-linear map; the
  coercion `(U : E →L[ℝ] F)` of a conjugate-linear `U`.

## Main results

* `RingHom.eq_id_or_conj_of_isometric`, `RingHom.eq_id_or_conj_of_ringHomIsometric` — an isometric
  ring endomorphism `σ` of `ℂ`, and its inverse `σ'`, are the identity or the conjugation.
* `RingHom.norm_apply_of_ringHomInvPair`, `RingHom.continuous_of_ringHomInvPair`,
  `RingHom.apply_ofReal_of_ringHomInvPair`, `RingHom.apply_I_of_ringHomIsometric` — consequences:
  `σ'` is isometric and continuous, fixes the reals, and `σ i = ± i`, `σ' i = ± i`.
* `LinearIsometry.inner_map_mapₛₗ`, `LinearIsometryEquiv.inner_map_mapₛₗ` —
  `⟪V x, V y⟫ = σ ⟪x, y⟫`.
* `ContinuousLinearMap.adjoint_restrictScalars` — the real adjoint of a complex-linear map is its
  complex adjoint.
* `ContinuousLinearMap.adjoint_map_smul_of_map_smul` — the real adjoint `U†` of a real-linear `U`
  with `U (c • x) = σ c • U x` satisfies `U† (c • y) = σ' c • U† y`.
-/

@[expose] public section

open Complex
open scoped InnerProductSpace InnerProduct ComplexConjugate

/-! ### Isometric ring endomorphisms of `ℂ` -/

section RingHom

variable {σ σ' : ℂ →+* ℂ}

/-- An isometric ring endomorphism of `ℂ` is the identity or the complex conjugation. -/
lemma RingHom.eq_id_or_conj_of_isometric (σ : ℂ →+* ℂ) [RingHomIsometric σ] :
    σ = RingHom.id ℂ ∨ σ = starRingEnd ℂ :=
  Complex.ringHom_eq_id_or_conj_of_continuous
    (AddMonoidHomClass.isometry_of_norm σ fun _ => RingHomIsometric.norm_map).continuous

/-- An isometric ring endomorphism of `ℂ` with inverse `σ'` is the identity or the complex
conjugation, and so is `σ'`. -/
lemma RingHom.eq_id_or_conj_of_ringHomIsometric [RingHomInvPair σ σ'] [RingHomIsometric σ] :
    (σ = RingHom.id ℂ ∧ σ' = RingHom.id ℂ) ∨ (σ = starRingEnd ℂ ∧ σ' = starRingEnd ℂ) := by
  rcases RingHom.eq_id_or_conj_of_isometric σ with rfl | rfl
  · refine Or.inl ⟨rfl, RingHom.ext fun x => ?_⟩
    simpa using (RingHomInvPair.comp_apply_eq₂ (σ := RingHom.id ℂ) (σ' := σ') (x := x))
  · refine Or.inr ⟨rfl, RingHom.ext fun x => ?_⟩
    have h := congrArg (starRingEnd ℂ)
      (RingHomInvPair.comp_apply_eq₂ (σ := starRingEnd ℂ) (σ' := σ') (x := x))
    rwa [Complex.conj_conj] at h

/-- The inverse of an isometric ring endomorphism of `ℂ` is isometric. -/
lemma RingHom.norm_apply_of_ringHomInvPair (σ : ℂ →+* ℂ) [RingHomInvPair σ σ']
    [RingHomIsometric σ] (z : ℂ) : ‖σ' z‖ = ‖z‖ := by
  rcases RingHom.eq_id_or_conj_of_ringHomIsometric (σ := σ) (σ' := σ') with
    ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp

/-- The inverse of an isometric ring endomorphism of `ℂ` is continuous. -/
lemma RingHom.continuous_of_ringHomInvPair (σ : ℂ →+* ℂ) [RingHomInvPair σ σ']
    [RingHomIsometric σ] : Continuous σ' := by
  rcases RingHom.eq_id_or_conj_of_ringHomIsometric (σ := σ) (σ' := σ') with
    ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact continuous_id
  · exact Complex.continuous_conj

/-- The inverse of an isometric ring endomorphism of `ℂ` fixes the reals. -/
lemma RingHom.apply_ofReal_of_ringHomInvPair (σ : ℂ →+* ℂ) [RingHomInvPair σ σ']
    [RingHomIsometric σ] (r : ℝ) : σ' r = r := by
  rcases RingHom.eq_id_or_conj_of_ringHomIsometric (σ := σ) (σ' := σ') with
    ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp

/-- `σ i = ± i` and `σ' i = ± i` for an isometric ring endomorphism `σ` of `ℂ` with inverse
`σ'`. -/
lemma RingHom.apply_I_of_ringHomIsometric [RingHomInvPair σ σ'] [RingHomIsometric σ] :
    (σ Complex.I = Complex.I ∨ σ Complex.I = -Complex.I) ∧
      (σ' Complex.I = Complex.I ∨ σ' Complex.I = -Complex.I) := by
  rcases RingHom.eq_id_or_conj_of_ringHomIsometric (σ := σ) (σ' := σ') with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

end RingHom

/-! ### Semilinear maps as real-linear maps -/

section ToRealCLM

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F] {σ : ℂ →+* ℂ}

/-- A bounded `σ`-semilinear map between complex normed spaces, as a bounded real-linear map: a
continuous additive map is `ℝ`-linear (`AddMonoidHom.toRealLinearMap`). For a conjugate-linear
map this is the coercion `(U : E →L[ℝ] F)`; complex-linear maps keep Mathlib's
`ContinuousLinearMap.restrictScalars ℝ`. -/
@[coe]
noncomputable def ContinuousLinearMap.toRealCLM (U : E →SL[σ] F) : E →L[ℝ] F :=
  (U : E →+ F).toRealLinearMap U.continuous

/-- `U.toRealCLM` is `U` as a function. -/
@[simp]
lemma ContinuousLinearMap.toRealCLM_apply (U : E →SL[σ] F) (x : E) : U.toRealCLM x = U x := rfl

/-- A bounded conjugate-linear map is a bounded real-linear map. -/
noncomputable instance ContinuousLinearMap.instCoeToRealCLM : Coe (E →L⋆[ℂ] F) (E →L[ℝ] F) :=
  ⟨ContinuousLinearMap.toRealCLM⟩

end ToRealCLM

/-! ### Inner products -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F]
  [InnerProductSpace ℂ F] {σ : ℂ →+* ℂ} [RingHomIsometric σ]

/-- A semilinear isometry for an isometric ring endomorphism `σ` of `ℂ` transforms inner products
by `σ`: `⟪V x, V y⟫ = σ ⟪x, y⟫`. -/
theorem LinearIsometry.inner_map_mapₛₗ (V : E →ₛₗᵢ[σ] F) (x y : E) :
    ⟪V x, V y⟫_ℂ = σ ⟪x, y⟫_ℂ := by
  rcases RingHom.eq_id_or_conj_of_isometric σ with rfl | rfl
  · exact V.inner_map_map x y
  · have hI : Complex.I • V y = V (-Complex.I • y) := by
      rw [V.map_smulₛₗ, map_neg, conj_I, neg_neg]
    have hre : (⟪V x, V y⟫_ℂ).re = (⟪x, y⟫_ℂ).re := by
      have h₁ := re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four (𝕜 := ℂ) (V x) (V y)
      have h₂ := re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four (𝕜 := ℂ) x y
      rw [← map_add, ← map_sub, V.norm_map, V.norm_map] at h₁
      simpa [← h₂] using h₁
    have him : (⟪V x, V y⟫_ℂ).im = -(⟪x, y⟫_ℂ).im := by
      have h₁ := im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four
        (𝕜 := ℂ) (V x) (V y)
      have h₂ := im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four
        (𝕜 := ℂ) x y
      simp only [RCLike.I_to_complex] at h₁ h₂
      rw [hI, ← map_sub, ← map_add, V.norm_map, V.norm_map, neg_smul, sub_neg_eq_add,
        ← sub_eq_add_neg] at h₁
      simp only [RCLike.im_to_complex] at h₁ h₂
      rw [h₁, h₂]
      ring
    apply Complex.ext
    · rw [conj_re]
      exact hre
    · rw [conj_im]
      exact him

/-- A semilinear isometric equivalence for an isometric ring endomorphism `σ` of `ℂ` transforms
inner products by `σ`: `⟪V x, V y⟫ = σ ⟪x, y⟫`. -/
theorem LinearIsometryEquiv.inner_map_mapₛₗ {σ' : ℂ →+* ℂ} [RingHomInvPair σ σ']
    [RingHomInvPair σ' σ] (V : E ≃ₛₗᵢ[σ] F) (x y : E) : ⟪V x, V y⟫_ℂ = σ ⟪x, y⟫_ℂ :=
  V.toLinearIsometry.inner_map_mapₛₗ x y

/-! ### Real adjoints of semilinear maps -/

open ClosedSubmodule

/-- **The real adjoint of a complex-linear map is its complex adjoint**: for the real inner
products `re ⟪·, ·⟫`, `(U ℝ)† = (U†) ℝ`. -/
lemma ContinuousLinearMap.adjoint_restrictScalars [CompleteSpace E] [CompleteSpace F]
    (U : E →L[ℂ] F) :
    ((U.restrictScalars ℝ)†) = (U†).restrictScalars ℝ :=
  ContinuousLinearMap.ext fun y => ext_inner_right ℝ fun x => by
    rw [ContinuousLinearMap.adjoint_inner_left, inner_real_eq_re_inner, inner_real_eq_re_inner,
      ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.adjoint_inner_left]

/-- The real adjoint of a semilinear map, for an isometric `σ`. -/
private lemma ContinuousLinearMap.adjoint_map_smul_of_map_smul_of_isometric [CompleteSpace E]
    [CompleteSpace F] {σ' : ℂ →+* ℂ} [RingHomInvPair σ σ'] (U : E →L[ℝ] F)
    (hU : ∀ (c : ℂ) x, U (c • x) = σ c • U x) (c : ℂ) (y : F) :
    (U†) (c • y) = σ' c • (U†) y := by
  -- `re (d ⟪U† y, x⟫) = re (σ d ⟪y, U x⟫)`
  have key : ∀ (d : ℂ) (y : F) (x : E),
      (d * ⟪(U†) y, x⟫_ℂ).re = (σ d * ⟪y, U x⟫_ℂ).re := fun d y x => by
    rw [← inner_smul_right, ← inner_real_eq_re_inner, ContinuousLinearMap.adjoint_inner_left, hU,
      inner_real_eq_re_inner, inner_smul_right]
  refine ext_inner_right ℝ fun x => ?_
  rw [inner_real_eq_re_inner, inner_real_eq_re_inner, inner_smul_left, ← one_mul (⟪_, x⟫_ℂ),
    key, map_one, one_mul, inner_smul_left, key]
  rcases RingHom.eq_id_or_conj_of_ringHomIsometric (σ := σ) (σ' := σ') with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

omit [RingHomIsometric σ] in
/-- The **real adjoint of a semilinear map is semilinear**: for a bounded real-linear `U` between
complex Hilbert spaces with `U (c • x) = σ c • U x`, the adjoint `U†` for the real inner products
`re ⟪·, ·⟫` satisfies `U† (c • y) = σ' c • U† y`. For `σ = id` this says that the real adjoint of a
complex-linear map is complex-linear; for the conjugation, that the real adjoint of a
conjugate-linear map is conjugate-linear. No continuity of `σ` is assumed: for `U ≠ 0` it follows
from that of `U`, so that `σ` is the identity or the conjugation. The real inner products are
Mathlib's scoped instance `ClosedSubmodule.instInnerProductSpaceReal`, which is why this file
imports `Mathlib.Analysis.InnerProductSpace.StandardSubspace`. -/
lemma ContinuousLinearMap.adjoint_map_smul_of_map_smul [CompleteSpace E] [CompleteSpace F]
    {σ' : ℂ →+* ℂ} [RingHomInvPair σ σ'] (U : E →L[ℝ] F) (hU : ∀ (c : ℂ) x, U (c • x) = σ c • U x)
    (c : ℂ) (y : F) :
    (U†) (c • y) = σ' c • (U†) y := by
  by_cases h0 : ∀ x, U x = 0
  · have hU0 : U = 0 := ContinuousLinearMap.ext h0
    simp [hU0]
  push Not at h0
  obtain ⟨x, hx⟩ := h0
  -- `σ c = ⟪U x, U (c • x)⟫ / ‖U x‖²` is continuous in `c`
  have hσc : Continuous σ := by
    have h : ∀ c : ℂ, σ c = ⟪U x, U (c • x)⟫_ℂ / (‖U x‖ ^ 2 : ℂ) := fun c => by
      have hn : (‖U x‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx)
      rw [hU, inner_smul_right, inner_self_eq_norm_sq_to_K]
      field_simp
      rfl
    simp_rw [funext h]
    fun_prop
  have : RingHomIsometric σ := by
    rcases Complex.ringHom_eq_id_or_conj_of_continuous hσc with rfl | rfl
    · exact RingHomIsometric.ids
    · exact ⟨fun {z} => by simp⟩
  exact ContinuousLinearMap.adjoint_map_smul_of_map_smul_of_isometric U hU c y
