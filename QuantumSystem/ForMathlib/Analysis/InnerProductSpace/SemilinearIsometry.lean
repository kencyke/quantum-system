/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Inner products under semilinear isometries

The isometric ring endomorphisms of `ℂ` are the identity and the complex conjugation
(`Complex.ringHom_eq_id_or_conj_of_continuous`). A `σ`-semilinear isometry `V` between complex
inner product spaces, for such a `σ`, transforms inner products by `σ`:
`⟪V x, V y⟫ = σ ⟪x, y⟫`. For `σ = id` this is Mathlib's `LinearIsometry.inner_map_map`; for the
complex conjugation it is the defining property `⟪J x, J y⟫ = conj ⟪x, y⟫` of an antiunitary `J`.

## Main results

* `RingHom.eq_id_or_conj_of_isometric`, `RingHom.eq_id_or_conj_of_ringHomIsometric` — an isometric
  ring endomorphism `σ` of `ℂ`, and its inverse `σ'`, are the identity or the conjugation.
* `RingHom.norm_apply_of_ringHomInvPair`, `RingHom.continuous_of_ringHomInvPair`,
  `RingHom.apply_ofReal_of_ringHomInvPair`, `RingHom.apply_I_of_ringHomIsometric` — consequences:
  `σ'` is isometric and continuous, fixes the reals, and `σ i = ± i`, `σ' i = ± i`.
* `LinearIsometry.inner_map_mapₛₗ`, `LinearIsometryEquiv.inner_map_mapₛₗ` —
  `⟪V x, V y⟫ = σ ⟪x, y⟫`.
-/

@[expose] public section

open Complex
open scoped InnerProductSpace ComplexConjugate

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
