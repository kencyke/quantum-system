/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Polarization with the operator on the right

Mathlib's `inner_map_polarization` recovers `⟪T y, x⟫` from the quadratic form `⟪T u, u⟫`. This file
gives the variant with the operator on the right: `⟪x, G y⟫` from `q(u) = ⟪u, G u⟫`, the form in
which scalar spectral measures `ν_u(g) = ⟪u, g(T) u⟫` are polarized into complex ones. As a
consequence, the norm of an operator is at most twice its numerical radius.

## Main results

* `ContinuousLinearMap.inner_apply_eq_polarization` —
  `⟪x, G y⟫ = ¼ (q(x+y) - q(x-y)) + i ¼ (q(x-iy) - q(x+iy))` with `q(u) = ⟪u, G u⟫`.
* `ContinuousLinearMap.norm_apply_le_of_norm_inner_self_le` — if `|⟪w, A w⟫| ≤ M ‖w‖²` for every
  `w`, then `‖A y‖ ≤ 2 M ‖y‖`.
* `ContinuousLinearMap.nonneg_iff_inner_nonneg` — on a complex inner product space an operator is
  nonnegative iff its quadratic form is, `0 ≤ ⟪x, T x⟫` in `ℂ`; self-adjointness comes for free.
-/

@[expose] public section

open Complex
open scoped InnerProductSpace ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Polarization** for an arbitrary operator `G`:
`⟪x, G y⟫ = ¼ (q(x+y) - q(x-y)) + i ¼ (q(x-iy) - q(x+iy))` with `q(u) = ⟪u, G u⟫`. -/
lemma ContinuousLinearMap.inner_apply_eq_polarization {G : E →L[ℂ] E} (x y : E) :
    ⟪x, G y⟫_ℂ = (4⁻¹ : ℝ) • (⟪x + y, G (x + y)⟫_ℂ - ⟪x - y, G (x - y)⟫_ℂ) +
      I * (4⁻¹ : ℝ) • (⟪x - I • y, G (x - I • y)⟫_ℂ - ⟪x + I • y, G (x + I • y)⟫_ℂ) := by
  simp only [map_add, map_sub, map_smul, inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right, inner_smul_left, inner_smul_right, conj_I, Complex.real_smul]
  ring_nf
  rw [I_sq]
  push_cast
  ring

/-- If `|⟪w, A w⟫| ≤ M ‖w‖²` for every `w`, then `|⟪x, A y⟫| ≤ M (‖x‖² + ‖y‖²)`, by polarization
and the parallelogram law. -/
lemma ContinuousLinearMap.norm_inner_apply_le_of_norm_inner_self_le (A : E →L[ℂ] E) {M : ℝ}
    (hM : ∀ w, ‖⟪w, A w⟫_ℂ‖ ≤ M * ‖w‖ ^ 2) (x y : E) :
    ‖⟪x, A y⟫_ℂ‖ ≤ M * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  rw [A.inner_apply_eq_polarization x y]
  have h1 := parallelogram_law_with_norm ℂ x y
  have h2 := parallelogram_law_with_norm ℂ x (I • y)
  rw [norm_smul, norm_I, one_mul] at h2
  calc ‖(4⁻¹ : ℝ) • (⟪x + y, A (x + y)⟫_ℂ - ⟪x - y, A (x - y)⟫_ℂ) +
        I * (4⁻¹ : ℝ) • (⟪x - I • y, A (x - I • y)⟫_ℂ - ⟪x + I • y, A (x + I • y)⟫_ℂ)‖
      ≤ 4⁻¹ * (‖⟪x + y, A (x + y)⟫_ℂ‖ + ‖⟪x - y, A (x - y)⟫_ℂ‖) +
        4⁻¹ * (‖⟪x - I • y, A (x - I • y)⟫_ℂ‖ + ‖⟪x + I • y, A (x + I • y)⟫_ℂ‖) := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
          gcongr
          exact norm_sub_le _ _
        · rw [norm_mul, norm_I, one_mul, norm_smul, Real.norm_of_nonneg (by norm_num)]
          gcongr
          exact norm_sub_le _ _
    _ ≤ 4⁻¹ * (M * ‖x + y‖ ^ 2 + M * ‖x - y‖ ^ 2) +
        4⁻¹ * (M * ‖x - I • y‖ ^ 2 + M * ‖x + I • y‖ ^ 2) := by
        gcongr <;> exact hM _
    _ = M * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
        linear_combination (M / 4) * h1 + (M / 4) * h2

/-- **Norm and numerical radius**: if `|⟪w, A w⟫| ≤ M ‖w‖²` for every `w`, then
`‖A y‖ ≤ 2 M ‖y‖`. -/
lemma ContinuousLinearMap.norm_apply_le_of_norm_inner_self_le (A : E →L[ℂ] E) {M : ℝ}
    (hM : ∀ w, ‖⟪w, A w⟫_ℂ‖ ≤ M * ‖w‖ ^ 2) (y : E) : ‖A y‖ ≤ 2 * M * ‖y‖ := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hy' : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hM0 : 0 ≤ M := by
    have h := (norm_nonneg _).trans (hM y)
    exact nonneg_of_mul_nonneg_left h (by positivity)
  rcases eq_or_ne (A y) 0 with h0 | h0
  · rw [h0, norm_zero]
    positivity
  have hAy : 0 < ‖A y‖ := norm_pos_iff.mpr h0
  set t : ℝ := ‖y‖ / ‖A y‖
  have h := A.norm_inner_apply_le_of_norm_inner_self_le hM ((t : ℂ) • A y) y
  have ht0 : 0 ≤ t := by positivity
  rw [inner_smul_left, conj_ofReal, inner_self_eq_norm_sq_to_K, norm_mul, norm_smul,
    Complex.norm_real, Real.norm_of_nonneg ht0, norm_pow] at h
  simp only [RCLike.norm_ofReal, abs_norm] at h
  have ht : t * ‖A y‖ = ‖y‖ := div_mul_cancel₀ _ hAy.ne'
  have : t * ‖A y‖ ^ 2 = ‖y‖ * ‖A y‖ := by rw [sq, ← mul_assoc, ht]
  rw [this, ht] at h
  nlinarith

open scoped ComplexOrder in
/-- On a complex inner product space an operator is nonnegative (positive in the Loewner order)
iff its quadratic form is nonnegative, `0 ≤ ⟪x, T x⟫` in the order of `ℂ`; self-adjointness comes
for free, since the quadratic form is real (`ContinuousLinearMap.isPositive_iff_complex`). -/
theorem ContinuousLinearMap.nonneg_iff_inner_nonneg {T : E →L[ℂ] E} :
    0 ≤ T ↔ ∀ x, 0 ≤ ⟪x, T x⟫_ℂ := by
  refine ⟨fun h x => (nonneg_iff_isPositive.1 h).inner_nonneg_right x, fun h => ?_⟩
  rw [nonneg_iff_isPositive, isPositive_iff_complex]
  intro x
  obtain ⟨h₁, h₂⟩ := Complex.nonneg_iff.mp (h x)
  rw [← inner_conj_symm]
  generalize ⟪x, T x⟫_ℂ = z at h₁ h₂ ⊢
  exact ⟨Complex.ext (by simp) (by simp [← h₂]), by simpa using h₁⟩
