module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Phase-aligned triangle inequality for `1 - ‖⟪⋅, ⋅⟫_ℂ‖`

This file proves the von Neumann / Bratteli–Robinson "C₀-triangle"
inequality for unit vectors in a complex inner-product space:

`1 - ‖⟪u, w⟫_ℂ‖ ≤ 2 (1 - ‖⟪u, v⟫_ℂ‖) + 2 (1 - ‖⟪v, w⟫_ℂ‖)`

The proof aligns phases via a unit complex scalar `c` so that
`⟪u, c • v⟫_ℂ` is real and non-negative, applies the parallelogram-style
bound `(a + b)² ≤ 2 a² + 2 b²` to the squared norms, and exploits
`Re z ≤ ‖z‖` to upper-bound `1 - ‖⟪u, w⟫_ℂ‖` by half the squared norm
`‖u - νw‖²`.

The result powers the transitivity of the Bratteli–Robinson C₀-equivalence
on unit-vector reference families used to decompose the complete infinite
tensor product.

## Main results

* `inner_phase_aligned` — for any `u, v : E`, there exists a unit `c : ℂ`
  with `⟪u, c • v⟫_ℂ = (‖⟪u, v⟫_ℂ‖ : ℂ)`.
* `c0_triangle` — the phase-aligned triangle inequality stated above.
-/

@[expose] public section

open scoped InnerProductSpace

namespace ForMathlib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- For any vectors `u, v` in a complex inner product space, there exists a
unit complex scalar `c` whose action aligns the inner product
`⟪u, c • v⟫_ℂ` with the non-negative real `‖⟪u, v⟫_ℂ‖ : ℂ`.

Concretely, `c = conj ⟪u, v⟫_ℂ / ‖⟪u, v⟫_ℂ‖` when `⟪u, v⟫_ℂ ≠ 0`, else
`c = 1`. -/
theorem inner_phase_aligned (u v : E) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ⟪u, c • v⟫_ℂ = ((‖⟪u, v⟫_ℂ‖ : ℝ) : ℂ) := by
  by_cases h : ⟪u, v⟫_ℂ = 0
  · refine ⟨1, by simp, ?_⟩
    rw [one_smul, h, norm_zero]
    simp
  · refine ⟨(starRingEnd ℂ) ⟪u, v⟫_ℂ / ((‖⟪u, v⟫_ℂ‖ : ℝ) : ℂ), ?_, ?_⟩
    · rw [norm_div, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg _),
          div_self (norm_ne_zero_iff.mpr h)]
    · rw [inner_smul_right]
      have hne : ((‖⟪u, v⟫_ℂ‖ : ℝ) : ℂ) ≠ 0 := by
        rw [Ne, Complex.ofReal_eq_zero, norm_eq_zero]
        exact h
      field_simp
      have hcm : (starRingEnd ℂ) ⟪u, v⟫_ℂ * ⟪u, v⟫_ℂ
          = ((‖⟪u, v⟫_ℂ‖ : ℝ) : ℂ) ^ 2 := by
        exact_mod_cast RCLike.conj_mul (K := ℂ) ⟪u, v⟫_ℂ
      rw [hcm, sq]

/-- For unit vectors `u, v` in a complex inner-product space and the
phase-aligned scalar `c` from `inner_phase_aligned`, the squared norm of the
phase-aligned difference equals `2 (1 - ‖⟪u, v⟫_ℂ‖)`. -/
theorem norm_sub_phase_aligned_sq (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      ‖u - c • v‖ ^ 2 = 2 * (1 - ‖⟪u, v⟫_ℂ‖) := by
  obtain ⟨c, hc1, hc2⟩ := inner_phase_aligned u v
  refine ⟨c, hc1, ?_⟩
  rw [@norm_sub_sq ℂ _ _ _ _ u (c • v), hu, norm_smul, hc1, hv]
  rw [hc2]
  simp
  ring

/-- The complex-IPS C₀-triangle inequality: for unit `u, v, w`,
`1 - ‖⟪u, w⟫_ℂ‖ ≤ 2 (1 - ‖⟪u, v⟫_ℂ‖) + 2 (1 - ‖⟪v, w⟫_ℂ‖)`.

Phase-align the `(u, v)` pair via `c` and the `(c • v, w)` pair via `d`,
giving exact equalities `‖u - c • v‖² = 2(1 - ‖⟪u, v⟫_ℂ‖)` and
`‖c • v - d • w‖² = 2(1 - ‖⟪v, w⟫_ℂ‖)` (using `|c| = 1`).  Triangle and
the bound `(a + b)² ≤ 2 a² + 2 b²` give an upper bound on `‖u - d • w‖²`,
which is in turn bounded below by `2(1 - ‖⟪u, w⟫_ℂ‖)` via `Re z ≤ ‖z‖`. -/
theorem c0_triangle (u v w : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    1 - ‖⟪u, w⟫_ℂ‖ ≤ 2 * (1 - ‖⟪u, v⟫_ℂ‖) + 2 * (1 - ‖⟪v, w⟫_ℂ‖) := by
  obtain ⟨c, hc1, hcuv⟩ := norm_sub_phase_aligned_sq u v hu hv
  -- Phase-align `(c • v, w)`: ‖c • v‖ = 1, then apply the same construction.
  have hcv : ‖c • v‖ = 1 := by rw [norm_smul, hc1, hv]; ring
  obtain ⟨d, hd1, hdvw⟩ := norm_sub_phase_aligned_sq (c • v) w hcv hw
  -- ‖c • v - d • w‖² = 2 (1 - ‖⟪c • v, w⟫_ℂ‖) and ‖⟪c • v, w⟫_ℂ‖ = ‖⟪v, w⟫_ℂ‖.
  have hinner_cv_w : ‖⟪c • v, w⟫_ℂ‖ = ‖⟪v, w⟫_ℂ‖ := by
    rw [inner_smul_left, norm_mul, RCLike.norm_conj, hc1, one_mul]
  rw [hinner_cv_w] at hdvw
  -- Triangle inequality on ‖u - d • w‖.
  have hT : ‖u - d • w‖ ≤ ‖u - c • v‖ + ‖c • v - d • w‖ := by
    have hsplit : u - d • w = (u - c • v) + (c • v - d • w) := by abel
    rw [hsplit]
    exact norm_add_le _ _
  -- Square the triangle and apply (a + b)² ≤ 2 a² + 2 b².
  have hsq : ‖u - d • w‖ ^ 2
      ≤ (‖u - c • v‖ + ‖c • v - d • w‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hT 2
  have hexpand :
      (‖u - c • v‖ + ‖c • v - d • w‖) ^ 2
      ≤ 2 * ‖u - c • v‖ ^ 2 + 2 * ‖c • v - d • w‖ ^ 2 := by
    nlinarith [sq_nonneg (‖u - c • v‖ - ‖c • v - d • w‖)]
  -- ‖u - d • w‖² ≥ 2 (1 - ‖⟪u, w⟫_ℂ‖).
  have hdw_norm : ‖d • w‖ = 1 := by rw [norm_smul, hd1, hw]; ring
  have hinner_u_dw : ‖⟪u, d • w⟫_ℂ‖ = ‖⟪u, w⟫_ℂ‖ := by
    rw [inner_smul_right, norm_mul, hd1, one_mul]
  have hlb : 2 * (1 - ‖⟪u, w⟫_ℂ‖) ≤ ‖u - d • w‖ ^ 2 := by
    rw [@norm_sub_sq ℂ _ _ _ _ u (d • w), hu, hdw_norm]
    have hre_le_norm : RCLike.re ⟪u, d • w⟫_ℂ ≤ ‖⟪u, d • w⟫_ℂ‖ :=
      RCLike.re_le_norm _
    rw [hinner_u_dw] at hre_le_norm
    nlinarith
  -- Combine.
  linarith [hcuv, hdvw]

end ForMathlib
