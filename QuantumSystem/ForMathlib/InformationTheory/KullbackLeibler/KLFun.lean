/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.KLFun

/-!
# ForMathlib: KL Divergence Function Lemmas

## Main Results

* `Real.sub_le_mul_log_div`: for `0 ≤ x` and `0 < y`, `x - y ≤ x log (x / y)`.
* `Real.mul_log_div_eq_sub_iff`: for `0 ≤ x` and `0 < y`, equality holds iff `x = y`.

Both follow from `Real.mul_log_div_sub_sub_eq_mul_klFun`: the gap `x log (x / y) - (x - y)` is
`y · klFun (x / y)`, and `klFun t ≥ 0` with equality exactly at `t = 1`.
-/

@[expose] public section

namespace Real

open InformationTheory

/-- The gap in `x - y ≤ x log (x / y)` is `y · klFun (x / y)`: with `t = x / y`,
`x log (x / y) - (x - y) = y (t log t - t + 1)`. -/
lemma mul_log_div_sub_sub_eq_mul_klFun {x y : ℝ} (hy : y ≠ 0) :
    x * log (x / y) - (x - y) = y * klFun (x / y) := by
  rw [klFun_apply]
  field_simp
  ring

/-- For `0 ≤ x` and `0 < y`, `x - y ≤ x log (x / y)`; equality is `Real.mul_log_div_eq_sub_iff`. -/
lemma sub_le_mul_log_div {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) : x - y ≤ x * log (x / y) := by
  rw [← sub_nonneg, mul_log_div_sub_sub_eq_mul_klFun hy.ne']
  exact mul_nonneg hy.le (klFun_nonneg (div_nonneg hx hy.le))

/-- For `0 ≤ x` and `0 < y`, `x log (x / y) = x - y` holds exactly when `x = y`. -/
lemma mul_log_div_eq_sub_iff {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    x * log (x / y) = x - y ↔ x = y := by
  rw [← sub_eq_zero, mul_log_div_sub_sub_eq_mul_klFun hy.ne', mul_eq_zero,
    klFun_eq_zero_iff (div_nonneg hx hy.le), div_eq_one_iff_eq hy.ne', or_iff_right hy.ne']

end Real

end
