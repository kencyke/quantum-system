module

public import Mathlib.InformationTheory.KullbackLeibler.KLFun

/-!
# ForMathlib: KL Divergence Function Lemmas

## Main Results

* `mul_log_div_ge_sub'`: For x, y > 0, x * log(x/y) ≥ x - y.
-/

@[expose] public section

/-- Key lemma: for x > 0, y > 0, we have x log(x/y) ≥ x - y with equality iff x = y.
Proof: Let t = x/y. Then x log(x/y) - (x - y) = y(t log t - t + 1) = y * klFun(t) ≥ 0. -/
lemma mul_log_div_ge_sub' {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x * Real.log (x / y) ≥ x - y := by
  have ht : x / y > 0 := div_pos hx hy
  have key : x * Real.log (x / y) - (x - y) = y * InformationTheory.klFun (x / y) := by
    unfold InformationTheory.klFun
    field_simp
    ring
  rw [ge_iff_le, ← sub_nonneg, key]
  exact mul_nonneg (le_of_lt hy) (InformationTheory.klFun_nonneg (le_of_lt ht))

end
