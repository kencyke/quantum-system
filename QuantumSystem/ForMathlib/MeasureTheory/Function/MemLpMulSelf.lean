/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Square-integrability of a function from that of its square

On a finite measure space, `|g| ≤ 1 + |g|²` shows that `g ∈ L²` as soon as `g g ∈ L²`. This is
the domain inclusion `dom A ⊆ dom A^{1/2}` of spectral calculus.

## Main results

* `MeasureTheory.memLp_of_memLp_mul_self` — `g g ∈ L²(μ)` implies `g ∈ L²(μ)` for finite `μ`.
-/

@[expose] public section

open Filter

namespace MeasureTheory

/-- On a finite measure space, `g g ∈ L²` forces `g ∈ L²`. -/
lemma memLp_of_memLp_mul_self {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] {g : X → ℂ} (hg : Measurable g) (h : MemLp (g * g) 2 μ) : MemLp g 2 μ :=
  ((memLp_const (1 : ℝ)).add h.norm).of_le_mul (c := 1) hg.aestronglyMeasurable
    (Eventually.of_forall fun x => by
      simp only [Pi.add_apply, Pi.mul_apply, norm_mul, one_mul, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity)]
      nlinarith [norm_nonneg (g x), sq_nonneg (‖g x‖ - 1)])

end MeasureTheory
