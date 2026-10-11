/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue

/-!
# Measures against counting measure

Only the empty set is null for counting measure, so every measure is absolutely continuous with
respect to it (`MeasureTheory.Measure.absolutelyContinuous_count`), and on a countable type with
measurable singletons the Radon–Nikodym derivative of `μ` is the mass function `a ↦ μ {a}`
(`MeasureTheory.Measure.rnDeriv_count`).
-/

@[expose] public section

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α]

/-- Every measure is absolutely continuous with respect to counting measure. -/
lemma absolutelyContinuous_count (μ : Measure α) : μ ≪ count :=
  AbsolutelyContinuous.mk fun s _ hs => by rw [count_eq_zero_iff] at hs; simp [hs]

/-- The Radon–Nikodym derivative with respect to counting measure is the mass function. -/
lemma rnDeriv_count [Countable α] [MeasurableSingletonClass α] (μ : Measure α) :
    μ.rnDeriv count =ᵐ[count] fun a => μ {a} := by
  conv_lhs => rw [← sum_smul_dirac μ, ← count_withDensity]
  exact rnDeriv_withDensity count Measurable.of_discrete

end MeasureTheory.Measure
