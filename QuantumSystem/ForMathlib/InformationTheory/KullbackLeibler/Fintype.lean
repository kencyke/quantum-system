/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Kullback–Leibler divergence on a finite type

For finite measures `μ, ν` on a finite type with measurable singletons, the Kullback–Leibler
divergence `InformationTheory.klDiv μ ν` is the finite sum

  `klDiv μ ν = ∑ₐ μ{a} log (μ{a} / ν{a}) + ν(univ) - μ(univ)`

when `ν{a} = 0 → μ{a} = 0` for every `a` (equivalently `μ ≪ ν`), and `∞` otherwise.

## Main results

* `MeasureTheory.Measure.absolutelyContinuous_iff_singleton` — on a finite type, `μ ≪ ν` iff
  `ν{a} = 0 → μ{a} = 0` for every `a`.
* `InformationTheory.klDiv_of_fintype` — the finite-sum formula for `klDiv μ ν`.
-/

@[expose] public section

open MeasureTheory Real

namespace MeasureTheory.Measure

variable {α : Type*} [Countable α] [MeasurableSpace α]

/-- On a countable type, `μ ≪ ν` iff every `ν`-null point is `μ`-null. -/
theorem absolutelyContinuous_iff_singleton {μ ν : Measure α} :
    μ ≪ ν ↔ ∀ a, ν {a} = 0 → μ {a} = 0 := by
  refine ⟨fun h a ha => h ha, fun h s hs => ?_⟩
  rw [← Set.biUnion_of_singleton s, measure_biUnion_null_iff s.to_countable]
  exact fun a ha => h a (measure_mono_null (Set.singleton_subset_iff.mpr ha) hs)

end MeasureTheory.Measure

namespace InformationTheory

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The density `a ↦ μ{a} / ν{a}` of `μ` against `ν` on a countable type. -/
private lemma withDensity_div_singleton [Countable α] {μ ν : Measure α} [IsFiniteMeasure ν]
    (h : μ ≪ ν) :
    ν.withDensity (fun a => μ {a} / ν {a}) = μ := by
  rw [Measure.ext_iff_singleton]
  intro a
  rw [withDensity_apply _ (measurableSet_singleton a), lintegral_singleton]
  rcases eq_or_ne (ν {a}) 0 with h0 | h0
  · rw [h0, mul_zero, h h0]
  · exact ENNReal.div_mul_cancel h0 (measure_ne_top _ _) |>.symm ▸ rfl

/-- **Kullback–Leibler divergence on a finite type.** For finite measures on a finite type with
measurable singletons, `klDiv μ ν = ∑ₐ μ{a} log (μ{a} / ν{a}) + ν(univ) - μ(univ)` if `μ ≪ ν`,
and `∞` otherwise. -/
theorem klDiv_of_fintype [Fintype α] (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [Decidable (μ ≪ ν)] :
    klDiv μ ν = if μ ≪ ν then
      ENNReal.ofReal (∑ a, μ.real {a} * Real.log (μ.real {a} / ν.real {a}) +
        ν.real Set.univ - μ.real Set.univ)
      else ⊤ := by
  split_ifs with h
  · rw [klDiv_of_ac_of_integrable h Integrable.of_finite, integral_fintype Integrable.of_finite]
    congr 3
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_eq_mul]
    rcases eq_or_ne (μ {a}) 0 with h0 | h0
    · simp [measureReal_def, h0]
    · have hν : ν {a} ≠ 0 := fun hν => h0 (h hν)
      have hd : μ.rnDeriv ν a = μ {a} / ν {a} := by
        have hae := Measure.rnDeriv_withDensity ν
          (f := fun a => μ {a} / ν {a}) (measurable_of_finite _)
        rw [withDensity_div_singleton h] at hae
        exact (ae_iff.mp hae |> fun hs => by
          by_contra hne
          exact hν (measure_mono_null (Set.singleton_subset_iff.mpr hne) hs))
      rw [llr, hd, ENNReal.toReal_div, measureReal_def, measureReal_def]
  · exact klDiv_of_not_ac h

end InformationTheory
