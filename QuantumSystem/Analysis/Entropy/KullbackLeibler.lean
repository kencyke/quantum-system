/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import QuantumSystem.ForMathlib.InformationTheory.KullbackLeibler.Fintype
public import QuantumSystem.ForMathlib.InformationTheory.KullbackLeibler.KLFun
public import QuantumSystem.ForMathlib.MeasureTheory.Integral.EReal

/-!
# The Kullback–Leibler divergence as an extended real

The **Kullback–Leibler divergence** of two measures `P, Q` on `α` is
`D(P ‖ Q) = ∫ log (dP/dQ) dP ∈ (-∞, +∞]` if `P ≪ Q`, and `+∞` otherwise
(`InformationTheory.klDivEReal`). The integral is the extended integral of the log-likelihood
ratio `llr P Q = log (dP/dQ)` (`MeasureTheory.erealIntegral`), whose negative part is finite for
finite `Q`, so the value is never `-∞` (`InformationTheory.klDivEReal_ne_bot`).

Mathlib's `InformationTheory.klDiv P Q = ∫ log (dP/dQ) dP + Q(α) - P(α)` carries the mass
correction `Q(α) - P(α)` that makes it nonnegative for unnormalised measures, and takes values in
`ℝ≥0∞`. The two agree on measures of equal total mass, in particular on probability measures
(`InformationTheory.klDivEReal_eq_klDiv_of_measure_univ_eq`), and differ by `P(α) - Q(α)` in
general (`InformationTheory.klDivEReal_eq_klDiv_add_sub`). The uncorrected form is the classical
relative entropy of Kullback and Leibler, and it is the value of Araki's relative entropy of the
functionals `ω_P, ω_Q` on a commutative von Neumann algebra
(`QuantumSystem.Analysis.Entropy.Araki.Multiplication`).

## Main definitions

* `InformationTheory.klDivEReal P Q` — `D(P ‖ Q) = ∫ log (dP/dQ) dP`, or `+∞` unless `P ≪ Q`.

## Main results

* `InformationTheory.klDivEReal_of_ac`, `klDivEReal_of_not_ac`, `klDivEReal_of_integrable`,
  `klDivEReal_eq_top_of_not_integrable` — the defining cases.
* `InformationTheory.klDivEReal_ne_bot` — the value is never `-∞` for finite `Q`.
* `InformationTheory.klDivEReal_eq_klDiv_add_sub`, `klDivEReal_eq_klDiv_of_measure_univ_eq` —
  comparison with Mathlib's `klDiv`.
* `InformationTheory.klDivEReal_of_fintype` — on a finite type,
  `D(P ‖ Q) = Σᵢ pᵢ log (pᵢ / qᵢ)` if `P ≪ Q`, with `pᵢ = P {i}`, `qᵢ = Q {i}`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace InformationTheory

variable {α : Type*} [MeasurableSpace α] {P Q : Measure α}

open Classical in
/-- The **Kullback–Leibler divergence** `D(P ‖ Q) = ∫ log (dP/dQ) dP ∈ (-∞, +∞]` of two measures,
`+∞` unless `P ≪ Q`, without the mass correction `Q(α) - P(α)` of `InformationTheory.klDiv`
(the two agree on measures of equal total mass, `klDivEReal_eq_klDiv_of_measure_univ_eq`). This is
the classical relative entropy, the value of Araki's relative entropy on a commutative algebra. -/
noncomputable def klDivEReal (P Q : Measure α) : EReal :=
  if P ≪ Q then erealIntegral P (fun x => (llr P Q x : EReal)) else ⊤

/-- `D(P ‖ Q) = ∫ log (dP/dQ) dP` for `P ≪ Q`. -/
lemma klDivEReal_of_ac (h : P ≪ Q) :
    klDivEReal P Q = erealIntegral P (fun x => (llr P Q x : EReal)) := by
  rw [klDivEReal, ite_eq_left h]

/-- `D(P ‖ Q) = +∞` unless `P ≪ Q`. -/
lemma klDivEReal_of_not_ac (h : ¬ P ≪ Q) : klDivEReal P Q = ⊤ := by
  rw [klDivEReal, ite_eq_right h]

/-- `D(P ‖ Q) = ∫ log (dP/dQ) dP` as a real number when `log (dP/dQ)` is `P`-integrable. -/
lemma klDivEReal_of_integrable (h : P ≪ Q) (hint : Integrable (llr P Q) P) :
    klDivEReal P Q = ((∫ x, llr P Q x ∂P : ℝ) : EReal) := by
  rw [klDivEReal_of_ac h, erealIntegral_coe hint]

/-- `D(P ‖ Q) = +∞` when `P ≪ Q` and `log (dP/dQ)` is not `P`-integrable, for finite `Q`. -/
lemma klDivEReal_eq_top_of_not_integrable [SigmaFinite P] [IsFiniteMeasure Q] (h : P ≪ Q)
    (hint : ¬ Integrable (llr P Q) P) : klDivEReal P Q = ⊤ := by
  rw [klDivEReal_of_ac h, erealIntegral_llr_eq_top h hint]

/-- `D(P ‖ Q) ≠ -∞` for finite `Q`. -/
lemma klDivEReal_ne_bot [SigmaFinite P] [IsFiniteMeasure Q] : klDivEReal P Q ≠ ⊥ := by
  by_cases h : P ≪ Q
  · rw [klDivEReal_of_ac h]
    exact erealIntegral_llr_ne_bot h
  · rw [klDivEReal_of_not_ac h]
    exact top_ne_bot

/-- **Comparison with Mathlib's `klDiv`**: `D(P ‖ Q) = klDiv P Q + P(α) - Q(α)` for finite
measures; the term `P(α) - Q(α)` cancels the mass correction of `klDiv`. -/
lemma klDivEReal_eq_klDiv_add_sub [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    klDivEReal P Q = (klDiv P Q : EReal) + P.real Set.univ - Q.real Set.univ := by
  by_cases hPQ : P ≪ Q
  · by_cases hint : Integrable (llr P Q) P
    · rw [klDivEReal_of_integrable hPQ hint, klDiv_of_ac_of_integrable hPQ hint,
        EReal.coe_ennreal_ofReal, max_eq_left (integral_llr_add_sub_measure_univ_nonneg hPQ hint),
        ← EReal.coe_add, ← EReal.coe_sub]
      congr 1
      ring
    · rw [klDiv_of_not_integrable hint, EReal.coe_ennreal_top,
        klDivEReal_eq_top_of_not_integrable hPQ hint, EReal.top_add_coe, EReal.top_sub_coe]
  · rw [klDivEReal_of_not_ac hPQ, klDiv_of_not_ac hPQ, EReal.coe_ennreal_top, EReal.top_add_coe,
      EReal.top_sub_coe]

/-- `D(P ‖ Q) = klDiv P Q` for finite measures of equal total mass, e.g. two probability
measures. -/
lemma klDivEReal_eq_klDiv_of_measure_univ_eq [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (h : P Set.univ = Q Set.univ) : klDivEReal P Q = klDiv P Q := by
  rw [klDivEReal_eq_klDiv_add_sub, measureReal_def, measureReal_def, h]
  exact EReal.add_sub_cancel_right

section Fintype

variable [Fintype α] [MeasurableSingletonClass α] [IsFiniteMeasure P] [IsFiniteMeasure Q]

/-- **Gibbs' inequality** for unnormalised measures: `Q(α) - P(α) ≤ Σᵢ pᵢ log (pᵢ / qᵢ)` when
`P ≪ Q`. -/
private lemma sum_mul_log_div_add_sub_nonneg (hPQ : P ≪ Q) :
    0 ≤ ∑ i, P.real {i} * Real.log (P.real {i} / Q.real {i}) + Q.real Set.univ - P.real Set.univ := by
  have h : ∀ i, P.real {i} - Q.real {i} ≤ P.real {i} * Real.log (P.real {i} / Q.real {i}) := by
    intro i
    rcases (measureReal_nonneg (μ := P) (s := {i})).eq_or_lt with h0 | hpi
    · rw [← h0]; simp
    · refine mul_log_div_ge_sub' hpi (measureReal_nonneg.lt_of_ne' fun hq => hpi.ne' ?_)
      rw [measureReal_eq_zero_iff] at hq ⊢
      exact hPQ hq
  have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h i
  rw [Finset.sum_sub_distrib] at this
  rw [← Finset.coe_univ (α := α), ← sum_measureReal_singleton, ← sum_measureReal_singleton]
  linarith

/-- **Kullback–Leibler divergence on a finite type**: `D(P ‖ Q) = Σᵢ pᵢ log (pᵢ / qᵢ)` if `P ≪ Q`,
with `pᵢ = P {i}` and `qᵢ = Q {i}` (a term with `pᵢ = 0` contributes `0`), and `+∞` otherwise. -/
lemma klDivEReal_of_fintype [Decidable (P ≪ Q)] :
    klDivEReal P Q =
      if P ≪ Q then ((∑ i, P.real {i} * Real.log (P.real {i} / Q.real {i}) : ℝ) : EReal)
      else ⊤ := by
  rw [klDivEReal_eq_klDiv_add_sub, klDiv_of_fintype]
  split_ifs with hPQ
  · rw [EReal.coe_ennreal_ofReal, max_eq_left (sum_mul_log_div_add_sub_nonneg hPQ), ← EReal.coe_add,
      ← EReal.coe_sub]
    congr 1
    ring
  · rw [EReal.coe_ennreal_top, EReal.top_add_coe, EReal.top_sub_coe]

end Fintype

end InformationTheory
