import Mathlib.Analysis.Complex.Basic

open ComplexConjugate

/-- Every complex number can be multiplied by a unit complex number to obtain its norm. -/
lemma Complex.phase_alignment (c : ℂ) : ∃ γ : ℂ, ‖γ‖ = 1 ∧ γ * c = ‖c‖ := by
  by_cases h : c = 0
  · refine ⟨1, ?_, ?_⟩
    · simp
    · simp [h]
  · refine ⟨conj c / ‖c‖, ?_, ?_⟩
    · simp [norm_eq_zero.not.2 h]
    · field_simp [norm_eq_zero.not.2 h]
      simp [Complex.conj_mul', pow_two]
