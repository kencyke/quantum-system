module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

@[expose] public section

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

/-- Lemma for rotation trick: exp(-I * arg z) * z = |z|. -/
lemma Complex.exp_neg_I_arg_mul_self (z : ℂ) : Complex.exp (-Complex.I * Complex.arg z) * z = ↑‖z‖ := by
  by_cases hz : z = 0
  · simp [hz]
  · have hz2 : z = ↑‖z‖ * Complex.exp (↑(Complex.arg z) * Complex.I) :=
      (Complex.norm_mul_exp_arg_mul_I z).symm
    calc Complex.exp (-Complex.I * Complex.arg z) * z
        = Complex.exp (-Complex.I * Complex.arg z) * (↑‖z‖ * Complex.exp (↑(Complex.arg z) * Complex.I)) := by rw [← hz2]
      _ = ↑‖z‖ * (Complex.exp (-Complex.I * Complex.arg z) * Complex.exp (↑(Complex.arg z) * Complex.I)) := by ring
      _ = ↑‖z‖ * Complex.exp (-Complex.I * ↑(Complex.arg z) + ↑(Complex.arg z) * Complex.I) := by rw [← Complex.exp_add]
      _ = ↑‖z‖ * Complex.exp 0 := by ring_nf
      _ = ↑‖z‖ := by simp

/-- Helper: for any complex z, there exists u with ‖u‖ ≤ 1 such that ‖z‖ = Re(u * z). -/
lemma Complex.exists_unit_mul_eq_norm (z : ℂ) : ∃ (u : ℂ), ‖u‖ ≤ 1 ∧ ‖z‖ = (u * z).re := by
  by_cases hz : z = 0
  · use 0; simp [hz]
  · use Complex.exp (-Complex.I * Complex.arg z)
    constructor
    · rw [Complex.norm_exp]
      simp only [neg_mul, neg_re, mul_re, Complex.I_re, Complex.I_im, one_mul,
        ofReal_re, zero_mul]
      simp
    · rw [exp_neg_I_arg_mul_self]
      simp
