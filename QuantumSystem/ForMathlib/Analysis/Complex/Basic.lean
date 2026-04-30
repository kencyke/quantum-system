module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

@[expose] public section

open ComplexConjugate

/-! ### Non-negativity in `ComplexOrder` for real-valued complex numbers

Convenience reformulations of `Complex.zero_le_real` for use sites that pass a
real witness; primarily consumed by spectral / density-matrix calculations
where one needs `(0 : ℂ) ≤ (ε : ℂ)` with `ε : ℝ`. -/

namespace Complex

open scoped ComplexOrder

/-- Real `ε` lifted to complex with the natural ordering: `0 ≤ ε` in ℝ implies `0 ≤ ε` in ℂ. -/
lemma zero_le_ofReal {ε : ℝ} (hε : 0 ≤ ε) : (0 : ℂ) ≤ (ε : ℂ) :=
  Complex.zero_le_real.mpr hε

/-- Real `1 - ε` lifted to complex is non-negative when `ε ≤ 1`. -/
lemma zero_le_one_sub_ofReal {ε : ℝ} (hε' : ε ≤ 1) : (0 : ℂ) ≤ (1 - (ε : ℂ)) := by
  rw [show (1 - (ε : ℂ)) = ((1 - ε : ℝ) : ℂ) from by push_cast; ring]
  exact Complex.zero_le_real.mpr (by linarith)

/-- The reciprocal of a natural number lifted to `ℂ` is non-negative. -/
lemma zero_le_natCast_inv (n : ℕ) : (0 : ℂ) ≤ ((n : ℂ)⁻¹) := by
  refine ⟨?_, ?_⟩
  · simp only [Complex.zero_re, Complex.inv_re, Complex.natCast_re, Complex.normSq_natCast]
    by_cases hn : n = 0
    · simp [hn]
    · have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      positivity
  · simp [Complex.inv_im, Complex.natCast_im]

end Complex

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
