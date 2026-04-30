module

public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Helper lemmas for Hilbert bases and Parseval identity

This file provides additional lemmas for Hilbert bases that extend Mathlib's `l2Space`.

## Main results

* `inner_mul_inner_eq_norm_sq`: For a Hilbert basis, `⟪x, bᵢ⟫ * ⟪bᵢ, x⟫ = ‖⟪bᵢ, x⟫‖²`
* `HilbertBasis.norm_sq_eq_tsum_norm_sq_inner'`: Parseval identity `‖x‖² = ∑ᵢ ‖⟪bᵢ, x⟫‖²`
* `HilbertBasis.summable_norm_sq_inner'`: The sequence `‖⟪bᵢ, x⟫‖²` is summable
-/

@[expose] public section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {ι : Type*}

/-- For a Hilbert basis, `⟪x, bᵢ⟫ * ⟪bᵢ, x⟫ = ‖⟪bᵢ, x⟫‖²` as complex numbers. -/
theorem inner_mul_inner_eq_norm_sq (b : HilbertBasis ι ℂ H) (x : H) (i : ι) :
    inner (𝕜 := ℂ) x (b i) * inner (𝕜 := ℂ) (b i) x = (‖inner (𝕜 := ℂ) (b i) x‖^2 : ℂ) := by
  rw [← inner_conj_symm (𝕜 := ℂ)]
  have h : ↑(Complex.normSq (inner ℂ (b i) x)) = (starRingEnd ℂ) (inner ℂ (b i) x) * inner ℂ (b i) x :=
    Complex.normSq_eq_conj_mul_self
  rw [← h]
  norm_cast
  exact Complex.normSq_eq_norm_sq _

/-- Helper: real part of a real power. -/
private lemma ofReal_pow_re (r : ℝ) (n : ℕ) : ((r : ℂ)^n).re = r^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, ih]
    ring

/-- Parseval identity for Hilbert bases: `‖x‖² = ∑ᵢ ‖⟪bᵢ, x⟫‖²`. -/
theorem HilbertBasis.norm_sq_eq_tsum_norm_sq_inner' (b : HilbertBasis ι ℂ H) (x : H) :
    ‖x‖^2 = ∑' i, ‖inner (𝕜 := ℂ) (b i) x‖^2 := by
  have h := b.tsum_inner_mul_inner x x
  simp_rw [inner_mul_inner_eq_norm_sq b x] at h
  have h2 : (inner (𝕜 := ℂ) x x).re = ‖x‖^2 := by
    rw [inner_self_eq_norm_sq_to_K]
    exact ofReal_pow_re _ 2
  have h3 : (∑' i, (‖inner (𝕜 := ℂ) (b i) x‖^2 : ℂ)).re = ∑' i, ‖inner (𝕜 := ℂ) (b i) x‖^2 := by
    rw [Complex.re_tsum]
    · congr 1
      ext i
      exact ofReal_pow_re _ 2
    · have := b.summable_inner_mul_inner x x
      simp_rw [inner_mul_inner_eq_norm_sq b x] at this
      exact this
  rw [← h2, ← h, h3]

/-- The sequence `‖⟪bᵢ, x⟫‖²` is summable for any Hilbert basis. -/
theorem HilbertBasis.summable_norm_sq_inner' (b : HilbertBasis ι ℂ H) (x : H) :
    Summable (fun i => ‖inner (𝕜 := ℂ) (b i) x‖^2) := by
  have hsummable := b.summable_inner_mul_inner x x
  simp_rw [inner_mul_inner_eq_norm_sq b x] at hsummable
  obtain ⟨s, hs⟩ := hsummable
  have hs_re := Complex.hasSum_re hs
  simp_rw [ofReal_pow_re] at hs_re
  exact hs_re.summable
