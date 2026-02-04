module

public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Root-of-Unity Utilities

Auxiliary lemmas about primitive roots of unity needed for the pinching method
in entropy inequalities.

## Main definitions

* `rootOfUnity r`: The r-th primitive root of unity ζ = e^{2πi/r}.

## Main results

* `rootOfUnity_norm`: ‖ζ‖ = 1.
* `rootOfUnity_ne_zero`: ζ ≠ 0.
* `rootOfUnity_star`: star(ζ) = ζ⁻¹.
* `rootOfUnity_sum_eq_zero`: ∑_{k=0}^{r-1} ζ^{nk} = 0 when r ∤ n.
-/

@[expose] public section

namespace Matrix

/-! ### Primitive root of unity -/

/-- The r-th primitive root of unity: ζ = e^{2πi/r}. -/
noncomputable def rootOfUnity (r : ℕ) [NeZero r] : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / r)

/-- The root of unity has norm 1. -/
lemma rootOfUnity_norm (r : ℕ) [NeZero r] : ‖rootOfUnity r‖ = 1 := by
  unfold rootOfUnity
  have hr_ne : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  have heq : (2 : ℂ) * ↑Real.pi * Complex.I / ↑r = ((2 * Real.pi / r : ℝ) : ℂ) * Complex.I := by
    rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_natCast]
    ring
  rw [heq, Complex.norm_exp_ofReal_mul_I]

/-- ζ ≠ 0 for the r-th root of unity. -/
lemma rootOfUnity_ne_zero (r : ℕ) [NeZero r] : rootOfUnity r ≠ 0 := by
  intro h
  have := rootOfUnity_norm r
  rw [h, norm_zero] at this
  exact zero_ne_one this

/-- The star (complex conjugate) of a root of unity equals its inverse. -/
lemma rootOfUnity_star (r : ℕ) [NeZero r] : star (rootOfUnity r) = (rootOfUnity r)⁻¹ := by
  -- For z with |z| = 1, we have star(z) * z = |z|² = 1, hence star(z) = z⁻¹
  have hne : rootOfUnity r ≠ 0 := rootOfUnity_ne_zero r
  have hnorm : ‖rootOfUnity r‖ = 1 := rootOfUnity_norm r
  -- star(z) * z = |z|² for complex numbers
  have hconj_mul : star (rootOfUnity r) * rootOfUnity r = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
    simp only [Complex.ofReal_eq_one]
    rw [Complex.normSq_eq_norm_sq, hnorm, one_pow]
  -- From star(z) * z = 1, we get star(z) = z⁻¹
  exact mul_eq_one_iff_eq_inv₀ hne |>.mp hconj_mul

/-- The sum of r-th roots of unity is 0 when n ≢ 0 (mod r). -/
lemma rootOfUnity_sum_eq_zero (r : ℕ) [NeZero r] (n : ℤ) (hn : n % (r : ℤ) ≠ 0) :
    ∑ k : Fin r, (rootOfUnity r) ^ (n * k) = 0 := by
  unfold rootOfUnity
  set ζ := Complex.exp (2 * Real.pi * Complex.I / ↑r) with hζ_def
  have hr_pos : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hr_ne : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  -- ζ is a primitive r-th root of unity
  have hζ_prim : IsPrimitiveRoot ζ r := by
    rw [hζ_def]
    exact Complex.isPrimitiveRoot_exp r (NeZero.ne r)
  -- ζ^r = 1
  have hζ_pow_r : ζ ^ r = 1 := hζ_prim.pow_eq_one
  -- ζ^n ≠ 1 when n % r ≠ 0
  have hζn_ne_one : ζ ^ n ≠ 1 := by
    intro heq
    have hdvd : (r : ℤ) ∣ n := hζ_prim.zpow_eq_one_iff_dvd n |>.mp heq
    exact hn (Int.emod_eq_zero_of_dvd hdvd)
  -- ζ ≠ 0
  have hζ_ne : ζ ≠ 0 := by
    rw [hζ_def]
    exact Complex.exp_ne_zero _
  -- Helper: ζ ^ (↑i * n) = (ζ ^ n) ^ i for natural i
  have hpow_eq : ∀ i : ℕ, ζ ^ (↑i * n) = (ζ ^ n) ^ i := fun i => by
    induction i with
    | zero => simp only [Nat.cast_zero, zero_mul, zpow_zero, pow_zero]
    | succ k ih =>
      rw [pow_succ, ← ih, Nat.cast_succ, add_mul, one_mul, zpow_add₀ hζ_ne]
  -- Rewrite the sum: ∑ k, ζ^(n*k) = ∑ k, (ζ^n)^k
  have hsum_eq : ∑ k : Fin r, ζ ^ (n * ↑↑k) = ∑ i ∈ Finset.range r, (ζ ^ n) ^ i := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_range] at hi
    simp only [dif_pos hi]
    rw [Int.mul_comm]
    exact hpow_eq i
  rw [hsum_eq]
  -- (ζ^n)^r = 1
  have hζn_pow_r : (ζ ^ n) ^ r = 1 := by
    -- We have hpow_eq : ζ ^ (↑i * n) = (ζ ^ n) ^ i
    -- So (ζ ^ n) ^ r = ζ ^ (↑r * n)
    rw [← hpow_eq r]
    -- Now need: ζ ^ (↑r * n) = 1
    -- We show: for any k : ℤ, ζ ^ (↑r * k) = 1 by k = k.natAbs or -k.natAbs
    have hζr_mul : ∀ k : ℤ, ζ ^ (↑r * k) = 1 := fun k => by
      rcases Int.eq_nat_or_neg k with ⟨m, rfl | rfl⟩
      · -- k = ↑m
        have h1 : (↑r : ℤ) * ↑m = ↑(r * m) := by norm_cast
        rw [h1, zpow_natCast, pow_mul, hζ_pow_r, one_pow]
      · -- k = -↑m
        have h1 : (↑r : ℤ) * -↑m = -↑(r * m) := by push_cast; ring
        rw [h1]
        rcases m.eq_zero_or_pos with rfl | hm_pos
        · simp
        · have hpos : 0 < r * m := Nat.mul_pos hr_pos hm_pos
          rw [zpow_neg_coe_of_pos ζ hpos, pow_mul, hζ_pow_r, one_pow, inv_one]
    exact hζr_mul n
  -- Apply geometric sum formula
  rw [geom_sum_eq hζn_ne_one]
  simp [hζn_pow_r]

end Matrix
