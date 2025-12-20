module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.NonUnital
public import QuantumSystem.ForMathlib.Analysis.Complex.Basic

@[expose] public section

section State

open NNReal

variable (𝕜 : Type*) [RCLike 𝕜]

/-- The operator norm on linear maps from a C*-algebra to the scalars. -/
noncomputable def linearOpNorm (A : Type*) [NonUnitalCStarAlgebra A] [Module 𝕜 A]
    (f : A →ₗ[𝕜] 𝕜) : ℝ :=
  sSup { r : ℝ | ∃ a : A, a ≠ 0 ∧ r = ‖f a‖ / ‖a‖ }

/-- A state on a non-unital C*-algebra: a positive linear functional with norm 1. -/
structure State (A : Type*) [NonUnitalCStarAlgebra A] [Module 𝕜 A]
    extends A →ₗ[𝕜] 𝕜 where
  positive : ∀ a : A, ∃ r : ℝ≥0, toLinearMap (star a * a) = RCLike.ofReal (r : ℝ)
  norm_eq_one : linearOpNorm 𝕜 A toLinearMap = 1

namespace State

variable {𝕜 A : Type*} [RCLike 𝕜] [NonUnitalCStarAlgebra A] [Module 𝕜 A]

/-- `FunLike` instance to make states callable like functions. -/
instance : FunLike (State 𝕜 A) A 𝕜 where
  coe ω := ω.toLinearMap
  coe_injective' ω₁ ω₂ h := by
    cases ω₁
    cases ω₂
    congr
    exact DFunLike.coe_injective h

/-- States are linear maps. -/
instance : LinearMapClass (State 𝕜 A) 𝕜 A 𝕜 where
  map_add ω := ω.toLinearMap.map_add
  map_smulₛₗ ω := ω.toLinearMap.map_smul

/-- Norm instance for states. -/
noncomputable instance : Norm (State 𝕜 A) where
  norm ω := linearOpNorm 𝕜 A ω.toLinearMap

@[simp]
lemma toLinearMap_apply (ω : State 𝕜 A) (a : A) : ω.toLinearMap a = ω a := rfl

@[ext]
lemma ext {ω₁ ω₂ : State 𝕜 A} (h : ∀ a, ω₁ a = ω₂ a) : ω₁ = ω₂ :=
  DFunLike.ext ω₁ ω₂ h

lemma norm_def (ω : State 𝕜 A) :
    ‖ω‖ = sSup { r : ℝ | ∃ a : A, a ≠ 0 ∧ r = ‖ω a‖ / ‖a‖ } := rfl

/-- States satisfy `‖ω a‖ ≤ ‖a‖` for all `a`. -/
lemma norm_le_norm (ω : State 𝕜 A) (a : A) : ‖ω a‖ ≤ ‖a‖ := by
  by_cases ha : a = 0
  · subst ha
    simp
  · have h_norm : ‖ω‖ = 1 := ω.norm_eq_one
    rw [norm_def] at h_norm
    have h_mem : ‖ω a‖ / ‖a‖ ∈ {r | ∃ b : A, b ≠ 0 ∧ r = ‖ω b‖ / ‖b‖} := ⟨a, ha, rfl⟩
    have hbdd : BddAbove {r | ∃ b : A, b ≠ 0 ∧ r = ‖ω b‖ / ‖b‖} := by
      by_contra h_not_bdd
      have : sSup {r | ∃ b : A, b ≠ 0 ∧ r = ‖ω b‖ / ‖b‖} = 0 := by
        rw [Real.sSup_def]
        simp [h_not_bdd]
      rw [this] at h_norm
      norm_num at h_norm
    have h_le : ‖ω a‖ / ‖a‖ ≤ 1 := by
      calc ‖ω a‖ / ‖a‖
          ≤ sSup {r | ∃ b : A, b ≠ 0 ∧ r = ‖ω b‖ / ‖b‖} := le_csSup hbdd h_mem
        _ = 1 := h_norm
    have ha_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha
    calc ‖ω a‖
        = (‖ω a‖ / ‖a‖) * ‖a‖ := by field_simp
      _ ≤ 1 * ‖a‖ := mul_le_mul_of_nonneg_right h_le (norm_nonneg _)
      _ = ‖a‖ := one_mul _

end State

end State

namespace State

open ComplexConjugate NNReal

variable {A : Type*} [NonUnitalCStarAlgebra A]
variable (ω : State ℂ A)
variable (x y : A)
variable (x₁ x₂ y₁ y₂ : A)
variable (z c : ℂ)

/-- The star of a complex number equals its conjugate. -/
lemma star_as_conj : star z = conj z := rfl

/-- The product of a complex number with its conjugate equals the squared norm. -/
lemma star_mul_self_eq_normSq : star z * z = ‖z‖^2 := Complex.conj_mul' z

/-- Quadratic expansion of `ω(star (z • x + y) * (z • x + y))`. -/
lemma quadratic_expansion : ω (star (z • x + y) * (z • x + y)) =
  ‖z‖^2 * ω (star x * x) + conj z * ω (star x * y) + z * ω (star y * x) + ω (star y * y) := by
  have hstar : star (z • x + y) = conj z • star x + star y := by simp [star_smul]
  rw [hstar]
  simp only [add_mul, mul_add]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  simp only [map_add, map_smul]
  rw [← Complex.conj_mul']
  simp [smul_eq_mul]
  ring

/-- States satisfy the conjugate symmetry property: `ω(star y * x) = conj(ω(star x * y))`. -/
lemma conj_sym : ω (star y * x) = conj (ω (star x * y)) := by
  set β : ℂ := ω (star x * y)
  set γ : ℂ := ω (star y * x)
  have quad_real : ∀ t : A, (ω (star t * t)).im = 0 := by
    intro t
    rcases ω.positive t with ⟨r, hr⟩
    have : (ω (star t * t)).im = (RCLike.ofReal (r : ℝ) : ℂ).im := by
      rw [← toLinearMap_apply]
      rw [hr]
    rw [this]
    exact @RCLike.ofReal_im ℂ _ (r : ℝ)
  have sum_im_zero : (β + γ).im = 0 := by
    have hE := quadratic_expansion (ω := ω) (x := x) (y := y) (z := (1 : ℂ))
    have eqim := congrArg Complex.im hE
    have : (ω (star ((1 : ℂ) • x + y) * ((1 : ℂ) • x + y))).im = 0 := quad_real ((1 : ℂ) • x + y)
    have : (ω (star x * x) + β + γ + ω (star y * y)).im = 0 := by
      simpa [norm_eq_one] using eqim.symm.trans this
    simpa [quad_real x, quad_real y] using this
  have diff_re_zero : γ.re = β.re := by
    have hE := quadratic_expansion (ω := ω) (x := x) (y := y) (z := Complex.I)
    have eqim := congrArg Complex.im hE
    have : (ω (star (Complex.I • x + y) * (Complex.I • x + y))).im = 0 := quad_real (Complex.I • x + y)
    have h := eqim.symm.trans this
    have : -β.re + γ.re = 0 := by
      have : ‖Complex.I‖ = 1 := by simp
      simpa [this, quad_real x, quad_real y, Complex.conj_I] using h
    linarith
  have im_eq : γ.im = -β.im := by
    have : β.im + γ.im = 0 := by simpa using sum_im_zero
    linarith
  exact Complex.ext diff_re_zero im_eq

/-- Extract the nonnegative real value from `ω(star a * a)`. -/
noncomputable def positiveReal (a : A) : ℝ≥0 :=
  Classical.choose (ω.positive a)

/-- The value of `ω(star x * x)` equals the extracted nonnegative real. -/
lemma positiveReal_spec : ω (star x * x) = RCLike.ofReal (positiveReal ω x : ℝ) :=
  Classical.choose_spec (ω.positive x)

/-- A conjugate linear combination simplifies to twice the real part. -/
lemma conj_linear_combination_real :
    (conj z) * ω (star x * y) + z * ω (star y * x)
      = Complex.ofReal (2 * (z * ω (star y * x)).re) := by
  set β := ω (star x * y)
  set γ := ω (star y * x)
  have hγβ : γ = conj β := conj_sym (ω := ω) (x := x) (y := y)
  -- Both real and imaginary parts
  refine Complex.ext ?_ ?_
  · -- Real part calculation
    simp [Complex.add_re, Complex.mul_re, hγβ, two_mul]
  · -- Imaginary part is zero
    simp [Complex.add_im, Complex.mul_im, hγβ]
    ring

open ComplexOrder in
lemma cauchy_schwarz_ineq : ‖ω (star y * x)‖^2 ≤ (ω (star x * x)) * (ω (star y * y)) := by
  have quad_nonneg : ∀ t : ℝ,
      0 ≤ (positiveReal ω x) * (t * t) + (2 * ‖ω (star y * x)‖ ) * t + (positiveReal ω y) := by
    intro t
    obtain ⟨γ, hγ_norm, hγ_phase⟩ := Complex.phase_alignment (ω (star y * x))
    let s : A := ((t : ℂ) * γ) • x + y
    have hexp2 : (ω (star s * s)).re = (positiveReal ω x) * (t * t) + (2 * ‖ω (star y * x)‖ ) * t + (positiveReal ω y) := by
      have hquad := quadratic_expansion (ω := ω) (x := x) (y := y) (z := ((t : ℂ) * γ))
      have h1 : (‖(t : ℂ) * γ‖^2 : ℂ) = (t^2 : ℂ) := by
        rw [Complex.norm_mul, hγ_norm, mul_one, Complex.norm_real, pow_two, pow_two]
        norm_cast
        exact abs_mul_abs_self t
      have h2 : conj ((t : ℂ) * γ) * ω (star x * y) + ((t : ℂ) * γ) * ω (star y * x) = 2 * t * ‖ω (star y * x)‖ := by
        have : ((t : ℂ) * γ) * ω (star y * x) = t * (γ * ω (star y * x)) := by ring
        rw [conj_linear_combination_real, this, hγ_phase]
        norm_cast
        ring_nf
      have hequiv : ω (star s * s) = (t^2 : ℂ) * ω (star x * x) + 2 * t * ‖ω (star y * x)‖ + ω (star y * y) := by
        unfold s
        rw [hquad, h1, ← h2]
        ring_nf
      simp only [congrArg Complex.re hequiv, positiveReal_spec (ω := ω) x, positiveReal_spec (ω := ω) y,
                 Complex.add_re, Complex.mul_re,
                 pow_two, Complex.re_ofNat]
      simp
      ring_nf
    rw [← hexp2, positiveReal_spec (ω := ω) s]
    simp
  have : (2 * ‖ω (star y * x)‖) ^ 2 ≤ 4 * (positiveReal ω x) * (positiveReal ω y) := by
    have := discrim_le_zero quad_nonneg
    rw [discrim] at this
    linarith
  have : ‖ω (star y * x)‖ ^ 2 ≤ (positiveReal ω x) * (positiveReal ω y) := by
    have : (2 * ‖ω (star y * x)‖) ^ 2 = 4 * ‖ω (star y * x)‖ ^ 2 := by ring
    linarith
  rw [positiveReal_spec (ω := ω) x, positiveReal_spec (ω := ω) y, ← RCLike.ofReal_mul]
  norm_cast

/-- If `ω(star x * x) = 0`, then `ω(star a * x) = 0` for any `a`. -/
lemma kernel_degenerate_left (a : A) (hx : ω (star x * x) = 0) : ω (star a * x) = 0 := by
  have := cauchy_schwarz_ineq (ω := ω) (x := x) (y := a)
  rw [hx, zero_mul] at this
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm (by exact_mod_cast this) (sq_nonneg _)))

/-- If `ω(star x * x) = 0`, then `ω(star x * a) = 0` for any `a`. -/
lemma kernel_degenerate_right (a : A) (hx : ω (star x * x) = 0) : ω (star x * a) = 0 := by
  rw [conj_sym (ω := ω) (x := a) (y := x), kernel_degenerate_left (ω := ω) (x := x) (a := a) hx]
  simp

/-- If `ω(star x * x) = 0` and `ω(star y * y) = 0`, then `ω(star (x + y) * (x + y)) = 0`. -/
lemma kernel_closed_under_add (hx : ω (star x * x) = 0) (hy : ω (star y * y) = 0) : ω (star (x + y) * (x + y)) = 0 := by
  calc ω (star (x + y) * (x + y))
      = ω (star x * x + star x * y + star y * x + star y * y) := by
          rw [star_add, add_mul, mul_add, mul_add]
          ac_rfl
    _ = ω (star x * x) + ω (star x * y) + ω (star y * x) + ω (star y * y) := by
          rw [map_add, map_add, map_add]
    _ = 0 := by
          rw [hx, hy, kernel_degenerate_left (ω := ω) (x := y) (a := x) hy, kernel_degenerate_left (ω := ω) (x := x) (a := y) hx]
          ring

/-- If `ω(star x * x) = 0`, then `ω(star (c • x) * (c • x)) = 0` for any scalar `c`. -/
lemma kernel_closed_under_smul (hx : ω (star x * x) = 0) : ω (star (c • x) * (c • x)) = 0 := by
  rw [star_smul, smul_mul_assoc, mul_smul_comm, smul_smul, star_as_conj, map_smul, hx, smul_zero]

/-- If `ω(star x * x) = 0`, then `ω(star (a * x) * (a * x)) = 0` for any `a`. -/
lemma kernel_closed_under_left_mul (a : A) (hx : ω (star x * x) = 0) : ω (star (a * x) * (a * x)) = 0 := by
  have : star (a * x) * (a * x) = star (star a * a * x) * x := by
    rw [star_mul, star_mul, star_mul, star_star]; ac_rfl
  rw [this]; exact kernel_degenerate_left (ω := ω) (x := x) (a := star a * a * x) hx

/-- If `ω(star (x₁ - x₂) * (x₁ - x₂)) = 0`, then `ω(star x₁ * y) = ω(star x₂ * y)`. -/
lemma equiv_left (hx : ω (star (x₁ - x₂) * (x₁ - x₂)) = 0) :
    ω (star x₁ * y) = ω (star x₂ * y) := by
  have hcs := cauchy_schwarz_ineq (ω := ω) (x := y) (y := x₁ - x₂)
  have h0 : ω (star (x₁ - x₂) * y) = 0 := by
    have : (‖ω (star (x₁ - x₂) * y)‖ : ℝ)^2 ≤ 0 := by rw [hx, mul_zero] at hcs; exact_mod_cast hcs
    simpa [sq_eq_zero_iff] using le_antisymm this (sq_nonneg _)
  calc ω (star x₁ * y)
      = ω (star (x₂ + (x₁ - x₂)) * y) := by rw [add_sub_cancel]
    _ = ω (star x₂ * y + star (x₁ - x₂) * y) := by rw [star_add, add_mul]
    _ = ω (star x₂ * y) + ω (star (x₁ - x₂) * y) := ω.map_add _ _
    _ = ω (star x₂ * y) := by rw [h0, add_zero]

/-- If `ω(star (y₁ - y₂) * (y₁ - y₂)) = 0`, then `ω(star x * y₁) = ω(star x * y₂)`. -/
lemma equiv_right (hy : ω (star (y₁ - y₂) * (y₁ - y₂)) = 0) :
    ω (star x * y₁) = ω (star x * y₂) := by
  have hzero : ω (star x * (y₁ - y₂)) = 0 :=
    kernel_degenerate_left (ω := ω) (x := y₁ - y₂) (a := x) hy
  have hmul : star x * y₁ = star x * y₂ + star x * (y₁ - y₂) := by
    simp [sub_eq_add_neg, add_comm, add_left_comm, mul_add]
  calc
    ω (star x * y₁) = ω (star x * y₂ + star x * (y₁ - y₂)) := by rw [hmul]
    _ = ω (star x * y₂) + ω (star x * (y₁ - y₂)) := ω.map_add _ _
    _ = ω (star x * y₂) := by rw [hzero, add_zero]

/-- States map nonnegative elements to nonnegative reals. -/
lemma nonneg_of_nonneg {a : A} (ha : 0 ≤ a) : ∃ r : ℝ≥0, ω a = RCLike.ofReal (r : ℝ) := by
  -- From 0 ≤ a, we know a is in the closure of sums of star s * s
  rw [StarOrderedRing.nonneg_iff] at ha
  -- We show by induction that ω maps elements in this closure to nonnegative reals
  refine AddSubmonoid.closure_induction ?_ ?_ ?_ ha
  · -- Base case: for elements of the form star s * s
    intro x hx
    obtain ⟨s, rfl⟩ := hx
    exact ω.positive s
  · -- Zero case: ω(0) = 0
    use 0
    simp [RCLike.ofReal_zero]
  · -- Addition case: if ω(x) and ω(y) are nonnegative reals, so is ω(x + y)
    intro x y _ _ ihx ihy
    obtain ⟨rx, hx⟩ := ihx
    obtain ⟨ry, hy⟩ := ihy
    use rx + ry
    calc ω (x + y)
        = ω x + ω y := by rw [map_add]
      _ = RCLike.ofReal (rx : ℝ) + RCLike.ofReal (ry : ℝ) := by rw [hx, hy]
      _ = RCLike.ofReal ((rx : ℝ) + (ry : ℝ)) := by rw [RCLike.ofReal_add]
      _ = RCLike.ofReal ((rx + ry : ℝ≥0) : ℝ) := by simp [NNReal.coe_add]

/-- States are monotone with respect to the order defined by `StarOrderedRing`.

If a ≤ b in a `StarOrderedRing`, then there exists a nonnegative element (b - a)
such that ω(b) = ω(a) + ω(b - a). This shows that states preserve the order structure. -/
lemma monotone {a b : A} (hab : a ≤ b) : ∃ r : ℝ≥0, ω b = ω a + RCLike.ofReal (r : ℝ) := by
  -- From a ≤ b, we have b - a ≥ 0
  have h_nonneg : 0 ≤ b - a := by
    rwa [sub_nonneg]
  -- By positivity, ω(b - a) is a nonnegative real
  obtain ⟨r, hr⟩ := nonneg_of_nonneg (ω := ω) h_nonneg
  use r
  calc ω b
      = ω a + (ω b - ω a) := by ring
    _ = ω a + ω (b - a) := by rw [← map_sub]
    _ = ω a + RCLike.ofReal (r : ℝ) := by rw [hr]

/-- Bound on `ω(star b * star a * a * b)` using the C*-algebra inequality. -/
lemma star_mul_bound (a b : A) :
    ∃ r : ℝ≥0, ‖a‖ ^ 2 * ω (star b * b) = ω (star b * star a * a * b) + RCLike.ofReal (r : ℝ) := by
  have h_ineq : star b * star a * a * b ≤ ‖a‖ ^ 2 • (star b * b) :=
    NonUnitalCStarAlgebra.positive_conjugate_le_norm_smul (a := a) (b := b)
  -- Apply monotonicity
  obtain ⟨r, hr⟩ := monotone (ω := ω) h_ineq
  use r
  calc ‖a‖ ^ 2 * ω (star b * b)
      = (‖a‖ ^ 2 : ℂ) * ω (star b * b) := by norm_cast
    _ = (‖a‖ ^ 2 : ℂ) • ω (star b * b) := by rw [smul_eq_mul]
    _ = ω ((‖a‖ ^ 2 : ℂ) • (star b * b)) := by rw [map_smul]
    _ = ω (‖a‖ ^ 2 • (star b * b)) := by norm_cast
    _ = ω (star b * star a * a * b) + RCLike.ofReal (r : ℝ) := hr

/-- Real parts of a state are nonnegative on positive elements. -/
lemma real_eval_nonneg_of_nonneg {a : A} (ha : 0 ≤ a) : 0 ≤ (ω a).re := by
  obtain ⟨r, hr⟩ := nonneg_of_nonneg (ω := ω) ha
  have hr_nonneg : 0 ≤ (r : ℝ) := by exact_mod_cast r.property
  have hr_rewrite : (ω a).re = (r : ℝ) := by rw [hr]; simp
  exact hr_rewrite ▸ hr_nonneg

/-- States are monotone on real parts: `a ≤ b` implies `(ω a).re ≤ (ω b).re`. -/
lemma real_eval_le_of_le {a b : A} (hab : a ≤ b) : (ω a).re ≤ (ω b).re := by
  obtain ⟨r, hr⟩ := monotone (ω := ω) hab
  have h_re : (ω b).re = (ω a).re + (r : ℝ) := by
    have := congrArg Complex.re hr
    simpa [Complex.add_re, RCLike.ofReal_re] using this
  have hr_nonneg : 0 ≤ (r : ℝ) := by exact_mod_cast r.property
  have h_le : (ω a).re ≤ (ω a).re + (r : ℝ) := le_add_of_nonneg_right hr_nonneg
  exact h_re ▸ h_le

/-- If `ω(star x * x) = 0`, then `ω(x) = 0`. This uses the approximate unit. -/
lemma kernel_vanish_on_elem (hx : ω (star x * x) = 0) : ω x = 0 := by
  -- Prove by showing ‖ω(x)‖ < ε for all ε > 0
  by_contra h_ne
  push_neg at h_ne
  -- If ω(x) ≠ 0, then ‖ω(x)‖ > 0
  have h_pos : 0 < ‖ω x‖ := norm_pos_iff.mpr h_ne
  -- Set ε = ‖ω(x)‖ / 2 > 0
  set ε := ‖ω x‖ / 2 with hε_def
  have hε_pos : 0 < ε := by linarith
  -- Use CStarAlgebra.exists_approxUnit_mul_close to get e with ‖e * x - x‖ < ε
  obtain ⟨e, h_close, _⟩ := NonUnitalCStarAlgebra.exists_approxUnit_mul_close x hε_pos
  -- Key step: ω(e * x) = ω(star (star e) * x) = 0
  have h_ex_zero : ω (e * x) = 0 := by
    have : e * x = star (star e) * x := by simp only [star_star]
    rw [this]
    exact kernel_degenerate_left (ω := ω) (x := x) (a := star e) hx
  -- Combine to derive contradiction: ‖ω(x)‖ < ‖ω(x)‖ / 2
  have : ‖ω x‖ < ‖ω x‖ / 2 := by
    calc ‖ω x‖
        = ‖ω x - ω (e * x)‖ := by rw [h_ex_zero, sub_zero]
      _ = ‖ω (x - e * x)‖ := by rw [← map_sub]
      _ ≤ ‖x - e * x‖ := ω.norm_le_norm (x - e * x)
      _ = ‖-(e * x - x)‖ := by rw [neg_sub]
      _ = ‖e * x - x‖ := norm_neg _
      _ < ε := h_close
      _ = ‖ω x‖ / 2 := hε_def
  -- This is a contradiction
  linarith

/-- Bound on `‖ω(e * a)‖²` for self-adjoint contractions `e` (i.e. `star e = e` and `‖e‖ ≤ 1`). -/
lemma approx_unit_cauchy_schwarz_bound (a e : A) (he_star : star e = e) (he_norm : ‖e‖ ≤ 1) :
    ‖ω (e * a)‖ ^ 2 ≤ (ω (star a * a)).re := by
  -- Apply Cauchy-Schwarz inequality
  have h_cs := cauchy_schwarz_ineq (ω := ω) (x := a) (y := e)
  -- Since star e = e, we have e * a = star e * a
  have : e * a = star e * a := by rw [he_star]
  rw [← this] at h_cs
  -- ω(star e * e) = ω(e * e) is a nonnegative real ≤ 1
  have h_ee : ω (star e * e) = ω (e * e) := by rw [he_star]
  rw [h_ee] at h_cs
  -- Bound ω(e * e) ≤ 1 using contractivity
  have h_ee_bound : (ω (e * e)).re ≤ 1 := by
    have := ω.norm_le_norm (e * e)
    have h_norm_ee : ‖e * e‖ ≤ 1 := by
      calc ‖e * e‖
          ≤ ‖e‖ * ‖e‖ := norm_mul_le _ _
        _ ≤ 1 * 1 := by gcongr
        _ = 1 := mul_one _
    calc (ω (e * e)).re
        ≤ ‖ω (e * e)‖ := Complex.re_le_norm _
      _ ≤ ‖e * e‖ := this
      _ ≤ 1 := h_norm_ee
  obtain ⟨r, hr⟩ := ω.positive e
  have h_ee_real : ω (e * e) = RCLike.ofReal (r : ℝ) := by rw [he_star] at hr; exact hr
  -- Combine inequalities to get the final bound
  calc ‖ω (e * a)‖ ^ 2
      ≤ (ω (star a * a) * ω (e * e)).re := by
        -- Use Complex.le_def to extract real part inequality
        have h_le : (↑‖ω (e * a)‖ ^ 2 : ℂ).re ≤ (ω (star a * a) * ω (e * e)).re := by
          exact (Complex.le_def.mp h_cs).1
        have h_cast : (↑‖ω (e * a)‖ ^ 2 : ℂ).re = ‖ω (e * a)‖ ^ 2 := by norm_cast
        rw [h_cast] at h_le
        exact h_le
    _ = (ω (star a * a)).re * (ω (e * e)).re := by
        -- Both are nonnegative reals, so imaginary parts are 0
        obtain ⟨s1, hs1⟩ := ω.positive a
        obtain ⟨s2, hs2⟩ := ω.positive e
        simp [h_ee_real, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    _ = (ω (star a * a)).re * r := by rw [h_ee_real]; simp [Complex.ofReal_re]
    _ ≤ (ω (star a * a)).re * 1 := by
        gcongr
        · obtain ⟨s, hs⟩ := ω.positive a; erw [hs]; simp
        · simpa [h_ee_real, RCLike.ofReal_re] using h_ee_bound
    _ = (ω (star a * a)).re := mul_one _


/-- For nonzero `a`, the element `star a * a` is also nonzero. -/
lemma star_mul_self_ne_zero_of_ne_zero {a : A} (ha : a ≠ 0) : star a * a ≠ 0 := by
  rw [← norm_ne_zero_iff] at ha ⊢
  rw [CStarRing.norm_star_mul_self]
  intro h
  have : ‖a‖ = 0 := by nlinarith [sq_nonneg ‖a‖]
  exact ha this


/-- The norm of `star a * a` equals the square of the norm of `a`. -/
lemma norm_star_mul_self_eq_sq (a : A) : ‖star a * a‖ = ‖a‖ ^ 2 := by
  rw [pow_two]
  exact CStarRing.norm_star_mul_self

end State
