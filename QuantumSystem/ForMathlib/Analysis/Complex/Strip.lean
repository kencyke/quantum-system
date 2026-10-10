/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Analysis.Complex.OpenMapping

/-!
# Bounded holomorphic functions on horizontal strips

This file collects maximum-principle type results for bounded functions that are complex
differentiable on a horizontal strip `{z : ℂ | a < im z < b}` and continuous on its closure
`{z : ℂ | a ≤ im z ≤ b}`. As in `PhragmenLindelof.horizontal_strip`, the open and the closed
strip are written `im ⁻¹' Ioo a b` and `im ⁻¹' Icc a b`, and boundedness is phrased as in
Mathlib's Hadamard three lines theorem, `BddAbove ((norm ∘ f) '' im ⁻¹' Icc a b)`.

## Main results

* `Complex.HadamardThreeLines.norm_le_interp_of_im_mem_Icc`: **Hadamard's three lines theorem**
  on a horizontal strip, for functions with values in a complex normed space: if `‖f‖ ≤ Ma` on
  the line `im z = a` and `‖f‖ ≤ Mb` on the line `im z = b`, then on the closed strip
  `‖f z‖ ≤ Ma ^ ((b - im z) / (b - a)) * Mb ^ ((im z - a) / (b - a))`. It is obtained from
  `Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'` by a rotation.
* `Complex.norm_le_of_im_mem_Icc`: the maximum principle on a horizontal strip: a
  bound on both boundary lines holds on the whole closed strip.
* `Complex.eqOn_zero_of_eqOn_zero_im_eq_lower`, `Complex.eqOn_zero_of_eqOn_zero_im_eq_upper`:
  a bounded function vanishing on *one* boundary line vanishes on the closed strip.
* `Complex.im_nonneg_of_im_mem_Icc`: a bounded function with non-negative imaginary
  part on both boundary lines has non-negative imaginary part on the closed strip.
* `Complex.eqOn_const_of_im_eq_zero_on_boundary`: a bounded scalar function that is real on both
  boundary lines is constant on the closed strip.

Auxiliary facts on the strip itself: `Complex.closure_preimage_im_Ioo`,
`Complex.isConnected_preimage_im_Ioo`, `Complex.eqOn_preimage_im_Icc_of_eqOn_Ioo`.
-/

@[expose] public section

open Set Filter Function

namespace Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The closure of the open horizontal strip `im ⁻¹' Ioo a b` is the closed strip. -/
lemma closure_preimage_im_Ioo {a b : ℝ} (hab : a < b) :
    closure (im ⁻¹' Ioo a b) = im ⁻¹' Icc a b := by
  rw [closure_preimage_im, closure_Ioo hab.ne]

/-- The open horizontal strip `im ⁻¹' Ioo a b` is connected when `a < b`. -/
lemma isConnected_preimage_im_Ioo {a b : ℝ} (hab : a < b) : IsConnected (im ⁻¹' Ioo a b) := by
  refine ⟨⟨((a + b) / 2 : ℝ) * I, ?_⟩, ?_⟩
  · simp only [mem_preimage, mul_I_im, ofReal_re, mem_Ioo]
    constructor <;> linarith
  · exact ((convex_Ioo a b).linear_preimage imLm).isPreconnected

namespace HadamardThreeLines

/-- **Hadamard three lines theorem** on the horizontal strip `im ⁻¹' [a, b]`: let `f` be a bounded
function with values in a complex normed space, complex differentiable on the open strip
`im ⁻¹' (a, b)` and continuous on its closure. If `‖f z‖ ≤ Ma` on the line `im z = a` and
`‖f z‖ ≤ Mb` on the line `im z = b`, then
`‖f z‖ ≤ Ma ^ ((b - im z) / (b - a)) * Mb ^ ((im z - a) / (b - a))` on the closed strip. -/
theorem norm_le_interp_of_im_mem_Icc {f : ℂ → E} {a b Ma Mb : ℝ} {z : ℂ} (hab : a < b)
    (hd : DiffContOnCl ℂ f (im ⁻¹' Ioo a b)) (hB : BddAbove ((norm ∘ f) '' (im ⁻¹' Icc a b)))
    (ha : ∀ w : ℂ, w.im = a → ‖f w‖ ≤ Ma) (hb : ∀ w : ℂ, w.im = b → ‖f w‖ ≤ Mb)
    (hz : z ∈ im ⁻¹' Icc a b) :
    ‖f z‖ ≤ Ma ^ ((b - z.im) / (b - a)) * Mb ^ ((z.im - a) / (b - a)) := by
  -- Rotate the horizontal strip onto the vertical strip `re ⁻¹' [a, b]`.
  have hmaps : MapsTo (I * ·) (verticalStrip a b) (im ⁻¹' Ioo a b) := fun w hw ↦ by
    simpa [verticalStrip] using hw
  have hd' : DiffContOnCl ℂ (fun w ↦ f (I * w)) (verticalStrip a b) :=
    hd.comp (differentiable_id.const_mul I).diffContOnCl hmaps
  have hB' : BddAbove ((norm ∘ fun w ↦ f (I * w)) '' verticalClosedStrip a b) := by
    refine hB.mono ?_
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨I * w, by simpa [verticalClosedStrip] using hw, rfl⟩
  have hz' : -I * z ∈ verticalClosedStrip a b := by simpa [verticalClosedStrip] using hz
  have key : ‖f (I * (-I * z))‖ ≤
      Ma ^ (1 - ((-I * z).re - a) / (b - a)) * Mb ^ (((-I * z).re - a) / (b - a)) :=
    norm_le_interp_of_mem_verticalClosedStrip' hab hz' hd' hB'
      (fun w hw ↦ ha _ (by simpa using hw)) (fun w hw ↦ hb _ (by simpa using hw))
  have hzz : I * (-I * z) = z := by rw [← mul_assoc, mul_neg, I_mul_I, neg_neg, one_mul]
  have hre : (-I * z).re = z.im := by simp
  have hexp : 1 - (z.im - a) / (b - a) = (b - z.im) / (b - a) := by
    field_simp [(sub_pos.2 hab).ne']
    ring
  rwa [hzz, hre, hexp] at key

end HadamardThreeLines

/-- **Maximum principle** on the horizontal strip `im ⁻¹' [a, b]`: a bounded function, complex
differentiable on the open strip and continuous on its closure, which is bounded by `C` on both
boundary lines `im z = a` and `im z = b`, is bounded by `C` on the closed strip. -/
lemma norm_le_of_im_mem_Icc {f : ℂ → E} {a b C : ℝ} {z : ℂ}
    (hd : DiffContOnCl ℂ f (im ⁻¹' Ioo a b)) (hB : BddAbove ((norm ∘ f) '' (im ⁻¹' Icc a b)))
    (ha : ∀ w : ℂ, w.im = a → ‖f w‖ ≤ C) (hb : ∀ w : ℂ, w.im = b → ‖f w‖ ≤ C)
    (hz : z ∈ im ⁻¹' Icc a b) : ‖f z‖ ≤ C := by
  rcases lt_or_ge a b with hab | hab
  · have hC : 0 ≤ C := (norm_nonneg _).trans (ha (a * I) (by simp))
    have key := HadamardThreeLines.norm_le_interp_of_im_mem_Icc hab hd hB ha hb hz
    have hsum : (b - z.im) / (b - a) + (z.im - a) / (b - a) = 1 := by
      field_simp [(sub_pos.2 hab).ne']
      ring
    rwa [← Real.rpow_add' hC (by rw [hsum]; exact one_ne_zero), hsum, Real.rpow_one] at key
  · exact ha z (le_antisymm (hz.2.trans hab) hz.1)

/-- Two functions which are continuous on the closed strip `im ⁻¹' [a, b]` and agree on the open
strip `im ⁻¹' (a, b)` agree on the closed strip. -/
lemma eqOn_preimage_im_Icc_of_eqOn_Ioo {Y : Type*} [TopologicalSpace Y] [T2Space Y] {f g : ℂ → Y}
    {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (im ⁻¹' Icc a b)) (hg : ContinuousOn g (im ⁻¹' Icc a b))
    (h : EqOn f g (im ⁻¹' Ioo a b)) : EqOn f g (im ⁻¹' Icc a b) :=
  h.of_subset_closure hf hg (preimage_mono Ioo_subset_Icc_self)
    (closure_preimage_im_Ioo hab).symm.subset

/-- A bounded function, complex differentiable on the open strip `im ⁻¹' (a, b)` and continuous
on its closure, which vanishes on the lower boundary line `im z = a`, vanishes on the closed strip
`im ⁻¹' [a, b]`. -/
lemma eqOn_zero_of_eqOn_zero_im_eq_lower {f : ℂ → E} {a b : ℝ}
    (hd : DiffContOnCl ℂ f (im ⁻¹' Ioo a b)) (hB : BddAbove ((norm ∘ f) '' (im ⁻¹' Icc a b)))
    (ha : ∀ w : ℂ, w.im = a → f w = 0) : EqOn f 0 (im ⁻¹' Icc a b) := by
  rcases lt_or_ge a b with hab | hab
  · obtain ⟨C, hC⟩ := hB
    have hCb : ∀ w : ℂ, w.im = b → ‖f w‖ ≤ C := fun w hw ↦
      hC ⟨w, by simp [hw, hab.le], rfl⟩
    refine eqOn_preimage_im_Icc_of_eqOn_Ioo hab ?_ continuousOn_const fun z hz ↦ ?_
    · simpa [closure_preimage_im_Ioo hab] using hd.continuousOn
    have key := HadamardThreeLines.norm_le_interp_of_im_mem_Icc hab hd ⟨C, hC⟩
      (fun w hw ↦ (ha w hw).symm ▸ norm_zero.le) hCb (preimage_mono Ioo_subset_Icc_self hz)
    rw [Real.zero_rpow (div_pos (sub_pos.2 hz.2) (sub_pos.2 hab)).ne', zero_mul] at key
    exact norm_le_zero_iff.1 key
  · exact fun z hz ↦ ha z (le_antisymm (hz.2.trans hab) hz.1)

/-- A bounded function, complex differentiable on the open strip `im ⁻¹' (a, b)` and continuous
on its closure, which vanishes on the upper boundary line `im z = b`, vanishes on the closed strip
`im ⁻¹' [a, b]`. -/
lemma eqOn_zero_of_eqOn_zero_im_eq_upper {f : ℂ → E} {a b : ℝ}
    (hd : DiffContOnCl ℂ f (im ⁻¹' Ioo a b)) (hB : BddAbove ((norm ∘ f) '' (im ⁻¹' Icc a b)))
    (hb : ∀ w : ℂ, w.im = b → f w = 0) : EqOn f 0 (im ⁻¹' Icc a b) := by
  rcases lt_or_ge a b with hab | hab
  · obtain ⟨C, hC⟩ := hB
    have hCa : ∀ w : ℂ, w.im = a → ‖f w‖ ≤ C := fun w hw ↦
      hC ⟨w, by simp [hw, hab.le], rfl⟩
    refine eqOn_preimage_im_Icc_of_eqOn_Ioo hab ?_ continuousOn_const fun z hz ↦ ?_
    · simpa [closure_preimage_im_Ioo hab] using hd.continuousOn
    have key := HadamardThreeLines.norm_le_interp_of_im_mem_Icc hab hd ⟨C, hC⟩ hCa
      (fun w hw ↦ (hb w hw).symm ▸ norm_zero.le) (preimage_mono Ioo_subset_Icc_self hz)
    rw [Real.zero_rpow (div_pos (sub_pos.2 hz.1) (sub_pos.2 hab)).ne', mul_zero] at key
    exact norm_le_zero_iff.1 key
  · exact fun z hz ↦ hb z (le_antisymm hz.2 (hab.trans hz.1))

/-- A bounded scalar function, complex differentiable on the open strip `im ⁻¹' (a, b)` and
continuous on its closure, whose imaginary part is non-negative on both boundary lines
`im z = a` and `im z = b`, has non-negative imaginary part on the closed strip `im ⁻¹' [a, b]`. -/
lemma im_nonneg_of_im_mem_Icc {f : ℂ → ℂ} {a b : ℝ} {z : ℂ}
    (hd : DiffContOnCl ℂ f (im ⁻¹' Ioo a b)) (hB : BddAbove ((norm ∘ f) '' (im ⁻¹' Icc a b)))
    (ha : ∀ w : ℂ, w.im = a → 0 ≤ (f w).im) (hb : ∀ w : ℂ, w.im = b → 0 ≤ (f w).im)
    (hz : z ∈ im ⁻¹' Icc a b) : 0 ≤ (f z).im := by
  -- Apply the maximum principle to `exp (I * f)`, whose norm is `Real.exp (-(im f))`.
  have hnorm : ∀ w, ‖exp (I * f w)‖ = Real.exp (-(f w).im) := fun w ↦ by simp [norm_exp]
  obtain ⟨C, hC⟩ := hB
  have hd' : DiffContOnCl ℂ (fun w ↦ exp (I * f w)) (im ⁻¹' Ioo a b) :=
    differentiable_exp.comp_diffContOnCl (hd.const_smul I)
  have hB' : BddAbove ((norm ∘ fun w ↦ exp (I * f w)) '' (im ⁻¹' Icc a b)) := by
    refine ⟨Real.exp C, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    simp only [comp_apply, hnorm, Real.exp_le_exp]
    exact (neg_le_abs _).trans ((abs_im_le_norm _).trans (hC ⟨w, hw, rfl⟩))
  have key := norm_le_of_im_mem_Icc (C := 1) hd' hB'
    (fun w hw ↦ by simpa [hnorm] using ha w hw) (fun w hw ↦ by simpa [hnorm] using hb w hw) hz
  simpa [hnorm] using key

/-- A bounded scalar function, complex differentiable on the open strip `im ⁻¹' (a, b)` and
continuous on its closure, which is real on both boundary lines `im z = a` and `im z = b`, is
constant on the closed strip `im ⁻¹' [a, b]`: it agrees there with its value at any point `w` of
the closed strip. -/
lemma eqOn_const_of_im_eq_zero_on_boundary {f : ℂ → ℂ} {a b : ℝ} {w : ℂ} (hab : a < b)
    (hd : DiffContOnCl ℂ f (im ⁻¹' Ioo a b)) (hB : BddAbove ((norm ∘ f) '' (im ⁻¹' Icc a b)))
    (ha : ∀ z : ℂ, z.im = a → (f z).im = 0) (hb : ∀ z : ℂ, z.im = b → (f z).im = 0)
    (hw : w ∈ im ⁻¹' Icc a b) : EqOn f (fun _ ↦ f w) (im ⁻¹' Icc a b) := by
  -- The imaginary part of `f` vanishes on the closed strip, by the maximum principle for `±f`.
  have hB' : BddAbove ((norm ∘ fun z ↦ -f z) '' (im ⁻¹' Icc a b)) := by
    simpa [comp_def] using hB
  have him : ∀ z ∈ im ⁻¹' Icc a b, (f z).im = 0 := fun z hz ↦ by
    have h₁ := im_nonneg_of_im_mem_Icc hd hB (fun w hw ↦ (ha w hw).ge)
      (fun w hw ↦ (hb w hw).ge) hz
    have h₂ := im_nonneg_of_im_mem_Icc hd.neg hB' (fun w hw ↦ by simp [ha w hw])
      (fun w hw ↦ by simp [hb w hw]) hz
    simp only [Pi.neg_apply, neg_im, Left.nonneg_neg_iff] at h₂
    exact le_antisymm h₂ h₁
  -- A holomorphic function with constant imaginary part on a connected open set is constant.
  have hopen : IsOpen (im ⁻¹' Ioo a b) := isOpen_Ioo.preimage continuous_im
  obtain ⟨c, hc⟩ := (hd.differentiableOn.analyticOnNhd hopen).eq_const_of_im_eq_const
    (fun z hz ↦ him z (preimage_mono Ioo_subset_Icc_self hz)) hopen
    (isConnected_preimage_im_Ioo hab)
  have hcont : ContinuousOn f (im ⁻¹' Icc a b) := by
    simpa [closure_preimage_im_Ioo hab] using hd.continuousOn
  have hconst : EqOn f (fun _ ↦ c) (im ⁻¹' Icc a b) :=
    eqOn_preimage_im_Icc_of_eqOn_Ioo hab hcont continuousOn_const hc
  intro z hz
  rw [hconst hz, hconst hw]

end Complex
