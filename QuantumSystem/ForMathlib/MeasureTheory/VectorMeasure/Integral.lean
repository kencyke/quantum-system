/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.MeasureTheory.Measure.Complex
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.MeasureTheory.VectorMeasure.Integral
public import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure

/-!
# Integrals against signed and complex measures

Complements to Mathlib's integral against vector measures (`∫ᵛ`), for signed and complex
measures.

* The variation of a signed measure is a finite measure (`SignedMeasure.totalVariation_eq_variation`
  and the finiteness of the Jordan parts), so bounded functions are integrable against every signed
  measure and `∫ᵛ` is additive in the measure without side conditions.
* **Uniqueness**: on a space where finite measures are determined by their integrals against
  bounded continuous functions (`HasOuterApproxClosed`), so are signed measures
  (`MeasureTheory.SignedMeasure.ext_of_forall_integral_eq`), and complex measures through their
  real and imaginary parts (`MeasureTheory.ComplexMeasure.ext_of_forall_integral_eq`). The proof
  splits a signed measure into its Jordan parts and applies the uniqueness for finite measures.

## Main results

* `MeasureTheory.SignedMeasure.integrable_toSignedMeasure_iff`,
  `MeasureTheory.SignedMeasure.integrable_boundedContinuousFunction` — integrability against
  `μ.toSignedMeasure` is integrability against `μ`; bounded continuous functions are integrable
  against every signed measure.
* `MeasureTheory.SignedMeasure.integral_eq_posPart_sub_negPart` — `∫ᵛ f ∂s = ∫ f ds⁺ - ∫ f ds⁻`.
* `MeasureTheory.SignedMeasure.ext_of_forall_integral_eq` — a signed measure is determined by its
  integrals against bounded continuous real functions.
* `MeasureTheory.ComplexMeasure.ext_re_im`, `MeasureTheory.ComplexMeasure.ext_of_forall_integral_eq`
  — a complex measure is determined by its real and imaginary parts, hence by their integrals.
* `MeasureTheory.SignedMeasure.ext_of_forall_integral_nnreal_eq`,
  `MeasureTheory.ComplexMeasure.ext_of_forall_integral_nnreal_eq` — the same with non-negative
  test functions.
* `MeasureTheory.ComplexMeasure.re_restrict`, `MeasureTheory.ComplexMeasure.im_restrict` — the real
  and imaginary parts commute with restriction.
* `MeasureTheory.ComplexMeasure.re_smul`, `MeasureTheory.ComplexMeasure.im_smul` — the real and
  imaginary parts of `c • μ` for a complex scalar `c`.
-/

@[expose] public section

open scoped ENNReal NNReal BoundedContinuousFunction

namespace MeasureTheory

variable {X : Type*} [MeasurableSpace X]

namespace SignedMeasure

/-- The variation of a signed measure is a finite measure. -/
instance isFiniteMeasure_variation (s : SignedMeasure X) : IsFiniteMeasure s.variation := by
  rw [← s.totalVariation_eq_variation]
  infer_instance

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

omit [NormedSpace ℝ G] in
/-- A function is integrable against `μ.toSignedMeasure` iff it is integrable against the finite
measure `μ`. -/
@[simp]
theorem integrable_toSignedMeasure_iff {μ : Measure X} [IsFiniteMeasure μ] {f : X → G} :
    VectorMeasure.Integrable μ.toSignedMeasure f ↔ Integrable f μ := by
  rw [VectorMeasure.Integrable, Measure.variation_toSignedMeasure]

/-- A bounded continuous function is integrable against every signed measure. -/
theorem integrable_boundedContinuousFunction [TopologicalSpace X] [OpensMeasurableSpace X]
    (s : SignedMeasure X) (g : X →ᵇ ℝ) : VectorMeasure.Integrable s g :=
  g.integrable s.variation

/-- Integration against a signed measure is integration against its positive Jordan part minus
integration against its negative Jordan part. -/
theorem integral_eq_posPart_sub_negPart (s : SignedMeasure X) {f : X → G}
    (h₁ : Integrable f s.toJordanDecomposition.posPart)
    (h₂ : Integrable f s.toJordanDecomposition.negPart) :
    ∫ᵛ x, f x ∂<•s =
      ∫ x, f x ∂s.toJordanDecomposition.posPart - ∫ x, f x ∂s.toJordanDecomposition.negPart := by
  conv_lhs => rw [← s.toSignedMeasure_toJordanDecomposition, JordanDecomposition.toSignedMeasure]
  rw [VectorMeasure.integral_sub_vectorMeasure (integrable_toSignedMeasure_iff.mpr h₁)
    (integrable_toSignedMeasure_iff.mpr h₂), VectorMeasure.integral_toSignedMeasure,
    VectorMeasure.integral_toSignedMeasure]

/-- **Uniqueness.** A signed measure on a space where finite measures are determined by their
integrals against bounded continuous functions is determined by its integrals against bounded
continuous real functions. -/
theorem ext_of_forall_integral_eq [TopologicalSpace X] [HasOuterApproxClosed X] [BorelSpace X]
    {s t : SignedMeasure X} (h : ∀ g : X →ᵇ ℝ, ∫ᵛ x, g x ∂<•s = ∫ᵛ x, g x ∂<•t) : s = t := by
  set js := s.toJordanDecomposition
  set jt := t.toJordanDecomposition
  have key : js.posPart + jt.negPart = jt.posPart + js.negPart :=
    ext_of_forall_integral_eq_of_IsFiniteMeasure fun g => by
      have hg := h g
      rw [s.integral_eq_posPart_sub_negPart (g.integrable _) (g.integrable _),
        t.integral_eq_posPart_sub_negPart (g.integrable _) (g.integrable _)] at hg
      rw [integral_add_measure (g.integrable _) (g.integrable _),
        integral_add_measure (g.integrable _) (g.integrable _)]
      linarith
  rw [← s.toSignedMeasure_toJordanDecomposition, ← t.toSignedMeasure_toJordanDecomposition,
    JordanDecomposition.toSignedMeasure, JordanDecomposition.toSignedMeasure,
    sub_eq_sub_iff_add_eq_add, ← Measure.toSignedMeasure_add, ← Measure.toSignedMeasure_add]
  exact Measure.toSignedMeasure_congr key

/-- **Uniqueness**, with non-negative test functions: a signed measure on a space where finite
measures are determined by their integrals against bounded continuous functions is determined by
its integrals against bounded continuous non-negative functions. -/
theorem ext_of_forall_integral_nnreal_eq [TopologicalSpace X] [HasOuterApproxClosed X]
    [BorelSpace X] {s t : SignedMeasure X}
    (h : ∀ g : X →ᵇ ℝ≥0, ∫ᵛ x, (g x : ℝ) ∂<•s = ∫ᵛ x, (g x : ℝ) ∂<•t) : s = t := by
  set js := s.toJordanDecomposition
  set jt := t.toJordanDecomposition
  have hi : ∀ (μ : Measure X) [IsFiniteMeasure μ] (g : X →ᵇ ℝ≥0),
      Integrable (fun x => (g x : ℝ)) μ := fun μ _ g =>
    BoundedContinuousFunction.integrable_of_nnreal μ g
  have key : js.posPart + jt.negPart = jt.posPart + js.negPart :=
    ext_of_forall_lintegral_eq_of_IsFiniteMeasure fun g => by
      have hg := h g
      rw [s.integral_eq_posPart_sub_negPart (hi _ g) (hi _ g),
        t.integral_eq_posPart_sub_negPart (hi _ g) (hi _ g)] at hg
      rw [lintegral_add_measure, lintegral_add_measure, lintegral_coe_eq_integral _ (hi _ g),
        lintegral_coe_eq_integral _ (hi _ g), lintegral_coe_eq_integral _ (hi _ g),
        lintegral_coe_eq_integral _ (hi _ g),
        ← ENNReal.ofReal_add (integral_nonneg fun _ => NNReal.coe_nonneg _)
          (integral_nonneg fun _ => NNReal.coe_nonneg _),
        ← ENNReal.ofReal_add (integral_nonneg fun _ => NNReal.coe_nonneg _)
          (integral_nonneg fun _ => NNReal.coe_nonneg _)]
      congr 1
      linarith
  rw [← s.toSignedMeasure_toJordanDecomposition, ← t.toSignedMeasure_toJordanDecomposition,
    JordanDecomposition.toSignedMeasure, JordanDecomposition.toSignedMeasure,
    sub_eq_sub_iff_add_eq_add, ← Measure.toSignedMeasure_add, ← Measure.toSignedMeasure_add]
  exact Measure.toSignedMeasure_congr key

end SignedMeasure

namespace ComplexMeasure

/-- A complex measure is determined by its real and imaginary parts. -/
theorem ext_re_im {μ ν : ComplexMeasure X} (hre : μ.re = ν.re) (him : μ.im = ν.im) : μ = ν :=
  equivSignedMeasure.injective (Prod.ext hre him)

/-- **Uniqueness.** A complex measure on a space where finite measures are determined by their
integrals against bounded continuous functions is determined by the integrals of bounded continuous
real functions against its real and imaginary parts. -/
theorem ext_of_forall_integral_eq [TopologicalSpace X] [HasOuterApproxClosed X] [BorelSpace X]
    {μ ν : ComplexMeasure X} (hre : ∀ g : X →ᵇ ℝ, ∫ᵛ x, g x ∂<•μ.re = ∫ᵛ x, g x ∂<•ν.re)
    (him : ∀ g : X →ᵇ ℝ, ∫ᵛ x, g x ∂<•μ.im = ∫ᵛ x, g x ∂<•ν.im) : μ = ν :=
  ext_re_im (SignedMeasure.ext_of_forall_integral_eq hre) (SignedMeasure.ext_of_forall_integral_eq him)

/-- **Uniqueness**, with non-negative test functions, through the real and imaginary parts. -/
theorem ext_of_forall_integral_nnreal_eq [TopologicalSpace X] [HasOuterApproxClosed X]
    [BorelSpace X] {μ ν : ComplexMeasure X}
    (hre : ∀ g : X →ᵇ ℝ≥0, ∫ᵛ x, (g x : ℝ) ∂<•μ.re = ∫ᵛ x, (g x : ℝ) ∂<•ν.re)
    (him : ∀ g : X →ᵇ ℝ≥0, ∫ᵛ x, (g x : ℝ) ∂<•μ.im = ∫ᵛ x, (g x : ℝ) ∂<•ν.im) : μ = ν :=
  ext_re_im (SignedMeasure.ext_of_forall_integral_nnreal_eq hre)
    (SignedMeasure.ext_of_forall_integral_nnreal_eq him)

/-- The real part of a restriction is the restriction of the real part. -/
theorem re_restrict (μ : ComplexMeasure X) {t : Set X} (ht : MeasurableSet t) :
    re (μ.restrict t) = μ.re.restrict t := by
  ext s hs
  simp [re, VectorMeasure.mapRangeL, VectorMeasure.mapRange_apply,
    VectorMeasure.restrict_apply _ ht hs]

/-- The imaginary part of a restriction is the restriction of the imaginary part. -/
theorem im_restrict (μ : ComplexMeasure X) {t : Set X} (ht : MeasurableSet t) :
    im (μ.restrict t) = μ.im.restrict t := by
  ext s hs
  simp [im, VectorMeasure.mapRangeL, VectorMeasure.mapRange_apply,
    VectorMeasure.restrict_apply _ ht hs]

/-- The real part of `c • μ` for a complex scalar `c` is `re c • re μ - im c • im μ`. -/
theorem re_smul (c : ℂ) (μ : ComplexMeasure X) : (c • μ).re = c.re • μ.re - c.im • μ.im := by
  ext s hs
  simp [re, im, VectorMeasure.mapRangeL, VectorMeasure.mapRange_apply, Complex.mul_re]

/-- The imaginary part of `c • μ` for a complex scalar `c` is `re c • im μ + im c • re μ`. -/
theorem im_smul (c : ℂ) (μ : ComplexMeasure X) : (c • μ).im = c.re • μ.im + c.im • μ.re := by
  ext s hs
  simp [re, im, VectorMeasure.mapRangeL, VectorMeasure.mapRange_apply, Complex.mul_im]

end ComplexMeasure

end MeasureTheory
