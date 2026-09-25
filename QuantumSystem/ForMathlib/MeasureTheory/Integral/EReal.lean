/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Extended-real-valued integrals and the integral of `-log`

For `f : α → EReal`, `MeasureTheory.erealIntegral μ f` is the extended Lebesgue integral
`∫ f dμ = ∫ f⁺ dμ - ∫ f⁻ dμ ∈ EReal`, the integrals of the positive and negative parts being taken
in `ℝ≥0∞` and subtracted in `EReal`. It is `+∞` when only `∫ f⁺` is infinite and `-∞ = ⊥` when only
`∫ f⁻` is infinite. When both are infinite, `EReal` subtraction `⊤ - ⊤ = ⊥` returns `⊥` as a junk
value. Mathlib has no such integral: the Bochner integral needs integrability, and `lintegral` only
takes values in `ℝ≥0∞`.

The main instance is `MeasureTheory.negLogIntegral μ = ∫ -log t dμ(t)` for a measure `μ` on `ℝ`,
with `-log t := -ENNReal.log (ENNReal.ofReal t)`, which is `+∞` for `t ≤ 0` (unlike `Real.log`, whose
junk value is `Real.log 0 = 0`). Araki's relative entropy `S = -∫ log λ dμ(λ)`, for `μ` the spectral
measure of a relative modular operator, has this form. `negLogIntegral μ ≠ ⊥` whenever
`∫ t dμ(t) < ∞` (`MeasureTheory.negLogIntegral_ne_bot_of_lintegral_ne_top`).

## Main definitions

* `MeasureTheory.erealIntegral μ f` — `∫ f dμ ∈ EReal` for `f : α → EReal`.
* `MeasureTheory.negLogIntegral μ` — `∫ -log t dμ(t) ∈ EReal`.

## Main results

* `MeasureTheory.erealIntegral_eq_lintegral_sub_lintegral` — any decomposition `f = u - v` with
  `∫ v < ∞` computes `∫ f`; inequality versions
  `MeasureTheory.lintegral_sub_lintegral_le_erealIntegral`,
  `MeasureTheory.erealIntegral_le_lintegral_sub_lintegral`.
* `MeasureTheory.erealIntegral_mono_ae`, `MeasureTheory.erealIntegral_congr_ae` — monotonicity.
* `MeasureTheory.erealIntegral_coe` — agreement with the Bochner integral for integrable real `f`;
  `MeasureTheory.erealIntegral_add_coe` — `∫ (f + g) = ∫ f + ∫ g` for integrable real `g`.
* `MeasureTheory.erealIntegral_dirac`, `MeasureTheory.erealIntegral_smul_measure`,
  `MeasureTheory.erealIntegral_add_measure`, `MeasureTheory.erealIntegral_finsetSum_measure`,
  `MeasureTheory.erealIntegral_map` — dependence on the measure; additivity in the measure is
  unconditional.
* `MeasureTheory.negLogIntegral_finsetSum_smul_dirac`,
  `MeasureTheory.negLogIntegral_finsetSum_smul_dirac_eq_top` — `∫ -log` against `∑ cᵢ δ_{aᵢ}`.
* `MeasureTheory.negLogIntegral_eq_neg_integral` — agreement with `-∫ Real.log t dμ(t)` when `log`
  is integrable and `μ` lives on `(0, ∞)`.
* `MeasureTheory.negLogIntegral_map_mul` — `∫ -log (c t) dμ(t) = ∫ -log t dμ(t) - μ(ℝ) log c`.
* `MeasureTheory.negLogIntegral_eq_top_of_measure_Iic_ne_zero` — a positive mass at `(-∞, 0]`
  forces the value `⊤`; `MeasureTheory.negLogIntegral_ne_top_of_ae_ge` — a finite measure living on
  `[δ, ∞)`, `δ > 0`, gives a value `< ⊤`.
* `MeasureTheory.mul_log_le_negLogIntegral` — **Jensen's inequality** for the convex function
  `-log`: `m log (m / b) ≤ ∫ -log t dμ(t)` for a finite measure of mass `m` with `∫ t⁺ dμ(t) ≤ b`.
* `MeasureTheory.lintegral_Ioi_ofReal_inv_add_sub_inv_one_add`,
  `MeasureTheory.lintegral_Ioi_ofReal_inv_one_add_sub_inv_add` — the **resolvent representation**
  `-log λ = ∫_{t > 0} ((t + λ)⁻¹ - (1 + t)⁻¹) dt` for `λ ≥ 0`, split into positive and negative
  parts (so that `λ = 0`, where `-log 0 = +∞`, is included).
* `MeasureTheory.negLogIntegral_le_of_integral_inv_add_le` — **comparison through resolvents**:
  `∫ (t + λ)⁻¹ dμ ≤ ∫ (t + λ)⁻¹ dν` for all `t > 0` (with `μ` on `[0, ∞)`, `ν(ℝ) ≤ μ(ℝ)`,
  `∫ -log dν ≠ -∞`) implies `∫ -log dμ ≤ ∫ -log dν`, by Tonelli's theorem.
-/

@[expose] public section

open scoped ENNReal NNReal

namespace MeasureTheory

/-! ### Arithmetic in `EReal` -/

/-- An extended real is its positive part minus its negative part. -/
private lemma toENNReal_sub_toENNReal_neg (x : EReal) :
    (x.toENNReal : EReal) - (-x).toENNReal = x := by
  induction x using EReal.rec with
  | bot => simp
  | top => simp
  | coe x =>
    rw [← EReal.coe_neg, EReal.real_coe_toENNReal, EReal.real_coe_toENNReal,
      EReal.coe_ennreal_ofReal, EReal.coe_ennreal_ofReal, ← EReal.coe_sub, EReal.coe_eq_coe_iff]
    rcases le_total x 0 with hx | hx
    · rw [max_eq_right hx, max_eq_left (by linarith), zero_sub, neg_neg]
    · rw [max_eq_left hx, max_eq_right (by linarith), sub_zero]

/-- `ofReal r - ofReal (-r) = r` in `EReal`. -/
private lemma coe_ofReal_sub_coe_ofReal_neg (r : ℝ) :
    (ENNReal.ofReal r : EReal) - ENNReal.ofReal (-r) = r := by
  have := toENNReal_sub_toENNReal_neg (r : EReal)
  rwa [← EReal.coe_neg, EReal.real_coe_toENNReal, EReal.real_coe_toENNReal] at this

/-- For finite `b, d`, `a - b ≤ c - d` in `EReal` iff `a + d ≤ b + c` in `ℝ≥0∞`. -/
private lemma coe_sub_coe_le_coe_sub_coe_iff {a b c d : ℝ≥0∞} (hb : b ≠ ∞) (hd : d ≠ ∞) :
    (a : EReal) - b ≤ c - d ↔ a + d ≤ b + c := by
  lift b to ℝ≥0 using hb
  lift d to ℝ≥0 using hd
  induction a using ENNReal.recTopCoe with
  | top =>
    induction c using ENNReal.recTopCoe with
    | top => simp
    | coe c =>
      simp only [EReal.coe_ennreal_top, EReal.coe_nnreal_eq_coe_real, EReal.top_sub_coe,
        top_le_iff, top_add]
      exact ⟨fun h => absurd h (by rw [← EReal.coe_sub]; exact EReal.coe_ne_top _),
        fun h => absurd h (by rw [← ENNReal.coe_add]; exact ENNReal.coe_ne_top)⟩
  | coe a =>
    induction c using ENNReal.recTopCoe with
    | top =>
      simp only [EReal.coe_ennreal_top, EReal.coe_nnreal_eq_coe_real, EReal.top_sub_coe, le_top,
        add_top]
    | coe c =>
      simp only [EReal.coe_nnreal_eq_coe_real, ← EReal.coe_sub, EReal.coe_le_coe_iff,
        ← ENNReal.coe_add, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, NNReal.coe_add]
      constructor <;> intro h <;> linarith

/-- `a - d ≠ ⊥` in `EReal` for `a, d ∈ ℝ≥0∞` with `d` finite. -/
private lemma coe_sub_coe_ne_bot (a : ℝ≥0∞) {d : ℝ≥0∞} (hd : d ≠ ∞) : (a : EReal) - d ≠ ⊥ := by
  rw [Ne, sub_eq_add_neg, EReal.add_eq_bot_iff, EReal.neg_eq_bot_iff, EReal.coe_ennreal_eq_top_iff]
  simp [EReal.coe_ennreal_ne_bot, hd]

/-- `(a + b) - (c + d) = (a - c) + (b - d)` for coerced elements of `ℝ≥0∞`. -/
private lemma coe_add_sub_coe_add (a b c d : ℝ≥0∞) :
    ((a + b : ℝ≥0∞) : EReal) - (c + d : ℝ≥0∞) = ((a : EReal) - c) + ((b : EReal) - d) := by
  rcases eq_or_ne c ∞ with rfl | hc
  · simp
  rcases eq_or_ne d ∞ with rfl | hd
  · simp
  have hcd : ((c + d : ℝ≥0∞) : EReal) ≠ ⊤ := by
    rw [Ne, EReal.coe_ennreal_eq_top_iff]
    exact ENNReal.add_ne_top.mpr ⟨hc, hd⟩
  rcases eq_or_ne a ∞ with rfl | ha
  · rw [top_add, EReal.coe_ennreal_top, EReal.top_sub hcd,
      EReal.top_sub (by rwa [Ne, EReal.coe_ennreal_eq_top_iff]),
      EReal.top_add_of_ne_bot (coe_sub_coe_ne_bot b hd)]
  rcases eq_or_ne b ∞ with rfl | hb
  · rw [add_top, EReal.coe_ennreal_top, EReal.top_sub hcd,
      EReal.top_sub (by rwa [Ne, EReal.coe_ennreal_eq_top_iff]),
      EReal.add_top_of_ne_bot (coe_sub_coe_ne_bot a hc)]
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  lift c to ℝ≥0 using hc
  lift d to ℝ≥0 using hd
  simp only [← ENNReal.coe_add, EReal.coe_nnreal_eq_coe_real, NNReal.coe_add, ← EReal.coe_sub,
    ← EReal.coe_add]
  congr 1
  ring

/-- `-(x + r) + r = -x` in `EReal` for real `r`. -/
private lemma neg_add_coe_add_coe (x : EReal) (r : ℝ) : -(x + r) + r = -x := by
  induction x using EReal.rec with
  | bot => simp
  | top => simp
  | coe x =>
    rw [← EReal.coe_add, ← EReal.coe_neg, ← EReal.coe_add, ← EReal.coe_neg]
    congr 1
    ring

/-- Pointwise form of `u - v ≤ x`, split into positive and negative parts. -/
private lemma add_toENNReal_neg_le_of_sub_le {u v : ℝ≥0∞} {x : EReal} (h : (u : EReal) - v ≤ x) :
    u + (-x).toENNReal ≤ v + x.toENNReal ∧ (-x).toENNReal ≤ v := by
  rcases eq_or_ne v ∞ with rfl | hv
  · simp
  have hn : (-x).toENNReal ≠ ∞ := fun hn => by
    rw [EReal.toENNReal_eq_top_iff, EReal.neg_eq_top_iff] at hn
    subst hn
    rw [le_bot_iff, sub_eq_add_neg, EReal.add_eq_bot_iff, EReal.neg_eq_bot_iff,
      EReal.coe_ennreal_eq_top_iff] at h
    exact h.elim (EReal.coe_ennreal_ne_bot u) hv
  rw [← toENNReal_sub_toENNReal_neg x, coe_sub_coe_le_coe_sub_coe_iff hv hn] at h
  refine ⟨h, ?_⟩
  rcases le_or_gt 0 x with hx | hx
  · rw [EReal.toENNReal_of_nonpos (x := -x) (by simpa using hx)]
    exact zero_le
  · rw [EReal.toENNReal_of_nonpos (x := x) hx.le, add_zero] at h
    exact le_trans le_add_self h

/-- Pointwise form of `x ≤ u - v`, split into positive and negative parts. -/
private lemma toENNReal_add_le_of_le_sub {u v : ℝ≥0∞} {x : EReal} (h : x ≤ (u : EReal) - v) :
    x.toENNReal + v ≤ u + (-x).toENNReal := by
  rcases eq_or_ne v ∞ with rfl | hv
  · rw [EReal.coe_ennreal_top, EReal.sub_top, le_bot_iff] at h
    simp [h]
  rcases eq_or_ne (-x).toENNReal ∞ with hn | hn
  · simp [hn]
  rw [← toENNReal_sub_toENNReal_neg x, coe_sub_coe_le_coe_sub_coe_iff hn hv] at h
  rwa [add_comm u]

/-! ### The extended integral -/

section ERealIntegral

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α} {f g : α → EReal}

/-- The extended Lebesgue integral `∫ f dμ = ∫ f⁺ dμ - ∫ f⁻ dμ ∈ EReal` of `f : α → EReal`. It is
`⊥` exactly when `∫ f⁻ dμ = ∞` (`MeasureTheory.erealIntegral_eq_bot_iff`); this is the value
`-∞` when `∫ f⁺ dμ < ∞`, and a junk value when both integrals are infinite. -/
noncomputable def erealIntegral (μ : Measure α) (f : α → EReal) : EReal :=
  (∫⁻ a, (f a).toENNReal ∂μ : ℝ≥0∞) - (∫⁻ a, (-f a).toENNReal ∂μ : ℝ≥0∞)

/-- A decomposition `u - v ≤ f` with `∫ v < ∞` bounds `∫ f` from below. -/
theorem lintegral_sub_lintegral_le_erealIntegral (hf : AEMeasurable f μ) {u v : α → ℝ≥0∞}
    (hv : ∫⁻ a, v a ∂μ ≠ ∞) (h : ∀ᵐ a ∂μ, (u a : EReal) - v a ≤ f a) :
    ((∫⁻ a, u a ∂μ : ℝ≥0∞) : EReal) - (∫⁻ a, v a ∂μ : ℝ≥0∞) ≤ erealIntegral μ f := by
  have h' := h.mono fun a ha => add_toENNReal_neg_le_of_sub_le ha
  have hN : ∫⁻ a, (-f a).toENNReal ∂μ ≠ ∞ :=
    ne_top_of_le_ne_top hv (lintegral_mono_ae (h'.mono fun a ha => ha.2))
  rw [erealIntegral, coe_sub_coe_le_coe_sub_coe_iff hv hN]
  calc ∫⁻ a, u a ∂μ + ∫⁻ a, (-f a).toENNReal ∂μ
      ≤ ∫⁻ a, u a + (-f a).toENNReal ∂μ := le_lintegral_add _ _
    _ ≤ ∫⁻ a, v a + (f a).toENNReal ∂μ := lintegral_mono_ae (h'.mono fun a ha => ha.1)
    _ = _ := lintegral_add_right' _ hf.ereal_toENNReal

/-- A decomposition `f ≤ u - v` with `∫ v < ∞` bounds `∫ f` from above. -/
theorem erealIntegral_le_lintegral_sub_lintegral (hf : AEMeasurable f μ) {u v : α → ℝ≥0∞}
    (hv : ∫⁻ a, v a ∂μ ≠ ∞) (h : ∀ᵐ a ∂μ, f a ≤ (u a : EReal) - v a) :
    erealIntegral μ f ≤ ((∫⁻ a, u a ∂μ : ℝ≥0∞) : EReal) - (∫⁻ a, v a ∂μ : ℝ≥0∞) := by
  rw [erealIntegral]
  rcases eq_or_ne (∫⁻ a, (-f a).toENNReal ∂μ) ∞ with hN | hN
  · rw [hN, EReal.coe_ennreal_top, EReal.sub_top]
    exact bot_le
  rw [coe_sub_coe_le_coe_sub_coe_iff hN hv]
  calc ∫⁻ a, (f a).toENNReal ∂μ + ∫⁻ a, v a ∂μ
      ≤ ∫⁻ a, (f a).toENNReal + v a ∂μ := le_lintegral_add _ _
    _ ≤ ∫⁻ a, u a + (-f a).toENNReal ∂μ :=
        lintegral_mono_ae (h.mono fun a ha => toENNReal_add_le_of_le_sub ha)
    _ = _ := by
        rw [lintegral_add_right' (g := fun a => (-f a).toENNReal) _ hf.neg.ereal_toENNReal,
          add_comm]

/-- Any decomposition `f = u - v` with `∫ v < ∞` computes `∫ f`. -/
theorem erealIntegral_eq_lintegral_sub_lintegral (hf : AEMeasurable f μ) {u v : α → ℝ≥0∞}
    (hv : ∫⁻ a, v a ∂μ ≠ ∞) (h : ∀ᵐ a ∂μ, (u a : EReal) - v a = f a) :
    erealIntegral μ f = ((∫⁻ a, u a ∂μ : ℝ≥0∞) : EReal) - (∫⁻ a, v a ∂μ : ℝ≥0∞) :=
  le_antisymm (erealIntegral_le_lintegral_sub_lintegral hf hv (h.mono fun _ ha => ha.ge))
    (lintegral_sub_lintegral_le_erealIntegral hf hv (h.mono fun _ ha => ha.le))

/-- The extended integral is monotone. -/
theorem erealIntegral_mono_ae (h : ∀ᵐ a ∂μ, f a ≤ g a) : erealIntegral μ f ≤ erealIntegral μ g :=
  EReal.sub_le_sub
    (EReal.coe_ennreal_le_coe_ennreal_iff.mpr
      (lintegral_mono_ae (h.mono fun _ ha => EReal.toENNReal_le_toENNReal ha)))
    (EReal.coe_ennreal_le_coe_ennreal_iff.mpr
      (lintegral_mono_ae (h.mono fun _ ha => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr
        ha))))

/-- The extended integral only depends on the almost-everywhere class of the integrand. -/
theorem erealIntegral_congr_ae (h : f =ᵐ[μ] g) : erealIntegral μ f = erealIntegral μ g :=
  le_antisymm (erealIntegral_mono_ae (h.mono fun _ ha => ha.le))
    (erealIntegral_mono_ae (h.mono fun _ ha => ha.ge))

/-- `∫ f⁻ dμ = ∞` exactly when the extended integral is `⊥`. -/
theorem erealIntegral_eq_bot_iff : erealIntegral μ f = ⊥ ↔ ∫⁻ a, (-f a).toENNReal ∂μ = ∞ := by
  rw [erealIntegral, sub_eq_add_neg, EReal.add_eq_bot_iff, EReal.neg_eq_bot_iff,
    EReal.coe_ennreal_eq_top_iff]
  simp [EReal.coe_ennreal_ne_bot]

/-- **Agreement with the Bochner integral** for integrable real functions. -/
theorem erealIntegral_coe {g : α → ℝ} (hg : Integrable g μ) :
    erealIntegral μ (fun a => (g a : EReal)) = ((∫ a, g a ∂μ : ℝ) : EReal) := by
  have h₁ : ∫⁻ a, ENNReal.ofReal (g a) ∂μ ≠ ∞ := hg.lintegral_lt_top.ne
  have h₂ : ∫⁻ a, ENNReal.ofReal (-g a) ∂μ ≠ ∞ := hg.neg.lintegral_lt_top.ne
  rw [erealIntegral, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hg, EReal.coe_sub,
    EReal.coe_ennreal_toReal h₁, EReal.coe_ennreal_toReal h₂]
  simp only [← EReal.coe_neg, EReal.real_coe_toENNReal]

/-- An integrable real function below `f` bounds `∫ f` from below. -/
theorem integral_le_erealIntegral {g : α → ℝ} (hg : Integrable g μ)
    (h : ∀ᵐ a ∂μ, (g a : EReal) ≤ f a) : ((∫ a, g a ∂μ : ℝ) : EReal) ≤ erealIntegral μ f :=
  erealIntegral_coe hg ▸ erealIntegral_mono_ae h

/-- An integrable real function above `f` bounds `∫ f` from above. -/
theorem erealIntegral_le_integral {g : α → ℝ} (hg : Integrable g μ)
    (h : ∀ᵐ a ∂μ, f a ≤ (g a : EReal)) : erealIntegral μ f ≤ ((∫ a, g a ∂μ : ℝ) : EReal) :=
  erealIntegral_coe hg ▸ erealIntegral_mono_ae h

/-- Adding an integrable real function adds its Bochner integral:
`∫ (f + g) = ∫ f + ∫ g` (unconditionally in `f`, thanks to the value `⊥`). -/
theorem erealIntegral_add_coe (hf : AEMeasurable f μ) {g : α → ℝ} (hg : Integrable g μ) :
    erealIntegral μ (fun a => f a + g a) = erealIntegral μ f + ((∫ a, g a ∂μ : ℝ) : EReal) := by
  have hgp : ∫⁻ a, ENNReal.ofReal (g a) ∂μ ≠ ∞ := hg.lintegral_lt_top.ne
  have hgn : ∫⁻ a, ENNReal.ofReal (-g a) ∂μ ≠ ∞ := hg.neg.lintegral_lt_top.ne
  have hgm : AEMeasurable (fun a => ENNReal.ofReal (g a)) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable hg.aemeasurable
  have hgm' : AEMeasurable (fun a => ENNReal.ofReal (-g a)) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable hg.neg.aemeasurable
  rcases eq_or_ne (∫⁻ a, (-f a).toENNReal ∂μ) ∞ with hN | hN
  · -- Both sides are `⊥`: `f⁻ ≤ (f + g)⁻ + g⁺`.
    rw [erealIntegral_eq_bot_iff.mpr hN, EReal.bot_add, erealIntegral_eq_bot_iff]
    by_contra hne
    refine hN.not_lt (lt_of_le_of_lt (b := ∫⁻ a, (-(f a + g a)).toENNReal +
      ENNReal.ofReal (g a) ∂μ) (lintegral_mono fun a => ?_) ?_)
    · rw [← EReal.real_coe_toENNReal, ← neg_add_coe_add_coe (f a) (g a)]
      exact EReal.toENNReal_add_le
    · rw [lintegral_add_right' _ hgm]
      exact ENNReal.add_lt_top.mpr ⟨lt_top_iff_ne_top.mpr hne, lt_top_iff_ne_top.mpr hgp⟩
  have key := erealIntegral_eq_lintegral_sub_lintegral (μ := μ) (f := fun a => f a + g a)
    (hf.add (measurable_coe_real_ereal.comp_aemeasurable hg.aemeasurable))
    (u := fun a => (f a).toENNReal + ENNReal.ofReal (g a))
    (v := fun a => (-f a).toENNReal + ENNReal.ofReal (-g a))
    (by
      rw [lintegral_add_right' _ hgm']
      exact ENNReal.add_ne_top.mpr ⟨hN, hgn⟩)
    (Filter.Eventually.of_forall fun a => by
      rw [coe_add_sub_coe_add, toENNReal_sub_toENNReal_neg, coe_ofReal_sub_coe_ofReal_neg])
  rw [key, lintegral_add_right' _ hgm, lintegral_add_right' _ hgm', coe_add_sub_coe_add,
    ← erealIntegral_coe hg, erealIntegral, erealIntegral]
  simp only [← EReal.coe_neg, EReal.real_coe_toENNReal]

/-- The extended integral against the zero measure vanishes. -/
@[simp]
theorem erealIntegral_zero_measure (f : α → EReal) : erealIntegral 0 f = 0 := by
  simp [erealIntegral]

/-- The extended integral against a Dirac mass is the value at the point. -/
@[simp]
theorem erealIntegral_dirac [MeasurableSingletonClass α] (a : α) (f : α → EReal) :
    erealIntegral (Measure.dirac a) f = f a := by
  rw [erealIntegral, lintegral_dirac, lintegral_dirac, toENNReal_sub_toENNReal_neg]

/-- The extended integral is homogeneous under scaling of the measure. -/
theorem erealIntegral_smul_measure (c : ℝ≥0) (μ : Measure α) (f : α → EReal) :
    erealIntegral (c • μ) f = ((c : ℝ) : EReal) * erealIntegral μ f := by
  rw [erealIntegral, erealIntegral, lintegral_smul_measure, lintegral_smul_measure,
    ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul, EReal.coe_ennreal_mul,
    EReal.coe_ennreal_mul, ← EReal.mul_sub_of_nonneg_of_ne_top (EReal.coe_ennreal_nonneg _)
      (by simp), EReal.coe_nnreal_eq_coe_real]

/-- The extended integral is additive in the measure (unconditionally, thanks to the value `⊥`). -/
theorem erealIntegral_add_measure (μ ν : Measure α) (f : α → EReal) :
    erealIntegral (μ + ν) f = erealIntegral μ f + erealIntegral ν f := by
  rw [erealIntegral, erealIntegral, erealIntegral, lintegral_add_measure, lintegral_add_measure,
    coe_add_sub_coe_add]

/-- The extended integral against a finite sum of measures. -/
theorem erealIntegral_finsetSum_measure {ι : Type*} (s : Finset ι) (μ : ι → Measure α)
    (f : α → EReal) : erealIntegral (∑ i ∈ s, μ i) f = ∑ i ∈ s, erealIntegral (μ i) f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, erealIntegral_add_measure, ih]

/-- Change of variables for the extended integral. -/
theorem erealIntegral_map {β : Type*} [MeasurableSpace β] {φ : α → β} {f : β → EReal}
    (hφ : AEMeasurable φ μ) (hf : AEMeasurable f (μ.map φ)) :
    erealIntegral (μ.map φ) f = erealIntegral μ (f ∘ φ) := by
  rw [erealIntegral, erealIntegral, lintegral_map' hf.ereal_toENNReal hφ,
    lintegral_map' (f := fun b => (-f b).toENNReal) hf.neg.ereal_toENNReal hφ]
  rfl

end ERealIntegral

/-! ### The integral of `-log` -/

variable {μ : Measure ℝ}

/-- The extended integral `∫ -log t dμ(t) ∈ EReal`, with `-log t = +∞` for `t ≤ 0`. It is `⊥`
exactly when `∫ log⁺ t dμ(t) = ∞` (`MeasureTheory.negLogIntegral_eq_bot_iff`). -/
noncomputable def negLogIntegral (μ : Measure ℝ) : EReal :=
  erealIntegral μ fun t => -ENNReal.log (ENNReal.ofReal t)

private lemma measurable_negLog : Measurable fun t : ℝ => -ENNReal.log (ENNReal.ofReal t) :=
  (ENNReal.measurable_log.comp ENNReal.measurable_ofReal).neg

/-- The integral of `-log` against the zero measure vanishes. -/
@[simp]
theorem negLogIntegral_zero : negLogIntegral 0 = 0 :=
  erealIntegral_zero_measure _

/-- The integral of `-log` against a Dirac mass is the value of `-log` at the point. -/
@[simp]
theorem negLogIntegral_dirac (a : ℝ) :
    negLogIntegral (Measure.dirac a) = -ENNReal.log (ENNReal.ofReal a) :=
  erealIntegral_dirac a _

/-- `negLogIntegral` is homogeneous under scaling of the measure. -/
theorem negLogIntegral_smul (c : ℝ≥0) (μ : Measure ℝ) :
    negLogIntegral (c • μ) = ((c : ℝ) : EReal) * negLogIntegral μ :=
  erealIntegral_smul_measure c μ _

/-- `negLogIntegral` is additive (unconditionally, thanks to the value `⊥`). -/
theorem negLogIntegral_add (μ ν : Measure ℝ) :
    negLogIntegral (μ + ν) = negLogIntegral μ + negLogIntegral ν :=
  erealIntegral_add_measure μ ν _

/-- `negLogIntegral` of a finite sum of measures. -/
theorem negLogIntegral_finsetSum {ι : Type*} (s : Finset ι) (μ : ι → Measure ℝ) :
    negLogIntegral (∑ i ∈ s, μ i) = ∑ i ∈ s, negLogIntegral (μ i) :=
  erealIntegral_finsetSum_measure s μ _

/-- `∫ -log` against a finite weighted sum of Dirac masses whose charged points are positive:
`∫ -log d(∑ cᵢ δ_{aᵢ}) = -∑ cᵢ log aᵢ` when `aᵢ > 0` for every `cᵢ ≠ 0`. -/
theorem negLogIntegral_finsetSum_smul_dirac {ι : Type*} (s : Finset ι) (c : ι → ℝ≥0) {a : ι → ℝ}
    (ha : ∀ i ∈ s, c i ≠ 0 → 0 < a i) :
    negLogIntegral (∑ i ∈ s, c i • Measure.dirac (a i)) =
      ((∑ i ∈ s, -((c i : ℝ) * Real.log (a i)) : ℝ) : EReal) := by
  classical
  rw [negLogIntegral_finsetSum]
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, EReal.coe_add,
      ih fun j hj => ha j (Finset.mem_insert_of_mem hj), negLogIntegral_smul]
    rcases eq_or_ne (c i) 0 with hc | hc
    · simp [hc]
    rw [negLogIntegral_dirac, ENNReal.log_ofReal_of_pos (ha i (Finset.mem_insert_self i s) hc),
      ← EReal.coe_neg, ← EReal.coe_mul, mul_neg]

/-- `negLogIntegral μ` is `⊥` exactly when `∫ log⁺ t dμ(t) = ∞`. -/
theorem negLogIntegral_eq_bot_iff :
    negLogIntegral μ = ⊥ ↔ ∫⁻ t, (ENNReal.log (ENNReal.ofReal t)).toENNReal ∂μ = ∞ := by
  rw [negLogIntegral, erealIntegral_eq_bot_iff]
  simp_rw [neg_neg]

/-- `log⁺ t ≤ t`. -/
private lemma toENNReal_log_ofReal_le (t : ℝ) :
    (ENNReal.log (ENNReal.ofReal t)).toENNReal ≤ ENNReal.ofReal t := by
  rcases le_or_gt t 0 with ht | ht
  · rw [ENNReal.ofReal_of_nonpos ht, ENNReal.log_zero, EReal.toENNReal_bot]
  · rw [ENNReal.log_ofReal_of_pos ht, EReal.real_coe_toENNReal]
    exact ENNReal.ofReal_le_ofReal (by linarith [Real.log_le_sub_one_of_pos ht])

/-- A finite first moment `∫ t⁺ dμ(t) < ∞` rules out the value `⊥`. -/
theorem negLogIntegral_ne_bot_of_lintegral_ne_top (h : ∫⁻ t, ENNReal.ofReal t ∂μ ≠ ∞) :
    negLogIntegral μ ≠ ⊥ := by
  rw [Ne, negLogIntegral_eq_bot_iff]
  exact ne_top_of_le_ne_top h (lintegral_mono toENNReal_log_ofReal_le)

/-- A positive mass on `(-∞, 0]`, where `-log = +∞`, forces `negLogIntegral μ = ⊤` (unless it is
`⊥`). -/
theorem negLogIntegral_eq_top_of_measure_Iic_ne_zero (h0 : μ (Set.Iic 0) ≠ 0)
    (hb : negLogIntegral μ ≠ ⊥) : negLogIntegral μ = ⊤ := by
  have hN := hb
  rw [negLogIntegral, Ne, erealIntegral_eq_bot_iff] at hN
  have hP : ∫⁻ t, (-ENNReal.log (ENNReal.ofReal t)).toENNReal ∂μ = ∞ := by
    refine top_le_iff.mp (le_trans ?_ (lintegral_mono (f := (Set.Iic (0 : ℝ)).indicator fun _ => ∞)
      fun t => ?_))
    · rw [lintegral_indicator_const measurableSet_Iic, ENNReal.top_mul h0]
    · by_cases ht : t ∈ Set.Iic (0 : ℝ)
      · rw [Set.indicator_of_mem ht, ENNReal.ofReal_of_nonpos ht, ENNReal.log_zero, EReal.neg_bot,
          EReal.toENNReal_top]
      · rw [Set.indicator_of_notMem ht]
        exact zero_le
  rw [negLogIntegral, erealIntegral, hP, EReal.coe_ennreal_top]
  exact EReal.top_sub (by rwa [Ne, EReal.coe_ennreal_eq_top_iff])

/-- A finite weighted sum of Dirac masses charging a point of `(-∞, 0]` has `∫ -log = +∞`. -/
theorem negLogIntegral_finsetSum_smul_dirac_eq_top {ι : Type*} {s : Finset ι} {c : ι → ℝ≥0}
    {a : ι → ℝ} {i : ι} (hi : i ∈ s) (hc : c i ≠ 0) (ha : a i ≤ 0) :
    negLogIntegral (∑ j ∈ s, c j • Measure.dirac (a j)) = ⊤ := by
  refine negLogIntegral_eq_top_of_measure_Iic_ne_zero (fun h0 => hc ?_)
    (negLogIntegral_ne_bot_of_lintegral_ne_top ?_)
  · exact ((by simpa using h0 : ∀ j ∈ s, c j = 0 ∨ 0 < a j) i hi).resolve_right ha.not_gt
  · rw [lintegral_finsetSum_measure]
    refine ENNReal.sum_ne_top.mpr fun j _ => ?_
    rw [lintegral_smul_measure, lintegral_dirac]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top

/-- A nonzero measure with `∫ t⁺ dμ(t) = 0` lives on `(-∞, 0]`, so `negLogIntegral μ = ⊤`. -/
theorem negLogIntegral_eq_top_of_lintegral_eq_zero (hμ : μ ≠ 0)
    (h : ∫⁻ t, ENNReal.ofReal t ∂μ = 0) : negLogIntegral μ = ⊤ := by
  refine negLogIntegral_eq_top_of_measure_Iic_ne_zero (fun h0 => hμ ?_)
    (negLogIntegral_ne_bot_of_lintegral_ne_top (h ▸ ENNReal.zero_ne_top))
  rw [lintegral_eq_zero_iff ENNReal.measurable_ofReal] at h
  have hc : μ (Set.Iic 0)ᶜ = 0 := by
    rw [Set.compl_Iic, measure_eq_zero_iff_ae_notMem]
    filter_upwards [h] with t ht
    simpa using ht
  rw [← Measure.measure_univ_eq_zero, ← measure_add_measure_compl measurableSet_Iic, h0, hc,
    add_zero]

/-- A finite measure living on `[δ, ∞)` with `δ > 0` has `negLogIntegral μ < ⊤`. -/
theorem negLogIntegral_ne_top_of_ae_ge [IsFiniteMeasure μ] {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ᵐ t ∂μ, δ ≤ t) : negLogIntegral μ ≠ ⊤ :=
  ne_top_of_le_ne_top (EReal.coe_ne_top (∫ _, -Real.log δ ∂μ))
    (erealIntegral_le_integral (integrable_const _) (h.mono fun t ht => by
      rw [ENNReal.log_ofReal_of_pos (hδ.trans_le ht), ← EReal.coe_neg, EReal.coe_le_coe_iff]
      exact neg_le_neg (Real.log_le_log hδ ht)))

/-- **Agreement with the Bochner integral.** If `μ` lives on `(0, ∞)` and `log` is
`μ`-integrable, then `negLogIntegral μ = -∫ log t dμ(t)`. -/
theorem negLogIntegral_eq_neg_integral (h0 : ∀ᵐ t ∂μ, 0 < t) (hi : Integrable Real.log μ) :
    negLogIntegral μ = ((-∫ t, Real.log t ∂μ : ℝ) : EReal) := by
  rw [negLogIntegral, erealIntegral_congr_ae (g := fun t => ((-Real.log t : ℝ) : EReal))
    (h0.mono fun t ht => by rw [ENNReal.log_ofReal_of_pos ht, ← EReal.coe_neg]),
    erealIntegral_coe (g := fun t => -Real.log t) hi.neg, integral_neg]

/-- **Scaling.** `∫ -log (c t) dμ(t) = ∫ -log t dμ(t) - μ(ℝ) log c` for `c > 0` and finite `μ`. -/
theorem negLogIntegral_map_mul [IsFiniteMeasure μ] {c : ℝ} (hc : 0 < c) :
    negLogIntegral (μ.map (c * ·)) =
      negLogIntegral μ - ((μ.real Set.univ * Real.log c : ℝ) : EReal) := by
  have hm : Measurable (c * · : ℝ → ℝ) := measurable_const_mul c
  rw [negLogIntegral, erealIntegral_map hm.aemeasurable measurable_negLog.aemeasurable,
    erealIntegral_congr_ae (g := fun t => -ENNReal.log (ENNReal.ofReal t) + ((-Real.log c : ℝ) : EReal))
      (Filter.Eventually.of_forall fun t => ?_),
    erealIntegral_add_coe measurable_negLog.aemeasurable (integrable_const _), integral_const,
    smul_eq_mul, mul_neg, EReal.coe_neg, ← sub_eq_add_neg, negLogIntegral]
  rcases le_or_gt t 0 with ht | ht
  · simp only [Function.comp_apply]
    rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hc.le ht),
      ENNReal.ofReal_of_nonpos ht, ENNReal.log_zero, EReal.neg_bot, EReal.top_add_coe]
  · simp only [Function.comp_apply]
    rw [ENNReal.log_ofReal_of_pos (mul_pos hc ht), ENNReal.log_ofReal_of_pos ht,
      Real.log_mul hc.ne' ht.ne', ← EReal.coe_neg, ← EReal.coe_neg, ← EReal.coe_add]
    congr 1
    ring

/-- **Jensen's inequality** for `-log`. For a finite measure `μ` of mass `m = μ(ℝ)` with
`∫ t⁺ dμ(t) ≤ b`, `m log (m / b) ≤ ∫ -log t dμ(t)`. With Mathlib's conventions the left side is `0`
when `m = 0` or `b = 0`; when `b ≤ 0` (so that `μ` lives on `(-∞, 0]`) or `μ` charges `(-∞, 0)`,
the right side is `⊤`. -/
theorem mul_log_le_negLogIntegral [IsFiniteMeasure μ] {b : ℝ}
    (hb : ∫⁻ t, ENNReal.ofReal t ∂μ ≤ ENNReal.ofReal b) :
    ((μ.real Set.univ * Real.log (μ.real Set.univ / b) : ℝ) : EReal) ≤ negLogIntegral μ := by
  set m := μ.real Set.univ
  have hfin : ∫⁻ t, ENNReal.ofReal t ∂μ ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb
  rcases eq_or_ne μ 0 with rfl | hμ0
  · simp [m]
  by_cases h0 : ∀ᵐ t ∂μ, 0 ≤ t
  swap
  · -- `μ` charges `(-∞, 0)`, where `-log = +∞`.
    rw [negLogIntegral_eq_top_of_measure_Iic_ne_zero ?_ (negLogIntegral_ne_bot_of_lintegral_ne_top
      hfin)]
    · exact le_top
    rw [ae_iff] at h0
    exact fun h => h0 (measure_mono_null (fun t (ht : ¬ 0 ≤ t) => (not_le.mp ht).le) h)
  have hm : 0 < m := by
    change 0 < (μ Set.univ).toReal
    exact ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hμ0) (measure_ne_top _ _)
  rcases le_or_gt b 0 with hb0 | hb0
  · rw [negLogIntegral_eq_top_of_lintegral_eq_zero hμ0
      (nonpos_iff_eq_zero.mp (ENNReal.ofReal_of_nonpos hb0 ▸ hb))]
    exact le_top
  -- Tangent line of `log` at `c = b / m`: `log t ≤ log c + t / c - 1`.
  set c := b / m with hc_def
  have hc : 0 < c := div_pos hb0 hm
  have hint : Integrable (fun t : ℝ => t) μ := by
    refine (integrable_toReal_of_lintegral_ne_top ENNReal.measurable_ofReal.aemeasurable
      hfin).congr ?_
    filter_upwards [h0] with t ht using ENNReal.toReal_ofReal ht
  have hle : ∫ t, t ∂μ ≤ b := by
    rw [integral_eq_lintegral_of_nonneg_ae h0 aestronglyMeasurable_id]
    exact ENNReal.toReal_le_of_le_ofReal hb0.le hb
  have hg : Integrable (fun t => 1 - Real.log c - t / c) μ :=
    (integrable_const _).sub (hint.div_const c)
  refine le_trans ?_ (integral_le_erealIntegral hg (h0.mono fun t ht => ?_))
  · rw [integral_sub (integrable_const _) (hint.div_const c), integral_const, integral_div,
      smul_eq_mul, EReal.coe_le_coe_iff]
    have hlog : Real.log (m / b) = -Real.log c := by rw [hc_def, ← Real.log_inv, inv_div]
    have hbc : b / c = m := by rw [hc_def, div_div_cancel₀ hb0.ne']
    rw [hlog]
    have := div_le_div_of_nonneg_right hle hc.le
    rw [hbc] at this
    linarith
  · rcases ht.eq_or_lt with rfl | ht
    · simp
    rw [ENNReal.log_ofReal_of_pos ht, ← EReal.coe_neg, EReal.coe_le_coe_iff]
    have := Real.log_le_sub_one_of_pos (div_pos ht hc)
    rw [Real.log_div ht.ne' hc.ne'] at this
    linarith

/-! ### The resolvent representation of `-log` -/

section Resolvent

open Filter Topology

/-- For `0 < a ≤ b`, `∫_{t > 0} ((t + a)⁻¹ - (t + b)⁻¹) dt = log b - log a`. -/
private lemma lintegral_Ioi_inv_add_sub_inv_add {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫⁻ t in Set.Ioi 0, ENNReal.ofReal ((t + a)⁻¹ - (t + b)⁻¹) =
      ENNReal.ofReal (Real.log b - Real.log a) := by
  have hb : 0 < b := ha.trans_le hab
  set g : ℝ → ℝ := fun t => Real.log (t + a) - Real.log (t + b)
  have hderiv : ∀ t ∈ Set.Ici (0 : ℝ), HasDerivAt g ((t + a)⁻¹ - (t + b)⁻¹) t := fun t ht => by
    have ht : (0 : ℝ) ≤ t := ht
    have h₁ : HasDerivAt (fun x => Real.log (x + a)) (t + a)⁻¹ t := by
      simpa [one_div] using ((hasDerivAt_id' t).add_const a).log (by linarith)
    have h₂ : HasDerivAt (fun x => Real.log (x + b)) (t + b)⁻¹ t := by
      simpa [one_div] using ((hasDerivAt_id' t).add_const b).log (by linarith)
    exact h₁.sub h₂
  have hpos : ∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ (t + a)⁻¹ - (t + b)⁻¹ := fun t ht => by
    have ht : (0 : ℝ) < t := ht
    exact sub_nonneg.mpr (inv_anti₀ (by linarith) (by linarith))
  have hlim : Tendsto g atTop (𝓝 0) := by
    have h : Tendsto (fun t : ℝ => (t + a) / (t + b)) atTop (𝓝 1) := by
      have := (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_const_nhds (x := b - a).div_atTop
        (tendsto_atTop_add_const_right _ b tendsto_id))
      rw [sub_zero] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop (-b)] with t ht
      have : t + b ≠ 0 := by linarith
      change 1 - (b - a) / (t + b) = (t + a) / (t + b)
      rw [eq_div_iff this, sub_mul, div_mul_cancel₀ _ this]
      ring
    have := (Real.continuousAt_log one_ne_zero).tendsto.comp h
    rw [Real.log_one] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp only [Function.comp_apply, g]
    rw [Real.log_div (by linarith) (by linarith)]
  have hint := integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hlim
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hpos)),
    integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hlim]
  congr 1
  simp only [g, zero_add]
  ring

/-- **Resolvent representation of `-log`**, positive part: for `s ≥ 0`,
`∫_{t > 0} ((t + s)⁻¹ - (1 + t)⁻¹)⁺ dt = (-log s)⁺`, both sides being `+∞` at `s = 0`. For
`0 < s ≤ 1` this is `∫_{t > 0} ((t + s)⁻¹ - (1 + t)⁻¹) dt = -log s`. -/
theorem lintegral_Ioi_ofReal_inv_add_sub_inv_one_add {s : ℝ} (hs : 0 ≤ s) :
    ∫⁻ t in Set.Ioi 0, ENNReal.ofReal ((t + s)⁻¹ - (1 + t)⁻¹) =
      (-ENNReal.log (ENNReal.ofReal s)).toENNReal := by
  rcases hs.eq_or_lt with rfl | hs
  · -- `s = 0`: the integral dominates `-log r = n` for `r = exp (-n)`.
    rw [ENNReal.ofReal_zero, ENNReal.log_zero, EReal.neg_bot, EReal.toENNReal_top]
    refine ENNReal.eq_top_of_forall_nnreal_le fun n => ?_
    have hr : 0 < Real.exp (-n) := Real.exp_pos _
    calc (n : ℝ≥0∞) = ENNReal.ofReal (Real.log 1 - Real.log (Real.exp (-n))) := by simp
      _ = ∫⁻ t in Set.Ioi 0, ENNReal.ofReal ((t + Real.exp (-n))⁻¹ - (t + 1)⁻¹) :=
          (lintegral_Ioi_inv_add_sub_inv_add hr (Real.exp_le_one_iff.mpr (by simp))).symm
      _ ≤ _ := setLIntegral_mono' measurableSet_Ioi fun t ht => ENNReal.ofReal_le_ofReal (by
          have ht : (0 : ℝ) < t := ht
          have := inv_anti₀ ht (by linarith : t ≤ t + Real.exp (-n))
          rw [add_zero, add_comm 1 t]
          linarith)
  rw [ENNReal.log_ofReal_of_pos hs, ← EReal.coe_neg, EReal.real_coe_toENNReal]
  rcases le_total s 1 with hs1 | hs1
  · simp_rw [add_comm (1 : ℝ)]
    rw [lintegral_Ioi_inv_add_sub_inv_add hs hs1, Real.log_one, zero_sub]
  · rw [ENNReal.ofReal_of_nonpos (by linarith [Real.log_nonneg hs1]),
      setLIntegral_congr_fun measurableSet_Ioi (g := fun _ => 0) fun t ht => ?_, lintegral_zero]
    have ht : (0 : ℝ) < t := ht
    exact ENNReal.ofReal_of_nonpos (sub_nonpos.mpr (inv_anti₀ (by linarith) (by linarith)))

/-- **Resolvent representation of `-log`**, negative part: for `s ≥ 0`,
`∫_{t > 0} ((1 + t)⁻¹ - (t + s)⁻¹)⁺ dt = (log s)⁺`. For `s ≥ 1` this is
`∫_{t > 0} ((1 + t)⁻¹ - (t + s)⁻¹) dt = log s`. -/
theorem lintegral_Ioi_ofReal_inv_one_add_sub_inv_add {s : ℝ} (hs : 0 ≤ s) :
    ∫⁻ t in Set.Ioi 0, ENNReal.ofReal ((1 + t)⁻¹ - (t + s)⁻¹) =
      (ENNReal.log (ENNReal.ofReal s)).toENNReal := by
  rcases le_total s 1 with hs1 | hs1
  · have h0 : (ENNReal.log (ENNReal.ofReal s)).toENNReal = 0 := by
      rcases hs.eq_or_lt with rfl | hs'
      · simp
      · rw [ENNReal.log_ofReal_of_pos hs', EReal.real_coe_toENNReal,
          ENNReal.ofReal_of_nonpos (Real.log_nonpos hs hs1)]
    rw [h0, setLIntegral_congr_fun measurableSet_Ioi (g := fun _ => 0) fun t ht => ?_,
      lintegral_zero]
    have ht : (0 : ℝ) < t := ht
    exact ENNReal.ofReal_of_nonpos (sub_nonpos.mpr (inv_anti₀ (by linarith) (by linarith)))
  · have hs' : 0 < s := by linarith
    rw [ENNReal.log_ofReal_of_pos hs', EReal.real_coe_toENNReal]
    simp_rw [add_comm (1 : ℝ)]
    rw [lintegral_Ioi_inv_add_sub_inv_add one_pos hs1, Real.log_one, sub_zero]

/-- **Comparison of `∫ -log` through resolvents.** Let `μ` be a finite measure on `[0, ∞)` and `ν`
a finite measure with `ν(ℝ) ≤ μ(ℝ)` and `∫ -log dν ≠ -∞`. If
`∫ (t + λ)⁻¹ dμ(λ) ≤ ∫ (t + λ)⁻¹ dν(λ)` for every `t > 0`, then `∫ -log dμ ≤ ∫ -log dν`.

The proof integrates `-log λ = ∫_{t > 0} ((t + λ)⁻¹ - (1 + t)⁻¹) dt`
(`MeasureTheory.lintegral_Ioi_ofReal_inv_add_sub_inv_one_add`,
`MeasureTheory.lintegral_Ioi_ofReal_inv_one_add_sub_inv_add`) against `μ` and `ν`; the positive and
negative parts of the integrand are exchanged with the `t`-integral separately, by Tonelli's
theorem. -/
theorem negLogIntegral_le_of_integral_inv_add_le {ν : Measure ℝ} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hμ : ∀ᵐ s ∂μ, 0 ≤ s) (hmass : ν Set.univ ≤ μ Set.univ)
    (hν : negLogIntegral ν ≠ ⊥)
    (h : ∀ t : ℝ, 0 < t → ∫ s, (t + s)⁻¹ ∂μ ≤ ∫ s, (t + s)⁻¹ ∂ν) :
    negLogIntegral μ ≤ negLogIntegral ν := by
  by_cases hν0 : ∀ᵐ s ∂ν, 0 ≤ s
  swap
  · -- `ν` charges `(-∞, 0)`, where `-log = +∞`.
    rw [negLogIntegral_eq_top_of_measure_Iic_ne_zero ?_ hν]
    · exact le_top
    rw [ae_iff] at hν0
    exact fun h0 => hν0 (measure_mono_null (fun s (hs : ¬ 0 ≤ s) => (not_le.mp hs).le) h0)
  set P : ℝ → ℝ → ℝ≥0∞ := fun t s => ENNReal.ofReal ((t + s)⁻¹ - (1 + t)⁻¹)
  set Q : ℝ → ℝ → ℝ≥0∞ := fun t s => ENNReal.ofReal ((1 + t)⁻¹ - (t + s)⁻¹)
  have hP : Measurable (Function.uncurry P) := by fun_prop
  have hQ : Measurable (Function.uncurry Q) := by fun_prop
  have hP' : Measurable fun p : ℝ × ℝ => P p.2 p.1 := by fun_prop
  have hQ' : Measurable fun p : ℝ × ℝ => Q p.2 p.1 := by fun_prop
  -- The positive and negative parts of `-log` as `t`-integrals, by Tonelli.
  have key : ∀ ρ : Measure ℝ, [IsFiniteMeasure ρ] → (∀ᵐ s ∂ρ, 0 ≤ s) →
      ∫⁻ s, (-ENNReal.log (ENNReal.ofReal s)).toENNReal ∂ρ =
          ∫⁻ t in Set.Ioi 0, ∫⁻ s, P t s ∂ρ ∧
        ∫⁻ s, (ENNReal.log (ENNReal.ofReal s)).toENNReal ∂ρ =
          ∫⁻ t in Set.Ioi 0, ∫⁻ s, Q t s ∂ρ := fun ρ _ hρ =>
    ⟨(lintegral_congr_ae (hρ.mono fun s hs =>
        (lintegral_Ioi_ofReal_inv_add_sub_inv_one_add hs).symm)).trans
      (lintegral_lintegral_swap (f := fun s t => P t s) hP'.aemeasurable),
    (lintegral_congr_ae (hρ.mono fun s hs =>
        (lintegral_Ioi_ofReal_inv_one_add_sub_inv_add hs).symm)).trans
      (lintegral_lintegral_swap (f := fun s t => Q t s) hQ'.aemeasurable)⟩
  -- For fixed `t > 0`, the two parts are finite and their difference is a Bochner integral.
  have fin : ∀ ρ : Measure ℝ, [IsFiniteMeasure ρ] → (∀ᵐ s ∂ρ, 0 ≤ s) → ∀ t : ℝ, 0 < t →
      ∫⁻ s, P t s ∂ρ ≠ ∞ ∧ ∫⁻ s, Q t s ∂ρ ≠ ∞ ∧
        (∫⁻ s, P t s ∂ρ).toReal - (∫⁻ s, Q t s ∂ρ).toReal =
          ∫ s, (t + s)⁻¹ ∂ρ - ρ.real Set.univ * (1 + t)⁻¹ := by
    intro ρ _ hρ t ht
    have hi : Integrable (fun s => (t + s)⁻¹) ρ := by
      refine Integrable.of_bound (by fun_prop) t⁻¹ ?_
      filter_upwards [hρ] with s hs
      rw [Real.norm_of_nonneg (inv_nonneg.mpr (by linarith))]
      exact inv_anti₀ ht (by linarith)
    have hg : Integrable (fun s => (t + s)⁻¹ - (1 + t)⁻¹) ρ := hi.sub (integrable_const _)
    have hQ : ∫⁻ s, Q t s ∂ρ = ∫⁻ s, ENNReal.ofReal (-((t + s)⁻¹ - (1 + t)⁻¹)) ∂ρ := by
      simp_rw [Q, neg_sub]
    refine ⟨hg.lintegral_lt_top.ne, hQ ▸ hg.neg.lintegral_lt_top.ne, ?_⟩
    rw [hQ, ← integral_eq_lintegral_pos_part_sub_lintegral_neg_part hg,
      integral_sub hi (integrable_const _), integral_const, smul_eq_mul]
  -- Pointwise in `t > 0`: `P_μ + Q_ν ≤ Q_μ + P_ν`.
  have hpt : ∀ t ∈ Set.Ioi (0 : ℝ),
      ∫⁻ s, P t s ∂μ + ∫⁻ s, Q t s ∂ν ≤ ∫⁻ s, Q t s ∂μ + ∫⁻ s, P t s ∂ν := by
    intro t ht
    have ht : (0 : ℝ) < t := ht
    obtain ⟨h₁, h₂, h₃⟩ := fin μ hμ t ht
    obtain ⟨h₄, h₅, h₆⟩ := fin ν hν0 t ht
    rw [← ENNReal.toReal_le_toReal (ENNReal.add_ne_top.mpr ⟨h₁, h₅⟩)
      (ENNReal.add_ne_top.mpr ⟨h₂, h₄⟩), ENNReal.toReal_add h₁ h₅, ENNReal.toReal_add h₂ h₄]
    have hm : ν.real Set.univ ≤ μ.real Set.univ := ENNReal.toReal_mono (measure_ne_top _ _) hmass
    have hc := mul_le_mul_of_nonneg_right hm (inv_pos.mpr (by linarith : (0 : ℝ) < 1 + t)).le
    linarith [h t ht]
  have hint : (∫⁻ t in Set.Ioi 0, ∫⁻ s, P t s ∂μ) + ∫⁻ t in Set.Ioi 0, ∫⁻ s, Q t s ∂ν ≤
      (∫⁻ t in Set.Ioi 0, ∫⁻ s, Q t s ∂μ) + ∫⁻ t in Set.Ioi 0, ∫⁻ s, P t s ∂ν := by
    have hPμ : Measurable fun t => ∫⁻ s, P t s ∂μ := hP.lintegral_prod_right'
    have hQμ : Measurable fun t => ∫⁻ s, Q t s ∂μ := hQ.lintegral_prod_right'
    rw [← lintegral_add_left hPμ, ← lintegral_add_left hQμ]
    exact lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hpt))
  obtain ⟨hμ₁, hμ₂⟩ := key μ hμ
  obtain ⟨hν₁, hν₂⟩ := key ν hν0
  have hνQ : ∫⁻ s, (ENNReal.log (ENNReal.ofReal s)).toENNReal ∂ν ≠ ∞ := by
    rwa [Ne, ← negLogIntegral_eq_bot_iff]
  by_cases hμQ : ∫⁻ s, (ENNReal.log (ENNReal.ofReal s)).toENNReal ∂μ = ∞
  · rw [negLogIntegral_eq_bot_iff.mpr hμQ]
    exact bot_le
  rw [negLogIntegral, negLogIntegral, erealIntegral, erealIntegral]
  simp only [neg_neg]
  rw [coe_sub_coe_le_coe_sub_coe_iff hμQ hνQ, hμ₁, hμ₂, hν₁, hν₂]
  exact hint

end Resolvent

end MeasureTheory
