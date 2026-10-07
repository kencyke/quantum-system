/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.SpectralTheory.ProjectionValuedIntegral
public import QuantumSystem.ForMathlib.Analysis.Complex.Strip
public import QuantumSystem.ForMathlib.Analysis.Complex.WeakHolomorphic

/-!
# Analytic continuation of spectral integrals

Let `E` be a projection-valued measure on `X` acting on a complex Hilbert space `H`, and `ξ ∈ H`.
For a family `F z` of measurable functions depending holomorphically on a complex parameter `z`,
the vectors `(∫ F z dE) ξ` depend holomorphically on `z` as soon as `|F z| ≤ G` for one
`G ∈ L²(E_ξ)` (`ProjectionValuedMeasure.differentiableOn_integralApply`): the isometry
`‖(∫ f dE) ξ‖² = ∫ |f|² dE_ξ` turns the norm of the remainder of the difference quotient into an
integral against `E_ξ`, which tends to `0` by dominated convergence, the domination coming from
the Cauchy estimates for `z ↦ F z x`. Continuity is proved in the same way
(`ProjectionValuedMeasure.continuousOn_integralApply`). No Bochner integral in `H` and no weak
holomorphy is involved.

The main instances are the exponentials `F z = exp (i z φ)` of a measurable real function `φ`:
* on a strip `a < im z < b`, when `exp (-a φ), exp (-b φ) ∈ L²(E_ξ)`
  (`ProjectionValuedMeasure.diffContOnCl_integralApply_cexp`); for the projection-valued measure
  of a self-adjoint `B` and `φ = id` this is the continuation of `t ↦ e^{itB} ξ` to the strip, for
  `ξ ∈ dom e^{-aB} ∩ dom e^{-bB}`, and for a positive injective `A` and `φ = log` it is the
  continuation of `t ↦ A^{it} ξ`, for `ξ ∈ dom A^{-a} ∩ dom A^{-b}`;
* on the upper half-plane, when `φ ≥ 0` (`ProjectionValuedMeasure.diffContOnCl_integralApply_cexp_of_nonneg`);
  for a positive self-adjoint `B` this is the continuation of `t ↦ e^{itB} ξ` to `im z > 0`.

## Main results

* `ProjectionValuedMeasure.norm_integralApply_sub` — `‖(∫ f dE) ξ - (∫ g dE) ξ‖² = ∫ |f - g|² dE_ξ`.
* `ProjectionValuedMeasure.continuousOn_integralApply` — continuity in a parameter.
* `ProjectionValuedMeasure.hasDerivAt_integralApply`,
  `ProjectionValuedMeasure.differentiableOn_integralApply` — holomorphy in a parameter, with the
  derivative `(∫ ∂F/∂z dE) ξ`.
* `ProjectionValuedMeasure.diffContOnCl_integralApply_cexp`,
  `ProjectionValuedMeasure.norm_integralApply_cexp_sq_le` — exponentials on a strip, with the
  bound `‖(∫ exp (i z φ) dE) ξ‖² ≤ ∫ exp (-2 a φ) dE_ξ + ∫ exp (-2 b φ) dE_ξ`.
* `ProjectionValuedMeasure.diffContOnCl_integralApply_cexp_of_nonneg` — exponentials on the upper
  half-plane for `φ ≥ 0`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Complex Metric
open scoped ENNReal InnerProductSpace ComplexConjugate LinearPMap

namespace MeasureTheory.ProjectionValuedMeasure

variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] (E : ProjectionValuedMeasure X H) {ξ : H}

/-- `‖(∫ f dE) ξ - (∫ g dE) ξ‖ = √(∫ |f - g|² dE_ξ)`. -/
lemma norm_integralApply_sub {f g : X → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hfξ : MemLp f 2 (E.measure ξ)) (hgξ : MemLp g 2 (E.measure ξ)) :
    ‖E.integralApply f ξ - E.integralApply g ξ‖ = √(∫ x, ‖f x - g x‖ ^ 2 ∂(E.measure ξ)) := by
  rw [← integralApply_sub hf hg hfξ hgξ, ← Real.sqrt_sq (norm_nonneg _),
    E.norm_integralApply_sq (hf.sub hg) (hfξ.sub hgξ)]
  rfl

/-- **Continuity of parameterized spectral integrals**: if `z ↦ F z x` is continuous on `S` for
every `x`, and `|F z| ≤ G` on `S` for some `G ∈ L²(E_ξ)`, then `z ↦ (∫ F z dE) ξ` is continuous
on `S`. -/
lemma continuousOn_integralApply {S : Set ℂ} {F : ℂ → X → ℂ}
    (hFm : ∀ z ∈ S, Measurable (F z)) (hFc : ∀ x, ContinuousOn (fun z => F z x) S)
    {G : X → ℝ} (hG : MemLp G 2 (E.measure ξ))
    (hFG : ∀ᵐ x ∂(E.measure ξ), ∀ z ∈ S, ‖F z x‖ ≤ G x) :
    ContinuousOn (fun z => E.integralApply (F z) ξ) S := by
  have hFξ : ∀ z ∈ S, MemLp (F z) 2 (E.measure ξ) := fun z hz =>
    hG.of_le_mul (c := 1) (hFm z hz).aestronglyMeasurable (hFG.mono fun x hx => by
      rw [one_mul]
      exact (hx z hz).trans (le_abs_self _))
  have hG2 : Integrable (fun x => (2 * G x) ^ 2) (E.measure ξ) := by
    have h4 : (fun x => (2 * G x) ^ 2) = fun x => 4 * ‖G x‖ ^ 2 := by
      ext x
      rw [Real.norm_eq_abs, sq_abs]
      ring
    rw [h4]
    exact ((memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).mp hG).const_mul 4
  intro z₀ hz₀
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hsq : ∀ᶠ z in 𝓝[S] z₀, ‖E.integralApply (F z) ξ - E.integralApply (F z₀) ξ‖ =
      √(∫ x, ‖F z x - F z₀ x‖ ^ 2 ∂(E.measure ξ)) :=
    eventually_nhdsWithin_of_forall fun z hz =>
      E.norm_integralApply_sub (hFm z hz) (hFm z₀ hz₀) (hFξ z hz) (hFξ z₀ hz₀)
  refine (tendsto_congr' hsq).mpr ?_
  rw [← Real.sqrt_zero]
  refine (Real.continuous_sqrt.tendsto 0).comp ?_
  have h := tendsto_integral_filter_of_dominated_convergence (μ := E.measure ξ)
    (l := 𝓝[S] z₀) (F := fun z x => ‖F z x - F z₀ x‖ ^ 2) (f := fun _ => 0)
    (fun x => (2 * G x) ^ 2)
    (eventually_nhdsWithin_of_forall fun z hz =>
      (((hFm z hz).sub (hFm z₀ hz₀)).norm.pow_const 2).aestronglyMeasurable)
    (eventually_nhdsWithin_of_forall fun z hz => hFG.mono fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      refine pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans ?_) 2
      linarith [hx z hz, hx z₀ hz₀])
    hG2
    (Eventually.of_forall fun x => by
      have := ((hFc x z₀ hz₀).tendsto.sub (tendsto_const_nhds (x := F z₀ x))).norm.pow 2
      simpa using this)
  simpa using h

/-- **Holomorphy of parameterized spectral integrals**, local form: if `z ↦ F z x` has derivative
`F' z x` on a ball for every `x`, and `|F z| ≤ G` on the ball for some `G ∈ L²(E_ξ)`, then
`z ↦ (∫ F z dE) ξ` has derivative `(∫ F' z₀ dE) ξ` at the centre. -/
lemma hasDerivAt_integralApply {F F' : ℂ → X → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hFm : ∀ z ∈ ball z₀ r, Measurable (F z)) (hF'm : Measurable (F' z₀))
    (hFd : ∀ x, ∀ z ∈ ball z₀ r, HasDerivAt (fun w => F w x) (F' z x) z)
    {G : X → ℝ} (hG : MemLp G 2 (E.measure ξ))
    (hFG : ∀ᵐ x ∂(E.measure ξ), ∀ z ∈ ball z₀ r, ‖F z x‖ ≤ G x) :
    HasDerivAt (fun z => E.integralApply (F z) ξ) (E.integralApply (F' z₀) ξ) z₀ := by
  have hz₀ : z₀ ∈ ball z₀ r := mem_ball_self hr
  have hdiff : ∀ x, DifferentiableOn ℂ (fun w => F w x) (ball z₀ r) := fun x z hz =>
    (hFd x z hz).differentiableAt.differentiableWithinAt
  have hFξ : ∀ z ∈ ball z₀ r, MemLp (F z) 2 (E.measure ξ) := fun z hz =>
    hG.of_le_mul (c := 1) (hFm z hz).aestronglyMeasurable (hFG.mono fun x hx => by
      rw [one_mul]
      exact (hx z hz).trans (le_abs_self _))
  -- Cauchy estimate for the derivative
  have hF'G : ∀ᵐ x ∂(E.measure ξ), ‖F' z₀ x‖ ≤ 2 / r * G x := hFG.mono fun x hx => by
    have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (half_pos hr)
      ((hdiff x).diffContOnCl_ball (closedBall_subset_ball (half_lt_self hr)))
      fun z hz => hx z (sphere_subset_closedBall.trans (closedBall_subset_ball (half_lt_self hr)) hz)
    rw [(hFd x z₀ hz₀).deriv] at h
    calc ‖F' z₀ x‖ ≤ G x / (r / 2) := h
      _ = 2 / r * G x := by field_simp
  have hF'ξ : MemLp (F' z₀) 2 (E.measure ξ) :=
    hG.of_le_mul (c := 2 / r) hF'm.aestronglyMeasurable (hF'G.mono fun x hx =>
      hx.trans (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)))
  rw [hasDerivAt_iff_tendsto_slope, tendsto_iff_norm_sub_tendsto_zero]
  -- the difference quotients, as spectral integrals
  have hq : ∀ᶠ w in 𝓝[≠] z₀, ‖slope (fun z => E.integralApply (F z) ξ) z₀ w -
      E.integralApply (F' z₀) ξ‖ = √(∫ x, ‖dslope (fun z => F z x) z₀ w - F' z₀ x‖ ^ 2
        ∂(E.measure ξ)) := by
    filter_upwards [inter_mem_nhdsWithin _ (ball_mem_nhds z₀ hr), self_mem_nhdsWithin]
      with w hw hwz
    have hwr : w ∈ ball z₀ r := hw.2
    have hfun : (fun x => dslope (fun z => F z x) z₀ w) = (w - z₀)⁻¹ • (F w - F z₀) := by
      ext x
      rw [dslope_of_ne _ hwz, slope_def_module]
      rfl
    have hm : Measurable fun x => dslope (fun z => F z x) z₀ w := by
      rw [hfun]
      exact ((hFm w hwr).sub (hFm z₀ hz₀)).const_smul _
    have hmξ : MemLp (fun x => dslope (fun z => F z x) z₀ w) 2 (E.measure ξ) := by
      rw [hfun]
      exact ((hFξ w hwr).sub (hFξ z₀ hz₀)).const_smul _
    rw [← E.norm_integralApply_sub hm hF'm hmξ hF'ξ, hfun, integralApply_smul ((hFm w hwr).sub
      (hFm z₀ hz₀)) _ ((hFξ w hwr).sub (hFξ z₀ hz₀)), integralApply_sub (hFm w hwr) (hFm z₀ hz₀)
      (hFξ w hwr) (hFξ z₀ hz₀), slope_def_module]
  refine (tendsto_congr' hq).mpr ?_
  rw [← Real.sqrt_zero]
  refine (Real.continuous_sqrt.tendsto 0).comp ?_
  have hG2 : Integrable (fun x => (2 / r * G x) ^ 2) (E.measure ξ) := by
    have h4 : (fun x => (2 / r * G x) ^ 2) = fun x => (2 / r) ^ 2 * ‖G x‖ ^ 2 := by
      ext x
      rw [Real.norm_eq_abs, sq_abs]
      ring
    rw [h4]
    exact ((memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).mp hG).const_mul _
  have h := tendsto_integral_filter_of_dominated_convergence (μ := E.measure ξ)
    (l := 𝓝[≠] z₀) (F := fun w x => ‖dslope (fun z => F z x) z₀ w - F' z₀ x‖ ^ 2)
    (f := fun _ => 0) (fun x => (2 / r * G x) ^ 2) ?_ ?_ hG2 ?_
  · simpa using h
  · filter_upwards [inter_mem_nhdsWithin _ (ball_mem_nhds z₀ hr), self_mem_nhdsWithin]
      with w hw hwz
    have hfun : (fun x => dslope (fun z => F z x) z₀ w) = (w - z₀)⁻¹ • (F w - F z₀) := by
      ext x
      rw [dslope_of_ne _ hwz, slope_def_module]
      rfl
    have hm : Measurable fun x => dslope (fun z => F z x) z₀ w := by
      rw [hfun]
      exact ((hFm w hw.2).sub (hFm z₀ hz₀)).const_smul _
    exact ((hm.sub hF'm).norm.pow_const 2).aestronglyMeasurable
  · filter_upwards [inter_mem_nhdsWithin _ (ball_mem_nhds z₀ (half_pos hr))] with w hw
    refine hFG.mono fun x hx => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    have h := Complex.norm_dslope_sub_dslope_le (hdiff x) hx hw.2 (mem_ball_self (half_pos hr))
    rw [dslope_same, (hFd x z₀ hz₀).deriv] at h
    refine h.trans ?_
    have hGx : 0 ≤ G x := (norm_nonneg _).trans (hx z₀ hz₀)
    have hwz : ‖w - z₀‖ ≤ r / 2 := by
      rw [← dist_eq_norm]
      exact (mem_ball.mp hw.2).le
    calc 4 * G x / r ^ 2 * ‖w - z₀‖ ≤ 4 * G x / r ^ 2 * (r / 2) := by gcongr
      _ = 2 / r * G x := by field_simp; ring
  · refine Eventually.of_forall fun x => ?_
    have h : Tendsto (fun w => dslope (fun z => F z x) z₀ w) (𝓝[≠] z₀) (𝓝 (F' z₀ x)) :=
      (hFd x z₀ hz₀).tendsto_slope.congr' (by
        filter_upwards [self_mem_nhdsWithin] with w hw
        rw [dslope_of_ne _ hw])
    simpa using (h.sub (tendsto_const_nhds (x := F' z₀ x))).norm.pow 2

/-- **Holomorphy of parameterized spectral integrals**: if `z ↦ F z x` is holomorphic on an open
set `U` with derivative `F' z x` for every `x`, and `|F z| ≤ G` on `U` for some `G ∈ L²(E_ξ)`,
then `z ↦ (∫ F z dE) ξ` is holomorphic on `U`. -/
theorem differentiableOn_integralApply {U : Set ℂ} (hU : IsOpen U) {F F' : ℂ → X → ℂ}
    (hFm : ∀ z ∈ U, Measurable (F z)) (hF'm : ∀ z ∈ U, Measurable (F' z))
    (hFd : ∀ x, ∀ z ∈ U, HasDerivAt (fun w => F w x) (F' z x) z)
    {G : X → ℝ} (hG : MemLp G 2 (E.measure ξ))
    (hFG : ∀ᵐ x ∂(E.measure ξ), ∀ z ∈ U, ‖F z x‖ ≤ G x) :
    DifferentiableOn ℂ (fun z => E.integralApply (F z) ξ) U := fun z₀ hz₀ => by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
  exact (E.hasDerivAt_integralApply hr (fun z hz => hFm z (hrU hz)) (hF'm z₀ hz₀)
    (fun x z hz => hFd x z (hrU hz)) hG (hFG.mono fun x hx z hz => hx z (hrU hz))
    ).differentiableAt.differentiableWithinAt

/-! ### Exponentials on strips and half-planes -/

section Exponential

variable {φ : X → ℝ} (hφ : Measurable φ)

/-- `|exp (i z φ)| = exp (-im z φ)`. -/
private lemma norm_cexp_I_mul (z : ℂ) (t : ℝ) : ‖cexp (I * z * t)‖ = Real.exp (-z.im * t) := by
  rw [norm_exp]
  congr 1
  simp [mul_re, mul_im]

/-- On `a ≤ im z ≤ b`, `|exp (i z t)| ≤ exp (-a t) + exp (-b t)`. -/
private lemma norm_cexp_I_mul_le {a b : ℝ} {z : ℂ} (hz : z.im ∈ Icc a b) (t : ℝ) :
    ‖cexp (I * z * t)‖ ≤ Real.exp (-a * t) + Real.exp (-b * t) := by
  rw [norm_cexp_I_mul]
  rcases le_total 0 t with ht | ht
  · exact (Real.exp_le_exp.mpr (by nlinarith [hz.1])).trans
      (le_add_of_nonneg_right (Real.exp_pos _).le)
  · exact (Real.exp_le_exp.mpr (by nlinarith [hz.2])).trans
      (le_add_of_nonneg_left (Real.exp_pos _).le)

/-- On `a ≤ im z ≤ b`, `|exp (i z t)|² ≤ exp (-a t)² + exp (-b t)²`. -/
private lemma norm_cexp_I_mul_sq_le {a b : ℝ} {z : ℂ} (hz : z.im ∈ Icc a b) (t : ℝ) :
    ‖cexp (I * z * t)‖ ^ 2 ≤ Real.exp (-a * t) ^ 2 + Real.exp (-b * t) ^ 2 := by
  rw [norm_cexp_I_mul]
  rcases le_total 0 t with ht | ht
  · exact (pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_le_exp.mpr (by nlinarith [hz.1])) 2).trans
      (le_add_of_nonneg_right (by positivity))
  · exact (pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_le_exp.mpr (by nlinarith [hz.2])) 2).trans
      (le_add_of_nonneg_left (by positivity))

include hφ in
/-- The phases `x ↦ exp (i z φ x)` are measurable. -/
private lemma measurable_cexp_I_mul (z : ℂ) : Measurable fun x => cexp (I * z * φ x) := by
  fun_prop

/-- The `z`-derivative of `exp (i z t)`. -/
private lemma hasDerivAt_cexp_I_mul (t : ℝ) (z : ℂ) :
    HasDerivAt (fun w => cexp (I * w * t)) (I * t * cexp (I * z * t)) z := by
  have h := ((hasDerivAt_id z).const_mul I).mul_const (t : ℂ)
  simpa [mul_comm, mul_left_comm] using h.cexp

include hφ in
/-- **Analytic continuation on a strip**: if `exp (-a φ)` and `exp (-b φ)` are in `L²(E_ξ)`, then
`z ↦ (∫ exp (i z φ) dE) ξ` is holomorphic on `a < im z < b` and continuous up to the boundary.
For `φ = id` and the projection-valued measure of a self-adjoint `B` this is `z ↦ e^{izB} ξ`; for
`φ = log` and a positive injective `A` it is `z ↦ A^{iz} ξ`. -/
theorem diffContOnCl_integralApply_cexp {a b : ℝ} (hab : a < b)
    (ha : MemLp (fun x => Real.exp (-a * φ x)) 2 (E.measure ξ))
    (hb : MemLp (fun x => Real.exp (-b * φ x)) 2 (E.measure ξ)) :
    DiffContOnCl ℂ (fun z => E.integralApply (fun x => cexp (I * z * φ x)) ξ)
      (im ⁻¹' Ioo a b) := by
  have hG := ha.add hb
  refine ⟨E.differentiableOn_integralApply (isOpen_Ioo.preimage continuous_im)
    (F' := fun z x => I * φ x * cexp (I * z * φ x)) (fun z _ => measurable_cexp_I_mul hφ z)
    (fun z _ => by fun_prop) (fun x z _ => hasDerivAt_cexp_I_mul (φ x) z) hG
    (Eventually.of_forall fun x z hz => norm_cexp_I_mul_le (Ioo_subset_Icc_self hz) (φ x)), ?_⟩
  rw [Complex.closure_preimage_im_Ioo hab]
  exact E.continuousOn_integralApply (fun z _ => measurable_cexp_I_mul hφ z)
    (fun x => by fun_prop) hG (Eventually.of_forall fun x z hz => norm_cexp_I_mul_le hz (φ x))

include hφ in
/-- **Bound on a strip**: `‖(∫ exp (i z φ) dE) ξ‖² ≤ ‖(∫ exp (-a φ) dE) ξ‖² + ‖(∫ exp (-b φ) dE) ξ‖²`
for `a ≤ im z ≤ b`, written with the `L²` norms `∫ exp (-2 a φ) dE_ξ`. -/
lemma norm_integralApply_cexp_sq_le {a b : ℝ} {z : ℂ} (hz : z.im ∈ Icc a b)
    (ha : MemLp (fun x => Real.exp (-a * φ x)) 2 (E.measure ξ))
    (hb : MemLp (fun x => Real.exp (-b * φ x)) 2 (E.measure ξ)) :
    ‖E.integralApply (fun x => cexp (I * z * φ x)) ξ‖ ^ 2 ≤
      ∫ x, Real.exp (-a * φ x) ^ 2 ∂(E.measure ξ) + ∫ x, Real.exp (-b * φ x) ^ 2 ∂(E.measure ξ) := by
  have hIa := (memLp_two_iff_integrable_sq_norm ha.aestronglyMeasurable).mp ha
  have hIb := (memLp_two_iff_integrable_sq_norm hb.aestronglyMeasurable).mp hb
  simp only [Real.norm_eq_abs, sq_abs] at hIa hIb
  have hF : MemLp (fun x => cexp (I * z * φ x)) 2 (E.measure ξ) :=
    (ha.add hb).of_le_mul (c := 1) (measurable_cexp_I_mul hφ z).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [one_mul]
        exact (norm_cexp_I_mul_le hz (φ x)).trans (le_abs_self _))
  rw [E.norm_integralApply_sq (measurable_cexp_I_mul hφ z) hF, ← MeasureTheory.integral_add hIa hIb]
  refine integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity) (hIa.add hIb)
    (Eventually.of_forall fun x => ?_)
  exact norm_cexp_I_mul_sq_le hz (φ x)

include hφ in
/-- **Analytic continuation to a half-plane**: if `φ ≥ 0` `E_ξ`-almost everywhere, then
`z ↦ (∫ exp (i z φ) dE) ξ` is holomorphic on `im z > 0` and continuous up to the real axis. For
`φ = id` and the projection-valued measure of a positive self-adjoint `B` this is
`z ↦ e^{izB} ξ`. -/
lemma diffContOnCl_integralApply_cexp_of_nonneg (hφ0 : ∀ᵐ x ∂(E.measure ξ), 0 ≤ φ x) :
    DiffContOnCl ℂ (fun z => E.integralApply (fun x => cexp (I * z * φ x)) ξ)
      (im ⁻¹' Ioi 0) := by
  have hle : ∀ᵐ x ∂(E.measure ξ), ∀ z ∈ im ⁻¹' Ici 0, ‖cexp (I * z * φ x)‖ ≤ (1 : ℝ) :=
    hφ0.mono fun x hx z hz => by
      rw [norm_cexp_I_mul, Real.exp_le_one_iff]
      nlinarith [show 0 ≤ z.im from hz]
  have hG : MemLp (fun _ : X => (1 : ℝ)) 2 (E.measure ξ) := memLp_const 1
  refine ⟨E.differentiableOn_integralApply (isOpen_Ioi.preimage continuous_im)
    (F' := fun z x => I * φ x * cexp (I * z * φ x)) (fun z _ => measurable_cexp_I_mul hφ z)
    (fun z _ => by fun_prop) (fun x z _ => hasDerivAt_cexp_I_mul (φ x) z) hG
    (hle.mono fun x hx z hz => hx z (le_of_lt hz)), ?_⟩
  rw [closure_preimage_im, closure_Ioi]
  exact E.continuousOn_integralApply (fun z _ => measurable_cexp_I_mul hφ z)
    (fun x => by fun_prop) hG hle

end Exponential

end MeasureTheory.ProjectionValuedMeasure
