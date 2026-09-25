/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import QuantumSystem.Analysis.UnboundedOperator.ResolventCFC

/-!
# Scalar spectral measures of self-adjoint operators

Let `A` be a self-adjoint operator on a complex Hilbert space `E`, `w` a point of its resolvent
set and `R_w = (w - A)⁻¹` the resolvent at `w`, a normal bounded operator. For `u : E`, the
functional `g ↦ re ⟪u, cfc g R_w u⟫` on real continuous functions on the spectrum of `R_w` is
positive (`IsSelfAdjoint.resolventFunctional`), and the Riesz–Markov–Kakutani theorem represents
it by a finite measure `ν_u^w` on `ℂ` (`IsSelfAdjoint.resolventMeasure`), concentrated on the
spectrum of `R_w`. Transporting `ν_u^w` along `ζ ↦ re (w - ζ⁻¹)`, the inverse of `λ ↦ (w - λ)⁻¹`
on the nonzero spectrum of `R_w`, gives the **scalar spectral measure** `μ_u` of `A` on `ℝ`
(`IsSelfAdjoint.spectralMeasure`, built at `w = i`). It does not depend on the base point `w`
(`IsSelfAdjoint.spectralMeasure_eq_map_resolventMeasure`), and it is tied to `A` by the
Stieltjes representation `⟪u, (z - A)⁻¹ u⟫ = ∫ (z - λ)⁻¹ dμ_u(λ)`.

"Spectral measure" here always means this scalar measure `μ_u = ⟪E(·) u, u⟫`; the
projection-valued measure `E` is not constructed. Functions of `A` are never named separately:
they are `cfc g R_w`, with `g ζ = f (w - ζ⁻¹)`.

## Main definitions

* `IsSelfAdjoint.resolventFunctional hA w u` — the positive functional `g ↦ re ⟪u, cfc g R_w u⟫`.
* `IsSelfAdjoint.resolventMeasure hA w u` — the measure `ν_u^w` on `ℂ`.
* `IsSelfAdjoint.spectralMeasure hA u` — the scalar spectral measure `μ_u` on `ℝ`.

## Main results

* `IsSelfAdjoint.integral_resolventMeasure`, `IsSelfAdjoint.inner_cfc_eq_integral_resolventMeasure`
  — `∫ g dν_u^w = ⟪u, cfc g R_w u⟫` for `g` continuous on the spectrum of `R_w` (real and complex
  forms).
* `IsSelfAdjoint.eq_resolventMeasure_of_integral` — uniqueness: `ν_u^w` is the only finite measure
  with these integrals against bounded continuous real functions.
* `IsSelfAdjoint.resolventMeasure_compl_spectrum` — `ν_u^w` is concentrated on the spectrum of
  `R_w`.
* `IsSelfAdjoint.resolventMeasure_univ`, `IsSelfAdjoint.spectralMeasure_univ` — total mass
  `‖u‖²`.
* `IsSelfAdjoint.resolventMeasure_singleton_eq_zero_of_mem_closure_range` — `ν_u^w {ζ₀} = 0`
  when `u` lies in the closure of the range of `R_w - ζ₀`.
* `IsSelfAdjoint.resolventMeasure_singleton_zero` — `ν_u^w {0} = 0`, because `R_w` has dense
  range.
* `IsSelfAdjoint.resolventMeasure_eq_map` — change of base point: `ν_u^w` is the image of `ν_u^v`
  under `ζ ↦ ζ / (1 - (v - w) ζ)`.
* `IsSelfAdjoint.spectralMeasure_eq_map_resolventMeasure` — **base-point independence**:
  `μ_u` is the image of `ν_u^w` under `ζ ↦ re (w - ζ⁻¹)` for every `w` in the resolvent set.
* `IsSelfAdjoint.map_spectralMeasure` — `μ_u` pushed forward along `λ ↦ (w - λ)⁻¹` is `ν_u^w`.
* `IsSelfAdjoint.integral_spectralMeasure_eq_inner_cfc` —
  `∫ g ((w - λ)⁻¹) dμ_u = ⟪u, cfc g R_w u⟫`.
* `IsSelfAdjoint.inner_resolvent_eq_integral` — the Stieltjes representation
  `⟪u, (z - A)⁻¹ u⟫ = ∫ (z - λ)⁻¹ dμ_u` for `z` in the resolvent set.
* `IsSelfAdjoint.integral_spectralMeasure` — `∫ f dμ_u = ∫ f (re (w - ζ⁻¹)) dν_u^w`.
* `IsSelfAdjoint.spectralMeasure_congr` — `μ_u` transports along equalities of operators.
-/

@[expose] public section

open Complex MeasureTheory CompactlySupportedContinuousMap
open scoped ComplexConjugate LinearPMap CompactlySupported BoundedContinuousFunction

/-- Real-valued continuous functions as complex-valued ones (Mathlib's
`ContinuousLinearMap.compLeftContinuous` along `Complex.ofRealCLM`). -/
local notation "ofRealCM" => ContinuousLinearMap.compLeftContinuous ℝ _ Complex.ofRealCLM

namespace IsSelfAdjoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {A : E →ₗ.[ℂ] E}

/-- `i` lies in the resolvent set of a self-adjoint operator. -/
lemma I_mem_resolventSet (hA : IsSelfAdjoint A) : I ∈ A.resolventSet :=
  hA.mem_resolventSet (by simp)

/-- The positive functional `g ↦ re ⟪u, g((w - A)⁻¹) u⟫` on real continuous functions on the
spectrum of `(w - A)⁻¹`. -/
noncomputable def resolventFunctional (hA : IsSelfAdjoint A) (w : ℂ) (u : E) :
    C_c(spectrum ℂ (A.resolvent w), ℝ) →ₚ[ℝ] ℝ where
  toFun g := re (inner ℂ u (cfcHom (hA.isStarNormal_resolvent w)
    (ofRealCM (g : C(spectrum ℂ (A.resolvent w), ℝ))) u))
  map_add' g g' := by
    rw [show ((g + g' : C_c(_, ℝ)) : C(spectrum ℂ (A.resolvent w), ℝ)) = g + g' from rfl, map_add,
      map_add, _root_.add_apply, inner_add_right, add_re]
  map_smul' c g := by
    have : ofRealCM ((c • g : C_c(_, ℝ)) : C(spectrum ℂ (A.resolvent w), ℝ)) =
        (c : ℂ) • ofRealCM (g : C(spectrum ℂ (A.resolvent w), ℝ)) := by
      ext x
      simp
    rw [this, map_smul, _root_.smul_apply, inner_smul_right, re_ofReal_mul, RingHom.id_apply,
      smul_eq_mul]
  monotone' g g' hgg' := by
    set h := g' - g
    have hh : ∀ x, 0 ≤ h x := fun x => sub_nonneg.mpr (hgg' x)
    let s : C(spectrum ℂ (A.resolvent w), ℂ) := ⟨fun x => (Real.sqrt (h x) : ℂ), by fun_prop⟩
    have hs : ofRealCM (h : C(spectrum ℂ (A.resolvent w), ℝ)) = star s * s := by
      ext x
      change ((h x : ℝ) : ℂ) = star (Real.sqrt (h x) : ℂ) * (Real.sqrt (h x) : ℂ)
      rw [star_def, conj_ofReal, ← ofReal_mul, Real.mul_self_sqrt (hh x)]
    have hg' : ofRealCM (g' : C(spectrum ℂ (A.resolvent w), ℝ)) =
        ofRealCM (g : C(spectrum ℂ (A.resolvent w), ℝ)) +
          ofRealCM (h : C(spectrum ℂ (A.resolvent w), ℝ)) := by
      rw [← map_add]
      congr 1
      ext x
      simp [h]
    have key : 0 ≤ re (inner ℂ u (cfcHom (hA.isStarNormal_resolvent w)
        (ofRealCM (h : C(spectrum ℂ (A.resolvent w), ℝ))) u)) := by
      rw [hs, map_mul, map_star, ContinuousLinearMap.star_eq_adjoint, mul_apply_eq_comp,
        ContinuousLinearMap.adjoint_inner_right]
      exact inner_self_nonneg (𝕜 := ℂ)
    change re _ ≤ re _
    rw [hg', map_add, _root_.add_apply, inner_add_right, add_re]
    linarith

/-- The measure `ν_u^w` on `ℂ` representing `g ↦ re ⟪u, cfc g R u⟫` for `R = (w - A)⁻¹`; it is
concentrated on the spectrum of `R` (`IsSelfAdjoint.resolventMeasure_compl_spectrum`). -/
noncomputable def resolventMeasure (hA : IsSelfAdjoint A) (w : ℂ) (u : E) : Measure ℂ :=
  (RealRMK.rieszMeasure (hA.resolventFunctional w u)).map Subtype.val

/-- The **scalar spectral measure** `μ_u` of a self-adjoint operator `A` at `u`: the image of
`ν_u^i` under `ζ ↦ re (i - ζ⁻¹)`, which inverts `λ ↦ (i - λ)⁻¹` on the nonzero spectrum of
`(i - A)⁻¹`. Any other point of the resolvent set gives the same measure
(`IsSelfAdjoint.spectralMeasure_eq_map_resolventMeasure`). -/
noncomputable def spectralMeasure (hA : IsSelfAdjoint A) (u : E) : Measure ℝ :=
  (hA.resolventMeasure I u).map fun ζ => re (I - ζ⁻¹)

instance (hA : IsSelfAdjoint A) (w : ℂ) (u : E) : IsFiniteMeasure (hA.resolventMeasure w u) := by
  unfold resolventMeasure
  infer_instance

instance (hA : IsSelfAdjoint A) (u : E) : IsFiniteMeasure (hA.spectralMeasure u) := by
  unfold spectralMeasure
  infer_instance

private lemma measurableEmbedding_val (R : E →L[ℂ] E) :
    MeasurableEmbedding (Subtype.val : spectrum ℂ R → ℂ) :=
  MeasurableEmbedding.subtype_coe (spectrum.isClosed R).measurableSet

variable (hA : IsSelfAdjoint A) (w : ℂ) (u : E)

/-- **Spectral integral formula.** For a real function `g` continuous on the spectrum of
`R = (w - A)⁻¹`, `∫ g dν_u^w = re ⟪u, cfc g R u⟫`. -/
theorem integral_resolventMeasure {g : ℂ → ℝ} (hg : ContinuousOn g (spectrum ℂ (A.resolvent w))) :
    ∫ ζ, g ζ ∂(hA.resolventMeasure w u) =
      re (inner ℂ u (cfc (fun ζ => (g ζ : ℂ)) (A.resolvent w) u)) := by
  let g' : C_c(spectrum ℂ (A.resolvent w), ℝ) :=
    ⟨⟨fun x => g x, hg.domRestrict⟩, HasCompactSupport.of_compactSpace _⟩
  rw [resolventMeasure, (measurableEmbedding_val _).integral_map]
  refine (RealRMK.integral_rieszMeasure (hA.resolventFunctional w u) g').trans ?_
  rw [cfc_apply (fun ζ => (g ζ : ℂ)) (A.resolvent w) (hA.isStarNormal_resolvent w)
    (continuous_ofReal.comp_continuousOn hg)]
  rfl

variable {w u} in
/-- **Uniqueness.** A finite measure `ν` on `ℂ` with `∫ g dν = re ⟪u, cfc g R u⟫` for every
bounded continuous real `g`, where `R = (w - A)⁻¹`, is the measure `ν_u^w`. -/
theorem eq_resolventMeasure_of_integral (ν : Measure ℂ) [IsFiniteMeasure ν]
    (h : ∀ g : ℂ →ᵇ ℝ, ∫ ζ, g ζ ∂ν =
      re (inner ℂ u (cfc (fun ζ => (g ζ : ℂ)) (A.resolvent w) u))) :
    ν = hA.resolventMeasure w u :=
  ext_of_forall_integral_eq_of_IsFiniteMeasure fun g =>
    (h g).trans (hA.integral_resolventMeasure w u g.continuous.continuousOn).symm

/-- `ν_u^w` is concentrated on the spectrum of `(w - A)⁻¹`. -/
theorem resolventMeasure_compl_spectrum :
    hA.resolventMeasure w u (spectrum ℂ (A.resolvent w))ᶜ = 0 := by
  rw [resolventMeasure, Measure.map_apply measurable_subtype_coe
    (spectrum.isClosed _).measurableSet.compl]
  convert measure_empty (μ := RealRMK.rieszMeasure (hA.resolventFunctional w u))
  ext x
  simp

/-- The total mass of `ν_u^w` is `‖u‖²`, as a real number. -/
theorem measureReal_resolventMeasure_univ :
    (hA.resolventMeasure w u).real Set.univ = ‖u‖ ^ 2 := by
  have : IsStarNormal (A.resolvent w) := hA.isStarNormal_resolvent w
  have h := hA.integral_resolventMeasure w u (g := fun _ => 1) continuousOn_const
  simp only [integral_const, smul_eq_mul, mul_one, ofReal_one] at h
  rw [h, cfc_const_one ℂ (A.resolvent w), one_apply_eq_self]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) u

/-- The total mass of `ν_u^w` is `‖u‖²`. -/
theorem resolventMeasure_univ :
    hA.resolventMeasure w u Set.univ = ENNReal.ofReal (‖u‖ ^ 2) := by
  rw [← hA.measureReal_resolventMeasure_univ w u, measureReal_def, ENNReal.ofReal_toReal
    (measure_ne_top _ _)]

variable {w u} in
/-- `ν_u^w` has no atom at `ζ₀` when `u` lies in the closure of the range of `R - ζ₀`, for
`R = (w - A)⁻¹`: then `(1 + n² |R - ζ₀|²)⁻¹ u → 0`. -/
theorem resolventMeasure_singleton_eq_zero_of_mem_closure_range {ζ₀ : ℂ}
    (hu : u ∈ closure (Set.range (A.resolvent w - algebraMap ℂ (E →L[ℂ] E) ζ₀))) :
    hA.resolventMeasure w u {ζ₀} = 0 := by
  have : IsStarNormal (A.resolvent w) := hA.isStarNormal_resolvent w
  set R := A.resolvent w
  set ν := hA.resolventMeasure w u
  let φ : ℕ → ℂ → ℝ := fun n ζ => (1 + (n : ℝ) ^ 2 * ‖ζ - ζ₀‖ ^ 2)⁻¹
  have hpos : ∀ (n : ℕ) (ζ : ℂ), 0 < 1 + (n : ℝ) ^ 2 * ‖ζ - ζ₀‖ ^ 2 := fun n ζ => by positivity
  have hcont : ∀ n, Continuous (φ n) := fun n =>
    Continuous.inv₀ (by fun_prop) fun ζ => (hpos n ζ).ne'
  have hφ1 : ∀ n ζ, φ n ζ ≤ 1 := fun n ζ =>
    inv_le_one_of_one_le₀ (le_add_of_nonneg_right (by positivity))
  have hφ0 : ∀ n ζ, 0 ≤ φ n ζ := fun n ζ => (inv_pos.mpr (hpos n ζ)).le
  -- `ν {ζ₀}` is controlled by `‖(1 + n² |R - ζ₀|²)⁻¹ u‖`.
  have hle : ∀ n, ν.real {ζ₀} ≤ ‖u‖ * ‖cfc (fun ζ => (φ n ζ : ℂ)) R u‖ := fun n => by
    calc ν.real {ζ₀} = ∫ ζ, Set.indicator {ζ₀} (fun _ => (1 : ℝ)) ζ ∂ν :=
          (integral_indicator_one (measurableSet_singleton ζ₀)).symm
      _ ≤ ∫ ζ, φ n ζ ∂ν := by
          refine integral_mono ((integrable_const 1).indicator (measurableSet_singleton ζ₀))
            (Integrable.of_bound (hcont n).aestronglyMeasurable 1
              (Filter.Eventually.of_forall fun ζ => ?_)) fun ζ => ?_
          · rw [Real.norm_of_nonneg (hφ0 n ζ)]
            exact hφ1 n ζ
          · by_cases hζ : ζ = ζ₀
            · simp [hζ, φ]
            · simp [hζ, hφ0 n ζ]
      _ = re (inner ℂ u (cfc (fun ζ => (φ n ζ : ℂ)) R u)) :=
          hA.integral_resolventMeasure w u (hcont n).continuousOn
      _ ≤ ‖inner ℂ u (cfc (fun ζ => (φ n ζ : ℂ)) R u)‖ := re_le_norm _
      _ ≤ ‖u‖ * ‖cfc (fun ζ => (φ n ζ : ℂ)) R u‖ := norm_inner_le_norm _ _
  -- `(1 + n² |R - ζ₀|²)⁻¹ u → 0`, since `u` is approximated by the range of `R - ζ₀`.
  have hsmall : ∀ ε > 0, ∃ n, ‖cfc (fun ζ => (φ n ζ : ℂ)) R u‖ ≤ ε := fun ε hε => by
    obtain ⟨b, hb, hub⟩ := Metric.mem_closure_iff.mp hu (ε / 2) (by positivity)
    obtain ⟨v, rfl⟩ := hb
    have hub' : dist u ((R - algebraMap ℂ (E →L[ℂ] E) ζ₀) v) < ε / 2 := hub
    obtain ⟨n, hn⟩ := exists_nat_gt (2 * ‖v‖ / ε)
    have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn
    refine ⟨n, ?_⟩
    have h₁ : ‖cfc (fun ζ => (φ n ζ : ℂ)) R‖ ≤ 1 := norm_cfc_le zero_le_one fun ζ _ => by
      rw [norm_real, Real.norm_of_nonneg (hφ0 n ζ)]
      exact hφ1 n ζ
    have h₂ : ‖cfc (fun ζ => (φ n ζ : ℂ) * (ζ - ζ₀)) R‖ ≤ (n : ℝ)⁻¹ :=
      norm_cfc_le (by positivity) fun ζ _ => by
        rw [norm_mul, norm_real, Real.norm_of_nonneg (hφ0 n ζ), inv_mul_eq_div,
          div_le_iff₀ (hpos n ζ), inv_mul_eq_div, le_div_iff₀' hn0]
        nlinarith [sq_nonneg ((n : ℝ) * ‖ζ - ζ₀‖ - 1), norm_nonneg (ζ - ζ₀)]
    have hsplit : cfc (fun ζ => (φ n ζ : ℂ)) R u =
        cfc (fun ζ => (φ n ζ : ℂ)) R (u - (R - algebraMap ℂ (E →L[ℂ] E) ζ₀) v) +
          cfc (fun ζ => (φ n ζ : ℂ) * (ζ - ζ₀)) R v := by
      have hc : ContinuousOn (fun ζ => (φ n ζ : ℂ)) (spectrum ℂ R) :=
        (continuous_ofReal.comp (hcont n)).continuousOn
      rw [cfc_mul (fun ζ => (φ n ζ : ℂ)) (fun ζ => ζ - ζ₀) R hc,
        cfc_sub (fun ζ : ℂ => ζ) (fun _ => ζ₀) R, cfc_id' ℂ R, cfc_const ζ₀ R,
        mul_apply_eq_comp, ContinuousLinearMap.map_sub, sub_add_cancel]
    rw [hsplit]
    calc _ ≤ ‖cfc (fun ζ => (φ n ζ : ℂ)) R (u - (R - algebraMap ℂ (E →L[ℂ] E) ζ₀) v)‖ +
          ‖cfc (fun ζ => (φ n ζ : ℂ) * (ζ - ζ₀)) R v‖ := norm_add_le _ _
      _ ≤ 1 * ‖u - (R - algebraMap ℂ (E →L[ℂ] E) ζ₀) v‖ + (n : ℝ)⁻¹ * ‖v‖ := by
          gcongr
          · exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr)
          · exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr)
      _ ≤ ε := by
          rw [one_mul, ← dist_eq_norm]
          have : (n : ℝ)⁻¹ * ‖v‖ ≤ ε / 2 := by
            rw [inv_mul_eq_div, div_le_iff₀ hn0]
            rw [div_lt_iff₀ hε] at hn
            linarith
          linarith [hub'.le]
  have h0 : ν.real {ζ₀} ≤ 0 := by
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    obtain ⟨n, hn⟩ := hsmall (δ / (‖u‖ + 1)) (by positivity)
    calc ν.real {ζ₀} ≤ ‖u‖ * ‖cfc (fun ζ => (φ n ζ : ℂ)) R u‖ := hle n
      _ ≤ (‖u‖ + 1) * (δ / (‖u‖ + 1)) := by gcongr; linarith
      _ = 0 + δ := by field_simp; ring
  rw [← measureReal_eq_zero_iff]
  exact le_antisymm h0 measureReal_nonneg

variable {w} in
/-- `ν_u^w` has no atom at `0`: for `w` in the resolvent set, `(w - A)⁻¹` has dense range
`dom A`. -/
theorem resolventMeasure_singleton_zero (hw : w ∈ A.resolventSet) :
    hA.resolventMeasure w u {0} = 0 := by
  refine hA.resolventMeasure_singleton_eq_zero_of_mem_closure_range ?_
  rw [map_zero, sub_zero]
  have := hA.dense_domain u
  rwa [← LinearPMap.range_resolvent hw, LinearMap.coe_range] at this

private lemma measurable_re_sub_inv (w : ℂ) : Measurable fun ζ : ℂ => re (w - ζ⁻¹) := by
  fun_prop

/-- `ν_u^w`-almost every point lies in the spectrum of `(w - A)⁻¹`. -/
lemma ae_mem_spectrum_resolventMeasure :
    ∀ᵐ ζ ∂(hA.resolventMeasure w u), ζ ∈ spectrum ℂ (A.resolvent w) :=
  ae_iff.mpr (hA.resolventMeasure_compl_spectrum w u)

variable {w} in
/-- `ν_u^w`-almost every point is nonzero. -/
lemma ae_ne_zero_resolventMeasure (hw : w ∈ A.resolventSet) :
    ∀ᵐ ζ ∂(hA.resolventMeasure w u), ζ ≠ 0 :=
  ae_iff.mpr (by simpa using hA.resolventMeasure_singleton_zero u hw)

variable {w} in
/-- A function continuous on the spectrum of `(w - A)⁻¹` is `ν_u^w`-integrable. -/
theorem integrable_resolventMeasure {g : ℂ → ℂ}
    (hg : ContinuousOn g (spectrum ℂ (A.resolvent w))) :
    Integrable g (hA.resolventMeasure w u) := by
  have := hg.integrableOn_compact (spectrum.isCompact _) (μ := hA.resolventMeasure w u)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem
    (hA.ae_mem_spectrum_resolventMeasure w u)] at this

variable {w} in
/-- **Spectral integral formula**, complex form. For `g` continuous on the spectrum of
`R = (w - A)⁻¹`, `⟪u, cfc g R u⟫ = ∫ g dν_u^w`. -/
theorem inner_cfc_eq_integral_resolventMeasure {g : ℂ → ℂ}
    (hg : ContinuousOn g (spectrum ℂ (A.resolvent w))) :
    inner ℂ u (cfc g (A.resolvent w) u) = ∫ ζ, g ζ ∂(hA.resolventMeasure w u) := by
  have : IsStarNormal (A.resolvent w) := hA.isStarNormal_resolvent w
  have hreal : ∀ h : ℂ → ℝ, ContinuousOn h (spectrum ℂ (A.resolvent w)) →
      inner ℂ u (cfc (fun ζ => (h ζ : ℂ)) (A.resolvent w) u) =
        ((∫ ζ, h ζ ∂(hA.resolventMeasure w u) : ℝ) : ℂ) := fun h hh => by
    rw [hA.integral_resolventMeasure w u hh]
    have hsa : ContinuousLinearMap.adjoint (cfc (fun ζ => (h ζ : ℂ)) (A.resolvent w)) =
        cfc (fun ζ => (h ζ : ℂ)) (A.resolvent w) := by
      rw [← ContinuousLinearMap.star_eq_adjoint, ← cfc_star]
      exact cfc_congr fun ζ _ => by simp
    have hc : conj (inner ℂ u (cfc (fun ζ => (h ζ : ℂ)) (A.resolvent w) u)) =
        inner ℂ u (cfc (fun ζ => (h ζ : ℂ)) (A.resolvent w) u) := by
      rw [inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_right, hsa]
    refine Complex.ext (ofReal_re _).symm ?_
    rw [ofReal_im]
    exact conj_eq_iff_im.mp hc
  have hsplit : cfc g (A.resolvent w) = cfc (fun ζ => ((g ζ).re : ℂ)) (A.resolvent w) +
      I • cfc (fun ζ => ((g ζ).im : ℂ)) (A.resolvent w) := by
    have hre : ContinuousOn (fun ζ => ((g ζ).re : ℂ)) (spectrum ℂ (A.resolvent w)) :=
      continuous_ofReal.comp_continuousOn (continuous_re.comp_continuousOn hg)
    have him : ContinuousOn (fun ζ => ((g ζ).im : ℂ)) (spectrum ℂ (A.resolvent w)) :=
      continuous_ofReal.comp_continuousOn (continuous_im.comp_continuousOn hg)
    rw [← cfc_const_mul I _ _ him, ← cfc_add (A.resolvent w) (fun ζ => ((g ζ).re : ℂ))
      (fun ζ => I * ((g ζ).im : ℂ)) hre (continuousOn_const.mul him)]
    exact cfc_congr fun ζ _ => by rw [mul_comm, re_add_im]
  rw [hsplit, _root_.add_apply, _root_.smul_apply, inner_add_right, inner_smul_right,
    hreal (fun ζ => (g ζ).re) (continuous_re.comp_continuousOn hg),
    hreal (fun ζ => (g ζ).im) (continuous_im.comp_continuousOn hg)]
  have := integral_re_add_im (hA.integrable_resolventMeasure u hg)
  simp only [RCLike.re_to_complex, RCLike.im_to_complex, RCLike.I_to_complex] at this
  rw [mul_comm]
  exact this

variable {w} in
/-- **Change of base point.** For `v`, `w` in the resolvent set, `ν_u^w` is the image of `ν_u^v`
under `ζ ↦ ζ / (1 - (v - w) ζ)`, the function sending `(v - A)⁻¹` to `(w - A)⁻¹`
(`IsSelfAdjoint.resolvent_eq_cfc`). -/
theorem resolventMeasure_eq_map {v : ℂ} (hv : v ∈ A.resolventSet) (hw : w ∈ A.resolventSet) :
    hA.resolventMeasure w u =
      (hA.resolventMeasure v u).map fun ζ => ζ / (1 - (v - w) * ζ) := by
  have : IsStarNormal (A.resolvent v) := hA.isStarNormal_resolvent v
  have hφ : ContinuousOn (fun ζ : ℂ => ζ / (1 - (v - w) * ζ)) (spectrum ℂ (A.resolvent v)) :=
    continuousOn_id.div (by fun_prop) fun ζ hζ =>
      LinearPMap.one_sub_mul_ne_zero_of_mem_spectrum hv hw hζ
  have hφm : Measurable fun ζ : ℂ => ζ / (1 - (v - w) * ζ) := by fun_prop
  refine (hA.eq_resolventMeasure_of_integral _ fun g => ?_).symm
  rw [integral_map hφm.aemeasurable g.continuous.aestronglyMeasurable,
    hA.integral_resolventMeasure v u (g := fun ζ => g (ζ / (1 - (v - w) * ζ)))
      (g.continuous.comp_continuousOn hφ),
    hA.resolvent_eq_cfc hv hw, ← cfc_comp' (fun ζ => (g ζ : ℂ)) _ _
      (continuous_ofReal.comp g.continuous).continuousOn hφ]

variable {w} in
/-- **Base-point independence.** For every `w` in the resolvent set, the scalar spectral measure
`μ_u` is the image of `ν_u^w` under `ζ ↦ re (w - ζ⁻¹)`: the construction of `μ_u` does not depend
on the base point `i` used in `IsSelfAdjoint.spectralMeasure`. -/
theorem spectralMeasure_eq_map_resolventMeasure (hw : w ∈ A.resolventSet) :
    hA.spectralMeasure u = (hA.resolventMeasure w u).map fun ζ => re (w - ζ⁻¹) := by
  have hφm : Measurable fun ζ : ℂ => ζ / (1 - (I - w) * ζ) := by fun_prop
  rw [spectralMeasure, hA.resolventMeasure_eq_map u hA.I_mem_resolventSet hw,
    Measure.map_map (measurable_re_sub_inv w) hφm]
  refine Measure.map_congr ?_
  filter_upwards [hA.ae_mem_spectrum_resolventMeasure I u,
    hA.ae_ne_zero_resolventMeasure u hA.I_mem_resolventSet] with ζ hζ h0
  have h1 := LinearPMap.one_sub_mul_ne_zero_of_mem_spectrum hA.I_mem_resolventSet hw hζ
  simp only [Function.comp_apply]
  congr 1
  rw [inv_div]
  field_simp
  ring

variable {w} in
/-- The spectral measure `μ_u` recovers `ν_u^w` under `λ ↦ (w - λ)⁻¹`. -/
theorem map_spectralMeasure (hw : w ∈ A.resolventSet) :
    (hA.spectralMeasure u).map (fun t : ℝ => (w - t)⁻¹) = hA.resolventMeasure w u := by
  have hψ : Measurable fun t : ℝ => (w - t)⁻¹ := by fun_prop
  rw [hA.spectralMeasure_eq_map_resolventMeasure u hw,
    Measure.map_map hψ (measurable_re_sub_inv w)]
  conv_rhs => rw [← Measure.map_id (μ := hA.resolventMeasure w u)]
  refine Measure.map_congr ?_
  filter_upwards [hA.ae_mem_spectrum_resolventMeasure w u, hA.ae_ne_zero_resolventMeasure u hw]
    with ζ hζ h0
  have him := hA.im_sub_inv_eq_zero_of_mem_spectrum hw hζ h0
  have hre : ((re (w - ζ⁻¹) : ℝ) : ℂ) = w - ζ⁻¹ := Complex.ext rfl (by simpa using him.symm)
  simp only [Function.comp_apply, hre, sub_sub_cancel, inv_inv, id_eq]

variable {w} in
/-- **Spectral integral formula** on the real line. For `w` in the resolvent set and `g`
continuous on the spectrum of `R = (w - A)⁻¹`, `∫ g ((w - λ)⁻¹) dμ_u(λ) = ⟪u, cfc g R u⟫`. -/
theorem integral_spectralMeasure_eq_inner_cfc (hw : w ∈ A.resolventSet) {g : ℂ → ℂ}
    (hg : ContinuousOn g (spectrum ℂ (A.resolvent w))) :
    ∫ t, g ((w - t)⁻¹) ∂(hA.spectralMeasure u) = inner ℂ u (cfc g (A.resolvent w) u) := by
  have hψ : Measurable fun t : ℝ => (w - t)⁻¹ := by fun_prop
  rw [hA.inner_cfc_eq_integral_resolventMeasure u hg, ← hA.map_spectralMeasure u hw,
    integral_map hψ.aemeasurable]
  rw [hA.map_spectralMeasure u hw]
  exact (hA.integrable_resolventMeasure u hg).aestronglyMeasurable

omit hA in
/-- The spectral measure transports along equalities of operators, whatever proofs of
self-adjointness are used to build it. -/
theorem spectralMeasure_congr {B : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (h : A = B) (u : E) : hA.spectralMeasure u = hB.spectralMeasure u := by
  subst h
  rfl

/-- The total mass of the spectral measure `μ_u` is `‖u‖²`. -/
theorem spectralMeasure_univ : hA.spectralMeasure u Set.univ = ENNReal.ofReal (‖u‖ ^ 2) := by
  rw [spectralMeasure, Measure.map_apply (measurable_re_sub_inv I) MeasurableSet.univ,
    Set.preimage_univ, resolventMeasure_univ]

variable {w} in
/-- Integration against the spectral measure `μ_u` is integration against `ν_u^w` after the
change of variables `λ = re (w - ζ⁻¹)`, for any `w` in the resolvent set. -/
theorem integral_spectralMeasure (hw : w ∈ A.resolventSet) {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (hA.spectralMeasure u)) :
    ∫ t, f t ∂(hA.spectralMeasure u) = ∫ ζ, f (re (w - ζ⁻¹)) ∂(hA.resolventMeasure w u) := by
  rw [hA.spectralMeasure_eq_map_resolventMeasure u hw] at hf ⊢
  rw [integral_map (measurable_re_sub_inv w).aemeasurable hf]

/-- **Stieltjes representation.** For `z` in the resolvent set of `A`,
`⟪u, (z - A)⁻¹ u⟫ = ∫ (z - λ)⁻¹ dμ_u(λ)`. -/
theorem inner_resolvent_eq_integral {z : ℂ} (hz : z ∈ A.resolventSet) :
    inner ℂ u (A.resolvent z u) = ∫ t, (z - t)⁻¹ ∂(hA.spectralMeasure u) := by
  have hcont : ContinuousOn (fun ζ : ℂ => ζ / (1 - (I - z) * ζ)) (spectrum ℂ (A.resolvent I)) :=
    continuousOn_id.div (by fun_prop) fun ζ hζ =>
      LinearPMap.one_sub_mul_ne_zero_of_mem_spectrum hA.I_mem_resolventSet hz hζ
  rw [hA.resolvent_eq_cfc hA.I_mem_resolventSet hz,
    ← hA.integral_spectralMeasure_eq_inner_cfc u hA.I_mem_resolventSet hcont]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  have hIt : I - (t : ℂ) ≠ 0 := fun h => by simpa using congrArg im h
  change (I - (t : ℂ))⁻¹ / (1 - (I - z) * (I - (t : ℂ))⁻¹) = (z - t)⁻¹
  rw [show (1 : ℂ) - (I - z) * (I - (t : ℂ))⁻¹ = (z - t) * (I - (t : ℂ))⁻¹ by
    field_simp
    ring, div_eq_mul_inv, mul_inv, inv_inv, mul_comm (z - (t : ℂ))⁻¹, ← mul_assoc,
    inv_mul_cancel₀ hIt, one_mul]

end IsSelfAdjoint
