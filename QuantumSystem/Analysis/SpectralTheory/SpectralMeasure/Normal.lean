/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.MeasureTheory.Measure.Support
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Intertwine
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.LinearMap
public import QuantumSystem.ForMathlib.MeasureTheory.VectorMeasure.Integral
public import QuantumSystem.ForMathlib.MeasureTheory.VectorMeasure.ProjectionValued

/-!
# The projection-valued measure of a normal operator

Let `T` be a normal bounded operator on a complex Hilbert space `E`. Its **projection-valued
measure** `E_T` on the Borel sets of `ℂ` (`IsStarNormal.pvm`) is the resolution of the identity
of Rudin, *Functional Analysis*, Theorems 12.22–12.23: `T = ∫ ζ dE_T(ζ)` weakly
(`IsStarNormal.inner_apply_eq_integral_pvm`), and more generally
`⟪x, cfc g T y⟫ = ∫ g dE_{x,y}` for `g` continuous on the spectrum
(`IsStarNormal.inner_cfc_eq_integral_pvm`), where `E_{x,y} = ⟪x, E_T(·) y⟫` is the complex measure
`hT.pvm.complexMeasure x y` and `E_x = ‖E_T(·) x‖²` the diagonal measure `hT.pvm.measure x`.

The construction follows the proof of Rudin, Theorem 12.22. Its inputs are the scalar spectral
measures `ν_u`, the finite measures on `ℂ` obtained from the positive functionals
`g ↦ re ⟪u, cfc g T u⟫` by the real Riesz–Markov–Kakutani theorem. By polarization,
`ν_{x,y} = ¼ (ν_{x+y} - ν_{x-y} - i ν_{x+iy} + i ν_{x-iy})` is a complex measure on `ℂ` (Rudin's
`E_{y,x}`, obtained without the complex Riesz–Markov–Kakutani theorem) whose real and imaginary
parts integrate real bounded continuous `g` to those of `⟪x, cfc g T y⟫`; by the uniqueness of
signed measures (`MeasureTheory.SignedMeasure.ext_of_forall_integral_eq`) this determines
`ν_{x,y}`, and every identity of the forms `⟪x, cfc g T y⟫` passes to the measures. The bounded
sesquilinear forms `(x, y) ↦ ν_{x,y}(s)` are represented by operators `E_T(s)` (through Mathlib's
`InnerProductSpace.continuousLinearMapOfBilin`), which form `E_T`. The projection property rests on
multiplicativity, `E_T(s ∩ t) = E_T(s) E_T(t)`, proved without densities of complex measures:
`E_T(s)` commutes with every `cfc h T`, so for `g = h²` with `h` real,
`⟪x, g(T) E_T(t) y⟫ = ν_{h(T) x, h(T) y}(t)`, and `ν_{h(T) u} = h² ν_u` identifies this with
`∫_t g dν_{x,y}`; by uniqueness `ν_{x, E_T(t) y}` is the restriction of `ν_{x,y}` to `t`.

The scalar and complex spectral measures are internal to this construction: they equal the
diagonal and complex measures of `E_T`, and every statement here and downstream is made for
`hT.pvm`, `hT.pvm.measure x` and `hT.pvm.complexMeasure x y` through the
`MeasureTheory.ProjectionValuedMeasure` API. The convention is Mathlib's: `E_{x,y}` is
conjugate-linear in `x` and linear in `y`.

## Main definitions

* `IsStarNormal.pvm hT` — the projection-valued measure `E_T` on `ℂ`.

## Main results

* `IsStarNormal.inner_cfc_eq_integral_pvm` — `⟪x, cfc g T y⟫ = ∫ g dE_{x,y}`;
  `IsStarNormal.inner_apply_eq_integral_pvm` — **the spectral theorem**, `T = ∫ ζ dE_T(ζ)`
  weakly.
* `IsStarNormal.commute_pvm_cfc` — `E_T(s)` commutes with `cfc h T`.
* `IsStarNormal.commute_pvm_of_commute` — **operators commuting with `T` commute with `E_T`**
  (Rudin, Theorem 12.23, through the Fuglede–Putnam–Rosenblum theorem
  `ContinuousLinearMap.comp_cfc_eq_cfc_comp`); with its converse
  `IsStarNormal.commute_of_forall_commute_pvm` it gives `IsStarNormal.forall_commute_pvm_iff`: an
  operator `S` commutes with `T` iff it commutes with every `E_T(s)` (Rudin, Theorems
  12.22–12.23). With
  `MeasureTheory.ProjectionValuedMeasure.commute_integral` it then commutes with every spectral
  integral `∫ f dE_T` of a bounded measurable `f`.
* `IsStarNormal.integral_measure_pvm`, `IsStarNormal.inner_cfc_eq_integral_measure_pvm`,
  `IsStarNormal.integrable_measure_pvm` — `∫ g dE_x = ⟪x, cfc g T x⟫` for `g` continuous on the
  spectrum (real and complex forms), and such `g` are `E_x`-integrable.
* `IsStarNormal.eq_measure_pvm_of_integral` — uniqueness: `E_x` is the only finite measure with
  these integrals against bounded continuous real functions.
* `IsStarNormal.measure_pvm_compl_spectrum`, `IsStarNormal.ae_mem_spectrum_measure_pvm`,
  `IsStarNormal.pvm_compl_spectrum` — `E_x` and `E_T` are concentrated on the spectrum of `T`.
* `IsStarNormal.measure_pvm_singleton_eq_zero_of_mem_closure_range` — `E_x {ζ₀} = 0` when `x`
  lies in the closure of the range of `T - ζ₀`.
* `IsStarNormal.measure_pvm_cfc_apply` — the transformation rule `E_{h(T) x} = |h|² E_x`.
* `IsStarNormal.pvm_cfc_eq_map` — **spectral mapping**: `E_{φ(T)}` is the image of `E_T` under `φ`.
* `IsStarNormal.eq_pvm_of_integral`, `IsStarNormal.eq_pvm_of_inner_self_eq_integral` —
  **uniqueness**: a projection-valued measure `F` on `ℂ` concentrated on a compact set with
  `T = ∫ ζ dF(ζ)` weakly is `E_T`.
* `IsStarNormal.mem_spectrum_iff_forall_pvm_ball_ne_zero` — **the spectrum is the support of
  `E_T`**: `ζ₀ ∈ σ(T)` iff `E_T` vanishes on no ball around `ζ₀`.
* `IsStarNormal.spectrum_eq_closure_iUnion_support` — `σ(T) = closure (⋃ᵤ supp E_u)`.
-/

@[expose] public section

open Complex MeasureTheory
open scoped ComplexConjugate InnerProductSpace BoundedContinuousFunction NNReal ENNReal

namespace IsStarNormal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ### Scalar spectral measures

For `u : E`, the functional `g ↦ re ⟪u, cfc g T u⟫` on real continuous functions on the spectrum
of `T` is positive, and the Riesz–Markov–Kakutani theorem represents it by a finite measure `ν_u`
on `ℂ`, concentrated on the spectrum of `T` (Rudin, *Functional Analysis*, Theorem 12.22,
restricted to the diagonal). These measures are the input of the construction; they coincide
with the diagonal measures of `E_T` (`measure_pvm`), and are not used past that point. -/

section ScalarSpectralMeasure

open CompactlySupportedContinuousMap
open scoped CompactlySupported

/-- Real-valued continuous functions as complex-valued ones (Mathlib's
`ContinuousLinearMap.compLeftContinuous` along `Complex.ofRealCLM`). -/
local notation "ofRealCM" => ContinuousLinearMap.compLeftContinuous ℝ _ Complex.ofRealCLM

variable [CompleteSpace E] {T : E →L[ℂ] E}

/-- The positive functional `g ↦ re ⟪u, g(T) u⟫` on real continuous functions on the spectrum of a
normal operator `T`. -/
private noncomputable def spectralFunctional (hT : IsStarNormal T) (u : E) :
    C_c(spectrum ℂ T, ℝ) →ₚ[ℝ] ℝ where
  toFun g := re (inner ℂ u (cfcHom hT (ofRealCM (g : C(spectrum ℂ T, ℝ))) u))
  map_add' g g' := by
    rw [show ((g + g' : C_c(_, ℝ)) : C(spectrum ℂ T, ℝ)) = g + g' from rfl, map_add,
      map_add, _root_.add_apply, inner_add_right, add_re]
  map_smul' c g := by
    have : ofRealCM ((c • g : C_c(_, ℝ)) : C(spectrum ℂ T, ℝ)) =
        (c : ℂ) • ofRealCM (g : C(spectrum ℂ T, ℝ)) := by
      ext x
      simp
    rw [this, map_smul, _root_.smul_apply, inner_smul_right, re_ofReal_mul, RingHom.id_apply,
      smul_eq_mul]
  monotone' g g' hgg' := by
    set h := g' - g
    have hh : ∀ x, 0 ≤ h x := fun x => sub_nonneg.mpr (hgg' x)
    let s : C(spectrum ℂ T, ℂ) := ⟨fun x => (Real.sqrt (h x) : ℂ), by fun_prop⟩
    have hs : ofRealCM (h : C(spectrum ℂ T, ℝ)) = star s * s := by
      ext x
      change ((h x : ℝ) : ℂ) = star (Real.sqrt (h x) : ℂ) * (Real.sqrt (h x) : ℂ)
      rw [star_def, conj_ofReal, ← ofReal_mul, Real.mul_self_sqrt (hh x)]
    have hg' : ofRealCM (g' : C(spectrum ℂ T, ℝ)) =
        ofRealCM (g : C(spectrum ℂ T, ℝ)) + ofRealCM (h : C(spectrum ℂ T, ℝ)) := by
      rw [← map_add]
      congr 1
      ext x
      simp [h]
    have key : 0 ≤ re (inner ℂ u (cfcHom hT (ofRealCM (h : C(spectrum ℂ T, ℝ))) u)) := by
      rw [hs, map_mul, map_star, ContinuousLinearMap.star_eq_adjoint, mul_apply_eq_comp,
        ContinuousLinearMap.adjoint_inner_right]
      exact inner_self_nonneg (𝕜 := ℂ)
    change re _ ≤ re _
    rw [hg', map_add, _root_.add_apply, inner_add_right, add_re]
    linarith

/-- The **scalar spectral measure** `ν_u` of a normal operator `T` at `u`: the measure on `ℂ`
representing `g ↦ re ⟪u, cfc g T u⟫`. It is concentrated on the spectrum of `T`
(`IsStarNormal.spectralMeasure_compl_spectrum`). -/
private noncomputable def spectralMeasure (hT : IsStarNormal T) (u : E) : Measure ℂ :=
  (RealRMK.rieszMeasure (hT.spectralFunctional u)).map Subtype.val

private instance (hT : IsStarNormal T) (u : E) : IsFiniteMeasure (hT.spectralMeasure u) := by
  unfold spectralMeasure
  infer_instance

private lemma measurableEmbedding_val (T : E →L[ℂ] E) :
    MeasurableEmbedding (Subtype.val : spectrum ℂ T → ℂ) :=
  MeasurableEmbedding.subtype_coe (spectrum.isClosed T).measurableSet

variable (hT : IsStarNormal T) (u : E)

/-- **Spectral integral formula.** For a real function `g` continuous on the spectrum of `T`,
`∫ g dν_u = re ⟪u, cfc g T u⟫`. -/
private lemma integral_spectralMeasure {g : ℂ → ℝ} (hg : ContinuousOn g (spectrum ℂ T)) :
    ∫ ζ, g ζ ∂(hT.spectralMeasure u) = re (inner ℂ u (cfc (fun ζ => (g ζ : ℂ)) T u)) := by
  let g' : C_c(spectrum ℂ T, ℝ) :=
    ⟨⟨fun x => g x, hg.domRestrict⟩, HasCompactSupport.of_compactSpace _⟩
  rw [spectralMeasure, (measurableEmbedding_val _).integral_map]
  refine (RealRMK.integral_rieszMeasure (hT.spectralFunctional u) g').trans ?_
  rw [cfc_apply (fun ζ => (g ζ : ℂ)) T hT (continuous_ofReal.comp_continuousOn hg)]
  rfl

variable {u} in
/-- **Uniqueness.** A finite measure `ν` on `ℂ` with `∫ g dν = re ⟪u, cfc g T u⟫` for every
bounded continuous real `g` is the scalar spectral measure `ν_u`. -/
private lemma eq_spectralMeasure_of_integral (ν : Measure ℂ) [IsFiniteMeasure ν]
    (h : ∀ g : ℂ →ᵇ ℝ, ∫ ζ, g ζ ∂ν = re (inner ℂ u (cfc (fun ζ => (g ζ : ℂ)) T u))) :
    ν = hT.spectralMeasure u :=
  ext_of_forall_integral_eq_of_IsFiniteMeasure fun g =>
    (h g).trans (hT.integral_spectralMeasure u g.continuous.continuousOn).symm

/-- `ν_u` is concentrated on the spectrum of `T`. -/
private lemma spectralMeasure_compl_spectrum : hT.spectralMeasure u (spectrum ℂ T)ᶜ = 0 := by
  rw [spectralMeasure, Measure.map_apply measurable_subtype_coe
    (spectrum.isClosed _).measurableSet.compl]
  convert measure_empty (μ := RealRMK.rieszMeasure (hT.spectralFunctional u))
  ext x
  simp

/-- `ν_u`-almost every point lies in the spectrum of `T`. -/
private lemma ae_mem_spectrum_spectralMeasure : ∀ᵐ ζ ∂(hT.spectralMeasure u), ζ ∈ spectrum ℂ T :=
  ae_iff.mpr (hT.spectralMeasure_compl_spectrum u)

/-- The support of `ν_u` is contained in the spectrum of `T`. -/
private lemma support_spectralMeasure_subset : (hT.spectralMeasure u).support ⊆ spectrum ℂ T :=
  Measure.support_subset_of_isClosed (spectrum.isClosed T) (hT.ae_mem_spectrum_spectralMeasure u)

/-- The total mass of `ν_u` is `‖u‖²`, as a real number. -/
private lemma measureReal_spectralMeasure_univ : (hT.spectralMeasure u).real Set.univ = ‖u‖ ^ 2 := by
  have := hT
  have h := hT.integral_spectralMeasure u (g := fun _ => 1) continuousOn_const
  simp only [integral_const, smul_eq_mul, mul_one, ofReal_one] at h
  rw [h, cfc_const_one ℂ T, one_apply_eq_self]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) u

variable {u} in
/-- `ν_u` has no atom at `ζ₀` when `u` lies in the closure of the range of `T - ζ₀`: then
`(1 + n² |T - ζ₀|²)⁻¹ u → 0`. -/
private lemma spectralMeasure_singleton_eq_zero_of_mem_closure_range {ζ₀ : ℂ}
    (hu : u ∈ closure (Set.range (T - algebraMap ℂ (E →L[ℂ] E) ζ₀))) :
    hT.spectralMeasure u {ζ₀} = 0 := by
  have := hT
  set ν := hT.spectralMeasure u
  let φ : ℕ → ℂ → ℝ := fun n ζ => (1 + (n : ℝ) ^ 2 * ‖ζ - ζ₀‖ ^ 2)⁻¹
  have hpos : ∀ (n : ℕ) (ζ : ℂ), 0 < 1 + (n : ℝ) ^ 2 * ‖ζ - ζ₀‖ ^ 2 := fun n ζ => by positivity
  have hcont : ∀ n, Continuous (φ n) := fun n =>
    Continuous.inv₀ (by fun_prop) fun ζ => (hpos n ζ).ne'
  have hφ1 : ∀ n ζ, φ n ζ ≤ 1 := fun n ζ =>
    inv_le_one_of_one_le₀ (le_add_of_nonneg_right (by positivity))
  have hφ0 : ∀ n ζ, 0 ≤ φ n ζ := fun n ζ => (inv_pos.mpr (hpos n ζ)).le
  -- `ν {ζ₀}` is controlled by `‖(1 + n² |T - ζ₀|²)⁻¹ u‖`.
  have hle : ∀ n, ν.real {ζ₀} ≤ ‖u‖ * ‖cfc (fun ζ => (φ n ζ : ℂ)) T u‖ := fun n => by
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
      _ = re (inner ℂ u (cfc (fun ζ => (φ n ζ : ℂ)) T u)) :=
          hT.integral_spectralMeasure u (hcont n).continuousOn
      _ ≤ ‖inner ℂ u (cfc (fun ζ => (φ n ζ : ℂ)) T u)‖ := re_le_norm _
      _ ≤ ‖u‖ * ‖cfc (fun ζ => (φ n ζ : ℂ)) T u‖ := norm_inner_le_norm _ _
  -- `(1 + n² |T - ζ₀|²)⁻¹ u → 0`, since `u` is approximated by the range of `T - ζ₀`.
  have hsmall : ∀ ε > 0, ∃ n, ‖cfc (fun ζ => (φ n ζ : ℂ)) T u‖ ≤ ε := fun ε hε => by
    obtain ⟨b, hb, hub⟩ := Metric.mem_closure_iff.mp hu (ε / 2) (by positivity)
    obtain ⟨v, rfl⟩ := hb
    have hub' : dist u ((T - algebraMap ℂ (E →L[ℂ] E) ζ₀) v) < ε / 2 := hub
    obtain ⟨n, hn⟩ := exists_nat_gt (2 * ‖v‖ / ε)
    have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn
    refine ⟨n, ?_⟩
    have h₁ : ‖cfc (fun ζ => (φ n ζ : ℂ)) T‖ ≤ 1 := norm_cfc_le zero_le_one fun ζ _ => by
      rw [norm_real, Real.norm_of_nonneg (hφ0 n ζ)]
      exact hφ1 n ζ
    have h₂ : ‖cfc (fun ζ => (φ n ζ : ℂ) * (ζ - ζ₀)) T‖ ≤ (n : ℝ)⁻¹ :=
      norm_cfc_le (by positivity) fun ζ _ => by
        rw [norm_mul, norm_real, Real.norm_of_nonneg (hφ0 n ζ), inv_mul_eq_div,
          div_le_iff₀ (hpos n ζ), inv_mul_eq_div, le_div_iff₀' hn0]
        nlinarith [sq_nonneg ((n : ℝ) * ‖ζ - ζ₀‖ - 1), norm_nonneg (ζ - ζ₀)]
    have hsplit : cfc (fun ζ => (φ n ζ : ℂ)) T u =
        cfc (fun ζ => (φ n ζ : ℂ)) T (u - (T - algebraMap ℂ (E →L[ℂ] E) ζ₀) v) +
          cfc (fun ζ => (φ n ζ : ℂ) * (ζ - ζ₀)) T v := by
      have hc : ContinuousOn (fun ζ => (φ n ζ : ℂ)) (spectrum ℂ T) :=
        (continuous_ofReal.comp (hcont n)).continuousOn
      rw [cfc_mul (fun ζ => (φ n ζ : ℂ)) (fun ζ => ζ - ζ₀) T hc,
        cfc_sub (fun ζ : ℂ => ζ) (fun _ => ζ₀) T, cfc_id' ℂ T, cfc_const ζ₀ T,
        mul_apply_eq_comp, ContinuousLinearMap.map_sub, sub_add_cancel]
    rw [hsplit]
    calc _ ≤ ‖cfc (fun ζ => (φ n ζ : ℂ)) T (u - (T - algebraMap ℂ (E →L[ℂ] E) ζ₀) v)‖ +
          ‖cfc (fun ζ => (φ n ζ : ℂ) * (ζ - ζ₀)) T v‖ := norm_add_le _ _
      _ ≤ 1 * ‖u - (T - algebraMap ℂ (E →L[ℂ] E) ζ₀) v‖ + (n : ℝ)⁻¹ * ‖v‖ := by
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
    calc ν.real {ζ₀} ≤ ‖u‖ * ‖cfc (fun ζ => (φ n ζ : ℂ)) T u‖ := hle n
      _ ≤ (‖u‖ + 1) * (δ / (‖u‖ + 1)) := by gcongr; linarith
      _ = 0 + δ := by field_simp; ring
  rw [← measureReal_eq_zero_iff]
  exact le_antisymm h0 measureReal_nonneg

/-- A function continuous on the spectrum of `T` is `ν_u`-integrable. -/
private lemma integrable_spectralMeasure {g : ℂ → ℂ} (hg : ContinuousOn g (spectrum ℂ T)) :
    Integrable g (hT.spectralMeasure u) := by
  have := hg.integrableOn_compact (spectrum.isCompact _) (μ := hT.spectralMeasure u)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem
    (hT.ae_mem_spectrum_spectralMeasure u)] at this

/-- **Spectral integral formula**, complex form. For `g` continuous on the spectrum of `T`,
`⟪u, cfc g T u⟫ = ∫ g dν_u`. -/
private lemma inner_cfc_eq_integral_spectralMeasure {g : ℂ → ℂ} (hg : ContinuousOn g (spectrum ℂ T)) :
    inner ℂ u (cfc g T u) = ∫ ζ, g ζ ∂(hT.spectralMeasure u) := by
  have := hT
  have hreal : ∀ h : ℂ → ℝ, ContinuousOn h (spectrum ℂ T) →
      inner ℂ u (cfc (fun ζ => (h ζ : ℂ)) T u) =
        ((∫ ζ, h ζ ∂(hT.spectralMeasure u) : ℝ) : ℂ) := fun h hh => by
    rw [hT.integral_spectralMeasure u hh]
    have hsa : ContinuousLinearMap.adjoint (cfc (fun ζ => (h ζ : ℂ)) T) =
        cfc (fun ζ => (h ζ : ℂ)) T := by
      rw [← ContinuousLinearMap.star_eq_adjoint, ← cfc_star]
      exact cfc_congr fun ζ _ => by simp
    have hc : conj (inner ℂ u (cfc (fun ζ => (h ζ : ℂ)) T u)) =
        inner ℂ u (cfc (fun ζ => (h ζ : ℂ)) T u) := by
      rw [inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_right, hsa]
    refine Complex.ext (ofReal_re _).symm ?_
    rw [ofReal_im]
    exact conj_eq_iff_im.mp hc
  have hsplit : cfc g T = cfc (fun ζ => ((g ζ).re : ℂ)) T + I • cfc (fun ζ => ((g ζ).im : ℂ)) T := by
    have hre : ContinuousOn (fun ζ => ((g ζ).re : ℂ)) (spectrum ℂ T) :=
      continuous_ofReal.comp_continuousOn (continuous_re.comp_continuousOn hg)
    have him : ContinuousOn (fun ζ => ((g ζ).im : ℂ)) (spectrum ℂ T) :=
      continuous_ofReal.comp_continuousOn (continuous_im.comp_continuousOn hg)
    rw [← cfc_const_mul I _ _ him, ← cfc_add T (fun ζ => ((g ζ).re : ℂ))
      (fun ζ => I * ((g ζ).im : ℂ)) hre (continuousOn_const.mul him)]
    exact cfc_congr fun ζ _ => by rw [mul_comm, re_add_im]
  rw [hsplit, _root_.add_apply, _root_.smul_apply, inner_add_right, inner_smul_right,
    hreal (fun ζ => (g ζ).re) (continuous_re.comp_continuousOn hg),
    hreal (fun ζ => (g ζ).im) (continuous_im.comp_continuousOn hg)]
  have := integral_re_add_im (hT.integrable_spectralMeasure u hg)
  simp only [RCLike.re_to_complex, RCLike.im_to_complex, RCLike.I_to_complex] at this
  rw [mul_comm]
  exact this

/-! ### Transformation rules -/

/-- **Transformation rule.** For `h` continuous on the spectrum of `T`,
`∫ g dν_{h(T) u} = ∫ |h|² g dν_u`. -/
private lemma integral_spectralMeasure_cfc_apply {h : ℂ → ℂ} (hh : ContinuousOn h (spectrum ℂ T))
    {g : ℂ → ℝ} (hg : ContinuousOn g (spectrum ℂ T)) :
    ∫ ζ, g ζ ∂(hT.spectralMeasure (cfc h T u)) =
      ∫ ζ, ‖h ζ‖ ^ 2 * g ζ ∂(hT.spectralMeasure u) := by
  have := hT
  have hg' : ContinuousOn (fun ζ => (g ζ : ℂ)) (spectrum ℂ T) :=
    continuous_ofReal.comp_continuousOn hg
  have e : cfc (fun ζ => ((‖h ζ‖ ^ 2 * g ζ : ℝ) : ℂ)) T =
      star (cfc h T) * (cfc (fun ζ => (g ζ : ℂ)) T * cfc h T) := by
    rw [← cfc_star, ← cfc_mul _ _ _ hg' hh,
      ← cfc_mul (fun x => star (h x)) (fun x => (g x : ℂ) * h x) _ hh.star (hg'.mul hh)]
    refine cfc_congr fun ζ _ => ?_
    simp only [star_def]
    rw [mul_left_comm, conj_mul']
    push_cast
    ring
  rw [hT.integral_spectralMeasure _ hg,
    hT.integral_spectralMeasure u (g := fun ζ => ‖h ζ‖ ^ 2 * g ζ) ((hh.norm.pow 2).mul hg), e,
    mul_apply_eq_comp, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

/-- **Transformation rule**, measure form. For `h` continuous on the spectrum of `T`,
`ν_{h(T) u} = |h|² ν_u`. -/
private lemma spectralMeasure_cfc_apply {h : ℂ → ℂ} (hh : ContinuousOn h (spectrum ℂ T)) :
    hT.spectralMeasure (cfc h T u) = (hT.spectralMeasure u).withDensity fun ζ => ‖h ζ‖ₑ ^ 2 := by
  classical
  set σ := spectrum ℂ T
  set ν := hT.spectralMeasure u
  -- A measurable density agreeing with `‖h‖²` on the spectrum, where `ν` lives.
  let ρ : ℂ → ℝ≥0 := σ.piecewise (fun ζ => ‖h ζ‖₊ ^ 2) 0
  have hρ : Measurable ρ := (hh.nnnorm.pow 2).measurable_piecewise continuousOn_const
    (spectrum.isClosed _).measurableSet
  have hρσ : ∀ ζ ∈ σ, ρ ζ = ‖h ζ‖₊ ^ 2 := fun ζ hζ => Set.piecewise_eq_of_mem _ _ _ hζ
  have hae : (fun ζ => ‖h ζ‖ₑ ^ 2) =ᵐ[ν] fun ζ => (ρ ζ : ℝ≥0∞) := by
    filter_upwards [hT.ae_mem_spectrum_spectralMeasure u] with ζ hζ
    rw [hρσ ζ hζ, enorm_eq_nnnorm, ENNReal.coe_pow]
  rw [withDensity_congr_ae hae]
  obtain ⟨C, hC⟩ := (spectrum.isCompact T).exists_bound_of_continuousOn hh
  have hρC : ∀ ζ, ρ ζ ≤ (C ^ 2).toNNReal := fun ζ => by
    by_cases hζ : ζ ∈ σ
    · rw [hρσ ζ hζ, Real.le_toNNReal_iff_coe_le (sq_nonneg C), NNReal.coe_pow, coe_nnnorm]
      exact pow_le_pow_left₀ (norm_nonneg _) (hC ζ hζ) 2
    · rw [show ρ ζ = 0 from Set.piecewise_eq_of_notMem _ _ _ hζ]
      exact zero_le
  have : IsFiniteMeasure (ν.withDensity fun ζ => (ρ ζ : ℝ≥0∞)) := by
    refine isFiniteMeasure_withDensity (ne_top_of_le_ne_top ?_
      (lintegral_mono fun ζ => ENNReal.coe_le_coe.mpr (hρC ζ)))
    rw [lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _)
  refine (hT.eq_spectralMeasure_of_integral _ fun g => ?_).symm
  rw [integral_withDensity_eq_integral_smul hρ,
    ← hT.integral_spectralMeasure _ g.continuous.continuousOn,
    hT.integral_spectralMeasure_cfc_apply u hh g.continuous.continuousOn]
  refine integral_congr_ae ?_
  filter_upwards [hT.ae_mem_spectrum_spectralMeasure u] with ζ hζ
  rw [hρσ ζ hζ, NNReal.smul_def, smul_eq_mul, NNReal.coe_pow, coe_nnnorm]

/-- **Spectral mapping.** For `φ` continuous on the spectrum of `T` (and measurable on `ℂ`), the
scalar spectral measure of the normal operator `cfc φ T` at `u` is the image of `ν_u` under `φ`. -/
private lemma spectralMeasure_cfc_eq_map {φ : ℂ → ℂ} (hφ : ContinuousOn φ (spectrum ℂ T))
    (hφm : Measurable φ) (hφT : IsStarNormal (cfc φ T)) :
    hφT.spectralMeasure u = (hT.spectralMeasure u).map φ := by
  have := hT
  refine (hφT.eq_spectralMeasure_of_integral _ fun g => ?_).symm
  rw [integral_map hφm.aemeasurable g.continuous.aestronglyMeasurable,
    hT.integral_spectralMeasure u (g := fun ζ => g (φ ζ)) (g.continuous.comp_continuousOn hφ),
    ← cfc_comp' (fun ζ => (g ζ : ℂ)) _ _ (continuous_ofReal.comp g.continuous).continuousOn hφ]

end ScalarSpectralMeasure

/-! ### Polarization identities -/

section Polarization

variable {G : E →L[ℂ] E} (hG : ∀ u v, ⟪u, G v⟫_ℂ = ⟪G u, v⟫_ℂ) (x y : E)
include hG

private lemma inner_apply_swap : ⟪y, G x⟫_ℂ = conj ⟪x, G y⟫_ℂ := by
  rw [hG, inner_conj_symm]

private lemma re_polarization :
    4⁻¹ * (re ⟪x + y, G (x + y)⟫_ℂ - re ⟪x - y, G (x - y)⟫_ℂ) = re ⟪x, G y⟫_ℂ := by
  simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    inner_apply_swap hG x y, add_re, sub_re, conj_re]
  ring

private lemma im_polarization :
    4⁻¹ * (re ⟪x - I • y, G (x - I • y)⟫_ℂ - re ⟪x + I • y, G (x + I • y)⟫_ℂ) =
      im ⟪x, G y⟫_ℂ := by
  simp only [map_add, map_sub, map_smul, inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right, inner_smul_left, inner_smul_right, inner_apply_swap hG x y, add_re, sub_re,
    mul_re, mul_im, add_im, sub_im, conj_re, conj_im, I_re, I_im]
  ring

end Polarization

variable [CompleteSpace E] {T : E →L[ℂ] E} (hT : IsStarNormal T)

include hT in
/-- `cfc g T` for a real function `g` is self-adjoint. -/
private lemma inner_cfc_real_comm (g : ℂ → ℝ) (u v : E) :
    ⟪u, cfc (fun ζ => (g ζ : ℂ)) T v⟫_ℂ = ⟪cfc (fun ζ => (g ζ : ℂ)) T u, v⟫_ℂ := by
  have := hT
  have hsa : ContinuousLinearMap.adjoint (cfc (fun ζ => (g ζ : ℂ)) T) =
      cfc (fun ζ => (g ζ : ℂ)) T := by
    rw [← ContinuousLinearMap.star_eq_adjoint, ← cfc_star]
    exact cfc_congr fun ζ _ => by simp
  rw [← ContinuousLinearMap.adjoint_inner_left, hsa]

/-! ### The complex spectral measure -/

/-- The **complex spectral measure** `ν_{x,y} = ¼ (ν_{x+y} - ν_{x-y} - i ν_{x+iy} + i ν_{x-iy})`
of a normal operator `T`, the polarization of the scalar spectral measures `ν_u`. It is
conjugate-linear in `x` and linear in `y`, and for real bounded continuous `g` its real and
imaginary parts integrate `g` to the real and imaginary parts of `⟪x, cfc g T y⟫`. -/
private noncomputable def complexSpectralMeasure (x y : E) : ComplexMeasure ℂ :=
  SignedMeasure.toComplexMeasure
    ((4⁻¹ : ℝ) • ((hT.spectralMeasure (x + y)).toSignedMeasure -
      (hT.spectralMeasure (x - y)).toSignedMeasure))
    ((4⁻¹ : ℝ) • ((hT.spectralMeasure (x - I • y)).toSignedMeasure -
      (hT.spectralMeasure (x + I • y)).toSignedMeasure))

variable (x y : E)

/-- **Spectral integral formula**, real part: `∫ g d(re ν_{x,y}) = re ⟪x, cfc g T y⟫` for a
bounded continuous real `g`. -/
private lemma integral_re_complexSpectralMeasure (g : ℂ →ᵇ ℝ) :
    ∫ᵛ ζ, g ζ ∂<•(hT.complexSpectralMeasure x y).re =
      re ⟪x, cfc (fun ζ => (g ζ : ℂ)) T y⟫_ℂ := by
  rw [complexSpectralMeasure, SignedMeasure.re_toComplexMeasure,
    VectorMeasure.integral_smul_vectorMeasure,
    VectorMeasure.integral_sub_vectorMeasure
      (SignedMeasure.integrable_toSignedMeasure_iff.mpr (g.integrable _))
      (SignedMeasure.integrable_toSignedMeasure_iff.mpr (g.integrable _)),
    VectorMeasure.integral_toSignedMeasure, VectorMeasure.integral_toSignedMeasure,
    hT.integral_spectralMeasure _ g.continuous.continuousOn,
    hT.integral_spectralMeasure _ g.continuous.continuousOn, smul_eq_mul]
  exact re_polarization (inner_cfc_real_comm hT g) x y

/-- **Spectral integral formula**, imaginary part: `∫ g d(im ν_{x,y}) = im ⟪x, cfc g T y⟫` for a
bounded continuous real `g`. -/
private lemma integral_im_complexSpectralMeasure (g : ℂ →ᵇ ℝ) :
    ∫ᵛ ζ, g ζ ∂<•(hT.complexSpectralMeasure x y).im =
      im ⟪x, cfc (fun ζ => (g ζ : ℂ)) T y⟫_ℂ := by
  rw [complexSpectralMeasure, SignedMeasure.im_toComplexMeasure,
    VectorMeasure.integral_smul_vectorMeasure,
    VectorMeasure.integral_sub_vectorMeasure
      (SignedMeasure.integrable_toSignedMeasure_iff.mpr (g.integrable _))
      (SignedMeasure.integrable_toSignedMeasure_iff.mpr (g.integrable _)),
    VectorMeasure.integral_toSignedMeasure, VectorMeasure.integral_toSignedMeasure,
    hT.integral_spectralMeasure _ g.continuous.continuousOn,
    hT.integral_spectralMeasure _ g.continuous.continuousOn, smul_eq_mul]
  exact im_polarization (inner_cfc_real_comm hT g) x y

variable {x y} in
/-- **Uniqueness.** A complex measure `ν` on `ℂ` whose real and imaginary parts integrate every
bounded continuous real `g` to `re ⟪x, cfc g T y⟫` and `im ⟪x, cfc g T y⟫` is `ν_{x,y}`. -/
private lemma eq_complexSpectralMeasure_of_integral (ν : ComplexMeasure ℂ)
    (hre : ∀ g : ℂ →ᵇ ℝ, ∫ᵛ ζ, g ζ ∂<•ν.re = re ⟪x, cfc (fun ζ => (g ζ : ℂ)) T y⟫_ℂ)
    (him : ∀ g : ℂ →ᵇ ℝ, ∫ᵛ ζ, g ζ ∂<•ν.im = im ⟪x, cfc (fun ζ => (g ζ : ℂ)) T y⟫_ℂ) :
    ν = hT.complexSpectralMeasure x y :=
  ComplexMeasure.ext_of_forall_integral_eq
    (fun g => (hre g).trans (hT.integral_re_complexSpectralMeasure x y g).symm)
    (fun g => (him g).trans (hT.integral_im_complexSpectralMeasure x y g).symm)

/-- The value of `ν_{x,y}` on a measurable set, by polarization. -/
private lemma complexSpectralMeasure_apply {s : Set ℂ} (hs : MeasurableSet s) :
    hT.complexSpectralMeasure x y s =
      ⟨4⁻¹ * ((hT.spectralMeasure (x + y)).real s - (hT.spectralMeasure (x - y)).real s),
        4⁻¹ * ((hT.spectralMeasure (x - I • y)).real s -
          (hT.spectralMeasure (x + I • y)).real s)⟩ := by
  rw [complexSpectralMeasure, SignedMeasure.toComplexMeasure_apply]
  simp only [_root_.smul_apply, _root_.sub_apply,
    Measure.toSignedMeasure_apply_measurable hs, smul_eq_mul]

/-- **Spectral integral formula**, complex form: for `g` continuous on the spectrum of `T`,
`⟪x, cfc g T y⟫ = ∫ g d(re ν_{x,y}) + i ∫ g d(im ν_{x,y})`, the integral of `g` against the complex
measure `ν_{x,y}`. -/
private lemma inner_cfc_eq_integral_complexSpectralMeasure {g : ℂ → ℂ}
    (hg : ContinuousOn g (spectrum ℂ T)) :
    ⟪x, cfc g T y⟫_ℂ = ∫ᵛ ζ, g ζ ∂<•(hT.complexSpectralMeasure x y).re +
      I * ∫ᵛ ζ, g ζ ∂<•(hT.complexSpectralMeasure x y).im := by
  have hi : ∀ u : E, VectorMeasure.Integrable (hT.spectralMeasure u).toSignedMeasure g := fun u =>
    SignedMeasure.integrable_toSignedMeasure_iff.mpr (hT.integrable_spectralMeasure u hg)
  rw [complexSpectralMeasure, SignedMeasure.re_toComplexMeasure, SignedMeasure.im_toComplexMeasure,
    VectorMeasure.integral_smul_vectorMeasure, VectorMeasure.integral_smul_vectorMeasure,
    VectorMeasure.integral_sub_vectorMeasure (hi _) (hi _),
    VectorMeasure.integral_sub_vectorMeasure (hi _) (hi _), VectorMeasure.integral_toSignedMeasure,
    VectorMeasure.integral_toSignedMeasure, VectorMeasure.integral_toSignedMeasure,
    VectorMeasure.integral_toSignedMeasure, ← hT.inner_cfc_eq_integral_spectralMeasure _ hg,
    ← hT.inner_cfc_eq_integral_spectralMeasure _ hg, ← hT.inner_cfc_eq_integral_spectralMeasure _ hg,
    ← hT.inner_cfc_eq_integral_spectralMeasure _ hg]
  exact ContinuousLinearMap.inner_apply_eq_polarization x y

/-- **The operator as an integral**: `⟪x, T y⟫ = ∫ ζ d(re ν_{x,y}) + i ∫ ζ d(im ν_{x,y})`, i.e.
`T = ∫ ζ dE_T(ζ)` weakly. -/
private lemma inner_apply_eq_integral_complexSpectralMeasure :
    ⟪x, T y⟫_ℂ = ∫ᵛ ζ, ζ ∂<•(hT.complexSpectralMeasure x y).re +
      I * ∫ᵛ ζ, ζ ∂<•(hT.complexSpectralMeasure x y).im := by
  have := hT
  rw [← hT.inner_cfc_eq_integral_complexSpectralMeasure x y (g := fun ζ => ζ) (continuousOn_id' _),
    cfc_id' ℂ T]

/-! ### Sesquilinearity -/

private lemma integrable (s : SignedMeasure ℂ) (g : ℂ →ᵇ ℝ) : VectorMeasure.Integrable s g :=
  SignedMeasure.integrable_boundedContinuousFunction s g

variable (z : E)

/-- `ν_{x,y}` is additive in `y`. -/
private lemma complexSpectralMeasure_add_right :
    hT.complexSpectralMeasure x (y + z) =
      hT.complexSpectralMeasure x y + hT.complexSpectralMeasure x z := by
  have := hT
  refine (hT.eq_complexSpectralMeasure_of_integral _ (fun g => ?_) (fun g => ?_)).symm
  · rw [map_add, VectorMeasure.integral_add_vectorMeasure (integrable _ g) (integrable _ g),
      integral_re_complexSpectralMeasure, integral_re_complexSpectralMeasure, map_add,
      inner_add_right, add_re]
  · rw [map_add, VectorMeasure.integral_add_vectorMeasure (integrable _ g) (integrable _ g),
      integral_im_complexSpectralMeasure, integral_im_complexSpectralMeasure, map_add,
      inner_add_right, add_im]

/-- `ν_{x,y}` is complex-linear in `y`. -/
private lemma complexSpectralMeasure_smul_right (c : ℂ) :
    hT.complexSpectralMeasure x (c • y) = c • hT.complexSpectralMeasure x y := by
  have := hT
  refine (hT.eq_complexSpectralMeasure_of_integral _ (fun g => ?_) (fun g => ?_)).symm
  · rw [ComplexMeasure.re_smul, VectorMeasure.integral_sub_vectorMeasure
      ((integrable _ g).smul_vectorMeasure _) ((integrable _ g).smul_vectorMeasure _),
      VectorMeasure.integral_smul_vectorMeasure, VectorMeasure.integral_smul_vectorMeasure,
      integral_re_complexSpectralMeasure, integral_im_complexSpectralMeasure,
      ContinuousLinearMap.map_smul, inner_smul_right, mul_re, smul_eq_mul, smul_eq_mul]
  · rw [ComplexMeasure.im_smul, VectorMeasure.integral_add_vectorMeasure
      ((integrable _ g).smul_vectorMeasure _) ((integrable _ g).smul_vectorMeasure _),
      VectorMeasure.integral_smul_vectorMeasure, VectorMeasure.integral_smul_vectorMeasure,
      integral_re_complexSpectralMeasure, integral_im_complexSpectralMeasure,
      ContinuousLinearMap.map_smul, inner_smul_right, mul_im, smul_eq_mul, smul_eq_mul]

/-- **Conjugate symmetry**, as measures: `ν_{y,x}` has the real part of `ν_{x,y}` and the opposite
imaginary part. -/
private lemma complexSpectralMeasure_swap :
    hT.complexSpectralMeasure y x = SignedMeasure.toComplexMeasure
      (hT.complexSpectralMeasure x y).re (-(hT.complexSpectralMeasure x y).im) := by
  refine (hT.eq_complexSpectralMeasure_of_integral _ (fun g => ?_) (fun g => ?_)).symm
  · rw [SignedMeasure.re_toComplexMeasure, integral_re_complexSpectralMeasure,
      inner_apply_swap (inner_cfc_real_comm hT g) y x, conj_re]
  · rw [SignedMeasure.im_toComplexMeasure, VectorMeasure.integral_neg_vectorMeasure,
      integral_im_complexSpectralMeasure, inner_apply_swap (inner_cfc_real_comm hT g) y x, conj_im,
      neg_neg]

/-- **Conjugate symmetry**: `ν_{y,x}(s) = conj ν_{x,y}(s)`. -/
private lemma complexSpectralMeasure_apply_swap (s : Set ℂ) :
    hT.complexSpectralMeasure y x s = conj (hT.complexSpectralMeasure x y s) := by
  rw [complexSpectralMeasure_swap, SignedMeasure.toComplexMeasure_apply]
  refine Complex.ext ?_ ?_
  · simp [ComplexMeasure.re, VectorMeasure.mapRangeL, VectorMeasure.mapRange_apply]
  · simp [ComplexMeasure.im, VectorMeasure.mapRangeL, VectorMeasure.mapRange_apply]

/-- `ν_{x,y}` is additive in `x`. -/
private lemma complexSpectralMeasure_add_left :
    hT.complexSpectralMeasure (x + z) y =
      hT.complexSpectralMeasure x y + hT.complexSpectralMeasure z y := by
  ext s hs
  rw [_root_.add_apply, hT.complexSpectralMeasure_apply_swap y (x + z) s,
    complexSpectralMeasure_add_right, _root_.add_apply, map_add,
    ← hT.complexSpectralMeasure_apply_swap, ← hT.complexSpectralMeasure_apply_swap]

/-- `ν_{x,y}` is conjugate-linear in `x`. -/
private lemma complexSpectralMeasure_smul_left (c : ℂ) :
    hT.complexSpectralMeasure (c • x) y = conj c • hT.complexSpectralMeasure x y := by
  ext s hs
  rw [_root_.smul_apply, hT.complexSpectralMeasure_apply_swap y (c • x) s,
    complexSpectralMeasure_smul_right, _root_.smul_apply, smul_eq_mul, smul_eq_mul, map_mul,
    ← hT.complexSpectralMeasure_apply_swap]

/-- On the diagonal, `ν_{x,x}` is the scalar spectral measure `ν_x`. -/
private lemma complexSpectralMeasure_self :
    hT.complexSpectralMeasure x x =
      SignedMeasure.toComplexMeasure (hT.spectralMeasure x).toSignedMeasure 0 := by
  refine (hT.eq_complexSpectralMeasure_of_integral _ (fun g => ?_) (fun g => ?_)).symm
  · rw [SignedMeasure.re_toComplexMeasure, VectorMeasure.integral_toSignedMeasure,
      hT.integral_spectralMeasure _ g.continuous.continuousOn]
  · rw [SignedMeasure.im_toComplexMeasure, VectorMeasure.integral_zero_vectorMeasure]
    have h := inner_apply_swap (inner_cfc_real_comm hT g) x x
    exact ((conj_eq_iff_im.mp h.symm)).symm

/-- On the diagonal, `ν_{x,x}(s) = ν_x(s)` for a measurable `s`. -/
private lemma complexSpectralMeasure_self_apply {s : Set ℂ} (hs : MeasurableSet s) :
    hT.complexSpectralMeasure x x s = ((hT.spectralMeasure x).real s : ℂ) := by
  rw [complexSpectralMeasure_self, SignedMeasure.toComplexMeasure_apply,
    Measure.toSignedMeasure_apply_measurable hs]
  rfl

/-- `ν_{0,y} = 0`. -/
private lemma complexSpectralMeasure_zero_left : hT.complexSpectralMeasure 0 y = 0 := by
  ext s hs
  simpa using congrArg (fun μ : ComplexMeasure ℂ => μ s) (hT.complexSpectralMeasure_smul_left 0 y 0)

/-- `ν_{x,0} = 0`. -/
private lemma complexSpectralMeasure_zero_right : hT.complexSpectralMeasure x 0 = 0 := by
  ext s hs
  simpa using congrArg (fun μ : ComplexMeasure ℂ => μ s) (hT.complexSpectralMeasure_smul_right x 0 0)

/-! ### Boundedness -/

/-- A crude bound, `‖ν_{x,y}(s)‖ ≤ ‖x‖² + ‖y‖²`, from the polarization formula and the
parallelogram law. -/
private lemma norm_complexSpectralMeasure_apply_le_sq (s : Set ℂ) :
    ‖hT.complexSpectralMeasure x y s‖ ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  by_cases hs : MeasurableSet s
  swap
  · rw [VectorMeasure.not_measurable _ hs, norm_zero]
    positivity
  have hbd : ∀ u, 0 ≤ (hT.spectralMeasure u).real s ∧ (hT.spectralMeasure u).real s ≤ ‖u‖ ^ 2 :=
    fun u => ⟨measureReal_nonneg, (measureReal_mono (Set.subset_univ s)).trans_eq
      (hT.measureReal_spectralMeasure_univ u)⟩
  have p₁ := parallelogram_law_with_norm ℂ x y
  have p₂ := parallelogram_law_with_norm ℂ x (I • y)
  rw [norm_smul, norm_I, one_mul] at p₂
  have h₁ := hbd (x + y)
  have h₂ := hbd (x - y)
  have h₃ := hbd (x - I • y)
  have h₄ := hbd (x + I • y)
  rw [complexSpectralMeasure_apply _ _ _ hs]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have e₁ : |4⁻¹ * ((hT.spectralMeasure (x + y)).real s - (hT.spectralMeasure (x - y)).real s)| ≤
      4⁻¹ * (‖x + y‖ ^ 2 + ‖x - y‖ ^ 2) := by
    rw [abs_le]
    constructor <;> nlinarith [h₁.1, h₁.2, h₂.1, h₂.2]
  have e₂ : |4⁻¹ * ((hT.spectralMeasure (x - I • y)).real s -
      (hT.spectralMeasure (x + I • y)).real s)| ≤ 4⁻¹ * (‖x + I • y‖ ^ 2 + ‖x - I • y‖ ^ 2) := by
    rw [abs_le]
    constructor <;> nlinarith [h₃.1, h₃.2, h₄.1, h₄.2]
  simp only at e₁ e₂ ⊢
  nlinarith [e₁, e₂, p₁, p₂]

/-- **Boundedness**: `‖ν_{x,y}(s)‖ ≤ 2 ‖x‖ ‖y‖`, by rescaling `(x, y)` to `(t x, t⁻¹ y)`, which
leaves `ν_{x,y}` unchanged, in the crude bound. -/
private lemma norm_complexSpectralMeasure_apply_le (s : Set ℂ) :
    ‖hT.complexSpectralMeasure x y s‖ ≤ 2 * ‖x‖ * ‖y‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [complexSpectralMeasure_zero_left]
  rcases eq_or_ne y 0 with rfl | hy
  · simp [complexSpectralMeasure_zero_right]
  have hx' : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hy' : 0 < ‖y‖ := norm_pos_iff.mpr hy
  set t := Real.sqrt (‖y‖ / ‖x‖)
  have ht : 0 < t := Real.sqrt_pos.mpr (div_pos hy' hx')
  have ht2 : t ^ 2 = ‖y‖ / ‖x‖ := Real.sq_sqrt (div_pos hy' hx').le
  have key : hT.complexSpectralMeasure ((t : ℂ) • x) ((t⁻¹ : ℝ) • y) =
      hT.complexSpectralMeasure x y := by
    rw [hT.complexSpectralMeasure_smul_left, ← Complex.coe_smul,
      hT.complexSpectralMeasure_smul_right, smul_smul, conj_ofReal, ← ofReal_mul,
      mul_inv_cancel₀ ht.ne', ofReal_one, one_smul]
  have h := hT.norm_complexSpectralMeasure_apply_le_sq ((t : ℂ) • x) ((t⁻¹ : ℝ) • y) s
  rw [key, norm_smul, norm_smul, norm_real, Real.norm_of_nonneg ht.le,
    Real.norm_of_nonneg (inv_pos.mpr ht).le, mul_pow, mul_pow, inv_pow, ht2] at h
  calc _ ≤ ‖y‖ / ‖x‖ * ‖x‖ ^ 2 + (‖y‖ / ‖x‖)⁻¹ * ‖y‖ ^ 2 := h
    _ = 2 * ‖x‖ * ‖y‖ := by
      field_simp
      ring

/-! ### The operators `E_T(s)` -/

/-- The bounded sesquilinear form `(x, y) ↦ ν_{x,y}(s)`, conjugate-linear in `x`. -/
private noncomputable def spectralForm (s : Set ℂ) : E →L⋆[ℂ] E →L[ℂ] ℂ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => hT.complexSpectralMeasure x y s)
      (fun x x' y => by rw [complexSpectralMeasure_add_left]; rfl)
      (fun c x y => by rw [complexSpectralMeasure_smul_left]; rfl)
      (fun x y y' => by rw [complexSpectralMeasure_add_right]; rfl)
      (fun c x y => by rw [complexSpectralMeasure_smul_right]; rfl))
    2 fun x y => hT.norm_complexSpectralMeasure_apply_le x y s

/-- The form `spectralForm s` evaluates to `ν_{x,y}(s)`. -/
private lemma spectralForm_apply (s : Set ℂ) (x y : E) :
    hT.spectralForm s x y = hT.complexSpectralMeasure x y s := rfl

/-- The operator `E_T(s)` represented by the form `(x, y) ↦ ν_{x,y}(s)`; it is the value on `s` of
the projection-valued measure of `T` (`IsStarNormal.pvm`). -/
private noncomputable def spectralOp (s : Set ℂ) : E →L[ℂ] E :=
  InnerProductSpace.continuousLinearMapOfBilin (hT.spectralForm s)

/-- `⟪E_T(s) x, y⟫ = ν_{x,y}(s)`. -/
private lemma inner_spectralOp_left (s : Set ℂ) (x y : E) :
    ⟪hT.spectralOp s x, y⟫_ℂ = hT.complexSpectralMeasure x y s :=
  InnerProductSpace.continuousLinearMapOfBilin_apply _ x y

/-- `⟪x, E_T(s) y⟫ = ν_{x,y}(s)`. -/
private lemma inner_spectralOp (s : Set ℂ) (x y : E) :
    ⟪x, hT.spectralOp s y⟫_ℂ = hT.complexSpectralMeasure x y s := by
  rw [← inner_conj_symm, inner_spectralOp_left, hT.complexSpectralMeasure_apply_swap x y,
    Complex.conj_conj]

omit [CompleteSpace E] in
/-- Operators with the same matrix coefficients `⟪x, A y⟫` are equal. -/
private lemma spectralOp_ext {A B : E →L[ℂ] E} (h : ∀ x y, ⟪x, A y⟫_ℂ = ⟪x, B y⟫_ℂ) : A = B :=
  ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => h x y

/-- `E_T(s) = 0` off the measurable sets. -/
private lemma spectralOp_of_not_measurableSet {s : Set ℂ} (hs : ¬MeasurableSet s) : hT.spectralOp s = 0 :=
  spectralOp_ext fun x y => by
    rw [inner_spectralOp, VectorMeasure.not_measurable _ hs, zero_apply, inner_zero_right]

/-- `E_T(s)` is self-adjoint. -/
private lemma isSelfAdjoint_spectralOp (s : Set ℂ) : IsSelfAdjoint (hT.spectralOp s) := by
  rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint, eq_comm,
    ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [inner_spectralOp_left, inner_spectralOp]

/-- `E_T(s)` commutes with every operator `H` commuting with the real continuous functions of `T`:
the complex measures `ν_{x, H y}` and `ν_{H† x, y}` integrate every such function to the same
value, hence agree. -/
private lemma spectralOp_mul_of_commute_cfc (s : Set ℂ) {H : E →L[ℂ] E}
    (hH : ∀ g : ℂ →ᵇ ℝ, Commute H (cfc (fun ζ => (g ζ : ℂ)) T)) :
    hT.spectralOp s * H = H * hT.spectralOp s := by
  have key : ∀ x y, hT.complexSpectralMeasure x (H y) =
      hT.complexSpectralMeasure (ContinuousLinearMap.adjoint H x) y := fun x y => by
    have hc : ∀ g : ℂ →ᵇ ℝ, ⟪ContinuousLinearMap.adjoint H x, cfc (fun ζ => (g ζ : ℂ)) T y⟫_ℂ =
        ⟪x, cfc (fun ζ => (g ζ : ℂ)) T (H y)⟫_ℂ := fun g => by
      rw [ContinuousLinearMap.adjoint_inner_left, ← mul_apply_eq_comp, (hH g).eq,
        mul_apply_eq_comp]
    refine (hT.eq_complexSpectralMeasure_of_integral _ (fun g => ?_) (fun g => ?_)).symm
    · rw [integral_re_complexSpectralMeasure, hc]
    · rw [integral_im_complexSpectralMeasure, hc]
  refine spectralOp_ext fun x y => ?_
  rw [mul_apply_eq_comp, mul_apply_eq_comp, inner_spectralOp, ← ContinuousLinearMap.adjoint_inner_left,
    inner_spectralOp, key]

/-- `E_T(s)` commutes with every continuous function of `T`. -/
private lemma spectralOp_mul_cfc (s : Set ℂ) (h : ℂ → ℂ) :
    hT.spectralOp s * cfc h T = cfc h T * hT.spectralOp s :=
  hT.spectralOp_mul_of_commute_cfc s fun g => cfc_commute_cfc h (fun ζ => (g ζ : ℂ)) T

/-! ### Multiplicativity -/

/-- For a real bounded continuous `h`, `ν_{h(T) u}(t) = ∫_t h² dν_u`. -/
private lemma measureReal_spectralMeasure_cfc_apply (h : ℂ →ᵇ ℝ) {t : Set ℂ} (ht : MeasurableSet t)
    (u : E) : (hT.spectralMeasure (cfc (fun ζ => (h ζ : ℂ)) T u)).real t =
      ∫ ζ in t, h ζ ^ 2 ∂(hT.spectralMeasure u) := by
  rw [hT.spectralMeasure_cfc_apply u (h := fun ζ => (h ζ : ℂ))
    (continuous_ofReal.comp h.continuous).continuousOn, measureReal_def, withDensity_apply _ ht]
  have hint : Integrable (fun ζ => h ζ ^ 2) ((hT.spectralMeasure u).restrict t) := by
    have := (h ^ 2).integrable ((hT.spectralMeasure u).restrict t)
    rwa [BoundedContinuousFunction.coe_pow] at this
  have : ∫⁻ ζ in t, ‖(h ζ : ℂ)‖ₑ ^ 2 ∂(hT.spectralMeasure u) =
      ENNReal.ofReal (∫ ζ in t, h ζ ^ 2 ∂(hT.spectralMeasure u)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun ζ => sq_nonneg _)]
    refine lintegral_congr fun ζ => ?_
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), norm_real, Real.norm_eq_abs, sq_abs]
  rw [this, ENNReal.toReal_ofReal (setIntegral_nonneg ht fun ζ _ => sq_nonneg _)]

/-- For a real bounded continuous `h` and `H = h(T)`, the value of `ν_{Hx,Hy}` on a measurable `t`,
by polarization of `ν_{H u}(t) = ∫_t h² dν_u`. -/
private lemma complexSpectralMeasure_cfc_apply (h : ℂ →ᵇ ℝ) {t : Set ℂ} (ht : MeasurableSet t) :
    hT.complexSpectralMeasure (cfc (fun ζ => (h ζ : ℂ)) T x) (cfc (fun ζ => (h ζ : ℂ)) T y) t =
      ⟨4⁻¹ * (∫ ζ in t, h ζ ^ 2 ∂(hT.spectralMeasure (x + y)) -
          ∫ ζ in t, h ζ ^ 2 ∂(hT.spectralMeasure (x - y))),
        4⁻¹ * (∫ ζ in t, h ζ ^ 2 ∂(hT.spectralMeasure (x - I • y)) -
          ∫ ζ in t, h ζ ^ 2 ∂(hT.spectralMeasure (x + I • y)))⟩ := by
  rw [complexSpectralMeasure_apply _ _ _ ht]
  simp only [← ContinuousLinearMap.map_add, ← ContinuousLinearMap.map_sub,
    ← ContinuousLinearMap.map_smul, hT.measureReal_spectralMeasure_cfc_apply h ht]

/-- The square root of a bounded continuous non-negative function, as a bounded continuous real
function. -/
private noncomputable def sqrtBCF (g : ℂ →ᵇ ℝ≥0) : ℂ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun ζ => Real.sqrt (g ζ)) (by fun_prop)
    (Real.sqrt ((g 0 : ℝ) + g.bounded.choose)) fun ζ => by
      rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      refine Real.sqrt_le_sqrt ?_
      have h := g.bounded.choose_spec ζ 0
      rw [NNReal.dist_eq] at h
      linarith [le_abs_self ((g ζ : ℝ) - g 0)]

private lemma sqrtBCF_sq (g : ℂ →ᵇ ℝ≥0) (ζ : ℂ) : sqrtBCF g ζ ^ 2 = g ζ :=
  Real.sq_sqrt (NNReal.coe_nonneg _)

/-- For `g = h²` with `h = √g`, `⟪x, g(T) E_T(t) y⟫ = ν_{h(T) x, h(T) y}(t)`. -/
private lemma inner_cfc_spectralOp (g : ℂ →ᵇ ℝ≥0) (t : Set ℂ) :
    ⟪x, cfc (fun ζ => ((g ζ : ℝ) : ℂ)) T (hT.spectralOp t y)⟫_ℂ =
      hT.complexSpectralMeasure (cfc (fun ζ => (sqrtBCF g ζ : ℂ)) T x)
        (cfc (fun ζ => (sqrtBCF g ζ : ℂ)) T y) t := by
  have := hT
  set H := cfc (fun ζ => (sqrtBCF g ζ : ℂ)) T
  have hc : ContinuousOn (fun ζ => (sqrtBCF g ζ : ℂ)) (spectrum ℂ T) :=
    (continuous_ofReal.comp (sqrtBCF g).continuous).continuousOn
  have hHH : cfc (fun ζ => ((g ζ : ℝ) : ℂ)) T = H * H := by
    rw [← cfc_mul _ _ T hc hc]
    refine cfc_congr fun ζ _ => ?_
    rw [← ofReal_mul, ← sq, sqrtBCF_sq]
  have hcomm := congrArg (fun A : E →L[ℂ] E => A y) (hT.spectralOp_mul_cfc t
    (fun ζ => (sqrtBCF g ζ : ℂ)))
  simp only [mul_apply_eq_comp] at hcomm
  rw [hHH, mul_apply_eq_comp, ← hcomm, inner_cfc_real_comm hT (sqrtBCF g), inner_spectralOp]

/-- **Restriction**: `ν_{x, E_T(t) y} = ν_{x,y}|_t` for a measurable `t`. -/
private lemma complexSpectralMeasure_spectralOp {t : Set ℂ} (ht : MeasurableSet t) :
    hT.complexSpectralMeasure x (hT.spectralOp t y) = (hT.complexSpectralMeasure x y).restrict t := by
  have hfun : ∀ g : ℂ →ᵇ ℝ≥0, (fun ζ => (g ζ : ℝ)) = fun ζ => ((sqrtBCF g) ^ 2 : ℂ →ᵇ ℝ) ζ :=
    fun g => funext fun ζ => by rw [BoundedContinuousFunction.coe_pow, Pi.pow_apply, sqrtBCF_sq]
  have hcfc : ∀ g : ℂ →ᵇ ℝ≥0, cfc (fun ζ => ((((sqrtBCF g) ^ 2 : ℂ →ᵇ ℝ) ζ : ℝ) : ℂ)) T =
      cfc (fun ζ => ((g ζ : ℝ) : ℂ)) T := fun g => by
    congr 1
    funext ζ
    rw [← congrFun (hfun g) ζ]
  have hint : ∀ (μ : Measure ℂ) [IsFiniteMeasure μ] (g : ℂ →ᵇ ℝ≥0),
      VectorMeasure.Integrable μ.toSignedMeasure (fun ζ => (g ζ : ℝ)) := fun μ _ g =>
    SignedMeasure.integrable_toSignedMeasure_iff.mpr (BoundedContinuousFunction.integrable_of_nnreal μ g)
  refine ComplexMeasure.ext_of_forall_integral_nnreal_eq (fun g => ?_) (fun g => ?_)
  · rw [hfun g, integral_re_complexSpectralMeasure, hcfc, inner_cfc_spectralOp,
      complexSpectralMeasure_cfc_apply _ _ _ _ ht, ← hfun g, ComplexMeasure.re_restrict _ ht,
      complexSpectralMeasure, SignedMeasure.re_toComplexMeasure, VectorMeasure.restrict_smul,
      VectorMeasure.restrict_sub, VectorMeasure.restrict_toSignedMeasure ht,
      VectorMeasure.restrict_toSignedMeasure ht, VectorMeasure.integral_smul_vectorMeasure,
      VectorMeasure.integral_sub_vectorMeasure (hint _ g) (hint _ g),
      VectorMeasure.integral_toSignedMeasure, VectorMeasure.integral_toSignedMeasure, smul_eq_mul]
    simp only [sqrtBCF_sq]
  · rw [hfun g, integral_im_complexSpectralMeasure, hcfc, inner_cfc_spectralOp,
      complexSpectralMeasure_cfc_apply _ _ _ _ ht, ← hfun g, ComplexMeasure.im_restrict _ ht,
      complexSpectralMeasure, SignedMeasure.im_toComplexMeasure, VectorMeasure.restrict_smul,
      VectorMeasure.restrict_sub, VectorMeasure.restrict_toSignedMeasure ht,
      VectorMeasure.restrict_toSignedMeasure ht, VectorMeasure.integral_smul_vectorMeasure,
      VectorMeasure.integral_sub_vectorMeasure (hint _ g) (hint _ g),
      VectorMeasure.integral_toSignedMeasure, VectorMeasure.integral_toSignedMeasure, smul_eq_mul]
    simp only [sqrtBCF_sq]

/-- **Multiplicativity**: `E_T(s ∩ t) = E_T(s) E_T(t)` for measurable `s` and `t`. -/
private lemma spectralOp_inter {s t : Set ℂ} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    hT.spectralOp (s ∩ t) = hT.spectralOp s * hT.spectralOp t :=
  spectralOp_ext fun x y => by
    rw [mul_apply_eq_comp, inner_spectralOp, inner_spectralOp,
      hT.complexSpectralMeasure_spectralOp x y ht, VectorMeasure.restrict_apply _ ht hs]

/-- `E_T(s)` is an orthogonal projection. -/
private lemma isStarProjection_spectralOp (s : Set ℂ) : IsStarProjection (hT.spectralOp s) := by
  by_cases hs : MeasurableSet s
  · refine ⟨?_, hT.isSelfAdjoint_spectralOp s⟩
    rw [IsIdempotentElem, ← hT.spectralOp_inter hs hs, Set.inter_self]
  · rw [hT.spectralOp_of_not_measurableSet hs]
    exact .zero _

/-- `E_T(ℂ) = 1`: `ν_{x,y}(ℂ) = ⟪x, y⟫` by polarization of `ν_u(ℂ) = ‖u‖²`. -/
private lemma spectralOp_univ : hT.spectralOp Set.univ = 1 :=
  spectralOp_ext fun x y => by
    have hG : ∀ u v : E, ⟪u, (1 : E →L[ℂ] E) v⟫_ℂ = ⟪(1 : E →L[ℂ] E) u, v⟫_ℂ := by simp
    have hre := re_polarization hG x y
    have him := im_polarization hG x y
    simp only [one_apply_eq_self, inner_self_eq_norm_sq_to_K] at hre him
    norm_cast at hre him
    rw [inner_spectralOp, complexSpectralMeasure_apply _ _ _ MeasurableSet.univ, one_apply_eq_self]
    simp only [measureReal_spectralMeasure_univ]
    exact Complex.ext hre him

/-- **Finite additivity**: `E_T(s ∪ t) = E_T(s) + E_T(t)` for disjoint measurable `s` and `t`. -/
private lemma spectralOp_union {s t : Set ℂ} (hst : Disjoint s t) (hs : MeasurableSet s)
    (ht : MeasurableSet t) : hT.spectralOp (s ∪ t) = hT.spectralOp s + hT.spectralOp t :=
  spectralOp_ext fun x y => by
    rw [inner_spectralOp, _root_.add_apply, inner_add_right, inner_spectralOp, inner_spectralOp,
      VectorMeasure.of_union hst hs ht]

/-- `E_T(∅) = 0`. -/
private lemma spectralOp_empty : hT.spectralOp ∅ = 0 :=
  spectralOp_ext fun x y => by
    rw [inner_spectralOp, VectorMeasure.empty, zero_apply, inner_zero_right]

/-- `‖E_T(s) x‖² = ν_x(s)` for a measurable `s`. -/
private lemma norm_spectralOp_apply_sq {s : Set ℂ} (hs : MeasurableSet s) :
    ‖hT.spectralOp s x‖ ^ 2 = (hT.spectralMeasure x).real s := by
  have h := (hT.isStarProjection_spectralOp s).inner_apply_self x
  rw [inner_spectralOp, complexSpectralMeasure_self_apply _ _ hs] at h
  exact_mod_cast h.symm

/-- **Strong countable additivity**: `E_T(⋃ sᵢ) x = Σ E_T(sᵢ) x` for pairwise disjoint measurable
`sᵢ`, since `‖E_T(⋃ sᵢ) x - Σ_{i ∈ F} E_T(sᵢ) x‖² = ν_x(⋃ sᵢ) - Σ_{i ∈ F} ν_x(sᵢ) → 0`. -/
private lemma hasSum_spectralOp (f : ℕ → Set ℂ) (hf : ∀ i, MeasurableSet (f i))
    (hd : Pairwise (Function.onFun Disjoint f)) (x : E) :
    HasSum (fun i => hT.spectralOp (f i) x) (hT.spectralOp (⋃ i, f i) x) := by
  set U := ⋃ i, f i
  have hU : MeasurableSet U := MeasurableSet.iUnion hf
  have hsum : ∀ F : Finset ℕ, ∑ i ∈ F, hT.spectralOp (f i) x = hT.spectralOp (⋃ i ∈ F, f i) x := by
    intro F
    induction F using Finset.induction_on with
    | empty => simp [spectralOp_empty]
    | insert a F ha ih =>
      have hdisj : Disjoint (f a) (⋃ i ∈ F, f i) :=
        Set.disjoint_iUnion₂_right.mpr fun i hi => hd (fun h : a = i => ha (h ▸ hi))
      rw [Finset.sum_insert ha, ih, Finset.set_biUnion_insert,
        hT.spectralOp_union hdisj (hf a) (Finset.measurableSet_biUnion F fun i _ => hf i),
        _root_.add_apply]
  have hmeas : HasSum (fun i => (hT.spectralMeasure x).real (f i)) ((hT.spectralMeasure x).real U) := by
    have h := ((hT.complexSpectralMeasure x x).hasSum_of_disjoint_iUnion hf hd).mapL Complex.reCLM
    convert h using 1
    · funext i
      simp [complexSpectralMeasure_self_apply _ _ (hf i)]
    · simp [U, complexSpectralMeasure_self_apply _ _ hU]
  have hnorm : ∀ F : Finset ℕ, ‖∑ i ∈ F, hT.spectralOp (f i) x - hT.spectralOp U x‖ =
      Real.sqrt ((hT.spectralMeasure x).real U - ∑ i ∈ F, (hT.spectralMeasure x).real (f i)) := by
    intro F
    set V := ⋃ i ∈ F, f i
    have hV : MeasurableSet V := Finset.measurableSet_biUnion F fun i _ => hf i
    have hVU : V ⊆ U := Set.iUnion₂_subset fun i _ => Set.subset_iUnion f i
    have hsplit : hT.spectralOp U = hT.spectralOp (U \ V) + hT.spectralOp V := by
      rw [← hT.spectralOp_union Set.disjoint_sdiff_left (hU.diff hV) hV, Set.sdiff_union_of_subset hVU]
    have hμ : (hT.spectralMeasure x).real U =
        (hT.spectralMeasure x).real (U \ V) + (hT.spectralMeasure x).real V := by
      conv_lhs => rw [← Set.sdiff_union_of_subset hVU]
      exact measureReal_union Set.disjoint_sdiff_left hV (measure_ne_top _ _) (measure_ne_top _ _)
    rw [hsum, hsplit, _root_.add_apply, norm_sub_rev, add_sub_cancel_right,
      ← measureReal_biUnion_finset (fun i _ j _ hij => hd hij) (fun i _ => hf i), hμ,
      add_sub_cancel_right, ← hT.norm_spectralOp_apply_sq _ (hU.diff hV),
      Real.sqrt_sq (norm_nonneg _)]
  rw [HasSum, tendsto_iff_norm_sub_tendsto_zero]
  simp only [hnorm]
  have h := (tendsto_const_nhds (x := (hT.spectralMeasure x).real U)).sub hmeas
  rw [sub_self] at h
  have h' := (Real.continuous_sqrt.tendsto 0).comp h
  rw [Real.sqrt_zero] at h'
  exact h'

/-! ### The projection-valued measure -/

/-- The **projection-valued measure** `E_T` of a normal operator `T` on the Borel sets of `ℂ`, with
`⟪x, E_T(s) y⟫ = ν_{x,y}(s)` (`IsStarNormal.inner_pvm_apply`); it is concentrated on the spectrum
of `T` (`IsStarNormal.pvm_compl_spectrum`). The construction is that of the proof of Rudin,
*Functional Analysis*, Theorem 12.22. -/
@[no_expose] noncomputable def pvm : ProjectionValuedMeasure ℂ E :=
  ProjectionValuedMeasure.ofHasSum hT.spectralOp (fun _ hs => hT.spectralOp_of_not_measurableSet hs)
    (fun f hf hd x => hT.hasSum_spectralOp f hf hd x) hT.isStarProjection_spectralOp
    hT.spectralOp_univ

/-- The projections of `E_T` are the operators `E_T(s)`. -/
private lemma pvm_apply (s : Set ℂ) : hT.pvm s = hT.spectralOp s := rfl

/-- `⟪x, E_T(s) y⟫ = ν_{x,y}(s)`. -/
private lemma inner_pvm_apply (s : Set ℂ) : ⟪x, hT.pvm s y⟫_ℂ = hT.complexSpectralMeasure x y s :=
  hT.inner_spectralOp s x y

/-- The complex measures of `E_T` are the complex spectral measures `ν_{x,y}`. -/
private lemma complexMeasure_pvm : hT.pvm.complexMeasure x y = hT.complexSpectralMeasure x y := by
  ext s hs
  rw [ProjectionValuedMeasure.complexMeasure_apply, inner_pvm_apply]

/-- **Functional calculus** through `E_T`: `⟪x, cfc g T y⟫ = ∫ g dE_{x,y}` for `g` continuous on
the spectrum, the integral against the complex measure `E_{x,y}` being taken part by part. -/
lemma inner_cfc_eq_integral_pvm {g : ℂ → ℂ} (hg : ContinuousOn g (spectrum ℂ T)) :
    ⟪x, cfc g T y⟫_ℂ = ∫ᵛ ζ, g ζ ∂<•(hT.pvm.complexMeasure x y).re +
      I * ∫ᵛ ζ, g ζ ∂<•(hT.pvm.complexMeasure x y).im := by
  rw [complexMeasure_pvm]
  exact hT.inner_cfc_eq_integral_complexSpectralMeasure x y hg

/-- **Spectral theorem** for a normal operator, weak form: `⟪x, T y⟫ = ∫ ζ dE_{x,y}(ζ)`, i.e.
`T = ∫ ζ dE_T(ζ)` weakly. -/
theorem inner_apply_eq_integral_pvm :
    ⟪x, T y⟫_ℂ = ∫ᵛ ζ, ζ ∂<•(hT.pvm.complexMeasure x y).re +
      I * ∫ᵛ ζ, ζ ∂<•(hT.pvm.complexMeasure x y).im := by
  rw [complexMeasure_pvm]
  exact hT.inner_apply_eq_integral_complexSpectralMeasure x y

/-- The projections of `E_T` commute with every continuous function of `T`. -/
lemma commute_pvm_cfc (s : Set ℂ) (h : ℂ → ℂ) : Commute (hT.pvm s) (cfc h T) :=
  hT.spectralOp_mul_cfc s h

/-- **Operators commuting with `T` commute with `E_T`** (Rudin, *Functional Analysis*,
Theorem 12.23): if `S T = T S`, then `S E_T(s) = E_T(s) S` for every `s`. By the
Fuglede–Putnam–Rosenblum theorem `S` also commutes with `T⋆`, hence with every continuous function
of `T` (`ContinuousLinearMap.comp_cfc_eq_cfc_comp`), and the complex measures `E_{S† x, y}` and
`E_{x, S y}` then integrate every bounded continuous real function to the same value. -/
theorem commute_pvm_of_commute {S : E →L[ℂ] E} (hS : Commute S T) (s : Set ℂ) :
    Commute S (hT.pvm s) :=
  (hT.spectralOp_mul_of_commute_cfc s fun g =>
    ContinuousLinearMap.comp_cfc_eq_cfc_comp hT hT hS.eq
      (by fun_prop : Continuous fun ζ => (g ζ : ℂ)).continuousOn
      (by fun_prop : Continuous fun ζ => (g ζ : ℂ)).continuousOn).symm

/-- Conversely, an operator commuting with every projection `E_T(s)` commutes with
`T = ∫ ζ dE_T(ζ)`: the complex measures `E_{x, S y}` and `E_{S† x, y}` coincide. -/
lemma commute_of_forall_commute_pvm {S : E →L[ℂ] E} (hS : ∀ s, Commute S (hT.pvm s)) :
    Commute S T := by
  have key : ∀ x y, hT.pvm.complexMeasure x (S y) =
      hT.pvm.complexMeasure (ContinuousLinearMap.adjoint S x) y := fun x y => by
    ext t -
    rw [ProjectionValuedMeasure.complexMeasure_apply, ProjectionValuedMeasure.complexMeasure_apply,
      ContinuousLinearMap.adjoint_inner_left, ← mul_apply_eq_comp, ← mul_apply_eq_comp,
      (hS t).eq]
  refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => ?_
  rw [mul_apply_eq_comp, mul_apply_eq_comp, ← ContinuousLinearMap.adjoint_inner_left,
    hT.inner_apply_eq_integral_pvm, hT.inner_apply_eq_integral_pvm, key]

/-- **The commutant of a normal operator is the commutant of its spectral projections**
(Rudin, *Functional Analysis*, Theorems 12.22–12.23): `S` commutes with `T` iff it commutes with
every `E_T(s)`. -/
lemma forall_commute_pvm_iff {S : E →L[ℂ] E} : (∀ s, Commute S (hT.pvm s)) ↔ Commute S T :=
  ⟨hT.commute_of_forall_commute_pvm, fun h => hT.commute_pvm_of_commute h⟩

/-- The diagonal measures of `E_T` are the scalar spectral measures `ν_x`. -/
private lemma measure_pvm : hT.pvm.measure x = hT.spectralMeasure x := by
  ext s hs
  rw [ProjectionValuedMeasure.measure_apply x hs, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    pvm_apply, hT.norm_spectralOp_apply_sq x hs, ofReal_measureReal]

/-! ### The diagonal measures of `E_T`

The scalar spectral measures `ν_x` are inputs to the construction of `E_T`; every statement from
here on, and downstream, is about the diagonal measures `E_T.measure x`, which equal them
(`measure_pvm`, private). The results below carry the properties of `ν_x` over once. -/

omit hT in
/-- `E_T` transports along equalities of operators, whatever proofs of normality are used. -/
lemma pvm_congr {S : E →L[ℂ] E} (hT : IsStarNormal T) (hS : IsStarNormal S) (h : T = S) :
    hT.pvm = hS.pvm := by
  subst h
  rfl

/-- **Spectral integral formula**: `∫ g dE_x = re ⟪x, cfc g T x⟫` for a real `g` continuous on the
spectrum of `T`. -/
lemma integral_measure_pvm {g : ℂ → ℝ} (hg : ContinuousOn g (spectrum ℂ T)) :
    ∫ ζ, g ζ ∂(hT.pvm.measure x) = re ⟪x, cfc (fun ζ => (g ζ : ℂ)) T x⟫_ℂ := by
  rw [measure_pvm]
  exact hT.integral_spectralMeasure x hg

/-- **Spectral integral formula**, complex form: `⟪x, cfc g T x⟫ = ∫ g dE_x` for `g` continuous on
the spectrum of `T`. -/
lemma inner_cfc_eq_integral_measure_pvm {g : ℂ → ℂ} (hg : ContinuousOn g (spectrum ℂ T)) :
    ⟪x, cfc g T x⟫_ℂ = ∫ ζ, g ζ ∂(hT.pvm.measure x) := by
  rw [measure_pvm]
  exact hT.inner_cfc_eq_integral_spectralMeasure x hg

/-- A function continuous on the spectrum of `T` is `E_x`-integrable. -/
lemma integrable_measure_pvm {g : ℂ → ℂ} (hg : ContinuousOn g (spectrum ℂ T)) :
    Integrable g (hT.pvm.measure x) := by
  rw [measure_pvm]
  exact hT.integrable_spectralMeasure x hg

variable {x} in
/-- **Uniqueness of the diagonal measures**: a finite measure `ν` on `ℂ` with
`∫ g dν = re ⟪x, cfc g T x⟫` for every bounded continuous real `g` is `E_x`. -/
lemma eq_measure_pvm_of_integral (ν : Measure ℂ) [IsFiniteMeasure ν]
    (h : ∀ g : ℂ →ᵇ ℝ, ∫ ζ, g ζ ∂ν = re ⟪x, cfc (fun ζ => (g ζ : ℂ)) T x⟫_ℂ) :
    ν = hT.pvm.measure x := by
  rw [measure_pvm]
  exact hT.eq_spectralMeasure_of_integral ν h

/-- `E_x` is concentrated on the spectrum of `T`. -/
lemma measure_pvm_compl_spectrum : hT.pvm.measure x (spectrum ℂ T)ᶜ = 0 := by
  rw [measure_pvm]
  exact hT.spectralMeasure_compl_spectrum x

/-- `E_x`-almost every point lies in the spectrum of `T`. -/
lemma ae_mem_spectrum_measure_pvm : ∀ᵐ ζ ∂(hT.pvm.measure x), ζ ∈ spectrum ℂ T := by
  rw [measure_pvm]
  exact hT.ae_mem_spectrum_spectralMeasure x

variable {x} in
/-- `E_x` has no atom at `ζ₀` when `x` lies in the closure of the range of `T - ζ₀`. -/
lemma measure_pvm_singleton_eq_zero_of_mem_closure_range {ζ₀ : ℂ}
    (hx : x ∈ closure (Set.range (T - algebraMap ℂ (E →L[ℂ] E) ζ₀))) :
    hT.pvm.measure x {ζ₀} = 0 := by
  rw [measure_pvm]
  exact hT.spectralMeasure_singleton_eq_zero_of_mem_closure_range hx

/-- **Transformation rule**: `E_{h(T) x} = |h|² E_x` for `h` continuous on the spectrum of `T`. -/
lemma measure_pvm_cfc_apply {h : ℂ → ℂ} (hh : ContinuousOn h (spectrum ℂ T)) :
    hT.pvm.measure (cfc h T x) = (hT.pvm.measure x).withDensity fun ζ => ‖h ζ‖ₑ ^ 2 := by
  rw [measure_pvm, measure_pvm]
  exact hT.spectralMeasure_cfc_apply x hh

/-- **Spectral mapping**: for `φ` continuous on the spectrum of `T` and measurable on `ℂ`, the
projection-valued measure of `φ(T)` is the image of `E_T` under `φ`. -/
theorem pvm_cfc_eq_map {φ : ℂ → ℂ} (hφ : ContinuousOn φ (spectrum ℂ T)) (hφm : Measurable φ)
    (hφT : IsStarNormal (cfc φ T)) : hφT.pvm = hT.pvm.map φ hφm :=
  ProjectionValuedMeasure.ext_of_measure _ fun u => by
    rw [ProjectionValuedMeasure.measure_map, measure_pvm, measure_pvm,
      hT.spectralMeasure_cfc_eq_map u hφ hφm hφT]

/-- `E_T` is concentrated on the spectrum of `T`. -/
lemma pvm_compl_spectrum : hT.pvm (spectrum ℂ T)ᶜ = 0 := by
  have hs : MeasurableSet (spectrum ℂ T)ᶜ := (spectrum.isClosed T).measurableSet.compl
  ext x
  have h := hT.norm_spectralOp_apply_sq x hs
  rw [measureReal_def, hT.spectralMeasure_compl_spectrum x, ENNReal.toReal_zero] at h
  rw [pvm_apply, zero_apply]
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h)

/-! ### Uniqueness

A projection-valued measure `F` on `ℂ`, concentrated on a compact set, with `T = ∫ ζ dF(ζ)` is
`E_T`. The argument uses only the quadratic form `⟪v, T v⟫ = ∫ ζ dF_v`:

1. every `F(s)` commutes with `T`, since `F_{F(s) a + F(sᶜ) b} = F_{F(s) a} + F_{F(sᶜ) b}`
   forces the cross terms `⟪F(s) a, T F(sᶜ) b⟫` to vanish;
2. for `s` in the disc of radius `r` about `c`, `|⟪v, (T - c) v⟫| ≤ r ‖v‖²` on the range of `F(s)`,
   so `‖(T - c)^k v‖ ≤ (2 r)^k ‖v‖` there (norm and numerical radius);
3. such a `v` has `‖(T - c)^k v‖² = ∫ |ζ - c|^{2k} dE_v`, so `E_v` lives on the disc of radius
   `3 r` (let `k → ∞`);
4. covering an open `U` by countably many such discs gives `F_v(U) ≤ E_v(U)`, and outer regularity
   and `F_v(ℂ) = E_v(ℂ)` give `F_v = E_v`. -/

section Uniqueness

variable {K : Set ℂ}

/-- The identity is integrable against the diagonal measures of a compactly supported
projection-valued measure. -/
private lemma integrable_id_measure (G : ProjectionValuedMeasure ℂ E) (hK : IsCompact K)
    (hG : G Kᶜ = 0) (w : E) : Integrable (fun ζ : ℂ => ζ) (G.measure w) := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  refine (integrable_const R).mono' measurable_id.aestronglyMeasurable ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp
    ((G.apply_eq_zero_iff hK.isClosed.measurableSet.compl).mp hG w)] with ζ hζ
  simpa using hR (not_not.mp hζ)

/-- If `⟪v, T v⟫ = ∫ ζ dG_v` for every `v`, then every projection `G(s)` commutes with `T`. -/
private lemma commute_of_inner_self (G : ProjectionValuedMeasure ℂ E) (hK : IsCompact K)
    (hG : G Kᶜ = 0) (hGT : ∀ v, ⟪v, T v⟫_ℂ = ∫ ζ, ζ ∂(G.measure v)) {s : Set ℂ}
    (hs : MeasurableSet s) : Commute (G s) T := by
  set P := G s
  set Q := G sᶜ
  have hPQ : P + Q = 1 := by
    rw [← G.apply_union disjoint_compl_right hs hs.compl, Set.union_compl_self, G.apply_univ]
  have hcross : ∀ a b, ⟪P a, T (Q b)⟫_ℂ + ⟪Q b, T (P a)⟫_ℂ = 0 := fun a b => by
    have h := hGT (P a + Q b)
    rw [ProjectionValuedMeasure.measure_add_apply_of_disjoint hs hs.compl disjoint_compl_right,
      integral_add_measure (integrable_id_measure G hK hG _) (integrable_id_measure G hK hG _),
      ← hGT, ← hGT, map_add, inner_add_left, inner_add_right, inner_add_right] at h
    linear_combination h
  have hX : ∀ a b, ⟪P a, T (Q b)⟫_ℂ = 0 := fun a b => by
    have h1 := hcross a b
    have h2 := hcross a (I • b)
    rw [map_smul, map_smul, inner_smul_right, inner_smul_left, conj_I] at h2
    linear_combination (1 / 2 : ℂ) * h1 - (I / 2) * h2 +
      ((⟪P a, T (Q b)⟫_ℂ - ⟪Q b, T (P a)⟫_ℂ) / 2) * I_sq
  have hY : ∀ a b, ⟪Q b, T (P a)⟫_ℂ = 0 := fun a b => by
    have h := hcross a b
    rwa [hX, zero_add] at h
  have hPTQ : P * T * Q = 0 := ContinuousLinearMap.ext fun b => ext_inner_left ℂ fun a => by
    rw [mul_apply_eq_comp, mul_apply_eq_comp, ← G.inner_apply_left, hX, zero_apply,
      inner_zero_right]
  have hQTP : Q * T * P = 0 := ContinuousLinearMap.ext fun b => ext_inner_left ℂ fun a => by
    rw [mul_apply_eq_comp, mul_apply_eq_comp, ← G.inner_apply_left, hY, zero_apply,
      inner_zero_right]
  calc P * T = P * T * (P + Q) := by rw [hPQ, mul_one]
    _ = P * T * P := by rw [mul_add, hPTQ, add_zero]
    _ = (P + Q) * T * P := by rw [add_mul, add_mul, hQTP, add_zero]
    _ = T * P := by rw [hPQ, one_mul]

/-- If `⟪v, T v⟫ = ∫ ζ dG_v` for every `v` and `s` lies in the closed disc of radius `r` about `c`,
then `‖(T - c)^k v‖ ≤ (2 r)^k ‖v‖` on the range of `G(s)`. -/
private lemma norm_sub_pow_apply_le (G : ProjectionValuedMeasure ℂ E) (hK : IsCompact K)
    (hG : G Kᶜ = 0) (hGT : ∀ v, ⟪v, T v⟫_ℂ = ∫ ζ, ζ ∂(G.measure v)) {s : Set ℂ}
    (hs : MeasurableSet s) {c : ℂ} {r : ℝ} (hr : 0 ≤ r) (hsc : s ⊆ Metric.closedBall c r) {v : E}
    (hv : G s v = v) (k : ℕ) :
    ‖((T - algebraMap ℂ (E →L[ℂ] E) c) ^ k) v‖ ≤ (2 * r) ^ k * ‖v‖ := by
  set B := T - algebraMap ℂ (E →L[ℂ] E) c
  have hcomm : Commute (G s) B :=
    (commute_of_inner_self G hK hG hGT hs).sub_right (Algebra.commutes c (G s)).symm
  have hidem : ∀ z, G s (G s z) = G s z := fun z => by
    rw [← mul_apply_eq_comp, (G.isStarProjection s).isIdempotentElem.eq]
  -- the numerical range of `B G(s)` lies in the disc of radius `r`
  have hnum : ∀ w, ‖⟪w, (B * G s) w⟫_ℂ‖ ≤ r * ‖w‖ ^ 2 := fun w => by
    set u := G s w
    have hBu : (B * G s) w = G s (B u) := by
      rw [mul_apply_eq_comp, ← hidem w, ← mul_apply_eq_comp B, ← hcomm.eq, mul_apply_eq_comp]
    have hint : ⟪u, B u⟫_ℂ = ∫ ζ, (ζ - c) ∂(G.measure u) := by
      rw [integral_sub (integrable_id_measure G hK hG u) (integrable_const c), integral_const,
        G.measureReal_apply u MeasurableSet.univ, G.apply_univ, one_apply_eq_self, ← hGT,
        sub_apply, inner_sub_right, Algebra.algebraMap_eq_smul_one, smul_apply,
        one_apply_eq_self, inner_smul_right, inner_self_eq_norm_sq_to_K, Complex.real_smul,
        mul_comm]
      simp
    rw [hBu, ← G.inner_apply_left, hint]
    calc ‖∫ ζ, (ζ - c) ∂(G.measure u)‖ ≤ r * (G.measure u).real Set.univ := by
          refine norm_integral_le_of_norm_le_const ?_
          rw [ProjectionValuedMeasure.measure_apply_eq_restrict hs w]
          filter_upwards [ae_restrict_mem hs] with ζ hζ
          simpa [dist_eq_norm] using hsc hζ
      _ ≤ r * ‖w‖ ^ 2 := by
          rw [G.measureReal_apply u MeasurableSet.univ, G.apply_univ, one_apply_eq_self]
          gcongr
          exact G.norm_apply_le s w
  have hA := (B * G s).norm_apply_le_of_norm_inner_self_le hnum
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : G s ((B ^ k) v) = (B ^ k) v := by
      rw [← mul_apply_eq_comp, (hcomm.pow_right k).eq, mul_apply_eq_comp, hv]
    calc ‖(B ^ (k + 1)) v‖ = ‖(B * G s) ((B ^ k) v)‖ := by
          rw [pow_succ', mul_apply_eq_comp, mul_apply_eq_comp, hk]
      _ ≤ 2 * r * ‖(B ^ k) v‖ := hA _
      _ ≤ 2 * r * ((2 * r) ^ k * ‖v‖) := by gcongr
      _ = (2 * r) ^ (k + 1) * ‖v‖ := by ring

include hT in
/-- A vector with `‖(T - c)^k v‖ ≤ (2 r)^k ‖v‖` for every `k` lies in the range of `E_T` of the
closed disc of radius `3 r` about `c`: `∫ |ζ - c|^{2k} dE_v ≤ (2 r)^{2k} ‖v‖²` leaves no mass where
`|ζ - c| ≥ 3 r`. -/
private lemma pvm_compl_closedBall_apply_eq_zero {c : ℂ} {r : ℝ} (hr : 0 < r) {v : E}
    (hv : ∀ k : ℕ, ‖((T - algebraMap ℂ (E →L[ℂ] E) c) ^ k) v‖ ≤ (2 * r) ^ k * ‖v‖) :
    hT.pvm (Metric.closedBall c (3 * r))ᶜ v = 0 := by
  have := hT
  set μ := hT.pvm.measure v
  have hcfc : ∀ k : ℕ, cfc (fun ζ => (ζ - c) ^ k) T = (T - algebraMap ℂ (E →L[ℂ] E) c) ^ k :=
    fun k => by
      rw [cfc_pow (fun ζ => ζ - c) k T, cfc_sub (fun ζ => ζ) (fun _ => c) T, cfc_id' ℂ T,
        cfc_const c T]
  have hmass : ∀ k : ℕ, ‖((T - algebraMap ℂ (E →L[ℂ] E) c) ^ k) v‖ₑ ^ 2 =
      ∫⁻ ζ, ‖(ζ - c) ^ k‖ₑ ^ 2 ∂μ := fun k => by
    have h := congrArg (fun m : Measure ℂ => m Set.univ)
      (hT.measure_pvm_cfc_apply v (h := fun ζ => (ζ - c) ^ k) (by fun_prop))
    rwa [ProjectionValuedMeasure.measure_univ, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ, hcfc] at h
  set A := {ζ : ℂ | 3 * r ≤ ‖ζ - c‖}
  have hAm : MeasurableSet A := measurableSet_le measurable_const (by fun_prop)
  have hA : ∀ k : ℕ, ENNReal.ofReal ((3 * r) ^ (2 * k)) * μ A ≤
      ENNReal.ofReal (((2 * r) ^ k * ‖v‖) ^ 2) := fun k => by
    calc ENNReal.ofReal ((3 * r) ^ (2 * k)) * μ A
        = ∫⁻ _ in A, ENNReal.ofReal ((3 * r) ^ (2 * k)) ∂μ := (setLIntegral_const A _).symm
      _ ≤ ∫⁻ ζ in A, ‖(ζ - c) ^ k‖ₑ ^ 2 ∂μ := by
          refine setLIntegral_mono' hAm fun ζ hζ => ?_
          rw [← ofReal_norm, norm_pow, ← ENNReal.ofReal_pow (by positivity), ← pow_mul,
            mul_comm k]
          exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) hζ _)
      _ ≤ ∫⁻ ζ, ‖(ζ - c) ^ k‖ₑ ^ 2 ∂μ := setLIntegral_le_lintegral _ _
      _ = ‖((T - algebraMap ℂ (E →L[ℂ] E) c) ^ k) v‖ₑ ^ 2 := (hmass k).symm
      _ ≤ ENNReal.ofReal (((2 * r) ^ k * ‖v‖) ^ 2) := by
          rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hv k) 2)
  have hreal : ∀ k : ℕ, μ.real A ≤ (4 / 9 : ℝ) ^ k * ‖v‖ ^ 2 := fun k => by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hA k)
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (by positivity), ← measureReal_def] at h
    have h3 : (0 : ℝ) < (3 * r) ^ (2 * k) := by positivity
    have heq : ((2 * r) ^ k * ‖v‖) ^ 2 = (4 / 9 : ℝ) ^ k * ‖v‖ ^ 2 * (3 * r) ^ (2 * k) := by
      rw [pow_mul, mul_pow, ← pow_mul, mul_comm k 2, pow_mul]
      rw [mul_assoc, mul_comm (‖v‖ ^ 2), ← mul_assoc, ← mul_pow]
      congr 2
      ring
    rw [heq, mul_comm] at h
    exact le_of_mul_le_mul_right h h3
  have hlim : Filter.Tendsto (fun k : ℕ => (4 / 9 : ℝ) ^ k * ‖v‖ ^ 2) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).mul_const
      (‖v‖ ^ 2)
  have hzero : μ A = 0 := (measureReal_eq_zero_iff (measure_ne_top _ _)).mp
    (le_antisymm (ge_of_tendsto' hlim hreal) measureReal_nonneg)
  have hsub : (Metric.closedBall c (3 * r))ᶜ ⊆ A := fun ζ hζ => by
    simp only [Set.mem_compl_iff, Metric.mem_closedBall, not_le, dist_eq_norm] at hζ
    exact hζ.le
  have hball := measure_mono_null hsub hzero
  rw [ProjectionValuedMeasure.measure_apply v Metric.isClosed_closedBall.measurableSet.compl,
    pow_eq_zero_iff two_ne_zero, enorm_eq_zero] at hball
  exact hball

include hT in
/-- If `⟪v, T v⟫ = ∫ ζ dF_v` for every `v`, then `F_v(U) ≤ E_v(U)` for every open `U`. -/
private lemma measure_le_measure_pvm_of_isOpen (F : ProjectionValuedMeasure ℂ E)
    (hK : IsCompact K) (hF : F Kᶜ = 0) (hFT : ∀ v, ⟪v, T v⟫_ℂ = ∫ ζ, ζ ∂(F.measure v))
    {U : Set ℂ} (hU : IsOpen U) (v : E) : F.measure v U ≤ hT.pvm.measure v U := by
  -- the range of `F(s)`, for `s` in a disc whose triple lies in `U`, lies in that of `E_T(U)`
  have hpiece : ∀ {s : Set ℂ} {c : ℂ} {r : ℝ}, MeasurableSet s → 0 < r →
      s ⊆ Metric.closedBall c r → Metric.closedBall c (3 * r) ⊆ U →
      ∀ w, hT.pvm U (F s w) = F s w := fun {s c r} hs hr hsc hcU w => by
    have hCm : MeasurableSet (Metric.closedBall c (3 * r)) :=
      Metric.isClosed_closedBall.measurableSet
    have hidem : F s (F s w) = F s w := by
      rw [← mul_apply_eq_comp, (F.isStarProjection s).isIdempotentElem.eq]
    have h0 := hT.pvm_compl_closedBall_apply_eq_zero hr
      (norm_sub_pow_apply_le F hK hF hFT hs hr.le hsc hidem)
    have hC : hT.pvm (Metric.closedBall c (3 * r)) (F s w) = F s w := by
      have h1 := hT.pvm.apply_union disjoint_compl_right hCm hCm.compl
      rw [Set.union_compl_self, hT.pvm.apply_univ] at h1
      have h2 := congrArg (fun A : E →L[ℂ] E => A (F s w)) h1
      simp only [one_apply_eq_self, add_apply, h0, add_zero] at h2
      exact h2.symm
    rw [← hC, ← mul_apply_eq_comp, ← hT.pvm.apply_inter hU.measurableSet hCm,
      Set.inter_eq_right.mpr hcU]
  -- a countable cover of `U` by such discs (Lindelöf), made disjoint
  have hε : ∀ z ∈ U, ∃ ε > 0, Metric.ball z ε ⊆ U := Metric.isOpen_iff.mp hU
  choose! ε hε0 hεU using hε
  set B : U → Set ℂ := fun z => Metric.ball (z : ℂ) (ε z / 4)
  have hBU : ⋃ z, B z = U := by
    refine subset_antisymm (Set.iUnion_subset fun z => ?_) fun x hx => ?_
    · exact (Metric.ball_subset_ball (by linarith [hε0 z z.2])).trans (hεU z z.2)
    · exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (by linarith [hε0 x hx])⟩
  obtain ⟨S, hS, hSU⟩ := TopologicalSpace.isOpen_iUnion_countable B fun _ => Metric.isOpen_ball
  rcases U.eq_empty_or_nonempty with hU0 | hU0
  · simp [hU0]
  have hSne : S.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, hBU] at hSU
    simp only [Set.mem_empty_iff_false, Set.iUnion_of_empty, Set.iUnion_empty] at hSU
    exact hU0.ne_empty hSU.symm
  obtain ⟨f, rfl⟩ := hS.exists_eq_range hSne
  rw [Set.biUnion_range, hBU] at hSU
  set t := disjointed fun n => B (f n)
  have htm : ∀ n, MeasurableSet (t n) :=
    MeasurableSet.disjointed fun n => Metric.isOpen_ball.measurableSet
  have htU : ⋃ n, t n = U := by rw [iUnion_disjointed, hSU]
  have hkey : ∀ n w, hT.pvm U (F (t n) w) = F (t n) w := fun n w => by
    have hz := (f n).2
    refine hpiece (c := f n) (r := ε (f n) / 4) (htm n) (by linarith [hε0 _ hz])
      ((disjointed_subset _ n).trans Metric.ball_subset_closedBall) ?_ w
    exact (Metric.closedBall_subset_ball (by linarith [hε0 _ hz])).trans (hεU _ hz)
  -- hence `E_T(U) F(U) = F(U)`, and `‖F(U) v‖ ≤ ‖E_T(U) v‖`
  have hfix : ∀ w, hT.pvm U (F U w) = F U w := fun w => by
    have hsum := F.hasSum_apply htm (disjoint_disjointed _) w
    rw [htU] at hsum
    have h := hsum.mapL (hT.pvm U)
    simp only [hkey] at h
    exact h.unique hsum
  have hFE : F U v = F U (hT.pvm U v) := ext_inner_left ℂ fun x => by
    rw [← F.inner_apply_left, ← hfix x, hT.pvm.inner_apply_left, F.inner_apply_left]
  rw [ProjectionValuedMeasure.measure_apply v hU.measurableSet,
    ProjectionValuedMeasure.measure_apply v hU.measurableSet, hFE]
  gcongr
  exact enorm_le_iff_norm_le.mpr (F.norm_apply_le U _)

/-- **Uniqueness of `E_T`**, quadratic-form version: a projection-valued measure `F` on `ℂ`,
concentrated on a compact set, with `⟪x, T x⟫ = ∫ ζ dF_x(ζ)` for every `x` is `E_T`. -/
lemma eq_pvm_of_inner_self_eq_integral (F : ProjectionValuedMeasure ℂ E) (hK : IsCompact K)
    (hF : F Kᶜ = 0) (h : ∀ x, ⟪x, T x⟫_ℂ = ∫ ζ, ζ ∂(F.measure x)) : F = hT.pvm := by
  refine F.ext_of_measure fun v => ?_
  refine Measure.eq_of_le_of_measure_univ_eq (Measure.le_iff.mpr fun A _ => ?_)
    (by rw [ProjectionValuedMeasure.measure_univ, ProjectionValuedMeasure.measure_univ])
  refine le_of_forall_gt_imp_ge_of_dense fun r hr => ?_
  obtain ⟨U, hAU, hU, hUr⟩ := A.exists_isOpen_lt_of_lt r hr
  exact (measure_mono hAU).trans
    ((hT.measure_le_measure_pvm_of_isOpen F hK hF h hU v).trans hUr.le)

/-- **Uniqueness of `E_T`**, the uniqueness half of the spectral theorem (Rudin, *Functional
Analysis*, Chapter 12): a projection-valued measure `F` on `ℂ`, concentrated on a compact set `K`,
with `T = ∫ ζ dF(ζ)` weakly, `⟪x, T y⟫ = ∫ ζ dF_{x,y}(ζ)`, is `E_T`. Rudin's resolutions of the
identity live on `σ(T)`, the case `K = σ(T)`. -/
theorem eq_pvm_of_integral (F : ProjectionValuedMeasure ℂ E) (hK : IsCompact K)
    (hF : F Kᶜ = 0)
    (h : ∀ x y : E, ⟪x, T y⟫_ℂ = ∫ᵛ ζ, ζ ∂<•(F.complexMeasure x y).re +
      I * ∫ᵛ ζ, ζ ∂<•(F.complexMeasure x y).im) : F = hT.pvm :=
  hT.eq_pvm_of_inner_self_eq_integral F hK hF fun x => by
    rw [h x x, F.re_complexMeasure_self, F.im_complexMeasure_self,
      VectorMeasure.integral_toSignedMeasure, VectorMeasure.integral_zero_vectorMeasure, mul_zero,
      add_zero]

end Uniqueness

/-! ### Spectrum and support -/

/-- **The spectrum is the support of `E_T`**: `ζ₀ ∈ σ(T)` iff `E_T` does not vanish on any ball
around `ζ₀`. If `E_T(B(ζ₀, ε)) = 0`, a continuous bump `g` supported in the ball with `g(ζ₀) = 1`
has `⟪u, g(T) u⟫ = ∫ g dν_u = 0` for every `u`, so `g(T) = 0` and `g` vanishes on the spectrum. -/
theorem mem_spectrum_iff_forall_pvm_ball_ne_zero {ζ₀ : ℂ} :
    ζ₀ ∈ spectrum ℂ T ↔ ∀ ε > 0, hT.pvm (Metric.ball ζ₀ ε) ≠ 0 := by
  constructor
  · intro hζ ε hε h0
    have := hT
    let g : ℂ → ℝ := fun ζ => max 0 (1 - dist ζ ζ₀ / ε)
    have hg : Continuous g := by fun_prop
    have hgball : ∀ ζ, ζ ∉ Metric.ball ζ₀ ε → g ζ = 0 := fun ζ hζ => by
      rw [Metric.mem_ball, not_lt] at hζ
      refine max_eq_left ?_
      rw [sub_nonpos, one_le_div hε]
      exact hζ
    have hzero : ∀ u, ⟪cfc (fun ζ => (g ζ : ℂ)) T u, u⟫_ℂ = ⟪(0 : E →L[ℂ] E) u, u⟫_ℂ := fun u => by
      have hν : hT.spectralMeasure u (Metric.ball ζ₀ ε) = 0 := by
        rw [← hT.measure_pvm]
        exact (hT.pvm.apply_eq_zero_iff Metric.isOpen_ball.measurableSet).mp h0 u
      rw [zero_apply, inner_zero_left, ← inner_conj_symm,
        hT.inner_cfc_eq_integral_spectralMeasure u (g := fun ζ => (g ζ : ℂ))
          (continuous_ofReal.comp hg).continuousOn, integral_eq_zero_of_ae, map_zero]
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hν] with ζ hζ
      simp [hgball ζ hζ]
    have hG : cfc (fun ζ => (g ζ : ℂ)) T = cfc (fun _ => (0 : ℂ)) T := by
      rw [cfc_const_zero]
      have hlin := (ext_inner_map ((cfc (fun ζ => (g ζ : ℂ)) T : E →L[ℂ] E) : E →ₗ[ℂ] E)
        ((0 : E →L[ℂ] E) : E →ₗ[ℂ] E)).mp hzero
      exact ContinuousLinearMap.coe_injective hlin
    have h1 := eqOn_of_cfc_eq_cfc hG (continuous_ofReal.comp hg).continuousOn continuousOn_const
    simpa [g] using h1 hζ
  · intro h
    by_contra hζ
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (spectrum.isClosed T).isOpen_compl ζ₀ hζ
    apply h ε hε
    rw [← Set.inter_eq_left.mpr hball, hT.pvm.apply_inter Metric.isOpen_ball.measurableSet
      (spectrum.isClosed T).measurableSet.compl, pvm_compl_spectrum, mul_zero]

/-- **The spectrum is the closed support of the diagonal measures**:
`σ(T) = closure (⋃ᵤ supp E_u)`. -/
lemma spectrum_eq_closure_iUnion_support :
    spectrum ℂ T = closure (⋃ u, (hT.pvm.measure u).support) := by
  simp only [measure_pvm]
  refine subset_antisymm (fun ζ₀ hζ => ?_) (closure_minimal
    (Set.iUnion_subset fun u => hT.support_spectralMeasure_subset u) (spectrum.isClosed T))
  rw [Metric.mem_closure_iff]
  intro ε hε
  have h := hT.mem_spectrum_iff_forall_pvm_ball_ne_zero.mp hζ ε hε
  obtain ⟨u, hu⟩ : ∃ u, hT.spectralMeasure u (Metric.ball ζ₀ ε) ≠ 0 := by
    by_contra! hc
    exact h ((hT.pvm.apply_eq_zero_iff Metric.isOpen_ball.measurableSet).mpr fun u => by
      rw [hT.measure_pvm]
      exact hc u)
  obtain ⟨ζ, hζball, hζsupp⟩ := Measure.nonempty_inter_support_of_pos (pos_iff_ne_zero.mpr hu)
  exact ⟨ζ, Set.mem_iUnion.mpr ⟨u, hζsupp⟩, by rw [dist_comm]; exact hζball⟩

end IsStarNormal
