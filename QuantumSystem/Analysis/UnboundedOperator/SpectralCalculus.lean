/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Eigenvector
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Intertwine
public import QuantumSystem.ForMathlib.Topology.Algebra.Module.LinearPMap
public import QuantumSystem.Analysis.UnboundedOperator.RestrictScalars
public import QuantumSystem.Analysis.UnboundedOperator.SpectralMeasure
public import QuantumSystem.Analysis.UnboundedOperator.VonNeumann

/-!
# Calculus of scalar spectral measures

Properties of the measures `ν_u^w = IsSelfAdjoint.resolventMeasure hA w u` and
`μ_u = IsSelfAdjoint.spectralMeasure hA u` of a self-adjoint operator `A`, with
`R = (w - A)⁻¹`.

## Main results

* `IsSelfAdjoint.integral_resolventMeasure_cfc_apply`, `IsSelfAdjoint.resolventMeasure_cfc_apply`,
  `IsSelfAdjoint.spectralMeasure_cfc_apply` — the transformation rule `ν_{h(R) u}^w = |h|² ν_u^w`,
  in integral and measure form, and `μ_{h(R) u} = |h((i - λ)⁻¹)|² μ_u`.
* `IsSelfAdjoint.resolventMeasure_smul`, `IsSelfAdjoint.spectralMeasure_smul` — scaling.
* `IsSelfAdjoint.resolventMeasure_of_mem_graph`, `IsSelfAdjoint.spectralMeasure_of_mem_graph` —
  an eigenvector `A u = c u` has `ν_u^w = ‖u‖² δ_{(w - c)⁻¹}` and `μ_u = ‖u‖² δ_c`.
* `IsSelfAdjoint.resolventMeasure_add_of_mem_graph` — `ν_{x + y}^w = ν_x^w + ν_y^w` for an
  eigenvector `x` and `y ⊥ x`.
* `IsSelfAdjoint.resolventMeasure_sum_of_mem_graph`, `IsSelfAdjoint.spectralMeasure_sum_of_mem_graph`
  — for pairwise orthogonal eigenvectors `A x_i = c_i x_i`, `μ_{Σ x_i} = Σ ‖x_i‖² δ_{c_i}`.
* `IsSelfAdjoint.mem_eigenspace_iff_resolvent_apply` — `ker (A - c) = ker (R - (w - c)⁻¹)`.
* `IsSelfAdjoint.resolventMeasure_singleton`, `IsSelfAdjoint.spectralMeasure_singleton` —
  **atoms**: `μ_u {c} = ‖P u‖²` for the orthogonal projection `P` onto `ker (A - c)`; hence
  `μ_u {c} = 0 ↔ P u = 0` (`IsSelfAdjoint.spectralMeasure_singleton_eq_zero_iff`).
* `IsSelfAdjoint.resolventMeasure_intertwiner`, `IsSelfAdjoint.spectralMeasure_intertwiner` —
  **covariance**: a bounded `V` mapping the graph of `A` into the graph of `B` satisfies
  `μ^B_{V u} = μ^A_u` whenever `V† V u = u`.
* `IsSelfAdjoint.exists_finite_spectralMeasure_compl_eq_zero` — in finite dimensions the `μ_u` are
  concentrated on one finite set.
* `IsSelfAdjoint.spectralMeasure_eq_zero_of_subset_resolventSet` — `μ_u` vanishes on measurable
  sets of real points of the resolvent set; for positive `A`, `μ_u (-∞, 0) = 0`
  (`IsSelfAdjoint.spectralMeasure_Iio_zero`, `IsSelfAdjoint.ae_nonneg_spectralMeasure`).
* `IsSelfAdjoint.inner_resolvent_neg_eq_integral` — the Stieltjes representation at real points
  `-t` of the resolvent set, `⟪u, (t + A)⁻¹ u⟫ = ∫ (t + λ)⁻¹ dμ_u`, with `(t + A)⁻¹ = -(-t - A)⁻¹`;
  for positive `A` and `t > 0` the integrand is integrable
  (`IsSelfAdjoint.integrable_inv_add_spectralMeasure`).

* `IsSelfAdjoint.spectralMeasure_ofReal_smul` — for real `r ≠ 0`, the spectral measure of `r A`
  is the image of that of `A` under `λ ↦ r λ`.

## Operators of the form `T†T`

Let `T : E → F` be a real-linear operator between complex Hilbert spaces, with the real inner
products `re ⟪·, ·⟫` (`open ClosedSubmodule`), and let `A` be a self-adjoint operator with
`A = T†T` as real operators (`A.restrictScalars ℝ = T†.compNat T`); `T` is then densely defined.

* `LinearPMap.isPositive_of_restrictScalars_eq`, `IsSelfAdjoint.isPositive_of_restrictScalars_eq`
  — `A` is positive, with `re ⟪x, A x⟫ = ‖T x‖²`
  (`IsSelfAdjoint.re_inner_eq_norm_sq_of_restrictScalars_eq`).
* `IsSelfAdjoint.isLeast_re_inner_resolvent_neg` — **variational formula**: for `t > 0`,
  `re ⟪u, (t + A)⁻¹ u⟫ = max_{w ∈ dom T} (2 re ⟪u, w⟫ - t ‖w‖² - ‖T w‖²)`, attained at
  `w = (t + A)⁻¹ u` (`IsSelfAdjoint.re_inner_resolvent_neg_eq`).
* `IsSelfAdjoint.lintegral_spectralMeasure_le_norm_sq` — **form bound**: `∫ λ dμ_u ≤ ‖T u‖²` for
  `u ∈ dom T`. For closed `T` equality holds and `dom T = {u | ∫ λ dμ_u < ∞}` is the form domain;
  neither the equality nor this characterisation is formalised.
* `IsSelfAdjoint.integral_inv_add_spectralMeasure_le_of_forall_mem_graph` — **comparison of
  resolvents** (Petz): if every point `(w, w')` of the graph of a closable `S` is dominated by a
  point `(v, v')` of the graph of `T` (`‖v‖ ≤ ‖w‖`, `‖v'‖ ≤ ‖w'‖`, `re ⟪u', w⟫ ≤ re ⟪u, v⟫`), then
  `⟪u', (t + S̄†S̄)⁻¹ u'⟫ ≤ ⟪u, (t + A)⁻¹ u⟫`.
-/

@[expose] public section

open Complex MeasureTheory
open scoped ComplexConjugate LinearPMap BoundedContinuousFunction NNReal ENNReal

namespace IsSelfAdjoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A)

/-- **Transformation rule.** For `h` continuous on the spectrum of `R = (w - A)⁻¹`,
`∫ g dν_{h(R) u}^w = ∫ |h|² g dν_u^w`. -/
theorem integral_resolventMeasure_cfc_apply (w : ℂ) (u : E) {h : ℂ → ℂ}
    (hh : ContinuousOn h (spectrum ℂ (A.resolvent w))) {g : ℂ → ℝ}
    (hg : ContinuousOn g (spectrum ℂ (A.resolvent w))) :
    ∫ ζ, g ζ ∂(hA.resolventMeasure w (cfc h (A.resolvent w) u)) =
      ∫ ζ, ‖h ζ‖ ^ 2 * g ζ ∂(hA.resolventMeasure w u) := by
  have : IsStarNormal (A.resolvent w) := hA.isStarNormal_resolvent w
  have hg' : ContinuousOn (fun ζ => (g ζ : ℂ)) (spectrum ℂ (A.resolvent w)) :=
    continuous_ofReal.comp_continuousOn hg
  have e : cfc (fun ζ => ((‖h ζ‖ ^ 2 * g ζ : ℝ) : ℂ)) (A.resolvent w) =
      star (cfc h (A.resolvent w)) * (cfc (fun ζ => (g ζ : ℂ)) (A.resolvent w) *
        cfc h (A.resolvent w)) := by
    rw [← cfc_star, ← cfc_mul _ _ _ hg' hh,
      ← cfc_mul (fun x => star (h x)) (fun x => (g x : ℂ) * h x) _ hh.star (hg'.mul hh)]
    refine cfc_congr fun ζ _ => ?_
    simp only [star_def]
    rw [mul_left_comm, conj_mul']
    push_cast
    ring
  rw [hA.integral_resolventMeasure w _ hg,
    hA.integral_resolventMeasure w u (g := fun ζ => ‖h ζ‖ ^ 2 * g ζ) ((hh.norm.pow 2).mul hg), e,
    mul_apply_eq_comp, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

/-- **Transformation rule**, measure form. For `h` continuous on the spectrum of
`R = (w - A)⁻¹`, `ν_{h(R) u}^w = |h|² ν_u^w`. -/
theorem resolventMeasure_cfc_apply (w : ℂ) (u : E) {h : ℂ → ℂ}
    (hh : ContinuousOn h (spectrum ℂ (A.resolvent w))) :
    hA.resolventMeasure w (cfc h (A.resolvent w) u) =
      (hA.resolventMeasure w u).withDensity fun ζ => ‖h ζ‖ₑ ^ 2 := by
  classical
  set σ := spectrum ℂ (A.resolvent w)
  set ν := hA.resolventMeasure w u
  -- A measurable density agreeing with `‖h‖²` on the spectrum, where `ν` lives.
  let ρ : ℂ → ℝ≥0 := σ.piecewise (fun ζ => ‖h ζ‖₊ ^ 2) 0
  have hρ : Measurable ρ := (hh.nnnorm.pow 2).measurable_piecewise continuousOn_const
    (spectrum.isClosed _).measurableSet
  have hρσ : ∀ ζ ∈ σ, ρ ζ = ‖h ζ‖₊ ^ 2 := fun ζ hζ => Set.piecewise_eq_of_mem _ _ _ hζ
  have hae : (fun ζ => ‖h ζ‖ₑ ^ 2) =ᵐ[ν] fun ζ => (ρ ζ : ℝ≥0∞) := by
    filter_upwards [hA.ae_mem_spectrum_resolventMeasure w u] with ζ hζ
    rw [hρσ ζ hζ, enorm_eq_nnnorm, ENNReal.coe_pow]
  rw [withDensity_congr_ae hae]
  obtain ⟨C, hC⟩ := (spectrum.isCompact (A.resolvent w)).exists_bound_of_continuousOn hh
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
  refine (hA.eq_resolventMeasure_of_integral _ fun g => ?_).symm
  rw [integral_withDensity_eq_integral_smul hρ,
    ← hA.integral_resolventMeasure w _ g.continuous.continuousOn,
    hA.integral_resolventMeasure_cfc_apply w u hh g.continuous.continuousOn]
  refine integral_congr_ae ?_
  filter_upwards [hA.ae_mem_spectrum_resolventMeasure w u] with ζ hζ
  rw [hρσ ζ hζ, NNReal.smul_def, smul_eq_mul, NNReal.coe_pow, coe_nnnorm]

/-- **Transformation rule** for the spectral measure. For `h` continuous on the spectrum of
`R = (i - A)⁻¹`, `μ_{h(R) u} = |h((i - λ)⁻¹)|² μ_u`. -/
theorem spectralMeasure_cfc_apply (u : E) {h : ℂ → ℂ}
    (hh : ContinuousOn h (spectrum ℂ (A.resolvent I))) :
    hA.spectralMeasure (cfc h (A.resolvent I) u) =
      (hA.spectralMeasure u).withDensity fun t => ‖h (I - t)⁻¹‖ₑ ^ 2 := by
  classical
  set σ := spectrum ℂ (A.resolvent I)
  have hψ : Measurable fun t : ℝ => (I - t)⁻¹ := by fun_prop
  have hφ : Measurable fun ζ : ℂ => re (I - ζ⁻¹) := by fun_prop
  -- A measurable density agreeing with `‖h‖²` on the spectrum.
  let ρ : ℂ → ℝ≥0∞ := σ.piecewise (fun ζ => ‖h ζ‖ₑ ^ 2) 0
  have hρ : Measurable ρ :=
    ((ENNReal.continuous_pow 2).comp_continuousOn hh.enorm).measurable_piecewise continuousOn_const
    (spectrum.isClosed _).measurableSet
  have hρσ : ∀ ζ ∈ σ, ρ ζ = ‖h ζ‖ₑ ^ 2 := fun ζ hζ => Set.piecewise_eq_of_mem _ _ _ hζ
  have hν : (fun ζ => ‖h ζ‖ₑ ^ 2) =ᵐ[hA.resolventMeasure I u] ρ := by
    filter_upwards [hA.ae_mem_spectrum_resolventMeasure I u] with ζ hζ
    exact (hρσ ζ hζ).symm
  have hμ : (fun t : ℝ => ‖h (I - t)⁻¹‖ₑ ^ 2) =ᵐ[hA.spectralMeasure u] ρ ∘ fun t => (I - t)⁻¹ := by
    have := hA.ae_mem_spectrum_resolventMeasure I u
    rw [← hA.map_spectralMeasure u hA.I_mem_resolventSet] at this
    filter_upwards [ae_of_ae_map hψ.aemeasurable this] with t ht
    exact (hρσ _ ht).symm
  -- `map ψ (μ.withDensity (ρ ∘ ψ)) = (map ψ μ).withDensity ρ`.
  have hmap : ((hA.spectralMeasure u).withDensity (ρ ∘ fun t => (I - t)⁻¹)).map
      (fun t : ℝ => (I - t)⁻¹) = (hA.resolventMeasure I u).withDensity ρ := by
    ext s hs
    rw [Measure.map_apply hψ hs, withDensity_apply _ (hψ hs), withDensity_apply _ hs,
      ← hA.map_spectralMeasure u hA.I_mem_resolventSet, setLIntegral_map hs hρ hψ]
    rfl
  rw [withDensity_congr_ae hμ, spectralMeasure, hA.resolventMeasure_cfc_apply I u hh,
    withDensity_congr_ae hν, ← hmap, Measure.map_map hφ hψ]
  conv_rhs => rw [← Measure.map_id (μ := (hA.spectralMeasure u).withDensity _)]
  congr 1
  funext t
  simp only [Function.comp_apply, inv_inv, sub_sub_cancel, ofReal_re, id_eq]

/-- **Scaling.** `ν_{a u}^w = |a|² ν_u^w`. -/
theorem resolventMeasure_smul (w a : ℂ) (u : E) :
    hA.resolventMeasure w (a • u) = (‖a‖₊ ^ 2) • hA.resolventMeasure w u := by
  refine (hA.eq_resolventMeasure_of_integral _ fun g => ?_).symm
  rw [integral_smul_nnreal_measure, hA.integral_resolventMeasure w u g.continuous.continuousOn,
    NNReal.smul_def, NNReal.coe_pow, coe_nnnorm, smul_eq_mul,
    ContinuousLinearMap.map_smul, inner_smul_left, inner_smul_right, ← mul_assoc, conj_mul',
    ← ofReal_pow, re_ofReal_mul]

/-- **Scaling.** `μ_{a u} = |a|² μ_u`. -/
theorem spectralMeasure_smul (a : ℂ) (u : E) :
    hA.spectralMeasure (a • u) = (‖a‖₊ ^ 2) • hA.spectralMeasure u := by
  rw [spectralMeasure, spectralMeasure, resolventMeasure_smul, Measure.map_smul]
  exact (by fun_prop : Measurable fun ζ : ℂ => re (I - ζ⁻¹)).aemeasurable

/-- An eigenvector `A u = c u` (`c` real) has `ν_u^w = ‖u‖² δ_{(w - c)⁻¹}` for `w` in the
resolvent set. -/
theorem resolventMeasure_of_mem_graph {w : ℂ} (hw : w ∈ A.resolventSet) {u : E} {c : ℝ}
    (hu : (u, (c : ℂ) • u) ∈ A.graph) :
    hA.resolventMeasure w u = (‖u‖₊ ^ 2) • Measure.dirac (w - (c : ℂ))⁻¹ := by
  have : IsStarNormal (A.resolvent w) := hA.isStarNormal_resolvent w
  have hRu := LinearPMap.resolvent_apply_of_mem_graph hw hu
  refine (hA.eq_resolventMeasure_of_integral _ fun g => ?_).symm
  rw [integral_smul_nnreal_measure, integral_dirac, NNReal.smul_def, NNReal.coe_pow, coe_nnnorm,
    smul_eq_mul,
    ContinuousLinearMap.cfc_apply_of_apply_eq_smul this hRu (f := fun ζ => (g ζ : ℂ))
      (continuous_ofReal.comp g.continuous).continuousOn,
    inner_smul_right, inner_self_eq_norm_sq_to_K, re_ofReal_mul, mul_comm]
  norm_cast

/-- An eigenvector `A u = c u` (`c` real) has spectral measure `μ_u = ‖u‖² δ_c`. -/
theorem spectralMeasure_of_mem_graph {u : E} {c : ℝ} (hu : (u, (c : ℂ) • u) ∈ A.graph) :
    hA.spectralMeasure u = (‖u‖₊ ^ 2) • Measure.dirac c := by
  have hlam : Measurable fun ζ : ℂ => re (I - ζ⁻¹) := by fun_prop
  rw [spectralMeasure, hA.resolventMeasure_of_mem_graph hA.I_mem_resolventSet hu,
    Measure.map_smul,
    Measure.map_dirac' hlam]
  · simp
  · exact hlam.aemeasurable

/-! ### Orthogonal eigenvector decompositions -/

variable {w : ℂ}

/-- **Splitting off an eigenvector.** If `A x = c x` (`c` real) and `y ⊥ x`, then
`ν_{x + y}^w = ν_x^w + ν_y^w`: the cross terms `⟪x, g(R) y⟫` vanish because `g(R) x = g((w - c)⁻¹) x`.
-/
theorem resolventMeasure_add_of_mem_graph (hw : w ∈ A.resolventSet) {x y : E} {c : ℝ}
    (hx : (x, (c : ℂ) • x) ∈ A.graph) (hxy : inner ℂ x y = 0) :
    hA.resolventMeasure w (x + y) = hA.resolventMeasure w x + hA.resolventMeasure w y := by
  have : IsStarNormal (A.resolvent w) := hA.isStarNormal_resolvent w
  have hRx := LinearPMap.resolvent_apply_of_mem_graph hw hx
  refine (hA.eq_resolventMeasure_of_integral _ fun g => ?_).symm
  set G := cfc (fun ζ => (g ζ : ℂ)) (A.resolvent w)
  have hG : IsStarNormal G := cfc_predicate _ _
  have hg : ContinuousOn (fun ζ => (g ζ : ℂ)) (spectrum ℂ (A.resolvent w)) :=
    (continuous_ofReal.comp g.continuous).continuousOn
  -- `x` is an eigenvector of `G` and of `G†`.
  have ha := ContinuousLinearMap.cfc_apply_of_apply_eq_smul this hRx hg
  have hyx : inner ℂ y x = 0 := by rw [← inner_conj_symm, hxy, map_zero]
  have h₁ : inner ℂ x (G y) = 0 := by
    rw [← ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.IsStarNormal.adjoint_apply_eq_conj_smul hG ha, inner_smul_left, hxy,
      mul_zero]
  have h₂ : inner ℂ y (G x) = 0 := by rw [ha, inner_smul_right, hyx, mul_zero]
  rw [integral_add_measure (g.integrable _) (g.integrable _),
    hA.integral_resolventMeasure w x g.continuous.continuousOn,
    hA.integral_resolventMeasure w y g.continuous.continuousOn, ContinuousLinearMap.map_add,
    inner_add_left, inner_add_right, inner_add_right, h₁, h₂, add_zero, zero_add, add_re]

/-- **Finite eigenvector sums.** For pairwise orthogonal eigenvectors `A x_i = c_i x_i` (`c_i`
real), `ν_{Σ x_i}^w = Σ ‖x_i‖² δ_{(w - c_i)⁻¹}`. -/
theorem resolventMeasure_sum_of_mem_graph (hw : w ∈ A.resolventSet) {ι : Type*} (s : Finset ι)
    {x : ι → E} {c : ι → ℝ} (hx : ∀ i ∈ s, (x i, (c i : ℂ) • x i) ∈ A.graph)
    (horth : (s : Set ι).Pairwise fun i j => inner ℂ (x i) (x j) = 0) :
    hA.resolventMeasure w (∑ i ∈ s, x i) =
      ∑ i ∈ s, (‖x i‖₊ ^ 2) • Measure.dirac (w - (c i : ℂ))⁻¹ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hA.resolventMeasure_smul w 0 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      hA.resolventMeasure_add_of_mem_graph hw (hx a (Finset.mem_insert_self a s)),
      hA.resolventMeasure_of_mem_graph hw (hx a (Finset.mem_insert_self a s)),
      ih (fun i hi => hx i (Finset.mem_insert_of_mem hi))
        (horth.mono (by simp))]
    rw [inner_sum]
    refine Finset.sum_eq_zero fun j hj => horth (by simp) (by simp [hj]) ?_
    rintro rfl
    exact ha hj

/-- **Finite eigenvector sums.** For pairwise orthogonal eigenvectors `A x_i = c_i x_i` (`c_i`
real), the spectral measure of `Σ x_i` is `Σ ‖x_i‖² δ_{c_i}`. -/
theorem spectralMeasure_sum_of_mem_graph {ι : Type*} (s : Finset ι) {x : ι → E} {c : ι → ℝ}
    (hx : ∀ i ∈ s, (x i, (c i : ℂ) • x i) ∈ A.graph)
    (horth : (s : Set ι).Pairwise fun i j => inner ℂ (x i) (x j) = 0) :
    hA.spectralMeasure (∑ i ∈ s, x i) = ∑ i ∈ s, (‖x i‖₊ ^ 2) • Measure.dirac (c i) := by
  have hlam : Measurable fun ζ : ℂ => re (I - ζ⁻¹) := by fun_prop
  rw [spectralMeasure, hA.resolventMeasure_sum_of_mem_graph hA.I_mem_resolventSet s hx horth,
    ← Measure.mapₗ_apply_of_measurable hlam, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.mapₗ_apply_of_measurable hlam, Measure.map_smul, Measure.map_dirac' hlam]
  · simp
  · exact hlam.aemeasurable

/-! ### Atoms -/

/-- For `w` in the resolvent set, `ker (A - c) = ker ((w - A)⁻¹ - (w - c)⁻¹)`. -/
theorem mem_eigenspace_iff_resolvent_apply (hw : w ∈ A.resolventSet) {c : ℂ} {v : E} :
    v ∈ hA.isClosed.eigenspace c ↔ A.resolvent w v = (w - c)⁻¹ • v := by
  rw [LinearPMap.IsClosed.mem_eigenspace_iff]
  refine ⟨LinearPMap.resolvent_apply_of_mem_graph hw, fun h => ?_⟩
  rcases eq_or_ne (w - c) 0 with hc | hc
  · have hv : v = 0 := LinearPMap.resolvent_injective hw (by
      rw [h, hc, inv_zero, zero_smul, ContinuousLinearMap.map_zero])
    rw [hv, smul_zero]
    exact A.graph.zero_mem
  have hg := A.graph.smul_mem (w - c) (LinearPMap.resolvent_mem_graph hw v)
  rw [h, Prod.smul_mk] at hg
  convert hg using 2
  · rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
  · rw [smul_sub, smul_smul, smul_smul, ← sub_smul]
    congr 1
    field_simp
    ring

/-- The eigenspace `ker (A - c)` is the kernel of `(w - A)⁻¹ - (w - c)⁻¹`. -/
theorem toSubmodule_eigenspace_eq_ker (hw : w ∈ A.resolventSet) (c : ℂ) :
    (hA.isClosed.eigenspace c).toSubmodule =
      (A.resolvent w - algebraMap ℂ (E →L[ℂ] E) (w - c)⁻¹).ker := by
  ext v
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, sub_apply, Algebra.algebraMap_eq_smul_one, smul_apply,
    one_apply_eq_self, sub_eq_zero]
  exact hA.mem_eigenspace_iff_resolvent_apply hw

/-- **Atoms of `ν_u^w`.** For `w` in the resolvent set and `c` real,
`ν_u^w {(w - c)⁻¹} = ‖P u‖²`, where `P` is the orthogonal projection onto `ker (A - c)`. -/
theorem resolventMeasure_singleton (hw : w ∈ A.resolventSet) (u : E) (c : ℝ) :
    hA.resolventMeasure w u {(w - (c : ℂ))⁻¹} =
      ENNReal.ofReal (‖(hA.isClosed.eigenspace (c : ℂ)).toSubmodule.starProjection u‖ ^ 2) := by
  have : IsStarNormal (A.resolvent w) := hA.isStarNormal_resolvent w
  set K := (hA.isClosed.eigenspace (c : ℂ)).toSubmodule
  set T := A.resolvent w - algebraMap ℂ (E →L[ℂ] E) (w - c)⁻¹
  set x := K.starProjection u
  have hx : (x, (c : ℂ) • x) ∈ A.graph :=
    (LinearPMap.IsClosed.mem_eigenspace_iff _).mp (K.starProjection_apply_mem u)
  have hy : u - x ∈ Kᗮ := K.sub_starProjection_mem_orthogonal u
  have hxy : inner ℂ x (u - x) = 0 :=
    Submodule.inner_right_of_mem_orthogonal (K.starProjection_apply_mem u) hy
  -- `Kᗮ` is the closure of the range of the normal operator `T`, where `K = ker T`.
  have hT : IsStarNormal T := IsStarNormal.sub_algebraMap this _
  have hKperp : Kᗮ = T.range.topologicalClosure := by
    rw [show K = T.ker from hA.toSubmodule_eigenspace_eq_ker hw _,
      ← ContinuousLinearMap.IsStarNormal.ker_adjoint_eq_ker hT, ContinuousLinearMap.orthogonal_ker,
      ContinuousLinearMap.adjoint_adjoint]
  have hy0 : hA.resolventMeasure w (u - x) {(w - (c : ℂ))⁻¹} = 0 := by
    refine hA.resolventMeasure_singleton_eq_zero_of_mem_closure_range ?_
    rw [hKperp] at hy
    rwa [← SetLike.mem_coe, Submodule.topologicalClosure_coe, LinearMap.coe_range,
      ContinuousLinearMap.coe_coe] at hy
  have hsplit := hA.resolventMeasure_add_of_mem_graph hw hx hxy
  rw [add_sub_cancel] at hsplit
  rw [hsplit, Measure.add_apply, hy0, add_zero, hA.resolventMeasure_of_mem_graph hw hx,
    Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_singleton _), ENNReal.smul_def,
    smul_eq_mul, mul_one, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm,
    ENNReal.coe_pow]

/-- **Atoms of the spectral measure.** For `c` real, `μ_u {c} = ‖P u‖²`, where `P` is the
orthogonal projection onto the eigenspace `ker (A - c)`. -/
theorem spectralMeasure_singleton (u : E) (c : ℝ) :
    hA.spectralMeasure u {c} =
      ENNReal.ofReal (‖(hA.isClosed.eigenspace (c : ℂ)).toSubmodule.starProjection u‖ ^ 2) := by
  have hψ : Measurable fun t : ℝ => (I - t)⁻¹ := by fun_prop
  rw [← hA.resolventMeasure_singleton hA.I_mem_resolventSet u c,
    ← hA.map_spectralMeasure u hA.I_mem_resolventSet, Measure.map_apply hψ
      (measurableSet_singleton _)]
  congr 1
  ext t
  simp

/-- `μ_u` has no atom at `c` iff `u` is orthogonal to the eigenspace `ker (A - c)`. -/
theorem spectralMeasure_singleton_eq_zero_iff (u : E) (c : ℝ) :
    hA.spectralMeasure u {c} = 0 ↔
      (hA.isClosed.eigenspace (c : ℂ)).toSubmodule.starProjection u = 0 := by
  rw [hA.spectralMeasure_singleton, ENNReal.ofReal_eq_zero]
  constructor <;> intro h
  · exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm h (sq_nonneg _)))
  · simp [h]

/-! ### Intertwiners -/

section Intertwiners

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {B : F →ₗ.[ℂ] F} (hB : IsSelfAdjoint B) {V : E →L[ℂ] F}

/-- **Covariance under intertwiners.** Let `V` map the graph of `A` into the graph of `B`
(`V (dom A) ⊆ dom B` and `B V = V A` there). If `V† V u = u`, as for `u` in the initial space of a
partial isometry, then `ν_{V u}^w` for `B` equals `ν_u^w` for `A`. -/
theorem resolventMeasure_intertwiner (hV : ∀ u v, (u, v) ∈ A.graph → (V u, V v) ∈ B.graph)
    {w : ℂ} (hwA : w ∈ A.resolventSet) (hwB : w ∈ B.resolventSet) {u : E}
    (hVu : ContinuousLinearMap.adjoint V (V u) = u) :
    hB.resolventMeasure w (V u) = hA.resolventMeasure w u := by
  have : IsStarNormal (A.resolvent w) := hA.isStarNormal_resolvent w
  have : IsStarNormal (B.resolvent w) := hB.isStarNormal_resolvent w
  have h₁ := LinearPMap.comp_resolvent_eq_resolvent_comp hwA hwB hV
  have h₂ : V ∘L ContinuousLinearMap.adjoint (A.resolvent w) =
      ContinuousLinearMap.adjoint (B.resolvent w) ∘L V := by
    rw [hA.adjoint_resolvent hwA, hB.adjoint_resolvent hwB]
    exact LinearPMap.comp_resolvent_eq_resolvent_comp (hA.conj_mem_resolventSet hwA)
      (hB.conj_mem_resolventSet hwB) hV
  refine hA.eq_resolventMeasure_of_integral (hB.resolventMeasure w (V u)) fun g => ?_
  have hcomm := ContinuousLinearMap.comp_cfc_eq_cfc_comp ‹_› ‹_› h₁ h₂
    (f := fun ζ => (g ζ : ℂ)) (continuous_ofReal.comp g.continuous).continuousOn
    (continuous_ofReal.comp g.continuous).continuousOn
  rw [hB.integral_resolventMeasure w (V u) g.continuous.continuousOn,
    ← ContinuousLinearMap.comp_apply, ← hcomm, ContinuousLinearMap.comp_apply,
    ← ContinuousLinearMap.adjoint_inner_left, hVu]

/-- **Covariance under intertwiners.** If `V` maps the graph of `A` into the graph of `B` and
`V† V u = u`, then the spectral measure of `V u` for `B` equals that of `u` for `A`. -/
theorem spectralMeasure_intertwiner (hV : ∀ u v, (u, v) ∈ A.graph → (V u, V v) ∈ B.graph) {u : E}
    (hVu : ContinuousLinearMap.adjoint V (V u) = u) :
    hB.spectralMeasure (V u) = hA.spectralMeasure u := by
  rw [spectralMeasure, spectralMeasure,
    hA.resolventMeasure_intertwiner hB hV hA.I_mem_resolventSet hB.I_mem_resolventSet hVu]

end Intertwiners

/-! ### Support and Stieltjes representation on the real axis -/

variable {u : E}

variable (u) in
/-- `μ_u` vanishes on every measurable set of real points of the resolvent set of `A`. -/
theorem spectralMeasure_eq_zero_of_subset_resolventSet {s : Set ℝ} (hs : MeasurableSet s)
    (h : ∀ t ∈ s, (t : ℂ) ∈ A.resolventSet) : hA.spectralMeasure u s = 0 := by
  have hφ : Measurable fun ζ : ℂ => re (I - ζ⁻¹) := by fun_prop
  rw [spectralMeasure, Measure.map_apply hφ hs, measure_eq_zero_iff_ae_notMem]
  filter_upwards [hA.ae_mem_spectrum_resolventMeasure I u,
    hA.ae_ne_zero_resolventMeasure u hA.I_mem_resolventSet] with ζ hζ h0 hmem
  have him := hA.im_sub_inv_eq_zero_of_mem_spectrum hA.I_mem_resolventSet hζ h0
  have hre : ((re (I - ζ⁻¹) : ℝ) : ℂ) = I - ζ⁻¹ := Complex.ext rfl (by simpa using him.symm)
  have hz := h _ hmem
  rw [hre] at hz
  refine LinearPMap.notMem_spectrum_resolvent hA.I_mem_resolventSet hz (by simpa using h0) ?_
  rwa [sub_sub_cancel, inv_inv]

/-- On a finite-dimensional space, all the spectral measures `μ_u` are concentrated on one finite
set of real numbers: the image of the (finite) spectrum of `(i - A)⁻¹` under `ζ ↦ re (i - ζ⁻¹)`. -/
theorem exists_finite_spectralMeasure_compl_eq_zero [FiniteDimensional ℂ E] :
    ∃ F : Set ℝ, F.Finite ∧ ∀ u, hA.spectralMeasure u Fᶜ = 0 := by
  have hφ : Measurable fun ζ : ℂ => re (I - ζ⁻¹) := by fun_prop
  have hfin : (spectrum ℂ (A.resolvent I)).Finite := by
    rw [ContinuousLinearMap.spectrum_eq]
    exact Module.End.finite_spectrum _
  refine ⟨(fun ζ : ℂ => re (I - ζ⁻¹)) '' spectrum ℂ (A.resolvent I), hfin.image _, fun u => ?_⟩
  rw [spectralMeasure, Measure.map_apply hφ ((hfin.image _).measurableSet.compl)]
  exact measure_mono_null (fun ζ hζ hmem => hζ (Set.mem_image_of_mem _ hmem))
    (hA.resolventMeasure_compl_spectrum I u)

variable (u) in
/-- **Stieltjes representation at real points.** For real `-t` in the resolvent set of `A` (for
instance `t > 0` and `A` positive), `⟪u, (t + A)⁻¹ u⟫ = ∫ (t + λ)⁻¹ dμ_u(λ)`, written with
`(t + A)⁻¹ = -(-t - A)⁻¹`. In particular `⟪u, (t + A)⁻¹ u⟫` is real. -/
theorem inner_resolvent_neg_eq_integral {t : ℝ} (ht : (-t : ℂ) ∈ A.resolventSet) :
    inner ℂ u (A.resolvent (-t) u) = -((∫ s, (t + s)⁻¹ ∂(hA.spectralMeasure u) : ℝ) : ℂ) := by
  rw [hA.inner_resolvent_eq_integral u ht]
  have : ∀ s : ℝ, (-(t : ℂ) - s)⁻¹ = ((-(t + s)⁻¹ : ℝ) : ℂ) := fun s => by
    push_cast
    rw [← neg_add', inv_neg]
  simp_rw [this, integral_complex_ofReal, integral_neg, ofReal_neg]

/-! ### Positive operators -/

variable (u) in
/-- For a positive self-adjoint operator, `μ_u` has no mass on the negative half-line. -/
theorem spectralMeasure_Iio_zero (hpos : A.IsPositive) :
    hA.spectralMeasure u (Set.Iio 0) = 0 :=
  hA.spectralMeasure_eq_zero_of_subset_resolventSet u measurableSet_Iio fun t ht =>
    hpos.mem_resolventSet hA (by simpa using ht)

variable (u) in
/-- For a positive self-adjoint operator, `μ_u` is concentrated on `[0, ∞)`. -/
theorem ae_nonneg_spectralMeasure (hpos : A.IsPositive) : ∀ᵐ t ∂(hA.spectralMeasure u), 0 ≤ t := by
  have := hA.spectralMeasure_Iio_zero u hpos
  rw [measure_eq_zero_iff_ae_notMem] at this
  filter_upwards [this] with t ht
  simpa using ht

variable (u) in
/-- For a positive self-adjoint operator and `t > 0`, `λ ↦ (t + λ)⁻¹` is `μ_u`-integrable. -/
theorem integrable_inv_add_spectralMeasure (hpos : A.IsPositive) {t : ℝ} (ht : 0 < t) :
    Integrable (fun s => (t + s)⁻¹) (hA.spectralMeasure u) := by
  refine Integrable.of_bound (by fun_prop) t⁻¹ ?_
  filter_upwards [hA.ae_nonneg_spectralMeasure u hpos] with s hs
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (by linarith))]
  exact inv_anti₀ ht (by linarith)

/-! ### Scaling the operator -/

variable (u) in
/-- **Scaling the operator.** For real `r ≠ 0` and self-adjoint `A` and `r A`, the spectral measure
of `r A` at `u` is the image of that of `A` under `λ ↦ r λ`. -/
theorem spectralMeasure_ofReal_smul {r : ℝ} (hr : r ≠ 0) (hrA : IsSelfAdjoint ((r : ℂ) • A)) :
    hrA.spectralMeasure u = (hA.spectralMeasure u).map fun t => r * t := by
  set w : ℂ := (r : ℂ)⁻¹ * I
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr
  have hw : w ∈ A.resolventSet := hA.mem_resolventSet (by
    simp [w, hr])
  have : IsStarNormal (A.resolvent w) := hA.isStarNormal_resolvent w
  have hR : ((r : ℂ) • A).resolvent I = (r : ℂ)⁻¹ • A.resolvent w :=
    LinearPMap.resolvent_smul hr0 hw
  have hm : Measurable fun ζ : ℂ => (r : ℂ)⁻¹ * ζ := by fun_prop
  -- `ν^{r A, i}_u` is the image of `ν^{A, i/r}_u` under `ζ ↦ ζ / r`.
  have hν : hrA.resolventMeasure I u = (hA.resolventMeasure w u).map fun ζ => (r : ℂ)⁻¹ * ζ := by
    refine (hrA.eq_resolventMeasure_of_integral _ fun g => ?_).symm
    rw [integral_map hm.aemeasurable g.continuous.aestronglyMeasurable,
      hA.integral_resolventMeasure w u (g := fun ζ => g ((r : ℂ)⁻¹ * ζ))
        (g.continuous.comp (continuous_const.mul continuous_id)).continuousOn, hR,
      ← cfc_comp_smul (r : ℂ)⁻¹ (fun ζ => (g ζ : ℂ)) (A.resolvent w)
        (continuous_ofReal.comp g.continuous).continuousOn]
    rfl
  have hφ : Measurable fun ζ : ℂ => re (I - ζ⁻¹) := by fun_prop
  have hφw : Measurable fun ζ : ℂ => re (w - ζ⁻¹) := by fun_prop
  rw [spectralMeasure, hν, Measure.map_map hφ hm, hA.spectralMeasure_eq_map_resolventMeasure u hw,
    Measure.map_map (by fun_prop) hφw]
  congr 1
  funext ζ
  change re (I - ((r : ℂ)⁻¹ * ζ)⁻¹) = r * re ((r : ℂ)⁻¹ * I - ζ⁻¹)
  rw [mul_inv, inv_inv, sub_re, sub_re, re_ofReal_mul, ← ofReal_inv, re_ofReal_mul, I_re, mul_zero]
  ring

/-! ### Operators of the form `T†T` -/

section Form

open ClosedSubmodule

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {T : E →ₗ.[ℝ] F}

private lemma re_inner_self {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] (x : G) :
    re (inner ℂ x x) = ‖x‖ ^ 2 :=
  inner_self_eq_norm_sq (𝕜 := ℂ) x

/-- A complex operator `A` with `A = T†T` as real operators, for a densely defined real-linear
`T`, is positive. -/
theorem _root_.LinearPMap.isPositive_of_restrictScalars_eq (hTd : Dense (T.domain : Set E))
    (hAT : A.restrictScalars ℝ = T†.compNat T) : A.IsPositive := by
  have h := LinearPMap.isPositive_adjoint_compNat_self hTd
  rw [← hAT] at h
  simpa using (LinearPMap.isComplexLinear_restrictScalars A).isPositive_toComplex h

variable (hAT : A.restrictScalars ℝ = T†.compNat T)
include hAT

/-- For `A = T†T`, a point `(w, w')` of the graph of `A` factors as `w' = T† y` with `y = T w`. -/
private lemma exists_mem_graph_of_restrictScalars_eq {w w' : E} (hw : (w, w') ∈ A.graph) :
    ∃ y, (w, y) ∈ T.graph ∧ (y, w') ∈ T†.graph := by
  rw [← LinearPMap.mem_graph_restrictScalars (R := ℝ), hAT] at hw
  exact LinearPMap.mem_graph_compNat.mp hw

include hA in
/-- For self-adjoint `A = T†T`, `dom T ⊇ dom A` is dense. -/
private lemma dense_domain_of_restrictScalars_eq : Dense (T.domain : Set E) :=
  hA.dense_domain.mono fun w hw => by
    obtain ⟨y, hwy, -⟩ := exists_mem_graph_of_restrictScalars_eq hAT (A.mem_graph ⟨w, hw⟩)
    exact LinearPMap.mem_domain_of_mem_graph hwy

include hA in
/-- The form identity for `A = T†T`: `re ⟪v, A w⟫ = re ⟪T v, T w⟫` for `v ∈ dom T`, `w ∈ dom A`,
in graph form. -/
private lemma re_inner_eq_of_mem_graph {v w w' : E} {v' y : F} (hv : (v, v') ∈ T.graph)
    (hw : (w, w') ∈ A.graph) (hy : (w, y) ∈ T.graph) :
    re (inner ℂ v w') = re (inner ℂ v' y) := by
  obtain ⟨y₀, hwy₀, hyw⟩ := exists_mem_graph_of_restrictScalars_eq hAT hw
  obtain rfl : y = y₀ :=
    sub_eq_zero.mp (T.graph_fst_eq_zero_snd (T.graph.sub_mem hy hwy₀) (sub_self w))
  have := LinearPMap.inner_eq_of_mem_graph_adjoint
    (dense_domain_of_restrictScalars_eq hA hAT) hv hyw
  rw [inner_real_eq_re_inner, inner_real_eq_re_inner] at this
  rw [← inner_conj_symm, conj_re, this, ← inner_conj_symm, conj_re]

include hA in
/-- For self-adjoint `A = T†T` and `x ∈ dom A`, `re ⟪x, A x⟫ = ‖T x‖²` (in graph form). -/
theorem re_inner_eq_norm_sq_of_restrictScalars_eq {x x' : E} {y : F} (hx : (x, x') ∈ A.graph)
    (hy : (x, y) ∈ T.graph) : re (inner ℂ x x') = ‖y‖ ^ 2 := by
  rw [re_inner_eq_of_mem_graph hA hAT hy hx hy, re_inner_self]

include hA in
/-- For self-adjoint `A = T†T`, `A` is positive. -/
theorem isPositive_of_restrictScalars_eq : A.IsPositive :=
  LinearPMap.isPositive_of_restrictScalars_eq (dense_domain_of_restrictScalars_eq hA hAT) hAT

include hA in
/-- For self-adjoint `A = T†T`, `t > 0` and `r = (-t - A)⁻¹ u`, there is `y = T r`, and
`re ⟪u, v⟫ = -t re ⟪v, r⟫ - re ⟪T v, y⟫` for every `v ∈ dom T`. -/
private lemma exists_mem_graph_resolvent_neg {t : ℝ} (ht : 0 < t) (u : E) :
    ∃ y, (A.resolvent (-t) u, y) ∈ T.graph ∧ ∀ v v', (v, v') ∈ T.graph →
      re (inner ℂ u v) = -(t * re (inner ℂ v (A.resolvent (-t) u))) - re (inner ℂ v' y) := by
  have hz : (-t : ℂ) ∈ A.resolventSet :=
    (hA.isPositive_of_restrictScalars_eq hAT).mem_resolventSet hA (by simpa using ht)
  set r := A.resolvent (-t) u
  have hr : (r, -((t : ℂ) • r) - u) ∈ A.graph := by
    simpa only [neg_smul] using LinearPMap.resolvent_mem_graph hz u
  obtain ⟨y, hry, -⟩ := exists_mem_graph_of_restrictScalars_eq hAT hr
  refine ⟨y, hry, fun v v' hv => ?_⟩
  have := re_inner_eq_of_mem_graph hA hAT hv hr hry
  rw [inner_sub_right, inner_neg_right, inner_smul_right, sub_re, neg_re, re_ofReal_mul] at this
  rw [← inner_conj_symm, conj_re]
  linarith

include hA in
/-- **Value at the minimiser** of the variational formula
(`IsSelfAdjoint.isLeast_re_inner_resolvent_neg`). For self-adjoint `A = T†T`, `t > 0` and
`r = (-t - A)⁻¹ u`, `re ⟪u, r⟫ = -(t ‖r‖² + ‖T r‖²)`. -/
theorem re_inner_resolvent_neg_eq {t : ℝ} (ht : 0 < t) (u : E) {y : F}
    (hy : (A.resolvent (-t) u, y) ∈ T.graph) :
    re (inner ℂ u (A.resolvent (-t) u)) = -(t * ‖A.resolvent (-t) u‖ ^ 2 + ‖y‖ ^ 2) := by
  obtain ⟨y₀, hy₀, key⟩ := exists_mem_graph_resolvent_neg hA hAT ht u
  obtain rfl : y = y₀ :=
    sub_eq_zero.mp (T.graph_fst_eq_zero_snd (T.graph.sub_mem hy hy₀) (sub_self _))
  rw [key _ _ hy, re_inner_self, re_inner_self]
  ring

include hA in
/-- **Variational formula for the resolvent.** For self-adjoint `A = T†T`, with `T` real-linear,
and `t > 0`,
`re ⟪u, (-t - A)⁻¹ u⟫ = min_{w ∈ dom T} (t ‖w‖² + ‖T w‖² - 2 re ⟪u, w⟫)`, the minimum being
attained at `w = (t + A)⁻¹ u = -(-t - A)⁻¹ u` (`IsSelfAdjoint.re_inner_resolvent_neg_eq`).
Equivalently, `re ⟪u, (t + A)⁻¹ u⟫` is the maximum of `2 re ⟪u, w⟫ - t ‖w‖² - ‖T w‖²` over
`w ∈ dom T`. -/
theorem isLeast_re_inner_resolvent_neg {t : ℝ} (ht : 0 < t) (u : E) :
    IsLeast {x | ∃ w w', (w, w') ∈ T.graph ∧ x = t * ‖w‖ ^ 2 + ‖w'‖ ^ 2 - 2 * re (inner ℂ u w)}
      (re (inner ℂ u (A.resolvent (-t) u))) := by
  obtain ⟨y, hry, key⟩ := exists_mem_graph_resolvent_neg hA hAT ht u
  set r := A.resolvent (-t) u
  have hrr := key r y hry
  rw [re_inner_self, re_inner_self] at hrr
  refine ⟨⟨-r, -y, T.graph.neg_mem hry, ?_⟩, ?_⟩
  · rw [norm_neg, norm_neg, inner_neg_right, neg_re, hrr]
    ring
  · rintro _ ⟨w, w', hw, rfl⟩
    have hw' := key w w' hw
    have h₁ := norm_add_sq (𝕜 := ℂ) w r
    have h₂ := norm_add_sq (𝕜 := ℂ) w' y
    simp only [RCLike.re_to_complex] at h₁ h₂
    rw [hw', hrr]
    nlinarith [sq_nonneg ‖w + r‖, sq_nonneg ‖w' + y‖]

/-- **Form bound.** For self-adjoint `A = T†T`, with `T` real-linear, and `u ∈ dom T`,
`∫ λ dμ_u(λ) ≤ ‖T u‖²`. For closed `T`, `dom T` is the form domain of `A` and equality holds; the
reverse inequality, and the characterisation of the form domain as `{u | ∫ λ dμ_u < ∞}`, are not
formalised. -/
theorem lintegral_spectralMeasure_le_norm_sq {u : E} {u' : F} (hu : (u, u') ∈ T.graph) :
    ∫⁻ s, ENNReal.ofReal s ∂(hA.spectralMeasure u) ≤ ENNReal.ofReal (‖u'‖ ^ 2) := by
  have hpos := hA.isPositive_of_restrictScalars_eq hAT
  set μ := hA.spectralMeasure u
  have hnn := hA.ae_nonneg_spectralMeasure u hpos
  have hμ : μ.real Set.univ = ‖u‖ ^ 2 := by
    rw [measureReal_def, spectralMeasure_univ, ENNReal.toReal_ofReal (sq_nonneg _)]
  -- For `t > 0`, `∫ t λ / (t + λ) dμ_u ≤ ‖T u‖²`, from the variational formula at `w = u / t`.
  have hbound : ∀ t : ℝ, 0 < t →
      ∫⁻ s, ENNReal.ofReal (t * s / (t + s)) ∂μ ≤ ENNReal.ofReal (‖u'‖ ^ 2) := fun t ht => by
    have hz : (-t : ℂ) ∈ A.resolventSet := hpos.mem_resolventSet hA (by simpa using ht)
    have hint := hA.integrable_inv_add_spectralMeasure u hpos ht
    have hae : (fun s => t * s / (t + s)) =ᵐ[μ] fun s => t - t ^ 2 * (t + s)⁻¹ := by
      filter_upwards [hnn] with s hs
      have : t + s ≠ 0 := by linarith
      field_simp
      ring
    have hI : Integrable (fun s => t * s / (t + s)) μ :=
      ((integrable_const t).sub (hint.const_mul _)).congr hae.symm
    rw [← ofReal_integral_eq_lintegral_ofReal hI (by
      filter_upwards [hnn] with s hs
      exact div_nonneg (mul_nonneg ht.le hs) (by linarith))]
    refine ENNReal.ofReal_le_ofReal ?_
    have hS : ∫ s, (t + s)⁻¹ ∂μ = -re (inner ℂ u (A.resolvent (-t) u)) := by
      rw [hA.inner_resolvent_neg_eq_integral u hz, neg_re, ofReal_re, neg_neg]
    rw [integral_congr_ae hae, integral_sub (integrable_const t) (hint.const_mul _),
      integral_const, integral_const_mul, hS, hμ, smul_eq_mul]
    have hmin := (hA.isLeast_re_inner_resolvent_neg hAT ht u).2
      ⟨t⁻¹ • u, t⁻¹ • u', T.graph.smul_mem t⁻¹ hu, rfl⟩
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ht.le), ← Complex.coe_smul,
      inner_smul_right, re_ofReal_mul, re_inner_self] at hmin
    have e : t ^ 2 * (t * (t⁻¹ * ‖u‖) ^ 2 + (t⁻¹ * ‖u'‖) ^ 2 - 2 * (t⁻¹ * ‖u‖ ^ 2)) =
        ‖u'‖ ^ 2 - t * ‖u‖ ^ 2 := by
      field_simp
      ring
    nlinarith [mul_le_mul_of_nonneg_left hmin (sq_nonneg t)]
  -- Monotone convergence as `t = n + 1 → ∞`: `t λ / (t + λ) ↑ λ` for `λ ≥ 0`.
  let f : ℕ → ℝ → ℝ≥0∞ := fun n s => ENNReal.ofReal (((n : ℝ) + 1) * s / ((n + 1) + s))
  have hmono : ∀ᵐ s ∂μ, Monotone fun n => f n s := by
    filter_upwards [hnn] with s hs m n hmn
    have hmn' : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hs hs) (sub_nonneg.mpr hmn')]
  have htend : ∀ᵐ s ∂μ, Filter.Tendsto (fun n => f n s) Filter.atTop
      (nhds (ENNReal.ofReal s)) := by
    filter_upwards [hnn] with s hs
    refine ENNReal.tendsto_ofReal ?_
    have e : ∀ n : ℕ, ((n : ℝ) + 1) * s / ((n + 1) + s) = s - s ^ 2 / ((n + 1) + s) := fun n => by
      have : (n : ℝ) + 1 + s ≠ 0 := by positivity
      field_simp
      ring
    simp_rw [e]
    conv => enter [3, 1]; rw [← sub_zero s]
    exact tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop
      (Filter.tendsto_atTop_add_const_right _ s
        (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)))
  exact le_of_tendsto' (lintegral_tendsto_of_tendsto_of_monotone
    (fun n => (ENNReal.measurable_ofReal.comp (by fun_prop)).aemeasurable) hmono htend)
    fun n => hbound _ (by positivity)

include hA in
/-- **Comparison of resolvents** (Petz). Let `A = T†T` on `E` and `B = S̄†S̄` on `E'` be
self-adjoint, with `S : E' → F'` closable and real-linear, and let `u ∈ E`, `u' ∈ E'`. Suppose every
point `(w, w')` of the graph of `S` is dominated by a point `(v, v')` of the graph of `T`:
`‖v‖ ≤ ‖w‖`, `‖v'‖ ≤ ‖w'‖` and `re ⟪u', w⟫ ≤ re ⟪u, v⟫` (for instance `v = V w` for a contraction
`V` with `V† u = u'` and `‖T V w‖ ≤ ‖S w‖`). Then `∫ (t + λ)⁻¹ dμ^B_{u'} ≤ ∫ (t + λ)⁻¹ dμ^A_u` for
every `t > 0`, i.e. `⟪u', (t + B)⁻¹ u'⟫ ≤ ⟪u, (t + A)⁻¹ u⟫`.

The domination is only required on the graph of `S`, not on that of its closure: the variational
formula (`IsSelfAdjoint.isLeast_re_inner_resolvent_neg`) passes to the closure by continuity. -/
theorem integral_inv_add_spectralMeasure_le_of_forall_mem_graph
    {E' F' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']
    [NormedAddCommGroup F'] [InnerProductSpace ℂ F']
    {B : E' →ₗ.[ℂ] E'} (hB : IsSelfAdjoint B) {S : E' →ₗ.[ℝ] F'} (hS : S.IsClosable)
    (hBS : B.restrictScalars ℝ = S.closure†.compNat S.closure) (u : E) (u' : E')
    (hdom : ∀ w w', (w, w') ∈ S.graph → ∃ v v', (v, v') ∈ T.graph ∧ ‖v‖ ≤ ‖w‖ ∧ ‖v'‖ ≤ ‖w'‖ ∧
      re (inner ℂ u' w) ≤ re (inner ℂ u v))
    {t : ℝ} (ht : 0 < t) :
    ∫ s, (t + s)⁻¹ ∂(hB.spectralMeasure u') ≤ ∫ s, (t + s)⁻¹ ∂(hA.spectralMeasure u) := by
  have hzA : (-t : ℂ) ∈ A.resolventSet :=
    (hA.isPositive_of_restrictScalars_eq hAT).mem_resolventSet hA (by simpa using ht)
  have hzB : (-t : ℂ) ∈ B.resolventSet :=
    (hB.isPositive_of_restrictScalars_eq hBS).mem_resolventSet hB (by simpa using ht)
  rw [← neg_neg (∫ s, (t + s)⁻¹ ∂(hB.spectralMeasure u')),
    ← neg_neg (∫ s, (t + s)⁻¹ ∂(hA.spectralMeasure u)), neg_le_neg_iff,
    ← ofReal_re (-∫ s, (t + s)⁻¹ ∂(hA.spectralMeasure u)),
    ← ofReal_re (-∫ s, (t + s)⁻¹ ∂(hB.spectralMeasure u')), ofReal_neg, ofReal_neg,
    ← hA.inner_resolvent_neg_eq_integral u hzA, ← hB.inner_resolvent_neg_eq_integral u' hzB]
  set m := re (inner ℂ u (A.resolvent (-t) u))
  have hmA := (hA.isLeast_re_inner_resolvent_neg hAT ht u).2
  -- `m ≤ t ‖w‖² + ‖w'‖² - 2 re ⟪u', w⟫` on the graph of `S`, hence on its closure.
  have hclosed : IsClosed
      {p : E' × F' | m ≤ t * ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2 - 2 * re (inner ℂ u' p.1)} :=
    isClosed_le continuous_const (by fun_prop)
  have hsub : (S.closure.graph : Set (E' × F')) ⊆
      {p : E' × F' | m ≤ t * ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2 - 2 * re (inner ℂ u' p.1)} := by
    rw [← hS.graph_closure_eq_closure_graph, Submodule.topologicalClosure_coe]
    refine closure_minimal (fun p hp => ?_) hclosed
    obtain ⟨v, v', hv, h₁, h₂, h₃⟩ := hdom p.1 p.2 hp
    have hm := hmA ⟨v, v', hv, rfl⟩
    have h₁' := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h₁ 2) ht.le
    have h₂' := pow_le_pow_left₀ (norm_nonneg _) h₂ 2
    simp only [Set.mem_ofPred_eq]
    linarith
  obtain ⟨⟨w, w', hw, hval⟩, -⟩ := hB.isLeast_re_inner_resolvent_neg hBS ht u'
  rw [hval]
  exact hsub hw

end Form

end IsSelfAdjoint
