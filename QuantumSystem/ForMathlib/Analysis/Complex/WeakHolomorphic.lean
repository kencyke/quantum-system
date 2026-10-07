/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-!
# Weakly holomorphic locally bounded functions are holomorphic

Let `E` be a complex Banach space and let `φ i`, `i : ι`, be a *norming* family of continuous
linear functionals on `E`: `‖φ i‖ ≤ 1` for all `i`, and `‖x‖ ≤ C * K` whenever `‖φ i x‖ ≤ K` for
all `i`. A function `f : ℂ → E` which is locally bounded on an open set `U` and such that every
`fun z ↦ φ i (f z)` is complex differentiable on `U` is itself complex differentiable on `U`.

The proof uses Cauchy estimates, uniform in `i`, for the difference quotients
`dslope (fun z ↦ φ i (f z)) z₀` (`Complex.norm_dslope_sub_dslope_le`): the norming property turns
them into a Lipschitz bound for the difference quotients of `f` itself, which are therefore Cauchy
at `z₀`. No integration in `E` is needed.

For a general norming family local boundedness is assumed (as in Arendt–Nikolski, *Vector-valued
holomorphic functions revisited*). For the coefficients `⟪η, f z⟫` of a Hilbert-space-valued
function, and the matrix coefficients `⟪η, f z ξ⟫` of an operator-valued function on a Banach
space, it is automatic by the uniform boundedness principle (Dunford's theorem), and those versions
assume only weak holomorphy.

## Main results

* `norm_le_of_forall_norm_inner_le`: in an inner product space, `‖x‖ ≤ K` as soon as
  `‖⟪η, x⟫‖ ≤ K` for all `η` in the closed unit ball.
* `Complex.norm_dslope_sub_dslope_le`: if `g` is complex differentiable on `ball c R` and bounded
  by `M` there, then `dslope g c` is `4 * M / R ^ 2`-Lipschitz on `ball c (R / 2)`.
* `Complex.differentiableOn_of_norming_family`: a locally bounded function into a complex Banach
  space whose compositions with a norming family of functionals are holomorphic is holomorphic.
* `Complex.exists_bound_of_continuousOn_apply`, `Complex.isBoundedUnder_norm_of_continuousOn_apply`
  — uniform boundedness on compact sets of a pointwise continuous family of operators on a Banach
  space.
* `Complex.differentiableOn_of_inner`: a function into a complex Hilbert space whose matrix
  coefficients `⟪η, f z⟫` are holomorphic is holomorphic (Dunford's theorem).
* `Complex.differentiableOn_continuousLinearMap_of_inner`: an operator-valued function
  `f : ℂ → (E →L[ℂ] H)`, `E` a complex Banach and `H` a complex Hilbert space, whose matrix
  coefficients `⟪η, f z ξ⟫` are holomorphic is holomorphic in the operator norm.
* `ContinuousOn.inner_apply_of_inner`: for a bounded operator-valued function with continuous
  matrix coefficients, `z ↦ ⟪c z, T z (a z)⟫` is continuous for continuous vectors `a`, `c`.

## TODO

* Weak holomorphy for a separating (not norming) family of functionals (Arendt–Nikolski).
-/

@[expose] public section

open Set Filter Metric
open scoped Topology InnerProductSpace

/-- In an inner product space, `‖x‖ ≤ K` as soon as `‖⟪η, x⟫‖ ≤ K` for every `η` in the closed
unit ball. -/
lemma norm_le_of_forall_norm_inner_le {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] {x : H} {K : ℝ} (h : ∀ η : H, ‖η‖ ≤ 1 → ‖⟪η, x⟫_𝕜‖ ≤ K) : ‖x‖ ≤ K := by
  rcases eq_or_ne x 0 with rfl | hx
  · simpa using h 0 (by simp)
  · have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
    have key := h (((‖x‖⁻¹ : ℝ) : 𝕜) • x) (by simp [norm_smul, hx'.ne'])
    simpa [inner_smul_left, inner_self_eq_norm_sq_to_K, sq, hx'.ne'] using key

namespace Complex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Auxiliary version of `Complex.norm_dslope_sub_dslope_le` for a complete codomain. -/
private lemma norm_dslope_sub_dslope_le_aux [CompleteSpace F] {g : ℂ → F} {c z w : ℂ} {R M : ℝ}
    (hd : DifferentiableOn ℂ g (ball c R)) (hM : ∀ u ∈ ball c R, ‖g u‖ ≤ M)
    (hz : z ∈ ball c (R / 2)) (hw : w ∈ ball c (R / 2)) :
    ‖dslope g c z - dslope g c w‖ ≤ 4 * M / R ^ 2 * ‖z - w‖ := by
  have hR : 0 < R := by linarith [pos_of_mem_ball hz]
  have hcR : c ∈ ball c R := mem_ball_self hR
  -- Schwarz lemma: `‖dslope g c u‖ ≤ 2 * M / R` on `ball c R`.
  have hmaps : MapsTo g (ball c R) (closedBall (g c) (2 * M)) := fun u hu ↦ by
    rw [mem_closedBall, dist_eq_norm]
    calc ‖g u - g c‖ ≤ ‖g u‖ + ‖g c‖ := norm_sub_le _ _
      _ ≤ M + M := add_le_add (hM u hu) (hM c hcR)
      _ = 2 * M := by ring
  have hq : ∀ u ∈ ball c R, ‖dslope g c u‖ ≤ 2 * M / R := fun u hu ↦
    norm_dslope_le_div_of_mapsTo_ball hd hmaps hu
  have hqd : DifferentiableOn ℂ (dslope g c) (ball c R) :=
    (differentiableOn_dslope (ball_mem_nhds c hR)).2 hd
  -- Cauchy estimate: `‖deriv (dslope g c) u‖ ≤ 4 * M / R ^ 2` on `ball c (R / 2)`.
  have hderiv : ∀ u ∈ ball c (R / 2), ‖deriv (dslope g c) u‖ ≤ 4 * M / R ^ 2 := fun u hu ↦ by
    have hsub : closedBall u (R / 2) ⊆ ball c R := fun v hv ↦ by
      rw [mem_ball] at hu ⊢
      rw [mem_closedBall] at hv
      calc dist v c ≤ dist v u + dist u c := dist_triangle _ _ _
        _ < R / 2 + R / 2 := add_lt_add_of_le_of_lt hv hu
        _ = R := add_halves R
    calc ‖deriv (dslope g c) u‖ ≤ 2 * M / R / (R / 2) :=
          norm_deriv_le_of_forall_mem_sphere_norm_le (half_pos hR) (hqd.diffContOnCl_ball hsub)
            fun v hv ↦ hq v (hsub (sphere_subset_closedBall hv))
      _ = 4 * M / R ^ 2 := by field_simp; ring
  -- Mean value inequality on the convex set `ball c (R / 2)`.
  have hdiff : ∀ u ∈ ball c (R / 2), DifferentiableAt ℂ (dslope g c) u := fun u hu ↦
    hqd.differentiableAt (isOpen_ball.mem_nhds (ball_subset_ball (half_le_self hR.le) hu))
  exact (convex_ball c (R / 2)).norm_image_sub_le_of_norm_deriv_le hdiff hderiv hw hz

/-- **Cauchy estimate for difference quotients**: if `g` is complex differentiable on `ball c R`
and `‖g‖ ≤ M` there, then the difference quotient `dslope g c` is `4 * M / R ^ 2`-Lipschitz on the
ball `ball c (R / 2)`. The codomain need not be complete. -/
lemma norm_dslope_sub_dslope_le {g : ℂ → F} {c z w : ℂ} {R M : ℝ}
    (hd : DifferentiableOn ℂ g (ball c R)) (hM : ∀ u ∈ ball c R, ‖g u‖ ≤ M)
    (hz : z ∈ ball c (R / 2)) (hw : w ∈ ball c (R / 2)) :
    ‖dslope g c z - dslope g c w‖ ≤ 4 * M / R ^ 2 * ‖z - w‖ := by
  -- Embed `F` isometrically into its completion and apply the complete case there.
  set e : F →L[ℂ] UniformSpace.Completion F := UniformSpace.Completion.toComplL
  have hR : 0 < R := by linarith [pos_of_mem_ball hz]
  have he : ∀ u, dslope (e ∘ g) c u = e (dslope g c u) := fun u ↦
    e.dslope_comp g c u fun _ ↦ hd.differentiableAt (ball_mem_nhds c hR)
  have key := norm_dslope_sub_dslope_le_aux (g := e ∘ g) (e.differentiable.comp_differentiableOn hd)
    (fun u hu ↦ (UniformSpace.Completion.norm_coe _).trans_le (hM u hu)) hz hw
  rw [he, he, ← map_sub] at key
  exact (UniformSpace.Completion.norm_coe _).symm.trans_le key

/-- **Weakly holomorphic functions are holomorphic.** Let `E` be a complex Banach space and let
`φ : ι → StrongDual ℂ E` be a norming family of functionals: `‖φ i‖ ≤ 1` for all `i`, and
`‖x‖ ≤ C * K` whenever `‖φ i x‖ ≤ K` for all `i`. If `f : ℂ → E` is locally bounded on an open set
`U` and every `fun z ↦ φ i (f z)` is complex differentiable on `U`, then `f` is complex
differentiable on `U`. -/
theorem differentiableOn_of_norming_family [CompleteSpace E] {ι : Type*} {φ : ι → StrongDual ℂ E}
    {C : ℝ} (hφ : ∀ i, ‖φ i‖ ≤ 1) (hnorming : ∀ (x : E) (K : ℝ), (∀ i, ‖φ i x‖ ≤ K) → ‖x‖ ≤ C * K)
    {f : ℂ → E} {U : Set ℂ} (hU : IsOpen U)
    (hbdd : ∀ z ∈ U, IsBoundedUnder (· ≤ ·) (𝓝 z) fun w ↦ ‖f w‖)
    (hf : ∀ i, DifferentiableOn ℂ (fun z ↦ φ i (f z)) U) : DifferentiableOn ℂ f U := by
  intro z₀ hz₀
  -- A ball `ball z₀ R ⊆ U` on which `‖f‖ ≤ M`.
  obtain ⟨M, hM⟩ := hbdd z₀ hz₀
  obtain ⟨R, hR, hball⟩ :=
    Metric.eventually_nhds_iff_ball.1 ((hU.eventually_mem hz₀).and (eventually_map.1 hM))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hball z₀ (mem_ball_self hR)).2
  -- The difference quotients of `f` at `z₀` are uniformly Lipschitz near `z₀`.
  set K := max C 0 * (4 * M / R ^ 2) with hK
  have hK0 : 0 ≤ K := by positivity
  have hslope : ∀ i u, φ i (slope f z₀ u) = slope (fun v ↦ φ i (f v)) z₀ u := fun i u ↦ by
    simp only [slope_def_module, map_smul, map_sub]
  have hlip : ∀ z ∈ ball z₀ (R / 2), ∀ w ∈ ball z₀ (R / 2), z ≠ z₀ → w ≠ z₀ →
      ‖slope f z₀ z - slope f z₀ w‖ ≤ K * ‖z - w‖ := by
    intro z hz w hw hz0 hw0
    have hφf : ∀ i, ‖φ i (slope f z₀ z - slope f z₀ w)‖ ≤ 4 * M / R ^ 2 * ‖z - w‖ := fun i ↦ by
      have key := norm_dslope_sub_dslope_le (g := fun v ↦ φ i (f v))
        ((hf i).mono fun u hu ↦ (hball u hu).1)
        (fun u hu ↦ ((φ i).le_of_opNorm_le (hφ i) (f u)).trans (by simpa using (hball u hu).2))
        hz hw
      rwa [dslope_of_ne _ hz0, dslope_of_ne _ hw0, ← hslope, ← hslope, ← map_sub] at key
    calc ‖slope f z₀ z - slope f z₀ w‖ ≤ C * (4 * M / R ^ 2 * ‖z - w‖) := hnorming _ _ hφf
      _ ≤ max C 0 * (4 * M / R ^ 2 * ‖z - w‖) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ = K * ‖z - w‖ := by rw [hK, mul_assoc]
  -- Hence they are Cauchy as `z → z₀`, and converge in the Banach space `E`.
  have hcauchy : Cauchy (map (slope f z₀) (𝓝[≠] z₀)) := by
    refine Metric.cauchy_iff.2 ⟨inferInstance, fun ε hε ↦ ?_⟩
    set δ := min (R / 2) (ε / (2 * K + 1))
    have hδ0 : 0 < δ := lt_min (half_pos hR) (by positivity)
    refine ⟨slope f z₀ '' (ball z₀ δ \ {z₀}),
      image_mem_map (sdiff_mem_nhdsWithin_compl (ball_mem_nhds z₀ hδ0) _), ?_⟩
    rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
    have hzw : ‖z - w‖ < 2 * δ := by
      have h₁ : ‖z - z₀‖ < δ := mem_ball_iff_norm.1 hz.1
      have h₂ : ‖w - z₀‖ < δ := mem_ball_iff_norm.1 hw.1
      calc ‖z - w‖ = ‖(z - z₀) - (w - z₀)‖ := by rw [sub_sub_sub_cancel_right]
        _ ≤ ‖z - z₀‖ + ‖w - z₀‖ := norm_sub_le _ _
        _ < δ + δ := add_lt_add h₁ h₂
        _ = 2 * δ := by ring
    have hsub : ball z₀ δ ⊆ ball z₀ (R / 2) := ball_subset_ball (min_le_left _ _)
    have hlt : K * (2 * (ε / (2 * K + 1))) < ε := by
      rw [show K * (2 * (ε / (2 * K + 1))) = ε * (2 * K / (2 * K + 1)) by ring]
      exact mul_lt_of_lt_one_right hε ((div_lt_one (by positivity)).2 (by linarith))
    rw [dist_eq_norm]
    calc ‖slope f z₀ z - slope f z₀ w‖ ≤ K * ‖z - w‖ := hlip z (hsub hz.1) w (hsub hw.1) hz.2 hw.2
      _ ≤ K * (2 * δ) := mul_le_mul_of_nonneg_left hzw.le hK0
      _ ≤ K * (2 * (ε / (2 * K + 1))) := by gcongr; exact min_le_right _ _
      _ < ε := hlt
  obtain ⟨L, hL⟩ := cauchy_map_iff_exists_tendsto.1 hcauchy
  exact (hasDerivAt_iff_tendsto_slope.2 hL).differentiableAt.differentiableWithinAt

/-- **Uniform boundedness on compact sets**: a family of operators on a Banach space which is
pointwise continuous on a compact set `K` is bounded in norm on `K`. -/
lemma exists_bound_of_continuousOn_apply {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    [CompleteSpace E] {σ : ℂ →+* ℂ} [RingHomIsometric σ] {g : ℂ → E →SL[σ] G} {K : Set ℂ}
    (hK : IsCompact K) (hg : ∀ x, ContinuousOn (fun z ↦ g z x) K) : ∃ C, ∀ z ∈ K, ‖g z‖ ≤ C := by
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun z : K ↦ g z) fun x ↦ by
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hg x)
    exact ⟨C, fun z ↦ hC z z.2⟩
  exact ⟨C, fun z hz ↦ hC ⟨z, hz⟩⟩

/-- A family of operators on a Banach space which is pointwise continuous on an open set `U` is
locally bounded in norm on `U`. -/
lemma isBoundedUnder_norm_of_continuousOn_apply {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℂ G] [CompleteSpace E] {σ : ℂ →+* ℂ} [RingHomIsometric σ] {g : ℂ → E →SL[σ] G}
    {U : Set ℂ} (hU : IsOpen U) (hg : ∀ x, ContinuousOn (fun z ↦ g z x) U) :
    ∀ z ∈ U, IsBoundedUnder (· ≤ ·) (𝓝 z) fun w ↦ ‖g w‖ := fun z hz ↦ by
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hz)
  obtain ⟨C, hC⟩ := exists_bound_of_continuousOn_apply (isCompact_closedBall z r)
    fun x ↦ (hg x).mono hrU
  exact isBoundedUnder_of_eventually_le (a := C)
    (eventually_of_mem (closedBall_mem_nhds z hr) fun w hw ↦ hC w hw)

section InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Weakly holomorphic functions into a Hilbert space are holomorphic.** A function `f : ℂ → H`
into a complex Hilbert space whose coefficients `fun z ↦ ⟪η, f z⟫` are complex differentiable on
an open set `U` is complex differentiable on `U`. Local boundedness, which the proof needs, follows
from the uniform boundedness principle (Dunford's theorem). -/
theorem differentiableOn_of_inner [CompleteSpace H] {f : ℂ → H} {U : Set ℂ} (hU : IsOpen U)
    (hf : ∀ η : H, DifferentiableOn ℂ (fun z ↦ ⟪η, f z⟫_ℂ) U) : DifferentiableOn ℂ f U := by
  have hbdd : ∀ z ∈ U, IsBoundedUnder (· ≤ ·) (𝓝 z) fun w ↦ ‖f w‖ := fun z hz ↦ by
    have h := isBoundedUnder_norm_of_continuousOn_apply (E := H) (g := fun w ↦ innerSL ℂ (f w))
      hU (fun η ↦ ?_) z hz
    · simpa only [innerSL_apply_norm] using h
    · have hc := Complex.continuous_conj.comp_continuousOn (hf η).continuousOn
      refine hc.congr fun w _ ↦ ?_
      simp [innerSL_apply_apply, inner_conj_symm]
  exact differentiableOn_of_norming_family (ι := {η : H // ‖η‖ ≤ 1}) (φ := fun η ↦ innerSL ℂ η.1)
    (C := 1) (fun η ↦ by simpa using η.2)
    (fun x K hK ↦ by simpa using norm_le_of_forall_norm_inner_le fun η hη ↦ hK ⟨η, hη⟩) hU hbdd
    fun η ↦ by simpa using hf η.1

/-- **Weakly holomorphic operator-valued functions are holomorphic.** Let `E` be a complex Banach
space and `H` a complex Hilbert space. A function `f : ℂ → (E →L[ℂ] H)` whose matrix coefficients
`fun z ↦ ⟪η, f z ξ⟫` are complex differentiable on an open set `U` is complex differentiable on `U`
with respect to the operator norm; local boundedness follows from the uniform boundedness
principle. -/
theorem differentiableOn_continuousLinearMap_of_inner [CompleteSpace E] [CompleteSpace H]
    {f : ℂ → (E →L[ℂ] H)} {U : Set ℂ} (hU : IsOpen U)
    (hf : ∀ (ξ : E) (η : H), DifferentiableOn ℂ (fun z ↦ ⟪η, f z ξ⟫_ℂ) U) :
    DifferentiableOn ℂ f U := by
  have hbdd : ∀ z ∈ U, IsBoundedUnder (· ≤ ·) (𝓝 z) fun w ↦ ‖f w‖ :=
    isBoundedUnder_norm_of_continuousOn_apply hU fun ξ ↦
      (differentiableOn_of_inner hU fun η ↦ hf ξ η).continuousOn
  -- The functionals `T ↦ ⟪η, T ξ⟫` for `‖ξ‖ ≤ 1`, `‖η‖ ≤ 1` form a norming family.
  let φ : {p : E × H // ‖p.1‖ ≤ 1 ∧ ‖p.2‖ ≤ 1} → StrongDual ℂ (E →L[ℂ] H) := fun p ↦
    (innerSL ℂ p.1.2).comp (ContinuousLinearMap.apply ℂ H p.1.1)
  have hφ : ∀ p T, φ p T = ⟪p.1.2, T p.1.1⟫_ℂ := fun p T ↦ rfl
  refine differentiableOn_of_norming_family (φ := φ) (C := 1) (fun p ↦ ?_) (fun T K hK ↦ ?_) hU
    hbdd fun p ↦ by simpa only [hφ] using hf p.1.1 p.1.2
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun T ↦ ?_
    rw [hφ, one_mul]
    calc ‖⟪p.1.2, T p.1.1⟫_ℂ‖ ≤ ‖p.1.2‖ * ‖T p.1.1‖ := norm_inner_le_norm _ _
      _ ≤ 1 * (‖T‖ * 1) := mul_le_mul p.2.2 (T.le_of_opNorm_le_of_le le_rfl p.2.1) (norm_nonneg _)
          zero_le_one
      _ = ‖T‖ := by ring
  · have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK ⟨(0, 0), by simp⟩)
    rw [one_mul]
    exact T.opNorm_le_of_unit_norm hK0 fun ξ hξ ↦
      norm_le_of_forall_norm_inner_le fun η hη ↦ hK ⟨(ξ, η), hξ.le, hη⟩

end InnerProductSpace

end Complex

/-- **Weakly continuous bounded operator families.** If `T z` is bounded on `S` and its matrix
coefficients `fun z ↦ ⟪η, T z ξ⟫` are continuous on `S`, then `fun z ↦ ⟪c z, T z (a z)⟫` is
continuous on `S` for continuous vectors `a` and `c`. -/
lemma ContinuousOn.inner_apply_of_inner {α 𝕜 E F : Type*} [TopologicalSpace α] [RCLike 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    {S : Set α} {T : α → E →L[𝕜] F} {a : α → E} {c : α → F} {C : ℝ}
    (hT : ∀ (ξ : E) (η : F), ContinuousOn (fun z ↦ ⟪η, T z ξ⟫_𝕜) S) (hC : ∀ z ∈ S, ‖T z‖ ≤ C)
    (ha : ContinuousOn a S) (hc : ContinuousOn c S) :
    ContinuousOn (fun z ↦ ⟪c z, T z (a z)⟫_𝕜) S := by
  intro z₀ hz₀
  have h₃ := hT (a z₀) (c z₀) z₀ hz₀
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero] at h₃ ⊢
  have hc₀ : Tendsto (fun z ↦ ‖c z - c z₀‖) (𝓝[S] z₀) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp (hc z₀ hz₀).tendsto
  have ha₀ : Tendsto (fun z ↦ ‖a z - a z₀‖) (𝓝[S] z₀) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp (ha z₀ hz₀).tendsto
  have h₁ := hc₀.mul ((ha z₀ hz₀).tendsto.norm.const_mul C)
  have h₂ := (ha₀.const_mul C).const_mul ‖c z₀‖
  have hlim := (h₁.add h₂).add h₃
  simp only [zero_mul, mul_zero, add_zero] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hTz : ∀ x, ‖T z x‖ ≤ C * ‖x‖ := fun x ↦
    ((T z).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hC z hz) (norm_nonneg x))
  have hdecomp : ⟪c z, T z (a z)⟫_𝕜 - ⟪c z₀, T z₀ (a z₀)⟫_𝕜 =
      ⟪c z - c z₀, T z (a z)⟫_𝕜 + ⟪c z₀, T z (a z - a z₀)⟫_𝕜 +
        (⟪c z₀, T z (a z₀)⟫_𝕜 - ⟪c z₀, T z₀ (a z₀)⟫_𝕜) := by
    rw [inner_sub_left, map_sub, inner_sub_right]
    ring
  rw [norm_norm, hdecomp]
  refine (norm_add₃_le).trans (add_le_add (add_le_add ?_ ?_) le_rfl)
  · exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hTz _) (norm_nonneg _))
  · exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hTz _) (norm_nonneg _))
