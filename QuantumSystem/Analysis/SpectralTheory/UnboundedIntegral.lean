/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.SpectralTheory.ProjectionValuedIntegral
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.LinearPMap.Positive
public import QuantumSystem.ForMathlib.Topology.Algebra.Module.LinearPMap.Semilinear

/-!
# Unbounded spectral integrals

Let `E` be a projection-valued measure on a measurable space `X`, acting on a complex Hilbert space
`H`. For a measurable `f : X → ℂ`, the **spectral integral** `∫ f dE`
(`ProjectionValuedMeasure.integralPMap`) is the partially defined operator with domain
`{y | f ∈ L²(E_y)}` on which `(∫ f dE) y` is the limit of the integrals of simple functions
approximating `f` (`QuantumSystem.Analysis.SpectralTheory.ProjectionValuedIntegral`); its norm is
`‖(∫ f dE) y‖² = ∫ |f|² dE_y`. For bounded `f` it is the bounded spectral integral
(`ProjectionValuedMeasure.integralPMap_eq_toPMap`).

The algebraic rules for unbounded integrals are reduced to the bounded calculus by two product
rules with a bounded measurable `g`: the diagonal measures transform as `E_{(∫ g dE) y} = |g|² E_y`,
so `(∫ f dE)(∫ g dE) y = (∫ f g dE) y` whenever `f g ∈ L²(E_y)`, and
`(∫ g dE)(∫ f dE) ⊆ ∫ g f dE`. Applied to the cutoffs `g = 1_{‖f‖ ≤ n}`, whose integrals
`E {‖f‖ ≤ n}` converge strongly to the identity, they give the adjoint formula `(∫ f dE)† = ∫ f̄ dE`
(Rudin, *Functional Analysis*, Theorem 13.24; Schmüdgen, Theorem 4.16): a vector `z` in the domain
of the adjoint satisfies `∫_{‖f‖ ≤ n} |f|² dE_z ≤ ‖(∫ f dE)† z‖²` for every `n`, hence `f ∈ L²(E_z)`
by monotone convergence. Closedness and self-adjointness for real `f` follow.

## Main definitions

* `ProjectionValuedMeasure.integralPMap E f` — the unbounded spectral integral `∫ f dE`.

## Main results

* `ProjectionValuedMeasure.mem_graph_integralPMap` — the graph of `∫ f dE`.
* `ProjectionValuedMeasure.integralPMap_eq_toPMap` — for bounded `f`, `∫ f dE` is the bounded
  integral.
* `ProjectionValuedMeasure.measure_integral_apply` — `E_{(∫ g dE) y} = |g|² E_y` for bounded `g`;
  `eLpNorm_measure_integral_apply`, `memLp_measure_integral_apply_iff` — the domain of `∫ f dE`
  after a bounded integral.
* `ProjectionValuedMeasure.integralApply_integral_apply`, `integral_integralApply` — the product
  rules `(∫ f dE)(∫ g dE) y = (∫ f g dE) y` and `(∫ g dE)(∫ f dE) y = (∫ g f dE) y` for bounded `g`.
* `ProjectionValuedMeasure.measure_integralApply`, `integralApply_integralApply`,
  `mem_graph_compNat_integralPMap`, `compNat_integralPMap_le`, `compNat_integralPMap` — the
  **product rule** `(∫ f dE)(∫ g dE) ⊆ ∫ f g dE`, with domain `dom (∫ g dE) ∩ dom (∫ f g dE)`.
* `ProjectionValuedMeasure.integral_compPMap_integralPMap_le` — bounded spectral integrals commute
  with unbounded ones.
* `ProjectionValuedMeasure.tendsto_apply_of_monotone`, `tendsto_apply_cutoff` — `E sₙ y → y` for
  measurable sets increasing to `X`, in particular for the cutoffs `{‖f‖ ≤ n}`.
* `ProjectionValuedMeasure.dense_integralDomain` — `∫ f dE` is densely defined.
* `ProjectionValuedMeasure.adjoint_integralPMap` — **adjoint**: `(∫ f dE)† = ∫ f̄ dE`.
* `ProjectionValuedMeasure.isClosed_integralPMap` — `∫ f dE` is closed.
* `ProjectionValuedMeasure.isSelfAdjoint_integralPMap`, `isSelfAdjoint_integralPMap_ofReal`,
  `isPositive_integralPMap_ofReal` — `∫ f dE` is self-adjoint for real `f`, and positive for
  `f ≥ 0`.
* `ProjectionValuedMeasure.hasCore_integralPMap` — a subspace of the domain containing all the
  spectral cutoffs `E {‖f‖ ≤ n} y` is a core.
* `ProjectionValuedMeasure.ker_integralPMap_eq_bot`, `ProjectionValuedMeasure.integralPMap_inv` —
  for `f ≠ 0` almost everywhere, `∫ f dE` is injective and `∫ f⁻¹ dE = (∫ f dE)⁻¹`
  (`LinearPMap.inverse`).
* `ProjectionValuedMeasure.integralPMap_congr_ae` — functions equal `E`-almost everywhere have the
  same integral.
* `ProjectionValuedMeasure.integralApply_map`, `integralPMap_map` — change of variables,
  `∫ f d(φ_* E) = ∫ f ∘ φ dE`.

## TODO

* The sum rule `∫ f dE + ∫ g dE ⊆ ∫ (f + g) dE` (Schmüdgen, Theorem 4.16 (ii)).
* The composition rule `∫ f d(E_{∫ g dE}) = ∫ f ∘ g dE` for the projection-valued measure of a
  normal spectral integral, which needs the spectral theorem for unbounded normal operators.

## References

* [W. Rudin, *Functional Analysis*][rudin1991], §13.22–13.24
* [K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*][schmudgen2012], §4.3
-/

@[expose] public section

open Set Filter Topology ContinuousLinearMap MeasureTheory
open scoped ENNReal NNReal InnerProductSpace ComplexConjugate LinearPMap

namespace MeasureTheory.ProjectionValuedMeasure

variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] (E : ProjectionValuedMeasure X H)

/-! ### Preliminaries -/

/-- The bounded spectral integral of a simple function is its finite sum. -/
lemma integral_simpleFunc (s : SimpleFunc X ℂ) : E.integral s = E.simpleIntegral s :=
  ContinuousLinearMap.ext_inner_self fun y => by
    rw [E.inner_integral_self s.measurable s.exists_forall_norm_le, inner_simpleIntegral_self]

/-- `‖f‖²_{L²(μ)} = ∫⁻ ‖f‖²`. -/
private lemma eLpNorm_two_sq {μ : Measure X} {f : X → ℂ} (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (p := 2) two_ne_zero hf
  simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_two] at h
  exact h

variable {f g : X → ℂ} {y : H}

/-- `‖(∫ f dE) y - (∫ g dE) y‖ = ‖f - g‖_{L²(E_y)}`. -/
lemma edist_integralApply (hf : Measurable f) (hg : Measurable g) (hfy : MemLp f 2 (E.measure y))
    (hgy : MemLp g 2 (E.measure y)) :
    edist (E.integralApply f y) (E.integralApply g y) = eLpNorm (f - g) 2 (E.measure y) := by
  rw [edist_eq_enorm_sub, ← integralApply_sub hf hg hfy hgy,
    E.enorm_integralApply (hf.sub hg) (hfy.sub hgy)]

/-- For an increasing sequence of measurable sets exhausting `X`, `E (sₙ) y → y`. -/
lemma tendsto_apply_of_monotone {s : ℕ → Set X} (hs : ∀ n, MeasurableSet (s n))
    (hmono : Monotone s) (hU : ⋃ n, s n = univ) (y : H) :
    Tendsto (fun n => E (s n) y) atTop (𝓝 y) := by
  have hc : ∀ n, ‖E (s n) y - y‖ = √((E.measure y (s n)ᶜ).toReal) := fun n => by
    have h : y - E (s n) y = E (s n)ᶜ y := by
      rw [sub_eq_iff_eq_add, ← add_apply, ← E.apply_union disjoint_compl_left (hs n).compl (hs n),
        compl_union_self, apply_univ, one_apply_eq_self]
    rw [norm_sub_rev, h, ← measureReal_def, measureReal_apply y (hs n).compl,
      Real.sqrt_sq (norm_nonneg _)]
  have hm : Tendsto (fun n => E.measure y (s n)ᶜ) atTop (𝓝 0) := by
    have := tendsto_measure_iInter_atTop (μ := E.measure y)
      (fun n => (hs n).compl.nullMeasurableSet)
      (fun m n hmn => compl_subset_compl.mpr (hmono hmn)) ⟨0, measure_ne_top _ _⟩
    rwa [← compl_iUnion, hU, compl_univ, measure_empty] at this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp_rw [hc]
  have h0 := (Real.continuous_sqrt.tendsto 0).comp ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hm)
  rw [Real.sqrt_zero] at h0
  exact h0

/-! ### Products with bounded spectral integrals -/

/-- **Transformation of the diagonal measures**: `E_{(∫ g dE) y} = |g|² E_y` for a bounded
measurable `g`. -/
lemma measure_integral_apply (hg : Measurable g) (hgb : ∃ C, ∀ x, ‖g x‖ ≤ C) (y : H) :
    E.measure (E.integral g y) = (E.measure y).withDensity fun x => ‖g x‖ₑ ^ 2 := by
  obtain ⟨C, hC⟩ := hgb
  ext s hs
  have h1 : Measurable (s.indicator (1 : X → ℂ)) := measurable_one.indicator hs
  have h1b : ∃ C, ∀ x, ‖s.indicator (1 : X → ℂ) x‖ ≤ C := ⟨1, fun x => by
    by_cases hx : x ∈ s <;> simp [hx]⟩
  have hb : ∀ x, ‖(s.indicator (1 : X → ℂ) * g) x‖ ≤ C := fun x => by
    by_cases hx : x ∈ s <;> simp [hx, (norm_nonneg _).trans (hC x), hC x]
  rw [measure_apply _ hs, withDensity_apply _ hs, ← mul_apply_eq_comp,
    ← E.integral_indicator_one hs, ← E.integral_mul h1 h1b hg ⟨C, hC⟩,
    E.integral_apply (h1.mul hg) ⟨C, hb⟩,
    E.enorm_integralApply (h1.mul hg) (E.memLp_measure_of_bound (h1.mul hg) hb y),
    eLpNorm_two_sq (h1.mul hg).aestronglyMeasurable, ← lintegral_indicator hs]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ s <;> simp [hx]

/-- `‖f‖_{L²(E_{(∫ g dE) y})} = ‖f g‖_{L²(E_y)}` for a bounded measurable `g`. -/
lemma eLpNorm_measure_integral_apply (hf : Measurable f) (hg : Measurable g)
    (hgb : ∃ C, ∀ x, ‖g x‖ ≤ C) (y : H) :
    eLpNorm f 2 (E.measure (E.integral g y)) = eLpNorm (f * g) 2 (E.measure y) := by
  refine ENNReal.rpow_left_injective (x := 2) two_ne_zero ?_
  simp only [ENNReal.rpow_two]
  rw [eLpNorm_two_sq hf.aestronglyMeasurable, eLpNorm_two_sq (hf.mul hg).aestronglyMeasurable,
    E.measure_integral_apply hg hgb,
    lintegral_withDensity_eq_lintegral_mul _ (hg.enorm.pow_const 2) (hf.enorm.pow_const 2)]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply, enorm_mul, mul_pow, mul_comm]

/-- `∫ g dE` maps `y` into the domain of `∫ f dE` iff `f g ∈ L²(E_y)`, for a bounded measurable
`g`. -/
lemma memLp_measure_integral_apply_iff (hf : Measurable f) (hg : Measurable g)
    (hgb : ∃ C, ∀ x, ‖g x‖ ≤ C) (y : H) :
    MemLp f 2 (E.measure (E.integral g y)) ↔ MemLp (f * g) 2 (E.measure y) := by
  rw [memLp_iff, memLp_iff, eLpNorm_measure_integral_apply E hf hg hgb]

/-- **Right multiplication by a bounded integral**: `(∫ f dE) (∫ g dE) y = (∫ f g dE) y` for a
bounded measurable `g` and `f g ∈ L²(E_y)`. -/
lemma integralApply_integral_apply (hf : Measurable f) (hg : Measurable g)
    (hgb : ∃ C, ∀ x, ‖g x‖ ≤ C) (hy : MemLp (f * g) 2 (E.measure y)) :
    E.integralApply f (E.integral g y) = E.integralApply (f * g) y := by
  obtain ⟨C, hC⟩ := hgb
  have hy' := (E.memLp_measure_integral_apply_iff hf hg ⟨C, hC⟩ y).mpr hy
  set a := fun n => SimpleFunc.approxOn f hf univ 0 (mem_univ 0) n
  have hab : ∀ n, ∀ x, ‖(⇑(a n) * g) x‖ ≤ (a n).exists_forall_norm_le.choose * C := fun n x => by
    rw [Pi.mul_apply, norm_mul]
    exact mul_le_mul ((a n).exists_forall_norm_le.choose_spec x) (hC x) (norm_nonneg _)
      ((norm_nonneg _).trans ((a n).exists_forall_norm_le.choose_spec x))
  suffices key : Tendsto (fun n => E.simpleIntegral (a n) (E.integral g y)) atTop
      (𝓝 (E.integralApply (f * g) y)) from
    tendsto_nhds_unique (E.tendsto_simpleIntegral_approxOn hf hy') key
  have h₁ : ∀ n, E.simpleIntegral (a n) (E.integral g y) = E.integralApply (⇑(a n) * g) y := fun n => by
    rw [← integral_simpleFunc, ← mul_apply_eq_comp, ← E.integral_mul (a n).measurable
      (a n).exists_forall_norm_le hg ⟨C, hC⟩, E.integral_apply ((a n).measurable.mul hg) ⟨_, hab n⟩]
  simp_rw [h₁]
  refine tendsto_iff_edist_tendsto_0.mpr ?_
  have h₂ : ∀ n, edist (E.integralApply (⇑(a n) * g) y) (E.integralApply (f * g) y) =
      eLpNorm (⇑(a n) - f) 2 (E.measure (E.integral g y)) := fun n => by
    rw [E.edist_integralApply ((a n).measurable.mul hg) (hf.mul hg)
      (E.memLp_measure_of_bound ((a n).measurable.mul hg) (hab n) y) hy,
      E.eLpNorm_measure_integral_apply ((a n).measurable.sub hf) hg ⟨C, hC⟩, sub_mul]
  simp_rw [h₂]
  exact E.tendsto_eLpNorm_approxOn hf hy'

/-- **Left multiplication by a bounded integral**: `(∫ g dE) (∫ f dE) y = (∫ g f dE) y` for a
bounded measurable `g` and `f ∈ L²(E_y)`. -/
lemma integral_integralApply (hf : Measurable f) (hg : Measurable g)
    (hgb : ∃ C, ∀ x, ‖g x‖ ≤ C) (hy : MemLp f 2 (E.measure y)) :
    E.integral g (E.integralApply f y) = E.integralApply (g * f) y := by
  obtain ⟨C, hC⟩ := hgb
  have hgf : MemLp (g * f) 2 (E.measure y) :=
    hy.of_le_mul (hg.mul hf).aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Pi.mul_apply, norm_mul]
      exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _))
  set a := fun n => SimpleFunc.approxOn f hf univ 0 (mem_univ 0) n
  have hab : ∀ n, ∀ x, ‖(g * ⇑(a n)) x‖ ≤ C * (a n).exists_forall_norm_le.choose := fun n x => by
    rw [Pi.mul_apply, norm_mul]
    exact mul_le_mul (hC x) ((a n).exists_forall_norm_le.choose_spec x) (norm_nonneg _)
      ((norm_nonneg _).trans (hC x))
  suffices key : Tendsto (fun n => E.integral g (E.simpleIntegral (a n) y)) atTop
      (𝓝 (E.integralApply (g * f) y)) from
    tendsto_nhds_unique (((E.integral g).continuous.tendsto _).comp
      (E.tendsto_simpleIntegral_approxOn hf hy)) key
  have h₁ : ∀ n, E.integral g (E.simpleIntegral (a n) y) = E.integralApply (g * ⇑(a n)) y :=
      fun n => by
    rw [← integral_simpleFunc, ← mul_apply_eq_comp, ← E.integral_mul hg
      ⟨C, hC⟩ (a n).measurable (a n).exists_forall_norm_le,
      E.integral_apply (hg.mul (a n).measurable) ⟨_, hab n⟩]
  simp_rw [h₁]
  refine tendsto_iff_edist_tendsto_0.mpr ?_
  have hle : ∀ n, edist (E.integralApply (g * ⇑(a n)) y) (E.integralApply (g * f) y) ≤
      C.toNNReal • eLpNorm (⇑(a n) - f) 2 (E.measure y) := fun n => by
    rw [E.edist_integralApply (hg.mul (a n).measurable) (hg.mul hf)
      (E.memLp_measure_of_bound (hg.mul (a n).measurable) (hab n) y) hgf, ← mul_sub]
    refine eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
      (hg.mul ((a n).measurable.sub hf)).aestronglyMeasurable (Eventually.of_forall fun x => ?_) 2
    rw [Pi.mul_apply, nnnorm_mul]
    gcongr
    simpa [norm_toNNReal] using Real.toNNReal_le_toNNReal (hC x)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => bot_le) hle
  have h := ENNReal.Tendsto.const_mul (E.tendsto_eLpNorm_approxOn hf hy)
    (Or.inr (ENNReal.coe_ne_top (r := C.toNNReal)))
  rw [mul_zero] at h
  simpa only [ENNReal.smul_def, smul_eq_mul] using h

/-! ### The unbounded spectral integral -/

/-- The **spectral integral** `∫ f dE` of a measurable function `f`, as a partially defined
operator with the domain `{y | f ∈ L²(E_y)}` (`ProjectionValuedMeasure.integralDomain`) on which
`(∫ f dE) y` is the limit of the integrals of simple functions approximating `f`. For a
non-measurable `f` its values are `0`. -/
noncomputable def integralPMap (f : X → ℂ) : H →ₗ.[ℂ] H where
  domain := E.integralDomain f
  toFun :=
    { toFun := fun y => E.integralApply f y
      map_add' := fun y y' => by
        by_cases hf : Measurable f
        · exact integralApply_add_right hf y.2 y'.2
        · simp [integralApply, hf]
      map_smul' := fun c y => by
        by_cases hf : Measurable f
        · exact integralApply_smul_right hf c y.2
        · simp [integralApply, hf] }

/-- The domain of `∫ f dE` is `{y | f ∈ L²(E_y)}`. -/
@[simp]
lemma integralPMap_domain (f : X → ℂ) : (E.integralPMap f).domain = E.integralDomain f := rfl

/-- `∫ f dE` acts on its domain by `integralApply`. -/
lemma integralPMap_apply (f : X → ℂ) (y : (E.integralPMap f).domain) :
    E.integralPMap f y = E.integralApply f y := rfl

/-- The graph of `∫ f dE`. -/
lemma mem_graph_integralPMap {f : X → ℂ} {y z : H} :
    (y, z) ∈ (E.integralPMap f).graph ↔ MemLp f 2 (E.measure y) ∧ E.integralApply f y = z := by
  rw [LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨w, hw, hwz⟩
    obtain rfl : (w : H) = y := hw
    exact ⟨w.2, hwz⟩
  · rintro ⟨hy, hyz⟩
    exact ⟨⟨y, hy⟩, rfl, hyz⟩

/-- For a bounded measurable `f`, `∫ f dE` is everywhere defined and is the bounded integral. -/
lemma integralPMap_eq_toPMap (hf : Measurable f) (hfb : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    E.integralPMap f = (E.integral f : H →ₗ[ℂ] H).toPMap ⊤ := by
  obtain ⟨C, hC⟩ := hfb
  refine LinearPMap.ext ?_ fun y z hyz => ?_
  · ext y
    simp only [integralPMap_domain, mem_integralDomain, E.memLp_measure_of_bound hf hC y]
    exact ⟨fun _ => Submodule.mem_top, fun _ => trivial⟩
  · change E.integralApply f y = E.integral f y
    rw [E.integral_apply hf ⟨C, hC⟩]

/-- The **spectral cutoffs** `E {x | ‖f x‖ ≤ n} y` converge to `y`. -/
lemma tendsto_apply_cutoff (hf : Measurable f) (y : H) :
    Tendsto (fun n : ℕ => E {x | ‖f x‖ ≤ n} y) atTop (𝓝 y) :=
  E.tendsto_apply_of_monotone (fun _ => measurableSet_le hf.norm measurable_const)
    (fun _ _ hmn x (hx : ‖f x‖ ≤ _) => hx.trans (Nat.cast_le.mpr hmn))
    (eq_univ_of_forall fun x => mem_iUnion.mpr ⟨⌈‖f x‖⌉₊, Nat.le_ceil _⟩) y

/-- The spectral cutoffs `E {x | ‖f x‖ ≤ n} y` lie in the domain of `∫ f dE`. -/
lemma memLp_measure_apply_cutoff (hf : Measurable f) (n : ℝ) (y : H) :
    MemLp f 2 (E.measure (E {x | ‖f x‖ ≤ n} y)) := by
  rw [measure_apply_eq_restrict (measurableSet_le hf.norm measurable_const)]
  exact MemLp.of_bound hf.aestronglyMeasurable n
    ((ae_restrict_iff' (measurableSet_le hf.norm measurable_const)).mpr
      (Eventually.of_forall fun x hx => hx))

/-- The domain of `∫ f dE` is dense. -/
lemma dense_integralDomain (hf : Measurable f) : Dense (E.integralDomain f : Set H) := fun y =>
  mem_closure_of_tendsto (E.tendsto_apply_cutoff hf y)
    (Eventually.of_forall fun n => E.memLp_measure_apply_cutoff hf n y)

/-- `E s (∫ f dE) y = (∫ 1_s f dE) y`: the cutoff of `f` by a measurable set. -/
lemma apply_integralApply (hf : Measurable f) {s : Set X} (hs : MeasurableSet s)
    (hy : MemLp f 2 (E.measure y)) :
    E s (E.integralApply f y) = E.integralApply (s.indicator f) y := by
  have h1 : Measurable (s.indicator (1 : X → ℂ)) := measurable_one.indicator hs
  have h1b : ∃ C, ∀ x, ‖s.indicator (1 : X → ℂ) x‖ ≤ C := ⟨1, fun x => by
    by_cases hx : x ∈ s <;> simp [hx]⟩
  have hmul : s.indicator (1 : X → ℂ) * f = s.indicator f := by
    ext x
    by_cases hx : x ∈ s <;> simp [hx]
  rw [← E.integral_indicator_one hs, E.integral_integralApply hf h1 h1b hy, hmul]

/-! ### Products of unbounded spectral integrals -/

/-- **Transformation of the diagonal measures**: `E_{(∫ g dE) y} = |g|² E_y` for `g ∈ L²(E_y)`. -/
lemma measure_integralApply (hg : Measurable g) (hy : MemLp g 2 (E.measure y)) :
    E.measure (E.integralApply g y) = (E.measure y).withDensity fun x => ‖g x‖ₑ ^ 2 := by
  ext s hs
  rw [measure_apply _ hs, withDensity_apply _ hs, E.apply_integralApply hg hs hy,
    E.enorm_integralApply (hg.indicator hs) (hy.indicator hs),
    eLpNorm_two_sq (hg.indicator hs).aestronglyMeasurable, ← lintegral_indicator hs]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ s <;> simp [hx]

/-- `‖f‖_{L²(E_{(∫ g dE) y})} = ‖f g‖_{L²(E_y)}` for `g ∈ L²(E_y)`. -/
lemma eLpNorm_measure_integralApply (hf : Measurable f) (hg : Measurable g)
    (hy : MemLp g 2 (E.measure y)) :
    eLpNorm f 2 (E.measure (E.integralApply g y)) = eLpNorm (f * g) 2 (E.measure y) := by
  refine ENNReal.rpow_left_injective (x := 2) two_ne_zero ?_
  simp only [ENNReal.rpow_two]
  rw [eLpNorm_two_sq hf.aestronglyMeasurable, eLpNorm_two_sq (hf.mul hg).aestronglyMeasurable,
    E.measure_integralApply hg hy,
    lintegral_withDensity_eq_lintegral_mul _ (hg.enorm.pow_const 2) (hf.enorm.pow_const 2)]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply, enorm_mul, mul_pow, mul_comm]

/-- `(∫ g dE) y` lies in the domain of `∫ f dE` iff `f g ∈ L²(E_y)`, for `g ∈ L²(E_y)`. -/
lemma memLp_measure_integralApply_iff (hf : Measurable f) (hg : Measurable g)
    (hy : MemLp g 2 (E.measure y)) :
    MemLp f 2 (E.measure (E.integralApply g y)) ↔ MemLp (f * g) 2 (E.measure y) := by
  rw [memLp_iff, memLp_iff, E.eLpNorm_measure_integralApply hf hg hy]

/-- **Product rule**: `(∫ f dE)(∫ g dE) y = (∫ f g dE) y` for `g, f g ∈ L²(E_y)`. -/
lemma integralApply_integralApply (hf : Measurable f) (hg : Measurable g)
    (hy : MemLp g 2 (E.measure y)) (hfg : MemLp (f * g) 2 (E.measure y)) :
    E.integralApply f (E.integralApply g y) = E.integralApply (f * g) y := by
  have hy' := (E.memLp_measure_integralApply_iff hf hg hy).mpr hfg
  set a := fun n => SimpleFunc.approxOn f hf univ 0 (mem_univ 0) n
  have hag : ∀ n, MemLp (⇑(a n) * g) 2 (E.measure y) := fun n =>
    hy.of_le_mul (c := (a n).exists_forall_norm_le.choose) ((a n).measurable.mul hg).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Pi.mul_apply, norm_mul]
        exact mul_le_mul_of_nonneg_right ((a n).exists_forall_norm_le.choose_spec x) (norm_nonneg _))
  suffices key : Tendsto (fun n => E.simpleIntegral (a n) (E.integralApply g y)) atTop
      (𝓝 (E.integralApply (f * g) y)) from
    tendsto_nhds_unique (E.tendsto_simpleIntegral_approxOn hf hy') key
  have h₁ : ∀ n, E.simpleIntegral (a n) (E.integralApply g y) = E.integralApply (⇑(a n) * g) y :=
    fun n => by
      rw [← integral_simpleFunc, E.integral_integralApply hg (a n).measurable
        (a n).exists_forall_norm_le hy]
  simp_rw [h₁]
  refine tendsto_iff_edist_tendsto_0.mpr ?_
  have h₂ : ∀ n, edist (E.integralApply (⇑(a n) * g) y) (E.integralApply (f * g) y) =
      eLpNorm (⇑(a n) - f) 2 (E.measure (E.integralApply g y)) := fun n => by
    rw [E.edist_integralApply ((a n).measurable.mul hg) (hf.mul hg) (hag n) hfg,
      E.eLpNorm_measure_integralApply ((a n).measurable.sub hf) hg hy, sub_mul]
  simp_rw [h₂]
  exact E.tendsto_eLpNorm_approxOn hf hy'

/-- The graph of the composite `(∫ f dE)(∫ g dE)`: it is the restriction of `∫ f g dE` to
`dom (∫ g dE) ∩ dom (∫ f g dE)`. -/
lemma mem_graph_compNat_integralPMap (hf : Measurable f) (hg : Measurable g) {y z : H} :
    (y, z) ∈ ((E.integralPMap f).compNat (E.integralPMap g)).graph ↔
      MemLp g 2 (E.measure y) ∧ MemLp (f * g) 2 (E.measure y) ∧
        E.integralApply (f * g) y = z := by
  rw [LinearPMap.mem_graph_compNat]
  constructor
  · rintro ⟨w, hyw, hwz⟩
    obtain ⟨hy, rfl⟩ := E.mem_graph_integralPMap.mp hyw
    obtain ⟨hw, rfl⟩ := E.mem_graph_integralPMap.mp hwz
    have hfg := (E.memLp_measure_integralApply_iff hf hg hy).mp hw
    exact ⟨hy, hfg, (E.integralApply_integralApply hf hg hy hfg).symm⟩
  · rintro ⟨hy, hfg, rfl⟩
    exact ⟨E.integralApply g y, E.mem_graph_integralPMap.mpr ⟨hy, rfl⟩,
      E.mem_graph_integralPMap.mpr ⟨(E.memLp_measure_integralApply_iff hf hg hy).mpr hfg,
        E.integralApply_integralApply hf hg hy hfg⟩⟩

/-- **Product rule**: `(∫ f dE)(∫ g dE) ⊆ ∫ f g dE`. -/
lemma compNat_integralPMap_le (hf : Measurable f) (hg : Measurable g) :
    (E.integralPMap f).compNat (E.integralPMap g) ≤ E.integralPMap (f * g) :=
  LinearPMap.le_of_le_graph fun ⟨y, z⟩ h => by
    obtain ⟨-, hfg, rfl⟩ := (E.mem_graph_compNat_integralPMap hf hg).mp h
    exact E.mem_graph_integralPMap.mpr ⟨hfg, rfl⟩

/-- **Product rule**, equality case: `(∫ f dE)(∫ g dE) = ∫ f g dE` when `f g ∈ L²(E_y)` forces
`g ∈ L²(E_y)`. -/
lemma compNat_integralPMap (hf : Measurable f) (hg : Measurable g)
    (hdom : ∀ y, MemLp (f * g) 2 (E.measure y) → MemLp g 2 (E.measure y)) :
    (E.integralPMap f).compNat (E.integralPMap g) = E.integralPMap (f * g) :=
  LinearPMap.eq_of_eq_graph (Submodule.ext fun ⟨y, z⟩ => by
    rw [E.mem_graph_compNat_integralPMap hf hg, E.mem_graph_integralPMap]
    exact ⟨fun ⟨_, h, hz⟩ => ⟨h, hz⟩, fun ⟨h, hz⟩ => ⟨hdom y h, h, hz⟩⟩)

/-- **Bounded integrals commute with unbounded ones**: `(∫ g dE)(∫ f dE) ⊆ (∫ f dE)(∫ g dE)`, for a
bounded measurable `g`. -/
lemma integral_compPMap_integralPMap_le (hf : Measurable f) (hg : Measurable g)
    (hgb : ∃ C, ∀ x, ‖g x‖ ≤ C) :
    (E.integral g : H →ₗ[ℂ] H).compPMap (E.integralPMap f) ≤
      (E.integralPMap f).compNat ((E.integral g : H →ₗ[ℂ] H).toPMap ⊤) := by
  -- the domain condition `g f ∈ L²(E_y)` is checked at each vector `y`
  refine LinearPMap.compPMap_le_compNat_toPMap_iff.mpr fun y z h => ?_
  simp only [ContinuousLinearMap.coe_coe]
  obtain ⟨hy, rfl⟩ := E.mem_graph_integralPMap.mp h
  obtain ⟨C, hC⟩ := hgb
  have hfg : MemLp (f * g) 2 (E.measure y) :=
    hy.of_le_mul (c := C) (hf.mul hg).aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Pi.mul_apply, norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _))
  refine E.mem_graph_integralPMap.mpr ⟨(E.memLp_measure_integral_apply_iff hf hg ⟨C, hC⟩ y).mpr hfg,
    ?_⟩
  rw [E.integralApply_integral_apply hf hg ⟨C, hC⟩ hfg, E.integral_integralApply hf hg ⟨C, hC⟩ hy,
    mul_comm]

/-! ### The adjoint -/

section Adjoint

variable (hf : Measurable f)

omit [MeasurableSpace X] in
/-- The cutoff `1_{‖f‖ ≤ n} f` is bounded by `n`. -/
private lemma norm_indicator_cutoff_le (n : ℕ) (x : X) :
    ‖{x | ‖f x‖ ≤ n}.indicator f x‖ ≤ n := by
  by_cases hx : x ∈ {x | ‖f x‖ ≤ (n : ℝ)}
  · rw [indicator_of_mem hx]
    exact hx
  · rw [indicator_of_notMem hx, norm_zero]
    exact Nat.cast_nonneg n

omit [MeasurableSpace X] in
/-- The cutoff `1_{‖f‖ ≤ n} f̄` is bounded by `n`. -/
private lemma norm_indicator_cutoff_conj_le (n : ℕ) (x : X) :
    ‖{x | ‖f x‖ ≤ n}.indicator (fun x => conj (f x)) x‖ ≤ n := by
  by_cases hx : x ∈ {x | ‖f x‖ ≤ (n : ℝ)}
  · rw [indicator_of_mem hx, Complex.norm_conj]
    exact hx
  · rw [indicator_of_notMem hx, norm_zero]
    exact Nat.cast_nonneg n

include hf in
/-- `(∫ f dE) (E s u) = (∫ 1_s f dE) u`. -/
private lemma integralApply_apply (n : ℕ) (u : H) :
    E.integralApply f (E {x | ‖f x‖ ≤ n} u) = E.integral ({x | ‖f x‖ ≤ n}.indicator f) u := by
  have hs : MeasurableSet {x | ‖f x‖ ≤ (n : ℝ)} := measurableSet_le hf.norm measurable_const
  have h1 : Measurable ({x | ‖f x‖ ≤ (n : ℝ)}.indicator (1 : X → ℂ)) := measurable_one.indicator hs
  have h1b : ∃ C, ∀ x, ‖{x | ‖f x‖ ≤ (n : ℝ)}.indicator (1 : X → ℂ) x‖ ≤ C := ⟨1, fun x => by
    by_cases hx : x ∈ {x | ‖f x‖ ≤ (n : ℝ)} <;> simp [hx]⟩
  have hmul : f * {x | ‖f x‖ ≤ (n : ℝ)}.indicator (1 : X → ℂ) = {x | ‖f x‖ ≤ (n : ℝ)}.indicator f := by
    ext x
    by_cases hx : x ∈ {x | ‖f x‖ ≤ (n : ℝ)} <;> simp [hx]
  rw [← E.integral_indicator_one hs, E.integralApply_integral_apply hf h1 h1b, hmul,
    E.integral_apply (hf.indicator hs) ⟨n, norm_indicator_cutoff_le n⟩]
  rw [hmul]
  exact E.memLp_measure_of_bound (hf.indicator hs) (norm_indicator_cutoff_le n) u

include hf in
/-- `∫ f dE` and `∫ f̄ dE` are formal adjoints: `⟪(∫ f dE) y, z⟫ = ⟪y, (∫ f̄ dE) z⟫`. -/
lemma isFormalAdjoint_integralPMap :
    (E.integralPMap f).IsFormalAdjoint (E.integralPMap fun x => conj (f x)) := by
  rintro ⟨y, hy⟩ ⟨z, hz⟩
  change ⟪E.integralApply f y, z⟫_ℂ = ⟪y, E.integralApply (fun x => conj (f x)) z⟫_ℂ
  have hcf : Measurable fun x => conj (f x) := Complex.continuous_conj.measurable.comp hf
  have hS : ∀ n : ℕ, MeasurableSet {x | ‖f x‖ ≤ (n : ℝ)} := fun n =>
    measurableSet_le hf.norm measurable_const
  have key : ∀ n : ℕ, ⟪E {x | ‖f x‖ ≤ n} (E.integralApply f y), z⟫_ℂ =
      ⟪y, E {x | ‖f x‖ ≤ n} (E.integralApply (fun x => conj (f x)) z)⟫_ℂ := fun n => by
    have hind : (fun x => conj ({x | ‖f x‖ ≤ (n : ℝ)}.indicator f x)) =
        {x | ‖f x‖ ≤ (n : ℝ)}.indicator fun x => conj (f x) := by
      ext x
      by_cases hx : x ∈ {x | ‖f x‖ ≤ (n : ℝ)} <;> simp [hx]
    rw [E.apply_integralApply hf (hS n) hy, E.apply_integralApply hcf (hS n) hz,
      ← E.integral_apply (hf.indicator (hS n)) ⟨n, norm_indicator_cutoff_le n⟩,
      ← E.integral_apply (hcf.indicator (hS n)) ⟨n, norm_indicator_cutoff_conj_le n⟩,
      ← adjoint_inner_right, ← star_eq_adjoint,
      E.star_integral (hf.indicator (hS n)) ⟨n, norm_indicator_cutoff_le n⟩, hind]
  refine tendsto_nhds_unique ((E.tendsto_apply_cutoff hf _).inner tendsto_const_nhds) ?_
  simp_rw [key]
  exact tendsto_const_nhds.inner (E.tendsto_apply_cutoff hf _)

include hf in
/-- `(∫ f dE)† ⊆ ∫ f̄ dE`: a vector in the domain of the adjoint has `f ∈ L²(E_z)`, by the
cutoffs `1_{‖f‖ ≤ n} f` and monotone convergence. -/
lemma adjoint_integralPMap_le : (E.integralPMap f)† ≤ E.integralPMap fun x => conj (f x) := by
  have hcf : Measurable fun x => conj (f x) := Complex.continuous_conj.measurable.comp hf
  have hS : ∀ n : ℕ, MeasurableSet {x | ‖f x‖ ≤ (n : ℝ)} := fun n =>
    measurableSet_le hf.norm measurable_const
  refine LinearPMap.le_of_le_graph fun ⟨z₀, w⟩ hp => ?_
  obtain ⟨⟨z, hz⟩, hzz, hw⟩ := (LinearPMap.mem_graph_iff _).mp hp
  obtain rfl : z = z₀ := hzz
  have hadj : ∀ u (hu : MemLp f 2 (E.measure u)), ⟪w, u⟫_ℂ = ⟪z, E.integralApply f u⟫_ℂ :=
    fun u hu => by
      have hw' : (E.integralPMap f)† ⟨z, hz⟩ = w := hw
      rw [← hw']
      exact LinearPMap.adjoint_isFormalAdjoint (E.dense_integralDomain hf) ⟨z, hz⟩ ⟨u, hu⟩
  -- `E sₙ w = (∫ 1_{sₙ} f̄ dE) z`
  have hPw : ∀ n : ℕ, E {x | ‖f x‖ ≤ n} w =
      E.integral ({x | ‖f x‖ ≤ n}.indicator fun x => conj (f x)) z := fun n => by
    have hind : (fun x => conj ({x | ‖f x‖ ≤ (n : ℝ)}.indicator f x)) =
        {x | ‖f x‖ ≤ (n : ℝ)}.indicator fun x => conj (f x) := by
      ext x
      by_cases hx : x ∈ {x | ‖f x‖ ≤ (n : ℝ)} <;> simp [hx]
    refine ext_inner_right ℂ fun u => ?_
    rw [inner_apply_left, hadj _ (E.memLp_measure_apply_cutoff hf n u),
      E.integralApply_apply hf n u, ← adjoint_inner_left, ← star_eq_adjoint,
      E.star_integral (hf.indicator (hS n)) ⟨n, norm_indicator_cutoff_le n⟩, hind]
  -- `f ∈ L²(E_z)`
  have hdom : MemLp (fun x => conj (f x)) 2 (E.measure z) := by
    have hle : ∀ n : ℕ, ∫⁻ x in {x | ‖f x‖ ≤ (n : ℝ)}, ‖conj (f x)‖ₑ ^ 2 ∂(E.measure z) ≤
        ‖w‖ₑ ^ 2 := fun n => by
      have h := E.enorm_integralApply (hcf.indicator (hS n))
        (E.memLp_measure_of_bound (hcf.indicator (hS n)) (norm_indicator_cutoff_conj_le n) z)
      rw [← E.integral_apply (hcf.indicator (hS n)) ⟨n, norm_indicator_cutoff_conj_le n⟩,
        ← hPw] at h
      rw [← lintegral_indicator (hS n)]
      calc ∫⁻ x, {x | ‖f x‖ ≤ (n : ℝ)}.indicator (fun x => ‖conj (f x)‖ₑ ^ 2) x ∂(E.measure z)
          = eLpNorm ({x | ‖f x‖ ≤ (n : ℝ)}.indicator fun x => conj (f x)) 2 (E.measure z) ^ 2 := by
            rw [eLpNorm_two_sq (hcf.indicator (hS n)).aestronglyMeasurable]
            refine lintegral_congr fun x => ?_
            by_cases hx : x ∈ {x | ‖f x‖ ≤ (n : ℝ)} <;> simp [hx]
        _ = ‖E {x | ‖f x‖ ≤ n} w‖ₑ ^ 2 := by rw [h]
        _ ≤ ‖w‖ₑ ^ 2 := by
            gcongr
            exact enorm_le_iff_norm_le.mpr (E.norm_apply_le _ w)
    have hU : (⋃ n : ℕ, {x | ‖f x‖ ≤ (n : ℝ)}) = univ :=
      eq_univ_of_forall fun x =>
        mem_iUnion.mpr ⟨⌈‖f x‖⌉₊, show ‖f x‖ ≤ (⌈‖f x‖⌉₊ : ℝ) from Nat.le_ceil _⟩
    have hsq : eLpNorm (fun x => conj (f x)) 2 (E.measure z) ^ 2 ≤ ‖w‖ₑ ^ 2 := by
      have hmono : Monotone fun n : ℕ => {x | ‖f x‖ ≤ (n : ℝ)} := fun m n hmn x
        (hx : ‖f x‖ ≤ (m : ℝ)) => show ‖f x‖ ≤ (n : ℝ) from hx.trans (Nat.cast_le.mpr hmn)
      rw [eLpNorm_two_sq hcf.aestronglyMeasurable, ← setLIntegral_univ, ← hU,
        setLIntegral_iUnion_of_directed _ hmono.directed_le]
      exact iSup_le hle
    refine memLp_iff.mpr (lt_top_iff_ne_top.mpr fun htop => ?_)
    rw [htop, ENNReal.top_pow two_ne_zero] at hsq
    exact (ENNReal.pow_lt_top enorm_lt_top).not_ge hsq
  rw [mem_graph_integralPMap]
  refine ⟨hdom, tendsto_nhds_unique (E.tendsto_apply_cutoff hf _) ?_⟩
  have h : ∀ n : ℕ, E {x | ‖f x‖ ≤ n} (E.integralApply (fun x => conj (f x)) z) =
      E {x | ‖f x‖ ≤ n} w := fun n => by
    rw [E.apply_integralApply hcf (hS n) hdom, hPw,
      E.integral_apply (hcf.indicator (hS n)) ⟨n, norm_indicator_cutoff_conj_le n⟩]
  simp_rw [h]
  exact E.tendsto_apply_cutoff hf w

include hf in
/-- **Adjoint**: `(∫ f dE)† = ∫ f̄ dE`. -/
theorem adjoint_integralPMap : (E.integralPMap f)† = E.integralPMap fun x => conj (f x) :=
  le_antisymm (E.adjoint_integralPMap_le hf)
    ((E.isFormalAdjoint_integralPMap hf).le_adjoint (E.dense_integralDomain hf))

include hf in
/-- `∫ f dE` is closed. -/
lemma isClosed_integralPMap : (E.integralPMap f).IsClosed := by
  have hcf : Measurable fun x => conj (f x) := Complex.continuous_conj.measurable.comp hf
  have h := E.adjoint_integralPMap hcf
  simp only [Complex.conj_conj] at h
  rw [← h]
  exact LinearPMap.adjoint_isClosed (E.dense_integralDomain hcf)

include hf in
/-- `∫ f dE` is self-adjoint for a real-valued `f`. -/
lemma isSelfAdjoint_integralPMap (hreal : ∀ x, conj (f x) = f x) :
    IsSelfAdjoint (E.integralPMap f) := by
  rw [LinearPMap.isSelfAdjoint_def, E.adjoint_integralPMap hf]
  simp_rw [hreal]

/-- `∫ φ dE` is self-adjoint for a measurable real function `φ`. -/
lemma isSelfAdjoint_integralPMap_ofReal {φ : X → ℝ} (hφ : Measurable φ) :
    IsSelfAdjoint (E.integralPMap fun x => (φ x : ℂ)) :=
  E.isSelfAdjoint_integralPMap (Complex.measurable_ofReal.comp hφ) fun _ => Complex.conj_ofReal _

include hf in
/-- `(∫ f dE) (E sₙ y) = E sₙ (∫ f dE) y` for the cutoff sets `sₙ = {‖f‖ ≤ n}`. -/
private lemma integralApply_apply_cutoff (n : ℕ) (hy : MemLp f 2 (E.measure y)) :
    E.integralApply f (E {x | ‖f x‖ ≤ n} y) = E {x | ‖f x‖ ≤ n} (E.integralApply f y) := by
  rw [E.integralApply_apply hf n y, E.apply_integralApply hf (measurableSet_le hf.norm
    measurable_const) hy, E.integral_apply (hf.indicator (measurableSet_le hf.norm
    measurable_const)) ⟨n, norm_indicator_cutoff_le n⟩]

include hf in
/-- **Spectral cutoffs form a core**: a subspace of the domain of `∫ f dE` containing the
cutoffs `E {‖f‖ ≤ n} y` of every vector `y` is a core for `∫ f dE`. -/
lemma hasCore_integralPMap {D : Submodule ℂ H} (hD : D ≤ E.integralDomain f)
    (hcut : ∀ (n : ℕ) y, E {x | ‖f x‖ ≤ n} y ∈ D) : (E.integralPMap f).HasCore D := by
  have hcl := E.isClosed_integralPMap hf
  have hKc : ((E.integralPMap f).domRestrict D).IsClosable :=
    hcl.isClosable.leIsClosable LinearPMap.domRestrict_le
  refine ⟨hD, LinearPMap.eq_of_eq_graph ?_⟩
  rw [← hKc.graph_closure_eq_closure_graph]
  refine le_antisymm (Submodule.topologicalClosure_minimal _
    (LinearPMap.le_graph_of_le LinearPMap.domRestrict_le) hcl) fun p hp => ?_
  obtain ⟨y, z⟩ := p
  obtain ⟨hy, rfl⟩ := (E.mem_graph_integralPMap).mp hp
  refine mem_closure_of_tendsto ((E.tendsto_apply_cutoff hf y).prodMk_nhds
    (E.tendsto_apply_cutoff hf _)) (Eventually.of_forall fun n => ?_)
  refine LinearPMap.mem_graph_domRestrict.mpr ⟨hcut n y, (E.mem_graph_integralPMap).mpr ⟨?_, ?_⟩⟩
  · exact E.memLp_measure_apply_cutoff hf n y
  · exact E.integralApply_apply_cutoff hf n hy

end Adjoint

/-! ### Almost everywhere equal functions -/

/-- Functions that agree `E`-almost everywhere have the same spectral integral. -/
lemma integralPMap_congr_ae (hf : Measurable f) (hg : Measurable g)
    (h : ∀ y, f =ᵐ[E.measure y] g) : E.integralPMap f = E.integralPMap g := by
  refine LinearPMap.ext ?_ fun y hy hy' => ?_
  · ext y
    exact memLp_congr_ae (h y)
  · change E.integralApply f y = E.integralApply g y
    rw [← edist_eq_zero, E.edist_integralApply hf hg hy hy']
    exact (eLpNorm_eq_zero_iff two_ne_zero).mpr ((h y).mono fun x hx => by simp [hx])

/-- `(∫ 1 dE) y = y`. -/
@[simp]
lemma integralApply_one : E.integralApply (fun _ => (1 : ℂ)) y = y := by
  rw [← E.integral_apply measurable_const ⟨1, fun _ => by simp⟩, integral_one,
    one_apply_eq_self]

/-- **Inverse**, one direction: if `f ≠ 0` `E_y`-almost everywhere, `(∫ f⁻¹ dE)(∫ f dE) y = y`. -/
private lemma mem_graph_integralPMap_inv_of_mem_graph (hf : Measurable f) {y z : H}
    (hf0 : ∀ᵐ x ∂(E.measure y), f x ≠ 0) (h : (y, z) ∈ (E.integralPMap f).graph) :
    (z, y) ∈ (E.integralPMap fun x => (f x)⁻¹).graph := by
  obtain ⟨hy, rfl⟩ := E.mem_graph_integralPMap.mp h
  have hfi : Measurable fun x => (f x)⁻¹ := hf.inv
  have hae : ((fun x => (f x)⁻¹) * f) =ᵐ[E.measure y] fun _ => (1 : ℂ) :=
    hf0.mono fun x hx => by simp [hx]
  have hmem : MemLp ((fun x => (f x)⁻¹) * f) 2 (E.measure y) :=
    (memLp_congr_ae hae).mpr (memLp_const 1)
  refine E.mem_graph_integralPMap.mpr ⟨(E.memLp_measure_integralApply_iff hfi hf hy).mpr hmem, ?_⟩
  rw [E.integralApply_integralApply hfi hf hy hmem,
    E.integralApply_congr_ae (hfi.mul hf) measurable_const hmem hae, integralApply_one]

/-- The graphs of `∫ f dE` and `∫ f⁻¹ dE` are each other's flips when `f ≠ 0` `E`-a.e. -/
private lemma mem_graph_integralPMap_inv_iff (hf : Measurable f)
    (hf0 : ∀ y, ∀ᵐ x ∂(E.measure y), f x ≠ 0) {y z : H} :
    (z, y) ∈ (E.integralPMap fun x => (f x)⁻¹).graph ↔ (y, z) ∈ (E.integralPMap f).graph := by
  refine ⟨fun h => ?_, E.mem_graph_integralPMap_inv_of_mem_graph hf (hf0 y)⟩
  have h' := E.mem_graph_integralPMap_inv_of_mem_graph hf.inv
    ((hf0 z).mono fun x hx => inv_ne_zero hx) h
  simpa using h'

/-- `∫ f dE` is injective when `f ≠ 0` `E`-almost everywhere. -/
lemma ker_integralPMap_eq_bot (hf : Measurable f) (hf0 : ∀ y, ∀ᵐ x ∂(E.measure y), f x ≠ 0) :
    (E.integralPMap f).ker = ⊥ :=
  LinearPMap.ker_eq_bot_iff_mem_graph.mpr fun _ hy =>
    (E.integralPMap fun x => (f x)⁻¹).graph_fst_eq_zero_snd
      ((E.mem_graph_integralPMap_inv_iff hf hf0).mpr hy) rfl

/-- **Inverse of a spectral integral**: if `f ≠ 0` `E`-almost everywhere, then
`∫ f⁻¹ dE = (∫ f dE)⁻¹`. -/
lemma integralPMap_inv (hf : Measurable f) (hf0 : ∀ y, ∀ᵐ x ∂(E.measure y), f x ≠ 0) :
    (E.integralPMap fun x => (f x)⁻¹) = (E.integralPMap f).inverse :=
  LinearPMap.eq_of_eq_graph (Submodule.ext fun ⟨z, y⟩ => by
    rw [LinearPMap.mem_graph_inverse_iff (E.ker_integralPMap_eq_bot hf hf0),
      E.mem_graph_integralPMap_inv_iff hf hf0])

/-! ### Positivity and change of variables -/

/-- `∫ φ dE` is positive for a nonnegative measurable real function `φ`. -/
lemma isPositive_integralPMap_ofReal {φ : X → ℝ} (hφ : Measurable φ) (hpos : ∀ x, 0 ≤ φ x) :
    (E.integralPMap fun x => (φ x : ℂ)).IsPositive := by
  refine ⟨(E.isSelfAdjoint_integralPMap_ofReal hφ).isFormalAdjoint, fun y => ?_⟩
  have hφc : Measurable fun x => (φ x : ℂ) := Complex.measurable_ofReal.comp hφ
  rw [integralPMap_apply, ← inner_conj_symm, E.inner_integralApply_self hφc y.2,
    integral_complex_ofReal]
  simpa using integral_nonneg hpos

variable {Y : Type*} [MeasurableSpace Y] {φ : Y → X}

/-- **Change of variables**: `(∫ f d(φ_* E)) y = (∫ f ∘ φ dE) y`. -/
lemma integralApply_map (hφ : Measurable φ) (E : ProjectionValuedMeasure Y H) (hf : Measurable f)
    (hy : MemLp f 2 ((E.map φ hφ).measure y)) :
    (E.map φ hφ).integralApply f y = E.integralApply (f ∘ φ) y := by
  have hy' : MemLp (f ∘ φ) 2 (E.measure y) := by
    rwa [measure_map, memLp_map_measure_iff hf.aestronglyMeasurable hφ.aemeasurable] at hy
  set a := fun n => SimpleFunc.approxOn f hf univ 0 (mem_univ 0) n
  suffices key : Tendsto (fun n => (E.map φ hφ).simpleIntegral (a n) y) atTop
      (𝓝 (E.integralApply (f ∘ φ) y)) from
    tendsto_nhds_unique ((E.map φ hφ).tendsto_simpleIntegral_approxOn hf hy) key
  have h₁ : ∀ n, (E.map φ hφ).simpleIntegral (a n) y = E.integralApply (⇑(a n) ∘ φ) y :=
    fun n => by
      rw [← integral_simpleFunc, integral_map (a n).measurable (a n).exists_forall_norm_le hφ,
        E.integral_apply ((a n).measurable.comp hφ)
          ⟨_, fun x => (a n).exists_forall_norm_le.choose_spec (φ x)⟩]
  simp_rw [h₁]
  refine tendsto_iff_edist_tendsto_0.mpr ?_
  have h₂ : ∀ n, edist (E.integralApply (⇑(a n) ∘ φ) y) (E.integralApply (f ∘ φ) y) =
      eLpNorm (⇑(a n) - f) 2 ((E.map φ hφ).measure y) := fun n => by
    rw [E.edist_integralApply ((a n).measurable.comp hφ) (hf.comp hφ)
      (E.memLp_measure_of_bound ((a n).measurable.comp hφ)
        (fun x => (a n).exists_forall_norm_le.choose_spec (φ x)) y) hy', measure_map,
      eLpNorm_map_measure ((a n).measurable.sub hf).aestronglyMeasurable hφ.aemeasurable]
    rfl
  simp_rw [h₂]
  exact (E.map φ hφ).tendsto_eLpNorm_approxOn hf hy

/-- **Change of variables**: `∫ f d(φ_* E) = ∫ f ∘ φ dE` as unbounded operators. -/
lemma integralPMap_map (hφ : Measurable φ) (E : ProjectionValuedMeasure Y H)
    (hf : Measurable f) : (E.map φ hφ).integralPMap f = E.integralPMap (f ∘ φ) := by
  have hdom : ∀ y, MemLp f 2 ((E.map φ hφ).measure y) ↔ MemLp (f ∘ φ) 2 (E.measure y) := fun y => by
    rw [measure_map, memLp_map_measure_iff hf.aestronglyMeasurable hφ.aemeasurable]
  refine LinearPMap.ext ?_ fun y hy _ => ?_
  · ext y
    exact hdom y
  · exact integralApply_map hφ E hf hy

end MeasureTheory.ProjectionValuedMeasure
