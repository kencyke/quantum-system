/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import QuantumSystem.ForMathlib.MeasureTheory.VectorMeasure.ProjectionValued

/-!
# Integrals against projection-valued measures

Let `E` be a projection-valued measure on a measurable space `X`, acting on a complex Hilbert space
`H`, with diagonal measures `E_y = E.measure y`. For a simple function `s` the **spectral integral**
is the finite sum `∫ s dE = ∑_c c E (s⁻¹{c})`; it satisfies `⟪y, (∫ s dE) y⟫ = ∫ s dE_y` and
`‖(∫ s dE) y‖ = ‖s‖_{L²(E_y)}`. For a measurable `f` and a vector `y` with `f ∈ L²(E_y)`, the
vectors `(∫ sₙ dE) y` for simple functions `sₙ → f` in `L²(E_y)` form a Cauchy sequence, and its
limit `(∫ f dE) y` (`ProjectionValuedMeasure.integralApply`) does not depend on the choice of `sₙ`.
The map `y ↦ (∫ f dE) y` is linear on the subspace `{y | f ∈ L²(E_y)}`
(`ProjectionValuedMeasure.integralDomain`), and isometric from `L²(E_y)`. Polarization identifies
`⟪(∫ f dE) y, (∫ g dE) y⟫ = ∫ f̄ g dE_y`, which turns all algebraic identities into identities
between integrals against the finite measures `E_y`.

For a measurable `f` that is `E`-essentially bounded, `‖f‖ ≤ C` almost everywhere for every
diagonal measure `E_y` (equivalently, outside an `E`-null set), every vector is in the domain, and
`∫ f dE` is a bounded operator (`ProjectionValuedMeasure.integral`). It depends only on the `E`-a.e.
class of `f` (`ProjectionValuedMeasure.integral_congr_ae`), so `f ↦ ∫ f dE` is the bounded
functional calculus of `E` on `L^∞(E)` (Rudin, *Functional Analysis*, Theorem 12.21), evaluated on
measurable representatives: a unital `*`-homomorphism, contractive for the supremum norm,
continuous for bounded pointwise convergence and the strong operator topology, with
`∫ 1_s dE = E s`. The unbounded spectral integral, defined on `integralDomain f`, is built on the
same construction in `QuantumSystem.Analysis.SpectralTheory.ProjectionValuedIntegral.Unbounded`.

*Junk values.* `integral E f` is `0` when `f` is not measurable or not `E`-essentially bounded,
and `integralApply E f y` is `0` when `f` is not measurable. The algebraic rules are stated for
everywhere bounded measurable functions, the case all applications need; `integral_apply_of_ae_bound`
and `integral_congr_ae` reduce the essentially bounded case to it.

The construction uses only Bochner integrals against the finite measures `E_y`, never integrals
against the complex measures `E.complexMeasure x y`, and makes no regularity assumption on `X`.

## Main definitions

* `ProjectionValuedMeasure.simpleIntegral E s` — `∑_c c E (s⁻¹{c})` for a simple function `s`.
* `ProjectionValuedMeasure.integralDomain E f` — the subspace `{y | f ∈ L²(E_y)}`.
* `ProjectionValuedMeasure.integralApply E f y` — the vector `(∫ f dE) y`.
* `ProjectionValuedMeasure.integral E f` — the bounded operator `∫ f dE`, for measurable `f`
  essentially bounded with respect to `E` (`0` otherwise).

## Main results

* `ProjectionValuedMeasure.tendsto_simpleIntegral_apply` — `(∫ sᵢ dE) y → (∫ f dE) y` for simple
  `sᵢ → f` in `L²(E_y)`.
* `ProjectionValuedMeasure.enorm_integralApply`, `norm_integralApply_sq` — **isometry**:
  `‖(∫ f dE) y‖ = ‖f‖_{L²(E_y)}`, `‖(∫ f dE) y‖² = ∫ |f|² dE_y`.
* `ProjectionValuedMeasure.inner_integralApply_self`, `inner_integralApply` — the diagonal formula
  `⟪y, (∫ f dE) y⟫ = ∫ f dE_y` and `⟪(∫ f dE) y, (∫ g dE) y⟫ = ∫ f̄ g dE_y`.
* `ProjectionValuedMeasure.integralApply_add`, `integralApply_smul`, `integralApply_add_right`,
  `integralApply_smul_right` — linearity in `f` and in `y`.
* `ProjectionValuedMeasure.integralApply_congr_ae`, `integral_congr_ae` — the spectral integrals
  depend only on the almost-everywhere class of `f`.
* `ProjectionValuedMeasure.inner_integral_self`, `norm_integral_apply_sq`, `norm_integral_le` —
  the same for bounded `f`, and `‖∫ f dE‖ ≤ sup |f|`.
* `ProjectionValuedMeasure.integral_add`, `integral_smul`, `integral_sub`, `integral_mul`,
  `star_integral`, `integral_const`, `integral_one`, `integral_indicator_one` — `f ↦ ∫ f dE` is a
  unital `*`-homomorphism with `∫ 1_s dE = E s`.
* `ProjectionValuedMeasure.integral_mem_unitary` — `∫ f dE` is unitary when `|f| = 1`.
* `ProjectionValuedMeasure.commute_integral` — operators commuting with every `E s` commute with
  every `∫ f dE`.
* `ProjectionValuedMeasure.integral_map` — change of variables, `∫ f d(φ_* E) = ∫ f ∘ φ dE`.
* `ProjectionValuedMeasure.integral_dirac` — `∫ f dδ_a = f(a)`.
* `ProjectionValuedMeasure.tendsto_integral_apply` — **dominated convergence** in the strong
  operator topology.

## References

* [W. Rudin, *Functional Analysis*][rudin1991], §12.17–12.21
* [K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*][schmudgen2012], §4.2–4.3
-/

@[expose] public section

open Set Filter Topology ContinuousLinearMap MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace MeasureTheory.ProjectionValuedMeasure

variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] (E : ProjectionValuedMeasure X H)

/-! ### Simple functions -/

/-- The spectral integral `∑_{c ∈ range s} c E (s⁻¹{c})` of a simple function `s`. -/
noncomputable def simpleIntegral (s : SimpleFunc X ℂ) : H →L[ℂ] H :=
  ∑ c ∈ s.range, c • E (s ⁻¹' {c})

/-- `⟪y, (∫ s dE) y⟫ = ∫ s dE_y` for a simple function `s`. -/
lemma inner_simpleIntegral_self (s : SimpleFunc X ℂ) (y : H) :
    ⟪y, E.simpleIntegral s y⟫_ℂ = ∫ x, s x ∂(E.measure y) := by
  rw [← SimpleFunc.integral_eq_integral _ (SimpleFunc.integrable_of_isFiniteMeasure s),
    SimpleFunc.integral_eq, simpleIntegral, sum_apply, inner_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [smul_apply, inner_smul_right, inner_apply_self,
    measureReal_apply y (s.measurableSet_preimage _), Complex.real_smul, mul_comm]

/-- The vectors `E (s⁻¹{c}) y` for distinct values `c` of `s` are orthogonal. -/
private lemma inner_apply_preimage_eq_zero (s : SimpleFunc X ℂ) (y : H) {c d : ℂ} (hcd : c ≠ d) :
    ⟪E (s ⁻¹' {c}) y, E (s ⁻¹' {d}) y⟫_ℂ = 0 := by
  rw [inner_apply_left, ← mul_apply_eq_comp, E.mul_eq_zero_of_disjoint, zero_apply,
    inner_zero_right]
  exact Disjoint.preimage _ (Set.disjoint_singleton.mpr hcd)

/-- `‖(∫ s dE) y‖² = ∫ |s|² dE_y` for a simple function `s`. -/
lemma norm_simpleIntegral_apply_sq (s : SimpleFunc X ℂ) (y : H) :
    ‖E.simpleIntegral s y‖ ^ 2 = ∫ x, ‖s x‖ ^ 2 ∂(E.measure y) := by
  have hsq : ∀ v : H, ‖v‖ ^ 2 = (⟪v, v⟫_ℂ).re := fun v => by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have hmap : (fun x => ‖s x‖ ^ 2) = ⇑(s.map fun c => ‖c‖ ^ 2) := rfl
  rw [hmap, ← SimpleFunc.integral_eq_integral _ (SimpleFunc.integrable_of_isFiniteMeasure _),
    SimpleFunc.map_integral _ _ (SimpleFunc.integrable_of_isFiniteMeasure s) (by simp), hsq,
    simpleIntegral, sum_apply, sum_inner, Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [inner_sum, Finset.sum_eq_single c (fun d _ hdc => ?_) (fun h => absurd ‹_› h), ← hsq,
    smul_apply, norm_smul, mul_pow, measureReal_apply y (s.measurableSet_preimage _), smul_eq_mul,
    mul_comm]
  rw [smul_apply, smul_apply, inner_smul_left, inner_smul_right,
    E.inner_apply_preimage_eq_zero s y (Ne.symm hdc), mul_zero, mul_zero]

/-- The spectral integral of simple functions is additive. -/
lemma simpleIntegral_add (s t : SimpleFunc X ℂ) :
    E.simpleIntegral (s + t) = E.simpleIntegral s + E.simpleIntegral t :=
  ContinuousLinearMap.ext_inner_self fun y => by
    rw [add_apply, inner_add_right, inner_simpleIntegral_self, inner_simpleIntegral_self,
      inner_simpleIntegral_self, SimpleFunc.coe_add]
    exact integral_add (SimpleFunc.integrable_of_isFiniteMeasure s)
      (SimpleFunc.integrable_of_isFiniteMeasure t)

/-- The spectral integral of simple functions is homogeneous. -/
lemma simpleIntegral_smul (c : ℂ) (s : SimpleFunc X ℂ) :
    E.simpleIntegral (c • s) = c • E.simpleIntegral s :=
  ContinuousLinearMap.ext_inner_self fun y => by
    rw [smul_apply, inner_smul_right, inner_simpleIntegral_self, inner_simpleIntegral_self,
      SimpleFunc.coe_smul]
    exact integral_const_mul c _

/-- The spectral integral of simple functions commutes with subtraction. -/
lemma simpleIntegral_sub (s t : SimpleFunc X ℂ) :
    E.simpleIntegral (s - t) = E.simpleIntegral s - E.simpleIntegral t :=
  ContinuousLinearMap.ext_inner_self fun y => by
    rw [sub_apply, inner_sub_right, inner_simpleIntegral_self, inner_simpleIntegral_self,
      inner_simpleIntegral_self, SimpleFunc.coe_sub]
    exact integral_sub (SimpleFunc.integrable_of_isFiniteMeasure s)
      (SimpleFunc.integrable_of_isFiniteMeasure t)

/-- The `L²` seminorm of a square-integrable complex function, through the integral of `‖g‖²`. -/
private lemma eLpNorm_two_eq_ofReal_sqrt {μ : Measure X} {g : X → ℂ} (hg : MemLp g 2 μ) :
    eLpNorm g 2 μ = ENNReal.ofReal √(∫ x, ‖g x‖ ^ 2 ∂μ) := by
  rw [hg.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top, Real.sqrt_eq_rpow]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, one_div]

/-- **Isometry on simple functions**: `‖(∫ s dE) y‖ = ‖s‖_{L²(E_y)}`. -/
lemma enorm_simpleIntegral_apply (s : SimpleFunc X ℂ) (y : H) :
    ‖E.simpleIntegral s y‖ₑ = eLpNorm s 2 (E.measure y) := by
  rw [eLpNorm_two_eq_ofReal_sqrt (s.memLp_of_isFiniteMeasure 2 _), ← norm_simpleIntegral_apply_sq,
    Real.sqrt_sq (norm_nonneg _), ofReal_norm]

/-- `‖(∫ s dE) y - (∫ t dE) y‖ = ‖s - t‖_{L²(E_y)}` for simple functions `s` and `t`. -/
lemma edist_simpleIntegral_apply (s t : SimpleFunc X ℂ) (y : H) :
    edist (E.simpleIntegral s y) (E.simpleIntegral t y) = eLpNorm (⇑s - ⇑t) 2 (E.measure y) := by
  rw [edist_eq_enorm_sub, ← sub_apply, ← simpleIntegral_sub, enorm_simpleIntegral_apply,
    SimpleFunc.coe_sub]

/-! ### The domain of a spectral integral -/

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
/-- `‖a + b‖² ≤ 2 (‖a‖² + ‖b‖²)`, in `ℝ≥0∞`. -/
private lemma enorm_add_sq_le (a b : H) : ‖a + b‖ₑ ^ 2 ≤ 2 * (‖a‖ₑ ^ 2 + ‖b‖ₑ ^ 2) := by
  simp only [enorm_eq_nnnorm, ← ENNReal.coe_pow, ← ENNReal.coe_add, ← ENNReal.coe_ofNat,
    ← ENNReal.coe_mul, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, NNReal.coe_pow, NNReal.coe_add,
    NNReal.coe_mul, NNReal.coe_ofNat, coe_nnnorm]
  nlinarith [norm_add_le a b, norm_nonneg (a + b), norm_nonneg a, norm_nonneg b,
    sq_nonneg (‖a‖ - ‖b‖)]

/-- `E_{y + y'} ≤ 2 (E_y + E_{y'})`. -/
lemma measure_add_le (y y' : H) :
    E.measure (y + y') ≤ (2 : ℝ≥0∞) • (E.measure y + E.measure y') :=
  Measure.le_iff.mpr fun s hs => by
    rw [measure_apply _ hs, Measure.smul_apply, Measure.add_apply, measure_apply _ hs,
      measure_apply _ hs, map_add, smul_eq_mul]
    exact enorm_add_sq_le _ _

/-- The diagonal measure at `0` vanishes. -/
@[simp]
lemma measure_zero : E.measure 0 = 0 := by
  simpa using E.measure_smul 0 0

/-- The **domain** of the spectral integral of `f`: the vectors `y` with `f ∈ L²(E_y)`. -/
def integralDomain (f : X → ℂ) : Submodule ℂ H where
  carrier := {y | MemLp f 2 (E.measure y)}
  zero_mem' := by
    change MemLp f 2 (E.measure 0)
    rw [measure_zero]
    exact memLp_measure_zero
  add_mem' {y y'} hy hy' := by
    have hm : AEStronglyMeasurable f (E.measure y + E.measure y') :=
      hy.aestronglyMeasurable.add_measure hy'.aestronglyMeasurable
    refine MemLp.of_measure_le_smul (c := 2) (by simp) (E.measure_add_le y y') ?_
    exact (memLp_two_iff_integrable_sq_norm hm).mpr
      (((memLp_two_iff_integrable_sq_norm hy.aestronglyMeasurable).mp hy).add_measure
        ((memLp_two_iff_integrable_sq_norm hy'.aestronglyMeasurable).mp hy'))
  smul_mem' c y hy := by
    change MemLp f 2 (E.measure (c • y))
    rw [measure_smul]
    exact hy.smul_measure (by simp)

variable {E} in
/-- `y` lies in the domain of the spectral integral of `f` iff `f ∈ L²(E_y)`. -/
@[simp]
lemma mem_integralDomain {f : X → ℂ} {y : H} : y ∈ E.integralDomain f ↔ MemLp f 2 (E.measure y) :=
  Iff.rfl

/-! ### The spectral integral as a limit of simple functions -/

open Classical in
/-- The vector `(∫ f dE) y`, for a measurable `f` and `y` with `f ∈ L²(E_y)`: the limit of
`(∫ sₙ dE) y` for the simple functions `sₙ = SimpleFunc.approxOn f …` approximating `f`
(`tendsto_simpleIntegral_approxOn`), or for any simple functions converging to `f` in
`L²(E_y)` (`tendsto_simpleIntegral_apply`). It is `0` for a non-measurable `f`, and has no
meaning when `f ∉ L²(E_y)`. -/
noncomputable def integralApply (f : X → ℂ) (y : H) : H :=
  if hf : Measurable f then
    limUnder atTop fun n => E.simpleIntegral (SimpleFunc.approxOn f hf univ 0 (mem_univ 0) n) y
  else 0

section Limit

variable {f g : X → ℂ} (hf : Measurable f) {y : H}

include hf in
/-- The simple functions `SimpleFunc.approxOn f …` converge to `f` in `L²(E_y)`. -/
lemma tendsto_eLpNorm_approxOn (hy : MemLp f 2 (E.measure y)) :
    Tendsto (fun n => eLpNorm (⇑(SimpleFunc.approxOn f hf univ 0 (mem_univ 0) n) - f) 2
      (E.measure y)) atTop (𝓝 0) :=
  SimpleFunc.tendsto_approxOn_Lp_eLpNorm hf (mem_univ 0) ENNReal.ofNat_ne_top (by simp)
    (by simpa using hy.eLpNorm_lt_top)

include hf in
private lemma edist_simpleIntegral_approxOn_le (s : SimpleFunc X ℂ) (n : ℕ) :
    edist (E.simpleIntegral s y)
        (E.simpleIntegral (SimpleFunc.approxOn f hf univ 0 (mem_univ 0) n) y) ≤
      eLpNorm (⇑s - f) 2 (E.measure y) +
        eLpNorm (⇑(SimpleFunc.approxOn f hf univ 0 (mem_univ 0) n) - f) 2 (E.measure y) := by
  rw [edist_simpleIntegral_apply, ← sub_add_sub_cancel _ f]
  exact (eLpNorm_add_le one_le_two).trans_eq (by rw [eLpNorm_sub_comm f])

include hf in
/-- `(∫ f dE) y` is the limit of `(∫ sₙ dE) y` for the simple functions
`sₙ = SimpleFunc.approxOn f …`. -/
lemma tendsto_simpleIntegral_approxOn (hy : MemLp f 2 (E.measure y)) :
    Tendsto (fun n => E.simpleIntegral (SimpleFunc.approxOn f hf univ 0 (mem_univ 0) n) y) atTop
      (𝓝 (E.integralApply f y)) := by
  have hc : CauchySeq fun n =>
      E.simpleIntegral (SimpleFunc.approxOn f hf univ 0 (mem_univ 0) n) y := by
    rw [EMetric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      ((E.tendsto_eLpNorm_approxOn hf hy).eventually (gt_mem_nhds (ENNReal.half_pos hε.ne')))
    refine ⟨N, fun n hn => ?_⟩
    calc _ ≤ _ := E.edist_simpleIntegral_approxOn_le hf _ N
      _ < ε / 2 + ε / 2 := ENNReal.add_lt_add (hN n hn) (hN N le_rfl)
      _ = ε := ENNReal.add_halves ε
  simp only [integralApply, hf, ↓reduceDIte]
  exact tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete hc)

include hf in
/-- `‖(∫ s dE) y - (∫ f dE) y‖ ≤ ‖s - f‖_{L²(E_y)}` for a simple function `s`. -/
lemma edist_simpleIntegral_integralApply_le (hy : MemLp f 2 (E.measure y)) (s : SimpleFunc X ℂ) :
    edist (E.simpleIntegral s y) (E.integralApply f y) ≤ eLpNorm (⇑s - f) 2 (E.measure y) := by
  refine le_of_tendsto_of_tendsto' (tendsto_const_nhds.edist
    (E.tendsto_simpleIntegral_approxOn hf hy)) ?_ fun n => E.edist_simpleIntegral_approxOn_le hf s n
  simpa using tendsto_const_nhds.add (E.tendsto_eLpNorm_approxOn hf hy)

include hf in
/-- `(∫ f dE) y` is the limit of `(∫ sᵢ dE) y` for any simple functions `sᵢ` converging to `f` in
`L²(E_y)`. -/
lemma tendsto_simpleIntegral_apply (hy : MemLp f 2 (E.measure y)) {ι : Type*} {l : Filter ι}
    {s : ι → SimpleFunc X ℂ} (hs : Tendsto (fun i => eLpNorm (⇑(s i) - f) 2 (E.measure y)) l (𝓝 0)) :
    Tendsto (fun i => E.simpleIntegral (s i) y) l (𝓝 (E.integralApply f y)) :=
  tendsto_iff_edist_tendsto_0.mpr (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs
    (fun _ => bot_le) fun i => E.edist_simpleIntegral_integralApply_le hf hy (s i))

/-- The spectral integral of the zero simple function vanishes. -/
@[simp]
lemma simpleIntegral_zero : E.simpleIntegral (0 : SimpleFunc X ℂ) = 0 :=
  ContinuousLinearMap.ext_inner_self fun y => by simp [inner_simpleIntegral_self]

variable {E} in
include hf in
/-- **Additivity** of `f ↦ (∫ f dE) y` on `L²(E_y)`. -/
lemma integralApply_add (hg : Measurable g) (hfy : MemLp f 2 (E.measure y))
    (hgy : MemLp g 2 (E.measure y)) :
    E.integralApply (f + g) y = E.integralApply f y + E.integralApply g y := by
  refine tendsto_nhds_unique (E.tendsto_simpleIntegral_apply (hf.add hg) (hfy.add hgy)
    (l := atTop) (s := fun n => SimpleFunc.approxOn f hf univ 0 (mem_univ 0) n +
      SimpleFunc.approxOn g hg univ 0 (mem_univ 0) n) ?_) ?_
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using (E.tendsto_eLpNorm_approxOn hf hfy).add (E.tendsto_eLpNorm_approxOn hg hgy))
      (fun _ => bot_le) fun n => ?_
    rw [SimpleFunc.coe_add, add_sub_add_comm]
    exact eLpNorm_add_le one_le_two
  · simp_rw [simpleIntegral_add, add_apply]
    exact (E.tendsto_simpleIntegral_approxOn hf hfy).add (E.tendsto_simpleIntegral_approxOn hg hgy)

variable {E} in
include hf in
/-- **Homogeneity** of `f ↦ (∫ f dE) y` on `L²(E_y)`. -/
lemma integralApply_smul (c : ℂ) (hfy : MemLp f 2 (E.measure y)) :
    E.integralApply (c • f) y = c • E.integralApply f y := by
  refine tendsto_nhds_unique (E.tendsto_simpleIntegral_apply (hf.const_smul c) (hfy.const_smul c)
    (l := atTop) (s := fun n => c • SimpleFunc.approxOn f hf univ 0 (mem_univ 0) n) ?_) ?_
  · have h := ENNReal.Tendsto.const_mul (E.tendsto_eLpNorm_approxOn hf hfy)
      (Or.inr (enorm_ne_top (x := c)))
    rw [mul_zero] at h
    refine h.congr fun n => ?_
    rw [SimpleFunc.coe_smul, ← smul_sub, eLpNorm_const_smul]
  · simp_rw [simpleIntegral_smul, smul_apply]
    exact (E.tendsto_simpleIntegral_approxOn hf hfy).const_smul c

variable {E} in
include hf in
/-- `f ↦ (∫ f dE) y` commutes with subtraction on `L²(E_y)`. -/
lemma integralApply_sub (hg : Measurable g) (hfy : MemLp f 2 (E.measure y))
    (hgy : MemLp g 2 (E.measure y)) :
    E.integralApply (f - g) y = E.integralApply f y - E.integralApply g y := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ g, integralApply_add hf (hg.const_smul _) hfy
    (hgy.const_smul _), integralApply_smul hg _ hgy, neg_one_smul, sub_eq_add_neg]

variable {E} in
include hf in
/-- **Additivity** of `y ↦ (∫ f dE) y` on the domain. -/
lemma integralApply_add_right {y' : H} (hy : MemLp f 2 (E.measure y))
    (hy' : MemLp f 2 (E.measure y')) :
    E.integralApply f (y + y') = E.integralApply f y + E.integralApply f y' := by
  refine tendsto_nhds_unique (E.tendsto_simpleIntegral_approxOn hf
    ((E.integralDomain f).add_mem hy hy')) ?_
  simp_rw [map_add]
  exact (E.tendsto_simpleIntegral_approxOn hf hy).add (E.tendsto_simpleIntegral_approxOn hf hy')

variable {E} in
include hf in
/-- **Homogeneity** of `y ↦ (∫ f dE) y` on the domain. -/
lemma integralApply_smul_right (c : ℂ) (hy : MemLp f 2 (E.measure y)) :
    E.integralApply f (c • y) = c • E.integralApply f y := by
  refine tendsto_nhds_unique (E.tendsto_simpleIntegral_approxOn hf
    ((E.integralDomain f).smul_mem c hy)) ?_
  simp_rw [map_smul]
  exact (E.tendsto_simpleIntegral_approxOn hf hy).const_smul c

include hf in
/-- **Isometry**: `‖(∫ f dE) y‖ = ‖f‖_{L²(E_y)}`. -/
lemma enorm_integralApply (hy : MemLp f 2 (E.measure y)) :
    ‖E.integralApply f y‖ₑ = eLpNorm f 2 (E.measure y) := by
  refine le_antisymm ?_ ?_
  · have h := E.edist_simpleIntegral_integralApply_le hf hy 0
    rwa [simpleIntegral_zero, zero_apply, edist_zero_left, SimpleFunc.coe_zero, zero_sub,
      eLpNorm_neg] at h
  · have h := (E.tendsto_eLpNorm_approxOn hf hy).add
      ((continuous_enorm.tendsto _).comp (E.tendsto_simpleIntegral_approxOn hf hy))
    rw [zero_add] at h
    refine le_of_tendsto_of_tendsto' tendsto_const_nhds h fun n => ?_
    simp only [Function.comp_apply, enorm_simpleIntegral_apply]
    calc eLpNorm f 2 (E.measure y)
        = eLpNorm (f - ⇑(SimpleFunc.approxOn f hf univ 0 (mem_univ 0) n) +
            ⇑(SimpleFunc.approxOn f hf univ 0 (mem_univ 0) n)) 2 (E.measure y) := by
          rw [sub_add_cancel]
      _ ≤ _ := eLpNorm_add_le one_le_two
      _ = _ := by rw [eLpNorm_sub_comm]

include hf in
/-- `‖(∫ f dE) y‖² = ∫ |f|² dE_y`. -/
lemma norm_integralApply_sq (hy : MemLp f 2 (E.measure y)) :
    ‖E.integralApply f y‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂(E.measure y) := by
  have h := E.enorm_integralApply hf hy
  rw [eLpNorm_two_eq_ofReal_sqrt hy, ← ofReal_norm,
    ENNReal.ofReal_eq_ofReal_iff (norm_nonneg _) (Real.sqrt_nonneg _)] at h
  rw [h, Real.sq_sqrt (integral_nonneg fun x => by positivity)]

include hf in
/-- **Diagonal formula**: `⟪y, (∫ f dE) y⟫ = ∫ f dE_y`. -/
lemma inner_integralApply_self (hy : MemLp f 2 (E.measure y)) :
    ⟪y, E.integralApply f y⟫_ℂ = ∫ x, f x ∂(E.measure y) := by
  refine tendsto_nhds_unique (tendsto_const_nhds.inner (E.tendsto_simpleIntegral_approxOn hf hy)) ?_
  simp_rw [inner_simpleIntegral_self]
  exact tendsto_integral_of_dominated_convergence (fun x => ‖f x‖ + ‖f x‖)
    (fun n => (SimpleFunc.approxOn f hf univ 0 (mem_univ 0) n).aestronglyMeasurable)
    ((hy.integrable one_le_two).norm.add (hy.integrable one_le_two).norm)
    (fun n => Eventually.of_forall fun x => SimpleFunc.norm_approxOn_zero_le hf (mem_univ 0) x n)
    (Eventually.of_forall fun x => SimpleFunc.tendsto_approxOn hf (mem_univ 0) (by simp))

include hf in
/-- **Polarization**: `⟪(∫ f dE) y, (∫ g dE) y⟫ = ∫ f̄ g dE_y`. -/
lemma inner_integralApply (hg : Measurable g) (hfy : MemLp f 2 (E.measure y))
    (hgy : MemLp g 2 (E.measure y)) :
    ⟪E.integralApply f y, E.integralApply g y⟫_ℂ = ∫ x, conj (f x) * g x ∂(E.measure y) := by
  have hQ : ∀ h : X → ℂ, Measurable h → MemLp h 2 (E.measure y) →
      ‖E.integralApply h y‖ * ‖E.integralApply h y‖ = ∫ x, ‖h x‖ * ‖h x‖ ∂(E.measure y) := by
    intro h hh hhy
    simp_rw [← sq]
    exact E.norm_integralApply_sq hh hhy
  have hI : ∀ h : X → ℂ, MemLp h 2 (E.measure y) →
      Integrable (fun x => ‖h x‖ * ‖h x‖) (E.measure y) := fun h hhy => by
    simpa [sq] using (memLp_two_iff_integrable_sq_norm hhy.aestronglyMeasurable).mp hhy
  have hint : Integrable (fun x => conj (f x) * g x) (E.measure y) := by
    refine Integrable.mono' ((hI f hfy).add (hI g hgy))
      (((Complex.continuous_conj.measurable.comp hf).mul hg).aestronglyMeasurable)
      (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg (f x), norm_nonneg (g x), sq_nonneg (‖f x‖ - ‖g x‖)]
  have hmIg : Measurable ((RCLike.I : ℂ) • g : X → ℂ) := hg.const_smul _
  have hIg : MemLp ((RCLike.I : ℂ) • g : X → ℂ) 2 (E.measure y) := hgy.const_smul _
  have e₁ : ‖E.integralApply f y + E.integralApply g y‖ *
      ‖E.integralApply f y + E.integralApply g y‖ =
        ∫ x, ‖f x + g x‖ * ‖f x + g x‖ ∂(E.measure y) := by
    rw [← integralApply_add hf hg hfy hgy]
    exact hQ _ (hf.add hg) (hfy.add hgy)
  have e₂ : ‖E.integralApply f y - E.integralApply g y‖ *
      ‖E.integralApply f y - E.integralApply g y‖ =
        ∫ x, ‖f x - g x‖ * ‖f x - g x‖ ∂(E.measure y) := by
    rw [← integralApply_sub hf hg hfy hgy]
    exact hQ _ (hf.sub hg) (hfy.sub hgy)
  have e₃ : ‖E.integralApply f y - (RCLike.I : ℂ) • E.integralApply g y‖ *
      ‖E.integralApply f y - (RCLike.I : ℂ) • E.integralApply g y‖ =
        ∫ x, ‖f x - (RCLike.I : ℂ) • g x‖ * ‖f x - (RCLike.I : ℂ) • g x‖ ∂(E.measure y) := by
    rw [← integralApply_smul hg _ hgy, ← integralApply_sub hf hmIg hfy hIg]
    exact hQ _ (hf.sub hmIg) (hfy.sub hIg)
  have e₄ : ‖E.integralApply f y + (RCLike.I : ℂ) • E.integralApply g y‖ *
      ‖E.integralApply f y + (RCLike.I : ℂ) • E.integralApply g y‖ =
        ∫ x, ‖f x + (RCLike.I : ℂ) • g x‖ * ‖f x + (RCLike.I : ℂ) • g x‖ ∂(E.measure y) := by
    rw [← integralApply_smul hg _ hgy, ← integralApply_add hf hmIg hfy hIg]
    exact hQ _ (hf.add hmIg) (hfy.add hIg)
  refine RCLike.ext ?_ ?_
  · rw [re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four, ← integral_re hint]
    simp_rw [← RCLike.inner_apply', re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four]
    rw [integral_div, integral_sub
      (hI _ (hfy.add hgy) : Integrable (fun x => ‖f x + g x‖ * ‖f x + g x‖) (E.measure y))
      (hI _ (hfy.sub hgy) : Integrable (fun x => ‖f x - g x‖ * ‖f x - g x‖) (E.measure y)), e₁, e₂]
  · rw [im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four,
      ← integral_im hint]
    simp_rw [← RCLike.inner_apply',
      im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four]
    rw [integral_div, integral_sub
      (hI _ (hfy.sub hIg) : Integrable (fun x => ‖f x - (RCLike.I : ℂ) • g x‖ *
        ‖f x - (RCLike.I : ℂ) • g x‖) (E.measure y))
      (hI _ (hfy.add hIg) : Integrable (fun x => ‖f x + (RCLike.I : ℂ) • g x‖ *
        ‖f x + (RCLike.I : ℂ) • g x‖) (E.measure y)), e₃, e₄]

include hf in
/-- `(∫ f dE) y` depends only on the `E_y`-a.e. class of the measurable function `f`. -/
lemma integralApply_congr_ae (hg : Measurable g) (hy : MemLp f 2 (E.measure y))
    (hfg : f =ᵐ[E.measure y] g) : E.integralApply f y = E.integralApply g y := by
  refine tendsto_nhds_unique (E.tendsto_simpleIntegral_approxOn hf hy)
    (E.tendsto_simpleIntegral_apply hg (hy.ae_eq hfg) ?_)
  refine (E.tendsto_eLpNorm_approxOn hf hy).congr fun n => eLpNorm_congr_ae ?_
  filter_upwards [hfg] with x hx
  simp [hx]

end Limit

/-! ### Bounded spectral integrals -/

section Bounded

variable {f g : X → ℂ}

/-- A measurable function bounded by `C` almost everywhere for the diagonal measure `E_y` is
square integrable against `E_y`. -/
lemma memLp_measure_of_ae_bound (hf : Measurable f) {C : ℝ} {y : H}
    (hC : ∀ᵐ x ∂E.measure y, ‖f x‖ ≤ C) : MemLp f 2 (E.measure y) :=
  MemLp.of_bound hf.aestronglyMeasurable C hC

/-- A bounded measurable function is square integrable against every diagonal measure `E_y`. -/
lemma memLp_measure_of_bound (hf : Measurable f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (y : H) :
    MemLp f 2 (E.measure y) :=
  E.memLp_measure_of_ae_bound hf (Eventually.of_forall hC)

/-- `‖(∫ f dE) y‖ ≤ C ‖y‖` for a measurable `f` bounded by `C ≥ 0` almost everywhere for the
diagonal measure `E_y`. -/
lemma norm_integralApply_le_of_ae_bound (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C) {y : H}
    (hC : ∀ᵐ x ∂E.measure y, ‖f x‖ ≤ C) : ‖E.integralApply f y‖ ≤ C * ‖y‖ := by
  have hy := E.memLp_measure_of_ae_bound hf hC
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
  rw [E.norm_integralApply_sq hf hy, mul_pow, ← E.measureReal_univ y, mul_comm, ← smul_eq_mul,
    ← MeasureTheory.integral_const]
  refine integral_mono_ae ((memLp_two_iff_integrable_sq_norm hy.aestronglyMeasurable).mp hy)
    (integrable_const _) ?_
  filter_upwards [hC] with x hx
  exact pow_le_pow_left₀ (norm_nonneg _) hx 2

/-- `‖(∫ f dE) y‖ ≤ C ‖y‖` for a measurable `f` bounded by `C`. -/
lemma norm_integralApply_le (hf : Measurable f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (y : H) :
    ‖E.integralApply f y‖ ≤ C * ‖y‖ := by
  have hy := E.memLp_measure_of_bound hf hC y
  have hsq := E.norm_integralApply_sq hf hy
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · have h0 : E.measure y = 0 := Measure.eq_zero_of_isEmpty _
    have hy0 : ‖y‖ = 0 := by
      have := E.measureReal_univ y
      rw [h0, measureReal_zero, Pi.zero_apply] at this
      exact pow_eq_zero_iff two_ne_zero |>.mp this.symm
    rw [h0, integral_zero_measure, pow_eq_zero_iff two_ne_zero] at hsq
    rw [hsq, hy0, mul_zero]
  · exact E.norm_integralApply_le_of_ae_bound hf ((norm_nonneg _).trans (hC x₀))
      (Eventually.of_forall hC)

open Classical in
/-- The **spectral integral** `∫ f dE` of a measurable `f` that is `E`-essentially bounded, i.e.
bounded by a constant `C` almost everywhere for every diagonal measure `E_y`: the bounded operator
with `⟪y, (∫ f dE) y⟫ = ∫ f dE_y` (`inner_integral_self`), the limit of the integrals
`∑ c E (s⁻¹{c})` of simple functions `s` approximating `f`. It depends only on the `E`-a.e. class
of `f` (`integral_congr_ae`). It is `0` for a non-measurable `f` or one that is not `E`-essentially
bounded. -/
noncomputable def integral (f : X → ℂ) : H →L[ℂ] H :=
  if h : Measurable f ∧ ∃ C, ∀ y, ∀ᵐ x ∂E.measure y, ‖f x‖ ≤ C then
    LinearMap.mkContinuousOfExistsBound
      { toFun := E.integralApply f
        map_add' := fun y y' => integralApply_add_right h.1
          (E.memLp_measure_of_ae_bound h.1 (h.2.choose_spec y))
          (E.memLp_measure_of_ae_bound h.1 (h.2.choose_spec y'))
        map_smul' := fun c y => integralApply_smul_right h.1 c
          (E.memLp_measure_of_ae_bound h.1 (h.2.choose_spec y)) }
      ⟨max h.2.choose 0, fun y => E.norm_integralApply_le_of_ae_bound h.1 (le_max_right _ _)
        ((h.2.choose_spec y).mono fun _ hx => hx.trans (le_max_left _ _))⟩
  else 0

/-- For a measurable `f` that is `E`-essentially bounded, `(∫ f dE) y` is the limit of the
integrals of the simple functions approximating `f`. -/
lemma integral_apply_of_ae_bound (hf : Measurable f)
    (hfb : ∃ C, ∀ y, ∀ᵐ x ∂E.measure y, ‖f x‖ ≤ C) (y : H) :
    E.integral f y = E.integralApply f y := by
  rw [integral, dite_eq_left ⟨hf, hfb⟩]
  rfl

/-- **Almost-everywhere invariance**: measurable functions that agree almost everywhere for every
diagonal measure `E_y` have the same spectral integral. -/
lemma integral_congr_ae (hf : Measurable f) (hg : Measurable g)
    (hfg : ∀ y, f =ᵐ[E.measure y] g) : E.integral f = E.integral g := by
  have hb : ∀ C : ℝ, (∀ y, ∀ᵐ x ∂E.measure y, ‖f x‖ ≤ C) ↔ ∀ y, ∀ᵐ x ∂E.measure y, ‖g x‖ ≤ C :=
    fun C => forall_congr' fun y => eventually_congr ((hfg y).mono fun x hx => by rw [hx])
  by_cases hfb : ∃ C, ∀ y, ∀ᵐ x ∂E.measure y, ‖f x‖ ≤ C
  · obtain ⟨C, hC⟩ := hfb
    ext y
    rw [E.integral_apply_of_ae_bound hf ⟨C, hC⟩, E.integral_apply_of_ae_bound hg ⟨C, (hb C).mp hC⟩,
      E.integralApply_congr_ae hf hg (E.memLp_measure_of_ae_bound hf (hC y)) (hfg y)]
  · have hgb : ¬∃ C, ∀ y, ∀ᵐ x ∂E.measure y, ‖g x‖ ≤ C := fun ⟨C, hC⟩ => hfb ⟨C, (hb C).mpr hC⟩
    rw [integral, integral, dite_eq_right fun h => hfb h.2, dite_eq_right fun h => hgb h.2]

variable (hf : Measurable f) (hfb : ∃ C, ∀ x, ‖f x‖ ≤ C)

include hf hfb in
/-- For a bounded measurable `f`, `(∫ f dE) y` is the limit of the integrals of the simple
functions approximating `f`. -/
lemma integral_apply (y : H) : E.integral f y = E.integralApply f y :=
  E.integral_apply_of_ae_bound hf (hfb.imp fun _ hC _ => Eventually.of_forall hC) y

include hf hfb in
/-- **Diagonal formula**: `⟪y, (∫ f dE) y⟫ = ∫ f dE_y`. -/
lemma inner_integral_self (y : H) : ⟪y, E.integral f y⟫_ℂ = ∫ x, f x ∂(E.measure y) := by
  obtain ⟨C, hC⟩ := hfb
  rw [E.integral_apply hf ⟨C, hC⟩, E.inner_integralApply_self hf (E.memLp_measure_of_bound hf hC y)]

include hf hfb in
/-- `‖(∫ f dE) y‖² = ∫ |f|² dE_y`. -/
lemma norm_integral_apply_sq (y : H) :
    ‖E.integral f y‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂(E.measure y) := by
  obtain ⟨C, hC⟩ := hfb
  rw [E.integral_apply hf ⟨C, hC⟩, E.norm_integralApply_sq hf (E.memLp_measure_of_bound hf hC y)]

include hf hfb in
/-- `‖∫ f dE‖ ≤ C` for a measurable `f` bounded by `C ≥ 0`. -/
lemma norm_integral_le {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (hC0 : 0 ≤ C) : ‖E.integral f‖ ≤ C :=
  opNorm_le_bound _ hC0 fun y => by
    rw [E.integral_apply hf hfb]
    exact E.norm_integralApply_le hf hC y

omit [MeasurableSpace X] in
/-- The sum of two bounded functions is bounded. -/
private lemma exists_bound_add (hfb : ∃ C, ∀ x, ‖f x‖ ≤ C) (hgb : ∃ C, ∀ x, ‖g x‖ ≤ C) :
    ∃ C, ∀ x, ‖f x + g x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hfb
  obtain ⟨D, hD⟩ := hgb
  exact ⟨C + D, fun x => (norm_add_le _ _).trans (add_le_add (hC x) (hD x))⟩

include hf hfb in
/-- The spectral integral is additive. -/
lemma integral_add (hg : Measurable g) (hgb : ∃ C, ∀ x, ‖g x‖ ≤ C) :
    E.integral (f + g) = E.integral f + E.integral g := by
  obtain ⟨C, hC⟩ := hfb
  obtain ⟨D, hD⟩ := hgb
  ext y
  rw [add_apply, E.integral_apply (hf.add hg) (exists_bound_add ⟨C, hC⟩ ⟨D, hD⟩),
    E.integral_apply hf ⟨C, hC⟩, E.integral_apply hg ⟨D, hD⟩,
    integralApply_add hf hg (E.memLp_measure_of_bound hf hC y) (E.memLp_measure_of_bound hg hD y)]

include hf hfb in
/-- The spectral integral is homogeneous. -/
lemma integral_smul (c : ℂ) : E.integral (c • f) = c • E.integral f := by
  obtain ⟨C, hC⟩ := hfb
  ext y
  rw [smul_apply, E.integral_apply (hf.const_smul c) ⟨‖c‖ * C, fun x => by
      rw [Pi.smul_apply, norm_smul]; exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg c)⟩,
    E.integral_apply hf ⟨C, hC⟩, integralApply_smul hf c (E.memLp_measure_of_bound hf hC y)]

include hf hfb in
/-- The spectral integral commutes with subtraction. -/
lemma integral_sub (hg : Measurable g) (hgb : ∃ C, ∀ x, ‖g x‖ ≤ C) :
    E.integral (f - g) = E.integral f - E.integral g := by
  obtain ⟨C, hC⟩ := hfb
  obtain ⟨D, hD⟩ := hgb
  ext y
  rw [sub_apply, E.integral_apply (hf.sub hg) ⟨C + D, fun x => (norm_sub_le _ _).trans
      (add_le_add (hC x) (hD x))⟩, E.integral_apply hf ⟨C, hC⟩, E.integral_apply hg ⟨D, hD⟩,
    integralApply_sub hf hg (E.memLp_measure_of_bound hf hC y) (E.memLp_measure_of_bound hg hD y)]

/-- The spectral integral of a constant: `∫ c dE = c • 1`. -/
@[simp]
lemma integral_const (c : ℂ) : E.integral (fun _ => c) = c • 1 :=
  ContinuousLinearMap.ext_inner_self fun y => by
    rw [E.inner_integral_self measurable_const ⟨‖c‖, fun _ => le_rfl⟩, MeasureTheory.integral_const,
      measureReal_univ, smul_apply, one_apply_eq_self, inner_smul_right,
      inner_self_eq_norm_sq_to_K,
      Complex.real_smul, mul_comm]
    norm_cast

/-- `∫ 1 dE = 1`. -/
@[simp]
lemma integral_one : E.integral (fun _ => (1 : ℂ)) = 1 := by
  rw [integral_const, one_smul]

/-- The spectral integral of the indicator function of a measurable set `s` is `E s`. -/
lemma integral_indicator_one {s : Set X} (hs : MeasurableSet s) :
    E.integral (s.indicator 1) = E s :=
  ContinuousLinearMap.ext_inner_self fun y => by
    rw [E.inner_integral_self (measurable_one.indicator hs) ⟨1, fun x => by
        by_cases hx : x ∈ s <;> simp [hx]⟩, integral_indicator hs]
    simp only [Pi.one_apply]
    rw [setIntegral_const, inner_apply_self, measureReal_apply y hs, Complex.real_smul, mul_one]


include hf hfb in
/-- **Adjoint**: `(∫ f dE)† = ∫ f̄ dE`. -/
lemma star_integral : star (E.integral f) = E.integral (fun x => conj (f x)) := by
  obtain ⟨C, hC⟩ := hfb
  have hcf : Measurable fun x => conj (f x) := Complex.continuous_conj.measurable.comp hf
  refine ContinuousLinearMap.ext_inner_self fun y => ?_
  rw [star_eq_adjoint, adjoint_inner_right, ← inner_conj_symm, E.inner_integral_self hf ⟨C, hC⟩,
    E.inner_integral_self hcf ⟨C, fun x => by rw [Complex.norm_conj]; exact hC x⟩, ← integral_conj]

include hf hfb in
/-- **Multiplicativity**: `∫ f g dE = (∫ f dE) (∫ g dE)`. -/
lemma integral_mul (hg : Measurable g) (hgb : ∃ C, ∀ x, ‖g x‖ ≤ C) :
    E.integral (f * g) = E.integral f * E.integral g := by
  obtain ⟨C, hC⟩ := hfb
  obtain ⟨D, hD⟩ := hgb
  have hcf : Measurable fun x => conj (f x) := Complex.continuous_conj.measurable.comp hf
  have hcfb : ∀ x, ‖conj (f x)‖ ≤ C := fun x => by rw [Complex.norm_conj]; exact hC x
  refine (ContinuousLinearMap.ext_inner_self fun y => ?_).symm
  rw [mul_apply_eq_comp, ← adjoint_inner_left, ← star_eq_adjoint, E.star_integral hf ⟨C, hC⟩,
    E.integral_apply hcf ⟨C, hcfb⟩, E.integral_apply hg ⟨D, hD⟩,
    E.inner_integralApply hcf hg (E.memLp_measure_of_bound hcf hcfb y)
      (E.memLp_measure_of_bound hg hD y),
    E.inner_integral_self (hf.mul hg) ⟨C * D, fun x => ?_⟩]
  · simp only [Complex.conj_conj, Pi.mul_apply]
  · rw [Pi.mul_apply, norm_mul]
    exact mul_le_mul (hC x) (hD x) (norm_nonneg _) ((norm_nonneg _).trans (hC x))

include hf in
/-- The spectral integral of a function of modulus one is unitary. -/
lemma integral_mem_unitary (hf1 : ∀ x, ‖f x‖ = 1) : E.integral f ∈ unitary (H →L[ℂ] H) := by
  have hfb : ∃ C, ∀ x, ‖f x‖ ≤ C := ⟨1, fun x => (hf1 x).le⟩
  have hcf : Measurable fun x => conj (f x) := Complex.continuous_conj.measurable.comp hf
  have hcfb : ∃ C, ∀ x, ‖conj (f x)‖ ≤ C := ⟨1, fun x => by rw [Complex.norm_conj, hf1]⟩
  have h₁ : (fun x => conj (f x)) * f = fun _ => 1 := funext fun x => by
    rw [Pi.mul_apply, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hf1]
    norm_num
  have h₂ : f * (fun x => conj (f x)) = fun _ => 1 := by rw [mul_comm, h₁]
  rw [Unitary.mem_iff, E.star_integral hf hfb, ← E.integral_mul hcf hcfb hf hfb, h₁,
    ← E.integral_mul hf hfb hcf hcfb, h₂, integral_one]
  exact ⟨rfl, rfl⟩

include hf hfb in
/-- Operators commuting with every `E s` commute with every spectral integral. -/
lemma commute_integral {T : H →L[ℂ] H} (hT : ∀ s, Commute T (E s)) :
    Commute T (E.integral f) := by
  have hs : ∀ s : SimpleFunc X ℂ, Commute T (E.simpleIntegral s) := fun s =>
    Commute.sum_right _ _ _ fun c _ => (hT _).smul_right c
  obtain ⟨C, hC⟩ := hfb
  ext y
  rw [mul_apply_eq_comp, mul_apply_eq_comp, E.integral_apply hf ⟨C, hC⟩,
    E.integral_apply hf ⟨C, hC⟩]
  refine tendsto_nhds_unique ((T.continuous.tendsto _).comp
    (E.tendsto_simpleIntegral_approxOn hf (E.memLp_measure_of_bound hf hC y))) ?_
  refine (E.tendsto_simpleIntegral_approxOn hf (E.memLp_measure_of_bound hf hC (T y))).congr
    fun n => ?_
  rw [Function.comp_apply, ← mul_apply_eq_comp, ← mul_apply_eq_comp, (hs _).eq]

include hf hfb in
/-- **Change of variables**: `∫ f d(φ_* E) = ∫ f ∘ φ dE`. -/
lemma integral_map {Y : Type*} [MeasurableSpace Y] {φ : Y → X} (hφ : Measurable φ)
    (E : ProjectionValuedMeasure Y H) : (E.map φ hφ).integral f = E.integral (f ∘ φ) := by
  obtain ⟨C, hC⟩ := hfb
  refine ContinuousLinearMap.ext_inner_self fun y => ?_
  rw [inner_integral_self _ hf ⟨C, hC⟩, inner_integral_self _ (hf.comp hφ) ⟨C, fun x => hC _⟩,
    measure_map, MeasureTheory.integral_map hφ.aemeasurable hf.aestronglyMeasurable]
  rfl

include hf hfb in
/-- Integration against the Dirac projection-valued measure at `a` evaluates at `a`:
`∫ f dδ_a = f(a)`. -/
lemma integral_dirac (a : X) : (dirac H a).integral f = f a • 1 :=
  ContinuousLinearMap.ext_inner_self fun y => by
    rw [inner_integral_self _ hf hfb, measure_dirac, integral_smul_measure,
      integral_dirac' _ _ hf.stronglyMeasurable, smul_apply, one_apply_eq_self, inner_smul_right,
      inner_self_eq_norm_sq_to_K, ENNReal.toReal_pow, toReal_enorm, Complex.real_smul]
    push_cast
    exact mul_comm _ _

/-- **Dominated convergence**: for measurable `fᵢ → f` pointwise along a countably generated filter,
uniformly bounded, `(∫ fᵢ dE) y → (∫ f dE) y` for every `y`. -/
lemma tendsto_integral_apply {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {F : ι → X → ℂ} (hF : ∀ i, Measurable (F i)) (hf : Measurable f) {C : ℝ}
    (hFC : ∀ i x, ‖F i x‖ ≤ C) (hfC : ∀ x, ‖f x‖ ≤ C)
    (hlim : ∀ x, Tendsto (fun i => F i x) l (𝓝 (f x))) (y : H) :
    Tendsto (fun i => E.integral (F i) y) l (𝓝 (E.integral f y)) := by
  have hsq : ∀ i, ‖E.integral (F i) y - E.integral f y‖ =
      √(∫ x, ‖F i x - f x‖ ^ 2 ∂(E.measure y)) := fun i => by
    rw [← sub_apply, ← E.integral_sub (hF i) ⟨C, hFC i⟩ hf ⟨C, hfC⟩,
      ← Real.sqrt_sq (norm_nonneg _), E.norm_integral_apply_sq ((hF i).sub hf)
        ⟨C + C, fun x => (norm_sub_le _ _).trans (add_le_add (hFC i x) (hfC x))⟩]
    rfl
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp_rw [hsq]
  rw [← Real.sqrt_zero]
  refine (Real.continuous_sqrt.tendsto 0).comp ?_
  have := tendsto_integral_filter_of_dominated_convergence (μ := E.measure y)
    (F := fun i x => ‖F i x - f x‖ ^ 2) (f := fun _ => 0) (fun _ => (2 * C) ^ 2)
    (Eventually.of_forall fun i => (((hF i).sub hf).norm.pow_const 2).aestronglyMeasurable)
    (Eventually.of_forall fun i => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      refine pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans ?_) 2
      linarith [hFC i x, hfC x])
    (integrable_const _)
    (Eventually.of_forall fun x => by
      simpa using ((hlim x).sub (tendsto_const_nhds (x := f x))).norm.pow 2)
  simpa using this

end Bounded

end MeasureTheory.ProjectionValuedMeasure

namespace MeasureTheory.ProjectionValuedMeasure

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Projection-valued measures on `(0, ∞)` -/

section Positive

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (E : ProjectionValuedMeasure ℝ H)

/-- A projection-valued measure living on `(0, ∞)` gives full mass to `(0, ∞)`. -/
lemma apply_Ioi_eq_one_of_apply_Iic_eq_zero (hE : E (Iic 0) = 0) :
    E (Ioi 0) = 1 := by
  have h := E.apply_union (Set.Iic_disjoint_Ioi (le_refl (0 : ℝ))) measurableSet_Iic
    measurableSet_Ioi
  rwa [Iic_union_Ioi, ProjectionValuedMeasure.apply_univ, hE, zero_add, eq_comm] at h

/-- On a projection-valued measure living on `(0, ∞)`, cutting off to `(0, ∞)` does not change
bounded integrals. -/
lemma integral_indicator_Ioi (hE : E (Iic 0) = 0) {f : ℝ → ℂ} (hf : Measurable f)
    (hfb : ∃ C, ∀ t, ‖f t‖ ≤ C) : E.integral ((Ioi 0).indicator f) = E.integral f := by
  have h : (Ioi (0 : ℝ)).indicator f = f * (Ioi 0).indicator 1 := by
    funext t
    by_cases ht : t ∈ Ioi (0 : ℝ) <;> simp [ht]
  rw [h, E.integral_mul hf hfb (measurable_one.indicator measurableSet_Ioi)
    ⟨1, fun t => by by_cases ht : t ∈ Ioi (0 : ℝ) <;> simp [ht]⟩,
    E.integral_indicator_one measurableSet_Ioi, E.apply_Ioi_eq_one_of_apply_Iic_eq_zero hE, mul_one]

end Positive

end MeasureTheory.ProjectionValuedMeasure
