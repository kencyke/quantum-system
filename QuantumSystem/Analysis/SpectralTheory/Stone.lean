/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.SpectralTheory.AnalyticContinuation
public import QuantumSystem.Analysis.SpectralTheory.Power
public import QuantumSystem.Analysis.SpectralTheory.SNAG
public import QuantumSystem.ForMathlib.Topology.Algebra.Module.PerfectPairing

/-!
# Stone's theorem

The **infinitesimal generator** of a one-parameter group `U : AddChar ℝ (E →L[R] E)` of bounded
operators on a normed space is the operator `G y = d/dt U(t) y |_{t = 0}`, defined on the vectors
`y` for which the derivative exists (`AddChar.generator`, Engel–Nagel, Definition II.1.2). For a
one-parameter unitary group `U : AddChar ℝ (unitary _)` the generator is `G = i A`, and
`A = -i G` is the **self-adjoint generator** (`AddChar.selfAdjointGenerator`), the generator in the
convention of Stone and Schmüdgen: `i A y = d/dt U(t) y |_{t = 0}`. **Stone's theorem** states that
the self-adjoint generator of a strongly continuous one-parameter unitary group is self-adjoint and
generates it, `U(t) = e^{itA}`
(`AddChar.IsStronglyContinuous.unitaryGroup_selfAdjointGenerator`), and that conversely the
self-adjoint generator of the unitary group `e^{itB}` of a self-adjoint `B` is `B`
(`IsSelfAdjoint.selfAdjointGenerator_unitaryGroup`). Hence `A ↦ (t ↦ e^{itA})` is a bijection from
the self-adjoint operators onto the strongly continuous one-parameter unitary groups
(`IsSelfAdjoint.unitaryGroupEquiv`).

Stone's theorem is the case `V = ℝ` of the SNAG theorem, for the multiplication pairing of `ℝ`
with itself (`LinearMap.mul_isContPerfPair`): `U(t) = ∫ e^{itλ} dE(λ)` for the projection-valued
measure `E = hU.pvm (LinearMap.mul ℝ ℝ)`, and the self-adjoint generator is `∫ λ dE(λ)`
(`AddChar.IsStronglyContinuous.selfAdjointGenerator_eq_integralPMap`). The identification rests on
a computation for an arbitrary projection-valued measure `E` and measurable real `φ`
(`ProjectionValuedMeasure.hasDerivAt_integral_cexp_apply_iff`): `t ↦ (∫ e^{itφ} dE) y` is
differentiable at `0` iff `φ ∈ L²(E_y)`, with derivative `i (∫ φ dE) y`. The difference quotients
are the spectral integrals of `(e^{itφ} - 1) / t`, which are dominated by `|φ|`; dominated
convergence gives the derivative, and Fatou's lemma, through the lower semicontinuity of the
`L²` norm, gives `φ ∈ L²(E_y)` from the convergence of the difference quotients.

## Main definitions

* `AddChar.generator U` — the infinitesimal generator `G` of a one-parameter group of bounded
  operators, `G y = d/dt U(t) y |_{t = 0}`.
* `AddChar.selfAdjointGenerator U` — the self-adjoint generator `A = -i G` of a one-parameter
  unitary group.
* `IsSelfAdjoint.unitaryGroupEquiv H` — **Stone's theorem** as a bijection
  `A ↦ (t ↦ e^{itA})` from the self-adjoint operators onto the strongly continuous one-parameter
  unitary groups.

## Main results

* `AddChar.mem_graph_generator_iff`, `AddChar.mem_graph_selfAdjointGenerator_iff` — `G y = z` iff
  `t ↦ U(t) y` has derivative `z` at `0`, and `A y = z` iff it has derivative `i z`.
* `AddChar.compPMap_generator_le`, `AddChar.hasDerivAt_apply_of_mem_graph_generator` —
  `U(t) G ⊆ G U(t)`, and `d/dt U(t) y = U(t) G y` at every `t`.
* `ProjectionValuedMeasure.hasDerivAt_integral_cexp_apply`,
  `ProjectionValuedMeasure.memLp_of_differentiableAt_integral_cexp_apply`,
  `ProjectionValuedMeasure.hasDerivAt_integral_cexp_apply_iff` — differentiating
  `t ↦ (∫ e^{itφ} dE) y`.
* `IsSelfAdjoint.selfAdjointGenerator_unitaryGroup` — **Stone's theorem**, converse: the
  self-adjoint generator of `t ↦ e^{itB}` is `B`.
* `AddChar.IsStronglyContinuous.selfAdjointGenerator_eq_integralPMap` — the self-adjoint generator
  of a strongly continuous `U` is `∫ λ dE(λ)` for the projection-valued measure `E` of the SNAG
  theorem.
* `AddChar.IsStronglyContinuous.isSelfAdjoint_selfAdjointGenerator`,
  `AddChar.IsStronglyContinuous.pvm_selfAdjointGenerator`,
  `AddChar.IsStronglyContinuous.unitaryGroup_selfAdjointGenerator` — **Stone's theorem**: the
  self-adjoint generator is self-adjoint, its projection-valued measure is that of the SNAG
  theorem, and `U(t) = e^{itA}`.
* `AddChar.IsStronglyContinuous.existsUnique_unitaryGroup_eq` — **Stone's theorem**: `U` is
  `t ↦ e^{itA}` for a unique self-adjoint `A`.

## TODO

* Strongly continuous one-parameter groups and semigroups of bounded operators on Banach spaces:
  closedness and density of the domain of `AddChar.generator`, and the Hille–Yosida theorem. Only
  unitary groups on Hilbert spaces are analysed here, through the SNAG theorem; semigroups need a
  one-sided derivative and a parameter monoid `ℝ≥0`.
* Weakly measurable one-parameter unitary groups on separable Hilbert spaces, which are strongly
  continuous by von Neumann's theorem (see the TODO of
  `QuantumSystem.Analysis.SpectralTheory.SNAG`).

## References

* M. H. Stone, *On one-parameter unitary groups in Hilbert space*, Ann. of Math. 33 (1932),
  643–648.
* [K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*][schmudgen2012], §6.1
  (Theorems 6.1 and 6.2)
* K.-J. Engel, R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Springer GTM
  194 (2000), §II.1
-/

@[expose] public section

open Set Filter Topology MeasureTheory Complex
open scoped ENNReal InnerProductSpace LinearPMap

/-! ### The infinitesimal generator of a one-parameter group -/

namespace AddChar

variable {R E : Type*} [Ring R] [NormedAddCommGroup E] [NormedSpace ℝ E] [Module R E]
  [SMulCommClass ℝ R E] [ContinuousConstSMul R E] (U : AddChar ℝ (E →L[R] E))

/-- The domain of the infinitesimal generator of a one-parameter group `U` of bounded operators:
the vectors `y` for which `t ↦ U(t) y` is differentiable at `0`. -/
def generatorDomain : Submodule R E where
  carrier := {y | DifferentiableAt ℝ (fun t => U t y) 0}
  add_mem' {x y} hx hy := by
    change DifferentiableAt ℝ (fun t => U t (x + y)) 0
    simp only [map_add]
    exact hx.add hy
  zero_mem' := by simp
  smul_mem' c y hy := by
    change DifferentiableAt ℝ (fun t => U t (c • y)) 0
    simp only [map_smul]
    exact hy.const_smul c

/-- The **infinitesimal generator** `G` of a one-parameter group `U` of bounded operators:
`G y = d/dt U(t) y |_{t = 0}`, on the vectors `y` for which the derivative exists (Engel–Nagel,
Definition II.1.2). For a one-parameter unitary group, `G = i A` for the self-adjoint operator `A`
with `U(t) = e^{itA}` (`AddChar.selfAdjointGenerator`, Stone's theorem). -/
noncomputable def generator : E →ₗ.[R] E where
  domain := U.generatorDomain
  toFun :=
    { toFun := fun y => deriv (fun t => U t y) 0
      map_add' := fun x y => by
        simp only [Submodule.coe_add, map_add]
        exact deriv_fun_add x.2 y.2
      map_smul' := fun c y => by
        simp only [SetLike.val_smul, map_smul, RingHom.id_apply]
        exact deriv_fun_const_smul c y.2 }

variable {U}

/-- `G y = z` iff `t ↦ U(t) y` has derivative `z` at `0`. -/
lemma mem_graph_generator_iff {y z : E} :
    (y, z) ∈ U.generator.graph ↔ HasDerivAt (fun t => U t y) z 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨⟨y', hy'⟩, rfl, rfl⟩ := (LinearPMap.mem_graph_iff _).mp h
    exact hy'.hasDerivAt
  · exact (LinearPMap.mem_graph_iff _).mpr ⟨⟨y, h.differentiableAt⟩, rfl, h.deriv⟩

omit [NormedSpace ℝ E] [SMulCommClass ℝ R E] [ContinuousConstSMul R E] in
/-- `U(s) U(t) = U(t) U(s)`. -/
private lemma apply_apply_comm (s t : ℝ) (y : E) : U s (U t y) = U t (U s y) := by
  rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul,
    add_comm]

/-- **`U(t)` commutes with the generator**: `U(t) G ⊆ G U(t)`. -/
lemma compPMap_generator_le (t : ℝ) :
    ((U t : E →L[R] E) : E →ₗ[R] E).compPMap U.generator ≤
      U.generator.compNat (((U t : E →L[R] E) : E →ₗ[R] E).toPMap ⊤) := by
  -- the derivative of `s ↦ U(s) U(t) y` is computed at each vector `y`
  refine LinearPMap.compPMap_le_compNat_toPMap_iff.mpr fun y z h => ?_
  simp only [ContinuousLinearMap.coe_coe]
  rw [mem_graph_generator_iff] at h ⊢
  simp_rw [apply_apply_comm _ t]
  exact ((U t).toLinearMap.toAddMonoidHom.toRealLinearMap (U t).continuous).hasFDerivAt.comp_hasDerivAt
    0 h

/-- `d/dt U(t) y = U(t) G y` at every `t`, for `y` in the domain of the generator. -/
lemma hasDerivAt_apply_of_mem_graph_generator {y z : E} (h : (y, z) ∈ U.generator.graph)
    (t : ℝ) : HasDerivAt (fun s => U s y) (U t z) t := by
  have h' := mem_graph_generator_iff.mp
    (LinearPMap.compPMap_le_compNat_toPMap_iff.mp (U.compPMap_generator_le t) h)
  simp only [ContinuousLinearMap.coe_coe] at h'
  rw [← sub_self t] at h'
  convert h'.comp_sub_const t t using 1
  funext s
  rw [← mul_apply_eq_comp, ← AddChar.map_add_eq_mul, sub_add_cancel]

end AddChar

/-! ### The self-adjoint generator of a one-parameter unitary group -/

namespace AddChar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The **self-adjoint generator** `A = -i G` of a one-parameter unitary group `U`, for the
infinitesimal generator `G` of `U` as a group of bounded operators: `i A y = d/dt U(t) y |_{t = 0}`.
This is the infinitesimal generator in the convention of Stone and Schmüdgen (§6.1); for a
strongly continuous `U` it is self-adjoint and `U(t) = e^{itA}`
(`AddChar.IsStronglyContinuous.unitaryGroup_selfAdjointGenerator`). -/
noncomputable def selfAdjointGenerator (U : AddChar ℝ (unitary (H →L[ℂ] H))) : H →ₗ.[ℂ] H :=
  -I • ((unitary (H →L[ℂ] H)).subtype.compAddChar U).generator

variable {U : AddChar ℝ (unitary (H →L[ℂ] H))}

/-- `A y = z` iff `t ↦ U(t) y` has derivative `i z` at `0`. -/
lemma mem_graph_selfAdjointGenerator_iff {y z : H} :
    (y, z) ∈ U.selfAdjointGenerator.graph ↔
      HasDerivAt (fun t => (U t : H →L[ℂ] H) y) (I • z) 0 := by
  set G := ((unitary (H →L[ℂ] H)).subtype.compAddChar U).generator
  have hG : ∀ y z, (y, z) ∈ G.graph ↔ HasDerivAt (fun t => (U t : H →L[ℂ] H) y) z 0 :=
    fun y z => mem_graph_generator_iff
  have hA : ∀ y : G.domain, U.selfAdjointGenerator ⟨y, y.2⟩ = -I • G y := fun y => rfl
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨⟨y', hy'⟩, rfl, rfl⟩ := (LinearPMap.mem_graph_iff _).mp h
    rw [hA ⟨y', hy'⟩, smul_smul, mul_neg, I_mul_I, neg_neg, one_smul]
    exact (hG _ _).mp (G.mem_graph ⟨y', hy'⟩)
  · obtain ⟨y', rfl, hy'⟩ := (LinearPMap.mem_graph_iff _).mp ((hG _ _).mpr h)
    refine (LinearPMap.mem_graph_iff _).mpr ⟨⟨y', y'.2⟩, rfl, ?_⟩
    rw [hA y', hy', smul_smul, neg_mul, I_mul_I, neg_neg, one_smul]

end AddChar

/-! ### Differentiating the Fourier transform of a projection-valued measure -/

namespace MeasureTheory.ProjectionValuedMeasure

variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] (E : ProjectionValuedMeasure X H) {φ : X → ℝ} {y : H}

/-- The difference quotient `(e^{ita} - 1) / t`. -/
private noncomputable abbrev quot (a t : ℝ) : ℂ := (t⁻¹ : ℂ) * (cexp (t * a * I) - 1)

/-- `(e^{ita} - 1) / t → i a` as `t → 0`. -/
private lemma tendsto_quot (a : ℝ) : Tendsto (fun t => quot a t) (𝓝[≠] 0) (𝓝 (I * a)) := by
  have h : HasDerivAt (fun t : ℝ => cexp (t * a * I)) (a * I) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const ((a : ℂ) * I)).cexp
    simpa [mul_assoc] using this
  rw [hasDerivAt_iff_tendsto_slope_zero] at h
  convert h using 2 with t
  · simp [quot, Complex.real_smul]
  · ring

/-- `|(e^{ita} - 1) / t| ≤ |a|`. -/
private lemma norm_quot_le (a t : ℝ) : ‖quot a t‖ ≤ |a| := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [quot]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := t * a)
  rw [quot, norm_mul, norm_inv, norm_real, Real.norm_eq_abs, show (t : ℂ) * a * I = I * (t * a : ℝ)
    by push_cast; ring, inv_mul_le_iff₀ (abs_pos.mpr ht)]
  simpa [abs_mul] using h

/-- The difference quotients of `t ↦ (∫ e^{itφ} dE) y` are the spectral integrals of
`(e^{itφ} - 1) / t`. -/
private lemma smul_integral_cexp_sub (hφ : Measurable φ) (t : ℝ) :
    t⁻¹ • (E.integral (fun x => cexp ((0 + t : ℝ) * φ x * I)) y -
      E.integral (fun x => cexp ((0 : ℝ) * φ x * I)) y) =
        E.integralApply (fun x => quot (φ x) t) y := by
  have he : Measurable fun x => cexp (t * φ x * I) := by fun_prop
  have heb : ∀ x, ‖cexp (t * φ x * I)‖ ≤ 1 := fun x => by
    rw [← ofReal_mul, norm_exp_ofReal_mul_I]
  have hq : (fun x => quot (φ x) t) = (t⁻¹ : ℂ) • ((fun x => cexp (t * φ x * I)) - fun _ => 1) := by
    ext x
    simp [quot]
  rw [← E.integral_apply (by fun_prop) ⟨|t|⁻¹ * 2, fun x => ?_⟩, hq,
    E.integral_smul (he.sub measurable_const) ⟨2, fun x => (norm_sub_le _ _).trans ?_⟩,
    E.integral_sub he ⟨1, heb⟩ measurable_const ⟨1, fun _ => by simp⟩]
  · simp [← ofReal_inv, Complex.coe_smul]
  · linarith [heb x, norm_one (α := ℂ)]
  · rw [quot, norm_mul, norm_inv, norm_real, Real.norm_eq_abs]
    gcongr
    exact (norm_sub_le _ _).trans (by linarith [heb x, norm_one (α := ℂ)])

private lemma measurable_quot (hφ : Measurable φ) (t : ℝ) : Measurable fun x => quot (φ x) t := by
  fun_prop

private lemma memLp_quot (hφ : Measurable φ) (t : ℝ) :
    MemLp (fun x => quot (φ x) t) 2 (E.measure y) :=
  E.memLp_measure_of_bound (measurable_quot hφ t) (C := |t|⁻¹ * 2) (fun x => by
    rw [quot, norm_mul, norm_inv, norm_real, Real.norm_eq_abs]
    gcongr
    refine (norm_sub_le _ _).trans ?_
    rw [← ofReal_mul, norm_exp_ofReal_mul_I, norm_one]
    norm_num) y

/-- **Derivative of the Fourier transform**: for `φ ∈ L²(E_y)`, `t ↦ (∫ e^{itφ} dE) y` has
derivative `i (∫ φ dE) y` at `0`. The difference quotients are the spectral integrals of
`(e^{itφ} - 1) / t`, dominated by `|φ|`, so dominated convergence applies. -/
lemma hasDerivAt_integral_cexp_apply (hφ : Measurable φ)
    (hy : MemLp (fun x => (φ x : ℂ)) 2 (E.measure y)) :
    HasDerivAt (fun t : ℝ => E.integral (fun x => cexp (t * φ x * I)) y)
      (I • E.integralApply (fun x => (φ x : ℂ)) y) 0 := by
  have hφc : Measurable fun x => (φ x : ℂ) := by fun_prop
  have hIφ : MemLp (I • fun x => (φ x : ℂ)) 2 (E.measure y) := hy.const_smul I
  rw [hasDerivAt_iff_tendsto_slope_zero, tendsto_iff_norm_sub_tendsto_zero]
  simp_rw [E.smul_integral_cexp_sub hφ, ← integralApply_smul hφc I hy,
    E.norm_integralApply_sub (measurable_quot hφ _) (hφc.const_smul I) (E.memLp_quot hφ _) hIφ]
  rw [← Real.sqrt_zero]
  refine (Real.continuous_sqrt.tendsto 0).comp ?_
  have h2 : Integrable (fun x => (2 * |φ x|) ^ 2) (E.measure y) := by
    have h4 : (fun x => (2 * |φ x|) ^ 2) = fun x => 4 * ‖(φ x : ℂ)‖ ^ 2 := by
      ext x
      rw [norm_real, Real.norm_eq_abs]
      ring
    rw [h4]
    exact ((memLp_two_iff_integrable_sq_norm hy.aestronglyMeasurable).mp hy).const_mul 4
  have h := tendsto_integral_filter_of_dominated_convergence (μ := E.measure y)
    (l := 𝓝[≠] (0 : ℝ)) (F := fun t x => ‖quot (φ x) t - (I • fun x => (φ x : ℂ)) x‖ ^ 2)
    (f := fun _ => 0) (fun x => (2 * |φ x|) ^ 2)
    (Eventually.of_forall fun t =>
      (((measurable_quot hφ t).sub (hφc.const_smul I)).norm.pow_const 2).aestronglyMeasurable)
    (Eventually.of_forall fun t => ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      refine pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans ?_) 2
      exact (add_le_add (norm_quot_le (φ x) t)
        (show ‖(I • fun x => (φ x : ℂ)) x‖ ≤ |φ x| by simp)).trans_eq (by ring))
    h2
    (ae_of_all _ fun x => by
      have := ((tendsto_quot (φ x)).sub (tendsto_const_nhds (x := I * φ x))).norm.pow 2
      simpa using this)
  simpa using h

/-- If `t ↦ (∫ e^{itφ} dE) y` is differentiable at `0`, then `φ ∈ L²(E_y)`: the difference
quotients along `t = 1 / (n + 1)` converge, so their norms, the `L²(E_y)` norms of
`(e^{itφ} - 1) / t`, are bounded, and these functions converge pointwise to `i φ`; the lower
semicontinuity of the `L²` norm (Fatou's lemma) bounds the norm of `i φ`. -/
lemma memLp_of_differentiableAt_integral_cexp_apply (hφ : Measurable φ)
    (h : DifferentiableAt ℝ (fun t : ℝ => E.integral (fun x => cexp (t * φ x * I)) y) 0) :
    MemLp (fun x => (φ x : ℂ)) 2 (E.measure y) := by
  have hs := hasDerivAt_iff_tendsto_slope_zero.mp h.hasDerivAt
  simp_rw [E.smul_integral_cexp_sub hφ] at hs
  set t : ℕ → ℝ := fun n => 1 / (n + 1)
  have ht : Tendsto t atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      tendsto_one_div_add_atTop_nhds_zero_nat (Eventually.of_forall fun n => by
        simp only [t, mem_compl_iff, mem_singleton_iff]
        positivity)
  have hIφm : Measurable fun x => I * (φ x : ℂ) := by fun_prop
  have hlim : eLpNorm (fun x => I * (φ x : ℂ)) 2 (E.measure y) ≤
      ‖deriv (fun t : ℝ => E.integral (fun x => cexp (t * φ x * I)) y) 0‖ₑ := by
    refine (Lp.eLpNorm_lim_le_liminf_eLpNorm (fun n => (measurable_quot hφ (t n)).aestronglyMeasurable)
      _ hIφm.aestronglyMeasurable (ae_of_all _ fun x => (tendsto_quot (φ x)).comp ht)).trans_eq ?_
    simp_rw [← E.enorm_integralApply (measurable_quot hφ _) (E.memLp_quot hφ _)]
    exact ((continuous_enorm.tendsto _).comp (hs.comp ht)).liminf_eq
  have hmem : MemLp (fun x => I * (φ x : ℂ)) 2 (E.measure y) := hlim.trans_lt enorm_lt_top
  convert hmem.const_mul (-I) using 2 with x
  rw [← mul_assoc, neg_mul, I_mul_I, neg_neg, one_mul]

/-- **Differentiating the Fourier transform**: `t ↦ (∫ e^{itφ} dE) y` has derivative `i z` at `0`
iff `φ ∈ L²(E_y)` and `(∫ φ dE) y = z`, i.e. iff `(y, z)` is in the graph of `∫ φ dE`. -/
lemma hasDerivAt_integral_cexp_apply_iff (hφ : Measurable φ) {z : H} :
    HasDerivAt (fun t : ℝ => E.integral (fun x => cexp (t * φ x * I)) y) (I • z) 0 ↔
      (y, z) ∈ (E.integralPMap fun x => (φ x : ℂ)).graph := by
  rw [E.mem_graph_integralPMap]
  refine ⟨fun h => ?_, fun ⟨hy, hz⟩ => hz ▸ E.hasDerivAt_integral_cexp_apply hφ hy⟩
  have hy := E.memLp_of_differentiableAt_integral_cexp_apply hφ h.differentiableAt
  exact ⟨hy, (smul_right_injective H I_ne_zero (h.unique
    (E.hasDerivAt_integral_cexp_apply hφ hy))).symm⟩

end MeasureTheory.ProjectionValuedMeasure

/-! ### Stone's theorem -/

namespace IsSelfAdjoint

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {B : H →ₗ.[ℂ] H}

/-- **Stone's theorem**, the generator of `e^{itB}`: the self-adjoint generator of the unitary
group `t ↦ e^{itB}` of a self-adjoint operator `B` is `B`. -/
theorem selfAdjointGenerator_unitaryGroup (hB : IsSelfAdjoint B) :
    hB.unitaryGroup.selfAdjointGenerator = B := by
  refine LinearPMap.eq_of_eq_graph (Submodule.ext fun ⟨y, z⟩ => ?_)
  rw [AddChar.mem_graph_selfAdjointGenerator_iff]
  simp_rw [coe_unitaryGroup_apply]
  conv_rhs => rw [hB.eq_integralPMap_pvm]
  exact hB.pvm.hasDerivAt_integral_cexp_apply_iff (φ := fun s => s) measurable_id

end IsSelfAdjoint

namespace AddChar.IsStronglyContinuous

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {U : AddChar ℝ (unitary (H →L[ℂ] H))} (hU : U.IsStronglyContinuous)

/-- The operator `∫ λ dE(λ)` of the projection-valued measure `E` of a strongly continuous
one-parameter unitary group is self-adjoint, with projection-valued measure `E` and unitary group
`U`. -/
private lemma unitaryGroup_integralPMap :
    ∃ hB : IsSelfAdjoint ((hU.pvm (LinearMap.mul ℝ ℝ)).integralPMap fun s => (s : ℂ)),
      hB.pvm = hU.pvm (LinearMap.mul ℝ ℝ) ∧ hB.unitaryGroup = U := by
  set E := hU.pvm (LinearMap.mul ℝ ℝ)
  have hB : IsSelfAdjoint (E.integralPMap fun s => (s : ℂ)) :=
    E.isSelfAdjoint_integralPMap_ofReal (φ := fun s => s) measurable_id
  have hpvm : hB.pvm = E := (E.pvm_integralPMap_ofReal measurable_id).trans E.map_id
  refine ⟨hB, hpvm, ?_⟩
  rw [IsSelfAdjoint.unitaryGroup, hpvm]
  exact hU.fourier_pvm _

/-- The self-adjoint generator of a strongly continuous one-parameter unitary group `U` is
`∫ λ dE(λ)` for the projection-valued measure `E` of `U` given by the SNAG theorem,
`U(t) = ∫ e^{itλ} dE(λ)`. -/
lemma selfAdjointGenerator_eq_integralPMap :
    U.selfAdjointGenerator = (hU.pvm (LinearMap.mul ℝ ℝ)).integralPMap fun s => (s : ℂ) := by
  obtain ⟨hB, -, hU'⟩ := hU.unitaryGroup_integralPMap
  calc U.selfAdjointGenerator = hB.unitaryGroup.selfAdjointGenerator := by rw [hU']
    _ = _ := hB.selfAdjointGenerator_unitaryGroup

include hU in
/-- **Stone's theorem**: the self-adjoint generator `A = -i G` of a strongly continuous
one-parameter unitary group, for the infinitesimal generator `G`, is self-adjoint. -/
theorem isSelfAdjoint_selfAdjointGenerator : IsSelfAdjoint U.selfAdjointGenerator := by
  rw [hU.selfAdjointGenerator_eq_integralPMap]
  exact (hU.pvm (LinearMap.mul ℝ ℝ)).isSelfAdjoint_integralPMap_ofReal (φ := fun s => s)
    measurable_id

/-- The projection-valued measure of the self-adjoint generator of `U` is the projection-valued
measure of `U` given by the SNAG theorem. -/
lemma pvm_selfAdjointGenerator :
    hU.isSelfAdjoint_selfAdjointGenerator.pvm = hU.pvm (LinearMap.mul ℝ ℝ) := by
  obtain ⟨hB, hpvm, -⟩ := hU.unitaryGroup_integralPMap
  rw [IsSelfAdjoint.pvm_congr _ hB hU.selfAdjointGenerator_eq_integralPMap, hpvm]

/-- **Stone's theorem**: a strongly continuous one-parameter unitary group is generated by its
self-adjoint generator `A`, `U(t) = e^{itA}`. -/
theorem unitaryGroup_selfAdjointGenerator :
    hU.isSelfAdjoint_selfAdjointGenerator.unitaryGroup = U := by
  rw [IsSelfAdjoint.unitaryGroup, hU.pvm_selfAdjointGenerator]
  exact hU.fourier_pvm _

include hU in
/-- **Stone's theorem**: a strongly continuous one-parameter unitary group is `t ↦ e^{itA}` for a
unique self-adjoint operator `A`, its self-adjoint generator. -/
theorem existsUnique_unitaryGroup_eq :
    ∃! A : H →ₗ.[ℂ] H, ∃ hA : IsSelfAdjoint A, hA.unitaryGroup = U :=
  ⟨U.selfAdjointGenerator,
    ⟨hU.isSelfAdjoint_selfAdjointGenerator, hU.unitaryGroup_selfAdjointGenerator⟩,
    fun A ⟨hA, h⟩ => by rw [← h, hA.selfAdjointGenerator_unitaryGroup]⟩

end AddChar.IsStronglyContinuous

namespace IsSelfAdjoint

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Stone's theorem** as a bijection: `A ↦ (t ↦ e^{itA})` maps the self-adjoint operators onto the
strongly continuous one-parameter unitary groups, with inverse the self-adjoint generator. -/
noncomputable def unitaryGroupEquiv : {A : H →ₗ.[ℂ] H // IsSelfAdjoint A} ≃
    {U : AddChar ℝ (unitary (H →L[ℂ] H)) // U.IsStronglyContinuous} where
  toFun A := ⟨A.2.unitaryGroup, A.2.isStronglyContinuous_unitaryGroup⟩
  invFun U := ⟨U.1.selfAdjointGenerator, U.2.isSelfAdjoint_selfAdjointGenerator⟩
  left_inv A := Subtype.ext A.2.selfAdjointGenerator_unitaryGroup
  right_inv U := Subtype.ext U.2.unitaryGroup_selfAdjointGenerator

end IsSelfAdjoint
