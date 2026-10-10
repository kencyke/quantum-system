/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.SpectralTheory.ScalarSpectralMeasure
public import QuantumSystem.Analysis.SpectralTheory.SpectralMeasure
public import QuantumSystem.Analysis.SpectralTheory.UnboundedIntegral
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.Semilinear

/-!
# The functional calculus of a self-adjoint operator

Let `A` be a self-adjoint operator on a complex Hilbert space `E`, with projection-valued measure
`E_A` on `ℝ` (`IsSelfAdjoint.pvm`, constructed from the resolvent in
`QuantumSystem.Analysis.SpectralTheory.SpectralMeasure`). This file proves the spectral theorem
in its proper form, `A = ∫ λ dE_A(λ)` as an identity of unbounded operators, the uniqueness of
`E_A`, and the basic rules of the Borel functional calculus `f(A) = ∫ f dE_A`
(`ProjectionValuedMeasure.integralPMap`, bounded case `ProjectionValuedMeasure.integral`).

The proofs go through the resolvent: `(z - A)⁻¹ = ∫ (z - λ)⁻¹ dE_A(λ)` follows from the Stieltjes
representation of the diagonal measures, the resolvent of `∫ λ dF(λ)` is `∫ (z - λ)⁻¹ dF(λ)` for
any projection-valued measure `F` on `ℝ`, and two self-adjoint operators with the same resolvent
at `i` coincide. Uniqueness reduces, through `λ ↦ (i - λ)⁻¹`, to the uniqueness of the
projection-valued measure of the bounded normal operator `(i - A)⁻¹`.

Covariance is stated for a semilinear isometric equivalence `V : E ≃ₛₗᵢ[σ] K`, with `σ` the
identity (unitary `V`) or the complex conjugation (antiunitary `V`), between possibly different
spaces: if `B V = V A`, then `E_B = V E_A V⁻¹`
(`ProjectionValuedMeasure.transport`), and `f(B) = V f̄(A) V⁻¹` in the antiunitary case.

## Main definitions

* `ProjectionValuedMeasure.transport E V` — the projection-valued measure `s ↦ V E(s) V⁻¹`.

## Main results

* `ProjectionValuedMeasure.resolvent_integralPMap_ofReal` — the resolvent of `∫ λ dF(λ)` at a
  non-real `z` is `∫ (z - λ)⁻¹ dF(λ)`.
* `IsSelfAdjoint.resolvent_eq_integral_pvm` — `(z - A)⁻¹ = ∫ (z - λ)⁻¹ dE_A(λ)`.
* `IsSelfAdjoint.eq_of_resolvent_I_eq` — self-adjoint operators with the same resolvent at `i` are
  equal.
* `IsSelfAdjoint.eq_integralPMap_pvm` — **spectral theorem**: `A = ∫ λ dE_A(λ)`.
* `IsSelfAdjoint.mem_domain_iff_memLp`, `IsSelfAdjoint.inner_eq_integral_of_mem_graph` —
  `dom A = {y | ∫ λ² dμ_y < ∞}` and `⟪y, A y⟫ = ∫ λ dμ_y`.
* `IsSelfAdjoint.isPositive_iff_pvm_Iio_eq_zero` — `A ≥ 0` iff `E_A((-∞, 0)) = 0`.
* `IsSelfAdjoint.eq_pvm_of_eq_integralPMap` — **uniqueness**: `E_A` is the only projection-valued
  measure `F` with `A = ∫ λ dF(λ)`.
* `ProjectionValuedMeasure.pvm_integralPMap_ofReal`,
  `ProjectionValuedMeasure.integralPMap_pvm_integralPMap_ofReal` — for measurable real `g`,
  `E_{g(A)} = g_* E_A` and `f(g(A)) = (f ∘ g)(A)`, for any projection-valued measure on `ℝ`.
* `ProjectionValuedMeasure.integralPMap_transport_compNat` — `(∫ f d(V E V⁻¹)) V = V ∫ σ⁻¹ ∘ f dE`.
* `ProjectionValuedMeasure.measure_transport`, `ProjectionValuedMeasure.integral_transport` —
  `(V E V⁻¹)_y = E_{V⁻¹ y}` and `∫ f d(V E V⁻¹) = V (∫ σ⁻¹ ∘ f dE) V⁻¹`.
* `LinearPMap.resolvent_eq_comp_of_compNat_toPMap_eq` — `(z - S)⁻¹ = V (σ⁻¹ z - T)⁻¹ V⁻¹` when
  `S V = V T`.
* `IsSelfAdjoint.pvm_eq_transport`, `IsSelfAdjoint.integral_pvm_eq_comp` — **covariance**:
  `E_B = V E_A V⁻¹` and `f(B) = V (σ⁻¹ ∘ f)(A) V⁻¹`.

## References

* [W. Rudin, *Functional Analysis*][rudin1991], Theorem 13.30
* [K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*][schmudgen2012], §5.2
-/

@[expose] public section

open Set Filter Topology MeasureTheory Complex
open scoped ENNReal InnerProductSpace ComplexConjugate LinearPMap

namespace MeasureTheory.ProjectionValuedMeasure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (F : ProjectionValuedMeasure ℝ E)

/-- `‖(z - t)⁻¹‖ ≤ |im z|⁻¹` for real `t`. -/
lemma norm_inv_sub_ofReal_le {z : ℂ} (hz : z.im ≠ 0) (t : ℝ) : ‖(z - t)⁻¹‖ ≤ |z.im|⁻¹ := by
  rw [norm_inv]
  refine inv_anti₀ (abs_pos.mpr hz) ?_
  simpa using abs_im_le_norm (z - t)

/-- The resolvent of `∫ λ dF(λ)` at a non-real `z` is `∫ (z - λ)⁻¹ dF(λ)`. -/
lemma resolvent_integralPMap_ofReal {z : ℂ} (hz : z.im ≠ 0) :
    (F.integralPMap fun t => (t : ℂ)).resolvent z = F.integral fun t : ℝ => (z - t)⁻¹ := by
  have hid : Measurable fun t : ℝ => (t : ℂ) := Complex.measurable_ofReal
  have hr : Measurable fun t : ℝ => (z - t)⁻¹ := by fun_prop
  have hrb : ∃ C, ∀ t : ℝ, ‖(z - (t : ℂ))⁻¹‖ ≤ C := ⟨_, norm_inv_sub_ofReal_le hz⟩
  have hne : ∀ t : ℝ, z - (t : ℂ) ≠ 0 := fun t h => hz (by simpa using congrArg Complex.im h)
  have hzr : ∃ C, ∀ t : ℝ, ‖z * (z - (t : ℂ))⁻¹‖ ≤ C := ⟨‖z‖ * |z.im|⁻¹, fun t => by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_inv_sub_ofReal_le hz t) (norm_nonneg _)⟩
  -- `λ (z - λ)⁻¹ = z (z - λ)⁻¹ - 1`, bounded
  have hfun : ((fun t : ℝ => (t : ℂ)) * fun t : ℝ => (z - t)⁻¹) =
      (fun t : ℝ => z * (z - t)⁻¹) - fun _ => 1 := by
    ext t
    simp only [Pi.mul_apply, Pi.sub_apply]
    field_simp [hne t]
    ring
  have hfun' : ((fun t : ℝ => (z - t)⁻¹) * fun t : ℝ => (t : ℂ)) =
      (fun t : ℝ => z * (z - t)⁻¹) - fun _ => 1 := by
    rw [mul_comm, hfun]
  have hb : ∃ C, ∀ t : ℝ, ‖((fun t : ℝ => (t : ℂ)) * fun t : ℝ => (z - t)⁻¹) t‖ ≤ C := by
    obtain ⟨C, hC⟩ := hzr
    exact ⟨C + 1, fun t => by
      rw [hfun, Pi.sub_apply]; exact (norm_sub_le _ _).trans (by simpa using hC t)⟩
  have hmulr : Measurable fun t : ℝ => z * (z - t)⁻¹ := hr.const_mul z
  have hgb : ∃ C, ∀ t : ℝ, ‖(((fun t : ℝ => z * (z - t)⁻¹) - fun _ => (1 : ℂ) : ℝ → ℂ)) t‖ ≤ C := by
    rw [← hfun]
    exact hb
  -- `∫ (z (z - λ)⁻¹ - 1) dF = z (∫ (z - λ)⁻¹ dF) - 1`
  have hcalc : ∀ y, F.integral ((fun t : ℝ => z * (z - t)⁻¹) - fun _ => (1 : ℂ) : ℝ → ℂ) y =
      z • F.integral (fun t : ℝ => (z - t)⁻¹) y - y := fun y => by
    rw [F.integral_sub hmulr hzr measurable_const ⟨1, fun _ => by simp⟩, integral_one, sub_apply,
      show (fun t : ℝ => z * (z - t)⁻¹) = z • fun t : ℝ => (z - t)⁻¹ from rfl,
      F.integral_smul hr hrb, smul_apply, one_apply_eq_self]
  refine LinearPMap.resolvent_eq_of (fun x => ?_) (fun u v huv => ?_)
  · have hmem : MemLp ((fun t : ℝ => (t : ℂ)) * fun t : ℝ => (z - t)⁻¹) 2 (F.measure x) :=
      F.memLp_measure_of_bound (hid.mul hr) hb.choose_spec x
    rw [mem_graph_integralPMap]
    refine ⟨(F.memLp_measure_integral_apply_iff hid hr hrb x).mpr hmem, ?_⟩
    rw [F.integralApply_integral_apply hid hr hrb hmem, ← F.integral_apply (hid.mul hr) hb, hfun,
      hcalc]
  · obtain ⟨hu, rfl⟩ := F.mem_graph_integralPMap.mp huv
    have hb' : ∃ C, ∀ t : ℝ, ‖((fun t : ℝ => (z - t)⁻¹) * fun t : ℝ => (t : ℂ)) t‖ ≤ C := by
      rw [hfun']
      exact hgb
    rw [map_sub, map_smul, F.integral_integralApply hid hr hrb hu,
      ← F.integral_apply (hr.mul hid) hb', hfun', hcalc]
    abel

/-! ### Transport along semilinear isometric equivalences -/

section Transport

variable {X K : Type*} [MeasurableSpace X] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K] {σ σ' : ℂ →+* ℂ} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  [RingHomIsometric σ]

/-- The **transport** `s ↦ V E(s) V⁻¹` of a projection-valued measure along a semilinear isometric
equivalence `V`, for the identity or the complex conjugation `σ`. -/
noncomputable def transport (E' : ProjectionValuedMeasure X E) (V : E ≃ₛₗᵢ[σ] K) :
    ProjectionValuedMeasure X K :=
  ofHasSum (fun s => V.toLinearIsometry.toContinuousLinearMap.comp
      ((E' s).comp V.symm.toLinearIsometry.toContinuousLinearMap))
    (fun s hs => by
      rw [E'.apply_of_not_measurableSet hs, ContinuousLinearMap.zero_comp,
        ContinuousLinearMap.comp_zero])
    (fun f hf hd x => (E'.hasSum_apply hf hd (V.symm x)).mapL V.toLinearIsometry.toContinuousLinearMap)
    (fun s => by
      refine ⟨?_, ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr fun x y => ?_⟩
      · change _ * _ = _
        ext x
        rw [mul_apply_eq_comp]
        simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
          LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.symm_apply_apply]
        rw [← mul_apply_eq_comp (E' s),
          (E'.isStarProjection s).isIdempotentElem.eq]
      · simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
          LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]
        conv_lhs => rw [← V.apply_symm_apply y]
        conv_rhs => rw [← V.apply_symm_apply x]
        rw [V.inner_map_mapₛₗ, V.inner_map_mapₛₗ, E'.inner_apply_left])
    (by
      ext x
      simp)

variable (E' : ProjectionValuedMeasure X E) (V : E ≃ₛₗᵢ[σ] K)

/-- `(V E V⁻¹)(s) y = V (E(s) (V⁻¹ y))`. -/
@[simp]
lemma transport_apply (s : Set X) (y : K) : E'.transport V s y = V (E' s (V.symm y)) := rfl

/-- The diagonal measures of the transported measure: `(V E V⁻¹)_y = E_{V⁻¹ y}`. -/
lemma measure_transport (y : K) : (E'.transport V).measure y = E'.measure (V.symm y) := by
  ext s hs
  rw [measure_apply _ hs, measure_apply _ hs, transport_apply, LinearIsometryEquiv.enorm_map]

/-- **Bounded integrals against the transported measure**: `∫ f d(V E V⁻¹) = V (∫ σ⁻¹ ∘ f dE) V⁻¹`;
for an antiunitary `V` this conjugates `f`. -/
lemma integral_transport {f : X → ℂ} (hf : Measurable f) (hfb : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    (E'.transport V).integral f = V.toLinearIsometry.toContinuousLinearMap.comp
      ((E'.integral fun x => σ' (f x)).comp V.symm.toLinearIsometry.toContinuousLinearMap) := by
  obtain ⟨C, hC⟩ := hfb
  refine ContinuousLinearMap.ext_inner_self fun y => ?_
  have h := V.inner_map_mapₛₗ (V.symm y) ((E'.integral fun x => σ' (f x)) (V.symm y))
  rw [V.apply_symm_apply] at h
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry]
  rw [h, inner_integral_self _ hf ⟨C, hC⟩, measure_transport]
  rcases RingHom.eq_id_or_conj_of_ringHomIsometric (σ := σ) (σ' := σ') with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [RingHom.id_apply]
    rw [E'.inner_integral_self hf ⟨C, hC⟩]
  · have hcf : Measurable fun x => starRingEnd ℂ (f x) := Complex.continuous_conj.measurable.comp hf
    have hcfb : ∃ C, ∀ x, ‖starRingEnd ℂ (f x)‖ ≤ C :=
      ⟨C, fun x => by rw [Complex.norm_conj]; exact hC x⟩
    rw [E'.inner_integral_self hcf hcfb, ← integral_conj]
    simp

/-- `f ∈ L²((V E V⁻¹)_y)` iff `σ⁻¹ ∘ f ∈ L²(E_{V⁻¹ y})`. -/
lemma memLp_measure_transport_iff {f : X → ℂ} (hf : Measurable f) (y : K) :
    MemLp f 2 ((E'.transport V).measure y) ↔
      MemLp (fun x => σ' (f x)) 2 (E'.measure (V.symm y)) := by
  rw [measure_transport]
  exact memLp_congr_norm hf.aestronglyMeasurable
    ((RingHom.continuous_of_ringHomInvPair σ).measurable.comp hf).aestronglyMeasurable
    (Eventually.of_forall fun x => (RingHom.norm_apply_of_ringHomInvPair σ (f x)).symm)

/-- **Unbounded integrals against the transported measure**:
`(∫ f d(V E V⁻¹)) y = V (∫ σ⁻¹ ∘ f dE) V⁻¹ y` for `f ∈ L²((V E V⁻¹)_y)`. -/
lemma integralApply_transport {f : X → ℂ} (hf : Measurable f) {y : K}
    (hy : MemLp f 2 ((E'.transport V).measure y)) :
    (E'.transport V).integralApply f y = V (E'.integralApply (fun x => σ' (f x)) (V.symm y)) := by
  have hσ := (RingHom.continuous_of_ringHomInvPair (σ' := σ') σ).measurable
  have hy' := (E'.memLp_measure_transport_iff V hf y).mp hy
  set a := fun n => SimpleFunc.approxOn f hf univ 0 (mem_univ 0) n
  have hσa : ∀ n, Measurable fun x => σ' (a n x) := fun n => hσ.comp (a n).measurable
  have hσf : Measurable fun x => σ' (f x) := hσ.comp hf
  have hab : ∀ n, ∃ C, ∀ x, ‖σ' (a n x)‖ ≤ C := fun n =>
    ⟨(a n).exists_forall_norm_le.choose, fun x => by
      rw [RingHom.norm_apply_of_ringHomInvPair σ]
      exact (a n).exists_forall_norm_le.choose_spec x⟩
  suffices key : Tendsto (fun n => (E'.transport V).simpleIntegral (a n) y) atTop
      (𝓝 (V (E'.integralApply (fun x => σ' (f x)) (V.symm y)))) from
    tendsto_nhds_unique ((E'.transport V).tendsto_simpleIntegral_approxOn hf hy) key
  have h₁ : ∀ n, (E'.transport V).simpleIntegral (a n) y =
      V (E'.integralApply (fun x => σ' (a n x)) (V.symm y)) := fun n => by
    rw [← integral_simpleFunc, E'.integral_transport V (a n).measurable
      (a n).exists_forall_norm_le, ← E'.integral_apply (hσa n) (hab n)]
    rfl
  simp_rw [h₁]
  refine (V.continuous.tendsto _).comp (tendsto_iff_edist_tendsto_0.mpr ?_)
  have h₂ : ∀ n, edist (E'.integralApply (fun x => σ' (a n x)) (V.symm y))
      (E'.integralApply (fun x => σ' (f x)) (V.symm y)) =
        eLpNorm (⇑(a n) - f) 2 ((E'.transport V).measure y) := fun n => by
    rw [E'.edist_integralApply (hσa n) hσf
      (E'.memLp_measure_of_bound (hσa n) (hab n).choose_spec _) hy',
      measure_transport]
    refine eLpNorm_congr_norm_ae ((hσa n).sub hσf).aestronglyMeasurable
      ((a n).measurable.sub hf).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply, ← map_sub, RingHom.norm_apply_of_ringHomInvPair σ]
  simp_rw [h₂]
  exact (E'.transport V).tendsto_eLpNorm_approxOn hf hy

/-- **Integrals against the transported measure**: `(∫ f d(V E V⁻¹)) V = V ∫ σ⁻¹ ∘ f dE`. -/
lemma integralPMap_transport_compNat {f : X → ℂ} (hf : Measurable f) :
    ((E'.transport V).integralPMap f).compNat ((V : E →ₛₗ[σ] K).toPMap ⊤) =
      (V : E →ₛₗ[σ] K).compPMap (E'.integralPMap fun x => σ' (f x)) := by
  -- domain and values of the integrals are computed vector by vector
  refine (LinearPMap.compNat_toPMap_eq_compPMap_iff V.toLinearEquiv).mpr fun u v => ?_
  have key : ∀ y z : K, (y, z) ∈ ((E'.transport V).integralPMap f).graph ↔
      (V.symm y, V.symm z) ∈ (E'.integralPMap fun x => σ' (f x)).graph := fun y z => by
    rw [mem_graph_integralPMap, mem_graph_integralPMap, E'.memLp_measure_transport_iff V hf y]
    constructor
    · rintro ⟨hy, rfl⟩
      refine ⟨hy, ?_⟩
      rw [E'.integralApply_transport V hf ((E'.memLp_measure_transport_iff V hf y).mpr hy),
        LinearIsometryEquiv.symm_apply_apply]
    · rintro ⟨hy, hz⟩
      refine ⟨hy, ?_⟩
      rw [E'.integralApply_transport V hf ((E'.memLp_measure_transport_iff V hf y).mpr hy), hz,
        LinearIsometryEquiv.apply_symm_apply]
  rw [key]
  exact Iff.of_eq (by simp only [LinearIsometryEquiv.coe_toLinearEquiv,
    LinearIsometryEquiv.symm_apply_apply])

/-- Transport commutes with images: `(V E V⁻¹)` under `g` is `V (g_* E) V⁻¹`. -/
lemma transport_map {Y : Type*} [MeasurableSpace Y] {g : X → Y} (hg : Measurable g) :
    (E'.transport V).map g hg = (E'.map g hg).transport V :=
  ext _ fun s hs => by
    ext y
    rw [map_apply _ hg hs, transport_apply, transport_apply, map_apply _ hg hs]

/-- Transporting twice along an involutive `V` gives back `E`. -/
lemma transport_transport {V' : K ≃ₛₗᵢ[σ] E} (hV : ∀ x, V' (V x) = x) :
    (E'.transport V).transport V' = E' :=
  ext _ fun s hs => by
    ext x
    have h₁ : V'.symm x = V x := by
      conv_lhs => rw [← hV x]
      exact V'.symm_apply_apply _
    rw [transport_apply, transport_apply, h₁, V.symm_apply_apply, hV]

end Transport

end MeasureTheory.ProjectionValuedMeasure

namespace IsSelfAdjoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A)

include hA in
/-- **Resolvent representation**: `(z - A)⁻¹ = ∫ (z - λ)⁻¹ dE_A(λ)` for non-real `z`. -/
lemma resolvent_eq_integral_pvm {z : ℂ} (hz : z.im ≠ 0) :
    A.resolvent z = hA.pvm.integral fun t : ℝ => (z - t)⁻¹ :=
  ContinuousLinearMap.ext_inner_self fun u => by
    rw [hA.inner_resolvent_eq_integral u (hA.mem_resolventSet hz),
      hA.pvm.inner_integral_self (by fun_prop) ⟨_, ProjectionValuedMeasure.norm_inv_sub_ofReal_le hz⟩]

include hA in
/-- Two self-adjoint operators with the same resolvent at `i` are equal. -/
lemma eq_of_resolvent_I_eq {B : E →ₗ.[ℂ] E} (hB : IsSelfAdjoint B)
    (h : A.resolvent I = B.resolvent I) : A = B := by
  refine IsSelfAdjoint.eq_of_le hB hA.isFormalAdjoint (LinearPMap.le_of_le_graph fun p hp => ?_)
  obtain ⟨u, v⟩ := p
  have h' := LinearPMap.resolvent_mem_graph (hA.mem_resolventSet (z := I) (by simp)) (I • u - v)
  rwa [h, LinearPMap.resolvent_sub_apply (hB.mem_resolventSet (z := I) (by simp)) hp,
    sub_sub_cancel] at h'

include hA in
/-- **Spectral theorem**: a self-adjoint operator is the spectral integral of the identity
against its projection-valued measure, `A = ∫ λ dE_A(λ)`. -/
theorem eq_integralPMap_pvm : A = hA.pvm.integralPMap fun t => (t : ℂ) :=
  hA.eq_of_resolvent_I_eq
    (hA.pvm.isSelfAdjoint_integralPMap_ofReal (φ := fun t : ℝ => t) measurable_id') (by
      rw [hA.resolvent_eq_integral_pvm (by simp), hA.pvm.resolvent_integralPMap_ofReal (by simp)])

include hA in
/-- **Domain of a self-adjoint operator**: `y ∈ dom A` iff `∫ λ² dμ_y < ∞`. -/
lemma mem_domain_iff_memLp {y : E} :
    y ∈ A.domain ↔ MemLp (fun t : ℝ => (t : ℂ)) 2 (hA.pvm.measure y) := by
  conv_lhs => rw [hA.eq_integralPMap_pvm]
  rfl

include hA in
/-- `⟪y, A y⟫ = ∫ λ dμ_y(λ)` for `y ∈ dom A`, in graph form. -/
lemma inner_eq_integral_of_mem_graph {y z : E} (h : (y, z) ∈ A.graph) :
    ⟪y, z⟫_ℂ = ∫ t, (t : ℂ) ∂(hA.pvm.measure y) := by
  rw [hA.eq_integralPMap_pvm, ProjectionValuedMeasure.mem_graph_integralPMap] at h
  rw [← h.2, hA.pvm.inner_integralApply_self Complex.measurable_ofReal h.1]

/-- A self-adjoint operator is positive iff its projection-valued measure vanishes on `(-∞, 0)`. -/
lemma isPositive_iff_pvm_Iio_eq_zero : A.IsPositive ↔ hA.pvm (Iio 0) = 0 := by
  refine ⟨fun hpos => (hA.pvm.apply_eq_zero_iff measurableSet_Iio).mpr fun u =>
    hA.measure_pvm_Iio_zero u hpos, fun h => ?_⟩
  have h' : ∀ u, ∀ᵐ t ∂(hA.pvm.measure u), 0 ≤ t := fun u => by
    have := (hA.pvm.apply_eq_zero_iff measurableSet_Iio).mp h u
    rw [measure_eq_zero_iff_ae_notMem] at this
    filter_upwards [this] with t ht
    simpa using ht
  rw [hA.eq_integralPMap_pvm, hA.pvm.integralPMap_congr_ae (g := fun t => ((max t 0 : ℝ) : ℂ))
    measurable_ofReal (by fun_prop) fun u => (h' u).mono fun t ht => by simp [max_eq_left ht]]
  exact hA.pvm.isPositive_integralPMap_ofReal (by fun_prop) fun t => le_max_right t 0

include hA in
/-- **Uniqueness of `E_A`**: the projection-valued measure `E_A` is the only projection-valued
measure `F` on `ℝ` with `A = ∫ λ dF(λ)`. -/
theorem eq_pvm_of_eq_integralPMap (F : ProjectionValuedMeasure ℝ E)
    (hF : A = F.integralPMap fun t => (t : ℂ)) : F = hA.pvm := by
  have hI : (I : ℂ).im ≠ 0 := by simp
  have hR : A.resolvent I = F.integral fun t : ℝ => (I - t)⁻¹ := by
    rw [hF, F.resolvent_integralPMap_ofReal hI]
  have hr : Measurable fun t : ℝ => (I - t)⁻¹ := by fun_prop
  have hrb : ∀ t : ℝ, ‖(I - (t : ℂ))⁻¹‖ ≤ 1 := fun t => by
    simpa using ProjectionValuedMeasure.norm_inv_sub_ofReal_le hI t
  have hG : F.map (fun t : ℝ => (I - t)⁻¹) hr = (hA.isStarNormal_resolvent I).pvm := by
    refine (hA.isStarNormal_resolvent I).eq_pvm_of_inner_self_eq_integral _
      (isCompact_closedBall 0 1) ?_ fun x => ?_
    · rw [ProjectionValuedMeasure.map_apply _ hr Metric.isClosed_closedBall.measurableSet.compl]
      convert F.apply_empty
      ext t
      simpa using hrb t
    · rw [hR, F.inner_integral_self hr ⟨1, hrb⟩, ProjectionValuedMeasure.measure_map]
      exact (integral_map hr.aemeasurable aestronglyMeasurable_id).symm
  refine F.ext_of_measure fun x => ?_
  change F.measure x = ((hA.isStarNormal_resolvent I).pvm.map (fun ζ => re (I - ζ⁻¹))
    (by fun_prop)).measure x
  rw [← hG, ProjectionValuedMeasure.measure_map, ProjectionValuedMeasure.measure_map,
    Measure.map_map (by fun_prop) hr]
  have h : ((fun ζ : ℂ => re (I - ζ⁻¹)) ∘ fun t : ℝ => (I - t)⁻¹) = id := by
    ext t
    change re (I - ((I - (t : ℂ))⁻¹)⁻¹) = t
    rw [inv_inv, sub_sub_cancel, ofReal_re]
  rw [h, Measure.map_id]

/-- **Functions of a self-adjoint operator**: for a measurable real `g` and a projection-valued
measure `F` on `ℝ`, the projection-valued measure of the self-adjoint operator `∫ g dF` is the
image `g_* F`; for `F = E_A`, the projection-valued measure of `g(A)` is `g_* E_A`. -/
lemma _root_.MeasureTheory.ProjectionValuedMeasure.pvm_integralPMap_ofReal
    (F : ProjectionValuedMeasure ℝ E) {g : ℝ → ℝ} (hg : Measurable g) :
    (F.isSelfAdjoint_integralPMap_ofReal hg).pvm = F.map g hg :=
  ((F.isSelfAdjoint_integralPMap_ofReal hg).eq_pvm_of_eq_integralPMap _ (by
    rw [ProjectionValuedMeasure.integralPMap_map hg _ Complex.measurable_ofReal]
    rfl)).symm

/-- **Composition rule**: `f(∫ g dF) = ∫ f ∘ g dF` for a measurable real `g` and measurable `f`; for
`F = E_A`, `f(g(A)) = (f ∘ g)(A)`. -/
lemma _root_.MeasureTheory.ProjectionValuedMeasure.integralPMap_pvm_integralPMap_ofReal
    (F : ProjectionValuedMeasure ℝ E) {g : ℝ → ℝ} (hg : Measurable g) {f : ℝ → ℂ}
    (hf : Measurable f) :
    (F.isSelfAdjoint_integralPMap_ofReal hg).pvm.integralPMap f = F.integralPMap (f ∘ g) := by
  rw [F.pvm_integralPMap_ofReal hg, ProjectionValuedMeasure.integralPMap_map hg _ hf]

/-! ### Covariance -/

section Covariance

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {σ σ' : ℂ →+* ℂ} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] [RingHomIsometric σ]

omit [CompleteSpace E] [CompleteSpace K] [RingHomIsometric σ] in
/-- **Resolvents along a semilinear isometric equivalence**: if `S V = V T`, then
`(z - S)⁻¹ = V (σ⁻¹ z - T)⁻¹ V⁻¹`. -/
lemma _root_.LinearPMap.resolvent_eq_comp_of_compNat_toPMap_eq {T : E →ₗ.[ℂ] E}
    {S : K →ₗ.[ℂ] K} (V : E ≃ₛₗᵢ[σ] K)
    (hTS : S.compNat ((V : E →ₛₗ[σ] K).toPMap ⊤) = (V : E →ₛₗ[σ] K).compPMap T) {z : ℂ}
    (hz : σ' z ∈ T.resolventSet) :
    S.resolvent z = V.toLinearIsometry.toContinuousLinearMap.comp
      ((T.resolvent (σ' z)).comp V.symm.toLinearIsometry.toContinuousLinearMap) := by
  -- the resolvent is characterised by its values on graph points
  replace hTS := (LinearPMap.compNat_toPMap_eq_compPMap_iff V.toLinearEquiv).mp hTS
  simp only [LinearIsometryEquiv.coe_toLinearEquiv] at hTS
  refine LinearPMap.resolvent_eq_of (fun x => ?_) (fun u v huv => ?_)
  · have h := (hTS _ _).mp (LinearPMap.resolvent_mem_graph hz (V.symm x))
    simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry]
    rwa [map_sub, V.map_smulₛₗ, RingHomInvPair.comp_apply_eq₂, V.apply_symm_apply] at h
  · have h : (V.symm u, V.symm v) ∈ T.graph := by
      rw [hTS, V.apply_symm_apply, V.apply_symm_apply]
      exact huv
    simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry]
    rw [map_sub V.symm, V.symm.map_smulₛₗ, LinearPMap.resolvent_sub_apply hz h, V.apply_symm_apply]

include hA in
/-- **Covariance of the projection-valued measure**: if a semilinear isometric equivalence `V`
(unitary or antiunitary) satisfies `B V = V A` for a self-adjoint `B`, then `E_B = V E_A V⁻¹`. -/
theorem pvm_eq_transport {B : K →ₗ.[ℂ] K} (hB : IsSelfAdjoint B) (V : E ≃ₛₗᵢ[σ] K)
    (hAB : B.compNat ((V : E →ₛₗ[σ] K).toPMap ⊤) = (V : E →ₛₗ[σ] K).compPMap A) :
    hB.pvm = hA.pvm.transport V := by
  refine (hB.eq_pvm_of_eq_integralPMap _ (hB.eq_of_resolvent_I_eq
    ((hA.pvm.transport V).isSelfAdjoint_integralPMap_ofReal (φ := fun t : ℝ => t)
      measurable_id') ?_)).symm
  have hσI : (σ' I).im ≠ 0 := by
    rcases RingHom.eq_id_or_conj_of_ringHomIsometric (σ := σ) (σ' := σ') with
      ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp
  have hr : Measurable fun t : ℝ => (I - t)⁻¹ := by fun_prop
  rw [(hA.pvm.transport V).resolvent_integralPMap_ofReal (by simp),
    ProjectionValuedMeasure.integral_transport _ _ hr
      ⟨_, ProjectionValuedMeasure.norm_inv_sub_ofReal_le (by simp)⟩,
    LinearPMap.resolvent_eq_comp_of_compNat_toPMap_eq V hAB
      (hA.mem_resolventSet (z := σ' I) hσI), hA.resolvent_eq_integral_pvm hσI]
  rcases RingHom.eq_id_or_conj_of_ringHomIsometric (σ := σ) (σ' := σ') with
    ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp

include hA in
/-- **Covariance of the functional calculus**: if a semilinear isometric equivalence `V` satisfies
`B V = V A` for a self-adjoint `B`, then `f(B) = V (σ⁻¹ ∘ f)(A) V⁻¹` for bounded measurable `f`;
for an antiunitary `V`, `f(B) = V f̄(A) V⁻¹`. -/
lemma integral_pvm_eq_comp {B : K →ₗ.[ℂ] K} (hB : IsSelfAdjoint B) (V : E ≃ₛₗᵢ[σ] K)
    (hAB : B.compNat ((V : E →ₛₗ[σ] K).toPMap ⊤) = (V : E →ₛₗ[σ] K).compPMap A) {f : ℝ → ℂ}
    (hf : Measurable f)
    (hfb : ∃ C, ∀ t, ‖f t‖ ≤ C) :
    hB.pvm.integral f = V.toLinearIsometry.toContinuousLinearMap.comp
      ((hA.pvm.integral fun t => σ' (f t)).comp V.symm.toLinearIsometry.toContinuousLinearMap) := by
  rw [hA.pvm_eq_transport hB V hAB, ProjectionValuedMeasure.integral_transport _ _ hf hfb]

end Covariance

end IsSelfAdjoint
