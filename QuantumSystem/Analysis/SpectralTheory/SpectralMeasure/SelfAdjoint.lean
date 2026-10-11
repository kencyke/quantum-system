/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.SpectralTheory.SpectralMeasure.Normal
public import QuantumSystem.Analysis.SpectralTheory.SpectralMeasure.ResolventCFC

/-!
# Spectral measures of self-adjoint operators

Let `A` be a self-adjoint operator on a complex Hilbert space `E`, `w` a point of its resolvent
set and `R_w = (w - A)⁻¹` the resolvent at `w`, a normal bounded operator
(`IsSelfAdjoint.isStarNormal_resolvent`) with projection-valued measure `IsStarNormal.pvm _` on `ℂ`,
whose diagonal measures are the scalar spectral measures `ν_u^w = (IsStarNormal.pvm _).measure u`.
Transporting the projection-valued measure of `R_i` along
`ζ ↦ re (i - ζ⁻¹)`, the inverse of `λ ↦ (i - λ)⁻¹` on the nonzero spectrum of `R_i`, gives the
**projection-valued measure** `E_A` of `A` on `ℝ` (`IsSelfAdjoint.pvm`), and its diagonal measures
are the **scalar spectral measures** `μ_u = ⟪E_A(·) u, u⟫` (`hA.pvm.measure u`). Neither
depends on the base point `i` (`IsSelfAdjoint.pvm_eq_map`,
`IsSelfAdjoint.measure_pvm_eq_map_measure_pvm_resolvent`), and both are tied to `A` by the
Stieltjes representation `⟪x, (z - A)⁻¹ y⟫ = ∫ (z - λ)⁻¹ dE_{x,y}(λ)`.

The complex measures follow Mathlib's convention: `E_{x,y}(s) = ⟪x, E_A(s) y⟫`, conjugate-linear in
`x` (Rudin's and Schmüdgen's `E_{y,x}`). Integrals against them are written part by part,
`∫ f dE_{x,y} = ∫ f d(re E_{x,y}) + i ∫ f d(im E_{x,y})`.

The continuous functional calculus `cfc g R_w` of the bounded normal resolvent is only the means of
constructing `E_A`; functions of `A` are the spectral integrals `f(A) = ∫ f dE_A`. The spectral
lemma in its operator form `A = ∫ λ dE_A(λ)`, the domain characterisation
`dom A = {y | ∫ λ² dμ_y < ∞}`, the uniqueness of `E_A` and this Borel functional calculus are in
`QuantumSystem.Analysis.SpectralTheory.SpectralTheorem`.

## Main definitions

* `IsSelfAdjoint.pvm hA` — the projection-valued measure `E_A` on `ℝ`.
* `hA.pvm.measure u` — the scalar spectral measure `μ_u = ⟪E_A(·) u, u⟫` on `ℝ`.

## Main results

* `IsSelfAdjoint.measure_pvm_eq_map` — `μ_u` is the image of `ν_u^i` under `ζ ↦ re (i - ζ⁻¹)`.
* `IsSelfAdjoint.pvm_eq_map` — base-point independence of `E_A`.
* `IsSelfAdjoint.inner_resolvent_eq_integral_pvm` — **resolvent representation**
  `⟪x, (z - A)⁻¹ y⟫ = ∫ (z - λ)⁻¹ dE_{x,y}(λ)` for `z` in the resolvent set.
* `IsSelfAdjoint.integrable_inv_sub_measure_pvm` — `λ ↦ (z - λ)⁻¹` is `μ_u`-integrable.
* `IsSelfAdjoint.measure_pvm_resolvent_singleton_zero` — `ν_u^w {0} = 0`, because `R_w` has
  dense range.
* `IsSelfAdjoint.pvm_resolvent_singleton_zero` — the projection-valued measure of `R_w` vanishes
  on `{0}`.
* `IsSelfAdjoint.measure_pvm_resolvent_eq_map` — change of base point: `ν_u^w` is the image of
  `ν_u^v` under `ζ ↦ ζ / (1 - (v - w) ζ)`.
* `IsSelfAdjoint.measure_pvm_eq_map_measure_pvm_resolvent` — **base-point independence**:
  `μ_u` is the image of `ν_u^w` under `ζ ↦ re (w - ζ⁻¹)` for every `w` in the resolvent set.
* `IsSelfAdjoint.map_measure_pvm` — `μ_u` pushed forward along `λ ↦ (w - λ)⁻¹` is `ν_u^w`.
* `IsSelfAdjoint.inner_resolvent_eq_integral` — the Stieltjes representation
  `⟪u, (z - A)⁻¹ u⟫ = ∫ (z - λ)⁻¹ dμ_u` for `z` in the resolvent set.
* `IsSelfAdjoint.integral_measure_pvm` — `∫ f dμ_u = ∫ f (re (w - ζ⁻¹)) dν_u^w`.
* `IsSelfAdjoint.pvm_congr` — `E_A` transports along equalities of operators.
-/

@[expose] public section

open Complex MeasureTheory

namespace IsSelfAdjoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {A : E →ₗ.[ℂ] E}

/-- `i` lies in the resolvent set of a self-adjoint operator. -/
lemma I_mem_resolventSet (hA : IsSelfAdjoint A) : I ∈ A.resolventSet :=
  hA.mem_resolventSet (by simp)

/-- The **projection-valued measure** `E_A` of a self-adjoint operator `A` on the Borel sets of
`ℝ`: the image of the projection-valued measure of the resolvent `(i - A)⁻¹` under
`ζ ↦ re (i - ζ⁻¹)`, which inverts `λ ↦ (i - λ)⁻¹` on the nonzero spectrum of `(i - A)⁻¹`. At
`ζ = 0` the map takes Lean's junk value `re (i - 0⁻¹) = 0`; this is harmless, because the
projection-valued measure of `(i - A)⁻¹` vanishes on `{0}`
(`IsSelfAdjoint.pvm_resolvent_singleton_zero`), so no spurious mass is sent to `λ = 0`. Any other
point of the resolvent set gives the same measure (`IsSelfAdjoint.pvm_eq_map`). -/
noncomputable def pvm (hA : IsSelfAdjoint A) : ProjectionValuedMeasure ℝ E :=
  (hA.isStarNormal_resolvent I).pvm.map (fun ζ => re (I - ζ⁻¹)) (by fun_prop)

/-- The scalar spectral measure `μ_u = ⟪E_A(·) u, u⟫`, the diagonal measure of `E_A` at `u`, is
the image of the scalar spectral measure of `(i - A)⁻¹` under `ζ ↦ re (i - ζ⁻¹)`. -/
lemma measure_pvm_eq_map (hA : IsSelfAdjoint A) (u : E) :
    hA.pvm.measure u =
      ((hA.isStarNormal_resolvent I).pvm.measure u).map fun ζ => re (I - ζ⁻¹) := by
  rw [pvm, ProjectionValuedMeasure.measure_map]

variable (hA : IsSelfAdjoint A) (w : ℂ) (u : E)

variable {w} in
/-- `ν_u^w` has no atom at `0`: for `w` in the resolvent set, `(w - A)⁻¹` has dense range
`dom A`. -/
lemma measure_pvm_resolvent_singleton_zero (hw : w ∈ A.resolventSet) :
    (hA.isStarNormal_resolvent w).pvm.measure u {0} = 0 := by
  refine (hA.isStarNormal_resolvent w).measure_pvm_singleton_eq_zero_of_mem_closure_range ?_
  rw [map_zero, sub_zero]
  have := hA.dense_domain u
  rwa [← LinearPMap.range_resolvent hw, LinearMap.coe_range] at this

variable {w} in
/-- The projection-valued measure of `(w - A)⁻¹` vanishes on `{0}`, for `w` in the resolvent set:
all its diagonal measures `ν_u^w` do (`IsSelfAdjoint.measure_pvm_resolvent_singleton_zero`). -/
lemma pvm_resolvent_singleton_zero (hw : w ∈ A.resolventSet) :
    (hA.isStarNormal_resolvent w).pvm {0} = 0 :=
  ((hA.isStarNormal_resolvent w).pvm.apply_eq_zero_iff (MeasurableSet.singleton 0)).mpr fun v =>
    hA.measure_pvm_resolvent_singleton_zero v hw

private lemma measurable_re_sub_inv (w : ℂ) : Measurable fun ζ : ℂ => re (w - ζ⁻¹) := by
  fun_prop

variable {w} in
/-- `ν_u^w`-almost every point is nonzero. -/
lemma ae_ne_zero_measure_pvm_resolvent (hw : w ∈ A.resolventSet) :
    ∀ᵐ ζ ∂((hA.isStarNormal_resolvent w).pvm.measure u), ζ ≠ 0 :=
  ae_iff.mpr (by simpa using hA.measure_pvm_resolvent_singleton_zero u hw)

variable {w} in
/-- **Change of base point.** For `v`, `w` in the resolvent set, `ν_u^w` is the image of `ν_u^v`
under `ζ ↦ ζ / (1 - (v - w) ζ)`, the function sending `(v - A)⁻¹` to `(w - A)⁻¹`
(`IsSelfAdjoint.resolvent_eq_cfc`). -/
lemma measure_pvm_resolvent_eq_map {v : ℂ} (hv : v ∈ A.resolventSet)
    (hw : w ∈ A.resolventSet) :
    (hA.isStarNormal_resolvent w).pvm.measure u =
      ((hA.isStarNormal_resolvent v).pvm.measure u).map fun ζ => ζ / (1 - (v - w) * ζ) := by
  have hφ : ContinuousOn (fun ζ : ℂ => ζ / (1 - (v - w) * ζ)) (spectrum ℂ (A.resolvent v)) :=
    continuousOn_id.div (by fun_prop) fun ζ hζ =>
      LinearPMap.one_sub_mul_ne_zero_of_mem_spectrum hv hw hζ
  have hφT : IsStarNormal (cfc (fun ζ : ℂ => ζ / (1 - (v - w) * ζ)) (A.resolvent v)) :=
    hA.resolvent_eq_cfc hv hw ▸ hA.isStarNormal_resolvent w
  rw [IsStarNormal.pvm_congr _ hφT (hA.resolvent_eq_cfc hv hw),
    (hA.isStarNormal_resolvent v).pvm_cfc_eq_map hφ (by fun_prop) hφT,
    ProjectionValuedMeasure.measure_map]

variable {w} in
/-- **Base-point independence.** For every `w` in the resolvent set, the scalar spectral measure
`μ_u` is the image of `ν_u^w` under `ζ ↦ re (w - ζ⁻¹)`: the construction of `μ_u` does not depend
on the base point `i` used in `IsSelfAdjoint.pvm`. -/
lemma measure_pvm_eq_map_measure_pvm_resolvent (hw : w ∈ A.resolventSet) :
    hA.pvm.measure u =
      ((hA.isStarNormal_resolvent w).pvm.measure u).map fun ζ => re (w - ζ⁻¹) := by
  have hφm : Measurable fun ζ : ℂ => ζ / (1 - (I - w) * ζ) := by fun_prop
  rw [measure_pvm_eq_map, hA.measure_pvm_resolvent_eq_map u hA.I_mem_resolventSet hw,
    Measure.map_map (measurable_re_sub_inv w) hφm]
  refine Measure.map_congr ?_
  filter_upwards [(hA.isStarNormal_resolvent I).ae_mem_spectrum_measure_pvm u,
    hA.ae_ne_zero_measure_pvm_resolvent u hA.I_mem_resolventSet] with ζ hζ h0
  have h1 := LinearPMap.one_sub_mul_ne_zero_of_mem_spectrum hA.I_mem_resolventSet hw hζ
  simp only [Function.comp_apply]
  congr 1
  rw [inv_div]
  field_simp
  ring

variable {w} in
/-- The spectral measure `μ_u` recovers `ν_u^w` under `λ ↦ (w - λ)⁻¹`. -/
lemma map_measure_pvm (hw : w ∈ A.resolventSet) :
    (hA.pvm.measure u).map (fun t : ℝ => (w - t)⁻¹) =
      (hA.isStarNormal_resolvent w).pvm.measure u := by
  have hψ : Measurable fun t : ℝ => (w - t)⁻¹ := by fun_prop
  rw [hA.measure_pvm_eq_map_measure_pvm_resolvent u hw,
    Measure.map_map hψ (measurable_re_sub_inv w)]
  conv_rhs => rw [← Measure.map_id (μ := (hA.isStarNormal_resolvent w).pvm.measure u)]
  refine Measure.map_congr ?_
  filter_upwards [(hA.isStarNormal_resolvent w).ae_mem_spectrum_measure_pvm u,
    hA.ae_ne_zero_measure_pvm_resolvent u hw] with ζ hζ h0
  have him := hA.im_sub_inv_eq_zero_of_mem_spectrum hw hζ h0
  have hre : ((re (w - ζ⁻¹) : ℝ) : ℂ) = w - ζ⁻¹ := Complex.ext rfl (by simpa using him.symm)
  simp only [Function.comp_apply, hre, sub_sub_cancel, inv_inv, id_eq]

variable {w} in
/-- Spectral integral formula on the real line. For `w` in the resolvent set and `g`
continuous on the spectrum of `R = (w - A)⁻¹`, `∫ g ((w - λ)⁻¹) dμ_u(λ) = ⟪u, cfc g R u⟫`. -/
private lemma integral_measure_pvm_eq_inner_cfc (hw : w ∈ A.resolventSet) {g : ℂ → ℂ}
    (hg : ContinuousOn g (spectrum ℂ (A.resolvent w))) :
    ∫ t, g ((w - t)⁻¹) ∂(hA.pvm.measure u) = inner ℂ u (cfc g (A.resolvent w) u) := by
  have hψ : Measurable fun t : ℝ => (w - t)⁻¹ := by fun_prop
  rw [(hA.isStarNormal_resolvent w).inner_cfc_eq_integral_measure_pvm u hg,
    ← hA.map_measure_pvm u hw, integral_map hψ.aemeasurable]
  rw [hA.map_measure_pvm u hw]
  exact ((hA.isStarNormal_resolvent w).integrable_measure_pvm u hg).aestronglyMeasurable

omit hA in
/-- The projection-valued measure transports along equalities of operators, whatever proofs of
self-adjointness are used to build it. -/
lemma pvm_congr {B : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (h : A = B) :
    hA.pvm = hB.pvm := by
  subst h
  rfl

variable {w} in
/-- Integration against the spectral measure `μ_u` is integration against `ν_u^w` after the
change of variables `λ = re (w - ζ⁻¹)`, for any `w` in the resolvent set. -/
lemma integral_measure_pvm (hw : w ∈ A.resolventSet) {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (hA.pvm.measure u)) :
    ∫ t, f t ∂(hA.pvm.measure u) =
      ∫ ζ, f (re (w - ζ⁻¹)) ∂((hA.isStarNormal_resolvent w).pvm.measure u) := by
  rw [hA.measure_pvm_eq_map_measure_pvm_resolvent u hw] at hf ⊢
  rw [integral_map (measurable_re_sub_inv w).aemeasurable hf]

omit [CompleteSpace E] in
private lemma inv_sub_eq_comp (z : ℂ) (t : ℝ) :
    (I - (t : ℂ))⁻¹ / (1 - (I - z) * (I - (t : ℂ))⁻¹) = (z - t)⁻¹ := by
  have hIt : I - (t : ℂ) ≠ 0 := fun h => by simpa using congrArg im h
  rw [show (1 : ℂ) - (I - z) * (I - (t : ℂ))⁻¹ = (z - t) * (I - (t : ℂ))⁻¹ by
    field_simp
    ring, div_eq_mul_inv, mul_inv, inv_inv, mul_comm (z - (t : ℂ))⁻¹, ← mul_assoc,
    inv_mul_cancel₀ hIt, one_mul]

private lemma continuousOn_resolvent_fun (hA : IsSelfAdjoint A) {z : ℂ} (hz : z ∈ A.resolventSet) :
    ContinuousOn (fun ζ : ℂ => ζ / (1 - (I - z) * ζ)) (spectrum ℂ (A.resolvent I)) :=
  continuousOn_id.div (by fun_prop) fun ζ hζ =>
    LinearPMap.one_sub_mul_ne_zero_of_mem_spectrum hA.I_mem_resolventSet hz hζ

/-- **Stieltjes representation.** For `z` in the resolvent set of `A`,
`⟪u, (z - A)⁻¹ u⟫ = ∫ (z - λ)⁻¹ dμ_u(λ)`. -/
lemma inner_resolvent_eq_integral {z : ℂ} (hz : z ∈ A.resolventSet) :
    inner ℂ u (A.resolvent z u) = ∫ t, (z - t)⁻¹ ∂(hA.pvm.measure u) := by
  rw [hA.resolvent_eq_cfc hA.I_mem_resolventSet hz,
    ← hA.integral_measure_pvm_eq_inner_cfc u hA.I_mem_resolventSet
      (hA.continuousOn_resolvent_fun hz)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun t => inv_sub_eq_comp z t)

variable {u} in
/-- For `z` in the resolvent set, `λ ↦ (z - λ)⁻¹` is `μ_u`-integrable. -/
lemma integrable_inv_sub_measure_pvm {z : ℂ} (hz : z ∈ A.resolventSet) :
    Integrable (fun t : ℝ => (z - t)⁻¹) (hA.pvm.measure u) := by
  have hψ : Measurable fun t : ℝ => (I - t)⁻¹ := by fun_prop
  have h := (hA.isStarNormal_resolvent I).integrable_measure_pvm u
    (hA.continuousOn_resolvent_fun hz)
  rw [← hA.map_measure_pvm u hA.I_mem_resolventSet] at h
  have h' := (integrable_map_measure h.aestronglyMeasurable hψ.aemeasurable).mp h
  exact h'.congr (Filter.Eventually.of_forall fun t => inv_sub_eq_comp z t)

/-! ### The projection-valued measure -/

variable {w} in
/-- **Base-point independence** of `E_A`: for every `w` in the resolvent set, `E_A` is the image of
the projection-valued measure of `(w - A)⁻¹` under `ζ ↦ re (w - ζ⁻¹)`. -/
theorem pvm_eq_map (hw : w ∈ A.resolventSet) :
    hA.pvm = (hA.isStarNormal_resolvent w).pvm.map (fun ζ => re (w - ζ⁻¹)) (by fun_prop) :=
  ProjectionValuedMeasure.ext_of_measure _ fun u => by
    rw [ProjectionValuedMeasure.measure_map,
      hA.measure_pvm_eq_map_measure_pvm_resolvent u hw]

variable (x y : E)

variable {x y} in
/-- **Resolvent representation**: for `z` in the resolvent set,
`⟪x, (z - A)⁻¹ y⟫ = ∫ (z - λ)⁻¹ dE_{x,y}(λ)`, the integral against the complex measure `E_{x,y}`
of `E_A` being taken part by part. -/
theorem inner_resolvent_eq_integral_pvm {z : ℂ} (hz : z ∈ A.resolventSet) :
    inner ℂ x (A.resolvent z y) = ∫ᵛ t, (z - t)⁻¹ ∂<•(hA.pvm.complexMeasure x y).re +
      I * ∫ᵛ t, (z - t)⁻¹ ∂<•(hA.pvm.complexMeasure x y).im := by
  have hi : ∀ u : E, VectorMeasure.Integrable (hA.pvm.measure u).toSignedMeasure
      (fun t : ℝ => (z - t)⁻¹) := fun u =>
    SignedMeasure.integrable_toSignedMeasure_iff.mpr (hA.integrable_inv_sub_measure_pvm hz)
  rw [ProjectionValuedMeasure.re_complexMeasure, ProjectionValuedMeasure.im_complexMeasure]
  rw [VectorMeasure.integral_smul_vectorMeasure,
    VectorMeasure.integral_smul_vectorMeasure, VectorMeasure.integral_sub_vectorMeasure (hi _) (hi _),
    VectorMeasure.integral_sub_vectorMeasure (hi _) (hi _), VectorMeasure.integral_toSignedMeasure,
    VectorMeasure.integral_toSignedMeasure, VectorMeasure.integral_toSignedMeasure,
    VectorMeasure.integral_toSignedMeasure, ← hA.inner_resolvent_eq_integral _ hz,
    ← hA.inner_resolvent_eq_integral _ hz, ← hA.inner_resolvent_eq_integral _ hz,
    ← hA.inner_resolvent_eq_integral _ hz]
  exact ContinuousLinearMap.inner_apply_eq_polarization x y

end IsSelfAdjoint
