/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.UnboundedOperator.SpectralMeasure
public import QuantumSystem.Analysis.UnboundedOperator.VonNeumann
public import QuantumSystem.ForMathlib.Analysis.Complex.Basic
public import QuantumSystem.ForMathlib.MeasureTheory.Function.LpSpace.Linfty

/-!
# Multiplication operators on `L²(μ)` and their spectral measures

Let `μ` be a measure on `α`. For `f ∈ L∞(μ)`, the scalar spectral measure of the normal operator
`M_f` on `L²(μ)` at `u` is the image of `|u|² μ` under `f`
(`MeasureTheory.Linfty.measure_pvm_mulL2`), from `g(M_f) = M_{g ∘ f}`.

For an unbounded function `φ : α → ℂ`, the **maximal multiplication operator** `M_φ`
(`MeasureTheory.L2.mulPMap`) has domain `{u ∈ L² | φ u ∈ L²}` and sends `u` to `φ u`; `M_φ̄` is a
formal adjoint of it. For a real measurable `h`, `M_h` is self-adjoint
(`MeasureTheory.L2.isSelfAdjoint_mulPMap`): it is symmetric, and `M_h ± i` are onto, with inverses
the bounded multiplications by `(h ± i)⁻¹`. Its resolvent is `(i - M_h)⁻¹ = M_{(i - h)⁻¹}`
(`MeasureTheory.L2.resolvent_I_mulPMap`), and its scalar spectral measures are `μ_u = h_*(|u|² μ)`
(`MeasureTheory.L2.measure_pvm_mulPMap`). None of this needs a hypothesis on `μ`: the parts of
`μ` carrying no `L²` vectors are not seen by the operators, and `|u|² μ` is always finite.

A symmetric operator `A` which extends `M_h` is `M_h` itself (`IsSelfAdjoint.eq_of_le`), since
`A ≤ M_h† = M_h`. This identifies every operator that acts as multiplication by `h` in a given
representation, such as the relative modular operators of the multiplication algebra
(`QuantumSystem.Analysis.Entropy.Araki.Multiplication`).

## Main definitions

* `MeasureTheory.L2.mulPMap φ` — the maximal multiplication operator `M_φ` on `L²(μ)`.

## Main results

* `MeasureTheory.Linfty.measure_pvm_mulL2` — `ν_u(M_f) = f_*(|u|² μ)`.
* `MeasureTheory.L2.mem_graph_mulPMap` — `(u, v) ∈ graph M_φ ↔ φ u ∈ L² ∧ v = φ u`.
* `MeasureTheory.L2.isFormalAdjoint_mulPMap` — `⟪M_φ u, w⟫ = ⟪u, M_φ̄ w⟫`.
* `MeasureTheory.L2.isSelfAdjoint_mulPMap` — `M_h` is self-adjoint for real measurable `h`.
* `MeasureTheory.L2.resolvent_I_mulPMap` — `(i - M_h)⁻¹ = M_{(i - h)⁻¹}`.
* `MeasureTheory.L2.measure_pvm_mulPMap` — `μ_u(M_h) = h_*(|u|² μ)`.
-/

@[expose] public section

open Complex MeasureTheory Filter
open scoped ENNReal InnerProductSpace BoundedContinuousFunction ComplexConjugate LinearPMap

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace MeasureTheory.Linfty

/-- **Scalar spectral measures of multiplication operators**: for `f ∈ L∞`, the scalar spectral
measure of `M_f` at `u`, the diagonal measure of its projection-valued measure, is `f_*(|u|² μ)`. -/
theorem measure_pvm_mulL2 (f : Lp ℂ ∞ μ) (u : Lp ℂ 2 μ) :
    (isStarNormal_mulL2 f).pvm.measure u = (μ.withDensity fun x => ‖u x‖ₑ ^ 2).map f := by
  have hfm : Measurable (⇑f) := (Lp.stronglyMeasurable f).measurable
  refine ((isStarNormal_mulL2 f).eq_measure_pvm_of_integral _ fun g => ?_).symm
  set gC : ℂ →ᵇ ℂ := BoundedContinuousFunction.comp (fun r : ℝ => (r : ℂ))
    Complex.isometry_ofReal.lipschitzWith g
  have hgC : (fun ζ => (g ζ : ℂ)) = ⇑gC := rfl
  rw [hgC, cfc_mulL2 gC f, integral_map hfm.aemeasurable g.continuous.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul (measurable_enorm_sq u)
      (Eventually.of_forall fun x => by simp), MeasureTheory.L2.inner_def,
    ← show ∫ a, (⟪u a, (mulL2 (compBCF gC f) u) a⟫_ℂ).re ∂μ =
        (∫ a, ⟪u a, (mulL2 (compBCF gC f) u) a⟫_ℂ ∂μ).re by
      simpa using integral_re (𝕜 := ℂ)
        (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) u (mulL2 (compBCF gC f) u))]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_mulL2 (compBCF gC f) u, coeFn_compBCF gC f] with x h₁ h₂
  rw [h₁, Pi.mul_apply, h₂, Function.comp_apply, RCLike.inner_apply,
    mul_assoc, Complex.mul_conj', smul_eq_mul, ENNReal.toReal_pow, toReal_enorm]
  change _ = ((g (f x) : ℂ) * ((‖u x‖ : ℂ) ^ 2)).re
  rw [← ofReal_pow, ← ofReal_mul, ofReal_re, mul_comm]

/-- The bounded function `(i - h)⁻¹`, as an element of `L∞`. -/
noncomputable def resolventFun {h : α → ℝ} (hh : Measurable h) : Lp ℂ ∞ μ :=
  (memLp_top_of_bound (by fun_prop : Measurable fun x => (I - (h x : ℂ))⁻¹).aestronglyMeasurable
    1 (Eventually.of_forall fun x => Complex.norm_inv_I_sub_ofReal_le (h x))).toLp _

lemma coeFn_resolventFun {h : α → ℝ} (hh : Measurable h) :
    ⇑(resolventFun (μ := μ) hh) =ᵐ[μ] fun x => (I - (h x : ℂ))⁻¹ :=
  MemLp.coeFn_toLp _

end MeasureTheory.Linfty

namespace MeasureTheory.L2

open Linfty

/-- The **maximal multiplication operator** `M_φ` on `L²(μ)` by a function `φ : α → ℂ`: its domain
is `{u ∈ L² | φ u ∈ L²}`, and it sends `u` to `φ u`. -/
noncomputable def mulPMap (φ : α → ℂ) : Lp ℂ 2 μ →ₗ.[ℂ] Lp ℂ 2 μ where
  domain :=
    { carrier := {u | MemLp (fun x => φ x * u x) 2 μ}
      add_mem' := fun {u v} (hu : MemLp _ 2 μ) (hv : MemLp _ 2 μ) => (hu.add hv).ae_eq <| by
        filter_upwards [Lp.coeFn_add u v] with x hx
        rw [hx, Pi.add_apply, Pi.add_apply, mul_add]
      zero_mem' := (Lp.memLp (0 : Lp ℂ 2 μ)).ae_eq <| by
        filter_upwards [Lp.coeFn_zero ℂ 2 μ] with x hx
        rw [hx, Pi.zero_apply, mul_zero]
      smul_mem' := fun c u (hu : MemLp _ 2 μ) => (hu.const_smul c).ae_eq <| by
        filter_upwards [Lp.coeFn_smul c (u : Lp ℂ 2 μ)] with x hx
        rw [hx, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm] }
  toFun :=
    { toFun := fun u => MemLp.toLp _ (show MemLp (fun x => φ x * u.1 x) 2 μ from u.2)
      map_add' := fun u v => Lp.ext <| by
        filter_upwards [MemLp.coeFn_toLp (show MemLp (fun x => φ x * (u + v).1 x) 2 μ from (u + v).2),
          MemLp.coeFn_toLp (show MemLp (fun x => φ x * u.1 x) 2 μ from u.2),
          MemLp.coeFn_toLp (show MemLp (fun x => φ x * v.1 x) 2 μ from v.2),
          Lp.coeFn_add u.1 v.1, Lp.coeFn_add (MemLp.toLp _ (show MemLp (fun x => φ x * u.1 x) 2 μ from u.2))
            (MemLp.toLp _ (show MemLp (fun x => φ x * v.1 x) 2 μ from v.2))] with x h₁ h₂ h₃ h₄ h₅
        rw [h₅, Pi.add_apply, h₁, h₂, h₃, Submodule.coe_add, h₄, Pi.add_apply, mul_add]
      map_smul' := fun c u => Lp.ext <| by
        filter_upwards [MemLp.coeFn_toLp (show MemLp (fun x => φ x * (c • u).1 x) 2 μ from (c • u).2),
          MemLp.coeFn_toLp (show MemLp (fun x => φ x * u.1 x) 2 μ from u.2),
          Lp.coeFn_smul c u.1, Lp.coeFn_smul c
            (MemLp.toLp _ (show MemLp (fun x => φ x * u.1 x) 2 μ from u.2))] with x h₁ h₂ h₃ h₄
        rw [RingHom.id_apply, h₄, Pi.smul_apply, h₁, h₂, Submodule.coe_smul, h₃, Pi.smul_apply,
          smul_eq_mul, smul_eq_mul, mul_left_comm] }

variable {φ : α → ℂ}

/-- The domain of `M_φ` is `{u ∈ L² | φ u ∈ L²}`. -/
lemma mem_domain_mulPMap {u : Lp ℂ 2 μ} :
    u ∈ (mulPMap φ).domain ↔ MemLp (fun x => φ x * u x) 2 μ :=
  Iff.rfl

/-- `M_φ u = φ u` almost everywhere. -/
lemma coeFn_mulPMap (u : (mulPMap (μ := μ) φ).domain) :
    ⇑(mulPMap φ u) =ᵐ[μ] fun x => φ x * (u : Lp ℂ 2 μ) x :=
  MemLp.coeFn_toLp (show MemLp (fun x => φ x * (u : Lp ℂ 2 μ) x) 2 μ from u.2)

/-- The graph of `M_φ`: `(u, v) ∈ graph M_φ ↔ φ u ∈ L² ∧ v = φ u`. -/
theorem mem_graph_mulPMap {u v : Lp ℂ 2 μ} :
    (u, v) ∈ (mulPMap φ).graph ↔
      MemLp (fun x => φ x * u x) 2 μ ∧ ⇑v =ᵐ[μ] fun x => φ x * u x := by
  refine ⟨fun huv => ?_, fun ⟨hu, hv⟩ => ?_⟩
  · obtain ⟨w, rfl, rfl⟩ := (LinearPMap.mem_graph_iff _).mp huv
    exact ⟨w.2, coeFn_mulPMap w⟩
  · refine (LinearPMap.mem_graph_iff _).mpr ⟨⟨u, hu⟩, rfl, Lp.ext ?_⟩
    exact (coeFn_mulPMap ⟨u, hu⟩).trans hv.symm

/-- **`M_φ̄` is a formal adjoint of `M_φ`**: `⟪φ u, w⟫ = ⟪u, φ̄ w⟫` on the domains. -/
theorem isFormalAdjoint_mulPMap :
    (mulPMap (μ := μ) φ).IsFormalAdjoint (mulPMap fun x => conj (φ x)) := fun u w => by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_mulPMap u, coeFn_mulPMap w] with x h₁ h₂
  rw [h₁, h₂, RCLike.inner_apply, RCLike.inner_apply, map_mul]
  ring

/-- `M_φ` maps its domain onto `L²` after adding `z`, if `(z + φ)⁻¹` is (almost everywhere) the
bounded function `Ψ`. -/
private lemma exists_mem_graph_mulPMap_smul_add {z : ℂ} {Ψ : Lp ℂ ∞ μ} {ψ : α → ℂ}
    (hΨ : ⇑Ψ =ᵐ[μ] ψ) (hψ : ∀ x, (z + φ x) * ψ x = 1) (g : Lp ℂ 2 μ) :
    ∃ u v, (u, v) ∈ (mulPMap φ).graph ∧ z • u + v = g := by
  refine ⟨mulL2 Ψ g, g - z • mulL2 Ψ g, ?_, add_sub_cancel _ _⟩
  have hv : ⇑(g - z • mulL2 Ψ g) =ᵐ[μ] fun x => φ x * mulL2 Ψ g x := by
    filter_upwards [Lp.coeFn_sub g (z • mulL2 Ψ g), Lp.coeFn_smul z (mulL2 Ψ g), coeFn_mulL2 Ψ g,
      hΨ] with x h₁ h₂ h₃ h₄
    rw [h₁, Pi.sub_apply, h₂, Pi.smul_apply, h₃, Pi.mul_apply, h₄, smul_eq_mul]
    linear_combination -(g x) * hψ x
  exact mem_graph_mulPMap.mpr ⟨(Lp.memLp _).ae_eq hv, hv⟩

variable {h : α → ℝ}

/-- **Multiplication by a real function is self-adjoint**: for measurable `h : α → ℝ`, the
maximal multiplication operator `M_h` is self-adjoint. It is symmetric, and `M_h ± i` map its
domain onto `L²`, with inverses the bounded multiplications by `(h ± i)⁻¹`. -/
theorem isSelfAdjoint_mulPMap (hh : Measurable h) :
    IsSelfAdjoint (mulPMap (μ := μ) fun x => (h x : ℂ)) := by
  have hsymm : (mulPMap (μ := μ) fun x => (h x : ℂ)).IsFormalAdjoint
      (mulPMap fun x => (h x : ℂ)) := by
    simpa only [conj_ofReal] using isFormalAdjoint_mulPMap (μ := μ) (φ := fun x => (h x : ℂ))
  refine hsymm.isSelfAdjoint_of_surjective_conj I
    (exists_mem_graph_mulPMap_smul_add (coeFn_resolventFun hh.neg) fun x => ?_)
    (exists_mem_graph_mulPMap_smul_add (Ψ := -resolventFun hh)
      ((Lp.coeFn_neg _).trans ((coeFn_resolventFun hh).neg)) fun x => ?_)
  · have hne : I + (h x : ℂ) ≠ 0 := fun h => by simpa using congrArg im h
    rw [Pi.neg_apply, ofReal_neg, sub_neg_eq_add, mul_inv_cancel₀ hne]
  · have hne : I - (h x : ℂ) ≠ 0 := fun h => by simpa using congrArg im h
    rw [Pi.neg_apply, conj_I, ← mul_inv_cancel₀ hne]
    ring

/-- **Resolvent of a multiplication operator**: `(i - M_h)⁻¹ = M_{(i - h)⁻¹}`. -/
theorem resolvent_I_mulPMap (hh : Measurable h) :
    (mulPMap (μ := μ) fun x => (h x : ℂ)).resolvent I = mulL2 (resolventFun hh) := by
  set Ψ := resolventFun (μ := μ) hh
  have hΨ : ⇑Ψ =ᵐ[μ] fun x => (I - (h x : ℂ))⁻¹ := coeFn_resolventFun (μ := μ) hh
  have key : ∀ x, (mulL2 Ψ x, I • mulL2 Ψ x - x) ∈ (mulPMap fun x => (h x : ℂ)).graph := fun x => by
    have hv : ⇑(I • mulL2 Ψ x - x) =ᵐ[μ] fun y => (h y : ℂ) * mulL2 Ψ x y := by
      filter_upwards [Lp.coeFn_sub (I • mulL2 Ψ x) x, Lp.coeFn_smul I (mulL2 Ψ x), coeFn_mulL2 Ψ x,
        hΨ] with y h₁ h₂ h₃ h₄
      rw [h₁, Pi.sub_apply, h₂, Pi.smul_apply, h₃, Pi.mul_apply, h₄, smul_eq_mul]
      have hne : I - (h y : ℂ) ≠ 0 := fun h => by simpa using congrArg im h
      field_simp
      ring
    exact mem_graph_mulPMap.mpr ⟨(Lp.memLp _).ae_eq hv, hv⟩
  refine LinearPMap.resolvent_eq_of key fun u v huv => ?_
  set w := mulL2 Ψ (I • u - v)
  have hd : (u - w, I • (u - w)) ∈ (mulPMap fun x => (h x : ℂ)).graph := by
    have heq : (u, v) - (w, I • w - (I • u - v)) = (u - w, I • (u - w)) := by
      refine Prod.ext rfl ?_
      simp only [Prod.snd_sub]
      module
    rw [← heq]
    exact Submodule.sub_mem _ huv (key (I • u - v))
  have h0 := LinearPMap.resolvent_sub_apply (isSelfAdjoint_mulPMap hh).I_mem_resolventSet hd
  rw [sub_self, map_zero] at h0
  exact (sub_eq_zero.mp h0.symm).symm

/-- **Spectral measures of a multiplication operator**: for measurable `h : α → ℝ`, the scalar
spectral measure of the self-adjoint `M_h` at `u` is `h_*(|u|² μ)`. -/
theorem measure_pvm_mulPMap (hh : Measurable h) (u : Lp ℂ 2 μ) :
    (isSelfAdjoint_mulPMap (μ := μ) hh).pvm.measure u =
      (μ.withDensity fun x => ‖u x‖ₑ ^ 2).map h := by
  have hΨm : Measurable (⇑(resolventFun (μ := μ) hh)) :=
    (Lp.stronglyMeasurable _).measurable
  have hφ : Measurable fun ζ : ℂ => re (I - ζ⁻¹) := by fun_prop
  rw [IsSelfAdjoint.measure_pvm_eq_map, IsStarNormal.pvm_congr _ (isStarNormal_mulL2 _)
    (resolvent_I_mulPMap hh), measure_pvm_mulL2, Measure.map_map hφ hΨm]
  refine Measure.map_congr ?_
  filter_upwards [(withDensity_absolutelyContinuous μ _).ae_le (coeFn_resolventFun (μ := μ) hh)]
    with x hx
  rw [Function.comp_apply, hx, inv_inv, sub_sub_cancel, ofReal_re]

end MeasureTheory.L2
