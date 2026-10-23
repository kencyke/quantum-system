/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Cone.Extension
public import Mathlib.Analysis.RCLike.Extend
public import Mathlib.LinearAlgebra.Complex.Module

/-!
# Extending positive functionals from a subspace containing an order unit

Let `E` be an ordered complex ⋆-vector space whose positive elements are self-adjoint, and let
`u ≥ 0` be an order unit for the self-adjoint elements: every self-adjoint `x` satisfies
`x ≤ r • u` for some real `r`. A positive linear functional on a ⋆-closed subspace `p ∋ u` extends
to a positive linear functional on `E` (`exists_extension_nonneg_of_orderUnit`).

The proof applies the M. Riesz extension theorem (`riesz_extension`) to the real part of the
functional and the cone of elements with positive real part `ℜ x = (x + x⋆)/2`; the order unit
makes `p` and this cone span `E`. The extension is then complexified (`Module.Dual.extendRCLike`):
on a positive `x` the real extension vanishes at `i • x`, whose real part is `0`, so the complex
extension is real and positive there.
-/

@[expose] public section

open scoped ComplexOrder ComplexStarModule

/-- **Extension of positive functionals.** In an ordered complex ⋆-vector space `E` whose
positive elements are self-adjoint and are preserved by positive real scalars, let `u ≥ 0` be an
order unit for the self-adjoint elements. A positive linear functional `f` on a ⋆-closed subspace
`p` containing `u` extends to a positive linear functional on `E`. -/
theorem exists_extension_nonneg_of_orderUnit {E : Type*} [AddCommGroup E] [Module ℂ E]
    [StarAddMonoid E] [StarModule ℂ E] [PartialOrder E] [IsOrderedAddMonoid E]
    (hsa : ∀ x : E, 0 ≤ x → IsSelfAdjoint x)
    (hsmul : ∀ (c : ℝ) (x : E), 0 ≤ c → 0 ≤ x → 0 ≤ (c : ℂ) • x)
    {u : E} (hu : 0 ≤ u) (hle : ∀ x : E, IsSelfAdjoint x → ∃ r : ℝ, x ≤ (r : ℂ) • u)
    (p : Submodule ℂ E) (hstar : ∀ x ∈ p, star x ∈ p) (hup : u ∈ p)
    (f : p →ₗ[ℂ] ℂ) (hf : ∀ x : p, 0 ≤ (x : E) → 0 ≤ f x) :
    ∃ F : E →ₗ[ℂ] ℂ, (∀ x : p, F x = f x) ∧ ∀ x, 0 ≤ x → 0 ≤ F x := by
  -- `f` is real on the self-adjoint elements of `p`, which lie below a multiple of `u`
  have hre : ∀ x : p, IsSelfAdjoint (x : E) → (f x).im = 0 := by
    intro x hx
    obtain ⟨r, hr⟩ := hle x hx
    have h₁ := (Complex.le_def.mp (hf (⟨(r : ℂ) • u, p.smul_mem _ hup⟩ - x) (by simpa using hr))).2
    have h₂ := (Complex.le_def.mp (hf ⟨u, hup⟩ hu)).2
    have : f ⟨(r : ℂ) • u, p.smul_mem _ hup⟩ = (r : ℂ) * f ⟨u, hup⟩ := by
      rw [← smul_eq_mul, ← map_smul]; rfl
    rw [map_sub, this, Complex.sub_im, Complex.mul_im, ← h₂] at h₁
    simpa using h₁.symm
  have hℜ : ∀ x ∈ p, (ℜ x : E) ∈ p := fun x hx => by
    rw [realPart_apply_coe]
    exact p.smul_of_tower_mem _ (p.add_mem hx (hstar x hx))
  have hℑ : ∀ x ∈ p, (ℑ x : E) ∈ p := fun x hx => by
    rw [imaginaryPart_apply_coe]
    exact p.smul_mem _ (p.smul_of_tower_mem _ (p.sub_mem hx (hstar x hx)))
  have hfre : ∀ x : p, (f x).re = (f ⟨ℜ (x : E), hℜ x x.2⟩).re := by
    intro x
    have hx : x = ⟨ℜ (x : E), hℜ x x.2⟩ + Complex.I • ⟨ℑ (x : E), hℑ x x.2⟩ :=
      Subtype.ext (realPart_add_I_smul_imaginaryPart (x : E)).symm
    conv_lhs => rw [hx, map_add, map_smul]
    simp [hre ⟨_, hℑ x x.2⟩ (ℑ (x : E)).2]
  -- the cone of elements with positive real part
  let s : PointedCone ℝ E :=
    { carrier := {x | 0 ≤ (ℜ x : E)}
      add_mem' := fun {x y} hx hy => by
        change 0 ≤ (ℜ (x + y) : E)
        rw [map_add, AddSubgroup.coe_add]
        exact add_nonneg hx hy
      zero_mem' := by simp
      smul_mem' := fun c {x} hx => by
        change 0 ≤ (ℜ x : E) at hx
        change 0 ≤ (ℜ (c • x) : E)
        have : (ℜ (c • x) : E) = ((c : ℝ) : ℂ) • (ℜ x : E) := by
          rw [show c • x = (c : ℝ) • x from rfl, map_smul, selfAdjoint.val_smul]
          exact (Complex.coe_smul _ _).symm
        rw [this]
        exact hsmul c _ c.2 hx }
  have hs : ∀ x, x ∈ s ↔ 0 ≤ (ℜ x : E) := fun _ => Iff.rfl
  -- the real part of `f`, as a partially defined real functional
  let fr : E →ₗ.[ℝ] ℝ :=
    { domain := p.restrictScalars ℝ
      toFun :=
        { toFun := fun x => (f ⟨x.1, x.2⟩).re
          map_add' := fun x y => by
            rw [← Complex.add_re, ← map_add]; rfl
          map_smul' := fun c x => by
            rw [RingHom.id_apply, smul_eq_mul, ← Complex.re_ofReal_mul, ← smul_eq_mul, ← map_smul]
            rfl } }
  obtain ⟨g, hgf, hgs⟩ := riesz_extension s fr
    (fun x hx => by
      change 0 ≤ (f ⟨x.1, x.2⟩).re
      rw [hfre]
      exact (Complex.le_def.mp (hf _ ((hs _).mp hx))).1)
    (fun y => by
      obtain ⟨r, hr⟩ := hle (-(ℜ y : E)) (ℜ y).2.neg
      refine ⟨⟨(r : ℂ) • u, p.smul_mem _ hup⟩, ?_⟩
      rw [hs, map_add, AddSubgroup.coe_add,
        IsSelfAdjoint.coe_realPart (IsSelfAdjoint.smul (Complex.conj_ofReal r) (hsa u hu))]
      exact neg_le_iff_add_nonneg.mp hr)
  -- the real extension vanishes at `i • x` for self-adjoint `x`, since `ℜ (i • x) = 0`
  have hg0 : ∀ x : E, IsSelfAdjoint x → g (Complex.I • x) = 0 := by
    intro x hx
    have hℜI : (ℜ (Complex.I • x) : E) = 0 := by
      rw [realPart_apply_coe, star_smul, hx.star_eq, Complex.star_def, Complex.conj_I, neg_smul,
        add_neg_cancel, smul_zero]
    have h₁ := hgs _ ((hs _).mpr hℜI.ge)
    have h₂ := hgs _ ((hs _).mpr (by rw [map_neg, NegMemClass.coe_neg, hℜI, neg_zero]) :
      -(Complex.I • x) ∈ s)
    rw [map_neg] at h₂
    linarith
  have hF : ∀ x, Module.Dual.extendRCLike (𝕜 := ℂ) g x = g x - Complex.I * g (Complex.I • x) :=
    fun x => Module.Dual.extendRCLike_apply g x
  refine ⟨Module.Dual.extendRCLike g, fun x => ?_, fun x hx => ?_⟩
  · have h₁ := hgf x
    have h₂ := hgf ⟨Complex.I • (x : E), p.smul_mem _ x.2⟩
    change g x = (f x).re at h₁
    change g (Complex.I • (x : E)) = (f (Complex.I • x)).re at h₂
    have h₃ : f (Complex.I • x) = Complex.I * f x := by rw [map_smul, smul_eq_mul]
    rw [h₃, Complex.mul_re] at h₂
    apply Complex.ext <;> simp [hF, h₁, h₂]
  · rw [hF, hg0 x (hsa x hx)]
    have : 0 ≤ g x := hgs x ((hs x).mpr ((IsSelfAdjoint.coe_realPart (hsa x hx)).symm ▸ hx))
    simpa using this
