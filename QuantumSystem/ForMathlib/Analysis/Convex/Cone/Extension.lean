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
public import Mathlib.LinearAlgebra.LinearPMap

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

When the order unit is moreover Archimedean, `x ≥ 0` as soon as `x + ε • u ≥ 0` for every `ε > 0`,
the positive functionals detect positivity: a self-adjoint `x` that is not positive has
`F x < 0` for a positive `F` with `F u = 1` (`exists_nonneg_functional_lt_zero_of_not_nonneg`). The
largest `t` with `t • u ≤ x` exists by the Archimedean property and is negative, and
`a • u + b • x ↦ a + b t` is positive on the span of `u` and `x`, so it extends.
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

/-- **Separation by positive functionals.** Let `E` and `u` be as in
`exists_extension_nonneg_of_orderUnit`, and let `u` moreover be Archimedean: `x` is positive when
`x + ε • u` is for every `ε > 0`. A self-adjoint `x` that is not positive is then separated from the
positive elements by a positive linear functional `F` with `F u = 1` and `F x < 0`. -/
theorem exists_nonneg_functional_lt_zero_of_not_nonneg {E : Type*} [AddCommGroup E] [Module ℂ E]
    [StarAddMonoid E] [StarModule ℂ E] [PartialOrder E] [IsOrderedAddMonoid E]
    (hsa : ∀ x : E, 0 ≤ x → IsSelfAdjoint x)
    (hsmul : ∀ (c : ℝ) (x : E), 0 ≤ c → 0 ≤ x → 0 ≤ (c : ℂ) • x)
    {u : E} (hu : 0 ≤ u) (hle : ∀ x : E, IsSelfAdjoint x → ∃ r : ℝ, x ≤ (r : ℂ) • u)
    (harch : ∀ x : E, (∀ ε : ℝ, 0 < ε → 0 ≤ x + (ε : ℂ) • u) → 0 ≤ x)
    {x : E} (hx : IsSelfAdjoint x) (hx0 : ¬0 ≤ x) :
    ∃ F : E →ₗ[ℂ] ℂ, (∀ y, 0 ≤ y → 0 ≤ F y) ∧ F u = 1 ∧ F x < 0 := by
  have husa : IsSelfAdjoint u := hsa u hu
  obtain ⟨r, hr⟩ := hle (-x) hx.neg
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hx0 (by simpa using hr)
  -- a real multiple `c • u` is positive only for `c ≥ 0`
  have hpos : ∀ c : ℝ, 0 ≤ (c : ℂ) • u → 0 ≤ c := by
    intro c hc
    by_contra hneg
    rw [not_le] at hneg
    have h := hsmul (-c)⁻¹ _ (inv_nonneg.mpr (neg_nonneg.mpr hneg.le)) hc
    have hc' : (-c)⁻¹ * c = -1 := by field_simp [hneg.ne]
    rw [smul_smul, ← Complex.ofReal_mul, hc', Complex.ofReal_neg, Complex.ofReal_one, neg_one_smul]
      at h
    exact hu0 (le_antisymm (neg_nonneg.mp h) hu)
  -- the coefficients of a self-adjoint element of the span are real
  have hreal : ∀ a : ℂ, star a • u = a • u → (a.re : ℂ) = a := fun a h => by
    have h' : (star a - a) • u = 0 := by rw [sub_smul, h, sub_self]
    exact Complex.conj_eq_iff_re.mp (sub_eq_zero.mp ((smul_eq_zero.mp h').resolve_right hu0))
  have hstar : ∀ v : E, IsSelfAdjoint v → ∀ y ∈ ℂ ∙ v, star y ∈ ℂ ∙ v := fun v hv y hy => by
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [star_smul, hv.star_eq]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  -- the largest `t` with `t • u ≤ x`, which is negative
  let A : Set ℝ := {s | (s : ℂ) • u ≤ x}
  have hA : ∀ s ∈ A, s < 0 := fun s hs => by
    by_contra h
    rw [not_lt] at h
    exact hx0 ((hsmul s u h hu).trans hs)
  have hrA : -r ∈ A := by
    change ((-r : ℝ) : ℂ) • u ≤ x
    rw [Complex.ofReal_neg, neg_smul]
    exact neg_le.mp hr
  have hbdd : BddAbove A := ⟨0, fun s hs => (hA s hs).le⟩
  set t := sSup A
  have htA : t ∈ A := by
    change (t : ℂ) • u ≤ x
    rw [← sub_nonneg]
    refine harch _ fun ε hε => ?_
    obtain ⟨s, hs, hts⟩ := exists_lt_of_lt_csSup ⟨-r, hrA⟩ (sub_lt_self t hε)
    have : x - (t : ℂ) • u + (ε : ℂ) • u = (x - (s : ℂ) • u) + ((s - t + ε : ℝ) : ℂ) • u := by
      push_cast
      module
    rw [this]
    exact add_nonneg (sub_nonneg.mpr hs) (hsmul _ u (by linarith) hu)
  have ht : t < 0 := hA t htA
  let f : E →ₗ.[ℂ] ℂ := LinearPMap.mkSpanSingleton u (1 : ℂ) hu0
  have hfu : ∀ h, f ⟨u, h⟩ = 1 := LinearPMap.mkSpanSingleton'_apply_self _ _ _
  by_cases hxu : x ∈ ℂ ∙ u
  · -- `x = c • u` with `c < 0`: extend `a • u ↦ a`
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxu
    have hc : (c.re : ℂ) = c := hreal c (by rw [← hx.star_eq, star_smul, husa.star_eq])
    obtain ⟨F, hFf, hF⟩ := exists_extension_nonneg_of_orderUnit hsa hsmul hu hle f.domain
      (hstar u husa) (Submodule.mem_span_singleton_self u) f.toFun fun z hz => by
        obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp z.2
        have hz' : z = ⟨a • u, ha ▸ z.2⟩ := Subtype.ext ha.symm
        have ha' : (a.re : ℂ) = a := hreal a (by
          rw [ha, ← (hsa _ hz).star_eq, ← ha, star_smul, husa.star_eq])
        change 0 ≤ f z
        rw [hz', LinearPMap.mkSpanSingleton'_apply, RingHom.id_apply, smul_eq_mul, mul_one, ← ha']
        rw [← ha, ← ha'] at hz
        exact Complex.zero_le_real.mpr (hpos _ hz)
    have hFu : F u = 1 := (hFf ⟨u, Submodule.mem_span_singleton_self u⟩).trans (hfu _)
    refine ⟨F, hF, hFu, ?_⟩
    rw [map_smul, hFu, smul_eq_mul, mul_one, ← hc]
    refine Complex.real_lt_real.mpr (lt_of_not_ge fun h => hx0 ?_)
    rw [← hc]
    exact hsmul _ u h hu
  · -- extend `a • u + b • x ↦ a + b t`
    let g := f.supSpanSingleton x (t : ℂ) hxu
    have hgu : u ∈ g.domain := Submodule.mem_sup_left (Submodule.mem_span_singleton_self u)
    have hgx : x ∈ g.domain := Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
    have hgstar : ∀ y ∈ g.domain, star y ∈ g.domain := fun y hy => by
      obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
      rw [star_add]
      exact Submodule.add_mem_sup (hstar u husa y₁ hy₁) (hstar x hx y₂ hy₂)
    obtain ⟨F, hFg, hF⟩ := exists_extension_nonneg_of_orderUnit hsa hsmul hu hle g.domain hgstar hgu
      g.toFun fun z hz => by
        obtain ⟨y₁, hy₁, y₂, hy₂, hy⟩ := Submodule.mem_sup.mp z.2
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy₁
        obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy₂
        have hz' : z = ⟨a • u + b • x, hy ▸ z.2⟩ := Subtype.ext hy.symm
        change 0 ≤ g z
        rw [hz', LinearPMap.supSpanSingleton_apply_mk f x _ hxu _ hy₁ b,
          LinearPMap.mkSpanSingleton'_apply, RingHom.id_apply, RingHom.id_apply, smul_eq_mul,
          mul_one, smul_eq_mul]
        -- the coefficients `a` and `b` are real
        have hsa' := (hsa _ hz).star_eq
        rw [← hy, star_add, star_smul, star_smul, husa.star_eq, hx.star_eq] at hsa'
        have hb : (b.re : ℂ) = b := by
          by_contra hb
          have hb' : star b - b ≠ 0 := fun h => hb (Complex.conj_eq_iff_re.mp (sub_eq_zero.mp h))
          refine hxu (Submodule.mem_span_singleton.mpr ⟨(star b - b)⁻¹ * (a - star a), ?_⟩)
          rw [mul_smul, inv_smul_eq_iff₀ hb', sub_smul, sub_smul, sub_eq_sub_iff_add_eq_add,
            ← hsa', add_comm]
        have hb'' : star b = b := by
          rw [← hb]
          exact Complex.conj_ofReal _
        have ha : (a.re : ℂ) = a := hreal a (by
          rw [hb''] at hsa'
          exact add_right_cancel hsa')
        rw [← hy, ← ha, ← hb] at hz
        rw [← ha, ← hb]
        rw [← Complex.ofReal_mul, ← Complex.ofReal_add]
        refine Complex.zero_le_real.mpr ?_
        rcases lt_or_ge 0 b.re with hb0 | hb0
        · -- `-a / b ≤ t`, as `x ≥ -(a / b) • u`
          have hmem : -a.re / b.re ∈ A := by
            change ((-a.re / b.re : ℝ) : ℂ) • u ≤ x
            rw [← sub_nonneg]
            have := hsmul b.re⁻¹ _ (inv_nonneg.mpr hb0.le) hz
            convert this using 1
            rw [smul_add, smul_smul, smul_smul, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
              inv_mul_cancel₀ hb0.ne', Complex.ofReal_one, one_smul]
            push_cast
            module
          have := (div_le_iff₀ hb0).mp (le_csSup hbdd hmem)
          linarith
        · -- `(a + b t) • u = (a • u + b • x) + (-b) • (x - t • u) ≥ 0`
          refine hpos _ ?_
          have h := add_nonneg hz (hsmul (-b.re) _ (neg_nonneg.mpr hb0) (sub_nonneg.mpr htA))
          convert h using 1
          push_cast
          module
    have hFu : F u = 1 := by
      refine (hFg ⟨u, hgu⟩).trans ?_
      exact (LinearPMap.supSpanSingleton_apply_mk_of_mem f (t : ℂ) hxu
        (Submodule.mem_span_singleton_self u)).trans (hfu _)
    refine ⟨F, hF, hFu, ?_⟩
    have hgx' : g ⟨x, hgx⟩ = t := LinearPMap.supSpanSingleton_apply_self f _ hxu
    rw [show F x = g ⟨x, hgx⟩ from hFg ⟨x, hgx⟩, hgx']
    exact Complex.real_lt_real.mpr ht
