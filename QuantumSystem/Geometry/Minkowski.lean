/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Convex.Cone.Basic
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.LinearAlgebra.BilinearForm.Basic

/-!
# Minkowski space and the Rindler wedge

On `ℝ × E` (time `x⁰`, space `x⃗ ∈ E`, a real inner product space) this file defines the
Minkowski form `η(x, y) = x⁰ y⁰ - ⟪x⃗, y⃗⟫` (`Minkowski.form`), the closed forward light cone
`V̄₊ = {‖x⃗‖ ≤ x⁰}` (`Minkowski.forwardCone`) and, for a unit vector `e ∈ E`, the closed Rindler
wedge `W̄ = {|x⁰| ≤ x¹}` with `x¹ = ⟪e, x⃗⟫` (`Minkowski.wedge`). For `E = EuclideanSpace ℝ (Fin d)`
and `e = e₁` this is the right wedge `W̄_R` of `ℝ^{1+d}`.

Every `x` decomposes as `x = r ℓ₊ + s ℓ₋ + z` (`Minkowski.eq_lightPlus_add`) with the light-like
vectors `ℓ₊ = (1, e) ∈ W̄ ∩ V̄₊`, `ℓ₋ = (-1, e) ∈ W̄ ∩ -V̄₊` and `z` in the edge
`{x⁰ = x¹ = 0} = W̄ ∩ -W̄`. The wedge boost `Λ_W(θ)` (`Minkowski.wedgeBoost`) multiplies `ℓ₊`
by `e^θ` and `ℓ₋` by `e^{-θ}`, and the wedge reflection `j_W : (x⁰, x¹, x⊥) ↦ (-x⁰, -x¹, x⊥)`
(`Minkowski.wedgeReflection`) negates both. `Λ_W` and `j_W` are given by their formulas and shown
to preserve `η`, with `Λ_W(θ)` preserving `V̄₊` and `W̄` and `j_W` mapping them onto `-V̄₊` and
`-W̄ = W̄'`. The Lorentz group itself is not formalised.

## Main definitions

* `Minkowski.form E` — the Minkowski form `η` on `ℝ × E`.
* `Minkowski.forwardCone E`, `Minkowski.wedge e` — `V̄₊` and the Rindler wedge `W̄` in `ℝ × E`;
  `Minkowski.mem_forwardCone_iff_form` is `V̄₊ = {x | x⁰ ≥ 0, η(x, x) ≥ 0}`.
* `Minkowski.wedgeBoost e θ`, `Minkowski.wedgeReflection e` — `Λ_W(θ)` and `j_W`, as linear maps
  of `ℝ × E`; for a unit vector `e`, `Minkowski.wedgeBoost_add` is the group law
  `Λ_W(θ + θ') = Λ_W(θ) Λ_W(θ')` and `Minkowski.wedgeReflection_comp_self` is `j_W² = 1`.
* `Minkowski.lightPlus e`, `Minkowski.lightMinus e`, `Minkowski.edge e x` — `ℓ₊`, `ℓ₋` and the
  edge component `(0, x⊥)` of `x`.

## Main results

* `Minkowski.wedgeBoost_form`, `Minkowski.wedgeReflection_form` — `Λ_W(θ)` and `j_W` preserve `η`.
* `Minkowski.wedgeBoost_mem_forwardCone`, `Minkowski.wedgeBoost_mem_wedge` — `Λ_W(θ) V̄₊ ⊆ V̄₊`
  and `Λ_W(θ) W̄ ⊆ W̄`.
* `Minkowski.neg_wedgeReflection_mem_forwardCone`, `Minkowski.neg_wedgeReflection_mem_wedge` —
  `j_W V̄₊ ⊆ -V̄₊` and `j_W W̄ ⊆ -W̄`.
* `Minkowski.eq_lightPlus_add` — the light-cone decomposition `x = r ℓ₊ + s ℓ₋ + z`.
-/

@[expose] public section

open scoped InnerProductSpace

namespace Minkowski

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The closed forward light cone `V̄₊ = {x | ‖x⃗‖ ≤ x⁰}` in `ℝ × E`. -/
noncomputable def forwardCone : ProperCone ℝ (ℝ × E) where
  carrier := {x | ‖x.2‖ ≤ x.1}
  add_mem' {x y} hx hy := (norm_add_le _ _).trans (add_le_add hx hy)
  zero_mem' := by simp
  smul_mem' c x hx := by
    change ‖(c : ℝ) • x.2‖ ≤ (c : ℝ) * x.1
    rw [norm_smul, Real.norm_of_nonneg c.2]
    exact mul_le_mul_of_nonneg_left hx c.2
  isClosed' := isClosed_le continuous_snd.norm continuous_fst

variable {E} in
/-- `x ∈ V̄₊` iff `‖x⃗‖ ≤ x⁰`. -/
lemma mem_forwardCone_iff {x : ℝ × E} : x ∈ forwardCone E ↔ ‖x.2‖ ≤ x.1 := Iff.rfl

/-- The **Minkowski form** `η(x, y) = x⁰ y⁰ - ⟪x⃗, y⃗⟫` on `ℝ × E`. -/
noncomputable def form : LinearMap.BilinForm ℝ (ℝ × E) :=
  LinearMap.mk₂ ℝ (fun x y => x.1 * y.1 - ⟪x.2, y.2⟫_ℝ)
    (fun x x' y => by simp only [Prod.fst_add, Prod.snd_add, inner_add_left]; ring)
    (fun c x y => by
      simp only [Prod.smul_fst, Prod.smul_snd, real_inner_smul_left, smul_eq_mul]; ring)
    (fun x y y' => by simp only [Prod.fst_add, Prod.snd_add, inner_add_right]; ring)
    (fun c x y => by
      simp only [Prod.smul_fst, Prod.smul_snd, real_inner_smul_right, smul_eq_mul]; ring)

/-- `η(x, y) = x⁰ y⁰ - ⟪x⃗, y⃗⟫`. -/
@[simp] lemma form_apply (x y : ℝ × E) : form E x y = x.1 * y.1 - ⟪x.2, y.2⟫_ℝ := rfl

variable {E} in
/-- The forward light cone in terms of the Minkowski form: `V̄₊ = {x | x⁰ ≥ 0, η(x, x) ≥ 0}`. -/
lemma mem_forwardCone_iff_form {x : ℝ × E} : x ∈ forwardCone E ↔ 0 ≤ x.1 ∧ 0 ≤ form E x x := by
  rw [mem_forwardCone_iff, form_apply, real_inner_self_eq_norm_sq]
  constructor
  · intro h
    have := norm_nonneg x.2
    exact ⟨by linarith, by nlinarith⟩
  · rintro ⟨h0, h⟩
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) h0 two_ne_zero).mp (by linarith)

variable {E} (e : E)

/-- The closed **Rindler wedge** `W̄_e = {x | |x⁰| ≤ ⟪e, x⃗⟫}` in the direction of a unit vector
`e` of `E`; for `E = EuclideanSpace ℝ (Fin d)` and `e = e₁` it is the right wedge
`W̄_R = {|x⁰| ≤ x¹}` of `ℝ^{1+d}`. (For a non-unit `e ≠ 0` it is still a closed convex cone, with a
different opening angle, and for `e = 0` it degenerates to the hyperplane `{x⁰ = 0}`; the theorems
below assume `‖e‖ = 1`.) -/
noncomputable def wedge : ProperCone ℝ (ℝ × E) where
  carrier := {x | |x.1| ≤ ⟪e, x.2⟫_ℝ}
  add_mem' {x y} hx hy := by
    change |x.1 + y.1| ≤ ⟪e, x.2 + y.2⟫_ℝ
    rw [inner_add_right]
    exact (abs_add_le _ _).trans (add_le_add hx hy)
  zero_mem' := by simp
  smul_mem' c x hx := by
    change |(c : ℝ) * x.1| ≤ ⟪e, (c : ℝ) • x.2⟫_ℝ
    rw [abs_mul, abs_of_nonneg c.2, real_inner_smul_right]
    exact mul_le_mul_of_nonneg_left hx c.2
  isClosed' := isClosed_le (continuous_abs.comp continuous_fst)
    (continuous_const.inner continuous_snd)

/-- `x ∈ W̄_e` iff `|x⁰| ≤ ⟪e, x⃗⟫`. -/
lemma mem_wedge_iff {x : ℝ × E} : x ∈ wedge e ↔ |x.1| ≤ ⟪e, x.2⟫_ℝ := Iff.rfl

/-- The **wedge boost** `Λ_W(θ)`: the Lorentz boost of rapidity `θ` in the plane of `x⁰` and
`x¹ = ⟪e, x⃗⟫`, `(x⁰, x¹, x⊥) ↦ (cosh θ x⁰ + sinh θ x¹, sinh θ x⁰ + cosh θ x¹, x⊥)`. For a unit
vector `e` the boosts form a one-parameter group (`Minkowski.wedgeBoost_add`) of isometries of the
Minkowski form (`Minkowski.wedgeBoost_form`) preserving `V̄₊` and `W̄`
(`Minkowski.wedgeBoost_mem_forwardCone`, `Minkowski.wedgeBoost_mem_wedge`). -/
noncomputable def wedgeBoost (θ : ℝ) : (ℝ × E) →ₗ[ℝ] (ℝ × E) where
  toFun x := (Real.cosh θ * x.1 + Real.sinh θ * ⟪e, x.2⟫_ℝ,
    x.2 + (Real.sinh θ * x.1 + Real.cosh θ * ⟪e, x.2⟫_ℝ - ⟪e, x.2⟫_ℝ) • e)
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, inner_add_right, Prod.mk_add_mk, Prod.mk.injEq]
    exact ⟨by ring, by module⟩
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, real_inner_smul_right, smul_eq_mul, RingHom.id_apply,
      Prod.smul_mk, Prod.mk.injEq]
    exact ⟨by ring, by module⟩

/-- The components of `Λ_W(θ) x`. -/
@[simp] lemma wedgeBoost_apply (θ : ℝ) (x : ℝ × E) :
    wedgeBoost e θ x = (Real.cosh θ * x.1 + Real.sinh θ * ⟪e, x.2⟫_ℝ,
      x.2 + (Real.sinh θ * x.1 + Real.cosh θ * ⟪e, x.2⟫_ℝ - ⟪e, x.2⟫_ℝ) • e) :=
  rfl

/-- `Λ_W(0) = 1`. -/
@[simp] lemma wedgeBoost_zero : wedgeBoost e 0 = LinearMap.id := by
  refine LinearMap.ext fun x => Prod.ext ?_ ?_
  · simp
  · simp

/-- The **wedge reflection** `j_W : (x⁰, x¹, x⊥) ↦ (-x⁰, -x¹, x⊥)`, `x¹ = ⟪e, x⃗⟫`; for a unit
vector `e` it is an involution (`Minkowski.wedgeReflection_comp_self`) and an isometry of the
Minkowski form (`Minkowski.wedgeReflection_form`) mapping `V̄₊` onto `-V̄₊` and `W̄` onto `-W̄`
(`Minkowski.neg_wedgeReflection_mem_forwardCone`, `Minkowski.neg_wedgeReflection_mem_wedge`). -/
noncomputable def wedgeReflection : (ℝ × E) →ₗ[ℝ] (ℝ × E) where
  toFun x := (-x.1, x.2 - (2 * ⟪e, x.2⟫_ℝ) • e)
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, inner_add_right, Prod.mk_add_mk, Prod.mk.injEq]
    exact ⟨by ring, by module⟩
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, real_inner_smul_right, smul_eq_mul, RingHom.id_apply,
      Prod.smul_mk, Prod.mk.injEq]
    exact ⟨by ring, by module⟩

/-- The components of `j_W x`. -/
@[simp] lemma wedgeReflection_apply (x : ℝ × E) :
    wedgeReflection e x = (-x.1, x.2 - (2 * ⟪e, x.2⟫_ℝ) • e) :=
  rfl

/-- The light-like vector `ℓ₊ = (1, e)`. -/
abbrev lightPlus : ℝ × E := (1, e)

/-- The light-like vector `ℓ₋ = (-1, e)`. -/
abbrev lightMinus : ℝ × E := (-1, e)

/-- The edge component `(0, x⊥)` of `x`, `x⊥ = x⃗ - ⟪e, x⃗⟫ e`. -/
noncomputable abbrev edge (x : ℝ × E) : ℝ × E := (0, x.2 - ⟪e, x.2⟫_ℝ • e)

/-- `x = r ℓ₊ + s ℓ₋ + z` with `r = (x¹ + x⁰)/2`, `s = (x¹ - x⁰)/2` and `z = (0, x⊥)`. -/
lemma eq_lightPlus_add (x : ℝ × E) :
    x = ((⟪e, x.2⟫_ℝ + x.1) / 2) • lightPlus e + ((⟪e, x.2⟫_ℝ - x.1) / 2) • lightMinus e +
      edge e x := by
  refine Prod.ext ?_ ?_
  · simp only [Prod.smul_mk, smul_eq_mul, mul_one, mul_neg, Prod.mk_add_mk, add_zero]
    ring
  · simp only [Prod.snd_add, Prod.smul_snd, edge, lightPlus, lightMinus]
    module

variable {e} (he : ‖e‖ = 1)
include he

/-- **The group law** `Λ_W(θ + θ') = Λ_W(θ) Λ_W(θ')` of the wedge boosts of a unit vector. -/
lemma wedgeBoost_add (θ θ' : ℝ) :
    wedgeBoost e (θ + θ') = wedgeBoost e θ ∘ₗ wedgeBoost e θ' := by
  refine LinearMap.ext fun x => Prod.ext ?_ ?_
  · simp only [LinearMap.coe_comp, Function.comp_apply, wedgeBoost_apply, Real.cosh_add,
      Real.sinh_add, inner_add_right, real_inner_smul_right, inner_self_eq_one_of_norm_eq_one he, mul_one]
    ring
  · simp only [LinearMap.coe_comp, Function.comp_apply, wedgeBoost_apply, Real.cosh_add,
      Real.sinh_add, inner_add_right, real_inner_smul_right, inner_self_eq_one_of_norm_eq_one he, mul_one]
    module

/-- **The wedge reflection is an involution**, `j_W² = 1`, for a unit vector. -/
lemma wedgeReflection_comp_self : wedgeReflection e ∘ₗ wedgeReflection e = LinearMap.id := by
  refine LinearMap.ext fun x => Prod.ext ?_ ?_
  · simp
  · simp only [LinearMap.coe_comp, Function.comp_apply, wedgeReflection_apply, inner_sub_right,
      real_inner_smul_right, inner_self_eq_one_of_norm_eq_one he, mul_one, LinearMap.id_apply]
    module

/-- **The wedge boosts preserve the Minkowski form**: `η(Λ_W(θ) x, Λ_W(θ) y) = η(x, y)`. -/
lemma wedgeBoost_form (θ : ℝ) (x y : ℝ × E) :
    form E (wedgeBoost e θ x) (wedgeBoost e θ y) = form E x y := by
  simp only [form_apply, wedgeBoost_apply, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, inner_self_eq_one_of_norm_eq_one he, real_inner_comm e]
  linear_combination (x.1 * y.1 - ⟪e, x.2⟫_ℝ * ⟪e, y.2⟫_ℝ) * Real.cosh_sq_sub_sinh_sq θ

/-- **The wedge reflection preserves the Minkowski form**: `η(j_W x, j_W y) = η(x, y)`. -/
lemma wedgeReflection_form (x y : ℝ × E) :
    form E (wedgeReflection e x) (wedgeReflection e y) = form E x y := by
  simp only [form_apply, wedgeReflection_apply, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, inner_self_eq_one_of_norm_eq_one he, real_inner_comm e]
  ring

/-- **The wedge boosts preserve the wedge**: `Λ_W(θ) W̄ ⊆ W̄`, since `Λ_W(θ)` multiplies the
light-cone coordinates `x¹ ± x⁰` by `e^{±θ}`. -/
lemma wedgeBoost_mem_wedge (θ : ℝ) {x : ℝ × E} (hx : x ∈ wedge e) : wedgeBoost e θ x ∈ wedge e := by
  rw [mem_wedge_iff, abs_le] at hx ⊢
  simp only [wedgeBoost_apply, inner_add_right, real_inner_smul_right, inner_self_eq_one_of_norm_eq_one he,
    mul_one]
  have h₁ := mul_nonneg (Real.exp_pos θ).le (by linarith [hx.1] : 0 ≤ x.1 + ⟪e, x.2⟫_ℝ)
  have h₂ := mul_nonneg (Real.exp_pos (-θ)).le (by linarith [hx.2] : 0 ≤ ⟪e, x.2⟫_ℝ - x.1)
  rw [← Real.cosh_add_sinh] at h₁
  rw [← Real.cosh_sub_sinh] at h₂
  constructor <;> nlinarith

/-- **The wedge boosts preserve the forward light cone**: `Λ_W(θ) V̄₊ ⊆ V̄₊`, since they preserve
the Minkowski form and the sign of `x⁰` on `V̄₊`. -/
lemma wedgeBoost_mem_forwardCone (θ : ℝ) {x : ℝ × E} (hx : x ∈ forwardCone E) :
    wedgeBoost e θ x ∈ forwardCone E := by
  rw [mem_forwardCone_iff_form] at hx ⊢
  refine ⟨?_, by rw [wedgeBoost_form he]; exact hx.2⟩
  have hp : |⟪e, x.2⟫_ℝ| ≤ x.1 := by
    have := abs_real_inner_le_norm e x.2
    rw [he, one_mul] at this
    exact this.trans (mem_forwardCone_iff_form.mpr hx)
  rw [abs_le] at hp
  have h₁ := mul_nonneg (Real.exp_pos θ).le (by linarith [hp.1] : 0 ≤ x.1 + ⟪e, x.2⟫_ℝ)
  have h₂ := mul_nonneg (Real.exp_pos (-θ)).le (by linarith [hp.2] : 0 ≤ x.1 - ⟪e, x.2⟫_ℝ)
  rw [← Real.cosh_add_sinh] at h₁
  rw [← Real.cosh_sub_sinh] at h₂
  simp only [wedgeBoost_apply]
  nlinarith

/-- **The wedge reflection maps the wedge onto its opposite**: `j_W W̄ ⊆ -W̄`. -/
lemma neg_wedgeReflection_mem_wedge {x : ℝ × E} (hx : x ∈ wedge e) :
    -wedgeReflection e x ∈ wedge e := by
  rw [mem_wedge_iff] at hx ⊢
  simp only [wedgeReflection_apply, Prod.fst_neg, Prod.snd_neg, neg_neg, inner_neg_right,
    inner_sub_right, real_inner_smul_right, inner_self_eq_one_of_norm_eq_one he, mul_one]
  convert hx using 1
  ring

/-- **The wedge reflection maps the forward light cone onto the backward one**:
`j_W V̄₊ ⊆ -V̄₊`. -/
lemma neg_wedgeReflection_mem_forwardCone {x : ℝ × E} (hx : x ∈ forwardCone E) :
    -wedgeReflection e x ∈ forwardCone E := by
  rw [mem_forwardCone_iff_form] at hx ⊢
  refine ⟨by simpa using hx.1, ?_⟩
  rw [LinearMap.BilinForm.neg_left, LinearMap.BilinForm.neg_right, neg_neg, wedgeReflection_form he]
  exact hx.2

/-- `ℓ₊ ∈ W̄`. -/
lemma lightPlus_mem_wedge : lightPlus e ∈ wedge e := by
  change |(1 : ℝ)| ≤ ⟪e, e⟫_ℝ
  rw [inner_self_eq_one_of_norm_eq_one he, abs_one]

/-- `ℓ₊ ∈ V̄₊`. -/
lemma lightPlus_mem_forwardCone : lightPlus e ∈ forwardCone E := by
  change ‖e‖ ≤ 1
  rw [he]

/-- `ℓ₋ ∈ W̄`. -/
lemma lightMinus_mem_wedge : lightMinus e ∈ wedge e := by
  change |(-1 : ℝ)| ≤ ⟪e, e⟫_ℝ
  rw [inner_self_eq_one_of_norm_eq_one he, abs_neg, abs_one]

/-- `ℓ₋ ∈ -V̄₊`. -/
lemma neg_lightMinus_mem_forwardCone : -lightMinus e ∈ forwardCone E := by
  change ‖-e‖ ≤ -(-1)
  rw [norm_neg, he, neg_neg]

/-- The edge component lies in `W̄`. -/
lemma edge_mem_wedge (x : ℝ × E) : edge e x ∈ wedge e := by
  change |(0 : ℝ)| ≤ ⟪e, x.2 - ⟪e, x.2⟫_ℝ • e⟫_ℝ
  rw [inner_sub_right, real_inner_smul_right, inner_self_eq_one_of_norm_eq_one he]
  simp

/-- The edge component lies in `-W̄`, so in the edge `W̄ ∩ -W̄`. -/
lemma neg_edge_mem_wedge (x : ℝ × E) : -edge e x ∈ wedge e := by
  change |-(0 : ℝ)| ≤ ⟪e, -(x.2 - ⟪e, x.2⟫_ℝ • e)⟫_ℝ
  rw [inner_neg_right, inner_sub_right, real_inner_smul_right, inner_self_eq_one_of_norm_eq_one he]
  simp

end Minkowski
