/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.Multiplier
public import Mathlib.Analysis.Normed.Operator.Extend
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.ClosureRange

/-!
# Multipliers from actions on a dense `⋆`-subalgebra

Let `Ψ : X → D` be a `⋆`-homomorphism of a `⋆`-algebra into a C⋆-algebra, and `D₀ = Ψ.closureRange`
the closure of its range. A C⋆-algebra `A` that acts on `X` from the left and from the right
(`MultiplierAction`), compatibly with the multiplication and the involution, acts boundedly for the
seminorm of `Ψ`, `‖Ψ (a · x)‖ ≤ ‖a‖ ‖Ψ x‖` (`MultiplierAction.norm_map_lmul_le`), and so acts on
`D₀` by multipliers: the actions extend by continuity to the left and right centralizers of a
double centralizer, and `a ↦` this double centralizer is a `⋆`-homomorphism `A → 𝓜(D₀)`
(`MultiplierAction.toMultiplier`). This is how a `⋆`-homomorphism of a tensor product is split into
commuting `⋆`-homomorphisms of the factors.

## Main definitions

* `NonUnitalStarAlgHom.extendClosureRange Ψ g` — the extension to `D₀` of a linear map `g` of `X`
  bounded for the seminorm of `Ψ`.
* `MultiplierAction X A` — a left and right action of `A` on `X`.
* `MultiplierAction.toMultiplier ρ Ψ` — for `Ψ : X →⋆ₙₐ[ℂ] D`, the `⋆`-homomorphism `A → 𝓜(D₀)`.

## Main results

* `NonUnitalStarAlgHom.ext_closureRange` — a multiplier of `D₀` is determined by its values on the
  image of `X`.
* `MultiplierAction.norm_map_lmul_le` — a multiplier action is bounded for the seminorm of `Ψ`.
* `MultiplierAction.commute_toMultiplier` — commuting actions give commuting
  multipliers.
-/

@[expose] public section

open Topology
open scoped MultiplierAlgebra

namespace NonUnitalStarAlgHom

variable {X D : Type*} [NonUnitalRing X] [StarRing X] [Module ℂ X] [NonUnitalCStarAlgebra D]
  (Ψ : X →⋆ₙₐ[ℂ] D)

/-! ### Extending bounded linear maps to the closure of the range -/

/-- The extension to the closure of the range of `Ψ` of a linear map `g` of `X`, by continuity; it
is `Ψ x ↦ Ψ (g x)` when `g` is bounded for the seminorm of `Ψ`
(`NonUnitalStarAlgHom.extendClosureRange_apply`). -/
noncomputable def extendClosureRange (g : X →ₗ[ℂ] X) : Ψ.closureRange →L[ℂ] Ψ.closureRange :=
  ((Ψ.closureRangeRestrict : X →ₗ[ℂ] Ψ.closureRange) ∘ₗ g).extendOfNorm
    (Ψ.closureRangeRestrict : X →ₗ[ℂ] Ψ.closureRange)

/-- On the image of `X`, the extension of a bounded `g` is `Ψ x ↦ Ψ (g x)`. -/
lemma extendClosureRange_apply {g : X →ₗ[ℂ] X} {c : ℝ} (hg : ∀ x, ‖Ψ (g x)‖ ≤ c * ‖Ψ x‖)
    (x : X) : Ψ.extendClosureRange g (Ψ.closureRangeRestrict x) = Ψ.closureRangeRestrict (g x) :=
  LinearMap.extendOfNorm_eq (denseRange_closureRangeRestrict Ψ) ⟨c, hg⟩ x

/-- Two continuous linear maps of the closure of the range agreeing on the image of `X` agree. -/
lemma continuousLinearMap_ext_closureRange {T T' : Ψ.closureRange →L[ℂ] Ψ.closureRange}
    (h : ∀ x, T (Ψ.closureRangeRestrict x) = T' (Ψ.closureRangeRestrict x)) : T = T' :=
  ContinuousLinearMap.ext fun y => congrFun ((denseRange_closureRangeRestrict Ψ).equalizer
    T.continuous T'.continuous (funext h)) y

/-- **A multiplier of the closure of the range is determined by its values on the image of
`X`.** -/
lemma ext_closureRange {M N : 𝓜(ℂ, Ψ.closureRange)}
    (h₁ : ∀ x, M.fst (Ψ.closureRangeRestrict x) = N.fst (Ψ.closureRangeRestrict x))
    (h₂ : ∀ x, M.snd (Ψ.closureRangeRestrict x) = N.snd (Ψ.closureRangeRestrict x)) : M = N :=
  DoubleCentralizer.ext _ _ M N (Prod.ext (Ψ.continuousLinearMap_ext_closureRange h₁)
    (Ψ.continuousLinearMap_ext_closureRange h₂))

end NonUnitalStarAlgHom

/-! ### Multipliers from actions -/

section Action

open NonUnitalStarAlgHom

variable {X D : Type*} [NonUnitalRing X] [StarRing X] [Module ℂ X] [NonUnitalCStarAlgebra D]

variable (A X) in
/-- A **left and right action** of `A` on `X` by multipliers: `x (a · y) = (x · a) y`,
`(a b) · x = a · (b · x)` and `(x⋆ · a)⋆ = a⋆ · x`. -/
structure MultiplierAction (A : Type*) [NonUnitalNonAssocSemiring A] [Star A] [Module ℂ A] where
  /-- The left action. -/
  lmul : A →ₗ[ℂ] X →ₗ[ℂ] X
  /-- The right action. -/
  rmul : A →ₗ[ℂ] X →ₗ[ℂ] X
  /-- `x (a · y) = (x · a) y`. -/
  mul_lmul : ∀ a x y, x * lmul a y = rmul a x * y
  /-- The left action is multiplicative: `(a b) · x = a · (b · x)`. -/
  lmul_mul : ∀ a b x, lmul (a * b) x = lmul a (lmul b x)
  /-- `(x⋆ · a)⋆ = a⋆ · x`. -/
  star_rmul : ∀ a x, star (rmul a (star x)) = lmul (star a) x

namespace MultiplierAction

variable {A : Type*} [NonUnitalCStarAlgebra A] (ρ : MultiplierAction X A) (Ψ : X →⋆ₙₐ[ℂ] D)

/-- The right action is determined by the left one: `x · a = (a⋆ · x⋆)⋆`. -/
lemma rmul_eq_star (a : A) (x : X) : ρ.rmul a x = star (ρ.lmul (star a) (star x)) := by
  rw [← ρ.star_rmul, star_star, star_star]

/-- The right action is antimultiplicative: `x · (a b) = (x · a) · b`. -/
lemma rmul_mul (a b : A) (x : X) : ρ.rmul (a * b) x = ρ.rmul b (ρ.rmul a x) := by
  rw [ρ.rmul_eq_star, star_mul, ρ.lmul_mul, ρ.rmul_eq_star b, ρ.rmul_eq_star a, star_star]

/-- The left action is the adjoint of the right one: `(a · x)⋆ = x⋆ · a⋆`. -/
lemma star_lmul (a : A) (x : X) : star (ρ.lmul a x) = ρ.rmul (star a) (star x) := by
  rw [ρ.rmul_eq_star, star_star, star_star]

/-! ### Automatic boundedness -/

/-- Through `Ψ`, the left action of `a` is adjoint to that of `a⋆`:
`Ψ (a · x)⋆ Ψ y = Ψ x⋆ Ψ (a⋆ · y)`. -/
private lemma star_map_lmul_mul (a : A) (x y : X) :
    star (Ψ (ρ.lmul a x)) * Ψ y = star (Ψ x) * Ψ (ρ.lmul (star a) y) := by
  rw [← map_star Ψ, ← map_star Ψ, ← map_mul Ψ, ← map_mul Ψ, ρ.star_lmul, ← ρ.mul_lmul]

/-- The action of the unitization of `A`, read through `Ψ`: `(λ, a) ↦ λ Ψ x + Ψ (a · x)`. -/
private noncomputable def unitAct (c : Unitization ℂ A) (x : X) : D :=
  c.fst • Ψ x + Ψ (ρ.lmul c.snd x)

/-- The action of the unitization is a `⋆`-action through `Ψ`:
`Ψ (c · x)⋆ Ψ (c · y) = Ψ x⋆ Ψ (c⋆ c · y)`. -/
private lemma star_unitAct_mul (c : Unitization ℂ A) (x y : X) :
    star (ρ.unitAct Ψ c x) * ρ.unitAct Ψ c y = star (Ψ x) * ρ.unitAct Ψ (star c * c) y := by
  simp only [unitAct, Unitization.fst_mul, Unitization.snd_mul, Unitization.fst_star,
    Unitization.snd_star, star_add, star_smul, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, star_map_lmul_mul, ρ.lmul_mul,
    smul_smul, smul_add]
  rw [mul_comm (star c.fst) c.fst]
  abel

/-- **A multiplier action is bounded for the seminorm of `Ψ`**: `‖Ψ (a · x)‖ ≤ ‖a‖ ‖Ψ x‖`. In the
unitization of `A`, `‖a‖² - a⋆ a = c⋆ c` for a self-adjoint `c`, so
`‖a‖² Ψ x⋆ Ψ x - Ψ (a · x)⋆ Ψ (a · x) = Ψ (c · x)⋆ Ψ (c · x)` is positive. -/
theorem norm_map_lmul_le (a : A) (x : X) : ‖Ψ (ρ.lmul a x)‖ ≤ ‖a‖ * ‖Ψ x‖ := by
  have h : star (a : Unitization ℂ A) * a ≤ algebraMap ℝ _ (‖(a : Unitization ℂ A)‖ ^ 2) :=
    CStarAlgebra.star_mul_le_algebraMap_norm_sq _
  rw [Unitization.norm_inr] at h
  set c : Unitization ℂ A := CFC.sqrt (algebraMap ℝ _ (‖a‖ ^ 2) - star (a : Unitization ℂ A) * a)
  have hc : star c = c := (CFC.sqrt_nonneg _).isSelfAdjoint
  have hcc : c * c = algebraMap ℝ _ (‖a‖ ^ 2) - star (a : Unitization ℂ A) * a :=
    CFC.sqrt_mul_sqrt_self _ (sub_nonneg.2 h)
  have hfst : (c * c).fst = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [hcc, ← Unitization.inr_star, ← Unitization.inr_mul, sub_eq_add_neg,
      Unitization.fst_add, Unitization.fst_neg, Unitization.fst_inr, neg_zero, add_zero]
    rfl
  have hsnd : (c * c).snd = -(star a * a) := by
    rw [hcc, ← Unitization.inr_star, ← Unitization.inr_mul, sub_eq_add_neg,
      Unitization.snd_add, Unitization.snd_neg, Unitization.snd_inr]
    exact zero_add _
  have key : star (ρ.unitAct Ψ c x) * ρ.unitAct Ψ c x =
      ((‖a‖ ^ 2 : ℝ) : ℂ) • (star (Ψ x) * Ψ x) - star (Ψ (ρ.lmul a x)) * Ψ (ρ.lmul a x) := by
    rw [star_unitAct_mul, hc, star_map_lmul_mul, ← ρ.lmul_mul, unitAct, hfst, hsnd, map_neg,
      LinearMap.neg_apply, map_neg, mul_add, mul_neg, mul_smul_comm, sub_eq_add_neg]
  let := CStarAlgebra.spectralOrder D
  have := CStarAlgebra.spectralOrderedRing D
  have hle : star (Ψ (ρ.lmul a x)) * Ψ (ρ.lmul a x) ≤ ((‖a‖ ^ 2 : ℝ) : ℂ) • (star (Ψ x) * Ψ x) :=
    sub_nonneg.1 (key ▸ star_mul_self_nonneg _)
  have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg hle (star_mul_self_nonneg _)
  rw [CStarRing.norm_star_mul_self, norm_smul, CStarRing.norm_star_mul_self, Complex.norm_real,
    Real.norm_of_nonneg (sq_nonneg _)] at hn
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
  rw [mul_pow, sq, sq ‖Ψ x‖]
  exact hn

/-- The right action is bounded for the seminorm of `Ψ`: `‖Ψ (x · a)‖ ≤ ‖a‖ ‖Ψ x‖`. -/
lemma norm_map_rmul_le (a : A) (x : X) : ‖Ψ (ρ.rmul a x)‖ ≤ ‖a‖ * ‖Ψ x‖ := by
  rw [rmul_eq_star, map_star, norm_star]
  refine (ρ.norm_map_lmul_le Ψ _ _).trans ?_
  rw [norm_star, map_star, norm_star]

/-! ### The multipliers of an action -/

/-- The double centralizer of the closure of the range of `Ψ` by which `a` acts. -/
noncomputable def multiplier (a : A) : 𝓜(ℂ, Ψ.closureRange) where
  toProd := (Ψ.extendClosureRange (ρ.lmul a), Ψ.extendClosureRange (ρ.rmul a))
  central x y := by
    have hd := (denseRange_closureRangeRestrict Ψ).prodMap (denseRange_closureRangeRestrict Ψ)
    have h := hd.equalizer (g := fun p : Ψ.closureRange × Ψ.closureRange =>
        Ψ.extendClosureRange (ρ.rmul a) p.1 * p.2)
      (h := fun p => p.1 * Ψ.extendClosureRange (ρ.lmul a) p.2) (by fun_prop) (by fun_prop)
      (funext fun p => by
        change Ψ.extendClosureRange (ρ.rmul a) (Ψ.closureRangeRestrict p.1) *
            Ψ.closureRangeRestrict p.2 =
          Ψ.closureRangeRestrict p.1 * Ψ.extendClosureRange (ρ.lmul a) (Ψ.closureRangeRestrict p.2)
        rw [extendClosureRange_apply Ψ (ρ.norm_map_rmul_le Ψ a), extendClosureRange_apply Ψ (ρ.norm_map_lmul_le Ψ a),
          ← map_mul, ← map_mul, ρ.mul_lmul])
    exact congrFun h (x, y)

/-- The left component of `ρ.multiplier Ψ a` is the left action of `a` on the range of `Ψ`. -/
lemma multiplier_fst (a : A) (x : X) :
    (ρ.multiplier Ψ a).fst (Ψ.closureRangeRestrict x) = Ψ.closureRangeRestrict (ρ.lmul a x) :=
  extendClosureRange_apply Ψ (ρ.norm_map_lmul_le Ψ a) x

/-- The right component of `ρ.multiplier Ψ a` is the right action of `a` on the range of `Ψ`. -/
lemma multiplier_snd (a : A) (x : X) :
    (ρ.multiplier Ψ a).snd (Ψ.closureRangeRestrict x) = Ψ.closureRangeRestrict (ρ.rmul a x) :=
  extendClosureRange_apply Ψ (ρ.norm_map_rmul_le Ψ a) x

/-- **A multiplier action is a `⋆`-homomorphism into the multiplier algebra of the closure of the
range of `Ψ`.** -/
noncomputable def toMultiplier : A →⋆ₙₐ[ℂ] 𝓜(ℂ, Ψ.closureRange) where
  toFun := ρ.multiplier Ψ
  map_smul' c a := Ψ.ext_closureRange
    (fun x => by
      rw [MonoidHom.id_apply, DoubleCentralizer.smul_fst, smul_apply,
        multiplier_fst, multiplier_fst, map_smul, LinearMap.smul_apply, map_smul])
    (fun x => by
      rw [MonoidHom.id_apply, DoubleCentralizer.smul_snd, smul_apply,
        multiplier_snd, multiplier_snd, map_smul, LinearMap.smul_apply, map_smul])
  map_zero' := Ψ.ext_closureRange
    (fun x => by rw [multiplier_fst, map_zero, LinearMap.zero_apply, map_zero]; rfl)
    (fun x => by rw [multiplier_snd, map_zero, LinearMap.zero_apply, map_zero]; rfl)
  map_add' a b := Ψ.ext_closureRange
    (fun x => by
      rw [DoubleCentralizer.add_fst, add_apply, multiplier_fst,
        multiplier_fst, multiplier_fst, map_add, LinearMap.add_apply, map_add])
    (fun x => by
      rw [DoubleCentralizer.add_snd, add_apply, multiplier_snd,
        multiplier_snd, multiplier_snd, map_add, LinearMap.add_apply, map_add])
  map_mul' a b := Ψ.ext_closureRange
    (fun x => by
      rw [DoubleCentralizer.mul_fst, mul_apply_eq_comp,
        multiplier_fst, multiplier_fst, multiplier_fst, ρ.lmul_mul])
    (fun x => by
      rw [DoubleCentralizer.mul_snd, mul_apply_eq_comp,
        multiplier_snd, multiplier_snd, multiplier_snd, ρ.rmul_mul])
  map_star' a := Ψ.ext_closureRange
    (fun x => by
      rw [DoubleCentralizer.star_fst, ← map_star Ψ.closureRangeRestrict, multiplier_snd,
        ← map_star Ψ.closureRangeRestrict, ρ.star_rmul, multiplier_fst])
    (fun x => by
      rw [DoubleCentralizer.star_snd, ← map_star Ψ.closureRangeRestrict, multiplier_fst,
        ← map_star Ψ.closureRangeRestrict, multiplier_snd, ρ.rmul_eq_star, star_star])

/-- The left component of `ρ.toMultiplier Ψ a` is the left action of `a` on the range of `Ψ`. -/
@[simp] lemma toMultiplier_fst (a : A) (x : X) :
    (ρ.toMultiplier Ψ a).fst (Ψ.closureRangeRestrict x) = Ψ.closureRangeRestrict (ρ.lmul a x) :=
  ρ.multiplier_fst Ψ a x

/-- The right component of `ρ.toMultiplier Ψ a` is the right action of `a` on the range of `Ψ`. -/
@[simp] lemma toMultiplier_snd (a : A) (x : X) :
    (ρ.toMultiplier Ψ a).snd (Ψ.closureRangeRestrict x) = Ψ.closureRangeRestrict (ρ.rmul a x) :=
  ρ.multiplier_snd Ψ a x

/-- **Commuting actions give commuting multipliers.** -/
lemma commute_toMultiplier {B : Type*} [NonUnitalCStarAlgebra B] (σ : MultiplierAction X B)
    (hl : ∀ a b x, ρ.lmul a (σ.lmul b x) = σ.lmul b (ρ.lmul a x)) (a : A) (b : B) :
    Commute (ρ.toMultiplier Ψ a) (σ.toMultiplier Ψ b) :=
  have hr (a : A) (b : B) (x : X) : ρ.rmul a (σ.rmul b x) = σ.rmul b (ρ.rmul a x) := by
    rw [ρ.rmul_eq_star, σ.rmul_eq_star, star_star, hl, σ.rmul_eq_star (x := ρ.rmul a x),
      ρ.rmul_eq_star, star_star]
  Ψ.ext_closureRange
    (fun x => by
      rw [DoubleCentralizer.mul_fst, DoubleCentralizer.mul_fst, mul_apply_eq_comp,
        mul_apply_eq_comp, toMultiplier_fst,
        toMultiplier_fst, toMultiplier_fst, toMultiplier_fst, hl])
    (fun x => by
      rw [DoubleCentralizer.mul_snd, DoubleCentralizer.mul_snd, mul_apply_eq_comp,
        mul_apply_eq_comp, toMultiplier_snd,
        toMultiplier_snd, toMultiplier_snd, toMultiplier_snd, hr])

end MultiplierAction

end Action

/-! ### Actions on tensor products -/

namespace MultiplierAction

open scoped TensorProduct

variable {A : Type*} [NonUnitalCStarAlgebra A]

variable (A) in
/-- The action of a C⋆-algebra on itself by left and right multiplication. -/
noncomputable def self : MultiplierAction A A where
  lmul := LinearMap.mul ℂ A
  rmul := (LinearMap.mul ℂ A).flip
  mul_lmul a x y := (mul_assoc x a y).symm
  lmul_mul a b x := mul_assoc a b x
  star_rmul a x := by
    change star (star x * a) = star a * x
    rw [star_mul, star_star]

variable {X : Type*} [NonUnitalRing X] [StarRing X] [Module ℂ X] [StarModule ℂ X]
  [IsScalarTower ℂ X X] [SMulCommClass ℂ X X]
  {Y : Type*} [NonUnitalRing Y] [StarRing Y] [Module ℂ Y] [StarModule ℂ Y]
  [IsScalarTower ℂ Y Y] [SMulCommClass ℂ Y Y]

/-- An action on `X` acts on `X ⊗[ℂ] Y` through the first factor. -/
noncomputable def rTensor (ρ : MultiplierAction X A) (Y : Type*) [NonUnitalRing Y] [StarRing Y]
    [Module ℂ Y] [StarModule ℂ Y] [IsScalarTower ℂ Y Y] [SMulCommClass ℂ Y Y] :
    MultiplierAction (X ⊗[ℂ] Y) A where
  lmul := (LinearMap.rTensorHom Y).comp ρ.lmul
  rmul := (LinearMap.rTensorHom Y).comp ρ.rmul
  mul_lmul a x y := by
    induction x using TensorProduct.inductionOn with
    | tmul x₁ x₂ =>
      induction y using TensorProduct.inductionOn with
      | tmul y₁ y₂ =>
        simp only [LinearMap.comp_apply, LinearMap.coe_rTensorHom, LinearMap.rTensor_tmul,
          Algebra.TensorProduct.tmul_mul_tmul, ρ.mul_lmul]
      | add y y' hy hy' => rw [map_add, mul_add, mul_add, hy, hy']
    | add x x' hx hx' => rw [add_mul, map_add, add_mul, hx, hx']
  lmul_mul a b x := by
    simp only [LinearMap.comp_apply, LinearMap.coe_rTensorHom]
    rw [← LinearMap.rTensor_comp_apply]
    congr 2
    exact LinearMap.ext (ρ.lmul_mul a b)
  star_rmul a x := by
    induction x using TensorProduct.inductionOn with
    | tmul x₁ x₂ =>
      simp only [LinearMap.comp_apply, LinearMap.coe_rTensorHom, TensorProduct.star_tmul,
        LinearMap.rTensor_tmul, star_star, ρ.star_rmul]
    | add x x' hx hx' => rw [star_add, map_add, star_add, hx, hx', map_add]

/-- An action on `Y` acts on `X ⊗[ℂ] Y` through the second factor. -/
noncomputable def lTensor (ρ : MultiplierAction Y A) (X : Type*) [NonUnitalRing X] [StarRing X]
    [Module ℂ X] [StarModule ℂ X] [IsScalarTower ℂ X X] [SMulCommClass ℂ X X] :
    MultiplierAction (X ⊗[ℂ] Y) A where
  lmul := (LinearMap.lTensorHom X).comp ρ.lmul
  rmul := (LinearMap.lTensorHom X).comp ρ.rmul
  mul_lmul a x y := by
    induction x using TensorProduct.inductionOn with
    | tmul x₁ x₂ =>
      induction y using TensorProduct.inductionOn with
      | tmul y₁ y₂ =>
        simp only [LinearMap.comp_apply, LinearMap.coe_lTensorHom, LinearMap.lTensor_tmul,
          Algebra.TensorProduct.tmul_mul_tmul, ρ.mul_lmul]
      | add y y' hy hy' => rw [map_add, mul_add, mul_add, hy, hy']
    | add x x' hx hx' => rw [add_mul, map_add, add_mul, hx, hx']
  lmul_mul a b x := by
    simp only [LinearMap.comp_apply, LinearMap.coe_lTensorHom]
    rw [← LinearMap.lTensor_comp_apply]
    congr 2
    exact LinearMap.ext (ρ.lmul_mul a b)
  star_rmul a x := by
    induction x using TensorProduct.inductionOn with
    | tmul x₁ x₂ =>
      simp only [LinearMap.comp_apply, LinearMap.coe_lTensorHom, TensorProduct.star_tmul,
        LinearMap.lTensor_tmul, star_star, ρ.star_rmul]
    | add x x' hx hx' => rw [star_add, map_add, star_add, hx, hx', map_add]

/-- `ρ.rTensor Y` acts on the left on the first factor. -/
@[simp] lemma rTensor_lmul (ρ : MultiplierAction X A) (a : A) (x : X) (y : Y) :
    (ρ.rTensor Y).lmul a (x ⊗ₜ[ℂ] y) = ρ.lmul a x ⊗ₜ[ℂ] y :=
  rfl

/-- `ρ.rTensor Y` acts on the right on the first factor. -/
@[simp] lemma rTensor_rmul (ρ : MultiplierAction X A) (a : A) (x : X) (y : Y) :
    (ρ.rTensor Y).rmul a (x ⊗ₜ[ℂ] y) = ρ.rmul a x ⊗ₜ[ℂ] y :=
  rfl

/-- `ρ.lTensor X` acts on the left on the second factor. -/
@[simp] lemma lTensor_lmul (ρ : MultiplierAction Y A) (a : A) (x : X) (y : Y) :
    (ρ.lTensor X).lmul a (x ⊗ₜ[ℂ] y) = x ⊗ₜ[ℂ] ρ.lmul a y :=
  rfl

/-- `ρ.lTensor X` acts on the right on the second factor. -/
@[simp] lemma lTensor_rmul (ρ : MultiplierAction Y A) (a : A) (x : X) (y : Y) :
    (ρ.lTensor X).rmul a (x ⊗ₜ[ℂ] y) = x ⊗ₜ[ℂ] ρ.rmul a y :=
  rfl

/-- The left action of `A` on itself is left multiplication. -/
@[simp] lemma self_lmul (a x : A) : (self A).lmul a x = a * x :=
  rfl

/-- The right action of `A` on itself is right multiplication. -/
@[simp] lemma self_rmul (a x : A) : (self A).rmul a x = x * a :=
  rfl

end MultiplierAction
