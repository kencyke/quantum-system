/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.Normed.Module.TransferInstance
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.SchwarzMap

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.ContractiveProjection

/-!
# The Choi–Effros product

Let `φ : A → A` be an idempotent Schwarz map on a C⋆-algebra, `φ ∘ φ = φ`. Its range need not be
a subalgebra of `A`, but it carries a product of its own, the **Choi–Effros product**
`x ∘ y = φ(x y)`, written `x * y` here, which makes it a C⋆-algebra with the involution and the
norm of `A` (`ChoiEffros`). The unital completely positive projections are examples, being Schwarz
maps (`KPositiveMapClass.toSchwarzMap` in `QuantumSystem.Analysis.CStarAlgebra.KPositiveMapSchwarz`:
a completely positive `φ` with `φ 1 ≤ 1` enters as `ChoiEffros (KPositiveMapClass.toSchwarzMap φ h)`).

Associativity rests on the identities `φ(a φ(b)) = φ(a b)` and `φ(φ(b) a) = φ(b a)` for `a` in the
range (`SchwarzMapClass.map_mul_map_of_map_eq_self`, `SchwarzMapClass.map_map_mul_of_map_eq_self`).
They are an equality case of the Kadison–Schwarz inequality: for `a` in the range, `φ` sends
`φ(a⋆ a) - φ(a)⋆ φ(a)` to `0`, and a positive map that kills this defect at `a` kills
`φ(a⋆ b) - φ(a)⋆ φ(b)` for every `b` (`SchwarzMapClass.map_map_star_mul_of_map_map_star_mul_self`),
so `φ(a⋆ b) = φ(a⋆ φ(b))`. The
C⋆-identity `‖φ(x⋆ x)‖ = ‖x‖²` follows from the contractivity of `φ`
(`SchwarzMapClass.norm_apply_le`) and from `x⋆ x = φ(x)⋆ φ(x) ≤ φ(x⋆ x)`. On a unital `A` the range
is unital, with unit `φ 1`, whether or not `φ 1 = 1`. The order of the range as a C⋆-algebra is the
order of `A` (`ChoiEffros.val_nonneg_iff`): a positive `x⋆ * x = φ(x⋆ x)` is positive in `A`, and
conversely `0 ≤ x` in `A` with `‖x‖ ≤ t` gives `‖t s - x * s‖ = ‖φ((t - x) s)‖ ≤ ‖t - x‖ ‖s‖ ≤ t ‖s‖`
for `s` in the range, so that `‖t - x‖ ≤ t` in the unitization of the range. The C⋆-algebra depends
only on the range: idempotent Schwarz maps with the same range have the same Choi–Effros product
(`ChoiEffros.starAlgEquivOfRangeEq`).

When `φ` is a projection onto a subalgebra `S` (`LinearMap.IsProj S.toSubmodule φ`), the range is
`S`, closed under products and fixed by `φ`, so the Choi–Effros product is the product of `A`
(`ChoiEffros.val_mul_of_isProj`).

The idempotence of `φ` is a `Fact` instance argument of the C⋆-algebra structure rather than an
argument of the type, so that the type does not depend on a proof.

`ChoiEffros φ` is a structure wrapping the range rather than a type synonym for it, so that the
range is not unfolded to the subtype of `A`, whose order (`Subtype.partialOrder`) agrees with the
spectral order of the C⋆-algebra (`ChoiEffros.val_le_val`) but not definitionally; the normed space
structure is transferred along `ChoiEffros.equivRange`.

## Main definitions

* `ChoiEffros φ` — the range of `φ`; for an idempotent Schwarz map `φ`, with the Choi–Effros
  product, a `NonUnitalCStarAlgebra`, and a `CStarAlgebra` when `A` is unital.
* `ChoiEffros.linearIsometryEquivRange` — `ChoiEffros φ` is isometrically isomorphic to the range
  of `φ` as a normed space.
* `ChoiEffros.starAlgEquivOfRangeEq` — idempotent Schwarz maps with the same range give
  ⋆-isomorphic C⋆-algebras.
* `ChoiEffros.starAlgEquivId` — `ChoiEffros (SchwarzMap.id A)` is `A`.

## Main results

* **`ChoiEffros.val_nonneg_iff`**, `ChoiEffros.val_le_val` — the order of the range as a C⋆-algebra is
  the order of `A`.
* `ChoiEffros.val_mul_of_isProj` — when `φ` is a projection onto a subalgebra, the Choi–Effros
  product is the product of `A`.

The identities on idempotent Schwarz maps that the construction rests on live in
`QuantumSystem.ForMathlib.Analysis.CStarAlgebra.SchwarzMap`.
-/

@[expose] public noncomputable section

open scoped CStarAlgebra NNReal

open SchwarzMapClass

variable {F A : Type*} [NonUnitalCStarAlgebra A] [FunLike F A A] [LinearMapClass F ℂ A A]

/-- The range of a linear map `φ : A → A`, which carries the Choi–Effros product `x * y = φ(x y)`
when `φ` is an idempotent Schwarz map. -/
structure ChoiEffros (φ : F) where
  /-- An element of the range as an element of `ChoiEffros φ`. -/
  ofRange ::
  /-- The underlying element of the range. -/
  toRange : LinearMap.range (φ : A →ₗ[ℂ] A)

namespace ChoiEffros

variable {φ : F}

variable (φ) in
/-- The canonical equivalence between `ChoiEffros φ` and the range of `φ`. -/
def equivRange : ChoiEffros φ ≃ LinearMap.range (φ : A →ₗ[ℂ] A) where
  toFun := toRange
  invFun := ofRange

/-- The normed group structure of the range, transferred along `equivRange`. -/
instance : NormedAddCommGroup (ChoiEffros φ) :=
  fast_instance% (equivRange φ).normedAddCommGroup

/-- The normed space structure of the range, transferred along `equivRange`. -/
instance : NormedSpace ℂ (ChoiEffros φ) :=
  fast_instance% (equivRange φ).addEquiv.normedSpace ℂ

/-- The underlying element of `A`. -/
@[coe] def val (x : ChoiEffros φ) : A :=
  x.toRange

/-- The coercion `ChoiEffros φ → A`. -/
instance : CoeOut (ChoiEffros φ) A := ⟨val⟩

/-- Elements of `ChoiEffros φ` are determined by their underlying elements of `A`. -/
lemma val_injective : Function.Injective (val : ChoiEffros φ → A) :=
  Subtype.val_injective.comp (equivRange φ).injective

/-- Two elements of `ChoiEffros φ` with the same underlying element of `A` are equal. -/
@[ext] lemma ext {x y : ChoiEffros φ} (h : x.val = y.val) : x = y :=
  val_injective h

/-- The underlying element of `0` is `0`. -/
@[simp] lemma val_zero : (0 : ChoiEffros φ).val = 0 := rfl

/-- The addition of `ChoiEffros φ` is the addition of `A`. -/
@[simp] lemma val_add (x y : ChoiEffros φ) : (x + y).val = x.val + y.val := rfl

/-- The negation of `ChoiEffros φ` is the negation of `A`. -/
@[simp] lemma val_neg (x : ChoiEffros φ) : (-x).val = -x.val := rfl

/-- The subtraction of `ChoiEffros φ` is the subtraction of `A`. -/
@[simp] lemma val_sub (x y : ChoiEffros φ) : (x - y).val = x.val - y.val := rfl

/-- The complex scalar multiplication of `ChoiEffros φ` is that of `A`. -/
@[simp] lemma val_smul (c : ℂ) (x : ChoiEffros φ) : (c • x).val = c • x.val := rfl

/-- The real scalar multiplication of `ChoiEffros φ` is that of `A`. -/
@[simp] lemma val_real_smul (r : ℝ) (x : ChoiEffros φ) : (r • x).val = r • x.val := rfl

/-- The norm of `ChoiEffros φ` is the norm of `A`. -/
@[simp] lemma norm_val (x : ChoiEffros φ) : ‖x.val‖ = ‖x‖ := rfl

/-- The `ℝ≥0`-valued norm of `ChoiEffros φ` is that of `A`. -/
@[simp] lemma nnnorm_val (x : ChoiEffros φ) : ‖x.val‖₊ = ‖x‖₊ := rfl

variable (φ) in
/-- The canonical isometric isomorphism between `ChoiEffros φ` and the range of `φ`. -/
def linearIsometryEquivRange : ChoiEffros φ ≃ₗᵢ[ℂ] LinearMap.range (φ : A →ₗ[ℂ] A) where
  __ := equivRange φ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

variable (φ) in
/-- The element `φ a` of the range. -/
def ofMap (a : A) : ChoiEffros φ :=
  ofRange ⟨φ a, LinearMap.mem_range_self (φ : A →ₗ[ℂ] A) a⟩

/-- The underlying element of `ofMap φ a` is `φ a`. -/
@[simp] lemma val_ofMap (a : A) : (ofMap φ a).val = φ a := rfl

/-- The Choi–Effros product `x * y = φ(x y)`. -/
instance : Mul (ChoiEffros φ) := ⟨fun x y => ofMap φ (x.val * y.val)⟩

/-- The underlying element of the Choi–Effros product `x * y` is `φ(x y)`. -/
lemma val_mul (x y : ChoiEffros φ) : (x * y).val = φ (x.val * y.val) := rfl

/-- When `φ` is a projection onto a subalgebra `S`, the Choi–Effros product is the product of `A`:
the range is `S`, closed under products and fixed by `φ`. -/
lemma val_mul_of_isProj {S : NonUnitalSubalgebra ℂ A} (hS : LinearMap.IsProj S.toSubmodule φ)
    (x y : ChoiEffros φ) : (x * y).val = x.val * y.val := by
  have hmem (z : ChoiEffros φ) : z.val ∈ S := by
    obtain ⟨a, ha⟩ := z.toRange.2
    rw [val, ← ha]
    exact hS.map_mem a
  exact hS.map_id _ (show x.val * y.val ∈ S from mul_mem (hmem x) (hmem y))

/-- Scalars commute with the Choi–Effros product on the left. -/
instance : IsScalarTower ℂ (ChoiEffros φ) (ChoiEffros φ) where
  smul_assoc c x y := ext <| by simp [val_mul, smul_mul_assoc]

/-- Scalars commute with the Choi–Effros product on the right. -/
instance : SMulCommClass ℂ (ChoiEffros φ) (ChoiEffros φ) where
  smul_comm c x y := ext <| by simp [val_mul, mul_smul_comm]

/-- The involution `star x = φ(x⋆)`, which is `x⋆` on the range of an idempotent Schwarz map
(`ChoiEffros.val_star`). -/
instance : Star (ChoiEffros φ) := ⟨fun x => ofMap φ (star x.val)⟩

/-- The involution is conjugate-linear. -/
instance : StarModule ℂ (ChoiEffros φ) where
  star_smul c x := ext <| by
    change φ (star (c • x.val)) = star c • φ (star x.val)
    rw [star_smul, map_smul]

variable [hφ : Fact (IsIdempotentElem (φ : A →ₗ[ℂ] A))]

/-- `φ` fixes its range. -/
@[simp] lemma map_val (x : ChoiEffros φ) : φ x.val = x.val :=
  (LinearMap.IsIdempotentElem.mem_range_iff hφ.out).mp x.toRange.2

/-- `ofMap φ` is a left inverse of `val`. -/
@[simp] lemma ofMap_val (x : ChoiEffros φ) : ofMap φ x.val = x := ext <| map_val x

/-- `ChoiEffros φ` is complete when `φ` is continuous: the range of a continuous idempotent map is its
set of fixed points, hence closed. -/
instance [ContinuousMapClass F A A] : CompleteSpace (ChoiEffros φ) :=
  have := (((LinearMap.isProj_range_iff_isIdempotentElem _).mpr hφ.out).isClosed
    (map_continuous φ)).completeSpace_coe
  (linearIsometryEquivRange φ).toIsometryEquiv.completeSpace

section Schwarz

variable [PartialOrder A] [StarOrderedRing A] [SchwarzMapClass F A A]

/-- The involution of `ChoiEffros φ` is the involution of `A`: `φ` preserves `star`. -/
@[simp] lemma val_star (x : ChoiEffros φ) : (star x).val = star x.val := by
  change φ (star x.val) = star x.val
  rw [map_star, map_val]

/-- The Choi–Effros product is associative and distributive. -/
instance : NonUnitalRing (ChoiEffros φ) where
  __ := (inferInstance : AddCommGroup (ChoiEffros φ))
  left_distrib x y z := ext <| by simp [val_mul, mul_add]
  right_distrib x y z := ext <| by simp [val_mul, add_mul]
  zero_mul x := ext <| by simp [val_mul]
  mul_zero x := ext <| by simp [val_mul]
  mul_assoc x y z := ext <| by
    simp only [val_mul]
    rw [map_map_mul_of_map_eq_self hφ.out (map_val z), mul_assoc,
      map_mul_map_of_map_eq_self hφ.out (map_val x)]

/-- The Choi–Effros product is submultiplicative, `φ` being contractive. -/
instance : NonUnitalNormedRing (ChoiEffros φ) where
  __ := (inferInstance : NormedAddCommGroup (ChoiEffros φ))
  __ := (inferInstance : NonUnitalRing (ChoiEffros φ))
  norm_mul_le x y := by
    rw [← norm_val, val_mul, ← norm_val, ← norm_val]
    exact (norm_apply_le φ _).trans (norm_mul_le _ _)

/-- The involution is additive, involutive and antimultiplicative. -/
instance : StarRing (ChoiEffros φ) where
  star_involutive x := ext <| by simp
  star_mul x y := ext <| by simp [val_mul, ← map_star, star_mul]
  star_add x y := ext <| by simp

/-- The C⋆-identity: `‖x‖² = ‖x⋆ x‖ ≤ ‖φ(x⋆ x)‖`, since `x⋆ x = φ(x)⋆ φ(x) ≤ φ(x⋆ x)`. -/
instance : CStarRing (ChoiEffros φ) where
  norm_mul_self_le x := by
    rw [← norm_val, ← norm_val, val_mul, val_star, ← CStarRing.norm_star_mul_self]
    refine CStarAlgebra.norm_le_norm_of_le_of_nonneg ?_ (star_mul_self_nonneg _)
    simpa only [map_val] using le_map_star_mul φ x.val

/-- The range of an idempotent Schwarz map, with the Choi–Effros product, is a C⋆-algebra. -/
instance : NonUnitalCStarAlgebra (ChoiEffros φ) where

/-- The order of the C⋆-algebra `ChoiEffros φ`: `x ≤ y` when `y - x` is self-adjoint with
nonnegative spectrum. It is the order of `A` (`ChoiEffros.val_le_val`). -/
instance : PartialOrder (ChoiEffros φ) := CStarAlgebra.spectralOrder _

/-- The spectral order makes `ChoiEffros φ` a star-ordered ring. -/
instance : StarOrderedRing (ChoiEffros φ) := CStarAlgebra.spectralOrderedRing _

/-- The positive elements of `ChoiEffros φ` are positive in `A`: `y⋆ * y = φ(y⋆ y)`. -/
lemma val_nonneg {x : ChoiEffros φ} (hx : 0 ≤ x) : 0 ≤ x.val := by
  obtain ⟨y, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hx
  rw [val_mul, val_star]
  exact map_nonneg φ (star_mul_self_nonneg _)

/-- In a C⋆-algebra, a self-adjoint `a` with `‖a‖ ≤ t` is positive if and only if `‖t - a‖ ≤ t`
in the unitization. -/
private lemma nonneg_iff_nnnorm_algebraMap_sub_inr_le {B : Type*} [NonUnitalCStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] {a : B} (ha : IsSelfAdjoint a) {t : ℝ≥0}
    (ht : ‖a‖₊ ≤ t) : 0 ≤ a ↔ ‖algebraMap ℝ B⁺¹ t - a‖₊ ≤ t := by
  rw [← Unitization.inr_nonneg_iff, nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts,
    quasispectrumRestricts_iff_spectrumRestricts,
    ← SpectrumRestricts.nnreal_iff_nnnorm (ha.inr ℂ) (by rwa [Unitization.nnnorm_inr])]
  exact and_iff_right (ha.inr ℂ)

/-- For `0 ≤ a` with `‖a‖ ≤ t`, `‖t s - a s‖ ≤ t ‖s‖`: in the unitization, `t s - a s = (t - a) s`
and `‖t - a‖ ≤ t`. -/
private lemma nnnorm_smul_sub_mul_le {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] {a : B} (ha : 0 ≤ a) {t : ℝ≥0} (ht : ‖a‖₊ ≤ t) (s : B) :
    ‖algebraMap ℝ ℂ t • s - a * s‖₊ ≤ t * ‖s‖₊ := by
  have h := (nonneg_iff_nnnorm_algebraMap_sub_inr_le (.of_nonneg ha) ht).mp ha
  have hs : ((algebraMap ℝ ℂ t • s - a * s : B) : B⁺¹) = (algebraMap ℝ B⁺¹ t - a) * s := by
    rw [sub_mul, Unitization.inr_sub, Unitization.inr_mul, Unitization.algebraMap_eq_inl_comp,
      Function.comp_apply, Unitization.inl_mul_inr]
  rw [← Unitization.nnnorm_inr (𝕜 := ℂ), hs, ← Unitization.nnnorm_inr (𝕜 := ℂ) s]
  exact (nnnorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right h (by simp))

/-- **The order of the range is the order of `A`.** An element of the range is positive for the
Choi–Effros product if and only if it is positive in `A`: conversely to `ChoiEffros.val_nonneg`,
`0 ≤ x` in `A` with `‖x‖ ≤ t` gives `‖t s - x * s‖ = ‖φ((t - x) s)‖ ≤ ‖t - x‖ ‖s‖ ≤ t ‖s‖` for `s` in
the range, so `‖t - x‖ ≤ t` in the unitization of the range. -/
@[simp, norm_cast]
theorem val_nonneg_iff {x : ChoiEffros φ} : 0 ≤ x.val ↔ 0 ≤ x := by
  refine ⟨fun hx => ?_, val_nonneg⟩
  have hsa : IsSelfAdjoint x := ext <| by simp [(IsSelfAdjoint.of_nonneg hx).star_eq]
  rw [nonneg_iff_nnnorm_algebraMap_sub_inr_le hsa le_rfl, sub_eq_add_neg, ← Unitization.inr_neg,
    Unitization.nnnorm_eq_sup, Unitization.algebraMap_eq_inl_comp, Function.comp_apply]
  simp only [Unitization.fst_add, Unitization.snd_add, Unitization.fst_inl, Unitization.snd_inl,
    Unitization.fst_inr, Unitization.snd_inr, add_zero, zero_add, nnnorm_algebraMap',
    NNReal.nnnorm_eq]
  refine sup_le le_rfl (ContinuousLinearMap.opNNNorm_le_bound _ _ fun s => ?_)
  rw [add_apply, ContinuousLinearMap.mul_apply', neg_mul, ← sub_eq_add_neg,
    Algebra.algebraMap_eq_smul_one, smul_apply, one_apply_eq_self, ← nnnorm_val, val_sub, val_smul,
    val_mul, ← map_val s, ← map_smul, ← map_sub, map_val, ← nnnorm_val s]
  exact (nnnorm_apply_le φ _).trans (nnnorm_smul_sub_mul_le hx (nnnorm_val x).le _)

/-- The order of `ChoiEffros φ` is the order of `A`. -/
@[simp, norm_cast]
lemma val_le_val {x y : ChoiEffros φ} : x.val ≤ y.val ↔ x ≤ y := by
  rw [← sub_nonneg, ← val_sub, val_nonneg_iff, sub_nonneg]

variable (φ) in
/-- Idempotent Schwarz maps with the same range give ⋆-isomorphic C⋆-algebras: the identity of the
range is multiplicative (`SchwarzMapClass.map_mul_eq_of_range_eq`). -/
def starAlgEquivOfRangeEq {G : Type*} [FunLike G A A] [LinearMapClass G ℂ A A]
    [SchwarzMapClass G A A] (ψ : G) [hψ : Fact (IsIdempotentElem (ψ : A →ₗ[ℂ] A))]
    (h : LinearMap.range (φ : A →ₗ[ℂ] A) = LinearMap.range (ψ : A →ₗ[ℂ] A)) :
    ChoiEffros φ ≃⋆ₐ[ℂ] ChoiEffros ψ where
  toFun x := ofRange (LinearEquiv.ofEq _ _ h x.toRange)
  invFun x := ofRange ((LinearEquiv.ofEq _ _ h).symm x.toRange)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' x y := ext <| map_mul_eq_of_range_eq h hφ.out hψ.out (map_val x) (map_val y)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' x := ext <| (val_star x).trans (val_star (ofRange (LinearEquiv.ofEq _ _ h x.toRange))).symm

/-- `ChoiEffros.starAlgEquivOfRangeEq` is the identity on the underlying elements of `A`. -/
@[simp] lemma val_starAlgEquivOfRangeEq {G : Type*} [FunLike G A A] [LinearMapClass G ℂ A A]
    [SchwarzMapClass G A A] (ψ : G) [Fact (IsIdempotentElem (ψ : A →ₗ[ℂ] A))]
    (h : LinearMap.range (φ : A →ₗ[ℂ] A) = LinearMap.range (ψ : A →ₗ[ℂ] A)) (x : ChoiEffros φ) :
    (starAlgEquivOfRangeEq φ ψ h x).val = x.val :=
  rfl

end Schwarz

section Unital

variable {F A : Type*} [CStarAlgebra A] [FunLike F A A] [LinearMapClass F ℂ A A] {φ : F}

/-- The unit `φ 1`: `φ(φ(1) x) = φ(x) = x` for `x` in the range. -/
instance : One (ChoiEffros φ) := ⟨ofMap φ 1⟩

/-- The underlying element of the unit of `ChoiEffros φ` is `φ 1`. -/
@[simp] lemma val_one : (1 : ChoiEffros φ).val = φ 1 := rfl

variable [PartialOrder A] [StarOrderedRing A] [SchwarzMapClass F A A]
  [hφ : Fact (IsIdempotentElem (φ : A →ₗ[ℂ] A))]

/-- `φ 1` is a unit for the Choi–Effros product. -/
instance : Ring (ChoiEffros φ) where
  __ := (inferInstance : NonUnitalRing (ChoiEffros φ))
  one_mul x := ext <| by
    rw [val_mul, val_one, map_map_mul_of_map_eq_self hφ.out (map_val x), one_mul, map_val]
  mul_one x := ext <| by
    rw [val_mul, val_one, map_mul_map_of_map_eq_self hφ.out (map_val x), mul_one, map_val]

/-- `ChoiEffros φ` is a normed ring. -/
instance : NormedRing (ChoiEffros φ) where
  __ := (inferInstance : NonUnitalNormedRing (ChoiEffros φ))
  __ := (inferInstance : Ring (ChoiEffros φ))

/-- `ChoiEffros φ` is a complex algebra. -/
instance : Algebra ℂ (ChoiEffros φ) := Algebra.ofModule smul_mul_assoc mul_smul_comm

/-- `ChoiEffros φ` is a normed complex algebra. -/
instance : NormedAlgebra ℂ (ChoiEffros φ) where
  norm_smul_le := norm_smul_le

/-- On a unital `A`, the range of an idempotent Schwarz map, with the Choi–Effros product, is a
unital C⋆-algebra with unit `φ 1`. -/
instance : CStarAlgebra (ChoiEffros φ) where

end Unital

/-! ## Examples

The identity is an idempotent Schwarz map, with `ChoiEffros (SchwarzMap.id A)` the C⋆-algebra `A`
itself (`ChoiEffros.starAlgEquivId`). The map `x ↦ x 0 • e` on `ℂ²` with `e = (1, 1/2)` is an
idempotent Schwarz map whose range `ℂ e` is not a subalgebra, and whose Choi–Effros product differs
from the product of `ℂ²`: the unit of the range is `φ 1 = e`, with `e * e = e` for the Choi–Effros
product, while `e e = (1, 1/4) ≠ e` in `ℂ²`. -/

/-- The identity is idempotent. -/
instance (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] :
    Fact (IsIdempotentElem (SchwarzMap.id A : A →ₗ[ℂ] A)) :=
  ⟨LinearMap.ext fun _ => rfl⟩

variable (A) in
/-- `ChoiEffros (SchwarzMap.id A)` is the C⋆-algebra `A` itself. -/
def starAlgEquivId [PartialOrder A] [StarOrderedRing A] :
    ChoiEffros (SchwarzMap.id A) ≃⋆ₐ[ℂ] A where
  toFun := val
  invFun := ofMap _
  left_inv := ofMap_val
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

example (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] :
    CStarAlgebra (ChoiEffros (SchwarzMap.id A)) :=
  inferInstance

section Example

open scoped ComplexOrder

/- The map `x ↦ x 0 • e` on `ℂ²` with `e = (1, 1/2)`: the Kadison–Schwarz inequality reads
`|x 0|² e² ≤ |x 0|² e`, and `e² ≤ e` since `0 ≤ e ≤ 1`. -/
private def exampleMap : SchwarzMap (Fin 2 → ℂ) (Fin 2 → ℂ) where
  toLinearMap := (LinearMap.proj 0 : (Fin 2 → ℂ) →ₗ[ℂ] ℂ).smulRight ![1, 1/2]
  le_map_star_mul' x := by
    have he : star (![1, 1/2] : Fin 2 → ℂ) * ![1, 1/2] ≤ ![1, 1/2] := by
      intro i
      fin_cases i <;> norm_num [Complex.le_def]
    change star (x 0 • _) * (x 0 • _) ≤ (star x * x) 0 • _
    rw [star_smul, smul_mul_smul_comm, Pi.mul_apply, Pi.star_apply]
    exact smul_le_smul_of_nonneg_left he (star_mul_self_nonneg (x 0))

@[simp] private lemma exampleMap_apply (x : Fin 2 → ℂ) : exampleMap x = x 0 • (![1, 1/2] : Fin 2 → ℂ) :=
  rfl

private instance : Fact (IsIdempotentElem (exampleMap : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ))) :=
  ⟨LinearMap.ext fun x => by ext i; fin_cases i <;> simp⟩

/-- The Choi–Effros product of `exampleMap` is not the product of `ℂ²`. -/
example : ((1 : ChoiEffros exampleMap) * 1).val ≠
    (1 : ChoiEffros exampleMap).val * (1 : ChoiEffros exampleMap).val := by
  intro h
  have := congrFun h 1
  simp at this

/-- The range of `exampleMap` is not a subalgebra: it contains `e` but not `e * e`. -/
example : ¬ ∃ S : NonUnitalSubalgebra ℂ (Fin 2 → ℂ), Set.range exampleMap = S := by
  rintro ⟨S, hS⟩
  have he : (![1, 1/2] : Fin 2 → ℂ) ∈ Set.range exampleMap := ⟨1, by simp⟩
  rw [hS] at he
  obtain ⟨y, hy⟩ : (![1, 1/2] : Fin 2 → ℂ) * ![1, 1/2] ∈ Set.range exampleMap := by
    rw [hS]
    exact mul_mem he he
  have h0 : y 0 = 1 := by simpa using congrFun hy 0
  have h1 : y 0 * 2⁻¹ = 2⁻¹ * 2⁻¹ := by simpa using congrFun hy 1
  rw [h0] at h1
  norm_num at h1

end Example

end ChoiEffros
