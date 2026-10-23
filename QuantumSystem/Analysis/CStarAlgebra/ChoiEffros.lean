/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

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

Associativity rests on the identities `φ(φ(x) φ(y)) = φ(φ(x) y) = φ(x φ(y))`
(`SchwarzMapClass.map_map_mul_map_eq_map_map_mul`,
`SchwarzMapClass.map_map_mul_map_eq_map_mul_map`). They are an equality case of the
Kadison–Schwarz inequality: for `a` in the range, `φ` sends `φ(a⋆ a) - φ(a)⋆ φ(a)` to `0`, and a
positive map that kills this defect at `a` kills `φ(a⋆ b) - φ(a)⋆ φ(b)` for every `b`
(`SchwarzMapClass.map_map_star_mul_of_map_map_star_mul_self`), so `φ(a⋆ b) = φ(a⋆ φ(b))`. The
C⋆-identity `‖φ(x⋆ x)‖ = ‖x‖²` follows from the contractivity of `φ`
(`SchwarzMapClass.norm_apply_le`) and from `x⋆ x = φ(x)⋆ φ(x) ≤ φ(x⋆ x)`. On a unital `A` the range
is unital, with unit `φ 1`, whether or not `φ 1 = 1`. The order of the range as a C⋆-algebra is the
order of `A` (`ChoiEffros.val_nonneg_iff`): a positive `x⋆ ∘ x = φ(x⋆ x)` is positive in `A`, and
conversely `0 ≤ x ≤ t` in `A` gives `‖t s - x ∘ s‖ = ‖φ((t - x) s)‖ ≤ ‖t - x‖ ‖s‖ ≤ t ‖s‖` for `s`
in the range, so that `‖t - x‖ ≤ t` in the unitization of the range.

When `φ` is a projection onto a ⋆-subalgebra `S` (`LinearMap.IsProj S.toSubmodule φ`), `S` lies in
the multiplicative domain of `φ` (`SchwarzMapClass.le_multiplicativeDomain_of_isProj`): `φ` is
`S`-bilinear, `φ(s x s') = s φ(x) s'`, and the Choi–Effros product is the product of `A`
(`ChoiEffros.val_mul_of_isProj`).

The idempotence of `φ` is a `Fact` instance argument of the C⋆-algebra structure rather than an
argument of the type, so that the type does not depend on a proof.

## Main definitions

* `ChoiEffros φ` — the range of `φ`; for an idempotent Schwarz map `φ`, with the Choi–Effros
  product, a `NonUnitalCStarAlgebra`, and a `CStarAlgebra` when `A` is unital.

## Main results

* `ChoiEffros.val_nonneg_iff`, `ChoiEffros.val_le_val` — the order of the range as a C⋆-algebra is the
  order of `A`.
* `ChoiEffros.val_mul_of_isProj` — when `φ` is a projection onto a ⋆-subalgebra, the Choi–Effros
  product is the product of `A`.

The identities on idempotent Schwarz maps that the construction rests on live in
`QuantumSystem.ForMathlib.Analysis.CStarAlgebra.SchwarzMap`.
-/

@[expose] public noncomputable section

open scoped CStarAlgebra ComplexConjugate NNReal

open SchwarzMapClass

variable {F A : Type*} [NonUnitalCStarAlgebra A] [FunLike F A A] [LinearMapClass F ℂ A A]

/-- The range of a linear map `φ : A → A`, which carries the Choi–Effros product `x * y = φ(x y)`
when `φ` is an idempotent Schwarz map. -/
def ChoiEffros (φ : F) : Type _ :=
  LinearMap.range (φ : A →ₗ[ℂ] A)

namespace ChoiEffros

variable {φ : F}

instance : NormedAddCommGroup (ChoiEffros φ) :=
  inferInstanceAs (NormedAddCommGroup (LinearMap.range (φ : A →ₗ[ℂ] A)))

instance : NormedSpace ℂ (ChoiEffros φ) :=
  inferInstanceAs (NormedSpace ℂ (LinearMap.range (φ : A →ₗ[ℂ] A)))

/-- The underlying element of `A`. -/
@[coe] def val (x : ChoiEffros φ) : A :=
  Subtype.val (p := (· ∈ LinearMap.range (φ : A →ₗ[ℂ] A))) x

instance : CoeOut (ChoiEffros φ) A := ⟨val⟩

lemma val_injective : Function.Injective (val : ChoiEffros φ → A) :=
  Subtype.val_injective

@[ext] lemma ext {x y : ChoiEffros φ} (h : x.val = y.val) : x = y :=
  val_injective h

@[simp] lemma val_zero : (0 : ChoiEffros φ).val = 0 := rfl

@[simp] lemma val_add (x y : ChoiEffros φ) : (x + y).val = x.val + y.val := rfl

@[simp] lemma val_neg (x : ChoiEffros φ) : (-x).val = -x.val := rfl

@[simp] lemma val_sub (x y : ChoiEffros φ) : (x - y).val = x.val - y.val := rfl

@[simp] lemma val_smul (c : ℂ) (x : ChoiEffros φ) : (c • x).val = c • x.val := rfl

@[simp] lemma val_real_smul (r : ℝ) (x : ChoiEffros φ) : (r • x).val = r • x.val := rfl

@[simp] lemma norm_val (x : ChoiEffros φ) : ‖x.val‖ = ‖x‖ := rfl

@[simp] lemma nnnorm_val (x : ChoiEffros φ) : ‖x.val‖₊ = ‖x‖₊ := rfl

variable (φ) in
/-- The element `φ a` of the range. -/
def ofMap (a : A) : ChoiEffros φ :=
  (⟨φ a, LinearMap.mem_range_self (φ : A →ₗ[ℂ] A) a⟩ : LinearMap.range (φ : A →ₗ[ℂ] A))

@[simp] lemma val_ofMap (a : A) : (ofMap φ a).val = φ a := rfl

/-- The Choi–Effros product `x * y = φ(x y)`. -/
instance : Mul (ChoiEffros φ) := ⟨fun x y => ofMap φ (x.val * y.val)⟩

lemma val_mul (x y : ChoiEffros φ) : (x * y).val = φ (x.val * y.val) := rfl

variable [hφ : Fact (IsIdempotentElem (φ : A →ₗ[ℂ] A))]

/-- `φ` fixes its range. -/
@[simp] lemma map_val (x : ChoiEffros φ) : φ x.val = x.val :=
  (LinearMap.IsIdempotentElem.mem_range_iff hφ.out).mp x.2

@[simp] lemma ofMap_val (x : ChoiEffros φ) : ofMap φ x.val = x := ext <| map_val x

/-- The range of a continuous idempotent map is its set of fixed points, hence closed. -/
instance [ContinuousMapClass F A A] : CompleteSpace (ChoiEffros φ) :=
  (((LinearMap.isProj_range_iff_isIdempotentElem _).mpr hφ.out).isClosed
    (map_continuous φ)).completeSpace_coe

section Schwarz

variable [PartialOrder A] [StarOrderedRing A] [SchwarzMapClass F A A]

instance : Star (ChoiEffros φ) := ⟨fun x => ofMap φ (star x.val)⟩

@[simp] lemma val_star (x : ChoiEffros φ) : (star x).val = star x.val := by
  change φ (star x.val) = star x.val
  rw [map_star, map_val]

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

instance : NonUnitalNormedRing (ChoiEffros φ) where
  __ := (inferInstance : NormedAddCommGroup (ChoiEffros φ))
  __ := (inferInstance : NonUnitalRing (ChoiEffros φ))
  norm_mul_le x y := by
    rw [← norm_val, val_mul, ← norm_val, ← norm_val]
    exact (norm_apply_le φ _).trans (norm_mul_le _ _)

instance : StarRing (ChoiEffros φ) where
  star_involutive x := ext <| by simp
  star_mul x y := ext <| by simp [val_mul, ← map_star, star_mul]
  star_add x y := ext <| by simp

instance : StarModule ℂ (ChoiEffros φ) where
  star_smul c x := ext <| by simp

instance : IsScalarTower ℂ (ChoiEffros φ) (ChoiEffros φ) where
  smul_assoc c x y := ext <| by simp [val_mul, smul_mul_assoc]

instance : SMulCommClass ℂ (ChoiEffros φ) (ChoiEffros φ) where
  smul_comm c x y := ext <| by simp [val_mul, mul_smul_comm]

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

instance : StarOrderedRing (ChoiEffros φ) := CStarAlgebra.spectralOrderedRing _

/-- The positive elements of `ChoiEffros φ` are positive in `A`: `x⋆ * x = φ(x⋆ x)`. -/
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
`0 ≤ x ≤ t` in `A` gives `‖t s - x * s‖ = ‖φ((t - x) s)‖ ≤ ‖t - x‖ ‖s‖ ≤ t ‖s‖` for `s` in the
range, so `‖t - x‖ ≤ t` in the unitization of the range. -/
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

/-- When `φ` is a projection onto a ⋆-subalgebra `S`, the Choi–Effros product is the product of
`A`. -/
lemma val_mul_of_isProj {S : NonUnitalStarSubalgebra ℂ A} (hS : LinearMap.IsProj S.toSubmodule φ)
    (x y : ChoiEffros φ) : (x * y).val = x.val * y.val := by
  rw [val_mul, ((le_multiplicativeDomain_of_isProj hS) _ _).1, map_val, map_val]
  exact map_val x ▸ hS.map_mem x.val

end Schwarz

section Unital

variable {F A : Type*} [CStarAlgebra A] [FunLike F A A] [LinearMapClass F ℂ A A] {φ : F}

/-- The unit `φ 1`: `φ(φ(1) x) = φ(x) = x` for `x` in the range. -/
instance : One (ChoiEffros φ) := ⟨ofMap φ 1⟩

@[simp] lemma val_one : (1 : ChoiEffros φ).val = φ 1 := rfl

variable [PartialOrder A] [StarOrderedRing A] [SchwarzMapClass F A A]
  [hφ : Fact (IsIdempotentElem (φ : A →ₗ[ℂ] A))]

instance : Ring (ChoiEffros φ) where
  __ := (inferInstance : NonUnitalRing (ChoiEffros φ))
  one_mul x := ext <| by
    rw [val_mul, val_one, map_map_mul_of_map_eq_self hφ.out (map_val x), one_mul, map_val]
  mul_one x := ext <| by
    rw [val_mul, val_one, map_mul_map_of_map_eq_self hφ.out (map_val x), mul_one, map_val]

instance : NormedRing (ChoiEffros φ) where
  __ := (inferInstance : NonUnitalNormedRing (ChoiEffros φ))
  __ := (inferInstance : Ring (ChoiEffros φ))

instance : Algebra ℂ (ChoiEffros φ) := Algebra.ofModule smul_mul_assoc mul_smul_comm

instance : NormedAlgebra ℂ (ChoiEffros φ) where
  norm_smul_le := norm_smul_le

/-- On a unital `A`, the range of an idempotent Schwarz map, with the Choi–Effros product, is a
unital C⋆-algebra with unit `φ 1`. -/
instance : CStarAlgebra (ChoiEffros φ) where

end Unital

/-! ## Examples

The identity is an idempotent Schwarz map, with `ChoiEffros (SchwarzMap.id A)` the C⋆-algebra `A`
itself. `ChoiEffros.exampleMap`, `x ↦ x 0 • e` on `ℂ²` with `e = (1, 1/2)`, is an idempotent
Schwarz map whose range `ℂ e` is not a subalgebra, and whose Choi–Effros product differs from the
product of `ℂ²`: `1 * 1 = 1` in the range, while `e e ≠ e`. -/

instance (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] :
    Fact (IsIdempotentElem (SchwarzMap.id A : A →ₗ[ℂ] A)) :=
  ⟨LinearMap.ext fun _ => rfl⟩

example (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] :
    CStarAlgebra (ChoiEffros (SchwarzMap.id A)) :=
  inferInstance

section Example

open scoped ComplexOrder

/-- The map `x ↦ x 0 • e` on `ℂ²` with `e = (1, 1/2)`: the Kadison–Schwarz inequality reads
`|x 0|² e² ≤ |x 0|² e`, and `e² ≤ e` since `0 ≤ e ≤ 1`. -/
def exampleMap : SchwarzMap (Fin 2 → ℂ) (Fin 2 → ℂ) where
  toLinearMap := (LinearMap.proj 0 : (Fin 2 → ℂ) →ₗ[ℂ] ℂ).smulRight ![1, 1/2]
  le_map_star_mul' x := by
    have he : star (![1, 1/2] : Fin 2 → ℂ) * ![1, 1/2] ≤ ![1, 1/2] := by
      intro i
      fin_cases i <;> norm_num [Complex.le_def]
    change star (x 0 • _) * (x 0 • _) ≤ (star x * x) 0 • _
    rw [star_smul, smul_mul_smul_comm, Pi.mul_apply, Pi.star_apply]
    exact smul_le_smul_of_nonneg_left he (star_mul_self_nonneg (x 0))

@[simp] lemma exampleMap_apply (x : Fin 2 → ℂ) : exampleMap x = x 0 • (![1, 1/2] : Fin 2 → ℂ) :=
  rfl

instance : Fact (IsIdempotentElem (exampleMap : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ))) :=
  ⟨LinearMap.ext fun x => by ext i; fin_cases i <;> simp⟩

/-- The Choi–Effros product of `exampleMap` is not the product of `ℂ²`. -/
example : ((1 : ChoiEffros exampleMap) * 1).val ≠
    (1 : ChoiEffros exampleMap).val * (1 : ChoiEffros exampleMap).val := by
  intro h
  have := congrFun h 1
  simp at this

/-- The range of `exampleMap` is not a ⋆-subalgebra: it contains `e` but not `e * e`. -/
example : ¬ ∃ S : NonUnitalStarSubalgebra ℂ (Fin 2 → ℂ), Set.range exampleMap = S := by
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
