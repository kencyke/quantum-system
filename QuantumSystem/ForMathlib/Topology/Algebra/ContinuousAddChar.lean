/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Constructions

/-!
# Continuous additive characters

Mathlib's `AddChar A M` is the type of maps `ψ` from an additive monoid `A` to a multiplicative
monoid `M` with `ψ 0 = 1` and `ψ (a + b) = ψ a * ψ b`: a homomorphism `Multiplicative A →* M`
applied to the elements of `A` themselves. This file bundles continuity with it, as
`ContinuousMonoidHom` does for `MonoidHom`: a `ContinuousAddChar A M` is a continuous additive
character, such as a strongly continuous one-parameter group `t ↦ U t`, for which
`U (s + t) = U s * U t`.

The class `AddCharClass F A M` states that the maps in `F` are additive characters, so that a result
holds for `AddChar A M` and `ContinuousAddChar A M` at once.

## Main definitions

* `AddCharClass F A M` — the maps in `F` send `0` to `1` and sums to products.
* `ContinuousAddChar A M` — the continuous additive characters of `A` with values in `M`.
* `ContinuousAddChar.toContinuousMonoidHomEquiv` — continuous additive characters of `A` are the
  continuous homomorphisms `Multiplicative A →ₜ* M`.
* `ContinuousAddChar.compContinuousAddMonoidHom ψ f` — the pullback `a ↦ ψ (f a)` along a continuous
  additive homomorphism `f`.
* `ContinuousMonoidHom.compContinuousAddChar f ψ` — the image `a ↦ f (ψ a)` under a continuous
  homomorphism `f`.
-/

@[expose] public section

/-! ### The class of additive characters -/

/-- `AddCharClass F A M` states that `F` is a type of additive characters: maps `ψ : A → M` from an
additive monoid to a multiplicative one with `ψ 0 = 1` and `ψ (a + b) = ψ a * ψ b`. -/
class AddCharClass (F : Type*) (A M : outParam Type*) [AddMonoid A] [Monoid M] [FunLike F A M] :
    Prop where
  /-- An additive character maps `0` to `1`. -/
  map_zero_eq_one (ψ : F) : ψ 0 = 1
  /-- An additive character maps sums to products. -/
  map_add_eq_mul (ψ : F) (a b : A) : ψ (a + b) = ψ a * ψ b

export AddCharClass (map_zero_eq_one map_add_eq_mul)

attribute [simp] map_zero_eq_one

namespace AddChar

variable {A M : Type*} [AddMonoid A] [Monoid M]

/-- Mathlib's additive characters are additive characters. -/
instance instAddCharClass : AddCharClass (AddChar A M) A M where
  map_zero_eq_one ψ := ψ.map_zero_eq_one
  map_add_eq_mul ψ := ψ.map_add_eq_mul

variable {F : Type*} [FunLike F A M] [AddCharClass F A M]

/-- An element of a type of additive characters, as an `AddChar`. -/
@[coe] def ofClass (ψ : F) : AddChar A M where
  toFun := ψ
  map_zero_eq_one' := AddCharClass.map_zero_eq_one ψ
  map_add_eq_mul' := AddCharClass.map_add_eq_mul ψ

/-- An element of a type of additive characters is coerced to an `AddChar`. -/
instance instCoeTC : CoeTC F (AddChar A M) := ⟨ofClass⟩

/-- The coercion to `AddChar` does not change the map. -/
@[simp, norm_cast] lemma coe_ofClass (ψ : F) : ⇑(ψ : AddChar A M) = ψ :=
  rfl

/-- The coercion to `AddChar` does not change the values. -/
lemma ofClass_apply (ψ : F) (a : A) : (ψ : AddChar A M) a = ψ a :=
  rfl

end AddChar

section AddCharClass

variable {F A M : Type*} [FunLike F A M]

/-- An additive character maps multiples by natural numbers to powers. -/
lemma map_nsmul_eq_pow [AddMonoid A] [Monoid M] [AddCharClass F A M] (ψ : F) (n : ℕ) (a : A) :
    ψ (n • a) = ψ a ^ n :=
  (ψ : AddChar A M).map_nsmul_eq_pow n a

/-- An additive character of a group maps negatives to inverses. -/
lemma map_neg_eq_inv [AddGroup A] [DivisionMonoid M] [AddCharClass F A M] (ψ : F) (a : A) :
    ψ (-a) = (ψ a)⁻¹ :=
  (ψ : AddChar A M).map_neg_eq_inv a

/-- An additive character of a group maps integer multiples to integer powers. -/
lemma map_zsmul_eq_zpow [AddGroup A] [DivisionMonoid M] [AddCharClass F A M] (ψ : F) (n : ℤ)
    (a : A) : ψ (n • a) = ψ a ^ n :=
  (ψ : AddChar A M).map_zsmul_eq_zpow n a

/-- An additive character of a group maps `a - b` to `ψ a * (ψ b)⁻¹`. -/
lemma map_sub_eq_mul_inv [AddGroup A] [DivisionMonoid M] [AddCharClass F A M] (ψ : F) (a b : A) :
    ψ (a - b) = ψ a * (ψ b)⁻¹ := by
  rw [sub_eq_add_neg, map_add_eq_mul, map_neg_eq_inv]

end AddCharClass

/-! ### Continuous additive characters -/

/-- The type of continuous additive characters of `A` with values in `M`: the continuous maps
`ψ : A → M` with `ψ 0 = 1` and `ψ (a + b) = ψ a * ψ b`.

When possible, instead of parametrizing results over `(ψ : ContinuousAddChar A M)`, parametrize
over `(F : Type*) [FunLike F A M] [ContinuousMapClass F A M] [AddCharClass F A M] (ψ : F)`. -/
structure ContinuousAddChar (A M : Type*) [AddMonoid A] [Monoid M] [TopologicalSpace A]
    [TopologicalSpace M] extends AddChar A M, C(A, M)

/-- Reinterpret a `ContinuousAddChar` as an `AddChar`. -/
add_decl_doc ContinuousAddChar.toAddChar

/-- Reinterpret a `ContinuousAddChar` as a `ContinuousMap`. -/
add_decl_doc ContinuousAddChar.toContinuousMap

namespace ContinuousAddChar

variable {A B M N : Type*} [AddMonoid A] [AddMonoid B] [Monoid M] [Monoid N] [TopologicalSpace A]
  [TopologicalSpace B] [TopologicalSpace M] [TopologicalSpace N]

/-- A continuous additive character is applied to the elements of `A`. -/
@[macro_inline]
instance instFunLike : FunLike (ContinuousAddChar A M) A M where
  coe ψ := ψ.toFun
  coe_injective ψ χ h := by
    obtain ⟨⟨_, _, _⟩, _⟩ := ψ
    obtain ⟨⟨_, _, _⟩, _⟩ := χ
    congr

/-- Continuous additive characters are additive characters. -/
instance instAddCharClass : AddCharClass (ContinuousAddChar A M) A M where
  map_zero_eq_one ψ := ψ.map_zero_eq_one'
  map_add_eq_mul ψ := ψ.map_add_eq_mul'

/-- Continuous additive characters are continuous. -/
instance instContinuousMapClass : ContinuousMapClass (ContinuousAddChar A M) A M where
  map_continuous ψ := ψ.continuous_toFun

/-- Continuous additive characters with the same values are equal. -/
@[ext] lemma ext {ψ χ : ContinuousAddChar A M} (h : ∀ a, ψ a = χ a) : ψ = χ :=
  DFunLike.ext ψ χ h

/-- The underlying `AddChar` has the same values. -/
@[simp] lemma coe_toAddChar (ψ : ContinuousAddChar A M) : ⇑ψ.toAddChar = ψ :=
  rfl

/-- The values of a continuous additive character given by an `AddChar` and its continuity. -/
@[simp] lemma coe_mk (ψ : AddChar A M) (hψ : Continuous ψ.toFun) :
    ⇑(ContinuousAddChar.mk ψ hψ) = ψ :=
  rfl

/-- A continuous additive character is continuous. -/
protected lemma continuous (ψ : ContinuousAddChar A M) : Continuous ψ :=
  ψ.continuous_toFun

/-- The trivial continuous additive character, sending everything to `1`. -/
instance instOne : One (ContinuousAddChar A M) := ⟨⟨1, continuous_const⟩⟩

/-- The trivial character is the constant map `1`. -/
@[simp, norm_cast] lemma coe_one : ⇑(1 : ContinuousAddChar A M) = 1 :=
  rfl

/-- The trivial character sends everything to `1`. -/
@[simp] lemma one_apply (a : A) : (1 : ContinuousAddChar A M) a = 1 :=
  rfl

/-- The trivial character is the default continuous additive character. -/
instance instInhabited : Inhabited (ContinuousAddChar A M) := ⟨1⟩

/-! ### Continuous homomorphisms from `Multiplicative A` -/

/-- A continuous additive character of `A`, as a continuous homomorphism from `Multiplicative A`. -/
def toContinuousMonoidHom (ψ : ContinuousAddChar A M) : Multiplicative A →ₜ* M where
  toMonoidHom := ψ.toAddChar.toMonoidHom
  continuous_toFun := ψ.continuous_toFun.comp continuous_toAdd

/-- `ψ.toContinuousMonoidHom` takes the value of `ψ` at the underlying element of `A`. -/
@[simp] lemma toContinuousMonoidHom_apply (ψ : ContinuousAddChar A M) (a : Multiplicative A) :
    ψ.toContinuousMonoidHom a = ψ a.toAdd :=
  rfl

/-- Continuous additive characters of `A` are the same thing as continuous homomorphisms from
`Multiplicative A`. -/
def toContinuousMonoidHomEquiv : ContinuousAddChar A M ≃ (Multiplicative A →ₜ* M) where
  toFun ψ := ψ.toContinuousMonoidHom
  invFun f := ⟨AddChar.toMonoidHomEquiv.symm f.toMonoidHom, f.continuous_toFun.comp continuous_ofAdd⟩

/-- `toContinuousMonoidHomEquiv ψ` takes the value of `ψ` at the underlying element of `A`. -/
@[simp] lemma toContinuousMonoidHomEquiv_apply (ψ : ContinuousAddChar A M) (a : Multiplicative A) :
    toContinuousMonoidHomEquiv ψ a = ψ a.toAdd :=
  rfl

/-- The continuous additive character of a continuous homomorphism `f` from `Multiplicative A` takes
the value of `f` at `Multiplicative.ofAdd a`. -/
@[simp] lemma toContinuousMonoidHomEquiv_symm_apply (f : Multiplicative A →ₜ* M) (a : A) :
    toContinuousMonoidHomEquiv.symm f a = f (Multiplicative.ofAdd a) :=
  rfl

/-! ### Composition -/

/-- The pullback `a ↦ ψ (f a)` of a continuous additive character along a continuous additive
homomorphism `f : A →ₜ+ B`. -/
def compContinuousAddMonoidHom (ψ : ContinuousAddChar B M) (f : A →ₜ+ B) : ContinuousAddChar A M :=
  ⟨ψ.toAddChar.compAddMonoidHom f.toAddMonoidHom, ψ.continuous_toFun.comp f.continuous_toFun⟩

/-- The pullback along `f` takes the value `ψ (f a)` at `a`. -/
@[simp] lemma compContinuousAddMonoidHom_apply (ψ : ContinuousAddChar B M) (f : A →ₜ+ B) (a : A) :
    ψ.compContinuousAddMonoidHom f a = ψ (f a) :=
  rfl

end ContinuousAddChar

namespace ContinuousMonoidHom

variable {A M N : Type*} [AddMonoid A] [Monoid M] [Monoid N] [TopologicalSpace A]
  [TopologicalSpace M] [TopologicalSpace N]

/-- The image `a ↦ f (ψ a)` of a continuous additive character under a continuous homomorphism
`f : M →ₜ* N`. -/
def compContinuousAddChar (f : M →ₜ* N) (ψ : ContinuousAddChar A M) : ContinuousAddChar A N :=
  ⟨f.toMonoidHom.compAddChar ψ.toAddChar, f.continuous_toFun.comp ψ.continuous_toFun⟩

/-- The image under `f` takes the value `f (ψ a)` at `a`. -/
@[simp] lemma compContinuousAddChar_apply (f : M →ₜ* N) (ψ : ContinuousAddChar A M) (a : A) :
    f.compContinuousAddChar ψ a = f (ψ a) :=
  rfl

end ContinuousMonoidHom
