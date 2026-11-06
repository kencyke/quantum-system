/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Algebra.Star.StarAlgHom

/-!
# Products of ⋆-homomorphisms and ⋆-isomorphisms

The ⋆-versions of `AlgHom.pi`, `AlgEquiv.piCongrRight` and `AlgEquiv.piCongrLeft'`. The
⋆-isomorphisms need only the operations `+`, `*`, `•` and `⋆` on the factors, as `StarAlgEquiv`
does, so they apply to non-unital ⋆-algebras as well.

## Main definitions

* `NonUnitalStarAlgHom.pi`, `StarAlgHom.pi`: the product of a family of (non-unital)
  ⋆-homomorphisms out of a common domain.
* `StarAlgEquiv.piCongrRight`: the product of a family of ⋆-isomorphisms.
* `StarAlgEquiv.piCongrLeft'`: reindexing a product of ⋆-algebras along an equivalence of the index
  types.
-/

@[expose] public section

section Pi

variable {ι R A : Type*} {B : ι → Type*} [Monoid R] [NonUnitalNonAssocSemiring A]
  [DistribMulAction R A] [Star A] [∀ i, NonUnitalNonAssocSemiring (B i)]
  [∀ i, DistribMulAction R (B i)] [∀ i, Star (B i)]

/-- The product of a family of non-unital ⋆-homomorphisms out of a common domain. -/
@[simps]
def NonUnitalStarAlgHom.pi (f : Π i, A →⋆ₙₐ[R] B i) : A →⋆ₙₐ[R] Π i, B i where
  toFun a i := f i a
  map_smul' r a := funext fun i ↦ map_smul (f i) r a
  map_zero' := funext fun i ↦ map_zero (f i)
  map_add' a b := funext fun i ↦ map_add (f i) a b
  map_mul' a b := funext fun i ↦ map_mul (f i) a b
  map_star' a := funext fun i ↦ map_star (f i) a

end Pi

section PiUnital

variable {ι R A : Type*} {B : ι → Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Star A]
  [∀ i, Semiring (B i)] [∀ i, Algebra R (B i)] [∀ i, Star (B i)]

/-- The product of a family of ⋆-homomorphisms out of a common domain; `AlgHom.pi` as a
⋆-homomorphism. -/
@[simps!]
def StarAlgHom.pi (f : Π i, A →⋆ₐ[R] B i) : A →⋆ₐ[R] Π i, B i where
  __ := AlgHom.pi fun i ↦ (f i).toAlgHom
  map_star' a := funext fun i ↦ map_star (f i) a

end PiUnital

section PiCongrRight

variable {ι R : Type*} {A B : ι → Type*} [∀ i, Add (A i)] [∀ i, Mul (A i)] [∀ i, SMul R (A i)]
  [∀ i, Star (A i)] [∀ i, Add (B i)] [∀ i, Mul (B i)] [∀ i, SMul R (B i)] [∀ i, Star (B i)]

/-- The product of a family of ⋆-isomorphisms. -/
def StarAlgEquiv.piCongrRight (e : ∀ i, A i ≃⋆ₐ[R] B i) : (Π i, A i) ≃⋆ₐ[R] Π i, B i where
  toFun x i := e i (x i)
  invFun y i := (e i).symm (y i)
  left_inv x := funext fun i ↦ (e i).symm_apply_apply (x i)
  right_inv y := funext fun i ↦ (e i).apply_symm_apply (y i)
  map_add' x y := funext fun i ↦ map_add (e i) (x i) (y i)
  map_mul' x y := funext fun i ↦ map_mul (e i) (x i) (y i)
  map_smul' r x := funext fun i ↦ map_smul (e i) r (x i)
  map_star' x := funext fun i ↦ map_star (e i) (x i)

/-- The product of ⋆-isomorphisms acts componentwise. -/
@[simp]
lemma StarAlgEquiv.piCongrRight_apply (e : ∀ i, A i ≃⋆ₐ[R] B i) (x : Π i, A i) (i : ι) :
    StarAlgEquiv.piCongrRight e x i = e i (x i) :=
  rfl

end PiCongrRight

section PiCongrLeft

variable {ι ι' : Type*} (R : Type*) (A : ι → Type*) [∀ i, Add (A i)] [∀ i, Mul (A i)]
  [∀ i, SMul R (A i)] [∀ i, Star (A i)]

/-- Reindexing a product of ⋆-algebras along an equivalence of the index types; the ⋆-version of
`AlgEquiv.piCongrLeft'`. -/
def StarAlgEquiv.piCongrLeft' (e : ι ≃ ι') : (Π i, A i) ≃⋆ₐ[R] Π i, A (e.symm i) where
  __ := Equiv.piCongrLeft' A e
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

/-- Reindexing acts by precomposition. -/
@[simp]
lemma StarAlgEquiv.piCongrLeft'_apply (e : ι ≃ ι') (x : Π i, A i) (i : ι') :
    StarAlgEquiv.piCongrLeft' R A e x i = x (e.symm i) :=
  rfl

end PiCongrLeft
