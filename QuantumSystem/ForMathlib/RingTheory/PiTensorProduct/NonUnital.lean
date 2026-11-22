/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.RingTheory.PiTensorProduct

/-!
# The tensor product of a family of non-unital rings

Mathlib defines the multiplication of `⨂[R] i, A i` for non-unital, non-associative semirings
`A i` (`PiTensorProduct.instNonUnitalNonAssocSemiring`), but its ring structure
(`PiTensorProduct.instRing`) and the compatibility of the multiplication with the scalars only for
unital algebras. This file drafts them for non-unital rings: `R` acts on `⨂[R] i, A i` as a scalar
tower and commutes with its multiplication, and `⨂[R] i, A i` is a non-unital ring when every
`A i` is one. For unital `A i` the ring structure agrees with Mathlib's by `rfl`.

## Main definitions

* `PiTensorProduct.instIsScalarTowerSelf`, `PiTensorProduct.instSMulCommClassSelf` — the scalars
  commute with the multiplication of `⨂[R] i, A i`.
* `PiTensorProduct.instNonUnitalRing` — the tensor product of non-unital rings is a non-unital
  ring.

## TODO

Generalizing `PiTensorProduct.instRing` upstream to non-unital rings, with the two scalar
instances, retires this draft.
-/

@[expose] public section

open scoped TensorProduct

namespace PiTensorProduct

section NonUnitalSemiring

variable {ι R : Type*} {A : ι → Type*} [CommSemiring R] [∀ i, NonUnitalNonAssocSemiring (A i)]
  [∀ i, Module R (A i)] [∀ i, SMulCommClass R (A i) (A i)] [∀ i, IsScalarTower R (A i) (A i)]

/-- The scalars form a scalar tower over the multiplication of `⨂[R] i, A i`. -/
instance instIsScalarTowerSelf : IsScalarTower R (⨂[R] i, A i) (⨂[R] i, A i) where
  smul_assoc r x y := by
    change mul (r • x) y = r • mul x y
    rw [map_smul, LinearMap.smul_apply]

/-- The scalars commute with the multiplication of `⨂[R] i, A i`. -/
instance instSMulCommClassSelf : SMulCommClass R (⨂[R] i, A i) (⨂[R] i, A i) where
  smul_comm r x y := by
    change r • mul x y = mul x (r • y)
    rw [map_smul]

end NonUnitalSemiring

section NonUnitalRing

variable {ι R : Type*} {A : ι → Type*} [CommRing R] [∀ i, NonUnitalRing (A i)]
  [∀ i, Module R (A i)] [∀ i, SMulCommClass R (A i) (A i)] [∀ i, IsScalarTower R (A i) (A i)]

/-- The tensor product of non-unital rings is a non-unital ring. -/
instance instNonUnitalRing : NonUnitalRing (⨂[R] i, A i) where
  __ := instNonUnitalSemiring
  __ := (inferInstance : AddCommGroup (⨂[R] i, A i))

end NonUnitalRing

end PiTensorProduct
