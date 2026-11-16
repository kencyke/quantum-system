/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Algebra.Star.Module
public import Mathlib.RingTheory.PiTensorProduct

/-!
# The involution on a tensor product of a family of star modules

For a family `A i` of star modules over a commutative star ring `R`, the tensor product
`⨂[R] i, A i` carries the involution `star (⨂ m) = ⨂ (star ∘ m)`, conjugate-linear:
`star (r • x) = star r • star x`. It is built from the universal property of the tensor product for
additive maps (`PiTensorProduct.liftAddHom`), as the conjugate-linearity rules out
`PiTensorProduct.lift`. For a family of star rings, the tensor product is a star ring.

## Main definitions

* `PiTensorProduct.instStar` — `star (⨂ m) = ⨂ (star ∘ m)`.

## Main results

* `PiTensorProduct.star_tprod` — `star (⨂ m) = ⨂ (star ∘ m)`.
* `PiTensorProduct.instStarAddMonoid`, `PiTensorProduct.instStarModule` — the involution is
  additive and conjugate-linear.
* `PiTensorProduct.instStarRing` — for a family of star rings, the tensor product is a star ring.
-/

@[expose] public section

open scoped TensorProduct

namespace PiTensorProduct

variable {ι R : Type*} [CommSemiring R] [StarRing R] {A : ι → Type*} [∀ i, AddCommMonoid (A i)]
  [∀ i, Module R (A i)] [∀ i, StarAddMonoid (A i)] [∀ i, StarModule R (A i)]

private lemma star_comp_update [DecidableEq ι] (f : Π i, A i) (i : ι) (x : A i) :
    (fun j => star (Function.update f i x j)) = Function.update (fun j => star (f j)) i (star x) :=
  funext fun j => Function.apply_update (fun _ y => star y) f i x j

/-- The involution `star (r • ⨂ m) = star r • ⨂ (star ∘ m)`, as an additive map. -/
noncomputable def starAddHom : (⨂[R] i, A i) →+ (⨂[R] i, A i) :=
  liftAddHom (fun p => tprodCoeff R (star p.1) fun i => star (p.2 i))
    (fun r f i hf => zero_tprodCoeff' _ _ i (by change star (f i) = 0; rw [hf, star_zero]))
    (fun f => by rw [star_zero, zero_tprodCoeff])
    (fun r f i m₁ m₂ => by
      simp only [star_comp_update, star_add]
      exact add_tprodCoeff _ _ i _ _)
    (fun r r' f => by rw [star_add, add_tprodCoeff'])
    (fun r f i r' => by
      simp only [star_comp_update, star_smul]
      rw [smul_tprodCoeff, smul_eq_mul, star_mul', mul_comm])

/-- The involution of the tensor product: `star (⨂ m) = ⨂ (star ∘ m)`. -/
noncomputable instance instStar : Star (⨂[R] i, A i) where
  star := starAddHom

/-- `star` acts on `tprodCoeff R r f` coefficientwise and factorwise. -/
lemma star_tprodCoeff (r : R) (f : Π i, A i) :
    star (tprodCoeff R r f) = tprodCoeff R (star r) fun i => star (f i) :=
  rfl

/-- `star (⨂ m) = ⨂ (star ∘ m)`. -/
@[simp] lemma star_tprod (f : Π i, A i) : star (tprod R f) = tprod R fun i => star (f i) := by
  rw [tprod_eq_tprodCoeff_one, star_tprodCoeff, star_one]

/-- The involution of the tensor product is additive. -/
private lemma star_add' (x y : ⨂[R] i, A i) : star (x + y) = star x + star y :=
  map_add starAddHom x y

/-- The involution of the tensor product is conjugate-linear. -/
private lemma star_smul' (r : R) (x : ⨂[R] i, A i) : star (r • x) = star r • star x := by
  induction x using PiTensorProduct.induction_on' with
  | tprodCoeff z f => rw [smul_tprodCoeff', star_tprodCoeff, star_tprodCoeff, smul_tprodCoeff',
      smul_eq_mul, smul_eq_mul, star_mul', mul_comm]
  | add x y hx hy => rw [smul_add, star_add', star_add', hx, hy, smul_add]

/-- The involution of the tensor product is involutive. -/
noncomputable instance instInvolutiveStar : InvolutiveStar (⨂[R] i, A i) where
  star_involutive x := by
    induction x using PiTensorProduct.induction_on' with
    | tprodCoeff z f => simp only [star_tprodCoeff, star_star]
    | add x y hx hy => rw [star_add', star_add', hx, hy]

/-- The tensor product of `⋆`-additive monoids is a `⋆`-additive monoid. -/
noncomputable instance instStarAddMonoid : StarAddMonoid (⨂[R] i, A i) where
  star_add := map_add starAddHom

/-- The involution of the tensor product is conjugate-linear: `star (r • x) = star r • star x`. -/
instance instStarModule : StarModule R (⨂[R] i, A i) where
  star_smul := star_smul'

section StarRing

variable {A : ι → Type*} [∀ i, NonUnitalNonAssocSemiring (A i)] [∀ i, Module R (A i)]
  [∀ i, SMulCommClass R (A i) (A i)] [∀ i, IsScalarTower R (A i) (A i)] [∀ i, StarRing (A i)]
  [∀ i, StarModule R (A i)]

/-- For a family of star rings, the tensor product is a star ring:
`star (⨂ m * ⨂ n) = ⨂ (star ∘ n) * ⨂ (star ∘ m)`. -/
noncomputable instance instStarRing : StarRing (⨂[R] i, A i) where
  star_mul x y := by
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r m =>
      induction y using PiTensorProduct.induction_on with
      | smul_tprod r' n =>
        rw [smul_tprod_mul_smul_tprod, star_smul', star_tprod, star_smul', star_smul', star_tprod,
          star_tprod, smul_tprod_mul_smul_tprod, star_mul', mul_comm (star r)]
        congr 2
        funext i
        exact star_mul (m i) (n i)
      | add y y' hy hy' => rw [mul_add, star_add', hy, hy', star_add', add_mul]
    | add x x' hx hx' => rw [add_mul, star_add', hx, hx', star_add', mul_add]
  star_add := star_add

end StarRing

end PiTensorProduct
