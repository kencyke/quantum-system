/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Algebra.Star.TensorProduct
public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# The tensor product of two non-unital `⋆`-algebra homomorphisms

For non-unital `⋆`-algebra homomorphisms `φ : A₁ → A₂` and `ψ : B₁ → B₂` over a commutative star
ring, `TensorProduct.map φ ψ` is a non-unital `⋆`-algebra homomorphism
`A₁ ⊗[R] B₁ →⋆ₙₐ[R] A₂ ⊗[R] B₂`. Mathlib has the unital `Algebra.TensorProduct.map` only; likewise
for the commutativity and associativity isomorphisms, which are stated here for non-unital
`⋆`-algebras.

## Main definitions

* `NonUnitalStarAlgebra.TensorProduct.map φ ψ` — the tensor product of `φ` and `ψ`.
* `NonUnitalStarAlgebra.TensorProduct.productMap φ ψ h` — for commuting `φ : A₁ → D` and `ψ : B₁ → D`,
  the `⋆`-homomorphism `a ⊗ b ↦ φ a * ψ b`.
* `NonUnitalStarAlgebra.TensorProduct.comm` — `A₁ ⊗[R] B₁ ≃⋆ₐ[R] B₁ ⊗[R] A₁`.
* `NonUnitalStarAlgebra.TensorProduct.assoc` — `(A₁ ⊗[R] B₁) ⊗[R] C₁ ≃⋆ₐ[R] A₁ ⊗[R] (B₁ ⊗[R] C₁)`.
-/

@[expose] public section

open scoped TensorProduct

namespace NonUnitalStarAlgebra.TensorProduct

variable {R A₁ A₂ B₁ B₂ : Type*} [CommSemiring R] [StarRing R]
  [NonUnitalNonAssocSemiring A₁] [Module R A₁] [SMulCommClass R A₁ A₁] [IsScalarTower R A₁ A₁]
  [StarAddMonoid A₁] [StarModule R A₁]
  [NonUnitalNonAssocSemiring A₂] [Module R A₂] [SMulCommClass R A₂ A₂] [IsScalarTower R A₂ A₂]
  [StarAddMonoid A₂] [StarModule R A₂]
  [NonUnitalNonAssocSemiring B₁] [Module R B₁] [SMulCommClass R B₁ B₁] [IsScalarTower R B₁ B₁]
  [StarAddMonoid B₁] [StarModule R B₁]
  [NonUnitalNonAssocSemiring B₂] [Module R B₂] [SMulCommClass R B₂ B₂] [IsScalarTower R B₂ B₂]
  [StarAddMonoid B₂] [StarModule R B₂]

/-- The **tensor product of two non-unital `⋆`-algebra homomorphisms**, `a ⊗ b ↦ φ a ⊗ ψ b`. -/
protected noncomputable def map (φ : A₁ →⋆ₙₐ[R] A₂) (ψ : B₁ →⋆ₙₐ[R] B₂) :
    A₁ ⊗[R] B₁ →⋆ₙₐ[R] A₂ ⊗[R] B₂ where
  toFun := _root_.TensorProduct.map (φ : A₁ →ₗ[R] A₂) (ψ : B₁ →ₗ[R] B₂)
  map_smul' := map_smul _
  map_zero' := map_zero _
  map_add' := map_add _
  map_mul' x y := by
    induction x using TensorProduct.inductionOn with
    | tmul a b =>
      induction y using TensorProduct.inductionOn with
      | tmul a' b' =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.map_tmul,
          LinearMap.coe_ofClass, map_mul]
      | add y y' hy hy' => rw [mul_add, map_add, hy, hy', map_add, mul_add]
    | add x x' hx hx' => rw [add_mul, map_add, hx, hx', map_add, add_mul]
  map_star' x := by
    induction x using TensorProduct.inductionOn with
    | tmul a b => simp only [TensorProduct.star_tmul, TensorProduct.map_tmul, LinearMap.coe_ofClass,
        map_star]
    | add x x' hx hx' => rw [star_add, map_add, hx, hx', map_add, star_add]

section Product

variable {D : Type*} [NonUnitalSemiring D] [Module R D] [SMulCommClass R D D] [IsScalarTower R D D]
  [StarRing D]

/-- The **product of two commuting non-unital `⋆`-algebra homomorphisms** `φ : A₁ → D` and
`ψ : B₁ → D`, as a `⋆`-algebra homomorphism of the tensor product, `a ⊗ b ↦ φ a * ψ b`. -/
protected noncomputable def productMap (φ : A₁ →⋆ₙₐ[R] D) (ψ : B₁ →⋆ₙₐ[R] D)
    (h : ∀ a b, Commute (φ a) (ψ b)) : A₁ ⊗[R] B₁ →⋆ₙₐ[R] D where
  toFun := TensorProduct.lift (((LinearMap.mul R D).comp (φ : A₁ →ₗ[R] D)).compl₂
    (ψ : B₁ →ₗ[R] D))
  map_smul' := map_smul _
  map_zero' := map_zero _
  map_add' := map_add _
  map_mul' x y := by
    induction x using TensorProduct.inductionOn with
    | tmul a b =>
      induction y using TensorProduct.inductionOn with
      | tmul a' b' =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.lift.tmul,
          LinearMap.compl₂_apply, LinearMap.comp_apply, LinearMap.coe_ofClass,
          LinearMap.mul_apply', map_mul]
        rw [mul_assoc (φ a) (ψ b), ← mul_assoc (ψ b), ← (h a' b).eq]
        simp only [mul_assoc]
      | add y y' hy hy' => rw [mul_add, map_add, hy, hy', map_add, mul_add]
    | add x x' hx hx' => rw [add_mul, map_add, hx, hx', map_add, add_mul]
  map_star' x := by
    induction x using TensorProduct.inductionOn with
    | tmul a b =>
      simp only [TensorProduct.star_tmul, TensorProduct.lift.tmul, LinearMap.compl₂_apply,
        LinearMap.comp_apply, LinearMap.coe_ofClass, LinearMap.mul_apply', map_star, star_mul]
      exact ((h a b).star_star).eq
    | add x x' hx hx' => rw [star_add, map_add, hx, hx', map_add, star_add]

/-- `NonUnitalStarAlgebra.TensorProduct.productMap φ ψ h` sends `a ⊗ b` to `φ a * ψ b`. -/
@[simp] lemma productMap_tmul (φ : A₁ →⋆ₙₐ[R] D) (ψ : B₁ →⋆ₙₐ[R] D)
    (h : ∀ a b, Commute (φ a) (ψ b)) (a : A₁) (b : B₁) :
    TensorProduct.productMap φ ψ h (a ⊗ₜ b) = φ a * ψ b :=
  rfl

end Product

/-- `NonUnitalStarAlgebra.TensorProduct.map φ ψ` is `TensorProduct.map φ ψ`. -/
@[simp] lemma map_apply (φ : A₁ →⋆ₙₐ[R] A₂) (ψ : B₁ →⋆ₙₐ[R] B₂)
    (x : A₁ ⊗[R] B₁) :
    TensorProduct.map φ ψ x = _root_.TensorProduct.map (φ : A₁ →ₗ[R] A₂) (ψ : B₁ →ₗ[R] B₂) x :=
  rfl

/-- The **commutativity of the tensor product of non-unital `⋆`-algebras**, `a ⊗ b ↦ b ⊗ a`, as a
`⋆`-algebra isomorphism. -/
protected noncomputable def comm : A₁ ⊗[R] B₁ ≃⋆ₐ[R] B₁ ⊗[R] A₁ :=
  { _root_.TensorProduct.comm R A₁ B₁ with
    map_mul' x y := by
      change _root_.TensorProduct.comm R A₁ B₁ (x * y) =
        _root_.TensorProduct.comm R A₁ B₁ x * _root_.TensorProduct.comm R A₁ B₁ y
      induction x using TensorProduct.inductionOn with
      | tmul a b =>
        induction y using TensorProduct.inductionOn with
        | tmul a' b' => simp only [Algebra.TensorProduct.tmul_mul_tmul, _root_.TensorProduct.comm_tmul]
        | add y y' hy hy' => rw [mul_add, map_add, hy, hy', map_add, mul_add]
      | add x x' hx hx' => rw [add_mul, map_add, hx, hx', map_add, add_mul]
    map_star' x := by
      change _root_.TensorProduct.comm R A₁ B₁ (star x) = star (_root_.TensorProduct.comm R A₁ B₁ x)
      induction x using TensorProduct.inductionOn with
      | tmul a b => simp only [TensorProduct.star_tmul, _root_.TensorProduct.comm_tmul]
      | add x x' hx hx' => rw [star_add, map_add, hx, hx', map_add, star_add] }

/-- `NonUnitalStarAlgebra.TensorProduct.comm` sends `a ⊗ b` to `b ⊗ a`. -/
@[simp] lemma comm_tmul (a : A₁) (b : B₁) :
    TensorProduct.comm (R := R) (a ⊗ₜ b) = b ⊗ₜ a :=
  rfl

/-- `NonUnitalStarAlgebra.TensorProduct.comm` is `TensorProduct.comm`. -/
@[simp] lemma comm_apply (x : A₁ ⊗[R] B₁) :
    TensorProduct.comm x = _root_.TensorProduct.comm R A₁ B₁ x :=
  rfl

section Assoc

variable {C₁ : Type*} [NonUnitalNonAssocSemiring C₁] [Module R C₁] [SMulCommClass R C₁ C₁]
  [IsScalarTower R C₁ C₁] [StarAddMonoid C₁] [StarModule R C₁]

/-- The **associativity of the tensor product of non-unital `⋆`-algebras**,
`(a ⊗ b) ⊗ c ↦ a ⊗ (b ⊗ c)`, as a `⋆`-algebra isomorphism. -/
protected noncomputable def assoc :
    (A₁ ⊗[R] B₁) ⊗[R] C₁ ≃⋆ₐ[R] A₁ ⊗[R] (B₁ ⊗[R] C₁) :=
  { _root_.TensorProduct.assoc R A₁ B₁ C₁ with
    map_mul' x y := by
      change _root_.TensorProduct.assoc R A₁ B₁ C₁ (x * y) =
        _root_.TensorProduct.assoc R A₁ B₁ C₁ x * _root_.TensorProduct.assoc R A₁ B₁ C₁ y
      induction x using TensorProduct.inductionOn with
      | tmul x c =>
        induction y using TensorProduct.inductionOn with
        | tmul y c' =>
          induction x using TensorProduct.inductionOn with
          | tmul a b =>
            induction y using TensorProduct.inductionOn with
            | tmul a' b' =>
              simp only [Algebra.TensorProduct.tmul_mul_tmul, _root_.TensorProduct.assoc_tmul]
            | add y y' hy hy' => simp only [TensorProduct.add_tmul, mul_add, map_add, hy, hy']
          | add x x' hx hx' => simp only [TensorProduct.add_tmul, add_mul, map_add, hx, hx']
        | add y y' hy hy' => rw [mul_add, map_add, hy, hy', map_add, mul_add]
      | add x x' hx hx' => rw [add_mul, map_add, hx, hx', map_add, add_mul]
    map_star' x := by
      change _root_.TensorProduct.assoc R A₁ B₁ C₁ (star x) = star (_root_.TensorProduct.assoc R A₁ B₁ C₁ x)
      induction x using TensorProduct.inductionOn with
      | tmul x c =>
        induction x using TensorProduct.inductionOn with
        | tmul a b => simp only [TensorProduct.star_tmul, _root_.TensorProduct.assoc_tmul]
        | add x x' hx hx' => simp only [TensorProduct.add_tmul, star_add, map_add, hx, hx']
      | add x x' hx hx' => rw [star_add, map_add, hx, hx', map_add, star_add] }

/-- `NonUnitalStarAlgebra.TensorProduct.assoc` sends `(a ⊗ b) ⊗ c` to `a ⊗ (b ⊗ c)`. -/
@[simp] lemma assoc_tmul (a : A₁) (b : B₁) (c : C₁) :
    TensorProduct.assoc (R := R) ((a ⊗ₜ b) ⊗ₜ c) = a ⊗ₜ (b ⊗ₜ c) :=
  rfl

/-- `NonUnitalStarAlgebra.TensorProduct.assoc` is `TensorProduct.assoc`. -/
@[simp] lemma assoc_apply (x : (A₁ ⊗[R] B₁) ⊗[R] C₁) :
    TensorProduct.assoc x = _root_.TensorProduct.assoc R A₁ B₁ C₁ x :=
  rfl

end Assoc

end NonUnitalStarAlgebra.TensorProduct
