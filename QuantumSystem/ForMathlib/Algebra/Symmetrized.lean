/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Algebra.Star.Module
public import Mathlib.Algebra.Symmetrized

/-!
# The star operation on the symmetrized algebra

The symmetrized algebra `αˢʸᵐ` carries the star operation of `α`, `star (sym a) = sym (star a)`.
When `α` is a ⋆-ring in which `2` is invertible, the Jordan product `a ∘ b = ⅟2 * (a * b + b * a)`
satisfies `star (a ∘ b) = star b ∘ star a`, so `αˢʸᵐ` is again a ⋆-ring. A Jordan ⋆-homomorphism
of ℂ-algebras, a linear map preserving `⋆` and the Jordan product, is then a non-unital ⋆-algebra
homomorphism `αˢʸᵐ →⋆ₙₐ[ℂ] βˢʸᵐ`, and a Jordan ⋆-isomorphism is a `αˢʸᵐ ≃⋆ₐ[ℂ] βˢʸᵐ`.

## Main definitions

* `SymAlg.instStar` — the star operation `star (sym a) = sym (star a)` on `αˢʸᵐ`.
* `SymAlg.instStarRing` — `αˢʸᵐ` is a ⋆-ring when `α` is one and `2` is invertible in `α`.
* `SymAlg.instStarModule` — `αˢʸᵐ` is a ⋆-module when `α` is one.
-/

@[expose] public section

namespace SymAlg

variable {α : Type*}

/-- The star operation on the symmetrized algebra, `star (sym a) = sym (star a)`. -/
instance instStar [Star α] : Star αˢʸᵐ where
  star a := sym (star (unsym a))

/-- `sym` commutes with `star`. -/
@[simp]
lemma sym_star [Star α] (a : α) : sym (star a) = star (sym a) :=
  rfl

/-- `unsym` commutes with `star`. -/
@[simp]
lemma unsym_star [Star α] (a : αˢʸᵐ) : unsym (star a) = star (unsym a) :=
  rfl

/-- The star operation on `αˢʸᵐ` is involutive when that of `α` is. -/
instance instInvolutiveStar [InvolutiveStar α] : InvolutiveStar αˢʸᵐ where
  star_involutive a := unsym_injective <| star_star (unsym a)

/-- The star operation on `αˢʸᵐ` is additive when that of `α` is. -/
instance instStarAddMonoid [AddMonoid α] [StarAddMonoid α] : StarAddMonoid αˢʸᵐ where
  star_add a b := unsym_injective <| star_add (unsym a) (unsym b)

/-- The symmetrized algebra of a ⋆-ring in which `2` is invertible is a ⋆-ring: `⅟2` is
self-adjoint and central, so `star (⅟2 * (a * b + b * a)) = ⅟2 * (star b * star a + star a * star b)`.
-/
instance instStarRing [Semiring α] [StarRing α] [Invertible (2 : α)] : StarRing αˢʸᵐ where
  star_mul a b := unsym_injective <| by
    have h₂ : (2 : α) * star ⅟2 = 1 :=
      calc (2 : α) * star ⅟2 = star (⅟2 * 2) := by rw [star_mul, star_ofNat]
        _ = 1 := by rw [invOf_mul_self, star_one]
    rw [unsym_star, unsym_mul, unsym_mul, unsym_star, unsym_star, star_mul, star_add, star_mul,
      star_mul, ← invOf_eq_right_inv h₂]
    exact ((Commute.ofNat_left 2 _).invOf_left).eq.symm
  star_add a b := star_add a b

/-- `star (r • a) = star r • star a` on `αˢʸᵐ` when it holds on `α`. -/
instance instStarModule {R : Type*} [Star R] [Star α] [SMul R α] [StarModule R α] :
    StarModule R αˢʸᵐ where
  star_smul r a := unsym_injective <| star_smul r (unsym a)

end SymAlg
