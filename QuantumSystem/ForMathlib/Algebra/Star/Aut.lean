/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Operations
public import Mathlib.Algebra.Star.StarAlgHom

/-!
# The group of ⋆-automorphisms: congruence and the tautological action

The ⋆-versions of two pieces of the API of `A ≃ₐ[R] A`:

* a ⋆-isomorphism `ϕ : A ≃⋆ₐ[R] B` carries the ⋆-automorphisms of `A` to those of `B` by
  `ψ ↦ ϕ ∘ ψ ∘ ϕ⁻¹` (`StarAlgEquiv.autCongr`, as `AlgEquiv.autCongr`);
* the ⋆-automorphisms of `A` act on `A` (`StarAlgEquiv.applyMulAction`, and
  `StarAlgEquiv.applyMulSemiringAction` for a unital `A`, as `AlgEquiv.applyMulSemiringAction`),
  so that Mathlib's fixed points of an action (`MulAction.fixedPoints`, `FixedPoints.subalgebra`)
  apply to a group of ⋆-automorphisms.

## Main definitions

* `StarAlgEquiv.autCongr ϕ`: the group isomorphism `(A ≃⋆ₐ[R] A) ≃* (B ≃⋆ₐ[R] B)` induced by `ϕ`.
* `StarAlgEquiv.applyMulAction`, `StarAlgEquiv.applyMulSemiringAction`: the tautological action of
  `A ≃⋆ₐ[R] A` on `A`.
-/

@[expose] public section

namespace StarAlgEquiv

section AutCongr

variable {R A B : Type*} [Add A] [Mul A] [SMul R A] [Star A] [Add B] [Mul B] [SMul R B] [Star B]

/-- A ⋆-isomorphism `ϕ` induces a group isomorphism between the groups of ⋆-automorphisms,
`ψ ↦ ϕ ∘ ψ ∘ ϕ⁻¹`; `AlgEquiv.autCongr` for ⋆-isomorphisms. -/
def autCongr (ϕ : A ≃⋆ₐ[R] B) : (A ≃⋆ₐ[R] A) ≃* (B ≃⋆ₐ[R] B) where
  toFun ψ := ϕ.symm.trans (ψ.trans ϕ)
  invFun ψ := ϕ.trans (ψ.trans ϕ.symm)
  left_inv ψ := by
    ext
    simp
  right_inv ψ := by
    ext
    simp
  map_mul' ψ χ := by
    ext
    simp

/-- `autCongr ϕ ψ` acts as `ϕ ∘ ψ ∘ ϕ⁻¹`. -/
@[simp] lemma autCongr_apply_apply (ϕ : A ≃⋆ₐ[R] B) (ψ : A ≃⋆ₐ[R] A) (b : B) :
    autCongr ϕ ψ b = ϕ (ψ (ϕ.symm b)) :=
  rfl

/-- The inverse of `autCongr ϕ` is `autCongr ϕ.symm`. -/
@[simp] lemma autCongr_symm (ϕ : A ≃⋆ₐ[R] B) : (autCongr ϕ).symm = autCongr ϕ.symm :=
  rfl

end AutCongr

section Action

section MulAction

variable {R A : Type*} [Add A] [Mul A] [SMul R A] [Star A]

/-- The tautological action of the ⋆-automorphisms `A ≃⋆ₐ[R] A` on `A`, for a ⋆-algebra `A` that
need not be unital or associative. -/
instance applyMulAction : MulAction (A ≃⋆ₐ[R] A) A where
  smul := (· ·)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- The action of a ⋆-automorphism is its application. -/
@[simp] protected lemma smul_def (f : A ≃⋆ₐ[R] A) (a : A) : f • a = f a :=
  rfl

end MulAction

variable {R A : Type*} [Semiring A] [SMul R A] [Star A]

/-- The tautological action of the ⋆-automorphisms `A ≃⋆ₐ[R] A` on a unital `A`;
`AlgEquiv.applyMulSemiringAction` for ⋆-automorphisms. -/
instance applyMulSemiringAction : MulSemiringAction (A ≃⋆ₐ[R] A) A where
  __ := applyMulAction
  smul_zero := map_zero
  smul_add := map_add
  smul_one := map_one
  smul_mul := map_mul

/-- The action of the ⋆-automorphisms commutes with the scalars. -/
instance apply_smulCommClass : SMulCommClass (A ≃⋆ₐ[R] A) R A where
  smul_comm e r a := map_smul e r a

end Action

end StarAlgEquiv
