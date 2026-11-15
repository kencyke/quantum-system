/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.CStarAlgebra.TensorProduct.CStarNorm

/-!
# Nuclear C⋆-algebras

A C⋆-algebra `A` is nuclear if, for every C⋆-algebra `B`, the norm of the minimal tensor product
`A ⊗ₘᵢₙ B` is the greatest C⋆-seminorm on the algebraic tensor product `A ⊗[ℂ] B`: every
`⋆`-homomorphism `Φ` of `A ⊗[ℂ] B` into a C⋆-algebra satisfies `‖Φ x‖ ≤ ‖x‖` in `A ⊗ₘᵢₙ B`. The
minimal norm being the least C⋆-norm (`MinTensorProduct.norm_of_le_norm_apply`), `A ⊗[ℂ] B` then has
exactly one C⋆-norm, and one completion for it.

The algebras are not assumed unital. A C⋆-seminorm on `A ⊗[ℂ] B` is given as `x ↦ ‖Φ x‖` for a
`⋆`-homomorphism `Φ` into a C⋆-algebra, as in
`QuantumSystem/Analysis/CStarAlgebra/TensorProduct/CStarNorm.lean`.

## Main definitions

* `CStarAlgebra.IsNuclear A` — `A` is nuclear.
* `CStarAlgebra.IsNuclear.closureRangeEquiv hΦ` — for a nuclear `A` and an injective `Φ`, the
  `⋆`-isomorphism of the completion `Φ.closureRange` of `A ⊗[ℂ] B` onto `A ⊗ₘᵢₙ B`.

## Main results

* `CStarAlgebra.IsNuclear.norm_apply_eq_norm_of` — for a nuclear `A`, every C⋆-norm on `A ⊗[ℂ] B` is
  the norm of `A ⊗ₘᵢₙ B`.
* `CStarAlgebra.IsNuclear.of_finiteDimensional` — finite-dimensional C⋆-algebras are nuclear.
* `MinTensorProduct.norm_apply_le_norm_of_of_surjective` — when the algebraic tensor product is all
  of `A ⊗ₘᵢₙ B`, its norm dominates every C⋆-seminorm.

## Implementation notes

A class cannot quantify over all universes, so `CStarAlgebra.IsNuclear.{v, w} A` carries two universe
parameters: `B` ranges over `Type v` and the target of `Φ` over `Type w`. Write `[IsNuclear.{v, w} A]`
when `B : Type v` and the target lies in `Type w`. The instance for finite-dimensional algebras holds
at every `v` and `w`.

## Not formalized

* The nuclearity of commutative C⋆-algebras, and its stability under tensor products, quotients and
  inductive limits.
* The maximal tensor product, for which nuclearity is the bijectivity of the canonical map onto the
  minimal one.
-/

@[expose] public section

open scoped TensorProduct MinTensorProduct

universe u v w

namespace MinTensorProduct

variable {A : Type u} {B : Type v} {C : Type w} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C]

/-- When the algebraic tensor product is all of `A ⊗ₘᵢₙ B`, the norm of `A ⊗ₘᵢₙ B` dominates every
C⋆-seminorm on `A ⊗[ℂ] B`: a `⋆`-homomorphism `Φ` of `A ⊗[ℂ] B` into a C⋆-algebra is then a
`⋆`-homomorphism of the C⋆-algebra `A ⊗ₘᵢₙ B`, hence contractive. -/
lemma norm_apply_le_norm_of_of_surjective (h : Function.Surjective (of A B))
    (Φ : A ⊗[ℂ] B →⋆ₙₐ[ℂ] C) (x : A ⊗[ℂ] B) : ‖Φ x‖ ≤ ‖of A B x‖ := by
  have hx : Φ.comp (ofEquiv h).symm.toNonUnitalStarAlgHom (of A B x) = Φ x :=
    congrArg Φ ((ofEquiv h).symm_apply_apply x)
  rw [← hx]
  exact NonUnitalStarAlgHom.norm_apply_le _ _

end MinTensorProduct

namespace CStarAlgebra

/-- A C⋆-algebra `A` is **nuclear** if for every C⋆-algebra `B` the norm of the minimal tensor
product `A ⊗ₘᵢₙ B` dominates every C⋆-seminorm on the algebraic tensor product `A ⊗[ℂ] B`:
`‖Φ x‖ ≤ ‖x‖` for every `⋆`-homomorphism `Φ` of `A ⊗[ℂ] B` into a C⋆-algebra. Then `A ⊗[ℂ] B` has
exactly one C⋆-norm (`CStarAlgebra.IsNuclear.norm_apply_eq_norm_of`). -/
class IsNuclear.{v', w', u'} (A : Type u') [NonUnitalCStarAlgebra A] : Prop where
  /-- The norm of `A ⊗ₘᵢₙ B` dominates every C⋆-seminorm on `A ⊗[ℂ] B`. -/
  norm_apply_le_norm_of : ∀ (B : Type v') [NonUnitalCStarAlgebra B] (C : Type w')
    [NonUnitalCStarAlgebra C] (Φ : A ⊗[ℂ] B →⋆ₙₐ[ℂ] C) (x : A ⊗[ℂ] B),
    ‖Φ x‖ ≤ ‖MinTensorProduct.of A B x‖

namespace IsNuclear

variable {A : Type u} {B : Type v} {C : Type w} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C]

/-- **A nuclear C⋆-algebra has exactly one C⋆-norm on its algebraic tensor product with any
C⋆-algebra**: for an injective `⋆`-homomorphism `Φ` of `A ⊗[ℂ] B` into a C⋆-algebra, `‖Φ x‖` is the
norm of `x` in `A ⊗ₘᵢₙ B`. -/
theorem norm_apply_eq_norm_of [IsNuclear.{v, w} A] {Φ : A ⊗[ℂ] B →⋆ₙₐ[ℂ] C} (hΦ : Function.Injective Φ)
    (x : A ⊗[ℂ] B) : ‖Φ x‖ = ‖MinTensorProduct.of A B x‖ :=
  le_antisymm (norm_apply_le_norm_of B C Φ x) (MinTensorProduct.norm_of_le_norm_apply hΦ x)

/-- For a nuclear `A` and an injective `⋆`-homomorphism `Φ` of `A ⊗[ℂ] B` into a C⋆-algebra, the
completion `Φ.closureRange` of `A ⊗[ℂ] B` for the C⋆-norm `x ↦ ‖Φ x‖` is `⋆`-isomorphic to the
minimal tensor product, by the isomorphism that sends `Φ x` to `x`. -/
noncomputable def closureRangeEquiv [IsNuclear.{v, w} A] {Φ : A ⊗[ℂ] B →⋆ₙₐ[ℂ] C}
    (hΦ : Function.Injective Φ) : Φ.closureRange ≃⋆ₐ[ℂ] A ⊗ₘᵢₙ B :=
  NonUnitalStarAlgHom.closureRangeEquiv (φ := Φ)
    (ψ := π₀[A, B]) fun x => norm_apply_eq_norm_of hΦ x

/-- `CStarAlgebra.IsNuclear.closureRangeEquiv` sends `Φ x` to `x`. -/
@[simp] lemma closureRangeEquiv_closureRangeRestrict [IsNuclear.{v, w} A] {Φ : A ⊗[ℂ] B →⋆ₙₐ[ℂ] C}
    (hΦ : Function.Injective Φ) (x : A ⊗[ℂ] B) :
    closureRangeEquiv hΦ (Φ.closureRangeRestrict x) = MinTensorProduct.of A B x :=
  NonUnitalStarAlgHom.closureRangeEquiv_closureRangeRestrict _ x

/-- **Finite-dimensional C⋆-algebras are nuclear**: the algebraic tensor product with any
C⋆-algebra is already the minimal tensor product
(`MinTensorProduct.of_surjective_of_finiteDimensional_left`). -/
instance of_finiteDimensional [FiniteDimensional ℂ A] : IsNuclear.{v, w} A :=
  ⟨fun _ _ _ _ Φ x => MinTensorProduct.norm_apply_le_norm_of_of_surjective
    MinTensorProduct.of_surjective_of_finiteDimensional_left Φ x⟩

end IsNuclear

end CStarAlgebra
