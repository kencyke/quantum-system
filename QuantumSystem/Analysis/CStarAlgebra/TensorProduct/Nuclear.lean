/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.CStarAlgebra.TensorProduct.CStarNorm
public import QuantumSystem.ForMathlib.Algebra.Star.TensorProductMap

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
* `CStarAlgebra.IsNuclear.of_starAlgEquiv` — nuclearity is invariant under `⋆`-isomorphism.
* `MinTensorProduct.norm_apply_le_norm_of_of_surjective` — when the algebraic tensor product is all
  of `A ⊗ₘᵢₙ B`, its norm dominates every C⋆-seminorm.

## Implementation notes

A class cannot quantify over all universes, so `CStarAlgebra.IsNuclear.{v, w} A` carries two universe
parameters: `B` ranges over `Type v` and the target of `Φ` over `Type w`. Write `[IsNuclear.{v, w} A]`
when `B : Type v` and the target lies in `Type w`. For `A : Type u`, the condition for one `v` at
`w = max u v`, the universe of `A ⊗ₘₐₓ B`, implies it for every `v` and every `w`
(`CStarAlgebra.IsNuclear.lift_universes`): finitely many elements of a test algebra lie in a closed
`⋆`-subalgebra small in `Type`. At a smaller `w` alone the condition is weaker. The instance for
finite-dimensional algebras holds at every `v` and `w`.

## Not formalized

* The stability of nuclearity under quotients.

## Related files

* `QuantumSystem/Analysis/CStarAlgebra/TensorProduct/Nuclear/Commutative.lean` — commutative
  C⋆-algebras are nuclear.
* `QuantumSystem/Analysis/CStarAlgebra/TensorProduct/Nuclear/InductiveLimit.lean` — nuclearity passes
  to inductive limits.
* `QuantumSystem/Analysis/CStarAlgebra/TensorProduct/Nuclear/TensorProduct.lean` — nuclearity passes
  to minimal tensor products of finitely many factors.
* `QuantumSystem/Analysis/CStarAlgebra/TensorProduct/Maximal.lean` — the maximal tensor product;
  nuclearity is the injectivity of its canonical map onto the minimal one.
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

/-- **Nuclearity is invariant under `⋆`-isomorphism**: a `⋆`-homomorphism `Φ` of `A' ⊗[ℂ] B` is read
on `A ⊗[ℂ] B` through `e ⊗ id`, and `e⁻¹ ⊗ id` is isometric for the minimal norms
(`MinTensorProduct.norm_map_of_injective`). -/
lemma of_starAlgEquiv {A' : Type*} [NonUnitalCStarAlgebra A'] [IsNuclear.{v, w} A]
    (e : A ≃⋆ₐ[ℂ] A') : IsNuclear.{v, w} A' := by
  refine ⟨fun B _ C _ Φ x => ?_⟩
  have key (y : A' ⊗[ℂ] B) : TensorProduct.map (e.toNonUnitalStarAlgHom : A →ₗ[ℂ] A')
      (NonUnitalStarAlgHom.id ℂ B : B →ₗ[ℂ] B) (TensorProduct.map
        (e.symm.toNonUnitalStarAlgHom : A' →ₗ[ℂ] A) (NonUnitalStarAlgHom.id ℂ B : B →ₗ[ℂ] B) y) =
        y := by
    induction y using TensorProduct.inductionOn with
    | tmul a b => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
  calc ‖Φ x‖ = ‖(Φ.comp (NonUnitalStarAlgebra.TensorProduct.map e.toNonUnitalStarAlgHom
        (NonUnitalStarAlgHom.id ℂ B))) (TensorProduct.map
          (e.symm.toNonUnitalStarAlgHom : A' →ₗ[ℂ] A) (NonUnitalStarAlgHom.id ℂ B : B →ₗ[ℂ] B) x)‖ := by
        rw [NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgebra.TensorProduct.map_apply, key]
    _ ≤ ‖MinTensorProduct.of A B (TensorProduct.map
          (e.symm.toNonUnitalStarAlgHom : A' →ₗ[ℂ] A) (NonUnitalStarAlgHom.id ℂ B : B →ₗ[ℂ] B) x)‖ :=
        norm_apply_le_norm_of B C _ _
    _ = ‖MinTensorProduct.of A' B x‖ := by
        rw [← MinTensorProduct.map_of e.symm.toNonUnitalStarAlgHom (NonUnitalStarAlgHom.id ℂ B) x,
          MinTensorProduct.norm_map_of_injective e.symm.injective Function.injective_id]

end IsNuclear

end CStarAlgebra
