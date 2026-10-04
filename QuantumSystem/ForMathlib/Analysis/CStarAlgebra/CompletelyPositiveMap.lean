/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import Mathlib.CategoryTheory.Category.Basic

/-!
# Identity and composition of completely positive maps

Mathlib's `CompletelyPositiveMap` (`A₁ →CP A₂`) comes with its `FunLike`, `LinearMapClass` and
`CompletelyPositiveMapClass` instances. This file adds the category structure: the identity map
is completely positive (`CompletelyPositiveMap.id`), and completely positive maps compose
(`CompletelyPositiveMap.comp`), since applying `ψ ∘ φ` entrywise to a block matrix is applying `φ`
and then `ψ`. Composition is associative and unital, so the C⋆-algebras with completely positive
maps form a category (`CStarAlgCP`). Completely positive maps transport along ⋆-isomorphisms of
their domains and codomains (`CompletelyPositiveMap.arrowCongr`).

## Main definitions

* `CompletelyPositiveMap.id` — the identity map as a completely positive map.
* `CompletelyPositiveMap.comp` — the composition of completely positive maps.
* `CompletelyPositiveMap.arrowCongr` — the transport `φ ↦ e₂ ∘ φ ∘ e₁⁻¹` along ⋆-isomorphisms
  `e₁`, `e₂`.
* `CStarAlgCP` — the category of (possibly non-unital) C⋆-algebras, with the star order, and
  completely positive maps.
-/

@[expose] public section

open scoped CStarAlgebra

namespace CompletelyPositiveMap

variable {A₁ A₂ A₃ : Type*} [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂]
  [NonUnitalCStarAlgebra A₃] [PartialOrder A₁] [PartialOrder A₂] [PartialOrder A₃]
  [StarOrderedRing A₁] [StarOrderedRing A₂] [StarOrderedRing A₃]

/-- The underlying linear map of `φ` is `φ` as a function. -/
@[simp] lemma coe_toLinearMap (φ : A₁ →CP A₂) : ⇑φ.toLinearMap = φ := rfl

/-- Completely positive maps are equal if they agree at every point. -/
@[ext] lemma ext {φ ψ : A₁ →CP A₂} (h : ∀ a, φ a = ψ a) : φ = ψ := DFunLike.ext _ _ h

/-- A completely positive map is determined by its underlying linear map
`(φ : A₁ →ₗ[ℂ] A₂)`. -/
lemma coe_injective : Function.Injective ((↑) : (A₁ →CP A₂) → A₁ →ₗ[ℂ] A₂) :=
  fun _ _ h => ext fun a => LinearMap.congr_fun h a

variable (A₁) in
/-- The identity map is completely positive. -/
protected def id : A₁ →CP A₁ where
  toLinearMap := LinearMap.id
  map_cstarMatrix_nonneg' _ _ hM := by simpa using hM

/-- The identity completely positive map is the identity function. -/
@[simp] lemma coe_id : ⇑(CompletelyPositiveMap.id A₁) = id := rfl

/-- The identity completely positive map sends `a` to `a`. -/
lemma id_apply (a : A₁) : CompletelyPositiveMap.id A₁ a = a := rfl

/-- The composition `ψ ∘ φ` of completely positive maps is completely positive: applying it
entrywise to a block matrix is applying `φ` and then `ψ`. -/
def comp (ψ : A₂ →CP A₃) (φ : A₁ →CP A₂) : A₁ →CP A₃ where
  toLinearMap := ψ.toLinearMap ∘ₗ φ.toLinearMap
  map_cstarMatrix_nonneg' k M hM :=
    ψ.map_cstarMatrix_nonneg' k _ (φ.map_cstarMatrix_nonneg' k M hM)

/-- The composition `ψ.comp φ` is `ψ ∘ φ` as a function. -/
@[simp] lemma coe_comp (ψ : A₂ →CP A₃) (φ : A₁ →CP A₂) : ⇑(ψ.comp φ) = ψ ∘ φ := rfl

/-- The composition `ψ.comp φ` sends `a` to `ψ (φ a)`. -/
lemma comp_apply (ψ : A₂ →CP A₃) (φ : A₁ →CP A₂) (a : A₁) : ψ.comp φ a = ψ (φ a) := rfl

/-- Composing with the identity on the right does nothing. -/
@[simp] lemma comp_id (φ : A₁ →CP A₂) : φ.comp (CompletelyPositiveMap.id A₁) = φ := rfl

/-- Composing with the identity on the left does nothing. -/
@[simp] lemma id_comp (φ : A₁ →CP A₂) : (CompletelyPositiveMap.id A₂).comp φ = φ := rfl

/-- Composition of completely positive maps is associative. -/
lemma comp_assoc {A₄ : Type*} [NonUnitalCStarAlgebra A₄] [PartialOrder A₄] [StarOrderedRing A₄]
    (χ : A₃ →CP A₄) (ψ : A₂ →CP A₃) (φ : A₁ →CP A₂) :
    (χ.comp ψ).comp φ = χ.comp (ψ.comp φ) := rfl

section ArrowCongr

variable {B₁ B₂ : Type*} [NonUnitalCStarAlgebra B₁] [NonUnitalCStarAlgebra B₂] [PartialOrder B₁]
  [PartialOrder B₂] [StarOrderedRing B₁] [StarOrderedRing B₂]

/-- Completely positive maps transport along ⋆-isomorphisms `e₁ : A₁ ≃ B₁` of the domains and
`e₂ : A₂ ≃ B₂` of the codomains, `φ ↦ e₂ ∘ φ ∘ e₁⁻¹`: ⋆-homomorphisms are completely positive
(`NonUnitalStarAlgHomClass.instCompletelyPositiveMapClass`), and so are composites. -/
def arrowCongr (e₁ : A₁ ≃⋆ₐ[ℂ] B₁) (e₂ : A₂ ≃⋆ₐ[ℂ] B₂) : (A₁ →CP A₂) ≃ (B₁ →CP B₂) where
  toFun φ := ((e₂ : A₂ →CP B₂).comp φ).comp e₁.symm
  invFun ψ := ((e₂.symm : B₂ →CP A₂).comp ψ).comp e₁
  left_inv φ := ext fun a => by
    change e₂.symm (e₂ (φ (e₁.symm (e₁ a)))) = φ a
    simp
  right_inv ψ := ext fun b => by
    change e₂ (e₂.symm (ψ (e₁ (e₁.symm b)))) = ψ b
    simp

/-- The transported map `arrowCongr e₁ e₂ φ` sends `b` to `e₂ (φ (e₁⁻¹ b))`. -/
@[simp] lemma arrowCongr_apply (e₁ : A₁ ≃⋆ₐ[ℂ] B₁) (e₂ : A₂ ≃⋆ₐ[ℂ] B₂) (φ : A₁ →CP A₂) (b : B₁) :
    arrowCongr e₁ e₂ φ b = e₂ (φ (e₁.symm b)) :=
  rfl

/-- The inverse transport `(arrowCongr e₁ e₂).symm ψ` sends `a` to `e₂⁻¹ (ψ (e₁ a))`. -/
@[simp] lemma arrowCongr_symm_apply (e₁ : A₁ ≃⋆ₐ[ℂ] B₁) (e₂ : A₂ ≃⋆ₐ[ℂ] B₂) (ψ : B₁ →CP B₂)
    (a : A₁) : (arrowCongr e₁ e₂).symm ψ a = e₂.symm (ψ (e₁ a)) :=
  rfl

end ArrowCongr

end CompletelyPositiveMap

universe u

/-- The category of (possibly non-unital) C⋆-algebras with their star order and completely
positive maps as morphisms. -/
structure CStarAlgCP : Type (u + 1) where
  /-- The underlying C⋆-algebra. -/
  carrier : Type u
  [instNonUnitalCStarAlgebra : NonUnitalCStarAlgebra carrier]
  [instPartialOrder : PartialOrder carrier]
  [instStarOrderedRing : StarOrderedRing carrier]

namespace CStarAlgCP

attribute [instance] instNonUnitalCStarAlgebra instPartialOrder instStarOrderedRing

instance : CoeSort CStarAlgCP (Type u) := ⟨carrier⟩

/-- The C⋆-algebras with completely positive maps form a category: identities and composites of
completely positive maps are completely positive (`CompletelyPositiveMap.id`,
`CompletelyPositiveMap.comp`), and the category laws hold definitionally. -/
instance : CategoryTheory.Category CStarAlgCP.{u} where
  Hom A B := A →CP B
  id A := CompletelyPositiveMap.id A
  comp φ ψ := ψ.comp φ

/-- A morphism of `CStarAlgCP` is a completely positive map. -/
lemma hom_def (A B : CStarAlgCP.{u}) : (A ⟶ B) = (A →CP B) := rfl

end CStarAlgCP
