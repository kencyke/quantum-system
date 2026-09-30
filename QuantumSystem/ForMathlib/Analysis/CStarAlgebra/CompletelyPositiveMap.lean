/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap

/-!
# Identity and composition of completely positive maps

Mathlib's `CompletelyPositiveMap` (`A₁ →CP A₂`) comes with its `FunLike`, `LinearMapClass` and
`CompletelyPositiveMapClass` instances. This file adds the category structure: the identity map
is completely positive (`CompletelyPositiveMap.id`), and completely positive maps compose
(`CompletelyPositiveMap.comp`), since applying `ψ ∘ φ` entrywise to a block matrix is applying `φ`
and then `ψ`.

## Main definitions

* `CompletelyPositiveMap.id` — the identity map as a completely positive map.
* `CompletelyPositiveMap.comp` — the composition of completely positive maps.
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

/-- A completely positive map is determined by its underlying linear map. -/
lemma toLinearMap_injective :
    Function.Injective (toLinearMap : (A₁ →CP A₂) → A₁ →ₗ[ℂ] A₂) :=
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

end CompletelyPositiveMap
