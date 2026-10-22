/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.KPositiveMap
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.SchwarzMap

/-!
# `2`-positive maps as Schwarz maps

By the Kadison–Schwarz inequality of Choi (`KPositiveMapClass.le_smul_map_star_mul_of_norm_le`),
a `2`-positive contraction `φ` (`‖φ x‖ ≤ ‖x‖`) between possibly non-unital C⋆-algebras is a
Schwarz map. Between unital C⋆-algebras the condition reads `φ 1 ≤ 1`: the normalised
Kadison–Schwarz inequality `KPositiveMapClass.le_map_star_mul` holds under it directly. This file
packages both as Schwarz maps. Through the rigidity of Schwarz maps
(`SchwarzMapClass.starAlgEquivOfInverse`), a unital `2`-positive map with a `2`-positive inverse,
in particular a unital complete order isomorphism, is then a ⋆-isomorphism. The file lives
outside `ForMathlib/` because it needs both `KPositiveMap.lean` and `SchwarzMap.lean`, and a
`ForMathlib` file imports Mathlib only.

## Main definitions

* `KPositiveMapClass.toSchwarzMapOfNormLe` — a `2`-positive contraction between possibly
  non-unital C⋆-algebras as a Schwarz map.
* `KPositiveMapClass.toSchwarzMap` — a `2`-positive map with `φ 1 ≤ 1` between unital C⋆-algebras
  as a Schwarz map.
* `KPositiveMapClass.starAlgEquivOfInverse` — a unital `2`-positive map with a `2`-positive
  inverse, in particular a unital complete order isomorphism, as a ⋆-isomorphism.
-/

@[expose] public section

namespace KPositiveMapClass

section NonUnital

variable {F A₁ A₂ : Type*} [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂] [PartialOrder A₁]
  [PartialOrder A₂] [StarOrderedRing A₁] [StarOrderedRing A₂] [FunLike F A₁ A₂]
  [LinearMapClass F ℂ A₁ A₂] [KPositiveMapClass F 2 A₁ A₂]

/-- A `2`-positive contraction (`‖φ x‖ ≤ ‖x‖`) between possibly non-unital C⋆-algebras as a
Schwarz map: `φ(a)⋆ φ(a) ≤ φ(a⋆ a)` is the Kadison–Schwarz inequality
`KPositiveMapClass.le_smul_map_star_mul_of_norm_le` with constant `1`. -/
noncomputable def toSchwarzMapOfNormLe (φ : F) (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖) : SchwarzMap A₁ A₂ where
  toLinearMap := (φ : A₁ →ₗ[ℂ] A₂)
  le_map_star_mul' a := by
    simpa using le_smul_map_star_mul_of_norm_le φ (C := 1) (by simpa using hφ) a

/-- `toSchwarzMapOfNormLe φ hφ` evaluates as `φ`. -/
@[simp] lemma toSchwarzMapOfNormLe_apply (φ : F) (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖) (a : A₁) :
    toSchwarzMapOfNormLe φ hφ a = φ a := rfl

end NonUnital

section Unital

variable {F A₁ A₂ : Type*} [CStarAlgebra A₁] [CStarAlgebra A₂] [PartialOrder A₁] [PartialOrder A₂]
  [StarOrderedRing A₁] [StarOrderedRing A₂] [FunLike F A₁ A₂] [LinearMapClass F ℂ A₁ A₂]
  [KPositiveMapClass F 2 A₁ A₂]

/-- A `2`-positive map with `φ 1 ≤ 1` between unital C⋆-algebras as a Schwarz map:
`φ(a)⋆ φ(a) ≤ φ(a⋆ a)` is the normalised Kadison–Schwarz inequality
`KPositiveMapClass.le_map_star_mul`. -/
noncomputable def toSchwarzMap (φ : F) (hφ : φ 1 ≤ 1) : SchwarzMap A₁ A₂ where
  toLinearMap := (φ : A₁ →ₗ[ℂ] A₂)
  le_map_star_mul' := le_map_star_mul φ hφ

/-- `toSchwarzMap φ hφ` evaluates as `φ`. -/
@[simp] lemma toSchwarzMap_apply (φ : F) (hφ : φ 1 ≤ 1) (a : A₁) :
    toSchwarzMap φ hφ a = φ a := rfl

variable {G : Type*} [FunLike G A₂ A₁] [KPositiveMapClass G 2 A₂ A₁]

/-- **Unital complete order isomorphisms are ⋆-isomorphisms.** A unital `2`-positive map `φ`
between unital C⋆-algebras with a `2`-positive inverse `ψ` is a ⋆-isomorphism; in particular so
is a unital completely positive map with a completely positive inverse. The inverse `ψ` is linear
as the inverse of `φ` and unital as `ψ 1 = ψ (φ 1) = 1`, so both maps are Schwarz maps by the
normalised Kadison–Schwarz inequality, and `φ` is multiplicative by
`SchwarzMapClass.map_mul_of_inverse`. Here `h₁` and `h₂` say `ψ ∘ φ = id` and `φ ∘ ψ = id`. -/
@[simps apply symm_apply]
noncomputable def starAlgEquivOfInverse (φ : F) (ψ : G) (hφ : φ 1 = 1)
    (h₁ : Function.LeftInverse ψ φ) (h₂ : Function.RightInverse ψ φ) : A₁ ≃⋆ₐ[ℂ] A₂ where
  toFun := φ
  invFun := ψ
  left_inv := h₁
  right_inv := h₂
  map_mul' := SchwarzMapClass.map_mul_of_inverse (toSchwarzMap φ hφ.le)
    (⟨(⟨(φ : A₁ →ₗ[ℂ] A₂), ψ, h₁, h₂⟩ : A₁ ≃ₗ[ℂ] A₂).symm.toLinearMap,
      le_map_star_mul ψ (by rw [← hφ, h₁ 1])⟩ : SchwarzMap A₂ A₁) h₁ h₂
  map_add' := map_add φ
  map_star' := map_star φ
  map_smul' := map_smul φ

end Unital

end KPositiveMapClass
