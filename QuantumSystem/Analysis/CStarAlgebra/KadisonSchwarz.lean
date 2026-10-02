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
Schwarz map. Between unital C⋆-algebras the condition reads `φ 1 ≤ 1`, since a `2`-positive map
attains its norm at the unit (`KPositiveMapClass.opNorm_eq_norm_map_one`), so that `φ 1 ≤ 1` makes
it a contraction (`KPositiveMapClass.norm_apply_le_of_map_one_le`). This file packages
both as Schwarz maps. It lives outside `ForMathlib/` because it needs both `KPositiveMap.lean` and
`SchwarzMap.lean`.

## Main definitions

* `KPositiveMapClass.toSchwarzMapOfNormLe` — a `2`-positive contraction between possibly
  non-unital C⋆-algebras as a Schwarz map.
* `KPositiveMapClass.toSchwarzMap` — a `2`-positive map with `φ 1 ≤ 1` between unital C⋆-algebras
  as a Schwarz map.
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

/-- A `2`-positive map with `φ 1 ≤ 1` between unital C⋆-algebras as a Schwarz map: it is a
contraction (`KPositiveMapClass.norm_apply_le_of_map_one_le`), so
`KPositiveMapClass.toSchwarzMapOfNormLe` applies. -/
noncomputable def toSchwarzMap (φ : F) (hφ : φ 1 ≤ 1) : SchwarzMap A₁ A₂ :=
  toSchwarzMapOfNormLe φ (norm_apply_le_of_map_one_le φ hφ)

/-- `toSchwarzMap φ hφ` evaluates as `φ`. -/
@[simp] lemma toSchwarzMap_apply (φ : F) (hφ : φ 1 ≤ 1) (a : A₁) :
    toSchwarzMap φ hφ a = φ a := rfl

end Unital

end KPositiveMapClass
