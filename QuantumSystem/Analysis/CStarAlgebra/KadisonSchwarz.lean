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

By the Kadison–Schwarz inequality of Choi (`KPositiveMapClass.le_map_star_mul`), a `2`-positive
map `φ` with `φ 1 ≤ 1` between unital C⋆-algebras is a Schwarz map. This file packages it as one.
It lives outside `ForMathlib/` because it needs both `KPositiveMap.lean` and `SchwarzMap.lean`.

## Main definitions

* `KPositiveMapClass.toSchwarzMap` — a `2`-positive map with `φ 1 ≤ 1` as a Schwarz map.
-/

@[expose] public section

namespace KPositiveMapClass

variable {F A₁ A₂ : Type*} [CStarAlgebra A₁] [CStarAlgebra A₂] [PartialOrder A₁] [PartialOrder A₂]
  [StarOrderedRing A₁] [StarOrderedRing A₂] [FunLike F A₁ A₂] [LinearMapClass F ℂ A₁ A₂]
  [KPositiveMapClass F 2 A₁ A₂]

/-- A `2`-positive map with `φ 1 ≤ 1` as a Schwarz map. -/
noncomputable def toSchwarzMap (φ : F) (hφ : φ 1 ≤ 1) : SchwarzMap A₁ A₂ where
  toLinearMap := (φ : A₁ →ₗ[ℂ] A₂)
  le_map_star_mul' := le_map_star_mul φ hφ

/-- `toSchwarzMap φ hφ` evaluates as `φ`. -/
@[simp] lemma toSchwarzMap_apply (φ : F) (hφ : φ 1 ≤ 1) (a : A₁) :
    toSchwarzMap φ hφ a = φ a := rfl

end KPositiveMapClass
