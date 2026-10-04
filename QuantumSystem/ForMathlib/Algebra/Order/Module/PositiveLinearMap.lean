/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Data.FunLike.Module

/-!
# Nonnegative scalar multiples of positive linear maps

A nonnegative multiple `c • f` of a positive linear map `f : E₁ →ₚ[R] E₂` is again positive, so the
positive linear maps form a module over `ℝ≥0` (they are a cone, not a vector space). This lets one
write conic combinations `Σᵢ wᵢ • fᵢ` of positive maps, e.g. weighted sums of positive functionals.

Only `ℝ≥0` acts: a general action of a canonically ordered semiring would clash with Mathlib's
`SMul ℕ (E₁ →ₚ[R] E₂)` instance for `ℕ`.

Also `PositiveLinearMap.coe_ofClass`: the positive linear map `PositiveLinearMap.ofClass f` of an
element `f` of a positive-linear-map class has the same underlying function as `f`.

## Main definitions

* `PositiveLinearMap.instModuleNNReal` — `E₁ →ₚ[R] E₂` is an `ℝ≥0`-module, with
  `(c • f) x = c • f x` (`IsSMulApply`, so `smul_apply` and `FunLike.sum_apply` evaluate it).
-/

@[expose] public section

open scoped NNReal

namespace PositiveLinearMap

/-- `PositiveLinearMap.ofClass f` has the same underlying function as `f`. -/
@[simp]
lemma coe_ofClass {F R E₁ E₂ : Type*} [Semiring R]
    [AddCommMonoid E₁] [PartialOrder E₁] [AddCommMonoid E₂] [PartialOrder E₂]
    [Module R E₁] [Module R E₂] [FunLike F E₁ E₂] [LinearMapClass F R E₁ E₂]
    [OrderHomClass F E₁ E₂] (f : F) : ⇑(ofClass f : E₁ →ₚ[R] E₂) = f :=
  rfl

variable {R E₁ E₂ : Type*} [Semiring R]
  [AddCommMonoid E₁] [PartialOrder E₁] [AddCommMonoid E₂] [PartialOrder E₂]
  [Module R E₁] [Module R E₂] [Module ℝ≥0 E₂] [SMulCommClass R ℝ≥0 E₂] [PosSMulMono ℝ≥0 E₂]

/-- A nonnegative multiple of a positive linear map is positive. -/
instance : SMul ℝ≥0 (E₁ →ₚ[R] E₂) where
  smul c f := .mk (c • f.toLinearMap) fun _ _ h ↦ smul_le_smul_of_nonneg_left (f.monotone' h) c.2

/-- `(c • f) x = c • f x`. -/
instance : IsSMulApply ℝ≥0 (E₁ →ₚ[R] E₂) E₁ E₂ where
  smul_apply _ _ _ := rfl

@[simp]
lemma toLinearMap_smul (c : ℝ≥0) (f : E₁ →ₚ[R] E₂) : (c • f).toLinearMap = c • f.toLinearMap :=
  rfl

/-- The positive linear maps form a module over `ℝ≥0`. -/
instance instModuleNNReal [IsOrderedAddMonoid E₂] : Module ℝ≥0 (E₁ →ₚ[R] E₂) := fast_instance% FunLike.module

end PositiveLinearMap
