/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# Coordinate inclusions into `WithLp p (α × β)`

The inclusions `x ↦ (x, 0)` and `y ↦ (0, y)` of the factors into the `L^p` product, bundled as
linear isometries. Mathlib records their norms (`WithLp.norm_toLp_fst`, `WithLp.norm_toLp_snd`)
but not the bundled maps.

## Main definitions

* `WithLp.inlₗᵢ p 𝕜 α β : α →ₗᵢ[𝕜] WithLp p (α × β)`, `x ↦ toLp p (x, 0)`.
* `WithLp.inrₗᵢ p 𝕜 α β : β →ₗᵢ[𝕜] WithLp p (α × β)`, `y ↦ toLp p (0, y)`.
-/

@[expose] public section

open scoped ENNReal

namespace WithLp

variable (p : ℝ≥0∞) [Fact (1 ≤ p)] (𝕜 α β : Type*) [Semiring 𝕜]
  [SeminormedAddCommGroup α] [Module 𝕜 α] [SeminormedAddCommGroup β] [Module 𝕜 β]

/-- The inclusion `x ↦ (x, 0)` of the first factor into `WithLp p (α × β)`, as a linear
isometry. -/
def inlₗᵢ : α →ₗᵢ[𝕜] WithLp p (α × β) where
  toFun x := toLp p (x, 0)
  map_add' x y := by rw [← toLp_add, Prod.mk_add_mk, add_zero]
  map_smul' c x := by rw [RingHom.id_apply, ← toLp_smul, Prod.smul_mk, smul_zero]
  norm_map' := norm_toLp_fst p α β

/-- The inclusion `y ↦ (0, y)` of the second factor into `WithLp p (α × β)`, as a linear
isometry. -/
def inrₗᵢ : β →ₗᵢ[𝕜] WithLp p (α × β) where
  toFun y := toLp p (0, y)
  map_add' x y := by rw [← toLp_add, Prod.mk_add_mk, add_zero]
  map_smul' c y := by rw [RingHom.id_apply, ← toLp_smul, Prod.smul_mk, smul_zero]
  norm_map' := norm_toLp_snd p α β

variable {p 𝕜 α β}

@[simp] lemma inlₗᵢ_apply (x : α) : inlₗᵢ p 𝕜 α β x = toLp p (x, 0) := rfl

@[simp] lemma inrₗᵢ_apply (y : β) : inrₗᵢ p 𝕜 α β y = toLp p (0, y) := rfl

end WithLp
