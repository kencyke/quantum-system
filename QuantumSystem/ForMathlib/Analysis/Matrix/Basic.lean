/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Block-matrix lemmas

This file collects lemmas on block matrices over `ℂ`: positive semidefiniteness of a
block-diagonal matrix, and the trace of a block matrix.

## Main results

- `Matrix.fromBlocks_diag_posSemidef`: `fromBlocks A 0 0 D` is PSD when `A` and `D` are PSD.
- `Matrix.trace_fromBlocks`: `Tr(fromBlocks A B C D) = Tr A + Tr D`.
-/

@[expose] public section

namespace Matrix

open scoped MatrixOrder ComplexOrder

/-! ### Positive semidefinite block matrices -/

/-- Block diagonal `fromBlocks A 0 0 D` is PSD when both `A` and `D` are PSD. -/
lemma fromBlocks_diag_posSemidef {n₁ n₂ : Type*}
    [Finite n₁] [Finite n₂]
    {A : Matrix n₁ n₁ ℂ} (hA : A.PosSemidef)
    {D : Matrix n₂ n₂ ℂ} (hD : D.PosSemidef) :
    (Matrix.fromBlocks A 0 0 D).PosSemidef := by
  let := Fintype.ofFinite n₁
  let := Fintype.ofFinite n₂
  refine PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.IsHermitian.fromBlocks hA.1 (by simp) hD.1) ?_
  intro v
  have heq : star v ⬝ᵥ (Matrix.fromBlocks A 0 0 D *ᵥ v) =
      star (fun i => v (Sum.inl i)) ⬝ᵥ (A *ᵥ fun i => v (Sum.inl i)) +
      star (fun i => v (Sum.inr i)) ⬝ᵥ (D *ᵥ fun i => v (Sum.inr i)) := by
    simp [dotProduct, Fintype.sum_sum_type, fromBlocks_mulVec, Function.comp_def]
  rw [heq]
  exact add_nonneg (hA.dotProduct_mulVec_nonneg _) (hD.dotProduct_mulVec_nonneg _)

/-- Trace of a `fromBlocks` matrix decomposes as sum of diagonal block traces. -/
lemma trace_fromBlocks {n₁ n₂ : Type*} [Fintype n₁] [Fintype n₂]
    (A : Matrix n₁ n₁ ℂ) (B : Matrix n₁ n₂ ℂ) (C : Matrix n₂ n₁ ℂ) (D : Matrix n₂ n₂ ℂ) :
    (Matrix.fromBlocks A B C D).trace = A.trace + D.trace := by
  unfold Matrix.trace
  rw [Fintype.sum_sum_type]
  simp

end Matrix
