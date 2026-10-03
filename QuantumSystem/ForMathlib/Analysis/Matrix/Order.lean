/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.Matrix.Order

/-!
# Löwner Order on Matrices

This file proves basic properties of Mathlib's Löwner order on complex matrices
(`MatrixOrder`: `A ≤ B` iff `B - A` is positive semidefinite).

## Main results

- `compression_le`: M ≤ N ⇒ V†MV ≤ V†NV.
-/
@[expose] public section

namespace Matrix

open scoped MatrixOrder ComplexOrder

/-- Compression preserves the Löwner order: M ≤ N ⇒ V†MV ≤ V†NV. -/
lemma compression_le {n m : Type*} [Fintype n] [Finite m]
    {M N : Matrix n n ℂ} (h : M ≤ N) (V : Matrix n m ℂ) :
    Vᴴ * M * V ≤ Vᴴ * N * V := by
  rw [Matrix.le_iff] at h ⊢
  have hdiff : Vᴴ * N * V - Vᴴ * M * V = Vᴴ * (N - M) * V := by
    simp [Matrix.mul_sub, Matrix.sub_mul]
  rw [hdiff]
  exact h.conjTranspose_mul_mul_same V

end Matrix
