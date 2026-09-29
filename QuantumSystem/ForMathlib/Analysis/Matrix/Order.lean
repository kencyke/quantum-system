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
- `trace_mono`: A ≤ B ⇒ Re(tr A) ≤ Re(tr B).
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

/-- Trace is monotone with respect to the Löwner order:
A ≤ B ⇒ Re(tr A) ≤ Re(tr B). -/
lemma trace_mono {m : Type*} [Fintype m]
    {A B : Matrix m m ℂ} (hle : A ≤ B) : A.trace.re ≤ B.trace.re := by
  have hpsd : (B - A).PosSemidef := Matrix.le_iff.mp hle
  have h_trace_nonneg : 0 ≤ (B - A).trace := hpsd.trace_nonneg
  have h : B.trace - A.trace = (B - A).trace := (trace_sub B A).symm
  have h' : (B.trace - A.trace).re = B.trace.re - A.trace.re :=
    Complex.sub_re B.trace A.trace
  have h_re_nonneg : 0 ≤ (B - A).trace.re := by
    have := Complex.nonneg_iff.mp h_trace_nonneg
    exact this.1
  have h_eq : (B - A).trace.re = B.trace.re - A.trace.re := by
    rw [← h, h']
  linarith [h_eq ▸ h_re_nonneg]

end Matrix
