module

public import Mathlib.Analysis.Matrix.Order

/-!
# Löwner Order on Matrices

This file defines the Löwner (positive semidefinite) order on Hermitian matrices over `ℂ`
and proves its basic properties.

## Main results

- `loewnerLE` (`A ≤ₗ B`): `B - A` is positive semidefinite.
- `loewnerLE_refl`: the Löwner order is reflexive.
- `loewnerLE_trans`: the Löwner order is transitive.
- `compression_le`: M ≤ N ⇒ V†MV ≤ V†NV.
- `trace_mono`: A ≤ B ⇒ Re(tr A) ≤ Re(tr B).
-/
@[expose] public section

namespace Matrix

open scoped MatrixOrder ComplexOrder

/-- Löwner order on Hermitian matrices: A ≤_L B iff B - A is positive semidefinite. -/
def loewnerLE {m : Type*} [Fintype m] [DecidableEq m]
    (A B : Matrix m m ℂ) : Prop :=
  (B - A).PosSemidef

notation:50 A " ≤ₗ " B => loewnerLE A B

/-- Löwner order is reflexive. -/
lemma loewnerLE_refl {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℂ) : A ≤ₗ A := by
  unfold loewnerLE
  simp only [sub_self]
  exact PosSemidef.zero

/-- Löwner order is transitive. -/
lemma loewnerLE_trans {m : Type*} [Fintype m] [DecidableEq m]
    {A B C : Matrix m m ℂ} (hab : A ≤ₗ B) (hbc : B ≤ₗ C) : A ≤ₗ C := by
  unfold loewnerLE at *
  have h : C - A = (C - B) + (B - A) := by abel
  rw [h]
  exact hbc.add hab

/-- Compression preserves the Löwner order: M ≤ N ⇒ V†MV ≤ V†NV. -/
lemma compression_le {n m : Type*} [Fintype n] [Fintype m]
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
