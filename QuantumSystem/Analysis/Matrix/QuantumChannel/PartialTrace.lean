/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.Matrix.QuantumChannel.Choi
public import QuantumSystem.ForMathlib.LinearAlgebra.Matrix.PartialTrace
public import QuantumSystem.ForMathlib.LinearAlgebra.Matrix.Trace

/-!
# Partial trace and reindexing as quantum channels

Tracing out either factor of a matrix on `X × Y` is completely positive and trace preserving, and
so is conjugation by an index equivalence. Composing the two gives the trace-out-`C` channel
`Matrix.QuantumChannel.traceOutC` on `A × B × C`, which realises the `lean-eval` marginal map.

## Main definitions

* `Matrix.QuantumChannel.partialTraceRight`, `Matrix.QuantumChannel.partialTraceLeft`: bundled
  quantum channels tracing out `Y` and `X`, acting as `Matrix.traceRight` and `Matrix.traceLeft`.
* `Matrix.QuantumChannel.reindex`: conjugation by an index equivalence, as a channel, acting as
  `Matrix.reindex e e`.
* `Matrix.QuantumChannel.traceOutC`: trace out the `C` factor of `A × B × C`.

## Main statements

* `Matrix.traceRight_eq_sum_kraus`, `Matrix.traceLeft_eq_sum_kraus`,
  `Matrix.reindex_eq_kraus`: Kraus representations of the partial traces and of reindexing, which
  make them completely positive (`CompletelyPositiveMap.ofKraus`).

## References

* Nielsen, Chuang, *Quantum Computation and Quantum Information*, §2.4.3
-/

@[expose] public section

namespace Matrix

/-! ### Kraus representations -/

/-- Kraus operator for the right partial trace, indexed by `y : Y`: `K_y x p = [p = (x, y)]`. -/
def traceRightKraus {X Y : Type*} [DecidableEq X] [DecidableEq Y] (y : Y) :
    Matrix X (X × Y) ℂ :=
  Matrix.of fun x p => if p = (x, y) then (1 : ℂ) else 0

/-- Tracing out `Y` is the Kraus map with operators `K_y`, `y : Y`:
`tr₂(M) = Σ_y K_y M K_yᴴ`. -/
-- The binder `y : Y` is annotated: with the type left to inference, Mathlib's `@[default_instance]`
-- rectangular product on `CStarMatrix` (`CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid`) is
-- selected for the products and elaboration fails.
lemma traceRight_eq_sum_kraus {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] (M : Matrix (X × Y) (X × Y) ℂ) :
    traceRight M = ∑ y : Y, traceRightKraus (X := X) y * M * (traceRightKraus (X := X) y)ᴴ := by
  ext i j
  rw [traceRight_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  symm
  rw [Matrix.mul_apply, Finset.sum_eq_single (j, y)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (i, y)]
    · simp [traceRightKraus, Matrix.conjTranspose_apply]
    · intro q _ hq
      simp only [traceRightKraus, Matrix.of_apply]
      rw [ite_eq_right hq]; ring
    · simp
  · intro q _ hq
    simp only [traceRightKraus, Matrix.conjTranspose_apply, Matrix.of_apply,
      apply_ite (star · : ℂ → ℂ), star_one, star_zero]
    rw [ite_eq_right hq]; simp
  · simp

/-- Kraus operator (permutation matrix) for `Matrix.reindex e e`: `P w z = [z = e.symm w]`. -/
def reindexKraus {Z W : Type*} [DecidableEq Z] (e : Z ≃ W) : Matrix W Z ℂ :=
  Matrix.of fun w z => if z = e.symm w then (1 : ℂ) else 0

/-- Reindexing by `e` is conjugation by the permutation matrix `P`. -/
lemma reindex_eq_kraus {Z W : Type*} [Fintype Z] [DecidableEq Z] (e : Z ≃ W)
    (M : Matrix Z Z ℂ) : M.reindex e e = reindexKraus e * M * (reindexKraus e)ᴴ := by
  ext w w'
  rw [reindex_apply, submatrix_apply]
  symm
  rw [Matrix.mul_apply, Finset.sum_eq_single (e.symm w')]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (e.symm w)]
    · simp [reindexKraus]
    · intro q _ hq
      simp only [reindexKraus, Matrix.of_apply]
      rw [ite_eq_right hq]; ring
    · simp
  · intro z _ hz
    simp only [reindexKraus, Matrix.conjTranspose_apply, Matrix.of_apply,
      apply_ite (star · : ℂ → ℂ), star_one, star_zero]
    rw [ite_eq_right hz]; simp
  · simp

/-- Tracing out `X` is the Kraus map with operators `K_x P`, `x : X`: swap the factors with the
permutation matrix `P` of `Equiv.prodComm`, then trace out the right factor. -/
lemma traceLeft_eq_sum_kraus {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] (M : Matrix (X × Y) (X × Y) ℂ) :
    traceLeft M = ∑ x : X, (traceRightKraus (X := Y) x * reindexKraus (Equiv.prodComm X Y)) * M *
      (traceRightKraus (X := Y) x * reindexKraus (Equiv.prodComm X Y))ᴴ := by
  rw [traceLeft_eq_traceRight_prodComm, traceRight_eq_sum_kraus, reindex_eq_kraus]
  simp only [conjTranspose_mul, Matrix.mul_assoc]

/-! ### Partial traces and reindexing as quantum channels -/

/-- Right partial trace (trace out `Y`) as a bundled `QuantumChannel`. -/
noncomputable def QuantumChannel.partialTraceRight {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] :
    Matrix.QuantumChannel (X × Y) X :=
  ⟨.ofKraus (traceRightLinearMap ℂ) traceRightKraus traceRight_eq_sum_kraus, trace_traceRight⟩

/-- Left partial trace (trace out `X`) as a bundled `QuantumChannel`. -/
noncomputable def QuantumChannel.partialTraceLeft {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] :
    Matrix.QuantumChannel (X × Y) Y :=
  ⟨.ofKraus (traceLeftLinearMap ℂ) _ traceLeft_eq_sum_kraus, trace_traceLeft⟩

/-- Conjugation by an index equivalence as a bundled `QuantumChannel`. -/
noncomputable def QuantumChannel.reindex {Z W : Type*} [Fintype Z] [DecidableEq Z] [Fintype W]
    [DecidableEq W] (e : Z ≃ W) :
    Matrix.QuantumChannel Z W :=
  ⟨.ofKraus (reindexLinearEquiv ℂ ℂ e e).toLinearMap (fun _ : Unit => reindexKraus e)
      fun M => by rw [Fintype.sum_unique]; exact reindex_eq_kraus e M,
    trace_reindex_self e⟩

/-! ### Trace-out-`C` channel for `A × B × C` -/

/-- Trace out the `C` factor of `A × B × C`, landing on `A × B`. Its action is the `lean-eval`
marginal map `M ↦ traceRight (M.reindex (prodAssoc).symm (prodAssoc).symm)`. -/
noncomputable def QuantumChannel.traceOutC {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] [Fintype C] [DecidableEq C] :
    Matrix.QuantumChannel (A × B × C) (A × B) :=
  QuantumChannel.partialTraceRight.comp (QuantumChannel.reindex (Equiv.prodAssoc A B C).symm)

/-- Tracing out `C` from `A × B × C` is the right partial trace after regrouping as
`(A × B) × C`. -/
@[simp] lemma QuantumChannel.traceOutC_val_apply {A B C : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    (M : Matrix (A × B × C) (A × B × C) ℂ) :
    (QuantumChannel.traceOutC (A := A) (B := B) (C := C)).val M
      = Matrix.traceRight
          (M.reindex (Equiv.prodAssoc A B C).symm (Equiv.prodAssoc A B C).symm) :=
  rfl

end Matrix
