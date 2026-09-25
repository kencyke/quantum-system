/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.Matrix.QuantumChannel.CPTP
public import QuantumSystem.ForMathlib.LinearAlgebra.Matrix.PartialTrace
public import QuantumSystem.ForMathlib.LinearAlgebra.Matrix.Trace

/-!
# Partial trace and reindexing as quantum channels

Tracing out a factor of a matrix on `X × Y` is completely positive and trace preserving, and so is
conjugation by an index equivalence. Composing the two gives the trace-out-`C` channel
`Matrix.QuantumChannel.traceOutC` on `A × B × C`, which realises the `lean-eval` marginal map.

## Main definitions

* `Matrix.partialTraceRightₗ`, `Matrix.partialTraceLeftₗ`: partial traces as `ℂ`-linear maps.
* `Matrix.QuantumChannel.partialTraceRight`: bundled quantum channel tracing out `Y`.
* `Matrix.QuantumChannel.reindex`: conjugation by an index equivalence, as a channel.
* `Matrix.QuantumChannel.traceOutC`: trace out the `C` factor of `A × B × C`.

## Main statements

* `Matrix.traceRight_posSemidef`, `Matrix.traceLeft_posSemidef`: partial traces preserve
  positive semidefiniteness.
* `Matrix.isCompletelyPositive_partialTraceRight`, `Matrix.isTracePreserving_partialTraceRight`.

## References

* Nielsen, Chuang, *Quantum Computation and Quantum Information*, §2.4.3
-/

@[expose] public section

namespace Matrix

/-! ### Partial trace as a quantum channel (product index types) -/

/-! #### Right partial trace as a linear map -/

/-- `Matrix.traceRight` as a `ℂ`-linear map `Matrix (X × Y) (X × Y) ℂ →ₗ[ℂ] Matrix X X ℂ`. -/
noncomputable def partialTraceRightₗ {X Y : Type*} [Fintype Y] :
    Matrix (X × Y) (X × Y) ℂ →ₗ[ℂ] Matrix X X ℂ where
  toFun M := Matrix.traceRight M
  map_add' M N := by
    ext i j; simp only [traceRight_apply, Matrix.add_apply, Finset.sum_add_distrib]
  map_smul' c M := by
    ext i j
    simp only [traceRight_apply, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]

@[simp] lemma partialTraceRightₗ_apply {X Y : Type*} [Fintype Y] (M : Matrix (X × Y) (X × Y) ℂ) :
    partialTraceRightₗ M = Matrix.traceRight M := rfl

/-- `Matrix.traceLeft` as a `ℂ`-linear map `Matrix (X × Y) (X × Y) ℂ →ₗ[ℂ] Matrix Y Y ℂ`. -/
noncomputable def partialTraceLeftₗ {X Y : Type*} [Fintype X] :
    Matrix (X × Y) (X × Y) ℂ →ₗ[ℂ] Matrix Y Y ℂ where
  toFun M := Matrix.traceLeft M
  map_add' M N := by
    ext i j; simp only [traceLeft_apply, Matrix.add_apply, Finset.sum_add_distrib]
  map_smul' c M := by
    ext i j
    simp only [traceLeft_apply, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]

@[simp] lemma partialTraceLeftₗ_apply {X Y : Type*} [Fintype X] (M : Matrix (X × Y) (X × Y) ℂ) :
    partialTraceLeftₗ M = Matrix.traceLeft M := rfl

/-! #### Kraus operators and complete positivity -/

/-- Kraus operator for the right partial trace, indexed by `y : Y`: `K_y x p = [p = (x, y)]`. -/
def traceRightKraus {X Y : Type*} [DecidableEq X] [DecidableEq Y] (y : Y) :
    Matrix X (X × Y) ℂ :=
  Matrix.of fun x p => if p = (x, y) then (1 : ℂ) else 0

lemma isCompletelyPositive_partialTraceRight {X Y : Type*} [Fintype X] [Fintype Y] :
    IsCompletelyPositive (partialTraceRightₗ (X := X) (Y := Y)) := by
  classical
  refine ⟨Fintype.card Y, fun i => traceRightKraus ((Fintype.equivFin Y).symm i), fun M => ?_⟩
  rw [partialTraceRightₗ_apply]
  ext i j
  rw [traceRight_apply, Matrix.sum_apply, ← (Fintype.equivFin Y).symm.sum_comp
    (fun y => M (i, y) (j, y))]
  refine Finset.sum_congr rfl fun p _ => ?_
  -- Goal: M (i, y) (j, y) = (K_y * M * K_yᴴ) i j with `y = (equivFin Y).symm p`
  -- (mul is `Matrix.mul` from `IsCompletelyPositive`).
  symm
  rw [Matrix.mul_apply, Finset.sum_eq_single (j, (Fintype.equivFin Y).symm p)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (i, (Fintype.equivFin Y).symm p)]
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

lemma isTracePreserving_partialTraceRight {X Y : Type*} [Fintype X] [Fintype Y] :
    IsTracePreserving (partialTraceRightₗ (X := X) (Y := Y)) :=
  fun M => by rw [partialTraceRightₗ_apply]; exact trace_traceRight M

/-- Right partial trace (trace out `Y`) as a bundled `QuantumChannel`. -/
noncomputable def QuantumChannel.partialTraceRight {X Y : Type*} [Fintype X] [Fintype Y] :
    Matrix.QuantumChannel (X × Y) X :=
  ⟨partialTraceRightₗ, isCompletelyPositive_partialTraceRight, isTracePreserving_partialTraceRight⟩

/-! #### Conjugation by an index equivalence as a channel -/

/-- Conjugation by a reindex `e : Z ≃ W`: `M ↦ M.submatrix e.symm e.symm`, as a linear map. -/
noncomputable def reindexₗ {Z W : Type*} (e : Z ≃ W) :
    Matrix Z Z ℂ →ₗ[ℂ] Matrix W W ℂ where
  toFun M := M.submatrix e.symm e.symm
  map_add' M N := by ext w w'; simp [Matrix.submatrix_apply]
  map_smul' c M := by ext w w'; simp [Matrix.submatrix_apply]

@[simp] lemma reindexₗ_apply {Z W : Type*} (e : Z ≃ W) (M : Matrix Z Z ℂ) :
    reindexₗ e M = M.submatrix e.symm e.symm := rfl

/-- Kraus operator (permutation matrix) for `reindexₗ e`: `P w z = [z = e.symm w]`. -/
def reindexKraus {Z W : Type*} [DecidableEq Z] (e : Z ≃ W) : Matrix W Z ℂ :=
  Matrix.of fun w z => if z = e.symm w then (1 : ℂ) else 0

lemma isCompletelyPositive_reindexₗ {Z W : Type*} [Fintype Z] (e : Z ≃ W) :
    IsCompletelyPositive (reindexₗ e) := by
  classical
  refine ⟨1, fun _ => reindexKraus e, fun M => ?_⟩
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
  ext w w'
  rw [reindexₗ_apply, Matrix.submatrix_apply]
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

lemma isTracePreserving_reindexₗ {Z W : Type*} [Fintype Z] [Fintype W] (e : Z ≃ W) :
    IsTracePreserving (reindexₗ e) := by
  intro M
  rw [reindexₗ_apply]
  exact trace_reindex_self e M

/-- Conjugation by an index equivalence as a bundled `QuantumChannel`. -/
noncomputable def QuantumChannel.reindex {Z W : Type*} [Fintype Z] [Fintype W] (e : Z ≃ W) :
    Matrix.QuantumChannel Z W :=
  ⟨reindexₗ e, isCompletelyPositive_reindexₗ e, isTracePreserving_reindexₗ e⟩

/-! #### Trace-out-`C` channel for `A × B × C` -/

/-- Trace out the `C` factor of `A × B × C`, landing on `A × B`. Its action is the `lean-eval`
marginal map `M ↦ traceRight (M.reindex (prodAssoc).symm (prodAssoc).symm)`. -/
noncomputable def QuantumChannel.traceOutC {A B C : Type*} [Fintype A] [Fintype B] [Fintype C] :
    Matrix.QuantumChannel (A × B × C) (A × B) :=
  (QuantumChannel.reindex (Equiv.prodAssoc A B C).symm).comp QuantumChannel.partialTraceRight

@[simp] lemma QuantumChannel.traceOutC_val_apply {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C] (M : Matrix (A × B × C) (A × B × C) ℂ) :
    (QuantumChannel.traceOutC (A := A) (B := B) (C := C)).val M
      = Matrix.traceRight
          (M.reindex (Equiv.prodAssoc A B C).symm (Equiv.prodAssoc A B C).symm) := by
  change partialTraceRightₗ (reindexₗ (Equiv.prodAssoc A B C).symm M) = _
  rw [partialTraceRightₗ_apply, reindexₗ_apply, Matrix.reindex_apply]

end Matrix
