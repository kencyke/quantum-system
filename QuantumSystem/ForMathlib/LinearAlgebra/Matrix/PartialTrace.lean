/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Partial trace of a matrix over a tensor factor

For a matrix whose row/column indices are product types sharing one factor, the **partial
traces** over that common factor:

* `Matrix.traceRight (M : Matrix (l × n) (c × n) R) : Matrix l c R` — trace out the **right**
  factor `n`, entry-wise `traceRight M i j = ∑ k, M (i, k) (j, k)`;
* `Matrix.traceLeft (M : Matrix (n × l) (n × c) R) : Matrix l c R` — trace out the **left**
  factor `n`, entry-wise `traceLeft M i j = ∑ k, M (k, i) (k, j)`.

In standard bases they correspond to the basis-free partial traces of operators on a tensor product
of finite-dimensional Hilbert spaces (this correspondence is not formalised). The row and
column "kept" indices `l`, `c` are allowed to differ, so the operations apply to rectangular
blocks; they are stated over an arbitrary `AddCommMonoid` so they specialise to scalars in any
finite-dimensional quantum system.

## Main definitions

* `Matrix.traceRightLinearMap`, `Matrix.traceLeftLinearMap` — `traceRight` and `traceLeft` as
  linear maps, for use where a bundled `LinearMap` is required (as `Matrix.traceLinearMap` is for
  `Matrix.trace`). Results about partial traces are stated with `traceRight` and `traceLeft`.

## Main results

* `Matrix.traceLeft_eq_traceRight_prodComm` — tracing out the left factor equals tracing out
  the right factor after swapping the two factors with `Equiv.prodComm`.
* `Matrix.traceRight_kronecker`, `Matrix.traceLeft_kronecker` — the partial traces of a Kronecker
  product, `traceRight (X ⊗ Y) = Tr(Y) • X` and `traceLeft (X ⊗ Y) = Tr(X) • Y`.
* `Matrix.trace_mul_kronecker_one_right` — the right partial trace is dual to `X ↦ X ⊗ 1`,
  `Tr (ρ (X ⊗ 1)) = Tr (traceRight ρ X)`.
-/

@[expose] public section

namespace Matrix

variable {R : Type*} [AddCommMonoid R]

/-- **Partial trace over the right factor**: trace out the common right factor `n` of a matrix
with rows indexed by `l × n` and columns by `c × n`, leaving a matrix on `l × c`. Entry-wise
`traceRight M i j = ∑ k, M (i, k) (j, k)`. -/
def traceRight {l c n : Type*} [Fintype n] (M : Matrix (l × n) (c × n) R) : Matrix l c R :=
  Matrix.of fun i j => ∑ k, M (i, k) (j, k)

/-- **Partial trace over the left factor**: trace out the common left factor `n` of a matrix
with rows indexed by `n × l` and columns by `n × c`, leaving a matrix on `l × c`. Entry-wise
`traceLeft M i j = ∑ k, M (k, i) (k, j)`. -/
def traceLeft {l c n : Type*} [Fintype n] (M : Matrix (n × l) (n × c) R) : Matrix l c R :=
  Matrix.of fun i j => ∑ k, M (k, i) (k, j)

/-- The entries of the right partial trace:
`traceRight M i j = Σₖ M (i, k) (j, k)`, summing over the right factor. -/
@[simp] lemma traceRight_apply {l c n : Type*} [Fintype n] (M : Matrix (l × n) (c × n) R)
    (i : l) (j : c) :
    traceRight M i j = ∑ k, M (i, k) (j, k) := rfl

/-- The entries of the left partial trace:
`traceLeft M i j = Σₖ M (k, i) (k, j)`, summing over the left factor. -/
@[simp] lemma traceLeft_apply {l c n : Type*} [Fintype n] (M : Matrix (n × l) (n × c) R)
    (i : l) (j : c) :
    traceLeft M i j = ∑ k, M (k, i) (k, j) := rfl

/-- The right partial trace of the zero matrix is zero. -/
@[simp] lemma traceRight_zero {l c n : Type*} [Fintype n] :
    traceRight (0 : Matrix (l × n) (c × n) ℂ) = 0 := by
  ext i j; simp [traceRight_apply]

/-- The left partial trace of the zero matrix is zero. -/
@[simp] lemma traceLeft_zero {l c n : Type*} [Fintype n] :
    traceLeft (0 : Matrix (n × l) (n × c) ℂ) = 0 := by
  ext i j; simp [traceLeft_apply]

/-- The right partial trace is `ℝ`-linear in the matrix. -/
@[simp] lemma traceRight_smul {l n : Type*} [Fintype n] (c : ℝ) (M : Matrix (l × n) (l × n) ℂ) :
    traceRight (c • M) = c • traceRight M := by
  ext i j; simp only [traceRight_apply, Matrix.smul_apply]; exact Finset.smul_sum.symm

/-- The left partial trace is `ℝ`-linear in the matrix. -/
@[simp] lemma traceLeft_smul {l n : Type*} [Fintype n] (c : ℝ) (M : Matrix (n × l) (n × l) ℂ) :
    traceLeft (c • M) = c • traceLeft M := by
  ext i j; simp only [traceLeft_apply, Matrix.smul_apply]; exact Finset.smul_sum.symm

section LinearMap

variable (S : Type*) {α : Type*} [Semiring S] [AddCommMonoid α] [Module S α]

/-- `Matrix.traceRight` as an `S`-linear map. -/
@[simps]
def traceRightLinearMap {l c n : Type*} [Fintype n] :
    Matrix (l × n) (c × n) α →ₗ[S] Matrix l c α where
  toFun := traceRight
  map_add' M N := by ext i j; simp [Finset.sum_add_distrib]
  map_smul' r M := by ext i j; simp [Finset.smul_sum]

/-- `Matrix.traceLeft` as an `S`-linear map. -/
@[simps]
def traceLeftLinearMap {l c n : Type*} [Fintype n] :
    Matrix (n × l) (n × c) α →ₗ[S] Matrix l c α where
  toFun := traceLeft
  map_add' M N := by ext i j; simp [Finset.sum_add_distrib]
  map_smul' r M := by ext i j; simp [Finset.smul_sum]

end LinearMap

/-- Tracing out the **left** factor equals tracing out the **right** factor after swapping the
two factors with `Equiv.prodComm`. -/
lemma traceLeft_eq_traceRight_prodComm {l c n : Type*} [Fintype n]
    (M : Matrix (n × l) (n × c) R) :
    traceLeft M = traceRight (M.reindex (Equiv.prodComm n l) (Equiv.prodComm n c)) := by
  ext i j
  simp [Matrix.reindex_apply]

/-- The right partial trace preserves the full trace: `Tr (traceRight M) = Tr M`. -/
@[simp] lemma trace_traceRight {l n : Type*} [Fintype l] [Fintype n]
    (M : Matrix (l × n) (l × n) R) :
    (traceRight M).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, traceRight_apply]
  exact (Fintype.sum_prod_type fun p : l × n => M p p).symm

/-- The left partial trace preserves the full trace: `Tr (traceLeft M) = Tr M`. -/
@[simp] lemma trace_traceLeft {l n : Type*} [Fintype l] [Fintype n]
    (M : Matrix (n × l) (n × l) R) :
    (traceLeft M).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, traceLeft_apply]
  rw [Finset.sum_comm]
  exact (Fintype.sum_prod_type fun p : n × l => M p p).symm

section Kronecker

open scoped Kronecker

variable {S : Type*} [CommSemiring S]

/-- Tracing out the right factor of a Kronecker product: `tr₂(X ⊗ Y) = Tr(Y) • X`. -/
@[simp] lemma traceRight_kronecker {l c n : Type*} [Fintype n] (X : Matrix l c S)
    (Y : Matrix n n S) :
    traceRight (X ⊗ₖ Y) = Y.trace • X := by
  ext i j
  simp only [traceRight_apply, kroneckerMap_apply, smul_apply, smul_eq_mul, Matrix.trace,
    diag_apply, ← Finset.mul_sum]
  exact mul_comm _ _

/-- Tracing out the left factor of a Kronecker product: `tr₁(X ⊗ Y) = Tr(X) • Y`. -/
@[simp] lemma traceLeft_kronecker {l c n : Type*} [Fintype n] (X : Matrix n n S)
    (Y : Matrix l c S) :
    traceLeft (X ⊗ₖ Y) = X.trace • Y := by
  ext i j
  simp only [traceLeft_apply, kroneckerMap_apply, smul_apply, smul_eq_mul, Matrix.trace,
    diag_apply, ← Finset.sum_mul]

/-- **Duality of the right partial trace**: tracing `ρ` against the embedded observable `X ⊗ 1`
is tracing its right partial trace against `X`, `Tr (ρ (X ⊗ 1)) = Tr (tr₂(ρ) X)`. -/
lemma trace_mul_kronecker_one_right {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (ρ : Matrix (n × m) (n × m) S) (X : Matrix n n S) :
    (ρ * (X ⊗ₖ (1 : Matrix m m S))).trace = (traceRight ρ * X).trace := by
  unfold Matrix.trace
  simp_rw [Matrix.diag_apply, Matrix.mul_apply, traceRight_apply]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type, Matrix.kronecker_apply, Matrix.one_apply]
  have inner (a : n) (b : m) (a' : n) :
      (∑ b' : m, ρ (a, b) (a', b') * (X a' a * (if b' = b then (1 : S) else 0))) =
        ρ (a, b) (a', b) * X a' a := by
    rw [Finset.sum_eq_single b]
    · simp
    · intro b' _ hb'
      simp [hb']
    · simp
  simp_rw [inner]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [Finset.sum_mul]

end Kronecker

section PosSemidef

open scoped ComplexOrder

/-- The right partial trace preserves positive semidefiniteness (it is a sum of principal
submatrices). -/
lemma traceRight_posSemidef {l n : Type*} [Fintype n]
    {M : Matrix (l × n) (l × n) ℂ} (hM : M.PosSemidef) : (Matrix.traceRight M).PosSemidef := by
  have hsum : Matrix.traceRight M
      = ∑ k : n, M.submatrix (fun i : l => (i, k)) (fun j : l => (j, k)) := by
    ext i j; simp [Matrix.traceRight_apply, Matrix.sum_apply, Matrix.submatrix_apply]
  rw [hsum]
  exact Matrix.posSemidef_sum _ (fun k _ => hM.submatrix _)

/-- The left partial trace preserves positive semidefiniteness. -/
lemma traceLeft_posSemidef {l n : Type*} [Fintype n]
    {M : Matrix (n × l) (n × l) ℂ} (hM : M.PosSemidef) : (Matrix.traceLeft M).PosSemidef := by
  have hsum : Matrix.traceLeft M
      = ∑ k : n, M.submatrix (fun i : l => (k, i)) (fun j : l => (k, j)) := by
    ext i j; simp [Matrix.traceLeft_apply, Matrix.sum_apply, Matrix.submatrix_apply]
  rw [hsum]
  exact Matrix.posSemidef_sum _ (fun k _ => hM.submatrix _)

end PosSemidef

end Matrix
