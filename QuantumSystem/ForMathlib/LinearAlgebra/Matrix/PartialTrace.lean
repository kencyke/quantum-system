module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Partial trace of a matrix over a tensor factor

For a matrix whose row/column indices are product types sharing one factor, the **partial
traces** over that common factor:

* `Matrix.traceRight (M : Matrix (l × n) (c × n) R) : Matrix l c R` — trace out the **right**
  factor `n`, entry-wise `traceRight M i j = ∑ k, M (i, k) (j, k)`;
* `Matrix.traceLeft (M : Matrix (n × l) (n × c) R) : Matrix l c R` — trace out the **left**
  factor `n`, entry-wise `traceLeft M i j = ∑ k, M (k, i) (k, j)`.

These are the concrete matrix-entry forms of the basis-free operator partial trace
`TensorProduct.partialTraceRight` (`QuantumSystem.ForMathlib.LinearAlgebra.Trace`). The row and
column "kept" indices `l`, `c` are allowed to differ, so the operations apply to rectangular
blocks; they are stated over an arbitrary `AddCommMonoid` so they specialise to scalars in any
finite-dimensional quantum system.

## Main results

* `Matrix.traceLeft_eq_traceRight_prodComm` — tracing out the left factor equals tracing out
  the right factor after swapping the two factors with `Equiv.prodComm`.
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

@[simp] lemma traceRight_apply {l c n : Type*} [Fintype n] (M : Matrix (l × n) (c × n) R)
    (i : l) (j : c) :
    traceRight M i j = ∑ k, M (i, k) (j, k) := rfl

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

/-- Tracing out the **left** factor equals tracing out the **right** factor after swapping the
two factors with `Equiv.prodComm`. -/
theorem traceLeft_eq_traceRight_prodComm {l c n : Type*} [Fintype n]
    (M : Matrix (n × l) (n × c) R) :
    traceLeft M = traceRight (M.reindex (Equiv.prodComm n l) (Equiv.prodComm n c)) := by
  ext i j
  simp [Matrix.reindex_apply]

/-- The right partial trace preserves the full trace: `Tr (traceRight M) = Tr M`. -/
@[simp] theorem trace_traceRight {l n : Type*} [Fintype l] [Fintype n]
    (M : Matrix (l × n) (l × n) R) :
    (traceRight M).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, traceRight_apply]
  exact (Fintype.sum_prod_type fun p : l × n => M p p).symm

/-- The left partial trace preserves the full trace: `Tr (traceLeft M) = Tr M`. -/
@[simp] theorem trace_traceLeft {l n : Type*} [Fintype l] [Fintype n]
    (M : Matrix (n × l) (n × l) R) :
    (traceLeft M).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, traceLeft_apply]
  rw [Finset.sum_comm]
  exact (Fintype.sum_prod_type fun p : n × l => M p p).symm

end Matrix
