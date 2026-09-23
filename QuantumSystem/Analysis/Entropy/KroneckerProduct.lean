/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.CFC.Diagonal
public import QuantumSystem.State
public import QuantumSystem.ForMathlib.LinearAlgebra.Matrix.PartialTrace

/-!
# Tensor product (Kronecker) of density matrices and bipartite Kronecker calculus

Given density matrices `ρ : DensityMatrix n` and `σ : DensityMatrix m`, we form
their tensor product `ρ ⊗ σ : DensityMatrix (n × m)` whose underlying matrix is
the Kronecker product of the underlying matrices. This is the bipartite product
state (independent-systems product state).

This file is the hub for **Kronecker-product calculus on bipartite matrices**:

* preservation of Hermitian structure under `⊗ₖ`,
* Kronecker spectral decomposition,
* and the **Heisenberg duality at product type**
  `Tr(ρ · (X ⊗ 1)) = Tr(tr₂(ρ) · X)` together with the symmetric `(1 ⊗ Y)` version.

Partial traces are the positional `Matrix.traceRight` / `Matrix.traceLeft`
(`ForMathlib/LinearAlgebra/Matrix/PartialTrace.lean`); this file only adds the paper notation
`tr₂(ρ) = traceRight ρ` / `tr₁(ρ) = traceLeft ρ` (Nielsen–Chuang §2.4).

## Main definitions

* `DensityMatrix.kronecker` — tensor product of density matrices.

## Main results

* `DensityMatrix.kronecker_toMatrix` — underlying-matrix unfolding.
* `Matrix.IsHermitian.kronecker` — Kronecker of Hermitian matrices is Hermitian.
* `Matrix.kronecker_eq_unitary_conj_diagonal` — Kronecker spectral decomposition.
* `Matrix.trace_mul_kronecker_one_right` — `Tr(ρ · (X ⊗ 1)) = Tr(tr₂(ρ) · X)`.
* `Matrix.trace_mul_kronecker_one_left`  — `Tr(ρ · (1 ⊗ Y)) = Tr(tr₁(ρ) · Y)`.
* `Matrix.sum_diag_conj_kronecker_right` / `Matrix.sum_diag_conj_kronecker_left` — diagonal
  block sums of `(U_A ⊗ U_B)ᴴ ρ (U_A ⊗ U_B)` are the diagonal entries of the conjugated marginals.
-/

@[expose] public section

namespace Matrix

open scoped Kronecker MatrixOrder ComplexOrder

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-! ### Kronecker preserves Hermitian -/

omit [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] in
/-- The Kronecker product of two Hermitian matrices is Hermitian. -/
lemma IsHermitian.kronecker {A : Matrix n n ℂ} {B : Matrix m m ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : (A ⊗ₖ B).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_kronecker, hA.eq, hB.eq]

/-! ### Kronecker spectral decomposition

Given spectral decompositions `A = U_A * diag λ * U_Aᴴ` and `B = U_B * diag μ * U_Bᴴ`,
the Kronecker product satisfies
  `A ⊗ₖ B = (U_A ⊗ U_B) * diag ((i,j) ↦ λ i * μ j) * (U_A ⊗ U_B)ᴴ`,
exhibiting `U_A ⊗ U_B` as a valid unitary diagonaliser of `A ⊗ B`. -/

/-- **Kronecker spectral decomposition.** If `A = U_A * D_A * U_Aᴴ` and
`B = U_B * D_B * U_Bᴴ` with `D_A = diagonal dA`, `D_B = diagonal dB`, then
`A ⊗ₖ B = (U_A ⊗ U_B) * diagonal (fun (i,j) => dA i * dB j) * (U_A ⊗ U_B)ᴴ`. -/
lemma kronecker_eq_unitary_conj_diagonal
    {U_A : Matrix n n ℂ} {U_B : Matrix m m ℂ}
    {dA : n → ℂ} {dB : m → ℂ}
    {A : Matrix n n ℂ} {B : Matrix m m ℂ}
    (hA : A = U_A * diagonal dA * U_Aᴴ)
    (hB : B = U_B * diagonal dB * U_Bᴴ) :
    A ⊗ₖ B =
      (U_A ⊗ₖ U_B) *
        diagonal (fun ij : n × m => dA ij.1 * dB ij.2) *
        (U_A ⊗ₖ U_B)ᴴ := by
  rw [hA, hB, conjTranspose_kronecker]
  -- Apply mul_kronecker_mul twice (forward) and diagonal_kronecker_diagonal
  rw [mul_kronecker_mul, mul_kronecker_mul, diagonal_kronecker_diagonal]


/-! ### Paper notation: `tr₁(ρ)` / `tr₂(ρ)`

Subscript convention follows Nielsen–Chuang §2.4: `trᵢ(ρ)` traces *out* factor
`i` and retains the other. For a bipartite matrix `ρ` on `n × m`:

* `tr₂(ρ) = Matrix.traceRight ρ` — traces out the second factor `m`, retaining `n`.
* `tr₁(ρ) = Matrix.traceLeft ρ` — traces out the first factor `n`, retaining `m`. -/

namespace QuantumInfo

scoped syntax:max "tr₁(" term ")" : term
scoped syntax:max "tr₂(" term ")" : term

scoped macro_rules
  | `(tr₁($ρ)) => `(Matrix.traceLeft $ρ)
  | `(tr₂($ρ)) => `(Matrix.traceRight $ρ)

end QuantumInfo

open scoped QuantumInfo

/-! ### Heisenberg duality at product type

`Tr(ρ · (X ⊗ 1)) = Tr(tr₂(ρ) · X)` and the symmetric `(1 ⊗ Y)` version. -/

omit [DecidableEq n] in
/-- **Right-factor Heisenberg dual**: tracing `ρ` against the embedded observable
`X ⊗ 1` reduces to the trace against the partial trace that retains the first factor. -/
lemma trace_mul_kronecker_one_right
    (ρ : Matrix (n × m) (n × m) ℂ) (X : Matrix n n ℂ) :
  Tr (ρ * (X ⊗ₖ (1 : Matrix m m ℂ))) =
    Tr (tr₂(ρ) * X) := by
  classical
  unfold Matrix.trace
  simp_rw [Matrix.diag_apply, Matrix.mul_apply, traceRight_apply]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type, Matrix.kronecker_apply, Matrix.one_apply]
  -- Goal: ∑ a, ∑ b, ∑ a', ∑ b', ρ (a, b) (a', b') * (X a' a * (if b' = b then 1 else 0))
  --     = ∑ a, ∑ a', (∑ b, ρ (a, b) (a', b)) * X a' a
  have inner : ∀ (a : n) (b : m) (a' : n),
      (∑ b' : m, ρ (a, b) (a', b') * (X a' a * (if b' = b then (1 : ℂ) else 0))) =
      ρ (a, b) (a', b) * X a' a := by
    intro a b a'
    rw [Finset.sum_eq_single b]
    · simp
    · intro b' _ hb'; rw [ite_eq_right hb']; ring
    · simp
  simp_rw [inner]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [Finset.sum_mul]

omit [DecidableEq m] in
/-- **Left-factor Heisenberg dual**: `Tr(ρ · (1 ⊗ Y))` reduces to the trace against the
partial trace that retains the second factor. -/
lemma trace_mul_kronecker_one_left
    (ρ : Matrix (n × m) (n × m) ℂ) (Y : Matrix m m ℂ) :
    Tr (ρ * ((1 : Matrix n n ℂ) ⊗ₖ Y)) =
      Tr (tr₁(ρ) * Y) := by
  classical
  unfold Matrix.trace
  simp_rw [Matrix.diag_apply, Matrix.mul_apply, traceLeft_apply]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type, Matrix.kronecker_apply, Matrix.one_apply]
  -- Goal: ∑ a, ∑ b, ∑ a', ∑ b', ρ (a, b) (a', b') * ((if a' = a then 1 else 0) * Y b' b)
  --     = ∑ b, ∑ b', (∑ a, ρ (a, b) (a, b')) * Y b' b
  have inner : ∀ (a : n) (b : m),
      (∑ a' : n, ∑ b' : m, ρ (a, b) (a', b') * ((if a' = a then (1 : ℂ) else 0) * Y b' b)) =
      ∑ b' : m, ρ (a, b) (a, b') * Y b' b := by
    intro a b
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [Finset.sum_eq_single a]
    · simp
    · intro a' _ ha'; rw [ite_eq_right ha']; ring
    · simp
  simp_rw [inner]
  -- Goal: ∑ a, ∑ b, ∑ b', ρ (a, b) (a, b') * Y b' b
  --     = ∑ b, ∑ b', (∑ a, ρ (a, b) (a, b')) * Y b' b
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [Finset.sum_mul]

/-! ### Diagonal block sums of a Kronecker-conjugated matrix

For `W = U_A ⊗ U_B` with `U_B` unitary, the sum of the diagonal entries of `Wᴴ ρ W` over the
second index at fixed first index `i` is the `(i, i)` entry of `U_Aᴴ · tr₂(ρ) · U_A`, and
symmetrically for the first index. These are the marginal identities behind the mutual-information
formula `D(ρ_AB ‖ ρ_A ⊗ ρ_B) = -S(ρ_AB) + S(ρ_A) + S(ρ_B)` for singular marginals. -/

/-- `Tr(M · diagonal (Pi.single i 1)) = M i i`. -/
lemma trace_mul_diagonal_single (M : Matrix n n ℂ) (i : n) :
    Tr (M * diagonal (Pi.single i 1)) = M i i := by
  simp only [Matrix.trace, Matrix.diag, mul_diagonal]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb; simp [hb]
  · simp

omit [DecidableEq n] in
/-- Second-index diagonal block sum of `(U_A ⊗ U_B)ᴴ ρ (U_A ⊗ U_B)` at fixed first index. -/
lemma sum_diag_conj_kronecker_right
    (ρ : Matrix (n × m) (n × m) ℂ) (U_A : Matrix n n ℂ) {U_B : Matrix m m ℂ}
    (hU_B : U_B * U_Bᴴ = 1) (i : n) :
    ∑ j, ((U_A ⊗ₖ U_B)ᴴ * ρ * (U_A ⊗ₖ U_B)) (i, j) (i, j) =
      (U_Aᴴ * tr₂(ρ) * U_A) i i := by
  classical
  set W := U_A ⊗ₖ U_B with hW
  set E : Matrix n n ℂ := diagonal (Pi.single i 1) with hE
  have hL : ∑ j, (Wᴴ * ρ * W) (i, j) (i, j) =
      Tr ((Wᴴ * ρ * W) * (E ⊗ₖ (1 : Matrix m m ℂ))) := by
    rw [trace_mul_kronecker_one_right, hE, trace_mul_diagonal_single, traceRight_apply]
  have hconj : W * (E ⊗ₖ (1 : Matrix m m ℂ)) * Wᴴ = (U_A * E * U_Aᴴ) ⊗ₖ (1 : Matrix m m ℂ) := by
    rw [hW, conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one,
      hU_B]
  rw [hL, ← trace_mul_diagonal_single (U_Aᴴ * tr₂(ρ) * U_A) i, ← hE]
  calc Tr ((Wᴴ * ρ * W) * (E ⊗ₖ (1 : Matrix m m ℂ)))
      = Tr (ρ * (W * (E ⊗ₖ (1 : Matrix m m ℂ)) * Wᴴ)) := by
        rw [show (Wᴴ * ρ * W) * (E ⊗ₖ (1 : Matrix m m ℂ)) =
            Wᴴ * (ρ * (W * (E ⊗ₖ (1 : Matrix m m ℂ)))) by simp only [Matrix.mul_assoc],
          Matrix.trace_mul_comm]
        simp only [Matrix.mul_assoc]
    _ = Tr (tr₂(ρ) * (U_A * E * U_Aᴴ)) := by
        rw [hconj, trace_mul_kronecker_one_right]
    _ = Tr ((U_Aᴴ * tr₂(ρ) * U_A) * E) := by
        rw [show tr₂(ρ) * (U_A * E * U_Aᴴ) =
            (tr₂(ρ) * U_A * E) * U_Aᴴ by simp only [Matrix.mul_assoc],
          Matrix.trace_mul_comm]
        simp only [Matrix.mul_assoc]

omit [DecidableEq m] in
/-- First-index diagonal block sum of `(U_A ⊗ U_B)ᴴ ρ (U_A ⊗ U_B)` at fixed second index. -/
lemma sum_diag_conj_kronecker_left
    (ρ : Matrix (n × m) (n × m) ℂ) {U_A : Matrix n n ℂ} (U_B : Matrix m m ℂ)
    (hU_A : U_A * U_Aᴴ = 1) (j : m) :
    ∑ i, ((U_A ⊗ₖ U_B)ᴴ * ρ * (U_A ⊗ₖ U_B)) (i, j) (i, j) =
      (U_Bᴴ * tr₁(ρ) * U_B) j j := by
  classical
  set W := U_A ⊗ₖ U_B with hW
  set E : Matrix m m ℂ := diagonal (Pi.single j 1) with hE
  have hL : ∑ i, (Wᴴ * ρ * W) (i, j) (i, j) =
      Tr ((Wᴴ * ρ * W) * ((1 : Matrix n n ℂ) ⊗ₖ E)) := by
    rw [trace_mul_kronecker_one_left, hE, trace_mul_diagonal_single, traceLeft_apply]
  have hconj : W * ((1 : Matrix n n ℂ) ⊗ₖ E) * Wᴴ = (1 : Matrix n n ℂ) ⊗ₖ (U_B * E * U_Bᴴ) := by
    rw [hW, conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one,
      hU_A]
  rw [hL, ← trace_mul_diagonal_single (U_Bᴴ * tr₁(ρ) * U_B) j, ← hE]
  calc Tr ((Wᴴ * ρ * W) * ((1 : Matrix n n ℂ) ⊗ₖ E))
      = Tr (ρ * (W * ((1 : Matrix n n ℂ) ⊗ₖ E) * Wᴴ)) := by
        rw [show (Wᴴ * ρ * W) * ((1 : Matrix n n ℂ) ⊗ₖ E) =
            Wᴴ * (ρ * (W * ((1 : Matrix n n ℂ) ⊗ₖ E))) by simp only [Matrix.mul_assoc],
          Matrix.trace_mul_comm]
        simp only [Matrix.mul_assoc]
    _ = Tr (tr₁(ρ) * (U_B * E * U_Bᴴ)) := by
        rw [hconj, trace_mul_kronecker_one_left]
    _ = Tr ((U_Bᴴ * tr₁(ρ) * U_B) * E) := by
        rw [show tr₁(ρ) * (U_B * E * U_Bᴴ) =
            (tr₁(ρ) * U_B * E) * U_Bᴴ by simp only [Matrix.mul_assoc],
          Matrix.trace_mul_comm]
        simp only [Matrix.mul_assoc]

end Matrix

/-! ### Tensor product of density matrices -/

namespace DensityMatrix

open scoped Kronecker
open Matrix

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-- **Tensor product (Kronecker) of density matrices.** Represents the
independent-systems product state on the joint system `n × m`. -/
noncomputable def kronecker (ρ : DensityMatrix n) (σ : DensityMatrix m) :
    DensityMatrix (n × m) where
  toMatrix := ρ.toMatrix ⊗ₖ σ.toMatrix
  posSemidef := ρ.posSemidef.kronecker σ.posSemidef
  trace_eq_one := by
    rw [trace_kronecker, ρ.trace_eq_one, σ.trace_eq_one, mul_one]

@[inherit_doc DensityMatrix.kronecker]
scoped[Kronecker] infixl:100 " ⊗ " => DensityMatrix.kronecker

@[simp] lemma kronecker_toMatrix (ρ : DensityMatrix n) (σ : DensityMatrix m) :
    (ρ ⊗ σ).toMatrix = ρ.toMatrix ⊗ₖ σ.toMatrix := rfl

end DensityMatrix
