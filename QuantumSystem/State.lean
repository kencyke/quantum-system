module

public import QuantumSystem.Analysis.Matrix.HermitianFunctionalCalculus
public import QuantumSystem.Notation

/-!
# Density Matrices

This file defines density matrices for finite dimensional systems.

## Main definitions

* `DensityMatrix`: Structure wrapping a positive semi-definite, trace-1 matrix.

## Mathematical Background

For a density matrix ρ on ℂⁿ:
- ρ is Hermitian (self-adjoint)
- ρ is positive semi-definite: ⟨v, ρv⟩ ≥ 0 for all v
- Tr(ρ) = 1

The spectral theorem gives ρ = U diag(λ₁, ..., λₙ) U* where λᵢ ≥ 0 and Σλᵢ = 1.

The Von Neumann entropy is:
  S(ρ) = -Tr(ρ log ρ) = -Σᵢ λᵢ log λᵢ

The relative entropy is:
  S(ρ || σ) = Tr(ρ (log ρ - log σ))

where log ρ and log σ are matrix logarithms computed via the continuous functional
calculus (CFC), applied to each matrix's own spectral decomposition. This definition
is correct for **non-commuting** ρ and σ. When ρ and σ commute (share eigenbasis),
it reduces to:
  S(ρ || σ) = Σᵢ λᵢ (log λᵢ - log μᵢ)
where λᵢ, μᵢ are eigenvalues in the shared basis.

**Note**: Defining S(ρ‖σ) via independently sorted eigenvalue sequences
Σᵢ λᵢ(log λᵢ - log μᵢ) is **incorrect** for non-commuting density matrices,
because independently sorting eigenvalues destroys the operator-algebraic structure.
The correct definition must use matrix logarithms.

## References

* Nielsen, Chuang, *Quantum Computation and Quantum Information*
-/

@[expose] public section

namespace Matrix

open scoped ComplexOrder MatrixOrder

/-- A density matrix is a positive semi-definite matrix with trace 1.
This represents a mixed quantum state: ρ ≥ 0, Tr(ρ) = 1. -/
structure DensityMatrix (n : Type*) [Fintype n] [DecidableEq n] where
  /-- The underlying matrix -/
  toMatrix : Matrix n n ℂ
  /-- ρ is positive semi-definite -/
  posSemidef : toMatrix.PosSemidef
  /-- Tr(ρ) = 1 -/
  trace_eq_one : Tr toMatrix = 1

namespace DensityMatrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Two density matrices are equal iff their underlying matrices are equal. -/
@[ext] theorem ext {ρ σ : DensityMatrix n} (h : ρ.toMatrix = σ.toMatrix) : ρ = σ := by
  cases ρ; cases σ; congr

/-- A density matrix is Hermitian. -/
theorem isHermitian (ρ : DensityMatrix n) : ρ.toMatrix.IsHermitian := ρ.posSemidef.1

/-- All eigenvalues of a density matrix are non-negative. -/
theorem eigenvalues_nonneg (ρ : DensityMatrix n) (i : n) :
    0 ≤ ρ.isHermitian.eigenvalues i :=
  (ρ.isHermitian.posSemidef_iff_eigenvalues_nonneg.mp ρ.posSemidef) i

/-- The eigenvalues of a density matrix sum to 1. -/
lemma sum_eigenvalues (ρ : DensityMatrix n) :
    ∑ i, ρ.isHermitian.eigenvalues i = 1 := by
  have htr := ρ.trace_eq_one
  rw [ρ.isHermitian.spectral_theorem] at htr
  rw [Unitary.conjStarAlgAut_apply, trace_mul_cycle, Unitary.coe_star_mul_self,
      Matrix.one_mul, Matrix.trace_diagonal] at htr
  simp only [Function.comp_apply] at htr
  have : (1 : ℂ) = ↑(1 : ℝ) := by simp
  rw [this] at htr
  have hinj := RCLike.ofReal_injective (K := ℂ)
  rw [← RCLike.ofReal_sum] at htr
  exact hinj htr

/-- Each eigenvalue of a density matrix is at most 1. -/
lemma eigenvalue_le_one (ρ : DensityMatrix n) (i : n) :
    ρ.isHermitian.eigenvalues i ≤ 1 := by
  have hsum := ρ.sum_eigenvalues
  calc ρ.isHermitian.eigenvalues i
      ≤ ∑ j, ρ.isHermitian.eigenvalues j := Finset.single_le_sum
          (fun j _ => ρ.eigenvalues_nonneg j) (Finset.mem_univ i)
    _ = 1 := hsum

/-- Coercion from `DensityMatrix` to `Matrix n n ℂ`. -/
instance : Coe (DensityMatrix n) (Matrix n n ℂ) where
  coe := DensityMatrix.toMatrix

@[simp] theorem coe_eq_toMatrix (ρ : DensityMatrix n) : (↑ρ : Matrix n n ℂ) = ρ.toMatrix := rfl

/-- Density matrix times a complex matrix (coercion on the left). -/
noncomputable instance : HMul (DensityMatrix n) (Matrix n n ℂ) (Matrix n n ℂ) where
  hMul ρ A := ρ.toMatrix * A

@[simp] theorem densityMatrix_hmul_eq (ρ : DensityMatrix n) (A : Matrix n n ℂ) :
    ρ * A = ρ.toMatrix * A := rfl

/-- Real-power of a density matrix, delegated to matrix rpow. -/
noncomputable instance : HPow (DensityMatrix n) ℝ (Matrix n n ℂ) where
  hPow ρ s := ρ.toMatrix ^ s

theorem densityMatrix_hpow_eq (ρ : DensityMatrix n) (s : ℝ) :
    ρ ^ s = ρ.toMatrix ^ s := rfl

/-- Matrix logarithm of a density matrix: `log ρ = U diag(log λᵢ) U*`.
    Computed via the spectral decomposition of `ρ`. -/
noncomputable def log (ρ : DensityMatrix n) :
    Matrix n n ℂ :=
  matrixLog ↑ρ ρ.isHermitian

/-- The product `ρ * log ρ` is Hermitian.
Both factors are Hermitian and commute because `log ρ` is a matrix function of `ρ`. -/
lemma mul_log_isHermitian (ρ : DensityMatrix n) :
    (ρ.toMatrix * log ρ).IsHermitian := by
  simpa [DensityMatrix.log] using
    (mul_matrixFunction_isHermitian ρ.isHermitian Real.log)

/-- Convex combination of two density matrices is a density matrix. -/
noncomputable def mix (ρ₁ ρ₂ : DensityMatrix n)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : DensityMatrix n where
  toMatrix := p • ↑ρ₁ + (1 - p) • ↑ρ₂
  posSemidef := by
    apply Matrix.PosSemidef.add
    · exact ρ₁.posSemidef.smul (by exact_mod_cast hp)
    · exact ρ₂.posSemidef.smul (by exact_mod_cast (sub_nonneg.mpr hp1))
  trace_eq_one := by
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
        ρ₁.trace_eq_one, ρ₂.trace_eq_one, Algebra.smul_def, Algebra.smul_def, mul_one, mul_one]
    push_cast
    ring

@[simp] theorem mix_toMatrix (ρ₁ ρ₂ : DensityMatrix n)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ↑(mix ρ₁ ρ₂ p hp hp1) = p • (↑ρ₁ : Matrix n n ℂ) + (1 - p) • ↑ρ₂ := rfl

end DensityMatrix

namespace QuantumInfo
scoped prefix:max "log " => DensityMatrix.log
end QuantumInfo

end Matrix
