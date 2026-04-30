module

public import QuantumSystem.Analysis.Matrix.HermitianFunctionalCalculus
public import QuantumSystem.ForMathlib.LinearAlgebra.Matrix.StarAlgEquiv
public import QuantumSystem.ForMathlib.Analysis.Complex.Basic
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
calculus (CFC), applied to each matrix's own spectral decomposition. This is the
operator-algebraically correct definition, including the non-commuting case.

## References

* Nielsen, Chuang, *Quantum Computation and Quantum Information*
-/

@[expose] public section

open Matrix
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

/-- Transport a density matrix along a trace-preserving `*-`algebra equivalence.

This is the abstract notion of "unitary equivalence" of density matrices in the
quantum-information sense. -/
noncomputable def map {m : Type*} [Fintype m] [DecidableEq m]
    (ρ : DensityMatrix n) (φ : Matrix n n ℂ ≃⋆ₐ[ℂ] Matrix m m ℂ)
    (hφ : ∀ A, (φ A).trace = A.trace) : DensityMatrix m where
  toMatrix := φ ρ.toMatrix
  posSemidef := ρ.posSemidef.map_starAlgEquiv φ
  trace_eq_one := by rw [hφ]; exact ρ.trace_eq_one

@[simp] lemma map_toMatrix {m : Type*} [Fintype m] [DecidableEq m]
    (ρ : DensityMatrix n) (φ : Matrix n n ℂ ≃⋆ₐ[ℂ] Matrix m m ℂ)
    (hφ : ∀ A, (φ A).trace = A.trace) :
    (ρ.map φ hφ).toMatrix = φ ρ.toMatrix := rfl

/-- `DensityMatrix` reindex via an index equivalence — built on `DensityMatrix.map`. -/
noncomputable def mapEquiv {m : Type*} [Fintype m] [DecidableEq m]
    (ρ : DensityMatrix n) (e : m ≃ n) : DensityMatrix m :=
  ρ.map (Matrix.reindexStarAlgEquiv (R := ℂ) e.symm)
    (Matrix.trace_reindexStarAlgEquiv e.symm)

@[simp] lemma mapEquiv_toMatrix {m : Type*} [Fintype m] [DecidableEq m]
    (ρ : DensityMatrix n) (e : m ≃ n) :
    (ρ.mapEquiv e).toMatrix = ρ.toMatrix.submatrix e e := by
  unfold mapEquiv
  rfl

/-! ### Maximally mixed state

The uniform state `π = I/d` is the unique state whose entropy attains the
maximum `log d`. -/

section MaximallyMixed

variable [Nonempty n]

omit [DecidableEq n] in
/-- `(Fintype.card n : ℂ)⁻¹` has positive real part. -/
private lemma card_inv_re_pos : (0 : ℝ) < ((Fintype.card n : ℂ)⁻¹).re := by
  simp only [Complex.inv_re, Complex.natCast_re, Complex.normSq_natCast]
  have hd : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos (α := n)
  positivity

omit [DecidableEq n] [Nonempty n] in
/-- `(Fintype.card n : ℂ)⁻¹` as a complex number equals its real part (it's real-valued). -/
private lemma card_inv_eq_re_ofReal :
    ((Fintype.card n : ℂ)⁻¹) = (((Fintype.card n : ℂ)⁻¹).re : ℂ) := by
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im, Complex.inv_im, Complex.natCast_im, neg_zero, zero_div]

/-- The **maximally-mixed (uniform) state** on a finite-dimensional system:
`π = I / d` where `d = Fintype.card n`. -/
noncomputable def maximallyMixed : DensityMatrix n where
  toMatrix := ((Fintype.card n : ℂ)⁻¹) • (1 : Matrix n n ℂ)
  posSemidef := PosSemidef.smul Matrix.PosSemidef.one (Complex.zero_le_natCast_inv _)
  trace_eq_one := by
    rw [Matrix.trace_smul, Matrix.trace_one]
    have hd : (Fintype.card n : ℂ) ≠ 0 := by
      exact_mod_cast (Fintype.card_pos (α := n)).ne'
    rw [smul_eq_mul, inv_mul_cancel₀ hd]

@[simp] lemma maximallyMixed_toMatrix :
    (maximallyMixed (n := n)).toMatrix = ((Fintype.card n : ℂ)⁻¹) • (1 : Matrix n n ℂ) := rfl

/-- The maximally-mixed state is positive definite. -/
theorem maximallyMixed_posDef : (maximallyMixed (n := n)).toMatrix.PosDef := by
  rw [maximallyMixed_toMatrix]
  have hzero : (0 : Matrix n n ℂ).PosSemidef := Matrix.PosSemidef.zero
  have hreg := PosSemidef.add_smul_one_posDef hzero (card_inv_re_pos (n := n))
  rw [zero_add] at hreg
  rwa [card_inv_eq_re_ofReal]

/-! ### Regularization

The convex mixture `(1 - ε) ρ + ε π` is the standard regularization. For `ε > 0`,
the result is positive definite (since `π` is). -/

/-- **Regularization of a density matrix**: `ρ_ε := (1-ε) ρ + ε π`,
where `π = I/d` is the maximally-mixed state. For `ε ∈ [0, 1]` this is a valid
density matrix; for `ε > 0` it is PosDef. -/
noncomputable def regularize (ρ : DensityMatrix n) {ε : ℝ}
    (hε : 0 ≤ ε) (hε' : ε ≤ 1) : DensityMatrix n where
  toMatrix := (1 - (ε : ℂ)) • ρ.toMatrix + (ε : ℂ) • (maximallyMixed (n := n)).toMatrix
  posSemidef :=
    PosSemidef.add
      (PosSemidef.smul ρ.posSemidef (Complex.zero_le_one_sub_ofReal hε'))
      (PosSemidef.smul maximallyMixed_posDef.posSemidef (Complex.zero_le_ofReal hε))
  trace_eq_one := by
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, ρ.trace_eq_one,
      maximallyMixed.trace_eq_one]
    rw [smul_eq_mul, smul_eq_mul, mul_one, mul_one]
    ring

@[simp] lemma regularize_toMatrix (ρ : DensityMatrix n) {ε : ℝ}
    (hε : 0 ≤ ε) (hε' : ε ≤ 1) :
    (regularize ρ hε hε').toMatrix =
      (1 - (ε : ℂ)) • ρ.toMatrix + (ε : ℂ) • (maximallyMixed (n := n)).toMatrix := rfl

/-- **The regularization is positive definite** for any `ε > 0`. -/
theorem regularize_posDef (ρ : DensityMatrix n) {ε : ℝ}
    (hε : 0 < ε) (hε' : ε ≤ 1) :
    (regularize ρ hε.le hε').toMatrix.PosDef := by
  rw [regularize_toMatrix]
  have h_psd : ((1 - (ε : ℂ)) • ρ.toMatrix).PosSemidef :=
    PosSemidef.smul ρ.posSemidef (Complex.zero_le_one_sub_ofReal hε')
  have h_unfold : (ε : ℂ) • (maximallyMixed (n := n)).toMatrix =
      ((ε / Fintype.card n : ℝ) : ℂ) • (1 : Matrix n n ℂ) := by
    rw [maximallyMixed_toMatrix, smul_smul]
    push_cast
    rw [div_eq_mul_inv]
  rw [h_unfold]
  exact PosSemidef.add_smul_one_posDef h_psd
    (by have hd_pos : (0 : ℝ) < Fintype.card n := by
          exact_mod_cast Fintype.card_pos (α := n)
        positivity)

/-- The regularization is also Hermitian. -/
lemma regularize_isHermitian (ρ : DensityMatrix n) {ε : ℝ}
    (hε : 0 ≤ ε) (hε' : ε ≤ 1) :
    (regularize ρ hε hε').toMatrix.IsHermitian :=
  (regularize ρ hε hε').posSemidef.1

/-- At `ε = 0`, the regularization equals the original. -/
@[simp] lemma regularize_zero (ρ : DensityMatrix n) :
    regularize ρ (le_refl 0) zero_le_one = ρ := by
  apply DensityMatrix.ext
  rw [regularize_toMatrix]
  simp

/-- At `ε = 1`, the regularization equals the maximally-mixed state. -/
@[simp] lemma regularize_one (ρ : DensityMatrix n) :
    regularize ρ zero_le_one (le_refl 1) = maximallyMixed := by
  apply DensityMatrix.ext
  rw [regularize_toMatrix]
  simp

/-! ### Spectral identity for `regularize`

The regularization expressed as `cfc` applied to ρ:
`regularize ρ ε.toMatrix = cfc (fun x => (1-ε) * x + ε/d) ρ.toMatrix`. -/

/-- The regularization expressed as `cfc` applied to ρ. -/
theorem regularize_eq_cfc (ρ : DensityMatrix n) {ε : ℝ}
    (hε : 0 ≤ ε) (hε' : ε ≤ 1) :
    (regularize ρ hε hε').toMatrix =
      cfc (fun x : ℝ => (1 - ε) * x + ε / Fintype.card n) ρ.toMatrix := by
  have hρ_sa : IsSelfAdjoint ρ.toMatrix := ρ.isHermitian
  rw [cfc_add (R := ℝ) (fun x => (1 - ε) * x) (fun _ => ε / (Fintype.card n : ℝ))
      (a := ρ.toMatrix) (by fun_prop) (by fun_prop),
      cfc_const_mul (R := ℝ) (1 - ε) (fun x : ℝ => x) ρ.toMatrix (by fun_prop),
      cfc_id' (R := ℝ) ρ.toMatrix,
      cfc_const (R := ℝ) (ε / (Fintype.card n : ℝ)) ρ.toMatrix,
      Algebra.algebraMap_eq_smul_one]
  rw [regularize_toMatrix, maximallyMixed_toMatrix, smul_smul]
  have h1 : (1 - (ε : ℂ)) • ρ.toMatrix = (1 - ε : ℝ) • ρ.toMatrix := by
    rw [show (1 - (ε : ℂ)) = ((1 - ε : ℝ) : ℂ) from by push_cast; ring]
    exact algebraMap_smul ℂ (1 - ε : ℝ) ρ.toMatrix
  have h2 : ((ε : ℂ) * (Fintype.card n : ℂ)⁻¹) • (1 : Matrix n n ℂ) =
            (ε / (Fintype.card n : ℝ) : ℝ) • (1 : Matrix n n ℂ) := by
    rw [show ((ε : ℂ) * (Fintype.card n : ℂ)⁻¹) = ((ε / (Fintype.card n : ℝ) : ℝ) : ℂ) from by
        push_cast; rw [div_eq_mul_inv]]
    exact algebraMap_smul ℂ (ε / Fintype.card n : ℝ) 1
  rw [h1, h2]

/-! ### Reindex compatibility

The regularization commutes with `mapEquiv`. -/

/-- For an `Equiv e : n ≃ m`, the regularization commutes with `mapEquiv`. -/
theorem regularize_mapEquiv {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
    (ρ : DensityMatrix m) (e : n ≃ m) {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1) :
    regularize (mapEquiv ρ e) hε hε' = mapEquiv (regularize ρ hε hε') e := by
  apply DensityMatrix.ext
  rw [mapEquiv_toMatrix, regularize_toMatrix, regularize_toMatrix,
      mapEquiv_toMatrix, maximallyMixed_toMatrix, maximallyMixed_toMatrix]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.submatrix_apply, Matrix.one_apply,
    Function.Injective.eq_iff e.injective]
  have h_card : (Fintype.card n : ℂ) = (Fintype.card m : ℂ) := by
    exact_mod_cast Fintype.card_congr e
  rw [h_card]

end MaximallyMixed

end DensityMatrix

namespace Matrix.QuantumInfo
scoped prefix:max "log " => DensityMatrix.log
end Matrix.QuantumInfo
