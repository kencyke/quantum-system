/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Hermitian Matrices

This file collects basic lemmas about Hermitian matrices over `ℂ`.

## Main results

- `IsHermitian.quadForm_im_eq_zero`: the quadratic form v†Av is real for a Hermitian
  matrix A.
- `IsHermitian.add_isHermitian`: the sum of two Hermitian matrices is Hermitian.
- `IsHermitian.smul_real`: a real scalar multiple of a Hermitian matrix is Hermitian.
- `IsHermitian.convex_combination`: a convex combination of Hermitian matrices is Hermitian.
- `IsHermitian.diagonal_real`: a diagonal matrix with real entries is Hermitian.
- `IsHermitian.smul_complex_real`: multiplication by a real scalar (viewed in `ℂ`) preserves
  Hermiticity.
- `IsHermitian.toEuclideanCLM_eigenvectorBasis`: an eigenvector of a Hermitian matrix is an
  eigenvector of the operator it defines on `ℂⁿ`.
- `PosSemidef.trace_mul_eq_sum_inner`: `Tr (ρ A) = Σᵢ rᵢ ⟪fᵢ, A fᵢ⟫` in the eigenvector basis of a
  positive semidefinite `ρ`.
-/
@[expose] public section

namespace Matrix

/-- For a Hermitian matrix A, the quadratic form v†Av is real. -/
lemma IsHermitian.quadForm_im_eq_zero {m : Type*} [Fintype m]
    {A : Matrix m m ℂ} (hA : A.IsHermitian) (v : m → ℂ) :
    (star v ⬝ᵥ A *ᵥ v).im = 0 := by
  have h : star (star v ⬝ᵥ A *ᵥ v) = star v ⬝ᵥ A *ᵥ v := by
    simp only [dotProduct, mulVec, star_sum, star_mul']
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    have hAij : star (A i j) = A j i := by
      have h := congrFun (congrFun hA j) i
      simp only [conjTranspose_apply] at h
      exact h
    simp_rw [hAij, Pi.star_apply, star_star]
    ring
  have him : -(star v ⬝ᵥ A *ᵥ v).im = (star v ⬝ᵥ A *ᵥ v).im := by
    have := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at this
    exact this
  linarith

/-- Sum of Hermitian matrices is Hermitian. -/
lemma IsHermitian.add_isHermitian {m : Type*}
    {A B : Matrix m m ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A + B).IsHermitian :=
  hA.add hB

/-- Real scalar multiple of a Hermitian matrix is Hermitian. -/
lemma IsHermitian.smul_real {m : Type*}
    {A : Matrix m m ℂ} (hA : A.IsHermitian) (r : ℝ) :
    (r • A).IsHermitian := by
  unfold IsHermitian at *
  rw [conjTranspose_smul, hA]
  simp only [RCLike.star_def, RCLike.conj_to_real]

/-- Convex combination of Hermitian matrices is Hermitian. -/
lemma IsHermitian.convex_combination {m : Type*}
    {A B : Matrix m m ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (t : ℝ) :
    (t • A + (1 - t) • B).IsHermitian :=
  (hA.smul_real t).add (hB.smul_real (1 - t))

/-- Diagonal matrix with real entries is Hermitian. -/
lemma IsHermitian.diagonal_real {m : Type*} [DecidableEq m]
    (f : m → ℝ) : (diagonal (fun i => (f i : ℂ))).IsHermitian := by
  rw [IsHermitian, diagonal_conjTranspose]
  ext i j
  simp only [diagonal_apply]
  split_ifs with h
  · simp [RCLike.star_def, Complex.conj_ofReal]
  · rfl

/-- Complex scalar multiple of a Hermitian matrix is Hermitian when the scalar is real. -/
lemma IsHermitian.smul_complex_real {m : Type*}
    {A : Matrix m m ℂ} (hA : A.IsHermitian) (r : ℝ) :
    ((r : ℂ) • A).IsHermitian := by
  unfold IsHermitian at *
  rw [conjTranspose_smul, hA]
  simp only [RCLike.star_def, Complex.conj_ofReal]

section Eigenbasis

open scoped InnerProductSpace ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An eigenvector of a Hermitian matrix is an eigenvector of the operator it defines on `ℂⁿ`. -/
lemma IsHermitian.toEuclideanCLM_eigenvectorBasis {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (i : n) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) A (hA.eigenvectorBasis i) =
      ((hA.eigenvalues i : ℝ) : ℂ) • hA.eigenvectorBasis i := by
  refine PiLp.ext fun k => ?_
  have := congrFun (hA.mulVec_eigenvectorBasis i) k
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)] at this
  exact this

variable {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef)

/-- `Tr (ρ A) = Σᵢ rᵢ ⟪fᵢ, A fᵢ⟫` in the eigenvector basis of `ρ`. -/
lemma PosSemidef.trace_mul_eq_sum_inner (A : Matrix n n ℂ) :
    Matrix.trace (ρ * A) = ∑ i, ((hρ.1.eigenvalues i : ℝ) : ℂ) *
      ⟪hρ.1.eigenvectorBasis i,
        Matrix.toEuclideanCLM (𝕜 := ℂ) A (hρ.1.eigenvectorBasis i)⟫_ℂ := by
  have h : Matrix.trace (ρ * A) =
      LinearMap.trace ℂ _ (Matrix.toEuclideanLin (ρ * A)) := by
    rw [LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun n ℂ).toBasis,
      Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]
  rw [h, LinearMap.trace_eq_sum_inner _ hρ.1.eigenvectorBasis]
  refine Finset.sum_congr rfl fun i _ => ?_
  change ⟪_, Matrix.toEuclideanCLM (𝕜 := ℂ) (ρ * A) _⟫_ℂ = _
  rw [map_mul]
  calc _ = ⟪Matrix.toEuclideanCLM (𝕜 := ℂ) ρ (hρ.1.eigenvectorBasis i),
        Matrix.toEuclideanCLM (𝕜 := ℂ) A (hρ.1.eigenvectorBasis i)⟫_ℂ :=
        (Matrix.isSymmetric_toEuclideanLin_iff.mpr hρ.1 _ _).symm
    _ = _ := by
      rw [hρ.1.toEuclideanCLM_eigenvectorBasis, inner_smul_left, Complex.conj_ofReal]

end Eigenbasis

end Matrix
