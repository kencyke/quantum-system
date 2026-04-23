module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.Matrix.Hermitian

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
lemma IsHermitian.add_isHermitian {m : Type*} [Fintype m]
    {A B : Matrix m m ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A + B).IsHermitian :=
  hA.add hB

/-- Real scalar multiple of a Hermitian matrix is Hermitian. -/
lemma IsHermitian.smul_real {m : Type*} [Fintype m]
    {A : Matrix m m ℂ} (hA : A.IsHermitian) (r : ℝ) :
    (r • A).IsHermitian := by
  unfold IsHermitian at *
  rw [conjTranspose_smul, hA]
  simp only [RCLike.star_def, RCLike.conj_to_real]

/-- Convex combination of Hermitian matrices is Hermitian. -/
lemma IsHermitian.convex_combination {m : Type*} [Fintype m]
    {A B : Matrix m m ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (t : ℝ) :
    (t • A + (1 - t) • B).IsHermitian :=
  (hA.smul_real t).add (hB.smul_real (1 - t))

/-- Diagonal matrix with real entries is Hermitian. -/
lemma IsHermitian.diagonal_real {m : Type*} [Fintype m] [DecidableEq m]
    (f : m → ℝ) : (diagonal (fun i => (f i : ℂ))).IsHermitian := by
  rw [IsHermitian, diagonal_conjTranspose]
  ext i j
  simp only [diagonal_apply]
  split_ifs with h
  · simp [RCLike.star_def, Complex.conj_ofReal]
  · rfl

/-- Complex scalar multiple of a Hermitian matrix is Hermitian when the scalar is real. -/
lemma IsHermitian.smul_complex_real {m : Type*} [Fintype m]
    {A : Matrix m m ℂ} (hA : A.IsHermitian) (r : ℝ) :
    ((r : ℂ) • A).IsHermitian := by
  unfold IsHermitian at *
  rw [conjTranspose_smul, hA]
  simp only [RCLike.star_def, Complex.conj_ofReal]

end Matrix
