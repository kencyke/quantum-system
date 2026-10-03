/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.Matrix.PosDef

/-!
# Hermitian Matrices

This file collects basic lemmas about Hermitian and positive semidefinite matrices over `ℂ`; the
rank-one decompositions of the last section, and the nonnegativity of `Tr (A B)` for positive
semidefinite `A` and `B` derived from them, are over any `RCLike` field.

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
- `IsHermitian.eq_sum_eigenvalues_smul_vecMulVec`: the spectral decomposition
  `A = Σⱼ λⱼ uⱼ uⱼᴴ` of a Hermitian matrix.
- `posSemidef_iff_dotProduct_mulVec_complex`: over `ℂ` a matrix is positive semidefinite
  iff its quadratic form is nonnegative; the Hermitian condition is automatic.
- `PosSemidef.exists_eq_sum_vecMulVec_rank`: a positive semidefinite matrix is a sum of
  `rank M` rank-one matrices `vᵢ vᵢᴴ`.
- `PosSemidef.trace_mul_nonneg`: the trace of a product of two positive semidefinite matrices is
  nonnegative.
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

section QuadraticForm

open scoped ComplexOrder

variable {n : Type*} [Fintype n]

/-- Over `ℂ` a matrix is positive semidefinite iff its quadratic form is nonnegative: a
nonnegative, in particular real, quadratic form `v ↦ vᴴ A v` forces `A` to be Hermitian. -/
lemma posSemidef_iff_dotProduct_mulVec_complex {A : Matrix n n ℂ} :
    A.PosSemidef ↔ ∀ x, 0 ≤ star x ⬝ᵥ (A *ᵥ x) := by
  refine ⟨fun h => h.dotProduct_mulVec_nonneg, fun h => .of_dotProduct_mulVec_nonneg ?_ h⟩
  classical
  rw [← isSymmetric_toEuclideanLin_iff, LinearMap.isSymmetric_iff_inner_map_self_real]
  intro v
  rw [EuclideanSpace.inner_eq_star_dotProduct, Complex.conj_eq_iff_im, dotProduct_star,
    Complex.star_def, Complex.conj_im, neg_eq_zero]
  simpa [toEuclideanLin, dotProduct_comm] using (Complex.nonneg_iff.mp (h (WithLp.ofLp v))).2.symm

end QuadraticForm

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

end Eigenbasis

section RankOne

open scoped ComplexOrder

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

/-- **Spectral decomposition** of a Hermitian matrix as a sum of rank-one matrices:
`A = Σⱼ λⱼ uⱼ uⱼᴴ`, with `uⱼ` the eigenvector basis and `λⱼ` the eigenvalues. -/
theorem IsHermitian.eq_sum_eigenvalues_smul_vecMulVec [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) :
    A = ∑ j, hA.eigenvalues j •
      vecMulVec ⇑(hA.eigenvectorBasis j) (star ⇑(hA.eigenvectorBasis j)) := by
  conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
  ext a b
  simp only [mul_apply, diagonal_apply, Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply,
    star_apply, Function.comp_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, eigenvectorUnitary_apply, Pi.star_apply, RCLike.real_smul_eq_coe_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- A positive semidefinite matrix is a sum of `rank M` rank-one matrices: `M = Σᵢ vᵢ vᵢᴴ` with
`i` ranging over `Fin (rank M)`. The vectors are `vⱼ = √λⱼ uⱼ` for the nonzero eigenvalues `λⱼ`.
Compare `Matrix.posSemidef_iff_eq_sum_vecMulVec`, which does not bound the number of terms. -/
theorem PosSemidef.exists_eq_sum_vecMulVec_rank {M : Matrix n n 𝕜} (hM : M.PosSemidef) :
    ∃ v : Fin M.rank → n → 𝕜, M = ∑ i, vecMulVec (v i) (star (v i)) := by
  classical
  set hA := hM.isHermitian
  let w : n → n → 𝕜 := fun j => ((√(hA.eigenvalues j) : ℝ) : 𝕜) • ⇑(hA.eigenvectorBasis j)
  have hw (j : n) : vecMulVec (w j) (star (w j)) = hA.eigenvalues j •
      vecMulVec ⇑(hA.eigenvectorBasis j) (star ⇑(hA.eigenvectorBasis j)) := by
    have h : ((√(hA.eigenvalues j) : ℝ) : 𝕜) * ((√(hA.eigenvalues j) : ℝ) : 𝕜) =
        (hA.eigenvalues j : 𝕜) := by exact_mod_cast Real.mul_self_sqrt (hM.eigenvalues_nonneg j)
    ext a b
    simp only [w, vecMulVec_apply, Pi.smul_apply, Pi.star_apply, star_smul, smul_eq_mul,
      Matrix.smul_apply, RCLike.real_smul_eq_coe_mul, RCLike.star_def, RCLike.conj_ofReal]
    linear_combination
      (⇑(hA.eigenvectorBasis j) a * (starRingEnd 𝕜) (⇑(hA.eigenvectorBasis j) b)) * h
  have hw0 (j : n) (hj : ¬hA.eigenvalues j ≠ 0) : vecMulVec (w j) (star (w j)) = 0 := by
    rw [hw, not_not.mp hj, zero_smul]
  let e : Fin M.rank ≃ {j // hA.eigenvalues j ≠ 0} :=
    (Fintype.equivFinOfCardEq hA.rank_eq_card_non_zero_eigs.symm).symm
  refine ⟨fun i => w (e i), ?_⟩
  rw [e.sum_comp (fun s => vecMulVec (w s.1) (star (w s.1))),
    ← Finset.sum_subtype (Finset.univ.filter fun j => hA.eigenvalues j ≠ 0) (fun j => by simp)
      (fun j => vecMulVec (w j) (star (w j))),
    Finset.sum_filter_of_ne (fun j _ h => by_contra fun hj => h (hw0 j hj))]
  conv_lhs => rw [hA.eq_sum_eigenvalues_smul_vecMulVec]
  exact Finset.sum_congr rfl fun j _ => (hw j).symm

/-- The trace of a product of two positive semidefinite matrices is nonnegative: writing
`B = Σᵢ vᵢ vᵢᴴ`, it is `Σᵢ vᵢᴴ A vᵢ`. -/
lemma PosSemidef.trace_mul_nonneg {A B : Matrix n n 𝕜} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace := by
  obtain ⟨v, hv⟩ := hB.exists_eq_sum_vecMulVec_rank
  rw [hv, Matrix.mul_sum, trace_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [mul_vecMulVec, trace_vecMulVec, dotProduct_comm]
  exact hA.dotProduct_mulVec_nonneg (v i)

end RankOne

end Matrix
