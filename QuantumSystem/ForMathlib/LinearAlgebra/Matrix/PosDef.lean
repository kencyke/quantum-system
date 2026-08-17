module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Positive semidefinite matrix lemmas

This file collects small positive-semidefinite matrix lemmas that are candidates for Mathlib.
-/

@[expose] public section

namespace Matrix

open scoped ComplexOrder

/-- A nonnegative real multiple of a positive semidefinite matrix is positive semidefinite. -/
lemma posSemidef_smul_nonneg {n : Type*} [Finite n] {c : ℝ} (hc : 0 ≤ c)
    {M : Matrix n n ℂ} (hM : M.PosSemidef) : (c • M).PosSemidef := by
  classical
  have : Fintype n := Fintype.ofFinite n
  suffices h' : (((c : ℝ) : ℂ) • M).PosSemidef by rwa [Complex.coe_smul] at h'
  have key : ((c : ℝ) : ℂ) • M = (((Real.sqrt c : ℝ) : ℂ) • (1 : Matrix n n ℂ)) * M
      * (((Real.sqrt c : ℝ) : ℂ) • (1 : Matrix n n ℂ))ᴴ := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Complex.star_def, Complex.conj_ofReal,
      smul_mul_assoc, Matrix.one_mul, smul_mul_assoc, mul_smul_comm, Matrix.mul_one, smul_smul,
      ← Complex.ofReal_mul, Real.mul_self_sqrt hc]
  rw [key]
  exact hM.mul_mul_conjTranspose_same _

end Matrix
