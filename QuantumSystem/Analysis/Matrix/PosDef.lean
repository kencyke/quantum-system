module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import QuantumSystem.ForMathlib.Analysis.Matrix.Hermitian

/-!
# Positive Definite Matrix Lemmas

This file collects basic results about positive definite (PD) matrices over ℂ
used in convexity arguments.

## Main results

- `Matrix.PosDef.convex_comb`: a strictly convex combination tA + (1-t)B of PD matrices
  is PD for 0 < t < 1.
- `Matrix.PosDef.convex_comb_nonneg`: same with nonneg weights w₁ + w₂ = 1.
-/
@[expose] public section

namespace Matrix

open scoped ComplexOrder

/-- A strictly positive convex combination of positive definite matrices is positive definite. -/
lemma PosDef.convex_comb {m : Type*} [Fintype m]
    {A B : Matrix m m ℂ} (hA : A.PosDef) (hB : B.PosDef)
    {t : ℝ} (ht0 : 0 < t) (ht1 : 0 < 1 - t) :
    (t • A + (1 - t) • B).PosDef := by
  classical
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · exact (hA.1.smul_real t).add (hB.1.smul_real (1 - t))
  · intro x hx
    have hApos := hA.dotProduct_mulVec_pos hx
    have hBpos := hB.dotProduct_mulVec_pos hx
    have hA_re : 0 < (star x ⬝ᵥ (A *ᵥ x)).re := (RCLike.pos_iff.mp hApos).1
    have hB_re : 0 < (star x ⬝ᵥ (B *ᵥ x)).re := (RCLike.pos_iff.mp hBpos).1
    have hC_im : (star x ⬝ᵥ ((t • A + (1 - t) • B) *ᵥ x)).im = 0 := by
      exact (hA.1.smul_real t).add (hB.1.smul_real (1 - t)) |>.quadForm_im_eq_zero x
    have hC_re :
        (star x ⬝ᵥ ((t • A + (1 - t) • B) *ᵥ x)).re =
          t * (star x ⬝ᵥ (A *ᵥ x)).re + (1 - t) * (star x ⬝ᵥ (B *ᵥ x)).re := by
      simp [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul,
        Complex.add_re, Complex.real_smul]
    refine (RCLike.pos_iff).2 ?_
    constructor
    · have hA' : 0 < t * (star x ⬝ᵥ (A *ᵥ x)).re := by
        exact mul_pos ht0 hA_re
      have hB' : 0 < (1 - t) * (star x ⬝ᵥ (B *ᵥ x)).re := by
        exact mul_pos ht1 hB_re
      have hsum : 0 < t * (star x ⬝ᵥ (A *ᵥ x)).re + (1 - t) * (star x ⬝ᵥ (B *ᵥ x)).re :=
        add_pos hA' hB'
      simpa [hC_re] using hsum
    · exact hC_im

/-- Convex combination of PD matrices with nonnegative weights is PD. -/
lemma PosDef.convex_comb_nonneg {m : Type*} [Fintype m]
    {A B : Matrix m m ℂ} (hA : A.PosDef) (hB : B.PosDef)
    {w₁ w₂ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hw : w₁ + w₂ = 1) :
    (w₁ • A + w₂ • B).PosDef := by
  by_cases h₁ : w₁ = 0
  · have h₂ : w₂ = 1 := by linarith [hw, h₁]
    subst h₁
    subst h₂
    simpa using hB
  by_cases h₂ : w₂ = 0
  · have h₁' : w₁ = 1 := by linarith [hw, h₂]
    subst h₂
    subst h₁'
    simpa using hA
  have hw₁pos : 0 < w₁ := lt_of_le_of_ne hw₁ (Ne.symm h₁)
  have hw₂pos : 0 < w₂ := lt_of_le_of_ne hw₂ (Ne.symm h₂)
  have hw₂' : w₂ = 1 - w₁ := by linarith [hw]
  have h1t : 0 < 1 - w₁ := by
    simpa [hw₂'] using hw₂pos
  simpa [hw₂'] using (PosDef.convex_comb (A := A) (B := B) hA hB hw₁pos h1t)

end Matrix
