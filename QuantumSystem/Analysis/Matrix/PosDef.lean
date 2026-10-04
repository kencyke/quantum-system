/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
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
lemma PosDef.convex_comb {m : Type*} [Finite m]
    {A B : Matrix m m ℂ} (hA : A.PosDef) (hB : B.PosDef)
    {t : ℝ} (ht0 : 0 < t) (ht1 : 0 < 1 - t) :
    (t • A + (1 - t) • B).PosDef := by
  let := Fintype.ofFinite m
  exact (hA.smul ht0).add (hB.smul ht1)

/-- Convex combination of PD matrices with nonnegative weights is PD. -/
lemma PosDef.convex_comb_nonneg {m : Type*} [Finite m]
    {A B : Matrix m m ℂ} (hA : A.PosDef) (hB : B.PosDef)
    {w₁ w₂ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hw : w₁ + w₂ = 1) :
    (w₁ • A + w₂ • B).PosDef := by
  by_cases h₁ : w₁ = 0
  · have h₂ : w₂ = 1 := by linarith [hw, h₁]
    subst h₁
    subst h₂
    convert hB using 1
    module
  by_cases h₂ : w₂ = 0
  · have h₁' : w₁ = 1 := by linarith [hw, h₂]
    subst h₂
    subst h₁'
    convert hA using 1
    module
  have hw₁pos : 0 < w₁ := lt_of_le_of_ne hw₁ (Ne.symm h₁)
  have hw₂pos : 0 < w₂ := lt_of_le_of_ne hw₂ (Ne.symm h₂)
  have hw₂' : w₂ = 1 - w₁ := by linarith [hw]
  have h1t : 0 < 1 - w₁ := by
    simpa [hw₂'] using hw₂pos
  simpa [hw₂'] using (PosDef.convex_comb (A := A) (B := B) hA hB hw₁pos h1t)

end Matrix
