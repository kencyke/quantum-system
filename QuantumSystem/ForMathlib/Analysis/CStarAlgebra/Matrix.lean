/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Matrices as operators on Euclidean space

Mathlib's star algebra isomorphism `Matrix.toEuclideanCLM : M_n(𝕜) ≃⋆ₐ B(𝕜ⁿ)` reads a square
matrix as an operator on `EuclideanSpace 𝕜 n`. This file computes it on matrix units and on
conjugations by rectangular matrices.

## Main statements

* `Matrix.toEuclideanCLM_single`: the matrix unit `Eᵢⱼ` is the rank-one operator `|eᵢ⟩⟨eⱼ|`.
* `Matrix.toEuclideanCLM_mul_mul_conjTranspose`: for `K : Matrix m n 𝕜`, the operator of `K A Kᴴ`
  is `K' A' K'†`, where `K' : 𝕜ⁿ →L 𝕜ᵐ` is the operator of `K`.
-/

@[expose] public section

open InnerProductSpace

namespace Matrix

variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The matrix unit `Eᵢⱼ` is the rank-one operator `|eᵢ⟩⟨eⱼ|` on `EuclideanSpace 𝕜 n`. -/
lemma toEuclideanCLM_single (i j : n) :
    toEuclideanCLM (n := n) (𝕜 := 𝕜) (single i j 1) =
      rankOne 𝕜 (EuclideanSpace.single i (1 : 𝕜)) (EuclideanSpace.single j (1 : 𝕜)) := by
  ext x k
  simp [rankOne_apply, mulVec, dotProduct, single_apply, EuclideanSpace.inner_single_left, ite_and,
    eq_comm]

/-- Conjugation by a rectangular matrix `K : Matrix m n 𝕜` is conjugation by its operator
`K' : 𝕜ⁿ →L 𝕜ᵐ`: the operator of `K A Kᴴ` is `K' A' K'†`, since `Kᴴ` is the matrix of `K'†`
(`Matrix.toEuclideanLin_conjTranspose_eq_adjoint`). -/
lemma toEuclideanCLM_mul_mul_conjTranspose (K : Matrix m n 𝕜) (A : Matrix n n 𝕜) :
    toEuclideanCLM (n := m) (𝕜 := 𝕜) (K * A * Kᴴ) =
      LinearMap.toContinuousLinearMap (toEuclideanLin K) ∘L toEuclideanCLM (n := n) (𝕜 := 𝕜) A ∘L
        ContinuousLinearMap.adjoint (LinearMap.toContinuousLinearMap (toEuclideanLin K)) := by
  refine ContinuousLinearMap.coe_injective ?_
  rw [coe_toEuclideanCLM_eq_toEuclideanLin, ContinuousLinearMap.toLinearMap_comp,
    ContinuousLinearMap.toLinearMap_comp, ← LinearMap.adjoint_toContinuousLinearMap,
    LinearMap.coe_toContinuousLinearMap, LinearMap.coe_toContinuousLinearMap,
    coe_toEuclideanCLM_eq_toEuclideanLin, ← toEuclideanLin_conjTranspose_eq_adjoint]
  simp [toEuclideanLin, toLpLin_mul (q := 2), LinearMap.comp_assoc]

end Matrix
