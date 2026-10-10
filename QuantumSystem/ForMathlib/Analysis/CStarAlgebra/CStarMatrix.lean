/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.Matrix.Order

/-!
# Flattening block matrices and their positivity

Flattening a `k × k` block matrix with entries in `Matrix n n R`, `Matrix.comp`, is a
⋆-algebra isomorphism `Matrix k k (Matrix n n R) ≃⋆ₐ Matrix (k × n) (k × n) R`, and also of the
C⋆-algebra of block matrices, `CStarMatrix k k (Matrix n n R) ≃⋆ₐ[ℂ] Matrix (k × n) (k × n) R`.
For complex matrices, with the C⋆-structure of `Matrix.Norms.L2Operator` and the order of
`MatrixOrder` (both scoped), this identifies the order of the C⋆-algebra of block matrices with
positive semidefiniteness of the flattened `kn × kn` matrix.

## Main definitions

* `Matrix.compStarAlgEquiv`: `Matrix.comp` as a `StarAlgEquiv`.
* `CStarMatrix.compStarAlgEquiv`: flattening of `CStarMatrix k k (Matrix n n R)` as a
  `StarAlgEquiv`.

## Main statements

* `Matrix.comp_conjTranspose`: `Matrix.comp` intertwines the two conjugate transposes.
* `CStarMatrix.nonneg_iff_posSemidef_comp`: `0 ≤ M ↔ (Matrix.comp k k n n ℂ M).PosSemidef`.
-/

@[expose] public section

namespace Matrix

variable {I J K R : Type*}

/-- Flattening a block matrix commutes with the conjugate transpose: the conjugate transpose of a
block matrix transposes the blocks and takes the conjugate transpose of each block. -/
lemma comp_conjTranspose [Star R] (M : Matrix I J (Matrix K K R)) :
    comp J I K K R Mᴴ = (comp I J K K R M)ᴴ := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp [conjTranspose_apply, star_apply]

variable (I J R) in
/-- `Matrix.comp` as a `StarAlgEquiv`. -/
def compStarAlgEquiv (S : Type*) [Fintype I] [Fintype J] [NonUnitalNonAssocSemiring R]
    [StarRing R] [SMul S R] :
    Matrix I I (Matrix J J R) ≃⋆ₐ[S] Matrix (I × J) (I × J) R where
  __ := compRingEquiv I J R
  map_smul' _ _ := rfl
  map_star' := comp_conjTranspose

/-- `Matrix.compStarAlgEquiv` flattens a block matrix by `Matrix.comp`. -/
@[simp]
lemma compStarAlgEquiv_apply (S : Type*) [Fintype I] [Fintype J] [NonUnitalNonAssocSemiring R]
    [StarRing R] [SMul S R] (M : Matrix I I (Matrix J J R)) :
    compStarAlgEquiv I J R S M = comp I I J J R M := rfl

/-- The inverse of `Matrix.compStarAlgEquiv` cuts a matrix into blocks by the inverse of
`Matrix.comp`. -/
@[simp]
lemma compStarAlgEquiv_symm_apply (S : Type*) [Fintype I] [Fintype J]
    [NonUnitalNonAssocSemiring R] [StarRing R] [SMul S R] (M : Matrix (I × J) (I × J) R) :
    (compStarAlgEquiv I J R S).symm M = (comp I I J J R).symm M := rfl

end Matrix

namespace CStarMatrix

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

/-- Flattening as a ⋆-algebra isomorphism of the C⋆-algebra of block matrices
`CStarMatrix k k (Matrix n n R)` onto `Matrix (k × n) (k × n) R`: the inverse of
`CStarMatrix.ofMatrixStarAlgEquiv` followed by `Matrix.compStarAlgEquiv`. -/
def compStarAlgEquiv (k n R : Type*) [Fintype k] [Fintype n] [DecidableEq n] [Semiring R]
    [StarRing R] [SMul ℂ R] : CStarMatrix k k (Matrix n n R) ≃⋆ₐ[ℂ] Matrix (k × n) (k × n) R :=
  ofMatrixStarAlgEquiv.symm.trans (Matrix.compStarAlgEquiv k n R ℂ)

/-- `CStarMatrix.compStarAlgEquiv` flattens a block matrix by `Matrix.comp`. -/
@[simp]
lemma compStarAlgEquiv_apply {k n R : Type*} [Fintype k] [Fintype n] [DecidableEq n] [Semiring R]
    [StarRing R] [SMul ℂ R] (M : CStarMatrix k k (Matrix n n R)) :
    compStarAlgEquiv k n R M = Matrix.comp k k n n R M := rfl

variable {k n : Type*} [Fintype k] [Fintype n] [DecidableEq n]

/-- A block matrix of complex matrices is nonnegative in the C⋆-algebra
`CStarMatrix k k (Matrix n n ℂ)` iff its flattening is positive semidefinite. Both orders are
the star orders (`StarOrderedRing`: the nonnegative elements form the additive submonoid generated
by the `star x * x`), so the star algebra isomorphism `CStarMatrix.compStarAlgEquiv` identifies them. -/
lemma nonneg_iff_posSemidef_comp {M : CStarMatrix k k (Matrix n n ℂ)} :
    0 ≤ M ↔ (Matrix.comp k k n n ℂ M).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef, ← map_le_map_iff (compStarAlgEquiv k n ℂ), map_zero]
  rfl

end CStarMatrix
