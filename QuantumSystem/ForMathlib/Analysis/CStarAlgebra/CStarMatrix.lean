/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.Matrix.Order

/-!
# Positivity of block matrices of complex matrices

A `k × k` block matrix `M : CStarMatrix k k (Matrix n n ℂ)` with entries in the C⋆-algebra
`Matrix n n ℂ` carries the star order of the C⋆-algebra `CStarMatrix k k (Matrix n n ℂ)`. This
file identifies that order with the Löwner order, positive semidefiniteness of the flattened matrix
`Matrix.comp k k n n ℂ M : Matrix (k × n) (k × n) ℂ`.

The C⋆-structure on `Matrix n n ℂ` is the one of `Matrix.Norms.L2Operator` and the order is the
one of `MatrixOrder`; both are scoped instances.

## Main definitions

* `Matrix.compStarAlgEquiv`: `Matrix.comp` as a `StarAlgEquiv`.

## Main statements

* `Matrix.comp_conjTranspose`: `Matrix.comp` intertwines the two conjugate transposes.
* `CStarMatrix.nonneg_iff_posSemidef_comp`: `0 ≤ M ↔ (Matrix.comp k k n n ℂ M).PosSemidef`.
-/

@[expose] public section

namespace Matrix

variable {I J K R : Type*}

/-- Flattening a block matrix commutes with the conjugate transpose: the conjugate transpose of a
block matrix transposes the blocks and takes the conjugate transpose of each block. -/
theorem comp_conjTranspose [Star R] (M : Matrix I J (Matrix K K R)) :
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

@[simp]
theorem compStarAlgEquiv_apply (S : Type*) [Fintype I] [Fintype J] [NonUnitalNonAssocSemiring R]
    [StarRing R] [SMul S R] (M : Matrix I I (Matrix J J R)) :
    compStarAlgEquiv I J R S M = comp I I J J R M := rfl

@[simp]
theorem compStarAlgEquiv_symm_apply (S : Type*) [Fintype I] [Fintype J]
    [NonUnitalNonAssocSemiring R] [StarRing R] [SMul S R] (M : Matrix (I × J) (I × J) R) :
    (compStarAlgEquiv I J R S).symm M = (comp I I J J R).symm M := rfl

end Matrix

namespace CStarMatrix

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {k n : Type*} [Fintype k] [Fintype n] [DecidableEq n]

/-- A block matrix of complex matrices is nonnegative in the C⋆-algebra
`CStarMatrix k k (Matrix n n ℂ)` iff its flattening is positive semidefinite. Both orders are
the star orders (`StarOrderedRing`: the nonnegative elements form the additive submonoid generated
by the `star x * x`), so the star algebra isomorphism `Matrix.comp` identifies them. -/
theorem nonneg_iff_posSemidef_comp {M : CStarMatrix k k (Matrix n n ℂ)} :
    0 ≤ M ↔ (Matrix.comp k k n n ℂ M).PosSemidef := by
  let f : CStarMatrix k k (Matrix n n ℂ) ≃⋆ₐ[ℂ] Matrix (k × n) (k × n) ℂ :=
    ofMatrixStarAlgEquiv.symm.trans (Matrix.compStarAlgEquiv k n ℂ ℂ)
  rw [← Matrix.nonneg_iff_posSemidef, ← map_le_map_iff f, map_zero]
  rfl

end CStarMatrix
