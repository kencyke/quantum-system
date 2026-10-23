/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.CStarAlgebra.Hom
public import Mathlib.Analysis.Matrix.Order

/-!
# Flattening block matrices and their positivity; block matrices of `CStarMatrix`

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
* `CStarMatrix.flatten`, `CStarMatrix.flattenStarAlgEquiv`: flattening an `m × m` block matrix with
  `n × n` blocks to an `mn × mn` matrix, indexed by `Fin (m * n)`.
* `CStarMatrix.transposeBlocks`, `CStarMatrix.transposeBlocksStarAlgEquiv`: exchanging the outer and
  inner indices of a block matrix.
* `CStarMatrix.directSum`: the block diagonal matrix `X ⊕ Y`.

## Main statements

* `Matrix.comp_conjTranspose`: `Matrix.comp` intertwines the two conjugate transposes.
* `CStarMatrix.nonneg_iff_posSemidef_comp`: `0 ≤ M ↔ (Matrix.comp k k n n ℂ M).PosSemidef`.
* `CStarMatrix.norm_directSum`: `‖X ⊕ Y‖ = max ‖X‖ ‖Y‖` over a C⋆-algebra.
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

/-! ### Block matrices of `CStarMatrix` -/

namespace CStarMatrix

section Blocks

variable {V W : Type*} {m n : ℕ}

/-- Flattening an `m × m` block matrix with `n × n` blocks to an `mn × mn` matrix, indexing
`Fin (m * n)` by `finProdFinEquiv`. -/
def flatten (M : CStarMatrix (Fin m) (Fin m) (CStarMatrix (Fin n) (Fin n) V)) :
    CStarMatrix (Fin (m * n)) (Fin (m * n)) V :=
  ofMatrix (Matrix.of fun p q => M (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm q).1
    (finProdFinEquiv.symm p).2 (finProdFinEquiv.symm q).2)

/-- The entries of a flattened block matrix. -/
lemma flatten_apply_finProdFinEquiv (M : CStarMatrix (Fin m) (Fin m) (CStarMatrix (Fin n) (Fin n) V))
    (i j : Fin m) (a b : Fin n) :
    flatten M (finProdFinEquiv (i, a)) (finProdFinEquiv (j, b)) = M i j a b := by
  change M (finProdFinEquiv.symm (finProdFinEquiv (i, a))).1
    (finProdFinEquiv.symm (finProdFinEquiv (j, b))).1 (finProdFinEquiv.symm (finProdFinEquiv (i, a))).2
    (finProdFinEquiv.symm (finProdFinEquiv (j, b))).2 = _
  simp only [Equiv.symm_apply_apply]

/-- Flattening commutes with applying a function entrywise. -/
lemma flatten_map (M : CStarMatrix (Fin m) (Fin m) (CStarMatrix (Fin n) (Fin n) V)) (f : V → W) :
    flatten (M.map (·.map f)) = (flatten M).map f :=
  rfl

/-- Exchanging the outer and the inner indices of a block matrix: `(transposeBlocks M) a b i j =
M i j a b`. -/
def transposeBlocks (M : CStarMatrix (Fin m) (Fin m) (CStarMatrix (Fin n) (Fin n) V)) :
    CStarMatrix (Fin n) (Fin n) (CStarMatrix (Fin m) (Fin m) V) :=
  ofMatrix (Matrix.of fun a b => ofMatrix (Matrix.of fun i j => M i j a b))

/-- The entries of `transposeBlocks M`. -/
lemma transposeBlocks_apply (M : CStarMatrix (Fin m) (Fin m) (CStarMatrix (Fin n) (Fin n) V))
    (i j : Fin m) (a b : Fin n) : transposeBlocks M a b i j = M i j a b :=
  rfl

/-- Exchanging the outer and inner indices commutes with applying a function entrywise. -/
lemma transposeBlocks_map (M : CStarMatrix (Fin m) (Fin m) (CStarMatrix (Fin n) (Fin n) V))
    (f : V → W) : transposeBlocks (M.map (·.map f)) = (transposeBlocks M).map (·.map f) :=
  rfl

variable {A : Type*} [NonUnitalCStarAlgebra A]

variable (m n A) in
/-- `CStarMatrix.flatten` as a ⋆-algebra isomorphism of C⋆-algebras. -/
def flattenStarAlgEquiv : CStarMatrix (Fin m) (Fin m) (CStarMatrix (Fin n) (Fin n) A) ≃⋆ₐ[ℂ]
    CStarMatrix (Fin (m * n)) (Fin (m * n)) A :=
  (Matrix.compStarAlgEquiv (Fin m) (Fin n) A ℂ :
      Matrix (Fin m) (Fin m) (Matrix (Fin n) (Fin n) A) ≃⋆ₐ[ℂ] _).trans
    (reindexₐ ℂ A finProdFinEquiv)

/-- `CStarMatrix.flattenStarAlgEquiv` is `CStarMatrix.flatten`. -/
@[simp]
lemma flattenStarAlgEquiv_apply (M : CStarMatrix (Fin m) (Fin m) (CStarMatrix (Fin n) (Fin n) A)) :
    flattenStarAlgEquiv m n A M = flatten M :=
  rfl

variable (m n A) in
/-- `CStarMatrix.transposeBlocks` as a ⋆-algebra isomorphism of C⋆-algebras. -/
def transposeBlocksStarAlgEquiv : CStarMatrix (Fin m) (Fin m) (CStarMatrix (Fin n) (Fin n) A) ≃⋆ₐ[ℂ]
    CStarMatrix (Fin n) (Fin n) (CStarMatrix (Fin m) (Fin m) A) :=
  (Matrix.compStarAlgEquiv (Fin m) (Fin n) A ℂ :
      Matrix (Fin m) (Fin m) (Matrix (Fin n) (Fin n) A) ≃⋆ₐ[ℂ] _).trans
    ((reindexₐ ℂ A (Equiv.prodComm (Fin m) (Fin n))).trans
      (Matrix.compStarAlgEquiv (Fin n) (Fin m) A ℂ :
        Matrix (Fin n) (Fin n) (Matrix (Fin m) (Fin m) A) ≃⋆ₐ[ℂ] _).symm)

/-- `CStarMatrix.transposeBlocksStarAlgEquiv` is `CStarMatrix.transposeBlocks`. -/
@[simp]
lemma transposeBlocksStarAlgEquiv_apply
    (M : CStarMatrix (Fin m) (Fin m) (CStarMatrix (Fin n) (Fin n) A)) :
    transposeBlocksStarAlgEquiv m n A M = transposeBlocks M :=
  rfl

end Blocks

section DirectSum

variable {V : Type*} [Zero V] {k l : ℕ}

/-- The block diagonal matrix `X ⊕ Y` of a `k × k` and an `l × l` matrix, indexing `Fin (k + l)` by
`finSumFinEquiv`. -/
def directSum (X : CStarMatrix (Fin k) (Fin k) V) (Y : CStarMatrix (Fin l) (Fin l) V) :
    CStarMatrix (Fin (k + l)) (Fin (k + l)) V :=
  ofMatrix ((Matrix.fromBlocks (ofMatrix.symm X) 0 0 (ofMatrix.symm Y)).reindex finSumFinEquiv
    finSumFinEquiv)

/-- The upper left block of `X ⊕ Y` is `X`. -/
lemma directSum_apply_castAdd (X : CStarMatrix (Fin k) (Fin k) V)
    (Y : CStarMatrix (Fin l) (Fin l) V) (i j : Fin k) :
    directSum X Y (Fin.castAdd l i) (Fin.castAdd l j) = X i j := by
  simp [directSum, ofMatrix_apply]

/-- The lower right block of `X ⊕ Y` is `Y`. -/
lemma directSum_apply_natAdd (X : CStarMatrix (Fin k) (Fin k) V)
    (Y : CStarMatrix (Fin l) (Fin l) V) (i j : Fin l) :
    directSum X Y (Fin.natAdd k i) (Fin.natAdd k j) = Y i j := by
  simp [directSum, ofMatrix_apply]

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (k l A) in
/-- The block diagonal embedding `(X, Y) ↦ X ⊕ Y` as a ⋆-homomorphism. -/
def directSumNonUnitalStarAlgHom :
    (CStarMatrix (Fin k) (Fin k) A × CStarMatrix (Fin l) (Fin l) A) →⋆ₙₐ[ℂ]
      CStarMatrix (Fin (k + l)) (Fin (k + l)) A where
  toFun p := directSum p.1 p.2
  map_smul' c p := by
    ext i j
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨t, rfl⟩ := finSumFinEquiv.surjective j
    change directSum (c • p).1 (c • p).2 _ _ = c • directSum p.1 p.2 _ _
    cases s <;> cases t <;> simp [directSum, ofMatrix_apply]
  map_zero' := by
    ext i j
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨t, rfl⟩ := finSumFinEquiv.surjective j
    change directSum (0 : CStarMatrix (Fin k) (Fin k) A) 0 _ _ = 0
    cases s <;> cases t <;> simp [directSum, ofMatrix_apply]
  map_add' p q := by
    ext i j
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨t, rfl⟩ := finSumFinEquiv.surjective j
    change directSum (p + q).1 (p + q).2 _ _ = directSum p.1 p.2 _ _ + directSum q.1 q.2 _ _
    cases s <;> cases t <;> simp [directSum, ofMatrix_apply]
  map_mul' p q := by
    change ofMatrix _ = ofMatrix _ * ofMatrix _
    rw [show (ofMatrix (Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (ofMatrix.symm p.1) 0 0 (ofMatrix.symm p.2))) :
          CStarMatrix (Fin (k + l)) (Fin (k + l)) A) * ofMatrix (Matrix.reindex finSumFinEquiv
          finSumFinEquiv (Matrix.fromBlocks (ofMatrix.symm q.1) 0 0 (ofMatrix.symm q.2))) =
        ofMatrix (Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (ofMatrix.symm p.1) 0 0 (ofMatrix.symm p.2)) *
          Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (ofMatrix.symm q.1) 0 0 (ofMatrix.symm q.2))) from rfl]
    simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp
    rfl
  map_star' p := by
    ext i j
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨t, rfl⟩ := finSumFinEquiv.surjective j
    rw [star_apply]
    cases s <;> cases t <;> simp [directSum, ofMatrix_apply, star_apply]

/-- The norm of a block diagonal matrix `X ⊕ Y` is the larger of `‖X‖` and `‖Y‖`: the block
diagonal embedding is an injective ⋆-homomorphism, hence isometric for the norm `max` of the
product. -/
lemma norm_directSum (X : CStarMatrix (Fin k) (Fin k) A) (Y : CStarMatrix (Fin l) (Fin l) A) :
    ‖directSum X Y‖ = max ‖X‖ ‖Y‖ := by
  have hinj : Function.Injective (directSumNonUnitalStarAlgHom k l A) := by
    intro p q h
    have h' : directSum p.1 p.2 = directSum q.1 q.2 := h
    refine Prod.ext (ext fun i j => ?_) (ext fun i j => ?_)
    · rw [← directSum_apply_castAdd p.1 p.2, ← directSum_apply_castAdd q.1 q.2, h']
    · rw [← directSum_apply_natAdd p.1 p.2, ← directSum_apply_natAdd q.1 q.2, h']
  exact (NonUnitalStarAlgHom.norm_map _ hinj (X, Y)).trans (Prod.norm_def _)

end DirectSum

end CStarMatrix
