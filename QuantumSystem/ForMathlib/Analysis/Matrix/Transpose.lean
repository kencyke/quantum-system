/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.Matrix.Order

/-!
# The transpose as a positive unital map

The transpose of square matrices over `𝕜` is a positive unital linear map for the order of
`MatrixOrder`, `A ≤ B ↔ (B - A).PosSemidef`. It is the standard example of a positive map which
violates the Kadison–Schwarz inequality `φ(a)⋆ φ(a) ≤ φ(a⋆ a)`: at a matrix unit `Eᵢⱼ` with
`i ≠ j`, `(Eᵢⱼ)ᵀ⋆ (Eᵢⱼ)ᵀ = Eᵢᵢ` while `(Eᵢⱼ⋆ Eᵢⱼ)ᵀ = Eⱼⱼ`, and `Eᵢᵢ ≰ Eⱼⱼ`. It is also its own
inverse, but reverses products, and `n × n` matrices do not commute when `n` has two distinct
elements, so it is not multiplicative and not a ⋆-isomorphism.

## Main definitions

* `Matrix.transposePositiveLinearMap` — the transpose as a positive linear map
  `Matrix n n 𝕜 →ₚ[𝕜] Matrix n n 𝕜`; it is unital (`Matrix.transposePositiveLinearMap_one`).

## Main results

* `Matrix.not_single_le_single` — `Eᵢᵢ ≰ Eⱼⱼ` for `i ≠ j`.
* `Matrix.not_star_map_mul_le_map_star_mul_transpose` — the transpose violates the
  Kadison–Schwarz inequality `φ(a)⋆ φ(a) ≤ φ(a⋆ a)` at `a = Eᵢⱼ` for `i ≠ j`.
* `Matrix.not_forall_mul_comm` — `n × n` matrices over a nontrivial semiring do not commute when
  `n` has two distinct elements; `Matrix.not_forall_transpose_mul_eq` — so the transpose is not
  multiplicative;
  `Matrix.not_exists_starAlgEquiv_transpose` — so no ⋆-isomorphism is the transpose.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace Matrix

variable {𝕜 n : Type*} [RCLike 𝕜]

/-- The transpose as a positive linear map: the transpose of a positive semidefinite matrix is
positive semidefinite (`Matrix.PosSemidef.transpose`). -/
noncomputable def transposePositiveLinearMap : Matrix n n 𝕜 →ₚ[𝕜] Matrix n n 𝕜 :=
  PositiveLinearMap.mk₀ (transposeLinearEquiv n n 𝕜 𝕜).toLinearMap
    fun _ hX => (nonneg_iff_posSemidef.1 hX).transpose.nonneg

/-- `Matrix.transposePositiveLinearMap` is the transpose. -/
@[simp]
lemma transposePositiveLinearMap_apply (X : Matrix n n 𝕜) : transposePositiveLinearMap X = Xᵀ :=
  rfl

variable [DecidableEq n]

/-- The transpose is unital. -/
lemma transposePositiveLinearMap_one : transposePositiveLinearMap (1 : Matrix n n 𝕜) = 1 :=
  transpose_one

/-- `Eᵢᵢ ≰ Eⱼⱼ` for `i ≠ j`: the quadratic form of `Eⱼⱼ - Eᵢᵢ` at `eᵢ` is `-1`. -/
lemma not_single_le_single {i j : n} (h : i ≠ j) :
    ¬ (single i i 1 : Matrix n n 𝕜) ≤ single j j 1 := by
  intro hle
  refine (zero_lt_one' 𝕜).not_ge ?_
  simpa [Finsupp.sum_single_index, single_apply, Matrix.sub_apply, h.symm] using
    (Matrix.le_iff.1 hle).2 (Finsupp.single i 1)

/-- **The transpose is not a Schwarz map**: the Kadison–Schwarz inequality
`φ(a)⋆ φ(a) ≤ φ(a⋆ a)` fails for the transpose at `a = Eᵢⱼ` with `i ≠ j`, as
`(Eᵢⱼ)ᵀ⋆ (Eᵢⱼ)ᵀ = Eᵢᵢ` and `(Eᵢⱼ⋆ Eᵢⱼ)ᵀ = Eⱼⱼ`. -/
lemma not_star_map_mul_le_map_star_mul_transpose [Fintype n] {i j : n} (h : i ≠ j) :
    ¬ star (transposePositiveLinearMap (single i j 1 : Matrix n n 𝕜)) *
        transposePositiveLinearMap (single i j 1) ≤
      transposePositiveLinearMap (star (single i j 1) * single i j 1) := by
  simpa [transpose_single, star_eq_conjTranspose, conjTranspose_single] using
    not_single_le_single (𝕜 := 𝕜) h

omit [RCLike 𝕜] [DecidableEq n] in
/-- `n × n` matrices over a nontrivial semiring do not commute when `n` has two distinct elements
`i ≠ j`: `Eᵢⱼ Eⱼᵢ = Eᵢᵢ` while `Eⱼᵢ Eᵢⱼ = Eⱼⱼ`. -/
lemma not_forall_mul_comm {R : Type*} [Semiring R] [Nontrivial R] [Fintype n] [Nontrivial n] :
    ¬ ∀ X Y : Matrix n n R, X * Y = Y * X := by
  classical
  intro h
  obtain ⟨i, j, hij⟩ := exists_pair_ne n
  have := congrFun₂ (h (single i j 1) (single j i 1)) i i
  simp [hij] at this

omit [DecidableEq n] in
/-- The transpose is not multiplicative when `n` has two distinct elements: it reverses products
(`Matrix.transpose_mul`), which do not commute (`Matrix.not_forall_mul_comm`). -/
lemma not_forall_transpose_mul_eq [Fintype n] [Nontrivial n] :
    ¬ ∀ X Y : Matrix n n 𝕜, (X * Y)ᵀ = Xᵀ * Yᵀ := fun h =>
  not_forall_mul_comm fun X Y => by simpa [transpose_mul] using h Yᵀ Xᵀ

omit [DecidableEq n] in
/-- **The transpose is not a ⋆-isomorphism** when `n` has two distinct elements, although it is a
unital positive map which is its own inverse: it is not multiplicative
(`Matrix.not_forall_transpose_mul_eq`). -/
lemma not_exists_starAlgEquiv_transpose [Fintype n] [Nontrivial n] :
    ¬ ∃ e : Matrix n n 𝕜 ≃⋆ₐ[𝕜] Matrix n n 𝕜, ∀ X, e X = Xᵀ := by
  rintro ⟨e, he⟩
  exact not_forall_transpose_mul_eq fun X Y => by rw [← he, ← he, ← he, map_mul]

end Matrix
