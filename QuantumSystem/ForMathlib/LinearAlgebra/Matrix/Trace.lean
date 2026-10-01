/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Data.Matrix.Composition
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Auxiliary results on `Matrix.trace`

Facts about `Matrix.trace` that plausibly belong upstream next to
`Mathlib.LinearAlgebra.Matrix.Trace`, including the **trace dual** (Heisenberg picture) of a linear
map between matrix algebras: for a linear map `Φ : Matrix n n R → Matrix m m R` over a commutative
semiring, `Matrix.traceDual Φ : Matrix m m R →ₗ[R] Matrix n n R` is the adjoint of `Φ` for the
trace pairing `(A, B) ↦ (A * B).trace`. The map `Φ` is taken from any `FunLike` type, with
`LinearMapClass` only where linearity is used (the duality `Matrix.trace_mul_traceDual`), so that
bundled linear maps and completely positive maps are covered alike.

## Main definitions

* `Matrix.traceDual Φ` — the trace dual of `Φ`.

## Main statements

* `Matrix.trace_reindex_self` — reindexing by an equivalence preserves the trace.
* `Matrix.trace_comp_mul_comp` — the trace of a product of flattened block matrices is the sum of
  the traces of the products of blocks.
* `Matrix.trace_mul_vecMulVec` — `Tr (A (v wᵀ)) = w ⬝ᵥ A v`.
* `Matrix.trace_mul_traceDual` — the defining duality
  `(Φ A * B).trace = (A * traceDual Φ B).trace`.
* `Matrix.trace_comp_map_mul_comp_map_traceDual` — the same duality for `Φ` and `traceDual Φ`
  applied blockwise to block matrices.
* `Matrix.traceDual_eq_of_kraus` — for a Kraus map `A ↦ Σᵢ Kᵢ A Kᵢᴴ` the trace dual is
  `B ↦ Σᵢ Kᵢᴴ B Kᵢ`.
* `Matrix.traceDual_one`, `Matrix.traceDual_one_iff` — a linear map is trace preserving iff its
  trace dual is unital.
* `Matrix.traceDual_traceDual` — the trace dual is an involution, `Φ** = Φ`.
-/

@[expose] public section

namespace Matrix

section Reindex

variable {n m R : Type*} [Fintype n] [Fintype m] [AddCommMonoid R]

/-- Reindexing by an index equivalence preserves the trace. -/
@[simp] lemma trace_reindex_self (e : n ≃ m) (M : Matrix n n R) :
    (M.reindex e e).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp e.symm (fun i => M i i)

end Reindex

section Composition

variable {s t p q R : Type*} [Fintype s] [Fintype t] [Fintype p] [Fintype q]
  [NonUnitalNonAssocSemiring R]

/-- The trace of a product of flattened block matrices is the sum of the traces of the products of
blocks: `Tr(comp A * comp B) = Σᵢⱼ Tr(Aᵢⱼ Bⱼᵢ)`. -/
lemma trace_comp_mul_comp (A : Matrix s t (Matrix p q R)) (B : Matrix t s (Matrix q p R)) :
    (comp s t p q R A * comp t s q p R B).trace = ∑ i, ∑ j, (A i j * B j i).trace := by
  simp only [trace, diag, mul_apply, comp_apply, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

end Composition

section VecMulVec

variable {n R : Type*} [Fintype n] [CommSemiring R]

/-- Pairing with a rank-one matrix evaluates a bilinear form: `Tr (A (v wᵀ)) = w ⬝ᵥ A v`. -/
lemma trace_mul_vecMulVec (A : Matrix n n R) (v w : n → R) :
    (A * vecMulVec v w).trace = w ⬝ᵥ (A *ᵥ v) := by
  rw [mul_vecMulVec, trace_vecMulVec, dotProduct_comm]

end VecMulVec

section TraceDual

variable {n m R : Type*} [Fintype n] [Fintype m] [DecidableEq n] [CommSemiring R]
variable {F : Type*} [FunLike F (Matrix n n R) (Matrix m m R)]

/-- The **trace dual** (Heisenberg picture) of a linear map `Φ` on matrix algebras, characterised by
`(Φ A * B).trace = (A * traceDual Φ B).trace` (`Matrix.trace_mul_traceDual`). Its entries are
`(traceDual Φ B) j i = (Φ (E_{ij}) * B).trace` for the matrix units `E_{ij} = Matrix.single i j 1`.
For a Kraus map `A ↦ Σᵢ Kᵢ A Kᵢᴴ` it is `B ↦ Σᵢ Kᵢᴴ B Kᵢ` (`Matrix.traceDual_eq_of_kraus`); it is
unital when `Φ` is trace preserving (`Matrix.traceDual_one`). -/
def traceDual (Φ : F) : Matrix m m R →ₗ[R] Matrix n n R where
  toFun B := Matrix.of fun j i => (Φ (Matrix.single i j 1) * B).trace
  map_add' B C := by
    ext j i
    simp [Matrix.mul_add, Matrix.trace_add]
  map_smul' c B := by
    ext j i
    simp [Matrix.mul_smul, Matrix.trace_smul]

omit [Fintype n] in
/-- The entries of the trace dual: `Φ*(B) j i = Tr (Φ(Eᵢⱼ) B)`. -/
lemma traceDual_apply (Φ : F) (B : Matrix m m R) (j i : n) :
    traceDual Φ B j i = (Φ (Matrix.single i j 1) * B).trace := rfl

/-- **The defining duality**: `(Φ A * B).trace = (A * traceDual Φ B).trace`. -/
theorem trace_mul_traceDual [LinearMapClass F R (Matrix n n R) (Matrix m m R)] (Φ : F)
    (A : Matrix n n R) (B : Matrix m m R) :
    (Φ A * B).trace = (A * traceDual Φ B).trace := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  simp only [map_sum, Finset.sum_mul, Matrix.trace_sum]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, traceDual_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show Matrix.single i j (A i j) = A i j • Matrix.single i j (1 : R) by
      rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul]
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- The defining duality for block matrices: applying `Φ` blockwise is dual to applying
`traceDual Φ` blockwise, `Tr(comp (Y.map Φ) * comp X) = Tr(comp Y * comp (X.map Φ*))`. -/
theorem trace_comp_map_mul_comp_map_traceDual [LinearMapClass F R (Matrix n n R) (Matrix m m R)]
    (Φ : F) {s : Type*} [Fintype s] (Y : Matrix s s (Matrix n n R)) (X : Matrix s s (Matrix m m R)) :
    (comp s s m m R (Y.map Φ) * comp s s m m R X).trace =
      (comp s s n n R Y * comp s s n n R (X.map (traceDual Φ))).trace := by
  simp only [trace_comp_mul_comp, map_apply, trace_mul_traceDual]

/-- The trace dual of a Kraus map `A ↦ Σᵢ Kᵢ A Kᵢᴴ` is `B ↦ Σᵢ Kᵢᴴ B Kᵢ`. The trace dual depends
on `Φ` only through its values, so no linearity of `Φ` is assumed: the Kraus form supplies it. -/
theorem traceDual_eq_of_kraus [Star R] {Φ : F} {ι : Type*} [Fintype ι] {K : ι → Matrix m n R}
    (hK : ∀ A, Φ A = ∑ i, K i * A * (K i)ᴴ) (B : Matrix m m R) :
    traceDual Φ B = ∑ i, (K i)ᴴ * B * K i := by
  let L : Matrix n n R →ₗ[R] Matrix m m R :=
    { toFun A := ∑ i, K i * A * (K i)ᴴ
      map_add' A C := by simp only [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
      map_smul' c A := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum, RingHom.id_apply] }
  have hL : traceDual Φ B = traceDual L B := by
    ext j i
    rw [traceDual_apply, traceDual_apply, hK]
    rfl
  refine hL.trans (Matrix.ext_iff_trace_mul_left.mpr fun x => ?_)
  rw [← trace_mul_traceDual]
  change ((∑ i, K i * x * (K i)ᴴ) * B).trace = _
  rw [Finset.sum_mul, Matrix.trace_sum, Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_assoc x]
  exact Matrix.trace_mul_comm _ _

/-- The trace dual of a trace-preserving map is unital. The converse, for linear `Φ`, is
`Matrix.traceDual_one_iff`. -/
theorem traceDual_one [DecidableEq m] {Φ : F} (hΦ : ∀ A, (Φ A).trace = A.trace) :
    traceDual Φ 1 = 1 := by
  ext j i
  rw [traceDual_apply, Matrix.mul_one, hΦ, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    simp
  · simp [Matrix.trace_single_eq_of_ne _ _ _ h, Ne.symm h]

/-- A linear map is trace preserving iff its trace dual is unital:
`Tr (Φ A) = Tr (Φ A * 1) = Tr (A * Φ*(1))`. -/
theorem traceDual_one_iff [DecidableEq m] [LinearMapClass F R (Matrix n n R) (Matrix m m R)]
    {Φ : F} : traceDual Φ 1 = 1 ↔ ∀ A, (Φ A).trace = A.trace :=
  ⟨fun h A => by rw [← Matrix.mul_one (Φ A), trace_mul_traceDual, h, Matrix.mul_one],
    traceDual_one⟩

/-- The trace dual is an involution: `Φ** = Φ`, by the defining duality applied twice,
`Tr (Φ**(A) B) = Tr (B Φ**(A)) = Tr (Φ*(B) A) = Tr (A Φ*(B)) = Tr (Φ(A) B)`. -/
theorem traceDual_traceDual [DecidableEq m] [LinearMapClass F R (Matrix n n R) (Matrix m m R)]
    (Φ : F) (A : Matrix n n R) : traceDual (traceDual Φ) A = Φ A :=
  Matrix.ext_iff_trace_mul_right.mpr fun B => by
    rw [Matrix.trace_mul_comm, ← trace_mul_traceDual, Matrix.trace_mul_comm,
      ← trace_mul_traceDual]

end TraceDual

end Matrix
