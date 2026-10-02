/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import QuantumSystem.Analysis.Matrix.QuantumChannel.CPTP
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.CStarMatrix
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.KPositiveMap
public import QuantumSystem.ForMathlib.Analysis.Matrix.Hermitian
public import QuantumSystem.ForMathlib.LinearAlgebra.Matrix.Trace

/-!
# The Choi–Kraus theorem

For a linear map `Φ : M_n(ℂ) → M_m(ℂ)` the following are equivalent:
1. `Φ` is completely positive;
2. `Φ` is `k`-positive (`KPositiveMap`) for some `k ≥ min(n, m)`: `id_k ⊗ Φ` is positive, for the
   single block size `k`;
3. its Choi matrix `J(Φ) = Σᵢⱼ Eᵢⱼ ⊗ Φ(Eᵢⱼ)` is positive semidefinite;
4. `Φ` has a Kraus representation `Φ(A) = Σₐ Kₐ A Kₐᴴ` with at most `nm` operators; indeed with
   exactly `rank J(Φ)` operators, the minimal number: every Kraus representation of `Φ` has at
   least `rank J(Φ)` operators.

## Main definitions

* `Matrix.choiMatrix Φ`: the Choi matrix `J(Φ) ((i, b), (j, b')) = Φ(Eᵢⱼ) b b'`.
* `CompletelyPositiveMap.ofKraus`, `CompletelyPositiveMap.ofPosSemidefChoiMatrix`,
  `CompletelyPositiveMap.ofKPositiveMap`: the completely positive map built from a Kraus
  representation, from a positive semidefinite Choi matrix, and from a `k`-positive map with
  `k ≥ min(n, m)`.
* `KPositiveMap.traceDual`, `CompletelyPositiveMap.traceDual`: the trace dual
  `φ* : M_m(ℂ) → M_n(ℂ)` of a `k`-positive, respectively completely positive, map, again
  `k`-positive, respectively completely positive.
* `CompletelyPositiveMap.toEuclidean ψ`: a completely positive map `ψ : A →CP M_n(ℂ)` as a
  completely positive map into `B(ℂⁿ)`.

## Main statements

* `Matrix.choiMatrix_eq_sum_kronecker`: `J(Φ) = Σᵢⱼ Eᵢⱼ ⊗ Φ(Eᵢⱼ)`.
* `Matrix.posSemidef_comp_map`: `k`-positivity in matrix form, `id_k ⊗ φ` sends
  positive semidefinite `kn × kn` matrices to positive semidefinite `km × km` matrices.
* `Matrix.posSemidef_choiMatrix_of_kPositive`: the Choi matrix of an `n`-positive map is positive
  semidefinite.
* `Matrix.exists_kraus_of_posSemidef_choiMatrix`: a map with positive semidefinite Choi matrix has
  a Kraus representation with `rank J(Φ)` operators.
* `Matrix.rank_choiMatrix_le_card_of_kraus`: every Kraus representation has at least `rank J(Φ)`
  operators; `Matrix.rank_choiMatrix_eq_card_iff_linearIndependent`: exactly `rank J(Φ)` iff the
  Kraus operators are linearly independent.
* `Matrix.posSemidef_comp_map_traceDual`: the trace dual of a `k`-positive map is
  `k`-positive, by self-duality of the positive semidefinite cone.
* `Matrix.posSemidef_choiMatrix_of_min_le`: the Choi matrix of a `k`-positive map with
  `k ≥ min(n, m)` is positive semidefinite; for `k ≥ m` through the trace dual.

**Choi's theorem**, where a linear map `Φ` is completely positive when it is the linear map of
some `φ : Matrix n n ℂ →CP Matrix m m ℂ`:

* `CompletelyPositiveMap.exists_toLinearMap_eq_iff_posSemidef_choiMatrix`: 1 ⟺ 3.
* `CompletelyPositiveMap.exists_toLinearMap_eq_iff_exists_kPositiveMap`: 1 ⟺ 2.
* `CompletelyPositiveMap.exists_toLinearMap_eq_iff_exists_kraus`: 1 ⟺ 4.

The two directions separately, for a completely positive map `φ` (1 ⇒ 2, 3, 4) and for a linear
map `Φ` with the data of 2, 3 or 4, from which the completely positive map is built
(2, 3, 4 ⇒ 1):

* `Matrix.posSemidef_comp_map` for every block size `k` (a finite index type `ι` with `k`
  elements), since a completely positive map is `k`-positive for every `k`
  (`CompletelyPositiveMapClass.instKPositiveMapClass`);
  `CompletelyPositiveMap.ofKPositiveMap` is the converse from a single block size `k ≥ min(n, m)`.
* `Matrix.posSemidef_choiMatrix_of_kPositive` (a completely positive map is `n`-positive),
  `CompletelyPositiveMap.ofPosSemidefChoiMatrix`: the Choi matrix.
* `CompletelyPositiveMap.exists_kraus_rank`: a CP map has a Kraus representation with exactly
  `rank J(φ)` operators, the minimal number by `Matrix.rank_choiMatrix_le_card_of_kraus`.
* `CompletelyPositiveMap.exists_kraus`, `CompletelyPositiveMap.ofKraus`: a CP map has a Kraus
  representation with at most `nm` operators, and a map with a Kraus representation, indexed by
  any finite type, is CP.

## Implementation notes

The Choi matrix uses Choi's ordering of the tensor factors, input first: `Σᵢⱼ Eᵢⱼ ⊗ Φ(Eᵢⱼ)`.
Watrous uses the opposite order `Σᵢⱼ Φ(Eᵢⱼ) ⊗ Eᵢⱼ`; the two differ by a swap of tensor factors, a
unitary conjugation, so positive semidefiniteness is unaffected.

The Kraus representation is obtained from the spectral rank-one decomposition
`J(Φ) = Σₐ vₐ vₐᴴ` of the Choi matrix into `rank J(Φ)` terms
(`Matrix.PosSemidef.exists_eq_sum_vecMulVec_rank`), with `Kₐ b i = vₐ (i, b)`. Complete positivity
of a Kraus map is checked on flattened block matrices, where `id_r ⊗ Φ` is conjugation by the
matrices `1 ⊗ Kₐ`.

## References

* M.-D. Choi, *Completely positive linear maps on complex matrices*, Linear Algebra Appl. 10
  (1975) 285–290
* Watrous, *The Theory of Quantum Information*, Theorem 2.22
-/

@[expose] public section

namespace Matrix

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
variable {F : Type*} [FunLike F (Matrix n n ℂ) (Matrix m m ℂ)]

open scoped ComplexOrder Kronecker

/-! ### The Choi matrix -/

omit [Fintype n] [Fintype m] [DecidableEq m] in
/-- The Choi matrix `J(Φ) = Σᵢⱼ Eᵢⱼ ⊗ Φ(Eᵢⱼ)` of a map `Φ : M_n(ℂ) → M_m(ℂ)`, indexed so that
`J(Φ) ((i, b), (j, b')) = Φ(Eᵢⱼ) b b'`. -/
def choiMatrix (Φ : F) : Matrix (n × m) (n × m) ℂ :=
  of fun p q => Φ (single p.1 q.1 1) p.2 q.2

omit [Fintype m] [DecidableEq m] in
/-- The Choi matrix is `J(Φ) = Σᵢⱼ Eᵢⱼ ⊗ Φ(Eᵢⱼ)`. -/
lemma choiMatrix_eq_sum_kronecker (Φ : F) :
    choiMatrix Φ = ∑ i, ∑ j, single i j (1 : ℂ) ⊗ₖ Φ (single i j 1) := by
  ext ⟨i, b⟩ ⟨j, b'⟩
  simp [choiMatrix, Matrix.sum_apply, kroneckerMap_apply, single_apply, ite_and]

omit [Fintype m] [DecidableEq m] in
/-- A linear map is recovered from its Choi matrix: `Φ(A) b b' = Σᵢⱼ Aᵢⱼ J(Φ) ((i, b), (j, b'))`. -/
lemma apply_eq_sum_choiMatrix [LinearMapClass F ℂ (Matrix n n ℂ) (Matrix m m ℂ)] (Φ : F)
    (A : Matrix n n ℂ) (b b' : m) : Φ A b b' = ∑ i, ∑ j, A i j * choiMatrix Φ (i, b) (j, b') := by
  have (i j : n) : single i j (A i j) = A i j • single i j (1 : ℂ) := by
    rw [smul_single, smul_eq_mul, mul_one]
  conv_lhs => rw [matrix_eq_sum_single A]
  simp only [this, map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rfl

/-! ### Kraus maps in block-matrix form -/

omit [Fintype m] [DecidableEq n] [DecidableEq m] in
/-- Applying a Kraus map `Φ(A) = Σₐ Kₐ A Kₐᴴ` entrywise to a block matrix is conjugation of the
flattened block matrix by `1 ⊗ Kₐ`, summed over `a`. -/
private lemma comp_map_eq_sum_kronecker {s : Type*} [Fintype s] [DecidableEq s]
    {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ} {ι : Type*} [Fintype ι] {K : ι → Matrix m n ℂ}
    (hK : ∀ A, Φ A = ∑ a, K a * A * (K a)ᴴ) (M : CStarMatrix s s (Matrix n n ℂ)) :
    comp s s m m ℂ (M.map Φ) =
      ∑ a, ((1 : Matrix s s ℂ) ⊗ₖ K a) * comp s s n n ℂ M * ((1 : Matrix s s ℂ) ⊗ₖ K a)ᴴ := by
  ext ⟨p, b⟩ ⟨q, b'⟩
  change Φ (M p q) b b' = _
  have hc : ∀ i j, comp s s n n ℂ M i j = M i.1 j.1 i.2 j.2 := fun _ _ => rfl
  simp [hK, hc, mul_apply, kroneckerMap_apply, Fintype.sum_prod_type, one_apply, Matrix.sum_apply,
    conjTranspose_apply, ite_mul, Finset.sum_mul, apply_ite (starRingEnd ℂ), mul_ite]

/-! ### Kraus representation from the Choi matrix -/

omit [DecidableEq m] in
/-- A linear map whose Choi matrix is positive semidefinite has a Kraus representation
`Φ(A) = Σₐ Kₐ A Kₐᴴ` with `rank J(Φ)` operators. -/
theorem exists_kraus_of_posSemidef_choiMatrix [LinearMapClass F ℂ (Matrix n n ℂ) (Matrix m m ℂ)]
    {Φ : F} (hΦ : (choiMatrix Φ).PosSemidef) :
    ∃ K : Fin (choiMatrix Φ).rank → Matrix m n ℂ, ∀ A, Φ A = ∑ a, K a * A * (K a)ᴴ := by
  obtain ⟨v, hv⟩ := hΦ.exists_eq_sum_vecMulVec_rank
  refine ⟨fun a => of fun b i => v a (i, b), fun A => ?_⟩
  ext b b'
  rw [apply_eq_sum_choiMatrix]
  conv_lhs => rw [hv]
  simp only [Matrix.sum_apply, mul_apply, vecMulVec_apply, conjTranspose_apply, of_apply,
    Finset.mul_sum, Finset.sum_mul, Pi.star_apply, RCLike.star_def]
  conv_rhs => rw [Finset.sum_comm]; enter [2, j]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => ?_
  ring

omit [Fintype m] [DecidableEq m] in
/-- The Choi matrix of a Kraus map `Φ(A) = Σₐ Kₐ A Kₐᴴ` is `W Wᴴ`, where the columns
`W (i, b) a = Kₐ b i` of `W` are the vectorised Kraus operators. -/
private lemma choiMatrix_eq_mul_conjTranspose_of_kraus {Φ : F} {ι : Type*} [Fintype ι]
    (K : ι → Matrix m n ℂ) (hK : ∀ A, Φ A = ∑ a, K a * A * (K a)ᴴ) :
    choiMatrix Φ = (of fun p a => K a p.2 p.1 : Matrix (n × m) ι ℂ) *
      (of fun p a => K a p.2 p.1 : Matrix (n × m) ι ℂ)ᴴ := by
  ext ⟨i, b⟩ ⟨j, b'⟩
  simp [choiMatrix, hK, mul_apply, Matrix.sum_apply, conjTranspose_apply, single_apply,
    ite_and, Finset.sum_ite_eq]

omit [DecidableEq m] in
/-- Every Kraus representation `Φ(A) = Σₐ Kₐ A Kₐᴴ` has at least `rank J(Φ)` operators: the Choi
matrix is `W Wᴴ`, where the columns of `W` are the vectorised Kraus operators. -/
theorem rank_choiMatrix_le_card_of_kraus {Φ : F} {ι : Type*} [Fintype ι] (K : ι → Matrix m n ℂ)
    (hK : ∀ A, Φ A = ∑ a, K a * A * (K a)ᴴ) :
    (choiMatrix Φ).rank ≤ Fintype.card ι := by
  rw [choiMatrix_eq_mul_conjTranspose_of_kraus K hK]
  exact (rank_mul_le_left _ _).trans (rank_le_card_width _)

omit [DecidableEq m] in
/-- A Kraus representation `Φ(A) = Σₐ Kₐ A Kₐᴴ` has exactly the minimal number `rank J(Φ)` of
operators iff its Kraus operators are linearly independent: `J(Φ) = W Wᴴ` has the rank of `W`,
whose columns are the vectorised Kraus operators. -/
theorem rank_choiMatrix_eq_card_iff_linearIndependent {Φ : F} {ι : Type*} [Fintype ι]
    (K : ι → Matrix m n ℂ) (hK : ∀ A, Φ A = ∑ a, K a * A * (K a)ᴴ) :
    (choiMatrix Φ).rank = Fintype.card ι ↔ LinearIndependent ℂ K := by
  let W : Matrix (n × m) ι ℂ := of fun p a => K a p.2 p.1
  have hW : LinearIndependent ℂ W.col ↔ LinearIndependent ℂ K := by
    simp only [Fintype.linearIndependent_iff]
    refine forall_congr' fun g => imp_congr_left ⟨fun h => ?_, fun h => ?_⟩
    · ext b i
      simpa [W, Matrix.sum_apply] using congrFun h (i, b)
    · ext ⟨i, b⟩
      simpa [W, Matrix.sum_apply] using congrFun (congrFun h b) i
  rw [choiMatrix_eq_mul_conjTranspose_of_kraus K hK, rank_self_mul_conjTranspose,
    rank_eq_finrank_span_cols, ← hW, linearIndependent_iff_card_eq_finrank_span, eq_comm]
  rfl

end Matrix

/-! ### `k`-positive maps and the Choi matrix -/

namespace Matrix
open scoped ComplexOrder CStarAlgebra

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
variable {F : Type*} [FunLike F (Matrix n n ℂ) (Matrix m m ℂ)]

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- `k`-positivity in matrix form: for a `k`-positive map `φ : M_n(ℂ) → M_m(ℂ)`, `id_k ⊗ φ` sends
positive semidefinite `kn × kn` matrices to positive semidefinite `km × km` matrices. The blocks may
be indexed by any finite type `ι` with `k` elements, not only by `Fin k`. -/
theorem posSemidef_comp_map {k : ℕ} [KPositiveMapClass F k (Matrix n n ℂ) (Matrix m m ℂ)]
    (φ : F) {ι : Type*} [Fintype ι] (hι : Fintype.card ι = k) {X : Matrix ι ι (Matrix n n ℂ)}
    (hX : (Matrix.comp ι ι n n ℂ X).PosSemidef) :
    (Matrix.comp ι ι m m ℂ (X.map φ)).PosSemidef := by
  subst hι
  let e := Fintype.equivFin ι
  have hY : (Matrix.comp _ _ n n ℂ (X.submatrix e.symm e.symm)).PosSemidef :=
    hX.submatrix (Prod.map e.symm id)
  have := CStarMatrix.nonneg_iff_posSemidef_comp.mp <|
    KPositiveMapClass.map_cstarMatrix_nonneg' φ (CStarMatrix.ofMatrix (X.submatrix e.symm e.symm))
      (CStarMatrix.nonneg_iff_posSemidef_comp.mpr hY)
  convert this.submatrix (Prod.map e id) using 1
  ext ⟨i, a⟩ ⟨j, b⟩
  change φ (X i j) a b = φ (X (e.symm (e i)) (e.symm (e j))) a b
  simp

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- The Choi matrix of an `n`-positive map `φ : M_n(ℂ) → M_m(ℂ)` is positive semidefinite: it is
`id_n ⊗ φ` applied to the block matrix `(Eᵢⱼ)ᵢⱼ`, whose flattening `ω ωᴴ` is `n` times the
rank-one projection onto the normalised maximally entangled vector `ω / √n`, `ω = Σᵢ eᵢ ⊗ eᵢ`.
Only the single block size `n` is used. -/
theorem posSemidef_choiMatrix_of_kPositive
    [KPositiveMapClass F (Fintype.card n) (Matrix n n ℂ) (Matrix m m ℂ)] (φ : F) :
    (choiMatrix φ).PosSemidef := by
  let ω : n × n → ℂ := fun p => if p.1 = p.2 then 1 else 0
  refine posSemidef_comp_map φ rfl (X := of fun i j => single i j 1) ?_
  convert posSemidef_vecMulVec_self_star ω using 1
  ext ⟨i, a⟩ ⟨j, b⟩
  change single i j (1 : ℂ) a b = _
  by_cases hi : i = a <;> by_cases hj : j = b <;> simp [ω, vecMulVec_apply, hi, hj]

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- The trace dual of a `k`-positive map `φ : M_n(ℂ) → M_m(ℂ)` is `k`-positive, in matrix form:
`id_k ⊗ φ*` sends positive semidefinite `km × km` matrices to positive semidefinite `kn × kn`
matrices. The positive semidefinite cone is self-dual for the trace pairing, and `id_k ⊗ φ*` is the
trace dual of `id_k ⊗ φ` (`Matrix.trace_comp_map_mul_comp_map_traceDual`): for a vector `v`,
`vᴴ (id_k ⊗ φ*)(X) v = Tr ((id_k ⊗ φ)(v vᴴ) X) ≥ 0`. -/
theorem posSemidef_comp_map_traceDual {k : ℕ} [KPositiveMapClass F k (Matrix n n ℂ) (Matrix m m ℂ)]
    [LinearMapClass F ℂ (Matrix n n ℂ) (Matrix m m ℂ)] (φ : F) {ι : Type*} [Fintype ι]
    (hι : Fintype.card ι = k) {X : Matrix ι ι (Matrix m m ℂ)}
    (hX : (Matrix.comp ι ι m m ℂ X).PosSemidef) :
    (Matrix.comp ι ι n n ℂ (X.map (traceDual φ))).PosSemidef := by
  refine posSemidef_iff_dotProduct_mulVec_complex.mpr fun v => ?_
  set Y := (Matrix.comp ι ι n n ℂ).symm (vecMulVec v (star v))
  have hY : (Matrix.comp ι ι n n ℂ Y).PosSemidef := by
    simpa [Y] using posSemidef_vecMulVec_self_star v
  rw [← trace_mul_vecMulVec, show vecMulVec v (star v) = Matrix.comp ι ι n n ℂ Y by simp [Y],
    Matrix.trace_mul_comm, ← trace_comp_map_mul_comp_map_traceDual]
  exact (posSemidef_comp_map φ hι hY).trace_mul_nonneg hX

end Matrix

namespace KPositiveMap

open Matrix
open scoped ComplexOrder CStarAlgebra

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
variable {F : Type*} [FunLike F (Matrix n n ℂ) (Matrix m m ℂ)]

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- The trace dual `φ*` of a `k`-positive map `φ : M_n(ℂ) → M_m(ℂ)`, characterised by
`Tr (φ(A) B) = Tr (A φ*(B))` (`Matrix.trace_mul_traceDual`), as a `k`-positive map
(`Matrix.posSemidef_comp_map_traceDual`). The block size `k` is explicit, since `φ` may
be `k`-positive for several `k`. -/
noncomputable def traceDual (k : ℕ) [KPositiveMapClass F k (Matrix n n ℂ) (Matrix m m ℂ)]
    [LinearMapClass F ℂ (Matrix n n ℂ) (Matrix m m ℂ)] (φ : F) :
    KPositiveMap k (Matrix m m ℂ) (Matrix n n ℂ) where
  toLinearMap := Matrix.traceDual φ
  map_cstarMatrix_nonneg' M hM := by
    rw [CStarMatrix.nonneg_iff_posSemidef_comp] at hM ⊢
    exact Matrix.posSemidef_comp_map_traceDual φ (Fintype.card_fin k) hM

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- The `k`-positive map `KPositiveMap.traceDual k φ` is the trace dual of `φ` as a
function. -/
@[simp] lemma coe_traceDual (k : ℕ) [KPositiveMapClass F k (Matrix n n ℂ) (Matrix m m ℂ)]
    [LinearMapClass F ℂ (Matrix n n ℂ) (Matrix m m ℂ)] (φ : F) :
    ⇑(traceDual k φ) = Matrix.traceDual φ :=
  rfl

end KPositiveMap

/-! ### Choi's theorem for completely positive maps -/

namespace CompletelyPositiveMap

open Matrix
open scoped ComplexOrder Kronecker CStarAlgebra

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- A linear map with a Kraus representation `Φ(A) = Σₐ Kₐ A Kₐᴴ`, indexed by any finite type, is
completely positive: on flattened block matrices `id_r ⊗ Φ` is conjugation by the `1 ⊗ Kₐ`. -/
def ofKraus (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) {ι : Type*} [Fintype ι]
    (K : ι → Matrix m n ℂ) (hK : ∀ A, Φ A = ∑ a, K a * A * (K a)ᴴ) :
    Matrix n n ℂ →CP Matrix m m ℂ where
  toLinearMap := Φ
  map_cstarMatrix_nonneg' _ M hM := by
    rw [CStarMatrix.nonneg_iff_posSemidef_comp] at hM ⊢
    rw [comp_map_eq_sum_kronecker hK]
    exact posSemidef_sum _ fun a _ => hM.mul_mul_conjTranspose_same _

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- The completely positive map `CompletelyPositiveMap.ofKraus Φ K hK` is `Φ` as a function. -/
@[simp] lemma coe_ofKraus (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) {ι : Type*} [Fintype ι]
    (K : ι → Matrix m n ℂ) (hK : ∀ A, Φ A = ∑ a, K a * A * (K a)ᴴ) : ⇑(ofKraus Φ K hK) = Φ :=
  rfl

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- **Choi's theorem**: a linear map with positive semidefinite Choi matrix is completely
positive. With `Matrix.posSemidef_choiMatrix_of_kPositive`, which applies to completely positive
maps (`CompletelyPositiveMapClass.instKPositiveMapClass`), this characterises complete
positivity. -/
def ofPosSemidefChoiMatrix (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (h : (choiMatrix Φ).PosSemidef) : Matrix n n ℂ →CP Matrix m m ℂ where
  toLinearMap := Φ
  map_cstarMatrix_nonneg' :=
    let ⟨K, hK⟩ := exists_kraus_of_posSemidef_choiMatrix h
    (ofKraus Φ K hK).map_cstarMatrix_nonneg'

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- The completely positive map `CompletelyPositiveMap.ofPosSemidefChoiMatrix Φ h` is `Φ` as a
function. -/
@[simp] lemma coe_ofPosSemidefChoiMatrix (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (h : (choiMatrix Φ).PosSemidef) : ⇑(ofPosSemidefChoiMatrix Φ h) = Φ :=
  rfl

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- A completely positive map has a Kraus representation `φ(A) = Σₐ Kₐ A Kₐᴴ` with exactly
`rank J(φ)` operators. This is the minimal number (`Matrix.rank_choiMatrix_le_card_of_kraus`). -/
theorem exists_kraus_rank (φ : Matrix n n ℂ →CP Matrix m m ℂ) :
    ∃ K : Fin (choiMatrix φ).rank → Matrix m n ℂ, ∀ A, φ A = ∑ a, K a * A * (K a)ᴴ :=
  exists_kraus_of_posSemidef_choiMatrix (posSemidef_choiMatrix_of_kPositive φ)

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- **Choi–Kraus theorem**: a completely positive map `φ : M_n(ℂ) → M_m(ℂ)` has a Kraus
representation `φ(A) = Σₐ Kₐ A Kₐᴴ` with at most `nm` operators. Conversely every Kraus map is
completely positive (`CompletelyPositiveMap.ofKraus`). -/
theorem exists_kraus (φ : Matrix n n ℂ →CP Matrix m m ℂ) :
    ∃ r ≤ Fintype.card n * Fintype.card m,
      ∃ K : Fin r → Matrix m n ℂ, ∀ A, φ A = ∑ a, K a * A * (K a)ᴴ :=
  ⟨_, (rank_le_card_width (choiMatrix φ)).trans_eq (Fintype.card_prod n m),
    φ.exists_kraus_rank⟩

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- The trace dual `φ*` of a completely positive map `φ : M_n(ℂ) → M_m(ℂ)`, characterised by
`Tr (φ(A) B) = Tr (A φ*(B))` (`Matrix.trace_mul_traceDual`), is completely positive: the positive
semidefinite cone is self-dual for the trace pairing, and `id_k ⊗ φ*` is the trace dual of
`id_k ⊗ φ` (`Matrix.posSemidef_comp_map_traceDual`). -/
def traceDual (φ : Matrix n n ℂ →CP Matrix m m ℂ) : Matrix m m ℂ →CP Matrix n n ℂ where
  toLinearMap := Matrix.traceDual φ
  map_cstarMatrix_nonneg' k M hM := by
    rw [CStarMatrix.nonneg_iff_posSemidef_comp] at hM ⊢
    exact Matrix.posSemidef_comp_map_traceDual φ (Fintype.card_fin k) hM

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- The completely positive map `CompletelyPositiveMap.traceDual φ` is the trace dual of `φ` as a
function. -/
@[simp] lemma coe_traceDual (φ : Matrix n n ℂ →CP Matrix m m ℂ) :
    ⇑φ.traceDual = Matrix.traceDual φ :=
  rfl

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- A completely positive map `ψ : A → M_n(ℂ)`, read as a completely positive map into the bounded
operators `B(ℂⁿ)` on `EuclideanSpace ℂ n` through `Matrix.toEuclideanCLM`; for the trace dual,
`φ.traceDual.toEuclidean`. -/
noncomputable def toEuclidean {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (ψ : A →CP Matrix n n ℂ) :
    A →CP (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :=
  (CompletelyPositiveMapClass.toCompletelyPositiveLinearMap
    (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ))).comp ψ

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- `ψ.toEuclidean a` is the operator of the matrix `ψ a`. -/
lemma toEuclidean_apply {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (ψ : A →CP Matrix n n ℂ) (a : A) :
    ψ.toEuclidean a = Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (ψ a) :=
  rfl

end CompletelyPositiveMap

namespace Matrix

open scoped ComplexOrder CStarAlgebra

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
variable {F : Type*} [FunLike F (Matrix n n ℂ) (Matrix m m ℂ)]

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- **Choi's theorem**, `min(n, m)`-positivity form: the Choi matrix of a `k`-positive map
`φ : M_n(ℂ) → M_m(ℂ)` with `k ≥ min(n, m)` is positive semidefinite. For `k ≥ n` the map is
`n`-positive (`KPositiveMapClass.of_le`, `Matrix.posSemidef_choiMatrix_of_kPositive`). For `k ≥ m`
its trace dual `φ* : M_m(ℂ) → M_n(ℂ)` is `m`-positive (`KPositiveMap.traceDual`), hence completely
positive, and so is `φ = φ**` (`Matrix.traceDual_traceDual`). -/
theorem posSemidef_choiMatrix_of_min_le {k : ℕ} [KPositiveMapClass F k (Matrix n n ℂ) (Matrix m m ℂ)]
    [LinearMapClass F ℂ (Matrix n n ℂ) (Matrix m m ℂ)] (φ : F)
    (hk : min (Fintype.card n) (Fintype.card m) ≤ k) : (choiMatrix φ).PosSemidef := by
  rcases min_le_iff.1 hk with h | h
  · have := KPositiveMapClass.of_le (F := F) h
    exact posSemidef_choiMatrix_of_kPositive φ
  · let χ : Matrix m m ℂ →CP Matrix n n ℂ := CompletelyPositiveMap.ofPosSemidefChoiMatrix
      (Matrix.traceDual φ)
      (posSemidef_choiMatrix_of_kPositive ((KPositiveMap.traceDual k φ).ofLE h))
    have hχ : ⇑χ.traceDual = ⇑φ := funext fun A => traceDual_traceDual φ A
    have hJ : choiMatrix φ = choiMatrix χ.traceDual := by
      ext p q
      simp only [choiMatrix, of_apply, hχ]
    rw [hJ]
    exact posSemidef_choiMatrix_of_kPositive χ.traceDual

end Matrix

namespace CompletelyPositiveMap

open Matrix
open scoped ComplexOrder Kronecker CStarAlgebra

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- **Choi's theorem**, `min(n, m)`-positivity form: a `k`-positive map `φ : M_n(ℂ) → M_m(ℂ)` with
`k ≥ min(n, m)`, i.e. one for which `id_k ⊗ φ` sends positive semidefinite `kn × kn` matrices to
positive semidefinite `km × km` matrices, is completely positive
(`Matrix.posSemidef_choiMatrix_of_min_le`). Conversely a completely positive map is
`k`-positive for every `k` (`CompletelyPositiveMapClass.instKPositiveMapClass`). -/
def ofKPositiveMap {F : Type*} [FunLike F (Matrix n n ℂ) (Matrix m m ℂ)] {k : ℕ}
    [KPositiveMapClass F k (Matrix n n ℂ) (Matrix m m ℂ)]
    [LinearMapClass F ℂ (Matrix n n ℂ) (Matrix m m ℂ)] (φ : F)
    (hk : min (Fintype.card n) (Fintype.card m) ≤ k) : Matrix n n ℂ →CP Matrix m m ℂ :=
  ofPosSemidefChoiMatrix (φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (Matrix.posSemidef_choiMatrix_of_min_le φ hk)

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- The completely positive map `CompletelyPositiveMap.ofKPositiveMap φ hk` is `φ` as a function. -/
@[simp] lemma coe_ofKPositiveMap {F : Type*} [FunLike F (Matrix n n ℂ) (Matrix m m ℂ)] {k : ℕ}
    [KPositiveMapClass F k (Matrix n n ℂ) (Matrix m m ℂ)]
    [LinearMapClass F ℂ (Matrix n n ℂ) (Matrix m m ℂ)] (φ : F)
    (hk : min (Fintype.card n) (Fintype.card m) ≤ k) : ⇑(ofKPositiveMap φ hk) = φ :=
  rfl

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- **Choi's theorem**: a linear map `Φ : M_n(ℂ) → M_m(ℂ)` is completely positive, i.e. it is the
linear map of some `φ : M_n(ℂ) →CP M_m(ℂ)`, iff its Choi matrix `J(Φ)` is positive
semidefinite. -/
theorem exists_toLinearMap_eq_iff_posSemidef_choiMatrix (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    (∃ φ : Matrix n n ℂ →CP Matrix m m ℂ, φ.toLinearMap = Φ) ↔ (choiMatrix Φ).PosSemidef :=
  ⟨fun ⟨φ, hφ⟩ => hφ ▸ posSemidef_choiMatrix_of_kPositive φ, fun h => ⟨ofPosSemidefChoiMatrix Φ h, rfl⟩⟩

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- **Choi's theorem**, `min(n, m)`-positivity form: a linear map `Φ : M_n(ℂ) → M_m(ℂ)` is
completely positive iff it is `k`-positive, i.e. `id_k ⊗ Φ` sends positive semidefinite
`kn × kn` matrices to positive semidefinite `km × km` matrices, for a single block size
`k ≥ min(n, m)`. -/
theorem exists_toLinearMap_eq_iff_exists_kPositiveMap (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    {k : ℕ} (hk : min (Fintype.card n) (Fintype.card m) ≤ k) :
    (∃ φ : Matrix n n ℂ →CP Matrix m m ℂ, φ.toLinearMap = Φ) ↔
      ∃ ψ : KPositiveMap k (Matrix n n ℂ) (Matrix m m ℂ), ψ.toLinearMap = Φ :=
  ⟨fun ⟨φ, hφ⟩ => ⟨⟨φ.toLinearMap, φ.map_cstarMatrix_nonneg' _⟩, hφ⟩,
    fun ⟨ψ, hψ⟩ => ⟨ofKPositiveMap ψ hk, hψ⟩⟩

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- **Choi–Kraus theorem**: a linear map `Φ : M_n(ℂ) → M_m(ℂ)` is completely positive iff it has
a Kraus representation `Φ(A) = Σₐ Kₐ A Kₐᴴ` with at most `nm` operators. -/
theorem exists_toLinearMap_eq_iff_exists_kraus (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    (∃ φ : Matrix n n ℂ →CP Matrix m m ℂ, φ.toLinearMap = Φ) ↔
      ∃ r ≤ Fintype.card n * Fintype.card m,
        ∃ K : Fin r → Matrix m n ℂ, ∀ A, Φ A = ∑ a, K a * A * (K a)ᴴ :=
  ⟨fun ⟨φ, hφ⟩ => hφ ▸ φ.exists_kraus, fun ⟨_, _, K, hK⟩ => ⟨ofKraus Φ K hK, rfl⟩⟩

end CompletelyPositiveMap
