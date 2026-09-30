/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.Matrix.QuantumChannel.CPTP
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.CStarMatrix
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.KPositiveMap
public import QuantumSystem.ForMathlib.Analysis.Matrix.Hermitian

/-!
# The Choi–Kraus theorem

For a linear map `Φ : M_n(ℂ) → M_m(ℂ)` the following are equivalent:
1. `Φ` is completely positive;
2. `Φ` is `n`-positive (`KPositiveMap`): `id_n ⊗ Φ` is positive, for the single block size `n`;
3. its Choi matrix `J(Φ) = Σᵢⱼ Eᵢⱼ ⊗ Φ(Eᵢⱼ)` is positive semidefinite;
4. `Φ` has a Kraus representation `Φ(A) = Σₐ Kₐ A Kₐᴴ` with at most `nm` operators; indeed with
   exactly `rank J(Φ)` operators, the minimal number: every Kraus representation of `Φ` has at
   least `rank J(Φ)` operators.

## Main definitions

* `Matrix.choiMatrix Φ`: the Choi matrix `J(Φ) ((i, b), (j, b')) = Φ(Eᵢⱼ) b b'`.
* `CompletelyPositiveMap.ofKraus`, `CompletelyPositiveMap.ofPosSemidefChoiMatrix`,
  `CompletelyPositiveMap.ofKPositiveMap`: the completely positive map built from a Kraus
  representation, from a positive semidefinite Choi matrix, and from an `n`-positive map.

## Main statements

* `Matrix.choiMatrix_eq_sum_kronecker`: `J(Φ) = Σᵢⱼ Eᵢⱼ ⊗ Φ(Eᵢⱼ)`.
* `KPositiveMapClass.posSemidef_comp_map`: `k`-positivity in matrix form, `id_k ⊗ φ` sends
  positive semidefinite `kn × kn` matrices to positive semidefinite `km × km` matrices.
* `KPositiveMapClass.posSemidef_choiMatrix`: the Choi matrix of an `n`-positive map is positive
  semidefinite.
* `Matrix.exists_kraus_of_posSemidef_choiMatrix`: a map with positive semidefinite Choi matrix has
  a Kraus representation with `rank J(Φ)` operators.
* `Matrix.rank_choiMatrix_le_card_of_kraus`: every Kraus representation has at least `rank J(Φ)`
  operators.

**Choi's theorem**, where a linear map `Φ` is completely positive when it is the linear map of
some `φ : Matrix n n ℂ →CP Matrix m m ℂ`:

* `CompletelyPositiveMap.exists_toLinearMap_eq_iff_posSemidef_choiMatrix`: 1 ⟺ 3.
* `CompletelyPositiveMap.exists_toLinearMap_eq_iff_exists_kPositiveMap`: 1 ⟺ 2.
* `CompletelyPositiveMap.exists_toLinearMap_eq_iff_exists_kraus`: 1 ⟺ 4.

The two directions separately, for a completely positive map `φ` (1 ⇒ 2, 3, 4) and for a linear
map `Φ` with the data of 2, 3 or 4, from which the completely positive map is built
(2, 3, 4 ⇒ 1):

* `CompletelyPositiveMap.posSemidef_comp_map`: complete positivity in matrix form, `id_k ⊗ φ`
  sends positive semidefinite `kn × kn` matrices to positive semidefinite `km × km` matrices for
  every finite index type `k`; `CompletelyPositiveMap.ofKPositiveMap` is the converse from
  the single block size `n`.
* `CompletelyPositiveMap.posSemidef_choiMatrix`, `CompletelyPositiveMap.ofPosSemidefChoiMatrix`:
  the Choi matrix.
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

omit [DecidableEq m] in
/-- Every Kraus representation `Φ(A) = Σₐ Kₐ A Kₐᴴ` has at least `rank J(Φ)` operators: the Choi
matrix is `W Wᴴ`, where the columns of `W` are the vectorised Kraus operators. -/
theorem rank_choiMatrix_le_card_of_kraus {Φ : F} {ι : Type*} [Fintype ι] (K : ι → Matrix m n ℂ)
    (hK : ∀ A, Φ A = ∑ a, K a * A * (K a)ᴴ) :
    (choiMatrix Φ).rank ≤ Fintype.card ι := by
  let W : Matrix (n × m) ι ℂ := of fun p a => K a p.2 p.1
  have hJ : choiMatrix Φ = W * Wᴴ := by
    ext ⟨i, b⟩ ⟨j, b'⟩
    simp [choiMatrix, hK, W, mul_apply, Matrix.sum_apply, conjTranspose_apply, single_apply,
      ite_and, Finset.sum_ite_eq]
  rw [hJ]
  exact (rank_mul_le_left _ _).trans (rank_le_card_width W)

end Matrix

/-! ### `k`-positive maps and the Choi matrix -/

namespace KPositiveMapClass

open Matrix
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
theorem posSemidef_choiMatrix
    [KPositiveMapClass F (Fintype.card n) (Matrix n n ℂ) (Matrix m m ℂ)] (φ : F) :
    (choiMatrix φ).PosSemidef := by
  let ω : n × n → ℂ := fun p => if p.1 = p.2 then 1 else 0
  refine posSemidef_comp_map φ rfl (X := of fun i j => single i j 1) ?_
  convert posSemidef_vecMulVec_self_star ω using 1
  ext ⟨i, a⟩ ⟨j, b⟩
  change single i j (1 : ℂ) a b = _
  by_cases hi : i = a <;> by_cases hj : j = b <;> simp [ω, vecMulVec_apply, hi, hj]

end KPositiveMapClass

/-! ### Choi's theorem for completely positive maps -/

namespace CompletelyPositiveMap

open Matrix
open scoped ComplexOrder Kronecker CStarAlgebra

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- Complete positivity in matrix form: `id_k ⊗ φ` sends positive semidefinite `kn × kn` matrices
to positive semidefinite `km × km` matrices, for every finite index type `k`. -/
theorem posSemidef_comp_map (φ : Matrix n n ℂ →CP Matrix m m ℂ) {k : Type*} [Finite k]
    {X : Matrix k k (Matrix n n ℂ)} (hX : (Matrix.comp k k n n ℂ X).PosSemidef) :
    (Matrix.comp k k m m ℂ (X.map φ)).PosSemidef := by
  have := Fintype.ofFinite k
  exact KPositiveMapClass.posSemidef_comp_map φ rfl hX

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
/-- The Choi matrix of a completely positive map is positive semidefinite. -/
theorem posSemidef_choiMatrix (φ : Matrix n n ℂ →CP Matrix m m ℂ) :
    (choiMatrix φ).PosSemidef :=
  KPositiveMapClass.posSemidef_choiMatrix φ

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- **Choi's theorem**: a linear map with positive semidefinite Choi matrix is completely
positive. With `CompletelyPositiveMap.posSemidef_choiMatrix` this characterises complete
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
/-- **Choi's theorem**, `n`-positivity form: an `n`-positive map `φ : M_n(ℂ) → M_m(ℂ)`, i.e. one for
which `id_n ⊗ φ` sends positive semidefinite `n² × n²` matrices to positive semidefinite `nm × nm`
matrices, is completely positive. Conversely a completely positive map is `k`-positive for every
`k` (`CompletelyPositiveMap.instKPositiveMapClass`). -/
def ofKPositiveMap (φ : KPositiveMap (Fintype.card n) (Matrix n n ℂ) (Matrix m m ℂ)) :
    Matrix n n ℂ →CP Matrix m m ℂ :=
  ofPosSemidefChoiMatrix φ.toLinearMap (KPositiveMapClass.posSemidef_choiMatrix φ)

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- The completely positive map `CompletelyPositiveMap.ofKPositiveMap φ` is `φ` as a function. -/
@[simp] lemma coe_ofKPositiveMap
    (φ : KPositiveMap (Fintype.card n) (Matrix n n ℂ) (Matrix m m ℂ)) :
    ⇑(ofKPositiveMap φ) = φ :=
  rfl

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- A completely positive map has a Kraus representation `φ(A) = Σₐ Kₐ A Kₐᴴ` with exactly
`rank J(φ)` operators. This is the minimal number (`Matrix.rank_choiMatrix_le_card_of_kraus`). -/
theorem exists_kraus_rank (φ : Matrix n n ℂ →CP Matrix m m ℂ) :
    ∃ K : Fin (choiMatrix φ).rank → Matrix m n ℂ, ∀ A, φ A = ∑ a, K a * A * (K a)ᴴ :=
  exists_kraus_of_posSemidef_choiMatrix φ.posSemidef_choiMatrix

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
/-- **Choi's theorem**: a linear map `Φ : M_n(ℂ) → M_m(ℂ)` is completely positive, i.e. it is the
linear map of some `φ : M_n(ℂ) →CP M_m(ℂ)`, iff its Choi matrix `J(Φ)` is positive
semidefinite. -/
theorem exists_toLinearMap_eq_iff_posSemidef_choiMatrix (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    (∃ φ : Matrix n n ℂ →CP Matrix m m ℂ, φ.toLinearMap = Φ) ↔ (choiMatrix Φ).PosSemidef :=
  ⟨fun ⟨φ, hφ⟩ => hφ ▸ φ.posSemidef_choiMatrix, fun h => ⟨ofPosSemidefChoiMatrix Φ h, rfl⟩⟩

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- **Choi's theorem**, `n`-positivity form: a linear map `Φ : M_n(ℂ) → M_m(ℂ)` is completely
positive iff it is `n`-positive, i.e. `id_n ⊗ Φ` sends positive semidefinite `n² × n²` matrices to
positive semidefinite `nm × nm` matrices, for the single block size `n`. -/
theorem exists_toLinearMap_eq_iff_exists_kPositiveMap (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    (∃ φ : Matrix n n ℂ →CP Matrix m m ℂ, φ.toLinearMap = Φ) ↔
      ∃ ψ : KPositiveMap (Fintype.card n) (Matrix n n ℂ) (Matrix m m ℂ), ψ.toLinearMap = Φ :=
  ⟨fun ⟨φ, hφ⟩ => ⟨⟨φ.toLinearMap, φ.map_cstarMatrix_nonneg' _⟩, hφ⟩,
    fun ⟨ψ, hψ⟩ => ⟨ofKPositiveMap ψ, hψ⟩⟩

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- **Choi–Kraus theorem**: a linear map `Φ : M_n(ℂ) → M_m(ℂ)` is completely positive iff it has
a Kraus representation `Φ(A) = Σₐ Kₐ A Kₐᴴ` with at most `nm` operators. -/
theorem exists_toLinearMap_eq_iff_exists_kraus (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    (∃ φ : Matrix n n ℂ →CP Matrix m m ℂ, φ.toLinearMap = Φ) ↔
      ∃ r ≤ Fintype.card n * Fintype.card m,
        ∃ K : Fin r → Matrix m n ℂ, ∀ A, Φ A = ∑ a, K a * A * (K a)ᴴ :=
  ⟨fun ⟨φ, hφ⟩ => hφ ▸ φ.exists_kraus, fun ⟨_, _, K, hK⟩ => ⟨ofKraus Φ K hK, rfl⟩⟩

end CompletelyPositiveMap
