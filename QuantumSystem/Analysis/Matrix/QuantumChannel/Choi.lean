/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.Matrix.QuantumChannel.CPTP
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.CStarMatrix
public import QuantumSystem.ForMathlib.Analysis.Matrix.Hermitian

/-!
# The Choi–Kraus theorem

For a linear map `Φ : M_n(ℂ) → M_m(ℂ)` the following are equivalent:
1. `Φ` is completely positive;
2. `Φ` is `n`-positive: `id_n ⊗ Φ` is positive, for the single block size `n`;
3. its Choi matrix `J(Φ) = Σᵢⱼ Eᵢⱼ ⊗ Φ(Eᵢⱼ)` is positive semidefinite;
4. `Φ` has a Kraus representation `Φ(A) = Σₐ Kₐ A Kₐᴴ` with at most `nm` operators; indeed with
   exactly `rank J(Φ)` operators, the minimal number: every Kraus representation of `Φ` has at
   least `rank J(Φ)` operators.

## Main definitions

* `Matrix.choiMatrix Φ`: the Choi matrix `J(Φ) ((i, b), (j, b')) = Φ(Eᵢⱼ) b b'`.

## Main statements

* `Matrix.choiMatrix_eq_sum_kronecker`: `J(Φ) = Σᵢⱼ Eᵢⱼ ⊗ Φ(Eᵢⱼ)`.
* `Matrix.isCompletelyPositive_iff_posSemidef_comp_map`: complete positivity in matrix form,
  `id_r ⊗ Φ` sends positive semidefinite `rn × rn` matrices to positive semidefinite `rm × rm`
  matrices for every `r : ℕ` (block index `Fin r`);
  `Matrix.IsCompletelyPositive.posSemidef_comp_map` gives the forward direction for block matrices
  indexed by any finite type `k`.
* `Matrix.isCompletelyPositive_of_kraus`: a map with a Kraus representation, indexed by any finite
  type, is CP.
* `Matrix.posSemidef_choiMatrix_of_posSemidef_comp_map`: the Choi matrix of an `n`-positive map is
  positive semidefinite; `Matrix.IsCompletelyPositive.posSemidef_choiMatrix` is the CP case.
* `Matrix.exists_kraus_of_posSemidef_choiMatrix`: a map with positive semidefinite Choi matrix has
  a Kraus representation with `rank J(Φ)` operators.
* `Matrix.rank_choiMatrix_le_card_of_kraus`: every Kraus representation has at least `rank J(Φ)`
  operators.
* `Matrix.isCompletelyPositive_iff_posSemidef_choiMatrix`,
  `Matrix.isCompletelyPositive_iff_posSemidef_comp_map_self`,
  `Matrix.isCompletelyPositive_iff_exists_kraus`: Choi's theorem.
* `Matrix.IsCompletelyPositive.exists_kraus_rank`: a CP map has a Kraus representation with
  exactly `rank J(Φ)` operators, the minimal number by `Matrix.rank_choiMatrix_le_card_of_kraus`.
* `Matrix.IsCompletelyPositive.exists_kraus`: a CP map has a Kraus representation with at most
  `nm` operators.

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

open scoped ComplexOrder Kronecker

/-! ### The Choi matrix -/

omit [Fintype n] [Fintype m] [DecidableEq m] in
/-- The Choi matrix `J(Φ) = Σᵢⱼ Eᵢⱼ ⊗ Φ(Eᵢⱼ)` of a linear map `Φ : M_n(ℂ) → M_m(ℂ)`, indexed so that
`J(Φ) ((i, b), (j, b')) = Φ(Eᵢⱼ) b b'`. -/
def choiMatrix (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Matrix (n × m) (n × m) ℂ :=
  of fun p q => Φ (single p.1 q.1 1) p.2 q.2

omit [Fintype m] [DecidableEq m] in
/-- The Choi matrix is `J(Φ) = Σᵢⱼ Eᵢⱼ ⊗ Φ(Eᵢⱼ)`. -/
lemma choiMatrix_eq_sum_kronecker (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    choiMatrix Φ = ∑ i, ∑ j, single i j (1 : ℂ) ⊗ₖ Φ (single i j 1) := by
  ext ⟨i, b⟩ ⟨j, b'⟩
  simp [choiMatrix, Matrix.sum_apply, kroneckerMap_apply, single_apply, ite_and]

omit [Fintype m] [DecidableEq m] in
/-- A linear map is recovered from its Choi matrix: `Φ(A) b b' = Σᵢⱼ Aᵢⱼ J(Φ) ((i, b), (j, b'))`. -/
lemma apply_eq_sum_choiMatrix (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) (A : Matrix n n ℂ)
    (b b' : m) : Φ A b b' = ∑ i, ∑ j, A i j * choiMatrix Φ (i, b) (j, b') := by
  have (i j : n) : single i j (A i j) = A i j • single i j (1 : ℂ) := by
    rw [smul_single, smul_eq_mul, mul_one]
  conv_lhs => rw [matrix_eq_sum_single A]
  simp only [this, map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rfl

/-! ### Complete positivity in matrix form -/

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- Complete positivity in matrix form: `id_k ⊗ Φ` sends positive semidefinite `kn × kn` matrices
to positive semidefinite `km × km` matrices, for every finite index type `k`. -/
theorem IsCompletelyPositive.posSemidef_comp_map {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ}
    (hΦ : IsCompletelyPositive Φ) {k : Type*} [Finite k] {X : Matrix k k (Matrix n n ℂ)}
    (hX : (Matrix.comp k k n n ℂ X).PosSemidef) : (Matrix.comp k k m m ℂ (X.map Φ)).PosSemidef := by
  have := Fintype.ofFinite k
  exact CStarMatrix.nonneg_iff_posSemidef_comp.mp <|
    hΦ.toCompletelyPositiveMap.map_cstarMatrix_nonneg (CStarMatrix.ofMatrix X)
      (CStarMatrix.nonneg_iff_posSemidef_comp.mpr hX)

/-- A linear map is completely positive iff `id_r ⊗ Φ` sends positive semidefinite `rn × rn`
matrices to positive semidefinite `rm × rm` matrices, for every `r`. -/
theorem isCompletelyPositive_iff_posSemidef_comp_map {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ} :
    IsCompletelyPositive Φ ↔ ∀ (r : ℕ) (X : Matrix (Fin r) (Fin r) (Matrix n n ℂ)),
      (comp _ _ n n ℂ X).PosSemidef → (comp _ _ m m ℂ (X.map Φ)).PosSemidef :=
  ⟨fun h _ _ hX => IsCompletelyPositive.posSemidef_comp_map h hX, fun h r M hM =>
    CStarMatrix.nonneg_iff_posSemidef_comp.mpr
      (h r M (CStarMatrix.nonneg_iff_posSemidef_comp.mp hM))⟩

/-! ### Kraus maps are completely positive -/

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

/-- A linear map with a Kraus representation `Φ(A) = Σₐ Kₐ A Kₐᴴ` is completely positive. -/
theorem isCompletelyPositive_of_kraus {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ} {ι : Type*}
    [Fintype ι] (K : ι → Matrix m n ℂ) (hK : ∀ A, Φ A = ∑ a, K a * A * (K a)ᴴ) :
    IsCompletelyPositive Φ := fun s M hM => by
  rw [CStarMatrix.nonneg_iff_posSemidef_comp] at hM ⊢
  rw [comp_map_eq_sum_kronecker hK]
  exact posSemidef_sum _ fun a _ => hM.mul_mul_conjTranspose_same _

/-! ### The Choi matrix of a completely positive map -/

omit [Fintype n] [Fintype m] [DecidableEq m] in
/-- The Choi matrix of an `n`-positive map is positive semidefinite: it is `id_n ⊗ Φ` applied to
the block matrix `(Eᵢⱼ)ᵢⱼ`, whose flattening `ω ωᴴ` is `n` times the rank-one projection onto the
normalised maximally entangled vector `ω / √n`, `ω = Σᵢ eᵢ ⊗ eᵢ`. Only the single block size `n`
is used. -/
theorem posSemidef_choiMatrix_of_posSemidef_comp_map [Finite n]
    {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ}
    (hΦ : ∀ X : Matrix n n (Matrix n n ℂ),
      (comp n n n n ℂ X).PosSemidef → (comp n n m m ℂ (X.map Φ)).PosSemidef) :
    (choiMatrix Φ).PosSemidef := by
  let ω : n × n → ℂ := fun p => if p.1 = p.2 then 1 else 0
  refine hΦ (of fun i j => single i j 1) ?_
  convert posSemidef_vecMulVec_self_star ω using 1
  ext ⟨i, a⟩ ⟨j, b⟩
  change single i j (1 : ℂ) a b = _
  by_cases hi : i = a <;> by_cases hj : j = b <;> simp [ω, vecMulVec_apply, hi, hj]

/-- The Choi matrix of a completely positive map is positive semidefinite. -/
theorem IsCompletelyPositive.posSemidef_choiMatrix {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ}
    (hΦ : IsCompletelyPositive Φ) : (choiMatrix Φ).PosSemidef :=
  posSemidef_choiMatrix_of_posSemidef_comp_map fun _ hX => hΦ.posSemidef_comp_map hX

/-! ### Kraus representation from the Choi matrix -/

omit [DecidableEq m] in
/-- A linear map whose Choi matrix is positive semidefinite has a Kraus representation
`Φ(A) = Σₐ Kₐ A Kₐᴴ` with `rank J(Φ)` operators. -/
theorem exists_kraus_of_posSemidef_choiMatrix {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ}
    (hΦ : (choiMatrix Φ).PosSemidef) :
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
theorem rank_choiMatrix_le_card_of_kraus {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ} {ι : Type*}
    [Fintype ι] (K : ι → Matrix m n ℂ) (hK : ∀ A, Φ A = ∑ a, K a * A * (K a)ᴴ) :
    (choiMatrix Φ).rank ≤ Fintype.card ι := by
  let W : Matrix (n × m) ι ℂ := of fun p a => K a p.2 p.1
  have hJ : choiMatrix Φ = W * Wᴴ := by
    ext ⟨i, b⟩ ⟨j, b'⟩
    simp [choiMatrix, hK, W, mul_apply, Matrix.sum_apply, conjTranspose_apply, single_apply,
      ite_and, Finset.sum_ite_eq]
  rw [hJ]
  exact (rank_mul_le_left _ _).trans (rank_le_card_width W)

/-! ### Choi's theorem -/

/-- **Choi's theorem**: a linear map is completely positive iff its Choi matrix is positive
semidefinite. -/
theorem isCompletelyPositive_iff_posSemidef_choiMatrix {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ} :
    IsCompletelyPositive Φ ↔ (choiMatrix Φ).PosSemidef :=
  ⟨IsCompletelyPositive.posSemidef_choiMatrix, fun h =>
    let ⟨K, hK⟩ := exists_kraus_of_posSemidef_choiMatrix h
    isCompletelyPositive_of_kraus K hK⟩

/-- **Choi's theorem**, `n`-positivity form: a linear map `Φ : M_n(ℂ) → M_m(ℂ)` is completely
positive iff it is `n`-positive, i.e. `id_n ⊗ Φ` sends positive semidefinite `n² × n²` matrices to
positive semidefinite `nm × nm` matrices. -/
theorem isCompletelyPositive_iff_posSemidef_comp_map_self
    {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ} :
    IsCompletelyPositive Φ ↔ ∀ X : Matrix n n (Matrix n n ℂ),
      (comp n n n n ℂ X).PosSemidef → (comp n n m m ℂ (X.map Φ)).PosSemidef :=
  ⟨fun h _ hX => h.posSemidef_comp_map hX, fun h =>
    isCompletelyPositive_iff_posSemidef_choiMatrix.mpr
      (posSemidef_choiMatrix_of_posSemidef_comp_map h)⟩

/-- A completely positive map has a Kraus representation `Φ(A) = Σₐ Kₐ A Kₐᴴ` with exactly
`rank J(Φ)` operators. This is the minimal number (`Matrix.rank_choiMatrix_le_card_of_kraus`). -/
theorem IsCompletelyPositive.exists_kraus_rank {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ}
    (hΦ : IsCompletelyPositive Φ) :
    ∃ K : Fin (choiMatrix Φ).rank → Matrix m n ℂ, ∀ A, Φ A = ∑ a, K a * A * (K a)ᴴ :=
  exists_kraus_of_posSemidef_choiMatrix hΦ.posSemidef_choiMatrix

/-- A completely positive map `Φ : M_n(ℂ) → M_m(ℂ)` has a Kraus representation
`Φ(A) = Σₐ Kₐ A Kₐᴴ` with at most `nm` operators. -/
theorem IsCompletelyPositive.exists_kraus {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ}
    (hΦ : IsCompletelyPositive Φ) :
    ∃ r ≤ Fintype.card n * Fintype.card m,
      ∃ K : Fin r → Matrix m n ℂ, ∀ A, Φ A = ∑ a, K a * A * (K a)ᴴ :=
  ⟨_, (rank_le_card_width (choiMatrix Φ)).trans_eq (Fintype.card_prod n m), hΦ.exists_kraus_rank⟩

/-- **Choi–Kraus theorem**: a linear map `Φ : M_n(ℂ) → M_m(ℂ)` is completely positive iff it has
a Kraus representation `Φ(A) = Σₐ Kₐ A Kₐᴴ` with at most `nm` operators. -/
theorem isCompletelyPositive_iff_exists_kraus {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ} :
    IsCompletelyPositive Φ ↔ ∃ r ≤ Fintype.card n * Fintype.card m,
      ∃ K : Fin r → Matrix m n ℂ, ∀ A, Φ A = ∑ a, K a * A * (K a)ᴴ :=
  ⟨IsCompletelyPositive.exists_kraus, fun ⟨_, _, K, hK⟩ => isCompletelyPositive_of_kraus K hK⟩

end Matrix
