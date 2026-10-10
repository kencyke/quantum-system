/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.CStarAlgebra.CompletelyPositiveMap.Stinespring
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.CStarMatrix
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.Matrix

/-!
# The Choi–Kraus theorem

For a linear map `Φ : M_n(ℂ) → M_m(ℂ)` the following are equivalent:
1. `Φ` is completely positive;
2. `Φ` is `k`-positive (`KPositiveMap`) for some `k ≥ min(n, m)`: applied entrywise, it preserves
   nonnegativity in the C⋆-algebra `CStarMatrix (Fin k) (Fin k) (Matrix n n ℂ)` of `k × k` block
   matrices, for the single block size `k`; equivalently `id_k ⊗ Φ` is positive, the flattened
   `kn × kn` matrices staying positive semidefinite
   (`KPositiveMap.exists_coe_eq_iff_forall_posSemidef_comp_map`);
3. its Choi matrix `J(Φ) = Σᵢⱼ Eᵢⱼ ⊗ Φ(Eᵢⱼ)` is positive semidefinite;
4. `Φ` has a Kraus representation `Φ(A) = Σₐ Kₐ A Kₐᴴ` with at most `nm` operators; indeed with
   exactly `rank J(Φ)` operators, the minimal number: every Kraus representation of `Φ` has at
   least `rank J(Φ)` operators.

## Derivation from bounded operators

These are corollaries of the Choi–Kraus theorem for bounded operators on finite-dimensional
Hilbert spaces (`QuantumSystem/Analysis/CStarAlgebra/CompletelyPositiveMap/Choi.lean` and
`QuantumSystem/Analysis/CStarAlgebra/CompletelyPositiveMap/Stinespring.lean`). The ⋆-isomorphism
`Matrix.toEuclideanCLM : M_n(ℂ) ≃ B(ℂⁿ)` turns `Φ` into its **operator form**
`Ψ : B(ℂⁿ) → B(ℂᵐ)`, `Ψ(A') = Φ(A)'` for the operator `A'` of each matrix `A`:
* complete and `k`-positivity transport along it (`CompletelyPositiveMap.arrowCongr`,
  `KPositiveMap.arrowCongr`);
* a Kraus representation by matrices `Kₐ` is one by their operators `K'ₐ`
  (`Matrix.toEuclideanCLM_mul_mul_conjTranspose`);
* the Choi matrix `J(Φ)` is the matrix of the Choi operator `J_e(Ψ)` in the product `e ⊗ e'` of the
  standard bases of `ℂⁿ` and `ℂᵐ` (`Matrix.choiMatrix_eq_toMatrix_choi`), so it has the positivity
  and the rank of `J_e(Ψ)`.

## Main definitions

* `Matrix.choiMatrix Φ`: the Choi matrix `J(Φ) ((i, b), (j, b')) = Φ(Eᵢⱼ) b b'`.

## Main statements

* `Matrix.choiMatrix_eq_sum_kronecker`: `J(Φ) = Σᵢⱼ Eᵢⱼ ⊗ Φ(Eᵢⱼ)`.
* `Matrix.choiMatrix_eq_toMatrix_choi`: the Choi matrix is the matrix of the Choi operator of the
  operator form; hence `Matrix.posSemidef_choiMatrix_iff_nonneg_choi` and
  `Matrix.rank_choiMatrix_eq_finrank_range_choi`.
* `KPositiveMap.exists_coe_eq_iff_forall_posSemidef_comp_map`: `k`-positivity is positivity of
  `id_k ⊗ Φ` on flattened `kn × kn` matrices.
* `Matrix.rank_choiMatrix_le_card_of_kraus`: every Kraus representation has at least `rank J(Φ)`
  operators; `Matrix.rank_choiMatrix_eq_card_iff_linearIndependent`: exactly `rank J(Φ)` iff the
  Kraus operators are linearly independent.

**Choi's theorem**, where a linear map `Φ` is completely positive when it is the linear map of
some `φ : Matrix n n ℂ →CP Matrix m m ℂ`:

* `CompletelyPositiveMap.exists_coe_eq_iff_posSemidef_choiMatrix`: 1 ⟺ 3.
* `CompletelyPositiveMap.exists_coe_eq_iff_exists_kPositiveMap`: 1 ⟺ 2;
  `CompletelyPositiveMap.exists_coe_eq_iff_forall_posSemidef_comp_map`: the same with `id_k ⊗ Φ`
  positive on flattened matrices, Choi's original form.
* `CompletelyPositiveMap.exists_coe_eq_iff_exists_kraus`: 1 ⟺ 4.

The two directions separately, for a completely positive map `φ` (1 ⇒ 2, 4) and for a linear map
`Φ` with the data of 4 (4 ⇒ 1):

* `CompletelyPositiveMapClass.instKPositiveMapClass`: a completely positive map is `k`-positive for
  every block size `k`.
* `CompletelyPositiveMap.exists_kraus_rank`: a CP map has a Kraus representation with exactly
  `rank J(φ)` operators, the minimal number by `Matrix.rank_choiMatrix_le_card_of_kraus`.
* `CompletelyPositiveMap.exists_coe_eq_of_kraus`: a map with a Kraus representation, indexed by any
  finite type, is CP.

## Implementation notes

The Choi matrix uses Choi's ordering of the tensor factors, input first: `Σᵢⱼ Eᵢⱼ ⊗ Φ(Eᵢⱼ)`, as
the Choi operator `ContinuousLinearMap.choi` does. Watrous uses the opposite order
`Σᵢⱼ Φ(Eᵢⱼ) ⊗ Eᵢⱼ`; the two differ by a swap of tensor factors, a unitary conjugation, so positive
semidefiniteness is unaffected.

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

/-! ### The Choi matrix and the Choi operator -/

section ChoiOperator

open InnerProductSpace TensorProduct
open scoped TensorProduct InnerProductSpace

variable {G : Type*} [FunLike G (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
  (EuclideanSpace ℂ m →L[ℂ] EuclideanSpace ℂ m)]

/-- The Choi matrix is the matrix of the Choi operator: if `Ψ : B(ℂⁿ) → B(ℂᵐ)` is the operator form
of `Φ : M_n(ℂ) → M_m(ℂ)`, `Ψ(A') = Φ(A)'` for the operator `A' = Matrix.toEuclideanCLM A` of each
matrix `A`, then `J(Φ)` is the matrix of the Choi operator `J_e(Ψ)` (`ContinuousLinearMap.choi`)
in the product `e ⊗ e'` of the standard bases. Its entries are
`⟪eᵢ ⊗ e'ₖ, J_e(Ψ) (eⱼ ⊗ e'ₗ)⟫ = ⟪e'ₖ, Ψ(|eᵢ⟩⟨eⱼ|) e'ₗ⟫ = Φ(Eᵢⱼ) k l`
(`ContinuousLinearMap.adjoint_mkL_comp_choi_comp_mkL`, `Matrix.toEuclideanCLM_single`). -/
lemma choiMatrix_eq_toMatrix_choi {Φ : F} {Ψ : G}
    (h : ∀ A, Ψ (toEuclideanCLM (𝕜 := ℂ) A) = toEuclideanCLM (𝕜 := ℂ) (Φ A)) :
    choiMatrix Φ =
      LinearMap.toMatrix
        ((EuclideanSpace.basisFun n ℂ).tensorProduct (EuclideanSpace.basisFun m ℂ)).toBasis
        ((EuclideanSpace.basisFun n ℂ).tensorProduct (EuclideanSpace.basisFun m ℂ)).toBasis
        (ContinuousLinearMap.choi (EuclideanSpace.basisFun n ℂ) Ψ :
          EuclideanSpace ℂ n ⊗[ℂ] EuclideanSpace ℂ m →ₗ[ℂ] EuclideanSpace ℂ n ⊗[ℂ] EuclideanSpace ℂ m) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.tensorProduct_apply, OrthonormalBasis.tensorProduct_apply,
    ContinuousLinearMap.coe_coe, ← mkL_apply_apply, ← mkL_apply_apply,
    ← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.comp_apply,
    ← ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_assoc,
    ContinuousLinearMap.adjoint_mkL_comp_choi_comp_mkL]
  simp [← toEuclideanCLM_single, h, choiMatrix, EuclideanSpace.inner_single_left]

/-- The Choi matrix is positive semidefinite iff the Choi operator `J_e(Ψ)` of the operator form
`Ψ` is positive (`Matrix.choiMatrix_eq_toMatrix_choi`). -/
lemma posSemidef_choiMatrix_iff_nonneg_choi {Φ : F} {Ψ : G}
    (h : ∀ A, Ψ (toEuclideanCLM (𝕜 := ℂ) A) = toEuclideanCLM (𝕜 := ℂ) (Φ A)) :
    (choiMatrix Φ).PosSemidef ↔ 0 ≤ ContinuousLinearMap.choi (EuclideanSpace.basisFun n ℂ) Ψ := by
  rw [choiMatrix_eq_toMatrix_choi h, LinearMap.posSemidef_toMatrix_iff,
    ContinuousLinearMap.isPositive_toLinearMap_iff, ContinuousLinearMap.nonneg_iff_isPositive]

/-- The rank of the Choi matrix is the rank of the Choi operator `J_e(Ψ)` of the operator form `Ψ`
(`Matrix.choiMatrix_eq_toMatrix_choi`). -/
lemma rank_choiMatrix_eq_finrank_range_choi {Φ : F} {Ψ : G}
    (h : ∀ A, Ψ (toEuclideanCLM (𝕜 := ℂ) A) = toEuclideanCLM (𝕜 := ℂ) (Φ A)) :
    (choiMatrix Φ).rank = Module.finrank ℂ (LinearMap.range
      (ContinuousLinearMap.choi (EuclideanSpace.basisFun n ℂ) Ψ :
        EuclideanSpace ℂ n ⊗[ℂ] EuclideanSpace ℂ m →ₗ[ℂ] EuclideanSpace ℂ n ⊗[ℂ] EuclideanSpace ℂ m)) := by
  rw [choiMatrix_eq_toMatrix_choi h, rank_eq_finrank_range_toLin _
    ((EuclideanSpace.basisFun n ℂ).tensorProduct (EuclideanSpace.basisFun m ℂ)).toBasis
    ((EuclideanSpace.basisFun n ℂ).tensorProduct (EuclideanSpace.basisFun m ℂ)).toBasis,
    toLin_toMatrix]

/-- The operator form of a Kraus map `A ↦ Σₐ Kₐ A Kₐᴴ` is the Kraus map of the operators
`K'ₐ : ℂⁿ →L ℂᵐ` of the `Kₐ` (`Matrix.toEuclideanCLM_mul_mul_conjTranspose`). -/
private lemma toEuclideanCLM_sum_mul_mul_conjTranspose {ι : Type*} [Fintype ι]
    (K : ι → Matrix m n ℂ) (A : Matrix n n ℂ) :
    toEuclideanCLM (𝕜 := ℂ) (∑ a, K a * A * (K a)ᴴ) =
      CompletelyPositiveMap.ofKraus (fun a => LinearMap.toContinuousLinearMap (toEuclideanLin (K a)))
        (toEuclideanCLM (𝕜 := ℂ) A) := by
  rw [map_sum, CompletelyPositiveMap.ofKraus_apply]
  simp only [toEuclideanCLM_mul_mul_conjTranspose]

omit [DecidableEq m] in
/-- Every Kraus representation `Φ(A) = Σₐ Kₐ A Kₐᴴ` has at least `rank J(Φ)` operators: its
operators `K'ₐ` are a Kraus representation of the operator form
(`ContinuousLinearMap.finrank_range_choi_le_card`). -/
lemma rank_choiMatrix_le_card_of_kraus {Φ : F} {ι : Type*} [Fintype ι] (K : ι → Matrix m n ℂ)
    (hK : ∀ A, Φ A = ∑ a, K a * A * (K a)ᴴ) :
    (choiMatrix Φ).rank ≤ Fintype.card ι := by
  classical
  set T : ι → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ m :=
    fun a => LinearMap.toContinuousLinearMap (toEuclideanLin (K a))
  have h (A : Matrix n n ℂ) : CompletelyPositiveMap.ofKraus T (toEuclideanCLM (𝕜 := ℂ) A) =
      toEuclideanCLM (𝕜 := ℂ) (Φ A) := by
    rw [hK, toEuclideanCLM_sum_mul_mul_conjTranspose]
  rw [rank_choiMatrix_eq_finrank_range_choi h]
  exact ContinuousLinearMap.finrank_range_choi_le_card _ (CompletelyPositiveMap.ofKraus_apply T)

omit [DecidableEq m] in
/-- A Kraus representation `Φ(A) = Σₐ Kₐ A Kₐᴴ` has exactly the minimal number `rank J(Φ)` of
operators iff its Kraus operators are linearly independent: so are their operators `K'ₐ`, a Kraus
representation of the operator form
(`ContinuousLinearMap.finrank_range_choi_eq_card_iff_linearIndependent`). -/
lemma rank_choiMatrix_eq_card_iff_linearIndependent {Φ : F} {ι : Type*} [Fintype ι]
    (K : ι → Matrix m n ℂ) (hK : ∀ A, Φ A = ∑ a, K a * A * (K a)ᴴ) :
    (choiMatrix Φ).rank = Fintype.card ι ↔ LinearIndependent ℂ K := by
  classical
  set T : ι → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ m :=
    fun a => LinearMap.toContinuousLinearMap (toEuclideanLin (K a))
  have h (A : Matrix n n ℂ) : CompletelyPositiveMap.ofKraus T (toEuclideanCLM (𝕜 := ℂ) A) =
      toEuclideanCLM (𝕜 := ℂ) (Φ A) := by
    rw [hK, toEuclideanCLM_sum_mul_mul_conjTranspose]
  rw [rank_choiMatrix_eq_finrank_range_choi h,
    ContinuousLinearMap.finrank_range_choi_eq_card_iff_linearIndependent _
      (CompletelyPositiveMap.ofKraus_apply T)]
  exact LinearMap.linearIndependent_iff
    ((LinearMap.toContinuousLinearMap : (EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ m) ≃ₗ[ℂ] _).toLinearMap ∘ₗ
      (toEuclideanLin : Matrix m n ℂ ≃ₗ[ℂ] _).toLinearMap)
    (by simp)

end ChoiOperator

end Matrix

/-! ### `k`-positivity in matrix form -/

namespace KPositiveMap

open Matrix
open scoped ComplexOrder CStarAlgebra

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- **`k`-positivity in Choi's form**: a linear map `Φ : M_n(ℂ) → M_m(ℂ)` is `k`-positive iff
`id_k ⊗ Φ` is positive, that is, applying `Φ` entrywise to a `k × k` block matrix `X` whose
flattening is a positive semidefinite `kn × kn` matrix gives a block matrix whose flattening is a
positive semidefinite `km × km` matrix. The order of `CStarMatrix (Fin k) (Fin k) (Matrix n n ℂ)`
in the definition of `KPositiveMap` is positive semidefiniteness of the flattening
(`CStarMatrix.nonneg_iff_posSemidef_comp`). -/
theorem exists_coe_eq_iff_forall_posSemidef_comp_map (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) (k : ℕ) :
    (∃ ψ : KPositiveMap k (Matrix n n ℂ) (Matrix m m ℂ),
        (ψ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) = Φ) ↔
      ∀ X : Matrix (Fin k) (Fin k) (Matrix n n ℂ), (Matrix.comp _ _ n n ℂ X).PosSemidef →
        (Matrix.comp _ _ m m ℂ (X.map Φ)).PosSemidef := by
  constructor
  · rintro ⟨ψ, rfl⟩ X hX
    exact CStarMatrix.nonneg_iff_posSemidef_comp.1 <|
      ψ.map_cstarMatrix_nonneg' (CStarMatrix.ofMatrix X)
        (CStarMatrix.nonneg_iff_posSemidef_comp.2 hX)
  · intro h
    refine ⟨⟨Φ, fun M hM => ?_⟩, rfl⟩
    rw [CStarMatrix.nonneg_iff_posSemidef_comp] at hM ⊢
    exact h M hM

end KPositiveMap

/-! ### Choi's theorem for completely positive maps -/

namespace CompletelyPositiveMap

open Matrix
open scoped ComplexOrder Kronecker CStarAlgebra

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-- The operator form `A' ↦ Φ(A)'` of a linear map `Φ` of matrices, along the ⋆-isomorphisms
`Matrix.toEuclideanCLM`. -/
private lemma arrowCongr_toEuclideanCLM_apply (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (A : Matrix n n ℂ) :
    (toEuclideanCLM (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv.arrowCongr
      (toEuclideanCLM (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv Φ
      (toEuclideanCLM (𝕜 := ℂ) A) = toEuclideanCLM (𝕜 := ℂ) (Φ A) := by
  simp

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- A linear map `Φ` of matrices is completely positive iff its operator form
`Ψ : B(ℂⁿ) → B(ℂᵐ)` is: completely positive maps transport along the ⋆-isomorphisms
`Matrix.toEuclideanCLM` (`CompletelyPositiveMap.arrowCongr`). -/
private lemma exists_coe_eq_iff_toEuclideanCLM {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ}
    {Ψ : (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) →ₗ[ℂ]
      (EuclideanSpace ℂ m →L[ℂ] EuclideanSpace ℂ m)}
    (h : ∀ A, Ψ (toEuclideanCLM (𝕜 := ℂ) A) = toEuclideanCLM (𝕜 := ℂ) (Φ A)) :
    (∃ φ : Matrix n n ℂ →CP Matrix m m ℂ, (φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) = Φ) ↔
      ∃ ψ : (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) →CP
          (EuclideanSpace ℂ m →L[ℂ] EuclideanSpace ℂ m),
        (ψ : (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) →ₗ[ℂ]
          (EuclideanSpace ℂ m →L[ℂ] EuclideanSpace ℂ m)) = Ψ := by
  constructor
  · rintro ⟨φ, rfl⟩
    refine ⟨arrowCongr (toEuclideanCLM (𝕜 := ℂ)) (toEuclideanCLM (𝕜 := ℂ)) φ,
      LinearMap.ext fun X => ?_⟩
    obtain ⟨A, rfl⟩ := EquivLike.surjective (toEuclideanCLM (𝕜 := ℂ)) X
    rw [h]
    simp
  · rintro ⟨ψ, rfl⟩
    refine ⟨(arrowCongr (toEuclideanCLM (𝕜 := ℂ)) (toEuclideanCLM (𝕜 := ℂ))).symm ψ,
      LinearMap.ext fun A => EquivLike.injective (toEuclideanCLM (𝕜 := ℂ)) ?_⟩
    rw [← h]
    simp

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- A linear map with a Kraus representation `Φ(A) = Σₐ Kₐ A Kₐᴴ`, indexed by any finite type, is
completely positive: its operator form is the Kraus map of the operators of the `Kₐ`
(`CompletelyPositiveMap.ofKraus`). -/
lemma exists_coe_eq_of_kraus (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) {ι : Type*} [Fintype ι]
    (K : ι → Matrix m n ℂ) (hK : ∀ A, Φ A = ∑ a, K a * A * (K a)ᴴ) :
    ∃ φ : Matrix n n ℂ →CP Matrix m m ℂ, (φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) = Φ := by
  refine (exists_coe_eq_iff_toEuclideanCLM (arrowCongr_toEuclideanCLM_apply Φ)).2
    ⟨ofKraus fun a => LinearMap.toContinuousLinearMap (toEuclideanLin (K a)),
      LinearMap.ext fun X => ?_⟩
  obtain ⟨A, rfl⟩ := EquivLike.surjective (toEuclideanCLM (𝕜 := ℂ)) X
  rw [arrowCongr_toEuclideanCLM_apply, hK, toEuclideanCLM_sum_mul_mul_conjTranspose]
  rfl

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- A completely positive map has a Kraus representation `φ(A) = Σₐ Kₐ A Kₐᴴ` with exactly
`rank J(φ)` operators. This is the minimal number (`Matrix.rank_choiMatrix_le_card_of_kraus`). The
`Kₐ` are the matrices of Kraus operators of the operator form of `φ`
(`CompletelyPositiveMap.exists_kraus_finrank_range_choi`). -/
lemma exists_kraus_rank (φ : Matrix n n ℂ →CP Matrix m m ℂ) :
    ∃ K : Fin (choiMatrix φ).rank → Matrix m n ℂ, ∀ A, φ A = ∑ a, K a * A * (K a)ᴴ := by
  set ψ := arrowCongr (toEuclideanCLM (𝕜 := ℂ)) (toEuclideanCLM (𝕜 := ℂ)) φ
  have hψ (A : Matrix n n ℂ) : ψ (toEuclideanCLM (𝕜 := ℂ) A) =
      toEuclideanCLM (𝕜 := ℂ) (φ A) := by
    simp [ψ]
  rw [rank_choiMatrix_eq_finrank_range_choi hψ]
  have hT := exists_kraus_finrank_range_choi (EuclideanSpace.basisFun n ℂ) ψ
  obtain ⟨T, hT⟩ := hT
  refine ⟨fun a => toEuclideanLin.symm (LinearMap.toContinuousLinearMap.symm (T a)),
    fun A => EquivLike.injective (toEuclideanCLM (𝕜 := ℂ)) ?_⟩
  rw [← hψ, hT, toEuclideanCLM_sum_mul_mul_conjTranspose, ofKraus_apply]
  simp only [LinearEquiv.apply_symm_apply]

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- **Choi's theorem**: a linear map `Φ : M_n(ℂ) → M_m(ℂ)` is completely positive, i.e. it is the
linear map of some `φ : M_n(ℂ) →CP M_m(ℂ)`, iff its Choi matrix `J(Φ)` is positive
semidefinite: the Choi operator of its operator form is positive
(`CompletelyPositiveMap.exists_coe_eq_iff_nonneg_choi`). -/
theorem exists_coe_eq_iff_posSemidef_choiMatrix (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    (∃ φ : Matrix n n ℂ →CP Matrix m m ℂ, (φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) = Φ) ↔
      (choiMatrix Φ).PosSemidef := by
  rw [exists_coe_eq_iff_toEuclideanCLM (arrowCongr_toEuclideanCLM_apply Φ),
    exists_coe_eq_iff_nonneg_choi (EuclideanSpace.basisFun n ℂ),
    posSemidef_choiMatrix_iff_nonneg_choi (arrowCongr_toEuclideanCLM_apply Φ)]

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- **Choi's theorem**, `min(n, m)`-positivity form: a linear map `Φ : M_n(ℂ) → M_m(ℂ)` is
completely positive iff it is `k`-positive, i.e. applied entrywise it preserves nonnegativity in the
C⋆-algebra `CStarMatrix (Fin k) (Fin k) (Matrix n n ℂ)` (`KPositiveMap`), equivalently `id_k ⊗ Φ`
is positive on flattened `kn × kn` matrices
(`CompletelyPositiveMap.exists_coe_eq_iff_forall_posSemidef_comp_map`), for a single block size
`k ≥ min(n, m)`. Its operator form is then `k`-positive (`KPositiveMap.arrowCongr`), hence
completely positive (`CompletelyPositiveMap.ofKPositiveMap`). -/
theorem exists_coe_eq_iff_exists_kPositiveMap (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    {k : ℕ} (hk : min (Fintype.card n) (Fintype.card m) ≤ k) :
    (∃ φ : Matrix n n ℂ →CP Matrix m m ℂ, (φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) = Φ) ↔
      ∃ ψ : KPositiveMap k (Matrix n n ℂ) (Matrix m m ℂ),
        (ψ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) = Φ := by
  refine ⟨fun ⟨φ, hφ⟩ => ⟨⟨φ.toLinearMap, φ.map_cstarMatrix_nonneg' _⟩, hφ⟩, ?_⟩
  rintro ⟨ψ, rfl⟩
  refine (exists_coe_eq_iff_toEuclideanCLM (arrowCongr_toEuclideanCLM_apply _)).2
    ⟨ofKPositiveMap
      (KPositiveMap.arrowCongr (toEuclideanCLM (𝕜 := ℂ)) (toEuclideanCLM (𝕜 := ℂ)) ψ)
      (by simpa [finrank_euclideanSpace] using hk), LinearMap.ext fun X => ?_⟩
  simp

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- **Choi's theorem** in Choi's original form: a linear map `Φ : M_n(ℂ) → M_m(ℂ)` is completely
positive iff `id_k ⊗ Φ` is positive for a single block size `k ≥ min(n, m)`, that is, it sends
`k × k` block matrices with positive semidefinite `kn × kn` flattening to block matrices with
positive semidefinite `km × km` flattening
(`CompletelyPositiveMap.exists_coe_eq_iff_exists_kPositiveMap`,
`KPositiveMap.exists_coe_eq_iff_forall_posSemidef_comp_map`). -/
theorem exists_coe_eq_iff_forall_posSemidef_comp_map (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    {k : ℕ} (hk : min (Fintype.card n) (Fintype.card m) ≤ k) :
    (∃ φ : Matrix n n ℂ →CP Matrix m m ℂ, (φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) = Φ) ↔
      ∀ X : Matrix (Fin k) (Fin k) (Matrix n n ℂ), (Matrix.comp _ _ n n ℂ X).PosSemidef →
        (Matrix.comp _ _ m m ℂ (X.map Φ)).PosSemidef :=
  (exists_coe_eq_iff_exists_kPositiveMap Φ hk).trans
    (KPositiveMap.exists_coe_eq_iff_forall_posSemidef_comp_map Φ k)

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- **Choi–Kraus theorem**: a linear map `Φ : M_n(ℂ) → M_m(ℂ)` is completely positive iff it has
a Kraus representation `Φ(A) = Σₐ Kₐ A Kₐᴴ` with at most `nm` operators. -/
theorem exists_coe_eq_iff_exists_kraus (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    (∃ φ : Matrix n n ℂ →CP Matrix m m ℂ, (φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) = Φ) ↔
      ∃ r ≤ Fintype.card n * Fintype.card m,
        ∃ K : Fin r → Matrix m n ℂ, ∀ A, Φ A = ∑ a, K a * A * (K a)ᴴ :=
  ⟨fun ⟨φ, hφ⟩ => hφ ▸ ⟨_, (rank_le_card_width (choiMatrix φ)).trans_eq (Fintype.card_prod n m),
    φ.exists_kraus_rank⟩, fun ⟨_, _, K, hK⟩ => exists_coe_eq_of_kraus Φ K hK⟩

end CompletelyPositiveMap
