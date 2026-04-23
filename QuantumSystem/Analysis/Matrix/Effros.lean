module

public import Mathlib.Data.Matrix.Bilinear
public import QuantumSystem.Analysis.Matrix.Order

/-!
# Effros's Matrix Convexity Approach

This file formalises the Effros (2008) machinery used to prove Lieb's joint concavity theorem.

## Contents

1. **Compression lemmas** – `compression_pow_eq`, `compression_aeval_eq`,
   `eigenvalues_compression_subset`, and `matrixFunction_compression_of_commuting`:
   the map `X ↦ V† X V` (sandwiching) interacts well with polynomial/functional calculus
   when `V†V = I` and `M` commutes with `VV†`.
2. **Block diagonal** – `compression_of_fromBlocks_cfc` and related CFC lemmas.
3. **`lownerConvex_compression_le`** – the fundamental inequality
   `f(V†TV) ≤ V†f(T)V` when `V†V ≤ I`, `f` is Löwner convex, and `f(0) ≤ 0`.
4. **`isJensenConvex_of_isLownerConvex`** – Löwner convexity implies Jensen/HPJ
   convexity (Effros 2008, Theorem 3.1; Hansen–Pedersen 1981).
5. **`neg_rpow_isJensenConvex`** – `f(t) = −tˢ` is Jensen convex for `0 < s ≤ 1`.
6. **`hpj_subhomogeneous`**, **`hpj_affine`** – concrete HPJ inequality instances.

## References

* Effros, *A Matrix Convexity Approach to Some Celebrated Quantum Inequalities* (2008)
* Hansen, Pedersen, *Jensen's operator inequality* (2003)
-/
@[expose] public section

namespace Matrix

open Real NNReal MeasureTheory Set
open scoped MatrixOrder ComplexOrder Kronecker

/-- Left multiplication operator on matrices. -/
noncomputable def leftMul {m : Type*} [Fintype m]
    (A : Matrix m m ℂ) : Matrix m m ℂ →ₗ[ℂ] Matrix m m ℂ :=
  mulLeftLinearMap m ℂ A

/-- Right multiplication operator on matrices. -/
noncomputable def rightMul {m : Type*} [Fintype m]
    (B : Matrix m m ℂ) : Matrix m m ℂ →ₗ[ℂ] Matrix m m ℂ :=
  mulRightLinearMap m ℂ B

/-- `leftMul A` applied to a matrix `X` yields `A * X`. -/
@[simp] lemma leftMul_apply {m : Type*} [Fintype m]
    (A X : Matrix m m ℂ) : leftMul A X = A * X := by
  simp [leftMul]

/-- `rightMul B` applied to a matrix `X` yields `X * B`. -/
@[simp] lemma rightMul_apply {m : Type*} [Fintype m]
    (B X : Matrix m m ℂ) : rightMul B X = X * B := by
  simp [rightMul]

/-- Left and right multiplication operators commute as linear maps. -/
lemma leftMul_rightMul_commute {m : Type*} [Fintype m]
    (A B : Matrix m m ℂ) :
    leftMul A ∘ₗ rightMul B = rightMul B ∘ₗ leftMul A := by
  simpa [leftMul, rightMul] using
    (commute_mulLeftLinearMap_mulRightLinearMap (R := ℂ) (a := A) (b := B))

/-- Standard basis on `Matrix m m ℂ`, used to represent linear maps as matrices. -/
noncomputable def matrixBasis (m : Type*) [Fintype m] [DecidableEq m] :
  Module.Basis (m × m) ℂ (Matrix m m ℂ) :=
  Matrix.stdBasis ℂ m m

/-- Matrix representation of left multiplication with respect to the standard basis. -/
noncomputable def leftMulMatrix {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℂ) : Matrix (m × m) (m × m) ℂ :=
  LinearMap.toMatrix (matrixBasis m) (matrixBasis m) (leftMul A)

/-- Matrix representation of right multiplication with respect to the standard basis. -/
noncomputable def rightMulMatrix {m : Type*} [Fintype m] [DecidableEq m]
    (B : Matrix m m ℂ) : Matrix (m × m) (m × m) ℂ :=
  LinearMap.toMatrix (matrixBasis m) (matrixBasis m) (rightMul B)

/-- Shorthand for `leftMulMatrix`. Corresponds to L_A in Effros (2008). -/
notation "𝐋" => leftMulMatrix

/-- Shorthand for `rightMulMatrix`. Corresponds to R_B in Effros (2008). -/
notation "𝐑" => rightMulMatrix

/-- Matrix representations of left and right multiplication commute. -/
lemma leftMulMatrix_rightMulMatrix_commute {m : Type*} [Fintype m] [DecidableEq m]
    (A B : Matrix m m ℂ) :
    𝐋 A * 𝐑 B = 𝐑 B * 𝐋 A := by
  classical
  have hcomp_left :
      LinearMap.toMatrix (matrixBasis m) (matrixBasis m) (leftMul A ∘ₗ rightMul B) =
        𝐋 A * 𝐑 B := by
    simpa [leftMulMatrix, rightMulMatrix] using
      (LinearMap.toMatrix_comp (v₁ := matrixBasis m) (v₂ := matrixBasis m)
        (v₃ := matrixBasis m) (f := leftMul A) (g := rightMul B))
  have hcomp_right :
      LinearMap.toMatrix (matrixBasis m) (matrixBasis m) (rightMul B ∘ₗ leftMul A) =
        𝐑 B * 𝐋 A := by
    simpa [leftMulMatrix, rightMulMatrix] using
      (LinearMap.toMatrix_comp (v₁ := matrixBasis m) (v₂ := matrixBasis m)
        (v₃ := matrixBasis m) (f := rightMul B) (g := leftMul A))
  have hcomm := congrArg
    (fun f => LinearMap.toMatrix (matrixBasis m) (matrixBasis m) f)
    (leftMul_rightMul_commute (A := A) (B := B))
  simpa [hcomp_left, hcomp_right] using hcomm

/-- leftMulMatrix is additive: leftMulMatrix (A + B) = leftMulMatrix A + leftMulMatrix B -/
theorem leftMulMatrix_add {m : Type*} [Fintype m] [DecidableEq m]
    (A B : Matrix m m ℂ) :
    𝐋 (A + B) = 𝐋 A + 𝐋 B := by
  simp only [leftMulMatrix]
  have h : leftMul (A + B) = leftMul A + leftMul B := by
    ext X; simp [leftMul, add_mul]
  rw [h]
  exact (LinearMap.toMatrix (matrixBasis m) (matrixBasis m)).map_add (leftMul A) (leftMul B)

/-- leftMulMatrix is homogeneous: leftMulMatrix (c • A) = c • leftMulMatrix A -/
lemma leftMulMatrix_smul {m : Type*} [Fintype m] [DecidableEq m]
    (c : ℂ) (A : Matrix m m ℂ) :
    𝐋 (c • A) = c • 𝐋 A := by
  simp only [leftMulMatrix]
  have h : leftMul (c • A) = c • leftMul A := by
    ext X; simp [leftMul]
  rw [h]
  exact (LinearMap.toMatrix (matrixBasis m) (matrixBasis m)).map_smul c (leftMul A)

/-- rightMulMatrix is additive: rightMulMatrix (A + B) = rightMulMatrix A + rightMulMatrix B -/
theorem rightMulMatrix_add {m : Type*} [Fintype m] [DecidableEq m]
    (A B : Matrix m m ℂ) :
    𝐑 (A + B) = 𝐑 A + 𝐑 B := by
  simp only [rightMulMatrix]
  have h : rightMul (A + B) = rightMul A + rightMul B := by
    ext X; simp [rightMul, mul_add]
  rw [h]
  exact (LinearMap.toMatrix (matrixBasis m) (matrixBasis m)).map_add (rightMul A) (rightMul B)

/-- rightMulMatrix is homogeneous: rightMulMatrix (c • A) = c • rightMulMatrix A -/
lemma rightMulMatrix_smul {m : Type*} [Fintype m] [DecidableEq m]
    (c : ℂ) (A : Matrix m m ℂ) :
    𝐑 (c • A) = c • 𝐑 A := by
  simp only [rightMulMatrix]
  have h : rightMul (c • A) = c • rightMul A := by
    ext X; simp [rightMul]
  rw [h]
  exact (LinearMap.toMatrix (matrixBasis m) (matrixBasis m)).map_smul c (rightMul A)

/-- leftMulMatrix is homogeneous for real scalars -/
theorem leftMulMatrix_smul_real {m : Type*} [Fintype m] [DecidableEq m]
    (r : ℝ) (A : Matrix m m ℂ) :
    𝐋 (r • A) = r • 𝐋 A := by
  have h : (r : ℂ) • A = r • A := by
    ext i j
    simp [Complex.real_smul]
  rw [← h, leftMulMatrix_smul]
  ext i j
  simp [Complex.real_smul]

/-- rightMulMatrix is homogeneous for real scalars -/
theorem rightMulMatrix_smul_real {m : Type*} [Fintype m] [DecidableEq m]
    (r : ℝ) (A : Matrix m m ℂ) :
    𝐑 (r • A) = r • 𝐑 A := by
  have h : (r : ℂ) • A = r • A := by
    ext i j
    simp [Complex.real_smul]
  rw [← h, rightMulMatrix_smul]
  ext i j
  simp [Complex.real_smul]

/-- leftMulMatrix is multiplicative: leftMulMatrix (A * B) = leftMulMatrix A * leftMulMatrix B -/
lemma leftMulMatrix_mul {m : Type*} [Fintype m] [DecidableEq m]
    (A B : Matrix m m ℂ) :
    𝐋 (A * B) = 𝐋 A * 𝐋 B := by
  simp only [leftMulMatrix]
  have h : leftMul (A * B) = (leftMul A).comp (leftMul B) := by
    ext X; simp [leftMul]
  rw [h, LinearMap.toMatrix_comp (matrixBasis m) (matrixBasis m) (matrixBasis m)]

/-- leftMulMatrix maps identity to identity -/
lemma leftMulMatrix_one {m : Type*} [Fintype m] [DecidableEq m] :
    𝐋 (1 : Matrix m m ℂ) = (1 : Matrix (m × m) (m × m) ℂ) := by
  simp only [leftMulMatrix]
  have h : leftMul (1 : Matrix m m ℂ) = LinearMap.id := by
    ext X; simp [leftMul]
  rw [h, LinearMap.toMatrix_id (matrixBasis m)]

/-- rightMulMatrix is anti-multiplicative:
    rightMulMatrix (A * B) = rightMulMatrix B * rightMulMatrix A -/
lemma rightMulMatrix_mul {m : Type*} [Fintype m] [DecidableEq m]
    (A B : Matrix m m ℂ) :
    𝐑 (A * B) = 𝐑 B * 𝐑 A := by
  simp only [rightMulMatrix]
  have h : rightMul (A * B) = (rightMul B).comp (rightMul A) := by
    ext X; simp [rightMul, Matrix.mul_assoc]
  rw [h, LinearMap.toMatrix_comp (matrixBasis m) (matrixBasis m) (matrixBasis m)]

/-- rightMulMatrix maps identity to identity -/
lemma rightMulMatrix_one {m : Type*} [Fintype m] [DecidableEq m] :
    𝐑 (1 : Matrix m m ℂ) = (1 : Matrix (m × m) (m × m) ℂ) := by
  simp only [rightMulMatrix]
  have h : rightMul (1 : Matrix m m ℂ) = LinearMap.id := by
    ext X; simp [rightMul]
  rw [h, LinearMap.toMatrix_id (matrixBasis m)]


/-- rightMulMatrix preserves powers: rightMulMatrix (B ^ n) = (rightMulMatrix B) ^ n -/
lemma rightMulMatrix_pow {m : Type*} [Fintype m] [DecidableEq m]
    (B : Matrix m m ℂ) (n : ℕ) :
    𝐑 (B ^ n) = (𝐑 B) ^ n := by
  induction n with
  | zero => simp [rightMulMatrix_one]
  | succ n ih =>
    rw [pow_succ, rightMulMatrix_mul, ih, ← pow_succ']

/-- leftMulMatrix preserves powers: leftMulMatrix (A ^ n) = (leftMulMatrix A) ^ n -/
lemma leftMulMatrix_pow {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℂ) (n : ℕ) :
    𝐋 (A ^ n) = (𝐋 A) ^ n := by
  induction n with
  | zero => simp [leftMulMatrix_one]
  | succ n ih =>
    rw [pow_succ, leftMulMatrix_mul, ih]
    rw [pow_succ]

/-- The standard basis element at index `(i, j)` is the matrix with `1` at `(i, j)` and `0` elsewhere. -/
lemma matrixBasis_apply_eq_single {m : Type*} [Fintype m] [DecidableEq m] (ij : m × m) :
    matrixBasis m ij = Matrix.single ij.1 ij.2 (1 : ℂ) := by
  cases ij with
  | mk a b =>
      simp [matrixBasis, Matrix.stdBasis_eq_single]

/-- The basis representation of a matrix `M` at index `(i, j)` is `M i j`. -/
lemma matrixBasis_repr_apply {m : Type*} [Fintype m] [DecidableEq m]
    (M : Matrix m m ℂ) (i j : m) :
    (matrixBasis m).repr M (i, j) = M i j := by
  classical
  have hsum := congrArg (fun N => N i j) ((matrixBasis m).sum_repr M)
  have hsum' :
      (∑ ij : m × m,
          (matrixBasis m).repr M ij *
            (if ij.1 = i ∧ ij.2 = j then (1 : ℂ) else 0)) = M i j := by
    simpa [Matrix.sum_apply, Matrix.smul_apply, matrixBasis_apply_eq_single,
      Matrix.single, Matrix.of_apply, mul_comm, mul_left_comm, mul_assoc] using hsum
  have hcoeff :
      (∑ ij : m × m,
          (matrixBasis m).repr M ij *
            (if ij.1 = i ∧ ij.2 = j then (1 : ℂ) else 0)) =
        (matrixBasis m).repr M (i, j) := by
    classical
    let f : m × m → ℂ := fun ij =>
      (matrixBasis m).repr M ij * (if ij.1 = i ∧ ij.2 = j then (1 : ℂ) else 0)
    have hsumf : (∑ ij, f ij) = f (i, j) := by
      refine Fintype.sum_eq_single (i, j) ?_
      intro ij hij
      have hne : ¬ (ij.1 = i ∧ ij.2 = j) := by
        intro h
        apply hij
        cases ij with
        | mk a b =>
            cases h with
            | intro h1 h2 =>
                subst h1
                subst h2
                rfl
      simp [f, hne]
    simpa [f] using hsumf
  calc
    (matrixBasis m).repr M (i, j) =
        ∑ ij : m × m,
          (matrixBasis m).repr M ij *
            (if ij.1 = i ∧ ij.2 = j then (1 : ℂ) else 0) := by
      symm
      exact hcoeff
    _ = M i j := hsum'

/-- Entry `(i, j), (k, l)` of `leftMulMatrix A` equals `A i k` if `j = l`, else `0`. -/
theorem leftMulMatrix_apply {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℂ) (i j k l : m) :
    𝐋 A (i, j) (k, l) = if j = l then A i k else 0 := by
  classical
  have hrepr :
      𝐋 A (i, j) (k, l) = (A * Matrix.single k l (1 : ℂ)) i j := by
    simp only [leftMulMatrix, leftMul, LinearMap.toMatrix_apply, matrixBasis_apply_eq_single]
    exact matrixBasis_repr_apply ..
  rw [hrepr]
  by_cases hjl : j = l
  · subst hjl; simp
  · simp [hjl]

/-- Entry `(i, j), (k, l)` of `rightMulMatrix B` equals `B l j` if `i = k`, else `0`. -/
theorem rightMulMatrix_apply {m : Type*} [Fintype m] [DecidableEq m]
    (B : Matrix m m ℂ) (i j k l : m) :
    𝐑 B (i, j) (k, l) = if i = k then B l j else 0 := by
  classical
  have hrepr :
      𝐑 B (i, j) (k, l) = (Matrix.single k l (1 : ℂ) * B) i j := by
    simp only [rightMulMatrix, rightMul, LinearMap.toMatrix_apply, matrixBasis_apply_eq_single]
    exact matrixBasis_repr_apply ..
  rw [hrepr]
  by_cases hik : i = k
  · subst hik
    simp
  · simp [hik]

/-- Action of `leftMulMatrix A` on the vectorized form of `Kᴴ` yields `(A * Kᴴ) i j`. -/
lemma leftMulMatrix_mulVec_vecConjTranspose {m : Type*} [Fintype m] [DecidableEq m]
    (A K : Matrix m m ℂ) (i j : m) :
    (𝐋 A *ᵥ (fun x : m × m => Kᴴ x.1 x.2)) (i, j) = (A * Kᴴ) i j := by
  classical
  simp [Matrix.mulVec, dotProduct, leftMulMatrix_apply, Matrix.mul_apply, Fintype.sum_prod_type]

/-- Action of `rightMulMatrix B` on the vectorized form of `Kᴴ` yields `(Kᴴ * B) i j`. -/
lemma rightMulMatrix_mulVec_vecConjTranspose {m : Type*} [Fintype m] [DecidableEq m]
    (B K : Matrix m m ℂ) (i j : m) :
    (𝐑 B *ᵥ (fun x : m × m => Kᴴ x.1 x.2)) (i, j) = (Kᴴ * B) i j := by
  classical
  simp [Matrix.mulVec, dotProduct, rightMulMatrix_apply, Matrix.mul_apply, Fintype.sum_prod_type, mul_comm]

/-- Composite mulVec: (leftMulMatrix X * rightMulMatrix Y) *ᵥ vec(K†) = vec(X * K† * Y). -/
lemma leftRightMul_mulVec_vecConjTranspose {m : Type*} [Fintype m] [DecidableEq m]
    (X Y K : Matrix m m ℂ) :
    (𝐋 X * 𝐑 Y) *ᵥ (fun x : m × m => Kᴴ x.1 x.2) =
    fun x : m × m => (X * Kᴴ * Y) x.1 x.2 := by
  rw [← Matrix.mulVec_mulVec]
  have hR : 𝐑 Y *ᵥ (fun x : m × m => Kᴴ x.1 x.2) =
            fun x : m × m => (Kᴴ * Y) x.1 x.2 := by
    ext ⟨i, j⟩; exact rightMulMatrix_mulVec_vecConjTranspose Y K i j
  rw [hR]
  ext ⟨i, j⟩
  classical
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, leftMulMatrix_apply]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Matrix.mul_assoc]; rfl

/-- The quadratic form star(vec(K†)) ⬝ᵥ (leftMulMatrix X * rightMulMatrix Y) *ᵥ vec(K†)
equals Tr(K * X * K† * Y). -/
theorem quadForm_leftRightMul_eq_trace {m : Type*} [Fintype m] [DecidableEq m]
    (X Y K : Matrix m m ℂ) :
    let v : (m × m) → ℂ := fun x => Kᴴ x.1 x.2
    star v ⬝ᵥ ((leftMulMatrix X * rightMulMatrix Y) *ᵥ v) =
    (K * X * Kᴴ * Y).trace := by
  dsimp only
  rw [leftRightMul_mulVec_vecConjTranspose]
  simp only [dotProduct, Fintype.sum_prod_type, Pi.star_apply,
    Matrix.conjTranspose_apply, star_star]
  rw [Finset.sum_comm]
  conv_rhs => rw [Matrix.mul_assoc K X Kᴴ, Matrix.mul_assoc K (X * Kᴴ) Y]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]

/-- `leftMulMatrix A` equals the Kronecker product `A ⊗ₖ I`. -/
lemma leftMulMatrix_eq_kronecker_one {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℂ) :
    𝐋 A = A ⊗ₖ (1 : Matrix m m ℂ) := by
  classical
  ext ⟨i, j⟩ ⟨k, l⟩
  by_cases hjl : j = l
  · subst hjl
    simp [leftMulMatrix_apply, Matrix.kroneckerMap_apply]
  · simp [leftMulMatrix_apply, Matrix.kroneckerMap_apply, hjl]

/-- `rightMulMatrix B` equals the Kronecker product `I ⊗ₖ Bᵀ`. -/
lemma rightMulMatrix_eq_one_kronecker_transpose {m : Type*} [Fintype m] [DecidableEq m]
    (B : Matrix m m ℂ) :
    𝐑 B = (1 : Matrix m m ℂ) ⊗ₖ Bᵀ := by
  classical
  ext ⟨i, j⟩ ⟨k, l⟩
  by_cases hik : i = k
  · subst hik
    simp [rightMulMatrix_apply, Matrix.kroneckerMap_apply, Matrix.transpose_apply]
  · simp [rightMulMatrix_apply, Matrix.kroneckerMap_apply, Matrix.transpose_apply, hik]

/-- `leftMulMatrix` commutes with conjugate transpose: `leftMulMatrix (Aᴴ) = (leftMulMatrix A)ᴴ`. -/
lemma leftMulMatrix_conjTranspose {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℂ) :
    𝐋 (Aᴴ) = (𝐋 A)ᴴ := by
  classical
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [leftMulMatrix_apply, Matrix.conjTranspose_apply]
  by_cases hjl : j = l
  · subst hjl; simp
  · have hlj : ¬ l = j := Ne.symm hjl
    simp [hjl, hlj]

/-- `rightMulMatrix` commutes with conjugate transpose: `rightMulMatrix (Bᴴ) = (rightMulMatrix B)ᴴ`. -/
lemma rightMulMatrix_conjTranspose {m : Type*} [Fintype m] [DecidableEq m]
    (B : Matrix m m ℂ) :
    𝐑 (Bᴴ) = (𝐑 B)ᴴ := by
  classical
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [rightMulMatrix_apply, Matrix.conjTranspose_apply]
  by_cases hik : i = k
  · subst hik; simp
  · have hki : ¬ k = i := Ne.symm hik
    simp [hik, hki]

/-- `leftMulMatrix` preserves positive semidefiniteness. -/
theorem leftMulMatrix_posSemidef {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.PosSemidef) :
    (𝐋 A).PosSemidef := by
  classical
  simpa [leftMulMatrix_eq_kronecker_one] using
    (Matrix.PosSemidef.kronecker (m := m) (x := A) (y := (1 : Matrix m m ℂ)) hA posSemidef_one)

/-- `rightMulMatrix` preserves positive semidefiniteness. -/
lemma rightMulMatrix_posSemidef {m : Type*} [Fintype m] [DecidableEq m]
    {B : Matrix m m ℂ} (hB : B.PosSemidef) :
    (𝐑 B).PosSemidef := by
  classical
  have hB' : Bᵀ.PosSemidef := hB.transpose
  simpa [rightMulMatrix_eq_one_kronecker_transpose] using
    (Matrix.PosSemidef.kronecker (m := m) (x := (1 : Matrix m m ℂ)) (y := Bᵀ) posSemidef_one hB')

/-- `rightMulMatrix` preserves positive definiteness. -/
theorem rightMulMatrix_posDef {m : Type*} [Fintype m] [DecidableEq m]
    {B : Matrix m m ℂ} (hB : B.PosDef) :
    (𝐑 B).PosDef := by
  classical
  have hB' : Bᵀ.PosDef := hB.transpose
  simpa [rightMulMatrix_eq_one_kronecker_transpose] using
    (Matrix.PosDef.kronecker (m := m) (x := (1 : Matrix m m ℂ)) (y := Bᵀ) posDef_one hB')

/-- leftMulMatrix as a star algebra homomorphism over ℝ.
    This allows using the CFC infrastructure to relate
    leftMulMatrix (f(A)) = f(leftMulMatrix(A)) for continuous f. -/
noncomputable def leftMulStarAlgHom {m : Type*} [Fintype m] [DecidableEq m] :
    Matrix m m ℂ →⋆ₐ[ℝ] Matrix (m × m) (m × m) ℂ where
  toFun := leftMulMatrix
  map_one' := leftMulMatrix_one
  map_mul' := leftMulMatrix_mul
  map_zero' := by
    change 𝐋 0 = 0
    have h : leftMul (0 : Matrix m m ℂ) = 0 := by ext X; simp [leftMul]
    simp only [leftMulMatrix, h, map_zero]
  map_add' := leftMulMatrix_add
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [leftMulMatrix_smul_real, leftMulMatrix_one]
  map_star' a := by
    simp only [star_eq_conjTranspose]
    exact leftMulMatrix_conjTranspose a

/-- The leftMulMatrix homomorphism is continuous (finite dimensional). -/
lemma leftMulStarAlgHom_continuous {m : Type*} [Fintype m] [DecidableEq m] :
    Continuous (leftMulStarAlgHom : Matrix m m ℂ →⋆ₐ[ℝ] Matrix (m × m) (m × m) ℂ) := by
  -- leftMulMatrix is a linear map between finite-dimensional normed spaces, hence continuous
  letI : NormedRing (Matrix m m ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedRing (Matrix (m × m) (m × m) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (m × m) (m × m) ℂ) := Matrix.linftyOpNormedAlgebra
  change Continuous (leftMulStarAlgHom.toAlgHom.toLinearMap : Matrix m m ℂ →ₗ[ℝ] Matrix (m × m) (m × m) ℂ)
  exact leftMulStarAlgHom.toAlgHom.toLinearMap.continuous_of_finiteDimensional

/-- CFC commutes with leftMulMatrix: for self-adjoint A and continuous f,
    leftMulMatrix (cfc f A) = cfc f (leftMulMatrix A). -/
lemma leftMulMatrix_cfc {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℂ) (hA : IsSelfAdjoint A) (f : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ A) := by cfc_cont_tac) :
    𝐋 (cfc f A) = cfc f (𝐋 A) := by
  letI : NormedRing (Matrix m m ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℂ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra
  letI : CStarAlgebra (Matrix m m ℂ) := by
    simpa [CStarMatrix] using CStarMatrix.instCStarAlgebra (n := m) (A := ℂ)
  letI : NormedRing (Matrix (m × m) (m × m) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (m × m) (m × m) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℂ (Matrix (m × m) (m × m) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : CStarAlgebra (Matrix (m × m) (m × m) ℂ) := by
    simpa [CStarMatrix] using CStarMatrix.instCStarAlgebra (n := m × m) (A := ℂ)
  exact StarAlgHom.map_cfc leftMulStarAlgHom f A hf
    leftMulStarAlgHom_continuous hA

/-- leftMulMatrix preserves rpow: leftMulMatrix (A ^ s) = (leftMulMatrix A) ^ s
    for positive semidefinite A and real s. -/
lemma leftMulMatrix_rpow {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.PosSemidef) {s : ℝ} (hs : 0 ≤ s) :
    𝐋 (A ^ s) = (𝐋 A) ^ s := by
  letI : NormedRing (Matrix m m ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℂ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra
  letI : CStarAlgebra (Matrix m m ℂ) := by
    simpa [CStarMatrix] using CStarMatrix.instCStarAlgebra (n := m) (A := ℂ)
  letI : NormedRing (Matrix (m × m) (m × m) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (m × m) (m × m) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℂ (Matrix (m × m) (m × m) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : CStarAlgebra (Matrix (m × m) (m × m) ℂ) := by
    simpa [CStarMatrix] using CStarMatrix.instCStarAlgebra (n := m × m) (A := ℂ)
  have hA0 : (0 : Matrix m m ℂ) ≤ A := by simpa [Matrix.le_iff] using hA
  have hLA0 : (0 : Matrix (m × m) (m × m) ℂ) ≤ 𝐋 A := by
    simpa [Matrix.le_iff] using leftMulMatrix_posSemidef hA
  have hcont_rpow : ContinuousOn (fun x : ℝ => x ^ s) (spectrum ℝ A) :=
    (Real.continuous_rpow_const hs).continuousOn
  rw [CFC.rpow_eq_cfc_real (a := A) (ha := hA0),
      CFC.rpow_eq_cfc_real (a := 𝐋 A) (ha := hLA0)]
  exact leftMulMatrix_cfc A hA.1.isSelfAdjoint (· ^ s) hcont_rpow

/-- B ↦ rightMulMatrix(Bᴴ) as a star algebra homomorphism over ℝ.
This composes the anti-homomorphism `rightMulMatrix` with the anti-involution
conjTranspose, yielding a genuine homomorphism. -/
noncomputable def rightMulConjTransposeStarAlgHom {m : Type*} [Fintype m] [DecidableEq m] :
    Matrix m m ℂ →⋆ₐ[ℝ] Matrix (m × m) (m × m) ℂ where
  toFun B := 𝐑 (Bᴴ)
  map_one' := by simp [conjTranspose_one, rightMulMatrix_one]
  map_mul' A B := by
    change 𝐑 ((A * B)ᴴ) = 𝐑 (Aᴴ) * 𝐑 (Bᴴ)
    rw [conjTranspose_mul, rightMulMatrix_mul]
  map_zero' := by
    change 𝐑 (0ᴴ) = 0
    rw [conjTranspose_zero]
    have h : rightMul (0 : Matrix m m ℂ) = 0 := by ext X; simp [rightMul]
    simp only [rightMulMatrix, h, map_zero]
  map_add' A B := by
    change 𝐑 ((A + B)ᴴ) = 𝐑 (Aᴴ) + 𝐑 (Bᴴ)
    rw [conjTranspose_add, rightMulMatrix_add]
  commutes' r := by
    change 𝐑 ((algebraMap ℝ (Matrix m m ℂ) r)ᴴ) = algebraMap ℝ _ r
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [conjTranspose_smul, conjTranspose_one, star_trivial,
      rightMulMatrix_smul_real, rightMulMatrix_one]
  map_star' A := by
    simp only [star_eq_conjTranspose, conjTranspose_conjTranspose,
      rightMulMatrix_conjTranspose]

/-- The `rightMulConjTransposeStarAlgHom` is continuous (finite dimensional). -/
lemma rightMulConjTransposeStarAlgHom_continuous {m : Type*} [Fintype m] [DecidableEq m] :
    Continuous (rightMulConjTransposeStarAlgHom :
        Matrix m m ℂ →⋆ₐ[ℝ] Matrix (m × m) (m × m) ℂ) := by
  letI : NormedRing (Matrix m m ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedRing (Matrix (m × m) (m × m) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (m × m) (m × m) ℂ) := Matrix.linftyOpNormedAlgebra
  exact rightMulConjTransposeStarAlgHom.toAlgHom.toLinearMap.continuous_of_finiteDimensional

/-- CFC commutes with rightMulMatrix for self-adjoint (Hermitian) matrices.
Uses the `rightMulConjTransposeStarAlgHom` to transport CFC via `StarAlgHom.map_cfc`.
Key insight: For Hermitian B, `Bᴴ = B`, so `Ψ(B) = rightMulMatrix(B)`,
and for self-adjoint `cfc f B`, `Ψ(cfc f B) = rightMulMatrix(cfc f B)`. -/
lemma rightMulMatrix_cfc {m : Type*} [Fintype m] [DecidableEq m]
    (B : Matrix m m ℂ) (hB : IsSelfAdjoint B) (f : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ B) := by cfc_cont_tac) :
    𝐑 (cfc f B) = cfc f (𝐑 B) := by
  letI : NormedRing (Matrix m m ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℂ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra
  letI : CStarAlgebra (Matrix m m ℂ) := by
    simpa [CStarMatrix] using CStarMatrix.instCStarAlgebra (n := m) (A := ℂ)
  letI : NormedRing (Matrix (m × m) (m × m) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (m × m) (m × m) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℂ (Matrix (m × m) (m × m) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : CStarAlgebra (Matrix (m × m) (m × m) ℂ) := by
    simpa [CStarMatrix] using CStarMatrix.instCStarAlgebra (n := m × m) (A := ℂ)
  -- Ψ = rightMulConjTransposeStarAlgHom: B ↦ rightMulMatrix(Bᴴ)
  -- StarAlgHom.map_cfc gives: Ψ(cfc f B) = cfc f (Ψ B)
  have h_map := StarAlgHom.map_cfc rightMulConjTransposeStarAlgHom f B hf
    rightMulConjTransposeStarAlgHom_continuous hB
  -- Ψ(B) = rightMulMatrix(Bᴴ) = rightMulMatrix(B) since B is Hermitian
  have h_psi_B : (rightMulConjTransposeStarAlgHom : Matrix m m ℂ →⋆ₐ[ℝ] _) B =
      𝐑 B := by
    dsimp [rightMulConjTransposeStarAlgHom]
    rw [← star_eq_conjTranspose, hB.star_eq]
  -- Ψ(cfc f B) = rightMulMatrix((cfc f B)ᴴ) = rightMulMatrix(cfc f B)
  -- since cfc f B is self-adjoint
  have h_psi_cfc : (rightMulConjTransposeStarAlgHom : Matrix m m ℂ →⋆ₐ[ℝ] _) (cfc f B) =
      𝐑 (cfc f B) := by
    dsimp [rightMulConjTransposeStarAlgHom]
    rw [← star_eq_conjTranspose, (cfc_predicate f B : IsSelfAdjoint (cfc f B)).star_eq]
  rw [h_psi_B, h_psi_cfc] at h_map
  exact h_map

/-- `rightMulMatrix` preserves rpow: `rightMulMatrix (B ^ s) = (rightMulMatrix B) ^ s`
for positive semidefinite `B` and real `s`. -/
lemma rightMulMatrix_rpow {m : Type*} [Fintype m] [DecidableEq m]
    {B : Matrix m m ℂ} (hB : B.PosSemidef) {s : ℝ} (hs : 0 ≤ s) :
    𝐑 (B ^ s) = (𝐑 B) ^ s := by
  letI : NormedRing (Matrix m m ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℂ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra
  letI : CStarAlgebra (Matrix m m ℂ) := by
    simpa [CStarMatrix] using CStarMatrix.instCStarAlgebra (n := m) (A := ℂ)
  letI : NormedRing (Matrix (m × m) (m × m) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (m × m) (m × m) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℂ (Matrix (m × m) (m × m) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : CStarAlgebra (Matrix (m × m) (m × m) ℂ) := by
    simpa [CStarMatrix] using CStarMatrix.instCStarAlgebra (n := m × m) (A := ℂ)
  have hB0 : (0 : Matrix m m ℂ) ≤ B := by simpa [Matrix.le_iff] using hB
  have hRB0 : (0 : Matrix (m × m) (m × m) ℂ) ≤ 𝐑 B := by
    simpa [Matrix.le_iff] using rightMulMatrix_posSemidef hB
  have hcont_rpow : ContinuousOn (fun x : ℝ => x ^ s) (spectrum ℝ B) :=
    (Real.continuous_rpow_const hs).continuousOn
  rw [CFC.rpow_eq_cfc_real (a := B) (ha := hB0),
      CFC.rpow_eq_cfc_real (a := 𝐑 B) (ha := hRB0)]
  exact rightMulMatrix_cfc B hB.1.isSelfAdjoint (· ^ s) hcont_rpow

/-- Matrix perspective of a function `f` using the Kubo-Ando style formula.
Defined for PSD `L` and PD `R`. -/
noncomputable def matrixPerspective {m : Type*} [Fintype m] [DecidableEq m]
    (f : ℝ → ℝ) (L R : Matrix m m ℂ) (hL : L.PosSemidef) (hR : R.PosDef) : Matrix m m ℂ :=
  let Rinv := matrixInvSqrt R hR
  let inner := Rinvᴴ * L * Rinv
  let hinner : inner.IsHermitian :=
    isHermitian_conjTranspose_mul_mul (B := Rinv) (A := L) hL.1
  let fInner := matrixFunction (fun x => (f x : ℂ)) inner hinner
  let Rhalf := matrixSqrt R hR.posSemidef
  Rhalf * fInner * Rhalf

/-- The matrix perspective of a function preserves Hermiticity. -/
lemma matrixPerspective_isHermitian {m : Type*} [Fintype m] [DecidableEq m]
    (f : ℝ → ℝ) (L R : Matrix m m ℂ) (hL : L.PosSemidef) (hR : R.PosDef) :
    (matrixPerspective f L R hL hR).IsHermitian := by
  classical
  unfold matrixPerspective
  dsimp
  set Rinv := matrixInvSqrt R hR
  set inner := Rinvᴴ * L * Rinv
  have hinner : inner.IsHermitian :=
    isHermitian_conjTranspose_mul_mul (B := Rinv) (A := L) hL.1
  set fInner := matrixFunction (fun x => (f x : ℂ)) inner hinner
  set Rhalf := matrixSqrt R hR.posSemidef
  have hRhalf : Rhalf.IsHermitian := matrixSqrt_isHermitian hR.posSemidef
  have hfin : fInner.IsHermitian :=
    matrixFunction_isHermitian hinner (fun x => f x)
  simpa [hRhalf.eq] using
    (isHermitian_mul_mul_conjTranspose (B := Rhalf) (A := fInner) hfin)

/-- Congruence lemma for matrixPerspective: equal matrices give equal results
    regardless of the proof terms. -/
theorem matrixPerspective_congr {m : Type*} [Fintype m] [DecidableEq m]
    (f : ℝ → ℝ) (L₁ L₂ R₁ R₂ : Matrix m m ℂ)
    (hL₁ : L₁.PosSemidef) (hL₂ : L₂.PosSemidef) (hR₁ : R₁.PosDef) (hR₂ : R₂.PosDef)
    (hL : L₁ = L₂) (hR : R₁ = R₂) :
    matrixPerspective f L₁ R₁ hL₁ hR₁ = matrixPerspective f L₂ R₂ hL₂ hR₂ := by
  cases hL; cases hR; rfl

/-- Perspective for left/right multiplication matrices. -/
noncomputable def leftRightMatrixPerspective {m : Type*} [Fintype m] [DecidableEq m]
    (f : ℝ → ℝ) (A B : Matrix m m ℂ)
    (hA : (𝐋 A).PosSemidef) (hB : (𝐑 B).PosDef) :
    Matrix (m × m) (m × m) ℂ :=
  matrixPerspective f (𝐋 A) (𝐑 B) hA hB

/-- The left-right matrix perspective preserves Hermiticity. -/
lemma leftRightMatrixPerspective_isHermitian {m : Type*} [Fintype m] [DecidableEq m]
    (f : ℝ → ℝ) (A B : Matrix m m ℂ)
    (hA : (𝐋 A).PosSemidef) (hB : (𝐑 B).PosDef) :
    (leftRightMatrixPerspective f A B hA hB).IsHermitian := by
  simpa [leftRightMatrixPerspective] using
    (matrixPerspective_isHermitian (m := m × m) f (𝐋 A) (𝐑 B) hA hB)

/-- Cancellation for (c · (S · P))† (c · (S · P)) = c² · (P · R · P) when S² = R. -/
lemma perspective_AA_cancel {n : Type*} [Fintype n]
    (c w : ℝ) (P S R : Matrix n n ℂ)
    (hP : P.IsHermitian) (hS : S.IsHermitian) (hSS : S * S = R)
    (hcsq : c * c = w) :
    ((c : ℂ) • (S * P))ᴴ * ((c : ℂ) • (S * P)) = (w : ℂ) • (P * R * P) := by
  simp only [conjTranspose_smul, RCLike.star_def, Complex.conj_ofReal,
    conjTranspose_mul, hP.eq, hS.eq, smul_mul_assoc, mul_smul_comm, smul_smul,
    show (↑c * ↑c : ℂ) = (↑w : ℂ) from by rw [← Complex.ofReal_mul]; exact congrArg _ hcsq,
    mul_assoc]
  congr 1
  rw [← mul_assoc S S P, hSS, ← mul_assoc P R P]

/-- Cancellation with triple product:
(c · (S · P))† (S⁻¹† · L · S⁻¹) (c · (S · P)) = c² · (P · L · P)
when S · S⁻¹ = 1 and S⁻¹ · S = 1. -/
lemma perspective_ATA_cancel {n : Type*} [Fintype n] [DecidableEq n]
    (c w : ℝ) (P S Sinv L : Matrix n n ℂ)
    (hP : P.IsHermitian) (hS : S.IsHermitian) (hSinv : Sinv.IsHermitian)
    (hSSinv : S * Sinv = 1) (hSinvS : Sinv * S = 1)
    (hcsq : c * c = w) :
    ((c : ℂ) • (S * P))ᴴ * (Sinvᴴ * L * Sinv) * ((c : ℂ) • (S * P)) =
      (w : ℂ) • (P * L * P) := by
  simp only [conjTranspose_smul, RCLike.star_def, Complex.conj_ofReal,
    conjTranspose_mul, hP.eq, hS.eq, hSinv.eq, smul_mul_assoc, mul_smul_comm, smul_smul,
    show (↑c * ↑c : ℂ) = (↑w : ℂ) from by rw [← Complex.ofReal_mul]; exact congrArg _ hcsq]
  congr 1
  simp only [mul_assoc]
  rw [← mul_assoc Sinv S P, hSinvS, one_mul,
      ← mul_assoc S Sinv (L * P), hSSinv, one_mul]

/-- Sandwich distribution for the perspective proof:
P(X₁ + X₂ - Z)P = Y₁ + Y₂ - PZ'P
where PXᵢP = Yᵢ and Z = Z'. -/
lemma perspective_sandwich_eq {n : Type*} [Fintype n]
    {P S₁ S₂ : Matrix n n ℂ}
    {A₁adj A₁ A₂adj A₂ M₁ M₂ Z Z' : Matrix n n ℂ}
    {c₁ c₂ : ℂ} {w₁ w₂ : ℝ}
    (hPA₁ : P * A₁adj = c₁ • S₁) (hA₁P : A₁ * P = c₁ • S₁)
    (hPA₂ : P * A₂adj = c₂ • S₂) (hA₂P : A₂ * P = c₂ • S₂)
    (hc₁ : c₁ * c₁ = (w₁ : ℂ)) (hc₂ : c₂ * c₂ = (w₂ : ℂ))
    (hZ : Z = Z') :
    P * (A₁adj * M₁ * A₁ + A₂adj * M₂ * A₂ - Z) * P =
      w₁ • (S₁ * M₁ * S₁) + w₂ • (S₂ * M₂ * S₂) - P * Z' * P := by
  have h₁ : P * (A₁adj * M₁ * A₁) * P = w₁ • (S₁ * M₁ * S₁) := by
    have ha : P * (A₁adj * M₁ * A₁) * P = (P * A₁adj) * M₁ * (A₁ * P) := by
      simp only [mul_assoc]
    rw [ha, hPA₁, hA₁P]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, hc₁, mul_assoc]
    exact (IsScalarTower.algebraMap_smul ℂ w₁ _).symm
  have h₂ : P * (A₂adj * M₂ * A₂) * P = w₂ • (S₂ * M₂ * S₂) := by
    have ha : P * (A₂adj * M₂ * A₂) * P = (P * A₂adj) * M₂ * (A₂ * P) := by
      simp only [mul_assoc]
    rw [ha, hPA₂, hA₂P]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, hc₂, mul_assoc]
    exact (IsScalarTower.algebraMap_smul ℂ w₂ _).symm
  rw [mul_sub, sub_mul, mul_add, add_mul, h₁, h₂, hZ]

/-- Joint convexity of the matrix perspective for Löwner convex `f`. -/
theorem matrixPerspective_joint_convex.{v} {m : Type v} [Fintype m] [DecidableEq m]
    {f : ℝ → ℝ} (hconv : IsJensenConvex.{v} f)
    {L₁ L₂ R₁ R₂ : Matrix m m ℂ}
    (hL₁ : L₁.PosSemidef) (hL₂ : L₂.PosSemidef)
    (hR₁ : R₁.PosDef) (hR₂ : R₂.PosDef)
    {w₁ w₂ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hw : w₁ + w₂ = 1) :
    matrixPerspective f (w₁ • L₁ + w₂ • L₂) (w₁ • R₁ + w₂ • R₂)
        ((hL₁.smul hw₁).add (hL₂.smul hw₂))
        (PosDef.convex_comb_nonneg hR₁ hR₂ hw₁ hw₂ hw) ≤
      w₁ • matrixPerspective f L₁ R₁ hL₁ hR₁ +
        w₂ • matrixPerspective f L₂ R₂ hL₂ hR₂ := by
  classical
  set L : Matrix m m ℂ := w₁ • L₁ + w₂ • L₂
  set R : Matrix m m ℂ := w₁ • R₁ + w₂ • R₂
  have hR : R.PosDef := PosDef.convex_comb_nonneg hR₁ hR₂ hw₁ hw₂ hw
  set Rinv : Matrix m m ℂ := matrixInvSqrt R hR
  set Rhalf : Matrix m m ℂ := matrixSqrt R hR.posSemidef
  set R₁inv : Matrix m m ℂ := matrixInvSqrt R₁ hR₁
  set R₂inv : Matrix m m ℂ := matrixInvSqrt R₂ hR₂
  set R₁half : Matrix m m ℂ := matrixSqrt R₁ hR₁.posSemidef
  set R₂half : Matrix m m ℂ := matrixSqrt R₂ hR₂.posSemidef
  set A₁ : Matrix m m ℂ := (Real.sqrt w₁ : ℂ) • (R₁half * Rinv)
  set A₂ : Matrix m m ℂ := (Real.sqrt w₂ : ℂ) • (R₂half * Rinv)
  set T₁ : Matrix m m ℂ := R₁invᴴ * L₁ * R₁inv
  set T₂ : Matrix m m ℂ := R₂invᴴ * L₂ * R₂inv
  have hT₁ : T₁.PosSemidef := by
    simpa [T₁] using hL₁.conjTranspose_mul_mul_same R₁inv
  have hT₂ : T₂.PosSemidef := by
    simpa [T₂] using hL₂.conjTranspose_mul_mul_same R₂inv
  have hRinv_herm : Rinv.IsHermitian := matrixInvSqrt_isHermitian hR
  have hR₁half_herm : R₁half.IsHermitian := matrixSqrt_isHermitian hR₁.posSemidef
  have hR₂half_herm : R₂half.IsHermitian := matrixSqrt_isHermitian hR₂.posSemidef
  have hRhalf_herm : Rhalf.IsHermitian := matrixSqrt_isHermitian hR.posSemidef
  have hA₁_adj : A₁ᴴ = (Real.sqrt w₁ : ℂ) • (Rinv * R₁half) := by
    simp [A₁, hRinv_herm.eq, hR₁half_herm.eq, Matrix.conjTranspose_mul]
  have hA₂_adj : A₂ᴴ = (Real.sqrt w₂ : ℂ) • (Rinv * R₂half) := by
    simp [A₂, hRinv_herm.eq, hR₂half_herm.eq, Matrix.conjTranspose_mul]
  have hsqrt₁_real : Real.sqrt w₁ * Real.sqrt w₁ = w₁ := Real.mul_self_sqrt hw₁
  have hsqrt₂_real : Real.sqrt w₂ * Real.sqrt w₂ = w₂ := Real.mul_self_sqrt hw₂
  have hsqrt₁ : (Real.sqrt w₁ : ℂ) * (Real.sqrt w₁ : ℂ) = (w₁ : ℂ) := by
    rw [← Complex.ofReal_mul]; exact congrArg _ hsqrt₁_real
  have hsqrt₂ : (Real.sqrt w₂ : ℂ) * (Real.sqrt w₂ : ℂ) = (w₂ : ℂ) := by
    rw [← Complex.ofReal_mul]; exact congrArg _ hsqrt₂_real
  -- A†A sum ≤ 1 (using AA cancellation helper)
  have hA_sum : A₁ᴴ * A₁ + A₂ᴴ * A₂ = (Rinv * R * Rinv) := by
    have hA₁A₁ : A₁ᴴ * A₁ = (w₁ : ℂ) • (Rinv * R₁ * Rinv) :=
      perspective_AA_cancel (Real.sqrt w₁) w₁ Rinv R₁half R₁
        hRinv_herm hR₁half_herm (matrixSqrt_mul_self hR₁) hsqrt₁_real
    have hA₂A₂ : A₂ᴴ * A₂ = (w₂ : ℂ) • (Rinv * R₂ * Rinv) :=
      perspective_AA_cancel (Real.sqrt w₂) w₂ Rinv R₂half R₂
        hRinv_herm hR₂half_herm (matrixSqrt_mul_self hR₂) hsqrt₂_real
    calc
      A₁ᴴ * A₁ + A₂ᴴ * A₂ =
          (w₁ : ℂ) • (Rinv * R₁ * Rinv) + (w₂ : ℂ) • (Rinv * R₂ * Rinv) := by
        rw [hA₁A₁, hA₂A₂]
      _ = Rinv * ((w₁ : ℂ) • R₁ + (w₂ : ℂ) • R₂) * Rinv := by
        simp [mul_add, add_mul, mul_assoc]
      _ = Rinv * R * Rinv := by
        simp [R]
  have hAB : A₁ᴴ * A₁ + A₂ᴴ * A₂ ≤ (1 : Matrix m m ℂ) := by
    have hRinv_mul : Rinv * R * Rinv = (1 : Matrix m m ℂ) := by
      simpa [Rinv, R] using matrixInvSqrt_mul_self hR
    simp [hA_sum, hRinv_mul]
  have hT₁_herm : T₁.IsHermitian :=
    isHermitian_conjTranspose_mul_mul (B := R₁inv) (A := L₁) hL₁.1
  have hT₂_herm : T₂.IsHermitian :=
    isHermitian_conjTranspose_mul_mul (B := R₂inv) (A := L₂) hL₂.1
  have hC : (A₁ᴴ * T₁ * A₁ + A₂ᴴ * T₂ * A₂).IsHermitian :=
    IsHermitian.add_isHermitian
      (isHermitian_conjTranspose_mul_mul (B := A₁) (A := T₁) hT₁_herm)
      (isHermitian_conjTranspose_mul_mul (B := A₂) (A := T₂) hT₂_herm)
  have hconv' := hconv (m := m) (A := A₁) (B := A₂) (T₁ := T₁) (T₂ := T₂) hT₁ hT₂ hAB hC
  have hpsd :
      (A₁ᴴ *
          matrixFunction (fun x => (f x : ℂ)) T₁ hT₁.1 * A₁ +
        A₂ᴴ *
          matrixFunction (fun x => (f x : ℂ)) T₂ hT₂.1 * A₂ -
          matrixFunction (fun x => (f x : ℂ)) (A₁ᴴ * T₁ * A₁ + A₂ᴴ * T₂ * A₂) hC
        ).PosSemidef := by
    simpa [Matrix.le_iff] using hconv'
  have hpsd' :
      (Rhalfᴴ *
          (A₁ᴴ *
              matrixFunction (fun x => (f x : ℂ)) T₁ hT₁.1 * A₁ +
            A₂ᴴ *
              matrixFunction (fun x => (f x : ℂ)) T₂ hT₂.1 * A₂ -
              matrixFunction (fun x => (f x : ℂ)) (A₁ᴴ * T₁ * A₁ + A₂ᴴ * T₂ * A₂) hC) * Rhalf
        ).PosSemidef :=
    hpsd.conjTranspose_mul_mul_same Rhalf
  have hRhalf_eq : Rhalfᴴ = Rhalf := hRhalf_herm.eq
  -- A†TA sum = Rinv† * L * Rinv (using ATA cancellation helper)
  have hinner : A₁ᴴ * T₁ * A₁ + A₂ᴴ * T₂ * A₂ = Rinvᴴ * L * Rinv := by
    have hA₁TA₁ : A₁ᴴ * T₁ * A₁ = (w₁ : ℂ) • (Rinv * L₁ * Rinv) :=
      perspective_ATA_cancel (Real.sqrt w₁) w₁ Rinv R₁half R₁inv L₁
        hRinv_herm hR₁half_herm (matrixInvSqrt_isHermitian hR₁)
        (matrixSqrt_mul_matrixInvSqrt hR₁) (matrixInvSqrt_mul_matrixSqrt hR₁) hsqrt₁_real
    have hA₂TA₂ : A₂ᴴ * T₂ * A₂ = (w₂ : ℂ) • (Rinv * L₂ * Rinv) :=
      perspective_ATA_cancel (Real.sqrt w₂) w₂ Rinv R₂half R₂inv L₂
        hRinv_herm hR₂half_herm (matrixInvSqrt_isHermitian hR₂)
        (matrixSqrt_mul_matrixInvSqrt hR₂) (matrixInvSqrt_mul_matrixSqrt hR₂) hsqrt₂_real
    calc
      A₁ᴴ * T₁ * A₁ + A₂ᴴ * T₂ * A₂ =
          (w₁ : ℂ) • (Rinv * L₁ * Rinv) + (w₂ : ℂ) • (Rinv * L₂ * Rinv) := by
        rw [hA₁TA₁, hA₂TA₂]
      _ = Rinv * ((w₁ : ℂ) • L₁ + (w₂ : ℂ) • L₂) * Rinv := by
        simp [mul_add, add_mul, mul_assoc]
      _ = Rinvᴴ * L * Rinv := by
        simp [L, hRinv_herm.eq]
  -- Cancellation lemmas for Rhalf and Rinv
  have hRhalf_Rinv : Rhalf * Rinv = 1 := by
    simpa [Rhalf, Rinv] using matrixSqrt_mul_matrixInvSqrt hR
  have hRinv_Rhalf : Rinv * Rhalf = 1 := by
    simpa [Rhalf, Rinv] using matrixInvSqrt_mul_matrixSqrt hR
  -- Sandwich helper lemmas (outside hfinal for performance)
  have hRhalf_A₁_adj : Rhalf * A₁ᴴ = (Real.sqrt w₁ : ℂ) • R₁half := by
    rw [hA₁_adj, mul_smul_comm]; congr 1; rw [← mul_assoc, hRhalf_Rinv, one_mul]
  have hA₁_Rhalf : A₁ * Rhalf = (Real.sqrt w₁ : ℂ) • R₁half := by
    simp only [A₁, smul_mul_assoc, mul_assoc, hRinv_Rhalf, mul_one]
  have hRhalf_A₂_adj : Rhalf * A₂ᴴ = (Real.sqrt w₂ : ℂ) • R₂half := by
    rw [hA₂_adj, mul_smul_comm]; congr 1; rw [← mul_assoc, hRhalf_Rinv, one_mul]
  have hA₂_Rhalf : A₂ * Rhalf = (Real.sqrt w₂ : ℂ) • R₂half := by
    simp only [A₂, smul_mul_assoc, mul_assoc, hRinv_Rhalf, mul_one]
  -- matrixFunction_congr for the f(C) term (precomputed for performance)
  have hmfC : matrixFunction (fun x => (f x : ℂ))
      (A₁ᴴ * T₁ * A₁ + A₂ᴴ * T₂ * A₂) hC =
      matrixFunction (fun x => (f x : ℂ)) (Rinvᴴ * L * Rinv)
        (isHermitian_conjTranspose_mul_mul (B := Rinv) (A := L)
          ((hL₁.smul hw₁).add (hL₂.smul hw₂)).1) :=
    matrixFunction_congr (fun x => (f x : ℂ)) hC _ hinner
  -- Final step: apply sandwich equation and conclude
  have hfinal :
      matrixPerspective f L R ((hL₁.smul hw₁).add (hL₂.smul hw₂)) hR ≤
        w₁ • matrixPerspective f L₁ R₁ hL₁ hR₁ +
          w₂ • matrixPerspective f L₂ R₂ hL₂ hR₂ := by
    rw [Matrix.le_iff]
    rw [hRhalf_eq] at hpsd'
    rw [perspective_sandwich_eq hRhalf_A₁_adj hA₁_Rhalf
      hRhalf_A₂_adj hA₂_Rhalf hsqrt₁ hsqrt₂ hmfC] at hpsd'
    exact hpsd'
  simpa [L, R] using hfinal

/-- The sign matrix Σ = I ⊕ (-I) on m ⊕ m is unitary. -/
lemma signMatrix_mem_unitary {m : Type*} [Fintype m] [DecidableEq m] :
    fromBlocks (1 : Matrix m m ℂ) 0 0 (-1 : Matrix m m ℂ) ∈
    unitary (Matrix (m ⊕ m) (m ⊕ m) ℂ) := by
  rw [Unitary.mem_iff]
  constructor <;> (simp [star_eq_conjTranspose, fromBlocks_conjTranspose,
    fromBlocks_multiply, fromBlocks_one])

/-- The sign matrix is self-adjoint: Σ* = Σ. -/
lemma signMatrix_star_eq {m : Type*} [Fintype m] [DecidableEq m] :
    star (fromBlocks (1 : Matrix m m ℂ) 0 0 (-1 : Matrix m m ℂ)) =
    fromBlocks (1 : Matrix m m ℂ) 0 0 (-1 : Matrix m m ℂ) := by
  simp [star_eq_conjTranspose, fromBlocks_conjTranspose]

/-! ### Kronecker Product Powers and Perspective Identity -/

/-- Kronecker product of natural number powers: `(A ⊗ₖ M)^n = A^n ⊗ₖ M^n`. -/
lemma kronecker_npow {m : Type*} [Fintype m] [DecidableEq m]
    (A M : Matrix m m ℂ) (n : ℕ) :
    (A ⊗ₖ M) ^ n = (A ^ n) ⊗ₖ (M ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    -- Work with the explicit Kronecker product type
    set K : Matrix (m × m) (m × m) ℂ := A ⊗ₖ M with hK
    change K ^ (n + 1) = _
    rw [pow_succ, ih, hK, ← mul_kronecker_mul, ← pow_succ, ← pow_succ]

/-- The matrixFunction `x ↦ x^(p:ℂ)` equals rpow for PosSemidef matrices with non-negative
    eigenvalues and real exponent p. -/
lemma matrixFunction_cpow_eq_rpow {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.PosSemidef) (p : ℝ) :
    matrixFunction (fun x => x ^ (p : ℂ)) A hA.1 =
    matrixFunction (fun x => ((x ^ p : ℝ) : ℂ)) A hA.1 := by
  unfold matrixFunction
  have h_diag : (fun i => (hA.1.eigenvalues i : ℂ) ^ (p : ℂ)) =
                (fun i => ((hA.1.eigenvalues i ^ p : ℝ) : ℂ)) := by
    funext i
    exact (Complex.ofReal_cpow (hA.eigenvalues_nonneg i) p).symm
  simp_rw [h_diag]

/-- For commuting PSD L and PD R, the perspective inner matrix simplifies:
Rinv† * L * Rinv = L * R^{-1}.
Since matrixInvSqrt is Hermitian (self-adjoint), Rinv† = Rinv,
and since Rinv commutes with L, the product is L * Rinv * Rinv = L * R^{-1}. -/
lemma perspective_inner_eq_commuting {n : Type*} [Fintype n] [DecidableEq n]
    {L R : Matrix n n ℂ} (hL : L.PosSemidef) (hR : R.PosDef)
    (hcomm : L * R = R * L) :
    (matrixInvSqrt R hR)ᴴ * L * matrixInvSqrt R hR = L * matrixInvSqrt R hR * matrixInvSqrt R hR := by
  have hRinv_herm := matrixInvSqrt_isHermitian hR
  rw [hRinv_herm.eq]  -- Rinv† = Rinv
  rw [← matrixInvSqrt_commute_of_commute hL hR hcomm]

/-- For commuting PSD L and PD R, the perspective inner matrix equals L * R^{-1}.
This combines the commutativity simplification with the fact that Rinv * Rinv = R^{-1}. -/
lemma perspective_inner_eq_mul_inv {n : Type*} [Fintype n] [DecidableEq n]
    {L R : Matrix n n ℂ} (hL : L.PosSemidef) (hR : R.PosDef)
    (hcomm : L * R = R * L) :
    (matrixInvSqrt R hR)ᴴ * L * matrixInvSqrt R hR = L * R⁻¹ := by
  rw [perspective_inner_eq_commuting hL hR hcomm]
  have hRinv_eq : matrixInvSqrt R hR = R ^ (-1 / 2 : ℝ) := by
    simpa [matrixInvSqrt] using matrixFunction_rpow_eq hR.posSemidef (-1 / 2 : ℝ)
  rw [hRinv_eq]
  letI : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℂ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  letI : CStarAlgebra (Matrix n n ℂ) := by
    simpa [CStarMatrix] using CStarMatrix.instCStarAlgebra (n := n) (A := ℂ)
  have hRunit := hR.isUnit
  have hR0 : (0 : Matrix n n ℂ) ≤ R := by simpa [Matrix.le_iff] using hR.posSemidef
  -- R^{-1/2} * R^{-1/2} = R^{-1}
  have hRhalf_sq : R ^ (-1 / 2 : ℝ) * R ^ (-1 / 2 : ℝ) = R⁻¹ := by
    -- Show (R^{-1/2})^2 * R = 1, hence (R^{-1/2})^2 = R⁻¹
    have h1 : R ^ (-1 / 2 : ℝ) * R ^ (-1 / 2 : ℝ) * R = 1 := by
      rw [← CFC.rpow_add hRunit (x := (-1 / 2 : ℝ)) (y := (-1 / 2 : ℝ))]
      norm_num
      -- goal: R ^ (-1 : ℝ) * R = 1
      have := CFC.rpow_neg_mul_rpow (1 : ℝ) hRunit hR0
      rwa [CFC.rpow_one R hR0] at this
    have hdet : IsUnit R.det :=
      (Matrix.isUnit_iff_isUnit_det R).mp hRunit
    have h2 : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R hdet
    exact hRunit.mul_right_cancel (h1.trans h2.symm)
  -- L * (R^{-1/2} * R^{-1/2}) = L * R⁻¹
  rw [mul_assoc, hRhalf_sq]  -- mul_assoc: (L * R^{-1/2}) * R^{-1/2} → L * (R^{-1/2} * R^{-1/2})

/-- Kronecker product distributes over rpow for PSD matrices:
`(X ⊗ₖ Y) ^ p = (X ^ p) ⊗ₖ (Y ^ p)` when `p ≥ 0`. -/
lemma kronecker_rpow_psd {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {X : Matrix m m ℂ} {Y : Matrix n n ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (p : ℝ) (hp : 0 ≤ p) :
    (X ⊗ₖ Y) ^ p = (X ^ p) ⊗ₖ (Y ^ p) := by
  -- Spectral decomposition data
  let UX := hX.1.eigenvectorUnitary
  let dX := hX.1.eigenvalues
  let UY := hY.1.eigenvectorUnitary
  let dY := hY.1.eigenvalues
  -- Eigenvalue nonnegativity
  have hdX : ∀ i, 0 ≤ dX i := hX.eigenvalues_nonneg
  have hdY : ∀ i, 0 ≤ dY i := hY.eigenvalues_nonneg
  -- Spectral decompositions: X = UX * diag(dX) * UX†, etc.
  have hX_eq : X = (UX : Matrix m m ℂ) * diagonal (RCLike.ofReal ∘ dX) *
      (UX : Matrix m m ℂ)ᴴ := by
    rw [hX.1.spectral_theorem (𝕜 := ℂ), Unitary.conjStarAlgAut_apply, star_eq_conjTranspose]
  have hY_eq : Y = (UY : Matrix n n ℂ) * diagonal (RCLike.ofReal ∘ dY) *
      (UY : Matrix n n ℂ)ᴴ := by
    rw [hY.1.spectral_theorem (𝕜 := ℂ), Unitary.conjStarAlgAut_apply, star_eq_conjTranspose]
  -- Diagonal matrices are PSD / nonneg
  have hDX_psd : (diagonal (RCLike.ofReal ∘ dX) : Matrix m m ℂ).PosSemidef :=
    posSemidef_diagonal_iff.mpr fun i => RCLike.ofReal_nonneg.mpr (hdX i)
  have hDY_psd : (diagonal (RCLike.ofReal ∘ dY) : Matrix n n ℂ).PosSemidef :=
    posSemidef_diagonal_iff.mpr fun j => RCLike.ofReal_nonneg.mpr (hdY j)
  have hDX_nonneg : (0 : Matrix m m ℂ) ≤ diagonal (RCLike.ofReal ∘ dX) := hDX_psd.nonneg
  have hDY_nonneg : (0 : Matrix n n ℂ) ≤ diagonal (RCLike.ofReal ∘ dY) := hDY_psd.nonneg
  -- The conjugated forms are nonneg (needed for rpow_unitary_conj auto-param)
  have hX_nonneg : 0 ≤ (UX : Matrix m m ℂ) * diagonal (RCLike.ofReal ∘ dX) *
      (UX : Matrix m m ℂ)ᴴ := by
    rw [← hX_eq]; exact hX.nonneg
  have hY_nonneg : 0 ≤ (UY : Matrix n n ℂ) * diagonal (RCLike.ofReal ∘ dY) *
      (UY : Matrix n n ℂ)ᴴ := by
    rw [← hY_eq]; exact hY.nonneg
  -- Diagonal rpow
  have hDX_rpow : diagonal (RCLike.ofReal ∘ dX) ^ p =
      diagonal (fun i => ((dX i ^ p : ℝ) : ℂ)) := by
    change diagonal (fun i => (dX i : ℂ)) ^ p = _
    exact diagonal_rpow dX hdX p hp
  have hDY_rpow : diagonal (RCLike.ofReal ∘ dY) ^ p =
      diagonal (fun j => ((dY j ^ p : ℝ) : ℂ)) := by
    change diagonal (fun j => (dY j : ℂ)) ^ p = _
    exact diagonal_rpow dY hdY p hp
  -- CFC rpow via spectral: X^p = UX * diag(dX^p) * UX†
  have hX_rpow : X ^ p = (UX : Matrix m m ℂ) * diagonal (fun i => ((dX i ^ p : ℝ) : ℂ)) *
      (UX : Matrix m m ℂ)ᴴ := by
    conv_lhs => rw [hX_eq]
    rw [rpow_unitary_conj UX.2 hp hDX_nonneg (hM' := hX_nonneg), hDX_rpow]
  have hY_rpow : Y ^ p = (UY : Matrix n n ℂ) * diagonal (fun j => ((dY j ^ p : ℝ) : ℂ)) *
      (UY : Matrix n n ℂ)ᴴ := by
    conv_lhs => rw [hY_eq]
    rw [rpow_unitary_conj UY.2 hp hDY_nonneg (hM' := hY_nonneg), hDY_rpow]
  -- Kronecker: X ⊗ₖ Y = (UX ⊗ₖ UY) * diag(dX ⊗ dY) * (UX ⊗ₖ UY)†
  have hXY_eq : X ⊗ₖ Y = ((UX : Matrix m m ℂ) ⊗ₖ (UY : Matrix n n ℂ)) *
      (diagonal (RCLike.ofReal ∘ dX) ⊗ₖ diagonal (RCLike.ofReal ∘ dY)) *
      ((UX : Matrix m m ℂ) ⊗ₖ (UY : Matrix n n ℂ))ᴴ := by
    rw [hX_eq, hY_eq, conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul]
  -- UX ⊗ₖ UY is in unitaryGroup
  have hUXY : ((UX : Matrix m m ℂ) ⊗ₖ (UY : Matrix n n ℂ)) ∈
      Matrix.unitaryGroup (m × n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    have h1 := Matrix.mem_unitaryGroup_iff'.mp UX.2
    have h2 := Matrix.mem_unitaryGroup_iff'.mp UY.2
    rw [star_eq_conjTranspose, conjTranspose_kronecker, ← mul_kronecker_mul]
    simp only [← star_eq_conjTranspose]
    rw [h1, h2, one_kronecker_one]
  -- DXY = diag(dX) ⊗ₖ diag(dY) is nonneg
  have hDXY_nonneg : 0 ≤ diagonal (RCLike.ofReal ∘ dX) ⊗ₖ
      diagonal (RCLike.ofReal ∘ dY) :=
    (hDX_psd.kronecker hDY_psd).nonneg
  -- The conjugated Kronecker form is nonneg
  have hXY_nonneg : 0 ≤ ((UX : Matrix m m ℂ) ⊗ₖ (UY : Matrix n n ℂ)) *
      (diagonal (RCLike.ofReal ∘ dX) ⊗ₖ diagonal (RCLike.ofReal ∘ dY)) *
      ((UX : Matrix m m ℂ) ⊗ₖ (UY : Matrix n n ℂ))ᴴ := by
    rw [← hXY_eq]; exact (hX.kronecker hY).nonneg
  -- CFC rpow on the Kronecker product
  have hXY_rpow : (X ⊗ₖ Y) ^ p = ((UX : Matrix m m ℂ) ⊗ₖ (UY : Matrix n n ℂ)) *
      ((diagonal (RCLike.ofReal ∘ dX) ⊗ₖ diagonal (RCLike.ofReal ∘ dY)) ^ p) *
      ((UX : Matrix m m ℂ) ⊗ₖ (UY : Matrix n n ℂ))ᴴ := by
    conv_lhs => rw [hXY_eq]
    exact rpow_unitary_conj hUXY hp hDXY_nonneg (hM' := hXY_nonneg)
  -- Diagonal Kronecker rpow: (DX ⊗ₖ DY)^p = DX^p ⊗ₖ DY^p
  have hDXY_rpow : (diagonal (RCLike.ofReal ∘ dX) ⊗ₖ
      diagonal (RCLike.ofReal ∘ dY)) ^ p =
      diagonal (fun i => ((dX i ^ p : ℝ) : ℂ)) ⊗ₖ
      diagonal (fun j => ((dY j ^ p : ℝ) : ℂ)) := by
    change (diagonal (fun i => (dX i : ℂ)) ⊗ₖ diagonal (fun j => (dY j : ℂ))) ^ p = _
    -- Convert LHS Kronecker to single diagonal
    have hkron : diagonal (fun i => (dX i : ℂ)) ⊗ₖ diagonal (fun j => (dY j : ℂ)) =
        diagonal (fun mn : m × n => ((dX mn.fst * dY mn.snd : ℝ) : ℂ)) := by
      rw [diagonal_kronecker_diagonal]; congr 1; ext ⟨a, b⟩; push_cast; ring
    rw [hkron, diagonal_rpow _ (fun ⟨a, b⟩ => mul_nonneg (hdX a) (hdY b)) p hp]
    -- Convert back to Kronecker
    rw [diagonal_kronecker_diagonal]; congr 1; ext ⟨a, b⟩
    push_cast [Real.mul_rpow (hdX a) (hdY b)]; ring
  -- Combine everything
  rw [hXY_rpow, hDXY_rpow, hX_rpow, hY_rpow]
  rw [conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul]

/-- The inner matrix of the perspective, raised to the power `p` and multiplied by `R`,
equals `L_{A^p} · R_{B^{1-p}}` for PD matrices `A`, `B` and `p ≥ 0`.
Here `L = L_A`, `R = R_B` are left/right multiplication operators, and
`S = R^{-1/2}` so that `Sᴴ * L * S` is the inner matrix of the perspective. -/
lemma perspective_inner_rpow_mul_eq_leftRight {m : Type*} [Fintype m] [DecidableEq m]
    (A B : Matrix m m ℂ) (hA : A.PosDef) (hB : B.PosDef) (p : ℝ) (hp : 0 ≤ p) :
    let L := 𝐋 A
    let R := 𝐑 B
    let hR_pd := rightMulMatrix_posDef hB
    let S := matrixInvSqrt R hR_pd
    (Sᴴ * L * S) ^ p * R = 𝐋 (A ^ p) * 𝐑 (B ^ (1 - p)) := by
  intro L R hR_pd S
  have hL_psd : L.PosSemidef := leftMulMatrix_posSemidef hA.posSemidef
  have hcomm : L * R = R * L := leftMulMatrix_rightMulMatrix_commute A B
  have hinner_eq : Sᴴ * L * S = L * R⁻¹ :=
    perspective_inner_eq_mul_inv hL_psd hR_pd hcomm
  have hB_unit : IsUnit B := hB.isUnit
  have hB_det : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hB_unit
  have hR_unit : IsUnit R := hR_pd.isUnit
  have hRinv_eq_rm : R⁻¹ = 𝐑 (B⁻¹) := by
    have h1 : R * 𝐑 (B⁻¹) = 1 := by
      change 𝐑 B * 𝐑 (B⁻¹) = 1
      rw [← rightMulMatrix_mul, Matrix.nonsing_inv_mul B hB_det, rightMulMatrix_one]
    have hR_detU : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det R).mp hR_unit
    have h2 : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hR_detU
    exact (hR_unit.mul_left_cancel (h1.trans h2.symm)).symm
  have hLRinv_kron : L * R⁻¹ = A ⊗ₖ (B⁻¹)ᵀ := by
    change 𝐋 A * R⁻¹ = A ⊗ₖ (B⁻¹)ᵀ
    rw [hRinv_eq_rm, leftMulMatrix_eq_kronecker_one,
      rightMulMatrix_eq_one_kronecker_transpose,
      ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  have hBinv_psd : (B⁻¹).PosSemidef := hB.posSemidef.inv
  have hBinvT_psd : ((B⁻¹)ᵀ).PosSemidef := hBinv_psd.transpose
  have hLRinv_rpow : (L * R⁻¹) ^ p = (A ^ p) ⊗ₖ (((B⁻¹)ᵀ) ^ p) := by
    rw [hLRinv_kron]
    exact kronecker_rpow_psd hA.posSemidef hBinvT_psd p hp
  have hBinvT_rpow_mul : ((B⁻¹)ᵀ) ^ p * Bᵀ = (B ^ (1 - p))ᵀ :=
    inv_transpose_rpow_mul_transpose_eq B hB p hp
  rw [hinner_eq, hLRinv_rpow]
  change ((A ^ p) ⊗ₖ (((B⁻¹)ᵀ) ^ p)) * 𝐑 B =
      𝐋 (A ^ p) * 𝐑 (B ^ (1 - p))
  rw [rightMulMatrix_eq_one_kronecker_transpose B]
  rw [← mul_kronecker_mul, Matrix.mul_one, hBinvT_rpow_mul]
  rw [leftMulMatrix_eq_kronecker_one, rightMulMatrix_eq_one_kronecker_transpose]
  rw [← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

/-- The p-th power of the inner matrix of the perspective commutes with `R^{1/2}`.
This follows from the fact that `L ⊗ I` and `I ⊗ Bᵀ` commute. -/
lemma perspective_inner_rpow_comm_sqrt_leftRight {m : Type*} [Fintype m] [DecidableEq m]
  (A B : Matrix m m ℂ) (hA : A.PosDef) (hB : B.PosDef) (p : ℝ) (_hp : 0 ≤ p) :
    let L := 𝐋 A
    let R := 𝐑 B
    let hR_pd := rightMulMatrix_posDef hB
    let S := matrixInvSqrt R hR_pd
    let T := matrixSqrt R hR_pd.posSemidef
    (Sᴴ * L * S) ^ p * T = T * (Sᴴ * L * S) ^ p := by
  intro L R hR_pd S T
  have hL_psd : L.PosSemidef := leftMulMatrix_posSemidef hA.posSemidef
  have hcomm : L * R = R * L := leftMulMatrix_rightMulMatrix_commute A B
  have hinner_eq : Sᴴ * L * S = L * R⁻¹ :=
    perspective_inner_eq_mul_inv hL_psd hR_pd hcomm
  have hR_nonneg : (0 : Matrix (m × m) (m × m) ℂ) ≤ R := by
    simpa [Matrix.le_iff] using hR_pd.posSemidef
  have hR_unit : IsUnit R := hR_pd.isUnit
  have hRhalf_eq : T = R ^ (1 / 2 : ℝ) := by
    change matrixSqrt R hR_pd.posSemidef = R ^ (1 / 2 : ℝ)
    simpa [matrixSqrt] using matrixFunction_rpow_eq hR_pd.posSemidef (1 / 2 : ℝ)
  have hR_det : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det R).mp hR_unit
  have hLRinv_comm_R : Commute R (L * R⁻¹) := by
    rw [Commute, SemiconjBy]
    have h1 : R * (L * R⁻¹) = L := by
      rw [← mul_assoc, hcomm.symm, mul_assoc,
          Matrix.mul_nonsing_inv R hR_det, mul_one]
    have h2 : L * R⁻¹ * R = L := by
      rw [mul_assoc, Matrix.nonsing_inv_mul R hR_det, mul_one]
    rw [h1, h2]
  have hinner_psd : (Sᴴ * L * S).PosSemidef :=
    hL_psd.conjTranspose_mul_mul_same S
  have hinner_psd_nonneg : (0 : Matrix (m × m) (m × m) ℂ) ≤ L * R⁻¹ := by
    rw [← hinner_eq]
    exact hinner_psd.nonneg
  rw [hinner_eq, hRhalf_eq,
      CFC.rpow_eq_cfc_real (a := L * R⁻¹) (ha := hinner_psd_nonneg),
      CFC.rpow_eq_cfc_real (a := R) (ha := hR_nonneg) (y := 1 / 2)]
  simpa [L, R, hR_pd] using
    (hLRinv_comm_R.symm.cfc_real (· ^ p) |>.symm.cfc_real (· ^ (1 / 2 : ℝ))).eq.symm

/-- The matrix perspective with f(x) = −xᵖ on left/right multiplication matrices
equals −(L_{Aᵖ} · R_{B¹⁻ᵖ}) for PD matrices A, B and p ≥ 0.
Here L = L_A, R = R_B, S = R^(⁻¹⁄₂), T = R^(¹⁄₂), and the perspective is
T · f(S* L S) · T. -/
theorem matrixPerspective_neg_leftRight_eq {m : Type*} [Fintype m] [DecidableEq m]
    (A B : Matrix m m ℂ) (hA : A.PosDef) (hB : B.PosDef) (p : ℝ) (hp : 0 ≤ p)
    (hL_psd : (𝐋 A).PosSemidef) (hR_pd : (𝐑 B).PosDef) :
    matrixPerspective (fun x => -(x ^ p)) (𝐋 A) (𝐑 B) hL_psd hR_pd =
      -(𝐋 (A ^ p) * 𝐑 (B ^ (1 - p))) := by
  set L := 𝐋 A
  set R := 𝐑 B
  set S := matrixInvSqrt R hR_pd
  set T := matrixSqrt R hR_pd.posSemidef
  have hinner_psd : (Sᴴ * L * S).PosSemidef :=
    hL_psd.conjTranspose_mul_mul_same S
  have hfun_neg : matrixFunction (fun x => ((-(x ^ p) : ℝ) : ℂ))
      (Sᴴ * L * S) hinner_psd.1 = -((Sᴴ * L * S) ^ p) := by
    have h1 : (fun x : ℝ => ((-(x ^ p) : ℝ) : ℂ)) = (fun x : ℝ => -((x ^ p : ℝ) : ℂ)) := by
      ext x
      push_cast
      ring
    rw [h1, matrixFunction_neg hinner_psd.1, matrixFunction_rpow_eq hinner_psd p]
  have hRhalf_sq : T * T = R := matrixSqrt_mul_self_posSemidef hR_pd.posSemidef
  have hinnerp_comm_Rhalf : (Sᴴ * L * S) ^ p * T = T * (Sᴴ * L * S) ^ p := by
    simpa [L, R, S, T] using
      perspective_inner_rpow_comm_sqrt_leftRight A B hA hB p hp
  have hpersp_simp : T * ((Sᴴ * L * S) ^ p) * T = (Sᴴ * L * S) ^ p * R := by
    rw [hinnerp_comm_Rhalf.symm, mul_assoc, hRhalf_sq]
  have hinnerp_R_eq : (Sᴴ * L * S) ^ p * R =
      𝐋 (A ^ p) * 𝐑 (B ^ (1 - p)) := by
    simpa [L, R, S] using
      perspective_inner_rpow_mul_eq_leftRight A B hA hB p hp
  unfold matrixPerspective
  dsimp only
  rw [hfun_neg, Matrix.mul_neg, Matrix.neg_mul]
  congr 1
  rw [hpersp_simp, hinnerp_R_eq]

end Matrix
