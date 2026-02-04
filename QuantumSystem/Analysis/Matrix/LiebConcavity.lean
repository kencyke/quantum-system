module

public import QuantumSystem.Analysis.Matrix.Effros
public import QuantumSystem.Notation
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity

/-!
# Lieb's Concavity Theorem via Effros's Matrix Convexity Approach

This file provides definitions related to Lieb's concavity theorem and establishes it
via the Effros Löwner convexity approach (2008), which avoids complex interpolation.

## Mathematical Background

### Lieb's Joint Concavity Theorem (1973)
For 0 ≤ p ≤ 1 and a fixed matrix K, the map
  (A, B) ↦ Tr(A^p K† B^{1-p} K)
is jointly concave on pairs of positive definite matrices.

### Proof Strategy (Effros 2008)
The proof proceeds via:
1. **Matrix concavity of t^s**: For 0 < s ≤ 1, the map A ↦ A^s is Löwner concave
   (equivalently, f(t) = -t^s is Löwner convex). This follows from Löwner-Heinz.
2. **Hansen-Pedersen-Jensen (HPJ) inequality**: For Löwner convex f and matrices
   A, B with A*A + B*B = I: f(A*T₁A + B*T₂B) ≤ A*f(T₁)A + B*f(T₂)B.
3. **Matrix perspective**: The perspective g(L,R) = f(L/R)R for commuting positive
   operators L, R is jointly convex when f is Löwner convex.
4. **Left/right multiplication**: For L(X) = AX and R(X) = XB (operators on M_n),
   apply the perspective with f(t) = -t^s to obtain joint concavity of
   (A,B) ↦ Tr(A^s K† B^{1-s} K).

## References

* Effros, *A Matrix Convexity Approach to Some Celebrated Quantum Inequalities* (2008)
* Lieb, *Convex trace functions and the Wigner-Yanase-Dyson conjecture* (1973)
-/
@[expose] public section

namespace Matrix

open scoped MatrixOrder ComplexOrder

/-- The Lieb joint function: Tr(Aᵖ K† B¹⁻ᵖ K)
for a (possibly rectangular) matrix K : m × n, A : n × n PSD, B : m × m PSD.
Uses CFC rpow (`A ^ p`) for positive semidefinite matrices. -/
noncomputable def liebJointFunction {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m]
    (K : Matrix m n ℂ) (p : ℝ)
    (A : Matrix n n ℂ) (_hA : A.PosSemidef)
    (B : Matrix m m ℂ) (_hB : B.PosSemidef) : ℂ :=
  Tr ((A ^ p) * Kᴴ * (B ^ (1 - p)) * K)

/-- liebJointFunction at p = 0 equals Tr(K†BK). -/
lemma liebJointFunction_zero_eq {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m]
    (K : Matrix m n ℂ)
    (A : Matrix n n ℂ) (hA : A.PosSemidef)
    (B : Matrix m m ℂ) (hB : B.PosSemidef) :
    liebJointFunction K 0 A hA B hB = Tr (Kᴴ * B * K) := by
  simp only [liebJointFunction, sub_zero]
  rw [CFC.rpow_zero A (by simpa [Matrix.le_iff] using hA),
      CFC.rpow_one B (by simpa [Matrix.le_iff] using hB), Matrix.one_mul]

/-- liebJointFunction at p = 1 equals Tr(AK†K). -/
lemma liebJointFunction_one_eq {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m]
    (K : Matrix m n ℂ)
    (A : Matrix n n ℂ) (hA : A.PosSemidef)
    (B : Matrix m m ℂ) (hB : B.PosSemidef) :
    liebJointFunction K 1 A hA B hB = Tr (A * Kᴴ * K) := by
  simp only [liebJointFunction, sub_self]
  rw [CFC.rpow_one A (by simpa [Matrix.le_iff] using hA),
      CFC.rpow_zero B (by simpa [Matrix.le_iff] using hB), Matrix.mul_one]

/-- Hilbert-Schmidt inner product: ⟨X, Y⟩_HS = Tr(X† Y).
Note: We use the physics convention ⟨X, Y⟩ = Tr(X† Y), which is conjugate-linear
in the first argument and linear in the second. -/
noncomputable def hsInnerProduct {m : Type*} [Fintype m]
    (X Y : Matrix m m ℂ) : ℂ :=
  (Xᴴ * Y).trace

namespace QuantumInfo
scoped notation "⟪" X ", " Y "⟫_HS" => Matrix.hsInnerProduct X Y
end QuantumInfo

/-- Hilbert-Schmidt inner product is related to liebJointFunction via left/right multiplication.
For positive semidefinite A, B and real p:
  ⟨A^p · K† · B^{1-p}, K†⟩_HS = Tr(A^p · K† · B^{1-p} · K)
This connects the operator-level perspective to the trace-level Lieb function. -/
private lemma hsInnerProduct_leftMul_rightMul {m : Type*} [Fintype m] [DecidableEq m]
    (A B : Matrix m m ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (K : Matrix m m ℂ) (p : ℝ) :
    hsInnerProduct ((A ^ p) * Kᴴ * (B ^ (1 - p))) Kᴴ = liebJointFunction K p A hA B hB := by
  simp only [hsInnerProduct, liebJointFunction]
  -- (A^p * K† * B^{1-p})† = B^{1-p}† * K * (A^p)†
  -- Since A^p and B^{1-p} are Hermitian (rpow of PSD is PSD hence Hermitian):
  have hAp_herm : (A ^ p)ᴴ = A ^ p := by
    rw [← matrixFunction_rpow_eq hA p]
    exact matrixFunction_isHermitian hA.1 (fun x => x ^ p)
  have hBp_herm : (B ^ (1 - p))ᴴ = B ^ (1 - p) := by
    rw [← matrixFunction_rpow_eq hB (1 - p)]
    exact matrixFunction_isHermitian hB.1 (fun x => x ^ (1 - p))
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hAp_herm, hBp_herm, Matrix.mul_assoc]
  -- LHS: Tr(B^{1-p} * K * A^p * K†), RHS: Tr(A^p * K† * B^{1-p} * K)
  -- By trace cyclicity (two shifts) these are equal
  simp only [← Matrix.mul_assoc]
  rw [trace_mul_cycle, trace_mul_cycle]
  simp only [Matrix.mul_assoc]

/-- The HS inner product ⟨v, matrixPerspective(f, L_A, R_B) v⟩ for f(t) = -t^p
and v = vec(K†) equals -Tr(A^p K† B^{1-p} K).

This is the key spectral identity connecting the matrix perspective
on left/right multiplication operators to the Lieb joint function.
See Effros (2008), Corollary 2.4 (proof).

The proof is technical but the key insight is:
- For commuting L = leftMulMatrix A and R = rightMulMatrix B,
  the perspective matrixPerspective(f, L, R) with f(t) = -t^p
  simplifies to -(L^p R^{1-p}) = -leftMulMatrix(A^p) * rightMulMatrix(B^{1-p})
- The quadratic form ⟨vec(K†), L_X R_Y vec(K†)⟩ = Tr(X K† Y K)
- Combining: ⟨v, (-L^p R^{1-p}) v⟩ = -Tr(A^p K† B^{1-p} K) = -liebJointFunction

For full generality this requires functional calculus on Kronecker products,
but the result follows from the trace identity hsInnerProduct_leftMul_rightMul
and the perspective structure. -/
private lemma matrixPerspective_inner_eq_neg_liebJointFunction {m : Type*} [Fintype m] [DecidableEq m]
    (K : Matrix m m ℂ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (A B : Matrix m m ℂ) (hA : A.PosDef) (hB : B.PosDef)
    (hL_psd : (𝐋 A).PosSemidef) (hR_pd : (𝐑 B).PosDef) :
    let v : (m × m) → ℂ := fun x => Kᴴ x.1 x.2
    (star v ⬝ᵥ (matrixPerspective (fun x => -(x ^ p))
      (𝐋 A) (𝐑 B) hL_psd hR_pd *ᵥ v)).re =
    -(liebJointFunction K p A hA.posSemidef B hB.posSemidef).re := by
  intro v
  have hp1' : 0 ≤ 1 - p := by linarith
  have h_persp :
      matrixPerspective (fun x => -(x ^ p)) (𝐋 A) (𝐑 B) hL_psd hR_pd =
      -(𝐋 (A ^ p) * 𝐑 (B ^ (1 - p))) :=
    Matrix.matrixPerspective_neg_leftRight_eq A B hA hB p hp hL_psd hR_pd
  -- Compute the quadratic form
  rw [h_persp, Matrix.neg_mulVec, dotProduct_neg, Complex.neg_re]
  congr 1
  -- Use quadForm_leftRightMul_eq_trace
  have h_quad := quadForm_leftRightMul_eq_trace (A ^ p) (B ^ (1 - p)) K
  rw [h_quad]
  -- Trace cyclicity:
  -- quadForm gives trace(K * A^p * K† * B^{1-p}), which after h_quad becomes
  -- trace(B^{1-p} * (K * A^p) * K†), need to show equals
  -- trace(A^p * K† * B^{1-p} * K) from liebJointFunction.
  congr 1
  -- Goal: (K * A^p * K† * B^{1-p}).trace = (A^p * K† * B^{1-p} * K).trace
  rw [Matrix.mul_assoc (K * A ^ p) Kᴴ (B ^ (1 - p)),
      Matrix.mul_assoc K (A ^ p) (Kᴴ * B ^ (1 - p)),
      trace_mul_cycle' K (A ^ p) (Kᴴ * B ^ (1 - p))]
  -- Now: (K† * B^{1-p} * (K * A^p)).trace = (A^p * K† * B^{1-p} * K).trace
  rw [← Matrix.mul_assoc (Kᴴ * B ^ (1 - p)) K (A ^ p)]
  -- Now: ((K†*B^{1-p}*K) * A^p).trace = (A^p * K†*B^{1-p}*K).trace
  rw [trace_mul_comm (Kᴴ * B ^ (1 - p) * K) (A ^ p)]
  -- Now: (A^p * (K†*B^{1-p}*K)).trace = (A^p * K†*B^{1-p}*K).trace
  congr 1; rw [Matrix.mul_assoc (A ^ p) Kᴴ, Matrix.mul_assoc (A ^ p)]

/-- **Lieb's Joint Concavity Theorem (Interior Case, Effros Proof)**

The key is that the Lieb function Tr(A^p K† B^{1-p} K) equals the HS inner product
⟨A^p K† B^{1-p}, K†⟩, and operator concavity of x^p implies joint concavity via
the left/right multiplication operator structure.

This proof uses the Effros approach: for Löwner convex f(t) = -t^p, the perspective
function g(L,R) = f(L/R)R is jointly convex for commuting operators L, R.
Applied to left/right multiplication operators L_A and R_B (which commute), the
HS inner product ⟨g(L_A, R_B)(K†), K†⟩ = -Tr(A^p K† B^{1-p} K) is jointly convex,
hence Tr(A^p K† B^{1-p} K) is jointly concave. -/
private lemma lieb_concavity_effros {m : Type*} [Fintype m] [DecidableEq m]
    (A₁ A₂ B₁ B₂ : Matrix m m ℂ)
    (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef) (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef)
    (K : Matrix m m ℂ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (w₁ w₂ : ℝ) (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hw : w₁ + w₂ = 1) :
    w₁ * (liebJointFunction K p A₁ hA₁.posSemidef B₁ hB₁.posSemidef).re +
    w₂ * (liebJointFunction K p A₂ hA₂.posSemidef B₂ hB₂.posSemidef).re ≤
    (liebJointFunction K p
      (w₁ • A₁ + w₂ • A₂) ((hA₁.posSemidef.smul hw₁).add (hA₂.posSemidef.smul hw₂))
      (w₁ • B₁ + w₂ • B₂) ((hB₁.posSemidef.smul hw₁).add (hB₂.posSemidef.smul hw₂))).re := by
  classical
  /- Proof by Effros's Matrix Perspective Approach -/
  -- 1. Setup the function f(x) = -x^p, which is Matrix Convex.
  let f : ℝ → ℝ := fun x => -(x ^ p)
  have hconv : IsJensenConvex f := neg_rpow_isJensenConvex hp0 (le_of_lt hp1)
  -- 2. Define Left and Right multiplication operators
  let L₁ := 𝐋 A₁
  let L₂ := 𝐋 A₂
  let R₁ := 𝐑 B₁
  let R₂ := 𝐑 B₂
  let L := w₁ • L₁ + w₂ • L₂
  let R := w₁ • R₁ + w₂ • R₂
  -- Properties of L and R
  have hL₁_psd : L₁.PosSemidef := leftMulMatrix_posSemidef hA₁.posSemidef
  have hL₂_psd : L₂.PosSemidef := leftMulMatrix_posSemidef hA₂.posSemidef
  have hR₁_pd : R₁.PosDef := rightMulMatrix_posDef hB₁
  have hR₂_pd : R₂.PosDef := rightMulMatrix_posDef hB₂
  have hR_pd : R.PosDef := PosDef.convex_comb_nonneg hR₁_pd hR₂_pd hw₁ hw₂ hw
  -- 3. Apply Joint Convexity of matrixPerspective
  have h_jconv := matrixPerspective_joint_convex hconv hL₁_psd hL₂_psd hR₁_pd hR₂_pd hw₁ hw₂ hw
  -- 4. Relate matrixPerspective to Lieb Function
  -- g(L, R) = f(L R⁻¹) R = -(L R⁻¹)^p R = -L^p R^{1-p} (for commuting L, R)
  -- Lieb(A, B) = Tr(A^p K† B^{1-p} K) = ⟨L_{A^p} R_{B^{1-p}} K†, K†⟩

  -- Helper: matrixPerspective f L R = -L^p R^(1-p)
  -- This requires commutativity L R = R L, which holds.
  -- And functional calculus property on Kronecker product.
  -- We assume the identity: ⟨matrixPerspective f L R K†, K†⟩_HS = -Lieb(A, B).
  let term1 := matrixPerspective f L₁ R₁ hL₁_psd hR₁_pd
  let term2 := matrixPerspective f L₂ R₂ hL₂_psd hR₂_pd
  let term_comb := matrixPerspective f L R ((hL₁_psd.smul hw₁).add (hL₂_psd.smul hw₂)) hR_pd
  -- The inequality is term_comb ≤ w₁ term1 + w₂ term2
  -- Apply ⟨· K†, K†⟩ which preserves order.
  let v : (m × m) → ℂ := fun x => Kᴴ x.1 x.2
  have h_jconv_le := h_jconv
  rw [Matrix.le_iff] at h_jconv_le
  -- Use that (RHS - LHS) is PSD => ⟨v, (RHS - LHS) v⟩ ≥ 0
  have h_vec_nonneg := h_jconv_le.dotProduct_mulVec_nonneg v
  -- Expand LHS linearity
  simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec] at h_vec_nonneg
  simp only [dotProduct_sub, dotProduct_add, dotProduct_smul] at h_vec_nonneg
  -- Connect to Lieb function
  -- Use the spectral identity: ⟨v, matrixPerspective(f, L_A, R_B) v⟩ = -liebJointFunction(K, p, A, B)
  have h_ident1 : (star v ⬝ᵥ (term1 *ᵥ v)).re = -(liebJointFunction K p A₁ hA₁.posSemidef B₁ hB₁.posSemidef).re := by
    simpa [term1, f] using
      matrixPerspective_inner_eq_neg_liebJointFunction K p (le_of_lt hp0) (le_of_lt hp1) A₁ B₁ hA₁ hB₁ hL₁_psd hR₁_pd
  have h_ident2 : (star v ⬝ᵥ (term2 *ᵥ v)).re = -(liebJointFunction K p A₂ hA₂.posSemidef B₂ hB₂.posSemidef).re := by
    simpa [term2, f] using
      matrixPerspective_inner_eq_neg_liebJointFunction K p (le_of_lt hp0) (le_of_lt hp1) A₂ B₂ hA₂ hB₂ hL₂_psd hR₂_pd
  have hA_comb : (w₁ • A₁ + w₂ • A₂).PosDef := PosDef.convex_comb_nonneg hA₁ hA₂ hw₁ hw₂ hw
  have hB_comb : (w₁ • B₁ + w₂ • B₂).PosDef := PosDef.convex_comb_nonneg hB₁ hB₂ hw₁ hw₂ hw
  -- The combined identity follows from matrixPerspective_inner_eq_neg_liebJointFunction
  -- applied to the convex combinations, after identifying L = leftMulMatrix(w₁A₁+w₂A₂)
  -- and R = rightMulMatrix(w₁B₁+w₂B₂) via linearity of leftMulMatrix/rightMulMatrix.
  have h_ident_comb : (star v ⬝ᵥ (term_comb *ᵥ v)).re = -(liebJointFunction K p
      (w₁ • A₁ + w₂ • A₂) ((hA₁.posSemidef.smul hw₁).add (hA₂.posSemidef.smul hw₂))
      (w₁ • B₁ + w₂ • B₂) ((hB₁.posSemidef.smul hw₁).add (hB₂.posSemidef.smul hw₂))).re := by
    have hLlin : L = 𝐋 (w₁ • A₁ + w₂ • A₂) := by
      ext ij kl
      rcases ij with ⟨i, j⟩
      rcases kl with ⟨k, l⟩
      by_cases h : j = l
      · subst h
        simp [L, L₁, L₂, leftMulMatrix_apply]
      · simp [L, L₁, L₂, leftMulMatrix_apply, h]
    have hRlin : R = 𝐑 (w₁ • B₁ + w₂ • B₂) := by
      ext ij kl
      rcases ij with ⟨i, j⟩
      rcases kl with ⟨k, l⟩
      by_cases h : i = k
      · subst h
        simp [R, R₁, R₂, rightMulMatrix_apply]
      · simp [R, R₁, R₂, rightMulMatrix_apply, h]
    have hR_pd' : (𝐑 (w₁ • B₁ + w₂ • B₂)).PosDef := by rw [← hRlin]; exact hR_pd
    have hL_psd' : (𝐋 (w₁ • A₁ + w₂ • A₂)).PosSemidef := by
      rw [← hLlin]; exact (hL₁_psd.smul hw₁).add (hL₂_psd.smul hw₂)
    -- Apply matrixPerspective_inner_eq_neg_liebJointFunction to the convex combination
    -- The key identity relates the HS inner product to the Lieb function.
    -- After establishing that term_comb = matrixPerspective f (leftMulMatrix (w₁•A₁+w₂•A₂))
    --   (rightMulMatrix (w₁•B₁+w₂•B₂)) via the linearity hLlin and hRlin,
    -- the result follows from the same spectral identity as h_ident1 and h_ident2.
    -- The connection: L = leftMulMatrix (w₁ • A₁ + w₂ • A₂) and
    -- R = rightMulMatrix (w₁ • B₁ + w₂ • B₂), so term_comb is the matrixPerspective
    -- applied to these operators with the convex combination matrices.
    -- The matrixPerspective_inner_eq_neg_liebJointFunction lemma gives us
    -- the result for general positive definite matrices.
    have h_apply := matrixPerspective_inner_eq_neg_liebJointFunction K p
        (le_of_lt hp0) (le_of_lt hp1)
        (w₁ • A₁ + w₂ • A₂) (w₁ • B₁ + w₂ • B₂) hA_comb hB_comb hL_psd' hR_pd'
    -- The term_comb uses L and R which equal leftMulMatrix/rightMulMatrix of convex combs.
    -- After substitution, the goal matches h_apply.
    -- The matrices are definitionally equal after applying hLlin and hRlin.
    -- term_comb = matrixPerspective f L R _ _
    --           = matrixPerspective f (leftMulMatrix (w₁•A₁+w₂•A₂)) (rightMulMatrix (w₁•B₁+w₂•B₂)) _ _
    -- The proof terms may differ but the matrices are equal by proof irrelevance.
    -- Since both sides compute the same quadratic form value, they are equal.
    -- We establish this by showing the matrixPerspective matrices are equal.
    have hpersp_eq : term_comb = matrixPerspective f
        (𝐋 (w₁ • A₁ + w₂ • A₂))
        (𝐑 (w₁ • B₁ + w₂ • B₂)) hL_psd' hR_pd' := by
      simp only [term_comb, L, R, L₁, L₂, R₁, R₂]
      exact matrixPerspective_congr f _ _ _ _
        _ hL_psd' _ hR_pd'
        (by rw [leftMulMatrix_add, ← leftMulMatrix_smul_real, ← leftMulMatrix_smul_real])
        (by rw [rightMulMatrix_add, ← rightMulMatrix_smul_real, ← rightMulMatrix_smul_real])
    rw [hpersp_eq]
    exact h_apply
  -- Substitute identities into the nonnegativity inequality
  have h_vec_re :
      0 ≤
        (w₁ • (star v ⬝ᵥ (term1 *ᵥ v)) + w₂ • (star v ⬝ᵥ (term2 *ᵥ v)) -
          (star v ⬝ᵥ (term_comb *ᵥ v))).re := by
    exact (Complex.nonneg_iff.mp h_vec_nonneg).1
  have h_vec_re' :
      0 ≤
        (w₁ * (star v ⬝ᵥ (term1 *ᵥ v)).re + w₂ * (star v ⬝ᵥ (term2 *ᵥ v)).re -
          (star v ⬝ᵥ (term_comb *ᵥ v)).re) := by
    simpa [Complex.add_re, Complex.sub_re, Complex.real_smul] using h_vec_re
  rw [h_ident1, h_ident2, h_ident_comb] at h_vec_re'
  linarith


/-- **Lieb's Joint Concavity Theorem (General Case)** -/
private lemma lieb_joint_concavity {m : Type*} [Fintype m] [DecidableEq m]
    (A₁ A₂ B₁ B₂ : Matrix m m ℂ)
    (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef) (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef)
    (K : Matrix m m ℂ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w₁ w₂ : ℝ) (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hw : w₁ + w₂ = 1) :
    w₁ * (liebJointFunction K p A₁ hA₁.posSemidef B₁ hB₁.posSemidef).re +
    w₂ * (liebJointFunction K p A₂ hA₂.posSemidef B₂ hB₂.posSemidef).re ≤
    (liebJointFunction K p
      (w₁ • A₁ + w₂ • A₂) ((hA₁.posSemidef.smul hw₁).add (hA₂.posSemidef.smul hw₂))
      (w₁ • B₁ + w₂ • B₂) ((hB₁.posSemidef.smul hw₁).add (hB₂.posSemidef.smul hw₂))).re := by
  -- Handle boundary cases p = 0 and p = 1 separately
  rcases eq_or_lt_of_le hp0 with rfl | hp0'
  · -- p = 0: Tr(K†BK) is linear in B, so equality holds
    rw [liebJointFunction_zero_eq, liebJointFunction_zero_eq, liebJointFunction_zero_eq]
    have h_linear : (Kᴴ * (w₁ • B₁ + w₂ • B₂) * K).trace =
        (w₁ : ℂ) * (Kᴴ * B₁ * K).trace + (w₂ : ℂ) * (Kᴴ * B₂ * K).trace := by
      rw [Matrix.mul_add, Matrix.add_mul]
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul]
      rw [trace_add, trace_smul, trace_smul]
      simp only [Complex.real_smul]
    rw [h_linear]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero]
    exact le_refl _
  rcases eq_or_lt_of_le hp1 with rfl | hp1'
  · -- p = 1: Tr(AK†K) is linear in A, so equality holds
    rw [liebJointFunction_one_eq, liebJointFunction_one_eq, liebJointFunction_one_eq]
    have h_linear : ((w₁ • A₁ + w₂ • A₂) * Kᴴ * K).trace =
        (w₁ : ℂ) * (A₁ * Kᴴ * K).trace + (w₂ : ℂ) * (A₂ * Kᴴ * K).trace := by
      rw [Matrix.add_mul, Matrix.add_mul]
      rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul]
      rw [trace_add, trace_smul, trace_smul]
      simp only [Complex.real_smul]
    rw [h_linear]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero]
    exact le_refl _
  -- For 0 < p < 1, apply Effros's Löwner convexity approach
  exact lieb_concavity_effros A₁ A₂ B₁ B₂ hA₁ hA₂ hB₁ hB₂ K p hp0' hp1' w₁ w₂ hw₁ hw₂ hw

/-- For a positive semidefinite matrix A and real p, the map
    ε ↦ (A + ε I)ᵖ converges to Aᵖ as ε → 0⁺. -/
private lemma rpow_tendsto_smul_one {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.PosSemidef) (p : ℝ) (hp : 0 ≤ p) :
    Filter.Tendsto (fun ε : ℝ => (A + (ε : ℂ) • (1 : Matrix m m ℂ)) ^ p)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (A ^ p)) := by
  -- Express A^p and (A + ε•1)^p via the continuous functional calculus.
  -- Using matrixFunction and cfc, reduce to pointwise convergence of x^p as ε → 0+.
  have hA_eq : A ^ p = cfc (fun x : ℝ => x ^ p) A := by
    rw [← matrixFunction_rpow_eq hA, matrixFunction_eq_cfc hA.1]
  have hshift_eq : ∀ ε : ℝ, 0 < ε → (A + (ε : ℂ) • (1 : Matrix m m ℂ)) ^ p =
      cfc (fun x : ℝ => (x + ε) ^ p) A := by
    intro ε hε
    have hcfc_shift : cfc (fun x : ℝ => x + ε) A = A + (ε : ℂ) • (1 : Matrix m m ℂ) := by
      rw [← matrixFunction_eq_cfc hA.1]; exact matrixFunction_add_const hA.1 ε
    have hcont_p : ContinuousOn (fun x : ℝ => x ^ p) ((fun x : ℝ => x + ε) '' spectrum ℝ A) := by
      apply ContinuousOn.rpow_const continuousOn_id
      rintro x ⟨_, hy_spec, rfl⟩
      rw [hA.1.spectrum_real_eq_range_eigenvalues] at hy_spec
      obtain ⟨i, rfl⟩ := hy_spec
      left; simp only [id, ne_eq]; linarith [hA.eigenvalues_nonneg i]
    rw [CFC.rpow_eq_cfc_real (a := A + (ε : ℂ) • 1)
          (ha := by simpa [Matrix.le_iff] using (hA.add_smul_one_posDef hε).posSemidef),
        ← hcfc_shift, ← cfc_comp' (fun x => x ^ p) (fun x => x + ε) A hcont_p]
  -- Build the tendsto for the cfc version via uniform convergence on the finite spectrum.
  have htend_cfc : Filter.Tendsto (fun ε : ℝ => cfc (fun x : ℝ => (x + ε) ^ p) A)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (cfc (fun x : ℝ => x ^ p) A)) := by
    apply tendsto_cfc_fun
    · -- TendstoUniformlyOn: reduce to pointwise convergence on the finite spectrum.
      have hspec_finite : (spectrum ℝ A).Finite := by
        rw [hA.1.spectrum_real_eq_range_eigenvalues]; exact Set.finite_range _
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε₀ hε₀
      have hptwise : ∀ x ∈ spectrum ℝ A, ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
          dist (x ^ p) ((x + ε) ^ p) < ε₀ := by
        intro x hx
        have hx_nn : 0 ≤ x := by
          rw [hA.1.spectrum_real_eq_range_eigenvalues] at hx
          obtain ⟨i, rfl⟩ := hx; exact hA.eigenvalues_nonneg i
        have hcont : ContinuousAt (fun ε : ℝ => (x + ε) ^ p) 0 := by
          apply ContinuousAt.rpow_const (continuousAt_const.add continuousAt_id)
          rcases hx_nn.eq_or_lt' with rfl | hx_pos
          · right; simpa using hp
          · left; simp; linarith
        have key : Filter.Tendsto (fun ε : ℝ => (x + ε) ^ p)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds (x ^ p)) := by
          have h := hcont.tendsto; simp only [add_zero] at h
          exact h.mono_left nhdsWithin_le_nhds
        exact (Metric.tendsto_nhds.mp key ε₀ hε₀).mono
          (fun ε hε => by rw [dist_comm]; exact hε)
      have key := (Filter.eventually_all_finset hspec_finite.toFinset).mpr
        (fun x hx => hptwise x (hspec_finite.mem_toFinset.mp hx))
      exact key.mono (fun ε hε x hx => hε x (hspec_finite.mem_toFinset.mpr hx))
    · -- ContinuousOn (fun x => (x + ε)^p) (spectrum ℝ A) for all ε > 0.
      apply eventually_nhdsWithin_of_forall
      intro ε hε_pos
      apply ContinuousOn.rpow_const (by fun_prop)
      rintro x hx; left
      rw [hA.1.spectrum_real_eq_range_eigenvalues] at hx
      obtain ⟨i, rfl⟩ := hx
      intro h
      linarith [hA.eigenvalues_nonneg i, Set.mem_Ioi.mp hε_pos]
  rw [hA_eq]
  exact htend_cfc.congr' (eventually_nhdsWithin_of_forall (fun ε hε => (hshift_eq ε hε).symm))

/-- **Lieb's Joint Concavity Theorem (PosSemidef extension)**

Extension of `lieb_joint_concavity` from positive definite to positive semidefinite matrices,
via an ε-regularization argument.

For positive semidefinite matrices A₁, A₂, B₁, B₂ and any matrix K, the map
(A, B) ↦ Tr(Aᵖ K† B¹⁻ᵖ K) is jointly concave:
  w₁ · Tr(A₁ᵖ K† B₁¹⁻ᵖ K) + w₂ · Tr(A₂ᵖ K† B₂¹⁻ᵖ K)
  ≤ Tr((w₁ A₁ + w₂ A₂)ᵖ K† (w₁ B₁ + w₂ B₂)¹⁻ᵖ K)

**Proof**: For each ε > 0, apply `lieb_joint_concavity` to (Aᵢ + ε I, Bᵢ + ε I)
which are positive definite (by `PosSemidef.add_smul_one_posDef`). The inequality is preserved in the
limit ε → 0⁺ by CFC continuity (`rpow_tendsto_smul_one`). -/
theorem lieb_joint_concavity_semidef {m : Type*} [Fintype m] [DecidableEq m]
    (A₁ A₂ B₁ B₂ : Matrix m m ℂ)
    (hA₁ : A₁.PosSemidef) (hA₂ : A₂.PosSemidef)
    (hB₁ : B₁.PosSemidef) (hB₂ : B₂.PosSemidef)
    (K : Matrix m m ℂ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w₁ w₂ : ℝ) (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hw : w₁ + w₂ = 1) :
    w₁ * (liebJointFunction K p A₁ hA₁ B₁ hB₁).re +
    w₂ * (liebJointFunction K p A₂ hA₂ B₂ hB₂).re ≤
    (liebJointFunction K p
      (w₁ • A₁ + w₂ • A₂) ((hA₁.smul hw₁).add (hA₂.smul hw₂))
      (w₁ • B₁ + w₂ • B₂) ((hB₁.smul hw₁).add (hB₂.smul hw₂))).re := by
  -- For each ε > 0, Aᵢ + ε•1 is PosDef; the inequality holds by lieb_joint_concavity
  -- Use unfolded form to avoid PosSemidef proof dependencies in the type
  have hε_ineq : ∀ ε : ℝ, 0 < ε →
      w₁ * ((A₁ + (ε:ℂ) • 1) ^ p * Kᴴ * (B₁ + (ε:ℂ) • 1) ^ (1 - p) * K).trace.re +
      w₂ * ((A₂ + (ε:ℂ) • 1) ^ p * Kᴴ * (B₂ + (ε:ℂ) • 1) ^ (1 - p) * K).trace.re ≤
      ((w₁ • A₁ + w₂ • A₂ + (ε:ℂ) • 1) ^ p * Kᴴ *
       (w₁ • B₁ + w₂ • B₂ + (ε:ℂ) • 1) ^ (1 - p) * K).trace.re := by
    intro ε hε
    -- Key: w₁•(Aᵢ + ε•1) + w₂•(Aᵢ + ε•1) = w₁•Aᵢ + w₂•Aᵢ + ε•1 (using w₁ + w₂ = 1)
    have hcomb_A : w₁ • (A₁ + (ε:ℂ) • 1) + w₂ • (A₂ + (ε:ℂ) • 1) = w₁ • A₁ + w₂ • A₂ + (ε:ℂ) • 1 :=
      calc w₁ • (A₁ + (ε:ℂ) • 1) + w₂ • (A₂ + (ε:ℂ) • 1)
            = w₁ • A₁ + w₁ • ((ε:ℂ) • 1) + (w₂ • A₂ + w₂ • ((ε:ℂ) • 1)) := by
                simp [smul_add]
          _ = w₁ • A₁ + w₂ • A₂ + (w₁ • ((ε:ℂ) • 1) + w₂ • ((ε:ℂ) • 1)) := by abel
          _ = w₁ • A₁ + w₂ • A₂ + (w₁ + w₂) • ((ε:ℂ) • 1) := by rw [← add_smul]
          _ = w₁ • A₁ + w₂ • A₂ + (ε:ℂ) • 1 := by rw [hw, one_smul]
    have hcomb_B : w₁ • (B₁ + (ε:ℂ) • 1) + w₂ • (B₂ + (ε:ℂ) • 1) = w₁ • B₁ + w₂ • B₂ + (ε:ℂ) • 1 :=
      calc w₁ • (B₁ + (ε:ℂ) • 1) + w₂ • (B₂ + (ε:ℂ) • 1)
            = w₁ • B₁ + w₁ • ((ε:ℂ) • 1) + (w₂ • B₂ + w₂ • ((ε:ℂ) • 1)) := by
                simp [smul_add]
          _ = w₁ • B₁ + w₂ • B₂ + (w₁ • ((ε:ℂ) • 1) + w₂ • ((ε:ℂ) • 1)) := by abel
          _ = w₁ • B₁ + w₂ • B₂ + (w₁ + w₂) • ((ε:ℂ) • 1) := by rw [← add_smul]
          _ = w₁ • B₁ + w₂ • B₂ + (ε:ℂ) • 1 := by rw [hw, one_smul]
    have h := lieb_joint_concavity (A₁ + (ε:ℂ) • 1) (A₂ + (ε:ℂ) • 1)
                                   (B₁ + (ε:ℂ) • 1) (B₂ + (ε:ℂ) • 1)
                                   (hA₁.add_smul_one_posDef hε) (hA₂.add_smul_one_posDef hε)
                                   (hB₁.add_smul_one_posDef hε) (hB₂.add_smul_one_posDef hε)
                                   K p hp0 hp1 w₁ w₂ hw₁ hw₂ hw
    simp only [liebJointFunction] at h ⊢
    rw [← hcomb_A, ← hcomb_B]
    exact h
  -- Convergence: as ε → 0⁺, liebJointFunction converges for each pair
  -- Unfold liebJointFunction to avoid PosSemidef proof dependencies in the type
  have hconv_lhs : Filter.Tendsto (fun ε : ℝ =>
        w₁ * ((A₁ + (ε:ℂ) • 1) ^ p * Kᴴ * (B₁ + (ε:ℂ) • 1) ^ (1 - p) * K).trace.re +
        w₂ * ((A₂ + (ε:ℂ) • 1) ^ p * Kᴴ * (B₂ + (ε:ℂ) • 1) ^ (1 - p) * K).trace.re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (w₁ * (liebJointFunction K p A₁ hA₁ B₁ hB₁).re +
             w₂ * (liebJointFunction K p A₂ hA₂ B₂ hB₂).re)) := by
    simp only [liebJointFunction]
    apply Filter.Tendsto.add
    · apply Filter.Tendsto.const_mul
      apply (Complex.continuous_re.comp continuous_id.matrix_trace).continuousAt.tendsto.comp
      exact ((rpow_tendsto_smul_one hA₁ p hp0).mul_const Kᴴ).mul
              (rpow_tendsto_smul_one hB₁ (1 - p) (by linarith)) |>.mul_const K
    · apply Filter.Tendsto.const_mul
      apply (Complex.continuous_re.comp continuous_id.matrix_trace).continuousAt.tendsto.comp
      exact ((rpow_tendsto_smul_one hA₂ p hp0).mul_const Kᴴ).mul
              (rpow_tendsto_smul_one hB₂ (1 - p) (by linarith)) |>.mul_const K
  have hconv_rhs : Filter.Tendsto (fun ε : ℝ =>
        ((w₁ • A₁ + w₂ • A₂ + (ε:ℂ) • 1) ^ p * Kᴴ *
         (w₁ • B₁ + w₂ • B₂ + (ε:ℂ) • 1) ^ (1 - p) * K).trace.re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (liebJointFunction K p (w₁ • A₁ + w₂ • A₂) ((hA₁.smul hw₁).add (hA₂.smul hw₂))
                                    (w₁ • B₁ + w₂ • B₂) ((hB₁.smul hw₁).add (hB₂.smul hw₂))).re) := by
    simp only [liebJointFunction]
    apply (Complex.continuous_re.comp continuous_id.matrix_trace).continuousAt.tendsto.comp
    exact ((rpow_tendsto_smul_one ((hA₁.smul hw₁).add (hA₂.smul hw₂)) p hp0).mul_const Kᴴ).mul
            (rpow_tendsto_smul_one ((hB₁.smul hw₁).add (hB₂.smul hw₂)) (1 - p) (by linarith)) |>.mul_const K
  -- Combine: lhs_limit ≤ rhs_limit via the ε-pointwise inequality
  apply le_of_tendsto_of_tendsto hconv_lhs hconv_rhs
  filter_upwards [self_mem_nhdsWithin (s := Set.Ioi (0:ℝ))] with ε (hε : ε ∈ Set.Ioi 0)
  exact hε_ineq ε (Set.mem_Ioi.mp hε)

/-- Block diagonal matrix `fromBlocks A 0 0 0` is positive semidefinite when `A` is. -/
private lemma fromBlocks_top_posSemidef {n m : Type*} [Fintype n] [Fintype m]
    {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    (Matrix.fromBlocks A 0 0 (0 : Matrix m m ℂ)).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg
      (by simpa using Matrix.IsHermitian.fromBlocks hA.1 (by simp) Matrix.isHermitian_zero) ?_
  intro v
  have heq : star v ⬝ᵥ (Matrix.fromBlocks A 0 0 0 *ᵥ v) =
      star (fun i => v (Sum.inl i)) ⬝ᵥ (A *ᵥ fun i => v (Sum.inl i)) := by
    simp [dotProduct, Fintype.sum_sum_type, fromBlocks_mulVec_inl, fromBlocks_mulVec_inr,
      Matrix.zero_mulVec]
  rw [heq]
  exact hA.dotProduct_mulVec_nonneg _

/-- Block diagonal matrix `fromBlocks 0 0 0 B` is positive semidefinite when `B` is. -/
private lemma fromBlocks_bot_posSemidef {n m : Type*} [Fintype n] [Fintype m]
    {B : Matrix m m ℂ} (hB : B.PosSemidef) :
    (Matrix.fromBlocks (0 : Matrix n n ℂ) 0 0 B).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg
      (by simpa using Matrix.IsHermitian.fromBlocks Matrix.isHermitian_zero (by simp) hB.1) ?_
  intro v
  have heq : star v ⬝ᵥ (Matrix.fromBlocks 0 0 0 B *ᵥ v) =
      star (fun i => v (Sum.inr i)) ⬝ᵥ (B *ᵥ fun i => v (Sum.inr i)) := by
    simp [dotProduct, Fintype.sum_sum_type, fromBlocks_mulVec_inl, fromBlocks_mulVec_inr,
      Matrix.zero_mulVec]
  rw [heq]
  exact hB.dotProduct_mulVec_nonneg _

/-- For `0 < p`, the rpow of `fromBlocks A 0 0 0` equals `fromBlocks (A^p) 0 0 0`. -/
private lemma fromBlocks_top_rpow {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m]
    {A : Matrix n n ℂ} (hA : A.PosSemidef) (p : ℝ) (hp : 0 < p) :
    (Matrix.fromBlocks A 0 0 (0 : Matrix m m ℂ)) ^ p = Matrix.fromBlocks (A ^ p) 0 0 0 := by
  have hAsa : IsSelfAdjoint A := hA.1
  have h0sa : IsSelfAdjoint (0 : Matrix m m ℂ) := Matrix.isHermitian_zero
  have hcont : ContinuousOn (fun x : ℝ => x ^ p)
      (spectrum ℝ A ∪ spectrum ℝ (0 : Matrix m m ℂ)) :=
    (continuousOn_id.rpow_const fun _ _ => Or.inr hp.le)
  have h0m : cfc (fun x : ℝ => x ^ p) (0 : Matrix m m ℂ) = 0 := by
    simp [Real.zero_rpow hp.ne']
  rw [CFC.rpow_eq_cfc_real (a := fromBlocks A 0 0 0)
        (ha := by rw [Matrix.le_iff, sub_zero]; exact fromBlocks_top_posSemidef hA),
      cfc_fromBlocks_diag' A 0 hAsa h0sa (fun x => x ^ p) hcont,
      ← CFC.rpow_eq_cfc_real (a := A)
          (ha := by rw [Matrix.le_iff, sub_zero]; exact hA),
      h0m]

/-- For `0 < p`, the rpow of `fromBlocks 0 0 0 B` equals `fromBlocks 0 0 0 (B^p)`. -/
private lemma fromBlocks_bot_rpow {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m]
    {B : Matrix m m ℂ} (hB : B.PosSemidef) (p : ℝ) (hp : 0 < p) :
    (Matrix.fromBlocks (0 : Matrix n n ℂ) 0 0 B) ^ p = Matrix.fromBlocks 0 0 0 (B ^ p) := by
  have hBsa : IsSelfAdjoint B := hB.1
  have h0sa : IsSelfAdjoint (0 : Matrix n n ℂ) := Matrix.isHermitian_zero
  have hcont : ContinuousOn (fun x : ℝ => x ^ p)
      (spectrum ℝ (0 : Matrix n n ℂ) ∪ spectrum ℝ B) :=
    (continuousOn_id.rpow_const fun _ _ => Or.inr hp.le)
  have h0n : cfc (fun x : ℝ => x ^ p) (0 : Matrix n n ℂ) = 0 := by
    simp [Real.zero_rpow hp.ne']
  rw [CFC.rpow_eq_cfc_real (a := fromBlocks 0 0 0 B)
        (ha := by rw [Matrix.le_iff, sub_zero]; exact fromBlocks_bot_posSemidef hB),
      cfc_fromBlocks_diag' 0 B h0sa hBsa (fun x => x ^ p) hcont,
      ← CFC.rpow_eq_cfc_real (a := B)
          (ha := by rw [Matrix.le_iff, sub_zero]; exact hB),
      h0n]

/-- The block Lieb identity: the rectangular Lieb function for the original matrices
equals the (square) Lieb function applied with block-embedded matrices.
For the block square matrix
K̃ = [0, K†; K, 0],
Ã = [A, 0; 0, 0],
B̃ = [0, 0; 0, B]:
  liebJointFunction(K̃, p, Ã, B̃) = liebJointFunction(K, p, A, B)

This identity is proved by direct block matrix computation. -/
private lemma liebJointFunction_eq_block {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m]
    (K : Matrix m n ℂ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (A : Matrix n n ℂ) (hA : A.PosSemidef)
    (B : Matrix m m ℂ) (hB : B.PosSemidef) :
    liebJointFunction (fromBlocks 0 Kᴴ K 0) p
        (fromBlocks A 0 0 0) (fromBlocks_top_posSemidef hA)
        (fromBlocks 0 0 0 B) (fromBlocks_bot_posSemidef hB) =
    liebJointFunction K p A hA B hB := by
  simp only [liebJointFunction]
  -- Compute (fromBlocks A 0 0 0)^p = fromBlocks (A^p) 0 0 0
  have hAp : (fromBlocks A 0 0 (0 : Matrix m m ℂ)) ^ p = fromBlocks (A ^ p) 0 0 0 :=
    fromBlocks_top_rpow hA p hp
  -- Compute (fromBlocks 0 0 0 B)^{1-p} = fromBlocks 0 0 0 (B^{1-p})
  have hB1p : (fromBlocks (0 : Matrix n n ℂ) 0 0 B) ^ (1 - p) =
      fromBlocks 0 0 0 (B ^ (1 - p)) :=
    fromBlocks_bot_rpow hB (1 - p) (by linarith)
  -- (fromBlocks 0 Kᴴ K 0)ᴴ = fromBlocks 0 Kᴴ K 0
  have hKH : (fromBlocks 0 Kᴴ K 0 : Matrix (n ⊕ m) (n ⊕ m) ℂ)ᴴ = fromBlocks 0 Kᴴ K 0 := by
    rw [Matrix.fromBlocks_conjTranspose]
    simp
  rw [hAp, hB1p, hKH]
  simp only [fromBlocks_multiply]
  simp [Matrix.trace, Fintype.sum_sum_type]

private lemma fromBlocks_smul_top {n m : Type*} [Fintype n] [Fintype m]
    (A : Matrix n n ℂ) (w : ℝ) :
    w • (fromBlocks A 0 0 (0 : Matrix m m ℂ)) = fromBlocks (w • A) 0 0 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [fromBlocks, smul_zero]

private lemma fromBlocks_smul_bot {n m : Type*} [Fintype n] [Fintype m]
    (B : Matrix m m ℂ) (w : ℝ) :
    w • (fromBlocks (0 : Matrix n n ℂ) 0 0 B) = fromBlocks 0 0 0 (w • B) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [fromBlocks, smul_zero]

/-- **Lieb's Joint Concavity Theorem for Rectangular Matrices (PosSemidef extension)**

For K : m × n rectangular and positive semidefinite A₁, A₂ : n × n,
B₁, B₂ : m × m, the map (A, B) ↦ Tr(Aᵖ K† B¹⁻ᵖ K)
is jointly concave:
  w₁ · Tr(A₁ᵖ K† B₁¹⁻ᵖ K) + w₂ · Tr(A₂ᵖ K† B₂¹⁻ᵖ K)
  ≤ Tr((w₁ A₁ + w₂ A₂)ᵖ K† (w₁ B₁ + w₂ B₂)¹⁻ᵖ K)

**Proof**: Embed in the block space n ⊕ m using
K̃ = [0, K†; K, 0],
Ãᵢ = [Aᵢ, 0; 0, 0],
B̃ᵢ = [0, 0; 0, Bᵢ],
and apply `lieb_joint_concavity_semidef`. -/
theorem lieb_joint_concavity_rect_semidef {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m]
    (A₁ A₂ : Matrix n n ℂ) (hA₁ : A₁.PosSemidef) (hA₂ : A₂.PosSemidef)
    (B₁ B₂ : Matrix m m ℂ) (hB₁ : B₁.PosSemidef) (hB₂ : B₂.PosSemidef)
    (K : Matrix m n ℂ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w₁ w₂ : ℝ) (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hw : w₁ + w₂ = 1) :
    w₁ * (liebJointFunction K p A₁ hA₁ B₁ hB₁).re +
    w₂ * (liebJointFunction K p A₂ hA₂ B₂ hB₂).re ≤
    (liebJointFunction K p
      (w₁ • A₁ + w₂ • A₂) ((hA₁.smul hw₁).add (hA₂.smul hw₂))
      (w₁ • B₁ + w₂ • B₂) ((hB₁.smul hw₁).add (hB₂.smul hw₂))).re := by
  -- Boundary cases p = 0 and p = 1: both sides are linear, giving equality
  rcases eq_or_lt_of_le hp0 with rfl | hp0'
  · -- p = 0: Tr(K†BK) is linear in B
    simp only [liebJointFunction_zero_eq]
    have h_linear : (Kᴴ * (w₁ • B₁ + w₂ • B₂) * K).trace =
        (w₁ : ℂ) * (Kᴴ * B₁ * K).trace + (w₂ : ℂ) * (Kᴴ * B₂ * K).trace := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
          Matrix.mul_smul, Matrix.smul_mul, trace_add, trace_smul, trace_smul]
      simp [Complex.real_smul]
    rw [h_linear]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    exact le_refl _
  rcases eq_or_lt_of_le hp1 with rfl | hp1'
  · -- p = 1: Tr(AK†K) is linear in A
    simp only [liebJointFunction_one_eq]
    have h_linear : ((w₁ • A₁ + w₂ • A₂) * Kᴴ * K).trace =
        (w₁ : ℂ) * (A₁ * Kᴴ * K).trace + (w₂ : ℂ) * (A₂ * Kᴴ * K).trace := by
      rw [Matrix.add_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul,
          Matrix.smul_mul, Matrix.smul_mul, trace_add, trace_smul, trace_smul]
      simp [Complex.real_smul]
    rw [h_linear]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    exact le_refl _
  -- Interior case: embed in (n ⊕ m) block space and apply lieb_joint_concavity_semidef
  -- Define block matrices in (n ⊕ m) × (n ⊕ m) space
  let Kblock : Matrix (n ⊕ m) (n ⊕ m) ℂ := fromBlocks 0 Kᴴ K 0
  let Ablock1 : Matrix (n ⊕ m) (n ⊕ m) ℂ := fromBlocks A₁ 0 0 0
  let Ablock2 : Matrix (n ⊕ m) (n ⊕ m) ℂ := fromBlocks A₂ 0 0 0
  let Bblock1 : Matrix (n ⊕ m) (n ⊕ m) ℂ := fromBlocks 0 0 0 B₁
  let Bblock2 : Matrix (n ⊕ m) (n ⊕ m) ℂ := fromBlocks 0 0 0 B₂
  -- PSD properties
  have hAb1 : Ablock1.PosSemidef := fromBlocks_top_posSemidef hA₁
  have hAb2 : Ablock2.PosSemidef := fromBlocks_top_posSemidef hA₂
  have hBb1 : Bblock1.PosSemidef := fromBlocks_bot_posSemidef hB₁
  have hBb2 : Bblock2.PosSemidef := fromBlocks_bot_posSemidef hB₂
  -- Apply lieb_joint_concavity_semidef in (n⊕m) space
  have key := lieb_joint_concavity_semidef Ablock1 Ablock2 Bblock1 Bblock2
    hAb1 hAb2 hBb1 hBb2 Kblock p hp0 hp1 w₁ w₂ hw₁ hw₂ hw
  -- Rewrite using the block identity
  have hid₁ := liebJointFunction_eq_block K p hp0' hp1' A₁ hA₁ B₁ hB₁
  have hid₂ := liebJointFunction_eq_block K p hp0' hp1' A₂ hA₂ B₂ hB₂
  -- Identify convex combinations of blocks
  have hAcomb : w₁ • Ablock1 + w₂ • Ablock2 = fromBlocks (w₁ • A₁ + w₂ • A₂) 0 0 0 := by
    simp only [Ablock1, Ablock2, fromBlocks_smul_top, fromBlocks_add, add_zero]
  have hBcomb : w₁ • Bblock1 + w₂ • Bblock2 = fromBlocks 0 0 0 (w₁ • B₁ + w₂ • B₂) := by
    simp only [Bblock1, Bblock2, fromBlocks_smul_bot, fromBlocks_add, zero_add]
  have hAcomb_psd : (w₁ • Ablock1 + w₂ • Ablock2).PosSemidef := (hAb1.smul hw₁).add (hAb2.smul hw₂)
  have hBcomb_psd : (w₁ • Bblock1 + w₂ • Bblock2).PosSemidef := (hBb1.smul hw₁).add (hBb2.smul hw₂)
  have hidcomb : liebJointFunction Kblock p (w₁ • Ablock1 + w₂ • Ablock2) hAcomb_psd
      (w₁ • Bblock1 + w₂ • Bblock2) hBcomb_psd =
      liebJointFunction K p (w₁ • A₁ + w₂ • A₂) ((hA₁.smul hw₁).add (hA₂.smul hw₂))
        (w₁ • B₁ + w₂ • B₂) ((hB₁.smul hw₁).add (hB₂.smul hw₂)) := by
    simp only [liebJointFunction]
    conv_lhs => rw [hAcomb, hBcomb]
    have key2 := liebJointFunction_eq_block K p hp0' hp1'
        (w₁ • A₁ + w₂ • A₂) ((hA₁.smul hw₁).add (hA₂.smul hw₂))
        (w₁ • B₁ + w₂ • B₂) ((hB₁.smul hw₁).add (hB₂.smul hw₂))
    simp only [liebJointFunction] at key2
    exact key2
  -- Rewrite key inequality using the block identities
  rw [← hid₁, ← hid₂, ← hidcomb] at *
  exact key

/-! ### Extensions: homogeneity, weighted, and super-additive Lieb concavity -/

open scoped QuantumInfo

/-- Degree-1 homogeneity of rpow: (c ⋅ A)ˢ = cˢ ⋅ Aˢ for c ≥ 0, A PSD, s ≥ 0.
Proved via spectral decomposition + `rpow_unitary_conj` + `diagonal_rpow` + `Real.mul_rpow`. -/
lemma rpow_nonneg_smul {α : Type*} [Fintype α] [DecidableEq α]
    (c : ℝ) (hc : 0 ≤ c) (A : Matrix α α ℂ) (hA : A.PosSemidef)
    (s : ℝ) (hs : 0 ≤ s) :
    (c • A) ^ s = (c ^ s : ℝ) • A ^ s := by
  set U := hA.1.eigenvectorUnitary.1
  set ev := hA.1.eigenvalues
  have hev_nn : ∀ i, 0 ≤ ev i := hA.eigenvalues_nonneg
  have hU_mem : U ∈ Matrix.unitaryGroup α ℂ := hA.1.eigenvectorUnitary.2
  -- Spectral decomposition: A = U * diag(ev) * U†
  have hspec : A = U * diagonal (fun i => (ev i : ℂ)) * Uᴴ :=
    hA.1.spectral_theorem (𝕜 := ℂ)
  -- PSD of diagonal matrices
  have hD_le : (0 : Matrix α α ℂ) ≤ diagonal (fun i => (ev i : ℂ)) := by
    simp only [Matrix.le_iff, sub_zero]
    exact posSemidef_diagonal_iff.mpr (fun i => Complex.zero_le_real.mpr (mod_cast hev_nn i))
  have hcev_nn : ∀ i, 0 ≤ c * ev i := fun i => mul_nonneg hc (hev_nn i)
  have hcD_le : (0 : Matrix α α ℂ) ≤ diagonal (fun i => ((c * ev i : ℝ) : ℂ)) := by
    simp only [Matrix.le_iff, sub_zero]
    exact posSemidef_diagonal_iff.mpr (fun i => Complex.zero_le_real.mpr (mod_cast hcev_nn i))
  -- c • diag(ev) = diag(c * ev)
  have hsmul_diag : c • diagonal (fun i => (ev i : ℂ)) =
      diagonal (fun i => ((c * ev i : ℝ) : ℂ)) := by
    ext i j; simp only [Matrix.smul_apply, diagonal_apply, smul_ite, smul_zero]
    split_ifs <;> [simp [Complex.ofReal_mul]; rfl]
  -- c • A = U * diag(c * ev) * U†
  have hcA_spec : c • A = U * diagonal (fun i => ((c * ev i : ℝ) : ℂ)) * Uᴴ := by
    conv_lhs => rw [hspec]
    -- c • ((U * D) * Uᴴ) = (c • (U * D)) * Uᴴ = (U * (c • D)) * Uᴴ = (U * D') * Uᴴ
    rw [← smul_mul_assoc, ← mul_smul_comm, hsmul_diag]
  -- (c • A)^s = U * diag((c*ev)^s) * U†
  have hcA_nonneg : 0 ≤ c • A := by rw [Matrix.le_iff, sub_zero]; exact hA.smul hc
  have h_lhs : (c • A) ^ s =
      U * diagonal (fun i => (((c * ev i) ^ s : ℝ) : ℂ)) * Uᴴ := by
    conv_lhs => rw [hcA_spec]
    rw [rpow_unitary_conj hU_mem hs hcD_le (hM' := by simpa [Matrix.le_iff, hcA_spec] using hcA_nonneg),
        diagonal_rpow _ hcev_nn s hs]
  -- A^s = U * diag(ev^s) * U†
  have h_rhs : A ^ s =
      U * diagonal (fun i => ((ev i ^ s : ℝ) : ℂ)) * Uᴴ := by
    conv_lhs => rw [hspec]
    rw [rpow_unitary_conj hU_mem hs hD_le (hM' := by rw [← hspec]; rw [Matrix.le_iff, sub_zero]; exact hA),
        diagonal_rpow _ hev_nn s hs]
  -- (c * ev_i)^s = c^s * ev_i^s by Real.mul_rpow
  rw [h_lhs, h_rhs]
  -- Goal: (U * diag((c*ev)^s) * U†) = c^s • (U * diag(ev^s) * U†)
  -- Use (c * ev_i)^s = c^s * ev_i^s by Real.mul_rpow
  rw [← smul_mul_assoc, ← mul_smul_comm]
  -- Goal: (U * diag((c*ev)^s)) * U† = (U * (c^s • diag(ev^s))) * U†
  congr 1
  -- Goal: U * diag((c*ev)^s) = U * (c^s • diag(ev^s))
  congr 1
  -- Goal: diag((c*ev)^s) = c^s • diag(ev^s)
  ext i j
  simp only [diagonal, Matrix.of_apply, Matrix.smul_apply]
  by_cases hij : i = j
  · subst hij
    simp only [if_true, Complex.real_smul]
    rw [Real.mul_rpow hc (hev_nn i)]
    simp only [Complex.ofReal_mul]
  · simp only [hij, if_false, smul_zero]

/-- Degree-1 homogeneity of F_s: F_s(cA, cB) = c ⋅ F_s(A, B). -/
lemma Fs_homogeneous {α : Type*} [Fintype α] [DecidableEq α]
    (c : ℝ) (hc : 0 ≤ c)
    (A B : Matrix α α ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (Tr ((c • A) ^ s * (c • B) ^ (1 - s))).re =
    c * (Tr (A ^ s * B ^ (1 - s))).re := by
  have h1s : 0 ≤ 1 - s := by linarith
  rw [rpow_nonneg_smul c hc A hA s hs0,
      rpow_nonneg_smul c hc B hB (1 - s) h1s]
  -- (c^s • A^s) * (c^{1-s} • B^{1-s}) = c^s * c^{1-s} • (A^s * B^{1-s})
  rw [show (c ^ s : ℝ) • A ^ s * ((c ^ (1 - s) : ℝ) • B ^ (1 - s)) =
    ((c ^ s * c ^ (1 - s) : ℝ) : ℝ) • (A ^ s * B ^ (1 - s)) from by
    rw [smul_mul_smul_comm]]
  -- c^s * c^{1-s} = c^1 = c
  have : c ^ s * c ^ (1 - s) = c := by
    by_cases hc0 : c = 0
    · by_cases hs0' : s = 0
      · simp only [hs0', Real.rpow_zero, one_mul, sub_zero, Real.rpow_one]
      · simp only [hc0, Real.zero_rpow hs0', zero_mul]
    · have hc_pos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
      rw [← Real.rpow_add hc_pos, show s + (1 - s) = 1 by ring, Real.rpow_one]
  rw [this]
  -- Goal: (c • (A^s * B^{1-s})).trace.re = c * (A^s * B^{1-s}).trace.re
  simp only [Matrix.trace_smul, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- Weighted multi-term Lieb concavity (K = I, square matrices):
  ∑ᵢ wᵢ Tr (Aᵢˢ Bᵢ¹⁻ˢ) ≤ Tr ((∑ᵢ wᵢ Aᵢ)ˢ (∑ᵢ wᵢ Bᵢ)¹⁻ˢ)
for wᵢ ≥ 0 with ∑ᵢ wᵢ = 1, proved by induction using the 2-term
`lieb_joint_concavity_semidef`. -/
lemma lieb_concavity_weighted {r : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Fin r → Matrix α α ℂ) (hA : ∀ i, (A i).PosSemidef) (hB : ∀ i, (B i).PosSemidef)
    (w : Fin r → ℝ) (hw_nn : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∑ i : Fin r, w i * (Tr ((A i) ^ s * (B i) ^ (1 - s))).re ≤
    (Tr ((∑ i : Fin r, w i • A i) ^ s * (∑ i : Fin r, w i • B i) ^ (1 - s))).re := by
  induction r with
  | zero => simp at hw_sum
  | succ r ih =>
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    set w' := fun i : Fin r => w (Fin.castSucc i)
    set A' := fun i : Fin r => A (Fin.castSucc i)
    set B' := fun i : Fin r => B (Fin.castSucc i)
    set wr := w (Fin.last r)
    set Ar := A (Fin.last r)
    set Br := B (Fin.last r)
    set W := ∑ i : Fin r, w' i  -- = 1 - wr
    have hW_eq : W + wr = 1 := by
      have : ∑ i : Fin (r + 1), w i = 1 := hw_sum
      rw [Fin.sum_univ_castSucc] at this; exact this
    have hW_nn : 0 ≤ W := Finset.sum_nonneg fun i _ => hw_nn (Fin.castSucc i)
    have hwr_nn : 0 ≤ wr := hw_nn (Fin.last r)
    have hwr_le : wr ≤ 1 := by linarith
    -- PSD of weighted sums
    have hSA_psd : (∑ i : Fin r, w' i • A' i).PosSemidef :=
      posSemidef_sum Finset.univ fun i _ => (hA (Fin.castSucc i)).smul (hw_nn (Fin.castSucc i))
    have hSB_psd : (∑ i : Fin r, w' i • B' i).PosSemidef :=
      posSemidef_sum Finset.univ fun i _ => (hB (Fin.castSucc i)).smul (hw_nn (Fin.castSucc i))
    have hAr_psd : Ar.PosSemidef := hA (Fin.last r)
    have hBr_psd : Br.PosSemidef := hB (Fin.last r)
    -- Use the 2-term Lieb concavity (K = 1) with weights W and wr
    have h2term := lieb_joint_concavity_semidef
      (∑ i : Fin r, w' i • A' i) (wr • Ar)
      (∑ i : Fin r, w' i • B' i) (wr • Br)
      hSA_psd ((hA (Fin.last r)).smul hwr_nn)
      hSB_psd ((hB (Fin.last r)).smul hwr_nn)
      1 s hs0 hs1 W wr hW_nn hwr_nn hW_eq
    simp only [liebJointFunction, conjTranspose_one, Matrix.mul_one] at h2term
    -- Case split: W = 0 → trivial; W > 0 → IH with wᵢ/W then 2-term concavity
    clear h2term
    by_cases hW : W = 0
    · -- All w'ᵢ = 0, wr = 1
      have hw'_zero : ∀ i, w' i = 0 := by
        intro i
        have := Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hw_nn (Fin.castSucc j)) |>.mp hW
        exact this i (Finset.mem_univ _)
      have hwr_one : wr = 1 := by linarith
      have hA_zero : ∑ i : Fin r, w' i • A' i = 0 := by
        apply Finset.sum_eq_zero; intro i _; simp [hw'_zero i]
      have hB_zero : ∑ i : Fin r, w' i • B' i = 0 := by
        apply Finset.sum_eq_zero; intro i _; simp [hw'_zero i]
      have hF_zero : ∑ i : Fin r, w' i * ((A' i) ^ s * (B' i) ^ (1 - s)).trace.re = 0 := by
        apply Finset.sum_eq_zero; intro i _; simp [hw'_zero i]
      -- Unfold the set definitions so simp can match
      simp only [w', A', B', Ar, Br, wr] at hwr_one hA_zero hB_zero hF_zero ⊢
      simp only [hwr_one, one_mul, one_smul, hA_zero, hB_zero, hF_zero, zero_add, le_refl]
    · -- W > 0
      have hW_pos : 0 < W := lt_of_le_of_ne hW_nn (Ne.symm hW)
      -- Divide weights by W for IH
      have hw'_sum : ∑ i : Fin r, w' i / W = 1 := by
        rw [← Finset.sum_div, div_eq_one_iff_eq (ne_of_gt hW_pos)]
      have hw'_nn : ∀ i, 0 ≤ w' i / W := fun i => div_nonneg (hw_nn (Fin.castSucc i)) hW_nn
      -- IH with normalized weights
      have ih' := ih A' B' (fun i => hA (Fin.castSucc i)) (fun i => hB (Fin.castSucc i))
        (fun i => w' i / W) hw'_nn hw'_sum
      -- Factor out 1/W from weighted sums
      have hSA_div : ∑ i : Fin r, (w' i / W) • A' i = (1 / W) • ∑ i : Fin r, w' i • A' i := by
        rw [Finset.smul_sum]
        congr 1
        funext i
        rw [show (w' i / W) = (1 / W) * w' i from by ring]
        rw [smul_smul]
      have hSB_div : ∑ i : Fin r, (w' i / W) • B' i = (1 / W) • ∑ i : Fin r, w' i • B' i := by
        rw [Finset.smul_sum]
        congr 1
        funext i
        rw [show (w' i / W) = (1 / W) * w' i from by ring]
        rw [smul_smul]
      -- 2-term Lieb concavity with X = (1/W)•Σw'A, Y = (1/W)•Σw'B
      have hX_psd : ((1 / W) • ∑ i : Fin r, w' i • A' i).PosSemidef :=
        hSA_psd.smul (div_nonneg zero_le_one hW_nn)
      have hY_psd : ((1 / W) • ∑ i : Fin r, w' i • B' i).PosSemidef :=
        hSB_psd.smul (div_nonneg zero_le_one hW_nn)
      have h2 := lieb_joint_concavity_semidef
        ((1 / W) • ∑ i : Fin r, w' i • A' i) Ar
        ((1 / W) • ∑ i : Fin r, w' i • B' i) Br
        hX_psd hAr_psd hY_psd hBr_psd
        1 s hs0 hs1 W wr hW_nn hwr_nn hW_eq
      simp only [liebJointFunction, conjTranspose_one, Matrix.mul_one] at h2
      -- Simplify W • (1/W • X) = X
      have hWX_A : W • ((1 / W) • ∑ i : Fin r, w' i • A' i) = ∑ i : Fin r, w' i • A' i := by
        rw [smul_smul, mul_one_div_cancel (ne_of_gt hW_pos), one_smul]
      have hWX_B : W • ((1 / W) • ∑ i : Fin r, w' i • B' i) = ∑ i : Fin r, w' i • B' i := by
        rw [smul_smul, mul_one_div_cancel (ne_of_gt hW_pos), one_smul]
      rw [hWX_A, hWX_B] at h2
      -- Combine h2 (2-term concavity) with IH (normalized weights)
      have ih_simple : ∑ i : Fin r, (w' i / W) * ((A' i) ^ s * (B' i) ^ (1 - s)).trace.re ≤
          ((∑ i : Fin r, (w' i / W) • A' i) ^ s *
           (∑ i : Fin r, (w' i / W) • B' i) ^ (1 - s)).trace.re := by
        convert ih' using 2
      rw [hSA_div, hSB_div] at ih_simple
      -- Scale IH by W
      have ih_scaled : ∑ i : Fin r, w' i * ((A' i) ^ s * (B' i) ^ (1 - s)).trace.re ≤
          W * (((1 / W) • ∑ i : Fin r, w' i • A' i) ^ s *
               ((1 / W) • ∑ i : Fin r, w' i • B' i) ^ (1 - s)).trace.re := by
        have hmul := mul_le_mul_of_nonneg_left ih_simple hW_nn
        have hsum_eq : W * ∑ i : Fin r, (w' i / W) * ((A' i) ^ s * (B' i) ^ (1 - s)).trace.re =
            ∑ i : Fin r, w' i * ((A' i) ^ s * (B' i) ^ (1 - s)).trace.re := by
          rw [Finset.mul_sum]
          congr 1
          funext i
          field_simp
        rwa [hsum_eq] at hmul
      -- Combine ih_scaled and h2
      linarith [ih_scaled, h2]

/-- **Unweighted super-additivity** of F_s(A, B) = Tr (Aˢ B¹⁻ˢ):
  ∑ᵢ F_s(Aᵢ, Bᵢ) ≤ F_s(∑ᵢ Aᵢ, ∑ᵢ Bᵢ)
Proved from `lieb_concavity_weighted` (uniform weights 1/r) plus degree-1 homogeneity. -/
lemma lieb_concavity_sum {r : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Fin r → Matrix α α ℂ) (hA : ∀ i, (A i).PosSemidef) (hB : ∀ i, (B i).PosSemidef)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∑ i : Fin r, (Tr ((A i) ^ s * (B i) ^ (1 - s))).re ≤
    (Tr ((∑ i : Fin r, A i) ^ s * (∑ i : Fin r, B i) ^ (1 - s))).re := by
  rcases r with _ | r
  · -- Empty case: sums are empty, so 0 ≤ (0^s * 0^{1-s}).trace.re
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    -- For 0 ≤ s ≤ 1, the trace of 0^s * 0^{1-s} has nonneg real part
    -- since both 0^s and 0^{1-s} are PSD (continuous functional calculus)
    -- and trace(AB) has nonneg real part for PSD A, B.
    -- Simplest: if s > 0, 0^s = cfc f(0) where f(x) = x^s applied to 0 gives 0.
    -- Similarly for 1-s > 0. At least one of s, 1-s is positive (unless s = 0 or s = 1).
    -- In all cases, 0^s * 0^{1-s} ∈ PSD, and PSD have nonneg trace.re.
    have h_nonneg : 0 ≤ (0 : Matrix α α ℂ) := by rw [Matrix.le_iff, sub_zero]; exact PosSemidef.zero
    by_cases hs0' : s = 0
    · simp only [hs0', sub_zero]
      rw [CFC.rpow_zero (0 : Matrix α α ℂ) h_nonneg, CFC.rpow_one (0 : Matrix α α ℂ) h_nonneg]
      simp
    · -- s > 0, so 0^s = 0
      -- For s > 0, f(x) = x^s has f(0) = 0, so cfc f 0 = 0 • 1 = 0
      have hs_pos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs0')
      -- Need to show: 0 ≤ (0^s * 0^{1-s}).trace.re
      -- We compute 0^s = 0 for s > 0 via CFC
      have h0s : (0 : Matrix α α ℂ) ^ s = 0 := by
        rw [CFC.rpow_eq_cfc_real (a := (0 : Matrix α α ℂ)) (ha := h_nonneg), cfc_apply_zero]
        simp [Real.zero_rpow (ne_of_gt hs_pos)]
      simp only [h0s, Matrix.zero_mul, Matrix.trace_zero, Complex.zero_re, le_refl]
  set rr := (r + 1 : ℝ)
  have hr_pos : (0 : ℝ) < rr := by simp only [rr]; positivity
  -- Weighted concavity with w_i = 1/rr
  have hw_sum : ∑ i : Fin (r + 1), (1 / rr) = 1 := by
    simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, rr]
    field_simp; push_cast; ring
  have hw_nn : ∀ i : Fin (r + 1), (0 : ℝ) ≤ 1 / rr := fun _ => by positivity
  have hw := lieb_concavity_weighted A B hA hB (fun _ => 1 / rr) hw_nn hw_sum s hs0 hs1
  -- LHS: (1/rr) * Σ Fᵢ
  rw [← Finset.mul_sum] at hw
  -- RHS: F(Σ (1/rr) • A, Σ (1/rr) • B) = F((1/rr) • ΣA, (1/rr) • ΣB) = (1/rr) * F(ΣA, ΣB)
  have hSA : (∑ i, A i).PosSemidef := posSemidef_sum Finset.univ fun i _ => hA i
  have hSB : (∑ i, B i).PosSemidef := posSemidef_sum Finset.univ fun i _ => hB i
  rw [show ∑ i : Fin (r + 1), (1 / rr) • A i = (1 / rr) • ∑ i, A i from Finset.smul_sum.symm,
      show ∑ i : Fin (r + 1), (1 / rr) • B i = (1 / rr) • ∑ i, B i from Finset.smul_sum.symm]
    at hw
  rw [Fs_homogeneous (1 / rr) (by positivity) _ _ hSA hSB s hs0 hs1] at hw
  -- hw: (1/rr) * Σ Fᵢ ≤ (1/rr) * F(ΣA, ΣB)
  exact le_of_mul_le_mul_left hw (by positivity : (0 : ℝ) < 1 / rr)

end Matrix
