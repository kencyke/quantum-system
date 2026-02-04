module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation
public import QuantumSystem.Analysis.Matrix.HermitianFunctionalCalculus
public import QuantumSystem.Analysis.Matrix.PosDef
public import QuantumSystem.ForMathlib.Analysis.Matrix.Basic
public import QuantumSystem.ForMathlib.Analysis.Matrix.Order

/-!
# Effros's Matrix Convexity Approach

This file formalises the Effros (2008) machinery used to prove Lieb's joint concavity theorem
and related operator-convexity results.

## Main definitions

- `Matrix.IsLownerMonotone f`: A ≤ B ⇒ f(A) ≤ f(B) in the Löwner order.
- `Matrix.IsLownerConvex f`: f(tA + (1-t)B) ≤ t f(A) + (1-t)f(B) in the Löwner order.
- `Matrix.IsLownerConcave f`: −f is Löwner convex.
- `Matrix.IsJensenConvex f`: for Löwner convex f and A†A + B†B ≤ I,
  f(A† T₁ A + B† T₂ B) ≤ A† f(T₁) A + B† f(T₂) B.
- `Matrix.IsJensenConcave f`: −f is Jensen convex.

## Main results

- `Matrix.isJensenConvex_of_isLownerConvex`: Löwner convexity with f(0) ≤ 0 implies
  Jensen (HPJ) convexity. Follows the defect-matrix proof of Hansen-Pedersen 1981.
- `Matrix.rpow_isLownerConcave`: the power function tˢ (0 < s ≤ 1) is Löwner concave.
  Proved via the Stieltjes integral representation of xˢ and pointwise resolvent concavity.
- `Matrix.neg_rpow_isLownerConvex`: −tˢ is Löwner convex.
- `Matrix.neg_rpow_isJensenConvex`: −tˢ is Jensen convex.
- `Matrix.hpj_subhomogeneous`: HPJ inequality for A†A + B†B ≤ I.
- `Matrix.hpj_affine`: HPJ inequality for A†A + B†B = I.

## References

* Effros, *A Matrix Convexity Approach to Some Celebrated Quantum Inequalities* (2008)
* Hansen, Pedersen, *Jensen's operator inequality* (1981)
* Bhatia, *Matrix Analysis*, Theorem V.2.5 (1997)
-/
@[expose] public section

namespace Matrix

open Real NNReal MeasureTheory Set
open scoped MatrixOrder ComplexOrder

/-- A real function f is Löwner monotone on positive semidefinite matrices if
A ≤ B (in the Löwner order) implies f(A) ≤ f(B). -/
def IsLownerMonotone (f : ℝ → ℝ) : Prop :=
  ∀ (m : Type*) [Fintype m] [DecidableEq m]
    (A B : Matrix m m ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef),
    A ≤ B →
    let fA := matrixFunction (fun x => (f x : ℂ)) A hA.1
    let fB := matrixFunction (fun x => (f x : ℂ)) B hB.1
    fA ≤ fB

/-- A real function f is Löwner convex if
f(tA + (1-t)B) ≤ t · f(A) + (1-t) · f(B) in the Löwner order for all t ∈ [0,1]. -/
def IsLownerConvex (f : ℝ → ℝ) : Prop :=
  ∀ (m : Type*) [Fintype m] [DecidableEq m]
    (A B : Matrix m m ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) (t : ℝ),
    0 ≤ t → t ≤ 1 →
    ∀ (hC : (t • A + (1 - t) • B).IsHermitian),
    let fA := matrixFunction (fun x => (f x : ℂ)) A hA.1
    let fB := matrixFunction (fun x => (f x : ℂ)) B hB.1
    let fC := matrixFunction (fun x => (f x : ℂ)) (t • A + (1 - t) • B) hC
    fC ≤ t • fA + (1 - t) • fB

/-- A real function f is Löwner concave if −f is Löwner convex. -/
def IsLownerConcave (f : ℝ → ℝ) : Prop :=
  ∀ (m : Type*) [Fintype m] [DecidableEq m]
    (A B : Matrix m m ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) (t : ℝ),
    0 ≤ t → t ≤ 1 →
    ∀ (hC : (t • A + (1 - t) • B).IsHermitian),
    let fA := matrixFunction (fun x => Complex.ofReal (-f x)) A hA.1
    let fB := matrixFunction (fun x => Complex.ofReal (-f x)) B hB.1
    let fC := matrixFunction (fun x => Complex.ofReal (-f x)) (t • A + (1 - t) • B) hC
    fC ≤ t • fA + (1 - t) • fB

/-- Jensen convexity (HPJ sense): compression inequality for two terms.
For A†A + B†B ≤ I and PSD T₁, T₂:
f(A† T₁ A + B† T₂ B) ≤ A† f(T₁) A + B† f(T₂) B. -/
def IsJensenConvex (f : ℝ → ℝ) : Prop :=
  ∀ (m : Type*) [Fintype m] [DecidableEq m]
    (A B T₁ T₂ : Matrix m m ℂ)
    (hT₁ : T₁.PosSemidef) (hT₂ : T₂.PosSemidef)
    (_hAB : Aᴴ * A + Bᴴ * B ≤ (1 : Matrix m m ℂ))
    (hC : (Aᴴ * T₁ * A + Bᴴ * T₂ * B).IsHermitian),
    let fT₁ := matrixFunction (fun x => (f x : ℂ)) T₁ hT₁.1
    let fT₂ := matrixFunction (fun x => (f x : ℂ)) T₂ hT₂.1
    let fC := matrixFunction (fun x => (f x : ℂ)) (Aᴴ * T₁ * A + Bᴴ * T₂ * B) hC
    fC ≤ Aᴴ * fT₁ * A + Bᴴ * fT₂ * B

/-- Jensen concavity in the HPJ sense: −f is Jensen convex. -/
def IsJensenConcave (f : ℝ → ℝ) : Prop :=
  ∀ (m : Type*) [Fintype m] [DecidableEq m]
    (A B T₁ T₂ : Matrix m m ℂ)
    (hT₁ : T₁.PosSemidef) (hT₂ : T₂.PosSemidef)
    (_hAB : Aᴴ * A + Bᴴ * B ≤ (1 : Matrix m m ℂ))
    (hC : (Aᴴ * T₁ * A + Bᴴ * T₂ * B).IsHermitian),
    let fT₁ := matrixFunction (fun x => Complex.ofReal (-f x)) T₁ hT₁.1
    let fT₂ := matrixFunction (fun x => Complex.ofReal (-f x)) T₂ hT₂.1
    let fC := matrixFunction (fun x => Complex.ofReal (-f x)) (Aᴴ * T₁ * A + Bᴴ * T₂ * B) hC
    fC ≤ Aᴴ * fT₁ * A + Bᴴ * fT₂ * B

/-- Block diagonal matrix is positive semidefinite if blocks are positive semidefinite. -/
private lemma fromBlocks_posSemidef_diag {m n : Type*} [Fintype m] [Fintype n]
  {A : Matrix m m ℂ} {D : Matrix n n ℂ}
    (hA : A.PosSemidef) (hD : D.PosSemidef) :
    (Matrix.fromBlocks A 0 0 D).PosSemidef := by
  classical
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · -- Hermitian
    simpa using (Matrix.IsHermitian.fromBlocks (A := A) (B := (0 : Matrix m n ℂ))
      (C := (0 : Matrix n m ℂ)) (D := D) hA.1 (by simp) hD.1)
  · intro v
    -- Split the vector into left/right blocks.
    let v₁ : m → ℂ := fun i => v (Sum.inl i)
    let v₂ : n → ℂ := fun i => v (Sum.inr i)
    have hleft :
        (star v ⬝ᵥ (Matrix.fromBlocks A 0 0 D *ᵥ v)).re =
          (star v₁ ⬝ᵥ (A *ᵥ v₁)).re + (star v₂ ⬝ᵥ (D *ᵥ v₂)).re := by
      -- Compute dotProduct with block structure.
      classical
      simp [dotProduct, Fintype.sum_sum_type, fromBlocks_mulVec_inl, fromBlocks_mulVec_inr,
        v₁, v₂, Finset.sum_add_distrib, Complex.add_re]
    have hA_nonneg : 0 ≤ (star v₁ ⬝ᵥ (A *ᵥ v₁)).re := hA.re_dotProduct_nonneg v₁
    have hD_nonneg : 0 ≤ (star v₂ ⬝ᵥ (D *ᵥ v₂)).re := hD.re_dotProduct_nonneg v₂
    have hsum_nonneg :
        0 ≤ (star v₁ ⬝ᵥ (A *ᵥ v₁)).re + (star v₂ ⬝ᵥ (D *ᵥ v₂)).re :=
      add_nonneg hA_nonneg hD_nonneg
    have hreal : 0 ≤ (star v ⬝ᵥ (Matrix.fromBlocks A 0 0 D *ᵥ v)).re := by
      simpa [hleft] using hsum_nonneg
    have him : (star v ⬝ᵥ (Matrix.fromBlocks A 0 0 D *ᵥ v)).im = 0 := by
      apply IsHermitian.quadForm_im_eq_zero
      simpa using (Matrix.IsHermitian.fromBlocks (A := A) (B := (0 : Matrix m n ℂ))
        (C := (0 : Matrix n m ℂ)) (D := D) hA.1 (by simp) hD.1)
    exact (Complex.nonneg_iff).2 ⟨hreal, him.symm⟩

/-- Fundamental compression inequality for Löwner convex functions.
For Löwner convex f with f(0) ≤ 0, and V with V†V ≤ I (contraction),
the compression satisfies f(V†TV) ≤ V†f(T)V.

The proof uses the defect technique: let D = √(I - V†V), W = [V; D], T' = T ⊕ 0.
Then W is an isometry (W†W = I), and:
- W†T'W = V†TV (the compression)
- W†f(T')W = V†f(T)V + f(0)·D†D = V†f(T)V + f(0)·(I - V†V)

The matrix Jensen inequality gives f(W†T'W) ≤ W†f(T')W for Löwner convex f.
Since f(0) ≤ 0 and I - V†V ≥ 0, we have f(0)·(I - V†V) ≤ 0.
Thus f(V†TV) ≤ V†f(T)V + f(0)·(I - V†V) ≤ V†f(T)V. -/
lemma lownerConvex_compression_le.{v} {n : Type v} {m : Type v} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    {f : ℝ → ℝ} (hconv : IsLownerConvex.{v} f) (hf0 : f 0 ≤ 0)
    (V : Matrix n m ℂ) (hVV : Vᴴ * V ≤ 1)
    (T : Matrix n n ℂ) (hT : T.PosSemidef) :
    matrixFunction (fun x => (f x : ℂ)) (Vᴴ * T * V)
      (isHermitian_conjTranspose_mul_mul (B := V) (A := T) hT.1) ≤
    Vᴴ * matrixFunction (fun x => (f x : ℂ)) T hT.1 * V := by
  -- The proof uses the defect technique and the block diagonal CFC formula.
  classical
  -- Step 1: Setup the defect matrix D = √(I - V†V)
  have hΔ : ((1 : Matrix m m ℂ) - Vᴴ * V).PosSemidef := by
    simpa [Matrix.le_iff] using hVV
  let D := matrixSqrt ((1 : Matrix m m ℂ) - Vᴴ * V) hΔ
  have hD_herm : D.IsHermitian := matrixSqrt_isHermitian hΔ
  have hDD : D * D = (1 : Matrix m m ℂ) - Vᴴ * V := matrixSqrt_mul_self_posSemidef hΔ
  -- D†D = DD since D is Hermitian (D† = D)
  have hDhD : Dᴴ * D = (1 : Matrix m m ℂ) - Vᴴ * V := by
    rw [hD_herm.eq, hDD]
  -- V†V + D†D = I
  have hsum : Vᴴ * V + Dᴴ * D = (1 : Matrix m m ℂ) := by
    rw [hDhD]; simp
  -- Step 2: Create the extended block diagonal matrix T' = T ⊕ 0
  let T' := Matrix.fromBlocks T 0 0 (0 : Matrix m m ℂ)
  have hT'_psd : T'.PosSemidef := by
    have h0_psd : (0 : Matrix m m ℂ).PosSemidef := Matrix.PosSemidef.zero
    exact fromBlocks_posSemidef_diag hT h0_psd
  have hT'_herm : T'.IsHermitian := hT'_psd.1
  -- Step 3: Create the extended contraction W = [V; D] : (n ⊕ m) → m
  -- Here V : n → m and D : m → m, stacked vertically
  let W : Matrix (n ⊕ m) m ℂ := Matrix.fromRows V D
  -- W†W = V†V + D†D = I (isometry property)
  have hWW : Wᴴ * W = (1 : Matrix m m ℂ) := by
    simp only [W, fromRows_conjTranspose_mul_self, hsum]
  -- Step 4: Compute W†T'W = V†TV
  have hWTW : Wᴴ * T' * W = Vᴴ * T * V := by
    have h := fromRows_compress_blockDiag V D T (0 : Matrix m m ℂ)
    simp only [W, T'] at h ⊢
    rw [h]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]
  -- Step 5: Relate matrixFunction to CFC
  have hfT_eq : matrixFunction (fun x => (f x : ℂ)) T hT.1 = cfc f T :=
    matrixFunction_eq_cfc hT.1 f
  -- Step 6-7: W†f(T')W = V†f(T)V + f(0)·D†D
  have hWfTW : Wᴴ * cfc f T' * W =
      Vᴴ * cfc f T * V + (f 0 : ℂ) • (Dᴴ * D) := by
    have hT_sa : IsSelfAdjoint T := by
      simpa [IsSelfAdjoint, star_eq_conjTranspose] using hT.1
    have h0_sa : IsSelfAdjoint (0 : Matrix m m ℂ) := by
      simp [IsSelfAdjoint]
    have hfinite : (spectrum ℝ T ∪ spectrum ℝ (0 : Matrix m m ℂ)).Finite :=
      (Matrix.finite_real_spectrum (A := T)).union
        (Matrix.finite_real_spectrum (A := (0 : Matrix m m ℂ)))
    have hcont : ContinuousOn f (spectrum ℝ T ∪ spectrum ℝ (0 : Matrix m m ℂ)) :=
      Set.Finite.continuousOn hfinite f
    have hfT' : cfc f T' = Matrix.fromBlocks (cfc f T) 0 0 (cfc f (0 : Matrix m m ℂ)) :=
      cfc_fromBlocks_diag' T (0 : Matrix m m ℂ) hT_sa h0_sa f hcont
    have hf0_mat : cfc f (0 : Matrix m m ℂ) = (f 0 : ℂ) • (1 : Matrix m m ℂ) := by
      rw [cfc_apply_zero]
      simp only [Algebra.algebraMap_eq_smul_one]
      ext i j
      simp only [smul_apply, smul_eq_mul, one_apply, Complex.real_smul]
    have hfT'_expanded : cfc f T' = Matrix.fromBlocks (cfc f T) 0 0 ((f 0 : ℂ) • 1) := by
      rw [hfT', hf0_mat]
    rw [hfT'_expanded]
    have h := fromRows_compress_blockDiag V D (cfc f T) ((f 0 : ℂ) • (1 : Matrix m m ℂ))
    simp only [W] at h ⊢
    rw [h]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  -- Step 8: Apply the matrix Jensen inequality
  have hVTV_herm := isHermitian_conjTranspose_mul_mul (B := V) (A := T) hT.1
  have hDD_psd : (Dᴴ * D).PosSemidef := by
    rw [hDhD]; exact hΔ
  have hf0_term_le : (f 0 : ℂ) • (Dᴴ * D) ≤ (0 : Matrix m m ℂ) := by
    have h := Matrix.PosSemidef.smul_nonpos hf0 hDD_psd
    have heq : (f 0 : ℂ) • (Dᴴ * D) = (f 0 : ℝ) • (Dᴴ * D) := by
      ext i j; simp only [smul_apply, Complex.real_smul, smul_eq_mul]
    rw [heq]
    exact h
  have hWfTW' : Wᴴ * cfc f T' * W = Vᴴ * cfc f T * V + (f 0 : ℂ) • (Dᴴ * D) := hWfTW
  rw [hfT_eq]
  have hfVTV_eq : matrixFunction (fun x => (f x : ℂ)) (Vᴴ * T * V) hVTV_herm =
      cfc f (Vᴴ * T * V) := matrixFunction_eq_cfc hVTV_herm f
  rw [hfVTV_eq]
  have h_jensen : cfc f (Wᴴ * T' * W) ≤ Wᴴ * cfc f T' * W := by
    set P : Matrix (n ⊕ m) (n ⊕ m) ℂ := W * Wᴴ with hP_def
    have hP_sq : P * P = P := by
      change W * Wᴴ * (W * Wᴴ) = W * Wᴴ
      rw [Matrix.mul_assoc W Wᴴ (W * Wᴴ),
          show Wᴴ * (W * Wᴴ) = (Wᴴ * W) * Wᴴ from (Matrix.mul_assoc _ _ _).symm,
          hWW, Matrix.one_mul]
    have hP_herm : Pᴴ = P := by
      change (W * Wᴴ)ᴴ = W * Wᴴ
      rw [conjTranspose_mul, conjTranspose_conjTranspose]
    set S : Matrix (n ⊕ m) (n ⊕ m) ℂ := (2 : ℝ) • P - 1 with hS_def
    have h2P : (2 : ℝ) • P = P + P := two_smul ℝ P
    have hS_herm : Sᴴ = S := by
      rw [hS_def, h2P, conjTranspose_sub, conjTranspose_one, conjTranspose_add,
          hP_herm]
    have hS_sq : S * S = 1 := by
      rw [hS_def, h2P]
      have hPstep : P * (P + P - 1) = P := by
        rw [mul_sub, mul_add, hP_sq, mul_one, add_sub_cancel_right]
      rw [sub_mul, one_mul, add_mul, hPstep]
      abel
    have hS_star_eq : star S = S := by
      rw [star_eq_conjTranspose, hS_herm]
    have hS_mem_unitary : S ∈ unitary (Matrix (n ⊕ m) (n ⊕ m) ℂ) := by
      rw [Unitary.mem_iff]; exact ⟨by rw [hS_star_eq, hS_sq], by rw [hS_star_eq, hS_sq]⟩
    let S_unit : unitary (Matrix (n ⊕ m) (n ⊕ m) ℂ) := ⟨S, hS_mem_unitary⟩
    have hPW : P * W = W := by
      change W * Wᴴ * W = W
      rw [Matrix.mul_assoc, hWW, Matrix.mul_one]
    have hSP : S * P = P := by
      rw [hS_def, h2P, sub_mul, one_mul, add_mul, hP_sq, add_sub_cancel_right]
    have hPS : P * S = P := by
      rw [hS_def, h2P, mul_sub, mul_one, mul_add, hP_sq, add_sub_cancel_right]
    have hSW : S * W = W := by
      have h : (S * P) * W = P * W := by rw [hSP]
      rw [Matrix.mul_assoc] at h; rwa [hPW] at h
    have hWhS : Wᴴ * S = Wᴴ := by
      have h := congr_arg Matrix.conjTranspose hSW
      rwa [conjTranspose_mul, hS_herm] at h
    have hST'S_psd : (S * T' * S).PosSemidef := by
      have h := hT'_psd.conjTranspose_mul_mul_same S
      rwa [hS_herm] at h
    have hST'S_herm : (S * T' * S).IsHermitian := hST'S_psd.1
    have hM_herm : ((1/2 : ℝ) • T' + (1 - 1/2 : ℝ) • (S * T' * S)).IsHermitian :=
      IsHermitian.add_isHermitian (IsHermitian.smul_real hT'_herm (1/2))
        (IsHermitian.smul_real hST'S_herm (1 - 1/2))
    set M : Matrix (n ⊕ m) (n ⊕ m) ℂ := (1/2 : ℝ) • T' + (1/2 : ℝ) • (S * T' * S) with hM_def
    have hM_eq : M = (1/2 : ℝ) • T' + (1 - 1/2 : ℝ) • (S * T' * S) := by
      simp only [hM_def]; congr 1; congr 1; norm_num
    have hM_herm' : M.IsHermitian := by rw [hM_eq]; exact hM_herm
    have hconv_app := hconv (n ⊕ m) T' (S * T' * S) hT'_psd hST'S_psd (1/2)
      (by norm_num) (by norm_num) hM_herm
    have hfT'_eq : matrixFunction (fun x => (f x : ℂ)) T' hT'_herm = cfc f T' :=
      matrixFunction_eq_cfc hT'_herm f
    have hfST'S_eq : matrixFunction (fun x => (f x : ℂ)) (S * T' * S) hST'S_herm =
        cfc f (S * T' * S) := matrixFunction_eq_cfc hST'S_herm f
    rw [hfT'_eq, hfST'S_eq] at hconv_app
    have hfM_conv : matrixFunction (fun x => (f x : ℂ))
        ((1 / 2 : ℝ) • T' + (1 - 1 / 2 : ℝ) • (S * T' * S)) hM_herm = cfc f M :=
      (matrixFunction_congr _ hM_herm hM_herm' hM_eq.symm).trans
        (matrixFunction_eq_cfc hM_herm' f)
    rw [hfM_conv] at hconv_app
    have hT'_sa : IsSelfAdjoint T' := by
      rwa [IsSelfAdjoint, star_eq_conjTranspose]
    have hcfc_conj : S * cfc f T' * S = cfc f (S * T' * S) := by
      have h : S * cfc f T' * star S = cfc f (S * T' * star S) :=
        cfc_unitary_conjugation' S_unit T' hT'_sa f
          (Set.Finite.continuousOn (Matrix.finite_real_spectrum) f)
      rwa [star_eq_conjTranspose, hS_herm] at h
    have hM_comm : M * (W * Wᴴ) = (W * Wᴴ) * M := by
      rw [← hP_def]
      suffices h : M * P = P * M from h
      rw [hM_def]
      rw [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.smul_mul,
          Matrix.mul_smul, Matrix.mul_smul,
          show S * T' * S * P = S * T' * (S * P) from by
            simp only [Matrix.mul_assoc], hSP,
          show P * (S * T' * S) = (P * S) * T' * S from by
            simp only [Matrix.mul_assoc], hPS,
          ← smul_add, ← smul_add]
      congr 1
      have hST'P : S * T' * P = P * T' * P + P * T' * P - T' * P := by
        rw [hS_def, h2P, sub_mul, one_mul, add_mul, sub_mul, add_mul]
      have hPT'S : P * T' * S = P * T' * P + P * T' * P - P * T' := by
        rw [hS_def, h2P, mul_sub, mul_one, mul_add]
      rw [hST'P, hPT'S]; abel
    have hWMW : Wᴴ * M * W = Wᴴ * T' * W := by
      rw [hM_def,
          Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
          Matrix.mul_smul, Matrix.smul_mul,
          show Wᴴ * (S * T' * S) * W = (Wᴴ * S) * T' * (S * W) from by
            simp only [Matrix.mul_assoc],
          hWhS, hSW, ← smul_add, ← two_smul ℝ (Wᴴ * T' * W), smul_smul,
          show (1 / 2 : ℝ) * 2 = 1 from by norm_num, one_smul]
    have hWMW_herm : (Wᴴ * M * W).IsHermitian :=
      isHermitian_conjTranspose_mul_mul (B := W) (A := M) hM_herm'
    have h_comp := matrixFunction_compression_of_commuting W M hM_herm' hWW hM_comm f hWMW_herm
    rw [matrixFunction_eq_cfc hM_herm' f, matrixFunction_eq_cfc hWMW_herm f, hWMW] at h_comp
    have h_compress := compression_le hconv_app W
    rw [h_comp] at h_compress
    have h_half : (1 - 1 / 2 : ℝ) = (1 / 2 : ℝ) := by norm_num
    calc cfc f (Wᴴ * T' * W)
        ≤ Wᴴ * ((1 / 2 : ℝ) • cfc f T' + (1 - 1 / 2 : ℝ) • cfc f (S * T' * S)) * W :=
          h_compress
      _ = Wᴴ * cfc f T' * W := by
          rw [h_half, ← hcfc_conj,
              Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
              Matrix.mul_smul, Matrix.smul_mul,
              show Wᴴ * (S * cfc f T' * S) * W = (Wᴴ * S) * cfc f T' * (S * W) from by
                simp only [Matrix.mul_assoc],
              hWhS, hSW, ← smul_add,
              show Wᴴ * cfc f T' * W + Wᴴ * cfc f T' * W = (2 : ℝ) • (Wᴴ * cfc f T' * W) from
                (two_smul ℝ _).symm,
              smul_smul, show (1 / 2 : ℝ) * 2 = 1 from by norm_num,
              one_smul]
  rw [hWTW] at h_jensen
  rw [hWfTW'] at h_jensen
  calc cfc f (Vᴴ * T * V)
      ≤ Vᴴ * cfc f T * V + (f 0 : ℂ) • (Dᴴ * D) := h_jensen
    _ ≤ Vᴴ * cfc f T * V + 0 := add_le_add (le_refl _) hf0_term_le
    _ = Vᴴ * cfc f T * V := by simp

private lemma fromRows_defect_sqrt {m : Type*} [Fintype m] [DecidableEq m]
    (A B : Matrix m m ℂ) (hAB : Aᴴ * A + Bᴴ * B ≤ (1 : Matrix m m ℂ)) :
    let V := Matrix.fromRows A B
    let Δ := (1 : Matrix m m ℂ) - Vᴴ * V
    let D := matrixSqrt Δ (Matrix.PosSemidef.one_sub_fromRows (A := A) (B := B) hAB)
    Dᴴ * D = Δ := by
  intro V Δ D
  have hΔ : Δ.PosSemidef := by
    simpa [Δ, V] using Matrix.PosSemidef.one_sub_fromRows (A := A) (B := B) hAB
  calc
    Dᴴ * D = D * D := by
      have hherm : D.IsHermitian := by
        simpa [D, Δ, V] using matrixSqrt_isHermitian hΔ
      simp [hherm.eq]
    _ = Δ := by
      simpa [D] using matrixSqrt_mul_self_posSemidef hΔ

/-- The compression V†f(T)V for block diagonal T equals
    A†f(T₁)A + B†f(T₂)B when V = [A; B] and T = T₁ ⊕ T₂. -/
private lemma compression_of_fromBlocks_cfc {m : Type*} [Fintype m] [DecidableEq m]
    (A B : Matrix m m ℂ) (T₁ T₂ : Matrix m m ℂ)
    (hT₁ : T₁.PosSemidef) (hT₂ : T₂.PosSemidef) (f : ℝ → ℝ) :
    let V := Matrix.fromRows A B
    let T := Matrix.fromBlocks T₁ 0 0 T₂
    let hT_herm : T.IsHermitian := by
      simpa using Matrix.IsHermitian.fromBlocks hT₁.1 (by simp : (0 : Matrix m m ℂ).IsHermitian) hT₂.1
    Vᴴ * matrixFunction (fun x => (f x : ℂ)) T hT_herm * V =
    Aᴴ * matrixFunction (fun x => (f x : ℂ)) T₁ hT₁.1 * A +
    Bᴴ * matrixFunction (fun x => (f x : ℂ)) T₂ hT₂.1 * B := by
  classical
  intro V T hT_herm
  -- Use the CFC block diagonal formula.
  have hT_cfc :
      matrixFunction (fun x => (f x : ℂ)) T hT_herm =
        Matrix.fromBlocks
          (matrixFunction (fun x => (f x : ℂ)) T₁ hT₁.1) 0 0
          (matrixFunction (fun x => (f x : ℂ)) T₂ hT₂.1) := by
    have hT_cfc' : matrixFunction (fun x => (f x : ℂ)) T hT_herm = cfc f T :=
      matrixFunction_eq_cfc hT_herm f
    have hT₁_cfc : matrixFunction (fun x => (f x : ℂ)) T₁ hT₁.1 = cfc f T₁ :=
      matrixFunction_eq_cfc hT₁.1 f
    have hT₂_cfc : matrixFunction (fun x => (f x : ℂ)) T₂ hT₂.1 = cfc f T₂ :=
      matrixFunction_eq_cfc hT₂.1 f
    have hT_sa : IsSelfAdjoint T := by
      simpa [IsSelfAdjoint, Matrix.IsHermitian, star_eq_conjTranspose] using hT_herm
    have hT₁_sa : IsSelfAdjoint T₁ := by
      simpa [IsSelfAdjoint, Matrix.IsHermitian, star_eq_conjTranspose] using hT₁.1
    have hT₂_sa : IsSelfAdjoint T₂ := by
      simpa [IsSelfAdjoint, Matrix.IsHermitian, star_eq_conjTranspose] using hT₂.1
    have hfinite : (spectrum ℝ T₁ ∪ spectrum ℝ T₂).Finite :=
      (Matrix.finite_real_spectrum (A := T₁)).union (Matrix.finite_real_spectrum (A := T₂))
    have hcont : ContinuousOn f (spectrum ℝ T₁ ∪ spectrum ℝ T₂) :=
      Set.Finite.continuousOn hfinite f
    have hblock := cfc_fromBlocks_diag (m := m) (A := T₁) (D := T₂) hT₁_sa hT₂_sa f hcont
    calc
      matrixFunction (fun x => (f x : ℂ)) T hT_herm = cfc f T := hT_cfc'
      _ = Matrix.fromBlocks (cfc f T₁) 0 0 (cfc f T₂) := by simpa [T] using hblock
      _ = Matrix.fromBlocks
            (matrixFunction (fun x => (f x : ℂ)) T₁ hT₁.1) 0 0
            (matrixFunction (fun x => (f x : ℂ)) T₂ hT₂.1) := by simp [hT₁_cfc, hT₂_cfc]
  rw [hT_cfc]
  simpa [V] using fromRows_compress_blockDiag
    (A := A) (B := B)
    (T₁ := matrixFunction (fun x => (f x : ℂ)) T₁ hT₁.1)
    (T₂ := matrixFunction (fun x => (f x : ℂ)) T₂ hT₂.1)

/-- IsLownerConvex + f(0) ≤ 0 implies HPJ inequality (Matrix Convexity).
Theorem 3.1 in Effros 2008, originally Hansen-Pedersen 1981 Theorem 2.1 (i)⟹(iii).

The proof reduces the 2-term subhomogeneous case to:
1. A single-term compression inequality: f(V†TV) ≤ V†f(T)V when V†V ≤ I
2. The block diagonal CFC identity: V†f(T₁⊕T₂)V = A†f(T₁)A + B†f(T₂)B

Step 1 uses the defect matrix D = √(I - V†V) and f(0) ≤ 0 to absorb the defect term.
Step 2 is compression_of_fromBlocks_cfc (already proved). -/
lemma isJensenConvex_of_isLownerConvex.{v}
    {f : ℝ → ℝ} (hconv : IsLownerConvex.{v} f) (hf0 : f 0 ≤ 0) :
    IsJensenConvex.{v} f := by
  classical
  intro m _ _ A B T₁ T₂ hT₁ hT₂ hAB hC
  -- Step 1: Set up block diagonal T = T₁ ⊕ T₂ and V = fromRows A B
  let V := Matrix.fromRows A B
  let T := Matrix.fromBlocks T₁ 0 0 T₂
  have hT_psd : T.PosSemidef := fromBlocks_posSemidef_diag hT₁ hT₂
  -- Step 2: V†TV = A†T₁A + B†T₂B (block multiplication)
  have hVTV : Vᴴ * T * V = Aᴴ * T₁ * A + Bᴴ * T₂ * B :=
    fromRows_compress_blockDiag A B T₁ T₂
  -- Step 3: V†f(T)V = A†f(T₁)A + B†f(T₂)B (block diagonal CFC)
  have hVfTV : Vᴴ * matrixFunction (fun x => (f x : ℂ)) T
      (by simpa using Matrix.IsHermitian.fromBlocks hT₁.1 (by simp : (0 : Matrix m m ℂ).IsHermitian) hT₂.1) * V =
      Aᴴ * matrixFunction (fun x => (f x : ℂ)) T₁ hT₁.1 * A +
      Bᴴ * matrixFunction (fun x => (f x : ℂ)) T₂ hT₂.1 * B :=
    compression_of_fromBlocks_cfc A B T₁ T₂ hT₁ hT₂ f
  have hΔ := Matrix.PosSemidef.one_sub_fromRows A B hAB
  let Δ := (1 : Matrix m m ℂ) - Vᴴ * V
  let D := matrixSqrt Δ hΔ
  have hDD : Dᴴ * D = Δ := fromRows_defect_sqrt A B hAB
  have hsum : Vᴴ * V + Dᴴ * D = (1 : Matrix m m ℂ) := by
    rw [hDD]; simp [Δ]
  have hf0_neg : f 0 • (Dᴴ * D) ≤ (0 : Matrix m m ℂ) := by
    have : (Dᴴ * D).PosSemidef := by
      rw [hDD]; exact hΔ
    exact Matrix.PosSemidef.smul_nonpos hf0 this
  have hfC := matrixFunction_congr (fun x => (f x : ℂ)) hC
    (isHermitian_conjTranspose_mul_mul (B := V) (A := T) hT_psd.1) hVTV.symm
  have hT_herm : T.IsHermitian := by
    simpa using Matrix.IsHermitian.fromBlocks hT₁.1
      (by simp : (0 : Matrix m m ℂ).IsHermitian) hT₂.1
  calc matrixFunction (fun x => (f x : ℂ)) (Aᴴ * T₁ * A + Bᴴ * T₂ * B) hC
      = matrixFunction (fun x => (f x : ℂ)) (Vᴴ * T * V)
          (isHermitian_conjTranspose_mul_mul (B := V) (A := T) hT_psd.1) := hfC
    _ ≤ Vᴴ * matrixFunction (fun x => (f x : ℂ)) T hT_herm * V := by
        have hVV : Vᴴ * V ≤ 1 := by simpa [V, fromRows_conjTranspose_mul_self] using hAB
        exact lownerConvex_compression_le hconv hf0 V hVV T hT_psd
    _ = Aᴴ * matrixFunction (fun x => (f x : ℂ)) T₁ hT₁.1 * A +
        Bᴴ * matrixFunction (fun x => (f x : ℂ)) T₂ hT₂.1 * B := hVfTV

/-- Matrix convexity of matrix inverse in the Löwner order. -/
private lemma inv_lowner_convex_le {m : Type*} [Fintype m] [DecidableEq m]
    {A B : Matrix m m ℂ} (hA : A.PosDef) (hB : B.PosDef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (t • A + (1 - t) • B)⁻¹ ≤ t • A⁻¹ + (1 - t) • B⁻¹ := by
  classical
  by_cases ht_zero : t = 0
  · subst ht_zero
    simp
  by_cases ht_one : t = 1
  · subst ht_one
    simp
  have ht_pos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht_zero)
  have h1t_pos : 0 < 1 - t := by
    have ht1' : t < 1 := lt_of_le_of_ne ht1 ht_one
    linarith
  set C : Matrix m m ℂ := t • A + (1 - t) • B
  have hC_pos : C.PosDef := hA.convex_comb hB ht_pos h1t_pos
  let _ := hC_pos.isUnit.invertible
  have hA_blk : (Matrix.fromBlocks A 1 1 A⁻¹).PosSemidef := fromBlocks_inv_posSemidef hA
  have hB_blk : (Matrix.fromBlocks B 1 1 B⁻¹).PosSemidef := fromBlocks_inv_posSemidef hB
  have hsum :
      (t • Matrix.fromBlocks A 1 1 A⁻¹ + (1 - t) • Matrix.fromBlocks B 1 1 B⁻¹).PosSemidef := by
    exact (Matrix.PosSemidef.add (Matrix.PosSemidef.smul hA_blk ht0)
      (Matrix.PosSemidef.smul hB_blk (by linarith)))
  have hblocks_eq :
      t • Matrix.fromBlocks A 1 1 A⁻¹ + (1 - t) • Matrix.fromBlocks B 1 1 B⁻¹ =
        Matrix.fromBlocks C 1 1 (t • A⁻¹ + (1 - t) • B⁻¹) := by
    ext i j
    cases i with
    | inl i =>
        cases j with
        | inl j =>
            by_cases h : i = j <;>
              simp [C, h, fromBlocks_apply₁₁, Matrix.add_apply, Matrix.smul_apply]
        | inr j =>
            by_cases h : i = j
            · have hsum : (t : ℂ) + (1 - t) = (1 : ℂ) := by ring
              simp [C, h, fromBlocks_apply₁₂, Matrix.add_apply, Matrix.smul_apply, hsum]
            · simp [C, h, fromBlocks_apply₁₂, Matrix.add_apply, Matrix.smul_apply]
    | inr i =>
        cases j with
        | inl j =>
            by_cases h : i = j
            · have hsum : (t : ℂ) + (1 - t) = (1 : ℂ) := by ring
              simp [C, h, fromBlocks_apply₂₁, Matrix.add_apply, Matrix.smul_apply, hsum]
            · simp [C, h, fromBlocks_apply₂₁, Matrix.add_apply, Matrix.smul_apply]
        | inr j =>
            by_cases h : i = j <;>
              simp [C, h, fromBlocks_apply₂₂, Matrix.add_apply, Matrix.smul_apply]
  have hsum' : (Matrix.fromBlocks C 1 1 (t • A⁻¹ + (1 - t) • B⁻¹)).PosSemidef := by
    simpa [hblocks_eq] using hsum
  have hsum'' :
      (Matrix.fromBlocks C 1 (1 : Matrix m m ℂ)ᴴ (t • A⁻¹ + (1 - t) • B⁻¹)).PosSemidef := by
    simpa using hsum'
  have hSchur :
      (t • A⁻¹ + (1 - t) • B⁻¹ - (1 : Matrix m m ℂ)ᴴ * C⁻¹ * (1 : Matrix m m ℂ)).PosSemidef :=
    (Matrix.PosDef.fromBlocks₁₁ (B := (1 : Matrix m m ℂ)) (D := t • A⁻¹ + (1 - t) • B⁻¹) hC_pos).1
      hsum''
  rw [Matrix.le_iff]
  simpa [C] using hSchur

/-- Matrix concavity of `X ↦ 1 - r * (X + rI)⁻¹` for `r > 0`. -/
private lemma resolvent_lowner_concave_le {m : Type*} [Fintype m] [DecidableEq m]
    {A B : Matrix m m ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {r : ℝ} (hr : 0 < r) :
    t • (1 - r • (A + r • (1 : Matrix m m ℂ))⁻¹) +
      (1 - t) • (1 - r • (B + r • (1 : Matrix m m ℂ))⁻¹)
        ≤ 1 - r • ((t • A + (1 - t) • B) + r • (1 : Matrix m m ℂ))⁻¹ := by
  classical
  set A' : Matrix m m ℂ := A + r • (1 : Matrix m m ℂ)
  set B' : Matrix m m ℂ := B + r • (1 : Matrix m m ℂ)
  set C : Matrix m m ℂ := t • A + (1 - t) • B
  set C' : Matrix m m ℂ := C + r • (1 : Matrix m m ℂ)
  have hA' : A'.PosDef := PosSemidef.add_smul_one_posDef hA hr
  have hB' : B'.PosDef := PosSemidef.add_smul_one_posDef hB hr
  have hconv : C'⁻¹ ≤ t • A'⁻¹ + (1 - t) • B'⁻¹ := by
    have hA'' : A'.PosDef := hA'
    have hB'' : B'.PosDef := hB'
    have hC' : C' = t • A' + (1 - t) • B' := by
      dsimp [A', B', C', C]
      module
    simpa [hC'] using inv_lowner_convex_le hA'' hB'' ht0 ht1
  have hconv_psd : (t • A'⁻¹ + (1 - t) • B'⁻¹ - C'⁻¹).PosSemidef := by
    simpa [Matrix.le_iff] using hconv
  have hconv_psd' : (r • (t • A'⁻¹ + (1 - t) • B'⁻¹ - C'⁻¹)).PosSemidef := by
    exact hconv_psd.smul (by linarith : 0 ≤ r)
  rw [Matrix.le_iff]
  -- Reduce to the PSD of the inverse convexity difference.
  have hcalc :
      (1 - r • C'⁻¹) - (t • (1 - r • A'⁻¹) + (1 - t) • (1 - r • B'⁻¹)) =
        r • (t • A'⁻¹ + (1 - t) • B'⁻¹ - C'⁻¹) := by
    module
  simpa [hcalc, A', B', C', C] using hconv_psd'

/-- Core operator concavity lemma for matrices.
Uses the integral representation of xˢ and resolvent operator concavity.

The key mathematical fact: For 0 < s ≤ 1, the function x ↦ x^s is operator
concave on positive semidefinite matrices. This means:
  (tA + (1-t)B)^s ≥ t·A^s + (1-t)·B^s
for any PSD matrices A, B and t ∈ [0,1].

**Proof Strategy**:
1. Use the integral representation of xˢ via `exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁`.
2. Identify the integrand with the resolvent form `1 - u * (x + u)⁻¹` using CFC.
3. Apply the resolvent operator concavity inequality pointwise in u.
4. Integrate and rewrite with `matrixFunction_rpow_eq` to conclude the inequality. -/
private lemma rpow_operator_concave_le {m : Type*} [Fintype m] [DecidableEq m] [Fintype (m × m)]
    {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    (A B : Matrix m m ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hC : (t • A + (1 - t) • B).IsHermitian) :
    t • matrixFunction (fun x => ((x ^ s : ℝ) : ℂ)) A hA.1 +
    (1 - t) • matrixFunction (fun x => ((x ^ s : ℝ) : ℂ)) B hB.1 ≤
    matrixFunction (fun x => ((x ^ s : ℝ) : ℂ)) (t • A + (1 - t) • B) hC := by
  classical
  by_cases hs_eq : s = 1
  · subst hs_eq
    simp [Real.rpow_one, matrixFunction_id]
  letI : NormedRing (Matrix m m ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra
  letI : CompleteSpace (Matrix m m ℂ) := by infer_instance
  letI : NonUnitalCStarAlgebra (Matrix m m ℂ) := by
    simpa [CStarMatrix] using
      (CStarMatrix.instNonUnitalCStarAlgebra (n := m) (A := ℂ))
  letI : NonUnitalContinuousFunctionalCalculus ℝ (Matrix m m ℂ) IsSelfAdjoint := by
    infer_instance
  have hs_lt : s < 1 := lt_of_le_of_ne hs1 hs_eq
  let q : ℝ≥0 := ⟨s, le_of_lt hs0⟩
  have hq : (q : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := ⟨hs0, hs_lt⟩
  obtain ⟨μ, hμ⟩ :=
    CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁
      (A := Matrix m m ℂ) hq
  set C : Matrix m m ℂ := t • A + (1 - t) • B
  have hA0 : (0 : Matrix m m ℂ) ≤ A := by
    simpa [Matrix.le_iff] using hA
  have hB0 : (0 : Matrix m m ℂ) ≤ B := by
    simpa [Matrix.le_iff] using hB
  have hCpsd : C.PosSemidef := (hA.smul ht0).add (hB.smul (by linarith))
  have hC0 : (0 : Matrix m m ℂ) ≤ C := by
    simpa [Matrix.le_iff, C] using hCpsd
  have hA_int : IntegrableOn (fun u => cfcₙ (rpowIntegrand₀₁ q u) A) (Ioi 0) μ :=
    (hμ A hA0).1
  have hB_int : IntegrableOn (fun u => cfcₙ (rpowIntegrand₀₁ q u) B) (Ioi 0) μ :=
    (hμ B hB0).1
  have hC_int : IntegrableOn (fun u => cfcₙ (rpowIntegrand₀₁ q u) C) (Ioi 0) μ :=
    (hμ C hC0).1
  have h_integrand_le :
      (fun u => t • cfcₙ (rpowIntegrand₀₁ q u) A +
        (1 - t) • cfcₙ (rpowIntegrand₀₁ q u) B) ≤ᵐ[μ.restrict (Ioi 0)]
        fun u => cfcₙ (rpowIntegrand₀₁ q u) C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu' : 0 < u := hu
    -- Express the integrand via the resolvent concavity lemma.
    have hcont_Ici : ContinuousOn (fun x => rpowIntegrand₀₁ (q : ℝ) u x) (Ici 0) := by
      have hcont_add : ContinuousOn (fun x => u + x) (Ici 0) := by
        fun_prop
      have hne : ∀ x ∈ Ici 0, u + x ≠ 0 := by
        intro x hx
        have hx' : 0 ≤ x := hx
        linarith
      have hcont_inv : ContinuousOn (fun x => (u + x)⁻¹) (Ici 0) :=
        ContinuousOn.inv₀ hcont_add hne
      have hcont_sub : ContinuousOn (fun x => u⁻¹ - (u + x)⁻¹) (Ici 0) := by
        simpa using (ContinuousOn.sub continuousOn_const hcont_inv)
      simpa [Real.rpowIntegrand₀₁] using (ContinuousOn.mul continuousOn_const hcont_sub)
    have hA_spec : quasispectrum ℝ A ⊆ Ici 0 := by
      intro x hx
      exact (StarOrderedRing.nonneg_iff_quasispectrum_nonneg (A := Matrix m m ℂ) A).1 hA0 x hx
    have hB_spec : quasispectrum ℝ B ⊆ Ici 0 := by
      intro x hx
      exact (StarOrderedRing.nonneg_iff_quasispectrum_nonneg (A := Matrix m m ℂ) B).1 hB0 x hx
    have hC_spec : quasispectrum ℝ C ⊆ Ici 0 := by
      intro x hx
      exact (StarOrderedRing.nonneg_iff_quasispectrum_nonneg (A := Matrix m m ℂ) C).1 hC0 x hx
    have hA_eq :
        cfcₙ (rpowIntegrand₀₁ q u) A =
          matrixFunction (fun x => ((rpowIntegrand₀₁ (q : ℝ) u x : ℝ) : ℂ)) A hA.1 := by
      calc
        cfcₙ (rpowIntegrand₀₁ q u) A =
            cfc (rpowIntegrand₀₁ (q : ℝ) u) A := by
              simpa [Real.rpowIntegrand₀₁_zero_right] using
                (cfcₙ_eq_cfc (a := A) (f := fun x => rpowIntegrand₀₁ (q : ℝ) u x)
                  (hf := hcont_Ici.mono hA_spec) (hf0 := Real.rpowIntegrand₀₁_zero_right))
        _ = _ := by
              symm
              exact matrixFunction_eq_cfc hA.1 (fun x => rpowIntegrand₀₁ (q : ℝ) u x)
    have hB_eq :
        cfcₙ (rpowIntegrand₀₁ q u) B =
          matrixFunction (fun x => ((rpowIntegrand₀₁ (q : ℝ) u x : ℝ) : ℂ)) B hB.1 := by
      calc
        cfcₙ (rpowIntegrand₀₁ q u) B =
            cfc (rpowIntegrand₀₁ (q : ℝ) u) B := by
              simpa [Real.rpowIntegrand₀₁_zero_right] using
                (cfcₙ_eq_cfc (a := B) (f := fun x => rpowIntegrand₀₁ (q : ℝ) u x)
                  (hf := hcont_Ici.mono hB_spec) (hf0 := Real.rpowIntegrand₀₁_zero_right))
        _ = _ := by
              symm
              exact matrixFunction_eq_cfc hB.1 (fun x => rpowIntegrand₀₁ (q : ℝ) u x)
    have hC_eq :
        cfcₙ (rpowIntegrand₀₁ q u) C =
          matrixFunction (fun x => ((rpowIntegrand₀₁ (q : ℝ) u x : ℝ) : ℂ)) C hCpsd.1 := by
      calc
        cfcₙ (rpowIntegrand₀₁ q u) C =
            cfc (rpowIntegrand₀₁ (q : ℝ) u) C := by
              simpa [Real.rpowIntegrand₀₁_zero_right] using
                (cfcₙ_eq_cfc (a := C) (f := fun x => rpowIntegrand₀₁ (q : ℝ) u x)
                  (hf := hcont_Ici.mono hC_spec) (hf0 := Real.rpowIntegrand₀₁_zero_right))
        _ = _ := by
              symm
              exact matrixFunction_eq_cfc hCpsd.1 (fun x => rpowIntegrand₀₁ (q : ℝ) u x)
    have hfun :
        (fun x : ℝ => rpowIntegrand₀₁ (q : ℝ) u x) =
          fun x => u ^ (s - 1) * (1 - u * (x + u)⁻¹) := by
      funext x
      have hu0 : u ≠ 0 := ne_of_gt hu'
      have hpow : u ^ s = u ^ (s - 1) * u := by
        have h := Real.rpow_add_one hu0 (s - 1)
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
      have hx : u + x = x + u := by ac_rfl
      calc
        rpowIntegrand₀₁ (q : ℝ) u x = u ^ s * (u⁻¹ - (u + x)⁻¹) := rfl
        _ = u ^ (s - 1) * (u * (u⁻¹ - (u + x)⁻¹)) := by
              simp [hpow, mul_assoc]
        _ = u ^ (s - 1) * (1 - u * (x + u)⁻¹) := by
              have hmul : u * (u⁻¹ - (u + x)⁻¹) = 1 - u * (x + u)⁻¹ := by
                calc
                  u * (u⁻¹ - (u + x)⁻¹) = u * u⁻¹ - u * (u + x)⁻¹ := by
                    simp [mul_sub]
                  _ = 1 - u * (x + u)⁻¹ := by
                    simp [hu0, hx]
              simp [hmul]
    have hA_res :
        matrixFunction (fun x => ((1 - u * (x + u)⁻¹ : ℝ) : ℂ)) A hA.1 =
          (1 : Matrix m m ℂ) - (u : ℂ) • (A + (u : ℂ) • 1)⁻¹ :=
      matrixFunction_resolvent (m := m) hA (r := u) hu'
    have hB_res :
        matrixFunction (fun x => ((1 - u * (x + u)⁻¹ : ℝ) : ℂ)) B hB.1 =
          (1 : Matrix m m ℂ) - (u : ℂ) • (B + (u : ℂ) • 1)⁻¹ :=
      matrixFunction_resolvent (m := m) hB (r := u) hu'
    have hC_res :
        matrixFunction (fun x => ((1 - u * (x + u)⁻¹ : ℝ) : ℂ)) C hCpsd.1 =
          (1 : Matrix m m ℂ) - (u : ℂ) • (C + (u : ℂ) • 1)⁻¹ :=
      matrixFunction_resolvent (m := m) hCpsd (r := u) hu'
    have hA_int' :
        matrixFunction (fun x => ((rpowIntegrand₀₁ (q : ℝ) u x : ℝ) : ℂ)) A hA.1 =
          ((u ^ (s - 1) : ℝ) : ℂ) •
            matrixFunction (fun x => ((1 - u * (x + u)⁻¹ : ℝ) : ℂ)) A hA.1 := by
      have hsmul :
          matrixFunction (fun x => (((u ^ (s - 1)) * (1 - u * (x + u)⁻¹) : ℝ) : ℂ)) A hA.1 =
            ((u ^ (s - 1) : ℝ) : ℂ) •
              matrixFunction (fun x => ((1 - u * (x + u)⁻¹ : ℝ) : ℂ)) A hA.1 := by
        simpa using
          (matrixFunction_smul hA.1 ((u ^ (s - 1) : ℝ) : ℂ)
            (fun x => ((1 - u * (x + u)⁻¹ : ℝ) : ℂ)))
      simpa [hfun] using hsmul
    have hB_int' :
        matrixFunction (fun x => ((rpowIntegrand₀₁ (q : ℝ) u x : ℝ) : ℂ)) B hB.1 =
          ((u ^ (s - 1) : ℝ) : ℂ) •
            matrixFunction (fun x => ((1 - u * (x + u)⁻¹ : ℝ) : ℂ)) B hB.1 := by
      have hsmul :
          matrixFunction (fun x => (((u ^ (s - 1)) * (1 - u * (x + u)⁻¹) : ℝ) : ℂ)) B hB.1 =
            ((u ^ (s - 1) : ℝ) : ℂ) •
              matrixFunction (fun x => ((1 - u * (x + u)⁻¹ : ℝ) : ℂ)) B hB.1 := by
        simpa
  using
          (matrixFunction_smul hB.1 ((u ^ (s - 1) : ℝ) : ℂ)
            (fun x => ((1 - u * (x + u)⁻¹ : ℝ) : ℂ)))
      simpa [hfun] using hsmul
    have hC_int' :
        matrixFunction (fun x => ((rpowIntegrand₀₁ (q : ℝ) u x : ℝ) : ℂ)) C hCpsd.1 =
          ((u ^ (s - 1) : ℝ) : ℂ) •
            matrixFunction (fun x => ((1 - u * (x + u)⁻¹ : ℝ) : ℂ)) C hCpsd.1 := by
      have hsmul :
          matrixFunction (fun x => (((u ^ (s - 1)) * (1 - u * (x + u)⁻¹) : ℝ) : ℂ)) C hCpsd.1 =
            ((u ^ (s - 1) : ℝ) : ℂ) •
              matrixFunction (fun x => ((1 - u * (x + u)⁻¹ : ℝ) : ℂ)) C hCpsd.1 := by
        simpa using
          (matrixFunction_smul hCpsd.1 ((u ^ (s - 1) : ℝ) : ℂ)
            (fun x => ((1 - u * (x + u)⁻¹ : ℝ) : ℂ)))
      simpa [hfun] using hsmul
    have hres_le :
        t • ((1 : Matrix m m ℂ) - (u : ℂ) • (A + (u : ℂ) • 1)⁻¹) +
          (1 - t) • ((1 : Matrix m m ℂ) - (u : ℂ) • (B + (u : ℂ) • 1)⁻¹)
            ≤ (1 : Matrix m m ℂ) - (u : ℂ) • (C + (u : ℂ) • 1)⁻¹ := by
      simpa [C] using
        (resolvent_lowner_concave_le (m := m) hA hB ht0 ht1 (r := u) hu')
    -- Scale the resolvent inequality by the positive factor u^(s-1).
    have hscale :
        ((u ^ (s - 1) : ℝ) : ℂ) •
          (t • ((1 : Matrix m m ℂ) - (u : ℂ) • (A + (u : ℂ) • 1)⁻¹) +
            (1 - t) • ((1 : Matrix m m ℂ) - (u : ℂ) • (B + (u : ℂ) • 1)⁻¹))
            ≤ ((u ^ (s - 1) : ℝ) : ℂ) •
              ((1 : Matrix m m ℂ) - (u : ℂ) • (C + (u : ℂ) • 1)⁻¹) := by
      have hnonneg : 0 ≤ u ^ (s - 1) := by
        exact Real.rpow_nonneg (le_of_lt hu') _
      rw [Matrix.le_iff] at hres_le ⊢
      have hpsd :
          (((u ^ (s - 1) : ℝ) : ℂ) •
              ((1 : Matrix m m ℂ) - (u : ℂ) • (C + (u : ℂ) • 1)⁻¹) -
            ((u ^ (s - 1) : ℝ) : ℂ) •
              (t • ((1 : Matrix m m ℂ) - (u : ℂ) • (A + (u : ℂ) • 1)⁻¹) +
                (1 - t) • ((1 : Matrix m m ℂ) - (u : ℂ) • (B + (u : ℂ) • 1)⁻¹))).PosSemidef := by
        simpa [smul_sub] using hres_le.smul hnonneg
      simpa [smul_sub] using hpsd
    -- Replace with the matrixFunction form.
    have hscale' :
        ((u ^ (s - 1) : ℝ) : ℂ) •
          (t • matrixFunction (fun x => ((1 - u * (x + u)⁻¹ : ℝ) : ℂ)) A hA.1 +
            (1 - t) • matrixFunction (fun x => ((1 - u * (x + u)⁻¹ : ℝ) : ℂ)) B hB.1)
            ≤ ((u ^ (s - 1) : ℝ) : ℂ) •
              matrixFunction (fun x => ((1 - u * (x + u)⁻¹ : ℝ) : ℂ)) C hCpsd.1 := by
      have hscale' := hscale
      rw [hA_res.symm, hB_res.symm, hC_res.symm] at hscale'
      exact hscale'
    simpa [hA_eq, hB_eq, hC_eq, hA_int', hB_int', hC_int', smul_add, smul_smul,
      mul_comm, mul_left_comm, mul_assoc] using hscale'
  have hle_integral :
      t • (∫ u in Ioi 0, cfcₙ (rpowIntegrand₀₁ q u) A ∂μ) +
        (1 - t) • (∫ u in Ioi 0, cfcₙ (rpowIntegrand₀₁ q u) B ∂μ)
        ≤ ∫ u in Ioi 0, cfcₙ (rpowIntegrand₀₁ q u) C ∂μ := by
    have hleft_int :
        Integrable (fun u =>
          t • cfcₙ (rpowIntegrand₀₁ q u) A +
            (1 - t) • cfcₙ (rpowIntegrand₀₁ q u) B) (μ.restrict (Ioi 0)) := by
      exact (hA_int.smul t).add (hB_int.smul (1 - t))
    have hright_int :
        Integrable (fun u => cfcₙ (rpowIntegrand₀₁ q u) C) (μ.restrict (Ioi 0)) :=
      hC_int
    have hmono := integral_mono_ae hleft_int hright_int h_integrand_le
    have hleft_eq :
        ∫ u in Ioi 0, t • cfcₙ (rpowIntegrand₀₁ q u) A +
          (1 - t) • cfcₙ (rpowIntegrand₀₁ q u) B ∂μ =
          t • (∫ u in Ioi 0, cfcₙ (rpowIntegrand₀₁ q u) A ∂μ) +
            (1 - t) • (∫ u in Ioi 0, cfcₙ (rpowIntegrand₀₁ q u) B ∂μ) := by
      calc
        ∫ u in Ioi 0, t • cfcₙ (rpowIntegrand₀₁ q u) A +
            (1 - t) • cfcₙ (rpowIntegrand₀₁ q u) B ∂μ =
          ∫ u in Ioi 0, t • cfcₙ (rpowIntegrand₀₁ q u) A ∂μ +
            ∫ u in Ioi 0, (1 - t) • cfcₙ (rpowIntegrand₀₁ q u) B ∂μ := by
            refine integral_add ?_ ?_
            · exact hA_int.smul t
            · exact hB_int.smul (1 - t)
        _ = t • (∫ u in Ioi 0, cfcₙ (rpowIntegrand₀₁ q u) A ∂μ) +
            (1 - t) • (∫ u in Ioi 0, cfcₙ (rpowIntegrand₀₁ q u) B ∂μ) := by
            simp [integral_smul]
    have hmono' :
        t • (∫ u in Ioi 0, cfcₙ (rpowIntegrand₀₁ q u) A ∂μ) +
          (1 - t) • (∫ u in Ioi 0, cfcₙ (rpowIntegrand₀₁ q u) B ∂μ) ≤
          ∫ u in Ioi 0, cfcₙ (rpowIntegrand₀₁ q u) C ∂μ := by
      simpa [hleft_eq] using hmono
    exact hmono'
  have hA_eq_int :
      A ^ s = ∫ u in Ioi 0, cfcₙ (rpowIntegrand₀₁ q u) A ∂μ := by
    have hq_pos : 0 < (q : ℝ) := by exact_mod_cast hs0
    simpa [CFC.nnrpow_eq_rpow (A := Matrix m m ℂ) (a := A) (x := q) hq_pos] using
      (hμ A hA0).2
  have hB_eq_int :
      B ^ s = ∫ u in Ioi 0, cfcₙ (rpowIntegrand₀₁ q u) B ∂μ := by
    have hq_pos : 0 < (q : ℝ) := by exact_mod_cast hs0
    simpa [CFC.nnrpow_eq_rpow (A := Matrix m m ℂ) (a := B) (x := q) hq_pos] using
      (hμ B hB0).2
  have hC_eq_int :
      C ^ s = ∫ u in Ioi 0, cfcₙ (rpowIntegrand₀₁ q u) C ∂μ := by
    have hq_pos : 0 < (q : ℝ) := by exact_mod_cast hs0
    simpa [CFC.nnrpow_eq_rpow (A := Matrix m m ℂ) (a := C) (x := q) hq_pos] using
      (hμ C hC0).2
  have hC_eq_mf :
      matrixFunction (fun x => ((x ^ s : ℝ) : ℂ)) C hC = C ^ s := by
    have hC' :
        matrixFunction (fun x => ((x ^ s : ℝ) : ℂ)) C hC =
          matrixFunction (fun x => ((x ^ s : ℝ) : ℂ)) C hCpsd.1 := by
      exact
        (matrixFunction_congr (A := C) (B := C)
          (f := fun x => ((x ^ s : ℝ) : ℂ)) (hA := hC) (hB := hCpsd.1) rfl)
    calc
      matrixFunction (fun x => ((x ^ s : ℝ) : ℂ)) C hC =
          matrixFunction (fun x => ((x ^ s : ℝ) : ℂ)) C hCpsd.1 := hC'
      _ = C ^ s := matrixFunction_rpow_eq hCpsd s
  have hA_eq_mf :
      matrixFunction (fun x => ((x ^ s : ℝ) : ℂ)) A hA.1 = A ^ s :=
    matrixFunction_rpow_eq hA s
  have hB_eq_mf :
      matrixFunction (fun x => ((x ^ s : ℝ) : ℂ)) B hB.1 = B ^ s :=
    matrixFunction_rpow_eq hB s
  -- Rewrite the integral inequality to the matrixFunction statement.
  have hfinal : t • A ^ s + (1 - t) • B ^ s ≤ C ^ s := by
    simpa [hA_eq_int, hB_eq_int, hC_eq_int] using hle_integral
  simpa [hA_eq_mf, hB_eq_mf, hC_eq_mf, C] using hfinal

/-- Helper: The difference in quadratic forms for operator concavity. -/
private lemma rpow_concavity_quadform_nonneg {m : Type*} [Fintype m] [DecidableEq m]
    {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    (A B : Matrix m m ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hC : (t • A + (1 - t) • B).IsHermitian) (v : m → ℂ) :
    0 ≤ (star v ⬝ᵥ (
      matrixFunction (fun x => Complex.ofReal (x ^ s)) (t • A + (1 - t) • B) hC -
      t • matrixFunction (fun x => Complex.ofReal (x ^ s)) A hA.1 -
      (1 - t) • matrixFunction (fun x => Complex.ofReal (x ^ s)) B hB.1) *ᵥ v).re := by
  have hle :
      t • matrixFunction (fun x => Complex.ofReal (x ^ s)) A hA.1 +
        (1 - t) • matrixFunction (fun x => Complex.ofReal (x ^ s)) B hB.1 ≤
        matrixFunction (fun x => Complex.ofReal (x ^ s)) (t • A + (1 - t) • B) hC :=
    rpow_operator_concave_le hs0 hs1 A B hA hB t ht0 ht1 hC
  have hpsd :
      (matrixFunction (fun x => Complex.ofReal (x ^ s)) (t • A + (1 - t) • B) hC -
        (t • matrixFunction (fun x => Complex.ofReal (x ^ s)) A hA.1 +
          (1 - t) • matrixFunction (fun x => Complex.ofReal (x ^ s)) B hB.1)).PosSemidef := by
    simpa [Matrix.le_iff] using hle
  have hpsd' :
      (matrixFunction (fun x => Complex.ofReal (x ^ s)) (t • A + (1 - t) • B) hC -
        t • matrixFunction (fun x => Complex.ofReal (x ^ s)) A hA.1 -
        (1 - t) • matrixFunction (fun x => Complex.ofReal (x ^ s)) B hB.1).PosSemidef := by
    have hcalc :
        (matrixFunction (fun x => Complex.ofReal (x ^ s)) (t • A + (1 - t) • B) hC -
          (t • matrixFunction (fun x => Complex.ofReal (x ^ s)) A hA.1 +
            (1 - t) • matrixFunction (fun x => Complex.ofReal (x ^ s)) B hB.1)) =
        (matrixFunction (fun x => Complex.ofReal (x ^ s)) (t • A + (1 - t) • B) hC -
          t • matrixFunction (fun x => Complex.ofReal (x ^ s)) A hA.1 -
          (1 - t) • matrixFunction (fun x => Complex.ofReal (x ^ s)) B hB.1) := by
      module
    simpa [hcalc] using hpsd
  have hnonneg := hpsd'.dotProduct_mulVec_nonneg v
  exact (Complex.nonneg_iff.mp hnonneg).1

/-- The power function t^s (0 < s ≤ 1) is Löwner concave.
This means: (λA + (1-λ)B)^s ≥ λ·A^s + (1-λ)·B^s in Löwner order.

This is a classical result (Bhatia, Theorem V.2.5) proven via the integral
representation of rpow combined with operator concavity of each integrand.
Here we use Mathlib's CFC (continuous functional calculus) infrastructure.

Reference: Bhatia, "Matrix Analysis", Theorem V.2.5 -/
lemma rpow_isLownerConcave {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    IsLownerConcave (fun t => t ^ s) := by
  unfold IsLownerConcave
  intro m _ _ A B hA hB t ht0 ht1 hC
  rw [Matrix.le_iff]
  -- Define the power function
  let f : ℝ → ℂ := fun x => Complex.ofReal (x ^ s)
  let neg_f : ℝ → ℂ := fun x => Complex.ofReal (-(x ^ s))
  -- Relate neg_f to -f
  have hfunc : neg_f = fun x => -f x := by
    funext x; exact Complex.ofReal_neg (x ^ s)
  -- The matrixFunction of neg_f equals -matrixFunction of f
  have hA_mf : matrixFunction neg_f A hA.1 = -matrixFunction f A hA.1 := by
    rw [hfunc]; exact matrixFunction_neg hA.1 f
  have hB_mf : matrixFunction neg_f B hB.1 = -matrixFunction f B hB.1 := by
    rw [hfunc]; exact matrixFunction_neg hB.1 f
  have hC_mf : matrixFunction neg_f (t • A + (1 - t) • B) hC =
      -matrixFunction f (t • A + (1 - t) • B) hC := by
    rw [hfunc]; exact matrixFunction_neg hC f
  -- The goal's function equals neg_f
  have hgoal_A : matrixFunction (fun x : ℝ => (((fun y => -(y ^ s)) x : ℝ) : ℂ)) A hA.1 =
      matrixFunction neg_f A hA.1 := rfl
  have hgoal_B : matrixFunction (fun x : ℝ => (((fun y => -(y ^ s)) x : ℝ) : ℂ)) B hB.1 =
      matrixFunction neg_f B hB.1 := rfl
  have hgoal_C : matrixFunction (fun x : ℝ => (((fun y => -(y ^ s)) x : ℝ) : ℂ))
      (t • A + (1 - t) • B) hC = matrixFunction neg_f (t • A + (1 - t) • B) hC := rfl
  simp only [hgoal_A, hgoal_B, hgoal_C, hA_mf, hB_mf, hC_mf]
  -- Simplify: t•(-A^s) + (1-t)•(-B^s) - (-C^s) = C^s - t•A^s - (1-t)•B^s
  have halg : t • -matrixFunction f A hA.1 + (1 - t) • -matrixFunction f B hB.1 -
      -matrixFunction f (t • A + (1 - t) • B) hC =
      matrixFunction f (t • A + (1 - t) • B) hC -
      t • matrixFunction f A hA.1 - (1 - t) • matrixFunction f B hB.1 := by module
  rw [halg]
  -- Show PosSemidef via Hermitian and quadratic form characterization
  -- Use PosSemidef.of_dotProduct_mulVec_nonneg which works with (n → R) instead of Finsupp
  apply PosSemidef.of_dotProduct_mulVec_nonneg
  -- First show Hermitian
  · have hC_herm : (matrixFunction f (t • A + (1 - t) • B) hC).IsHermitian := by
      simpa [f] using matrixFunction_isHermitian hC (fun x => x ^ s)
    have hA_herm : (t • matrixFunction f A hA.1).IsHermitian := by
      simpa [f] using IsHermitian.smul_real (matrixFunction_isHermitian hA.1 (fun x => x ^ s)) t
    have hB_herm : ((1 - t) • matrixFunction f B hB.1).IsHermitian := by
      simpa [f] using IsHermitian.smul_real (matrixFunction_isHermitian hB.1 (fun x => x ^ s)) (1 - t)
    exact IsHermitian.sub (IsHermitian.sub hC_herm hA_herm) hB_herm
  -- Then show the quadratic form is nonneg for all vectors
  · intro v
    -- The helper lemma gives us the real part is nonneg
    have h_re : 0 ≤ (star v ⬝ᵥ (matrixFunction f (t • A + (1 - t) • B) hC -
        t • matrixFunction f A hA.1 - (1 - t) • matrixFunction f B hB.1) *ᵥ v).re :=
      rpow_concavity_quadform_nonneg hs0 hs1 A B hA hB t ht0 ht1 hC v
    -- The result is real (imaginary part is 0), so nonneg iff real part is nonneg
    have hreal : (star v ⬝ᵥ (matrixFunction f (t • A + (1 - t) • B) hC -
        t • matrixFunction f A hA.1 - (1 - t) • matrixFunction f B hB.1) *ᵥ v).im = 0 := by
      apply IsHermitian.quadForm_im_eq_zero
      have hC_herm : (matrixFunction f (t • A + (1 - t) • B) hC).IsHermitian := by
        simpa [f] using matrixFunction_isHermitian hC (fun x => x ^ s)
      have hA_herm : (t • matrixFunction f A hA.1).IsHermitian := by
        simpa [f] using IsHermitian.smul_real (matrixFunction_isHermitian hA.1 (fun x => x ^ s)) t
      have hB_herm : ((1 - t) • matrixFunction f B hB.1).IsHermitian := by
        simpa [f] using IsHermitian.smul_real (matrixFunction_isHermitian hB.1 (fun x => x ^ s)) (1 - t)
      exact IsHermitian.sub (IsHermitian.sub hC_herm hA_herm) hB_herm
    rw [Complex.nonneg_iff]
    exact ⟨h_re, hreal.symm⟩

/-- The negated power function -t^s (0 < s ≤ 1) is Löwner convex.
This is the dual statement of rpow_isLownerConcave. -/
lemma neg_rpow_isLownerConvex {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    IsLownerConvex (fun t => -(t ^ s)) :=
  rpow_isLownerConcave hs0 hs1

/-- The function `f(t) = −t^s` is Jensen convex for `0 < s ≤ 1`.
This follows from Löwner concavity of t^s together with the equivalence
IsLownerConvex ↔ IsJensenConvex. -/
lemma neg_rpow_isJensenConvex.{v} {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    IsJensenConvex.{v} (fun t => -(t ^ s)) := by
  apply isJensenConvex_of_isLownerConvex.{v} (neg_rpow_isLownerConvex hs0 hs1)
  simp only [Real.zero_rpow (ne_of_gt hs0), neg_zero]
  exact le_refl 0

/-- HPJ subhomogeneous inequality: for `IsJensenConvex` f with f(0) ≤ 0 and
A†A + B†B ≤ I, we have f(A† T₁ A + B† T₂ B)
≤ A† f(T₁) A + B† f(T₂) B. -/
lemma hpj_subhomogeneous.{v} {f : ℝ → ℝ}
  (hconv : IsJensenConvex.{v} f) (hf0 : f 0 ≤ 0)
  {m : Type v} [Fintype m] [DecidableEq m]
    (A B T₁ T₂ : Matrix m m ℂ)
    (hT₁ : T₁.PosSemidef) (hT₂ : T₂.PosSemidef)
    (hAB : Aᴴ * A + Bᴴ * B ≤ (1 : Matrix m m ℂ))
    (hC : (Aᴴ * T₁ * A + Bᴴ * T₂ * B).IsHermitian) :
    let fT₁ := matrixFunction (fun x => (f x : ℂ)) T₁ hT₁.1
    let fT₂ := matrixFunction (fun x => (f x : ℂ)) T₂ hT₂.1
    let fC := matrixFunction (fun x => (f x : ℂ)) (Aᴴ * T₁ * A + Bᴴ * T₂ * B) hC
    fC ≤ Aᴴ * fT₁ * A + Bᴴ * fT₂ * B := by
  have _ := hf0
  exact hconv m A B T₁ T₂ hT₁ hT₂ hAB hC

/-- HPJ affine inequality: the case AᴴA + BᴴB = I. -/
lemma hpj_affine.{v} {f : ℝ → ℝ}
  (hconv : IsJensenConvex.{v} f)
  {m : Type v} [Fintype m] [DecidableEq m]
    (A B T₁ T₂ : Matrix m m ℂ)
    (hT₁ : T₁.PosSemidef) (hT₂ : T₂.PosSemidef)
    (hAB : Aᴴ * A + Bᴴ * B = (1 : Matrix m m ℂ))
    (hC : (Aᴴ * T₁ * A + Bᴴ * T₂ * B).IsHermitian) :
    let fT₁ := matrixFunction (fun x => (f x : ℂ)) T₁ hT₁.1
    let fT₂ := matrixFunction (fun x => (f x : ℂ)) T₂ hT₂.1
    let fC := matrixFunction (fun x => (f x : ℂ)) (Aᴴ * T₁ * A + Bᴴ * T₂ * B) hC
    fC ≤ Aᴴ * fT₁ * A + Bᴴ * fT₂ * B := by
  have hAB' : Aᴴ * A + Bᴴ * B ≤ (1 : Matrix m m ℂ) := by
    simp [hAB]
  exact hconv m A B T₁ T₂ hT₁ hT₂ hAB' hC

end Matrix
