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
open scoped MatrixOrder ComplexOrder NNReal

/-- A real function f is Löwner monotone on positive semidefinite matrices if
A ≤ B (in the Löwner order) implies f(A) ≤ f(B). -/
def IsLownerMonotone (f : ℝ → ℝ) : Prop :=
  ∀ (m : Type*) [Fintype m] [DecidableEq m]
    (A B : Matrix m m ℂ) (_hA : A.PosSemidef) (_hB : B.PosSemidef),
    A ≤ B →
    let fA := cfc f A
    let fB := cfc f B
    fA ≤ fB

/-- A real function f is Löwner convex if
f(tA + (1-t)B) ≤ t · f(A) + (1-t) · f(B) in the Löwner order for all t ∈ [0,1]. -/
def IsLownerConvex (f : ℝ → ℝ) : Prop :=
  ∀ (m : Type*) [Fintype m] [DecidableEq m]
    (A B : Matrix m m ℂ) (_hA : A.PosSemidef) (_hB : B.PosSemidef) (t : ℝ),
    0 ≤ t → t ≤ 1 →
    ∀ (_hC : (t • A + (1 - t) • B).IsHermitian),
    let fA := cfc f A
    let fB := cfc f B
    let fC := cfc f (t • A + (1 - t) • B)
    fC ≤ t • fA + (1 - t) • fB

/-- A real function f is Löwner concave if −f is Löwner convex. -/
def IsLownerConcave (f : ℝ → ℝ) : Prop :=
  ∀ (m : Type*) [Fintype m] [DecidableEq m]
    (A B : Matrix m m ℂ) (_hA : A.PosSemidef) (_hB : B.PosSemidef) (t : ℝ),
    0 ≤ t → t ≤ 1 →
    ∀ (_hC : (t • A + (1 - t) • B).IsHermitian),
    let fA := cfc (fun x => -f x) A
    let fB := cfc (fun x => -f x) B
    let fC := cfc (fun x => -f x) (t • A + (1 - t) • B)
    fC ≤ t • fA + (1 - t) • fB

/-- Jensen convexity (HPJ sense): compression inequality for two terms.
For A†A + B†B ≤ I and PSD T₁, T₂:
f(A† T₁ A + B† T₂ B) ≤ A† f(T₁) A + B† f(T₂) B. -/
def IsJensenConvex (f : ℝ → ℝ) : Prop :=
  ∀ (m : Type*) [Fintype m] [DecidableEq m]
    (A B T₁ T₂ : Matrix m m ℂ)
    (_hT₁ : T₁.PosSemidef) (_hT₂ : T₂.PosSemidef)
    (_hAB : Aᴴ * A + Bᴴ * B ≤ (1 : Matrix m m ℂ))
    (_hC : (Aᴴ * T₁ * A + Bᴴ * T₂ * B).IsHermitian),
    let fT₁ := cfc f T₁
    let fT₂ := cfc f T₂
    let fC := cfc f (Aᴴ * T₁ * A + Bᴴ * T₂ * B)
    fC ≤ Aᴴ * fT₁ * A + Bᴴ * fT₂ * B

/-- Jensen concavity in the HPJ sense: −f is Jensen convex. -/
def IsJensenConcave (f : ℝ → ℝ) : Prop :=
  ∀ (m : Type*) [Fintype m] [DecidableEq m]
    (A B T₁ T₂ : Matrix m m ℂ)
    (_hT₁ : T₁.PosSemidef) (_hT₂ : T₂.PosSemidef)
    (_hAB : Aᴴ * A + Bᴴ * B ≤ (1 : Matrix m m ℂ))
    (_hC : (Aᴴ * T₁ * A + Bᴴ * T₂ * B).IsHermitian),
    let fT₁ := cfc (fun x => -f x) T₁
    let fT₂ := cfc (fun x => -f x) T₂
    let fC := cfc (fun x => -f x) (Aᴴ * T₁ * A + Bᴴ * T₂ * B)
    fC ≤ Aᴴ * fT₁ * A + Bᴴ * fT₂ * B

/-- Block diagonal matrix is positive semidefinite if blocks are positive semidefinite. -/
private lemma fromBlocks_posSemidef_diag {m n : Type*} [Finite m] [Finite n]
  {A : Matrix m m ℂ} {D : Matrix n n ℂ}
    (hA : A.PosSemidef) (hD : D.PosSemidef) :
    (Matrix.fromBlocks A 0 0 D).PosSemidef := by
  letI := Fintype.ofFinite m
  letI := Fintype.ofFinite n
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
    cfc f (Vᴴ * T * V) ≤ Vᴴ * cfc f T * V := by
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
    rw [← hM_eq] at hconv_app
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
      rw [hM_def, Matrix.add_mul, Matrix.mul_add, smul_mul_assoc, smul_mul_assoc,
          mul_smul_comm, mul_smul_comm,
          show S * T' * S * P = S * T' * (S * P) from by
            simp only [Matrix.mul_assoc], hSP,
          show P * (S * T' * S) = (P * S) * T' * S from by
            simp only [Matrix.mul_assoc], hPS]
      have hST'P : S * T' * P = P * T' * P + P * T' * P - T' * P := by
        rw [hS_def, h2P, sub_mul, one_mul, add_mul, sub_mul, add_mul]
      have hPT'S : P * T' * S = P * T' * P + P * T' * P - P * T' := by
        rw [hS_def, h2P, mul_sub, mul_one, mul_add]
      rw [hST'P, hPT'S]
      module
    have hWMW : Wᴴ * M * W = Wᴴ * T' * W := by
      rw [hM_def, Matrix.mul_add, Matrix.add_mul,
          show Wᴴ * (1/2 : ℝ) • T' = (1/2 : ℝ) • (Wᴴ * T') from Matrix.mul_smul _ _ _,
          show Wᴴ * (1/2 : ℝ) • (S * T' * S) = (1/2 : ℝ) • (Wᴴ * (S * T' * S))
            from Matrix.mul_smul _ _ _,
          show (1/2 : ℝ) • (Wᴴ * T') * W = (1/2 : ℝ) • (Wᴴ * T' * W)
            from Matrix.smul_mul _ _ _,
          show (1/2 : ℝ) • (Wᴴ * (S * T' * S)) * W = (1/2 : ℝ) • (Wᴴ * (S * T' * S) * W)
            from Matrix.smul_mul _ _ _,
          show Wᴴ * (S * T' * S) * W = (Wᴴ * S) * T' * (S * W) from by
            simp only [Matrix.mul_assoc],
          hWhS, hSW]
      module
    have hWMW_herm : (Wᴴ * M * W).IsHermitian :=
      isHermitian_conjTranspose_mul_mul (B := W) (A := M) hM_herm'
    have h_comp := cfc_compression_of_commuting W M hM_herm' hWW hM_comm f hWMW_herm
    rw [hWMW] at h_comp
    have h_compress := compression_le hconv_app W
    rw [h_comp] at h_compress
    have h_half : (1 - 1 / 2 : ℝ) = (1 / 2 : ℝ) := by norm_num
    calc cfc f (Wᴴ * T' * W)
        ≤ Wᴴ * ((1 / 2 : ℝ) • cfc f T' + (1 - 1 / 2 : ℝ) • cfc f (S * T' * S)) * W :=
          h_compress
      _ = Wᴴ * cfc f T' * W := by
          rw [h_half, ← hcfc_conj, Matrix.mul_add, Matrix.add_mul,
              show Wᴴ * (1/2 : ℝ) • cfc f T' = (1/2 : ℝ) • (Wᴴ * cfc f T')
                from Matrix.mul_smul _ _ _,
              show Wᴴ * (1/2 : ℝ) • (S * cfc f T' * S) =
                  (1/2 : ℝ) • (Wᴴ * (S * cfc f T' * S))
                from Matrix.mul_smul _ _ _,
              show (1/2 : ℝ) • (Wᴴ * cfc f T') * W = (1/2 : ℝ) • (Wᴴ * cfc f T' * W)
                from Matrix.smul_mul _ _ _,
              show (1/2 : ℝ) • (Wᴴ * (S * cfc f T' * S)) * W =
                  (1/2 : ℝ) • (Wᴴ * (S * cfc f T' * S) * W)
                from Matrix.smul_mul _ _ _,
              show Wᴴ * (S * cfc f T' * S) * W = (Wᴴ * S) * cfc f T' * (S * W) from by
                simp only [Matrix.mul_assoc],
              hWhS, hSW]
          module
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
    Vᴴ * cfc f T * V = Aᴴ * cfc f T₁ * A + Bᴴ * cfc f T₂ * B := by
  classical
  intro V T
  -- Use the CFC block diagonal formula.
  have hT₁_sa : IsSelfAdjoint T₁ := by
    simpa [IsSelfAdjoint, Matrix.IsHermitian, star_eq_conjTranspose] using hT₁.1
  have hT₂_sa : IsSelfAdjoint T₂ := by
    simpa [IsSelfAdjoint, Matrix.IsHermitian, star_eq_conjTranspose] using hT₂.1
  have hfinite : (spectrum ℝ T₁ ∪ spectrum ℝ T₂).Finite :=
    (Matrix.finite_real_spectrum (A := T₁)).union (Matrix.finite_real_spectrum (A := T₂))
  have hcont : ContinuousOn f (spectrum ℝ T₁ ∪ spectrum ℝ T₂) :=
    Set.Finite.continuousOn hfinite f
  have hblock := cfc_fromBlocks_diag (m := m) (A := T₁) (D := T₂) hT₁_sa hT₂_sa f hcont
  have hT_cfc : cfc f T = Matrix.fromBlocks (cfc f T₁) 0 0 (cfc f T₂) := by
    simpa [T] using hblock
  rw [hT_cfc]
  simpa [V] using fromRows_compress_blockDiag
    (A := A) (B := B) (T₁ := cfc f T₁) (T₂ := cfc f T₂)

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
  have hVfTV : Vᴴ * cfc f T * V = Aᴴ * cfc f T₁ * A + Bᴴ * cfc f T₂ * B :=
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
  calc cfc f (Aᴴ * T₁ * A + Bᴴ * T₂ * B)
      = cfc f (Vᴴ * T * V) := by rw [hVTV]
    _ ≤ Vᴴ * cfc f T * V := by
        have hVV : Vᴴ * V ≤ 1 := by simpa [V, fromRows_conjTranspose_mul_self] using hAB
        exact lownerConvex_compression_le hconv hf0 V hVV T hT_psd
    _ = Aᴴ * cfc f T₁ * A + Bᴴ * cfc f T₂ * B := hVfTV

/-- Matrix convexity of matrix inverse in the Löwner order. -/
private lemma inv_lowner_convex_le {m : Type*} [Fintype m] [DecidableEq m]
    {A B : Matrix m m ℂ} (hA : A.PosDef) (hB : B.PosDef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (t • A + (1 - t) • B)⁻¹ ≤ t • A⁻¹ + (1 - t) • B⁻¹ := by
  classical
  by_cases ht_zero : t = 0
  · subst ht_zero
    have h1 : ((0 : ℝ) • A + ((1 : ℝ) - 0) • B : Matrix m m ℂ) = B := by module
    have h2 : ((0 : ℝ) • A⁻¹ + ((1 : ℝ) - 0) • B⁻¹ : Matrix m m ℂ) = B⁻¹ := by module
    exact le_of_eq ((congrArg (·⁻¹) h1).trans h2.symm)
  by_cases ht_one : t = 1
  · subst ht_one
    have h1 : ((1 : ℝ) • A + ((1 : ℝ) - 1) • B : Matrix m m ℂ) = A := by module
    have h2 : ((1 : ℝ) • A⁻¹ + ((1 : ℝ) - 1) • B⁻¹ : Matrix m m ℂ) = A⁻¹ := by module
    exact le_of_eq ((congrArg (·⁻¹) h1).trans h2.symm)
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
    have hA_smul :
        t • Matrix.fromBlocks A 1 1 A⁻¹ = ((t : ℂ)) • Matrix.fromBlocks A 1 1 A⁻¹ := by
      ext i j; simp [Matrix.smul_apply, Complex.real_smul]
    have hB_smul :
        (1 - t) • Matrix.fromBlocks B 1 1 B⁻¹ =
          ((1 - t : ℝ) : ℂ) • Matrix.fromBlocks B 1 1 B⁻¹ := by
      ext i j; simp [Matrix.smul_apply, Complex.real_smul]
    rw [hA_smul, hB_smul]
    refine (Matrix.PosSemidef.smul hA_blk ?_).add (Matrix.PosSemidef.smul hB_blk ?_)
    · exact_mod_cast ht0
    · exact_mod_cast (by linarith : (0 : ℝ) ≤ 1 - t)
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
    have hr_smul :
        r • (t • A'⁻¹ + (1 - t) • B'⁻¹ - C'⁻¹) =
          ((r : ℂ)) • (t • A'⁻¹ + (1 - t) • B'⁻¹ - C'⁻¹) := by
      ext i j; simp [Matrix.smul_apply, Complex.real_smul]
    rw [hr_smul]
    exact hconv_psd.smul (by exact_mod_cast (show (0 : ℝ) ≤ r by linarith))
  rw [Matrix.le_iff]
  -- Reduce to the PSD of the inverse convexity difference.
  have hcalc :
      (1 - r • C'⁻¹) - (t • (1 - r • A'⁻¹) + (1 - t) • (1 - r • B'⁻¹)) =
        r • (t • A'⁻¹ + (1 - t) • B'⁻¹ - C'⁻¹) := by
    module
  simpa [hcalc, A', B', C', C] using hconv_psd'

section RpowOperatorConcaveAux

-- Activate the linfty operator norm tower on `Matrix _ _ ℂ` for the proof of
-- `rpow_operator_concave_le` below.  These instances are defined as `local
-- instance` in Mathlib and need to be re-activated with `attribute [local
-- instance]` here so that `Integrable.smul`, `integral_smul`, `integral_mono_ae`
-- etc. can synthesise the required typeclass tower.
attribute [local instance] Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra Matrix.linftyOpIsBoundedSMul
  Matrix.linftyOpNormSMulClass Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNonUnitalNormedRing

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
4. Integrate and rewrite with `CFC.rpow_eq_cfc_real` to conclude the inequality. -/
private lemma rpow_operator_concave_le {m : Type*} [Fintype m] [DecidableEq m]
    {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    (A B : Matrix m m ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hC : (t • A + (1 - t) • B).IsHermitian) :
    t • A ^ s + (1 - t) • B ^ s ≤ (t • A + (1 - t) • B) ^ s := by
  classical
  by_cases hs_eq : s = 1
  · subst hs_eq
    have hA0 : (0 : Matrix m m ℂ) ≤ A := by simpa [Matrix.le_iff] using hA
    have hB0 : (0 : Matrix m m ℂ) ≤ B := by simpa [Matrix.le_iff] using hB
    have hC0 : (0 : Matrix m m ℂ) ≤ t • A + (1 - t) • B := by
      simpa [Matrix.le_iff] using (hA.real_smul ht0).add (hB.real_smul (by linarith))
    simp only [CFC.rpow_one (a := A) hA0, CFC.rpow_one (a := B) hB0,
      CFC.rpow_one (a := t • A + (1 - t) • B) hC0, le_refl]
  -- The `attribute [local instance]` directives at the top of this
  -- `RpowOperatorConcaveAux` section activate the linfty operator-norm tower
  -- on `Matrix _ _ ℂ`.  We additionally need to pin a few non-instance
  -- theorems and routes that Mathlib v4.30 does not pick up automatically.
  letI : NonUnitalCStarAlgebra (Matrix m m ℂ) := by
    simpa [CStarMatrix] using
      (CStarMatrix.instNonUnitalCStarAlgebra (n := m) (A := ℂ))
  letI nucfc : NonUnitalContinuousFunctionalCalculus ℝ (Matrix m m ℂ) IsSelfAdjoint := by
    letI : CStarAlgebra (Matrix m m ℂ) := by
      simpa [CStarMatrix] using (CStarMatrix.instCStarAlgebra (n := m) (A := ℂ))
    letI : ContinuousFunctionalCalculus ℂ (Matrix m m ℂ) IsStarNormal :=
      IsStarNormal.instContinuousFunctionalCalculus
    letI : ContinuousFunctionalCalculus ℝ (Matrix m m ℂ) IsSelfAdjoint :=
      IsSelfAdjoint.instContinuousFunctionalCalculus
    exact ContinuousFunctionalCalculus.toNonUnital
  letI scc : SMulCommClass ℝ (Matrix m m ℂ) (Matrix m m ℂ) :=
    Matrix.Semiring.smulCommClass
  letI ist : IsScalarTower ℝ (Matrix m m ℂ) (Matrix m m ℂ) := inferInstance
  letI sor : StarOrderedRing (Matrix m m ℂ) := Matrix.instStarOrderedRing
  letI nsc : NonnegSpectrumClass ℝ (Matrix m m ℂ) := Matrix.instNonnegSpectrumClass
  -- `integral_mono_ae` requires `ClosedIciTopology` on the target.  The Löwner
  -- order on `Matrix m m ℂ` makes `Set.Ici a` closed because `PosSemidef` is a
  -- closed condition: it is the intersection of `IsHermitian` (closed under
  -- `star`) and `∀ y, 0 ≤ star y ⬝ᵥ M.mulVec y` (each is a closed condition
  -- since the dot-product map is continuous).
  letI cit : ClosedIciTopology (Matrix m m ℂ) := by
    refine ⟨fun a => ?_⟩
    have hSet : Set.Ici a = {M : Matrix m m ℂ | (M - a).PosSemidef} := by
      ext M; exact Matrix.le_iff
    rw [hSet]
    have hcont : Continuous fun M : Matrix m m ℂ => M - a := by fun_prop
    suffices hPSD : IsClosed {M : Matrix m m ℂ | M.PosSemidef} from
      hPSD.preimage hcont
    have heq : {M : Matrix m m ℂ | M.PosSemidef} =
        {M | M.IsHermitian} ∩ ⋂ y : m → ℂ, {M | 0 ≤ star y ⬝ᵥ M.mulVec y} := by
      ext M
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
      exact Matrix.posSemidef_iff_dotProduct_mulVec
    rw [heq]
    refine IsClosed.inter ?_ ?_
    · -- {M | M.IsHermitian} = {M | M.conjTranspose = M}
      exact isClosed_eq (by fun_prop) continuous_id
    · refine isClosed_iInter (fun y => ?_)
      exact isClosed_le continuous_const (by fun_prop)
  have hs_lt : s < 1 := lt_of_le_of_ne hs1 hs_eq
  let q : ℝ≥0 := ⟨s, le_of_lt hs0⟩
  have hq : (q : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := ⟨hs0, hs_lt⟩
  obtain ⟨μ, hμ⟩ :=
    @CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁ (Matrix m m ℂ)
      inferInstance inferInstance inferInstance scc ist inferInstance sor
      nsc nucfc inferInstance q hq
  set C : Matrix m m ℂ := t • A + (1 - t) • B
  have hA0 : (0 : Matrix m m ℂ) ≤ A := by
    simpa [Matrix.le_iff] using hA
  have hB0 : (0 : Matrix m m ℂ) ≤ B := by
    simpa [Matrix.le_iff] using hB
  have hCpsd : C.PosSemidef := by
    have hA_smul : t • A = ((t : ℂ)) • A := by
      ext i j; simp [Matrix.smul_apply, Complex.real_smul]
    have hB_smul : (1 - t) • B = ((1 - t : ℝ) : ℂ) • B := by
      ext i j; simp [Matrix.smul_apply, Complex.real_smul]
    refine (Matrix.PosSemidef.add ?_ ?_)
    · rw [show t • A = ((t : ℂ)) • A from hA_smul]
      exact hA.smul (by exact_mod_cast ht0)
    · rw [show (1 - t) • B = ((1 - t : ℝ) : ℂ) • B from hB_smul]
      exact hB.smul (by exact_mod_cast (show (0 : ℝ) ≤ 1 - t by linarith))
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
    have hcont_res : ContinuousOn (fun x : ℝ => 1 - u * (x + u)⁻¹) (Ici 0) := by
      have hcont_add : ContinuousOn (fun x : ℝ => x + u) (Ici 0) := by fun_prop
      have hne : ∀ x ∈ Ici (0 : ℝ), x + u ≠ 0 := by
        intro x hx; have hx' : 0 ≤ x := hx; linarith
      exact continuousOn_const.sub
        (continuousOn_const.mul (ContinuousOn.inv₀ hcont_add hne))
    have hAspec' : spectrum ℝ A ⊆ Ici 0 := by
      rw [hA.1.spectrum_real_eq_range_eigenvalues]
      rintro _ ⟨i, rfl⟩; exact hA.eigenvalues_nonneg i
    have hBspec' : spectrum ℝ B ⊆ Ici 0 := by
      rw [hB.1.spectrum_real_eq_range_eigenvalues]
      rintro _ ⟨i, rfl⟩; exact hB.eigenvalues_nonneg i
    have hCspec' : spectrum ℝ C ⊆ Ici 0 := by
      rw [hCpsd.1.spectrum_real_eq_range_eigenvalues]
      rintro _ ⟨i, rfl⟩; exact hCpsd.eigenvalues_nonneg i
    have hA_eq :
        cfcₙ (rpowIntegrand₀₁ q u) A = cfc (rpowIntegrand₀₁ (q : ℝ) u) A := by
      simpa [Real.rpowIntegrand₀₁_zero_right] using
        (cfcₙ_eq_cfc (a := A) (f := fun x => rpowIntegrand₀₁ (q : ℝ) u x)
          (hf := hcont_Ici.mono hA_spec) (hf0 := Real.rpowIntegrand₀₁_zero_right))
    have hB_eq :
        cfcₙ (rpowIntegrand₀₁ q u) B = cfc (rpowIntegrand₀₁ (q : ℝ) u) B := by
      simpa [Real.rpowIntegrand₀₁_zero_right] using
        (cfcₙ_eq_cfc (a := B) (f := fun x => rpowIntegrand₀₁ (q : ℝ) u x)
          (hf := hcont_Ici.mono hB_spec) (hf0 := Real.rpowIntegrand₀₁_zero_right))
    have hC_eq :
        cfcₙ (rpowIntegrand₀₁ q u) C = cfc (rpowIntegrand₀₁ (q : ℝ) u) C := by
      simpa [Real.rpowIntegrand₀₁_zero_right] using
        (cfcₙ_eq_cfc (a := C) (f := fun x => rpowIntegrand₀₁ (q : ℝ) u x)
          (hf := hcont_Ici.mono hC_spec) (hf0 := Real.rpowIntegrand₀₁_zero_right))
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
        cfc (fun x => 1 - u * (x + u)⁻¹) A =
          (1 : Matrix m m ℂ) - (u : ℂ) • (A + (u : ℂ) • 1)⁻¹ :=
      cfc_resolvent (m := m) hA hu'
    have hB_res :
        cfc (fun x => 1 - u * (x + u)⁻¹) B =
          (1 : Matrix m m ℂ) - (u : ℂ) • (B + (u : ℂ) • 1)⁻¹ :=
      cfc_resolvent (m := m) hB hu'
    have hC_res :
        cfc (fun x => 1 - u * (x + u)⁻¹) C =
          (1 : Matrix m m ℂ) - (u : ℂ) • (C + (u : ℂ) • 1)⁻¹ :=
      cfc_resolvent (m := m) hCpsd hu'
    have hA_int' :
        cfc (fun x => rpowIntegrand₀₁ (q : ℝ) u x) A =
          (u ^ (s - 1) : ℝ) • cfc (fun x => 1 - u * (x + u)⁻¹) A := by
      rw [hfun, cfc_const_mul (R := ℝ) (u ^ (s - 1)) (fun x => 1 - u * (x + u)⁻¹) A
        (hcont_res.mono hAspec')]
    have hB_int' :
        cfc (fun x => rpowIntegrand₀₁ (q : ℝ) u x) B =
          (u ^ (s - 1) : ℝ) • cfc (fun x => 1 - u * (x + u)⁻¹) B := by
      rw [hfun, cfc_const_mul (R := ℝ) (u ^ (s - 1)) (fun x => 1 - u * (x + u)⁻¹) B
        (hcont_res.mono hBspec')]
    have hC_int' :
        cfc (fun x => rpowIntegrand₀₁ (q : ℝ) u x) C =
          (u ^ (s - 1) : ℝ) • cfc (fun x => 1 - u * (x + u)⁻¹) C := by
      rw [hfun, cfc_const_mul (R := ℝ) (u ^ (s - 1)) (fun x => 1 - u * (x + u)⁻¹) C
        (hcont_res.mono hCspec')]
    have hres_le :
        t • ((1 : Matrix m m ℂ) - (u : ℂ) • (A + (u : ℂ) • 1)⁻¹) +
          (1 - t) • ((1 : Matrix m m ℂ) - (u : ℂ) • (B + (u : ℂ) • 1)⁻¹)
            ≤ (1 : Matrix m m ℂ) - (u : ℂ) • (C + (u : ℂ) • 1)⁻¹ := by
      simpa [C] using
        (resolvent_lowner_concave_le (m := m) hA hB ht0 ht1 (r := u) hu')
    -- Scale the resolvent inequality by the positive factor u^(s-1).
    have hscale :
        (u ^ (s - 1) : ℝ) •
          (t • ((1 : Matrix m m ℂ) - (u : ℂ) • (A + (u : ℂ) • 1)⁻¹) +
            (1 - t) • ((1 : Matrix m m ℂ) - (u : ℂ) • (B + (u : ℂ) • 1)⁻¹))
            ≤ (u ^ (s - 1) : ℝ) •
              ((1 : Matrix m m ℂ) - (u : ℂ) • (C + (u : ℂ) • 1)⁻¹) := by
      have hnonneg : 0 ≤ u ^ (s - 1) := by positivity
      rw [Matrix.le_iff]
      have h := (Matrix.le_iff.mp hres_le).real_smul hnonneg
      convert h using 1
      exact (smul_sub _ _ _).symm
    -- Replace with the cfc resolvent form.
    have hscale' :
        (u ^ (s - 1) : ℝ) •
          (t • cfc (fun x => 1 - u * (x + u)⁻¹) A +
            (1 - t) • cfc (fun x => 1 - u * (x + u)⁻¹) B)
            ≤ (u ^ (s - 1) : ℝ) •
              cfc (fun x => 1 - u * (x + u)⁻¹) C := by
      have hscale' := hscale
      rw [hA_res.symm, hB_res.symm, hC_res.symm] at hscale'
      exact hscale'
    have hscale'' :
        t • (u ^ (s - 1) : ℝ) • cfc (fun x => 1 - u * (x + u)⁻¹) A +
        (1 - t) • (u ^ (s - 1) : ℝ) • cfc (fun x => 1 - u * (x + u)⁻¹) B ≤
        (u ^ (s - 1) : ℝ) • cfc (fun x => 1 - u * (x + u)⁻¹) C := by
      have e : (u ^ (s - 1) : ℝ) • (t • cfc (fun x => 1 - u * (x + u)⁻¹) A +
            (1 - t) • cfc (fun x => 1 - u * (x + u)⁻¹) B) =
          t • (u ^ (s - 1) : ℝ) • cfc (fun x => 1 - u * (x + u)⁻¹) A +
          (1 - t) • (u ^ (s - 1) : ℝ) • cfc (fun x => 1 - u * (x + u)⁻¹) B := by
        module
      rw [← e]; exact hscale'
    simpa [hA_eq, hB_eq, hC_eq, hA_int', hB_int', hC_int'] using hscale''
  have hle_integral :
      t • (∫ u in Ioi 0, cfcₙ (rpowIntegrand₀₁ q u) A ∂μ) +
        (1 - t) • (∫ u in Ioi 0, cfcₙ (rpowIntegrand₀₁ q u) B ∂μ)
        ≤ ∫ u in Ioi 0, cfcₙ (rpowIntegrand₀₁ q u) C ∂μ := by
    have hAi : Integrable (fun u => cfcₙ (rpowIntegrand₀₁ q u) A) (μ.restrict (Ioi 0)) :=
      hA_int.integrable
    have hBi : Integrable (fun u => cfcₙ (rpowIntegrand₀₁ q u) B) (μ.restrict (Ioi 0)) :=
      hB_int.integrable
    have hA_smul : Integrable (fun u => t • cfcₙ (rpowIntegrand₀₁ q u) A)
        (μ.restrict (Ioi 0)) := hAi.smul (𝕜 := ℝ) t
    have hB_smul : Integrable (fun u => (1 - t) • cfcₙ (rpowIntegrand₀₁ q u) B)
        (μ.restrict (Ioi 0)) := hBi.smul (𝕜 := ℝ) (1 - t)
    have hleft_int :
        Integrable (fun u =>
          t • cfcₙ (rpowIntegrand₀₁ q u) A +
            (1 - t) • cfcₙ (rpowIntegrand₀₁ q u) B) (μ.restrict (Ioi 0)) :=
      hA_smul.add hB_smul
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
            congr 1
            · exact hAi.integral_smul (R := ℝ) t
            · exact hBi.integral_smul (R := ℝ) (1 - t)
    have hmono' :
        t • (∫ u in Ioi 0, cfcₙ (rpowIntegrand₀₁ q u) A ∂μ) +
          (1 - t) • (∫ u in Ioi 0, cfcₙ (rpowIntegrand₀₁ q u) B ∂μ) ≤
          ∫ u in Ioi 0, cfcₙ (rpowIntegrand₀₁ q u) C ∂μ := by
      simpa [hleft_eq] using hmono
    exact hmono'
  have hq_pos : 0 < (q : ℝ) := by exact_mod_cast hs0
  have hqs : (q : ℝ) = s := rfl
  have hA_eq_int :
      A ^ s = ∫ u in Ioi 0, cfcₙ (rpowIntegrand₀₁ q u) A ∂μ := by
    have h1 : A ^ q = A ^ (q : ℝ) :=
      CFC.nnrpow_eq_rpow (A := Matrix m m ℂ) (a := A) (x := q) hq_pos
    have h2 : A ^ q = ∫ u in Ioi 0, cfcₙ (rpowIntegrand₀₁ q u) A ∂μ := (hμ A hA0).2
    rw [← hqs, ← h1]; exact h2
  have hB_eq_int :
      B ^ s = ∫ u in Ioi 0, cfcₙ (rpowIntegrand₀₁ q u) B ∂μ := by
    have h1 : B ^ q = B ^ (q : ℝ) :=
      CFC.nnrpow_eq_rpow (A := Matrix m m ℂ) (a := B) (x := q) hq_pos
    have h2 : B ^ q = ∫ u in Ioi 0, cfcₙ (rpowIntegrand₀₁ q u) B ∂μ := (hμ B hB0).2
    rw [← hqs, ← h1]; exact h2
  have hC_eq_int :
      C ^ s = ∫ u in Ioi 0, cfcₙ (rpowIntegrand₀₁ q u) C ∂μ := by
    have h1 : C ^ q = C ^ (q : ℝ) :=
      CFC.nnrpow_eq_rpow (A := Matrix m m ℂ) (a := C) (x := q) hq_pos
    have h2 : C ^ q = ∫ u in Ioi 0, cfcₙ (rpowIntegrand₀₁ q u) C ∂μ := (hμ C hC0).2
    rw [← hqs, ← h1]; exact h2
  -- Conclude from the integral inequality.
  have hfinal : t • A ^ s + (1 - t) • B ^ s ≤ C ^ s := by
    simpa [hA_eq_int, hB_eq_int, hC_eq_int] using hle_integral
  exact hfinal

end RpowOperatorConcaveAux

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
  have hA0 : (0 : Matrix m m ℂ) ≤ A := by simpa [Matrix.le_iff] using hA
  have hB0 : (0 : Matrix m m ℂ) ≤ B := by simpa [Matrix.le_iff] using hB
  have hC0 : (0 : Matrix m m ℂ) ≤ t • A + (1 - t) • B := by
    simpa [Matrix.le_iff] using (hA.real_smul ht0).add (hB.real_smul (by linarith))
  change cfc (fun x : ℝ => -(x ^ s)) (t • A + (1 - t) • B) ≤
      t • cfc (fun x : ℝ => -(x ^ s)) A + (1 - t) • cfc (fun x : ℝ => -(x ^ s)) B
  have eA : cfc (fun x : ℝ => -(x ^ s)) A = -(A ^ s) := by
    rw [cfc_neg, ← CFC.rpow_eq_cfc_real (a := A) (ha := hA0)]
  have eB : cfc (fun x : ℝ => -(x ^ s)) B = -(B ^ s) := by
    rw [cfc_neg, ← CFC.rpow_eq_cfc_real (a := B) (ha := hB0)]
  have eC : cfc (fun x : ℝ => -(x ^ s)) (t • A + (1 - t) • B) = -((t • A + (1 - t) • B) ^ s) := by
    rw [cfc_neg, ← CFC.rpow_eq_cfc_real (a := t • A + (1 - t) • B) (ha := hC0)]
  rw [eA, eB, eC]
  have key := rpow_operator_concave_le hs0 hs1 A B hA hB t ht0 ht1 hC
  rw [Matrix.le_iff] at key ⊢
  convert key using 1
  module

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
    let fT₁ := cfc f T₁
    let fT₂ := cfc f T₂
    let fC := cfc f (Aᴴ * T₁ * A + Bᴴ * T₂ * B)
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
    let fT₁ := cfc f T₁
    let fT₂ := cfc f T₂
    let fC := cfc f (Aᴴ * T₁ * A + Bᴴ * T₂ * B)
    fC ≤ Aᴴ * fT₁ * A + Bᴴ * fT₂ * B := by
  have hAB' : Aᴴ * A + Bᴴ * B ≤ (1 : Matrix m m ℂ) := by
    simp [hAB]
  exact hconv m A B T₁ T₂ hT₁ hT₂ hAB' hC

end Matrix
