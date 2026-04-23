module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.LinearAlgebra.Lagrange
public import QuantumSystem.ForMathlib.Analysis.Matrix.Basic
public import QuantumSystem.ForMathlib.Analysis.Matrix.Hermitian

/-!
# Matrix Functional Calculus and Foundational Inequalities

This file develops the core tools for matrix analysis. Foundational lemmas about Hermitian
matrices, positive semidefiniteness, block-matrix identities, and the Löwner order are in
`QuantumSystem.ForMathlib.Analysis.Matrix.*`.

## Main results

### Functional Calculus
- `matrixFunction f A hA`: spectral decomposition f(A) = U diag(f(λᵢ)) U*
  for Hermitian A with eigendecomposition A = UΛ U*.
- Algebraic properties: `matrixFunction_id`, `matrixFunction_neg`, `matrixFunction_add`,
  `matrixFunction_smul`, `matrixFunction_const`, `matrixFunction_add_const`, etc.
- Complex power instances: `matrixFunction_cpow_zero`, `matrixFunction_cpow_one`.
- Compatibility with Mathlib's CFC: `matrixFunction_eq_cfc`.
- Special functions: `matrixExp`, `matrixLog`, `matrixSqrt` (via `matrixFunction`).

### Hermitian and PSD Structure
- `matrixFunction_isHermitian`: f(A) is Hermitian when f maps ℝ to ℝ.
- `matrixFunction_posSemidef`: f(A) ≥ 0 when f(λᵢ) ≥ 0 on eigenvalues.
- `matrixFunction_inv_add_const`: (A + tI)⁻¹ from `matrixFunction`.
- `matrixFunction_rpow_eq`: `matrixFunction` agrees with `CFC.rpow` on PSD matrices.
- `matrixSqrt`: the matrix square root A¹⁄² for PSD A.
- `matrixInvSqrt_commute_of_commute`: R⁻¹⁄² commutes with L when L and R commute
  (for PSD L, PD R).

### Spectral Decomposition Identities
- `Matrix.UHU_eq_one`: Uᴴ * U = 1 for the eigenvector unitary.
- `Matrix.UUH_eq_one`: U * Uᴴ = 1 for the eigenvector unitary.
- `Matrix.spectral_expand`: A = U * diag(eigenvalues) * Uᴴ.
- `Matrix.mulVec_eigenvector_col`: column j of U is an eigenvector with eigenvalue j.
- `Matrix.fromBlocks_diag_rpow`: (A ⊕ D)ᵖ = Aᵖ ⊕ Dᵖ for PSD A, D with p > 0.

## References

* Bhatia, *Matrix Analysis* (1997)
-/

@[expose] public section

namespace Matrix

open scoped MatrixOrder ComplexOrder

/-- Functional calculus for Hermitian matrices via spectral decomposition.
Given f : ℝ → ℂ and a Hermitian matrix A = U Λ U*, we define f(A) = U f(Λ) U*
where f(Λ) applies f to each diagonal entry (eigenvalue). -/
noncomputable def matrixFunction {m : Type*} [Fintype m] [DecidableEq m]
    (f : ℝ → ℂ) (A : Matrix m m ℂ) (hA : A.IsHermitian) : Matrix m m ℂ :=
  let U : Matrix m m ℂ := hA.eigenvectorUnitary
  let Λ := diagonal (fun i => f (hA.eigenvalues i))
  U * Λ * Uᴴ

/-- Trace of f(A) equals sum of f(λ_i) by cyclicity of trace and unitarity of U. -/
lemma matrixFunction_trace {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℂ) (hA : A.IsHermitian) (f : ℝ → ℂ) :
    (matrixFunction f A hA).trace = ∑ i, f (hA.eigenvalues i) := by
  unfold matrixFunction
  rw [trace_mul_cycle]
  have h := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  simp only [star_eq_conjTranspose] at h
  rw [h, Matrix.one_mul]
  exact trace_diagonal _

/-- matrixFunction of a real-valued function produces a Hermitian matrix. -/
lemma matrixFunction_isHermitian {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (matrixFunction (fun x => (f x : ℂ)) A hA).IsHermitian := by
  unfold matrixFunction
  -- U * D * Uᴴ is Hermitian when D is Hermitian and U is unitary
  have hD : (diagonal (fun i => (f (hA.eigenvalues i) : ℂ))).IsHermitian := by
    rw [isHermitian_diagonal_iff]
    intro i
    exact Complex.conj_ofReal _
  -- (U D Uᴴ)ᴴ = U Dᴴ Uᴴ = U D Uᴴ since D is Hermitian
  rw [IsHermitian]
  simp only [conjTranspose_mul, conjTranspose_conjTranspose]
  conv_rhs => rw [mul_assoc]
  rw [hD]

/-- Spectral lemma: matrixFunction(id) = A. -/
lemma matrixFunction_id {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.IsHermitian) :
    matrixFunction (fun x => (x : ℂ)) A hA = A := by
  unfold matrixFunction
  simp only
  conv_rhs => rw [hA.spectral_theorem]
  unfold Unitary.conjStarAlgAut
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  rfl

/-- Negation distributes through matrixFunction. -/
lemma matrixFunction_neg {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.IsHermitian) (f : ℝ → ℂ) :
    matrixFunction (fun x => -f x) A hA = -matrixFunction f A hA := by
  unfold matrixFunction
  simp only
  have hdiag : diagonal (fun i => -f (hA.eigenvalues i)) =
               -diagonal (fun i => f (hA.eigenvalues i)) := by
    ext i j
    simp only [diagonal_apply, neg_apply]
    split_ifs <;> ring
  rw [hdiag, mul_neg, neg_mul]

/-- matrixFunction distributes over addition. -/
lemma matrixFunction_add {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.IsHermitian) (f g : ℝ → ℂ) :
    matrixFunction (fun x => f x + g x) A hA =
      matrixFunction f A hA + matrixFunction g A hA := by
  unfold matrixFunction
  simp only
  have hdiag :
      diagonal (fun i => f (hA.eigenvalues i) + g (hA.eigenvalues i)) =
        diagonal (fun i => f (hA.eigenvalues i)) +
        diagonal (fun i => g (hA.eigenvalues i)) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp
    · simp [h]
  rw [hdiag]
  rw [Matrix.mul_add, Matrix.add_mul]

/-- matrixFunction commutes with scalar multiplication. -/
lemma matrixFunction_smul {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.IsHermitian) (c : ℂ) (f : ℝ → ℂ) :
    matrixFunction (fun x => c * f x) A hA = c • matrixFunction f A hA := by
  unfold matrixFunction
  simp only
  have hdiag :
      diagonal (fun i => c * f (hA.eigenvalues i)) =
        c • diagonal (fun i => f (hA.eigenvalues i)) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp
    · simp [h]
  rw [hdiag]
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-- matrixFunction of a constant function is a scalar multiple of the identity. -/
lemma matrixFunction_const {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.IsHermitian) (c : ℂ) :
    matrixFunction (fun _ => c) A hA = c • (1 : Matrix m m ℂ) := by
  classical
  unfold matrixFunction
  simp only
  have hdiag : diagonal (fun _ => c) = c • (1 : Matrix m m ℂ) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp
    · simp [h]
  rw [hdiag]
  have hU : (hA.eigenvectorUnitary : Matrix m m ℂ) *
      (hA.eigenvectorUnitary : Matrix m m ℂ)ᴴ = 1 := by
    simpa [star_eq_conjTranspose] using Unitary.coe_mul_star_self hA.eigenvectorUnitary
  simp [hU]

/-- matrixFunction of negation is negation of A. -/
lemma matrixFunction_neg_id {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.IsHermitian) :
    matrixFunction (fun x => -(x : ℂ)) A hA = -A := by
  have h : (fun x : ℝ => -(x : ℂ)) = (fun x => -((fun y : ℝ => (y : ℂ)) x)) := rfl
  rw [h, matrixFunction_neg, matrixFunction_id]

/-- matrixFunction depends only on the matrix value, not on the specific proof term.
    If two matrices are equal, their matrixFunctions are equal. -/
lemma matrixFunction_congr {m : Type*} [Fintype m] [DecidableEq m]
    {A B : Matrix m m ℂ} (f : ℝ → ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : A = B) : matrixFunction f A hA = matrixFunction f B hB := by
  subst hAB
  rfl

/-- matrixFunction equals Mathlib's IsHermitian.cfc for real-valued functions.
This connects our spectral decomposition definition to Mathlib's CFC infrastructure. -/
lemma matrixFunction_eq_cfc {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    matrixFunction (fun x => (f x : ℂ)) A hA = cfc f A := by
  have h : matrixFunction (fun x => (f x : ℂ)) A hA = hA.cfc f := by
    unfold matrixFunction Matrix.IsHermitian.cfc
    rw [Unitary.conjStarAlgAut_apply]
    simp only [Function.comp_def, star_eq_conjTranspose]
    rfl
  calc
    matrixFunction (fun x => (f x : ℂ)) A hA = hA.cfc f := h
    _ = cfc f A := by
      simpa using (Matrix.IsHermitian.cfc_eq (A := A) (hA := hA) (f := f)).symm

/-- `matrixFunction` for the affine function `x ↦ x + t` adds `t • I`. -/
lemma matrixFunction_add_const {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.IsHermitian) (t : ℝ) :
    matrixFunction (fun x => ((x + t : ℝ) : ℂ)) A hA = A + (t : ℂ) • 1 := by
  classical
  unfold matrixFunction
  set U : Matrix m m ℂ := (hA.eigenvectorUnitary : Matrix m m ℂ)
  have hdiag :
      diagonal (fun i => ((hA.eigenvalues i + t : ℝ) : ℂ)) =
        diagonal (fun i => (hA.eigenvalues i : ℂ)) + (t : ℂ) • 1 := by
    ext i j
    by_cases h : i = j
    · subst h
      simp
    · simp [h]
  rw [hdiag]
  simp only [Matrix.mul_add, Matrix.add_mul]
  have hU : U * Uᴴ = 1 := by
    simpa [U, star_eq_conjTranspose] using Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hU1 : U * (1 : Matrix m m ℂ) * Uᴴ = 1 := by
    simp [hU]
  have hspec := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose] at hspec
  have hspec' : U * diagonal (fun i => (hA.eigenvalues i : ℂ)) * Uᴴ = A := by
    simpa [U, Function.comp] using hspec.symm
  -- Rewrite the two diagonal terms using the spectral theorem and unitarity.
  calc
    U * diagonal (fun i => (hA.eigenvalues i : ℂ)) * Uᴴ +
        U * ((t : ℂ) • (1 : Matrix m m ℂ)) * Uᴴ =
        A + (t : ℂ) • 1 := by
      rw [hspec']
      have hUt : U * ((t : ℂ) • (1 : Matrix m m ℂ)) * Uᴴ =
          (t : ℂ) • (U * (1 : Matrix m m ℂ) * Uᴴ) := by
        calc
          U * ((t : ℂ) • (1 : Matrix m m ℂ)) * Uᴴ =
              ((t : ℂ) • (U * (1 : Matrix m m ℂ))) * Uᴴ := by
                simp
          _ = (t : ℂ) • (U * (1 : Matrix m m ℂ) * Uᴴ) := by
                simp
      calc
        A + U * ((t : ℂ) • (1 : Matrix m m ℂ)) * Uᴴ =
            A + (t : ℂ) • (U * (1 : Matrix m m ℂ) * Uᴴ) := by
          rw [hUt]
        _ = A + (t : ℂ) • 1 := by
          calc
            A + (t : ℂ) • (U * (1 : Matrix m m ℂ) * Uᴴ) =
                A + (t : ℂ) • (U * Uᴴ) := by
              simp
            _ = A + (t : ℂ) • 1 := by
              simp [hU]

/-- `matrixFunction` for `x ↦ (x + t)⁻¹` equals `(A + t•I)⁻¹` when `t > 0` and `A` is PSD. -/
lemma matrixFunction_inv_add_const {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.PosSemidef) {t : ℝ} (ht : 0 < t) :
    matrixFunction (fun x => ((x + t : ℝ) : ℂ)⁻¹) A hA.1 =
      (A + (t : ℂ) • 1)⁻¹ := by
  classical
  have hA' : A.IsHermitian := hA.1
  have hneq : ∀ x ∈ spectrum ℝ A, (x + t) ≠ 0 := by
    intro x hx
    have hx' : x ∈ Set.range hA'.eigenvalues := by
      simpa [hA'.spectrum_real_eq_range_eigenvalues] using hx
    rcases hx' with ⟨i, rfl⟩
    have hx_nonneg : 0 ≤ hA.1.eigenvalues i := hA.eigenvalues_nonneg i
    linarith
  have hcfcinv :
      cfc (fun x : ℝ => (x + t)⁻¹) A = Ring.inverse (cfc (fun x : ℝ => x + t) A) := by
    simpa using (cfc_inv (A := Matrix m m ℂ) (f := fun x : ℝ => x + t) (a := A) hneq)
  have hcfcaff : cfc (fun x : ℝ => x + t) A = A + (t : ℂ) • 1 := by
    have h := matrixFunction_add_const (m := m) hA' t
    calc
      cfc (fun x : ℝ => x + t) A =
          matrixFunction (fun x => ((x + t : ℝ) : ℂ)) A hA' := by
        simpa using (matrixFunction_eq_cfc hA' (fun x => x + t)).symm
      _ = A + (t : ℂ) • 1 := h
  have hposdef : (A + (t : ℂ) • 1).PosDef := PosSemidef.add_smul_one_posDef hA ht
  have hunit : IsUnit (A + (t : ℂ) • 1) := hposdef.isUnit
  let _ := hunit.invertible
  have hcfcaff_inv : Ring.inverse (cfc (fun x : ℝ => x + t) A) = (A + (t : ℂ) • 1)⁻¹ := by
    simpa [hcfcaff] using (Ring.inverse_unit hunit.unit)
  have hmf : matrixFunction (fun x => ((x + t : ℝ) : ℂ)⁻¹) A hA.1 =
      cfc (fun x : ℝ => (x + t)⁻¹) A := by
    simpa using (matrixFunction_eq_cfc hA' (fun x => (x + t)⁻¹))
  rw [hmf, hcfcinv, hcfcaff_inv]

/-- `matrixFunction` agrees with `CFC.rpow` for PSD matrices. -/
lemma matrixFunction_rpow_eq {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.PosSemidef) (s : ℝ) :
    matrixFunction (fun x => ((x ^ s : ℝ) : ℂ)) A hA.1 = A ^ s := by
  have hA0 : 0 ≤ A := by
    simpa [Matrix.le_iff] using hA
  calc
    matrixFunction (fun x => ((x ^ s : ℝ) : ℂ)) A hA.1 = cfc (fun x : ℝ => x ^ s) A := by
      simpa using (matrixFunction_eq_cfc hA.1 (fun x => x ^ s))
    _ = A ^ s := by
      symm
      exact CFC.rpow_eq_cfc_real (A := Matrix m m ℂ) (a := A) (y := s) (ha := hA0)

/-- Resolvent form for `matrixFunction` on PSD matrices. -/
lemma matrixFunction_resolvent {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.PosSemidef) {r : ℝ} (hr : 0 < r) :
    matrixFunction (fun x => ((1 - r * (x + r)⁻¹ : ℝ) : ℂ)) A hA.1 =
      (1 : Matrix m m ℂ) - (r : ℂ) • (A + (r : ℂ) • 1)⁻¹ := by
  have hfun_inv : (fun x : ℝ => ((x : ℂ) + (r : ℂ))⁻¹) =
      (fun x : ℝ => ((x + r : ℝ) : ℂ)⁻¹) := by
    funext x
    simp
  have hfun : (fun x : ℝ => ((1 - r * (x + r)⁻¹ : ℝ) : ℂ)) =
      (fun x : ℝ => (1 : ℂ) + -((r : ℂ) * ((x : ℂ) + (r : ℂ))⁻¹)) := by
    funext x
    push_cast
    ring
  have hconst : matrixFunction (fun _ => (1 : ℂ)) A hA.1 = (1 : Matrix m m ℂ) := by
    simpa using (matrixFunction_const (m := m) hA.1 (1 : ℂ))
  have hinv : matrixFunction (fun x => ((x + r : ℝ) : ℂ)⁻¹) A hA.1 =
      (A + (r : ℂ) • 1)⁻¹ := by
    exact matrixFunction_inv_add_const (m := m) hA hr
  calc
    matrixFunction (fun x => ((1 - r * (x + r)⁻¹ : ℝ) : ℂ)) A hA.1 =
        matrixFunction (fun x => (1 : ℂ) + -((r : ℂ) * ((x : ℂ) + (r : ℂ))⁻¹)) A hA.1 := by
          rw [hfun]
    _ = matrixFunction (fun _ => (1 : ℂ)) A hA.1 +
        matrixFunction (fun x => -((r : ℂ) * ((x : ℂ) + (r : ℂ))⁻¹)) A hA.1 := by
          simpa using (matrixFunction_add hA.1 (fun _ => (1 : ℂ))
            (fun x => -((r : ℂ) * ((x : ℂ) + (r : ℂ))⁻¹)))
    _ = (1 : Matrix m m ℂ) +
        -((r : ℂ) • matrixFunction (fun x => ((x : ℂ) + (r : ℂ))⁻¹) A hA.1) := by
      have hsmul :
          matrixFunction (fun x => (r : ℂ) * ((x : ℂ) + (r : ℂ))⁻¹) A hA.1 =
            (r : ℂ) • matrixFunction (fun x => ((x : ℂ) + (r : ℂ))⁻¹) A hA.1 := by
        simpa using
          (matrixFunction_smul hA.1 (r : ℂ) (fun x => ((x : ℂ) + (r : ℂ))⁻¹))
      have hneg :
          matrixFunction (fun x => -((r : ℂ) * ((x : ℂ) + (r : ℂ))⁻¹)) A hA.1 =
            -((r : ℂ) • matrixFunction (fun x => ((x : ℂ) + (r : ℂ))⁻¹) A hA.1) := by
        simpa [hsmul] using
          (matrixFunction_neg hA.1 (fun x => (r : ℂ) * ((x : ℂ) + (r : ℂ))⁻¹))
      simp [hconst, hneg]
    _ = (1 : Matrix m m ℂ) - (r : ℂ) • (A + (r : ℂ) • 1)⁻¹ := by
      calc
        (1 : Matrix m m ℂ) +
            -((r : ℂ) • matrixFunction (fun x => ((x : ℂ) + (r : ℂ))⁻¹) A hA.1) =
          (1 : Matrix m m ℂ) + -((r : ℂ) • (A + (r : ℂ) • 1)⁻¹) := by
            have hinv' :
                matrixFunction (fun x : ℝ => ((x : ℂ) + (r : ℂ))⁻¹) A hA.1 =
                  (A + (r : ℂ) • 1)⁻¹ := by
              simpa [hfun_inv] using hinv
            simp [hinv']
        _ = (1 : Matrix m m ℂ) - (r : ℂ) • (A + (r : ℂ) • 1)⁻¹ := by
          simp [sub_eq_add_neg]

/-- matrixFunction preserves positive semidefiniteness when f maps nonneg eigenvalues to nonneg. -/
lemma matrixFunction_posSemidef {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.PosSemidef)
    (f : ℝ → ℝ) (hf : ∀ i, 0 ≤ f (hA.1.eigenvalues i)) :
    (matrixFunction (fun x => (f x : ℂ)) A hA.1).PosSemidef := by
  unfold matrixFunction
  have hD : (diagonal (fun i => (f (hA.1.eigenvalues i) : ℂ))).PosSemidef :=
    PosSemidef.diagonal_ofReal hf
  have key := hD.conjTranspose_mul_mul_same ((hA.1.eigenvectorUnitary : Matrix m m ℂ)ᴴ)
  simp only [conjTranspose_conjTranspose] at key
  exact key

/-- matrixFunction (f - c) = matrixFunction f - c • I -/
lemma matrixFunction_sub_const {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) (c : ℝ) :
    matrixFunction (fun x => (f x - c : ℂ)) A hA = matrixFunction (fun x => (f x : ℂ)) A hA - (c : ℂ) • 1 := by
  classical
  let U : Matrix m m ℂ := hA.eigenvectorUnitary
  have hU : U * Uᴴ = 1 := by
    simpa [U, star_eq_conjTranspose] using Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hdiag :
      diagonal (fun i => (f (hA.eigenvalues i) - c : ℂ)) =
        diagonal (fun i => (f (hA.eigenvalues i) : ℂ)) - diagonal (fun _ => (c : ℂ)) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp
    · simp [h]
  have hdiagc : diagonal (fun _ => (c : ℂ)) = (c : ℂ) • (1 : Matrix m m ℂ) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp
    · simp [h]
  unfold matrixFunction
  rw [hdiag]
  simp only [Matrix.mul_sub, Matrix.sub_mul]
  rw [hdiagc]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  rw [hU]

/-- Product of two matrixFunctions is the matrixFunction of the pointwise product.
Since both share the eigenbasis U, f(A) g(A) = U diag(f(λ) · g(λ)) U*. -/
lemma matrixFunction_mul {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.IsHermitian) (f g : ℝ → ℂ) :
    matrixFunction f A hA * matrixFunction g A hA =
      matrixFunction (fun x => f x * g x) A hA := by
  unfold matrixFunction
  set U : Matrix m m ℂ := (hA.eigenvectorUnitary : Matrix m m ℂ) with hU_def
  have hUU : Uᴴ * U = 1 := by
    simpa [star_eq_conjTranspose] using Unitary.coe_star_mul_self hA.eigenvectorUnitary
  simp only [hU_def, Matrix.mul_assoc]
  congr 1
  rw [← Matrix.mul_assoc Uᴴ U, hUU, Matrix.one_mul, ← Matrix.mul_assoc, diagonal_mul_diagonal]

/-- Tr(A · f(A)) = ∑ᵢ λᵢ · f(λᵢ).
We first rewrite A as id(A) via `matrixFunction_id`, then apply
`matrixFunction_mul` and `matrixFunction_trace`. -/
lemma trace_mul_matrixFunction {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℂ) (hA : A.IsHermitian) (f : ℝ → ℂ) :
    (A * matrixFunction f A hA).trace =
      ∑ i, ((hA.eigenvalues i : ℂ) * f (hA.eigenvalues i)) := by
  suffices h : (matrixFunction (fun x => (x : ℂ)) A hA *
               matrixFunction f A hA).trace =
               ∑ i, ((hA.eigenvalues i : ℂ) * f (hA.eigenvalues i)) by
    rwa [matrixFunction_id] at h
  rw [matrixFunction_mul, matrixFunction_trace]

/-- A Hermitian matrix commutes with any matrixFunction of itself.
This follows from `matrixFunction_id` (A = id(A)) and `matrixFunction_mul`
(id(A) · f(A) = f(A) · id(A) by pointwise commutativity of multiplication). -/
lemma commute_matrixFunction_self {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.IsHermitian) (f : ℝ → ℂ) :
    Commute A (matrixFunction f A hA) := by
  have hlhs : A * matrixFunction f A hA =
      matrixFunction (fun x => (x : ℂ) * f x) A hA := by
    have := matrixFunction_mul hA (fun x => (x : ℂ)) f
    rwa [matrixFunction_id] at this
  have hrhs : matrixFunction f A hA * A =
      matrixFunction (fun x => f x * (x : ℂ)) A hA := by
    have := matrixFunction_mul hA f (fun x => (x : ℂ))
    rwa [matrixFunction_id] at this
  change A * matrixFunction f A hA = matrixFunction f A hA * A
  rw [hlhs, hrhs]
  congr 1; ext x; ring

/-- The product A · f(A) is Hermitian when A is Hermitian and f : ℝ → ℝ.
Since A and f(A) share the same eigenbasis, they commute; both are Hermitian,
so their product is Hermitian by `IsHermitian.commute_iff`. -/
lemma mul_matrixFunction_isHermitian {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (A * matrixFunction (fun x => (f x : ℂ)) A hA).IsHermitian :=
  (hA.commute_iff (matrixFunction_isHermitian hA f)).mp
    (commute_matrixFunction_self hA _)

/-- The trace of a Hermitian matrix is real: casting its real part back to ℂ recovers the trace.
Proof: Aᴴ = A implies star(Tr A) = Tr(Aᴴ) = Tr A, so Tr A is self-adjoint,
hence equal to its real part cast to ℂ. -/
lemma IsHermitian.trace_ofReal_re {m : Type*} [Fintype m]
    {A : Matrix m m ℂ} (hA : A.IsHermitian) :
    (A.trace.re : ℂ) = A.trace := by
  have h : (starRingEnd ℂ) A.trace = A.trace := by
    change star A.trace = A.trace
    rw [← trace_conjTranspose, hA.eq]
  exact (RCLike.conj_eq_iff_re (K := ℂ)).mp h

/-- Matrix exponential for Hermitian matrices via spectral decomposition. -/
noncomputable def matrixExp {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℂ) (hA : A.IsHermitian) : Matrix m m ℂ :=
  matrixFunction (fun x => Real.exp x) A hA

/-- Matrix logarithm for positive definite matrices via spectral decomposition. -/
noncomputable def matrixLog {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℂ) (hA : A.IsHermitian) : Matrix m m ℂ :=
  matrixFunction (fun x => Real.log x) A hA

/-- Trace of matrix exponential equals sum of exp of eigenvalues. -/
lemma matrixExp_trace {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℂ) (hA : A.IsHermitian) :
    (matrixExp A hA).trace = ∑ i, (Real.exp (hA.eigenvalues i) : ℂ) := by
  unfold matrixExp
  rw [matrixFunction_trace]

/-- Trace of matrix logarithm equals sum of log of eigenvalues. -/
lemma matrixLog_trace {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℂ) (hA : A.IsHermitian) :
    (matrixLog A hA).trace = ∑ i, (Real.log (hA.eigenvalues i) : ℂ) := by
  unfold matrixLog
  rw [matrixFunction_trace]

/-- Matrix logarithm of a Hermitian matrix is Hermitian. -/
lemma matrixLog_isHermitian {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℂ) (hA : A.IsHermitian) :
    (matrixLog A hA).IsHermitian := by
  unfold matrixLog matrixFunction IsHermitian
  simp only [conjTranspose_mul, conjTranspose_conjTranspose]
  have hDiag := IsHermitian.diagonal_real (fun i => Real.log (hA.eigenvalues i))
  rw [IsHermitian] at hDiag
  rw [hDiag, Matrix.mul_assoc]

/-- Matrix inverse square root via functional calculus for PD matrices. -/
noncomputable def matrixInvSqrt {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℂ) (hA : A.PosDef) : Matrix m m ℂ :=
  matrixFunction (fun x => (Real.rpow x (-1 / 2 : ℝ) : ℂ)) A hA.1

/-- The matrix inverse square root of a PD matrix is Hermitian. -/
lemma matrixInvSqrt_isHermitian {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.PosDef) :
    (matrixInvSqrt A hA).IsHermitian := by
  unfold matrixInvSqrt
  exact matrixFunction_isHermitian hA.1 (fun x => Real.rpow x (-1 / 2 : ℝ))

/-- For a positive definite matrix `A`, `A^{-1/2} * A * A^{-1/2} = I`. -/
lemma matrixInvSqrt_mul_self {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.PosDef) :
    matrixInvSqrt A hA * A * matrixInvSqrt A hA = 1 := by
  have hS : matrixInvSqrt A hA = A ^ (-1 / 2 : ℝ) := by
    simpa [matrixInvSqrt] using (matrixFunction_rpow_eq hA.posSemidef (-1 / 2 : ℝ))
  have hAunit : IsUnit A := hA.isUnit
  have hnonneg : 0 ≤ A := by
    simpa [Matrix.le_iff] using hA.posSemidef
  calc
    matrixInvSqrt A hA * A * matrixInvSqrt A hA =
        A ^ (-1 / 2 : ℝ) * A * A ^ (-1 / 2 : ℝ) := by
      simp [hS]
    _ = A ^ (-1 / 2 : ℝ) * A ^ (1 : ℝ) * A ^ (-1 / 2 : ℝ) := by
      simp [CFC.rpow_one (a := A) hnonneg]
    _ = A ^ ((-1 / 2 : ℝ) + (1 : ℝ)) * A ^ (-1 / 2 : ℝ) := by
      simp [CFC.rpow_add (a := A) (x := (-1 / 2 : ℝ)) (y := (1 : ℝ)) hAunit, mul_assoc]
    _ = A ^ (1 / 2 : ℝ) * A ^ (-1 / 2 : ℝ) := by
      ring_nf
    _ = 1 := by
      calc
        A ^ (1 / 2 : ℝ) * A ^ (-1 / 2 : ℝ) =
            A ^ ((1 / 2 : ℝ) + (-1 / 2 : ℝ)) := by
          symm
          simpa using (CFC.rpow_add (a := A) (x := (1 / 2 : ℝ)) (y := (-1 / 2 : ℝ)) hAunit)
        _ = 1 := by
          ring_nf
          simpa using (CFC.rpow_zero (a := A) hnonneg)

/-- Matrix square root via functional calculus for PSD matrices. -/
noncomputable def matrixSqrt {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℂ) (hA : A.PosSemidef) : Matrix m m ℂ :=
  matrixFunction (fun x => (Real.rpow x (1 / 2 : ℝ) : ℂ)) A hA.1

/-- The matrix square root of a PSD matrix is Hermitian. -/
lemma matrixSqrt_isHermitian {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.PosSemidef) :
    (matrixSqrt A hA).IsHermitian := by
  unfold matrixSqrt
  exact matrixFunction_isHermitian hA.1 (fun x => Real.rpow x (1 / 2 : ℝ))

/-- For a positive semidefinite matrix `A`, `A^{1/2} * A^{1/2} = A`. -/
lemma matrixSqrt_mul_self_posSemidef {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.PosSemidef) :
    matrixSqrt A hA * matrixSqrt A hA = A := by
  classical
  -- Use the spectral decomposition and diagonal computation.
  unfold matrixSqrt matrixFunction
  set U : Matrix m m ℂ := (hA.1.eigenvectorUnitary : Matrix m m ℂ)
  set D : Matrix m m ℂ :=
    diagonal (fun i => (Real.rpow (hA.1.eigenvalues i) (1 / 2 : ℝ) : ℂ))
  have hU : Uᴴ * U = (1 : Matrix m m ℂ) := by
    simpa [U, star_eq_conjTranspose] using Unitary.coe_star_mul_self hA.1.eigenvectorUnitary
  have hD_mul : D * D = diagonal (fun i => (hA.1.eigenvalues i : ℂ)) := by
    ext i j
    by_cases h : i = j
    · subst h
      have hnonneg : 0 ≤ hA.1.eigenvalues i := hA.eigenvalues_nonneg i
      simp only [D, mul_diagonal, diagonal_apply_eq]
      norm_cast
      simp only [Real.rpow_eq_pow]
      rw [← Real.sqrt_eq_rpow, Real.mul_self_sqrt hnonneg]
    · simp only [D, mul_diagonal]
      simp [h]
  calc
    U * D * Uᴴ * (U * D * Uᴴ)
        = U * (D * D) * Uᴴ := by
            simp only [Matrix.mul_assoc]
            congr 1
            rw [← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul]
    _ = U * diagonal (fun i => (hA.1.eigenvalues i : ℂ)) * Uᴴ := by
            simp [hD_mul]
    _ = A := by
            simpa [U] using (hA.1.spectral_theorem).symm

/-- For a positive definite matrix `A`, `A^{1/2} * A^{1/2} = A`. -/
lemma matrixSqrt_mul_self {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.PosDef) :
    matrixSqrt A hA.posSemidef * matrixSqrt A hA.posSemidef = A := by
  have hS : matrixSqrt A hA.posSemidef = A ^ (1 / 2 : ℝ) := by
    simpa [matrixSqrt] using (matrixFunction_rpow_eq hA.posSemidef (1 / 2 : ℝ))
  have hAunit : IsUnit A := hA.isUnit
  calc
    matrixSqrt A hA.posSemidef * matrixSqrt A hA.posSemidef =
        A ^ (1 / 2 : ℝ) * A ^ (1 / 2 : ℝ) := by
      simp [hS]
    _ = A ^ ((1 / 2 : ℝ) + (1 / 2 : ℝ)) := by
      symm
      simpa using (CFC.rpow_add (a := A) (x := (1 / 2 : ℝ)) (y := (1 / 2 : ℝ)) hAunit)
    _ = A := by
      have hnonneg : 0 ≤ A := by
        simpa [Matrix.le_iff] using hA.posSemidef
      ring_nf
      simpa using (CFC.rpow_one (a := A) hnonneg)

/-- For a positive definite matrix `A`, `A^{1/2} * A^{-1/2} = I`. -/
lemma matrixSqrt_mul_matrixInvSqrt {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.PosDef) :
    matrixSqrt A hA.posSemidef * matrixInvSqrt A hA = 1 := by
  have hS : matrixSqrt A hA.posSemidef = A ^ (1 / 2 : ℝ) := by
    simpa [matrixSqrt] using (matrixFunction_rpow_eq hA.posSemidef (1 / 2 : ℝ))
  have hSi : matrixInvSqrt A hA = A ^ (-1 / 2 : ℝ) := by
    simpa [matrixInvSqrt] using (matrixFunction_rpow_eq hA.posSemidef (-1 / 2 : ℝ))
  have hAunit : IsUnit A := hA.isUnit
  have hnonneg : 0 ≤ A := by
    simpa [Matrix.le_iff] using hA.posSemidef
  calc
    matrixSqrt A hA.posSemidef * matrixInvSqrt A hA =
        A ^ (1 / 2 : ℝ) * A ^ (-1 / 2 : ℝ) := by
      simp [hS, hSi]
    _ = A ^ ((1 / 2 : ℝ) + (-1 / 2 : ℝ)) := by
      symm
      simpa using (CFC.rpow_add (a := A) (x := (1 / 2 : ℝ)) (y := (-1 / 2 : ℝ)) hAunit)
    _ = 1 := by
      ring_nf
      simpa using (CFC.rpow_zero (a := A) hnonneg)

/-- For a positive definite matrix `A`, `A^{-1/2} * A^{1/2} = I`. -/
lemma matrixInvSqrt_mul_matrixSqrt {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.PosDef) :
    matrixInvSqrt A hA * matrixSqrt A hA.posSemidef = 1 := by
  have hS : matrixSqrt A hA.posSemidef = A ^ (1 / 2 : ℝ) := by
    simpa [matrixSqrt] using (matrixFunction_rpow_eq hA.posSemidef (1 / 2 : ℝ))
  have hSi : matrixInvSqrt A hA = A ^ (-1 / 2 : ℝ) := by
    simpa [matrixInvSqrt] using (matrixFunction_rpow_eq hA.posSemidef (-1 / 2 : ℝ))
  have hAunit : IsUnit A := hA.isUnit
  have hnonneg : 0 ≤ A := by
    simpa [Matrix.le_iff] using hA.posSemidef
  calc
    matrixInvSqrt A hA * matrixSqrt A hA.posSemidef =
        A ^ (-1 / 2 : ℝ) * A ^ (1 / 2 : ℝ) := by
      simp [hS, hSi]
    _ = A ^ ((-1 / 2 : ℝ) + (1 / 2 : ℝ)) := by
      symm
      simpa using (CFC.rpow_add (a := A) (x := (-1 / 2 : ℝ)) (y := (1 / 2 : ℝ)) hAunit)
    _ = 1 := by
      ring_nf
      simpa using (CFC.rpow_zero (a := A) hnonneg)

/-- For commuting PSD L and PD R, matrixInvSqrt R commutes with L.
This follows from the fact that L commutes with R, and CFC (hence rpow) preserves
commutativity. Since matrixInvSqrt R = R^{-1/2} (by matrixFunction_rpow_eq), and
Commute.cfc_real gives that cfc g R commutes with L when L commutes with R,
the result follows. -/
lemma matrixInvSqrt_commute_of_commute {n : Type*} [Fintype n] [DecidableEq n]
    {L R : Matrix n n ℂ} (_hL : L.PosSemidef) (hR : R.PosDef)
    (hcomm : L * R = R * L) :
    matrixInvSqrt R hR * L = L * matrixInvSqrt R hR := by
  letI : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℂ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  letI : CStarAlgebra (Matrix n n ℂ) := by
    simpa [CStarMatrix] using CStarMatrix.instCStarAlgebra (n := n) (A := ℂ)
  have hRinv_eq : matrixInvSqrt R hR = R ^ (-1 / 2 : ℝ) := by
    simpa [matrixInvSqrt] using matrixFunction_rpow_eq hR.posSemidef (-1 / 2 : ℝ)
  rw [hRinv_eq]
  -- R^{-1/2} = cfc(x^{-1/2}, R), so it commutes with L since L commutes with R
  have hR0 : (0 : Matrix n n ℂ) ≤ R := by simpa [Matrix.le_iff] using hR.posSemidef
  rw [CFC.rpow_eq_cfc_real (a := R) (ha := hR0)]
  have hcommute : Commute R L := hcomm.symm
  exact Commute.cfc_real hcommute _

/-- For a PSD matrix `A`, `(A^{1/2})ᴴ * A^{1/2} = A` (since the square root is Hermitian). -/
lemma matrixSqrt_conjTranspose_mul_self_posSemidef {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.PosSemidef) :
    (matrixSqrt A hA)ᴴ * matrixSqrt A hA = A := by
  have hherm : (matrixSqrt A hA).IsHermitian := matrixSqrt_isHermitian hA
  calc
    (matrixSqrt A hA)ᴴ * matrixSqrt A hA = matrixSqrt A hA * matrixSqrt A hA := by
      simp [hherm.eq]
    _ = A := matrixSqrt_mul_self_posSemidef hA

/-- At p = 0: `matrixFunction (fun x => x ^ 0) A = I`. -/
lemma matrixFunction_cpow_zero {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℂ) (hA : A.IsHermitian) :
    matrixFunction (fun x => x ^ (0 : ℂ)) A hA = 1 := by
  unfold matrixFunction
  have h_pow : (fun i => ((hA.eigenvalues i : ℝ) : ℂ) ^ (0 : ℂ)) = (fun _ => 1) := by
    ext i
    simp [Complex.cpow_zero]
  simp only [h_pow, Matrix.diagonal_one, Matrix.mul_one]
  have h := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  simp only [Unitary.coe_star, star_eq_conjTranspose] at h
  exact h

/-- `matrixFunction (fun x => x ^ 1) A = A`. -/
lemma matrixFunction_cpow_one {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℂ) (hA : A.IsHermitian) :
    matrixFunction (fun x => x ^ (1 : ℂ)) A hA = A := by
  unfold matrixFunction
  have h_pow : (fun i => ((hA.eigenvalues i : ℝ) : ℂ) ^ (1 : ℂ)) =
      (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) := by
    ext i
    simp [Complex.cpow_one]
  have h_diag : diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) =
      diagonal (RCLike.ofReal ∘ hA.eigenvalues) := rfl
  simp only [h_pow, h_diag]
  have h_spec := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose] at h_spec
  exact h_spec.symm

/-- CFC commutes with unitary conjugation using `Unitary.conjStarAlgAut`. -/
lemma cfc_unitary_conjugation' {m : Type*} [Fintype m] [DecidableEq m]
    (U : unitary (Matrix m m ℂ)) (M : Matrix m m ℂ)
    (hM : IsSelfAdjoint M) (f : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ M)) :
    (U : Matrix m m ℂ) * cfc f M * star (U : Matrix m m ℂ) =
    cfc f ((U : Matrix m m ℂ) * M * star (U : Matrix m m ℂ)) := by
  change (Unitary.conjStarAlgAut ℝ _ U) (cfc f M) =
    cfc f ((Unitary.conjStarAlgAut ℝ _ U) M)
  have hcont : Continuous (Unitary.conjStarAlgAut ℝ (Matrix m m ℂ) U) :=
    (Unitary.conjStarAlgAut ℝ (Matrix m m ℂ) U).toAlgEquiv.toLinearMap.continuous_of_finiteDimensional
  exact StarAlgHomClass.map_cfc (Unitary.conjStarAlgAut ℝ _ U) f M hf hcont hM

/-- Block diagonal embedding as a star algebra homomorphism.
Maps (A, D) ↦ fromBlocks(A, 0, 0, D). -/
noncomputable def blockDiagEmbed (m : Type*) [Fintype m] [DecidableEq m] :
    (Matrix m m ℂ × Matrix m m ℂ) →⋆ₐ[ℝ] Matrix (m ⊕ m) (m ⊕ m) ℂ where
  toFun p := fromBlocks p.1 0 0 p.2
  map_one' := fromBlocks_one
  map_mul' p q := by simp [fromBlocks_multiply]
  map_zero' := by simp [fromBlocks_zero]
  map_add' p q := by simp [fromBlocks_add]
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one]
    ext (i | i) (j | j) <;> simp [fromBlocks, Matrix.one_apply, Sum.inl.injEq, Sum.inr.injEq]
  map_star' p := by
    simp [star_eq_conjTranspose, fromBlocks_conjTranspose, Prod.star_def]

/-- CFC of a block diagonal matrix equals the block diagonal of CFC of the blocks.
  f(A ⊕ D) = f(A) ⊕ f(D) -/
lemma cfc_fromBlocks_diag {m : Type*} [Fintype m] [DecidableEq m]
    (A D : Matrix m m ℂ) (hA : IsSelfAdjoint A)
    (hD : IsSelfAdjoint D) (f : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ A ∪ spectrum ℝ D)) :
    cfc f (fromBlocks A 0 0 D) = fromBlocks (cfc f A) 0 0 (cfc f D) := by
  letI : NormedRing (Matrix m m ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℂ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra
  letI : CStarAlgebra (Matrix m m ℂ) := by
    simpa [CStarMatrix] using CStarMatrix.instCStarAlgebra (n := m) (A := ℂ)
  have hcont : Continuous (blockDiagEmbed m) := by
    change Continuous fun p : Matrix m m ℂ × Matrix m m ℂ => fromBlocks p.1 0 0 p.2
    fun_prop
  have hAD : IsSelfAdjoint (A, D) := by
    rw [IsSelfAdjoint, Prod.star_def]
    exact Prod.ext hA.star_eq hD.star_eq
  have h_map := StarAlgHom.map_cfc (blockDiagEmbed m) f (A, D) (by
    rwa [Prod.spectrum_eq]) hcont hAD
  have h_prod := cfc_map_prod (S := ℝ) f A D hf hAD hA hD
  rw [h_prod] at h_map
  exact h_map.symm

/-- Block diagonal embedding for different-dimension blocks as a star algebra homomorphism.
Maps (A, D) ↦ fromBlocks(A, 0, 0, D) where A : n×n and D : m×m. -/
noncomputable def blockDiagEmbed' (n m : Type*) [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] :
    (Matrix n n ℂ × Matrix m m ℂ) →⋆ₐ[ℝ] Matrix (n ⊕ m) (n ⊕ m) ℂ where
  toFun p := fromBlocks p.1 0 0 p.2
  map_one' := fromBlocks_one
  map_mul' p q := by simp [fromBlocks_multiply]
  map_zero' := by simp [fromBlocks_zero]
  map_add' p q := by simp [fromBlocks_add]
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one]
    ext (i | i) (j | j) <;> simp [fromBlocks, Matrix.one_apply, Sum.inl.injEq, Sum.inr.injEq]
  map_star' p := by
    simp [star_eq_conjTranspose, fromBlocks_conjTranspose, Prod.star_def]

/-- CFC of a block diagonal matrix (different dimensions) equals the block diagonal of CFC.
  f(A ⊕ D) = f(A) ⊕ f(D) where A : n×n and D : m×m. -/
lemma cfc_fromBlocks_diag' {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (A : Matrix n n ℂ) (D : Matrix m m ℂ) (hA : IsSelfAdjoint A)
    (hD : IsSelfAdjoint D) (f : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ A ∪ spectrum ℝ D)) :
    cfc f (fromBlocks A 0 0 D) = fromBlocks (cfc f A) 0 0 (cfc f D) := by
  letI : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℂ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  letI : CStarAlgebra (Matrix n n ℂ) := by
    simpa [CStarMatrix] using CStarMatrix.instCStarAlgebra (n := n) (A := ℂ)
  letI : NormedRing (Matrix m m ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℂ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra
  letI : CStarAlgebra (Matrix m m ℂ) := by
    simpa [CStarMatrix] using CStarMatrix.instCStarAlgebra (n := m) (A := ℂ)
  have hcont : Continuous (blockDiagEmbed' n m) := by
    change Continuous fun p : Matrix n n ℂ × Matrix m m ℂ => fromBlocks p.1 0 0 p.2
    fun_prop
  have hAD : IsSelfAdjoint (A, D) := by
    rw [IsSelfAdjoint, Prod.star_def]
    exact Prod.ext hA.star_eq hD.star_eq
  have h_map := StarAlgHom.map_cfc (blockDiagEmbed' n m) f (A, D) (by
    rwa [Prod.spectrum_eq]) hcont hAD
  have h_prod := cfc_map_prod (S := ℝ) f A D hf hAD hA hD
  rw [h_prod] at h_map
  exact h_map.symm

/-! ### Matrix Convexity Implies Jensen Convexity

The equivalence between Löwner convexity and Löwner convexity (HPJ form) is a
classical result in matrix analysis. The standard proof uses the block diagonal
technique: embed the 2-term HPJ problem into a larger space using block matrices.

Reference: Hansen-Pedersen (2003), "Jensen's Operator Inequality" -/

-- Helper: V†M^k V = (V†MV)^k when PM = MP and V†V = I
-- where P = VV†.
lemma compression_pow_eq {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (V : Matrix n m ℂ) (M : Matrix n n ℂ)
    (hVV : Vᴴ * V = (1 : Matrix m m ℂ))
    (hcomm : M * (V * Vᴴ) = V * Vᴴ * M) (k : ℕ) :
    Vᴴ * M ^ k * V = (Vᴴ * M * V) ^ k := by
  -- First establish: M^j commutes with VV† for all j
  have hcommk : ∀ j : ℕ, M ^ j * (V * Vᴴ) = V * Vᴴ * M ^ j := by
    intro j; induction j with
    | zero => simp [pow_zero]
    | succ j ihj =>
      rw [pow_succ, Matrix.mul_assoc, hcomm, ← Matrix.mul_assoc, ihj,
          Matrix.mul_assoc, ← pow_succ]
  -- Key: V†Q = 0 where Q = I - VV†
  have hVQ : Vᴴ * ((1 : Matrix n n ℂ) - V * Vᴴ) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one]
    rw [show Vᴴ * (V * Vᴴ) = (Vᴴ * V) * Vᴴ from (Matrix.mul_assoc _ _ _).symm]
    rw [hVV, Matrix.one_mul, sub_self]
  -- V†M^k(I - VV†) = 0
  have hV_Mk_Q : ∀ j : ℕ, Vᴴ * M ^ j * ((1 : Matrix n n ℂ) - V * Vᴴ) = 0 := by
    intro j
    -- M^j(I - VV†) = (I - VV†)M^j (since M^j commutes with VV†)
    have h_comm_q : M ^ j * ((1 : Matrix n n ℂ) - V * Vᴴ) =
        ((1 : Matrix n n ℂ) - V * Vᴴ) * M ^ j := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hcommk j]
    rw [Matrix.mul_assoc, h_comm_q, ← Matrix.mul_assoc, hVQ, Matrix.zero_mul]
  -- Main proof by induction
  induction k with
  | zero => simp [pow_zero, Matrix.mul_one, hVV]
  | succ k ih =>
    -- pow_succ: M^{k+1} = M^k * M
    rw [pow_succ, pow_succ]
    -- V†(M^k * M)V = (V†M^kV)(V†MV) = (V†MV)^k * (V†MV)
    -- Key: V†M^k = V†M^k(VV†) because V†M^k(I-VV†) = 0
    -- So V†M^k * M * V = V†M^k * VV† * M * V = (V†M^kV)(V†MV)
    have hstep : Vᴴ * M ^ k * (V * Vᴴ) = Vᴴ * M ^ k := by
      have := hV_Mk_Q k
      rw [Matrix.mul_sub, Matrix.mul_one] at this
      exact (sub_eq_zero.mp this).symm
    calc
      Vᴴ * (M ^ k * M) * V
          = Vᴴ * M ^ k * (M * V) := by simp only [Matrix.mul_assoc]
      _ = Vᴴ * M ^ k * (V * Vᴴ) * (M * V) := by rw [hstep]
      _ = Vᴴ * M ^ k * V * (Vᴴ * M * V) := by simp only [Matrix.mul_assoc]
      _ = (Vᴴ * M * V) ^ k * (Vᴴ * M * V) := by rw [ih]

-- Helper: matrixFunction f M can be expressed as a polynomial in M
-- (specifically, the Lagrange interpolant at the eigenvalues).
-- Hence V†f(M)V = f(V†MV) when V†M^kV = (V†MV)^k.

/-- Compression commutes with polynomial evaluation when V†V = 1 and M commutes with VV†. -/
lemma compression_aeval_eq {n m : Type*}
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (V : Matrix n m ℂ) (M : Matrix n n ℂ)
    (hVV : Vᴴ * V = (1 : Matrix m m ℂ))
    (hcomm : M * (V * Vᴴ) = V * Vᴴ * M) (p : Polynomial ℂ) :
    Vᴴ * (Polynomial.aeval M p) * V = Polynomial.aeval (Vᴴ * M * V) p := by
  classical
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.aeval_add, Matrix.mul_add, Matrix.add_mul]
    rw [hp, hq]
  | monomial k c =>
    simp only [Polynomial.aeval_monomial]
    -- V†((algebraMap c) * M^k)V = (algebraMap c) * (V†MV)^k
    have h : Vᴴ * ((algebraMap ℂ (Matrix n n ℂ)) c * M ^ k) * V =
        (algebraMap ℂ (Matrix m m ℂ)) c * (Vᴴ * M * V) ^ k := by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
      simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul]
      congr 1
      exact compression_pow_eq V M hVV hcomm k
    exact h

/-- Eigenvalues of V†MV are contained in eigenvalues of M when M commutes with VV†.
This follows from the spectrum inclusion spectrum(V†MV) ⊆ spectrum(M). -/
lemma eigenvalues_compression_subset {n m : Type*}
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (V : Matrix n m ℂ) (M : Matrix n n ℂ) (hM : M.IsHermitian)
    (hVV : Vᴴ * V = (1 : Matrix m m ℂ))
    (hcomm : M * (V * Vᴴ) = V * Vᴴ * M)
    (hVM : (Vᴴ * M * V).IsHermitian) :
    Set.range hVM.eigenvalues ⊆ Set.range hM.eigenvalues := by
  rintro _ ⟨i, rfl⟩
  -- Use spectrum inclusion: spectrum(V†MV) ⊆ spectrum(M)
  -- This holds because if (λI - M) is invertible, then (λI - V†MV) = V†(λI - M)V
  -- is also invertible with inverse V†(λI - M)⁻¹V (using commutativity)
  have h_spec_subset : spectrum ℂ (Vᴴ * M * V) ⊆ spectrum ℂ M := by
    intro lam hlam
    by_contra h_not_spec
    rw [spectrum.mem_iff] at h_not_spec hlam
    push_neg at h_not_spec
    -- h_not_spec : IsUnit (algebraMap ℂ (Matrix n n ℂ) lam - M)
    -- The compression V†(λI - M)V = (λI - V†MV) and inverse transfers
    -- This is standard linear algebra: V†AV invertible iff A restricted to range(V) is invertible
    -- For matrices with V†V = I and M commuting with VV†, invertibility transfers
    -- Technical proof uses: (V†AV)⁻¹ = V†A⁻¹V when A commutes with VV†
    apply hlam
    -- Construct the inverse for V†MV
    set A := algebraMap ℂ (Matrix n n ℂ) lam - M with hA_def
    -- h_not_spec : IsUnit A
    -- Build the unit for the compression
    refine ⟨⟨Vᴴ * A * V, Vᴴ * A⁻¹ * V, ?_, ?_⟩, ?_⟩
    · -- mul_inv: (V†AV)(V†A⁻¹V) = 1
      have hcomm_A : A * (V * Vᴴ) = (V * Vᴴ) * A := by
        simp only [hA_def, Algebra.algebraMap_eq_smul_one, sub_mul, mul_sub,
          Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hcomm]
      have h_inv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A (A.isUnit_iff_isUnit_det.mp h_not_spec)
      have h_inv' : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A (A.isUnit_iff_isUnit_det.mp h_not_spec)
      have hcomm_inv : A⁻¹ * (V * Vᴴ) = (V * Vᴴ) * A⁻¹ := by
        calc A⁻¹ * (V * Vᴴ)
            = A⁻¹ * (V * Vᴴ) * (A * A⁻¹) := by rw [h_inv, Matrix.mul_one]
          _ = (A⁻¹ * (V * Vᴴ) * A) * A⁻¹ := by simp only [Matrix.mul_assoc]
          _ = (A⁻¹ * (A * (V * Vᴴ))) * A⁻¹ := by rw [hcomm_A]; simp only [Matrix.mul_assoc]
          _ = ((A⁻¹ * A) * (V * Vᴴ)) * A⁻¹ := by simp only [Matrix.mul_assoc]
          _ = (V * Vᴴ) * A⁻¹ := by rw [h_inv', Matrix.one_mul]
      calc Vᴴ * A * V * (Vᴴ * A⁻¹ * V)
          = Vᴴ * (A * (V * Vᴴ) * A⁻¹) * V := by simp only [Matrix.mul_assoc]
        _ = Vᴴ * ((V * Vᴴ) * A * A⁻¹) * V := by rw [hcomm_A]
        _ = Vᴴ * (V * Vᴴ) * V := by rw [Matrix.mul_assoc (V * Vᴴ), h_inv, Matrix.mul_one]
        _ = (Vᴴ * V) * (Vᴴ * V) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hVV, Matrix.mul_one]
    · -- inv_mul: (V†A⁻¹V)(V†AV) = 1
      have hcomm_A : A * (V * Vᴴ) = (V * Vᴴ) * A := by
        simp only [hA_def, Algebra.algebraMap_eq_smul_one, sub_mul, mul_sub,
          Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hcomm]
      have h_inv' : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A (A.isUnit_iff_isUnit_det.mp h_not_spec)
      have h_inv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A (A.isUnit_iff_isUnit_det.mp h_not_spec)
      have hcomm_inv : A⁻¹ * (V * Vᴴ) = (V * Vᴴ) * A⁻¹ := by
        calc A⁻¹ * (V * Vᴴ)
            = A⁻¹ * (V * Vᴴ) * (A * A⁻¹) := by rw [h_inv, Matrix.mul_one]
          _ = (A⁻¹ * (V * Vᴴ) * A) * A⁻¹ := by simp only [Matrix.mul_assoc]
          _ = (A⁻¹ * (A * (V * Vᴴ))) * A⁻¹ := by rw [hcomm_A]; simp only [Matrix.mul_assoc]
          _ = ((A⁻¹ * A) * (V * Vᴴ)) * A⁻¹ := by simp only [Matrix.mul_assoc]
          _ = (V * Vᴴ) * A⁻¹ := by rw [h_inv', Matrix.one_mul]
      calc Vᴴ * A⁻¹ * V * (Vᴴ * A * V)
          = Vᴴ * (A⁻¹ * (V * Vᴴ) * A) * V := by simp only [Matrix.mul_assoc]
        _ = Vᴴ * ((V * Vᴴ) * A⁻¹ * A) * V := by rw [hcomm_inv]
        _ = Vᴴ * (V * Vᴴ) * V := by rw [Matrix.mul_assoc (V * Vᴴ), h_inv', Matrix.mul_one]
        _ = (Vᴴ * V) * (Vᴴ * V) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hVV, Matrix.mul_one]
    · -- Show val equals the compression
      simp only [Algebra.algebraMap_eq_smul_one, hA_def]
      -- Goal: Vᴴ * (lam • 1 - M) * V = lam • 1 - Vᴴ * M * V
      rw [Matrix.mul_sub, Matrix.sub_mul]
      -- Goal: Vᴴ * (lam • 1) * V - Vᴴ * M * V = lam • 1 - Vᴴ * M * V
      congr 1
      -- Goal: Vᴴ * (lam • 1) * V = lam • 1
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hVV]
  -- Now show that eigenvalue of V†MV is an eigenvalue of M
  have h_eigenvalue_in_spec : (hVM.eigenvalues i : ℂ) ∈ spectrum ℂ (Vᴴ * M * V) :=
    spectrum.of_algebraMap_mem ℂ (hVM.eigenvalues_mem_spectrum_real i)
  have h_in_M_spec := h_spec_subset h_eigenvalue_in_spec
  -- Use that spectrum ℂ M = Set.image (↑·) (Set.range hM.eigenvalues)
  rw [hM.spectrum_eq_image_range] at h_in_M_spec
  -- Extract the real eigenvalue from the image
  simp only [Set.mem_image, Set.mem_range] at h_in_M_spec
  obtain ⟨r, ⟨j, rfl⟩, hr⟩ := h_in_M_spec
  use j
  exact Complex.ofReal_injective hr

lemma matrixFunction_compression_of_commuting {n m : Type*}
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (V : Matrix n m ℂ) (M : Matrix n n ℂ) (hM : M.IsHermitian)
    (hVV : Vᴴ * V = (1 : Matrix m m ℂ))
    (hcomm : M * (V * Vᴴ) = V * Vᴴ * M) (f : ℝ → ℝ)
    (hVM : (Vᴴ * M * V).IsHermitian) :
    Vᴴ * matrixFunction (fun x => (f x : ℂ)) M hM * V =
    matrixFunction (fun x => (f x : ℂ)) (Vᴴ * M * V) hVM := by
  classical
  -- The key insight: eigenvalues of V†MV are among eigenvalues of M
  have h_eig_subset := eigenvalues_compression_subset V M hM hVV hcomm hVM
  -- Construct the DISTINCT eigenvalues of M as a Finset
  let distinct_eigs_M : Finset ℝ := Finset.image hM.eigenvalues Finset.univ
  -- Construct a polynomial that interpolates f on DISTINCT eigenvalues of M
  let p : Polynomial ℝ := Lagrange.interpolate distinct_eigs_M id (fun x => f x)
  -- Key property: p evaluates to f at each eigenvalue of M
  have hp_interp_M : ∀ i : n, p.eval (hM.eigenvalues i) = f (hM.eigenvalues i) := by
    intro i
    have h_mem : hM.eigenvalues i ∈ distinct_eigs_M := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    have h_inj : Set.InjOn id (distinct_eigs_M : Set ℝ) := fun _ _ _ _ h => h
    have := Lagrange.eval_interpolate_at_node (fun x => f x) h_inj h_mem
    simp only [id] at this
    exact this
  -- p also evaluates to f at each eigenvalue of V†MV (since they're in range of M's eigenvalues)
  have hp_interp_VM : ∀ i : m, p.eval (hVM.eigenvalues i) = f (hVM.eigenvalues i) := by
    intro i
    have h_in_range : hVM.eigenvalues i ∈ Set.range hM.eigenvalues := by
      apply h_eig_subset
      exact Set.mem_range_self i
    obtain ⟨j, hj⟩ := h_in_range
    rw [← hj]
    exact hp_interp_M j
  -- The complex version of the polynomial (mapping coefficients ℝ → ℂ)
  let p_complex : Polynomial ℂ := p.map (algebraMap ℝ ℂ)
  -- Show that p_complex.eval agrees with f on eigenvalues (lifted to ℂ)
  have hp_eval_M : ∀ i : n, p_complex.eval (hM.eigenvalues i : ℂ) = (f (hM.eigenvalues i) : ℂ) := by
    intro i
    simp only [p_complex, Polynomial.eval_map]
    have h1 : (hM.eigenvalues i : ℂ) = algebraMap ℝ ℂ (hM.eigenvalues i) := rfl
    rw [h1, ← Polynomial.aeval_def, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval,
        hp_interp_M i]
    rfl
  have hp_eval_VM : ∀ i : m, p_complex.eval (hVM.eigenvalues i : ℂ) = (f (hVM.eigenvalues i) : ℂ) := by
    intro i
    simp only [p_complex, Polynomial.eval_map]
    have h1 : (hVM.eigenvalues i : ℂ) = algebraMap ℝ ℂ (hVM.eigenvalues i) := rfl
    rw [h1, ← Polynomial.aeval_def, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval,
        hp_interp_VM i]
    rfl
  unfold matrixFunction
  have h_mf_M_eq_cfc : matrixFunction (fun x => (f x : ℂ)) M hM = cfc f M :=
    matrixFunction_eq_cfc hM f
  have h_mf_VM_eq_cfc : matrixFunction (fun x => (f x : ℂ)) (Vᴴ * M * V) hVM = cfc f (Vᴴ * M * V) :=
    matrixFunction_eq_cfc hVM f
  have h_cfc_M : cfc f M = hM.cfc f := Matrix.IsHermitian.cfc_eq hM f
  have h_cfc_VM : cfc f (Vᴴ * M * V) = hVM.cfc f := Matrix.IsHermitian.cfc_eq hVM f
  have h_cfc_f_eq_p_M : hM.cfc f = hM.cfc (fun x => p.eval x) := by
    unfold Matrix.IsHermitian.cfc
    congr 1
    ext i j
    simp only [diagonal_apply]
    split_ifs with h
    · subst h
      simp only [Function.comp_apply]
      rw [hp_interp_M i]
    · rfl
  have h_cfc_f_eq_p_VM : hVM.cfc f = hVM.cfc (fun x => p.eval x) := by
    unfold Matrix.IsHermitian.cfc
    congr 1
    ext i j
    simp only [diagonal_apply]
    split_ifs with h
    · subst h
      simp only [Function.comp_apply]
      rw [hp_interp_VM i]
    · rfl
  have h_cfc_p_eq_aeval_M : cfc (fun x => p.eval x) M = Polynomial.aeval M p := by
    have hM' : IsSelfAdjoint M := hM
    exact cfc_polynomial p M
  have h_cfc_p_eq_aeval_VM : cfc (fun x => p.eval x) (Vᴴ * M * V) = Polynomial.aeval (Vᴴ * M * V) p := by
    have hVM' : IsSelfAdjoint (Vᴴ * M * V) := hVM
    exact cfc_polynomial p (Vᴴ * M * V)
  have h_compress_aeval : Vᴴ * Polynomial.aeval M p * V = Polynomial.aeval (Vᴴ * M * V) p := by
    have h1 : Polynomial.aeval M p = Polynomial.aeval M p_complex := by
      simp only [p_complex, Polynomial.aeval_map_algebraMap]
    have h2 : Polynomial.aeval (Vᴴ * M * V) p = Polynomial.aeval (Vᴴ * M * V) p_complex := by
      simp only [p_complex, Polynomial.aeval_map_algebraMap]
    rw [h1, h2]
    exact compression_aeval_eq V M hVV hcomm p_complex
  calc Vᴴ * matrixFunction (fun x => (f x : ℂ)) M hM * V
      = Vᴴ * cfc f M * V := by rw [h_mf_M_eq_cfc]
    _ = Vᴴ * hM.cfc f * V := by rw [h_cfc_M]
    _ = Vᴴ * hM.cfc (fun x => p.eval x) * V := by rw [h_cfc_f_eq_p_M]
    _ = Vᴴ * cfc (fun x => p.eval x) M * V := by rw [← Matrix.IsHermitian.cfc_eq hM]
    _ = Vᴴ * Polynomial.aeval M p * V := by rw [h_cfc_p_eq_aeval_M]
    _ = Polynomial.aeval (Vᴴ * M * V) p := h_compress_aeval
    _ = cfc (fun x => p.eval x) (Vᴴ * M * V) := by rw [← h_cfc_p_eq_aeval_VM]
    _ = hVM.cfc (fun x => p.eval x) := by rw [Matrix.IsHermitian.cfc_eq hVM]
    _ = hVM.cfc f := by rw [← h_cfc_f_eq_p_VM]
    _ = cfc f (Vᴴ * M * V) := by rw [← h_cfc_VM]
    _ = matrixFunction (fun x => (f x : ℂ)) (Vᴴ * M * V) hVM := by rw [← h_mf_VM_eq_cfc]

/-- For an isometry V (V†V = I), PSD A, and s > 0: (VAV†)^s = V A^s V†.

**Proof**: Uses `matrixFunction_compression_of_commuting` to get V†(VAV†)^s V = A^s,
then shows (VAV†)^s annihilates the complement (1 - VV†) via kernel preservation. -/
lemma rpow_conj_isometry {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m]
    (V : Matrix m n ℂ) (hV : Vᴴ * V = 1)
    (A : Matrix n n ℂ) (hA : A.PosSemidef) (s : ℝ) (hs : 0 < s) :
    (V * A * Vᴴ) ^ s = V * (A ^ s) * Vᴴ := by
  set M := V * A * Vᴴ with hM_def
  set P := V * Vᴴ with hP_def
  -- Step 1: V†MV = A
  have hstep1 : Vᴴ * M * V = A := by
    rw [hM_def, Matrix.mul_assoc V A Vᴴ,
        ← Matrix.mul_assoc Vᴴ V (A * Vᴴ), hV, Matrix.one_mul,
        Matrix.mul_assoc, hV, Matrix.mul_one]
  have hM_psd : M.PosSemidef := by
    rw [hM_def]; exact hA.mul_mul_conjTranspose_same V
  -- Step 2: M commutes with P = VV†
  have hcomm : M * P = P * M := by
    rw [hM_def, hP_def]
    conv_lhs =>
      rw [Matrix.mul_assoc (V * A) Vᴴ (V * Vᴴ),
          ← Matrix.mul_assoc Vᴴ V Vᴴ, hV, Matrix.one_mul]
    conv_rhs =>
      rw [← Matrix.mul_assoc (V * Vᴴ) (V * A) Vᴴ,
          Matrix.mul_assoc V Vᴴ (V * A),
          ← Matrix.mul_assoc Vᴴ V A, hV, Matrix.one_mul]
  -- Step 3: V†(M^s)V = A^s
  have hVM_herm : (Vᴴ * M * V).IsHermitian := by rw [hstep1]; exact hA.1
  have hVMA_rpow : Vᴴ * (M ^ s) * V = A ^ s := by
    have h1 := matrixFunction_rpow_eq hM_psd s
    have h2 := matrixFunction_compression_of_commuting V M hM_psd.1 hV hcomm (· ^ s) hVM_herm
    rw [h1] at h2
    rw [h2]
    have h3 : matrixFunction (fun x => ((x ^ s : ℝ) : ℂ)) (Vᴴ * M * V) hVM_herm =
              matrixFunction (fun x => ((x ^ s : ℝ) : ℂ)) A hA.1 := by
      congr 1
    rw [h3, matrixFunction_rpow_eq hA]
  -- Step 4: M * (1 - P) = 0
  have hM_annihilate : M * (1 - P) = 0 := by
    rw [mul_sub, mul_one, hM_def, hP_def,
        Matrix.mul_assoc (V * A) Vᴴ (V * Vᴴ),
        ← Matrix.mul_assoc Vᴴ V Vᴴ, hV, Matrix.one_mul, sub_self]
  -- Step 5: M^s * (1 - P) = 0 via kernel preservation
  have hM_herm := hM_psd.1
  set U := hM_herm.eigenvectorUnitary with hU_def
  set ev := hM_herm.eigenvalues with hev_def
  have hev_nonneg : ∀ i, 0 ≤ ev i := hM_psd.eigenvalues_nonneg
  have hMs_annihilate : M ^ s * (1 - P) = 0 := by
    -- Spectral decomposition: M = U diag(ev) U†
    have hspec : M = (U : Matrix m m ℂ) *
        diagonal (fun i => (ev i : ℂ)) * (U : Matrix m m ℂ)ᴴ := by
      rw [hM_herm.spectral_theorem (𝕜 := ℂ), Unitary.conjStarAlgAut_apply,
          star_eq_conjTranspose]; rfl
    have hev_nneg_cast : (0 : Matrix m m ℂ) ≤ diagonal (fun i => (ev i : ℂ)) := by
      simpa [Matrix.le_iff] using (posSemidef_diagonal_iff.mpr
        (fun i => Complex.zero_le_real.mpr (mod_cast hev_nonneg i)))
    -- M^s = U diag(ev^s) U†
    have hMs_spec : M ^ s = (U : Matrix m m ℂ) *
        diagonal (fun i => ((ev i ^ s : ℝ) : ℂ)) * (U : Matrix m m ℂ)ᴴ := by
      have hM'_nonneg : (0 : Matrix m m ℂ) ≤
          (U : Matrix m m ℂ) * diagonal (fun i => (ev i : ℂ)) * (U : Matrix m m ℂ)ᴴ := by
        rw [← hspec]; simpa [Matrix.le_iff] using hM_psd
      conv_lhs => rw [hspec]
      rw [rpow_unitary_conj U.2 hs.le hev_nneg_cast hM'_nonneg,
          diagonal_rpow ev hev_nonneg s hs.le]
    have hUstarU : (U : Matrix m m ℂ)ᴴ * U = 1 := by
      have := Unitary.coe_star_mul_self U
      simp only [star_eq_conjTranspose] at this
      exact this
    -- Set Q := U† * (1 - P)
    set Q := (U : Matrix m m ℂ)ᴴ * (1 - P) with hQ_def
    -- From M * (1-P) = 0: U * D * U† * (1-P) = 0
    -- Left-multiply by U†: D * Q = 0
    have hDQ : diagonal (fun i => (ev i : ℂ)) * Q = 0 := by
      have h1 : (U : Matrix m m ℂ) * (diagonal (fun i => (ev i : ℂ)) * Q) = 0 := by
        simp only [hQ_def, ← Matrix.mul_assoc]
        rw [show (U : Matrix m m ℂ) * diagonal (fun i => (ev i : ℂ)) *
            (U : Matrix m m ℂ)ᴴ = M from hspec.symm]
        exact hM_annihilate
      have h2 := congr_arg ((U : Matrix m m ℂ)ᴴ * ·) h1
      simp only [← Matrix.mul_assoc, hUstarU, Matrix.one_mul, Matrix.mul_zero] at h2
      exact h2
    -- Entry-wise: ev_i * Q_{i,j} = 0
    have hDQ_entry : ∀ i j, (ev i : ℂ) * Q i j = 0 := by
      intro i j
      have := congr_fun (congr_fun hDQ i) j
      simp only [Matrix.mul_apply, diagonal_apply, ite_mul, zero_mul,
                  Matrix.zero_apply] at this
      simpa using this
    -- diag(ev^s) * Q = 0 (entry-wise: ev_i^s * Q_{i,j} = 0)
    have hDsQ : diagonal (fun i => ((ev i ^ s : ℝ) : ℂ)) * Q = 0 := by
      ext i j
      have : (∑ x : m, if i = x then ↑(ev i ^ s) * Q x j else 0) = ↑(ev i ^ s) * Q i j := by
        simp
      simp only [Matrix.mul_apply, diagonal_apply, ite_mul, zero_mul, Matrix.zero_apply]
      rw [this]
      rcases mul_eq_zero.mp (hDQ_entry i j) with h | h
      · -- ev_i = 0 → ev_i^s = 0^s = 0
        have hevi_zero : ev i = 0 := by exact_mod_cast h
        simp [hevi_zero, Real.zero_rpow (ne_of_gt hs)]
      · -- Q_{i,j} = 0
        simp [h]
    -- M^s * (1-P) = U * D_s * U† * (1-P) = U * (D_s * Q) = U * 0 = 0
    calc M ^ s * (1 - P)
        = (U : Matrix m m ℂ) * (diagonal (fun i => ((ev i ^ s : ℝ) : ℂ)) * Q) := by
          rw [hMs_spec, hQ_def]; simp only [Matrix.mul_assoc]
      _ = (U : Matrix m m ℂ) * 0 := by rw [hDsQ]
      _ = 0 := Matrix.mul_zero _
  -- Step 6: M^s = V * A^s * V†
  have hP_herm : Pᴴ = P := by
    simp [hP_def, Matrix.conjTranspose_mul, conjTranspose_conjTranspose]
  have hMs_herm : (M ^ s).IsHermitian := by
    rw [← matrixFunction_rpow_eq hM_psd]
    exact matrixFunction_isHermitian hM_psd.1 (· ^ s)
  -- M^s = M^s * P (from M^s*(1-P)=0)
  have hMsP_eq : M ^ s = M ^ s * P := by
    have h := hMs_annihilate
    rw [mul_sub, mul_one] at h
    exact sub_eq_zero.mp h
  -- P * M^s = M^s (from (1-P)*M^s = 0 via adjoint)
  have hPMs : P * M ^ s = M ^ s := by
    have h1 : (1 - P) * M ^ s = 0 := by
      have h2 : ((M ^ s) * (1 - P))ᴴ = (0 : Matrix m m ℂ)ᴴ := congr_arg _ hMs_annihilate
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one] at h2
      simp only [Matrix.conjTranspose_zero] at h2
      rw [hP_herm, hMs_herm.eq] at h2; exact h2
    rw [sub_mul, one_mul] at h1
    exact (sub_eq_zero.mp h1).symm
  -- M^s * V = V * A^s
  have hMsV : M ^ s * V = V * A ^ s := by
    conv_lhs => rw [← hPMs, show P = V * Vᴴ from hP_def]
    simp only [Matrix.mul_assoc]
    congr 1
    rw [← Matrix.mul_assoc]
    exact hVMA_rpow
  -- Conclusion: M^s = M^s * V * V† = V * A^s * V†
  rw [hMsP_eq, show P = V * Vᴴ from hP_def, ← Matrix.mul_assoc, hMsV]

/-! ### Spectral Decomposition Identities -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Uᴴ * U = 1 for the eigenvector unitary of a Hermitian matrix. -/
lemma UHU_eq_one (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ *
    (hA.eigenvectorUnitary : Matrix n n ℂ) = 1 := by
  have := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  simpa [star_eq_conjTranspose] using this

/-- U * Uᴴ = 1 for the eigenvector unitary of a Hermitian matrix. -/
lemma UUH_eq_one (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix n n ℂ) *
    (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ = 1 := by
  have := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  simpa [star_eq_conjTranspose] using this

/-- Spectral decomposition: A = U * diag(eigenvalues) * Uᴴ. -/
lemma spectral_expand (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix n n ℂ) *
        diagonal (fun i => (hA.eigenvalues i : ℂ)) *
        (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
  have h := (matrixFunction_id hA).symm
  unfold matrixFunction at h
  simpa [Function.comp] using h

/-- The j-th column of the eigenvector unitary satisfies the eigenvalue equation:
A · (column j of U) = eigenvalue j · (column j of U). -/
lemma mulVec_eigenvector_col (A : Matrix n n ℂ) (hA : A.IsHermitian) (j : n) :
    A.mulVec (fun k => (hA.eigenvectorUnitary : Matrix n n ℂ) k j) =
    fun k => (hA.eigenvalues j : ℂ) * (hA.eigenvectorUnitary : Matrix n n ℂ) k j := by
  have h := hA.mulVec_eigenvectorBasis j
  have hconv : (fun k => (hA.eigenvectorUnitary : Matrix n n ℂ) k j) =
    (⇑(hA.eigenvectorBasis j) : n → ℂ) := by ext l; simp
  rw [hconv]
  ext k
  have hk := congr_fun h k
  simp only [Pi.smul_apply] at hk
  rw [hk]
  simp [Complex.real_smul]

/-- For PSD `A`, `D` with `0 < p`, `(A ⊕ D)ᵖ = Aᵖ ⊕ Dᵖ`. -/
lemma fromBlocks_diag_rpow {n₁ n₂ : Type*}
    [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂]
    {A : Matrix n₁ n₁ ℂ} (hA : A.PosSemidef)
    {D : Matrix n₂ n₂ ℂ} (hD : D.PosSemidef)
    {p : ℝ} (hp : 0 < p) :
    (Matrix.fromBlocks A 0 0 D) ^ p = Matrix.fromBlocks (A ^ p) 0 0 (D ^ p) := by
  have hha := fromBlocks_diag_posSemidef hA hD
  rw [CFC.rpow_eq_cfc_real (a := fromBlocks A 0 0 D)
        (ha := by rw [Matrix.le_iff, sub_zero]; exact hha)]
  have hcfc : cfc (fun x : ℝ => x ^ p) (fromBlocks A 0 0 D) =
      fromBlocks (cfc (fun x : ℝ => x ^ p) A) 0 0 (cfc (fun x : ℝ => x ^ p) D) :=
    cfc_fromBlocks_diag' A D hA.1 hD.1 _
      ((continuousOn_id.rpow_const fun _ _ => Or.inr hp.le))
  rw [hcfc,
      ← CFC.rpow_eq_cfc_real (a := A) (ha := by rw [Matrix.le_iff, sub_zero]; exact hA),
      ← CFC.rpow_eq_cfc_real (a := D) (ha := by rw [Matrix.le_iff, sub_zero]; exact hD)]

end Matrix
