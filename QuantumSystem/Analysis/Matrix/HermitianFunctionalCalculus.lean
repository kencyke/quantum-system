module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.LinearAlgebra.Lagrange
public import QuantumSystem.ForMathlib.Analysis.Matrix.Basic
public import QuantumSystem.ForMathlib.Analysis.Matrix.Hermitian
public import QuantumSystem.ForMathlib.LinearAlgebra.Matrix.StarAlgEquiv

/-!
# Matrix Functional Calculus and Foundational Inequalities

This file develops the core tools for matrix analysis. Foundational lemmas about Hermitian
matrices, positive semidefiniteness, block-matrix identities, and the Löwner order are in
`QuantumSystem.ForMathlib.Analysis.Matrix.*`.

All functional calculus is expressed directly through Mathlib's continuous functional
calculus `cfc`; the spectral expansion `cfc f A = U diag(f(λᵢ)) Uᴴ` is `cfc_spectral_eq`.

## Main results

### Continuous Functional Calculus
- `cfc_spectral_eq`: spectral decomposition `cfc f A = U diag(f(λᵢ)) Uᴴ`
  for Hermitian A with eigendecomposition A = UΛ Uᴴ.
- `trace_cfc`, `trace_mul_cfc`: trace formulas `Tr(f(A)) = ∑ f(λᵢ)` and `Tr(A·f(A)) = ∑ λᵢ f(λᵢ)`.
- `cfc_isHermitian`, `mul_cfc_isHermitian`: `f(A)` and `A·f(A)` are Hermitian for real `f`.
- `cfc_add_const_eq`, `cfc_inv_add_const`, `cfc_resolvent`: affine / resolvent identities.
- `cfc_compression_of_commuting`: `Vᴴ f(M) V = f(Vᴴ M V)` for an isometry commuting with `M`.
- Matrix logarithm `cfc Real.log`: `cfc_spectral_eq`, `cfc_log_spectral_eq`, `cfc_log_map_starAlgEquiv`.
- Special functions: `matrixSqrt`, `matrixInvSqrt` defined via `CFC.rpow`.

### Hermitian and PSD Structure
- `matrixSqrt`: the matrix square root A¹⁄² for PSD A (`= A ^ (1/2 : ℝ)`).
- `matrixInvSqrt`: the matrix inverse square root A⁻¹⁄² for PD A (`= A ^ (-1/2 : ℝ)`).
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

/-- `cfc f A` of a Hermitian matrix expands into the spectral decomposition
`U · diag(f(λᵢ)) · Uᴴ` attached to the chosen Hermitian proof. -/
lemma cfc_spectral_eq {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f A =
      (hA.eigenvectorUnitary : Matrix m m ℂ) *
        diagonal (fun i => ((f (hA.eigenvalues i) : ℝ) : ℂ)) *
        (hA.eigenvectorUnitary : Matrix m m ℂ)ᴴ := by
  rw [Matrix.IsHermitian.cfc_eq hA f]
  unfold Matrix.IsHermitian.cfc
  rw [Unitary.conjStarAlgAut_apply]
  simp only [Function.comp_def, star_eq_conjTranspose]
  rfl

/-- Trace of `cfc f A` equals the sum of `f` over the eigenvalues of `A`. -/
lemma trace_cfc {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, (f (hA.eigenvalues i) : ℂ) := by
  rw [cfc_spectral_eq hA f, trace_mul_cycle]
  have h := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  simp only [star_eq_conjTranspose] at h
  rw [h, Matrix.one_mul]
  exact trace_diagonal _

/-- `f(A)` is Hermitian for Hermitian `A` and real `f` (continuous functional calculus). -/
lemma cfc_isHermitian {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).IsHermitian := by
  rw [cfc_spectral_eq hA f]
  have hD : (diagonal (fun i => ((f (hA.eigenvalues i) : ℝ) : ℂ))).IsHermitian := by
    rw [isHermitian_diagonal_iff]
    intro i
    exact Complex.conj_ofReal _
  rw [IsHermitian]
  simp only [conjTranspose_mul, conjTranspose_conjTranspose]
  conv_rhs => rw [mul_assoc]
  rw [hD]

/-- `Tr(A · f(A)) = ∑ᵢ λᵢ · f(λᵢ)` for the continuous functional calculus. -/
lemma trace_mul_cfc {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (A * cfc f A).trace = ∑ i, ((hA.eigenvalues i : ℂ) * (f (hA.eigenvalues i) : ℂ)) := by
  have hfin : (spectrum ℝ A).Finite := by
    rw [hA.spectrum_real_eq_range_eigenvalues]; exact Set.finite_range _
  have hcont_id : ContinuousOn (fun x : ℝ => x) (spectrum ℝ A) := continuousOn_id
  have hcont_f : ContinuousOn f (spectrum ℝ A) := hfin.continuousOn f
  have hsa : IsSelfAdjoint A := hA
  have hmul : A * cfc f A = cfc (fun x => x * f x) A := by
    rw [cfc_mul (fun x => x) f A hcont_id hcont_f, cfc_id' (R := ℝ) (a := A) hsa]
  rw [hmul, trace_cfc hA (fun x => x * f x)]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

/-- `cfc (· + t) A = A + t • I` for Hermitian `A` via the continuous functional calculus. -/
lemma cfc_add_const_eq {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.IsHermitian) (t : ℝ) :
    cfc (fun x => x + t) A = A + (t : ℂ) • 1 := by
  have hsa : IsSelfAdjoint A := hA
  have hcont_id : ContinuousOn (fun x : ℝ => x) (spectrum ℝ A) := continuousOn_id
  have hcont_c : ContinuousOn (fun _ : ℝ => t) (spectrum ℝ A) := continuousOn_const
  rw [cfc_add A (fun x => x) (fun _ => t) hcont_id hcont_c, cfc_id' (R := ℝ) (a := A) hsa,
      cfc_const t A, Algebra.algebraMap_eq_smul_one]
  congr 1

/-- `cfc ((· + t)⁻¹) A = (A + t • I)⁻¹` for PSD `A` and `t > 0`. -/
lemma cfc_inv_add_const {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.PosSemidef) {t : ℝ} (ht : 0 < t) :
    cfc (fun x : ℝ => (x + t)⁻¹) A = (A + (t : ℂ) • 1)⁻¹ := by
  classical
  have hA' : A.IsHermitian := hA.1
  have hneq : ∀ x ∈ spectrum ℝ A, (x + t) ≠ 0 := by
    intro x hx
    have hx' : x ∈ Set.range hA'.eigenvalues := by
      simpa [hA'.spectrum_real_eq_range_eigenvalues] using hx
    rcases hx' with ⟨i, rfl⟩
    linarith [hA.eigenvalues_nonneg i]
  have hcfcinv : cfc (fun x : ℝ => (x + t)⁻¹) A = Ring.inverse (cfc (fun x : ℝ => x + t) A) := by
    simpa using (cfc_inv (A := Matrix m m ℂ) (f := fun x : ℝ => x + t) (a := A) hneq)
  have hcfcaff : cfc (fun x : ℝ => x + t) A = A + (t : ℂ) • 1 := cfc_add_const_eq hA' t
  have hposdef : (A + (t : ℂ) • 1).PosDef := PosSemidef.add_smul_one_posDef hA ht
  have hunit : IsUnit (A + (t : ℂ) • 1) := hposdef.isUnit
  let _ := hunit.invertible
  have hcfcaff_inv : Ring.inverse (cfc (fun x : ℝ => x + t) A) = (A + (t : ℂ) • 1)⁻¹ := by
    simpa [hcfcaff] using (Ring.inverse_unit hunit.unit)
  rw [hcfcinv, hcfcaff_inv]

/-- Resolvent form for `cfc` on PSD matrices:
`cfc (1 - r·(· + r)⁻¹) A = I - r·(A + r·I)⁻¹` for `r > 0`. -/
lemma cfc_resolvent {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.PosSemidef) {r : ℝ} (hr : 0 < r) :
    cfc (fun x => 1 - r * (x + r)⁻¹) A =
      (1 : Matrix m m ℂ) - (r : ℂ) • (A + (r : ℂ) • 1)⁻¹ := by
  have hA' : A.IsHermitian := hA.1
  have hneq : ∀ x ∈ spectrum ℝ A, (x + r) ≠ 0 := by
    intro x hx
    have hx' : x ∈ Set.range hA'.eigenvalues := by
      simpa [hA'.spectrum_real_eq_range_eigenvalues] using hx
    rcases hx' with ⟨i, rfl⟩
    linarith [hA.eigenvalues_nonneg i]
  have hcont_inv : ContinuousOn (fun x : ℝ => (x + r)⁻¹) (spectrum ℝ A) :=
    ContinuousOn.inv₀ (by fun_prop) hneq
  have hcontc : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (spectrum ℝ A) := continuousOn_const
  have hcontri : ContinuousOn (fun x : ℝ => r * (x + r)⁻¹) (spectrum ℝ A) :=
    continuousOn_const.mul hcont_inv
  rw [cfc_sub (fun _ : ℝ => (1 : ℝ)) (fun x => r * (x + r)⁻¹) A hcontc hcontri,
      cfc_const (1 : ℝ) A, map_one,
      cfc_const_mul r (fun x : ℝ => (x + r)⁻¹) A hcont_inv,
      cfc_inv_add_const hA hr]
  congr 1

/-- The product `A · f(A)` is Hermitian for Hermitian `A` and real `f`. -/
lemma mul_cfc_isHermitian {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (A * cfc f A).IsHermitian := by
  have hsa : IsSelfAdjoint A := hA
  have hcomm : Commute A (cfc f A) := (hsa.commute_cfc (Commute.refl A) f).symm
  exact (hA.commute_iff (cfc_isHermitian hA f)).mp hcomm

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

/-- `cfc Real.log` of a Hermitian matrix (the matrix logarithm) expands into the spectral
decomposition attached to the chosen Hermitian proof. -/
lemma cfc_log_spectral_eq {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.IsHermitian) :
    cfc Real.log A =
      (hA.eigenvectorUnitary : Matrix m m ℂ) *
        diagonal (fun i => ((Real.log (hA.eigenvalues i) : ℝ) : ℂ)) *
        (hA.eigenvectorUnitary : Matrix m m ℂ)ᴴ :=
  cfc_spectral_eq hA Real.log

/-- The matrix logarithm `cfc Real.log` commutes with any `*-`algebra equivalence between
complex matrix algebras on PosDef matrices. Continuity is automatic in finite dimensions. -/
theorem cfc_log_map_starAlgEquiv {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] {M : Matrix m m ℂ} (hM : M.PosDef)
    (φ : Matrix m m ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ) :
    cfc Real.log (φ M) = φ (cfc Real.log M) := by
  letI : NormedRing (Matrix m m ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℂ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra
  letI : CStarAlgebra (Matrix m m ℂ) := by
    simpa [CStarMatrix] using CStarMatrix.instCStarAlgebra (n := m) (A := ℂ)
  letI : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℂ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  letI : CStarAlgebra (Matrix n n ℂ) := by
    simpa [CStarMatrix] using CStarMatrix.instCStarAlgebra (n := n) (A := ℂ)
  -- View `φ` as an ℝ-`StarAlgHom` to apply `StarAlgHomClass.map_cfc`.
  let ψ : Matrix m m ℂ →⋆ₐ[ℝ] Matrix n n ℂ :=
    { toAlgHom := (φ.toAlgEquiv.restrictScalars ℝ).toAlgHom
      map_star' := fun X => map_star φ X }
  have h_ψ_apply : ∀ X, ψ X = φ X := fun _ => rfl
  have hψ_cont : Continuous ψ := by
    -- ψ x = φ x, so it suffices to show φ is continuous.
    -- Continuity follows entrywise: each entry `(φ A) i j` is a ℂ-linear functional in `A`,
    -- and ℂ-linear maps on a finite-dimensional ℂ-space are automatically continuous.
    have hcont_φ : Continuous (φ : Matrix m m ℂ → Matrix n n ℂ) := by
      refine continuous_matrix fun i j => ?_
      -- The entry map is ℂ-linear; package it as a `LinearMap`.
      let g : Matrix m m ℂ →ₗ[ℂ] ℂ :=
        { toFun := fun A => (φ A) i j
          map_add' := fun A B => by simp
          map_smul' := fun c A => by simp }
      change Continuous fun A => g A
      exact g.continuous_of_finiteDimensional
    exact hcont_φ
  have hM_sa : IsSelfAdjoint M := hM.1
  have hψM_sa : IsSelfAdjoint (ψ M) := by
    rw [IsSelfAdjoint, ← map_star ψ]
    exact congr_arg ψ hM_sa.star_eq
  have h_cont : ContinuousOn Real.log (spectrum ℝ M) := by
    refine Real.continuousOn_log.mono ?_
    intro x hx
    rw [hM.1.spectrum_real_eq_range_eigenvalues] at hx
    rcases hx with ⟨i, rfl⟩
    exact ne_of_gt (hM.eigenvalues_pos i)
  have h_map := StarAlgHomClass.map_cfc (R := ℝ) (S := ℝ) ψ Real.log M
    h_cont hψ_cont hM_sa hψM_sa
  rw [h_ψ_apply, h_ψ_apply] at h_map
  exact h_map.symm

/-- Matrix inverse square root via the continuous functional calculus for PD matrices. -/
noncomputable def matrixInvSqrt {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℂ) (_hA : A.PosDef) : Matrix m m ℂ :=
  cfc (fun x => Real.rpow x (-1 / 2 : ℝ)) A

/-- `matrixInvSqrt A = A ^ (-1/2)` via `CFC.rpow`. -/
lemma matrixInvSqrt_eq_rpow {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.PosDef) :
    matrixInvSqrt A hA = A ^ (-1 / 2 : ℝ) :=
  (CFC.rpow_eq_cfc_real (a := A) (ha := by rw [Matrix.le_iff, sub_zero]; exact hA.posSemidef)).symm

/-- The matrix inverse square root of a PD matrix is Hermitian. -/
lemma matrixInvSqrt_isHermitian {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.PosDef) :
    (matrixInvSqrt A hA).IsHermitian := by
  rw [matrixInvSqrt]
  exact cfc_isHermitian hA.1 (fun x => Real.rpow x (-1 / 2 : ℝ))

/-- For a positive definite matrix `A`, `A^{-1/2} * A * A^{-1/2} = I`. -/
lemma matrixInvSqrt_mul_self {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.PosDef) :
    matrixInvSqrt A hA * A * matrixInvSqrt A hA = 1 := by
  have hS : matrixInvSqrt A hA = A ^ (-1 / 2 : ℝ) := by
    exact matrixInvSqrt_eq_rpow hA
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

/-- Matrix square root via the continuous functional calculus for PSD matrices. -/
noncomputable def matrixSqrt {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℂ) (_hA : A.PosSemidef) : Matrix m m ℂ :=
  cfc (fun x => Real.rpow x (1 / 2 : ℝ)) A

/-- `matrixSqrt A = A ^ (1/2)` via `CFC.rpow`. -/
lemma matrixSqrt_eq_rpow {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.PosSemidef) :
    matrixSqrt A hA = A ^ (1 / 2 : ℝ) :=
  (CFC.rpow_eq_cfc_real (a := A) (ha := by rw [Matrix.le_iff, sub_zero]; exact hA)).symm

/-- The matrix square root of a PSD matrix is Hermitian. -/
lemma matrixSqrt_isHermitian {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.PosSemidef) :
    (matrixSqrt A hA).IsHermitian := by
  rw [matrixSqrt]
  exact cfc_isHermitian hA.1 (fun x => Real.rpow x (1 / 2 : ℝ))

/-- For a positive semidefinite matrix `A`, `A^{1/2} * A^{1/2} = A`. -/
lemma matrixSqrt_mul_self_posSemidef {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.PosSemidef) :
    matrixSqrt A hA * matrixSqrt A hA = A := by
  classical
  -- Use the spectral decomposition and diagonal computation.
  rw [matrixSqrt, cfc_spectral_eq hA.1 (fun x => Real.rpow x (1 / 2 : ℝ))]
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
    exact matrixSqrt_eq_rpow hA.posSemidef
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
    exact matrixSqrt_eq_rpow hA.posSemidef
  have hSi : matrixInvSqrt A hA = A ^ (-1 / 2 : ℝ) := by
    exact matrixInvSqrt_eq_rpow hA
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
    exact matrixSqrt_eq_rpow hA.posSemidef
  have hSi : matrixInvSqrt A hA = A ^ (-1 / 2 : ℝ) := by
    exact matrixInvSqrt_eq_rpow hA
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
commutativity. Since matrixInvSqrt R = R^{-1/2} (by CFC.rpow), and
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
  have hRinv_eq : matrixInvSqrt R hR = R ^ (-1 / 2 : ℝ) := matrixInvSqrt_eq_rpow hR
  rw [hRinv_eq]
  -- R^{-1/2} = cfc(x^{-1/2}, R), so it commutes with L since L commutes with R
  have hR0 : (0 : Matrix n n ℂ) ≤ R := by simpa [Matrix.le_iff] using hR.posSemidef
  rw [CFC.rpow_eq_cfc_real (a := R) (ha := hR0)]
  have hcommute : Commute R L := hcomm.symm
  exact Commute.cfc_real hcommute _

/-- CFC commutes with unitary conjugation using `Unitary.conjStarAlgAut`. -/
lemma cfc_unitary_conjugation' {m : Type*} [Fintype m] [DecidableEq m]
    (U : unitary (Matrix m m ℂ)) (M : Matrix m m ℂ)
    (hM : IsSelfAdjoint M) (f : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ M)) :
    (U : Matrix m m ℂ) * cfc f M * star (U : Matrix m m ℂ) =
    cfc f ((U : Matrix m m ℂ) * M * star (U : Matrix m m ℂ)) := by
  change (Unitary.conjStarAlgAut ℝ _ U) (cfc f M) =
    cfc f ((Unitary.conjStarAlgAut ℝ _ U) M)
  have hcont : Continuous (Unitary.conjStarAlgAut ℝ (Matrix m m ℂ) U) := by
    have happly : ∀ x, Unitary.conjStarAlgAut ℝ (Matrix m m ℂ) U x =
        (U : Matrix m m ℂ) * x * (U : Matrix m m ℂ)ᴴ := by
      intro x; simp [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose]
    rw [show (Unitary.conjStarAlgAut ℝ (Matrix m m ℂ) U : Matrix m m ℂ → Matrix m m ℂ) =
        fun x => (U : Matrix m m ℂ) * x * (U : Matrix m m ℂ)ᴴ from funext happly]
    exact (continuous_const.mul continuous_id).mul continuous_const
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
  letI : ContinuousFunctionalCalculus ℂ (Matrix m m ℂ) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  letI : CStarAlgebra (Matrix m m ℂ × Matrix m m ℂ) := inferInstance
  letI : ContinuousFunctionalCalculus ℂ (Matrix m m ℂ × Matrix m m ℂ) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  letI : ContinuousFunctionalCalculus ℝ (Matrix m m ℂ × Matrix m m ℂ) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
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
  letI : ContinuousFunctionalCalculus ℂ (Matrix n n ℂ) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  letI : ContinuousFunctionalCalculus ℂ (Matrix m m ℂ) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  letI : CStarAlgebra (Matrix n n ℂ × Matrix m m ℂ) := inferInstance
  letI : ContinuousFunctionalCalculus ℂ (Matrix n n ℂ × Matrix m m ℂ) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  letI : ContinuousFunctionalCalculus ℝ (Matrix n n ℂ × Matrix m m ℂ) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
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

section JensenConvexity

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

-- Helper: cfc f M can be expressed as a polynomial in M
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
    push Not at h_not_spec
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

/-- Compression commutes with the continuous functional calculus when `Vᴴ V = 1` and `M`
commutes with `V Vᴴ`: `Vᴴ · f(M) · V = f(Vᴴ M V)`. -/
lemma cfc_compression_of_commuting {n m : Type*}
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (V : Matrix n m ℂ) (M : Matrix n n ℂ) (hM : M.IsHermitian)
    (hVV : Vᴴ * V = (1 : Matrix m m ℂ))
    (hcomm : M * (V * Vᴴ) = V * Vᴴ * M) (f : ℝ → ℝ)
    (hVM : (Vᴴ * M * V).IsHermitian) :
    Vᴴ * cfc f M * V = cfc f (Vᴴ * M * V) := by
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
  calc Vᴴ * cfc f M * V
      = Vᴴ * hM.cfc f * V := by rw [h_cfc_M]
    _ = Vᴴ * hM.cfc (fun x => p.eval x) * V := by rw [h_cfc_f_eq_p_M]
    _ = Vᴴ * cfc (fun x => p.eval x) M * V := by rw [← Matrix.IsHermitian.cfc_eq hM]
    _ = Vᴴ * Polynomial.aeval M p * V := by rw [h_cfc_p_eq_aeval_M]
    _ = Polynomial.aeval (Vᴴ * M * V) p := h_compress_aeval
    _ = cfc (fun x => p.eval x) (Vᴴ * M * V) := by rw [← h_cfc_p_eq_aeval_VM]
    _ = hVM.cfc (fun x => p.eval x) := by rw [Matrix.IsHermitian.cfc_eq hVM]
    _ = hVM.cfc f := by rw [← h_cfc_f_eq_p_VM]
    _ = cfc f (Vᴴ * M * V) := by rw [← h_cfc_VM]

/-- For an isometry V (V†V = I), PSD A, and s > 0: (VAV†)^s = V A^s V†.

**Proof**: Uses `cfc_compression_of_commuting` to get V†(VAV†)^s V = A^s,
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
    have hM0 : (0 : Matrix m m ℂ) ≤ M := by rw [Matrix.le_iff, sub_zero]; exact hM_psd
    have hA0 : (0 : Matrix n n ℂ) ≤ A := by rw [Matrix.le_iff, sub_zero]; exact hA
    rw [CFC.rpow_eq_cfc_real (a := M) (ha := hM0),
        cfc_compression_of_commuting V M hM_psd.1 hV hcomm (fun x : ℝ => x ^ s) hVM_herm,
        hstep1, ← CFC.rpow_eq_cfc_real (a := A) (ha := hA0)]
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
    rw [CFC.rpow_eq_cfc_real (a := M) (ha := by rw [Matrix.le_iff, sub_zero]; exact hM_psd)]
    exact cfc_isHermitian hM_psd.1 (fun x : ℝ => x ^ s)
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

end JensenConvexity

/-! ### Spectral Decomposition Identities -/

section SpectralIdentities

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
  have h := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose] at h
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

end SpectralIdentities

end Matrix
