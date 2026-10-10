/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.Matrix.Order

/-!
# Continuous functional calculus on diagonal matrices, unitary conjugates and Kronecker products

For a real diagonal matrix `diagonal (fun i => (d i : ℂ))`, the continuous functional
calculus `cfc f` reduces to the diagonal of the entrywise `f`, for **any** `f : ℝ → ℝ`:
the spectrum is finite, so continuity on it is automatic. Likewise `cfc f` commutes with
unitary conjugation of any self-adjoint matrix. The real powers `M ^ p` (`CFC.rpow`) of
diagonal matrices and of unitary conjugates are the special case `f = (· ^ p)`.

## Main results

* `Matrix.cfc_diagonal` — `cfc f (diagonal d) = diagonal (f ∘ d)` for `d : m → ℝ`.
* `Matrix.cfc_unitary_conj` — `cfc f` commutes with unitary conjugation of a self-adjoint
  matrix: `cfc f (U · M · Uᴴ) = U · cfc f M · Uᴴ`; `Matrix.cfc_unitary_conj_diagonal` combines it
  with `Matrix.cfc_diagonal`: `cfc f (W · diag d · Wᴴ) = W · diag (f ∘ d) · Wᴴ`.
* `Matrix.rpow_unitary_conj`, `Matrix.diagonal_rpow` — the real powers `(U · M · Uᴴ) ^ p`
  for `0 ≤ M` and `(diag d) ^ p` for `0 ≤ d`, for every real `p`;
  `Matrix.inv_transpose_rpow_mul_transpose_eq` — `((B⁻¹)ᵀ) ^ p · Bᵀ = (B ^ (1 - p))ᵀ` for
  positive definite `B`.
* `Matrix.cfc_kronecker_eq_add` — `f(A ⊗ B) = g₁(A) ⊗ h₁(B) + g₂(A) ⊗ h₂(B)` for Hermitian
  `A, B` whenever `f(xy) = g₁(x) h₁(y) + g₂(x) h₂(y)` on the spectra; special cases
  `Matrix.cfc_kronecker` (multiplicative `f`), `Matrix.cfc_kronecker_one`,
  `Matrix.cfc_one_kronecker`, `Matrix.PosSemidef.rpow_kronecker`
  (`(A ⊗ B)ᵖ = Aᵖ ⊗ Bᵖ`), `Matrix.cfc_log_kronecker` (`log(A ⊗ B) = log A ⊗ P_B + P_A ⊗ log B`)
  and `Matrix.PosDef.cfc_log_kronecker`.
-/

@[expose] public section

namespace Matrix

open scoped ComplexOrder

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- `cfc f` of a real diagonal matrix is the diagonal of the entrywise `f`, for **any**
`f : ℝ → ℝ`: the spectrum is finite, so no continuity hypothesis is needed.

Proof outline:
1. `diagonal : (m → ℂ) →⋆ₐ[ℝ] Matrix m m ℂ` is a continuous star algebra
   homomorphism (constructed inline), so `StarAlgHomClass.map_cfc` moves the CFC
   inside: `cfc f (diagonal dc) = diagonal (cfc f dc)`.
2. In the commutative Pi C*-algebra `m → ℂ`, CFC is pointwise (`cfc_map_pi`),
   and each entry `(d i : ℂ) = algebraMap ℝ ℂ (d i)` gives
   `cfc f (d i : ℂ) = (f (d i) : ℝ) : ℂ` via `cfc_algebraMap`. -/
lemma cfc_diagonal (f : ℝ → ℝ) (d : m → ℝ) :
    cfc f (diagonal (fun i => (d i : ℂ)) : Matrix m m ℂ) =
      diagonal (fun i => ((f (d i) : ℝ) : ℂ)) := by
  let : NormedRing (Matrix m m ℂ) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℝ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra
  let : NormedAlgebra ℂ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra
  let : CStarAlgebra (Matrix m m ℂ) := by
    simpa [CStarMatrix] using CStarMatrix.instCStarAlgebra (n := m) (A := ℂ)
  -- Provide CFC instances on `ℂ` and the Pi type `(m → ℂ)`.
  let : ContinuousFunctionalCalculus ℂ ℂ IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  let : ContinuousFunctionalCalculus ℝ ℂ IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  let : CStarAlgebra (m → ℂ) := inferInstance
  let : ContinuousFunctionalCalculus ℂ (m → ℂ) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  let : ContinuousFunctionalCalculus ℝ (m → ℂ) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  -- Pi self-adjoint
  let dc : m → ℂ := fun i => (d i : ℂ)
  have hdc_sa : IsSelfAdjoint dc := by
    rw [IsSelfAdjoint, Pi.star_def]; ext i; simp [dc, Complex.conj_ofReal]
  -- `diagonal` as star algebra hom (m → ℂ) →⋆ₐ[ℝ] Matrix m m ℂ
  let φ : (m → ℂ) →⋆ₐ[ℝ] Matrix m m ℂ :=
    { Matrix.diagonalAlgHom (R := ℝ) with
      map_star' := fun v => by
        change diagonal (star v) = (diagonal v)ᴴ
        rw [diagonal_conjTranspose] }
  have hφ_cont : Continuous φ := by
    have : (φ : (m → ℂ) → Matrix m m ℂ) = fun v => diagonal v := rfl
    rw [show ⇑φ = fun v => diagonal v from this]
    exact Continuous.matrix_diagonal continuous_id
  have hφ_dc : φ dc = diagonal dc := rfl
  have hφdc_sa : IsSelfAdjoint (φ dc) := by
    rw [IsSelfAdjoint, ← map_star φ]; exact congr_arg φ hdc_sa.star_eq
  -- Each component is self-adjoint (real-valued in ℂ).
  have hdc_i_sa : ∀ i, IsSelfAdjoint (dc i) := by
    intro i; simp [dc, IsSelfAdjoint, Complex.conj_ofReal]
  -- spectrum ℝ (dc i) ⊆ {d i} by CFC.spectrum_algebraMap_subset.
  have hspec_i : ∀ i, spectrum ℝ (dc i) ⊆ {d i} := by
    intro i
    change spectrum ℝ ((d i : ℂ)) ⊆ {d i}
    rw [show ((d i : ℂ) : ℂ) = algebraMap ℝ ℂ (d i) from rfl]
    exact CFC.spectrum_algebraMap_subset (d i)
  -- The union of the component spectra is finite, so `f` is continuous on it.
  have hcont_union : ContinuousOn f (⋃ i, spectrum ℝ (dc i)) := by
    refine ((Set.finite_range d).subset ?_).continuousOn f
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
    exact ⟨i, ((hspec_i i) hxi).symm⟩
  -- cfc on Pi computed componentwise.
  have h_pi_cfc : cfc f dc = fun i : m => ((f (d i) : ℝ) : ℂ) := by
    rw [cfc_map_pi (S := ℝ) f dc hcont_union hdc_sa hdc_i_sa]
    funext i
    simp only [dc]
    rw [show (d i : ℂ) = algebraMap ℝ ℂ (d i) from rfl, cfc_algebraMap (A := ℂ) (d i) f]
    rfl
  -- Apply StarAlgHom.map_cfc. Need ContinuousOn f (spectrum ℝ dc).
  have hspec_dc : spectrum ℝ dc ⊆ ⋃ i, spectrum ℝ (dc i) := by
    rw [Pi.spectrum_eq]
  have hcont_dc : ContinuousOn f (spectrum ℝ dc) := hcont_union.mono hspec_dc
  have h_map := StarAlgHomClass.map_cfc (R := ℝ) (S := ℝ)
    φ f dc hcont_dc hφ_cont hdc_sa hφdc_sa
  rw [← hφ_dc, ← h_map, h_pi_cfc]
  rfl

/-- `cfc f` commutes with unitary conjugation of a self-adjoint matrix, for any `f : ℝ → ℝ`:
`cfc f (U · M · Uᴴ) = U · cfc f M · Uᴴ`. The spectrum is finite, so no continuity hypothesis is
needed. This is `StarAlgHomClass.map_cfc` for the inner automorphism `Unitary.conjStarAlgAut`. -/
lemma cfc_unitary_conj {n : Type*} [Fintype n] [DecidableEq n] {U M : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (hM : IsSelfAdjoint M) (f : ℝ → ℝ) :
    cfc f (U * M * Uᴴ) = U * cfc f M * Uᴴ := by
  let : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℝ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  let : NormedAlgebra ℂ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  let : CStarAlgebra (Matrix n n ℂ) := by
    simpa [CStarMatrix] using CStarMatrix.instCStarAlgebra (n := n) (A := ℂ)
  let : ContinuousFunctionalCalculus ℂ (Matrix n n ℂ) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  let : ContinuousFunctionalCalculus ℝ (Matrix n n ℂ) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  have hUmem : U ∈ unitary (Matrix n n ℂ) := by
    rw [Unitary.mem_iff]
    exact ⟨Matrix.mem_unitaryGroup_iff'.mp hU, Matrix.mem_unitaryGroup_iff.mp hU⟩
  let φ := Unitary.conjStarAlgAut ℝ (Matrix n n ℂ) ⟨U, hUmem⟩
  have hφ : ∀ x, φ x = U * x * Uᴴ := fun x => by
    simp [φ, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose]
  have hφ_cont : Continuous φ := by
    rw [show ⇑φ = fun x => U * x * Uᴴ from funext hφ]
    exact (continuous_const.mul continuous_id).mul continuous_const
  have h_map := StarAlgHomClass.map_cfc (R := ℝ) (S := ℝ) φ f M
    (M.finite_real_spectrum.continuousOn f) hφ_cont hM (hM.map φ)
  rw [hφ, hφ] at h_map
  exact h_map.symm

/-- `cfc f` commutes with unitary conjugation of a real diagonal matrix, for any
`f : ℝ → ℝ`: `cfc f (W · diag d · Wᴴ) = W · diag (f ∘ d) · Wᴴ`. -/
lemma cfc_unitary_conj_diagonal
    {k : Type*} [Fintype k] [DecidableEq k]
    (W : unitary (Matrix k k ℂ)) (f : ℝ → ℝ) (d : k → ℝ) :
    cfc f
        ((W : Matrix k k ℂ) *
          diagonal (fun i => ((d i : ℝ) : ℂ)) * (W : Matrix k k ℂ)ᴴ) =
      (W : Matrix k k ℂ) *
        diagonal (fun i => ((f (d i) : ℝ) : ℂ)) * (W : Matrix k k ℂ)ᴴ := by
  have h_diag_sa : IsSelfAdjoint (diagonal (fun i => ((d i : ℝ) : ℂ)) : Matrix k k ℂ) := by
    rw [IsSelfAdjoint, star_eq_conjTranspose, diagonal_conjTranspose]
    congr 1
    funext i
    simp [Complex.conj_ofReal]
  rw [cfc_unitary_conj W.2 h_diag_sa f, cfc_diagonal f d]

/-! ### Real powers

`M ^ p` for a matrix `M` and `p : ℝ` is `CFC.rpow`, the functional calculus of `t ↦ t ^ p` on a
nonnegative matrix, and inherits the conventions `0 ^ 0 = 1` and `0 ^ p = 0` for `p ≠ 0` of
`Real.rpow`: for a singular `0 ≤ M`, `M ^ 0 = 1`, and for `p < 0`, `M ^ p` is the Moore–Penrose
power, inverse to `M ^ (-p)` on the range of `M` and `0` on its kernel. -/

section Rpow

open scoped MatrixOrder

/-- Real powers commute with unitary conjugation of a nonnegative matrix:
`(U M Uᴴ) ^ p = U M ^ p Uᴴ` for `0 ≤ M`, `U` unitary and every real `p`
(`Matrix.cfc_unitary_conj` for `t ↦ t ^ p`). -/
lemma rpow_unitary_conj {n : Type*} [Fintype n] [DecidableEq n]
    {U M : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ) {p : ℝ} (hM : 0 ≤ M) :
    (U * M * Uᴴ) ^ p = U * (M ^ p) * Uᴴ := by
  have hM' : 0 ≤ U * M * Uᴴ := star_right_conjugate_nonneg hM U
  rw [CFC.rpow_eq_cfc_real (ha := hM'), CFC.rpow_eq_cfc_real (ha := hM)]
  exact cfc_unitary_conj hU (IsSelfAdjoint.of_nonneg hM) _

/-- A real power of a diagonal matrix with nonnegative real entries is the diagonal of the
entrywise powers, for every real `p` (`Matrix.cfc_diagonal` for `t ↦ t ^ p`). -/
lemma diagonal_rpow {n : Type*} [Fintype n] [DecidableEq n]
    (d : n → ℝ) (hd : ∀ i, 0 ≤ d i) (p : ℝ) :
    (diagonal (fun i => (d i : ℂ))) ^ p = diagonal (fun i => ((d i ^ p : ℝ) : ℂ)) := by
  have hD : (0 : Matrix n n ℂ) ≤ diagonal (fun i => (d i : ℂ)) :=
    (posSemidef_diagonal_iff.mpr fun i => Complex.zero_le_real.mpr (hd i)).nonneg
  rw [CFC.rpow_eq_cfc_real (ha := hD)]
  exact cfc_diagonal (· ^ p) d

/-- For a positive definite matrix `B` and every real `p`,
`((B⁻¹)ᵀ) ^ p * Bᵀ = (B ^ (1 - p))ᵀ`. -/
lemma inv_transpose_rpow_mul_transpose_eq {m : Type*} [Fintype m] [DecidableEq m]
    (B : Matrix m m ℂ) (hB : B.PosDef) (p : ℝ) :
    ((B⁻¹)ᵀ) ^ p * Bᵀ = (B ^ (1 - p))ᵀ := by
  let : NormedRing (Matrix m m ℂ) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℝ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra
  let : NormedAlgebra ℂ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra
  let : CStarAlgebra (Matrix m m ℂ) := by
    simpa [CStarMatrix] using CStarMatrix.instCStarAlgebra (n := m) (A := ℂ)
  have hB_unit : IsUnit B := hB.isUnit
  have hB_det : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hB_unit
  have hBinv_herm : (B⁻¹).IsHermitian := by
    rw [Matrix.IsHermitian, conjTranspose_nonsing_inv, hB.1.eq]
  have hBinv_psd : (B⁻¹).PosSemidef := hB.posSemidef.inv
  -- Spectral decomposition of B⁻¹
  set UB := hBinv_herm.eigenvectorUnitary with hUB_def
  set dB := hBinv_herm.eigenvalues with hdB_def
  have hdB_nonneg : ∀ i, 0 ≤ dB i := hBinv_psd.eigenvalues_nonneg
  have hD_nonneg : (0 : Matrix m m ℂ) ≤ diagonal (RCLike.ofReal ∘ dB) :=
    (posSemidef_diagonal_iff.mpr fun i => RCLike.ofReal_nonneg.mpr (hdB_nonneg i)).nonneg
  have hSpec : B⁻¹ = (UB : Matrix m m ℂ) * diagonal (RCLike.ofReal ∘ dB) *
      (UB : Matrix m m ℂ)ᴴ := by
    rw [hBinv_herm.spectral_theorem (𝕜 := ℂ), Unitary.conjStarAlgAut_apply,
        star_eq_conjTranspose]
  have hD_rpow : diagonal (RCLike.ofReal ∘ dB) ^ p =
      diagonal (fun i => ((dB i ^ p : ℝ) : ℂ)) := by
    change diagonal (fun i => (dB i : ℂ)) ^ p = _
    exact diagonal_rpow dB hdB_nonneg p
  have hBinv_rpow_spec : (B⁻¹) ^ p = (UB : Matrix m m ℂ) *
      diagonal (fun i => ((dB i ^ p : ℝ) : ℂ)) * (UB : Matrix m m ℂ)ᴴ := by
    conv_lhs => rw [hSpec]
    rw [rpow_unitary_conj UB.2 hD_nonneg, hD_rpow]
  -- Transpose commutes with rpow for B⁻¹ via spectral decomposition
  have htr_rpow : ((B⁻¹)ᵀ) ^ p = ((B⁻¹) ^ p)ᵀ := by
    have hDt : (diagonal (RCLike.ofReal ∘ dB) : Matrix m m ℂ)ᵀ =
        diagonal (RCLike.ofReal ∘ dB) := by
      ext i j
      simp only [transpose_apply, diagonal_apply]
      by_cases h : i = j
      · subst h
        simp
      · simp [h, show ¬(j = i) from fun a => h a.symm]
    have hDpt : (diagonal (fun i => ((dB i ^ p : ℝ) : ℂ)))ᵀ =
        diagonal (fun i => ((dB i ^ p : ℝ) : ℂ)) := by
      ext i j
      simp only [transpose_apply, diagonal_apply]
      by_cases h : i = j
      · subst h
        simp
      · simp [h, show ¬(j = i) from fun a => h a.symm]
    have hWH_eq : ((UB : Matrix m m ℂ)ᴴ)ᵀᴴ = ((UB : Matrix m m ℂ))ᵀ := by
      ext i j
      simp [conjTranspose_apply, transpose_apply]
    have hW_unitary : ((UB : Matrix m m ℂ)ᴴ)ᵀ ∈ Matrix.unitaryGroup m ℂ := by
      rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose, hWH_eq]
      have hU_mul : (UB : Matrix m m ℂ)ᴴ * (UB : Matrix m m ℂ) = 1 := by
        have := Unitary.coe_star_mul_self UB
        simp only [star_eq_conjTranspose] at this
        exact this
      have h_prod := congr_arg Matrix.transpose hU_mul
      simp only [Matrix.transpose_mul, Matrix.transpose_one] at h_prod
      exact h_prod
    have hBinvT_spec : (B⁻¹)ᵀ = ((UB : Matrix m m ℂ)ᴴ)ᵀ *
        diagonal (RCLike.ofReal ∘ dB) * (((UB : Matrix m m ℂ)ᴴ)ᵀ)ᴴ := by
      rw [hWH_eq, hSpec]
      simp only [Matrix.transpose_mul, hDt, Matrix.mul_assoc]
    conv_lhs => rw [hBinvT_spec]
    rw [rpow_unitary_conj hW_unitary hD_nonneg, hD_rpow]
    rw [hBinv_rpow_spec]
    simp only [Matrix.transpose_mul, hDpt, Matrix.mul_assoc, hWH_eq]
  rw [htr_rpow, ← Matrix.transpose_mul]
  congr 1
  have hB_nonneg : (0 : Matrix m m ℂ) ≤ B := by
    simpa [Matrix.le_iff] using hB.posSemidef
  have hB_sp : IsStrictlyPositive B := hB.isStrictlyPositive
  have hBinv_cfc : B⁻¹ = B ^ (-1 : ℝ) := by
    have h1 : B ^ (-1 : ℝ) * B = 1 := by
      have := CFC.rpow_neg_mul_rpow (a := B) (1 : ℝ) hB_sp
      rwa [CFC.rpow_one B hB_nonneg] at this
    have h2 : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hB_det
    exact hB_unit.mul_right_cancel (h2.trans h1.symm)
  have hBinv_rpow : (B⁻¹) ^ p = B ^ (-p) := by
    rw [hBinv_cfc, CFC.rpow_rpow B (-1 : ℝ) p (by norm_num) hB_sp]
    congr 1
    ring
  rw [hBinv_rpow]
  have h_add : B ^ (1 + (-p)) = B ^ (1 : ℝ) * B ^ (-p) :=
    CFC.rpow_add (x := 1) (y := -p) hB_unit
  rw [CFC.rpow_one B hB_nonneg] at h_add
  rw [← h_add, show (1 + (-p) : ℝ) = 1 - p from by ring]

end Rpow

/-! ### Kronecker products

For Hermitian `A` and `B` with eigendecompositions `A = U diag a Uᴴ` and `B = V diag b Vᴴ`,
`A ⊗ₖ B = (U ⊗ₖ V) diag (aᵢ bⱼ) (U ⊗ₖ V)ᴴ`, so `cfc f (A ⊗ₖ B)` is computed from the products
of eigenvalues. Whenever `f (x y)` splits into products of functions of `x` and of `y` on the
spectra, `cfc f (A ⊗ₖ B)` splits accordingly (`Matrix.cfc_kronecker_eq_add`). -/

section Kronecker

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Kronecker MatrixOrder

/-- **Functional calculus of a Kronecker product.** For Hermitian `A`, `B` and functions with
`f (x y) = g₁ x h₁ y + g₂ x h₂ y` for `x ∈ spectrum ℝ A`, `y ∈ spectrum ℝ B`,
`f(A ⊗ B) = g₁(A) ⊗ h₁(B) + g₂(A) ⊗ h₂(B)`. -/
lemma cfc_kronecker_eq_add {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {f g₁ h₁ g₂ h₂ : ℝ → ℝ}
    (hf : ∀ x ∈ spectrum ℝ A, ∀ y ∈ spectrum ℝ B, f (x * y) = g₁ x * h₁ y + g₂ x * h₂ y) :
    cfc f (A ⊗ₖ B) = cfc g₁ A ⊗ₖ cfc h₁ B + cfc g₂ A ⊗ₖ cfc h₂ B := by
  set U : Matrix m m ℂ := (hA.eigenvectorUnitary : Matrix m m ℂ)
  set V : Matrix n n ℂ := (hB.eigenvectorUnitary : Matrix n n ℂ)
  let W : unitary (Matrix (m × n) (m × n) ℂ) :=
    ⟨U ⊗ₖ V, kronecker_mem_unitary hA.eigenvectorUnitary.2 hB.eigenvectorUnitary.2⟩
  have hconj : ∀ (a : m → ℝ) (b : n → ℝ),
      (U * diagonal (fun i => ((a i : ℝ) : ℂ)) * Uᴴ) ⊗ₖ
          (V * diagonal (fun j => ((b j : ℝ) : ℂ)) * Vᴴ) =
        (W : Matrix (m × n) (m × n) ℂ) * diagonal (fun p => ((a p.1 * b p.2 : ℝ) : ℂ)) *
          (W : Matrix (m × n) (m × n) ℂ)ᴴ := by
    intro a b
    simp only [W, conjTranspose_kronecker, mul_kronecker_mul, diagonal_kronecker_diagonal,
      Complex.ofReal_mul]
  have hspecA : ∀ g : ℝ → ℝ,
      cfc g A = U * diagonal (fun i => ((g (hA.eigenvalues i) : ℝ) : ℂ)) * Uᴴ := fun g => by
    rw [hA.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose]; rfl
  have hspecB : ∀ g : ℝ → ℝ,
      cfc g B = V * diagonal (fun i => ((g (hB.eigenvalues i) : ℝ) : ℂ)) * Vᴴ := fun g => by
    rw [hB.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose]; rfl
  have hAB : A ⊗ₖ B = (W : Matrix (m × n) (m × n) ℂ) *
      diagonal (fun p => ((hA.eigenvalues p.1 * hB.eigenvalues p.2 : ℝ) : ℂ)) *
        (W : Matrix (m × n) (m × n) ℂ)ᴴ := by
    rw [← hconj]
    have h1 := hspecA id
    have h2 := hspecB id
    rw [cfc_id ℝ A] at h1
    rw [cfc_id ℝ B] at h2
    exact congrArg₂ _ h1 h2
  rw [hAB, cfc_unitary_conj_diagonal, hspecA g₁, hspecB h₁, hspecA g₂,
    hspecB h₂, hconj, hconj, ← Matrix.add_mul, ← Matrix.mul_add, diagonal_add]
  congr 3
  funext p
  rw [hf _ (hA.eigenvalues_mem_spectrum_real p.1) _ (hB.eigenvalues_mem_spectrum_real p.2)]
  push_cast; ring

/-- For Hermitian `A`, `B` and `f` multiplicative on their spectra,
`f(A ⊗ B) = f(A) ⊗ f(B)`. -/
lemma cfc_kronecker {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {f : ℝ → ℝ}
    (hf : ∀ x ∈ spectrum ℝ A, ∀ y ∈ spectrum ℝ B, f (x * y) = f x * f y) :
    cfc f (A ⊗ₖ B) = cfc f A ⊗ₖ cfc f B := by
  rw [cfc_kronecker_eq_add hA hB (g₁ := f) (h₁ := f) (g₂ := fun _ => 0) (h₂ := fun _ => 0)
    fun x hx y hy => by rw [hf x hx y hy]; ring, cfc_const_zero ℝ, zero_kronecker, add_zero]

omit [Fintype n] in
private lemma eq_one_of_mem_spectrum_one [Fintype n] {y : ℝ}
    (hy : y ∈ spectrum ℝ (1 : Matrix n n ℂ)) : y = 1 := by
  rcases subsingleton_or_nontrivial (Matrix n n ℂ) with h | h
  · simp [spectrum.of_subsingleton] at hy
  · rwa [spectrum.one_eq, Set.mem_singleton_iff] at hy

/-- `f(A ⊗ 1) = f(A) ⊗ 1` for Hermitian `A` and any `f : ℝ → ℝ`. -/
lemma cfc_kronecker_one {A : Matrix m m ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f (A ⊗ₖ (1 : Matrix n n ℂ)) = cfc f A ⊗ₖ 1 := by
  rw [cfc_kronecker_eq_add hA isHermitian_one (g₁ := f) (h₁ := fun _ => 1) (g₂ := fun _ => 0)
    (h₂ := fun _ => 0) fun x _ y hy => by simp [eq_one_of_mem_spectrum_one hy],
    cfc_const_one ℝ (1 : Matrix n n ℂ) isHermitian_one.isSelfAdjoint, cfc_const_zero ℝ A,
    zero_kronecker, add_zero]

/-- `f(1 ⊗ B) = 1 ⊗ f(B)` for Hermitian `B` and any `f : ℝ → ℝ`. -/
lemma cfc_one_kronecker {B : Matrix n n ℂ} (hB : B.IsHermitian) (f : ℝ → ℝ) :
    cfc f ((1 : Matrix m m ℂ) ⊗ₖ B) = 1 ⊗ₖ cfc f B := by
  rw [cfc_kronecker_eq_add isHermitian_one hB (g₁ := fun _ => 1) (h₁ := f) (g₂ := fun _ => 0)
    (h₂ := fun _ => 0) fun x hx _ _ => by simp [eq_one_of_mem_spectrum_one hx],
    cfc_const_one ℝ (1 : Matrix m m ℂ) isHermitian_one.isSelfAdjoint, cfc_const_zero ℝ B,
    kronecker_zero, add_zero]

/-- Real powers distribute over Kronecker products of positive semidefinite matrices:
`(A ⊗ B)ᵖ = Aᵖ ⊗ Bᵖ` for every `p : ℝ` (including `p ≤ 0`, with Mathlib's `0 ^ p` convention). -/
lemma PosSemidef.rpow_kronecker {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (p : ℝ) :
    (A ⊗ₖ B) ^ p = (A ^ p) ⊗ₖ (B ^ p) := by
  rw [CFC.rpow_eq_cfc_real (hA.kronecker hB).nonneg, CFC.rpow_eq_cfc_real hA.nonneg,
    CFC.rpow_eq_cfc_real hB.nonneg]
  exact cfc_kronecker hA.1 hB.1 fun x hx y hy => Real.mul_rpow
    (spectrum_nonneg_of_nonneg hA.nonneg hx) (spectrum_nonneg_of_nonneg hB.nonneg hy)

/-- **Logarithm of a Kronecker product.** For Hermitian `A`, `B`,
`log(A ⊗ B) = log A ⊗ P_B + P_A ⊗ log B`, where `P_X = cfc (x ↦ if x = 0 then 0 else 1) X` is
the support projection. With Mathlib's `Real.log 0 = 0`, no invertibility is needed. -/
lemma cfc_log_kronecker {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    cfc Real.log (A ⊗ₖ B) =
      cfc Real.log A ⊗ₖ cfc (fun y : ℝ => if y = 0 then (0 : ℝ) else 1) B +
        cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) A ⊗ₖ cfc Real.log B := by
  refine cfc_kronecker_eq_add hA hB fun x _ y _ => ?_
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  simp [hx, hy, Real.log_mul hx hy]

/-- For positive definite `A`, `B`, `log(A ⊗ B) = log A ⊗ 1 + 1 ⊗ log B`. -/
lemma PosDef.cfc_log_kronecker {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hA : A.PosDef) (hB : B.PosDef) :
    cfc Real.log (A ⊗ₖ B) = cfc Real.log A ⊗ₖ 1 + 1 ⊗ₖ cfc Real.log B := by
  rw [cfc_kronecker_eq_add hA.isHermitian hB.isHermitian (g₁ := Real.log) (h₁ := fun _ => 1)
    (g₂ := fun _ => 1) (h₂ := Real.log) fun x hx y hy => by
      rw [Real.log_mul (hA.isStrictlyPositive.spectrum_pos hx).ne'
        (hB.isStrictlyPositive.spectrum_pos hy).ne']
      ring,
    cfc_const_one ℝ B hB.isHermitian.isSelfAdjoint,
    cfc_const_one ℝ A hA.isHermitian.isSelfAdjoint]

end Kronecker

end Matrix
