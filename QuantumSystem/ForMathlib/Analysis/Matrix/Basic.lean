/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Block-Matrix and Real-Power Lemmas

This file collects lemmas on complex matrices: block-diagonal matrix-vector products, real powers
under unitary conjugation and of diagonal matrices, positive semidefiniteness of block-diagonal
matrices, and the trace of a block matrix.

## Main results

- `Matrix.fromBlocks_mulVec_inl`: block-diagonal matrix-vector product on the left block.
- `Matrix.fromBlocks_mulVec_inr`: block-diagonal matrix-vector product on the right block.
- `Matrix.rpow_unitary_conj`: CFC rpow commutes with unitary conjugation,
  (UMU†)ᵖ = U Mᵖ U†.
- `Matrix.diagonal_rpow`: rpow of a diagonal matrix equals the diagonal of componentwise rpow.
- `Matrix.inv_transpose_rpow_mul_transpose_eq`: for PD B and every real p,
  ((B⁻¹)ᵀ)ᵖ · Bᵀ = (B¹⁻ᵖ)ᵀ.

## Positive Definite / Positive Semidefinite results

- `Matrix.fromBlocks_diag_posSemidef`: `fromBlocks A 0 0 D` is PSD when A and D are PSD.

## Block matrices

- `Matrix.trace_fromBlocks`: Tr(fromBlocks A B C D) = Tr A + Tr D.
-/

@[expose] public section

namespace Matrix

open scoped MatrixOrder ComplexOrder

/-- For a block-diagonal matrix `fromBlocks A 0 0 D`, the left block of the product `M *ᵥ v`
depends only on `A` and the left part of `v`: `(M *ᵥ v) (inl i) = (A *ᵥ vₗ) i`. -/
lemma fromBlocks_mulVec_inl {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m m ℂ) (D : Matrix n n ℂ) (v : m ⊕ n → ℂ) (i : m) :
    (Matrix.fromBlocks A 0 0 D *ᵥ v) (Sum.inl i) = (A *ᵥ fun j => v (Sum.inl j)) i := by
  classical
  -- Split the sum over the sum type and use block entry formulas.
  change (∑ j, Matrix.fromBlocks A 0 0 D (Sum.inl i) j * v j) = _
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂]

/-- For a block-diagonal matrix `fromBlocks A 0 0 D`, the right block of the product `M *ᵥ v`
depends only on `D` and the right part of `v`: `(M *ᵥ v) (inr i) = (D *ᵥ vᵣ) i`. -/
lemma fromBlocks_mulVec_inr {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m m ℂ) (D : Matrix n n ℂ) (v : m ⊕ n → ℂ) (i : n) :
    (Matrix.fromBlocks A 0 0 D *ᵥ v) (Sum.inr i) = (D *ᵥ fun j => v (Sum.inr j)) i := by
  classical
  -- Split the sum over the sum type and use block entry formulas.
  change (∑ j, Matrix.fromBlocks A 0 0 D (Sum.inr i) j * v j) = _
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, fromBlocks_apply₂₁, fromBlocks_apply₂₂]

/-- CFC rpow commutes with unitary conjugation: (U M U†)^p = U M^p U†.
This follows from `StarAlgHomClass.map_cfc` applied to the inner automorphism. -/
lemma rpow_unitary_conj {n : Type*} [Fintype n] [DecidableEq n]
    {U M : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ)
    {p : ℝ} (hM : 0 ≤ M) (hM' : 0 ≤ U * M * Uᴴ := by cfc_tac) :
    (U * M * Uᴴ) ^ p = U * (M ^ p) * Uᴴ := by
  let : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℝ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  let : NormedAlgebra ℂ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  let : NormedSpace ℝ (Matrix n n ℂ) := NormedAlgebra.toNormedSpace _
  let : IsBoundedSMul ℝ (Matrix n n ℂ) := NormedSpace.toIsBoundedSMul (𝕜 := ℝ)
  let : ContinuousSMul ℝ (Matrix n n ℂ) := IsBoundedSMul.continuousSMul
  let : CStarAlgebra (Matrix n n ℂ) := by
    simpa [CStarMatrix] using CStarMatrix.instCStarAlgebra (n := n) (A := ℂ)
  -- Convert to unitary element
  have hUmem : U ∈ unitary (Matrix n n ℂ) := by
    rw [Unitary.mem_iff]
    exact ⟨Matrix.mem_unitaryGroup_iff'.mp hU, Matrix.mem_unitaryGroup_iff.mp hU⟩
  let u : unitary (Matrix n n ℂ) := ⟨U, hUmem⟩
  let φ := Unitary.conjStarAlgAut ℝ (Matrix n n ℂ) u
  have hφ_apply : ∀ x, φ x = U * x * Uᴴ := by
    intro x; simp [φ, Unitary.conjStarAlgAut_apply, u, star_eq_conjTranspose]
  rw [← hφ_apply M, ← hφ_apply (M ^ p)]
  -- Convert rpow to CFC
  rw [CFC.rpow_eq_cfc_real (a := M) (ha := hM)]
  rw [CFC.rpow_eq_cfc_real (a := φ M) (ha := by rw [hφ_apply]; exact hM')]
  have hcont : ContinuousOn (· ^ p) (spectrum ℝ M) := M.finite_real_spectrum.continuousOn _
  -- Continuity of φ follows from finite-dimensionality.  Build the FiniteDimensional
  -- instance locally inside the `have`-block so the instance database stays focused.
  -- φ is x ↦ U * x * Uᴴ, which is continuous as a composition of multiplications.
  have hφ_cont : Continuous φ := by
    have hfun : (φ : Matrix n n ℂ → Matrix n n ℂ) = fun x => U * x * Uᴴ :=
      funext hφ_apply
    rw [show ⇑φ = fun x => U * x * Uᴴ from hfun]
    exact (continuous_const.mul continuous_id).mul continuous_const
  -- IsSelfAdjoint φ M follows from M being self-adjoint and φ preserving star
  have hM_sa : IsSelfAdjoint M := by
    have : M.PosSemidef := by simpa [Matrix.le_iff] using hM
    exact this.1.isSelfAdjoint
  have hφM_sa : IsSelfAdjoint (φ M) := by
    rw [IsSelfAdjoint]
    rw [← map_star φ]
    exact congr_arg φ hM_sa.star_eq
  symm
  exact StarAlgHomClass.map_cfc (R := ℝ) (S := ℝ) φ (· ^ p) M hcont hφ_cont

/-- rpow of a diagonal matrix with nonneg real entries equals the diagonal
of componentwise rpow.

Proof outline:
1. Express Dᵖ via `CFC.rpow_eq_cfc_real`, reducing to showing
   `cfc (· ^ p) (diagonal d) = diagonal (fun i => d i ^ p)`.
2. `diagonal : (n → ℂ) →⋆ₐ[ℝ] Matrix n n ℂ` is a continuous star algebra
   homomorphism (constructed inline), so `StarAlgHomClass.map_cfc` moves the CFC
   inside: `cfc (· ^ p) (diagonal dc) = diagonal (cfc (· ^ p) dc)`.
3. In the commutative Pi C*-algebra `n → ℂ`, CFC is pointwise
   (`cfc_map_pi`), and each entry `(d i : ℂ) = algebraMap ℝ ℂ (d i)` gives
   `cfc (· ^ p) (d i : ℂ) = (d i ^ p : ℝ) : ℂ` via `cfc_algebraMap`. -/
lemma diagonal_rpow {n : Type*} [Fintype n] [DecidableEq n]
    (d : n → ℝ) (hd : ∀ i, 0 ≤ d i) (p : ℝ) :
    (diagonal (fun i => (d i : ℂ))) ^ p = diagonal (fun i => ((d i ^ p : ℝ) : ℂ)) := by
  let : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℝ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  let : NormedAlgebra ℂ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  let : NormedSpace ℝ (Matrix n n ℂ) := NormedAlgebra.toNormedSpace _
  let : IsBoundedSMul ℝ (Matrix n n ℂ) := NormedSpace.toIsBoundedSMul (𝕜 := ℝ)
  let : ContinuousSMul ℝ (Matrix n n ℂ) := IsBoundedSMul.continuousSMul
  have : Module.Free ℝ ℂ := Module.Free.of_divisionRing _ _
  have : Module.Finite ℝ ℂ := inferInstance
  have : Module.Finite ℝ (Matrix n n ℂ) := Module.Finite.matrix
  let : CStarAlgebra (Matrix n n ℂ) := by
    simpa [CStarMatrix] using CStarMatrix.instCStarAlgebra (n := n) (A := ℂ)
  let : NormedSpace ℝ (n → ℂ) := inferInstance
  let : IsBoundedSMul ℝ (n → ℂ) := NormedSpace.toIsBoundedSMul (𝕜 := ℝ)
  let : ContinuousSMul ℝ (n → ℂ) := IsBoundedSMul.continuousSMul
  have : Module.Free ℝ ℂ := Module.Free.of_divisionRing _ _
  have : Module.Finite ℝ ℂ := inferInstance
  have : Module.Finite ℝ (n → ℂ) := Module.Finite.pi
  -- Provide CFC instances for the Pi C*-algebra `n → ℂ` and the fiber `ℂ`.  These are not
  -- registered globally in Mathlib (`IsStarNormal.instContinuousFunctionalCalculus` is a
  -- `theorem` with `attribute [local instance]` only), but follow once the appropriate
  -- normed/CStar structure is in scope.
  let : ContinuousFunctionalCalculus ℂ ℂ IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  let : ContinuousFunctionalCalculus ℝ ℂ IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  let : CStarAlgebra (n → ℂ) := inferInstance
  let : ContinuousFunctionalCalculus ℂ (n → ℂ) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  let : ContinuousFunctionalCalculus ℝ (n → ℂ) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  let dc : n → ℂ := fun i => (d i : ℂ)
  have hD_psd : (diagonal dc).PosSemidef := by
    rw [posSemidef_diagonal_iff]
    intro i; simp only [dc, Complex.zero_le_real]; exact_mod_cast hd i
  have hD : (0 : Matrix n n ℂ) ≤ diagonal dc := by
    simpa [Matrix.le_iff] using hD_psd
  rw [show (fun i => (d i : ℂ)) = dc from rfl, CFC.rpow_eq_cfc_real (ha := hD)]
  -- Build `diagonal` as a star algebra hom (n → ℂ) →⋆ₐ[ℝ] Matrix n n ℂ inline.
  let φ : (n → ℂ) →⋆ₐ[ℝ] Matrix n n ℂ :=
    { Matrix.diagonalAlgHom (R := ℝ) with
      map_star' := fun v => by
        change diagonal (star v) = (diagonal v)ᴴ
        rw [diagonal_conjTranspose] }
  have hφ_cont : Continuous φ := by
    have : (φ : (n → ℂ) → Matrix n n ℂ) = fun v => diagonal v := rfl
    rw [show ⇑φ = fun v => diagonal v from this]
    exact Continuous.matrix_diagonal continuous_id
  -- `dc` is self-adjoint: all entries are real, hence equal to their conjugate.
  have hdc_sa : IsSelfAdjoint dc := by
    rw [IsSelfAdjoint, Pi.star_def]; ext i; simp [dc, Complex.conj_ofReal]
  have hφdc_sa : IsSelfAdjoint (φ dc) := by
    rw [IsSelfAdjoint, ← map_star φ]; exact congr_arg φ hdc_sa.star_eq
  -- CFC commutes with the star algebra hom φ.
  -- The spectrum of `dc` is the finite set of its entries (`Pi.spectrum_eq`).
  have hdc_fin' : (⋃ i, spectrum ℝ (dc i)).Finite :=
    Set.finite_iUnion fun i => by
      rw [show dc i = algebraMap ℝ ℂ (d i) from rfl, spectrum.scalar_eq]
      exact Set.finite_singleton _
  have hdc_fin : (spectrum ℝ dc).Finite := (Pi.spectrum_eq (R := ℝ) dc) ▸ hdc_fin'
  have h_map := StarAlgHomClass.map_cfc (R := ℝ) (S := ℝ) φ (· ^ p) dc
    (hdc_fin.continuousOn _) hφ_cont hdc_sa hφdc_sa
  -- φ dc = diagonal dc, so rewrite both sides.
  have hφ_dc : φ dc = diagonal dc := rfl
  rw [← hφ_dc, ← h_map]
  -- Goal: φ (cfc (· ^ p) dc) = diagonal (fun i => (d i ^ p : ℝ) : ℂ)
  change diagonal (cfc (· ^ p) dc) = diagonal (fun i => ((d i ^ p : ℝ) : ℂ))
  -- In the Pi C*-algebra n → ℂ, CFC is pointwise.
  rw [cfc_map_pi (S := ℝ) (· ^ p) dc (hdc_fin'.continuousOn _)]
  congr 1; funext i
  simp only [dc]
  rw [show (d i : ℂ) = algebraMap ℝ ℂ (d i) from rfl, cfc_algebraMap (A := ℂ) (d i) (· ^ p)]
  rfl

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
  have hBinvT_psd : ((B⁻¹)ᵀ).PosSemidef := hBinv_psd.transpose
  have hBinvT_nonneg : (0 : Matrix m m ℂ) ≤ (B⁻¹)ᵀ := by
    simpa [Matrix.le_iff] using hBinvT_psd
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
    rw [rpow_unitary_conj UB.2 hD_nonneg
        (hM' := by rw [← hSpec]; simpa [Matrix.le_iff] using hBinv_psd), hD_rpow]
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
    have hBinvT_nonneg' : 0 ≤ ((UB : Matrix m m ℂ)ᴴ)ᵀ *
        diagonal (RCLike.ofReal ∘ dB) * (((UB : Matrix m m ℂ)ᴴ)ᵀ)ᴴ := by
      rw [← hBinvT_spec]
      exact hBinvT_nonneg
    conv_lhs => rw [hBinvT_spec]
    rw [rpow_unitary_conj hW_unitary hD_nonneg (hM' := hBinvT_nonneg'), hD_rpow]
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

/-! ### Positive Definite and Positive Semidefinite Matrices -/

/-- Block diagonal `fromBlocks A 0 0 D` is PSD when both `A` and `D` are PSD. -/
lemma fromBlocks_diag_posSemidef {n₁ n₂ : Type*}
    [Finite n₁] [Finite n₂]
    {A : Matrix n₁ n₁ ℂ} (hA : A.PosSemidef)
    {D : Matrix n₂ n₂ ℂ} (hD : D.PosSemidef) :
    (Matrix.fromBlocks A 0 0 D).PosSemidef := by
  let := Fintype.ofFinite n₁
  let := Fintype.ofFinite n₂
  refine PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.IsHermitian.fromBlocks hA.1 (by simp) hD.1) ?_
  intro v
  have heq : star v ⬝ᵥ (Matrix.fromBlocks A 0 0 D *ᵥ v) =
      star (fun i => v (Sum.inl i)) ⬝ᵥ (A *ᵥ fun i => v (Sum.inl i)) +
      star (fun i => v (Sum.inr i)) ⬝ᵥ (D *ᵥ fun i => v (Sum.inr i)) := by
    simp [dotProduct, Fintype.sum_sum_type, fromBlocks_mulVec_inl, fromBlocks_mulVec_inr]
  rw [heq]
  exact add_nonneg (hA.dotProduct_mulVec_nonneg _) (hD.dotProduct_mulVec_nonneg _)

/-- Trace of a `fromBlocks` matrix decomposes as sum of diagonal block traces. -/
lemma trace_fromBlocks {n₁ n₂ : Type*} [Fintype n₁] [Fintype n₂]
    (A : Matrix n₁ n₁ ℂ) (B : Matrix n₁ n₂ ℂ) (C : Matrix n₂ n₁ ℂ) (D : Matrix n₂ n₂ ℂ) :
    (Matrix.fromBlocks A B C D).trace = A.trace + D.trace := by
  unfold Matrix.trace
  rw [Fintype.sum_sum_type]
  simp

end Matrix
