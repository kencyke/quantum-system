module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Block-Matrix Lemmas

This file collects block-matrix identities used in the HPJ and related inequalities.

## Main results

- `Matrix.fromBlocks_mulVec_inl`: block-diagonal matrix-vector product on the left block.
- `Matrix.fromBlocks_mulVec_inr`: block-diagonal matrix-vector product on the right block.
- `Matrix.fromRows_compress_blockDiag`:
  `(fromRows A B)ᴴ * fromBlocks(T₁, 0, 0, T₂) * (fromRows A B) = AᴴT₁A + BᴴT₂B`.
- `Matrix.inner_conjTranspose_mul_self_mulVec`: `x†(VᴴV)x = (Vx)†(Vx)`.
- `Matrix.inner_compress_mulVec`: `x†(VᴴAV)x = (Vx)†A(Vx)`.
- `Matrix.rpow_unitary_conj`: CFC rpow commutes with unitary conjugation,
  (UMU†)ᵖ = U Mᵖ U†.
- `Matrix.diagonal_rpow`: rpow of a diagonal matrix equals the diagonal of componentwise rpow.
- `Matrix.inv_transpose_rpow_mul_transpose_eq`: for PD B and p ≥ 0,
  ((B⁻¹)ᵀ)ᵖ · Bᵀ = (B¹⁻ᵖ)ᵀ.

## Positive Definite / Positive Semidefinite results

- `Matrix.posDef_one`: the identity matrix is positive definite.
- `Matrix.posSemidef_one`: the identity matrix is positive semidefinite.
- `Matrix.fromBlocks_inv_posSemidef`: the block matrix [A, I; I, A⁻¹]
  is positive semidefinite when A is positive definite.
- `Matrix.fromRows_conjTranspose_mul_self`: VᴴV = AᴴA + BᴴB for V = [A; B].
- `Matrix.PosSemidef.diagonal_ofReal`: a diagonal matrix with nonneg real entries is positive
  semidefinite.
- `Matrix.PosSemidef.one_sub_fromRows`: if AᴴA + BᴴB ≤ I, then I − VᴴV is PSD for
  V = [A; B].
- `Matrix.PosSemidef.smul_nonpos`: scaling a PSD matrix by a nonpositive real scalar gives a
  matrix ≤ 0.
- `Matrix.PosSemidef.add_smul_one_posDef`: A + rI is positive definite for A ≥ 0, r > 0.
- `Matrix.fromBlocks_diag_posSemidef`: `fromBlocks A 0 0 D` is PSD when A and D are PSD.
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

/-- Sandwiching a block-diagonal matrix `fromBlocks T₁ 0 0 T₂` by the stacked matrix
`fromRows A B` decomposes into two independent terms:
`(fromRows A B)ᴴ * fromBlocks T₁ 0 0 T₂ * fromRows A B = Aᴴ * T₁ * A + Bᴴ * T₂ * B`.
This is useful for reducing block-matrix inequalities to separate inequalities for each block. -/
lemma fromRows_compress_blockDiag
    {m₁ m₂ n : Type*} [Fintype m₁] [Fintype m₂] [Fintype n]
    (A : Matrix m₁ n ℂ) (B : Matrix m₂ n ℂ)
    (T₁ : Matrix m₁ m₁ ℂ) (T₂ : Matrix m₂ m₂ ℂ) :
    (Matrix.fromRows A B)ᴴ * (Matrix.fromBlocks T₁ 0 0 T₂) * Matrix.fromRows A B =
      Aᴴ * T₁ * A + Bᴴ * T₂ * B := by
  classical
  -- Compute with block multiplication rules.
  have hconj : (Matrix.fromRows A B)ᴴ = Matrix.fromCols Aᴴ Bᴴ := by
    simpa using (Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose (A₁ := A) (A₂ := B))
  have hmul1 :
      (Matrix.fromCols Aᴴ Bᴴ) *
          (Matrix.fromBlocks T₁ (0 : Matrix m₁ m₂ ℂ) (0 : Matrix m₂ m₁ ℂ) T₂) =
        Matrix.fromCols (Aᴴ * T₁) (Bᴴ * T₂) := by
    simpa [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] using
      (Matrix.fromCols_mul_fromBlocks (A₁ := Aᴴ) (A₂ := Bᴴ)
        (B₁₁ := T₁) (B₁₂ := (0 : Matrix m₁ m₂ ℂ))
        (B₂₁ := (0 : Matrix m₂ m₁ ℂ)) (B₂₂ := T₂))
  have hmul2 :
      Matrix.fromCols (Aᴴ * T₁) (Bᴴ * T₂) * Matrix.fromRows A B =
        Aᴴ * T₁ * A + Bᴴ * T₂ * B := by
    simpa [Matrix.mul_assoc] using
      (Matrix.fromCols_mul_fromRows (A₁ := Aᴴ * T₁) (A₂ := Bᴴ * T₂)
        (B₁ := A) (B₂ := B))
  calc
    (Matrix.fromRows A B)ᴴ * (Matrix.fromBlocks T₁ 0 0 T₂) * Matrix.fromRows A B =
        (Matrix.fromCols Aᴴ Bᴴ) * (Matrix.fromBlocks T₁ 0 0 T₂) * Matrix.fromRows A B := by
          simp [hconj]
    _ = Matrix.fromCols (Aᴴ * T₁) (Bᴴ * T₂) * Matrix.fromRows A B := by
          rw [hmul1]
    _ = Aᴴ * T₁ * A + Bᴴ * T₂ * B := by
          simpa using hmul2

/-- The quadratic form `x† (Vᴴ V) x` equals `(Vx)† (Vx)`. -/
lemma inner_conjTranspose_mul_self_mulVec {m n : Type*} [Fintype m] [Fintype n]
    (V : Matrix m n ℂ) (x : n → ℂ) :
    star x ⬝ᵥ ((Vᴴ * V) *ᵥ x) = star (V *ᵥ x) ⬝ᵥ (V *ᵥ x) := by
  classical
  have hmul : (Vᴴ * V) *ᵥ x = Vᴴ *ᵥ (V *ᵥ x) := by
    simp only [Matrix.mulVec_mulVec]
  calc
    star x ⬝ᵥ ((Vᴴ * V) *ᵥ x) = star x ⬝ᵥ (Vᴴ *ᵥ (V *ᵥ x)) := by
      rw [hmul]
    _ = (star x ᵥ* Vᴴ) ⬝ᵥ (V *ᵥ x) := by
      simpa using (Matrix.dotProduct_mulVec (v := star x) (A := Vᴴ) (w := V *ᵥ x))
    _ = star (V *ᵥ x) ⬝ᵥ (V *ᵥ x) := by
      simp [Matrix.vecMul_conjTranspose]

/-- The quadratic form `x† (Vᴴ A V) x` equals `(Vx)† A (Vx)`. -/
lemma inner_compress_mulVec {m n : Type*} [Fintype m] [Fintype n]
    (V : Matrix m n ℂ) (A : Matrix m m ℂ) (x : n → ℂ) :
    star x ⬝ᵥ ((Vᴴ * A * V) *ᵥ x) = star (V *ᵥ x) ⬝ᵥ (A *ᵥ (V *ᵥ x)) := by
  classical
  calc
    star x ⬝ᵥ ((Vᴴ * A * V) *ᵥ x) = star x ⬝ᵥ (Vᴴ *ᵥ (A *ᵥ (V *ᵥ x))) := by
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = (star x ᵥ* Vᴴ) ⬝ᵥ (A *ᵥ (V *ᵥ x)) := by
      simpa using (Matrix.dotProduct_mulVec (v := star x) (A := Vᴴ)
        (w := A *ᵥ (V *ᵥ x)))
    _ = star (V *ᵥ x) ⬝ᵥ (A *ᵥ (V *ᵥ x)) := by
      simp [Matrix.vecMul_conjTranspose]

/-- CFC rpow commutes with unitary conjugation: (U M U†)^p = U M^p U†.
This follows from `StarAlgHomClass.map_cfc` applied to the inner automorphism. -/
lemma rpow_unitary_conj {n : Type*} [Fintype n] [DecidableEq n]
    {U M : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ)
    {p : ℝ} (hp : 0 ≤ p) (hM : 0 ≤ M) (hM' : 0 ≤ U * M * Uᴴ := by cfc_tac) :
    (U * M * Uᴴ) ^ p = U * (M ^ p) * Uᴴ := by
  letI : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℂ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  letI : CStarAlgebra (Matrix n n ℂ) := by
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
  have hcont : ContinuousOn (· ^ p) (spectrum ℝ M) :=
    (Real.continuous_rpow_const hp).continuousOn
  -- Continuity of φ follows from finite-dimensionality
  have hφ_cont : Continuous φ :=
    φ.toAlgEquiv.toLinearMap.continuous_of_finiteDimensional
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
    (d : n → ℝ) (hd : ∀ i, 0 ≤ d i) (p : ℝ) (hp : 0 ≤ p) :
    (diagonal (fun i => (d i : ℂ))) ^ p = diagonal (fun i => ((d i ^ p : ℝ) : ℂ)) := by
  letI : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℂ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  letI : CStarAlgebra (Matrix n n ℂ) := by
    simpa [CStarMatrix] using CStarMatrix.instCStarAlgebra (n := n) (A := ℂ)
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
  have hφ_cont : Continuous φ :=
    φ.toAlgHom.toLinearMap.continuous_of_finiteDimensional
  -- `dc` is self-adjoint: all entries are real, hence equal to their conjugate.
  have hdc_sa : IsSelfAdjoint dc := by
    rw [IsSelfAdjoint, Pi.star_def]; ext i; simp [dc, Complex.conj_ofReal]
  have hφdc_sa : IsSelfAdjoint (φ dc) := by
    rw [IsSelfAdjoint, ← map_star φ]; exact congr_arg φ hdc_sa.star_eq
  -- CFC commutes with the star algebra hom φ.
  have h_map := StarAlgHomClass.map_cfc (R := ℝ) (S := ℝ) φ (· ^ p) dc
    ((Real.continuous_rpow_const hp).continuousOn) hφ_cont hdc_sa hφdc_sa
  -- φ dc = diagonal dc, so rewrite both sides.
  have hφ_dc : φ dc = diagonal dc := rfl
  rw [← hφ_dc, ← h_map]
  -- Goal: φ (cfc (· ^ p) dc) = diagonal (fun i => (d i ^ p : ℝ) : ℂ)
  change diagonal (cfc (· ^ p) dc) = diagonal (fun i => ((d i ^ p : ℝ) : ℂ))
  -- In the Pi C*-algebra n → ℂ, CFC is pointwise.
  rw [cfc_map_pi (S := ℝ) (· ^ p) dc]
  congr 1; funext i
  simp only [dc]
  rw [show (d i : ℂ) = algebraMap ℝ ℂ (d i) from rfl, cfc_algebraMap (A := ℂ) (d i) (· ^ p)]
  rfl

/-- For a positive definite matrix `B` and `p ≥ 0`,
`((B⁻¹)ᵀ) ^ p * Bᵀ = (B ^ (1 - p))ᵀ`. -/
lemma inv_transpose_rpow_mul_transpose_eq {m : Type*} [Fintype m] [DecidableEq m]
    (B : Matrix m m ℂ) (hB : B.PosDef) (p : ℝ) (hp : 0 ≤ p) :
    ((B⁻¹)ᵀ) ^ p * Bᵀ = (B ^ (1 - p))ᵀ := by
  letI : NormedRing (Matrix m m ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℂ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra
  letI : CStarAlgebra (Matrix m m ℂ) := by
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
    exact diagonal_rpow dB hdB_nonneg p hp
  have hBinv_rpow_spec : (B⁻¹) ^ p = (UB : Matrix m m ℂ) *
      diagonal (fun i => ((dB i ^ p : ℝ) : ℂ)) * (UB : Matrix m m ℂ)ᴴ := by
    conv_lhs => rw [hSpec]
    rw [rpow_unitary_conj UB.2 hp hD_nonneg
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
    rw [rpow_unitary_conj hW_unitary hp hD_nonneg (hM' := hBinvT_nonneg'), hD_rpow]
    rw [hBinv_rpow_spec]
    simp only [Matrix.transpose_mul, hDpt, Matrix.mul_assoc, hWH_eq]
  rw [htr_rpow, ← Matrix.transpose_mul]
  congr 1
  have hB_nonneg : (0 : Matrix m m ℂ) ≤ B := by
    simpa [Matrix.le_iff] using hB.posSemidef
  have hBinv_cfc : B⁻¹ = B ^ (-1 : ℝ) := by
    have h1 : B ^ (-1 : ℝ) * B = 1 := by
      have := CFC.rpow_neg_mul_rpow (1 : ℝ) hB_unit hB_nonneg
      rwa [CFC.rpow_one B hB_nonneg] at this
    have h2 : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hB_det
    exact hB_unit.mul_right_cancel (h2.trans h1.symm)
  have hBinv_rpow : (B⁻¹) ^ p = B ^ (-p) := by
    rw [hBinv_cfc, CFC.rpow_rpow B (-1 : ℝ) p hB_unit (by norm_num)]
    congr 1
    ring
  rw [hBinv_rpow]
  have h_add : B ^ (1 + (-p)) = B ^ (1 : ℝ) * B ^ (-p) :=
    CFC.rpow_add (x := 1) (y := -p) hB_unit
  rw [CFC.rpow_one B hB_nonneg] at h_add
  rw [← h_add, show (1 + (-p) : ℝ) = 1 - p from by ring]

/-! ### Positive Definite and Positive Semidefinite Matrices -/

/-- The identity matrix is positive definite. -/
lemma posDef_one {m : Type*} [Fintype m] [DecidableEq m] :
    (1 : Matrix m m ℂ).PosDef := by
  classical
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · simp [IsHermitian]
  · intro x hx
    have hpos : 0 < (star x ⬝ᵥ x) := (dotProduct_star_self_pos_iff (v := x)).2 hx
    simpa using hpos

/-- The identity matrix is positive semidefinite. -/
lemma posSemidef_one {m : Type*} [Fintype m] [DecidableEq m] :
    (1 : Matrix m m ℂ).PosSemidef :=
  posDef_one.posSemidef

/-- The block matrix [[A, I], [I, A⁻¹]] is positive semidefinite for positive definite A. -/
lemma fromBlocks_inv_posSemidef {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.PosDef) :
    (Matrix.fromBlocks A 1 1 A⁻¹).PosSemidef := by
  classical
  let _ := hA.isUnit.invertible
  have hSchur :
      (A⁻¹ - (1 : Matrix m m ℂ)ᴴ * A⁻¹ * (1 : Matrix m m ℂ)).PosSemidef := by
    simpa using (Matrix.PosSemidef.zero : (0 : Matrix m m ℂ).PosSemidef)
  simpa using (Matrix.PosDef.fromBlocks₁₁ (B := (1 : Matrix m m ℂ)) (D := A⁻¹) hA).2 hSchur

/-- The product `(fromRows A B)ᴴ * (fromRows A B)` equals `Aᴴ * A + Bᴴ * B`. -/
lemma fromRows_conjTranspose_mul_self
    {m₁ m₂ n : Type*} [Fintype m₁] [Fintype m₂] [Fintype n]
    (A : Matrix m₁ n ℂ) (B : Matrix m₂ n ℂ) :
    (Matrix.fromRows A B)ᴴ * Matrix.fromRows A B = Aᴴ * A + Bᴴ * B := by
  classical
  -- Expand with block column/row identities.
  simp [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromRows]

namespace PosSemidef

/-- Diagonal matrix with nonnegative real entries is positive semidefinite. -/
lemma diagonal_ofReal {m : Type*} [Fintype m] [DecidableEq m]
    {f : m → ℝ} (hf : ∀ i, 0 ≤ f i) :
    (diagonal (fun i => (f i : ℂ))).PosSemidef := by
  rw [posSemidef_diagonal_iff]
  intro i
  simp only [Complex.zero_le_real]
  exact hf i

/-- If `AᴴA + BᴴB ≤ I`, then the defect `I - VᴴV` is positive semidefinite for `V = fromRows A B`. -/
lemma one_sub_fromRows {m : Type*} [Fintype m] [DecidableEq m]
    (A B : Matrix m m ℂ) (hAB : Aᴴ * A + Bᴴ * B ≤ (1 : Matrix m m ℂ)) :
    ((1 : Matrix m m ℂ) - (Matrix.fromRows A B)ᴴ * Matrix.fromRows A B).PosSemidef := by
  have hV : (Matrix.fromRows A B)ᴴ * Matrix.fromRows A B ≤ (1 : Matrix m m ℂ) := by
    simpa [fromRows_conjTranspose_mul_self] using hAB
  simpa [Matrix.le_iff] using hV

/-- Scaling a PSD matrix by a nonpositive real scalar gives a matrix `≤ 0`. -/
lemma smul_nonpos {m : Type*} [Fintype m]
    {c : ℝ} (hc : c ≤ 0) {M : Matrix m m ℂ} (hM : M.PosSemidef) :
    c • M ≤ (0 : Matrix m m ℂ) := by
  have hnonneg : 0 ≤ -c := by linarith
  have hsmul : ((-c) • M).PosSemidef := hM.smul hnonneg
  rw [Matrix.le_iff]
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsmul

/-- Adding a positive scalar multiple of the identity to a PSD matrix gives a PD matrix. -/
lemma add_smul_one_posDef {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.PosSemidef) {r : ℝ} (hr : 0 < r) :
    (A + (r : ℂ) • (1 : Matrix m m ℂ)).PosDef := by
  classical
  have h1 : ((r : ℂ) • (1 : Matrix m m ℂ)).IsHermitian := by
    change ((r : ℂ) • (1 : Matrix m m ℂ))ᴴ = (r : ℂ) • (1 : Matrix m m ℂ)
    ext i j
    by_cases h : i = j
    · subst h
      simp
    · have h1 : (1 : Matrix m m ℂ) i j = 0 := by
        simp [h]
      have hji : ¬ j = i := by
        simpa [eq_comm] using h
      have h2 : (1 : Matrix m m ℂ) j i = 0 := by
        simp [hji]
      simp [Matrix.conjTranspose_apply, h1, h2]
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · exact hA.1.add h1
  · intro x hx
    have hA_re : 0 ≤ (star x ⬝ᵥ (A *ᵥ x)).re := hA.re_dotProduct_nonneg x
    have hxx_pos : 0 < (star x ⬝ᵥ x).re := by
      have hpos : 0 < (star x ⬝ᵥ x) := (dotProduct_star_self_pos_iff (v := x)).2 hx
      exact (RCLike.pos_iff.mp hpos).1
    have hsum_re :
        (star x ⬝ᵥ ((A + (r : ℂ) • (1 : Matrix m m ℂ)) *ᵥ x)).re =
          (star x ⬝ᵥ (A *ᵥ x)).re + r * (star x ⬝ᵥ x).re := by
      simp [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul,
        Complex.add_re, Complex.real_smul]
    have hsum_im :
        (star x ⬝ᵥ ((A + (r : ℂ) • (1 : Matrix m m ℂ)) *ᵥ x)).im = 0 := by
      set M := A + (r : ℂ) • (1 : Matrix m m ℂ)
      have hM : M.IsHermitian := hA.1.add h1
      have hconj : star (star x ⬝ᵥ M *ᵥ x) = star x ⬝ᵥ M *ᵥ x := by
        simp only [dotProduct, mulVec, star_sum, star_mul']
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro i _
        have hMij : star (M i j) = M j i := by
          have h := congrFun (congrFun hM j) i
          simp only [conjTranspose_apply] at h
          exact h
        simp_rw [hMij, Pi.star_apply, star_star]; ring
      have him : -(star x ⬝ᵥ M *ᵥ x).im = (star x ⬝ᵥ M *ᵥ x).im := by
        have := congrArg Complex.im hconj
        simp only [Complex.star_def, Complex.conj_im] at this
        exact this
      linarith
    have hpos_r : 0 < r * (star x ⬝ᵥ x).re := mul_pos hr hxx_pos
    have hsum_pos : 0 < (star x ⬝ᵥ ((A + (r : ℂ) • (1 : Matrix m m ℂ)) *ᵥ x)).re := by
      have hpos' : 0 < (star x ⬝ᵥ (A *ᵥ x)).re + r * (star x ⬝ᵥ x).re :=
        add_pos_of_nonneg_of_pos hA_re hpos_r
      rw [hsum_re]
      exact hpos'
    exact (RCLike.pos_iff).2 ⟨hsum_pos, hsum_im⟩

end PosSemidef

/-- Block diagonal `fromBlocks A 0 0 D` is PSD when both `A` and `D` are PSD. -/
lemma fromBlocks_diag_posSemidef {n₁ n₂ : Type*}
    [Fintype n₁] [Fintype n₂]
    {A : Matrix n₁ n₁ ℂ} (hA : A.PosSemidef)
    {D : Matrix n₂ n₂ ℂ} (hD : D.PosSemidef) :
    (Matrix.fromBlocks A 0 0 D).PosSemidef := by
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
