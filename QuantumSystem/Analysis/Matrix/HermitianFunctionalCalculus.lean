/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import QuantumSystem.ForMathlib.Analysis.Matrix.Basic
public import QuantumSystem.ForMathlib.Analysis.Matrix.HermitianFunctionalCalculus

/-!
# Matrix functional calculus: shifts, square roots and block diagonals

Identities for Mathlib's continuous functional calculus `cfc` on Hermitian complex matrices, used
by the matrix convexity results (`QuantumSystem/Analysis/Matrix/Order.lean`) and by Effros' proof of
Lieb concavity (`QuantumSystem/Analysis/Matrix/Effros.lean`,
`QuantumSystem/Analysis/Matrix/LiebConcavity.lean`). Foundational lemmas about Hermitian
matrices, positive semidefiniteness, block-matrix identities, and the Löwner order are in
`QuantumSystem.ForMathlib.Analysis.Matrix.*`.

## Main definitions

- `blockDiagEmbed`, `blockDiagEmbed'`: the block diagonal embedding `(A, D) ↦ A ⊕ D` as a star
  algebra homomorphism.

## Main results

### Continuous functional calculus
- `cfc_add_const_eq`: `cfc (· + t) A = A + t • 1`.
- `cfc_fromBlocks_diag`, `cfc_fromBlocks_diag'`: `f(A ⊕ D) = f(A) ⊕ f(D)` for block diagonal
  matrices.

### Square roots
Square roots are Mathlib's real powers `A ^ (1 / 2 : ℝ)`, `A ^ (-1 / 2 : ℝ)` (`CFC.rpow`).
- `posSemidef_rpow`: `A ^ s` is positive semidefinite.
- `rpow_half_mul_rpow_half`, `rpow_half_mul_rpow_neg_half`, `rpow_neg_half_mul_rpow_half`,
  `rpow_neg_half_mul_mul_rpow_neg_half`: the square-root identities.
- `rpow_commute_of_commute`: `R ^ s` commutes with every matrix commuting with `R`.

## References

* Bhatia, *Matrix Analysis* (1997)
-/

@[expose] public section

namespace Matrix

open scoped MatrixOrder ComplexOrder

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

/-! ### Square roots via `CFC.rpow`

Square roots and inverse square roots are Mathlib's real powers `A ^ (1 / 2 : ℝ)` and
`A ^ (-1 / 2 : ℝ)` (`CFC.rpow`); `CFC.sqrt_eq_rpow` identifies the first with `CFC.sqrt A`. -/

/-- The CFC real power of any matrix is positive semidefinite.
(`CFC.rpow_nonneg` is unconditional: on non-PSD input the CFC returns a junk
value that is still `0 ≤ ·`.) -/
lemma posSemidef_rpow {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℂ) (s : ℝ) : (A ^ s).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg

/-- For a positive semidefinite matrix `A`, `A^{1/2} * A^{1/2} = A`. -/
lemma rpow_half_mul_rpow_half {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.PosSemidef) :
    A ^ (1 / 2 : ℝ) * A ^ (1 / 2 : ℝ) = A := by
  rw [← CFC.sqrt_eq_rpow]
  exact CFC.sqrt_mul_sqrt_self A hA.nonneg

/-- For a positive definite matrix `A`, `A^{1/2} * A^{-1/2} = I`. -/
lemma rpow_half_mul_rpow_neg_half {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.PosDef) :
    A ^ (1 / 2 : ℝ) * A ^ (-1 / 2 : ℝ) = 1 := by
  rw [neg_div]
  exact CFC.rpow_mul_rpow_neg (1 / 2 : ℝ) hA.isStrictlyPositive

/-- For a positive definite matrix `A`, `A^{-1/2} * A^{1/2} = I`. -/
lemma rpow_neg_half_mul_rpow_half {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.PosDef) :
    A ^ (-1 / 2 : ℝ) * A ^ (1 / 2 : ℝ) = 1 := by
  rw [neg_div]
  exact CFC.rpow_neg_mul_rpow (1 / 2 : ℝ) hA.isStrictlyPositive

/-- For a positive definite matrix `A`, `A^{-1/2} * A * A^{-1/2} = I`. -/
lemma rpow_neg_half_mul_mul_rpow_neg_half {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A.PosDef) :
    A ^ (-1 / 2 : ℝ) * A * A ^ (-1 / 2 : ℝ) = 1 := by
  conv_lhs => enter [1, 2]; rw [← rpow_half_mul_rpow_half hA.posSemidef]
  rw [← Matrix.mul_assoc, rpow_neg_half_mul_rpow_half hA, Matrix.one_mul,
    rpow_half_mul_rpow_neg_half hA]

/-- A real power `R ^ s` commutes with every matrix that commutes with `R`. -/
lemma rpow_commute_of_commute {n : Type*} [Fintype n] [DecidableEq n]
    {L R : Matrix n n ℂ} (hcomm : Commute R L) (s : ℝ) : Commute (R ^ s) L := by
  rw [CFC.rpow_def]
  exact hcomm.cfc_nnreal _

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
  let : NormedRing (Matrix m m ℂ) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℝ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra
  let : NormedAlgebra ℂ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra
  let : CStarAlgebra (Matrix m m ℂ) := by
    simpa [CStarMatrix] using CStarMatrix.instCStarAlgebra (n := m) (A := ℂ)
  let : ContinuousFunctionalCalculus ℂ (Matrix m m ℂ) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  let : CStarAlgebra (Matrix m m ℂ × Matrix m m ℂ) := inferInstance
  let : ContinuousFunctionalCalculus ℂ (Matrix m m ℂ × Matrix m m ℂ) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  let : ContinuousFunctionalCalculus ℝ (Matrix m m ℂ × Matrix m m ℂ) IsSelfAdjoint :=
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
  let : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℝ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  let : NormedAlgebra ℂ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  let : CStarAlgebra (Matrix n n ℂ) := by
    simpa [CStarMatrix] using CStarMatrix.instCStarAlgebra (n := n) (A := ℂ)
  let : NormedRing (Matrix m m ℂ) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℝ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra
  let : NormedAlgebra ℂ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra
  let : CStarAlgebra (Matrix m m ℂ) := by
    simpa [CStarMatrix] using CStarMatrix.instCStarAlgebra (n := m) (A := ℂ)
  let : ContinuousFunctionalCalculus ℂ (Matrix n n ℂ) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  let : ContinuousFunctionalCalculus ℂ (Matrix m m ℂ) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  let : CStarAlgebra (Matrix n n ℂ × Matrix m m ℂ) := inferInstance
  let : ContinuousFunctionalCalculus ℂ (Matrix n n ℂ × Matrix m m ℂ) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  let : ContinuousFunctionalCalculus ℝ (Matrix n n ℂ × Matrix m m ℂ) IsSelfAdjoint :=
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

end Matrix
