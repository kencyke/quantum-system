/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.Matrix.HermitianFunctionalCalculus
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.CStarMatrix
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.OperatorConvex
public import QuantumSystem.ForMathlib.Analysis.Matrix.Hermitian
public import QuantumSystem.ForMathlib.Analysis.Matrix.Order
public import QuantumSystem.ForMathlib.LinearAlgebra.Matrix.StarAlgEquiv

/-!
# Matrix convexity and Jensen's operator inequality for matrices

A real function `f` is matrix convex on `s` (`IsMatrixConvexOn`, Bhatia Chapter V; Effros's
"matrix convexity") when `A ↦ f(A)` is convex in the Löwner order on the self-adjoint matrices
with spectrum in `s`, in every size. No continuity of `f` is required; for `f` continuous on `s`,
matrix convexity is operator convexity (`isOperatorConvexOn_iff_continuousOn_and_isMatrixConvexOn`
in `QuantumSystem/Analysis/CStarAlgebra/OperatorConvex.lean`). This file proves Jensen's
operator inequality for matrix convex functions, in the unital form of Hansen–Pedersen 2003 and
the sub-unital form of Hansen–Pedersen 1982, with square and with rectangular weights, and the
characterisations of matrix convexity by these inequalities. The common core over a C⋆-algebra,
`cfc_sum_le_of_convexOn_cstarMatrix`, is in `OperatorConvex.lean`; here the C⋆-algebra structure
on matrices (the operator norm of scope `Matrix.Norms.L2Operator`) is used only inside proofs, and
continuity on the finite spectra of matrices is automatic.

## Main results

* `Matrix.PosSemidef.mem_setOf_isSelfAdjoint_spectrum_subset_Ici`,
  `Matrix.PosDef.mem_setOf_isSelfAdjoint_spectrum_subset_Ioi`: positive semidefinite and positive
  definite matrices lie in the domains for `[0, ∞)` and `(0, ∞)`.
* `IsMatrixConvexOn.convexOn`: matrix convexity in every finite index type.
* `IsMatrixConvexOn.cfc_sum_le`, `IsMatrixConvexOn.cfc_affine_le` (Hansen–Pedersen 2003):
  `f(Σᵢ Aᵢ† Tᵢ Aᵢ) ≤ Σᵢ Aᵢ† f(Tᵢ) Aᵢ` for `Σᵢ Aᵢ† Aᵢ = I`;
  `IsMatrixConvexOn.cfc_sum_conjTranspose_mul_mul_le` for rectangular `Aᵢ : Matrix k m ℂ`
  (Davis 1957 for a single isometry).
* `IsMatrixConvexOn.cfc_sum_le_of_le_one`, `IsMatrixConvexOn.cfc_affine_le_of_le_one`,
  `IsMatrixConvexOn.cfc_sum_conjTranspose_mul_mul_le_of_le_one` (Hansen–Pedersen 1982): the
  sub-unital forms for `Σᵢ Aᵢ† Aᵢ ≤ I`, on `s ∋ 0` with `f(0) ≤ 0`.
* `isMatrixConvexOn_iff_cfc_affine_le` (Hansen–Pedersen 2003): on an interval, `f` is matrix
  convex iff the two-term unital Jensen inequality holds in every size.
* `isMatrixConvexOn_and_map_zero_nonpos_iff` (Hansen–Pedersen 1982): on an interval `s ∋ 0`,
  `f` is matrix convex with `f(0) ≤ 0` iff the two-term sub-unital Jensen inequality holds.
* `Matrix.rpow_concavity_le`: operator concavity of `xˢ` in unfolded form.
* `Matrix.trace_mul_mono_of_posSemidef`: monotonicity of the trace pairing.

## Implementation notes

The square inequalities come from `cfc_sum_le_of_convexOn_cstarMatrix`, applied to the C⋆-algebra
`Matrix m m ℂ` with the ⋆-isomorphism `CStarMatrix ι ι (Matrix m m ℂ) ≃⋆ₐ Matrix (ι × m) (ι × m) ℂ`
(`Matrix.compStarAlgEquiv`), where matrix convexity supplies the convexity of `cfc f` and
finiteness of the spectrum (`Matrix.finite_real_spectrum`) the continuity. The rectangular
inequalities pad `Aᵢ` to `(0 Aᵢ; 0 0)` in `Matrix (k ⊕ m) (k ⊕ m) ℂ` and read off the lower right
block.

## References

* C. Davis, *A Schwarz inequality for convex operator functions*, Proc. Amer. Math. Soc. 8 (1957),
  42–44
* F. Hansen, G. K. Pedersen, *Jensen's inequality for operators and Löwner's theorem*,
  Math. Ann. 258 (1982), 229–241
* F. Hansen, G. K. Pedersen, *Jensen's operator inequality*, Bull. London Math. Soc. 35 (2003),
  553–564
* R. Bhatia, *Matrix Analysis*, Chapter V (1997)
* E. G. Effros, *A matrix convexity approach to some celebrated quantum inequalities*, Proc. Natl.
  Acad. Sci. USA 106 (2009), 1006–1008
-/
@[expose] public section

open Real Set
open scoped MatrixOrder ComplexOrder

namespace Matrix

/-- A positive semidefinite matrix lies in the domain for `s = [0, ∞)`. -/
lemma PosSemidef.mem_setOf_isSelfAdjoint_spectrum_subset_Ici {m : Type*} [Fintype m]
    [DecidableEq m] {A : Matrix m m ℂ} (hA : A.PosSemidef) :
    A ∈ {A : Matrix m m ℂ | IsSelfAdjoint A ∧ spectrum ℝ A ⊆ Ici 0} := by
  rw [setOf_isSelfAdjoint_spectrum_subset_Ici]
  exact hA.nonneg

/-- A positive definite matrix lies in the domain for `s = (0, ∞)`. -/
lemma PosDef.mem_setOf_isSelfAdjoint_spectrum_subset_Ioi {m : Type*} [Fintype m]
    [DecidableEq m] {A : Matrix m m ℂ} (hA : A.PosDef) :
    A ∈ {A : Matrix m m ℂ | IsSelfAdjoint A ∧ spectrum ℝ A ⊆ Ioi 0} := by
  rw [setOf_isSelfAdjoint_spectrum_subset_Ioi]
  exact hA.isStrictlyPositive

/-- A block diagonal matrix `T₁ ⊕ T₂` with blocks in the domain for `s` lies in the domain: its
spectrum is contained in `spectrum T₁ ∪ spectrum T₂`. -/
private lemma fromBlocks_mem_setOf_isSelfAdjoint_spectrum_subset {n m : Type*} [Fintype n]
    [DecidableEq n] [Fintype m] [DecidableEq m] {s : Set ℝ} {T₁ : Matrix n n ℂ} {T₂ : Matrix m m ℂ}
    (h₁ : T₁ ∈ {A : Matrix n n ℂ | IsSelfAdjoint A ∧ spectrum ℝ A ⊆ s})
    (h₂ : T₂ ∈ {A : Matrix m m ℂ | IsSelfAdjoint A ∧ spectrum ℝ A ⊆ s}) :
    fromBlocks T₁ 0 0 T₂ ∈
      {A : Matrix (n ⊕ m) (n ⊕ m) ℂ | IsSelfAdjoint A ∧ spectrum ℝ A ⊆ s} := by
  refine ⟨IsHermitian.fromBlocks (show T₁.IsHermitian from h₁.1) (by simp)
    (show T₂.IsHermitian from h₂.1), ?_⟩
  have h := AlgHom.spectrum_apply_subset (blockDiagEmbed' n m) (T₁, T₂)
  rw [Prod.spectrum_eq] at h
  exact (h : spectrum ℝ (fromBlocks T₁ 0 0 T₂) ⊆ _).trans (union_subset h₁.2 h₂.2)

/-- The lower right block is monotone in the Löwner order. -/
private lemma toBlocks₂₂_mono {n m : Type*} [Finite n] [Finite m]
    {X Y : Matrix (n ⊕ m) (n ⊕ m) ℂ} (h : X ≤ Y) : X.toBlocks₂₂ ≤ Y.toBlocks₂₂ := by
  have := Fintype.ofFinite n
  have := Fintype.ofFinite m
  rw [Matrix.le_iff] at h ⊢
  convert h.submatrix Sum.inr using 1
  ext i j
  rfl

/-- The block diagonal `cfc f (T₁ ⊕ T₂) = f(T₁) ⊕ f(T₂)` for self-adjoint blocks. -/
private lemma cfc_fromBlocks_zero_zero {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
    [DecidableEq m] (f : ℝ → ℝ) {T₁ : Matrix n n ℂ} {T₂ : Matrix m m ℂ} (h₁ : IsSelfAdjoint T₁)
    (h₂ : IsSelfAdjoint T₂) : cfc f (fromBlocks T₁ 0 0 T₂) = fromBlocks (cfc f T₁) 0 0 (cfc f T₂) :=
  cfc_fromBlocks_diag' T₁ T₂ h₁ h₂ f ((finite_real_spectrum.union finite_real_spectrum).continuousOn f)

/-- A sum `Σᵢ Aᵢ† Tᵢ Aᵢ` of compressions of Hermitian matrices is self-adjoint. -/
private lemma isSelfAdjoint_sum_conjTranspose_mul_mul {ι k m : Type*} [Fintype ι] [Fintype k]
    (A : ι → Matrix k m ℂ) {T : ι → Matrix k k ℂ} (hT : ∀ i, IsSelfAdjoint (T i)) :
    IsSelfAdjoint (∑ i, (A i)ᴴ * T i * A i) :=
  isSelfAdjoint_sum _ fun i _ => isHermitian_conjTranspose_mul_mul (A i) (hT i)

/-- A positive semidefinite lower right block gives a positive semidefinite block matrix. -/
private lemma posSemidef_fromBlocks_zero_zero_zero {k m : Type*} [Finite k] [Finite m]
    {R : Matrix m m ℂ} (hR : R.PosSemidef) :
    (fromBlocks 0 0 0 R : Matrix (k ⊕ m) (k ⊕ m) ℂ).PosSemidef := by
  classical
  have := Fintype.ofFinite k
  have := Fintype.ofFinite m
  have h := hR.conjTranspose_mul_mul_same (fromCols (0 : Matrix m k ℂ) (1 : Matrix m m ℂ))
  have heq : (fromCols (0 : Matrix m k ℂ) (1 : Matrix m m ℂ))ᴴ * R * fromCols (0 : Matrix m k ℂ) (1 : Matrix m m ℂ) =
      fromBlocks 0 0 0 R := by
    ext (a | a) (b | b) <;> simp [fromCols, Matrix.mul_apply, Matrix.one_apply]
  rwa [heq] at h

/-- Compressing a matrix by the padded weight `(0 A; 0 0)` picks out `A† T₁₁ A` in the lower right
block. -/
private lemma fromBlocks_zero_conjTranspose_mul_mul {k m : Type*} [Fintype k] [Fintype m]
    (A : Matrix k m ℂ) (T : Matrix (k ⊕ m) (k ⊕ m) ℂ) :
    (fromBlocks 0 A 0 0 : Matrix (k ⊕ m) (k ⊕ m) ℂ)ᴴ * T * fromBlocks 0 A 0 0 =
      fromBlocks 0 0 0 (Aᴴ * T.toBlocks₁₁ * A) := by
  rw [← fromBlocks_toBlocks T, fromBlocks_conjTranspose]
  simp [fromBlocks_multiply]

/-- A sum of lower right blocks is the lower right block of the sum. -/
private lemma sum_fromBlocks_zero_zero_zero {ι k m : Type*} [Fintype ι] (X : ι → Matrix m m ℂ) :
    ∑ i, (fromBlocks 0 0 0 (X i) : Matrix (k ⊕ m) (k ⊕ m) ℂ) = fromBlocks 0 0 0 (∑ i, X i) := by
  ext (a | a) (b | b) <;> simp [Matrix.sum_apply]

end Matrix

open Matrix

section Square

variable {s : Set ℝ} {f : ℝ → ℝ}

/-- A matrix convex function is convex on the matrices of every finite index type, through
`Matrix.reindexStarAlgEquiv`. -/
theorem IsMatrixConvexOn.convexOn (hf : IsMatrixConvexOn s f) (m : Type*) [Fintype m]
    [DecidableEq m] :
    ConvexOn ℝ {A : Matrix m m ℂ | IsSelfAdjoint A ∧ spectrum ℝ A ⊆ s} (cfc f) := by
  open scoped Matrix.Norms.L2Operator in
  exact ConvexOn.cfc_of_injective (Matrix.reindexStarAlgEquiv (R := ℂ) (Fintype.equivFin m))
    (EquivLike.injective _) (hf _)

/-- **Jensen's operator inequality for matrices** (Hansen–Pedersen 2003, Theorem 2.1): for `f`
matrix convex on `s`, a finite family `Aᵢ : Matrix m m ℂ` with `Σᵢ Aᵢ† Aᵢ = I` and self-adjoint
`Tᵢ` with spectrum in `s`, `f(Σᵢ Aᵢ† Tᵢ Aᵢ) ≤ Σᵢ Aᵢ† f(Tᵢ) Aᵢ`. No continuity of `f` is needed:
the spectra are finite. -/
theorem IsMatrixConvexOn.cfc_sum_le (hf : IsMatrixConvexOn s f) {ι m : Type*} [Fintype ι]
    [Fintype m] [DecidableEq m] (A : ι → Matrix m m ℂ) (T : ι → Matrix m m ℂ)
    (hT : ∀ i, T i ∈ {X : Matrix m m ℂ | IsSelfAdjoint X ∧ spectrum ℝ X ⊆ s})
    (hA : ∑ i, (A i)ᴴ * A i = 1) :
    cfc f (∑ i, (A i)ᴴ * T i * A i) ≤ ∑ i, (A i)ᴴ * cfc f (T i) * A i := by
  classical
  open scoped Matrix.Norms.L2Operator in
  exact cfc_sum_le_of_convexOn_cstarMatrix (A := Matrix m m ℂ) (B := Matrix (ι × m) (ι × m) ℂ)
    (CStarMatrix.ofMatrixStarAlgEquiv.symm.trans (Matrix.compStarAlgEquiv ι m ℂ ℂ))
    (EquivLike.injective _) (hf.convexOn (ι × m)) (fun _ _ _ => finite_real_spectrum.continuousOn f) A T hT hA

/-- **Jensen's operator inequality for matrices**, two-term case (Hansen–Pedersen 2003): for `f`
matrix convex on `s`, `A†A + B†B = I` and self-adjoint `T₁, T₂` with spectrum in `s`,
`f(A† T₁ A + B† T₂ B) ≤ A† f(T₁) A + B† f(T₂) B`. -/
theorem IsMatrixConvexOn.cfc_affine_le (hf : IsMatrixConvexOn s f) {m : Type*} [Fintype m]
    [DecidableEq m] (A B T₁ T₂ : Matrix m m ℂ)
    (hT₁ : T₁ ∈ {X : Matrix m m ℂ | IsSelfAdjoint X ∧ spectrum ℝ X ⊆ s})
    (hT₂ : T₂ ∈ {X : Matrix m m ℂ | IsSelfAdjoint X ∧ spectrum ℝ X ⊆ s})
    (hAB : Aᴴ * A + Bᴴ * B = 1) :
    cfc f (Aᴴ * T₁ * A + Bᴴ * T₂ * B) ≤ Aᴴ * cfc f T₁ * A + Bᴴ * cfc f T₂ * B := by
  simpa [Fin.sum_univ_two] using hf.cfc_sum_le ![A, B] ![T₁, T₂] (Fin.forall_fin_two.2 ⟨hT₁, hT₂⟩)
    (by simpa [Fin.sum_univ_two] using hAB)

/-- **Jensen's operator inequality for matrices, sub-unital form** (Hansen–Pedersen 1982,
Theorem 2.1): for `f` matrix convex on `s ∋ 0` with `f(0) ≤ 0`, a finite family `Aᵢ` with
`Σᵢ Aᵢ† Aᵢ ≤ I` and self-adjoint `Tᵢ` with spectrum in `s`, `f(Σᵢ Aᵢ† Tᵢ Aᵢ) ≤ Σᵢ Aᵢ† f(Tᵢ) Aᵢ`
(`cfc_sum_le_of_le_one_of_forall`). -/
theorem IsMatrixConvexOn.cfc_sum_le_of_le_one (hf : IsMatrixConvexOn s f) (h0 : (0 : ℝ) ∈ s)
    (hf0 : f 0 ≤ 0) {ι m : Type*} [Fintype ι] [Fintype m] [DecidableEq m]
    (A : ι → Matrix m m ℂ) (T : ι → Matrix m m ℂ)
    (hT : ∀ i, T i ∈ {X : Matrix m m ℂ | IsSelfAdjoint X ∧ spectrum ℝ X ⊆ s})
    (hA : ∑ i, (A i)ᴴ * A i ≤ 1) :
    cfc f (∑ i, (A i)ᴴ * T i * A i) ≤ ∑ i, (A i)ᴴ * cfc f (T i) * A i := by
  open scoped Matrix.Norms.L2Operator in
  exact cfc_sum_le_of_le_one_of_forall (A := Matrix m m ℂ) h0 hf0
    (fun a x hx ha => hf.cfc_sum_le a x hx ha) A T hT hA

/-- **Jensen's operator inequality for matrices, sub-unital two-term form** (Hansen–Pedersen
1982): for `f` matrix convex on `s ∋ 0` with `f(0) ≤ 0`, `A†A + B†B ≤ I` and self-adjoint `T₁, T₂`
with spectrum in `s`, `f(A† T₁ A + B† T₂ B) ≤ A† f(T₁) A + B† f(T₂) B`. -/
theorem IsMatrixConvexOn.cfc_affine_le_of_le_one (hf : IsMatrixConvexOn s f) (h0 : (0 : ℝ) ∈ s)
    (hf0 : f 0 ≤ 0) {m : Type*} [Fintype m] [DecidableEq m] (A B T₁ T₂ : Matrix m m ℂ)
    (hT₁ : T₁ ∈ {X : Matrix m m ℂ | IsSelfAdjoint X ∧ spectrum ℝ X ⊆ s})
    (hT₂ : T₂ ∈ {X : Matrix m m ℂ | IsSelfAdjoint X ∧ spectrum ℝ X ⊆ s})
    (hAB : Aᴴ * A + Bᴴ * B ≤ 1) :
    cfc f (Aᴴ * T₁ * A + Bᴴ * T₂ * B) ≤ Aᴴ * cfc f T₁ * A + Bᴴ * cfc f T₂ * B := by
  simpa [Fin.sum_univ_two] using hf.cfc_sum_le_of_le_one h0 hf0 ![A, B] ![T₁, T₂]
    (Fin.forall_fin_two.2 ⟨hT₁, hT₂⟩) (by simpa [Fin.sum_univ_two] using hAB)

/-- `√c • 1` conjugates `T` to `c • T`. -/
private lemma conjTranspose_sqrt_smul_one_mul_mul {m : Type*} [Fintype m] [DecidableEq m] {c : ℝ}
    (hc : 0 ≤ c) (T : Matrix m m ℂ) :
    ((√c : ℝ) • (1 : Matrix m m ℂ))ᴴ * T * ((√c : ℝ) • 1) = c • T := by
  simp only [conjTranspose_smul, conjTranspose_one, star_trivial, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, smul_smul, Real.mul_self_sqrt hc]

/-- **Hansen–Pedersen** (2003, Theorem 2.1 (i)⟺(ii) with `n = 2`) for matrices: on an interval
`s`, `f` is matrix convex iff the two-term Jensen inequality
`f(A† T₁ A + B† T₂ B) ≤ A† f(T₁) A + B† f(T₂) B` holds in every size for all `A†A + B†B = I` and
self-adjoint `T₁, T₂` with spectrum in `s`. The
converse takes the scalars `A = √λ`, `B = √(1 - λ)`. No continuity of `f` and no condition on
`f(0)` is needed; compare `isMatrixConvexOn_and_map_zero_nonpos_iff`. -/
theorem isMatrixConvexOn_iff_cfc_affine_le (hs : s.OrdConnected) :
    IsMatrixConvexOn s f ↔ ∀ (n : ℕ) (A B T₁ T₂ : Matrix (Fin n) (Fin n) ℂ),
      T₁ ∈ {X : Matrix (Fin n) (Fin n) ℂ | IsSelfAdjoint X ∧ spectrum ℝ X ⊆ s} →
      T₂ ∈ {X : Matrix (Fin n) (Fin n) ℂ | IsSelfAdjoint X ∧ spectrum ℝ X ⊆ s} →
      Aᴴ * A + Bᴴ * B = 1 →
      cfc f (Aᴴ * T₁ * A + Bᴴ * T₂ * B) ≤ Aᴴ * cfc f T₁ * A + Bᴴ * cfc f T₂ * B := by
  refine ⟨fun hf n A B T₁ T₂ hT₁ hT₂ hAB => hf.cfc_affine_le A B T₁ T₂ hT₁ hT₂ hAB, fun hJ n =>
    ⟨hs.convex_setOf_isSelfAdjoint_spectrum_subset, fun T₁ hT₁ T₂ hT₂ a b ha hb hab => ?_⟩⟩
  have key := hJ n ((√a : ℝ) • 1) ((√b : ℝ) • 1) T₁ T₂ hT₁ hT₂ (by
    rw [← Matrix.mul_one ((√a : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ,
      conjTranspose_sqrt_smul_one_mul_mul ha,
      ← Matrix.mul_one ((√b : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ,
      conjTranspose_sqrt_smul_one_mul_mul hb, ← add_smul, hab, one_smul])
  simpa only [conjTranspose_sqrt_smul_one_mul_mul ha, conjTranspose_sqrt_smul_one_mul_mul hb]
    using key

/-- **Hansen–Pedersen** (1982, Theorem 2.1 (i)⟺(iii), stated there on `[0, α)`) for matrices: on
an interval `s ∋ 0`, `f` is matrix convex with `f(0) ≤ 0` iff the sub-unital Jensen inequality
`f(A† T₁ A + B† T₂ B) ≤ A† f(T₁) A + B† f(T₂) B` holds in every size for all `A†A + B†B ≤ I` and
self-adjoint `T₁, T₂` with spectrum in `s`. The converse takes the scalars `A = √λ`,
`B = √(1 - λ)` for convexity and `A = B = 0` in size one for `f(0) ≤ 0`. The unital form
`isMatrixConvexOn_iff_cfc_affine_le` characterises matrix convexity alone; the sub-unital form is
specific to intervals containing `0`, since `A† T A` has spectrum in the convex hull of
`spectrum T ∪ {0}`. -/
theorem isMatrixConvexOn_and_map_zero_nonpos_iff (hs : s.OrdConnected) (h0 : (0 : ℝ) ∈ s) :
    IsMatrixConvexOn s f ∧ f 0 ≤ 0 ↔ ∀ (n : ℕ) (A B T₁ T₂ : Matrix (Fin n) (Fin n) ℂ),
      T₁ ∈ {X : Matrix (Fin n) (Fin n) ℂ | IsSelfAdjoint X ∧ spectrum ℝ X ⊆ s} →
      T₂ ∈ {X : Matrix (Fin n) (Fin n) ℂ | IsSelfAdjoint X ∧ spectrum ℝ X ⊆ s} →
      Aᴴ * A + Bᴴ * B ≤ 1 →
      cfc f (Aᴴ * T₁ * A + Bᴴ * T₂ * B) ≤ Aᴴ * cfc f T₁ * A + Bᴴ * cfc f T₂ * B := by
  refine ⟨fun ⟨hf, hf0⟩ n A B T₁ T₂ hT₁ hT₂ hAB =>
    hf.cfc_affine_le_of_le_one h0 hf0 A B T₁ T₂ hT₁ hT₂ hAB, fun hJ => ⟨?_, ?_⟩⟩
  · exact (isMatrixConvexOn_iff_cfc_affine_le hs).2 fun n A B T₁ T₂ hT₁ hT₂ hAB =>
      hJ n A B T₁ T₂ hT₁ hT₂ hAB.le
  · have h0mem : (0 : Matrix (Fin 1) (Fin 1) ℂ) ∈
        {X : Matrix (Fin 1) (Fin 1) ℂ | IsSelfAdjoint X ∧ spectrum ℝ X ⊆ s} :=
      zero_mem_setOf_isSelfAdjoint_spectrum_subset h0
    have h := hJ 1 0 0 0 0 h0mem h0mem (by simp)
    simp only [conjTranspose_zero, Matrix.mul_zero, add_zero, cfc_apply_zero] at h
    rw [← map_zero (algebraMap ℝ (Matrix (Fin 1) (Fin 1) ℂ))] at h
    exact (le_algebraMap_iff_spectrum_le (IsSelfAdjoint.algebraMap _ (.all (f 0)))).1 h (f 0)
      (by rw [spectrum.scalar_eq]; rfl)

end Square

/-- **Jensen's operator inequality for rectangular weights** (Hansen–Pedersen 2003; Davis 1957 for
one isometry): for `f` matrix convex on `s`, a finite family `Aᵢ : Matrix k m ℂ` with
`Σᵢ Aᵢ† Aᵢ = I` and self-adjoint `Tᵢ` with spectrum in `s`, `f(Σᵢ Aᵢ† Tᵢ Aᵢ) ≤ Σᵢ Aᵢ† f(Tᵢ) Aᵢ`.
For `k = m` this is `IsMatrixConvexOn.cfc_sum_le`. -/
theorem IsMatrixConvexOn.cfc_sum_conjTranspose_mul_mul_le {s : Set ℝ} {f : ℝ → ℝ}
    (hf : IsMatrixConvexOn s f) {ι k m : Type*} [Fintype ι] [Fintype k] [DecidableEq k]
    [Fintype m] [DecidableEq m] (A : ι → Matrix k m ℂ) (T : ι → Matrix k k ℂ)
    (hT : ∀ i, T i ∈ {X : Matrix k k ℂ | IsSelfAdjoint X ∧ spectrum ℝ X ⊆ s})
    (hA : ∑ i, (A i)ᴴ * A i = 1) :
    cfc f (∑ i, (A i)ᴴ * T i * A i) ≤ ∑ i, (A i)ᴴ * cfc f (T i) * A i := by
  classical
  rcases isEmpty_or_nonempty m with hm | hm
  · exact le_of_eq (Subsingleton.elim _ _)
  obtain ⟨i₁⟩ : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hA
  have hk : Nonempty k := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp [Subsingleton.elim (A _) 0] at hA
  obtain ⟨t, ht⟩ := ContinuousFunctionalCalculus.spectrum_nonempty (R := ℝ) (T i₁) (hT i₁).1
  have hts := (hT i₁).2 ht
  have hck := algebraMap_mem_setOf_isSelfAdjoint_spectrum_subset (A := Matrix k k ℂ) hts
  have hcm := algebraMap_mem_setOf_isSelfAdjoint_spectrum_subset (A := Matrix m m ℂ) hts
  let c₁ : Matrix k k ℂ := algebraMap ℝ _ t
  let c₂ : Matrix m m ℂ := algebraMap ℝ _ t
  let W : Option ι → Matrix (k ⊕ m) (k ⊕ m) ℂ :=
    fun o => o.elim (fromBlocks 1 0 0 0) fun i => fromBlocks 0 (A i) 0 0
  let X : Option ι → Matrix (k ⊕ m) (k ⊕ m) ℂ :=
    fun o => o.elim (fromBlocks c₁ 0 0 c₂) fun i => fromBlocks (T i) 0 0 c₂
  have hX : ∀ o, X o ∈ {Y : Matrix (k ⊕ m) (k ⊕ m) ℂ | IsSelfAdjoint Y ∧ spectrum ℝ Y ⊆ s} :=
    fun o => match o with
      | none => fromBlocks_mem_setOf_isSelfAdjoint_spectrum_subset hck hcm
      | some i => fromBlocks_mem_setOf_isSelfAdjoint_spectrum_subset (hT i) hcm
  have hP (Y : Matrix (k ⊕ m) (k ⊕ m) ℂ) :
      (fromBlocks 1 0 0 0 : Matrix (k ⊕ m) (k ⊕ m) ℂ)ᴴ * Y * fromBlocks 1 0 0 0 =
        fromBlocks Y.toBlocks₁₁ 0 0 0 := by
    rw [← fromBlocks_toBlocks Y, fromBlocks_conjTranspose]
    simp [fromBlocks_multiply]
  have hsum (Y : Option ι → Matrix (k ⊕ m) (k ⊕ m) ℂ) :
      ∑ o, (W o)ᴴ * Y o * W o =
        fromBlocks (Y none).toBlocks₁₁ 0 0 (∑ i, (A i)ᴴ * (Y (some i)).toBlocks₁₁ * A i) := by
    rw [Fintype.sum_option]
    simp only [W, Option.elim_none, Option.elim_some, hP, fromBlocks_zero_conjTranspose_mul_mul,
      sum_fromBlocks_zero_zero_zero, fromBlocks_add, add_zero, zero_add]
  have h1 : (1 : Matrix (k ⊕ m) (k ⊕ m) ℂ).toBlocks₁₁ = 1 := by
    rw [← fromBlocks_one, toBlocks_fromBlocks₁₁]
  have hW : ∑ o, (W o)ᴴ * W o = 1 := by
    have h := hsum 1
    simp only [Pi.one_apply, Matrix.mul_one, h1, hA, fromBlocks_one] at h
    exact h
  have h := hf.cfc_sum_le W X hX hW
  have hc₁ : (cfc f (fromBlocks c₁ 0 0 c₂)).toBlocks₁₁ = cfc f c₁ := by
    rw [cfc_fromBlocks_zero_zero f hck.1 hcm.1, toBlocks_fromBlocks₁₁]
  have hcT (i : ι) : (cfc f (fromBlocks (T i) 0 0 c₂)).toBlocks₁₁ = cfc f (T i) := by
    rw [cfc_fromBlocks_zero_zero f (hT i).1 hcm.1, toBlocks_fromBlocks₁₁]
  rw [hsum X, hsum fun o => cfc f (X o)] at h
  simp only [X, Option.elim_none, Option.elim_some, toBlocks_fromBlocks₁₁, hc₁, hcT] at h
  rw [cfc_fromBlocks_zero_zero f hck.1
    (isSelfAdjoint_sum_conjTranspose_mul_mul A fun i => (hT i).1)] at h
  simpa using toBlocks₂₂_mono h

/-- **Jensen's operator inequality for rectangular weights, sub-unital form** (Hansen–Pedersen
1982): for `f` matrix convex on `s ∋ 0` with `f(0) ≤ 0`, a finite family `Aᵢ : Matrix k m ℂ` with
`Σᵢ Aᵢ† Aᵢ ≤ I` and self-adjoint `Tᵢ` with spectrum in `s`, `f(Σᵢ Aᵢ† Tᵢ Aᵢ) ≤ Σᵢ Aᵢ† f(Tᵢ) Aᵢ`.
For `k = m` this is `IsMatrixConvexOn.cfc_sum_le_of_le_one`. -/
theorem IsMatrixConvexOn.cfc_sum_conjTranspose_mul_mul_le_of_le_one {s : Set ℝ}
    {f : ℝ → ℝ} (hf : IsMatrixConvexOn s f) (h0 : (0 : ℝ) ∈ s) (hf0 : f 0 ≤ 0)
    {ι k m : Type*} [Fintype ι] [Fintype k] [DecidableEq k] [Fintype m] [DecidableEq m]
    (A : ι → Matrix k m ℂ) (T : ι → Matrix k k ℂ)
    (hT : ∀ i, T i ∈ {X : Matrix k k ℂ | IsSelfAdjoint X ∧ spectrum ℝ X ⊆ s})
    (hA : ∑ i, (A i)ᴴ * A i ≤ 1) :
    cfc f (∑ i, (A i)ᴴ * T i * A i) ≤ ∑ i, (A i)ᴴ * cfc f (T i) * A i := by
  classical
  have h0k := zero_mem_setOf_isSelfAdjoint_spectrum_subset (A := Matrix k k ℂ) h0
  have h0m := zero_mem_setOf_isSelfAdjoint_spectrum_subset (A := Matrix m m ℂ) h0
  let W : ι → Matrix (k ⊕ m) (k ⊕ m) ℂ := fun i => fromBlocks 0 (A i) 0 0
  let X : ι → Matrix (k ⊕ m) (k ⊕ m) ℂ := fun i => fromBlocks (T i) 0 0 0
  have hX (i : ι) : X i ∈ {Y : Matrix (k ⊕ m) (k ⊕ m) ℂ | IsSelfAdjoint Y ∧ spectrum ℝ Y ⊆ s} :=
    fromBlocks_mem_setOf_isSelfAdjoint_spectrum_subset (hT i) h0m
  have hsum (Y : ι → Matrix (k ⊕ m) (k ⊕ m) ℂ) :
      ∑ i, (W i)ᴴ * Y i * W i = fromBlocks 0 0 0 (∑ i, (A i)ᴴ * (Y i).toBlocks₁₁ * A i) := by
    simp only [W, fromBlocks_zero_conjTranspose_mul_mul, sum_fromBlocks_zero_zero_zero]
  have h1 : (1 : Matrix (k ⊕ m) (k ⊕ m) ℂ).toBlocks₁₁ = 1 := by
    rw [← fromBlocks_one, toBlocks_fromBlocks₁₁]
  have hW : ∑ i, (W i)ᴴ * W i ≤ 1 := by
    have h := hsum 1
    simp only [Pi.one_apply, Matrix.mul_one, h1] at h
    rw [h, Matrix.le_iff, show (1 : Matrix (k ⊕ m) (k ⊕ m) ℂ) - fromBlocks 0 0 0 (∑ i, (A i)ᴴ * A i) =
        fromBlocks 1 0 0 0 + fromBlocks 0 0 0 (1 - ∑ i, (A i)ᴴ * A i) by
      ext (a | a) (b | b) <;> simp [Matrix.one_apply]]
    refine PosSemidef.add ?_ (posSemidef_fromBlocks_zero_zero_zero (Matrix.le_iff.1 hA))
    simpa [fromBlocks_conjTranspose, fromBlocks_multiply] using
      posSemidef_conjTranspose_mul_self (fromBlocks (1 : Matrix k k ℂ) 0 0 (0 : Matrix m m ℂ))
  have h := hf.cfc_sum_le_of_le_one h0 hf0 W X hX hW
  have hcT (i : ι) : (cfc f (fromBlocks (T i) 0 0 (0 : Matrix m m ℂ))).toBlocks₁₁ = cfc f (T i) := by
    rw [cfc_fromBlocks_zero_zero f (hT i).1 h0m.1, toBlocks_fromBlocks₁₁]
  rw [hsum X, hsum fun i => cfc f (X i)] at h
  simp only [X, toBlocks_fromBlocks₁₁, hcT] at h
  rw [cfc_fromBlocks_zero_zero f h0k.1
    (isSelfAdjoint_sum_conjTranspose_mul_mul A fun i => (hT i).1)] at h
  simpa using toBlocks₂₂_mono h

namespace Matrix

/-! ### Consequences for the CFC real power

Unfolded operator concavity of real powers and monotonicity of the trace pairing (positive
semidefiniteness of real powers is `Matrix.posSemidef_rpow` in `HermitianFunctionalCalculus.lean`).
Together with Löwner–Heinz monotonicity
(`Matrix.rpow_le_rpow` in `LiebConcavity.lean`, a wrapper around Mathlib's
`CFC.rpow_le_rpow`), they extend Lieb's joint concavity from the boundary case
`p + q = 1` to the full region `p + q ≤ 1`
(`Matrix.lieb_joint_concavity_general`). -/

/-- Operator concavity of `x ↦ xˢ` for `0 ≤ s ≤ 1`, in unfolded form:
`t • Aˢ + (1 - t) • Bˢ ≤ (t • A + (1 - t) • B)ˢ` on positive semidefinite
matrices (Mathlib's `CFC.concaveOn_rpow`). -/
lemma rpow_concavity_le {m : Type*} [Fintype m] [DecidableEq m]
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    {A B : Matrix m m ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t • A ^ s + (1 - t) • B ^ s ≤ (t • A + (1 - t) • B) ^ s := by
  open scoped Matrix.Norms.L2Operator in
  exact (CFC.concaveOn_rpow ⟨hs0, hs1⟩).2 hA.nonneg hB.nonneg ht0 (sub_nonneg.2 ht1)
    (add_sub_cancel t 1)

/-- Monotonicity of the trace pairing against a positive semidefinite matrix:
`X ≤ Y` implies `Re Tr(X·M) ≤ Re Tr(Y·M)` for `M` positive semidefinite: `Tr((Y - X) M) ≥ 0` as
`Y - X` and `M` are positive semidefinite (`Matrix.PosSemidef.trace_mul_nonneg`). -/
lemma trace_mul_mono_of_posSemidef {m : Type*} [Fintype m]
    {X Y M : Matrix m m ℂ} (hXY : X ≤ Y) (hM : M.PosSemidef) :
    (X * M).trace.re ≤ (Y * M).trace.re := by
  have h := (Complex.le_def.1 ((Matrix.le_iff.1 hXY).trace_mul_nonneg hM)).1
  rwa [Matrix.sub_mul, trace_sub, Complex.sub_re, Complex.zero_re, sub_nonneg] at h

end Matrix
