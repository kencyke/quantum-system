/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.RingInverseOrder
public import QuantumSystem.Analysis.Matrix.HermitianFunctionalCalculus
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
public import QuantumSystem.ForMathlib.Analysis.Matrix.Hermitian
public import QuantumSystem.ForMathlib.Analysis.Matrix.Order

/-!
# Operator convexity and Jensen's operator inequality for matrices

This file formalises the Effros (2008) machinery used to prove Lieb's joint concavity theorem
and related operator-convexity results.

## Main definitions

- `Matrix.IsLownerMonotoneOn s f`, `Matrix.IsLownerAntitoneOn s f`, `Matrix.IsLownerConvexOn s f`,
  `Matrix.IsLownerConcaveOn s f`: in every matrix dimension, `A ↦ f(A)` is monotone / antitone /
  convex / concave in the Löwner order on self-adjoint matrices with spectrum in `s`, stated with
  Mathlib's `MonotoneOn`, `AntitoneOn`, `ConvexOn`, `ConcaveOn`. For `s = [0, ∞)` the domain is the
  positive semidefinite cone `Set.Ici 0`, for `s = (0, ∞)` the positive definite matrices
  `{A | IsStrictlyPositive A}`; `s` is meant to be an interval, since for an `s` with a gap the
  domain is not convex and the convex / concave predicates fail for every `f`. The domain is a
  parameter because `Real.log 0 = 0` and `0 ^ p = 0` for `p < 0`: the logarithm is Löwner monotone
  and concave, and `tᵖ` (`-1 ≤ p < 0`) Löwner convex, on `(0, ∞)`, but the logarithm is not Löwner
  monotone on `[0, ∞)` (`Matrix.not_log_isLownerMonotoneOn_Ici`).
- `Matrix.IsJensenConvex f`: for A†A + B†B ≤ I and positive semidefinite T₁, T₂,
  f(A† T₁ A + B† T₂ B) ≤ A† f(T₁) A + B† f(T₂) B.

## Main results

- `Matrix.lownerConvex_compression_le`: f(V†TV) ≤ V†f(T)V for f Löwner convex on `[0, ∞)` with
  f(0) ≤ 0 and V†V ≤ I.
- `Matrix.isJensenConvex_iff` (Hansen–Pedersen 1982): f is Jensen convex iff it is Löwner convex
  on `[0, ∞)` and f(0) ≤ 0. The direction `Matrix.isJensenConvex_of_isLownerConvexOn` follows
  the defect-matrix proof of Hansen–Pedersen; the converse is `Matrix.IsJensenConvex.isLownerConvexOn`
  with `Matrix.IsJensenConvex.map_zero_nonpos`.
- `Matrix.IsLownerConvexOn.comp_isLownerConcaveOn`: a Löwner convex and antitone function of a
  Löwner concave function is Löwner convex.
- `Matrix.lownerConvex_isometry_compression_le`: f(W†TW) ≤ W†f(T)W for f Löwner convex on
  `[0, ∞)` and an isometry W, with no condition on f(0).
- `Matrix.hpj_affine`: Jensen's operator inequality for f Löwner convex on `[0, ∞)` and
  A†A + B†B = I.
- `Matrix.rpow_isLownerMonotoneOn`, `Matrix.rpow_isLownerConcaveOn`: tˢ (0 ≤ s ≤ 1) is Löwner
  monotone and concave on `[0, ∞)` (Löwner–Heinz; Mathlib's `CFC.monotone_rpow`,
  `CFC.concaveOn_rpow`), and `Matrix.neg_rpow_isLownerConvexOn`, `Matrix.neg_rpow_isJensenConvex`.
- `Matrix.log_isLownerMonotoneOn`, `Matrix.log_isLownerConcaveOn`: log is Löwner monotone and
  concave on `(0, ∞)`; `Matrix.not_log_isLownerMonotoneOn_Ici`: not monotone on `[0, ∞)`.
- `Matrix.inv_isLownerConvexOn`, `Matrix.inv_isLownerAntitoneOn`: t⁻¹ is Löwner convex and
  antitone on `(0, ∞)`.
- `Matrix.rpow_isLownerConvexOn_of_nonpos`: tᵖ (−1 ≤ p ≤ 0) is Löwner convex on `(0, ∞)`.
- `Matrix.rpow_concavity_le`: operator concavity of xˢ in unfolded form.

## References

* Effros, *A Matrix Convexity Approach to Some Celebrated Quantum Inequalities* (2008)
* F. Hansen, G. K. Pedersen, *Jensen's inequality for operators and Löwner's theorem*,
  Math. Ann. 258 (1982), 229–241
* F. Hansen, G. K. Pedersen, *Jensen's operator inequality*, Bull. London Math. Soc. 35 (2003),
  553–564
* Bhatia, *Matrix Analysis*, Chapter V (1997)
-/
@[expose] public section

namespace Matrix

open Real NNReal Set
open scoped MatrixOrder ComplexOrder NNReal

/-! ### Löwner monotone, antitone, convex and concave functions

The domain of `A ↦ f(A)` is the set of self-adjoint matrices with spectrum in `s`. For
`s = [0, ∞)` this is the positive semidefinite cone `Set.Ici 0`
(`setOf_isSelfAdjoint_spectrum_subset_Ici`), and for `s = (0, ∞)` the positive definite matrices
`{A | IsStrictlyPositive A}` (`setOf_isSelfAdjoint_spectrum_subset_Ioi`). The domain is convex when
`s` is an interval (`Set.OrdConnected.convex_setOf_isSelfAdjoint_spectrum_subset`). -/

/-- A real function `f` is **Löwner monotone** (operator monotone) on `s ⊆ ℝ`: in every matrix
dimension, `A ↦ f(A)` is monotone in the Löwner order on self-adjoint matrices with spectrum in
`s`. -/
def IsLownerMonotoneOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ (m : Type*) [Fintype m] [DecidableEq m],
    MonotoneOn (fun A : Matrix m m ℂ => cfc f A) {A | IsSelfAdjoint A ∧ spectrum ℝ A ⊆ s}

/-- A real function `f` is **Löwner antitone** (operator antitone) on `s ⊆ ℝ`: in every matrix
dimension, `A ↦ f(A)` is antitone in the Löwner order on self-adjoint matrices with spectrum in
`s`. -/
def IsLownerAntitoneOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ (m : Type*) [Fintype m] [DecidableEq m],
    AntitoneOn (fun A : Matrix m m ℂ => cfc f A) {A | IsSelfAdjoint A ∧ spectrum ℝ A ⊆ s}

/-- A real function `f` is **Löwner convex** (operator convex) on `s ⊆ ℝ`: in every matrix
dimension, `A ↦ f(A)` is convex in the Löwner order on self-adjoint matrices with spectrum in
`s`. This requires `s` to be an interval, since `ConvexOn` includes convexity of the domain. -/
def IsLownerConvexOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ (m : Type*) [Fintype m] [DecidableEq m],
    ConvexOn ℝ {A : Matrix m m ℂ | IsSelfAdjoint A ∧ spectrum ℝ A ⊆ s} (fun A => cfc f A)

/-- A real function `f` is **Löwner concave** (operator concave) on `s ⊆ ℝ`: in every matrix
dimension, `A ↦ f(A)` is concave in the Löwner order on self-adjoint matrices with spectrum in
`s`. This requires `s` to be an interval, since `ConcaveOn` includes convexity of the domain. -/
def IsLownerConcaveOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ (m : Type*) [Fintype m] [DecidableEq m],
    ConcaveOn ℝ {A : Matrix m m ℂ | IsSelfAdjoint A ∧ spectrum ℝ A ⊆ s} (fun A => cfc f A)

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

/-- Löwner convexity in unfolded form: `f(tA + (1-t)B) ≤ t f(A) + (1-t) f(B)` for `A, B` in the
domain and `t ∈ [0, 1]`. -/
lemma IsLownerConvexOn.cfc_le.{v} {s : Set ℝ} {f : ℝ → ℝ} (hconv : IsLownerConvexOn.{v} s f)
    {m : Type v} [Fintype m] [DecidableEq m] {A B : Matrix m m ℂ}
    (hA : A ∈ {A : Matrix m m ℂ | IsSelfAdjoint A ∧ spectrum ℝ A ⊆ s})
    (hB : B ∈ {A : Matrix m m ℂ | IsSelfAdjoint A ∧ spectrum ℝ A ⊆ s})
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    cfc f (t • A + (1 - t) • B) ≤ t • cfc f A + (1 - t) • cfc f B :=
  (hconv m).2 hA hB ht0 (sub_nonneg.2 ht1) (add_sub_cancel t 1)

/-- `f` is Löwner convex iff `-f` is Löwner concave. -/
lemma isLownerConvexOn_neg_iff.{v} {s : Set ℝ} {f : ℝ → ℝ} :
    IsLownerConvexOn.{v} s (fun x => -f x) ↔ IsLownerConcaveOn.{v} s f := by
  refine forall_congr' fun m => forall_congr' fun _ => forall_congr' fun _ => ?_
  have : (fun A : Matrix m m ℂ => cfc (fun x => -f x) A) = -fun A => cfc f A := by
    funext A; simp [cfc_neg]
  rw [this, neg_convexOn_iff]

/-- Löwner convexity only depends on the values of `f` on `s`. -/
lemma IsLownerConvexOn.congr.{v} {s : Set ℝ} {f g : ℝ → ℝ} (h : IsLownerConvexOn.{v} s f)
    (hfg : EqOn f g s) : IsLownerConvexOn.{v} s g :=
  fun m _ _ => (h m).congr fun _ hA => cfc_congr fun _ hx => hfg (hA.2 hx)

/-- Löwner antitonicity only depends on the values of `f` on `s`. -/
lemma IsLownerAntitoneOn.congr.{v} {s : Set ℝ} {f g : ℝ → ℝ} (h : IsLownerAntitoneOn.{v} s f)
    (hfg : EqOn f g s) : IsLownerAntitoneOn.{v} s g :=
  fun m _ _ => (h m).congr fun _ hA => cfc_congr fun _ hx => hfg (hA.2 hx)

/-- Löwner concavity on `s` restricts to any interval `t ⊆ s`. -/
lemma IsLownerConcaveOn.subset.{v} {s t : Set ℝ} {f : ℝ → ℝ} (h : IsLownerConcaveOn.{v} s f)
    (hts : t ⊆ s) (ht : t.OrdConnected) : IsLownerConcaveOn.{v} t f :=
  fun m _ _ => (h m).subset (fun _ hA => ⟨hA.1, hA.2.trans hts⟩)
    ht.convex_setOf_isSelfAdjoint_spectrum_subset

/-- Löwner monotonicity on `s` restricts to any `t ⊆ s`. -/
lemma IsLownerMonotoneOn.subset.{v} {s t : Set ℝ} {f : ℝ → ℝ} (h : IsLownerMonotoneOn.{v} s f)
    (hts : t ⊆ s) : IsLownerMonotoneOn.{v} t f :=
  fun m _ _ => (h m).mono fun _ hA => ⟨hA.1, hA.2.trans hts⟩

/-- `f(A)` lies in the domain for `t` when `A` lies in the domain for `s` and `f` maps `s` into
`t`. -/
private lemma cfc_mem_setOf_isSelfAdjoint_spectrum_subset {m : Type*} [Fintype m] [DecidableEq m]
    {s t : Set ℝ} {f : ℝ → ℝ} (hst : MapsTo f s t) {A : Matrix m m ℂ}
    (hA : A ∈ {A : Matrix m m ℂ | IsSelfAdjoint A ∧ spectrum ℝ A ⊆ s}) :
    cfc f A ∈ {A : Matrix m m ℂ | IsSelfAdjoint A ∧ spectrum ℝ A ⊆ t} := by
  refine ⟨cfc_predicate f A, ?_⟩
  rw [cfc_map_spectrum (f := f) (a := A) hA.1 (finite_real_spectrum.continuousOn _)]
  exact image_subset_iff.2 fun _ hx => hst (hA.2 hx)

/-- A Löwner convex and antitone function of a Löwner concave function is Löwner convex. -/
lemma IsLownerConvexOn.comp_isLownerConcaveOn.{v} {s t : Set ℝ} {g f : ℝ → ℝ}
    (hg : IsLownerConvexOn.{v} t g) (hg' : IsLownerAntitoneOn.{v} t g)
    (hf : IsLownerConcaveOn.{v} s f) (hst : MapsTo f s t) :
    IsLownerConvexOn.{v} s (g ∘ f) := by
  intro m _ _
  have hcomp : ∀ A : Matrix m m ℂ, IsSelfAdjoint A → cfc (g ∘ f) A = cfc g (cfc f A) :=
    fun A hA => cfc_comp g f A hA ((finite_real_spectrum.image f).continuousOn _)
      (finite_real_spectrum.continuousOn _)
  refine ⟨(hf m).1, fun A hA B hB a b ha hb hab => ?_⟩
  have hAB := (hf m).1 hA hB ha hb hab
  have hfA := cfc_mem_setOf_isSelfAdjoint_spectrum_subset hst hA
  have hfB := cfc_mem_setOf_isSelfAdjoint_spectrum_subset hst hB
  simp only
  rw [hcomp _ hAB.1, hcomp _ hA.1, hcomp _ hB.1]
  calc cfc g (cfc f (a • A + b • B))
      ≤ cfc g (a • cfc f A + b • cfc f B) :=
        (hg' m) ((hg m).1 hfA hfB ha hb hab)
          (cfc_mem_setOf_isSelfAdjoint_spectrum_subset hst hAB) ((hf m).2 hA hB ha hb hab)
    _ ≤ a • cfc g (cfc f A) + b • cfc g (cfc f B) := (hg m).2 hfA hfB ha hb hab

/-- Jensen convexity (HPJ sense) on `[0, ∞)`: compression inequality for two terms.
For A†A + B†B ≤ I and PSD T₁, T₂:
f(A† T₁ A + B† T₂ B) ≤ A† f(T₁) A + B† f(T₂) B. The domain is the positive semidefinite cone:
`A = B = 0` is allowed, which forces `f 0 ≤ 0` (`Matrix.isJensenConvex_iff`). -/
def IsJensenConvex (f : ℝ → ℝ) : Prop :=
  ∀ (m : Type*) [Fintype m] [DecidableEq m]
    (A B T₁ T₂ : Matrix m m ℂ)
    (_hT₁ : T₁.PosSemidef) (_hT₂ : T₂.PosSemidef)
    (_hAB : Aᴴ * A + Bᴴ * B ≤ (1 : Matrix m m ℂ)),
    let fT₁ := cfc f T₁
    let fT₂ := cfc f T₂
    let fC := cfc f (Aᴴ * T₁ * A + Bᴴ * T₂ * B)
    fC ≤ Aᴴ * fT₁ * A + Bᴴ * fT₂ * B

/-- Block diagonal matrix is positive semidefinite if blocks are positive semidefinite. -/
private lemma fromBlocks_posSemidef_diag {m n : Type*} [Finite m] [Finite n]
  {A : Matrix m m ℂ} {D : Matrix n n ℂ}
    (hA : A.PosSemidef) (hD : D.PosSemidef) :
    (Matrix.fromBlocks A 0 0 D).PosSemidef := by
  let := Fintype.ofFinite m
  let := Fintype.ofFinite n
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

/-- **Jensen's operator inequality for isometries** (Davis 1957, Choi 1974): for Löwner convex
`f`, an isometry `W` (`W†W = I`) and positive semidefinite `T`, `f(W†TW) ≤ W†f(T)W`. No condition
on `f(0)` is needed.

The proof is the pinching argument: with `P = WW†` and the symmetry `S = 2P - 1`, the matrix
`M = (T + STS)/2` commutes with `P`, so `W†f(M)W = f(W†MW) = f(W†TW)`, while convexity gives
`f(M) ≤ (f(T) + S f(T) S)/2`, whose compression by `W` is `W†f(T)W`. -/
lemma lownerConvex_isometry_compression_le.{v} {k m : Type v} [Fintype k] [Fintype m]
    [DecidableEq k] [DecidableEq m]
    {f : ℝ → ℝ} (hconv : IsLownerConvexOn.{v} (Ici 0) f)
    (W : Matrix k m ℂ) (hWW : Wᴴ * W = 1) (T' : Matrix k k ℂ) (hT'_psd : T'.PosSemidef) :
    cfc f (Wᴴ * T' * W) ≤ Wᴴ * cfc f T' * W := by
  classical
  have hT'_herm : T'.IsHermitian := hT'_psd.1
  set P : Matrix k k ℂ := W * Wᴴ with hP_def
  have hP_sq : P * P = P := by
    change W * Wᴴ * (W * Wᴴ) = W * Wᴴ
    rw [Matrix.mul_assoc W Wᴴ (W * Wᴴ),
        show Wᴴ * (W * Wᴴ) = (Wᴴ * W) * Wᴴ from (Matrix.mul_assoc _ _ _).symm,
        hWW, Matrix.one_mul]
  have hP_herm : Pᴴ = P := by
    change (W * Wᴴ)ᴴ = W * Wᴴ
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
  set S : Matrix k k ℂ := (2 : ℝ) • P - 1 with hS_def
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
  have hS_mem_unitary : S ∈ unitary (Matrix k k ℂ) := by
    rw [Unitary.mem_iff]; exact ⟨by rw [hS_star_eq, hS_sq], by rw [hS_star_eq, hS_sq]⟩
  let S_unit : unitary (Matrix k k ℂ) := ⟨S, hS_mem_unitary⟩
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
  set M : Matrix k k ℂ := (1/2 : ℝ) • T' + (1/2 : ℝ) • (S * T' * S) with hM_def
  have hM_eq : M = (1/2 : ℝ) • T' + (1 - 1/2 : ℝ) • (S * T' * S) := by
    simp only [hM_def]; congr 1; congr 1; norm_num
  have hM_herm' : M.IsHermitian := by rw [hM_eq]; exact hM_herm
  have hconv_app := hconv.cfc_le hT'_psd.mem_setOf_isSelfAdjoint_spectrum_subset_Ici
    hST'S_psd.mem_setOf_isSelfAdjoint_spectrum_subset_Ici (t := 1/2) (by norm_num) (by norm_num)
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
    {f : ℝ → ℝ} (hconv : IsLownerConvexOn.{v} (Ici 0) f) (hf0 : f 0 ≤ 0)
    (V : Matrix n m ℂ) (hVV : Vᴴ * V ≤ 1)
    (T : Matrix n n ℂ) (hT : T.PosSemidef) :
    cfc f (Vᴴ * T * V) ≤ Vᴴ * cfc f T * V := by
  -- The proof uses the defect technique and the block diagonal CFC formula.
  classical
  -- Step 1: Setup the defect matrix D = √(I - V†V)
  have hΔ : ((1 : Matrix m m ℂ) - Vᴴ * V).PosSemidef := by
    simpa [Matrix.le_iff] using hVV
  let D := ((1 : Matrix m m ℂ) - Vᴴ * V) ^ (1 / 2 : ℝ)
  have hD_herm : D.IsHermitian := (posSemidef_rpow _ _).isHermitian
  have hDD : D * D = (1 : Matrix m m ℂ) - Vᴴ * V := rpow_half_mul_rpow_half hΔ
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
      exact hT.1.isSelfAdjoint
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
  have h_jensen : cfc f (Wᴴ * T' * W) ≤ Wᴴ * cfc f T' * W :=
    lownerConvex_isometry_compression_le hconv W hWW T' hT'_psd
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
    let D := Δ ^ (1 / 2 : ℝ)
    Dᴴ * D = Δ := by
  intro V Δ D
  have hΔ : Δ.PosSemidef := by
    simpa [Δ, V] using Matrix.PosSemidef.one_sub_fromRows (A := A) (B := B) hAB
  calc
    Dᴴ * D = D * D := by
      have hherm : D.IsHermitian := by
        simpa [D, Δ, V] using (posSemidef_rpow _ _).isHermitian
      simp [hherm.eq]
    _ = Δ := by
      simpa [D] using rpow_half_mul_rpow_half hΔ

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

/-- Löwner convexity on `[0, ∞)` with f(0) ≤ 0 implies the HPJ inequality (Jensen convexity).
Theorem 3.1 in Effros 2008, originally Hansen–Pedersen 1982 Theorem 2.1 (i)⟹(iii).

The proof reduces the 2-term subhomogeneous case to:
1. A single-term compression inequality: f(V†TV) ≤ V†f(T)V when V†V ≤ I
2. The block diagonal CFC identity: V†f(T₁⊕T₂)V = A†f(T₁)A + B†f(T₂)B

Step 1 uses the defect matrix D = √(I - V†V) and f(0) ≤ 0 to absorb the defect term.
Step 2 is compression_of_fromBlocks_cfc (already proved). -/
lemma isJensenConvex_of_isLownerConvexOn.{v}
    {f : ℝ → ℝ} (hconv : IsLownerConvexOn.{v} (Ici 0) f) (hf0 : f 0 ≤ 0) :
    IsJensenConvex.{v} f := by
  classical
  intro m _ _ A B T₁ T₂ hT₁ hT₂ hAB
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
  let D := Δ ^ (1 / 2 : ℝ)
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

/-- Jensen convexity implies Löwner convexity on `[0, ∞)`: take the scalars `A = √t`,
`B = √(1 - t)` in `IsJensenConvex`. -/
lemma IsJensenConvex.isLownerConvexOn.{v} {f : ℝ → ℝ} (hJ : IsJensenConvex.{v} f) :
    IsLownerConvexOn.{v} (Ici 0) f := by
  intro m _ _
  rw [setOf_isSelfAdjoint_spectrum_subset_Ici]
  refine ⟨convex_Ici 0, fun T₁ hT₁ T₂ hT₂ a b ha hb hab => ?_⟩
  have hsq {c : ℝ} (hc : 0 ≤ c) (T : Matrix m m ℂ) :
      (√c • (1 : Matrix m m ℂ))ᴴ * T * (√c • 1) = c • T := by
    simp only [conjTranspose_smul, conjTranspose_one, star_trivial, smul_mul_assoc,
      mul_smul_comm, one_mul, mul_one, smul_smul, Real.mul_self_sqrt hc]
  have key := hJ m (√a • 1) (√b • 1) T₁ T₂ (nonneg_iff_posSemidef.mp hT₁)
    (nonneg_iff_posSemidef.mp hT₂) (by
      rw [← Matrix.mul_one (√a • (1 : Matrix m m ℂ))ᴴ, ← Matrix.mul_one (√b • (1 : Matrix m m ℂ))ᴴ,
        hsq ha, hsq hb, ← add_smul, hab, one_smul])
  simp only [hsq ha, hsq hb] at key
  exact key

/-- Jensen convexity forces `f 0 ≤ 0`: take `A = B = 0` in dimension one. -/
lemma IsJensenConvex.map_zero_nonpos.{v} {f : ℝ → ℝ} (hJ : IsJensenConvex.{v} f) : f 0 ≤ 0 := by
  have h := hJ PUnit.{v + 1} 0 0 0 0 PosSemidef.zero PosSemidef.zero (by simp)
  simp only [Matrix.mul_zero, add_zero] at h
  rw [← map_zero (algebraMap ℝ (Matrix PUnit.{v + 1} PUnit.{v + 1} ℂ)), cfc_algebraMap] at h
  exact (le_algebraMap_iff_spectrum_le (IsSelfAdjoint.algebraMap _ (.all _))).1 h _
    (by rw [spectrum.scalar_eq]; rfl)

/-- **Hansen–Pedersen** (1982, Theorem 2.1, stated there on `[0, α)`; this is the case `α = ∞`):
`f` is Jensen convex on `[0, ∞)` iff it is Löwner convex on `[0, ∞)` and `f 0 ≤ 0`. -/
theorem isJensenConvex_iff.{v} {f : ℝ → ℝ} :
    IsJensenConvex.{v} f ↔ IsLownerConvexOn.{v} (Ici 0) f ∧ f 0 ≤ 0 :=
  ⟨fun h => ⟨h.isLownerConvexOn, h.map_zero_nonpos⟩,
    fun h => isJensenConvex_of_isLownerConvexOn h.1 h.2⟩

/-- **Operator concavity of the power function** (Löwner–Heinz; Bhatia, Chapter V): `t ↦ tˢ` is
Löwner concave on `[0, ∞)` for `0 ≤ s ≤ 1`. This is Mathlib's `CFC.concaveOn_rpow` on the
C⋆-algebra `Matrix.Norms.L2Operator` of matrices. -/
lemma rpow_isLownerConcaveOn {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    IsLownerConcaveOn (Ici 0) (fun t => t ^ s) := by
  intro m _ _
  rw [setOf_isSelfAdjoint_spectrum_subset_Ici]
  open scoped Matrix.Norms.L2Operator in
  exact (CFC.concaveOn_rpow ⟨hs0, hs1⟩).congr fun A hA =>
    CFC.rpow_eq_cfc_real (a := A) hA

/-- **Löwner–Heinz theorem** (Bhatia, Theorem V.1.9): `t ↦ tˢ` is Löwner monotone on `[0, ∞)` for
`0 ≤ s ≤ 1`. This is Mathlib's `CFC.monotone_rpow`. -/
lemma rpow_isLownerMonotoneOn {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    IsLownerMonotoneOn (Ici 0) (fun t => t ^ s) := by
  intro m _ _
  rw [setOf_isSelfAdjoint_spectrum_subset_Ici]
  open scoped Matrix.Norms.L2Operator in
  exact ((CFC.monotone_rpow ⟨hs0, hs1⟩).monotoneOn _).congr fun A hA =>
    CFC.rpow_eq_cfc_real (a := A) hA

/-- The negated power function `-tˢ` (`0 ≤ s ≤ 1`) is Löwner convex on `[0, ∞)`. -/
lemma neg_rpow_isLownerConvexOn {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    IsLownerConvexOn (Ici 0) (fun t => -(t ^ s)) :=
  isLownerConvexOn_neg_iff.2 (rpow_isLownerConcaveOn hs0 hs1)

/-- The matrix logarithm is Löwner monotone on `(0, ∞)` (Mathlib's `CFC.log_monotoneOn`). On
`[0, ∞)` it is not (`not_log_isLownerMonotoneOn_Ici`). -/
lemma log_isLownerMonotoneOn : IsLownerMonotoneOn (Ioi 0) Real.log := by
  intro m _ _
  rw [setOf_isSelfAdjoint_spectrum_subset_Ioi]
  open scoped Matrix.Norms.L2Operator in
  exact CFC.log_monotoneOn

/-- The matrix logarithm is **not** Löwner monotone on `[0, ∞)`: `Real.log 0 = 0`, so in dimension
one `0 ≤ ½` but `log 0 = 0 > log ½`. -/
lemma not_log_isLownerMonotoneOn_Ici.{v} : ¬ IsLownerMonotoneOn.{v} (Ici 0) Real.log := by
  intro h
  have hmono := h PUnit.{v + 1}
  rw [setOf_isSelfAdjoint_spectrum_subset_Ici] at hmono
  have hspec (r : ℝ) :
      spectrum ℝ (algebraMap ℝ (Matrix PUnit.{v + 1} PUnit.{v + 1} ℂ) r) = {r} :=
    spectrum.scalar_eq (A := Matrix PUnit.{v + 1} PUnit.{v + 1} ℂ) r
  have hc : algebraMap ℝ (Matrix PUnit.{v + 1} PUnit.{v + 1} ℂ) 0 ≤
      algebraMap ℝ (Matrix PUnit.{v + 1} PUnit.{v + 1} ℂ) (1 / 2) :=
    (algebraMap_le_iff_le_spectrum (IsSelfAdjoint.algebraMap _ (.all _))).2 fun x hx => by
      rw [hspec, Set.mem_singleton_iff] at hx
      rw [hx]; norm_num
  have h0 : (0 : Matrix PUnit.{v + 1} PUnit.{v + 1} ℂ) ≤ algebraMap ℝ _ 0 := by rw [map_zero]
  have hle := hmono h0 (h0.trans hc) hc
  simp only [cfc_algebraMap] at hle
  have hlog := (algebraMap_le_iff_le_spectrum (IsSelfAdjoint.algebraMap _ (.all _))).1 hle
    (Real.log (1 / 2)) (by rw [hspec]; rfl)
  rw [Real.log_zero] at hlog
  exact absurd hlog (not_le.2 (Real.log_neg (by norm_num) (by norm_num)))

/-- The matrix logarithm is Löwner concave on `(0, ∞)` (Mathlib's `CFC.concaveOn_log`). -/
lemma log_isLownerConcaveOn : IsLownerConcaveOn (Ioi 0) Real.log := by
  intro m _ _
  rw [setOf_isSelfAdjoint_spectrum_subset_Ioi]
  open scoped Matrix.Norms.L2Operator in
  exact CFC.concaveOn_log

/-- The inverse `t ↦ t⁻¹` is Löwner convex on `(0, ∞)` (Mathlib's
`CStarAlgebra.convexOn_ringInverse`). -/
lemma inv_isLownerConvexOn : IsLownerConvexOn (Ioi 0) (fun t => t⁻¹) := by
  intro m _ _
  rw [setOf_isSelfAdjoint_spectrum_subset_Ioi]
  open scoped Matrix.Norms.L2Operator in
  exact CStarAlgebra.convexOn_ringInverse.congr fun A hA =>
    (cfc_ringInverse_id (R := ℝ) (a := A) hA.isUnit).symm

/-- The inverse `t ↦ t⁻¹` is Löwner antitone on `(0, ∞)` (Mathlib's
`CStarAlgebra.antitoneOn_ringInverse`). -/
lemma inv_isLownerAntitoneOn : IsLownerAntitoneOn (Ioi 0) (fun t => t⁻¹) := by
  intro m _ _
  rw [setOf_isSelfAdjoint_spectrum_subset_Ioi]
  open scoped Matrix.Norms.L2Operator in
  exact CStarAlgebra.antitoneOn_ringInverse.congr fun A hA =>
    (cfc_ringInverse_id (R := ℝ) (a := A) hA.isUnit).symm

/-- `t ↦ tᵖ` is Löwner convex on `(0, ∞)` for `-1 ≤ p ≤ 0` (Bhatia, Chapter V): it is the inverse,
Löwner convex and antitone, of the Löwner concave `t ↦ t⁻ᵖ`. -/
lemma rpow_isLownerConvexOn_of_nonpos {p : ℝ} (hp1 : -1 ≤ p) (hp0 : p ≤ 0) :
    IsLownerConvexOn (Ioi 0) (fun t => t ^ p) := by
  have h := inv_isLownerConvexOn.comp_isLownerConcaveOn inv_isLownerAntitoneOn
    ((rpow_isLownerConcaveOn (s := -p) (by linarith) (by linarith)).subset Ioi_subset_Ici_self
      ordConnected_Ioi)
    (fun _ ht => Real.rpow_pos_of_pos ht _)
  refine h.congr fun t ht => ?_
  simp only [Function.comp_apply]
  rw [← Real.rpow_neg (le_of_lt ht), neg_neg]

/-- The function `f(t) = −t^s` is Jensen convex for `0 < s ≤ 1`, by
`isJensenConvex_of_isLownerConvexOn`: `f` is Löwner convex and `f(0) = 0`. -/
lemma neg_rpow_isJensenConvex.{v} {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    IsJensenConvex.{v} (fun t => -(t ^ s)) := by
  apply isJensenConvex_of_isLownerConvexOn.{v} (neg_rpow_isLownerConvexOn hs0.le hs1)
  simp only [Real.zero_rpow (ne_of_gt hs0), neg_zero]
  exact le_refl 0

/-- **Jensen's operator inequality** (Hansen–Pedersen), two-term affine case: for `f` Löwner
convex on `[0, ∞)`, `A†A + B†B = I` and positive semidefinite `T₁, T₂`,
`f(A† T₁ A + B† T₂ B) ≤ A† f(T₁) A + B† f(T₂) B`. No condition on `f(0)` is needed; compare
`isJensenConvex_of_isLownerConvexOn`, where `A†A + B†B ≤ I` forces `f(0) ≤ 0`. -/
lemma hpj_affine.{v} {f : ℝ → ℝ} (hconv : IsLownerConvexOn.{v} (Ici 0) f)
    {m : Type v} [Fintype m] [DecidableEq m]
    (A B T₁ T₂ : Matrix m m ℂ)
    (hT₁ : T₁.PosSemidef) (hT₂ : T₂.PosSemidef)
    (hAB : Aᴴ * A + Bᴴ * B = (1 : Matrix m m ℂ)) :
    cfc f (Aᴴ * T₁ * A + Bᴴ * T₂ * B) ≤ Aᴴ * cfc f T₁ * A + Bᴴ * cfc f T₂ * B := by
  classical
  let V := Matrix.fromRows A B
  let T := Matrix.fromBlocks T₁ 0 0 T₂
  have hVV : Vᴴ * V = 1 := by simpa [V, fromRows_conjTranspose_mul_self] using hAB
  rw [← fromRows_compress_blockDiag A B T₁ T₂,
    ← compression_of_fromBlocks_cfc A B T₁ T₂ hT₁ hT₂ f]
  exact lownerConvex_isometry_compression_le hconv V hVV T (fromBlocks_posSemidef_diag hT₁ hT₂)

/-! ### Consequences for the CFC real power

Positive semidefiniteness of real powers, unfolded operator concavity, and
monotonicity of the trace pairing. Together with Löwner–Heinz monotonicity
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
`X ≤ Y` implies `Re Tr(X·M) ≤ Re Tr(Y·M)` for `M` positive semidefinite.
Proved by conjugating with `M^{1/2}` and applying `trace_mono`. -/
lemma trace_mul_mono_of_posSemidef {m : Type*} [Fintype m]
    {X Y M : Matrix m m ℂ} (hXY : X ≤ Y) (hM : M.PosSemidef) :
    (X * M).trace.re ≤ (Y * M).trace.re := by
  classical
  set S : Matrix m m ℂ := M ^ (1 / 2 : ℝ) with hS_def
  have hSH : Sᴴ = S := (posSemidef_rpow _ _).isHermitian
  have hSS : S * S = M := rpow_half_mul_rpow_half hM
  have hkey : ∀ Z : Matrix m m ℂ, (Z * M).trace = (Sᴴ * Z * S).trace := by
    intro Z
    rw [hSH, ← hSS, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  have h := trace_mono (compression_le hXY S)
  rwa [← hkey X, ← hkey Y] at h

end Matrix
