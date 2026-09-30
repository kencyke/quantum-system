/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap

/-!
# `k`-positive maps

A ℂ-linear map `φ` between C⋆-algebras is **`k`-positive** if applying it entrywise to a `k × k`
matrix over its domain preserves nonnegativity (Paulsen, *Completely Bounded Maps and Operator
Algebras*, Ch. 3). Mathlib's completely positive maps (`CompletelyPositiveMap`) are the maps that
are `k`-positive for every `k`; this file adds the notion at a single matrix size `k`, mirroring
Mathlib's structure and morphism class.

The main result is the **Kadison–Schwarz inequality** of Choi (*A Schwarz inequality for positive
linear maps on C⋆-algebras*, Illinois J. Math. 18 (1974)): a `2`-positive map with `φ 1 ≤ 1`
satisfies `φ(a)⋆ φ(a) ≤ φ(a⋆ a)`. As completely positive maps are `2`-positive, it applies to them.

## Main definitions

* `KPositiveMap k A₁ A₂` — `k`-positive ℂ-linear maps.
* `KPositiveMapClass F k A₁ A₂` — the corresponding morphism class. As
  `CompletelyPositiveMapClass`, it records only the order property and is meant to be used
  together with `LinearMapClass`.

## Main results

* `CStarMatrix.diag_nonneg` — the diagonal entries of a nonnegative `CStarMatrix` are
  nonnegative.
* `CompletelyPositiveMap.instKPositiveMapClass` — completely positive maps are `k`-positive.
* `KPositiveMapClass.le_map_star_mul` — the Kadison–Schwarz inequality for `2`-positive maps with
  `φ 1 ≤ 1`.
-/

@[expose] public section

open scoped CStarAlgebra

namespace CStarMatrix

variable {n A : Type*} [Fintype n] [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The diagonal entries of a nonnegative `CStarMatrix` are nonnegative. The positive matrices are the
additive closure of the `X⋆ X` (`StarOrderedRing.le_iff`), and `(X⋆ X) i i = ∑ₖ (X k i)⋆ (X k i)`. -/
theorem diag_nonneg {M : CStarMatrix n n A} (hM : 0 ≤ M) {i : n} : 0 ≤ M i i := by
  obtain ⟨P, hP, rfl⟩ := (StarOrderedRing.le_iff 0 M).mp hM
  clear hM
  rw [zero_add]
  induction hP using AddSubmonoid.closure_induction with
  | mem _ h =>
    obtain ⟨X, rfl⟩ := h
    change 0 ≤ (star X * X) i i
    rw [mul_apply]
    exact Finset.sum_nonneg fun k _ => by rw [star_apply]; exact star_mul_self_nonneg _
  | zero => exact le_rfl
  | add _ _ _ _ h₁ h₂ => exact add_nonneg h₁ h₂

end CStarMatrix

/-- A ℂ-linear map `φ : A₁ →ₗ[ℂ] A₂` between C⋆-algebras is **`k`-positive** if applying it
entrywise to a `k × k` matrix over `A₁` preserves nonnegativity (Paulsen, *Completely Bounded Maps
and Operator Algebras*, Ch. 3). The completely positive maps (`CompletelyPositiveMap`) are the
maps that are `k`-positive for every `k`. -/
structure KPositiveMap (k : ℕ) (A₁ : Type*) (A₂ : Type*) [NonUnitalCStarAlgebra A₁]
    [NonUnitalCStarAlgebra A₂] [PartialOrder A₁] [PartialOrder A₂] [StarOrderedRing A₁]
    [StarOrderedRing A₂] extends A₁ →ₗ[ℂ] A₂ where
  map_cstarMatrix_nonneg' (M : CStarMatrix (Fin k) (Fin k) A₁) (hM : 0 ≤ M) :
    0 ≤ M.map toLinearMap

/-- The morphism class of `k`-positive maps. As `CompletelyPositiveMapClass`, it records only the
order property and is meant to be used together with `LinearMapClass`. -/
class KPositiveMapClass (F : Type*) (k : ℕ) (A₁ A₂ : outParam Type*)
    [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂] [PartialOrder A₁] [PartialOrder A₂]
    [StarOrderedRing A₁] [StarOrderedRing A₂] [FunLike F A₁ A₂] : Prop where
  map_cstarMatrix_nonneg' (φ : F) (M : CStarMatrix (Fin k) (Fin k) A₁) (hM : 0 ≤ M) :
    0 ≤ M.map φ

namespace KPositiveMap

variable {k : ℕ} {A₁ A₂ : Type*} [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂]
  [PartialOrder A₁] [PartialOrder A₂] [StarOrderedRing A₁] [StarOrderedRing A₂]

instance : FunLike (KPositiveMap k A₁ A₂) A₁ A₂ where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective
    exact h

instance : LinearMapClass (KPositiveMap k A₁ A₂) ℂ A₁ A₂ where
  map_add f := map_add f.toLinearMap
  map_smulₛₗ f := map_smulₛₗ f.toLinearMap

instance : KPositiveMapClass (KPositiveMap k A₁ A₂) k A₁ A₂ where
  map_cstarMatrix_nonneg' f := f.map_cstarMatrix_nonneg'

end KPositiveMap

/-- A completely positive map is `k`-positive for every `k`. -/
instance CompletelyPositiveMap.instKPositiveMapClass {k : ℕ} {A₁ A₂ : Type*}
    [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂] [PartialOrder A₁] [PartialOrder A₂]
    [StarOrderedRing A₁] [StarOrderedRing A₂] :
    KPositiveMapClass (A₁ →CP A₂) k A₁ A₂ where
  map_cstarMatrix_nonneg' φ := φ.map_cstarMatrix_nonneg' k

namespace KPositiveMapClass

variable {F A₁ A₂ : Type*} [CStarAlgebra A₁] [CStarAlgebra A₂] [PartialOrder A₁] [PartialOrder A₂]
  [StarOrderedRing A₁] [StarOrderedRing A₂] [FunLike F A₁ A₂] [LinearMapClass F ℂ A₁ A₂]
  [KPositiveMapClass F 2 A₁ A₂]

/-- **Kadison–Schwarz inequality** (Choi 1974): a `2`-positive map with `φ 1 ≤ 1` satisfies
`φ(a)⋆ φ(a) ≤ φ(a⋆ a)`. The matrix `!![1, a; a⋆, a⋆ a] = X⋆ X`, `X = !![1, a; 0, 0]`, is positive,
hence so is `N = !![φ 1, b; φ(a⋆), c]` with `b = φ a`, `c = φ(a⋆ a)` by `2`-positivity; being
self-adjoint, `N` has `φ(a⋆) = b⋆`. The lower-right entry of `Y⋆ N Y`, `Y = !![1, -b; 0, 1]`, is
`c - 2 b⋆ b + b⋆ φ(1) b ≤ c - b⋆ b` and is positive (`CStarMatrix.diag_nonneg`). -/
theorem le_map_star_mul (φ : F) (hφ : φ 1 ≤ 1) (a : A₁) :
    star (φ a) * φ a ≤ φ (star a * a) := by
  set b := φ a
  let X : CStarMatrix (Fin 2) (Fin 2) A₁ := CStarMatrix.ofMatrix !![1, a; 0, 0]
  let Y : CStarMatrix (Fin 2) (Fin 2) A₂ := CStarMatrix.ofMatrix !![1, -b; 0, 1]
  have hN : 0 ≤ (star X * X).map φ := map_cstarMatrix_nonneg' φ _ (star_mul_self_nonneg X)
  have hstar : φ (star a) = star b := by
    have := congrArg (fun M : CStarMatrix (Fin 2) (Fin 2) A₂ => M 0 1)
      (IsSelfAdjoint.of_nonneg hN).star_eq
    simp only [Fin.isValue, CStarMatrix.star_apply, CStarMatrix.map_apply, CStarMatrix.mul_apply,
      CStarMatrix.ofMatrix_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.cons_val_zero, Fin.sum_univ_two, star_one, one_mul, mul_one,
      star_zero, zero_mul, add_zero, X] at this
    exact (star_star _).symm.trans (congrArg star this)
  have h₁ := CStarMatrix.diag_nonneg (star_left_conjugate_nonneg hN Y) (i := 1)
  have h₂ : (star Y * (star X * X).map φ * Y) 1 1 =
      φ (star a * a) - star b * b - star b * b + star b * φ 1 * b := by
    simp only [Fin.isValue, CStarMatrix.mul_apply, CStarMatrix.star_apply, CStarMatrix.ofMatrix_apply,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one,
      CStarMatrix.map_apply, Fin.sum_univ_two, Matrix.cons_val_zero, map_add, star_neg, star_one, one_mul,
      star_zero, zero_mul, map_zero, add_zero, neg_mul, mul_one, hstar, mul_neg, Y, b, X]
    noncomm_ring
  have h₃ : star b * φ 1 * b ≤ star b * b := by
    simpa using star_left_conjugate_le_conjugate hφ b
  rw [h₂] at h₁
  rw [← sub_nonneg]
  calc (0 : A₂) ≤ _ + (star b * b - star b * φ 1 * b) := add_nonneg h₁ (sub_nonneg.mpr h₃)
    _ = φ (star a * a) - star b * b := by noncomm_ring

end KPositiveMapClass
