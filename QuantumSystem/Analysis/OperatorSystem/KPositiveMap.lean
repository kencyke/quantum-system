/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.CStarAlgebra.KPositiveMapSchwarz
public import QuantumSystem.ForMathlib.Analysis.OperatorSystem.Basic

/-!
# `k`-positivity of completely positive maps between spaces with matrix orders

A completely positive map between spaces with matrix orders (`CompletelyPositiveMapClass'`) is
`k`-positive for every `k` (`CompletelyPositiveMapClass'.instKPositiveMapClass`). So the results on
`k`-positive maps between C⋆-algebras, such as the Kadison–Schwarz inequality
(`KPositiveMapClass.le_map_star_mul`), apply to the maps `A₁ →CP' A₂` between C⋆-algebras directly,
without passing through `CompletelyPositiveMap'.equivCompletelyPositiveMap`.

In particular a unital complete order isomorphism of unital C⋆-algebras, a linear isomorphism
`e : A₁ ≃ₗ[ℂ] A₂` with `e 1 = 1` and `0 ≤ X.map e ↔ 0 ≤ X` for every square matrix `X`, is a
⋆-isomorphism (`LinearMap.IsCompleteOrderEmbedding.starAlgEquiv`): `e` and its inverse
(`LinearMap.IsCompleteOrderEmbedding.symm`) are completely positive, and
`KPositiveMapClass.starAlgEquivOfInverse` applies.

The file lives outside `ForMathlib/` because it needs both `ForMathlib/Analysis/CStarAlgebra/KPositiveMap.lean`
and `ForMathlib/Analysis/OperatorSystem/Basic.lean`, and a `ForMathlib` file imports Mathlib only.

## Main definitions

* `LinearMap.IsCompleteOrderEmbedding.starAlgEquiv` — a unital complete order isomorphism of unital
  C⋆-algebras as a ⋆-isomorphism.

## Main results

* `CompletelyPositiveMapClass'.instKPositiveMapClass` — completely positive maps between spaces with
  matrix orders are `k`-positive.
-/

@[expose] public section

open scoped CStarAlgebra

/-- A completely positive map between spaces with matrix orders is `k`-positive for every `k`. This
covers the bundled maps `A₁ →CP' A₂` and every other `CompletelyPositiveMapClass'`. -/
instance CompletelyPositiveMapClass'.instKPositiveMapClass {k : ℕ} {F A₁ A₂ : Type*} [AddCommMonoid A₁]
    [Module ℂ A₁] [AddCommMonoid A₂] [Module ℂ A₂] [∀ n, PartialOrder (CStarMatrix (Fin n) (Fin n) A₁)]
    [∀ n, PartialOrder (CStarMatrix (Fin n) (Fin n) A₂)] [FunLike F A₁ A₂]
    [CompletelyPositiveMapClass' F A₁ A₂] : KPositiveMapClass F k A₁ A₂ where
  map_cstarMatrix_nonneg' φ := CompletelyPositiveMapClass'.map_cstarMatrix_nonneg' φ k

namespace LinearMap.IsCompleteOrderEmbedding

variable {A₁ A₂ : Type*} [CStarAlgebra A₁] [CStarAlgebra A₂] [PartialOrder A₁] [PartialOrder A₂]
  [StarOrderedRing A₁] [StarOrderedRing A₂] {e : A₁ ≃ₗ[ℂ] A₂}

/-- **Unital complete order isomorphisms are ⋆-isomorphisms.** A linear isomorphism `e` of unital
C⋆-algebras with `e 1 = 1` that is a complete order embedding is a ⋆-isomorphism: `e` and its
inverse are completely positive (`LinearMap.IsCompleteOrderEmbedding.symm`), hence `2`-positive, and
`KPositiveMapClass.starAlgEquivOfInverse` applies. -/
noncomputable def starAlgEquiv (he : IsCompleteOrderEmbedding (e : A₁ →ₗ[ℂ] A₂)) (he1 : e 1 = 1) :
    A₁ ≃⋆ₐ[ℂ] A₂ :=
  KPositiveMapClass.starAlgEquivOfInverse he.toCompletelyPositiveMap' he.symm.toCompletelyPositiveMap'
    he1 e.left_inv e.right_inv

/-- `he.starAlgEquiv he1` is `e` as a function. -/
@[simp] lemma coe_starAlgEquiv (he : IsCompleteOrderEmbedding (e : A₁ →ₗ[ℂ] A₂)) (he1 : e 1 = 1) :
    ⇑(he.starAlgEquiv he1) = e :=
  rfl

/-- The inverse of `he.starAlgEquiv he1` is `e.symm` as a function. -/
@[simp] lemma coe_starAlgEquiv_symm (he : IsCompleteOrderEmbedding (e : A₁ →ₗ[ℂ] A₂)) (he1 : e 1 = 1) :
    ⇑(he.starAlgEquiv he1).symm = e.symm :=
  rfl

end LinearMap.IsCompleteOrderEmbedding
