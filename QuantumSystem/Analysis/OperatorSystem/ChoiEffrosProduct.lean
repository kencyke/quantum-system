/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.CStarAlgebra.ChoiEffros
public import QuantumSystem.Analysis.CStarAlgebra.KPositiveMapSchwarz
public import QuantumSystem.ForMathlib.Analysis.OperatorSystem.Basic

/-!
# Matrix orders of the Choi–Effros product

For an idempotent Schwarz map `φ` on a C⋆-algebra `A`, the inclusion `val : ChoiEffros φ → A` of the
Choi–Effros C⋆-algebra on the range of `φ` is a complete order embedding exactly when `φ` is
completely positive (`ChoiEffros.isCompleteOrderEmbedding_valₗ_iff`): positivity of matrices is
always reflected (`ChoiEffros.nonneg_of_map_val_nonneg`), and preserved at each matrix size exactly
when `φ` is positive at that size (`ChoiEffros.forall_map_val_nonneg_iff_forall_map_nonneg`). Then
the C⋆-algebra `ChoiEffros φ`, with its matrix orders as a C⋆-algebra, is the range of `φ` with the
matrix orders of `A`. This holds for an idempotent completely positive map `φ` with `φ 1 ≤ 1` on a
unital C⋆-algebra, entering as `ChoiEffros (KPositiveMapClass.toSchwarzMap φ h)`.

The file lives apart from `QuantumSystem.Analysis.CStarAlgebra.ChoiEffros` so that the C⋆-algebra
construction does not depend on the operator-system API of
`QuantumSystem.ForMathlib.Analysis.OperatorSystem.Basic`.

## Main results

* **`ChoiEffros.isCompleteOrderEmbedding_valₗ_iff`** — the matrix orders of the range as a
  C⋆-algebra are the matrix orders of `A` exactly when `φ` is completely positive.
-/

@[expose] public section

open scoped CStarAlgebra

namespace ChoiEffros

variable {F A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [FunLike F A A]
  [LinearMapClass F ℂ A A] [SchwarzMapClass F A A] {φ : F} [Fact (IsIdempotentElem (φ : A →ₗ[ℂ] A))]

/-- **The matrix order of `ChoiEffros φ` is the matrix order of `A` exactly when `φ` is completely
positive**: `val : ChoiEffros φ → A` is a complete order embedding if and only if `φ` preserves the
positivity of matrices of every size. Positivity is always reflected
(`ChoiEffros.nonneg_of_map_val_nonneg`), and preserved at each matrix size exactly when `φ` is positive
at that size (`ChoiEffros.forall_map_val_nonneg_iff_forall_map_nonneg`). -/
theorem isCompleteOrderEmbedding_valₗ_iff :
    (valₗ φ).IsCompleteOrderEmbedding ↔
      ∀ (k : ℕ) (X : CStarMatrix (Fin k) (Fin k) A), 0 ≤ X → 0 ≤ X.map φ :=
  ⟨fun h k => forall_map_val_nonneg_iff_forall_map_nonneg.mp fun X => (h k X).mpr,
    fun h k X => ⟨nonneg_of_map_val_nonneg, forall_map_val_nonneg_iff_forall_map_nonneg.mpr (h k) X⟩⟩

end ChoiEffros

/- On the range of an idempotent completely positive map `φ` with `φ 1 ≤ 1`, the Choi–Effros
C⋆-algebra carries the matrix order of `A`. -/
example {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (φ : A →CP A) (hφ : φ 1 ≤ 1)
    [Fact (IsIdempotentElem (φ : A →ₗ[ℂ] A))] :
    (ChoiEffros.valₗ (KPositiveMapClass.toSchwarzMap φ hφ)).IsCompleteOrderEmbedding :=
  ChoiEffros.isCompleteOrderEmbedding_valₗ_iff.mpr (CompletelyPositiveMapClass.map_cstarMatrix_nonneg' φ)
