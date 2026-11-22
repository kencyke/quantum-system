/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.CStarAlgebra.CompletelyPositiveMap.Choi
public import QuantumSystem.Analysis.CStarAlgebra.TensorProduct.CompletelyPositiveMap
public import QuantumSystem.Analysis.InnerProductSpace.PartialTrace

/-!
# Tensor products of CPTP maps

For completely positive maps `φ : B(H₁) → B(K₁)` and `ψ : B(H₂) → B(K₂)` between the operator
algebras of finite-dimensional Hilbert spaces, the **tensor product**
`φ ⊗ ψ : B(H₁ ⊗ H₂) → B(K₁ ⊗ K₂)` is determined by `(φ ⊗ ψ)(A ⊗ B) = φ(A) ⊗ ψ(B)`
(`CompletelyPositiveMap.tensorProduct_mapL`): it is the tensor product
`CompletelyPositiveMap.minTensorProduct φ ψ` of completely positive maps on the minimal tensor
products, read through `B(H) ⊗ₘᵢₙ B(K) ≃ B(H ⊗ K)` (`MinTensorProduct.continuousLinearMapEquiv`),
with no choice of bases. Kraus operators `Tₐ` of `φ` and `S_b` of `ψ` give the Kraus operators
`Tₐ ⊗ S_b` of `φ ⊗ ψ`; the tensor product of CPTP maps is a CPTP map
(`CPTPMap.tensorProduct`), since `tr(A ⊗ B) = tr A · tr B`. Tracing out the second factor
intertwines `Φ ⊗ Ψ` with `Φ` when `Ψ` is trace preserving
(`CPTPMap.traceRight_tensorProduct`).

The operator tensor product `A ⊗ B` is Mathlib's `TensorProduct.mapL A B`. No infix notation is
introduced for `φ ⊗ ψ`, which would clash with `TensorProduct`.

## Main definitions

* `CompletelyPositiveMap.tensorProduct φ ψ`: the tensor product of completely positive maps, the
  case `B(H₁) ⊗ₘᵢₙ B(H₂) → B(K₁) ⊗ₘᵢₙ B(K₂)` of `CompletelyPositiveMap.minTensorProduct`.
* `CPTPMap.tensorProduct Φ Ψ`: the tensor product of CPTP maps.

## Main statements

* `CompletelyPositiveMap.tensorProduct_mapL`: `(φ ⊗ ψ)(A ⊗ B) = φ(A) ⊗ ψ(B)`.
* `CompletelyPositiveMap.tensorProduct_continuousLinearMapEquiv`: under
  `B(H) ⊗ₘᵢₙ B(K) ≃ B(H ⊗ K)` it is `CompletelyPositiveMap.minTensorProduct φ ψ`.
* `CompletelyPositiveMap.tensorProduct_apply_eq_sum_kraus`: for Kraus operators `Tₐ` of `φ` and
  `S_b` of `ψ`, `φ ⊗ ψ` has the Kraus operators `Tₐ ⊗ S_b`.
* `CompletelyPositiveMap.traceRight_tensorProduct`, `CPTPMap.traceRight_tensorProduct`:
  `tr₂ ∘ (φ ⊗ Ψ) = φ ∘ tr₂` for a trace-preserving `Ψ`.
-/

@[expose] public section

open TensorProduct InnerProductSpace ContinuousLinearMap
open scoped TensorProduct InnerProductSpace InnerProduct CStarAlgebra

variable {H₁ H₂ K₁ K₂ : Type*}
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [FiniteDimensional ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [FiniteDimensional ℂ H₂]
  [NormedAddCommGroup K₁] [InnerProductSpace ℂ K₁] [FiniteDimensional ℂ K₁]
  [NormedAddCommGroup K₂] [InnerProductSpace ℂ K₂] [FiniteDimensional ℂ K₂]

namespace CompletelyPositiveMap

open scoped MinTensorProduct in
/-- The **tensor product** `φ ⊗ ψ : B(H₁ ⊗ H₂) → B(K₁ ⊗ K₂)` of completely positive maps: the
tensor product `CompletelyPositiveMap.minTensorProduct` on the minimal tensor products, transported
(`CompletelyPositiveMap.arrowCongr`) along `B(H) ⊗ₘᵢₙ B(K) ≃ B(H ⊗ K)`
(`MinTensorProduct.continuousLinearMapEquiv`) on both sides. It
is determined by `(φ ⊗ ψ)(A ⊗ B) = φ(A) ⊗ ψ(B)` (`CompletelyPositiveMap.tensorProduct_mapL`). -/
noncomputable def tensorProduct (φ : (H₁ →L[ℂ] H₁) →CP (K₁ →L[ℂ] K₁))
    (ψ : (H₂ →L[ℂ] H₂) →CP (K₂ →L[ℂ] K₂)) :
    (H₁ ⊗[ℂ] H₂ →L[ℂ] H₁ ⊗[ℂ] H₂) →CP (K₁ ⊗[ℂ] K₂ →L[ℂ] K₁ ⊗[ℂ] K₂) :=
  arrowCongr (MinTensorProduct.continuousLinearMapEquiv H₁ H₂)
    (MinTensorProduct.continuousLinearMapEquiv K₁ K₂) (minTensorProduct φ ψ)

open scoped MinTensorProduct in
/-- The tensor product on `B(H₁ ⊗ H₂)` is the tensor product of the minimal tensor products, under
`B(H) ⊗ₘᵢₙ B(K) ≃ B(H ⊗ K)` (`MinTensorProduct.continuousLinearMapEquiv`). -/
lemma tensorProduct_continuousLinearMapEquiv (φ : (H₁ →L[ℂ] H₁) →CP (K₁ →L[ℂ] K₁))
    (ψ : (H₂ →L[ℂ] H₂) →CP (K₂ →L[ℂ] K₂)) (T : (H₁ →L[ℂ] H₁) ⊗ₘᵢₙ (H₂ →L[ℂ] H₂)) :
    tensorProduct φ ψ (MinTensorProduct.continuousLinearMapEquiv H₁ H₂ T) =
      MinTensorProduct.continuousLinearMapEquiv K₁ K₂ (minTensorProduct φ ψ T) := by
  rw [tensorProduct, arrowCongr_apply, StarAlgEquiv.symm_apply_apply]

/-- The tensor product of completely positive maps acts on operator tensors as
`(φ ⊗ ψ)(A ⊗ B) = φ(A) ⊗ ψ(B)`. -/
@[simp] lemma tensorProduct_mapL (φ : (H₁ →L[ℂ] H₁) →CP (K₁ →L[ℂ] K₁))
    (ψ : (H₂ →L[ℂ] H₂) →CP (K₂ →L[ℂ] K₂)) (A : H₁ →L[ℂ] H₁) (B : H₂ →L[ℂ] H₂) :
    tensorProduct φ ψ (mapL A B) = mapL (φ A) (ψ B) := by
  rw [← MinTensorProduct.continuousLinearMapEquiv_of_tmul, tensorProduct_continuousLinearMapEquiv,
    minTensorProduct_of_tmul, MinTensorProduct.continuousLinearMapEquiv_of_tmul]

/-- Kraus operators `Tₐ` of `φ` and `S_b` of `ψ` give the Kraus operators `Tₐ ⊗ S_b` of the tensor
product: `(φ ⊗ ψ)(X) = Σₐ_b (Tₐ ⊗ S_b) X (Tₐ ⊗ S_b)†`, checked on `X = A ⊗ B` by
`(Tₐ ⊗ S_b)(A ⊗ B)(Tₐ ⊗ S_b)† = Tₐ A Tₐ† ⊗ S_b B S_b†`. -/
lemma tensorProduct_apply_eq_sum_kraus {φ : (H₁ →L[ℂ] H₁) →CP (K₁ →L[ℂ] K₁)}
    {ψ : (H₂ →L[ℂ] H₂) →CP (K₂ →L[ℂ] K₂)} {κ₁ κ₂ : Type*} [Fintype κ₁] [Fintype κ₂]
    {T : κ₁ → H₁ →L[ℂ] K₁} {S : κ₂ → H₂ →L[ℂ] K₂}
    (hT : ∀ A, φ A = ∑ a, T a ∘L A ∘L (T a)†)
    (hS : ∀ B, ψ B = ∑ b, S b ∘L B ∘L (S b)†) (X : H₁ ⊗[ℂ] H₂ →L[ℂ] H₁ ⊗[ℂ] H₂) :
    tensorProduct φ ψ X =
      ∑ p : κ₁ × κ₂, mapL (T p.1) (S p.2) ∘L X ∘L (mapL (T p.1) (S p.2))† := by
  have h := TensorProduct.ext_mapL (u := (tensorProduct φ ψ).toLinearMap)
    (v := (ofKraus fun p : κ₁ × κ₂ => mapL (T p.1) (S p.2)).toLinearMap) fun A B => by
      rw [coe_toLinearMap, tensorProduct_mapL, hT, hS]
      change _ = ∑ p : κ₁ × κ₂, mapL (T p.1) (S p.2) ∘L mapL A B ∘L (mapL (T p.1) (S p.2))†
      simp only [adjoint_mapL, ← mapL_comp, Fintype.sum_prod_type]
      rw [← mapLEquiv_tmul, sum_tmul, ← LinearEquiv.coe_coe, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [tmul_sum, map_sum]
      simp only [LinearEquiv.coe_coe, mapLEquiv_tmul]
  exact LinearMap.congr_fun h X

/-- Tracing out the second factor intertwines `φ ⊗ ψ` with `φ` when `ψ` is trace preserving:
`tr₂((φ ⊗ ψ)(X)) = φ(tr₂ X)`, since `tr₂(φ(A) ⊗ ψ(B)) = tr ψ(B) • φ(A) = φ(tr B • A)`. -/
lemma traceRight_tensorProduct (φ : (H₁ →L[ℂ] H₁) →CP (K₁ →L[ℂ] K₁))
    (ψ : (H₂ →L[ℂ] H₂) →CP (K₂ →L[ℂ] K₂)) (hψ : IsTracePreserving ψ)
    (X : H₁ ⊗[ℂ] H₂ →L[ℂ] H₁ ⊗[ℂ] H₂) :
    ContinuousLinearMap.traceRight K₁ K₂ (tensorProduct φ ψ X) =
      φ (ContinuousLinearMap.traceRight H₁ H₂ X) := by
  have h := TensorProduct.ext_mapL
    (u := ContinuousLinearMap.traceRight K₁ K₂ ∘ₗ (tensorProduct φ ψ).toLinearMap)
    (v := φ.toLinearMap ∘ₗ ContinuousLinearMap.traceRight H₁ H₂)
    fun A B => by
      simp only [LinearMap.comp_apply, coe_toLinearMap, tensorProduct_mapL]
      rw [traceRight_mapL, traceRight_mapL, hψ, map_smul]
  exact LinearMap.congr_fun h X

end CompletelyPositiveMap

namespace CPTPMap

/-- The **tensor product** `Φ ⊗ Ψ : B(H₁ ⊗ H₂) → B(K₁ ⊗ K₂)` of CPTP maps: completely
positive (`CompletelyPositiveMap.tensorProduct`) and trace preserving, since
`tr(Φ(A) ⊗ Ψ(B)) = tr Φ(A) · tr Ψ(B) = tr A · tr B = tr(A ⊗ B)`. -/
noncomputable def tensorProduct (Φ : CPTPMap H₁ K₁) (Ψ : CPTPMap H₂ K₂) :
    CPTPMap (H₁ ⊗[ℂ] H₂) (K₁ ⊗[ℂ] K₂) where
  toCompletelyPositiveMap :=
    CompletelyPositiveMap.tensorProduct Φ.toCompletelyPositiveMap Ψ.toCompletelyPositiveMap
  isTracePreserving' X := by
    have h := TensorProduct.ext_mapL (M := ℂ)
      (u := LinearMap.trace ℂ (K₁ ⊗[ℂ] K₂) ∘ₗ coeLM ℂ ∘ₗ (CompletelyPositiveMap.tensorProduct
        Φ.toCompletelyPositiveMap Ψ.toCompletelyPositiveMap).toLinearMap)
      (v := LinearMap.trace ℂ (H₁ ⊗[ℂ] H₂) ∘ₗ coeLM ℂ) fun A B => by
        simp only [LinearMap.comp_apply, CompletelyPositiveMap.coe_toLinearMap,
          CompletelyPositiveMap.tensorProduct_mapL, coeLM_apply, toLinearMap_mapL,
          LinearMap.trace_tensorProduct', coe_toCompletelyPositiveMap, trace_map]
    exact LinearMap.congr_fun h X

/-- The tensor product of CPTP maps acts on operator tensors as
`(Φ ⊗ Ψ)(A ⊗ B) = Φ(A) ⊗ Ψ(B)`. -/
@[simp] lemma tensorProduct_mapL (Φ : CPTPMap H₁ K₁) (Ψ : CPTPMap H₂ K₂)
    (A : H₁ →L[ℂ] H₁) (B : H₂ →L[ℂ] H₂) :
    tensorProduct Φ Ψ (mapL A B) = mapL (Φ A) (Ψ B) :=
  CompletelyPositiveMap.tensorProduct_mapL _ _ A B

/-- Tracing out the second factor intertwines `Φ ⊗ Ψ` with `Φ`: `tr₂((Φ ⊗ Ψ)(X)) = Φ(tr₂ X)`
(`CompletelyPositiveMap.traceRight_tensorProduct`, which needs only `Ψ` trace preserving). -/
lemma traceRight_tensorProduct (Φ : CPTPMap H₁ K₁) (Ψ : CPTPMap H₂ K₂)
    (X : H₁ ⊗[ℂ] H₂ →L[ℂ] H₁ ⊗[ℂ] H₂) :
    ContinuousLinearMap.traceRight K₁ K₂ (tensorProduct Φ Ψ X) =
      Φ (ContinuousLinearMap.traceRight H₁ H₂ X) :=
  CompletelyPositiveMap.traceRight_tensorProduct _ _ (isTracePreserving Ψ) X

end CPTPMap
