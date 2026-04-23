module

public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Operator tensor product for finite-dimensional inner product spaces

This file provides the continuous-linear-map version of `TensorProduct.map` for
finite-dimensional inner product spaces, filling a gap in Mathlib's
`Analysis/InnerProductSpace/TensorProduct.lean` (whose header TODO lists
"Define the continuous linear map version of `TensorProduct.map`").

Because finite-dimensional normed spaces are automatically complete and all
linear maps between them are continuous, we specialise to
`[FiniteDimensional ℂ H] [FiniteDimensional ℂ K]` throughout.

## Main definitions

* `ContinuousLinearMap.tensor` — for finite-dimensional Hilbert spaces `H`, `K`
  over `ℂ`, the tensor product `A ⊗ B : H ⊗[ℂ] K →L[ℂ] H ⊗[ℂ] K` of two
  operators `A : H →L[ℂ] H` and `B : K →L[ℂ] K`.

## Main results

* `ContinuousLinearMap.tensor_tmul` — action on pure tensors:
  `(A ⊗ B)(x ⊗ y) = A x ⊗ B y`.
* `ContinuousLinearMap.tensor_one` — `(1 : H →L[ℂ] H) ⊗ (1 : K →L[ℂ] K) = 1`.
* `ContinuousLinearMap.tensor_mul` — multiplicativity under composition:
  `(A₁ * A₂) ⊗ (B₁ * B₂) = (A₁ ⊗ B₁) * (A₂ ⊗ B₂)`.
* `ContinuousLinearMap.tensor_add_left` / `tensor_add_right` — bilinearity.

## TODO

* The adjoint-tensor compatibility `(A ⊗ B)† = A† ⊗ B†` is immediate from
  Mathlib's `TensorProduct.adjoint_map` at the `LinearMap` level; lifting to
  `ContinuousLinearMap` requires bridging CLM-adjoint and LinearMap-adjoint
  and is left for a follow-up.
-/

@[expose] public section

open scoped TensorProduct

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [FiniteDimensional ℂ H] [FiniteDimensional ℂ K]

namespace ContinuousLinearMap

/-- Tensor product of operators on finite-dimensional Hilbert spaces.

Defined as the continuous linear map underlying `TensorProduct.map A.toLinearMap
B.toLinearMap`; the continuity is automatic because `H ⊗[ℂ] K` is
finite-dimensional. -/
noncomputable def tensor (A : H →L[ℂ] H) (B : K →L[ℂ] K) :
    H ⊗[ℂ] K →L[ℂ] H ⊗[ℂ] K :=
  LinearMap.toContinuousLinearMap (TensorProduct.map A.toLinearMap B.toLinearMap)

lemma tensor_toLinearMap (A : H →L[ℂ] H) (B : K →L[ℂ] K) :
    (tensor A B).toLinearMap = TensorProduct.map A.toLinearMap B.toLinearMap :=
  LinearMap.coe_toContinuousLinearMap _

@[simp]
lemma tensor_tmul (A : H →L[ℂ] H) (B : K →L[ℂ] K) (x : H) (y : K) :
    tensor A B (x ⊗ₜ[ℂ] y) = A x ⊗ₜ[ℂ] B y := by
  change ((tensor A B).toLinearMap) (x ⊗ₜ[ℂ] y) = _
  rw [tensor_toLinearMap]
  exact TensorProduct.map_tmul _ _ _ _

@[simp]
lemma tensor_one : tensor (1 : H →L[ℂ] H) (1 : K →L[ℂ] K) = 1 := by
  ext z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add a b ha hb => simp [map_add, ha, hb]

lemma tensor_mul (A₁ A₂ : H →L[ℂ] H) (B₁ B₂ : K →L[ℂ] K) :
    tensor (A₁ * A₂) (B₁ * B₂) = tensor A₁ B₁ * tensor A₂ B₂ := by
  ext z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [ContinuousLinearMap.mul_apply]
  | add a b ha hb => simp [map_add, ha, hb]

lemma tensor_add_left (A₁ A₂ : H →L[ℂ] H) (B : K →L[ℂ] K) :
    tensor (A₁ + A₂) B = tensor A₁ B + tensor A₂ B := by
  ext z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [ContinuousLinearMap.add_apply, TensorProduct.add_tmul]
  | add a b ha hb => simp [map_add, ha, hb]

lemma tensor_add_right (A : H →L[ℂ] H) (B₁ B₂ : K →L[ℂ] K) :
    tensor A (B₁ + B₂) = tensor A B₁ + tensor A B₂ := by
  ext z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [ContinuousLinearMap.add_apply, TensorProduct.tmul_add]
  | add a b ha hb => simp [map_add, ha, hb]

end ContinuousLinearMap
