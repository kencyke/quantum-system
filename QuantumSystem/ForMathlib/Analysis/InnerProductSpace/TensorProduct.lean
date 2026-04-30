module

public import Mathlib.Analysis.InnerProductSpace.TensorProduct

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

The supporting lemmas (action on pure tensors, multiplicativity, bilinearity,
`tensor 1 1 = 1`) are kept `private`; downstream code only consumes the
definition itself together with the standard `simp` set.
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

private lemma tensor_toLinearMap (A : H →L[ℂ] H) (B : K →L[ℂ] K) :
    (tensor A B).toLinearMap = TensorProduct.map A.toLinearMap B.toLinearMap :=
  LinearMap.coe_toContinuousLinearMap _

@[simp]
private lemma tensor_tmul (A : H →L[ℂ] H) (B : K →L[ℂ] K) (x : H) (y : K) :
    tensor A B (x ⊗ₜ[ℂ] y) = A x ⊗ₜ[ℂ] B y := by
  change ((tensor A B).toLinearMap) (x ⊗ₜ[ℂ] y) = _
  rw [tensor_toLinearMap]
  exact TensorProduct.map_tmul _ _ _ _

@[simp]
private lemma tensor_one : tensor (1 : H →L[ℂ] H) (1 : K →L[ℂ] K) = 1 := by
  ext z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add a b ha hb => simp [map_add, ha, hb]

private lemma tensor_mul (A₁ A₂ : H →L[ℂ] H) (B₁ B₂ : K →L[ℂ] K) :
    tensor (A₁ * A₂) (B₁ * B₂) = tensor A₁ B₁ * tensor A₂ B₂ := by
  ext z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [ContinuousLinearMap.mul_apply]
  | add a b ha hb => simp [map_add, ha, hb]

private lemma tensor_add_left (A₁ A₂ : H →L[ℂ] H) (B : K →L[ℂ] K) :
    tensor (A₁ + A₂) B = tensor A₁ B + tensor A₂ B := by
  ext z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [ContinuousLinearMap.add_apply, TensorProduct.add_tmul]
  | add a b ha hb => simp [map_add, ha, hb]

private lemma tensor_add_right (A : H →L[ℂ] H) (B₁ B₂ : K →L[ℂ] K) :
    tensor A (B₁ + B₂) = tensor A B₁ + tensor A B₂ := by
  ext z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [ContinuousLinearMap.add_apply, TensorProduct.tmul_add]
  | add a b ha hb => simp [map_add, ha, hb]

end ContinuousLinearMap
