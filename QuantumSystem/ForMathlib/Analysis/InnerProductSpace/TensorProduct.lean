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

/-! ### Tensor factorisation of Euclidean spaces along an index bijection

For an index bijection `e : m × n ≃ p`, the Hilbert-space tensor product
`EuclideanSpace 𝕜 m ⊗ EuclideanSpace 𝕜 n` is isometrically the Euclidean space
`EuclideanSpace 𝕜 p`. This realises, at the level of Hilbert spaces, the factorisation
underlying any bijective splitting of the index set. -/

section EuclideanTensor

open WithLp

variable {𝕜 : Type*} [RCLike 𝕜] {m n p : Type*}
  [Fintype m] [Fintype n] [Fintype p] [DecidableEq m] [DecidableEq n] [DecidableEq p]

/-- The Hilbert-space tensor factorisation along an index bijection `e : m × n ≃ p`: the tensor
product of `EuclideanSpace 𝕜 m` and `EuclideanSpace 𝕜 n`, transported along `e`, as a linear
isometry equivalence onto `EuclideanSpace 𝕜 p`. Built as the orthonormal-basis representation of
the (reindexed) tensor of the standard bases. -/
noncomputable def EuclideanSpace.tensorEquiv (e : (m × n) ≃ p) :
    EuclideanSpace 𝕜 m ⊗[𝕜] EuclideanSpace 𝕜 n ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 p :=
  (((EuclideanSpace.basisFun m 𝕜).tensorProduct (EuclideanSpace.basisFun n 𝕜)).reindex e).repr

/-- The tensor factorisation sends a pure tensor of standard basis vectors to the standard basis
vector at the combined index. -/
@[simp]
lemma EuclideanSpace.tensorEquiv_single_tmul (e : (m × n) ≃ p) (i : m) (j : n) :
    EuclideanSpace.tensorEquiv (𝕜 := 𝕜) e
        (EuclideanSpace.single i (1 : 𝕜) ⊗ₜ[𝕜] EuclideanSpace.single j (1 : 𝕜))
      = EuclideanSpace.single (e (i, j)) (1 : 𝕜) := by
  have hb :
      (((EuclideanSpace.basisFun m 𝕜).tensorProduct (EuclideanSpace.basisFun n 𝕜)).reindex e)
          (e (i, j))
        = EuclideanSpace.single i (1 : 𝕜) ⊗ₜ[𝕜] EuclideanSpace.single j (1 : 𝕜) := by
    rw [OrthonormalBasis.reindex_apply, Equiv.symm_apply_apply,
      OrthonormalBasis.tensorProduct_apply, EuclideanSpace.basisFun_apply,
      EuclideanSpace.basisFun_apply]
  change (((EuclideanSpace.basisFun m 𝕜).tensorProduct (EuclideanSpace.basisFun n 𝕜)).reindex e).repr
      (EuclideanSpace.single i (1 : 𝕜) ⊗ₜ[𝕜] EuclideanSpace.single j (1 : 𝕜)) = _
  rw [← hb, OrthonormalBasis.repr_self]

end EuclideanTensor

section EuclideanTensorCoord

open WithLp

variable {𝕜 : Type*} [RCLike 𝕜] {m n p : Type*}
  [Fintype m] [Fintype n] [Fintype p]

/-- Coordinate formula for the tensor factorisation on a pure tensor: the `k`-coordinate of
`tensorEquiv e (w₁ ⊗ w₂)` is the product of the `(e.symm k).1`-coordinate of `w₁` and the
`(e.symm k).2`-coordinate of `w₂`. -/
lemma EuclideanSpace.ofLp_tensorEquiv_tmul (e : (m × n) ≃ p) (w₁ : EuclideanSpace 𝕜 m)
    (w₂ : EuclideanSpace 𝕜 n) (k : p) :
    ofLp (EuclideanSpace.tensorEquiv (𝕜 := 𝕜) e (w₁ ⊗ₜ[𝕜] w₂)) k
      = ofLp w₁ (e.symm k).1 * ofLp w₂ (e.symm k).2 := by
  classical
  have hk : EuclideanSpace.single k (1 : 𝕜)
      = EuclideanSpace.tensorEquiv (𝕜 := 𝕜) e
          (EuclideanSpace.single (e.symm k).1 (1 : 𝕜) ⊗ₜ[𝕜]
            EuclideanSpace.single (e.symm k).2 (1 : 𝕜)) := by
    rw [EuclideanSpace.tensorEquiv_single_tmul, Prod.mk.eta, Equiv.apply_symm_apply]
  have hofLp : ofLp (EuclideanSpace.tensorEquiv (𝕜 := 𝕜) e (w₁ ⊗ₜ[𝕜] w₂)) k
      = inner 𝕜 (EuclideanSpace.single k (1 : 𝕜))
          (EuclideanSpace.tensorEquiv (𝕜 := 𝕜) e (w₁ ⊗ₜ[𝕜] w₂)) := by
    rw [EuclideanSpace.inner_single_left, map_one, one_mul]
  rw [hofLp, hk, LinearIsometryEquiv.inner_map_map, TensorProduct.inner_tmul,
    EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_left]
  simp

end EuclideanTensorCoord
