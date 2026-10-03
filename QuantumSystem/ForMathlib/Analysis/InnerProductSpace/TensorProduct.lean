/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.LinearAlgebra.Contraction

/-!
# Operators on tensor products of inner product spaces

Supplements to Mathlib's `Mathlib/Analysis/InnerProductSpace/TensorProduct.lean` for bounded
operators on the inner product space `E ⊗[𝕜] G`: the ampliation `A ↦ A ⊗ 1` as a
⋆-homomorphism, tensor products of rank-one operators, and the adjoints of the insertions
`y ↦ x ⊗ y` and `x ↦ x ⊗ y`.

The operator tensor product `A ⊗ B` of `A : E →L[𝕜] F` and `B : G →L[𝕜] H` is Mathlib's
`TensorProduct.mapL A B`, and the ampliation `A ⊗ 1` is `A.rTensor G`.

## Main definitions

* `ContinuousLinearMap.rTensorStarAlgHom 𝕜 E G` — the ampliation `A ↦ A ⊗ 1 = A.rTensor G` as a
  unital ⋆-homomorphism `B(E) →⋆ₐ B(E ⊗ G)`.
* `TensorProduct.mapLEquiv 𝕜 E F G H` — for finite-dimensional `E` and `G`, the linear
  equivalence `(E →L F) ⊗ (G →L H) ≃ (E ⊗ G →L F ⊗ H)`, `f ⊗ g ↦ mapL f g`; so linear maps out
  of `E ⊗ G →L F ⊗ H` are determined on the `mapL f g` (`TensorProduct.ext_mapL`).

## Main statements

* `TensorProduct.mapL_rankOne_rankOne` — `|x⟩⟨y| ⊗ |z⟩⟨w| = |x ⊗ z⟩⟨y ⊗ w|`.
* `TensorProduct.adjoint_mkL_apply_tmul` — the adjoint of the insertion `y ↦ x ⊗ y` is the
  partial inner product `x' ⊗ y' ↦ ⟪x, x'⟫ • y'`.
* `TensorProduct.adjoint_flip_mkL_apply_tmul` — the adjoint of the insertion `x ↦ x ⊗ y` is the
  partial inner product `x' ⊗ y' ↦ ⟪y, y'⟫ • x'`.
* `TensorProduct.mapL_rankOne_left` — `|x⟩⟨y| ⊗ B = ιₓ B ι_y†` for the insertions `ιₓ : z ↦ x ⊗ z`.
* `TensorProduct.adjoint_mkL_comp_mkL`, `TensorProduct.sum_mkL_comp_adjoint_mkL` — `ιₓ† ι_y = ⟪x, y⟫`,
  and `Σᵢ ι_{bᵢ} ι_{bᵢ}† = 1` along an orthonormal basis `b`.
-/

@[expose] public section

open scoped TensorProduct InnerProductSpace

variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

namespace ContinuousLinearMap

variable (𝕜 E G) in
/-- The **ampliation** `A ↦ A ⊗ 1 = A.rTensor G` as a unital ⋆-homomorphism
`B(E) →⋆ₐ B(E ⊗ G)`. It is the identity representation of `B(E)` with multiplicity `G`. -/
noncomputable def rTensorStarAlgHom [CompleteSpace E] [CompleteSpace G]
    [CompleteSpace (E ⊗[𝕜] G)] : (E →L[𝕜] E) →⋆ₐ[𝕜] (E ⊗[𝕜] G →L[𝕜] E ⊗[𝕜] G) where
  toFun A := A.rTensor G
  map_one' := rTensor_one G
  map_mul' A B := rTensor_mul G A B
  map_zero' := rTensor_zero G
  map_add' A B := rTensor_add G A B
  commutes' r := by simp [Algebra.algebraMap_eq_smul_one]
  map_star' A := by simp [star_eq_adjoint]

/-- The ampliation sends `A` to `A ⊗ 1 = A.rTensor G`. -/
@[simp] lemma rTensorStarAlgHom_apply [CompleteSpace E] [CompleteSpace G]
    [CompleteSpace (E ⊗[𝕜] G)] (A : E →L[𝕜] E) : rTensorStarAlgHom 𝕜 E G A = A.rTensor G :=
  rfl

end ContinuousLinearMap

namespace TensorProduct

open InnerProductSpace

/-- The tensor product of rank-one operators is rank-one: `|x⟩⟨y| ⊗ |z⟩⟨w| = |x ⊗ z⟩⟨y ⊗ w|`. -/
theorem mapL_rankOne_rankOne (x : E) (y : F) (z : G) (w : H) :
    mapL (rankOne 𝕜 x y) (rankOne 𝕜 z w) = rankOne 𝕜 (x ⊗ₜ[𝕜] z) (y ⊗ₜ[𝕜] w) := by
  refine ContinuousLinearMap.coe_inj.mp <| ext' fun u v => ?_
  simp [TensorProduct.smul_tmul', smul_smul, mul_comm]

/-- The adjoint of the insertion `mkL 𝕜 E F x : y ↦ x ⊗ y` is the partial inner product
`x' ⊗ y' ↦ ⟪x, x'⟫ • y'`. -/
theorem adjoint_mkL_apply_tmul [CompleteSpace F] [CompleteSpace (E ⊗[𝕜] F)] (x x' : E) (y : F) :
    (mkL 𝕜 E F x).adjoint (x' ⊗ₜ y) = ⟪x, x'⟫_𝕜 • y :=
  ext_inner_left 𝕜 fun w => by
    rw [ContinuousLinearMap.adjoint_inner_right, mkL_apply_apply, inner_tmul, inner_smul_right]

/-- The adjoint of the insertion `(mkL 𝕜 E F).flip y : x ↦ x ⊗ y` is the partial inner product
`x' ⊗ y' ↦ ⟪y, y'⟫ • x'`. -/
theorem adjoint_flip_mkL_apply_tmul [CompleteSpace E] [CompleteSpace (E ⊗[𝕜] F)] (y y' : F)
    (x : E) : ((mkL 𝕜 E F).flip y).adjoint (x ⊗ₜ y') = ⟪y, y'⟫_𝕜 • x :=
  ext_inner_left 𝕜 fun w => by
    rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.flip_apply, mkL_apply_apply,
      inner_tmul, inner_smul_right, mul_comm]

variable (𝕜 E F G H) in
/-- For finite-dimensional `E` and `G`, operators on `E ⊗ G` are tensors of operators: the linear
equivalence `(E →L F) ⊗ (G →L H) ≃ (E ⊗ G →L F ⊗ H)`, `f ⊗ g ↦ mapL f g`
(`TensorProduct.mapLEquiv_tmul`), the continuous form of Mathlib's `homTensorHomEquiv`. -/
noncomputable def mapLEquiv [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 G] :
    (E →L[𝕜] F) ⊗[𝕜] (G →L[𝕜] H) ≃ₗ[𝕜] (E ⊗[𝕜] G →L[𝕜] F ⊗[𝕜] H) :=
  (TensorProduct.congr LinearMap.toContinuousLinearMap.symm
    LinearMap.toContinuousLinearMap.symm).trans
      ((homTensorHomEquiv 𝕜 E G F H).trans LinearMap.toContinuousLinearMap)

/-- `mapLEquiv` sends `f ⊗ g` to the operator tensor product `mapL f g`. -/
@[simp] theorem mapLEquiv_tmul [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 G] (f : E →L[𝕜] F)
    (g : G →L[𝕜] H) : mapLEquiv 𝕜 E F G H (f ⊗ₜ g) = mapL f g := by
  refine ContinuousLinearMap.coe_inj.mp <| ext' fun x y => ?_
  simp [mapLEquiv]

/-- Two linear maps out of `E ⊗ G →L F ⊗ H` agree if they agree on the operator tensors
`mapL f g`, which span it (`TensorProduct.mapLEquiv`). -/
theorem ext_mapL [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 G] {M : Type*} [AddCommGroup M]
    [Module 𝕜 M] {u v : (E ⊗[𝕜] G →L[𝕜] F ⊗[𝕜] H) →ₗ[𝕜] M}
    (h : ∀ (f : E →L[𝕜] F) (g : G →L[𝕜] H), u (mapL f g) = v (mapL f g)) : u = v := by
  refine LinearMap.ext fun X => ?_
  obtain ⟨z, rfl⟩ := (mapLEquiv 𝕜 E F G H).surjective X
  induction z using TensorProduct.inductionOn with
  | tmul f g => rw [mapLEquiv_tmul, h]
  | add z z' hz hz' => rw [map_add, map_add, map_add, hz, hz']

/-- The tensor product of a rank-one operator with an operator `B` factors through the insertions
`ιₓ = mkL 𝕜 E H x : z ↦ x ⊗ z`: `|x⟩⟨y| ⊗ B = ιₓ B ι_y†`. -/
theorem mapL_rankOne_left [CompleteSpace G] [CompleteSpace (F ⊗[𝕜] G)] (x : E) (y : F)
    (B : G →L[𝕜] H) :
    mapL (rankOne 𝕜 x y) B = mkL 𝕜 E H x ∘L B ∘L (mkL 𝕜 F G y).adjoint := by
  refine ContinuousLinearMap.coe_inj.mp <| ext' fun u v => ?_
  simp [adjoint_mkL_apply_tmul, smul_tmul]

/-- The insertions are orthogonal: `ιₓ† ι_y = ⟪x, y⟫ • 1`. -/
theorem adjoint_mkL_comp_mkL [CompleteSpace F] [CompleteSpace (E ⊗[𝕜] F)] (x y : E) :
    (mkL 𝕜 E F x).adjoint ∘L mkL 𝕜 E F y = ⟪x, y⟫_𝕜 • (1 : F →L[𝕜] F) := by
  ext v
  simp [adjoint_mkL_apply_tmul]

/-- **Resolution of the identity** on `E ⊗ F` along an orthonormal basis `b` of `E`:
`Σᵢ ι_{bᵢ} ι_{bᵢ}† = 1`, that is, `z = Σᵢ bᵢ ⊗ ι_{bᵢ}† z`. -/
theorem sum_mkL_comp_adjoint_mkL [CompleteSpace F] [CompleteSpace (E ⊗[𝕜] F)] {ι : Type*}
    [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) :
    ∑ i, mkL 𝕜 E F (b i) ∘L (mkL 𝕜 E F (b i)).adjoint = 1 := by
  refine ContinuousLinearMap.coe_inj.mp <| ext' fun u v => ?_
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.toLinearMap_sum,
    LinearMap.coe_sum, Finset.sum_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    adjoint_mkL_apply_tmul, mkL_apply_apply, one_apply_eq_self]
  simp_rw [← smul_tmul, ← sum_tmul, b.sum_repr']

end TensorProduct
