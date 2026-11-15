/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.TensorProduct

import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Operators on tensor products of inner product spaces

Supplements to Mathlib's `Mathlib/Analysis/InnerProductSpace/TensorProduct.lean` for bounded
operators on the inner product space `E ⊗[𝕜] G`: the amplification `A ↦ A ⊗ 1` as a
⋆-homomorphism, tensor products of rank-one operators, and the adjoints of the insertions
`y ↦ x ⊗ y` and `x ↦ x ⊗ y`.

The operator tensor product `A ⊗ B` of `A : E →L[𝕜] F` and `B : G →L[𝕜] H` is Mathlib's
`TensorProduct.mapL A B`, and the amplification `A ⊗ 1` is `A.rTensor G`.

The statements that involve an adjoint or the order of operators on `E ⊗[𝕜] G` assume that algebraic
tensor product complete, as Mathlib's `TensorProduct.adjoint_mapL` does. It is complete when one
factor is finite-dimensional and the other complete
(`TensorProduct.completeSpace_of_finiteDimensional_left`,
`TensorProduct.completeSpace_of_finiteDimensional_right`); for Hilbert spaces in general the
statements are those on the completion `UniformSpace.Completion (E ⊗[𝕜] G)`.

## Main definitions

* `ContinuousLinearMap.rTensorStarAlgHom 𝕜 E G` — the amplification `A ↦ A ⊗ 1 = A.rTensor G` as a
  unital ⋆-homomorphism `B(E) →⋆ₐ B(E ⊗ G)`; `ContinuousLinearMap.lTensorStarAlgHom 𝕜 E G` — the
  amplification `A ↦ 1 ⊗ A = A.lTensor G`, `B(E) →⋆ₐ B(G ⊗ E)`.
* `TensorProduct.mapLEquiv 𝕜 E F G H` — for finite-dimensional `E` and `G`, the linear
  equivalence `(E →L F) ⊗ (G →L H) ≃ (E ⊗ G →L F ⊗ H)`, `f ⊗ g ↦ mapL f g`; so linear maps out
  of `E ⊗ G →L F ⊗ H` are determined on the `mapL f g` (`TensorProduct.ext_mapL`).
* `TensorProduct.mapLStarAlgEquiv 𝕜 E G` — the same equivalence for `F = E` and `H = G`, as a
  `⋆`-algebra equivalence `B(E) ⊗ B(G) ≃⋆ₐ B(E ⊗ G)`.

Nested tensor products `E ⊗ (F ⊗ G)` and `(E ⊗ F) ⊗ G` get shortcut instances for their normed
structures, without which the C⋆-algebra and Loewner order of their operators are not found
(see the section *Nested tensor products*).

## Main statements

* `TensorProduct.mapL_rankOne_rankOne` — `|x⟩⟨y| ⊗ |z⟩⟨w| = |x ⊗ z⟩⟨y ⊗ w|`.
* `TensorProduct.adjoint_mkL_apply_tmul` — the adjoint of the insertion `y ↦ x ⊗ y` is the
  partial inner product `x' ⊗ y' ↦ ⟪x, x'⟫ • y'`.
* `TensorProduct.adjoint_flip_mkL_apply_tmul` — the adjoint of the insertion `x ↦ x ⊗ y` is the
  partial inner product `x' ⊗ y' ↦ ⟪y, y'⟫ • x'`.
* `TensorProduct.mapL_rankOne_left` — `|x⟩⟨y| ⊗ B = ιₓ B ι_y†` for the insertions `ιₓ : z ↦ x ⊗ z`.
* `TensorProduct.lTensor_comp_mkL` — `(1 ⊗ A) ιₓ = ιₓ A`.
* `TensorProduct.rTensor_rankOne_eq_sum`, `TensorProduct.lTensor_rankOne_eq_sum` —
  `|x⟩⟨y| ⊗ 1 = Σⱼ |x ⊗ bⱼ⟩⟨y ⊗ bⱼ|` and its mirror image.
* `TensorProduct.trace_mapL` — `tr(A ⊗ B) = tr A · tr B`.
* `TensorProduct.mapL_nonneg` — the tensor product of positive operators is positive, for complex
  spaces with `E ⊗[ℂ] G` complete.
* `TensorProduct.adjoint_mkL_comp_mkL`, `TensorProduct.sum_mkL_comp_adjoint_mkL` — `ιₓ† ι_y = ⟪x, y⟫`,
  and `Σᵢ ι_{bᵢ} ι_{bᵢ}† = 1` along an orthonormal basis `b`.
-/

@[expose] public section

open scoped TensorProduct InnerProductSpace InnerProduct

variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-! ### Nested tensor products

The type `E ⊗[𝕜] (F ⊗[𝕜] G)` carries, for its inner factor `F ⊗ G`, the algebraic instances
`TensorProduct.addCommMonoid` and `TensorProduct.instModule`, whereas Mathlib's
`TensorProduct.instNormedAddCommGroup` and `TensorProduct.instInnerProductSpace` state their
conclusion with the factor's additive and module structure projected from its normed structure.
Unifying the two triggers a nested instance search for `NormedAddCommGroup (F ⊗ G)`. When the
outer search was itself started inside a unification (as for `ContinuousSMul`, the Loewner order or
`CStarAlgebra` on `E ⊗ (F ⊗ G) →L E ⊗ (F ⊗ G)`), this nested search runs at depth 2 and exceeds
the default `maxSynthPendingDepth = 1`, so these instances are not found. The shortcut instances
below state the normed structures with the nested type as it is elaborated, so that no nested
search is needed; their values are Mathlib's instances. They make the C⋆-algebra structure and the
order of `(E ⊗ F) ⊗ G →L[ℂ] (E ⊗ F) ⊗ G` available anywhere.

`set_option maxSynthPendingDepth 2 in` is the other workaround. The shortcuts do not cover
composites of generic constructions at nested types, which still time out at depth `1`.

TODO: fix the instance statements upstream so that nested tensor products of inner product spaces
need no shortcut, and remove these. Only one level of nesting (three factors) is covered. -/

namespace TensorProduct

/-- Shortcut instance for the right-nested tensor product `E ⊗ (F ⊗ G)`; see the section doc. -/
noncomputable instance instNormedAddCommGroupTensorRight :
    NormedAddCommGroup (E ⊗[𝕜] (F ⊗[𝕜] G)) :=
  TensorProduct.instNormedAddCommGroup

/-- Shortcut instance for the right-nested tensor product `E ⊗ (F ⊗ G)`; see the section doc. -/
noncomputable instance instInnerProductSpaceTensorRight :
    InnerProductSpace 𝕜 (E ⊗[𝕜] (F ⊗[𝕜] G)) :=
  TensorProduct.instInnerProductSpace

/-- Shortcut instance for the left-nested tensor product `(E ⊗ F) ⊗ G`; see the section doc. -/
noncomputable instance instNormedAddCommGroupTensorLeft :
    NormedAddCommGroup ((E ⊗[𝕜] F) ⊗[𝕜] G) :=
  TensorProduct.instNormedAddCommGroup

/-- Shortcut instance for the left-nested tensor product `(E ⊗ F) ⊗ G`; see the section doc. -/
noncomputable instance instInnerProductSpaceTensorLeft :
    InnerProductSpace 𝕜 ((E ⊗[𝕜] F) ⊗[𝕜] G) :=
  TensorProduct.instInnerProductSpace

end TensorProduct

/-! ### Completeness with a finite-dimensional factor

The algebraic tensor product of a finite-dimensional inner product space `E` and a complete one `F`
is complete: along an orthonormal basis `b` of `E`, `ξ ↦ ∑ᵢ bᵢ ⊗ ξᵢ` is an isometry of the Hilbert
sum of copies of `F` onto `E ⊗ F`. -/

namespace TensorProduct

/-- `E ⊗[𝕜] F` is complete when `E` is finite-dimensional and `F` is complete. -/
instance completeSpace_of_finiteDimensional_left [FiniteDimensional 𝕜 E] [CompleteSpace F] :
    CompleteSpace (E ⊗[𝕜] F) := by
  classical
  let b := stdOrthonormalBasis 𝕜 E
  let Ψ : PiLp 2 (fun _ : Fin (Module.finrank 𝕜 E) => F) →ₗ[𝕜] E ⊗[𝕜] F :=
    { toFun := fun ξ => ∑ i, b i ⊗ₜ[𝕜] ξ i
      map_add' := fun x y => by simp [TensorProduct.tmul_add, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [Finset.smul_sum] }
  have hnorm : ∀ ξ, ‖Ψ ξ‖ = ‖ξ‖ := fun ξ => by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), PiLp.norm_sq_eq_of_L2,
      @norm_sq_eq_re_inner 𝕜]
    change RCLike.re ⟪∑ i, b i ⊗ₜ[𝕜] ξ i, ∑ i, b i ⊗ₜ[𝕜] ξ i⟫_𝕜 = _
    simp only [sum_inner, inner_sum, TensorProduct.inner_tmul, orthonormal_iff_ite.1 b.orthonormal,
      ite_mul, one_mul, zero_mul, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i (fun j _ hji => by simp [hji])
      (fun h => (h (Finset.mem_univ i)).elim)]
    simp only [↓reduceIte]
    exact (@norm_sq_eq_re_inner 𝕜 _ _ _ _ (ξ i)).symm
  have hsurj : Function.Surjective Ψ := fun z => by
    induction z using TensorProduct.inductionOn with
    | tmul e f =>
      refine ⟨WithLp.toLp 2 fun i => b.repr e i • f, ?_⟩
      calc ∑ i, b i ⊗ₜ[𝕜] (b.repr e i • f) = ∑ i, (b.repr e i • b i) ⊗ₜ[𝕜] f :=
            Finset.sum_congr rfl fun i _ => by
              rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
        _ = (∑ i, b.repr e i • b i) ⊗ₜ[𝕜] f := (TensorProduct.sum_tmul _ _ _).symm
        _ = e ⊗ₜ[𝕜] f := by rw [b.sum_repr]
    | add p q hp hq =>
      obtain ⟨x, rfl⟩ := hp
      obtain ⟨y, rfl⟩ := hq
      exact ⟨x + y, map_add Ψ x y⟩
  exact ((LinearIsometryEquiv.ofSurjective ⟨Ψ, hnorm⟩ hsurj).symm.toIsometryEquiv).completeSpace

/-- `E ⊗[𝕜] F` is complete when `E` is complete and `F` is finite-dimensional. -/
instance completeSpace_of_finiteDimensional_right [CompleteSpace E] [FiniteDimensional 𝕜 F] :
    CompleteSpace (E ⊗[𝕜] F) :=
  ((TensorProduct.commIsometry 𝕜 E F).toIsometryEquiv).completeSpace

end TensorProduct

namespace ContinuousLinearMap

variable (𝕜 E G) in
/-- The **amplification** `A ↦ A ⊗ 1 = A.rTensor G` as a unital ⋆-homomorphism
`B(E) →⋆ₐ B(E ⊗ G)`, for `E ⊗[𝕜] G` complete. It is the identity representation of `B(E)` with
multiplicity `G`. -/
noncomputable def rTensorStarAlgHom [CompleteSpace E] [CompleteSpace G]
    [CompleteSpace (E ⊗[𝕜] G)] : (E →L[𝕜] E) →⋆ₐ[𝕜] (E ⊗[𝕜] G →L[𝕜] E ⊗[𝕜] G) where
  toFun A := A.rTensor G
  map_one' := rTensor_one G
  map_mul' A B := rTensor_mul G A B
  map_zero' := rTensor_zero G
  map_add' A B := rTensor_add G A B
  commutes' r := by simp [Algebra.algebraMap_eq_smul_one]
  map_star' A := by simp [star_eq_adjoint]

/-- The amplification sends `A` to `A ⊗ 1 = A.rTensor G`. -/
@[simp] lemma rTensorStarAlgHom_apply [CompleteSpace E] [CompleteSpace G]
    [CompleteSpace (E ⊗[𝕜] G)] (A : E →L[𝕜] E) : rTensorStarAlgHom 𝕜 E G A = A.rTensor G :=
  rfl

variable (𝕜 E G) in
/-- The **amplification** `A ↦ 1 ⊗ A = A.lTensor G` as a unital ⋆-homomorphism
`B(E) →⋆ₐ B(G ⊗ E)`, for `G ⊗[𝕜] E` complete, with the multiplicity space on the left. -/
noncomputable def lTensorStarAlgHom [CompleteSpace E] [CompleteSpace G]
    [CompleteSpace (G ⊗[𝕜] E)] : (E →L[𝕜] E) →⋆ₐ[𝕜] (G ⊗[𝕜] E →L[𝕜] G ⊗[𝕜] E) where
  toFun A := A.lTensor G
  map_one' := lTensor_one G
  map_mul' A B := lTensor_mul G A B
  map_zero' := lTensor_zero G
  map_add' A B := lTensor_add G A B
  commutes' r := by simp [Algebra.algebraMap_eq_smul_one]
  map_star' A := by simp [star_eq_adjoint]

/-- The amplification sends `A` to `1 ⊗ A = A.lTensor G`. -/
@[simp] lemma lTensorStarAlgHom_apply [CompleteSpace E] [CompleteSpace G]
    [CompleteSpace (G ⊗[𝕜] E)] (A : E →L[𝕜] E) : lTensorStarAlgHom 𝕜 E G A = A.lTensor G :=
  rfl

end ContinuousLinearMap

namespace TensorProduct

open InnerProductSpace

/-- The tensor product of rank-one operators is rank-one: `|x⟩⟨y| ⊗ |z⟩⟨w| = |x ⊗ z⟩⟨y ⊗ w|`. -/
lemma mapL_rankOne_rankOne (x : E) (y : F) (z : G) (w : H) :
    mapL (rankOne 𝕜 x y) (rankOne 𝕜 z w) = rankOne 𝕜 (x ⊗ₜ[𝕜] z) (y ⊗ₜ[𝕜] w) := by
  refine ContinuousLinearMap.coe_inj.mp <| ext' fun u v => ?_
  simp [TensorProduct.smul_tmul', smul_smul, mul_comm]

/-- The adjoint of the insertion `mkL 𝕜 E F x : y ↦ x ⊗ y` is the partial inner product
`x' ⊗ y' ↦ ⟪x, x'⟫ • y'`. -/
lemma adjoint_mkL_apply_tmul [CompleteSpace F] [CompleteSpace (E ⊗[𝕜] F)] (x x' : E) (y : F) :
    ((mkL 𝕜 E F x)†) (x' ⊗ₜ y) = ⟪x, x'⟫_𝕜 • y :=
  ext_inner_left 𝕜 fun w => by
    rw [ContinuousLinearMap.adjoint_inner_right, mkL_apply_apply, inner_tmul, inner_smul_right]

/-- The adjoint of the insertion `(mkL 𝕜 E F).flip y : x ↦ x ⊗ y` is the partial inner product
`x' ⊗ y' ↦ ⟪y, y'⟫ • x'`. -/
lemma adjoint_flip_mkL_apply_tmul [CompleteSpace E] [CompleteSpace (E ⊗[𝕜] F)] (y y' : F)
    (x : E) : (((mkL 𝕜 E F).flip y)†) (x ⊗ₜ y') = ⟪y, y'⟫_𝕜 • x :=
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
@[simp] lemma mapLEquiv_tmul [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 G] (f : E →L[𝕜] F)
    (g : G →L[𝕜] H) : mapLEquiv 𝕜 E F G H (f ⊗ₜ g) = mapL f g := by
  refine ContinuousLinearMap.coe_inj.mp <| ext' fun x y => ?_
  simp [mapLEquiv]

/-- Two linear maps out of `E ⊗ G →L F ⊗ H` agree if they agree on the operator tensors
`mapL f g`, which span it (`TensorProduct.mapLEquiv`). -/
lemma ext_mapL [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 G] {M : Type*} [AddCommGroup M]
    [Module 𝕜 M] {u v : (E ⊗[𝕜] G →L[𝕜] F ⊗[𝕜] H) →ₗ[𝕜] M}
    (h : ∀ (f : E →L[𝕜] F) (g : G →L[𝕜] H), u (mapL f g) = v (mapL f g)) : u = v := by
  refine LinearMap.ext fun X => ?_
  obtain ⟨z, rfl⟩ := (mapLEquiv 𝕜 E F G H).surjective X
  induction z using TensorProduct.inductionOn with
  | tmul f g => rw [mapLEquiv_tmul, h]
  | add z z' hz hz' => rw [map_add, map_add, map_add, hz, hz']

variable (𝕜 E G) in
/-- For finite-dimensional `E` and `G`, the linear equivalence `TensorProduct.mapLEquiv` of
`B(E) ⊗ B(G)` onto `B(E ⊗ G)`, `f ⊗ g ↦ mapL f g`, is a `⋆`-algebra equivalence. -/
noncomputable def mapLStarAlgEquiv [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 G]
    [CompleteSpace E] [CompleteSpace G] :
    (E →L[𝕜] E) ⊗[𝕜] (G →L[𝕜] G) ≃⋆ₐ[𝕜] (E ⊗[𝕜] G →L[𝕜] E ⊗[𝕜] G) where
  __ := mapLEquiv 𝕜 E E G G
  map_mul' x y := by
    change mapLEquiv 𝕜 E E G G (x * y) = mapLEquiv 𝕜 E E G G x * mapLEquiv 𝕜 E E G G y
    induction x using TensorProduct.inductionOn with
    | tmul f g =>
      induction y using TensorProduct.inductionOn with
      | tmul f' g' =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, mapLEquiv_tmul, mapLEquiv_tmul, mapLEquiv_tmul,
          mapL_mul]
      | add p q hp hq => rw [mul_add, map_add, hp, hq, map_add, mul_add]
    | add p q hp hq => rw [add_mul, map_add, hp, hq, map_add, add_mul]
  map_star' x := by
    change mapLEquiv 𝕜 E E G G (star x) = star (mapLEquiv 𝕜 E E G G x)
    induction x using TensorProduct.inductionOn with
    | tmul f g =>
      rw [star_tmul, mapLEquiv_tmul, mapLEquiv_tmul, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint, adjoint_mapL]
    | add p q hp hq => rw [star_add, map_add, hp, hq, map_add, star_add]

/-- `mapLStarAlgEquiv` sends `f ⊗ g` to the operator tensor product `mapL f g`. -/
@[simp] lemma mapLStarAlgEquiv_tmul [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 G]
    [CompleteSpace E] [CompleteSpace G] (f : E →L[𝕜] E) (g : G →L[𝕜] G) :
    mapLStarAlgEquiv 𝕜 E G (f ⊗ₜ g) = mapL f g :=
  mapLEquiv_tmul f g

/-- The tensor product of a rank-one operator with an operator `B` factors through the insertions
`ιₓ = mkL 𝕜 E H x : z ↦ x ⊗ z`: `|x⟩⟨y| ⊗ B = ιₓ B ι_y†`. -/
lemma mapL_rankOne_left [CompleteSpace G] [CompleteSpace (F ⊗[𝕜] G)] (x : E) (y : F)
    (B : G →L[𝕜] H) :
    mapL (rankOne 𝕜 x y) B = mkL 𝕜 E H x ∘L B ∘L (mkL 𝕜 F G y)† := by
  refine ContinuousLinearMap.coe_inj.mp <| ext' fun u v => ?_
  simp [adjoint_mkL_apply_tmul, smul_tmul]

/-- The insertion `ιₓ : z ↦ x ⊗ z` intertwines `A` with `1 ⊗ A`: `(1 ⊗ A) ιₓ = ιₓ A`. -/
lemma lTensor_comp_mkL (x : E) (A : G →L[𝕜] H) :
    A.lTensor E ∘L mkL 𝕜 E G x = mkL 𝕜 E H x ∘L A := by
  ext z
  simp

/-- The insertions are orthogonal: `ιₓ† ι_y = ⟪x, y⟫ • 1`. -/
lemma adjoint_mkL_comp_mkL [CompleteSpace F] [CompleteSpace (E ⊗[𝕜] F)] (x y : E) :
    (mkL 𝕜 E F x)† ∘L mkL 𝕜 E F y = ⟪x, y⟫_𝕜 • (1 : F →L[𝕜] F) := by
  ext v
  simp [adjoint_mkL_apply_tmul]

/-- **Resolution of the identity** on `E ⊗ F` along an orthonormal basis `b` of `E`:
`Σᵢ ι_{bᵢ} ι_{bᵢ}† = 1`, that is, `z = Σᵢ bᵢ ⊗ ι_{bᵢ}† z`. -/
lemma sum_mkL_comp_adjoint_mkL [CompleteSpace F] [CompleteSpace (E ⊗[𝕜] F)] {ι : Type*}
    [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) :
    ∑ i, mkL 𝕜 E F (b i) ∘L (mkL 𝕜 E F (b i))† = 1 := by
  refine ContinuousLinearMap.coe_inj.mp <| ext' fun u v => ?_
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.toLinearMap_sum,
    LinearMap.coe_sum, Finset.sum_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    adjoint_mkL_apply_tmul, mkL_apply_apply, one_apply_eq_self]
  simp_rw [← smul_tmul, ← sum_tmul, b.sum_repr']

/-- `|x⟩⟨y| ⊗ 1 = Σⱼ |x ⊗ bⱼ⟩⟨y ⊗ bⱼ|` along an orthonormal basis `b` of the second factor. -/
lemma rTensor_rankOne_eq_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι 𝕜 G) (x y : E) :
    (rankOne 𝕜 x y).rTensor G = ∑ j, rankOne 𝕜 (x ⊗ₜ[𝕜] b j) (y ⊗ₜ[𝕜] b j) := by
  refine ContinuousLinearMap.coe_inj.mp <| ext' fun u v => ?_
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.rTensor_tmul, rankOne_apply,
    ContinuousLinearMap.toLinearMap_sum, LinearMap.coe_sum, Finset.sum_apply, inner_tmul]
  conv_lhs => rw [← b.sum_repr' v, tmul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [tmul_smul, ← smul_tmul', smul_smul]
  rw [mul_comm]

/-- `1 ⊗ |x⟩⟨y| = Σᵢ |bᵢ ⊗ x⟩⟨bᵢ ⊗ y|` along an orthonormal basis `b` of the first factor. -/
lemma lTensor_rankOne_eq_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) (x y : G) :
    (rankOne 𝕜 x y).lTensor E = ∑ i, rankOne 𝕜 (b i ⊗ₜ[𝕜] x) (b i ⊗ₜ[𝕜] y) := by
  refine ContinuousLinearMap.coe_inj.mp <| ext' fun u v => ?_
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.lTensor_tmul, rankOne_apply,
    ContinuousLinearMap.toLinearMap_sum, LinearMap.coe_sum, Finset.sum_apply, inner_tmul]
  conv_lhs => rw [← b.sum_repr' u, sum_tmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [tmul_smul, ← smul_tmul', smul_smul]
  rw [mul_comm]

/-- The trace is multiplicative on operator tensor products: `tr(A ⊗ B) = tr A · tr B`
(`LinearMap.trace_tensorProduct'`). -/
lemma trace_mapL [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 G] (A : E →L[𝕜] E)
    (B : G →L[𝕜] G) :
    LinearMap.trace 𝕜 (E ⊗[𝕜] G) (mapL A B) = LinearMap.trace 𝕜 E A * LinearMap.trace 𝕜 G B := by
  rw [toLinearMap_mapL, LinearMap.trace_tensorProduct']

open scoped ComplexOrder in
/-- **The tensor product of positive operators is positive**, for complex Hilbert spaces whose
algebraic tensor product `E ⊗[ℂ] G` is complete: with `A = a⋆ a` and `B = b⋆ b`,
`A ⊗ B = (a ⊗ b)⋆ (a ⊗ b)`. -/
theorem mapL_nonneg {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] [CompleteSpace (E ⊗[ℂ] G)]
    {A : E →L[ℂ] E} {B : G →L[ℂ] G} (hA : 0 ≤ A) (hB : 0 ≤ B) : 0 ≤ mapL A B := by
  obtain ⟨a, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA
  obtain ⟨b, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB
  rw [mapL_mul, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
    ← adjoint_mapL, ← ContinuousLinearMap.star_eq_adjoint]
  exact star_mul_self_nonneg _

end TensorProduct
