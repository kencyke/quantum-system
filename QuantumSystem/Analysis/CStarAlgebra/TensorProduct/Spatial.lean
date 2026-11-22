/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Algebra.Star.TensorProduct
public import QuantumSystem.Analysis.CStarAlgebra.Representation.VectorFunctional
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.TensorProduct

import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Basis
import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.Hom
import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.Quotient
import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.Stinespring

/-!
# The tensor product of two representations

For representations `π` of a C⋆-algebra `A` on `H` and `ρ` of a C⋆-algebra `B` on `K`, the
operators `π(a) ⊗ ρ(b)` on the Hilbert space tensor product `Completion (H ⊗[ℂ] K)` define a
`⋆`-homomorphism `π ⊗ ρ` of the algebraic tensor product `A ⊗[ℂ] B` into the operators on
`Completion (H ⊗[ℂ] K)`: `CStarRep.spatial`. For faithful `π` and `ρ` it is faithful, and the norm
`x ↦ ‖(π ⊗ ρ)(x)‖` it induces on `A ⊗[ℂ] B` is the same for every pair of faithful
representations. This is the spatial C⋆-norm; the completion of `A ⊗[ℂ] B` in it is the minimal
tensor product of `QuantumSystem/Analysis/CStarAlgebra/TensorProduct/Minimal.lean`.

The algebras are not assumed unital, as for `CStarRep`. The operator `π(a) ⊗ ρ(b)` is the completion
`(TensorProduct.mapL (π a) (ρ b)).completion` of Mathlib's operator tensor product, and `R.spatial S`
is the tensor product `NonUnitalStarAlgHom.mapLCompletion` of the `⋆`-homomorphisms `π` and `ρ`,
which needs no C⋆-algebra structure on `A` and `B`; the results below do. `R.spatial S` is
a `⋆`-homomorphism of the algebraic tensor product, which is no C⋆-algebra, and not a `CStarRep`:
its extension to a representation of the minimal tensor product is `CStarRep.tensorProduct`, in
`QuantumSystem/Analysis/CStarAlgebra/TensorProduct/Minimal.lean`.

## Main definitions

* `CStarRep.spatial R S` — the tensor product `π ⊗ ρ : A ⊗[ℂ] B →⋆ₙₐ[ℂ] B(Completion (H ⊗[ℂ] K))`
  of two representations.

## Main results

* `CStarRep.norm_spatial_tmul` — the cross norm `‖π(a) ⊗ ρ(b)‖ = ‖π(a)‖ * ‖ρ(b)‖`.
* `CStarRep.denseRange_spatial_apply_tmul` — the orbit of `ξ ⊗ η` under `(π ⊗ ρ)(A ⊗[ℂ] B)` is dense
  when those of `ξ` and `η` are.
* `CStarRep.spatial_injective` — the tensor product of two faithful representations is faithful on
  the algebraic tensor product.
* `CStarRep.norm_spatial_le_of_injective` — `‖(π' ⊗ ρ')(x)‖ ≤ ‖(π ⊗ ρ)(x)‖` for faithful `π`, `ρ`
  and any `π'`, `ρ'`.
* `CStarRep.norm_spatial_eq_of_injective` — hence the norm `‖(π ⊗ ρ)(x)‖` does not depend on the
  faithful representations `π` and `ρ`.
* `CStarRep.norm_spatial_le_of_forall` — families of representations of `A` and of `B` with no
  common kernel bound the norm of `(π' ⊗ ρ')(x)` for all representations `π'` and `ρ'`: a common
  bound `c ≥ 0` of the `‖(πᵢ ⊗ ρⱼ)(x)‖` bounds it.
* `CStarRep.norm_spatial_comm` — swapping the factors does not change the norm.
* `CStarRep.isClosed_range_spatial_of_finiteDimensional_left`,
  `CStarRep.isClosed_range_spatial_of_finiteDimensional_right` — the image of `A ⊗[ℂ] B` under
  `π ⊗ ρ` is norm closed when `A` or `B` is finite-dimensional.

## Implementation notes

The independence is proved one factor at a time. A finite orthonormal family `e` of `K` gives an
isometry `TensorProduct.sumTmulL e` of the Hilbert sum of copies of `H` into
`Completion (H ⊗[ℂ] K)`, and the compression of `(π ⊗ ρ)(x)` by it is the image under `π`, entry by
entry, of a matrix over `A` that depends on `ρ`, `e` and `x` only. The matrix amplification of an
injective `⋆`-homomorphism is injective, hence isometric, so for a faithful `π` the norm of the
compression does not depend on `π`; and the norm of an operator on `Completion (H ⊗[ℂ] K)` is the
supremum of the norms of these compressions: it is at most a common bound of them
(`ContinuousLinearMap.opNorm_le_of_forall_inner_sumTmulL`), and each compression, by an isometry, has
norm at most that of the operator.
-/

@[expose] public section

open scoped TensorProduct InnerProduct InnerProductSpace Amplification

open UniformSpace TensorProduct

universe u v w w₁ w₂ w₃

namespace CStarRep

variable {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- The tensor product `π ⊗ ρ` of two representations `π` of `A` on `H` and `ρ` of `B` on `K`,
**on the algebraic tensor product**: the `⋆`-homomorphism of `A ⊗[ℂ] B` into the operators on the
Hilbert space tensor product `Completion (H ⊗[ℂ] K)` that sends `a ⊗ b` to `π(a) ⊗ ρ(b)`, the
tensor product `NonUnitalStarAlgHom.mapLCompletion` of the `⋆`-homomorphisms `π` and `ρ`. It
induces the spatial norm `x ↦ ‖(π ⊗ ρ)(x)‖`; its extension to `A ⊗ₘᵢₙ B`, a representation, is
`CStarRep.tensorProduct`. -/
noncomputable def spatial (R : CStarRep A) (S : CStarRep B) :
    A ⊗[ℂ] B →⋆ₙₐ[ℂ] (Completion (R.H ⊗[ℂ] S.H) →L[ℂ] Completion (R.H ⊗[ℂ] S.H)) :=
  NonUnitalStarAlgHom.mapLCompletion R.π S.π

/-- `R.spatial S` sends the pure tensor `a ⊗ b` to the operator `π(a) ⊗ ρ(b)`. -/
@[simp] lemma spatial_tmul (R : CStarRep A) (S : CStarRep B) (a : A) (b : B) :
    R.spatial S (a ⊗ₜ[ℂ] b) = R.π a ⊗ S.π b := rfl

/-- The tensor product of two representations has the cross norm `‖π(a) ⊗ ρ(b)‖ = ‖π(a)‖ * ‖ρ(b)‖`
on pure tensors. -/
lemma norm_spatial_tmul (R : CStarRep A) (S : CStarRep B) (a : A) (b : B) :
    ‖R.spatial S (a ⊗ₜ[ℂ] b)‖ = ‖R.π a‖ * ‖S.π b‖ := by
  rw [spatial_tmul, ContinuousLinearMap.norm_completion_mapL]

/-- The tensor product of two unital representations of unital C⋆-algebras is unital:
`(π ⊗ ρ)(1 ⊗ 1) = 1`. -/
lemma spatial_one_tmul_one {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
    (R : CStarRep A) (S : CStarRep B) (hR : R.π 1 = 1) (hS : S.π 1 = 1) :
    R.spatial S (1 ⊗ₜ[ℂ] 1) = 1 := by
  rw [spatial_tmul, hR, hS]
  simp only [ContinuousLinearMap.one_def, mapL_id_id, ContinuousLinearMap.completion_id]

/-- On a pure tensor of vectors, `(π ⊗ ρ)(a ⊗ b) (ξ ⊗ η) = π(a) ξ ⊗ ρ(b) η`. -/
lemma spatial_tmul_apply_tmul (R : CStarRep A) (S : CStarRep B) (a : A) (b : B)
    (ξ : R.H) (η : S.H) :
    R.spatial S (a ⊗ₜ[ℂ] b) ↑(ξ ⊗ₜ[ℂ] η) = ↑(R.π a ξ ⊗ₜ[ℂ] S.π b η) := by
  rw [spatial_tmul, ContinuousLinearMap.completion_apply_coe, TensorProduct.mapL_tmul]

/-- The vector functional of `ξ ⊗ η` in the tensor product of two representations is, on pure
tensors, the product of the vector functionals of `ξ` and `η`:
`⟪ξ ⊗ η, (π ⊗ ρ)(a ⊗ b) (ξ ⊗ η)⟫ = ⟪ξ, π(a) ξ⟫ * ⟪η, ρ(b) η⟫`. -/
lemma inner_tmul_spatial_tmul_apply_tmul (R : CStarRep A) (S : CStarRep B) (a : A)
    (b : B) (ξ : R.H) (η : S.H) :
    ⟪(↑(ξ ⊗ₜ[ℂ] η) : Completion (R.H ⊗[ℂ] S.H)), R.spatial S (a ⊗ₜ[ℂ] b) ↑(ξ ⊗ₜ[ℂ] η)⟫_ℂ =
      ⟪ξ, R.π a ξ⟫_ℂ * ⟪η, S.π b η⟫_ℂ := by
  rw [spatial_tmul_apply_tmul, Completion.inner_coe, TensorProduct.inner_tmul]

/-- If the orbits of `ξ` under `π(A)` and of `η` under `ρ(B)` are dense, so is the orbit of `ξ ⊗ η`
under `(π ⊗ ρ)(A ⊗[ℂ] B)`. For the representation `CStarRep.tensorProduct` of the minimal tensor
product this says that `ξ ⊗ η` is cyclic: `CStarRep.denseRange_orbit_tensorProduct`. -/
lemma denseRange_spatial_apply_tmul (R : CStarRep A) (S : CStarRep B) {ξ : R.H}
    {η : S.H} (hξ : DenseRange (R.orbit ξ)) (hη : DenseRange (S.orbit η)) :
    DenseRange fun y : A ⊗[ℂ] B => R.spatial S y ↑(ξ ⊗ₜ[ℂ] η) := by
  let F : A ⊗[ℂ] B →ₗ[ℂ] Completion (R.H ⊗[ℂ] S.H) :=
    (ContinuousLinearMap.apply ℂ (Completion (R.H ⊗[ℂ] S.H))
      ((ξ ⊗ₜ[ℂ] η : R.H ⊗[ℂ] S.H) : Completion (R.H ⊗[ℂ] S.H))).toLinearMap ∘ₗ
        (R.spatial S : A ⊗[ℂ] B →ₗ[ℂ] _)
  have hcont : Continuous fun p : R.H × S.H =>
      ((p.1 ⊗ₜ[ℂ] p.2 : R.H ⊗[ℂ] S.H) : Completion (R.H ⊗[ℂ] S.H)) :=
    (Completion.continuous_coe _).comp (IsBoundedBilinearMap.continuous (𝕜 := ℂ)
      { add_left := TensorProduct.add_tmul
        smul_left := fun c h k => (TensorProduct.smul_tmul' c h k).symm
        add_right := TensorProduct.tmul_add
        smul_right := fun c h k => TensorProduct.tmul_smul c h k
        bound := ⟨1, zero_lt_one, fun h k => by rw [TensorProduct.norm_tmul, one_mul]⟩ })
  have htm (p : R.H × S.H) : ((p.1 ⊗ₜ[ℂ] p.2 : R.H ⊗[ℂ] S.H) : Completion (R.H ⊗[ℂ] S.H)) ∈
      (LinearMap.range F).topologicalClosure :=
    (hξ.prodMap hη).induction_on p
      ((LinearMap.range F).isClosed_topologicalClosure.preimage hcont)
      fun q => Submodule.le_topologicalClosure _
        ⟨q.1 ⊗ₜ[ℂ] q.2, spatial_tmul_apply_tmul R S q.1 q.2 ξ η⟩
  have hall (z : R.H ⊗[ℂ] S.H) :
      (z : Completion (R.H ⊗[ℂ] S.H)) ∈ (LinearMap.range F).topologicalClosure := by
    induction z using TensorProduct.inductionOn with
    | tmul h k => exact htm (h, k)
    | add p q hp hq =>
      rw [Completion.coe_add]
      exact add_mem hp hq
  intro w
  exact Completion.induction_on w (LinearMap.range F).isClosed_topologicalClosure hall

/-! ### Matrix coefficients along the second factor

For vectors `η`, `η'` of the second representation, the matrix coefficient `⟪η, ρ(·) η'⟫` is
`CStarRep.matrixCoeff`, and `id ⊗ ⟪η, ρ(·) η'⟫` maps `A ⊗[ℂ] B` to `A`.
A finite family `e` of such vectors turns `x` into the matrix `[(id ⊗ ⟪eᵢ, ρ(·) eⱼ⟫) x]` over `A`,
whose image under the first representation is the compression of `(π ⊗ ρ)(x)` to the range of
`TensorProduct.sumTmulL e` in the completed tensor product. The matrix does not involve the first
representation. -/

section Slice

variable {ι : Type*}

/-- The matrix `[(id ⊗ ⟪eᵢ, ρ(·) eⱼ⟫) x]` over `A` of `x : A ⊗[ℂ] B`. -/
private noncomputable def sliceMatrix (S : CStarRep B) (e : ι → S.H) :
    A ⊗[ℂ] B →ₗ[ℂ] CStarMatrix ι ι A where
  toFun x := CStarMatrix.ofMatrix
    (Matrix.of fun i j =>
      TensorProduct.rid ℂ A ((S.matrixCoeff (e i) (e j) : B →ₗ[ℂ] ℂ).lTensor A x))
  map_add' x y := by ext i j; simp
  map_smul' c x := by ext i j; simp

private lemma sliceMatrix_apply (S : CStarRep B) (e : ι → S.H) (x : A ⊗[ℂ] B) (i j : ι) :
    S.sliceMatrix e x i j =
      TensorProduct.rid ℂ A ((S.matrixCoeff (e i) (e j) : B →ₗ[ℂ] ℂ).lTensor A x) := rfl

private lemma sliceMatrix_tmul (S : CStarRep B) (e : ι → S.H) (a : A) (b : B) (i j : ι) :
    S.sliceMatrix e (a ⊗ₜ[ℂ] b) i j = ⟪e i, S.π b (e j)⟫_ℂ • a := by
  simp [sliceMatrix_apply]

variable [Fintype ι]

/-- The compression of `(π ⊗ ρ)(x)` to the range of `sumTmulL e` is the image under `π` of the
matrix `sliceMatrix e x`. -/
private lemma inner_sumTmulL_spatial_sumTmulL [DecidableEq ι] (R : CStarRep A)
    (S : CStarRep B) (e : ι → S.H) (x : A ⊗[ℂ] B) (ξ ξ' : PiLp 2 (fun _ : ι => R.H)) :
    ⟪((sumTmulL e ξ : R.H ⊗[ℂ] S.H) : Completion (R.H ⊗[ℂ] S.H)),
        R.spatial S x (sumTmulL e ξ' : R.H ⊗[ℂ] S.H)⟫_ℂ =
      ⟪ξ, CStarMatrix.toPiLpStarAlgEquiv ι R.H (CStarMatrix.mapₙₐ R.π (S.sliceMatrix e x)) ξ'⟫_ℂ := by
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    rw [spatial_tmul, ContinuousLinearMap.completion_apply_coe, Completion.inner_coe,
      inner_sumTmulL_mapL, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [CStarMatrix.toPiLpStarAlgEquiv_apply, inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [sliceMatrix_tmul, inner_smul_right, mul_comm]
  | add p q hp hq => simp only [map_add, add_apply, inner_add_right, hp, hq]

/-- The `⋆`-isomorphism `M_ι(B(H)) ≃ B(H^ι)` is isometric. -/
private lemma norm_toPiLpStarAlgEquiv [DecidableEq ι] {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (Y : CStarMatrix ι ι (H →L[ℂ] H)) :
    ‖CStarMatrix.toPiLpStarAlgEquiv ι H Y‖ = ‖Y‖ :=
  NonUnitalStarAlgHom.norm_map (CStarMatrix.toPiLpStarAlgEquiv ι H) (EquivLike.injective _) Y

/-- For an orthonormal family `e`, the image under `π` of the matrix `sliceMatrix e x` is a
compression of `(π ⊗ ρ)(x)` by an isometry, so its norm is at most `‖(π ⊗ ρ)(x)‖`. -/
private lemma norm_mapₙₐ_sliceMatrix_le (R : CStarRep A) (S : CStarRep B)
    {e : ι → S.H} (he : Orthonormal ℂ e) (x : A ⊗[ℂ] B) :
    ‖CStarMatrix.mapₙₐ R.π (S.sliceMatrix e x)‖ ≤ ‖R.spatial S x‖ := by
  classical
  rw [← norm_toPiLpStarAlgEquiv]
  refine ContinuousLinearMap.opNorm_le_of_re_inner_le (norm_nonneg (R.spatial S x))
    fun ξ' ξ hξ' hξ => ?_
  rw [← inner_re_symm, ← inner_sumTmulL_spatial_sumTmulL]
  set u : Completion (R.H ⊗[ℂ] S.H) := ((sumTmulL e ξ : R.H ⊗[ℂ] S.H) : Completion (R.H ⊗[ℂ] S.H))
  set u' : Completion (R.H ⊗[ℂ] S.H) := ((sumTmulL e ξ' : R.H ⊗[ℂ] S.H) : Completion (R.H ⊗[ℂ] S.H))
  have hu : ‖u‖ = 1 := by rw [Completion.norm_coe, norm_sumTmulL_apply he, hξ]
  have hu' : ‖u'‖ = 1 := by rw [Completion.norm_coe, norm_sumTmulL_apply he, hξ']
  calc RCLike.re ⟪u, R.spatial S x u'⟫_ℂ
      ≤ ‖⟪u, R.spatial S x u'⟫_ℂ‖ := RCLike.re_le_norm _
    _ ≤ ‖u‖ * ‖R.spatial S x u'‖ := norm_inner_le_norm _ _
    _ ≤ ‖u‖ * (‖R.spatial S x‖ * ‖u'‖) := by
      gcongr
      exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖R.spatial S x‖ := by rw [hu, hu', mul_one, one_mul]

/-- **The tensor product of two faithful representations is faithful** on the algebraic tensor
product: if `π` and `ρ` are injective, so is `π ⊗ ρ : A ⊗[ℂ] B → B(Completion (H ⊗[ℂ] K))`. -/
theorem spatial_injective {R : CStarRep A} {S : CStarRep B}
    (hR : Function.Injective R.π) (hS : Function.Injective S.π) :
    Function.Injective (R.spatial S) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hslice (η η' : S.H) :
      TensorProduct.rid ℂ A ((S.matrixCoeff η η' : B →ₗ[ℂ] ℂ).lTensor A x) = 0 := by
    have hM : CStarMatrix.mapₙₐ R.π (S.sliceMatrix ![η, η'] x) = 0 := by
      have h0 : CStarMatrix.toPiLpStarAlgEquiv (Fin 2) R.H
          (CStarMatrix.mapₙₐ R.π (S.sliceMatrix ![η, η'] x)) = 0 := by
        refine ContinuousLinearMap.ext fun ξ' => ext_inner_left ℂ fun ξ => ?_
        rw [← inner_sumTmulL_spatial_sumTmulL, hx]
        simp
      exact EquivLike.injective (CStarMatrix.toPiLpStarAlgEquiv (Fin 2) R.H)
        (h0.trans (map_zero _).symm)
    have h01 : R.π (S.sliceMatrix ![η, η'] x 0 1) = 0 := congrFun (congrFun hM 0) 1
    rw [← map_zero R.π] at h01
    simpa [sliceMatrix_apply] using hR h01
  obtain ⟨c, rfl⟩ := eq_repr_basis_left (Module.Basis.ofVectorSpace ℂ A) x
  suffices hc : c = 0 by simp [hc]
  ext k
  refine hS ?_
  rw [Finsupp.zero_apply, map_zero]
  refine ContinuousLinearMap.ext fun η' => ext_inner_left ℂ fun η => ?_
  have h := hslice η η'
  simp only [Finsupp.sum, map_sum, LinearMap.lTensor_tmul, TensorProduct.rid_tmul, LinearMap.coe_ofClass,
    matrixCoeff_apply] at h
  by_cases hk : k ∈ c.support
  · simpa using linearIndependent_iff'.1 (Module.Basis.ofVectorSpace ℂ A).linearIndependent
      c.support _ h k hk
  · simp [Finsupp.notMem_support_iff.1 hk]

omit [Fintype ι] in
/-- The matrix coefficients of `(π ⊗ ρ)(z)` at pure tensors are those of `π` at the slice of `z` by
a matrix coefficient of `ρ`. -/
lemma inner_tmul_spatial_apply_tmul (R : CStarRep A) (S : CStarRep B) (ξ ξ' : R.H)
    (η η' : S.H) (z : A ⊗[ℂ] B) :
    ⟪(↑(ξ ⊗ₜ[ℂ] η) : Completion (R.H ⊗[ℂ] S.H)), R.spatial S z ↑(ξ' ⊗ₜ[ℂ] η')⟫_ℂ =
      ⟪ξ, R.π (TensorProduct.rid ℂ A ((S.matrixCoeff η η' : B →ₗ[ℂ] ℂ).lTensor A z)) ξ'⟫_ℂ := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    rw [spatial_tmul_apply_tmul, Completion.inner_coe, TensorProduct.inner_tmul,
      LinearMap.lTensor_tmul, TensorProduct.rid_tmul, map_smul, smul_apply, inner_smul_right,
      LinearMap.coe_ofClass, matrixCoeff_apply, mul_comm]
  | add p q hp hq => simp only [map_add, add_apply, inner_add_right, hp, hq]

omit [Fintype ι] in
/-- For a faithful `π`, the slice `id ⊗ ⟪η, ρ(·) η'⟫ : A ⊗[ℂ] B → A` is bounded by `‖η‖ ‖η'‖` for
the norm `z ↦ ‖(π ⊗ ρ)(z)‖`. -/
lemma norm_rid_lTensor_matrixCoeff_le {R : CStarRep A} (hR : Function.Injective R.π) (S : CStarRep B)
    (η η' : S.H) (z : A ⊗[ℂ] B) :
    ‖TensorProduct.rid ℂ A ((S.matrixCoeff η η' : B →ₗ[ℂ] ℂ).lTensor A z)‖ ≤ ‖R.spatial S z‖ * ‖η‖ * ‖η'‖ := by
  rw [← NonUnitalStarAlgHom.norm_map R.π hR]
  refine ContinuousLinearMap.opNorm_le_of_re_inner_le (by positivity) fun ξ' ξ hξ' hξ => ?_
  rw [← inner_re_symm, ← inner_tmul_spatial_apply_tmul]
  calc RCLike.re ⟪(↑(ξ ⊗ₜ[ℂ] η) : Completion (R.H ⊗[ℂ] S.H)), R.spatial S z ↑(ξ' ⊗ₜ[ℂ] η')⟫_ℂ
      ≤ ‖⟪(↑(ξ ⊗ₜ[ℂ] η) : Completion (R.H ⊗[ℂ] S.H)), R.spatial S z ↑(ξ' ⊗ₜ[ℂ] η')⟫_ℂ‖ :=
        RCLike.re_le_norm _
    _ ≤ ‖(↑(ξ ⊗ₜ[ℂ] η) : Completion (R.H ⊗[ℂ] S.H))‖ * ‖R.spatial S z ↑(ξ' ⊗ₜ[ℂ] η')‖ :=
        norm_inner_le_norm _ _
    _ ≤ ‖(↑(ξ ⊗ₜ[ℂ] η) : Completion (R.H ⊗[ℂ] S.H))‖ *
          (‖R.spatial S z‖ * ‖(↑(ξ' ⊗ₜ[ℂ] η') : Completion (R.H ⊗[ℂ] S.H))‖) := by
        gcongr
        exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖R.spatial S z‖ * ‖η‖ * ‖η'‖ := by
        rw [Completion.norm_coe, Completion.norm_coe, TensorProduct.norm_tmul,
          TensorProduct.norm_tmul, hξ, hξ']
        ring

/-! ### A finite-dimensional factor

When `B` is finite-dimensional, the coordinates of `x : A ⊗[ℂ] B` along a basis of `B` are bounded
by the norm of `(π ⊗ ρ)(x)`, for faithful `π` and `ρ`: the vector functionals `⟪η, ρ(·) η⟫` span the
dual of `B`, and each `id ⊗ ⟪η, ρ(·) η⟫` is a contraction for that norm. Hence the image of
`A ⊗[ℂ] B` is closed; for arbitrary `π` and `ρ` it is the image under the tensor product of the
inclusions of the C⋆-algebras `π(A)` and `ρ(B)`, which are faithful. -/

omit [Fintype ι] in
/-- For a faithful representation `ρ` of a finite-dimensional `B`, the vector functionals
`⟪η, ρ(·) η⟫` of the unit vectors `η` span the dual of `B`. -/
private lemma span_vectorFunctional_eq_top [FiniteDimensional ℂ B] {S : CStarRep B}
    (hS : Function.Injective S.π) :
    Submodule.span ℂ {φ : Module.Dual ℂ B | ∃ η : S.H, ‖η‖ = 1 ∧ φ = S.vectorFunctional η} = ⊤ := by
  rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ _)]
  suffices h : (Submodule.span ℂ {φ : Module.Dual ℂ B | ∃ η : S.H, ‖η‖ = 1 ∧ φ = S.vectorFunctional η}
      ).dualCoannihilator = ⊥ by rw [h, Submodule.dualAnnihilator_bot]
  refine (Submodule.eq_bot_iff _).2 fun b hb => ?_
  rw [Submodule.mem_dualCoannihilator] at hb
  have hunit (η : S.H) (hη : ‖η‖ = 1) : ⟪η, S.π b η⟫_ℂ = 0 :=
    hb _ (Submodule.subset_span ⟨η, hη, rfl⟩)
  have hzero (η : S.H) : ⟪S.π b η, η⟫_ℂ = 0 := by
    by_cases h0 : η = 0
    · rw [h0, inner_zero_right]
    have h := hunit ((‖η‖⁻¹ : ℂ) • η) (norm_smul_inv_norm h0)
    rw [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc] at h
    have hne : (starRingEnd ℂ) (‖η‖⁻¹ : ℂ) * (‖η‖⁻¹ : ℂ) ≠ 0 := by
      simp [h0]
    have h' : ⟪η, S.π b η⟫_ℂ = 0 := (mul_eq_zero.1 h).resolve_left hne
    rw [← inner_conj_symm, h', map_zero]
  have hπ : (S.π b : S.H →ₗ[ℂ] S.H) = 0 := (inner_map_self_eq_zero _).1 hzero
  exact hS (by rw [map_zero]; exact ContinuousLinearMap.coe_injective hπ)

omit [Fintype ι] in
/-- The image of the algebraic tensor product under the tensor product of two faithful
representations is closed when the second algebra is finite-dimensional. -/
private lemma isClosed_range_spatial_of_injective [FiniteDimensional ℂ B]
    {R : CStarRep A} {S : CStarRep B} (hR : Function.Injective R.π)
    (hS : Function.Injective S.π) : IsClosed (Set.range (R.spatial S)) := by
  -- each `id ⊗ φ : A ⊗[ℂ] B → A`, `φ` a functional on `B`, is bounded for `x ↦ ‖(π ⊗ ρ)(x)‖`
  have hbound (φ : Module.Dual ℂ B) : ∃ C : ℝ, ∀ x : A ⊗[ℂ] B,
      ‖TensorProduct.rid ℂ A (φ.lTensor A x)‖ ≤ C * ‖R.spatial S x‖ := by
    have hφ : φ ∈ Submodule.span ℂ {φ : Module.Dual ℂ B | ∃ η : S.H, ‖η‖ = 1 ∧ φ = S.vectorFunctional η} := by
      rw [span_vectorFunctional_eq_top hS]
      trivial
    induction hφ using Submodule.span_induction with
    | mem φ h =>
      obtain ⟨η, hη, rfl⟩ := h
      refine ⟨1, fun x => ?_⟩
      have h := norm_rid_lTensor_matrixCoeff_le hR S η η x
      rw [hη, mul_one, mul_one] at h
      rwa [one_mul]
    | zero => exact ⟨0, fun x => by simp⟩
    | add φ ψ _ _ hφ hψ =>
      obtain ⟨C, hC⟩ := hφ
      obtain ⟨C', hC'⟩ := hψ
      refine ⟨C + C', fun x => ?_⟩
      rw [LinearMap.lTensor_add, LinearMap.add_apply, map_add, add_mul]
      exact (norm_add_le _ _).trans (add_le_add (hC x) (hC' x))
    | smul c φ _ hφ =>
      obtain ⟨C, hC⟩ := hφ
      refine ⟨‖c‖ * C, fun x => ?_⟩
      rw [LinearMap.lTensor_smul, LinearMap.smul_apply, map_smul, norm_smul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg c)
  let ℬ := Module.finBasis ℂ B
  choose C hC using fun i => hbound (ℬ.coord i)
  -- the coordinates of `A ⊗[ℂ] B` along the basis `ℬ` of `B`
  let e : A ⊗[ℂ] B ≃ₗ[ℂ] (Fin (Module.finrank ℂ B) → A) :=
    (TensorProduct.equivFinsuppOfBasisRight ℬ).trans (Finsupp.linearEquivFunOnFinite ℂ A _)
  have he (x : A ⊗[ℂ] B) (i : Fin (Module.finrank ℂ B)) :
      e x i = TensorProduct.rid ℂ A ((ℬ.coord i).lTensor A x) :=
    TensorProduct.equivFinsuppOfBasisRight_apply ℬ x i
  have hsymm (a : Fin (Module.finrank ℂ B) → A) : e.symm a = ∑ i, a i ⊗ₜ[ℂ] ℬ i := by
    simp [e, Finsupp.sum_fintype]
  let Φ : (Fin (Module.finrank ℂ B) → A) →ₗ[ℂ]
      (Completion (R.H ⊗[ℂ] S.H) →L[ℂ] Completion (R.H ⊗[ℂ] S.H)) :=
    (R.spatial S : A ⊗[ℂ] B →ₗ[ℂ] _) ∘ₗ e.symm.toLinearMap
  have hΦ (a : Fin (Module.finrank ℂ B) → A) : ‖Φ a‖ ≤ (∑ i, ‖ℬ i‖) * ‖a‖ := by
    change ‖R.spatial S (e.symm a)‖ ≤ _
    rw [hsymm, map_sum, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_spatial_tmul, mul_comm]
    exact mul_le_mul (NonUnitalStarAlgHom.norm_apply_le S.π _)
      ((NonUnitalStarAlgHom.norm_apply_le R.π _).trans (norm_le_pi_norm a i)) (norm_nonneg _)
      (norm_nonneg _)
  let Φc := Φ.mkContinuous _ hΦ
  have hanti : AntilipschitzWith (∑ i, ‖C i‖₊) Φc := by
    refine ContinuousLinearMap.antilipschitz_of_bound Φc fun a => ?_
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    have hi : ‖a i‖ ≤ C i * ‖Φc a‖ := by
      have h := hC i (e.symm a)
      rwa [← he, LinearEquiv.apply_symm_apply] at h
    refine hi.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    calc C i ≤ ‖C i‖ := Real.le_norm_self _
      _ = ((‖C i‖₊ : NNReal) : ℝ) := rfl
      _ ≤ ((∑ j, ‖C j‖₊ : NNReal) : ℝ) :=
        NNReal.coe_le_coe.2
          (Finset.single_le_sum (f := fun j => ‖C j‖₊) (fun _ _ => zero_le) (Finset.mem_univ i))
  have hrange : Set.range (R.spatial S) = Set.range Φc :=
    (e.symm.surjective.range_comp (R.spatial S)).symm
  rw [hrange]
  exact hanti.isClosed_range Φc.uniformContinuous

omit [Fintype ι] in
/-- **The image of the algebraic tensor product under the tensor product of two representations is
closed when the second algebra is finite-dimensional.** The representations need not be faithful:
`π ⊗ ρ` factors through the tensor product of the inclusions of the C⋆-algebras `π(A)` and
`ρ(B)`. -/
theorem isClosed_range_spatial_of_finiteDimensional_right [FiniteDimensional ℂ B]
    (R : CStarRep A) (S : CStarRep B) : IsClosed (Set.range (R.spatial S)) := by
  have : IsClosed (NonUnitalStarAlgHom.range R.π : Set (R.H →L[ℂ] R.H)) :=
    NonUnitalStarAlgHom.isClosed_range R.π
  have : IsClosed (NonUnitalStarAlgHom.range S.π : Set (S.H →L[ℂ] S.H)) :=
    NonUnitalStarAlgHom.isClosed_range S.π
  let f : A →ₗ[ℂ] NonUnitalStarAlgHom.range R.π := (R.π.rangeRestrict : A →ₗ[ℂ] _)
  let g : B →ₗ[ℂ] NonUnitalStarAlgHom.range S.π := (S.π.rangeRestrict : B →ₗ[ℂ] _)
  have hf : Function.Surjective f := by rintro ⟨_, a, rfl⟩; exact ⟨a, rfl⟩
  have hg : Function.Surjective g := by rintro ⟨_, b, rfl⟩; exact ⟨b, rfl⟩
  have : FiniteDimensional ℂ (NonUnitalStarAlgHom.range S.π) := Module.Finite.of_surjective g hg
  have hrange : Set.range (R.spatial S) = Set.range (NonUnitalStarAlgHom.mapLCompletion
      (NonUnitalStarSubalgebraClass.subtype (NonUnitalStarAlgHom.range R.π))
      (NonUnitalStarSubalgebraClass.subtype (NonUnitalStarAlgHom.range S.π))) := by
    rw [← (TensorProduct.map_surjective hf hg).range_comp]
    exact congrArg Set.range (funext fun x =>
      NonUnitalStarAlgHom.mapLCompletion_eq_mapLCompletion_map (fun _ => rfl) (fun _ => rfl) x)
  rw [hrange]
  exact isClosed_range_spatial_of_injective
    (R := ⟨R.H, NonUnitalStarSubalgebraClass.subtype (NonUnitalStarAlgHom.range R.π)⟩)
    (S := ⟨S.H, NonUnitalStarSubalgebraClass.subtype (NonUnitalStarAlgHom.range S.π)⟩)
    Subtype.val_injective Subtype.val_injective

end Slice

/-! ### Independence of the representations -/

/-- A family of representations of `A` with no common kernel bounds the norm of `(π' ⊗ ρ)(x)` for
every representation `π'` of `A`: if `0 ≤ c` and `‖(πᵢ ⊗ ρ)(x)‖ ≤ c` for all `i`, then
`‖(π' ⊗ ρ)(x)‖ ≤ c`. The
matrix amplifications of the `πᵢ` have no common kernel either, so they determine the norm of
the matrices `sliceMatrix e x` (`NonUnitalStarAlgHom.norm_le_of_forall_norm_apply_le`). -/
lemma norm_spatial_le_of_forall_left {ι : Type*} {R : ι → CStarRep A}
    (hR : ∀ a : A, (∀ i, (R i).π a = 0) → a = 0) (R' : CStarRep A) (S : CStarRep B)
    {x : A ⊗[ℂ] B} {c : ℝ} (hc : 0 ≤ c) (h : ∀ i, ‖(R i).spatial S x‖ ≤ c) :
    ‖R'.spatial S x‖ ≤ c := by
  let := CStarAlgebra.spectralOrder A
  have := CStarAlgebra.spectralOrderedRing A
  refine ContinuousLinearMap.opNorm_le_of_forall_inner_sumTmulL _ hc fun n e he ξ ξ' => ?_
  have hsep (M : CStarMatrix (Fin n) (Fin n) A)
      (hM : ∀ i, CStarMatrix.mapₙₐ (n := Fin n) (R i).π M = 0) : M = 0 :=
    CStarMatrix.ext fun p q => hR _ fun i => congrFun (congrFun (hM i) p) q
  have hle : ‖CStarMatrix.toPiLpStarAlgEquiv (Fin n) R'.H
      (CStarMatrix.mapₙₐ R'.π (S.sliceMatrix e x))‖ ≤ c := by
    rw [norm_toPiLpStarAlgEquiv]
    calc ‖CStarMatrix.mapₙₐ R'.π (S.sliceMatrix e x)‖
        ≤ ‖S.sliceMatrix e x‖ := NonUnitalStarAlgHom.norm_apply_le _ _
      _ ≤ c := NonUnitalStarAlgHom.norm_le_of_forall_norm_apply_le
        (fun i => CStarMatrix.mapₙₐ (n := Fin n) (R i).π) hsep hc
        fun i => (norm_mapₙₐ_sliceMatrix_le (R i) S he x).trans (h i)
  rw [inner_sumTmulL_spatial_sumTmulL, mul_assoc, mul_left_comm]
  refine (norm_inner_le_norm _ _).trans ?_
  gcongr
  exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr)

/-- The norm of `(π ⊗ ρ)(x)` is largest when `π` is faithful: for a faithful representation `π` of
`A` and any representations `π'` of `A` and `ρ` of `B`, `‖(π' ⊗ ρ)(x)‖ ≤ ‖(π ⊗ ρ)(x)‖`. It is the
case of the family of `π` alone in `CStarRep.norm_spatial_le_of_forall_left`. -/
lemma norm_spatial_le_of_injective_left {R : CStarRep A} (hR : Function.Injective R.π)
    (R' : CStarRep A) (S : CStarRep B) (x : A ⊗[ℂ] B) :
    ‖R'.spatial S x‖ ≤ ‖R.spatial S x‖ :=
  norm_spatial_le_of_forall_left (R := fun _ : Unit => R)
    (fun _ h => hR ((h ()).trans (map_zero R.π).symm)) R' S (norm_nonneg _) fun _ => le_rfl

/-- Conjugation by an isometric equivalence of Hilbert spaces preserves the operator norm. -/
private lemma norm_conjStarAlgEquiv {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (e : H ≃ₗᵢ[ℂ] K) (x : H →L[ℂ] H) : ‖e.conjStarAlgEquiv x‖ = ‖x‖ := by
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg x) fun y => ?_)
    (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (e.conjStarAlgEquiv x)) fun y => ?_)
  · rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, e.norm_map]
    exact (x.le_opNorm _).trans_eq (by rw [e.symm.norm_map])
  · have h := (e.conjStarAlgEquiv x).le_opNorm (e y)
    rwa [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, e.symm_apply_apply, e.norm_map,
      e.norm_map] at h

/-- Swapping the factors carries the tensor product `π ⊗ ρ` of two representations onto `ρ ⊗ π`. -/
lemma conjStarAlgEquiv_completion_commIsometry_spatial (R : CStarRep A)
    (S : CStarRep B) (x : A ⊗[ℂ] B) :
    (TensorProduct.commIsometry ℂ R.H S.H).completion.conjStarAlgEquiv (R.spatial S x) =
      S.spatial R (TensorProduct.comm ℂ A B x) := by
  ext w
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    rw [← LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, spatial_tmul,
      ContinuousLinearMap.conjStarAlgEquiv_completion_commIsometry_mapL, comm_tmul, spatial_tmul]
  | add p q hp hq => simp only [map_add, add_apply, hp, hq]

/-- Swapping the factors does not change the norm: `‖(ρ ⊗ π)(x')‖ = ‖(π ⊗ ρ)(x)‖` for the flip
`x'` of `x`. -/
lemma norm_spatial_comm (R : CStarRep A) (S : CStarRep B) (x : A ⊗[ℂ] B) :
    ‖S.spatial R (TensorProduct.comm ℂ A B x)‖ = ‖R.spatial S x‖ := by
  rw [← conjStarAlgEquiv_completion_commIsometry_spatial, norm_conjStarAlgEquiv]

/-- **The image of the algebraic tensor product under the tensor product of two representations is
closed when the first algebra is finite-dimensional.** -/
theorem isClosed_range_spatial_of_finiteDimensional_left [FiniteDimensional ℂ A]
    (R : CStarRep A) (S : CStarRep B) : IsClosed (Set.range (R.spatial S)) := by
  have hcont : Continuous fun T : Completion (R.H ⊗[ℂ] S.H) →L[ℂ] Completion (R.H ⊗[ℂ] S.H) =>
      (TensorProduct.commIsometry ℂ R.H S.H).completion.conjStarAlgEquiv T := by
    simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply]
    fun_prop
  have hpre : Set.range (R.spatial S) =
      (fun T => (TensorProduct.commIsometry ℂ R.H S.H).completion.conjStarAlgEquiv T) ⁻¹'
        Set.range (S.spatial R) := by
    ext T
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨TensorProduct.comm ℂ A B x, (conjStarAlgEquiv_completion_commIsometry_spatial R S x).symm⟩
    · rintro ⟨y, hy⟩
      refine ⟨(TensorProduct.comm ℂ A B).symm y, ?_⟩
      refine EquivLike.injective (TensorProduct.commIsometry ℂ R.H S.H).completion.conjStarAlgEquiv ?_
      rw [conjStarAlgEquiv_completion_commIsometry_spatial, LinearEquiv.apply_symm_apply]
      exact hy
  rw [hpre]
  exact (isClosed_range_spatial_of_finiteDimensional_right S R).preimage hcont

/-- The norm of `(π ⊗ ρ)(x)` is largest when both representations are faithful: for faithful
representations `π` of `A` and `ρ` of `B` and any representations `π'` of `A` and `ρ'` of `B`,
`‖(π' ⊗ ρ')(x)‖ ≤ ‖(π ⊗ ρ)(x)‖`. -/
lemma norm_spatial_le_of_injective {R : CStarRep A} {S : CStarRep B}
    (hR : Function.Injective R.π) (hS : Function.Injective S.π) (R' : CStarRep A)
    (S' : CStarRep B) (x : A ⊗[ℂ] B) : ‖R'.spatial S' x‖ ≤ ‖R.spatial S x‖ :=
  calc ‖R'.spatial S' x‖ ≤ ‖R.spatial S' x‖ := norm_spatial_le_of_injective_left hR R' S' x
    _ = ‖S'.spatial R (TensorProduct.comm ℂ A B x)‖ := (norm_spatial_comm R S' x).symm
    _ ≤ ‖S.spatial R (TensorProduct.comm ℂ A B x)‖ := norm_spatial_le_of_injective_left hS S' R _
    _ = ‖R.spatial S x‖ := norm_spatial_comm R S x

/-- **The spatial norm does not depend on the faithful representations**: for faithful
representations `π`, `π'` of `A` and `ρ`, `ρ'` of `B`, `‖(π ⊗ ρ)(x)‖ = ‖(π' ⊗ ρ')(x)‖` for every
`x` in the algebraic tensor product `A ⊗[ℂ] B`. -/
theorem norm_spatial_eq_of_injective {R : CStarRep A} {S : CStarRep B}
    {R' : CStarRep A} {S' : CStarRep B} (hR : Function.Injective R.π)
    (hS : Function.Injective S.π) (hR' : Function.Injective R'.π) (hS' : Function.Injective S'.π)
    (x : A ⊗[ℂ] B) : ‖R.spatial S x‖ = ‖R'.spatial S' x‖ :=
  le_antisymm (norm_spatial_le_of_injective hR' hS' R S x) (norm_spatial_le_of_injective hR hS R' S' x)

/-- Families of representations with no common kernel bound the spatial norm: if the
representations `πᵢ` of `A` have no common kernel, and neither have the representations `ρⱼ` of `B`,
then a common bound `c ≥ 0` of the norms `‖(πᵢ ⊗ ρⱼ)(x)‖` bounds `‖(π' ⊗ ρ')(x)‖` for all
representations `π'` of `A` and `ρ'` of `B`. -/
lemma norm_spatial_le_of_forall {ι κ : Type*} {R : ι → CStarRep A}
    {S : κ → CStarRep B} (hR : ∀ a : A, (∀ i, (R i).π a = 0) → a = 0)
    (hS : ∀ b : B, (∀ j, (S j).π b = 0) → b = 0) (R' : CStarRep A)
    (S' : CStarRep B) {x : A ⊗[ℂ] B} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i j, ‖(R i).spatial (S j) x‖ ≤ c) : ‖R'.spatial S' x‖ ≤ c :=
  norm_spatial_le_of_forall_left hR R' S' hc fun i => by
    rw [← norm_spatial_comm]
    exact norm_spatial_le_of_forall_left hS S' (R i) hc fun j => by
      rw [norm_spatial_comm]
      exact h i j

end CStarRep
