/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Finite
public import QuantumSystem.Analysis.CStarAlgebra.TensorProduct.CStarNorm
public import QuantumSystem.ForMathlib.Algebra.Star.TensorProductMap
public import QuantumSystem.Analysis.CStarAlgebra.StarAlgEquiv
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.PiTensorProduct
public import QuantumSystem.ForMathlib.LinearAlgebra.PiTensorProduct.Star
public import QuantumSystem.ForMathlib.RingTheory.PiTensorProduct.NonUnital
import QuantumSystem.ForMathlib.Algebra.Central.Basic

/-!
# The minimal tensor product of a finite family of C⋆-algebras

For a finite family `A i` of C⋆-algebras, the minimal tensor product `⨂ₘᵢₙ i, A i` is the
norm closure of the image of the algebraic tensor product `⨂[ℂ] i, A i` under the tensor product of
the faithful representations `CStarRep.gelfandNaimark (A i)`, on the Hilbert space tensor product
`Completion (InnerPiTensorProduct ℂ H)` of their Hilbert spaces `H i`. The choice of the faithful
representations does not matter: the tensor product of any family of faithful representations of the
`A i` induces the same norm on `⨂[ℂ] i, A i` (`PiMinTensorProduct.norm_of_eq_norm_piSpatial`). For
two factors it is the minimal tensor product `A 0 ⊗ₘᵢₙ A 1`
(`PiMinTensorProduct.equivMinTensorProduct`). Splitting the index set along a predicate `p`, it is
`(⨂ₘᵢₙ i : {i // p i}, A i) ⊗ₘᵢₙ (⨂ₘᵢₙ i : {i // ¬p i}, A i)` (`PiMinTensorProduct.splitEquiv`), and
over a single index `i₀` it is `A i₀` (`PiMinTensorProduct.subsingletonEquiv`).

The algebras are not assumed unital: `⨂ₘᵢₙ i, A i` is a `NonUnitalCStarAlgebra`, and a
`CStarAlgebra` when every `A i` is unital. Its order is the spectral order.

## Main definitions

* `NonUnitalStarAlgHom.piMapLCompletion π` — for `⋆`-homomorphisms `π i : A i → B(H i)`, the
  `⋆`-homomorphism of `⨂[𝕜] i, A i` into the operators on `Completion (InnerPiTensorProduct 𝕜 H)`
  that sends `⨂ a` to the completion of `⨂ π i (a i)`.
* `CStarRep.piSpatial R` — the tensor product of a family of representations, on the algebraic
  tensor product.
* `PiMinTensorProduct A`, written `⨂ₘᵢₙ i, A i` — the minimal tensor product of a finite family of
  C⋆-algebras.
* `PiMinTensorProduct.of A` — the `⋆`-homomorphism `(⨂[ℂ] i, A i) →⋆ₙₐ[ℂ] ⨂ₘᵢₙ i, A i`.
* `PiMinTensorProduct.equivMinTensorProduct A` — for two factors,
  `(⨂ₘᵢₙ i, A i) ≃⋆ₐ[ℂ] A 0 ⊗ₘᵢₙ A 1`.
* `PiMinTensorProduct.splitEquiv A p` — splitting the index set along `p`,
  `(⨂ₘᵢₙ i, A i) ≃⋆ₐ[ℂ] (⨂ₘᵢₙ i : {i // p i}, A i) ⊗ₘᵢₙ (⨂ₘᵢₙ i : {i // ¬p i}, A i)`.
* `PiMinTensorProduct.subsingletonEquiv A i₀` — over a single index `i₀`,
  `(⨂ₘᵢₙ i, A i) ≃⋆ₐ[ℂ] A i₀`.
* `PiMinTensorProduct.reindex A e` — reindexing along `e : ι ≃ κ`,
  `(⨂ₘᵢₙ i, A i) ≃⋆ₐ[ℂ] ⨂ₘᵢₙ k, A (e.symm k)`.
* `PiTensorProduct.splitStarAlgEquiv R A p`, `PiTensorProduct.subsingletonStarAlgEquiv R A i₀`,
  `PiTensorProduct.reindexStarAlgEquiv R A e` — the same on the algebraic tensor products of
  `⋆`-algebras.
* `PiMinTensorProduct.subtype A` — the minimal tensor product as a C⋆-subalgebra of operators.
* `CStarRep.piTensorProduct R` — the tensor product of a family of representations `πᵢ` of the
  `A i`, faithful or not, as a representation of `⨂ₘᵢₙ i, A i`.
* `PiTensorProduct.mapStarAlgHom e` — the tensor product `⨂ eᵢ` of a family of unital
  `⋆`-homomorphisms, on the algebraic tensor products.
* `PiMinTensorProduct.map e` — the tensor product `⨂ eᵢ` of a family of unital `⋆`-homomorphisms of
  unital C⋆-algebras, on the minimal tensor products; `PiMinTensorProduct.congr e` — for
  `⋆`-isomorphisms, as a `⋆`-isomorphism.

## Main results

* `CStarRep.norm_piSpatial_le_of_injective` — `‖(⨂ πᵢ')(x)‖ ≤ ‖(⨂ πᵢ)(x)‖` for faithful `πᵢ` and
  any `πᵢ'`.
* `PiMinTensorProduct.norm_piSpatial_le_norm_of` — the norm of the minimal tensor product dominates
  the tensor product of any family of representations `πᵢ` of the `A i`: `‖(⨂ πᵢ)(x)‖ ≤ ‖x‖` for `x`
  in the algebraic tensor product.
* `PiMinTensorProduct.norm_of_eq_norm_piSpatial` — the norm of the minimal tensor product is computed
  in any family of faithful representations `πᵢ` of the `A i`: `‖x‖ = ‖(⨂ πᵢ)(x)‖` for `x` in the
  algebraic tensor product.
* `PiMinTensorProduct.denseRange_of` — the algebraic tensor product is dense.
* `PiMinTensorProduct.of_one` — for unital algebras, `PiMinTensorProduct.of` is unital.
* `PiMinTensorProduct.of_surjective_of_finiteDimensional`, `PiMinTensorProduct.finiteDimensional` —
  for finite-dimensional algebras, the algebraic tensor product is the whole minimal tensor product,
  which is finite-dimensional.
* `PiMinTensorProduct.norm_of_tprod_le` — `‖⨂ aᵢ‖ ≤ ∏ ‖aᵢ‖`.
* `PiMinTensorProduct.norm_of_mapStarAlgHom_le` — `⨂ eᵢ` is contractive for the minimal norms;
  `PiMinTensorProduct.map_map` — it is functorial.
* `PiMinTensorProduct.continuous_congr` — `e ↦ ⨂ eᵢ` is continuous for the point-norm topologies.
* `PiMinTensorProduct.isCentral` — the minimal tensor product of finitely many finite-dimensional
  factors is a factor.

## Notation

Activated by `open scoped PiMinTensorProduct`: `⨂ₘᵢₙ i, A i` — `PiMinTensorProduct A`, after
Mathlib's `⨂[R] i, A i` for the algebraic tensor product; `⨂ₘᵢₙ i : s, A i` for the subfamily over
`s`.
-/

@[expose] public section

open scoped TensorProduct InnerProductSpace MinTensorProduct

open UniformSpace

universe u w

/-! ### Operators on the completed tensor product -/

namespace InnerPiTensorProduct

variable {ι 𝕜 : Type*} [Fintype ι] [RCLike 𝕜] {E F : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace 𝕜 (E i)] [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace 𝕜 (F i)]

/-- The adjoint of `⨂ T` on the completed tensor product is `⨂ T†`. -/
lemma adjoint_completion_mapL [∀ i, CompleteSpace (E i)] [∀ i, CompleteSpace (F i)]
    (T : Π i, E i →L[𝕜] F i) :
    ContinuousLinearMap.adjoint (mapL T).completion =
      (mapL fun i => ContinuousLinearMap.adjoint (T i)).completion :=
  (ContinuousLinearMap.completion_eq_adjoint_completion (inner_mapL_adjoint T)).symm

/-- For two factors, the identification `⨂ ξ ↦ ξ 0 ⊗ ξ 1` of the completed Hilbert spaces
intertwines `⨂ T` with `T 0 ⊗ T 1`. -/
lemma completion_linearIsometryEquivTensorProduct_mapL
    {H₂ : Fin 2 → Type*} [∀ i, NormedAddCommGroup (H₂ i)] [∀ i, InnerProductSpace 𝕜 (H₂ i)]
    (T : Π i, H₂ i →L[𝕜] H₂ i) (w : Completion (InnerPiTensorProduct 𝕜 H₂)) :
    (linearIsometryEquivTensorProduct 𝕜 H₂).completion ((mapL T).completion w) =
      (TensorProduct.mapL (T 0) (T 1)).completion
        ((linearIsometryEquivTensorProduct 𝕜 H₂).completion w) := by
  induction w using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih v =>
    rw [ContinuousLinearMap.completion_apply_coe, LinearIsometryEquiv.completion_apply_coe,
      LinearIsometryEquiv.completion_apply_coe, ContinuousLinearMap.completion_apply_coe,
      linearIsometryEquivTensorProduct_mapL]

end InnerPiTensorProduct

namespace NonUnitalStarAlgHom

variable {ι 𝕜 : Type*} [Fintype ι] [RCLike 𝕜] {A : ι → Type*} [∀ i, NonUnitalSemiring (A i)]
  [∀ i, StarRing (A i)] [∀ i, Module 𝕜 (A i)] [∀ i, IsScalarTower 𝕜 (A i) (A i)]
  [∀ i, SMulCommClass 𝕜 (A i) (A i)] [∀ i, StarModule 𝕜 (A i)] {H : ι → Type*}
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace 𝕜 (H i)] [∀ i, CompleteSpace (H i)]

omit [∀ i, IsScalarTower 𝕜 (A i) (A i)] [∀ i, SMulCommClass 𝕜 (A i) (A i)] [∀ i, StarModule 𝕜 (A i)] in
/-- The tensor product `⨂ a ↦ ⨂ π i (a i)` of a family of `⋆`-homomorphisms into operator
algebras, as a linear map into the operators on the algebraic tensor product
`InnerPiTensorProduct 𝕜 H`; its completion is `NonUnitalStarAlgHom.piMapLCompletion π`. -/
noncomputable def piMapL (π : Π i, A i →⋆ₙₐ[𝕜] (H i →L[𝕜] H i)) :
    (⨂[𝕜] i, A i) →ₗ[𝕜] (InnerPiTensorProduct 𝕜 H →L[𝕜] InnerPiTensorProduct 𝕜 H) :=
  PiTensorProduct.lift <|
    (InnerPiTensorProduct.mapLMultilinear 𝕜 H H).compLinearMap fun i => (π i : A i →ₗ[𝕜] (H i →L[𝕜] H i))

omit [∀ i, IsScalarTower 𝕜 (A i) (A i)] [∀ i, SMulCommClass 𝕜 (A i) (A i)] [∀ i, StarModule 𝕜 (A i)] in
/-- `piMapL π` sends `⨂ a` to `⨂ π i (a i)`. -/
@[simp] lemma piMapL_tprod (π : Π i, A i →⋆ₙₐ[𝕜] (H i →L[𝕜] H i)) (a : Π i, A i) :
    piMapL π (⨂ₜ[𝕜] i, a i) = InnerPiTensorProduct.mapL fun i => π i (a i) := by
  simp [piMapL]

omit [∀ i, StarModule 𝕜 (A i)] in
/-- `piMapL π` is multiplicative. -/
lemma piMapL_mul (π : Π i, A i →⋆ₙₐ[𝕜] (H i →L[𝕜] H i)) (x y : ⨂[𝕜] i, A i) :
    piMapL π (x * y) = piMapL π x * piMapL π y := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r' b =>
      rw [PiTensorProduct.smul_tprod_mul_smul_tprod, map_smul, map_smul, map_smul,
        smul_mul_smul_comm, piMapL_tprod, piMapL_tprod, piMapL_tprod,
        ← InnerPiTensorProduct.mapL_mul]
      simp only [Pi.mul_apply, map_mul]
    | add y y' hy hy' => rw [mul_add, map_add, hy, hy', map_add, mul_add]
  | add x x' hx hx' => rw [add_mul, map_add, hx, hx', map_add, add_mul]

/-- The **tensor product of a family of `⋆`-homomorphisms into operator algebras**
`π i : A i → B(H i)`, on the algebraic tensor product: the `⋆`-homomorphism of `⨂[𝕜] i, A i` into
the operators on the Hilbert space tensor product `Completion (InnerPiTensorProduct 𝕜 H)` that sends
`⨂ a` to the completion of `⨂ π i (a i)`. -/
noncomputable def piMapLCompletion (π : Π i, A i →⋆ₙₐ[𝕜] (H i →L[𝕜] H i)) :
    (⨂[𝕜] i, A i) →⋆ₙₐ[𝕜]
      (Completion (InnerPiTensorProduct 𝕜 H) →L[𝕜] Completion (InnerPiTensorProduct 𝕜 H)) where
  toFun x := (piMapL π x).completion
  map_smul' c x := by rw [map_smul, ContinuousLinearMap.completion_smul]; rfl
  map_zero' := by rw [map_zero, ContinuousLinearMap.completion_zero]
  map_add' x y := by rw [map_add, ContinuousLinearMap.completion_add]
  map_mul' x y := by rw [piMapL_mul, ContinuousLinearMap.completion_mul]
  map_star' x := by
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r a =>
      rw [star_smul, PiTensorProduct.star_tprod, map_smul, map_smul,
        ContinuousLinearMap.completion_smul, ContinuousLinearMap.completion_smul, star_smul,
        piMapL_tprod, piMapL_tprod, ContinuousLinearMap.star_eq_adjoint,
        InnerPiTensorProduct.adjoint_completion_mapL]
      simp only [map_star, ContinuousLinearMap.star_eq_adjoint]
    | add x x' hx hx' =>
      rw [star_add, map_add, ContinuousLinearMap.completion_add, hx, hx', map_add,
        ContinuousLinearMap.completion_add, star_add]

/-- `piMapLCompletion π` is the completion of `piMapL π`. -/
lemma piMapLCompletion_apply (π : Π i, A i →⋆ₙₐ[𝕜] (H i →L[𝕜] H i)) (x : ⨂[𝕜] i, A i) :
    piMapLCompletion π x = (piMapL π x).completion :=
  rfl

/-- `piMapLCompletion π` sends `⨂ a` to the completion of `⨂ π i (a i)`. -/
@[simp] lemma piMapLCompletion_tprod (π : Π i, A i →⋆ₙₐ[𝕜] (H i →L[𝕜] H i)) (a : Π i, A i) :
    piMapLCompletion π (⨂ₜ[𝕜] i, a i) =
      (InnerPiTensorProduct.mapL fun i => π i (a i)).completion := by
  rw [piMapLCompletion_apply, piMapL_tprod]

end NonUnitalStarAlgHom

/-! ### The tensor product of a family of representations -/

namespace CStarRep

variable {ι : Type*} [Fintype ι] {A : ι → Type*} [∀ i, NonUnitalCStarAlgebra (A i)]

/-- The tensor product `⨂ πᵢ` of a family of representations `πᵢ` of `A i` on `Hᵢ`, **on the
algebraic tensor product**: the `⋆`-homomorphism of `⨂[ℂ] i, A i` into the operators on the Hilbert
space tensor product `Completion (InnerPiTensorProduct ℂ H)` that sends `⨂ a` to `⨂ πᵢ(aᵢ)`. -/
noncomputable def piSpatial (R : Π i, CStarRep (A i)) :
    (⨂[ℂ] i, A i) →⋆ₙₐ[ℂ] (Completion (InnerPiTensorProduct ℂ fun i => (R i).H) →L[ℂ]
      Completion (InnerPiTensorProduct ℂ fun i => (R i).H)) :=
  NonUnitalStarAlgHom.piMapLCompletion fun i => (R i).π

/-- `CStarRep.piSpatial R` sends `⨂ a` to the operator `⨂ πᵢ(aᵢ)`. -/
@[simp] lemma piSpatial_tprod (R : Π i, CStarRep (A i)) (a : Π i, A i) :
    piSpatial R (⨂ₜ[ℂ] i, a i) =
      (InnerPiTensorProduct.mapL fun i => (R i).π (a i)).completion :=
  NonUnitalStarAlgHom.piMapLCompletion_tprod _ a

/-- The tensor product of unital representations of unital C⋆-algebras is unital. -/
lemma piSpatial_one {A : ι → Type*} [∀ i, CStarAlgebra (A i)] (R : Π i, CStarRep (A i))
    (hR : ∀ i, (R i).π 1 = 1) : piSpatial R 1 = 1 := by
  rw [PiTensorProduct.one_def, piSpatial_tprod]
  simp only [Pi.one_apply, hR, InnerPiTensorProduct.mapL_one, ContinuousLinearMap.completion_one]

end CStarRep

/-! ### The minimal tensor product -/

section Defs

variable {ι : Type*} [Fintype ι] (A : ι → Type u) [∀ i, NonUnitalCStarAlgebra (A i)]

/-- The **minimal tensor product** of a finite family of C⋆-algebras: the norm closure of the image
of the algebraic tensor product `⨂[ℂ] i, A i` under the tensor product of the faithful
representations `CStarRep.gelfandNaimark (A i)`. Any family of faithful representations induces the
same norm (`PiMinTensorProduct.norm_of_eq_norm_piSpatial`). -/
def PiMinTensorProduct : Type _ :=
  (CStarRep.piSpatial fun i => CStarRep.gelfandNaimark (A i)).closureRange

end Defs

/-- `⨂ₘᵢₙ i, A i` is the minimal tensor product `PiMinTensorProduct A` of the family `A`. -/
scoped[PiMinTensorProduct] notation3:100 "⨂ₘᵢₙ "(...)", "r:(scoped f => PiMinTensorProduct f) => r

open scoped PiMinTensorProduct

namespace PiMinTensorProduct

variable {ι : Type*} [Fintype ι] {A : ι → Type u}

section NonUnital

variable [∀ i, NonUnitalCStarAlgebra (A i)]

/-- The minimal tensor product is a C⋆-algebra, as a norm closed `⋆`-subalgebra of the operators on
a Hilbert space. -/
noncomputable instance instNonUnitalCStarAlgebra : NonUnitalCStarAlgebra (⨂ₘᵢₙ i, A i) :=
  inferInstanceAs (NonUnitalCStarAlgebra
    (CStarRep.piSpatial fun i => CStarRep.gelfandNaimark (A i)).closureRange)

/-- The order of the minimal tensor product is its spectral order. -/
noncomputable instance instPartialOrder : PartialOrder (⨂ₘᵢₙ i, A i) :=
  CStarAlgebra.spectralOrder (⨂ₘᵢₙ i, A i)

/-- The minimal tensor product is a star-ordered ring for its spectral order. -/
instance instStarOrderedRing : StarOrderedRing (⨂ₘᵢₙ i, A i) :=
  CStarAlgebra.spectralOrderedRing (⨂ₘᵢₙ i, A i)

variable (A) in
/-- The canonical `⋆`-homomorphism of the algebraic tensor product into the minimal tensor
product, with dense range (`PiMinTensorProduct.denseRange_of`). -/
noncomputable def of : (⨂[ℂ] i, A i) →⋆ₙₐ[ℂ] (⨂ₘᵢₙ i, A i) :=
  (CStarRep.piSpatial fun i => CStarRep.gelfandNaimark (A i)).closureRangeRestrict

/-- The norm of the minimal tensor product on the algebraic tensor product is the norm of the tensor
product of the representations `CStarRep.gelfandNaimark (A i)`. For the same statement with any
family of faithful representations, see `PiMinTensorProduct.norm_of_eq_norm_piSpatial`. -/
lemma norm_of (x : ⨂[ℂ] i, A i) :
    ‖of A x‖ = ‖CStarRep.piSpatial (fun i => CStarRep.gelfandNaimark (A i)) x‖ :=
  rfl

/-- The algebraic tensor product is dense in the minimal tensor product. -/
lemma denseRange_of : DenseRange (of A) :=
  NonUnitalStarAlgHom.denseRange_closureRangeRestrict _

/-- For finite-dimensional algebras, the algebraic tensor product is the whole minimal tensor
product: its image is a finite-dimensional, hence closed, subspace. -/
lemma of_surjective_of_finiteDimensional [∀ i, FiniteDimensional ℂ (A i)] :
    Function.Surjective (of A) :=
  NonUnitalStarAlgHom.closureRangeRestrict_surjective_of_isClosed <| by
    have h := (LinearMap.range (LinearMap.ofClass
      (CStarRep.piSpatial fun i => CStarRep.gelfandNaimark (A i)))).closed_of_finiteDimensional
    rwa [LinearMap.coe_range] at h

/-- The minimal tensor product of finite-dimensional C⋆-algebras is finite-dimensional. -/
instance finiteDimensional [∀ i, FiniteDimensional ℂ (A i)] :
    FiniteDimensional ℂ (⨂ₘᵢₙ i, A i) :=
  Module.Finite.of_surjective (of A : (⨂[ℂ] i, A i) →ₗ[ℂ] (⨂ₘᵢₙ i, A i))
    of_surjective_of_finiteDimensional

end NonUnital

section Unital

variable [∀ i, CStarAlgebra (A i)]

/-- For unital algebras, the identity operator is the image of `1`, so it lies in the minimal tensor
product. -/
lemma one_mem_closureRange : (1 : Completion (InnerPiTensorProduct ℂ
    fun i => (CStarRep.gelfandNaimark (A i)).H) →L[ℂ] _) ∈
      (CStarRep.piSpatial fun i => CStarRep.gelfandNaimark (A i)).closureRange :=
  NonUnitalStarSubalgebra.le_topologicalClosure _
    ⟨1, CStarRep.piSpatial_one _ fun i => CStarRep.gelfandNaimark_π_one (A i)⟩

/-- The minimal tensor product of unital C⋆-algebras is a unital C⋆-algebra, with unit the identity
operator. Its non-unital structure is `PiMinTensorProduct.instNonUnitalCStarAlgebra`. -/
noncomputable instance instCStarAlgebra : CStarAlgebra (⨂ₘᵢₙ i, A i) :=
  letI nu : NonUnitalCStarAlgebra (⨂ₘᵢₙ i, A i) := instNonUnitalCStarAlgebra
  letI ring : NormedRing (⨂ₘᵢₙ i, A i) :=
    { nu.toNonUnitalNormedRing with
      one := ⟨1, one_mem_closureRange⟩
      one_mul := fun _ => Subtype.ext (one_mul _)
      mul_one := fun _ => Subtype.ext (mul_one _) }
  letI alg : NormedAlgebra ℂ (⨂ₘᵢₙ i, A i) :=
    { Algebra.ofModule (fun c T T' => smul_mul_assoc c T T')
        (fun c T T' => mul_smul_comm c T T') with
      norm_smul_le := norm_smul_le }
  { ring, alg, nu with }

/-- For unital algebras, `PiMinTensorProduct.of` is unital. -/
@[simp] lemma of_one : of A 1 = 1 :=
  Subtype.ext <| CStarRep.piSpatial_one _ fun i => CStarRep.gelfandNaimark_π_one (A i)

end Unital

end PiMinTensorProduct

/-! ### Two factors -/

namespace PiTensorProduct

variable {R : Type*} [CommSemiring R] [StarRing R] {A₂ : Fin 2 → Type*}
  [∀ i, NonUnitalSemiring (A₂ i)] [∀ i, StarRing (A₂ i)] [∀ i, Module R (A₂ i)]
  [∀ i, SMulCommClass R (A₂ i) (A₂ i)] [∀ i, IsScalarTower R (A₂ i) (A₂ i)]
  [∀ i, StarModule R (A₂ i)]

variable (R A₂) in
/-- For two factors, the identification `⨂ a ↦ a 0 ⊗ a 1` of the tensor products of `⋆`-algebras,
as a `⋆`-algebra isomorphism. -/
noncomputable def tmulFinTwoStarAlgEquiv : (⨂[R] i, A₂ i) ≃⋆ₐ[R] A₂ 0 ⊗[R] A₂ 1 :=
  { tmulFinTwoEquiv R A₂ with
    map_mul' x y := by
      change tmulFinTwoEquiv R A₂ (x * y) = tmulFinTwoEquiv R A₂ x * tmulFinTwoEquiv R A₂ y
      induction x using PiTensorProduct.induction_on with
      | smul_tprod r a =>
        induction y using PiTensorProduct.induction_on with
        | smul_tprod r' b =>
          rw [smul_tprod_mul_smul_tprod, map_smul, map_smul, map_smul, tmulFinTwoEquiv_tprod,
            tmulFinTwoEquiv_tprod, tmulFinTwoEquiv_tprod, smul_mul_smul_comm,
            Algebra.TensorProduct.tmul_mul_tmul]
          rfl
        | add y y' hy hy' => rw [mul_add, map_add, hy, hy', map_add, mul_add]
      | add x x' hx hx' => rw [add_mul, map_add, hx, hx', map_add, add_mul]
    map_star' x := by
      change tmulFinTwoEquiv R A₂ (star x) = star (tmulFinTwoEquiv R A₂ x)
      induction x using PiTensorProduct.induction_on with
      | smul_tprod r a =>
        rw [star_smul, star_tprod, map_smul, map_smul, tmulFinTwoEquiv_tprod,
          tmulFinTwoEquiv_tprod, star_smul, TensorProduct.star_tmul]
      | add x x' hx hx' => rw [star_add, map_add, hx, hx', map_add, star_add] }

/-- `PiTensorProduct.tmulFinTwoStarAlgEquiv R A` sends `⨂ a` to `a 0 ⊗ a 1`. -/
@[simp] lemma tmulFinTwoStarAlgEquiv_tprod (a : Π i, A₂ i) :
    tmulFinTwoStarAlgEquiv R A₂ (tprod R a) = a 0 ⊗ₜ a 1 :=
  tmulFinTwoEquiv_tprod a

end PiTensorProduct

namespace PiMinTensorProduct

variable {A₂ : Fin 2 → Type u} [∀ i, NonUnitalCStarAlgebra (A₂ i)]

/-- For two factors, the norm of the tensor product of the representations
`CStarRep.gelfandNaimark (A i)` is that of the binary one, through `⨂ a ↦ a 0 ⊗ a 1`: the two are
intertwined by the identification `⨂ ξ ↦ ξ 0 ⊗ ξ 1` of the Hilbert spaces. -/
lemma norm_piSpatial_eq_norm_spatial (x : ⨂[ℂ] i, A₂ i) :
    ‖CStarRep.piSpatial (fun i => CStarRep.gelfandNaimark (A₂ i)) x‖ =
      ‖π₀[A₂ 0, A₂ 1] (PiTensorProduct.tmulFinTwoStarAlgEquiv ℂ A₂ x)‖ := by
  refine (InnerPiTensorProduct.linearIsometryEquivTensorProduct ℂ
    fun i => (CStarRep.gelfandNaimark (A₂ i)).H).completion.opNorm_eq_of_intertwine fun w => ?_
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    simp only [map_smul, FunLike.coe_smul, Pi.smul_apply,
      PiTensorProduct.tmulFinTwoStarAlgEquiv_tprod, CStarRep.piSpatial_tprod,
      CStarRep.spatial_tmul,
      InnerPiTensorProduct.completion_linearIsometryEquivTensorProduct_mapL]
  | add x y hx hy =>
    simp only [map_add, add_apply, hx, hy]

variable (A₂) in
/-- **For two factors, the minimal tensor product is `A 0 ⊗ₘᵢₙ A 1`**, by the isomorphism that is
`⨂ a ↦ a 0 ⊗ a 1` on the algebraic tensor product. -/
noncomputable def equivMinTensorProduct : (⨂ₘᵢₙ i, A₂ i) ≃⋆ₐ[ℂ] A₂ 0 ⊗ₘᵢₙ A₂ 1 :=
  (NonUnitalStarAlgHom.closureRangeEquiv
    (φ := CStarRep.piSpatial fun i => CStarRep.gelfandNaimark (A₂ i))
    (ψ := π₀[A₂ 0, A₂ 1].comp
      (PiTensorProduct.tmulFinTwoStarAlgEquiv ℂ A₂).toNonUnitalStarAlgHom)
    norm_piSpatial_eq_norm_spatial).trans
    (NonUnitalStarSubalgebra.equivOfEq _ _ (NonUnitalStarAlgHom.closureRange_comp_of_surjective _
      (PiTensorProduct.tmulFinTwoStarAlgEquiv ℂ A₂).surjective))

/-- `PiMinTensorProduct.equivMinTensorProduct A` is `⨂ a ↦ a 0 ⊗ a 1` on the algebraic tensor
product. -/
lemma equivMinTensorProduct_of (x : ⨂[ℂ] i, A₂ i) :
    equivMinTensorProduct A₂ (of A₂ x) =
      MinTensorProduct.of (A₂ 0) (A₂ 1) (PiTensorProduct.tmulFinTwoStarAlgEquiv ℂ A₂ x) :=
  Subtype.ext <| by
    have h := NonUnitalStarAlgHom.closureRangeEquiv_closureRangeRestrict
      (φ := CStarRep.piSpatial fun i => CStarRep.gelfandNaimark (A₂ i))
      (ψ := π₀[A₂ 0, A₂ 1].comp (PiTensorProduct.tmulFinTwoStarAlgEquiv ℂ A₂).toNonUnitalStarAlgHom)
      norm_piSpatial_eq_norm_spatial x
    exact (congrArg Subtype.val h :)

end PiMinTensorProduct

/-! ### Splitting the index set and a single factor -/

namespace PiTensorProduct

variable {ι R : Type*} [CommSemiring R] [StarRing R] {A : ι → Type*}
  [∀ i, NonUnitalSemiring (A i)] [∀ i, StarRing (A i)] [∀ i, Module R (A i)]
  [∀ i, SMulCommClass R (A i) (A i)] [∀ i, IsScalarTower R (A i) (A i)] [∀ i, StarModule R (A i)]

variable (R A) (p : ι → Prop) [DecidablePred p] in
/-- Splitting the index set along `p`, `⨂ a ↦ (⨂ a|ₚ) ⊗ (⨂ a|¬ₚ)`, as a `⋆`-algebra isomorphism. -/
noncomputable def splitStarAlgEquiv :
    (⨂[R] i, A i) ≃⋆ₐ[R] (⨂[R] i : {i // p i}, A i) ⊗[R] (⨂[R] i : {i // ¬p i}, A i) :=
  { splitEquiv R A p with
    map_mul' x y := by
      change splitEquiv R A p (x * y) = splitEquiv R A p x * splitEquiv R A p y
      induction x using PiTensorProduct.induction_on with
      | smul_tprod r a =>
        induction y using PiTensorProduct.induction_on with
        | smul_tprod r' b =>
          rw [smul_tprod_mul_smul_tprod, map_smul, map_smul, map_smul, splitEquiv_tprod,
            splitEquiv_tprod, splitEquiv_tprod, smul_mul_smul_comm,
            Algebra.TensorProduct.tmul_mul_tmul, tprod_mul_tprod, tprod_mul_tprod]
          rfl
        | add y y' hy hy' => rw [mul_add, map_add, hy, hy', map_add, mul_add]
      | add x x' hx hx' => rw [add_mul, map_add, hx, hx', map_add, add_mul]
    map_star' x := by
      change splitEquiv R A p (star x) = star (splitEquiv R A p x)
      induction x using PiTensorProduct.induction_on with
      | smul_tprod r a =>
        rw [star_smul, star_tprod, map_smul, map_smul, splitEquiv_tprod, splitEquiv_tprod,
          star_smul, TensorProduct.star_tmul, star_tprod, star_tprod]
      | add x x' hx hx' => rw [star_add, map_add, hx, hx', map_add, star_add] }

/-- `PiTensorProduct.splitStarAlgEquiv R A p` sends `⨂ a` to `(⨂ a|ₚ) ⊗ (⨂ a|¬ₚ)`. -/
@[simp] lemma splitStarAlgEquiv_tprod (p : ι → Prop) [DecidablePred p] (a : Π i, A i) :
    splitStarAlgEquiv R A p (tprod R a) =
      tprod R (fun i : {i // p i} => a i) ⊗ₜ tprod R (fun i : {i // ¬p i} => a i) :=
  splitEquiv_tprod p a

/-- `PiTensorProduct.splitStarAlgEquiv R A p` is `PiTensorProduct.splitEquiv R A p`. -/
lemma splitStarAlgEquiv_apply (p : ι → Prop) [DecidablePred p] (x : ⨂[R] i, A i) :
    splitStarAlgEquiv R A p x = splitEquiv R A p x :=
  rfl

section Reindex

variable {κ : Type*}

variable (R A) in
/-- **Reindexing** along `e : ι ≃ κ`, `⨂ a ↦ ⨂ (a ∘ e.symm)`, as a `⋆`-algebra isomorphism. -/
noncomputable def reindexStarAlgEquiv (e : ι ≃ κ) :
    (⨂[R] i, A i) ≃⋆ₐ[R] (⨂[R] k, A (e.symm k)) :=
  { reindex R A e with
    map_mul' x y := by
      change reindex R A e (x * y) = reindex R A e x * reindex R A e y
      induction x using PiTensorProduct.induction_on with
      | smul_tprod r a =>
        induction y using PiTensorProduct.induction_on with
        | smul_tprod r' b =>
          rw [smul_tprod_mul_smul_tprod, map_smul, map_smul, map_smul, reindex_tprod,
            reindex_tprod, reindex_tprod, smul_mul_smul_comm, tprod_mul_tprod]
          rfl
        | add y y' hy hy' => rw [mul_add, map_add, hy, hy', map_add, mul_add]
      | add x x' hx hx' => rw [add_mul, map_add, hx, hx', map_add, add_mul]
    map_star' x := by
      change reindex R A e (star x) = star (reindex R A e x)
      induction x using PiTensorProduct.induction_on with
      | smul_tprod r a =>
        rw [star_smul, star_tprod, map_smul, map_smul, reindex_tprod, reindex_tprod,
          star_smul, star_tprod]
      | add x x' hx hx' => rw [star_add, map_add, hx, hx', map_add, star_add] }

/-- `PiTensorProduct.reindexStarAlgEquiv R A e` sends `⨂ a` to `⨂ (a ∘ e.symm)`. -/
@[simp] lemma reindexStarAlgEquiv_tprod (e : ι ≃ κ) (a : Π i, A i) :
    reindexStarAlgEquiv R A e (tprod R a) = tprod R fun k => a (e.symm k) :=
  reindex_tprod e a

end Reindex

variable [Subsingleton ι] (i₀ : ι)

variable (R A) in
/-- Over a single index `i₀`, the identification `⨂ a ↦ a i₀` as a `⋆`-algebra isomorphism. -/
noncomputable def subsingletonStarAlgEquiv : (⨂[R] i, A i) ≃⋆ₐ[R] A i₀ :=
  { subsingletonEquiv (R := R) (s := A) i₀ with
    map_mul' x y := by
      change subsingletonEquiv i₀ (x * y) = subsingletonEquiv i₀ x * subsingletonEquiv i₀ y
      induction x using PiTensorProduct.induction_on with
      | smul_tprod r a =>
        induction y using PiTensorProduct.induction_on with
        | smul_tprod r' b =>
          rw [smul_tprod_mul_smul_tprod, map_smul, map_smul, map_smul,
            subsingletonEquiv_apply_tprod, subsingletonEquiv_apply_tprod,
            subsingletonEquiv_apply_tprod, smul_mul_smul_comm]
          rfl
        | add y y' hy hy' => rw [mul_add, map_add, hy, hy', map_add, mul_add]
      | add x x' hx hx' => rw [add_mul, map_add, hx, hx', map_add, add_mul]
    map_star' x := by
      change subsingletonEquiv i₀ (star x) = star (subsingletonEquiv i₀ x)
      induction x using PiTensorProduct.induction_on with
      | smul_tprod r a =>
        rw [star_smul, star_tprod, map_smul, map_smul, subsingletonEquiv_apply_tprod,
          subsingletonEquiv_apply_tprod, star_smul]
      | add x x' hx hx' => rw [star_add, map_add, hx, hx', map_add, star_add] }

/-- `PiTensorProduct.subsingletonStarAlgEquiv R A i₀` sends `⨂ a` to `a i₀`. -/
@[simp] lemma subsingletonStarAlgEquiv_tprod (a : Π i, A i) :
    subsingletonStarAlgEquiv R A i₀ (tprod R a) = a i₀ :=
  subsingletonEquiv_apply_tprod i₀ a


end PiTensorProduct

namespace CStarRep

variable {ι : Type*} [Fintype ι] {A : ι → Type*} [∀ i, NonUnitalCStarAlgebra (A i)]
  (R : Π i, CStarRep (A i))

/-- Over the empty index type, the norm of the tensor product of a family of representations is the
norm of the scalar, through `PiTensorProduct.isEmptyEquiv`. -/
lemma norm_piSpatial_eq_norm_isEmptyEquiv [IsEmpty ι] (x : ⨂[ℂ] i, A i) :
    ‖piSpatial R x‖ = ‖PiTensorProduct.isEmptyEquiv ι x‖ := by
  have : ∀ i, Nontrivial (R i).H := fun i => isEmptyElim i
  obtain ⟨c, rfl⟩ := (PiTensorProduct.isEmptyEquiv ι).symm.surjective x
  rw [LinearEquiv.apply_symm_apply, PiTensorProduct.isEmptyEquiv_symm_apply, map_smul,
    piSpatial_tprod]
  have h : (fun i => (R i).π ((isEmptyElim : Π i, A i) i)) = fun i => 1 :=
    funext fun i => isEmptyElim i
  rw [h, InnerPiTensorProduct.mapL_one, norm_smul, ContinuousLinearMap.norm_completion, norm_one,
    mul_one]

section Subsingleton

variable [Subsingleton ι] (i₀ : ι)

/-- Over a single index `i₀`, the identification `⨂ ξ ↦ ξ i₀` of the Hilbert spaces intertwines
`⨂ πᵢ(aᵢ)` with `πᵢ₀(aᵢ₀)`. -/
private lemma subsingletonLinearIsometryEquiv_piMapL (x : ⨂[ℂ] i, A i)
    (w : InnerPiTensorProduct ℂ fun i => (R i).H) :
    InnerPiTensorProduct.subsingletonLinearIsometryEquiv ℂ _ i₀
        (NonUnitalStarAlgHom.piMapL (fun i => (R i).π) x w) =
      (R i₀).π (PiTensorProduct.subsingletonStarAlgEquiv ℂ A i₀ x)
        (InnerPiTensorProduct.subsingletonLinearIsometryEquiv ℂ _ i₀ w) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    simp only [map_smul, smul_apply, NonUnitalStarAlgHom.piMapL_tprod,
      InnerPiTensorProduct.subsingletonLinearIsometryEquiv_mapL,
      PiTensorProduct.subsingletonStarAlgEquiv_tprod]
  | add x y hx hy => simp only [map_add, add_apply, hx, hy]

/-- Over a single index `i₀`, the norm of the tensor product of a family of representations is the
norm of `πᵢ₀` at the image under `⨂ a ↦ a i₀`: the two are intertwined by the identification
`⨂ ξ ↦ ξ i₀` of the Hilbert spaces. -/
lemma norm_piSpatial_eq_norm_π_subsingletonStarAlgEquiv (x : ⨂[ℂ] i, A i) :
    ‖piSpatial R x‖ = ‖(R i₀).π (PiTensorProduct.subsingletonStarAlgEquiv ℂ A i₀ x)‖ := by
  rw [← ContinuousLinearMap.norm_completion ((R i₀).π _)]
  refine (InnerPiTensorProduct.subsingletonLinearIsometryEquiv ℂ
    (fun i => (R i).H) i₀).completion.opNorm_eq_of_intertwine fun v => ?_
  induction v using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih w =>
    rw [piSpatial, NonUnitalStarAlgHom.piMapLCompletion_apply,
      ContinuousLinearMap.completion_apply_coe, LinearIsometryEquiv.completion_apply_coe,
      LinearIsometryEquiv.completion_apply_coe, ContinuousLinearMap.completion_apply_coe,
      subsingletonLinearIsometryEquiv_piMapL]

/-- Over a single index `i₀`, the norm of the tensor product of a family of representations is the
norm of `A i₀`, through `⨂ a ↦ a i₀`, when the representation `πᵢ₀` of `A i₀` is faithful. -/
lemma norm_piSpatial_eq_norm_subsingletonStarAlgEquiv (hR : Function.Injective (R i₀).π)
    (x : ⨂[ℂ] i, A i) :
    ‖piSpatial R x‖ = ‖PiTensorProduct.subsingletonStarAlgEquiv ℂ A i₀ x‖ := by
  rw [norm_piSpatial_eq_norm_π_subsingletonStarAlgEquiv R i₀, NonUnitalStarAlgHom.norm_map _ hR]

end Subsingleton

section Split

variable (p : ι → Prop) [DecidablePred p]

/-- The identification of the Hilbert space of `⨂ πᵢ` with the Hilbert space tensor product of those
of `⨂ πᵢ|ₚ` and `⨂ πᵢ|¬ₚ`. -/
private noncomputable def splitUnitary :
    Completion (InnerPiTensorProduct ℂ fun i => (R i).H) ≃ₗᵢ[ℂ]
      Completion (Completion (InnerPiTensorProduct ℂ fun i : {i // p i} => (R i).H) ⊗[ℂ]
        Completion (InnerPiTensorProduct ℂ fun i : {i // ¬p i} => (R i).H)) :=
  (InnerPiTensorProduct.splitLinearIsometryEquiv ℂ _ p).completion.trans
    ((TensorProduct.completionLeftEquiv ℂ _ _).trans (TensorProduct.completionRightEquiv ℂ _ _))

/-- `splitUnitary R p` intertwines `⨂ T` with `(⨂ T|ₚ) ⊗ (⨂ T|¬ₚ)`. -/
private lemma splitUnitary_mapL (T : Π i, (R i).H →L[ℂ] (R i).H)
    (v : Completion (InnerPiTensorProduct ℂ fun i => (R i).H)) :
    splitUnitary R p ((InnerPiTensorProduct.mapL T).completion v) =
      (TensorProduct.mapL (InnerPiTensorProduct.mapL fun i : {i // p i} => T i).completion
        (InnerPiTensorProduct.mapL fun i : {i // ¬p i} => T i).completion).completion
          (splitUnitary R p v) := by
  have h : (InnerPiTensorProduct.splitLinearIsometryEquiv ℂ _ p).completion
      ((InnerPiTensorProduct.mapL T).completion v) =
        (TensorProduct.mapL (InnerPiTensorProduct.mapL fun i : {i // p i} => T i)
          (InnerPiTensorProduct.mapL fun i : {i // ¬p i} => T i)).completion
          ((InnerPiTensorProduct.splitLinearIsometryEquiv ℂ _ p).completion v) := by
    induction v using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih w =>
      rw [ContinuousLinearMap.completion_apply_coe, LinearIsometryEquiv.completion_apply_coe,
        LinearIsometryEquiv.completion_apply_coe, ContinuousLinearMap.completion_apply_coe,
        InnerPiTensorProduct.splitLinearIsometryEquiv_mapL]
  simp only [splitUnitary, LinearIsometryEquiv.trans_apply]
  rw [h, TensorProduct.completionLeftEquiv_mapL, TensorProduct.completionRightEquiv_mapL]

/-- `splitUnitary R p` intertwines `⨂ πᵢ` with the tensor product of `⨂ πᵢ|ₚ` and `⨂ πᵢ|¬ₚ`,
through the splitting of the algebraic tensor product. -/
private lemma splitUnitary_piSpatial (x : ⨂[ℂ] i, A i)
    (v : Completion (InnerPiTensorProduct ℂ fun i => (R i).H)) :
    splitUnitary R p (piSpatial R x v) =
      NonUnitalStarAlgHom.mapLCompletion (piSpatial fun i : {i // p i} => R i)
        (piSpatial fun i : {i // ¬p i} => R i) (PiTensorProduct.splitStarAlgEquiv ℂ A p x)
        (splitUnitary R p v) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    simp only [map_smul, smul_apply, piSpatial_tprod, PiTensorProduct.splitStarAlgEquiv_tprod,
      NonUnitalStarAlgHom.mapLCompletion_tmul]
    exact congrArg (r • ·) (splitUnitary_mapL R p _ v)
  | add x y hx hy => simp only [map_add, add_apply, hx, hy]

/-- Splitting the index set along `p`, the norm of the tensor product `⨂ πᵢ` of a family of
representations is that of the tensor product of `⨂ πᵢ|ₚ` and `⨂ πᵢ|¬ₚ`, through
`⨂ a ↦ (⨂ a|ₚ) ⊗ (⨂ a|¬ₚ)`: the two are intertwined by the splitting of the Hilbert spaces. -/
lemma norm_piSpatial_eq_norm_mapLCompletion_splitStarAlgEquiv (x : ⨂[ℂ] i, A i) :
    ‖piSpatial R x‖ = ‖NonUnitalStarAlgHom.mapLCompletion (piSpatial fun i : {i // p i} => R i)
      (piSpatial fun i : {i // ¬p i} => R i) (PiTensorProduct.splitStarAlgEquiv ℂ A p x)‖ :=
  (splitUnitary R p).opNorm_eq_of_intertwine (splitUnitary_piSpatial R p x)

end Split

section Reindex

variable {κ : Type*} [Fintype κ]

/-- **Reindexing preserves the norm of the tensor product of representations**: along `e : ι ≃ κ`,
`⨂ πᵢ` and `⨂ π_{e.symm k}` are intertwined by the reindexing of the Hilbert spaces. -/
lemma norm_piSpatial_reindexStarAlgEquiv (e : ι ≃ κ) (x : ⨂[ℂ] i, A i) :
    ‖piSpatial (fun k => R (e.symm k)) (PiTensorProduct.reindexStarAlgEquiv ℂ A e x)‖ =
      ‖piSpatial R x‖ := by
  refine ((InnerPiTensorProduct.reindexLinearIsometryEquiv ℂ (fun i => (R i).H) e).completion
    |>.opNorm_eq_of_intertwine fun v => ?_).symm
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    simp only [map_smul, smul_apply, piSpatial_tprod, PiTensorProduct.reindexStarAlgEquiv_tprod]
    congr 1
    induction v using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih w =>
      rw [ContinuousLinearMap.completion_apply_coe, LinearIsometryEquiv.completion_apply_coe,
        LinearIsometryEquiv.completion_apply_coe, ContinuousLinearMap.completion_apply_coe,
        InnerPiTensorProduct.reindexLinearIsometryEquiv_mapL]
  | add x y hx hy => simp only [map_add, add_apply, hx, hy]

end Reindex

end CStarRep

/-! ### Comparison with a family of faithful representations -/

namespace CStarRep

variable {ι : Type*} [Fintype ι] {A : ι → Type*} [∀ i, NonUnitalCStarAlgebra (A i)]

/-- Splitting the index set along `p`, the tensor product `⨂ πᵢ'` of a family of representations is
dominated by that of a family `πᵢ` when the tensor products of the subfamilies over `p` and over
`¬p` are: `⨂ πᵢ'|ₚ` and `⨂ πᵢ'|¬ₚ` factor through the C⋆-algebras generated by `⨂ πᵢ|ₚ` and
`⨂ πᵢ|¬ₚ`, on which the inclusions are faithful representations. -/
private lemma norm_piSpatial_le_of_forall_split (p : ι → Prop) [DecidablePred p]
    {R R' : Π i, CStarRep (A i)}
    (hp : ∀ y, ‖piSpatial (fun i : {i // p i} => R' i) y‖ ≤ ‖piSpatial (fun i : {i // p i} => R i) y‖)
    (hq : ∀ z, ‖piSpatial (fun i : {i // ¬p i} => R' i) z‖ ≤
      ‖piSpatial (fun i : {i // ¬p i} => R i) z‖) (x : ⨂[ℂ] i, A i) :
    ‖piSpatial R' x‖ ≤ ‖piSpatial R x‖ := by
  let φ := piSpatial fun i : {i // p i} => R i
  let ψ := piSpatial fun i : {i // ¬p i} => R i
  let π' := (NonUnitalStarSubalgebraClass.subtype _).comp
    (NonUnitalStarAlgHom.closureRangeMap (φ := φ) hp)
  let ρ' := (NonUnitalStarSubalgebraClass.subtype _).comp
    (NonUnitalStarAlgHom.closureRangeMap (φ := ψ) hq)
  have h' := NonUnitalStarAlgHom.mapLCompletion_eq_mapLCompletion_map
    (π := piSpatial fun i : {i // p i} => R' i) (ρ := piSpatial fun i : {i // ¬p i} => R' i)
    (π' := π') (ρ' := ρ')
    (f := LinearMap.ofClass φ.closureRangeRestrict) (g := LinearMap.ofClass ψ.closureRangeRestrict)
    (fun y => (congrArg Subtype.val
      (NonUnitalStarAlgHom.closureRangeMap_closureRangeRestrict hp y)).symm)
    (fun z => (congrArg Subtype.val
      (NonUnitalStarAlgHom.closureRangeMap_closureRangeRestrict hq z)).symm)
    (PiTensorProduct.splitStarAlgEquiv ℂ A p x)
  have h := NonUnitalStarAlgHom.mapLCompletion_eq_mapLCompletion_map (π := φ) (ρ := ψ)
    (π' := NonUnitalStarSubalgebraClass.subtype φ.closureRange)
    (ρ' := NonUnitalStarSubalgebraClass.subtype ψ.closureRange)
    (f := LinearMap.ofClass φ.closureRangeRestrict) (g := LinearMap.ofClass ψ.closureRangeRestrict)
    (fun _ => rfl) (fun _ => rfl) (PiTensorProduct.splitStarAlgEquiv ℂ A p x)
  have hle := norm_spatial_le_of_injective
    (R := .mk _ (NonUnitalStarSubalgebraClass.subtype φ.closureRange))
    (S := .mk _ (NonUnitalStarSubalgebraClass.subtype ψ.closureRange))
    Subtype.val_injective Subtype.val_injective (.mk _ π') (.mk _ ρ')
    (TensorProduct.map (LinearMap.ofClass φ.closureRangeRestrict)
      (LinearMap.ofClass ψ.closureRangeRestrict) (PiTensorProduct.splitStarAlgEquiv ℂ A p x))
  exact ((norm_piSpatial_eq_norm_mapLCompletion_splitStarAlgEquiv R' p x).trans
    (congrArg norm h')).trans_le (hle.trans_eq
      ((norm_piSpatial_eq_norm_mapLCompletion_splitStarAlgEquiv R p x).trans (congrArg norm h)).symm)

/-- The norm of `(⨂ πᵢ)(x)` is largest when every `πᵢ` is faithful: for faithful representations
`πᵢ` of `A i` and any representations `πᵢ'` of `A i`, `‖(⨂ πᵢ')(x)‖ ≤ ‖(⨂ πᵢ)(x)‖` for every `x` in
the algebraic tensor product. For two factors this is `CStarRep.norm_spatial_le_of_injective`. -/
lemma norm_piSpatial_le_of_injective {R : Π i, CStarRep (A i)}
    (hR : ∀ i, Function.Injective (R i).π) (R' : Π i, CStarRep (A i)) (x : ⨂[ℂ] i, A i) :
    ‖piSpatial R' x‖ ≤ ‖piSpatial R x‖ := by
  induction hn : Fintype.card ι using Nat.strong_induction_on generalizing ι with
  | _ n ih =>
    subst hn
    cases isEmpty_or_nonempty ι with
    | inl hι =>
      rw [norm_piSpatial_eq_norm_isEmptyEquiv, norm_piSpatial_eq_norm_isEmptyEquiv]
    | inr hι =>
      -- For a general `p`: with `p := (· = i₀)`, another `Fintype {i // p i}` instance is synthesized.
      have key (p : ι → Prop) [DecidablePred p] [Subsingleton {i // p i}] (j : {i // p i}) :
          ‖piSpatial R' x‖ ≤ ‖piSpatial R x‖ := by
        refine norm_piSpatial_le_of_forall_split p (fun y => ?_) (fun z => ?_) x
        · rw [norm_piSpatial_eq_norm_π_subsingletonStarAlgEquiv _ j,
            norm_piSpatial_eq_norm_subsingletonStarAlgEquiv _ j (hR j)]
          exact NonUnitalStarAlgHom.norm_apply_le _ _
        · exact ih _ (Fintype.card_subtype_lt (x := j.1) (not_not.2 j.2))
            (R := fun i : {i // ¬p i} => R i) (fun i => hR i) _ z rfl
      classical
      obtain ⟨i₀⟩ := hι
      have : Subsingleton {i // i = i₀} := ⟨fun a b => Subtype.ext (a.2.trans b.2.symm)⟩
      exact key (· = i₀) ⟨i₀, rfl⟩

/-- The norm `‖(⨂ πᵢ)(x)‖` does not depend on the faithful representations `πᵢ`. For two factors
this is `CStarRep.norm_spatial_eq_of_injective`. -/
lemma norm_piSpatial_eq_of_injective {R R' : Π i, CStarRep (A i)}
    (hR : ∀ i, Function.Injective (R i).π) (hR' : ∀ i, Function.Injective (R' i).π)
    (x : ⨂[ℂ] i, A i) : ‖piSpatial R x‖ = ‖piSpatial R' x‖ :=
  le_antisymm (norm_piSpatial_le_of_injective hR' R x) (norm_piSpatial_le_of_injective hR R' x)

end CStarRep

namespace PiMinTensorProduct

variable {ι : Type*} [Fintype ι] {A : ι → Type u} [∀ i, NonUnitalCStarAlgebra (A i)]

variable (A) in
/-- The minimal tensor product as a C⋆-subalgebra of the operators on the Hilbert space tensor
product of the representations `CStarRep.gelfandNaimark (A i)`. -/
noncomputable def subtype : (⨂ₘᵢₙ i, A i) →⋆ₙₐ[ℂ]
    (Completion (InnerPiTensorProduct ℂ fun i => (CStarRep.gelfandNaimark (A i)).H) →L[ℂ]
      Completion (InnerPiTensorProduct ℂ fun i => (CStarRep.gelfandNaimark (A i)).H)) :=
  NonUnitalStarSubalgebraClass.subtype
    (CStarRep.piSpatial fun i => CStarRep.gelfandNaimark (A i)).closureRange

/-- `PiMinTensorProduct.subtype A` is injective. -/
lemma subtype_injective : Function.Injective (subtype A) :=
  Subtype.val_injective

/-- `PiMinTensorProduct.subtype A` is the tensor product of the representations on the algebraic
tensor product. -/
@[simp] lemma subtype_of (x : ⨂[ℂ] i, A i) :
    subtype A (of A x) = CStarRep.piSpatial (fun i => CStarRep.gelfandNaimark (A i)) x :=
  rfl

section Subsingleton

variable [Subsingleton ι] (i₀ : ι)

/-- Over a single index `i₀`, the norm of the minimal tensor product on the algebraic tensor product
is the norm of `A i₀`, through `⨂ a ↦ a i₀`. -/
lemma norm_of_eq_norm_subsingletonStarAlgEquiv (x : ⨂[ℂ] i, A i) :
    ‖of A x‖ = ‖PiTensorProduct.subsingletonStarAlgEquiv ℂ A i₀ x‖ :=
  CStarRep.norm_piSpatial_eq_norm_subsingletonStarAlgEquiv _ i₀
    (CStarRep.gelfandNaimark_injective _) x

variable (A) in
/-- **Over a single index `i₀`, the minimal tensor product is `A i₀`**, by the isomorphism that is
`⨂ a ↦ a i₀` on the algebraic tensor product. -/
noncomputable def subsingletonEquiv : (⨂ₘᵢₙ i, A i) ≃⋆ₐ[ℂ] A i₀ :=
  NonUnitalStarAlgHom.equivOfDenseRange (φ := of A)
    (ψ := (PiTensorProduct.subsingletonStarAlgEquiv ℂ A i₀).toNonUnitalStarAlgHom) denseRange_of
    (PiTensorProduct.subsingletonStarAlgEquiv ℂ A i₀).surjective.denseRange
    (norm_of_eq_norm_subsingletonStarAlgEquiv i₀)

/-- `PiMinTensorProduct.subsingletonEquiv A i₀` is `⨂ a ↦ a i₀` on the algebraic tensor product. -/
lemma subsingletonEquiv_of (x : ⨂[ℂ] i, A i) :
    subsingletonEquiv A i₀ (of A x) = PiTensorProduct.subsingletonStarAlgEquiv ℂ A i₀ x :=
  NonUnitalStarAlgHom.equivOfDenseRange_apply _ _ _ x

end Subsingleton

section Reindex

variable {κ : Type*} [Fintype κ]

variable (A) in
/-- **Reindexing the minimal tensor product** along `e : ι ≃ κ`: the isomorphism that is
`⨂ a ↦ ⨂ (a ∘ e.symm)` on the algebraic tensor product, isometric since reindexing preserves the
norm of the tensor product of representations (`CStarRep.norm_piSpatial_reindexStarAlgEquiv`). -/
noncomputable def reindex (e : ι ≃ κ) : (⨂ₘᵢₙ i, A i) ≃⋆ₐ[ℂ] (⨂ₘᵢₙ k, A (e.symm k)) :=
  NonUnitalStarAlgHom.equivOfDenseRange (φ := of A)
    (ψ := (of fun k => A (e.symm k)).comp
      (PiTensorProduct.reindexStarAlgEquiv ℂ A e).toNonUnitalStarAlgHom) denseRange_of
    (show Dense (Set.range
        ((of fun k => A (e.symm k)) ∘ PiTensorProduct.reindexStarAlgEquiv ℂ A e)) from
      (PiTensorProduct.reindexStarAlgEquiv ℂ A e).surjective.range_comp _ ▸ denseRange_of)
    fun x => (CStarRep.norm_piSpatial_reindexStarAlgEquiv _ e x).symm

/-- `PiMinTensorProduct.reindex A e` is `⨂ a ↦ ⨂ (a ∘ e.symm)` on the algebraic tensor product. -/
lemma reindex_of (e : ι ≃ κ) (x : ⨂[ℂ] i, A i) :
    reindex A e (of A x) = of _ (PiTensorProduct.reindexStarAlgEquiv ℂ A e x) :=
  NonUnitalStarAlgHom.equivOfDenseRange_apply _ _ _ x

end Reindex

section Split

variable (p : ι → Prop) [DecidablePred p]

/-- Splitting the index set along `p`, the norm of the minimal tensor product on the algebraic
tensor product is that of `(⨂ₘᵢₙ i : {i // p i}, A i) ⊗ₘᵢₙ (⨂ₘᵢₙ i : {i // ¬p i}, A i)`, through
`⨂ a ↦ (⨂ a|ₚ) ⊗ (⨂ a|¬ₚ)`: for the representations `πᵢ = CStarRep.gelfandNaimark (A i)`, the two
are computed in `⨂ πᵢ` and in `(⨂ πᵢ|ₚ) ⊗ (⨂ πᵢ|¬ₚ)`, intertwined by the splitting of the Hilbert
spaces. -/
lemma norm_of_eq_norm_splitStarAlgEquiv (x : ⨂[ℂ] i, A i) :
    ‖of A x‖ = ‖MinTensorProduct.of _ _ (TensorProduct.map
      (of (fun i : {i // p i} => A i) : (⨂[ℂ] i : {i // p i}, A i) →ₗ[ℂ]
        (⨂ₘᵢₙ i : {i // p i}, A i))
      (of (fun i : {i // ¬p i} => A i) : (⨂[ℂ] i : {i // ¬p i}, A i) →ₗ[ℂ]
        (⨂ₘᵢₙ i : {i // ¬p i}, A i))
      (PiTensorProduct.splitStarAlgEquiv ℂ A p x))‖ := by
  have h := NonUnitalStarAlgHom.mapLCompletion_eq_mapLCompletion_map
    (π' := subtype fun i : {i // p i} => A i) (ρ' := subtype fun i : {i // ¬p i} => A i)
    (f := LinearMap.ofClass (of fun i : {i // p i} => A i))
    (g := LinearMap.ofClass (of fun i : {i // ¬p i} => A i))
    (fun y => (subtype_of y).symm) (fun z => (subtype_of z).symm)
    (PiTensorProduct.splitStarAlgEquiv ℂ A p x)
  exact (CStarRep.norm_piSpatial_eq_norm_mapLCompletion_splitStarAlgEquiv _ p x).trans
    ((congrArg norm h).trans (MinTensorProduct.norm_of_eq_norm_spatial
      (R := .mk _ (subtype fun i : {i // p i} => A i))
      (S := .mk _ (subtype fun i : {i // ¬p i} => A i))
      subtype_injective subtype_injective _).symm)

/-- The algebraic tensor product is dense in
`(⨂ₘᵢₙ i : {i // p i}, A i) ⊗ₘᵢₙ (⨂ₘᵢₙ i : {i // ¬p i}, A i)`, through `⨂ a ↦ (⨂ a|ₚ) ⊗ (⨂ a|¬ₚ)`. -/
lemma denseRange_of_map_of_splitStarAlgEquiv : DenseRange fun x : ⨂[ℂ] i, A i =>
    MinTensorProduct.of _ _ (TensorProduct.map
      (of (fun i : {i // p i} => A i) : (⨂[ℂ] i : {i // p i}, A i) →ₗ[ℂ]
        (⨂ₘᵢₙ i : {i // p i}, A i))
      (of (fun i : {i // ¬p i} => A i) : (⨂[ℂ] i : {i // ¬p i}, A i) →ₗ[ℂ]
        (⨂ₘᵢₙ i : {i // ¬p i}, A i))
      (PiTensorProduct.splitStarAlgEquiv ℂ A p x)) := by
  have h := NonUnitalStarAlgHom.denseRange_comp_map (MinTensorProduct.of _ _)
    MinTensorProduct.denseRange_of
    (f := (of (fun i : {i // p i} => A i) : (⨂[ℂ] i : {i // p i}, A i) →ₗ[ℂ]
      (⨂ₘᵢₙ i : {i // p i}, A i))) denseRange_of
    (g := (of (fun i : {i // ¬p i} => A i) : (⨂[ℂ] i : {i // ¬p i}, A i) →ₗ[ℂ]
      (⨂ₘᵢₙ i : {i // ¬p i}, A i))) denseRange_of
  unfold DenseRange at h ⊢
  rwa [← (PiTensorProduct.splitStarAlgEquiv ℂ A p).surjective.range_comp] at h

variable (A) in
/-- **Splitting the index set along `p`**: the minimal tensor product of a finite family is the
minimal tensor product of those of the subfamilies over `p` and over `¬p`, by the isomorphism that
is `⨂ a ↦ (⨂ a|ₚ) ⊗ (⨂ a|¬ₚ)` on the algebraic tensor product. -/
noncomputable def splitEquiv : (⨂ₘᵢₙ i, A i) ≃⋆ₐ[ℂ]
    (⨂ₘᵢₙ i : {i // p i}, A i) ⊗ₘᵢₙ
      (⨂ₘᵢₙ i : {i // ¬p i}, A i) := by
  refine NonUnitalStarAlgHom.equivOfDenseRange (φ := of A)
    (ψ := ((MinTensorProduct.of _ _).comp (NonUnitalStarAlgebra.TensorProduct.map
      (of fun i : {i // p i} => A i) (of fun i : {i // ¬p i} => A i))).comp
      (PiTensorProduct.splitStarAlgEquiv ℂ A p).toNonUnitalStarAlgHom) denseRange_of ?_ ?_
  · exact denseRange_of_map_of_splitStarAlgEquiv p
  · exact norm_of_eq_norm_splitStarAlgEquiv p

/-- `PiMinTensorProduct.splitEquiv A p` is `⨂ a ↦ (⨂ a|ₚ) ⊗ (⨂ a|¬ₚ)` on the algebraic tensor
product. -/
lemma splitEquiv_of (x : ⨂[ℂ] i, A i) :
    splitEquiv A p (of A x) = MinTensorProduct.of _ _ (TensorProduct.map
      (of (fun i : {i // p i} => A i) : (⨂[ℂ] i : {i // p i}, A i) →ₗ[ℂ]
        (⨂ₘᵢₙ i : {i // p i}, A i))
      (of (fun i : {i // ¬p i} => A i) : (⨂[ℂ] i : {i // ¬p i}, A i) →ₗ[ℂ]
        (⨂ₘᵢₙ i : {i // ¬p i}, A i))
      (PiTensorProduct.splitStarAlgEquiv ℂ A p x)) :=
  NonUnitalStarAlgHom.equivOfDenseRange_apply _ _ _ x

end Split

/-! ### The norm in a family of representations -/

/-- **The norm of the minimal tensor product of a finite family dominates the tensor product of any
family of representations**: for representations `πᵢ` of `A i`, faithful or not, the operator norm
of `(⨂ πᵢ)(x)` is at most the norm of `x` in `⨂ₘᵢₙ i, A i`. For two factors this is
`MinTensorProduct.norm_spatial_le_norm_of`. -/
theorem norm_piSpatial_le_norm_of (R : Π i, CStarRep.{u, w} (A i)) (x : ⨂[ℂ] i, A i) :
    ‖CStarRep.piSpatial R x‖ ≤ ‖of A x‖ :=
  CStarRep.norm_piSpatial_le_of_injective (fun i => CStarRep.gelfandNaimark_injective (A i)) R x

/-- **The norm of the minimal tensor product of a finite family is computed in any family of faithful
representations**: for faithful representations `πᵢ` of `A i`, the norm of `x` in `⨂ₘᵢₙ i, A i` is
the operator norm of `(⨂ πᵢ)(x)`. -/
theorem norm_of_eq_norm_piSpatial {R : Π i, CStarRep.{u, w} (A i)}
    (hR : ∀ i, Function.Injective (R i).π) (x : ⨂[ℂ] i, A i) :
    ‖of A x‖ = ‖CStarRep.piSpatial R x‖ :=
  le_antisymm (CStarRep.norm_piSpatial_le_of_injective hR _ x) (norm_piSpatial_le_norm_of R x)

end PiMinTensorProduct

/-! ### The tensor product of a family of representations, on the minimal tensor product -/

namespace CStarRep

variable {ι : Type*} [Fintype ι] {A : ι → Type u} [∀ i, NonUnitalCStarAlgebra (A i)]

/-- The **tensor product of a family of representations** `πᵢ` of `A i` on `Hᵢ`: the representation
of the minimal tensor product `⨂ₘᵢₙ i, A i` on the Hilbert space tensor product
`Completion (InnerPiTensorProduct ℂ H)` that is `⨂ πᵢ` on the algebraic tensor product
(`CStarRep.piTensorProduct_π_of`). The `πᵢ` need not be faithful: `⨂ πᵢ` is bounded by the norm of
`⨂ₘᵢₙ i, A i` (`PiMinTensorProduct.norm_piSpatial_le_norm_of`). For two factors this is
`CStarRep.tensorProduct`. -/
noncomputable abbrev piTensorProduct (R : Π i, CStarRep.{u, w} (A i)) : CStarRep (⨂ₘᵢₙ i, A i) where
  H := Completion (InnerPiTensorProduct ℂ fun i => (R i).H)
  π := (NonUnitalStarSubalgebraClass.subtype (piSpatial R).closureRange).comp
    (NonUnitalStarAlgHom.closureRangeMap (φ := piSpatial fun i => gelfandNaimark (A i))
      (ψ := piSpatial R) (PiMinTensorProduct.norm_piSpatial_le_norm_of R))

/-- On the algebraic tensor product, the tensor product of a family of representations is `⨂ πᵢ`. -/
@[simp] lemma piTensorProduct_π_of (R : Π i, CStarRep.{u, w} (A i)) (x : ⨂[ℂ] i, A i) :
    (piTensorProduct R).π (PiMinTensorProduct.of A x) = piSpatial R x :=
  congrArg Subtype.val (NonUnitalStarAlgHom.closureRangeMap_closureRangeRestrict
    (φ := piSpatial fun i => gelfandNaimark (A i)) (ψ := piSpatial R)
    (PiMinTensorProduct.norm_piSpatial_le_norm_of R) x)

end CStarRep

/-! ### The tensor product of a family of `⋆`-isomorphisms -/

namespace PiTensorProduct

variable {ι R : Type*} [CommSemiring R] [StarRing R] {A B C : ι → Type*}
  [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)] [∀ i, StarRing (A i)] [∀ i, StarModule R (A i)]
  [∀ i, Semiring (B i)] [∀ i, Algebra R (B i)] [∀ i, StarRing (B i)] [∀ i, StarModule R (B i)]
  [∀ i, Semiring (C i)] [∀ i, Algebra R (C i)] [∀ i, StarRing (C i)] [∀ i, StarModule R (C i)]

/-- The tensor product `⨂ a ↦ ⨂ e i (a i)` of a family of `⋆`-algebra homomorphisms, on the
algebraic tensor products. -/
noncomputable def mapStarAlgHom (e : Π i, A i →⋆ₐ[R] B i) : (⨂[R] i, A i) →⋆ₐ[R] ⨂[R] i, B i :=
  { liftAlgHom ((tprod R).compLinearMap fun i => (e i).toLinearMap)
      (by simp [PiTensorProduct.one_def]; rfl)
      (fun x y => by simp [PiTensorProduct.tprod_mul_tprod]; rfl) with
    map_star' x := by
      induction x using PiTensorProduct.induction_on with
      | smul_tprod r a => simp [star_tprod, map_star]
      | add x y hx hy => simp_all [star_add] }

/-- `PiTensorProduct.mapStarAlgHom e` sends `⨂ a` to `⨂ e i (a i)`. -/
@[simp] lemma mapStarAlgHom_tprod (e : Π i, A i →⋆ₐ[R] B i) (a : Π i, A i) :
    mapStarAlgHom e (⨂ₜ[R] i, a i) = ⨂ₜ[R] i, e i (a i) := by
  simp [mapStarAlgHom]

/-- The tensor product of homomorphisms is functorial. -/
lemma mapStarAlgHom_mapStarAlgHom (f : Π i, B i →⋆ₐ[R] C i) (e : Π i, A i →⋆ₐ[R] B i)
    (x : ⨂[R] i, A i) :
    mapStarAlgHom f (mapStarAlgHom e x) = mapStarAlgHom (fun i => (f i).comp (e i)) x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r a => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

/-- The tensor product of the identities is the identity. -/
lemma mapStarAlgHom_id (x : ⨂[R] i, A i) : mapStarAlgHom (fun i => StarAlgHom.id R (A i)) x = x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r a => simp
  | add x y hx hy => rw [map_add, hx, hy]

end PiTensorProduct

namespace PiMinTensorProduct

variable {ι : Type*} [Fintype ι] {A B : ι → Type u} [∀ i, CStarAlgebra (A i)]
  [∀ i, CStarAlgebra (B i)]

/-- **The minimal norm is a cross norm on elementary tensors**: `‖⨂ aᵢ‖ ≤ ∏ ‖aᵢ‖`. -/
lemma norm_of_tprod_le (a : Π i, A i) : ‖of A (⨂ₜ[ℂ] i, a i)‖ ≤ ∏ i, ‖a i‖ := by
  rw [norm_of, CStarRep.piSpatial_tprod, ContinuousLinearMap.norm_completion]
  refine (InnerPiTensorProduct.norm_mapL_le _).trans ?_
  gcongr with i
  exact NonUnitalStarAlgHom.norm_apply_le _ _

/-- The tensor product of the representations `πᵢ ∘ eᵢ` is that of the `πᵢ` after `⨂ eᵢ`. -/
lemma piSpatial_comp_mapStarAlgHom (R : Π i, CStarRep (B i)) (e : Π i, A i →⋆ₐ[ℂ] B i)
    (x : ⨂[ℂ] i, A i) :
    CStarRep.piSpatial (fun i => (R i).comp (e i).toNonUnitalStarAlgHom) x =
      CStarRep.piSpatial R (PiTensorProduct.mapStarAlgHom e x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    rw [map_smul, map_smul, map_smul, CStarRep.piSpatial_tprod,
      PiTensorProduct.mapStarAlgHom_tprod, CStarRep.piSpatial_tprod]
    rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

/-- **The tensor product of `⋆`-homomorphisms is contractive** for the minimal norms: the norm of
`⨂ eᵢ (x)` is that of `x` in the representations `πᵢ ∘ eᵢ` of the `A i`, which the minimal norm
dominates (`PiMinTensorProduct.norm_piSpatial_le_norm_of`). -/
lemma norm_of_mapStarAlgHom_le (e : Π i, A i →⋆ₐ[ℂ] B i) (x : ⨂[ℂ] i, A i) :
    ‖of B (PiTensorProduct.mapStarAlgHom e x)‖ ≤ ‖of A x‖ := by
  calc ‖of B (PiTensorProduct.mapStarAlgHom e x)‖
      = ‖CStarRep.piSpatial (fun i => CStarRep.gelfandNaimark (B i))
          (PiTensorProduct.mapStarAlgHom e x)‖ := norm_of _
    _ = ‖CStarRep.piSpatial (fun i => (CStarRep.gelfandNaimark (B i)).comp
          (e i).toNonUnitalStarAlgHom) x‖ := by rw [piSpatial_comp_mapStarAlgHom]
    _ ≤ ‖of A x‖ := norm_piSpatial_le_norm_of _ x

/-- The `⋆`-homomorphism `x ↦ of (⨂ eᵢ (x))` of the algebraic tensor product of the `A i` into the
minimal tensor product of the `B i`, whose extension is `PiMinTensorProduct.map`. -/
noncomputable abbrev ofMap (e : Π i, A i →⋆ₐ[ℂ] B i) : (⨂[ℂ] i, A i) →⋆ₙₐ[ℂ] (⨂ₘᵢₙ i, B i) :=
  (of B).comp (PiTensorProduct.mapStarAlgHom e).toNonUnitalStarAlgHom

/-- **The tensor product of a family of unital `⋆`-homomorphisms** `eᵢ : A i →⋆ₐ[ℂ] B i`, on the
minimal tensor products: the extension of `⨂ eᵢ` from the algebraic tensor product
(`PiMinTensorProduct.map_of`), which is contractive (`PiMinTensorProduct.norm_of_mapStarAlgHom_le`).
For two factors the non-unital version is `MinTensorProduct.map`. -/
noncomputable def map (e : Π i, A i →⋆ₐ[ℂ] B i) : (⨂ₘᵢₙ i, A i) →⋆ₐ[ℂ] (⨂ₘᵢₙ i, B i) :=
  let f : (⨂ₘᵢₙ i, A i) →⋆ₙₐ[ℂ] (⨂ₘᵢₙ i, B i) :=
    (NonUnitalStarSubalgebraClass.subtype (ofMap e).closureRange).comp
      (NonUnitalStarAlgHom.closureRangeMap
        (φ := CStarRep.piSpatial fun i => CStarRep.gelfandNaimark (A i)) (ψ := ofMap e)
        fun x => norm_of_mapStarAlgHom_le e x)
  have hf (x : ⨂[ℂ] i, A i) : f (of A x) = of B (PiTensorProduct.mapStarAlgHom e x) :=
    congrArg Subtype.val (NonUnitalStarAlgHom.closureRangeMap_closureRangeRestrict
      (φ := CStarRep.piSpatial fun i => CStarRep.gelfandNaimark (A i)) (ψ := ofMap e)
      (fun x => norm_of_mapStarAlgHom_le e x) x)
  have h1 : f 1 = 1 := by rw [← of_one, hf, map_one, of_one]
  { f with
    map_one' := h1
    commutes' := fun r => by
      simp only [Algebra.algebraMap_eq_smul_one]
      exact (map_smul f r 1).trans (congrArg (r • ·) h1) }

/-- `PiMinTensorProduct.map e` is `⨂ eᵢ` on the algebraic tensor product. -/
@[simp] lemma map_of (e : Π i, A i →⋆ₐ[ℂ] B i) (x : ⨂[ℂ] i, A i) :
    map e (of A x) = of B (PiTensorProduct.mapStarAlgHom e x) :=
  congrArg Subtype.val (NonUnitalStarAlgHom.closureRangeMap_closureRangeRestrict
    (φ := CStarRep.piSpatial fun i => CStarRep.gelfandNaimark (A i)) (ψ := ofMap e)
    (fun x => norm_of_mapStarAlgHom_le e x) x)

/-- The tensor product of the identities is the identity. -/
@[simp] lemma map_id_apply (z : ⨂ₘᵢₙ i, A i) : map (fun i => StarAlgHom.id ℂ (A i)) z = z := by
  induction z using denseRange_of.induction_on with
  | hp => exact isClosed_eq (map_continuous _) continuous_id
  | ih x =>
    rw [map_of]
    exact congrArg (of A) (PiTensorProduct.mapStarAlgHom_id x)

/-- **The tensor product of `⋆`-homomorphisms is functorial**: `(⨂ fᵢ) ∘ (⨂ eᵢ) = ⨂ (fᵢ ∘ eᵢ)`. -/
lemma map_map {C : ι → Type u} [∀ i, CStarAlgebra (C i)] (f : Π i, B i →⋆ₐ[ℂ] C i)
    (e : Π i, A i →⋆ₐ[ℂ] B i) (z : ⨂ₘᵢₙ i, A i) :
    map f (map e z) = map (fun i => (f i).comp (e i)) z := by
  induction z using denseRange_of.induction_on with
  | hp => exact isClosed_eq ((map_continuous _).comp (map_continuous _)) (map_continuous _)
  | ih x => rw [map_of, map_of, map_of, PiTensorProduct.mapStarAlgHom_mapStarAlgHom]

/-- **The tensor product of a family of `⋆`-isomorphisms** `eᵢ : A i ≃⋆ₐ[ℂ] B i`, on the minimal
tensor products: `PiMinTensorProduct.map` of the `eᵢ`, with inverse that of the `eᵢ⁻¹`. -/
noncomputable def congr (e : Π i, A i ≃⋆ₐ[ℂ] B i) : (⨂ₘᵢₙ i, A i) ≃⋆ₐ[ℂ] (⨂ₘᵢₙ i, B i) :=
  StarAlgEquiv.ofStarAlgHom (map fun i => (e i).toStarAlgHom)
    (map fun i => (e i).symm.toStarAlgHom)
    (StarAlgHom.ext fun z => by
      rw [StarAlgHom.comp_apply, map_map]
      change _ = z
      convert map_id_apply (A := A) z using 3
      funext i
      ext a
      exact (e i).symm_apply_apply a)
    (StarAlgHom.ext fun z => by
      rw [StarAlgHom.comp_apply, map_map]
      change _ = z
      convert map_id_apply (A := B) z using 3
      funext i
      ext a
      exact (e i).apply_symm_apply a)

/-- `PiMinTensorProduct.congr e` is `PiMinTensorProduct.map` of the `eᵢ`. -/
lemma congr_apply (e : Π i, A i ≃⋆ₐ[ℂ] B i) (z : ⨂ₘᵢₙ i, A i) :
    congr e z = map (fun i => (e i).toStarAlgHom) z :=
  rfl

/-- `PiMinTensorProduct.congr e` is `⨂ eᵢ` on the algebraic tensor product. -/
@[simp] lemma congr_of (e : Π i, A i ≃⋆ₐ[ℂ] B i) (x : ⨂[ℂ] i, A i) :
    congr e (of A x) = of B (PiTensorProduct.mapStarAlgHom (fun i => (e i).toStarAlgHom) x) :=
  map_of _ x

/-- The tensor product of the identities is the identity. -/
@[simp] lemma congr_refl_apply (z : ⨂ₘᵢₙ i, A i) :
    congr (fun i => StarAlgEquiv.refl ℂ (A i)) z = z :=
  map_id_apply z

/-- **The tensor product of `⋆`-isomorphisms is functorial**: `(⨂ fᵢ) ∘ (⨂ eᵢ) = ⨂ (fᵢ ∘ eᵢ)`. -/
lemma congr_congr {C : ι → Type u} [∀ i, CStarAlgebra (C i)] (f : Π i, B i ≃⋆ₐ[ℂ] C i)
    (e : Π i, A i ≃⋆ₐ[ℂ] B i) (z : ⨂ₘᵢₙ i, A i) :
    congr f (congr e z) = congr (fun i => (e i).trans (f i)) z :=
  map_map _ _ z

/-- **`e ↦ ⨂ eᵢ` is continuous for the point-norm topologies**: on an elementary tensor it is
`e ↦ ⨂ eᵢ aᵢ`, continuous as `‖⨂ aᵢ‖ ≤ ∏ ‖aᵢ‖` (`PiMinTensorProduct.norm_of_tprod_le`), and the
algebraic tensor product is dense, the `⨂ eᵢ` being isometric. -/
theorem continuous_congr :
    Continuous (congr : (Π i, A i ≃⋆ₐ[ℂ] B i) → (⨂ₘᵢₙ i, A i) ≃⋆ₐ[ℂ] (⨂ₘᵢₙ i, B i)) := by
  refine StarAlgEquiv.continuous_of_dense denseRange_of fun a ha => ?_
  obtain ⟨x, rfl⟩ := ha
  simp only [congr_of]
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    simp only [map_smul, PiTensorProduct.mapStarAlgHom_tprod, StarAlgEquiv.toStarAlgHom_apply]
    have hT : Continuous fun a : Π i, B i => of B (⨂ₜ[ℂ] i, a i) :=
      ((of B : (⨂[ℂ] i, B i) →ₗ[ℂ] (⨂ₘᵢₙ i, B i)).compMultilinearMap
        (PiTensorProduct.tprod ℂ)).continuous_of_bound 1 fun a => by
          simpa using norm_of_tprod_le a
    exact (hT.comp (continuous_pi fun i =>
      (continuous_eval_const (m i)).comp (continuous_apply i))).const_smul r
  | add x y hx hy =>
    simp only [map_add]
    exact hx.add hy

end PiMinTensorProduct

/-! ### Finite families of finite-dimensional factors -/

namespace PiMinTensorProduct

variable {ι : Type*} [Fintype ι] {A : ι → Type u} [∀ i, CStarAlgebra (A i)]

/-- **Over an empty index set the minimal tensor product is central**: every element is a scalar,
the algebraic tensor product over no factor being `ℂ`. -/
lemma isCentral_of_isEmpty [IsEmpty ι] : Algebra.IsCentral ℂ (⨂ₘᵢₙ i, A i) where
  out x _ := by
    have : ∀ i, FiniteDimensional ℂ (A i) := fun i => isEmptyElim i
    have key (y : ⨂[ℂ] i, A i) :
        of A y = algebraMap ℂ (⨂ₘᵢₙ i, A i) (PiTensorProduct.isEmptyEquiv ι y) := by
      induction y using PiTensorProduct.induction_on with
      | smul_tprod r a =>
        rw [Subsingleton.elim a 1, ← PiTensorProduct.one_def, map_smul, of_one, map_smul,
          PiTensorProduct.one_def, PiTensorProduct.isEmptyEquiv_apply_tprod, smul_eq_mul, mul_one,
          Algebra.algebraMap_eq_smul_one]
      | add y z hy hz => rw [map_add, map_add, map_add, hy, hz]
    obtain ⟨y, rfl⟩ := of_surjective_of_finiteDimensional (A := A) x
    exact ⟨PiTensorProduct.isEmptyEquiv ι y, (key y).symm⟩

/-- The statement of `PiMinTensorProduct.isCentral`, by induction on the number of factors. -/
private lemma isCentral_of_card_eq (n : ℕ) : ∀ (κ : Type w) [Fintype κ] (B : κ → Type u)
    [∀ k, CStarAlgebra (B k)] [∀ k, FiniteDimensional ℂ (B k)] [∀ k, Algebra.IsCentral ℂ (B k)],
    Fintype.card κ = n → Algebra.IsCentral ℂ (⨂ₘᵢₙ k, B k) := by
  induction n with
  | zero =>
    intro κ _ B _ _ _ h
    have := Fintype.card_eq_zero_iff.mp h
    exact isCentral_of_isEmpty
  | succ n ih =>
    intro κ _ B _ _ _ h
    classical
    obtain ⟨k₀⟩ : Nonempty κ := Fintype.card_pos_iff.mp (h ▸ Nat.succ_pos n)
    let : Fintype {k // k = k₀} := Subtype.fintype _
    let : Fintype {k // ¬k = k₀} := Subtype.fintype _
    have : Subsingleton {k // k = k₀} := ⟨fun a b => Subtype.ext (a.2.trans b.2.symm)⟩
    have : Algebra.IsCentral ℂ (⨂ₘᵢₙ k : {k // k = k₀}, B k) :=
      .of_algEquiv' (subsingletonEquiv (fun k : {k // k = k₀} => B k) ⟨k₀, rfl⟩).symm.toAlgEquiv
    have : Algebra.IsCentral ℂ (⨂ₘᵢₙ k : {k // ¬k = k₀}, B k) :=
      ih _ _ (by
        rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, h, Nat.add_sub_cancel])
    exact .of_algEquiv' (D := (⨂ₘᵢₙ k : {k // k = k₀}, B k) ⊗ₘᵢₙ (⨂ₘᵢₙ k : {k // ¬k = k₀}, B k))
      (splitEquiv B (· = k₀)).symm.toAlgEquiv

/-- **The minimal tensor product of finitely many finite-dimensional factors is a factor**: by
induction on the number of factors, splitting off one (`PiMinTensorProduct.splitEquiv`) and using
that the minimal tensor product of two central C⋆-algebras, one finite-dimensional, is central
(`MinTensorProduct.isCentral`). -/
instance isCentral [∀ i, FiniteDimensional ℂ (A i)] [∀ i, Algebra.IsCentral ℂ (A i)] :
    Algebra.IsCentral ℂ (⨂ₘᵢₙ i, A i) :=
  isCentral_of_card_eq _ ι A rfl

end PiMinTensorProduct
