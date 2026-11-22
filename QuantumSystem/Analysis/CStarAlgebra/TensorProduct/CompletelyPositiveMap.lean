/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.CStarAlgebra.TensorProduct.Minimal
public import QuantumSystem.Analysis.OperatorSpace.CompletelyPositive
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal

/-!
# The tensor product of completely positive maps on the minimal tensor product

For completely positive maps `φ : A₁ → A₂` and `ψ : B₁ → B₂` of C⋆-algebras, the map
`a ⊗ b ↦ φ(a) ⊗ ψ(b)` of the algebraic tensor products extends to a completely positive map
`φ ⊗ ψ : A₁ ⊗ₘᵢₙ B₁ → A₂ ⊗ₘᵢₙ B₂` of the minimal tensor products, bounded by `‖φ‖ ‖ψ‖`.

With `A₂` and `B₂` represented faithfully on `H` and `K`, Stinespring's theorem gives
representations `σ` of `A₁` and `τ` of `B₁` and operators `V` and `W` with `φ(a) = V† σ(a) V` and
`ψ(b) = W† τ(b) W`. The compression `T ↦ (V ⊗ W)† (σ ⊗ τ)(T) (V ⊗ W)` of the tensor product
`CStarRep.tensorProduct` of `σ` and `τ` is completely positive, sends `a ⊗ b` to `φ(a) ⊗ ψ(b)`, and so
maps `A₁ ⊗ₘᵢₙ B₁` into the closure `A₂ ⊗ₘᵢₙ B₂` of the image of `A₂ ⊗[ℂ] B₂`; the inclusion of
`A₂ ⊗ₘᵢₙ B₂` in the operators reflects the order of matrices.

The algebras are not assumed unital, and the minimal tensor products carry their spectral order.

## Main definitions

* `CStarRep.tensorProductCompression R S V W` — the completely positive map
  `T ↦ (V ⊗ W)† (π ⊗ ρ)(T) (V ⊗ W)` on `A ⊗ₘᵢₙ B`.
* `CompletelyPositiveMap.minTensorProduct φ ψ` — the tensor product
  `φ ⊗ ψ : A₁ ⊗ₘᵢₙ B₁ →CP A₂ ⊗ₘᵢₙ B₂` of two completely positive maps.

## Main results

* `CompletelyPositiveMap.minTensorProduct_of_tmul` — `(φ ⊗ ψ)(a ⊗ b) = φ(a) ⊗ ψ(b)`.
* `CompletelyPositiveMap.norm_minTensorProduct_apply_le` — `‖(φ ⊗ ψ)(T)‖ ≤ ‖φ‖ ‖ψ‖ ‖T‖`.
* `CompletelyPositiveMap.eq_minTensorProduct` — `φ ⊗ ψ` is the only continuous additive map with
  the values `φ(a) ⊗ ψ(b)` on the pure tensors.
* `CompletelyPositiveMap.minTensorProduct_eq_map` — for `⋆`-homomorphisms `φ` and `ψ` it is
  `MinTensorProduct.map φ ψ`.
-/

@[expose] public section

open scoped TensorProduct InnerProduct MinTensorProduct CStarAlgebra Amplification PositiveLinearMap

open UniformSpace

universe u v w₁ w₂

/-! ### Compressions of the tensor product of two representations -/

namespace CStarRep

variable {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The compression `T ↦ (V ⊗ W)† (π ⊗ ρ)(T) (V ⊗ W)` of the tensor product of two representations
`π` of `A` and `ρ` of `B` by operators `V` and `W` into their Hilbert spaces: a completely positive
map of the minimal tensor product `A ⊗ₘᵢₙ B` into the operators on the Hilbert space tensor
product. -/
noncomputable def tensorProductCompression (R : CStarRep A) (S : CStarRep B)
    (V : H →L[ℂ] R.H) (W : K →L[ℂ] S.H) :
    A ⊗ₘᵢₙ B →CP (Completion (H ⊗[ℂ] K) →L[ℂ] Completion (H ⊗[ℂ] K)) :=
  CompletelyPositiveMap.comp (ContinuousLinearMap.compressionCP (V ⊗ W))
    (CompletelyPositiveMapClass.toCompletelyPositiveLinearMap (R.tensorProduct S).π)

/-- `CStarRep.tensorProductCompression R S V W T = (V ⊗ W)† (π ⊗ ρ)(T) (V ⊗ W)`. -/
lemma tensorProductCompression_apply (R : CStarRep A) (S : CStarRep B)
    (V : H →L[ℂ] R.H) (W : K →L[ℂ] S.H) (T : A ⊗ₘᵢₙ B) :
    R.tensorProductCompression S V W T = (V ⊗ W)† ∘L (R.tensorProduct S).π T ∘L (V ⊗ W) :=
  ContinuousLinearMap.compressionCP_apply (V ⊗ W) ((R.tensorProduct S).π T)

/-- The compression of the tensor product of two representations sends `a ⊗ b` to the tensor
product of the compressions: `(V ⊗ W)† (π(a) ⊗ ρ(b)) (V ⊗ W) = (V† π(a) V) ⊗ (W† ρ(b) W)`. -/
lemma tensorProductCompression_of_tmul [CompleteSpace H] [CompleteSpace K] (R : CStarRep A)
    (S : CStarRep B) (V : H →L[ℂ] R.H) (W : K →L[ℂ] S.H) (a : A) (b : B) :
    R.tensorProductCompression S V W (MinTensorProduct.of A B (a ⊗ₜ[ℂ] b)) =
      (V† ∘L R.π a ∘L V) ⊗ (W† ∘L S.π b ∘L W) := by
  rw [tensorProductCompression_apply, tensorProduct_π_of, spatial_tmul,
    ContinuousLinearMap.adjoint_completion_mapL, ← ContinuousLinearMap.completion_comp,
    ← ContinuousLinearMap.completion_comp, ← TensorProduct.mapL_comp, ← TensorProduct.mapL_comp]

/-- The compression of the tensor product of two representations is bounded by `(‖V‖ ‖W‖)²`. -/
lemma norm_tensorProductCompression_apply_le (R : CStarRep A) (S : CStarRep B)
    (V : H →L[ℂ] R.H) (W : K →L[ℂ] S.H) (T : A ⊗ₘᵢₙ B) :
    ‖R.tensorProductCompression S V W T‖ ≤ (‖V‖ * ‖W‖) ^ 2 * ‖T‖ := by
  rw [tensorProductCompression_apply]
  calc ‖(V ⊗ W)† ∘L (R.tensorProduct S).π T ∘L (V ⊗ W)‖
      ≤ ‖(V ⊗ W)†‖ * (‖(R.tensorProduct S).π T‖ * ‖V ⊗ W‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ (‖V‖ * ‖W‖) * (‖T‖ * (‖V‖ * ‖W‖)) := by
        rw [LinearIsometryEquiv.norm_map, ContinuousLinearMap.norm_completion_mapL]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (NonUnitalStarAlgHom.norm_apply_le _ T) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = (‖V‖ * ‖W‖) ^ 2 * ‖T‖ := by ring

/-- The compression of the tensor product of two representations is continuous. -/
lemma continuous_tensorProductCompression (R : CStarRep A) (S : CStarRep B)
    (V : H →L[ℂ] R.H) (W : K →L[ℂ] S.H) : Continuous (R.tensorProductCompression S V W) :=
  AddMonoidHomClass.continuous_of_bound _ _ (norm_tensorProductCompression_apply_le R S V W)

end CStarRep

/-! ### The tensor product of two completely positive maps -/

namespace CompletelyPositiveMap

variable {A₁ : Type u} {B₁ : Type v} {A₂ : Type w₁} {B₂ : Type w₂}
  [NonUnitalCStarAlgebra A₁] [PartialOrder A₁] [StarOrderedRing A₁]
  [NonUnitalCStarAlgebra B₁] [PartialOrder B₁] [StarOrderedRing B₁]
  [NonUnitalCStarAlgebra A₂] [PartialOrder A₂] [StarOrderedRing A₂]
  [NonUnitalCStarAlgebra B₂] [PartialOrder B₂] [StarOrderedRing B₂]

/-- A completely positive map `φ : A₁ → A₂` followed by the faithful representation
`CStarRep.gelfandNaimark A₂` of `A₂`: a completely positive map of `A₁` into the operators on a
Hilbert space, to which Stinespring's theorem applies. -/
noncomputable def gelfandNaimarkComp (φ : A₁ →CP A₂) :
    A₁ →CP ((CStarRep.gelfandNaimark A₂).H →L[ℂ] (CStarRep.gelfandNaimark A₂).H) :=
  CompletelyPositiveMap.comp
    (CompletelyPositiveMapClass.toCompletelyPositiveLinearMap (CStarRep.gelfandNaimark A₂).π) φ

/-- `φ.gelfandNaimarkComp a` is the operator representing `φ a`. -/
@[simp] lemma gelfandNaimarkComp_apply (φ : A₁ →CP A₂) (a : A₁) :
    φ.gelfandNaimarkComp a = (CStarRep.gelfandNaimark A₂).π (φ a) := rfl

/-- The Stinespring representation of `φ.gelfandNaimarkComp`, as a representation of `A₁`. -/
noncomputable abbrev stinespringRep (φ : A₁ →CP A₂) : CStarRep.{u, max u w₁} A₁ where
  H := φ.gelfandNaimarkComp.Stinespring
  π := φ.gelfandNaimarkComp.stinespringNonUnitalStarAlgHom

/-- The compression of the tensor product of the Stinespring representations of `φ` and `ψ` by the
tensor product of their Stinespring operators: `φ ⊗ ψ` as a completely positive map into the
operators on the Hilbert space on which `A₂ ⊗ₘᵢₙ B₂` acts. -/
noncomputable def stinespringCompression (φ : A₁ →CP A₂) (ψ : B₁ →CP B₂) :
    A₁ ⊗ₘᵢₙ B₁ →CP
      (Completion ((CStarRep.gelfandNaimark A₂).H ⊗[ℂ] (CStarRep.gelfandNaimark B₂).H) →L[ℂ]
        Completion ((CStarRep.gelfandNaimark A₂).H ⊗[ℂ] (CStarRep.gelfandNaimark B₂).H)) :=
  CStarRep.tensorProductCompression φ.stinespringRep ψ.stinespringRep
    φ.gelfandNaimarkComp.stinespringOperator ψ.gelfandNaimarkComp.stinespringOperator

/-- On pure tensors, `CompletelyPositiveMap.stinespringCompression φ ψ` is the operator representing
`φ(a) ⊗ ψ(b)`. -/
lemma stinespringCompression_of_tmul (φ : A₁ →CP A₂) (ψ : B₁ →CP B₂) (a : A₁) (b : B₁) :
    stinespringCompression φ ψ (MinTensorProduct.of A₁ B₁ (a ⊗ₜ[ℂ] b)) =
      π₀[A₂, B₂] (φ a ⊗ₜ[ℂ] ψ b) := by
  rw [stinespringCompression, CStarRep.tensorProductCompression_of_tmul, CStarRep.spatial_tmul,
    ← gelfandNaimarkComp_apply, ← gelfandNaimarkComp_apply,
    φ.gelfandNaimarkComp.apply_eq_adjoint_comp_stinespringNonUnitalStarAlgHom_comp,
    ψ.gelfandNaimarkComp.apply_eq_adjoint_comp_stinespringNonUnitalStarAlgHom_comp]

/-- On the algebraic tensor product, `CompletelyPositiveMap.stinespringCompression φ ψ` is the
algebraic tensor product of the linear maps `φ` and `ψ`, followed by the representation of
`A₂ ⊗[ℂ] B₂`. -/
lemma stinespringCompression_of (φ : A₁ →CP A₂) (ψ : B₁ →CP B₂) (x : A₁ ⊗[ℂ] B₁) :
    stinespringCompression φ ψ (MinTensorProduct.of A₁ B₁ x) =
      π₀[A₂, B₂] (TensorProduct.map (φ : A₁ →ₗ[ℂ] A₂) (ψ : B₁ →ₗ[ℂ] B₂) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => exact stinespringCompression_of_tmul φ ψ a b
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]

/-- `CompletelyPositiveMap.stinespringCompression φ ψ` takes its values in `A₂ ⊗ₘᵢₙ B₂`, the closure
of the image of `A₂ ⊗[ℂ] B₂`: it is continuous, and the algebraic tensor product is dense. -/
lemma stinespringCompression_mem (φ : A₁ →CP A₂) (ψ : B₁ →CP B₂) (T : A₁ ⊗ₘᵢₙ B₁) :
    stinespringCompression φ ψ T ∈ π₀[A₂, B₂].closureRange :=
  MinTensorProduct.denseRange_of.induction_on T
    ((NonUnitalStarAlgHom.isClosed_closureRange _).preimage
      (CStarRep.continuous_tensorProductCompression _ _ _ _))
    fun x => NonUnitalStarSubalgebra.le_topologicalClosure _
      ⟨_, (stinespringCompression_of φ ψ x).symm⟩

/-- The **tensor product of two completely positive maps** `φ : A₁ → A₂` and `ψ : B₁ → B₂`, as a
completely positive map `A₁ ⊗ₘᵢₙ B₁ → A₂ ⊗ₘᵢₙ B₂` of the minimal tensor products: the extension of
`a ⊗ b ↦ φ(a) ⊗ ψ(b)` (`CompletelyPositiveMap.minTensorProduct_of_tmul`). -/
noncomputable def minTensorProduct (φ : A₁ →CP A₂) (ψ : B₁ →CP B₂) :
    A₁ ⊗ₘᵢₙ B₁ →CP A₂ ⊗ₘᵢₙ B₂ where
  toFun T := ⟨stinespringCompression φ ψ T, stinespringCompression_mem φ ψ T⟩
  map_add' T T' := Subtype.ext (map_add (stinespringCompression φ ψ) T T')
  map_smul' c T := Subtype.ext (map_smul (stinespringCompression φ ψ) c T)
  map_cstarMatrix_nonneg' k M hM := by
    have hinj : Function.Injective
        (CStarMatrix.mapₙₐ (n := Fin k) (MinTensorProduct.subtype A₂ B₂)) :=
      fun X Y h => CStarMatrix.ext fun i j =>
        MinTensorProduct.subtype_injective (congrFun (congrFun h i) j)
    refine (NonUnitalStarAlgHom.map_le_map_iff _ hinj (x := 0)).1 ?_
    rw [map_zero]
    exact (stinespringCompression φ ψ).map_cstarMatrix_nonneg M hM

/-- As an operator, `(φ ⊗ ψ)(T)` is `CompletelyPositiveMap.stinespringCompression φ ψ T`. -/
lemma subtype_minTensorProduct_apply (φ : A₁ →CP A₂) (ψ : B₁ →CP B₂) (T : A₁ ⊗ₘᵢₙ B₁) :
    MinTensorProduct.subtype A₂ B₂ (minTensorProduct φ ψ T) = stinespringCompression φ ψ T := rfl

/-- On the algebraic tensor product, `φ ⊗ ψ` is the algebraic tensor product of the linear maps `φ`
and `ψ`. -/
lemma minTensorProduct_of (φ : A₁ →CP A₂) (ψ : B₁ →CP B₂) (x : A₁ ⊗[ℂ] B₁) :
    minTensorProduct φ ψ (MinTensorProduct.of A₁ B₁ x) =
      MinTensorProduct.of A₂ B₂ (TensorProduct.map (φ : A₁ →ₗ[ℂ] A₂) (ψ : B₁ →ₗ[ℂ] B₂) x) :=
  Subtype.ext (stinespringCompression_of φ ψ x)

/-- **The tensor product of completely positive maps on pure tensors**:
`(φ ⊗ ψ)(a ⊗ b) = φ(a) ⊗ ψ(b)`. -/
@[simp] lemma minTensorProduct_of_tmul (φ : A₁ →CP A₂) (ψ : B₁ →CP B₂) (a : A₁) (b : B₁) :
    minTensorProduct φ ψ (MinTensorProduct.of A₁ B₁ (a ⊗ₜ[ℂ] b)) =
      MinTensorProduct.of A₂ B₂ (φ a ⊗ₜ[ℂ] ψ b) :=
  minTensorProduct_of φ ψ (a ⊗ₜ[ℂ] b)

/-- The Stinespring operator `V` of `φ.gelfandNaimarkComp` has `‖V‖² = ‖φ‖`: the representation of
`A₂` is isometric. -/
lemma norm_stinespringOperator_gelfandNaimarkComp_sq (φ : A₁ →CP A₂) :
    ‖φ.gelfandNaimarkComp.stinespringOperator‖ ^ 2 = ‖φ‖ₒₚ := by
  rw [φ.gelfandNaimarkComp.norm_stinespringOperator_sq, PositiveLinearMap.opNorm_def]
  refine le_antisymm
    (ContinuousLinearMap.opNorm_le_bound _ (PositiveLinearMap.opNorm_nonneg φ) fun a => ?_)
    (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun a => ?_)
  · exact (NonUnitalStarAlgHom.norm_apply_le (CStarRep.gelfandNaimark A₂).π (φ a)).trans
      (PositiveLinearMap.norm_apply_le_opNorm_mul φ a)
  · have h := ContinuousLinearMap.le_opNorm
      (PositiveContinuousLinearMap.ofClass φ.gelfandNaimarkComp :
        A₁ →L[ℂ] (CStarRep.gelfandNaimark A₂).H →L[ℂ] (CStarRep.gelfandNaimark A₂).H) a
    exact (NonUnitalStarAlgHom.norm_map (CStarRep.gelfandNaimark A₂).π
      (CStarRep.gelfandNaimark_injective A₂) (φ a)).symm.le.trans h

/-- **The tensor product of completely positive maps is bounded by the product of the norms**:
`‖(φ ⊗ ψ)(T)‖ ≤ ‖φ‖ ‖ψ‖ ‖T‖`. -/
theorem norm_minTensorProduct_apply_le (φ : A₁ →CP A₂) (ψ : B₁ →CP B₂) (T : A₁ ⊗ₘᵢₙ B₁) :
    ‖minTensorProduct φ ψ T‖ ≤ ‖φ‖ₒₚ * ‖ψ‖ₒₚ * ‖T‖ := by
  have h := CStarRep.norm_tensorProductCompression_apply_le φ.stinespringRep ψ.stinespringRep
    φ.gelfandNaimarkComp.stinespringOperator ψ.gelfandNaimarkComp.stinespringOperator T
  rw [mul_pow, norm_stinespringOperator_gelfandNaimarkComp_sq,
    norm_stinespringOperator_gelfandNaimarkComp_sq] at h
  exact h

/-- The tensor product of two completely positive maps is continuous. -/
lemma continuous_minTensorProduct (φ : A₁ →CP A₂) (ψ : B₁ →CP B₂) :
    Continuous (minTensorProduct φ ψ) :=
  AddMonoidHomClass.continuous_of_bound _ _ (norm_minTensorProduct_apply_le φ ψ)

/-- `φ ⊗ ψ` is the only continuous additive map of `A₁ ⊗ₘᵢₙ B₁` into `A₂ ⊗ₘᵢₙ B₂` with the values
`φ(a) ⊗ ψ(b)` on the pure tensors. -/
lemma eq_minTensorProduct {F : Type*} [FunLike F (A₁ ⊗ₘᵢₙ B₁) (A₂ ⊗ₘᵢₙ B₂)]
    [AddHomClass F (A₁ ⊗ₘᵢₙ B₁) (A₂ ⊗ₘᵢₙ B₂)] {φ : A₁ →CP A₂} {ψ : B₁ →CP B₂} {Θ : F}
    (hΘ : Continuous Θ) (h : ∀ (a : A₁) (b : B₁),
      Θ (MinTensorProduct.of A₁ B₁ (a ⊗ₜ[ℂ] b)) = MinTensorProduct.of A₂ B₂ (φ a ⊗ₜ[ℂ] ψ b))
    (T : A₁ ⊗ₘᵢₙ B₁) : Θ T = minTensorProduct φ ψ T := by
  have hof (x : A₁ ⊗[ℂ] B₁) :
      Θ (MinTensorProduct.of A₁ B₁ x) = minTensorProduct φ ψ (MinTensorProduct.of A₁ B₁ x) := by
    induction x using TensorProduct.inductionOn with
    | tmul a b => rw [h, minTensorProduct_of_tmul]
    | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  exact congrFun (MinTensorProduct.denseRange_of.equalizer hΘ (continuous_minTensorProduct φ ψ)
    (funext hof)) T

/-- **For `⋆`-homomorphisms, the tensor product of completely positive maps is the tensor product
of `⋆`-homomorphisms** `MinTensorProduct.map`. -/
theorem minTensorProduct_eq_map (φ : A₁ →⋆ₙₐ[ℂ] A₂) (ψ : B₁ →⋆ₙₐ[ℂ] B₂) (T : A₁ ⊗ₘᵢₙ B₁) :
    minTensorProduct (CompletelyPositiveMapClass.toCompletelyPositiveLinearMap φ)
      (CompletelyPositiveMapClass.toCompletelyPositiveLinearMap ψ) T = MinTensorProduct.map φ ψ T :=
  (eq_minTensorProduct (φ := CompletelyPositiveMapClass.toCompletelyPositiveLinearMap φ)
    (ψ := CompletelyPositiveMapClass.toCompletelyPositiveLinearMap ψ)
    (Θ := MinTensorProduct.map φ ψ) (MinTensorProduct.continuous_map φ ψ)
    (fun a b => MinTensorProduct.map_of_tmul φ ψ a b) T).symm

end CompletelyPositiveMap
