module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Topology.Algebra.LinearMapCompletion
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import QuantumSystem.Analysis.InfiniteTensor.Completion
public import QuantumSystem.Analysis.InfiniteTensor.OperatorExtension
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# Lifting local operators to the incomplete tensor-product sector

This file upgrades the finite-region operator extension `extendOpLe` from
`OperatorExtension.lean` to the algebraic colimit `preITPSector Ω` and then to
the Hilbert completion `ITPSector Ω`.

The construction proceeds in three steps.

* First, `extendOpLe` is shown to satisfy the sharp norm bound
  `‖extendOpLe Ω h A‖ ≤ ‖A‖`.
* Next, the finite-region fibers are assembled into
  `liftToSectorPre Ω S A : preITPSector Ω →ₗ[ℂ] preITPSector Ω` via
  `Module.DirectLimit.lift`.
* Finally, the bounded pre-sector map is promoted to
  `liftToSector Ω S A : ITPSector Ω →L[ℂ] ITPSector Ω` using completion.
-/

@[expose] public section

open scoped InnerProductSpace TensorProduct
open Module _root_.PiTensorProduct

namespace InfiniteTensor

variable {ι : Type*} [DecidableEq ι] {H : ι → Type*}
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
  [∀ i, FiniteDimensional ℂ (H i)]

namespace UnitFamily

noncomputable local instance instCompleteSpaceRegionTensor (S : Finset ι) :
    CompleteSpace (regionTensor S (H := H)) :=
  FiniteDimensional.complete ℂ (regionTensor S (H := H))

noncomputable local instance instCompleteSpaceTensorRegionTensor (S T : Finset ι) :
    CompleteSpace (regionTensor S (H := H) ⊗[ℂ] regionTensor T (H := H)) :=
  FiniteDimensional.complete ℂ _

theorem regionTensorSplit_inner_tprod_tprod {S S' : Finset ι} (h : S ⊆ S')
    (ξ η : (s : {x // x ∈ S'}) → H s.val) :
    ⟪regionTensorSplit (H := H) h (PiTensorProduct.tprod ℂ ξ),
      regionTensorSplit (H := H) h (PiTensorProduct.tprod ℂ η)⟫_ℂ
      = ⟪(PiTensorProduct.tprod ℂ ξ : regionTensor S' (H := H)),
          PiTensorProduct.tprod ℂ η⟫_ℂ := by
  rw [regionTensorSplit_tprod, regionTensorSplit_tprod, _root_.TensorProduct.inner_tmul,
    ForMathlib.PiTensorProduct.inner_tprod_tprod,
    ForMathlib.PiTensorProduct.inner_tprod_tprod,
    ForMathlib.PiTensorProduct.inner_tprod_tprod]
  symm
  have hprod :
      (∏ s' : {x // x ∈ S'}, ⟪ξ s', η s'⟫_ℂ) =
        ∏ i : {x // x ∈ S} ⊕ {x // x ∈ S' \ S},
          ⟪ξ ((subsetSumEquiv h).symm i), η ((subsetSumEquiv h).symm i)⟫_ℂ := by
    refine Fintype.prod_equiv (subsetSumEquiv h)
      (fun s' : {x // x ∈ S'} => ⟪ξ s', η s'⟫_ℂ)
      (fun i : {x // x ∈ S} ⊕ {x // x ∈ S' \ S} =>
        ⟪ξ ((subsetSumEquiv h).symm i), η ((subsetSumEquiv h).symm i)⟫_ℂ) ?_
    intro s'
    simpa using
      (congrArg (fun t => ⟪ξ t, η t⟫_ℂ) ((subsetSumEquiv h).left_inv s')).symm
  rw [hprod, Fintype.prod_sum_type]
  congr 1

theorem regionTensorSplit_inner {S S' : Finset ι} (h : S ⊆ S')
    (x y : regionTensor S' (H := H)) :
    ⟪regionTensorSplit (H := H) h x, regionTensorSplit (H := H) h y⟫_ℂ = ⟪x, y⟫_ℂ := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r ξ =>
      induction y using PiTensorProduct.induction_on with
      | smul_tprod r' η =>
          rw [map_smul, map_smul]
          let a := regionTensorSplit (H := H) h (PiTensorProduct.tprod ℂ ξ)
          let b := regionTensorSplit (H := H) h (PiTensorProduct.tprod ℂ η)
          calc
            ⟪r • a, r' • b⟫_ℂ = (starRingEnd ℂ) r * ⟪a, r' • b⟫_ℂ :=
              inner_smul_left a (r' • b) r
            _ = (starRingEnd ℂ) r * (r' * ⟪a, b⟫_ℂ) := by
              simpa using congrArg (((starRingEnd ℂ) r) * ·) (inner_smul_right a b r')
            _ = (starRingEnd ℂ) r * (r' *
                  ⟪(PiTensorProduct.tprod ℂ ξ : regionTensor S' (H := H)),
                    PiTensorProduct.tprod ℂ η⟫_ℂ) := by
              rw [regionTensorSplit_inner_tprod_tprod]
            _ = (starRingEnd ℂ) r *
                  ⟪(PiTensorProduct.tprod ℂ ξ : regionTensor S' (H := H)),
                    r' • PiTensorProduct.tprod ℂ η⟫_ℂ := by
              simpa using congrArg (((starRingEnd ℂ) r) * ·)
                (Eq.symm (inner_smul_right
                  (PiTensorProduct.tprod ℂ ξ : regionTensor S' (H := H))
                  (PiTensorProduct.tprod ℂ η) r'))
            _ = ⟪r • (PiTensorProduct.tprod ℂ ξ : regionTensor S' (H := H)),
                  r' • PiTensorProduct.tprod ℂ η⟫_ℂ := by
              exact (inner_smul_left _ _ r).symm
      | add y₁ y₂ ihy₁ ihy₂ =>
          rw [map_add, inner_add_right, inner_add_right, ihy₁, ihy₂]
  | add x₁ x₂ ihx₁ ihx₂ =>
      rw [map_add, inner_add_left, inner_add_left, ihx₁, ihx₂]

/-- Bundled isometric form of `regionTensorSplit`. -/
noncomputable def regionTensorSplitIsometry {S S' : Finset ι} (h : S ⊆ S') :
    regionTensor S' (H := H) ≃ₗᵢ[ℂ]
      (regionTensor S (H := H) ⊗[ℂ] regionTensor (S' \ S) (H := H)) :=
  (regionTensorSplit (H := H) h).isometryOfInner (regionTensorSplit_inner (H := H) h)

theorem tensorMap_id_eq_rTensor {E K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K] [CompleteSpace K]
    (A : E →L[ℂ] E) :
    (TensorProduct.map A.toLinearMap LinearMap.id).toContinuousLinearMap =
      (LinearMap.rTensor K A.toLinearMap).toContinuousLinearMap := by
  ext z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [LinearMap.rTensor_tmul, TensorProduct.map_tmul]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

/-- The operator `A ↦ A ⊗ id` as a linear map on endomorphism spaces. -/
noncomputable def tensorRightLinear {E K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K] [CompleteSpace K] :
    (E →L[ℂ] E) →ₗ[ℂ] (E ⊗[ℂ] K →L[ℂ] E ⊗[ℂ] K) where
  toFun := fun A => (LinearMap.rTensor K A.toLinearMap).toContinuousLinearMap
  map_add' A B := by simp [LinearMap.rTensor_add]
  map_smul' c A := by simp [LinearMap.rTensor_smul]

/-- The operator `A ↦ A ⊗ id` as a non-unital star algebra hom. -/
noncomputable def tensorRightHom {E K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K] [CompleteSpace K]
  [CompleteSpace (E ⊗[ℂ] K)] :
    (E →L[ℂ] E) →⋆ₙₐ[ℂ] (E ⊗[ℂ] K →L[ℂ] E ⊗[ℂ] K) where
  toNonUnitalAlgHom :=
    { toFun := tensorRightLinear (K := K)
      map_zero' := by ext z; simp [tensorRightLinear, LinearMap.rTensor_zero]
      map_add' := by intro A B; exact (tensorRightLinear (K := K)).map_add A B
      map_smul' := by intro c A; exact (tensorRightLinear (K := K)).map_smul c A
      map_mul' := by
        intro A B
        ext z
        change (LinearMap.rTensor K ((A * B).toLinearMap)) z =
          (LinearMap.rTensor K A.toLinearMap) ((LinearMap.rTensor K B.toLinearMap) z)
        simpa using congrArg (fun f : E ⊗[ℂ] K →ₗ[ℂ] E ⊗[ℂ] K => f z)
          (LinearMap.rTensor_comp K A.toLinearMap B.toLinearMap) }
  map_star' := by
    intro A
    ext z
    change ((LinearMap.rTensor K (LinearMap.adjoint A.toLinearMap)).toContinuousLinearMap) z =
      (ContinuousLinearMap.adjoint ((LinearMap.rTensor K A.toLinearMap).toContinuousLinearMap)) z
    rw [← LinearMap.adjoint_toContinuousLinearMap, LinearMap.adjoint_rTensor]

theorem tensorRightLinear_norm_le {E K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K] [CompleteSpace K]
    [CompleteSpace (E ⊗[ℂ] K)]
    (A : E →L[ℂ] E) :
    ‖tensorRightLinear (K := K) A‖ ≤ ‖A‖ := by
  exact_mod_cast NonUnitalStarAlgHom.nnnorm_apply_le
    (tensorRightHom (E := E) (K := K)) A

/-- Pointwise norm bound for the finite-region extension operator. -/
theorem extendOpLe_norm_le (Ω : UnitFamily H) {S S' : Finset ι} (h : S ⊆ S')
    (A : regionTensor S (H := H) →L[ℂ] regionTensor S (H := H))
    (x : regionTensor S' (H := H)) :
    ‖extendOpLe Ω h A x‖ ≤ ‖A‖ * ‖x‖ := by
  let e := regionTensorSplitIsometry (H := H) h
  let mid := tensorRightLinear (K := regionTensor (S' \ S) (H := H)) A
  have hmid :
      ‖(TensorProduct.map A.toLinearMap LinearMap.id).toContinuousLinearMap (e x)‖
        ≤ ‖A‖ * ‖e x‖ := by
    rw [tensorMap_id_eq_rTensor (K := regionTensor (S' \ S) (H := H))]
    calc
      ‖mid (e x)‖ ≤ ‖mid‖ * ‖e x‖ := mid.le_opNorm _
      _ ≤ ‖A‖ * ‖e x‖ := by
        gcongr
        exact tensorRightLinear_norm_le (K := regionTensor (S' \ S) (H := H)) A
  rw [extendOpLe_apply]
  calc
    ‖e.symm ((TensorProduct.map A.toLinearMap LinearMap.id) (e x))‖
      = ‖(TensorProduct.map A.toLinearMap LinearMap.id).toContinuousLinearMap (e x)‖ := by
        rw [show ((TensorProduct.map A.toLinearMap LinearMap.id) (e x)) =
            (TensorProduct.map A.toLinearMap LinearMap.id).toContinuousLinearMap (e x) by rfl,
          (regionTensorSplitIsometry (H := H) h).symm.norm_map]
    _ ≤ ‖A‖ * ‖e x‖ := hmid
    _ = ‖A‖ * ‖x‖ := by rw [e.norm_map]

/-- Operator-norm bound for the finite-region extension operator. -/
theorem extendOpLe_opNorm_le (Ω : UnitFamily H) {S S' : Finset ι} (h : S ⊆ S')
    (A : regionTensor S (H := H) →L[ℂ] regionTensor S (H := H)) :
    ‖extendOpLe Ω h A‖ ≤ ‖A‖ := by
  refine (extendOpLe Ω h A).opNorm_le_bound (show 0 ≤ ‖A‖ by exact norm_nonneg _) ?_
  intro x
  exact extendOpLe_norm_le (H := H) Ω h A x

/-- The fiber map over `T`, sending a `T`-local vector to the class of the
`(S ∪ T)`-local vector obtained by embedding into `S ∪ T` and applying
`extendOpLe`. -/
noncomputable def liftToSectorFiber (Ω : UnitFamily H) (S : Finset ι)
    (A : regionTensor S (H := H) →L[ℂ] regionTensor S (H := H)) (T : Finset ι) :
    regionTensor T (H := H) →ₗ[ℂ] preITPSector Ω :=
  (preITPSector.of Ω (S ∪ T)).comp <|
    (extendOpLe Ω (Finset.subset_union_left : S ⊆ S ∪ T) A).toLinearMap.comp
      (regionEmbedLe Ω (Finset.subset_union_right : T ⊆ S ∪ T))

@[simp]
theorem liftToSectorFiber_apply (Ω : UnitFamily H) (S T : Finset ι)
    (A : regionTensor S (H := H) →L[ℂ] regionTensor S (H := H))
    (x : regionTensor T (H := H)) :
    liftToSectorFiber (H := H) Ω S A T x =
      preITPSector.of Ω (S ∪ T)
        (extendOpLe Ω (Finset.subset_union_left : S ⊆ S ∪ T) A
          (regionEmbedLe Ω (Finset.subset_union_right : T ⊆ S ∪ T) x)) := rfl

theorem liftToSectorFiber_cocycle (Ω : UnitFamily H) (S : Finset ι)
    (A : regionTensor S (H := H) →L[ℂ] regionTensor S (H := H))
    {T U : Finset ι} (hTU : T ⊆ U) (x : regionTensor T (H := H)) :
    liftToSectorFiber (H := H) Ω S A U (regionEmbedLe Ω hTU x)
      = liftToSectorFiber (H := H) Ω S A T x := by
  rw [liftToSectorFiber_apply, liftToSectorFiber_apply]
  let hSU : S ∪ T ⊆ S ∪ U := Finset.union_subset_union_right hTU
  have hcomm := congrArg
    (fun f : regionTensor (S ∪ T) (H := H) →ₗ[ℂ] regionTensor (S ∪ U) (H := H) =>
      f (regionEmbedLe Ω (Finset.subset_union_right : T ⊆ S ∪ T) x))
    (extendOpLe_regionEmbedLe_commute (H := H) Ω
      (h₀ := (Finset.subset_union_left : S ⊆ S ∪ T)) (h := hSU) A)
  simp only [LinearMap.comp_apply] at hcomm
  have hEmbed :
      regionEmbedLe Ω hSU (regionEmbedLe Ω (Finset.subset_union_right : T ⊆ S ∪ T) x) =
        regionEmbedLe Ω (Finset.subset_union_right : U ⊆ S ∪ U) (regionEmbedLe Ω hTU x) := by
    rw [regionEmbedLe_trans, regionEmbedLe_trans]
  rw [← preITPSector.of_extend Ω hSU]
  have hleft :
      preITPSector.of Ω (S ∪ U)
        (extendOpLe Ω (Finset.subset_union_left : S ⊆ S ∪ U) A
          (regionEmbedLe Ω (Finset.subset_union_right : U ⊆ S ∪ U)
            (regionEmbedLe Ω hTU x))) =
      preITPSector.of Ω (S ∪ U)
        (extendOpLe Ω (Finset.subset_union_left : S ⊆ S ∪ U) A
          (regionEmbedLe Ω hSU
            (regionEmbedLe Ω (Finset.subset_union_right : T ⊆ S ∪ T) x))) := by
    exact congrArg (fun z => preITPSector.of Ω (S ∪ U)
      (extendOpLe Ω (Finset.subset_union_left : S ⊆ S ∪ U) A z)) hEmbed.symm
  have hcommOf :
      preITPSector.of Ω (S ∪ U)
        (regionEmbedLe Ω hSU
          (extendOpLe Ω (Finset.subset_union_left : S ⊆ S ∪ T) A
            (regionEmbedLe Ω (Finset.subset_union_right : T ⊆ S ∪ T) x))) =
      preITPSector.of Ω (S ∪ U)
        (extendOpLe Ω (Finset.subset_union_left : S ⊆ S ∪ U) A
          (regionEmbedLe Ω hSU
            (regionEmbedLe Ω (Finset.subset_union_right : T ⊆ S ∪ T) x))) :=
    congrArg (preITPSector.of Ω (S ∪ U)) hcomm
  exact hleft.trans hcommOf.symm

/-- The algebraic colimit lift of a local operator. -/
noncomputable def liftToSectorPre (Ω : UnitFamily H) (S : Finset ι)
    (A : regionTensor S (H := H) →L[ℂ] regionTensor S (H := H)) :
    preITPSector Ω →ₗ[ℂ] preITPSector Ω :=
  Module.DirectLimit.lift ℂ (Finset ι)
    (fun T : Finset ι => regionTensor T (H := H))
    (regionDirectedLink Ω)
    (liftToSectorFiber (H := H) Ω S A)
    (fun _ _ hTU => liftToSectorFiber_cocycle (H := H) Ω S A hTU)

@[simp]
theorem liftToSectorPre_of (Ω : UnitFamily H) (S T : Finset ι)
    (A : regionTensor S (H := H) →L[ℂ] regionTensor S (H := H))
    (x : regionTensor T (H := H)) :
    liftToSectorPre (H := H) Ω S A (preITPSector.of Ω T x) =
      liftToSectorFiber (H := H) Ω S A T x :=
  Module.DirectLimit.lift_of (R := ℂ)
    (G := fun T : Finset ι => regionTensor T (H := H))
    (f := regionDirectedLink Ω) _ _ x

/-- Pointwise norm bound on the algebraic colimit lift. -/
theorem liftToSectorPre_norm_le (Ω : UnitFamily H) (S : Finset ι)
    (A : regionTensor S (H := H) →L[ℂ] regionTensor S (H := H))
    (x : preITPSector Ω) :
    ‖liftToSectorPre (H := H) Ω S A x‖ ≤ ‖A‖ * ‖x‖ := by
  obtain ⟨T, x', rfl⟩ := preITPSector.exists_of Ω x
  rw [liftToSectorPre_of]
  change ‖ITPSector.fromRegion Ω (S ∪ T)
      (extendOpLe Ω (Finset.subset_union_left : S ⊆ S ∪ T) A
        (regionEmbedLe Ω (Finset.subset_union_right : T ⊆ S ∪ T) x'))‖
    ≤ ‖A‖ * ‖ITPSector.fromRegion Ω T x'‖
  rw [(ITPSector.fromRegion Ω (S ∪ T)).norm_map, (ITPSector.fromRegion Ω T).norm_map]
  have hEmbedNorm :
      ‖regionEmbedLe Ω (Finset.subset_union_right : T ⊆ S ∪ T) x'‖ = ‖x'‖ :=
    (regionEmbedLeIsom Ω (Finset.subset_union_right : T ⊆ S ∪ T)).norm_map x'
  exact (extendOpLe_norm_le (H := H) Ω (Finset.subset_union_left : S ⊆ S ∪ T) A _).trans_eq
    (by rw [hEmbedNorm])

/-- The bounded continuous-linear version of `liftToSectorPre`. -/
noncomputable def liftToSectorPreL (Ω : UnitFamily H) (S : Finset ι)
    (A : regionTensor S (H := H) →L[ℂ] regionTensor S (H := H)) :
    preITPSector Ω →L[ℂ] preITPSector Ω :=
  (liftToSectorPre (H := H) Ω S A).mkContinuous ‖A‖
    (liftToSectorPre_norm_le (H := H) Ω S A)

@[simp]
theorem liftToSectorPreL_of (Ω : UnitFamily H) (S T : Finset ι)
    (A : regionTensor S (H := H) →L[ℂ] regionTensor S (H := H))
    (x : regionTensor T (H := H)) :
    liftToSectorPreL (H := H) Ω S A (preITPSector.of Ω T x) =
      liftToSectorFiber (H := H) Ω S A T x := by
  change liftToSectorPre (H := H) Ω S A (preITPSector.of Ω T x) = _
  rw [liftToSectorPre_of]

/-- The completed sector-level lift of a local operator. -/
noncomputable def liftToSector (Ω : UnitFamily H) (S : Finset ι)
    (A : regionTensor S (H := H) →L[ℂ] regionTensor S (H := H)) :
    ITPSector Ω →L[ℂ] ITPSector Ω :=
  (liftToSectorPreL (H := H) Ω S A).completion

@[simp]
theorem liftToSector_apply_coe (Ω : UnitFamily H) (S : Finset ι)
    (A : regionTensor S (H := H) →L[ℂ] regionTensor S (H := H))
    (x : preITPSector Ω) :
    liftToSector (H := H) Ω S A (x : UniformSpace.Completion (preITPSector Ω)) =
      (liftToSectorPreL (H := H) Ω S A x : UniformSpace.Completion (preITPSector Ω)) := by
  change (liftToSectorPreL (H := H) Ω S A).completion x = _
  rw [ContinuousLinearMap.completion_apply_coe]

@[simp]
theorem liftToSector_apply_embedRegion (Ω : UnitFamily H) (S T : Finset ι)
    (A : regionTensor S (H := H) →L[ℂ] regionTensor S (H := H))
    (x : regionTensor T (H := H)) :
    liftToSector (H := H) Ω S A (ITPSector.embedRegion Ω T x) =
      ITPSector.embedRegion Ω (S ∪ T)
        (extendOpLe Ω (Finset.subset_union_left : S ⊆ S ∪ T) A
          (regionEmbedLe Ω (Finset.subset_union_right : T ⊆ S ∪ T) x)) := by
  change liftToSector (H := H) Ω S A
      ((preITPSector.of Ω T x : preITPSector Ω) : UniformSpace.Completion (preITPSector Ω)) = _
  rw [liftToSector_apply_coe, liftToSectorPreL_of]
  rfl

/-- Pointwise norm bound on the completed sector lift. -/
theorem liftToSector_norm_le (Ω : UnitFamily H) (S : Finset ι)
    (A : regionTensor S (H := H) →L[ℂ] regionTensor S (H := H))
    (x : ITPSector Ω) :
    ‖liftToSector (H := H) Ω S A x‖ ≤ ‖A‖ * ‖x‖ := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_le ((liftToSector (H := H) Ω S A).continuous.norm)
      ((continuous_const.mul continuous_norm))) ?_
  intro a
  change ‖(liftToSectorPreL (H := H) Ω S A).completion
      (a : UniformSpace.Completion (preITPSector Ω))‖
    ≤ ‖A‖ * ‖(a : UniformSpace.Completion (preITPSector Ω))‖
  rw [ContinuousLinearMap.completion_apply_coe, UniformSpace.Completion.norm_coe]
  simpa [liftToSectorPreL, LinearMap.mkContinuous_apply] using
    liftToSectorPre_norm_le (H := H) Ω S A a

/-- Operator-norm bound on the completed sector lift. -/
theorem liftToSector_opNorm_le (Ω : UnitFamily H) (S : Finset ι)
    (A : regionTensor S (H := H) →L[ℂ] regionTensor S (H := H)) :
    ‖liftToSector (H := H) Ω S A‖ ≤ ‖A‖ := by
  refine (liftToSector (H := H) Ω S A).opNorm_le_bound
    (show 0 ≤ ‖A‖ by exact norm_nonneg _) ?_
  intro x
  exact liftToSector_norm_le (H := H) Ω S A x

/-! ### Structural lemmas: zero / add / smul / one / mul -/

theorem liftToSectorPre_zero (Ω : UnitFamily H) (S : Finset ι) :
    liftToSectorPre (H := H) Ω S 0 = 0 := by
  apply LinearMap.ext
  intro x
  obtain ⟨T, x', rfl⟩ := preITPSector.exists_of Ω x
  rw [liftToSectorPre_of, liftToSectorFiber_apply, extendOpLe_zero]
  simp

theorem liftToSectorPre_add (Ω : UnitFamily H) (S : Finset ι)
    (A B : regionTensor S (H := H) →L[ℂ] regionTensor S (H := H)) :
    liftToSectorPre (H := H) Ω S (A + B) =
      liftToSectorPre (H := H) Ω S A + liftToSectorPre (H := H) Ω S B := by
  apply LinearMap.ext
  intro x
  obtain ⟨T, x', rfl⟩ := preITPSector.exists_of Ω x
  rw [liftToSectorPre_of, LinearMap.add_apply, liftToSectorPre_of, liftToSectorPre_of,
    liftToSectorFiber_apply, liftToSectorFiber_apply, liftToSectorFiber_apply,
    extendOpLe_add]
  simp

theorem liftToSectorPre_smul (Ω : UnitFamily H) (S : Finset ι)
    (c : ℂ) (A : regionTensor S (H := H) →L[ℂ] regionTensor S (H := H)) :
    liftToSectorPre (H := H) Ω S (c • A) =
      c • liftToSectorPre (H := H) Ω S A := by
  apply LinearMap.ext
  intro x
  obtain ⟨T, x', rfl⟩ := preITPSector.exists_of Ω x
  rw [liftToSectorPre_of, LinearMap.smul_apply, liftToSectorPre_of,
    liftToSectorFiber_apply, liftToSectorFiber_apply, extendOpLe_smul]
  simp

theorem liftToSectorPre_one (Ω : UnitFamily H) (S : Finset ι) :
    liftToSectorPre (H := H) Ω S (ContinuousLinearMap.id ℂ (regionTensor S (H := H)))
      = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨T, x', rfl⟩ := preITPSector.exists_of Ω x
  rw [liftToSectorPre_of, liftToSectorFiber_apply, extendOpLe_one]
  change preITPSector.of Ω (S ∪ T)
      (regionEmbedLe Ω (Finset.subset_union_right : T ⊆ S ∪ T) x') =
    LinearMap.id (preITPSector.of Ω T x')
  rw [LinearMap.id_apply, preITPSector.of_extend]

theorem liftToSectorPre_mul (Ω : UnitFamily H) (S : Finset ι)
    (A B : regionTensor S (H := H) →L[ℂ] regionTensor S (H := H)) :
    liftToSectorPre (H := H) Ω S (A.comp B) =
      (liftToSectorPre (H := H) Ω S A) ∘ₗ (liftToSectorPre (H := H) Ω S B) := by
  apply LinearMap.ext
  intro x
  obtain ⟨T, x', rfl⟩ := preITPSector.exists_of Ω x
  rw [liftToSectorPre_of, liftToSectorFiber_apply, extendOpLe_mul,
    LinearMap.comp_apply, liftToSectorPre_of, liftToSectorFiber_apply]
  -- LHS: of Ω (S∪T) (((extendOpLe A).comp (extendOpLe B)) (regionEmbedLe x'))
  --    = of Ω (S∪T) ((extendOpLe A) ((extendOpLe B) (regionEmbedLe x')))
  -- RHS: liftToSectorPre A (of Ω (S∪T) ((extendOpLe B) (regionEmbedLe x')))
  -- Lift the inner intermediate value through `preITPSector.of`
  set y : regionTensor (S ∪ T) (H := H) :=
    (extendOpLe Ω (Finset.subset_union_left : S ⊆ S ∪ T) B)
      (regionEmbedLe Ω (Finset.subset_union_right : T ⊆ S ∪ T) x') with hy_def
  rw [liftToSectorPre_of, liftToSectorFiber_apply]
  change preITPSector.of Ω (S ∪ T)
      ((extendOpLe Ω (Finset.subset_union_left : S ⊆ S ∪ T) A) y) =
    preITPSector.of Ω (S ∪ (S ∪ T))
      (extendOpLe Ω (Finset.subset_union_left : S ⊆ S ∪ (S ∪ T)) A
        (regionEmbedLe Ω (Finset.subset_union_right : (S ∪ T) ⊆ S ∪ (S ∪ T)) y))
  -- The right-hand side sits over `S ∪ (S ∪ T) = S ∪ T`. Reduce via
  -- `extendOpLe_regionEmbedLe_commute` and `preITPSector.of_extend`.
  have hSS : S ∪ T ⊆ S ∪ (S ∪ T) := Finset.subset_union_right
  have hcomm := congrArg (fun f : regionTensor (S ∪ T) (H := H) →ₗ[ℂ] regionTensor (S ∪ (S ∪ T)) (H := H) => f y)
    (extendOpLe_regionEmbedLe_commute (H := H) Ω
      (h₀ := (Finset.subset_union_left : S ⊆ S ∪ T)) (h := hSS) A)
  simp only [LinearMap.comp_apply] at hcomm
  rw [← preITPSector.of_extend Ω hSS]
  exact congrArg (preITPSector.of Ω (S ∪ (S ∪ T))) hcomm

@[simp]
theorem liftToSector_zero (Ω : UnitFamily H) (S : Finset ι) :
    liftToSector (H := H) Ω S 0 = 0 := by
  ext x
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (liftToSector Ω S 0).continuous continuous_const) ?_
  intro a
  rw [liftToSector_apply_coe]
  change ((liftToSectorPreL (H := H) Ω S 0 a : preITPSector Ω) :
      UniformSpace.Completion (preITPSector Ω)) = 0
  have hpre : liftToSectorPreL (H := H) Ω S 0 a = 0 := by
    change liftToSectorPre (H := H) Ω S 0 a = 0
    rw [liftToSectorPre_zero]
    rfl
  rw [hpre]
  exact map_zero (UniformSpace.Completion.toComplL : preITPSector Ω →L[ℂ] _)

@[simp]
theorem liftToSector_add (Ω : UnitFamily H) (S : Finset ι)
    (A B : regionTensor S (H := H) →L[ℂ] regionTensor S (H := H)) :
    liftToSector (H := H) Ω S (A + B) =
      liftToSector (H := H) Ω S A + liftToSector (H := H) Ω S B := by
  ext x
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (liftToSector Ω S (A + B)).continuous
      ((liftToSector Ω S A).continuous.add (liftToSector Ω S B).continuous)) ?_
  intro a
  rw [liftToSector_apply_coe, ContinuousLinearMap.add_apply,
    liftToSector_apply_coe, liftToSector_apply_coe]
  change ((liftToSectorPreL (H := H) Ω S (A + B) a : preITPSector Ω) :
      UniformSpace.Completion (preITPSector Ω)) =
    ((liftToSectorPreL (H := H) Ω S A a : preITPSector Ω) :
      UniformSpace.Completion (preITPSector Ω)) +
      ((liftToSectorPreL (H := H) Ω S B a : preITPSector Ω) :
        UniformSpace.Completion (preITPSector Ω))
  have hpre : liftToSectorPreL (H := H) Ω S (A + B) a =
      liftToSectorPreL (H := H) Ω S A a + liftToSectorPreL (H := H) Ω S B a := by
    change liftToSectorPre (H := H) Ω S (A + B) a =
      liftToSectorPre (H := H) Ω S A a + liftToSectorPre (H := H) Ω S B a
    rw [liftToSectorPre_add]; rfl
  rw [hpre]
  push_cast
  rfl

@[simp]
theorem liftToSector_smul (Ω : UnitFamily H) (S : Finset ι)
    (c : ℂ) (A : regionTensor S (H := H) →L[ℂ] regionTensor S (H := H)) :
    liftToSector (H := H) Ω S (c • A) = c • liftToSector (H := H) Ω S A := by
  ext x
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (liftToSector Ω S (c • A)).continuous
      (c • liftToSector Ω S A).continuous) ?_
  intro a
  rw [liftToSector_apply_coe, ContinuousLinearMap.smul_apply,
    liftToSector_apply_coe]
  change ((liftToSectorPreL (H := H) Ω S (c • A) a : preITPSector Ω) :
      UniformSpace.Completion (preITPSector Ω)) =
    c • ((liftToSectorPreL (H := H) Ω S A a : preITPSector Ω) :
      UniformSpace.Completion (preITPSector Ω))
  have hpre : liftToSectorPreL (H := H) Ω S (c • A) a =
      c • liftToSectorPreL (H := H) Ω S A a := by
    change liftToSectorPre (H := H) Ω S (c • A) a =
      c • liftToSectorPre (H := H) Ω S A a
    rw [liftToSectorPre_smul]; rfl
  rw [hpre]
  push_cast
  rfl

@[simp]
theorem liftToSector_one (Ω : UnitFamily H) (S : Finset ι) :
    liftToSector (H := H) Ω S (ContinuousLinearMap.id ℂ (regionTensor S (H := H)))
      = ContinuousLinearMap.id ℂ (ITPSector Ω) := by
  ext x
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq
      (liftToSector Ω S (ContinuousLinearMap.id ℂ (regionTensor S (H := H)))).continuous
      continuous_id) ?_
  intro a
  rw [liftToSector_apply_coe, ContinuousLinearMap.id_apply]
  change ((liftToSectorPreL (H := H) Ω S
      (ContinuousLinearMap.id ℂ (regionTensor S (H := H))) a : preITPSector Ω) :
      UniformSpace.Completion (preITPSector Ω)) =
    ((a : preITPSector Ω) : UniformSpace.Completion (preITPSector Ω))
  have hpre :
      liftToSectorPreL (H := H) Ω S (ContinuousLinearMap.id ℂ (regionTensor S (H := H))) a = a := by
    change liftToSectorPre (H := H) Ω S
        (ContinuousLinearMap.id ℂ (regionTensor S (H := H))) a = a
    rw [liftToSectorPre_one]; rfl
  rw [hpre]

@[simp]
theorem liftToSector_mul (Ω : UnitFamily H) (S : Finset ι)
    (A B : regionTensor S (H := H) →L[ℂ] regionTensor S (H := H)) :
    liftToSector (H := H) Ω S (A.comp B) =
      (liftToSector (H := H) Ω S A).comp (liftToSector (H := H) Ω S B) := by
  ext x
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (liftToSector Ω S (A.comp B)).continuous
      ((liftToSector Ω S A).continuous.comp (liftToSector Ω S B).continuous)) ?_
  intro a
  rw [liftToSector_apply_coe, ContinuousLinearMap.comp_apply]
  -- RHS: liftToSector Ω S A (liftToSector Ω S B (↑a))
  --    = liftToSector Ω S A (↑(liftToSectorPreL Ω S B a))
  --    = ↑(liftToSectorPreL Ω S A (liftToSectorPreL Ω S B a))
  rw [liftToSector_apply_coe, liftToSector_apply_coe]
  change ((liftToSectorPreL (H := H) Ω S (A.comp B) a : preITPSector Ω) :
      UniformSpace.Completion (preITPSector Ω)) =
    ((liftToSectorPreL (H := H) Ω S A
        (liftToSectorPreL (H := H) Ω S B a) : preITPSector Ω) :
      UniformSpace.Completion (preITPSector Ω))
  have hpre :
      liftToSectorPreL (H := H) Ω S (A.comp B) a =
        liftToSectorPreL (H := H) Ω S A (liftToSectorPreL (H := H) Ω S B a) := by
    change liftToSectorPre (H := H) Ω S (A.comp B) a =
      liftToSectorPre (H := H) Ω S A (liftToSectorPre (H := H) Ω S B a)
    rw [liftToSectorPre_mul]; rfl
  rw [hpre]

/-! ### Isotony -/

theorem liftToSectorPre_isotony (Ω : UnitFamily H)
    {S S' : Finset ι} (h : S ⊆ S')
    (A : regionTensor S (H := H) →L[ℂ] regionTensor S (H := H)) :
    liftToSectorPre (H := H) Ω S' (extendOpLe Ω h A)
      = liftToSectorPre (H := H) Ω S A := by
  apply LinearMap.ext
  intro x
  obtain ⟨T, x', rfl⟩ := preITPSector.exists_of Ω x
  rw [liftToSectorPre_of, liftToSectorPre_of, liftToSectorFiber_apply,
    liftToSectorFiber_apply]
  -- LHS: of Ω (S' ∪ T) (extendOpLe (S' ⊆ S'∪T) (extendOpLe h A) (regionEmbedLe (T ⊆ S'∪T) x'))
  --    = of Ω (S' ∪ T) (extendOpLe (h.trans (subset_union_left)) A (regionEmbedLe (T ⊆ S'∪T) x'))  via extendOpLe_trans
  -- Both sides land in different unions: S' ∪ T vs S ∪ T. Use of_extend on S ∪ T ⊆ S' ∪ T.
  rw [← extendOpLe_trans]
  -- Goal: of Ω (S' ∪ T) (extendOpLe (h.trans _ : S ⊆ S' ∪ T) A (regionEmbedLe (T ⊆ S' ∪ T) x'))
  --     = of Ω (S ∪ T) (extendOpLe (S ⊆ S ∪ T) A (regionEmbedLe (T ⊆ S ∪ T) x'))
  have hST : S ∪ T ⊆ S' ∪ T := Finset.union_subset_union_left h
  rw [← preITPSector.of_extend Ω hST]
  -- Goal: of Ω (S'∪T) (extendOpLe ... (regionEmbedLe (T ⊆ S'∪T) x'))
  --     = of Ω (S'∪T) (regionEmbedLe (S∪T ⊆ S'∪T) (extendOpLe ... (regionEmbedLe (T ⊆ S∪T) x')))
  congr 1
  -- Apply commutation between regionEmbedLe and extendOpLe.
  have hcomm := congrArg
    (fun f : regionTensor (S ∪ T) (H := H) →ₗ[ℂ] regionTensor (S' ∪ T) (H := H) =>
      f (regionEmbedLe Ω (Finset.subset_union_right : T ⊆ S ∪ T) x'))
    (extendOpLe_regionEmbedLe_commute (H := H) Ω
      (h₀ := (Finset.subset_union_left : S ⊆ S ∪ T)) (h := hST) A)
  simp only [LinearMap.comp_apply] at hcomm
  -- hcomm: regionEmbedLe hST (extendOpLe (S ⊆ S∪T) A (regionEmbedLe (T ⊆ S∪T) x'))
  --      = extendOpLe (S ⊆ S'∪T) A (regionEmbedLe hST (regionEmbedLe (T ⊆ S∪T) x'))
  -- Rewrite the outer regionEmbedLe on the LHS via regionEmbedLe_trans to match hcomm.
  have hregionTrans :
      regionEmbedLe Ω (Finset.subset_union_right : T ⊆ S' ∪ T) x' =
        regionEmbedLe Ω hST
          (regionEmbedLe Ω (Finset.subset_union_right : T ⊆ S ∪ T) x') :=
    (regionEmbedLe_trans Ω _ _ x').symm
  rw [hregionTrans]
  exact hcomm.symm

theorem liftToSector_isotony (Ω : UnitFamily H)
    {S S' : Finset ι} (h : S ⊆ S')
    (A : regionTensor S (H := H) →L[ℂ] regionTensor S (H := H)) :
    liftToSector (H := H) Ω S' (extendOpLe Ω h A)
      = liftToSector (H := H) Ω S A := by
  ext x
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (liftToSector Ω S' (extendOpLe Ω h A)).continuous
      (liftToSector Ω S A).continuous) ?_
  intro a
  rw [liftToSector_apply_coe, liftToSector_apply_coe]
  congr 1
  change liftToSectorPre (H := H) Ω S' (extendOpLe Ω h A) a =
    liftToSectorPre (H := H) Ω S A a
  rw [liftToSectorPre_isotony]

/-! ### Adjoint -/

/-- The TensorProduct.map of `A.toLinearMap` and `id` is equal to
`LinearMap.rTensor K A.toLinearMap` as linear maps. -/
theorem tensorMap_id_eq_rTensor_lm
    {E K : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup K] [Module ℂ K]
    (A : E →ₗ[ℂ] E) :
    (TensorProduct.map A (LinearMap.id : K →ₗ[ℂ] K) :
        E ⊗[ℂ] K →ₗ[ℂ] E ⊗[ℂ] K) =
      LinearMap.rTensor K A := by
  ext a b
  simp [LinearMap.rTensor_tmul, TensorProduct.map_tmul]

theorem extendOpLe_adjoint (Ω : UnitFamily H) {S S' : Finset ι} (h : S ⊆ S')
    (A : regionTensor S (H := H) →L[ℂ] regionTensor S (H := H)) :
    ContinuousLinearMap.adjoint (extendOpLe Ω h A) =
      extendOpLe Ω h (ContinuousLinearMap.adjoint A) := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right]
  -- Goal: ⟪extendOpLe Ω h A x, y⟫ = ⟪x, extendOpLe Ω h A.adjoint y⟫
  rw [← regionTensorSplit_inner (H := H) h (extendOpLe Ω h A x) y,
      ← regionTensorSplit_inner (H := H) h x (extendOpLe Ω h A.adjoint y)]
  rw [regionTensorSplit_extendOpLe, regionTensorSplit_extendOpLe]
  -- Reduce `TensorProduct.map A.toLinearMap LinearMap.id` to `LinearMap.rTensor`.
  rw [tensorMap_id_eq_rTensor_lm A.toLinearMap,
      tensorMap_id_eq_rTensor_lm (ContinuousLinearMap.adjoint A).toLinearMap]
  -- Goal: ⟪rTensor K A.toLin (split x), split y⟫
  --     = ⟪split x, rTensor K A.adjoint.toLin (split y)⟫
  set u := regionTensorSplit (H := H) h x
  set v := regionTensorSplit (H := H) h y
  -- View `rTensor K A.toLin u` as `(rTensor K A.toLin).toCLM u`.
  change ⟪LinearMap.toContinuousLinearMap
          (LinearMap.rTensor (regionTensor (S' \ S) (H := H)) A.toLinearMap) u, v⟫_ℂ =
    ⟪u, LinearMap.toContinuousLinearMap
          (LinearMap.rTensor (regionTensor (S' \ S) (H := H))
            (ContinuousLinearMap.adjoint A).toLinearMap) v⟫_ℂ
  rw [← ContinuousLinearMap.adjoint_inner_right
        (LinearMap.toContinuousLinearMap
          (LinearMap.rTensor (regionTensor (S' \ S) (H := H)) A.toLinearMap)) u v]
  -- Goal: ⟪u, (rTensor K A.toLin).toCLM.adjoint v⟫ = ⟪u, (rTensor K A.adjoint.toLin).toCLM v⟫
  congr 1
  -- Use `tensorRightHom.map_star`.
  have hstar : tensorRightHom (E := regionTensor S (H := H))
      (K := regionTensor (S' \ S) (H := H)) (star A) =
    star (tensorRightHom (E := regionTensor S (H := H))
      (K := regionTensor (S' \ S) (H := H)) A) :=
    map_star (tensorRightHom (E := regionTensor S (H := H))
      (K := regionTensor (S' \ S) (H := H))) A
  have hstarEq :
      LinearMap.toContinuousLinearMap
          (LinearMap.rTensor (regionTensor (S' \ S) (H := H))
            (ContinuousLinearMap.adjoint A).toLinearMap) =
        ContinuousLinearMap.adjoint
          (LinearMap.toContinuousLinearMap
            (LinearMap.rTensor (regionTensor (S' \ S) (H := H)) A.toLinearMap)) := hstar
  rw [hstarEq]

theorem liftToSectorPre_adjoint_apply (Ω : UnitFamily H) (S : Finset ι)
    (A : regionTensor S (H := H) →L[ℂ] regionTensor S (H := H))
    (x y : preITPSector Ω) :
    ⟪liftToSectorPre (H := H) Ω S A x, y⟫_ℂ =
      ⟪x, liftToSectorPre (H := H) Ω S (ContinuousLinearMap.adjoint A) y⟫_ℂ := by
  obtain ⟨T, x', rfl⟩ := preITPSector.exists_of Ω x
  obtain ⟨U, y', rfl⟩ := preITPSector.exists_of Ω y
  rw [liftToSectorPre_of, liftToSectorPre_of, liftToSectorFiber_apply,
    liftToSectorFiber_apply]
  -- Transport every preITPSector.of to the common union V := (S ∪ T) ∪ U.
  set V : Finset ι := (S ∪ T) ∪ U with hV
  have hSTV : S ∪ T ⊆ V := Finset.subset_union_left
  have hSUV : S ∪ U ⊆ V := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact (Finset.subset_union_left : S ⊆ S ∪ T).trans hSTV hi
    · exact Finset.subset_union_right hi
  have hTV : T ⊆ V :=
    (Finset.subset_union_right : T ⊆ S ∪ T).trans hSTV
  have hUV : U ⊆ V := Finset.subset_union_right
  rw [← preITPSector.of_extend Ω hSTV
        (extendOpLe Ω (Finset.subset_union_left : S ⊆ S ∪ T) A
          (regionEmbedLe Ω (Finset.subset_union_right : T ⊆ S ∪ T) x')),
      ← preITPSector.of_extend Ω hUV y',
      ← preITPSector.of_extend Ω hTV x',
      ← preITPSector.of_extend Ω hSUV
        (extendOpLe Ω (Finset.subset_union_left : S ⊆ S ∪ U)
          (ContinuousLinearMap.adjoint A)
          (regionEmbedLe Ω (Finset.subset_union_right : U ⊆ S ∪ U) y'))]
  rw [inner_of_of, inner_of_of]
  -- Push extendOpLe through regionEmbedLe on both sides (commutation).
  have hcomm_left := congrArg
    (fun f : regionTensor (S ∪ T) (H := H) →ₗ[ℂ] regionTensor V (H := H) =>
      f (regionEmbedLe Ω (Finset.subset_union_right : T ⊆ S ∪ T) x'))
    (extendOpLe_regionEmbedLe_commute (H := H) Ω
      (h₀ := (Finset.subset_union_left : S ⊆ S ∪ T)) (h := hSTV) A)
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe] at hcomm_left
  have hcomm_right := congrArg
    (fun f : regionTensor (S ∪ U) (H := H) →ₗ[ℂ] regionTensor V (H := H) =>
      f (regionEmbedLe Ω (Finset.subset_union_right : U ⊆ S ∪ U) y'))
    (extendOpLe_regionEmbedLe_commute (H := H) Ω
      (h₀ := (Finset.subset_union_left : S ⊆ S ∪ U)) (h := hSUV)
      (ContinuousLinearMap.adjoint A))
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe] at hcomm_right
  rw [hcomm_left, hcomm_right]
  -- Replace nested regionEmbedLe via regionEmbedLe_trans on both sides.
  rw [regionEmbedLe_trans, regionEmbedLe_trans]
  -- Inner product on regionTensor V; convert LHS via adjoint_inner_right.
  rw [← ContinuousLinearMap.adjoint_inner_right
    (extendOpLe Ω
      ((Finset.subset_union_left : S ⊆ S ∪ T).trans hSTV) A)]
  rw [extendOpLe_adjoint]

theorem liftToSector_adjoint (Ω : UnitFamily H) (S : Finset ι)
    (A : regionTensor S (H := H) →L[ℂ] regionTensor S (H := H)) :
    ContinuousLinearMap.adjoint (liftToSector (H := H) Ω S A) =
      liftToSector (H := H) Ω S (ContinuousLinearMap.adjoint A) := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right]
  -- Goal: ⟪liftToSector Ω S A x, y⟫ = ⟪x, liftToSector Ω S A.adjoint y⟫
  refine UniformSpace.Completion.induction_on₂ x y ?_ ?_
  · refine isClosed_eq ?_ ?_
    · exact continuous_inner.comp
        (((liftToSector Ω S A).continuous.comp continuous_fst).prodMk
          continuous_snd)
    · exact continuous_inner.comp
        (continuous_fst.prodMk
          ((liftToSector Ω S
              (ContinuousLinearMap.adjoint A)).continuous.comp continuous_snd))
  · intro a b
    rw [liftToSector_apply_coe, liftToSector_apply_coe]
    change ⟪((liftToSectorPreL (H := H) Ω S A a : preITPSector Ω) :
          UniformSpace.Completion (preITPSector Ω)),
        ((b : preITPSector Ω) :
          UniformSpace.Completion (preITPSector Ω))⟫_ℂ =
      ⟪((a : preITPSector Ω) :
          UniformSpace.Completion (preITPSector Ω)),
        ((liftToSectorPreL (H := H) Ω S (ContinuousLinearMap.adjoint A) b :
            preITPSector Ω) :
          UniformSpace.Completion (preITPSector Ω))⟫_ℂ
    rw [UniformSpace.Completion.inner_coe, UniformSpace.Completion.inner_coe]
    change ⟪liftToSectorPre (H := H) Ω S A a, b⟫_ℂ =
      ⟪a, liftToSectorPre (H := H) Ω S (ContinuousLinearMap.adjoint A) b⟫_ℂ
    exact liftToSectorPre_adjoint_apply (H := H) Ω S A a b

/-! ### Disjoint commutation -/

theorem liftToSector_disjoint_commute (Ω : UnitFamily H)
    {S S' : Finset ι} (hd : Disjoint S S')
    (A : regionTensor S (H := H) →L[ℂ] regionTensor S (H := H))
    (B : regionTensor S' (H := H) →L[ℂ] regionTensor S' (H := H)) :
    Commute (liftToSector (H := H) Ω S A) (liftToSector (H := H) Ω S' B) := by
  rw [← liftToSector_isotony (H := H) Ω
      (h := (Finset.subset_union_left : S ⊆ S ∪ S')) A,
    ← liftToSector_isotony (H := H) Ω
      (h := (Finset.subset_union_right : S' ⊆ S ∪ S')) B]
  change (liftToSector (H := H) Ω (S ∪ S')
      (extendOpLe Ω (Finset.subset_union_left : S ⊆ S ∪ S') A)).comp
      (liftToSector (H := H) Ω (S ∪ S')
        (extendOpLe Ω (Finset.subset_union_right : S' ⊆ S ∪ S') B)) =
    (liftToSector (H := H) Ω (S ∪ S')
      (extendOpLe Ω (Finset.subset_union_right : S' ⊆ S ∪ S') B)).comp
      (liftToSector (H := H) Ω (S ∪ S')
        (extendOpLe Ω (Finset.subset_union_left : S ⊆ S ∪ S') A))
  rw [← liftToSector_mul, ← liftToSector_mul]
  exact congrArg (liftToSector (H := H) Ω (S ∪ S'))
    (extendOpLe_disjoint_commute (H := H) Ω hd A B)

end UnitFamily

end InfiniteTensor
