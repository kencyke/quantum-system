/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.LocallyConvex.WeakOperatorTopology
public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM

/-!
# Strong and weak closures of convex sets of operators

The topology of pointwise convergence on `E →SL[σ] F` (the strong operator topology, Mathlib's type
copy `E →SLₚₜ[σ] F`) is finer than the weak operator topology (`E →SWOT[σ] F`): the identity
`PointwiseConvergenceCLM.toWOT` between the two type copies is continuous, so a set of operators
closed in the weak operator topology is closed in the strong one.

For a module `E` with continuous scalar multiplication and a locally convex space `F` over `𝕜 = ℝ`
or `ℂ`, a convex set of continuous linear maps `E →L[𝕜] F` has the same closure in both topologies,
and so is closed in one iff it is closed in the other. The two topologies have the same continuous
linear functionals, the finite sums `T ↦ ∑ᵢ yᵢ (T xᵢ)`, and closed convex sets are determined by
those (`LinearMap.image_closure_of_convex`). Of that identification of the two duals this file
proves the part the argument uses, that such a finite sum is weakly continuous; that every strongly
continuous functional is such a sum is not formalized.

## Main definitions

* `PointwiseConvergenceCLM.toWOT`: the identity from the strong to the weak type copy, as a
  continuous linear map.

## Main results

* `ContinuousLinearMap.isClosed_image_toPointwiseConvergenceCLM_of_isClosed_image_ofCLM`: a weakly
  closed set of operators is strongly closed.
* `Convex.toPointwiseConvergenceCLM_mem_closure_image_iff`: for convex `C`, `T` is in the strong
  closure of `C` iff it is in its weak closure.
* `Convex.isClosed_image_toPointwiseConvergenceCLM_iff`: a convex set of operators is strongly
  closed iff it is weakly closed.
-/

@[expose] public section

open scoped Topology

section Comparison

variable {𝕜₁ 𝕜₂ : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} {E F : Type*}
  [AddCommGroup E] [TopologicalSpace E] [Module 𝕜₁ E] [AddCommGroup F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [Module 𝕜₂ F] [ContinuousConstSMul 𝕜₂ F]

namespace PointwiseConvergenceCLM

variable (σ E F) in
/-- **The strong operator topology is finer than the weak one**: the identity on operators, from
the type copy `E →SLₚₜ[σ] F` carrying the topology of pointwise convergence to the type copy
`E →SWOT[σ] F` carrying the weak operator topology, as a continuous linear map. A net converging
pointwise converges in every coefficient `T ↦ y (T x)`. -/
def toWOT : (E →SLₚₜ[σ] F) →L[𝕜₂] E →SWOT[σ] F where
  toFun T := ContinuousLinearMapWOT.ofCLM ((ContinuousLinearMap.toUniformConvergenceCLM _ _ _).symm T)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := ContinuousLinearMapWOT.continuous_of_dual_apply_continuous fun x y =>
    y.continuous.comp ((continuous_apply x).comp
      (PointwiseConvergenceCLM.isEmbedding_coeFn σ E F).continuous)

/-- `PointwiseConvergenceCLM.toWOT` does not change the underlying operator. -/
@[simp] lemma toWOT_apply (T : E →SLₚₜ[σ] F) (x : E) : toWOT σ E F T x = T x := rfl

end PointwiseConvergenceCLM

namespace ContinuousLinearMap

variable [ContinuousSMul 𝕜₁ E]

/-- `PointwiseConvergenceCLM.toWOT` carries the strong copy of an operator to its weak copy. -/
@[simp] lemma toWOT_toPointwiseConvergenceCLM (T : E →SL[σ] F) :
    PointwiseConvergenceCLM.toWOT σ E F (toPointwiseConvergenceCLM 𝕜₂ σ E F T) =
      ContinuousLinearMapWOT.ofCLM T := rfl

/-- **A weakly closed set of operators is strongly closed.** No hypothesis on the set is needed:
the topology of pointwise convergence is finer than the weak operator topology
(`PointwiseConvergenceCLM.toWOT`). For a convex set the converse holds
(`Convex.isClosed_image_toPointwiseConvergenceCLM_iff`). -/
lemma isClosed_image_toPointwiseConvergenceCLM_of_isClosed_image_ofCLM {S : Set (E →SL[σ] F)}
    (hS : IsClosed (ContinuousLinearMapWOT.ofCLM '' S)) :
    IsClosed (toPointwiseConvergenceCLM 𝕜₂ σ E F '' S) := by
  have h : toPointwiseConvergenceCLM 𝕜₂ σ E F '' S =
      PointwiseConvergenceCLM.toWOT σ E F ⁻¹' (ContinuousLinearMapWOT.ofCLM '' S) := by
    ext Y
    refine ⟨by rintro ⟨T, hT, rfl⟩; exact ⟨T, hT, rfl⟩, ?_⟩
    rintro ⟨T, hT, hTY⟩
    obtain rfl := ContinuousLinearMapWOT.ofCLM_injective hTY
    exact ⟨_, hT, rfl⟩
  rw [h]
  exact hS.preimage (PointwiseConvergenceCLM.toWOT σ E F).continuous

end ContinuousLinearMap

end Comparison

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
  [ContinuousSMul 𝕜 E] [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F] [Module 𝕜 F]
  [ContinuousSMul 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [ContinuousConstSMul ℝ F]
  [LocallyConvexSpace ℝ F]

/-- The values of operators at the points of a finite set `I`, as a linear map
`E →WOT[𝕜] F → F^I`. -/
private noncomputable def evalFinset (I : Finset E) : (E →WOT[𝕜] F) →ₗ[𝕜] (I → F) where
  toFun T i := T i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [ContinuousSMul 𝕜 E] [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [ContinuousConstSMul ℝ F]
  [LocallyConvexSpace ℝ F] in
private lemma continuous_evalFinset_dualMap (I : Finset E) (f : StrongDual 𝕜 (I → F)) :
    Continuous ((evalFinset (𝕜 := 𝕜) (F := F) I).dualMap (f : Module.Dual 𝕜 (I → F))) := by
  classical
  have hf : ∀ v : I → F, f v = ∑ i, f (Pi.single i (v i)) := fun v => by
    conv_lhs => rw [← Finset.univ_sum_single v]
    exact map_sum f _ _
  have : ⇑((evalFinset (𝕜 := 𝕜) (F := F) I).dualMap (f : Module.Dual 𝕜 (I → F))) =
      fun T : E →WOT[𝕜] F =>
      ∑ i : I, (f ∘L ContinuousLinearMap.single 𝕜 (fun _ : I => F) i) (T i) := by
    funext T
    rw [LinearMap.dualMap_apply, ContinuousLinearMap.coe_coe, hf]
    rfl
  rw [this]
  exact continuous_finsetSum _ fun i _ => ContinuousLinearMapWOT.continuous_dual_apply (i : E) _

end ContinuousLinearMap

open ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
  [ContinuousSMul 𝕜 E] [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F] [Module 𝕜 F]
  [ContinuousSMul 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F] [ContinuousConstSMul ℝ F]
  [LocallyConvexSpace ℝ F]

/-- **The strong and the weak closure of a convex set of operators agree.** For a convex set `C` of
continuous linear maps from a module `E` with continuous scalar multiplication to a locally convex
space, `T` lies in the closure of `C` for the topology of pointwise convergence iff it lies in the
closure of `C` for the weak operator topology. No topological group structure is assumed of `E`. -/
theorem Convex.toPointwiseConvergenceCLM_mem_closure_image_iff
    {C : Set (E →L[𝕜] F)} (hC : Convex ℝ C) (T : E →L[𝕜] F) :
    toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) E F T ∈
        closure (toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) E F '' C) ↔
      ContinuousLinearMapWOT.ofCLM T ∈ closure (ContinuousLinearMapWOT.ofCLM '' C) := by
  set ι := toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) E F
  constructor
  · intro hT
    refine map_mem_closure (f := PointwiseConvergenceCLM.toWOT (RingHom.id 𝕜) E F)
      (ContinuousLinearMap.continuous _) hT ?_
    rintro _ ⟨S, hS, rfl⟩
    exact ⟨S, hS, rfl⟩
  intro hT
  rw [(PointwiseConvergenceCLM.isEmbedding_coeFn (RingHom.id 𝕜) E
    F).isInducing.closure_eq_preimage_closure_image, Set.mem_preimage, mem_closure_iff_nhds]
  intro U hU
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, hI, t, ht, htU⟩ := hU
  classical
  let J := hI.toFinset
  have hconv : Convex ℝ (ContinuousLinearMapWOT.ofCLM '' C : Set (E →WOT[𝕜] F)) :=
    hC.linear_image ((ContinuousLinearMapWOT.linearEquiv 𝕜).symm.toLinearMap.restrictScalars ℝ)
  have hmem : evalFinset J (ContinuousLinearMapWOT.ofCLM T) ∈
      closure (evalFinset J '' (ContinuousLinearMapWOT.ofCLM '' C)) :=
    (evalFinset J).image_closure_of_convex hconv (continuous_evalFinset_dualMap J) ⟨_, hT, rfl⟩
  have hnhds :
      Set.pi Set.univ (fun i : J => t i) ∈ 𝓝 (evalFinset J (ContinuousLinearMapWOT.ofCLM T)) :=
    set_pi_mem_nhds Set.finite_univ fun i _ => ht i
  obtain ⟨_, hv, ⟨_, ⟨S, hS, rfl⟩, rfl⟩⟩ := mem_closure_iff_nhds.mp hmem _ hnhds
  exact ⟨_, htU fun x hx => hv ⟨x, hI.mem_toFinset.mpr hx⟩ trivial, ⟨ι S, ⟨S, hS, rfl⟩, rfl⟩⟩

/-- **A convex set of operators is strongly closed iff it is weakly closed.** A weakly closed set is
strongly closed whether convex or not
(`ContinuousLinearMap.isClosed_image_toPointwiseConvergenceCLM_of_isClosed_image_ofCLM`); for a
convex set the two closures agree (`Convex.toPointwiseConvergenceCLM_mem_closure_image_iff`). -/
theorem Convex.isClosed_image_toPointwiseConvergenceCLM_iff {C : Set (E →L[𝕜] F)}
    (hC : Convex ℝ C) :
    IsClosed (toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) E F '' C) ↔
      IsClosed (ContinuousLinearMapWOT.ofCLM '' C) := by
  refine ⟨fun h => isClosed_of_closure_subset fun Y hY => ?_,
    isClosed_image_toPointwiseConvergenceCLM_of_isClosed_image_ofCLM⟩
  obtain ⟨T, rfl⟩ := ContinuousLinearMapWOT.ofCLM_surjective Y
  have hT := (hC.toPointwiseConvergenceCLM_mem_closure_image_iff T).mpr hY
  rw [h.closure_eq] at hT
  obtain ⟨S, hS, hST⟩ := hT
  obtain rfl : S = T := hST
  exact ⟨S, hS, rfl⟩
