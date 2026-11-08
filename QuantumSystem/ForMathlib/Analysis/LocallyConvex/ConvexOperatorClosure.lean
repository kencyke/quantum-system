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

For normed spaces `E` and `F` over `𝕜 = ℝ` or `ℂ`, a convex set of continuous linear maps
`E →L[𝕜] F` has the same closure in the topology of pointwise convergence (the strong operator
topology, Mathlib's type copy `E →Lₚₜ[𝕜] F`) as in the weak operator topology (`E →WOT[𝕜] F`).
The two topologies have the same continuous linear functionals, the finite sums `T ↦ ∑ᵢ yᵢ (T xᵢ)`,
and closed convex sets are determined by those (`LinearMap.image_closure_of_convex`).

## Main results

* `Convex.toPointwiseConvergenceCLM_mem_closure_image_iff`: for convex `C`, `T` is in the strong
  closure of `C` iff it is in its weak closure.
-/

@[expose] public section

open scoped Topology

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]

/-- The values of operators at the points of a finite set `I`, as a linear map `E →WOT[𝕜] F → F^I`. -/
private noncomputable def evalFinset (I : Finset E) : (E →WOT[𝕜] F) →ₗ[𝕜] (I → F) where
  toFun T i := T i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] in
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

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]

/-- **The strong and the weak closure of a convex set of operators agree.** For a convex set `C` of
continuous linear maps between normed spaces, `T` lies in the closure of `C` for the topology of
pointwise convergence iff it lies in the closure of `C` for the weak operator topology. -/
theorem Convex.toPointwiseConvergenceCLM_mem_closure_image_iff {C : Set (E →L[𝕜] F)}
    (hC : Convex ℝ C) (T : E →L[𝕜] F) :
    toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) E F T ∈
        closure (toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) E F '' C) ↔
      ContinuousLinearMapWOT.ofCLM T ∈ closure (ContinuousLinearMapWOT.ofCLM '' C) := by
  set ι := toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) E F
  -- The identity from the strong to the weak copy.
  let toW : (E →Lₚₜ[𝕜] F) → E →WOT[𝕜] F := fun Y =>
    ContinuousLinearMapWOT.ofCLM ((toUniformConvergenceCLM _ _ _).symm Y)
  have htoW : Continuous toW := by
    refine ContinuousLinearMapWOT.continuous_of_dual_apply_continuous fun x y => ?_
    exact y.continuous.comp ((continuous_apply x).comp
      (PointwiseConvergenceCLM.isEmbedding_coeFn (RingHom.id 𝕜) E F).continuous)
  constructor
  · intro hT
    refine map_mem_closure (f := toW) htoW hT ?_
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
  have hnhds : Set.pi Set.univ (fun i : J => t i) ∈ 𝓝 (evalFinset J (ContinuousLinearMapWOT.ofCLM T)) :=
    set_pi_mem_nhds Set.finite_univ fun i _ => ht i
  obtain ⟨_, hv, ⟨_, ⟨S, hS, rfl⟩, rfl⟩⟩ := mem_closure_iff_nhds.mp hmem _ hnhds
  exact ⟨_, htU fun x hx => hv ⟨x, hI.mem_toFinset.mpr hx⟩ trivial, ⟨ι S, ⟨S, hS, rfl⟩, rfl⟩⟩
