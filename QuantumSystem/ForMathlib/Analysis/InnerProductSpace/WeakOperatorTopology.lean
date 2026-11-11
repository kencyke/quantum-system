/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology

/-!
# Compactness of balls in the weak operator topology

The closed balls of bounded operators from a normed space into a Hilbert space are compact in the
weak operator topology (`ContinuousLinearMapWOT.isCompact_closedBall`), hence closed in it
(`ContinuousLinearMapWOT.isClosed_closedBall`).

Along an ultrafilter on a ball of radius `r`, every matrix coefficient `⟪y, A x⟫` stays in a disc
of radius `r ‖x‖ ‖y‖` and so converges; its limit `L x y` is linear in `x`, conjugate-linear in `y`
and bounded by `r ‖x‖ ‖y‖`. The Fréchet–Riesz representation of the bounded functionals
`y ↦ conj (L x y)` gives an operator `T` with `⟪y, T x⟫ = L x y` and `‖T‖ ≤ r`, to which the
ultrafilter converges.
-/

@[expose] public section

open Filter Topology
open scoped InnerProductSpace ComplexConjugate

namespace ContinuousLinearMapWOT

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The operators of norm at most `r` form a compact set in the weak operator topology. -/
private lemma isCompact_closedBall_zero (r : ℝ) :
    IsCompact (ofCLM '' Metric.closedBall (0 : E →L[𝕜] F) r : Set (E →WOT[𝕜] F)) := by
  rw [isCompact_iff_ultrafilter_le_nhds]
  intro 𝒰 h𝒰
  have hK : ∀ᶠ A in (𝒰 : Filter (E →WOT[𝕜] F)), ‖toCLM A‖ ≤ r := by
    filter_upwards [le_principal_iff.mp h𝒰] with A hA
    obtain ⟨A, hA, rfl⟩ := hA
    simpa using hA
  have hr : 0 ≤ r := by
    obtain ⟨A, hA⟩ := hK.exists
    exact (norm_nonneg _).trans hA
  -- every matrix coefficient converges along `𝒰`
  have hbound : ∀ x y, ∀ᶠ A in (𝒰 : Filter (E →WOT[𝕜] F)), ‖⟪y, A x⟫_𝕜‖ ≤ r * ‖x‖ * ‖y‖ := by
    intro x y
    filter_upwards [hK] with A hA
    calc ‖⟪y, A x⟫_𝕜‖ ≤ ‖y‖ * ‖A x‖ := norm_inner_le_norm _ _
      _ = ‖y‖ * ‖toCLM A x‖ := rfl
      _ ≤ ‖y‖ * (‖toCLM A‖ * ‖x‖) := by gcongr; exact (toCLM A).le_opNorm x
      _ ≤ ‖y‖ * (r * ‖x‖) := by gcongr
      _ = r * ‖x‖ * ‖y‖ := by ring
  have hlim : ∀ x y, ∃ c, Tendsto (fun A : E →WOT[𝕜] F => ⟪y, A x⟫_𝕜) 𝒰 (𝓝 c) := by
    intro x y
    obtain ⟨c, -, hc⟩ := (ProperSpace.isCompact_closedBall (0 : 𝕜) (r * ‖x‖ * ‖y‖)).ultrafilter_le_nhds
      (𝒰.map fun A : E →WOT[𝕜] F => ⟪y, A x⟫_𝕜)
      (le_principal_iff.mpr ((hbound x y).mono fun A hA => by simpa using hA))
    exact ⟨c, hc⟩
  choose L hL using hlim
  have hL_add : ∀ x x' y, L (x + x') y = L x y + L x' y := fun x x' y =>
    tendsto_nhds_unique (hL (x + x') y) ((hL x y).add (hL x' y) |>.congr fun A => by
      simp [map_add, inner_add_right])
  have hL_smul : ∀ (c : 𝕜) x y, L (c • x) y = c * L x y := fun c x y =>
    tendsto_nhds_unique (hL (c • x) y) (((hL x y).const_mul c).congr fun A => by
      simp [map_smul, inner_smul_right])
  have hL_add' : ∀ x y y', L x (y + y') = L x y + L x y' := fun x y y' =>
    tendsto_nhds_unique (hL x (y + y')) ((hL x y).add (hL x y') |>.congr fun A => by
      simp [inner_add_left])
  have hL_smul' : ∀ (c : 𝕜) x y, L x (c • y) = conj c * L x y := fun c x y =>
    tendsto_nhds_unique (hL x (c • y)) (((hL x y).const_mul (conj c)).congr fun A => by
      simp [inner_smul_left])
  have hL_le : ∀ x y, ‖L x y‖ ≤ r * ‖x‖ * ‖y‖ := fun x y =>
    (isClosed_le continuous_norm continuous_const).mem_of_tendsto (hL x y) (hbound x y)
  -- the Fréchet–Riesz representation of `y ↦ conj (L x y)`
  let φ : E → StrongDual 𝕜 F := fun x =>
    LinearMap.mkContinuous
      { toFun := fun y => conj (L x y)
        map_add' := fun y y' => by rw [hL_add', map_add]
        map_smul' := fun c y => by simp [hL_smul'] }
      (r * ‖x‖) fun y => by simpa using hL_le x y
  let T₀ : E → F := fun x => (InnerProductSpace.toDual 𝕜 F).symm (φ x)
  have hT₀ : ∀ x y, ⟪y, T₀ x⟫_𝕜 = L x y := fun x y => by
    rw [← inner_conj_symm, InnerProductSpace.toDual_symm_apply]
    simp [φ]
  have hT₀_le : ∀ x, ‖T₀ x‖ ≤ r * ‖x‖ := fun x => by
    rw [LinearIsometryEquiv.norm_map]
    exact LinearMap.mkContinuous_norm_le _ (by positivity) _
  let T : E →L[𝕜] F := LinearMap.mkContinuous
    { toFun := T₀
      map_add' := fun x x' => ext_inner_left 𝕜 fun y => by
        rw [inner_add_right, hT₀, hT₀, hT₀, hL_add]
      map_smul' := fun c x => ext_inner_left 𝕜 fun y => by
        rw [RingHom.id_apply, inner_smul_right, hT₀, hT₀, hL_smul] }
    r hT₀_le
  refine ⟨ofCLM T, ?_, ?_⟩
  · exact ⟨T, by simpa using LinearMap.mkContinuous_norm_le _ hr hT₀_le, rfl⟩
  · rw [le_nhds_iff_forall_inner_apply_le_nhds]
    intro x y
    change Tendsto _ _ _
    rw [show (ofCLM T) x = T₀ x from rfl, hT₀]
    exact hL x y

/-- **Compactness of balls in the weak operator topology.** The closed balls of operators from a
normed space into a Hilbert space are compact in the weak operator topology: the ball about `x'` is
the translate by `x'` of the ball about `0`. -/
theorem isCompact_closedBall (x' : E →L[𝕜] F) (r : ℝ) :
    IsCompact (ofCLM '' Metric.closedBall x' r : Set (E →WOT[𝕜] F)) := by
  have h : (ofCLM '' Metric.closedBall x' r : Set (E →WOT[𝕜] F)) =
      (fun A => A + ofCLM x') '' (ofCLM '' Metric.closedBall 0 r) := by
    rw [Set.image_image]
    ext A
    simp only [Set.mem_image, Metric.mem_closedBall, dist_eq_norm, sub_zero]
    constructor
    · rintro ⟨B, hB, rfl⟩
      exact ⟨B - x', hB, by rw [← ofCLM_add, sub_add_cancel]⟩
    · rintro ⟨B, hB, rfl⟩
      exact ⟨B + x', by rwa [add_sub_cancel_right], rfl⟩
  rw [h]
  exact (isCompact_closedBall_zero r).image (continuous_id.add continuous_const)

/-- The closed balls of operators into a Hilbert space are closed in the weak operator topology,
being compact in a Hausdorff topology: the operator norm is lower semicontinuous in it. -/
lemma isClosed_closedBall (x' : E →L[𝕜] F) (r : ℝ) :
    IsClosed (ofCLM '' Metric.closedBall x' r : Set (E →WOT[𝕜] F)) :=
  (isCompact_closedBall x' r).isClosed

end ContinuousLinearMapWOT
