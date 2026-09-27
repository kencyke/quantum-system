/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# The closed graph theorem for partially defined linear maps

A closed partially defined linear map between Banach spaces whose domain is closed is continuous
on its domain. In particular a closed, everywhere-defined `LinearPMap` is a bounded operator; this
is how resolvents and other inverses of closed operators become elements of `E →L[𝕜] F`.

## Main results

* `LinearPMap.IsClosed.continuous` — a closed `LinearPMap` with closed domain is continuous.
* `LinearPMap.IsClosed.toContinuousLinearMap` — a closed, everywhere-defined `LinearPMap` as a
  bounded operator, with `LinearPMap.IsClosed.toPMap_toContinuousLinearMap` recovering the
  original map.
* `LinearPMap.IsClosed.neg`, `LinearPMap.IsClosed.vadd` — closedness is preserved by negation and
  by bounded perturbation.
* `LinearPMap.IsClosed.isClosed_range` — a closed operator that is bounded below has closed range.
* `LinearPMap.IsClosed.exists_inverse` — a closed operator that is bounded below with dense range
  has a bounded two-sided inverse.
-/

@[expose] public section

namespace LinearPMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {T : E →ₗ.[𝕜] F}

/-- **Closed graph theorem** for partially defined maps: a closed `LinearPMap` between Banach
spaces whose domain is closed is continuous on its domain. -/
theorem IsClosed.continuous (hT : T.IsClosed) (hdom : _root_.IsClosed (T.domain : Set E)) :
    Continuous T := by
  have : CompleteSpace T.domain := hdom.completeSpace_coe
  refine T.toFun.continuous_of_isClosed_graph ?_
  have : (T.toFun.graph : Set (T.domain × F)) = Prod.map Subtype.val id ⁻¹' T.graph := by
    ext ⟨x, y⟩
    simp only [SetLike.mem_coe, LinearMap.mem_graph_iff, Set.mem_preimage, Prod.map_apply, id_eq,
      mem_graph_iff, Subtype.exists, exists_and_left, exists_eq_left, Subtype.coe_eta,
      toFun_eq_coe, exists_prop]
    exact ⟨fun h => ⟨x.2, h.symm⟩, fun h => h.2.symm⟩
  rw [this]
  exact hT.preimage (continuous_subtype_val.prodMap continuous_id)

/-- A closed, everywhere-defined `LinearPMap` between Banach spaces, as a bounded operator
(closed graph theorem). -/
noncomputable def IsClosed.toContinuousLinearMap (hT : T.IsClosed) (hdom : T.domain = ⊤) :
    E →L[𝕜] F where
  toLinearMap := T.toFun ∘ₗ (LinearEquiv.ofTop T.domain hdom).symm.toLinearMap
  cont := (hT.continuous (hdom ▸ isClosed_univ)).comp
    (continuous_id.subtype_mk fun _ => hdom.symm ▸ Submodule.mem_top)

/-- The bounded operator `hT.toContinuousLinearMap hdom` agrees with `T` on `T.domain`. -/
@[simp]
lemma IsClosed.toContinuousLinearMap_apply (hT : T.IsClosed) (hdom : T.domain = ⊤)
    (x : T.domain) : hT.toContinuousLinearMap hdom x = T x :=
  rfl

/-- The bounded operator `hT.toContinuousLinearMap hdom` evaluated at a point `x : E`. -/
lemma IsClosed.toContinuousLinearMap_apply' (hT : T.IsClosed) (hdom : T.domain = ⊤) (x : E) :
    hT.toContinuousLinearMap hdom x = T ⟨x, hdom ▸ Submodule.mem_top⟩ :=
  rfl

/-- Restricting `hT.toContinuousLinearMap hdom` to `⊤` recovers `T`. -/
@[simp]
lemma IsClosed.toPMap_toContinuousLinearMap (hT : T.IsClosed) (hdom : T.domain = ⊤) :
    (hT.toContinuousLinearMap hdom : E →ₗ[𝕜] F).toPMap ⊤ = T :=
  LinearPMap.ext hdom.symm fun _ _ _ => rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- The negative of a closed operator is closed. -/
theorem IsClosed.neg (hT : T.IsClosed) : (-T).IsClosed := by
  have : ((-T).graph : Set (E × F)) = Prod.map id (fun y => -y) ⁻¹' T.graph := by
    ext ⟨x, y⟩
    simp only [SetLike.mem_coe, mem_graph_iff, neg_domain, neg_apply, Set.mem_preimage,
      Prod.map_apply, id_eq, neg_eq_iff_eq_neg]
  rw [IsClosed, this]
  exact hT.preimage (continuous_id.prodMap continuous_neg)

omit [CompleteSpace E] [CompleteSpace F] in
/-- A bounded perturbation of a closed operator is closed. -/
theorem IsClosed.vadd (hT : T.IsClosed) (A : E →L[𝕜] F) : ((A : E →ₗ[𝕜] F) +ᵥ T).IsClosed := by
  have : (((A : E →ₗ[𝕜] F) +ᵥ T).graph : Set (E × F)) =
      (fun p : E × F => (p.1, p.2 - A p.1)) ⁻¹' T.graph := by
    ext ⟨x, y⟩
    simp only [SetLike.mem_coe, mem_graph_iff, vadd_domain, Set.mem_preimage]
    refine exists_congr fun z => and_congr_right fun hz => ?_
    rw [vadd_apply, eq_sub_iff_add_eq, add_comm, ← hz]
    rfl
  rw [IsClosed, this]
  exact hT.preimage (by fun_prop)

omit [CompleteSpace F] in
/-- A closed operator on a Banach space that is bounded below has closed range. -/
theorem IsClosed.isClosed_range (hT : T.IsClosed) {c : ℝ} (hc : 0 < c)
    (hbdd : ∀ x y, (x, y) ∈ T.graph → c * ‖x‖ ≤ ‖y‖) :
    _root_.IsClosed (LinearMap.range T.toFun : Set F) := by
  refine isClosed_of_closure_subset fun w hw => ?_
  obtain ⟨x, hxS, hxw⟩ := mem_closure_iff_seq_limit.mp hw
  choose u hu using fun n => LinearMap.mem_range.mp (hxS n)
  have hu' : ∀ m n, dist (u m : E) (u n) ≤ c⁻¹ * dist (x m) (x n) := fun m n => by
    rw [dist_eq_norm, dist_eq_norm, le_inv_mul_iff₀ hc, ← hu m, ← hu n, toFun_eq_coe,
      toFun_eq_coe, ← map_sub]
    exact hbdd _ _ (T.mem_graph (u m - u n))
  have hcau : CauchySeq fun n => (u n : E) := by
    refine Metric.cauchySeq_iff.mpr fun ε hε => ?_
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hxw.cauchySeq (c * ε) (mul_pos hc hε)
    refine ⟨N, fun m hm n hn => (hu' m n).trans_lt ?_⟩
    rw [inv_mul_lt_iff₀ hc]
    exact hN m hm n hn
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hcau
  have hmem : (v, w) ∈ T.graph := by
    refine hT.mem_of_tendsto (hv.prodMk_nhds hxw) (Filter.Eventually.of_forall fun n => ?_)
    rw [← hu n]
    exact T.mem_graph (u n)
  obtain ⟨y, -, hy⟩ := (mem_graph_iff T).mp hmem
  exact ⟨y, hy⟩

/-- A closed operator between Banach spaces that is bounded below and has dense range is
invertible, with a bounded inverse `R`: `(R y, y)` lies in the graph for every `y`, and
`R (T x) = x`. -/
theorem IsClosed.exists_inverse (hT : T.IsClosed) {c : ℝ} (hc : 0 < c)
    (hbdd : ∀ x y, (x, y) ∈ T.graph → c * ‖x‖ ≤ ‖y‖)
    (hdense : Dense (LinearMap.range T.toFun : Set F)) :
    ∃ R : F →L[𝕜] E, (∀ y, (R y, y) ∈ T.graph) ∧ ∀ x z, (x, z) ∈ T.graph → R z = x := by
  have hker : T.ker = ⊥ := ker_eq_bot'.mpr fun x hx => by
    have := hbdd _ _ (T.mem_graph x)
    rw [hx, norm_zero] at this
    exact norm_eq_zero.mp (le_antisymm ((mul_nonpos_iff_pos_imp_nonpos.mp this).1 hc)
      (norm_nonneg _)) |> Subtype.ext
  have hrange : LinearMap.range T.toFun = ⊤ := by
    refine SetLike.coe_injective ?_
    rw [Submodule.top_coe, ← (hT.isClosed_range hc hbdd).closure_eq, hdense.closure_eq]
  have hinv : T.inverse.IsClosed := (inverse_closed_iff hker).mpr hT
  have hdom : T.inverse.domain = ⊤ := inverse_domain.trans hrange
  refine ⟨hinv.toContinuousLinearMap hdom, fun y => ?_, fun x z hxz => ?_⟩
  · have h := T.inverse.mem_graph ⟨y, hdom ▸ Submodule.mem_top⟩
    rw [inverse_graph hker, Submodule.mem_map] at h
    obtain ⟨⟨a, b⟩, hab, he⟩ := h
    simp only [LinearEquiv.coe_coe, LinearEquiv.prodComm_apply, Prod.swap_prod_mk,
      Prod.mk.injEq] at he
    rw [IsClosed.toContinuousLinearMap_apply', ← he.2, ← he.1]
    exact hab
  · have hzx : (z, x) ∈ T.inverse.graph := by
      rw [inverse_graph hker]
      exact Submodule.mem_map.mpr ⟨(x, z), hxz, rfl⟩
    exact ((image_iff _).mpr hzx).symm

end LinearPMap
