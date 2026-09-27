/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# The double adjoint of an unbounded operator

For a densely defined operator `T` between Hilbert spaces:

* `T` is closable if and only if its adjoint `T†` is densely defined;
* the closure has the same adjoint, `(closure T)† = T†`;
* when `T` is closable, `T†† = closure T`; in particular `T†† = T` for closed `T`.

All of this reduces to the graph statement `g.adjoint.adjoint = closure g` for a submodule
`g ⊆ E × F`, proved by writing the closure of `g` as its double orthogonal complement in the
`L²` product `WithLp 2 (E × F)`.

## Main results

* `Submodule.adjoint_adjoint` — `g.adjoint.adjoint = g.topologicalClosure`.
* `Submodule.adjoint_topologicalClosure` — `g.topologicalClosure.adjoint = g.adjoint`.
* `LinearPMap.mem_graph_adjoint_iff` — the graph of `T†` in terms of the graph of `T`.
* `LinearPMap.adjoint_closure` — `T.closure† = T†`.
* `LinearPMap.isClosable_iff_dense_adjoint_domain` — `T` is closable iff `T†` is densely defined.
* `LinearPMap.adjoint_adjoint` — `T†† = T.closure` for closable `T`.
* `LinearPMap.IsClosed.adjoint_adjoint` — `T†† = T` for closed `T`.

## References

* [J. Weidmann, *Linear Operators in Hilbert Spaces*][weidmann_linear]
-/

@[expose] public section

open scoped LinearPMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

namespace Submodule

/-- The adjoint of a submodule of `E × F` is closed. -/
theorem isClosed_adjoint (g : Submodule 𝕜 (E × F)) : IsClosed (g.adjoint : Set (F × E)) := by
  have : (g.adjoint : Set (F × E)) =
      ⋂ p ∈ g, {x : F × E | ⟪p.2, x.1⟫ - ⟪p.1, x.2⟫ = 0} := by
    ext x
    simp only [SetLike.mem_coe, mem_adjoint_iff, Set.mem_iInter, Set.mem_ofPred_eq, Prod.forall]
  rw [this]
  exact isClosed_biInter fun p _ => isClosed_eq (by fun_prop) continuous_const

/-- A submodule is contained in its double adjoint. -/
theorem le_adjoint_adjoint (g : Submodule 𝕜 (E × F)) : g ≤ g.adjoint.adjoint := by
  intro p hp
  rw [mem_adjoint_iff]
  intro y x hyx
  rw [mem_adjoint_iff] at hyx
  have := hyx p.1 p.2 hp
  dsimp only at this
  rw [← inner_conj_symm x, ← inner_conj_symm y, ← map_sub, ← neg_sub, this, neg_zero, map_zero]

/-- Passing to the closure does not change the adjoint of a submodule. -/
theorem adjoint_topologicalClosure (g : Submodule 𝕜 (E × F)) :
    g.topologicalClosure.adjoint = g.adjoint := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · rw [mem_adjoint_iff] at hx ⊢
    exact fun a b hab => hx a b (g.le_topologicalClosure hab)
  · rw [mem_adjoint_iff] at hx ⊢
    intro a b hab
    have hcl : IsClosed {p : E × F | ⟪p.2, x.1⟫ - ⟪p.1, x.2⟫ = 0} :=
      isClosed_eq (by fun_prop) continuous_const
    exact closure_minimal (fun p hp => hx p.1 p.2 hp) hcl (show (a, b) ∈ closure (g : Set (E × F)) from hab)

/-- **Double adjoint of a graph-like submodule.** For Hilbert spaces `E`, `F`, the double adjoint
of a submodule `g ⊆ E × F` is its closure. -/
theorem adjoint_adjoint [CompleteSpace E] [CompleteSpace F] (g : Submodule 𝕜 (E × F)) :
    g.adjoint.adjoint = g.topologicalClosure := by
  refine le_antisymm (fun p hp => ?_)
    (g.topologicalClosure_minimal g.le_adjoint_adjoint g.adjoint.isClosed_adjoint)
  let gL : Submodule 𝕜 (WithLp 2 (E × F)) := g.comap (WithLp.linearEquiv 2 𝕜 (E × F)).toLinearMap
  have key : WithLp.toLp 2 p ∈ gLᗮᗮ := by
    rw [mem_orthogonal]
    intro u hu
    rw [mem_orthogonal] at hu
    have hvu : ((WithLp.ofLp u).2, -(WithLp.ofLp u).1) ∈ g.adjoint := by
      rw [mem_adjoint_iff]
      intro a b hab
      have := hu (WithLp.toLp 2 (a, b)) hab
      rw [WithLp.prod_inner_apply, WithLp.ofLp_toLp] at this
      simp only [inner_neg_right, sub_neg_eq_add]
      linear_combination this
    have := (mem_adjoint_iff _ _).mp hp _ _ hvu
    rw [WithLp.prod_inner_apply]
    simp only [inner_neg_left, neg_sub_left, neg_eq_zero] at this
    simpa [add_comm] using this
  rw [orthogonal_orthogonal_eq_closure] at key
  refine map_mem_closure (WithLp.prod_continuous_ofLp 2 E F) key fun q hq => hq

end Submodule

namespace LinearPMap

variable [CompleteSpace E] {T : E →ₗ.[𝕜] F}

/-- The graph of the adjoint of a densely defined operator: `(y, w) ∈ graph T†` iff
`⟪v', y⟫ = ⟪v, w⟫` for every `(v, v')` in the graph of `T`. -/
theorem mem_graph_adjoint_iff (hT : Dense (T.domain : Set E)) {y : F} {w : E} :
    (y, w) ∈ T†.graph ↔ ∀ v v', (v, v') ∈ T.graph → inner 𝕜 v' y = inner 𝕜 v w := by
  rw [adjoint_graph_eq_graph_adjoint hT, Submodule.mem_adjoint_iff]
  exact forall₂_congr fun _ _ => imp_congr_right fun _ => sub_eq_zero

/-- A densely defined operator and its closure have the same adjoint. (If `T` is not closable,
`T.closure = T` by convention and the statement is trivial.) -/
theorem adjoint_closure (hT : Dense (T.domain : Set E)) : T.closure† = T† := by
  by_cases hc : T.IsClosable
  · refine eq_of_eq_graph ?_
    rw [adjoint_graph_eq_graph_adjoint (hT.mono T.le_closure.1), adjoint_graph_eq_graph_adjoint hT,
      ← hc.graph_closure_eq_closure_graph, Submodule.adjoint_topologicalClosure]
  · rw [closure_def' hc]

/-- A densely defined operator between Hilbert spaces is closable if and only if its adjoint is
densely defined. -/
theorem isClosable_iff_dense_adjoint_domain [CompleteSpace F] (hT : Dense (T.domain : Set E)) :
    T.IsClosable ↔ Dense (T†.domain : Set F) := by
  refine ⟨fun hc => ?_, fun hd => isClosable_iff_exists_closed_extension.mpr
    ⟨T††, adjoint_isClosed hd, IsFormalAdjoint.le_adjoint hd (adjoint_isFormalAdjoint hT)⟩⟩
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro z hz
  have h0z : ((0 : E), z) ∈ T†.graph.adjoint := by
    rw [Submodule.mem_adjoint_iff]
    intro a b hab
    rw [inner_zero_right, zero_sub, neg_eq_zero]
    exact (Submodule.mem_orthogonal _ _).mp hz a (mem_domain_of_mem_graph hab)
  rw [adjoint_graph_eq_graph_adjoint hT, Submodule.adjoint_adjoint,
    hc.graph_closure_eq_closure_graph] at h0z
  exact T.closure.graph_fst_eq_zero_snd h0z rfl

/-- **Double adjoint.** For a densely defined closable operator `T` between Hilbert spaces,
`T†† = closure T`. -/
theorem adjoint_adjoint [CompleteSpace F] (hT : Dense (T.domain : Set E)) (hc : T.IsClosable) :
    T†† = T.closure := by
  refine eq_of_eq_graph ?_
  rw [adjoint_graph_eq_graph_adjoint ((isClosable_iff_dense_adjoint_domain hT).mp hc),
    adjoint_graph_eq_graph_adjoint hT, Submodule.adjoint_adjoint, hc.graph_closure_eq_closure_graph]

/-- A densely defined closed operator between Hilbert spaces is its own double adjoint. -/
theorem IsClosed.adjoint_adjoint [CompleteSpace F] (hT : Dense (T.domain : Set E))
    (hTc : T.IsClosed) : T†† = T := by
  refine eq_of_eq_graph ?_
  rw [adjoint_graph_eq_graph_adjoint ((isClosable_iff_dense_adjoint_domain hT).mp hTc.isClosable),
    adjoint_graph_eq_graph_adjoint hT, Submodule.adjoint_adjoint, hTc.submodule_topologicalClosure_eq]

end LinearPMap
