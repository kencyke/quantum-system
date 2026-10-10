/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import QuantumSystem.ForMathlib.LinearAlgebra.LinearPMap
public import QuantumSystem.ForMathlib.Topology.Algebra.Module.LinearPMap

/-!
# Adjoints of sums and composites of unbounded operators

Rules for the adjoint `T†` of a densely defined `LinearPMap` between Hilbert spaces under
perturbation and composition by bounded operators, following [Weidmann].

## Main results

* `LinearPMap.adjoint_vadd` — `(A + T)† = A† + T†` for a bounded, everywhere-defined `A`.
* `LinearPMap.adjoint_compNat_le` — `T† S† ⊆ (S T)†` for densely defined `S` whenever `S T` is
  densely defined.
* `LinearPMap.adjoint_compPMap` — `(B T)† = T† B†` for a bounded, everywhere-defined `B` on the
  left.
* `LinearPMap.adjoint_compNat_toPMap` — `(T B)† = B† T†` for a bounded `B` on the right, provided
  `T` factors through `B` via a bounded `C`: `B C` maps `dom T` into itself and `T (B C x) = T x`.
  The two standard instances are `B` invertible (`C = B⁻¹`) and `B` a partial isometry whose
  range projection `B B†` does not change `T` (`C = B†`).

* `LinearPMap.compPMap_adjoint_le_adjoint_compNat_toPMap` — `B† S† ⊆ (S B)†` for a bounded `B`.
* `LinearPMap.compPMap_closure_le`, `LinearPMap.closure_compNat_toPMap_le`,
  `LinearPMap.IsClosed.compNat_toPMap` — `B T̄ ⊆ closure (B T)`, `closure (T B) ⊆ T̄ B`, and `T B` is
  closed for closed `T`, for a bounded `B`.
* `LinearPMap.compPMap_closure_le_closure_compNat_toPMap` — `B T ⊆ S C` implies `B T̄ ⊆ S̄ C`.

All composites are taken on the natural domain (`LinearPMap.compNat`).

## References

* [J. Weidmann, *Linear Operators in Hilbert Spaces*][weidmann_linear]
-/

@[expose] public section

open scoped LinearPMap

namespace LinearPMap

variable {𝕜 E F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]

/-- **Bounded perturbation.** For a bounded, everywhere-defined `A` and a densely defined `T`,
`(A + T)† = A† + T†`; in particular the adjoint domain is unchanged. -/
lemma adjoint_vadd [CompleteSpace E] [CompleteSpace F] {T : E →ₗ.[𝕜] F}
    (hT : Dense (T.domain : Set E)) (A : E →L[𝕜] F) :
    ((A : E →ₗ[𝕜] F) +ᵥ T)† = ((ContinuousLinearMap.adjoint A : F →L[𝕜] E) : F →ₗ[𝕜] E) +ᵥ T† := by
  have hAT : Dense (((A : E →ₗ[𝕜] F) +ᵥ T).domain : Set E) := hT
  have hle : ((ContinuousLinearMap.adjoint A : F →L[𝕜] E) : F →ₗ[𝕜] E) +ᵥ T† ≤
      ((A : E →ₗ[𝕜] F) +ᵥ T)† := by
    refine IsFormalAdjoint.le_adjoint hAT fun x y => ?_
    rw [vadd_apply, vadd_apply]
    simp only [ContinuousLinearMap.coe_coe, inner_add_left, inner_add_right,
      ContinuousLinearMap.adjoint_inner_right]
    rw [(adjoint_isFormalAdjoint hT).symm x y]
  refine (eq_of_le_of_domain_eq hle (le_antisymm hle.1 fun y hy => ?_)).symm
  refine mem_adjoint_domain_of_exists y ⟨((A : E →ₗ[𝕜] F) +ᵥ T)† ⟨y, hy⟩ -
    ContinuousLinearMap.adjoint A y, fun x => ?_⟩
  rw [inner_sub_left, (adjoint_isFormalAdjoint hAT) ⟨y, hy⟩ x, vadd_apply, inner_add_right,
    ContinuousLinearMap.adjoint_inner_left]
  simp

/-- **Adjoint of a composite, general inclusion.** For densely defined `S` with `S T` densely
defined (on its natural domain; then `T` is densely defined too), `T† S† ⊆ (S T)†`. -/
lemma adjoint_compNat_le [CompleteSpace E] [CompleteSpace F] {T : E →ₗ.[𝕜] F}
    {S : F →ₗ.[𝕜] G} (hS : Dense (S.domain : Set F)) (hST : Dense ((S.compNat T).domain : Set E)) :
    T†.compNat S† ≤ (S.compNat T)† := by
  have hT : Dense (T.domain : Set E) := hST.mono compNat_domain_le
  refine IsFormalAdjoint.le_adjoint hST fun x y => ?_
  rw [compNat_apply, compNat_apply]
  exact ((adjoint_isFormalAdjoint hS).symm ⟨_, compNat_apply_mem x⟩ ⟨_, compNat_domain_le y.2⟩).trans
    ((adjoint_isFormalAdjoint hT).symm ⟨_, compNat_domain_le x.2⟩ ⟨_, compNat_apply_mem y⟩)

/-- **Adjoint of a composite with a bounded left factor.** For a bounded, everywhere-defined `B`
and a densely defined `T`, `(B T)† = T† B†`, the right-hand side on its natural domain
`{y | B† y ∈ dom T†}`. -/
lemma adjoint_compPMap [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]
    {T : E →ₗ.[𝕜] F} (hT : Dense (T.domain : Set E)) (B : F →L[𝕜] G) :
    ((B : F →ₗ[𝕜] G).compPMap T)† =
      T†.compNat (((ContinuousLinearMap.adjoint B : G →L[𝕜] F) : G →ₗ[𝕜] F).toPMap ⊤) := by
  have hBT : Dense (((B : F →ₗ[𝕜] G).compPMap T).domain : Set E) := hT
  have hle : T†.compNat (((ContinuousLinearMap.adjoint B : G →L[𝕜] F) : G →ₗ[𝕜] F).toPMap ⊤) ≤
      ((B : F →ₗ[𝕜] G).compPMap T)† := by
    refine IsFormalAdjoint.le_adjoint hBT fun x y => ?_
    rw [compNat_apply, ← (adjoint_isFormalAdjoint hT).symm ⟨_, x.2⟩]
    simp only [LinearMap.compPMap_apply, ContinuousLinearMap.coe_coe]
    exact (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
  refine (eq_of_le_of_domain_eq hle (le_antisymm hle.1 fun y hy => ?_)).symm
  refine mem_compNat_toPMap_domain.mpr (mem_adjoint_domain_of_exists _
    ⟨((B : F →ₗ[𝕜] G).compPMap T)† ⟨y, hy⟩, fun x => ?_⟩)
  rw [(adjoint_isFormalAdjoint hBT) ⟨y, hy⟩ x, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.adjoint_inner_left]
  rfl

/-- **Adjoint of a composite with a bounded right factor, general inclusion**: `B† S† ⊆ (S B)†` for
a densely defined `S` and a bounded `B` with `S B` densely defined. -/
lemma compPMap_adjoint_le_adjoint_compNat_toPMap [CompleteSpace E] [CompleteSpace F]
    {S : E →ₗ.[𝕜] G} (hS : Dense (S.domain : Set E)) (B : F →L[𝕜] E)
    (hSB : Dense ((S.compNat ((B : F →ₗ[𝕜] E).toPMap ⊤)).domain : Set F)) :
    ((ContinuousLinearMap.adjoint B : E →L[𝕜] F) : E →ₗ[𝕜] F).compPMap S† ≤
      (S.compNat ((B : F →ₗ[𝕜] E).toPMap ⊤))† := by
  have h := adjoint_compNat_le (T := (B : F →ₗ[𝕜] E).toPMap ⊤) hS hSB
  rwa [show ((B : F →ₗ[𝕜] E).toPMap ⊤)† =
      ((ContinuousLinearMap.adjoint B : E →L[𝕜] F) : E →ₗ[𝕜] F).toPMap ⊤ from
    ContinuousLinearMap.toPMap_adjoint_eq_adjoint_toPMap_of_dense B (by simp),
    toPMap_compNat] at h

/-- **Adjoint of a composite with a bounded right factor.** Let `B` be bounded and `T` densely
defined with `T B` densely defined, and suppose `T` factors through `B` via a bounded `C`:
`T ⊆ T B C`. Then `(T B)† = B† T†`.

Without the factorisation only `B† T† ⊆ (T B)†` holds (this is `LinearPMap.adjoint_compNat_le`
combined with `ContinuousLinearMap.toPMap_adjoint_eq_adjoint_toPMap_of_dense`). The
hypothesis holds with `C = B⁻¹` for invertible `B`, and with `C = B†` for a partial isometry `B`
whose range projection `B B†` does not change `T`. -/
lemma adjoint_compNat_toPMap [CompleteSpace E] [CompleteSpace F] {T : E →ₗ.[𝕜] G}
    (hT : Dense (T.domain : Set E)) (B : F →L[𝕜] E)
    (hTB : Dense ((T.compNat ((B : F →ₗ[𝕜] E).toPMap ⊤)).domain : Set F)) (C : E →L[𝕜] F)
    (hBC : T ≤ T.compNat (((B ∘L C : E →L[𝕜] E) : E →ₗ[𝕜] E).toPMap ⊤)) :
    (T.compNat ((B : F →ₗ[𝕜] E).toPMap ⊤))† =
      ((ContinuousLinearMap.adjoint B : E →L[𝕜] F) : E →ₗ[𝕜] F).compPMap T† := by
  have hle : ((ContinuousLinearMap.adjoint B : E →L[𝕜] F) : E →ₗ[𝕜] F).compPMap T† ≤
      (T.compNat ((B : F →ₗ[𝕜] E).toPMap ⊤))† := by
    refine IsFormalAdjoint.le_adjoint hTB fun x y => ?_
    rw [compNat_apply, (adjoint_isFormalAdjoint hT).symm _ y]
    simp only [LinearMap.compPMap_apply, ContinuousLinearMap.coe_coe]
    exact (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
  refine (eq_of_le_of_domain_eq hle (le_antisymm hle.1 fun y hy => ?_)).symm
  refine mem_adjoint_domain_of_exists _ ⟨ContinuousLinearMap.adjoint C
    ((T.compNat ((B : F →ₗ[𝕜] E).toPMap ⊤))† ⟨y, hy⟩), fun u => ?_⟩
  -- the factorisation at the single vector `u`
  have hu : (B (C u), T u) ∈ T.graph :=
    (mem_graph_compNat_toPMap (g := T) (f := ((B ∘L C : E →L[𝕜] E) : E →ₗ[𝕜] E))).mp
      (le_graph_of_le hBC (T.mem_graph u))
  have hCu : C u ∈ (T.compNat ((B : F →ₗ[𝕜] E).toPMap ⊤)).domain :=
    mem_compNat_toPMap_domain.mpr (mem_domain_of_mem_graph hu)
  rw [ContinuousLinearMap.adjoint_inner_left,
    (adjoint_isFormalAdjoint hTB) ⟨y, hy⟩ ⟨C u, hCu⟩, compNat_apply]
  exact congrArg _ ((image_iff _).mpr hu).symm

/-! ### Closures of composites with bounded operators -/

/-- **`B T̄ ⊆ closure (B T)`** for a bounded `B` with `B T` closable. -/
lemma compPMap_closure_le {T : E →ₗ.[𝕜] F} (hT : T.IsClosable) (B : F →L[𝕜] G)
    (hBT : ((B : F →ₗ[𝕜] G).compPMap T).IsClosable) :
    (B : F →ₗ[𝕜] G).compPMap T.closure ≤ ((B : F →ₗ[𝕜] G).compPMap T).closure := by
  -- the closure of a graph is a limit argument
  refine le_of_le_graph fun ⟨x, z⟩ hz => ?_
  obtain ⟨y, hy, rfl⟩ := mem_graph_compPMap.mp hz
  rw [← hT.graph_closure_eq_closure_graph, ← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hy
  rw [← hBT.graph_closure_eq_closure_graph, ← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  exact map_mem_closure (f := fun p : E × F => (p.1, B p.2)) (by fun_prop) hy
    fun p hp => mem_graph_compPMap.mpr ⟨p.2, hp, rfl⟩

/-- A closed operator composed with a bounded right factor is closed. -/
lemma IsClosed.compNat_toPMap {T : E →ₗ.[𝕜] G} (hT : T.IsClosed) (B : F →L[𝕜] E) :
    (T.compNat ((B : F →ₗ[𝕜] E).toPMap ⊤)).IsClosed := by
  -- the graph is the preimage of the graph of `T` under `(x, z) ↦ (B x, z)`
  have h : ((T.compNat ((B : F →ₗ[𝕜] E).toPMap ⊤)).graph : Set (F × G)) =
      (fun p : F × G => (B p.1, p.2)) ⁻¹' T.graph :=
    Set.ext fun ⟨_, _⟩ => mem_graph_compNat_toPMap
  unfold LinearPMap.IsClosed
  rw [h]
  exact IsClosed.preimage (by fun_prop) hT

/-- **`closure (T B) ⊆ T̄ B`** for a closable `T` and a bounded `B`. -/
lemma closure_compNat_toPMap_le {T : E →ₗ.[𝕜] G} (hT : T.IsClosable) (B : F →L[𝕜] E) :
    (T.compNat ((B : F →ₗ[𝕜] E).toPMap ⊤)).closure ≤
      T.closure.compNat ((B : F →ₗ[𝕜] E).toPMap ⊤) := by
  have hc := hT.closure_isClosed.compNat_toPMap B
  have h := hc.isClosable.closure_mono (compNat_mono (le_closure T) le_rfl)
  rwa [hc.closure_eq] at h

/-- **Intertwining passes to closures**: if `B T ⊆ S C` for closable `T`, `S` and bounded `B`, `C`,
then `B T̄ ⊆ S̄ C`, since `B T̄ ⊆ closure (B T) ⊆ closure (S̄ C) = S̄ C`. -/
lemma compPMap_closure_le_closure_compNat_toPMap {E' : Type*} [NormedAddCommGroup E']
    [InnerProductSpace 𝕜 E'] {T : E →ₗ.[𝕜] F} {S : E' →ₗ.[𝕜] G} (hT : T.IsClosable)
    (hS : S.IsClosable) (B : F →L[𝕜] G) (C : E →L[𝕜] E')
    (h : (B : F →ₗ[𝕜] G).compPMap T ≤ S.compNat ((C : E →ₗ[𝕜] E').toPMap ⊤)) :
    (B : F →ₗ[𝕜] G).compPMap T.closure ≤ S.closure.compNat ((C : E →ₗ[𝕜] E').toPMap ⊤) := by
  have hc := hS.closure_isClosed.compNat_toPMap C
  have h' := h.trans (compNat_mono (le_closure S) le_rfl)
  calc (B : F →ₗ[𝕜] G).compPMap T.closure ≤ ((B : F →ₗ[𝕜] G).compPMap T).closure :=
        compPMap_closure_le hT B (hc.isClosable.leIsClosable h')
    _ ≤ (S.closure.compNat ((C : E →ₗ[𝕜] E').toPMap ⊤)).closure := hc.isClosable.closure_mono h'
    _ = _ := hc.closure_eq

end LinearPMap
