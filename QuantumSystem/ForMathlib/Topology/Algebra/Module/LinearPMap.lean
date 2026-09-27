/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
public import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# Eigenspaces of closed operators; graph maps and closures

For a partially defined operator `T` and a scalar `c`, the eigenspace `ker (T - c)` is Mathlib's
kernel `LinearPMap.ker` of `-c + T` (`-(c • LinearMap.id) +ᵥ T`): the vectors `u ∈ dom T` with
`T u = c u`. When `T` is closed it is a closed submodule, and it is bundled as a
`ClosedSubmodule` so that, in a Hilbert space, its orthogonal projection is available without
further hypotheses.

## Main definitions

* `LinearPMap.IsClosed.eigenspace hT c` — the eigenspace `ker (T - c)` of a closed operator, as a
  closed submodule.

## Main results

* `LinearPMap.IsClosed.mem_eigenspace_iff` — `u ∈ ker (T - c) ↔ (u, c u) ∈ graph T`.
* `LinearPMap.IsClosed.toSubmodule_eigenspace_zero` — for `c = 0` it is `LinearPMap.ker T`.
* `LinearPMap.mem_graph_closure_of_mapsTo` — a continuous map carrying the graph of `T₁` into the
  graph of a closable `T₂` carries the graph of `T̄₁` into that of `T̄₂`.
-/

@[expose] public section

namespace LinearPMap

variable {R E : Type*} [CommRing R] [AddCommGroup E] [Module R E] {T : E →ₗ.[R] E}

/-- `u ∈ ker (T - c)` iff `(u, c u)` lies in the graph of `T`. -/
lemma mem_ker_neg_smul_id_vadd_iff (c : R) {u : E} :
    u ∈ ker ((-(c • LinearMap.id) : E →ₗ[R] E) +ᵥ T) ↔ (u, c • u) ∈ T.graph := by
  rw [mem_ker_iff, mem_graph_iff]
  constructor
  · rintro ⟨y, rfl, hy⟩
    refine ⟨y, rfl, ?_⟩
    rw [vadd_apply, LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.id_apply] at hy
    exact (neg_add_eq_zero.mp hy).symm
  · rintro ⟨y, rfl, hy⟩
    refine ⟨y, rfl, ?_⟩
    rw [vadd_apply, LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.id_apply]
    exact neg_add_eq_zero.mpr hy.symm

variable [TopologicalSpace E] [ContinuousConstSMul R E]

/-- The **eigenspace** `ker (T - c)` of a closed operator `T`: the vectors `u ∈ dom T` with
`T u = c u`, as a closed submodule. Its underlying submodule is Mathlib's kernel of
`-(c • LinearMap.id) +ᵥ T`. -/
def IsClosed.eigenspace (hT : T.IsClosed) (c : R) : ClosedSubmodule R E where
  toSubmodule := ker ((-(c • LinearMap.id) : E →ₗ[R] E) +ᵥ T)
  isClosed' := by
    have : (ker ((-(c • LinearMap.id) : E →ₗ[R] E) +ᵥ T) : Set E) =
        (fun u => (u, c • u)) ⁻¹' T.graph := by
      ext u
      exact mem_ker_neg_smul_id_vadd_iff c
    change _root_.IsClosed (ker ((-(c • LinearMap.id) : E →ₗ[R] E) +ᵥ T) : Set E)
    rw [this]
    exact hT.preimage (continuous_id.prodMk (continuous_const_smul c))

variable (hT : T.IsClosed)

/-- `u` lies in the eigenspace `ker (T - c)` iff `(u, c u)` lies in the graph of `T`. -/
lemma IsClosed.mem_eigenspace_iff {c : R} {u : E} :
    u ∈ hT.eigenspace c ↔ (u, c • u) ∈ T.graph :=
  mem_ker_neg_smul_id_vadd_iff c

/-- The eigenspace for `0` is the kernel of `T`. -/
lemma IsClosed.toSubmodule_eigenspace_zero : (hT.eigenspace 0).toSubmodule = T.ker := by
  change ker ((-((0 : R) • LinearMap.id) : E →ₗ[R] E) +ᵥ T) = T.ker
  rw [zero_smul, neg_zero, zero_vadd]

section Closure

variable {R E F E' F' : Type*} [CommRing R] [TopologicalSpace R]
  [AddCommGroup E] [Module R E] [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul R E]
  [AddCommGroup F] [Module R F] [TopologicalSpace F] [ContinuousAdd F] [ContinuousSMul R F]
  [AddCommGroup E'] [Module R E'] [TopologicalSpace E'] [ContinuousAdd E'] [ContinuousSMul R E']
  [AddCommGroup F'] [Module R F'] [TopologicalSpace F'] [ContinuousAdd F'] [ContinuousSMul R F']
  {T₁ : E →ₗ.[R] F} {T₂ : E' →ₗ.[R] F'}

/-- A continuous map carrying the graph of `T₁` into the graph of a closable `T₂` carries the graph
of the closure `T̄₁` into that of `T̄₂`. -/
lemma mem_graph_closure_of_mapsTo (h₂ : T₂.IsClosable) {f : E × F → E' × F'} (hf : Continuous f)
    (h : ∀ p ∈ T₁.graph, f p ∈ T₂.graph) {p : E × F} (hp : p ∈ T₁.closure.graph) :
    f p ∈ T₂.closure.graph := by
  rw [← h₂.graph_closure_eq_closure_graph, ← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  by_cases h₁ : T₁.IsClosable
  · rw [← h₁.graph_closure_eq_closure_graph, ← SetLike.mem_coe,
      Submodule.topologicalClosure_coe] at hp
    exact map_mem_closure hf hp h
  · rw [closure_def' h₁] at hp
    exact subset_closure (h p hp)

end Closure

end LinearPMap
