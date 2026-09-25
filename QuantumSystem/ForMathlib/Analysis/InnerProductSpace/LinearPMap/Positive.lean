/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Symmetric and positive unbounded operators

A partially defined operator `T` on an inner product space is *symmetric* when it is a formal
adjoint of itself, `⟪T x, y⟫ = ⟪x, T y⟫` on its domain (Mathlib's `T.IsFormalAdjoint T`), and
*positive* when it is moreover `0 ≤ re ⟪T x, x⟫` on its domain. This mirrors Mathlib's
`LinearMap.IsPositive` for everywhere-defined maps. Positivity does not include
self-adjointness; a *positive self-adjoint* operator is `IsSelfAdjoint T ∧ T.IsPositive`.

## Main definitions

* `LinearPMap.IsPositive` — `T` is symmetric and `0 ≤ re ⟪T x, x⟫` for `x ∈ dom T`.

## Main results

* `IsSelfAdjoint.isFormalAdjoint` — a self-adjoint operator is symmetric.
* `LinearPMap.IsFormalAdjoint.inner_map_self_im_eq_zero` — for symmetric `T`, `⟪x, T x⟫` is real.
* `LinearPMap.IsFormalAdjoint.inner_eq_of_mem_graph`, `LinearPMap.isFormalAdjoint_of_mem_graph` —
  symmetry in graph form.
-/

@[expose] public section

open RCLike
open scoped ComplexConjugate
open scoped LinearPMap

namespace LinearPMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- A partially defined operator is **positive** if it is symmetric and `0 ≤ re ⟪T x, x⟫` on its
domain. This does not include self-adjointness. -/
def IsPositive (T : E →ₗ.[𝕜] E) : Prop :=
  T.IsFormalAdjoint T ∧ ∀ x : T.domain, 0 ≤ re ⟪T x, x⟫

variable {T : E →ₗ.[𝕜] E}

/-- A positive operator is symmetric. -/
lemma IsPositive.isFormalAdjoint (hT : T.IsPositive) : T.IsFormalAdjoint T := hT.1

/-- For a positive operator, `0 ≤ re ⟪T x, x⟫`. -/
lemma IsPositive.re_inner_nonneg_left (hT : T.IsPositive) (x : T.domain) :
    0 ≤ re ⟪T x, x⟫ :=
  hT.2 x

/-- For a positive operator, `0 ≤ re ⟪x, T x⟫`. -/
lemma IsPositive.re_inner_nonneg_right (hT : T.IsPositive) (x : T.domain) :
    0 ≤ re ⟪(x : E), T x⟫ := by
  rw [← inner_conj_symm, conj_re]
  exact hT.2 x

/-- For a symmetric operator, `⟪x, T x⟫` is real. -/
lemma IsFormalAdjoint.inner_map_self_im_eq_zero (hT : T.IsFormalAdjoint T) (x : T.domain) :
    im ⟪(x : E), T x⟫ = 0 := by
  have h : conj ⟪(x : E), T x⟫ = ⟪(x : E), T x⟫ := by rw [inner_conj_symm, hT x x]
  exact conj_eq_iff_im.mp h

/-- Symmetry in graph form: for `(u, v)` and `(u', v')` in the graph of a symmetric operator,
`⟪v, u'⟫ = ⟪u, v'⟫`. -/
lemma IsFormalAdjoint.inner_eq_of_mem_graph (hT : T.IsFormalAdjoint T) {u v u' v' : E}
    (h : (u, v) ∈ T.graph) (h' : (u', v') ∈ T.graph) : ⟪v, u'⟫ = ⟪u, v'⟫ := by
  obtain ⟨p, rfl, rfl⟩ := (mem_graph_iff T).mp h
  obtain ⟨q, rfl, rfl⟩ := (mem_graph_iff T).mp h'
  exact hT p q

/-- Symmetry can be checked in graph form. -/
lemma isFormalAdjoint_of_mem_graph
    (h : ∀ u v u' v', (u, v) ∈ T.graph → (u', v') ∈ T.graph → ⟪v, u'⟫ = ⟪u, v'⟫) :
    T.IsFormalAdjoint T := fun x y => h _ _ _ _ (T.mem_graph x) (T.mem_graph y)

end LinearPMap

/-- A self-adjoint operator is symmetric. -/
lemma IsSelfAdjoint.isFormalAdjoint {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A) :
    A.IsFormalAdjoint A := by
  have h := LinearPMap.adjoint_isFormalAdjoint hA.dense_domain (T := A)
  rw [LinearPMap.isSelfAdjoint_def.mp hA] at h
  exact h
