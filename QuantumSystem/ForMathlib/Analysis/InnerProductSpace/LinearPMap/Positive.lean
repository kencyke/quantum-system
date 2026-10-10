/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.Positive

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

* `IsSelfAdjoint.isFormalAdjoint` — a self-adjoint operator is symmetric;
  `IsSelfAdjoint.eq_of_le` — and it has no proper symmetric extension.
* `LinearPMap.IsFormalAdjoint.inner_map_self_im_eq_zero` — for symmetric `T`, `⟪x, T x⟫` is real.
* `LinearPMap.IsFormalAdjoint.inner_eq_of_mem_graph`, `LinearPMap.isFormalAdjoint_of_mem_graph` —
  symmetry in graph form.
* `IsSelfAdjoint.toPMap`, `LinearMap.IsPositive.toPMap` — a bounded self-adjoint operator, and a
  positive everywhere-defined one, stay self-adjoint, respectively positive, as partially defined
  operators with domain `⊤`.
-/

@[expose] public section

open RCLike
open scoped ComplexConjugate InnerProductSpace
open scoped LinearPMap

namespace LinearPMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A partially defined operator is **positive** if it is symmetric and `0 ≤ re ⟪T x, x⟫` on its
domain. This does not include self-adjointness. -/
def IsPositive (T : E →ₗ.[𝕜] E) : Prop :=
  T.IsFormalAdjoint T ∧ ∀ x : T.domain, 0 ≤ re ⟪T x, x⟫_𝕜

variable {T : E →ₗ.[𝕜] E}

/-- A positive operator is symmetric. -/
lemma IsPositive.isFormalAdjoint (hT : T.IsPositive) : T.IsFormalAdjoint T := hT.1

/-- For a positive operator, `0 ≤ re ⟪T x, x⟫`. -/
lemma IsPositive.re_inner_nonneg_left (hT : T.IsPositive) (x : T.domain) :
    0 ≤ re ⟪T x, x⟫_𝕜 :=
  hT.2 x

/-- For a positive operator, `0 ≤ re ⟪x, T x⟫`. -/
lemma IsPositive.re_inner_nonneg_right (hT : T.IsPositive) (x : T.domain) :
    0 ≤ re ⟪(x : E), T x⟫_𝕜 := by
  rw [← inner_conj_symm, conj_re]
  exact hT.2 x

/-- For a symmetric operator, `⟪x, T x⟫` is real. -/
lemma IsFormalAdjoint.inner_map_self_im_eq_zero (hT : T.IsFormalAdjoint T) (x : T.domain) :
    im ⟪(x : E), T x⟫_𝕜 = 0 := by
  have h : conj ⟪(x : E), T x⟫_𝕜 = ⟪(x : E), T x⟫_𝕜 := by rw [inner_conj_symm, hT x x]
  exact conj_eq_iff_im.mp h

/-- Symmetry in graph form: for `(u, v)` and `(u', v')` in the graph of a symmetric operator,
`⟪v, u'⟫ = ⟪u, v'⟫`. -/
lemma IsFormalAdjoint.inner_eq_of_mem_graph (hT : T.IsFormalAdjoint T) {u v u' v' : E}
    (h : (u, v) ∈ T.graph) (h' : (u', v') ∈ T.graph) : ⟪v, u'⟫_𝕜 = ⟪u, v'⟫_𝕜 := by
  obtain ⟨p, rfl, rfl⟩ := (mem_graph_iff T).mp h
  obtain ⟨q, rfl, rfl⟩ := (mem_graph_iff T).mp h'
  exact hT p q

/-- Symmetry can be checked in graph form. -/
lemma isFormalAdjoint_of_mem_graph
    (h : ∀ u v u' v', (u, v) ∈ T.graph → (u', v') ∈ T.graph → ⟪v, u'⟫_𝕜 = ⟪u, v'⟫_𝕜) :
    T.IsFormalAdjoint T := fun x y => h _ _ _ _ (T.mem_graph x) (T.mem_graph y)

end LinearPMap

/-- A self-adjoint operator is symmetric. -/
lemma IsSelfAdjoint.isFormalAdjoint {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A) :
    A.IsFormalAdjoint A := by
  have h := LinearPMap.adjoint_isFormalAdjoint hA.dense_domain (T := A)
  rw [LinearPMap.isSelfAdjoint_def.mp hA] at h
  exact h

/-- **A self-adjoint operator has no proper symmetric extension**: if `A` is symmetric and extends
the self-adjoint `B`, then `A = B`, since `A ≤ B† = B`. -/
lemma IsSelfAdjoint.eq_of_le {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] {A B : E →ₗ.[𝕜] E} (hB : IsSelfAdjoint B)
    (hA : A.IsFormalAdjoint A) (hle : B ≤ A) : A = B := by
  have hform : B.IsFormalAdjoint A := fun x y => by
    rw [hle.2 (y := ⟨x, hle.1 x.2⟩) rfl]
    exact hA ⟨x, hle.1 x.2⟩ y
  refine le_antisymm ?_ hle
  calc A ≤ B† := hform.le_adjoint hB.dense_domain
    _ = B := hB

/-- A bounded self-adjoint operator, as a partially defined operator with domain `⊤`, is
self-adjoint: its adjoint is `y†.toPMap ⊤ = y.toPMap ⊤`
(`ContinuousLinearMap.toPMap_adjoint_eq_adjoint_toPMap_of_dense`). -/
lemma IsSelfAdjoint.toPMap {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] {y : E →L[𝕜] E} (hy : IsSelfAdjoint y) :
    IsSelfAdjoint ((y : E →ₗ[𝕜] E).toPMap ⊤) := by
  rw [LinearPMap.isSelfAdjoint_def,
    ContinuousLinearMap.toPMap_adjoint_eq_adjoint_toPMap_of_dense y (by simp),
    ← ContinuousLinearMap.star_eq_adjoint, hy.star_eq]

/-- A positive everywhere-defined operator, as a partially defined operator with domain `⊤`, is
positive. -/
lemma LinearMap.IsPositive.toPMap {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {y : E →ₗ[𝕜] E} (hy : y.IsPositive) : (y.toPMap ⊤).IsPositive :=
  ⟨fun a b => hy.isSymmetric a b, fun a => hy.re_inner_nonneg_left a⟩
