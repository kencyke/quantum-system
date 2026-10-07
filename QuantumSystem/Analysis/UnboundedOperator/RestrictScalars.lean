/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.InnerProductSpace.StandardSubspace
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.LinearPMap.Positive
public import Mathlib.Topology.Algebra.Module.LinearPMap
public import QuantumSystem.ForMathlib.LinearAlgebra.LinearPMap
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.SemilinearIsometry

/-!
# Real-linear operators on complex Hilbert spaces

A complex Hilbert space `E` is a real Hilbert space for the inner product `re ⟪x, y⟫`, Mathlib's
scoped instance `ClosedSubmodule.instInnerProductSpaceReal` (activated by `open ClosedSubmodule`).
Conjugate-linear unbounded operators, such as Tomita operators, are treated here as real-linear
`LinearPMap`s that are semilinear for the complex conjugation, `LinearPMap.IsSemilinear
(starRingEnd ℂ)`; the real adjoint and closure are then Mathlib's, and composition is
`LinearPMap.compNat`.

## Main definitions

* `LinearPMap.IsSemilinear σ T`, `LinearPMap.IsSemilinear.toLinearPMap` — semilinearity of an
  `R`-linear partially defined map and its regrading as an `S`-linear one, defined for arbitrary
  rings in `QuantumSystem.ForMathlib.LinearAlgebra.LinearPMap`, together with their algebraic and
  topological properties (composition, closure, restriction of scalars).

## Main results

* `Submodule.adjoint_restrictScalars`, `LinearPMap.adjoint_restrictScalars` — the real adjoint of a
  complex operator is its complex adjoint.
* `LinearPMap.IsSemilinear.adjoint` — for the identity and the complex conjugation, semilinearity
  passes to the adjoint.
* `LinearPMap.IsSemilinear.adjoint_toLinearPMap`, `LinearPMap.IsSemilinear.isSelfAdjoint_toLinearPMap`,
  `LinearPMap.IsSemilinear.isPositive_toLinearPMap` — for complex Hilbert spaces, `toLinearPMap`
  transports adjoints, self-adjointness and positivity.

## Implementation notes

Complex-linear operators are spelled `E →ₗ.[ℂ] F` throughout the project; the real spelling
`E →ₗ.[ℝ] F` is reserved for conjugate-linear operators and the operators built from them. A
conjugate-linear operator cannot be an `E →ₗ.[ℂ] F`, and Mathlib's semilinear partial maps
`E →ₛₗ.[starRingEnd ℂ] F` have no graph, closure or adjoint. The bridge
`IsSemilinear.toLinearPMap` exists only to bring a complex-linear composite such as the modular
operator `S̄† S̄` back to `E →ₗ.[ℂ] F`, where the spectral calculus lives.

## TODO

Develop the graph, closure and adjoint of semilinear partial maps, and von Neumann's theorem for
them, so that a conjugate-linear operator is an `E →ₛₗ.[starRingEnd ℂ] F` and `S̄† S̄` is
complex-linear by `LinearPMap.compNat` directly. `IsSemilinear` and `toLinearPMap` would then
disappear; this needs a conjugate space, which Mathlib also lacks.
-/

@[expose] public section

open Complex ClosedSubmodule
open scoped ComplexConjugate LinearPMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

namespace Submodule

/-- For a complex submodule `g ⊆ E × F`, the real adjoint of `g` (for the inner products
`re ⟪·, ·⟫`) is its complex adjoint. -/
theorem adjoint_restrictScalars (g : Submodule ℂ (E × F)) :
    (g.restrictScalars ℝ).adjoint = g.adjoint.restrictScalars ℝ := by
  ext ⟨y, x⟩
  simp only [mem_adjoint_iff, restrictScalars_mem, inner_real_eq_re_inner]
  refine ⟨fun h a b hab => ?_, fun h a b hab => ?_⟩
  · have h₁ := h a b hab
    have h₂ := h (I • a) (I • b) (g.smul_mem I hab)
    simp only [inner_smul_left, conj_I, mul_re, neg_re, I_re, neg_im, I_im] at h₂
    apply Complex.ext <;> simp only [sub_re, sub_im, zero_re, zero_im] <;> linarith
  · simpa using congrArg re (h a b hab)

end Submodule

namespace LinearPMap

/-- The real adjoint of a densely defined complex operator is its complex adjoint. -/
theorem adjoint_restrictScalars [CompleteSpace E] {T : E →ₗ.[ℂ] F}
    (hT : Dense (T.domain : Set E)) : (T.restrictScalars ℝ)† = T†.restrictScalars ℝ := by
  refine eq_of_eq_graph ?_
  rw [adjoint_graph_eq_graph_adjoint (T := T.restrictScalars ℝ) hT,
    graph_restrictScalars, Submodule.adjoint_restrictScalars, ← adjoint_graph_eq_graph_adjoint hT,
    graph_restrictScalars]

variable {T : E →ₗ.[ℝ] F}

/-- The adjoint of a densely defined `σ`-semilinear operator is `σ`-semilinear, for an isometric
`σ : ℂ →+* ℂ`, that is, the identity or the complex conjugation
(`RingHom.eq_id_or_conj_of_isometric`). -/
lemma IsSemilinear.adjoint [CompleteSpace E] {σ : ℂ →+* ℂ} [RingHomIsometric σ]
    (hT : IsSemilinear σ T) (hd : Dense (T.domain : Set E)) : IsSemilinear σ T† := by
  have hσ : ∀ c, conj (σ (conj (σ c))) = c := by
    rcases RingHom.eq_id_or_conj_of_isometric σ with rfl | rfl <;> simp
  intro c y x h
  rw [adjoint_graph_eq_graph_adjoint hd, Submodule.mem_adjoint_iff] at h ⊢
  intro a b hab
  have := h _ _ (hT (conj (σ c)) a b hab)
  simp only [inner_real_eq_re_inner, inner_smul_left, inner_smul_right, conj_conj, hσ] at this ⊢
  exact this

/-- The complex adjoint of `hT.toLinearPMap` is the complex form of the real adjoint of `T`. -/
lemma IsSemilinear.adjoint_toLinearPMap [CompleteSpace E] (hT : IsSemilinear (RingHom.id ℂ) T)
    (hd : Dense (T.domain : Set E)) : hT.toLinearPMap† = (hT.adjoint hd).toLinearPMap := by
  refine restrictScalars_injective (R := ℝ) ?_
  rw [IsSemilinear.restrictScalars_toLinearPMap, ← adjoint_restrictScalars
    (by rwa [hT.coe_domain_toLinearPMap]), IsSemilinear.restrictScalars_toLinearPMap]

/-- A self-adjoint complex-linear real operator is self-adjoint as a complex operator. -/
lemma IsSemilinear.isSelfAdjoint_toLinearPMap [CompleteSpace E] {A : E →ₗ.[ℝ] E}
    (hA : IsSemilinear (RingHom.id ℂ) A) (hsa : IsSelfAdjoint A) :
    IsSelfAdjoint hA.toLinearPMap := by
  rw [isSelfAdjoint_def]
  refine restrictScalars_injective (R := ℝ) ?_
  rw [← adjoint_restrictScalars (by rw [hA.coe_domain_toLinearPMap]; exact hsa.dense_domain),
    IsSemilinear.restrictScalars_toLinearPMap]
  exact isSelfAdjoint_def.mp hsa

/-- A positive complex-linear real operator is positive as a complex operator. -/
lemma IsSemilinear.isPositive_toLinearPMap {A : E →ₗ.[ℝ] E} (hA : IsSemilinear (RingHom.id ℂ) A)
    (hpos : A.IsPositive) : hA.toLinearPMap.IsPositive := by
  refine ⟨isFormalAdjoint_of_mem_graph fun u v u' v' h h' => ?_, fun x => ?_⟩
  · rw [hA.mem_graph_toLinearPMap] at h h'
    have h₁ := hpos.1.inner_eq_of_mem_graph h h'
    have h₂ := hpos.1.inner_eq_of_mem_graph (hA I u v h) h'
    simp only [RingHom.id_apply, inner_real_eq_re_inner, inner_smul_left, conj_I, neg_mul, neg_re,
      mul_re, I_re, I_im, zero_mul, one_mul, zero_sub, neg_neg] at h₁ h₂
    exact Complex.ext h₁ h₂
  · obtain ⟨p, hp, hpx⟩ := (mem_graph_iff A).mp
      (hA.mem_graph_toLinearPMap.mp (hA.toLinearPMap.mem_graph x))
    have := hpos.2 p
    rw [inner_real_eq_re_inner, RCLike.re_to_real, hpx, hp] at this
    exact this

end LinearPMap
