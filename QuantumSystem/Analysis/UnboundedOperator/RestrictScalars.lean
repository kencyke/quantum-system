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
* `LinearPMap.IsSemilinear.inner_eq_of_mem_graph_adjoint` — the complex adjoint identity
  `⟪ψ, u⟫ = σ ⟪φ, v⟫` for `(u, v) ∈ graph T` and `(φ, ψ) ∈ graph T†`.
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

## Notation

`V ⬝ T` and `T ⬝ V` compose a bounded complex-linear map `V` with a real-linear operator `T`
(`LinearMap.compPMap` and `LinearPMap.compNat` along `(V : E →ₗ[ℂ] F).restrictScalars ℝ`), so
the intertwining `V T ⊆ T′ V` reads `V ⬝ T ≤ T′ ⬝ V`. Activate them with
`open scoped LinearPMap`.
-/

@[expose] public section

open Complex ClosedSubmodule
open scoped ComplexConjugate LinearPMap InnerProductSpace

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

/-! ### Bounded complex-linear maps composed with real-linear operators -/

/-- `V ⬝ T`: the real-linear operator `T` followed by the bounded complex-linear map `V`, the
real-linear operator `x ↦ V (T x)` on `dom T` (`LinearMap.compPMap` with
`(V : E →ₗ[ℂ] F).restrictScalars ℝ`). Together with `T ⬝ V` it spells the intertwining relation
`V T ⊆ T′ V` as `V ⬝ T ≤ T′ ⬝ V`. -/
scoped notation:70 V:71 " ⬝ " T:70 =>
  LinearMap.compPMap (LinearMap.restrictScalars ℝ (ContinuousLinearMap.toLinearMap V)) T

/-- `T ⬝ V`: the bounded complex-linear map `V` followed by the real-linear operator `T`, the
real-linear operator `x ↦ T (V x)` on `V⁻¹ (dom T)` (`LinearPMap.compNat` with the everywhere
defined `(V : E →ₗ[ℂ] F).restrictScalars ℝ`). -/
scoped notation:70 T:71 " ⬝ " V:70 =>
  LinearPMap.compNat T
    (LinearMap.toPMap (LinearMap.restrictScalars ℝ (ContinuousLinearMap.toLinearMap V)) ⊤)

open Lean PrettyPrinter Delaborator SubExpr in
/-- Delaborator displaying `LinearMap.compPMap ((V : E →ₗ[ℂ] F).restrictScalars ℝ) T` as
`V ⬝ T`. -/
@[scoped delab app.LinearMap.compPMap]
meta def delabCompPMapRestrictScalars : Delab := do
  let e ← getExpr
  guard <| e.isAppOfArity ``LinearMap.compPMap 21
  let g := e.getArg! 19
  guard <| g.isAppOfArity ``LinearMap.restrictScalars 14 && (g.getArg! 0).isConstOf ``Real
  guard <| (g.getArg! 13).isAppOfArity ``ContinuousLinearMap.toLinearMap 14
  let V ← withNaryArg 19 <| withNaryArg 13 <| withNaryArg 13 delab
  let T ← withNaryArg 20 delab
  `($V ⬝ $T)

open Lean PrettyPrinter Delaborator SubExpr in
/-- Delaborator displaying `LinearPMap.compNat T (((V : E →ₗ[ℂ] F).restrictScalars ℝ).toPMap ⊤)`
as `T ⬝ V`. -/
@[scoped delab app.LinearPMap.compNat]
meta def delabCompNatRestrictScalars : Delab := do
  let e ← getExpr
  guard <| e.isAppOfArity ``LinearPMap.compNat 21
  let s := e.getArg! 20
  guard <| s.isAppOfArity ``LinearMap.toPMap 13 && (s.getArg! 12).isAppOf ``Top.top
  let g := s.getArg! 11
  guard <| g.isAppOfArity ``LinearMap.restrictScalars 14 && (g.getArg! 0).isConstOf ``Real
  guard <| (g.getArg! 13).isAppOfArity ``ContinuousLinearMap.toLinearMap 14
  let T ← withNaryArg 19 delab
  let V ← withNaryArg 20 <| withNaryArg 11 <| withNaryArg 13 <| withNaryArg 13 delab
  `($T ⬝ $V)

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

/-- **The complex adjoint identity** for a densely defined `σ`-semilinear `T`, `σ` the identity or
the complex conjugation: the real adjoint identity `re ⟪ψ, u⟫ = re ⟪φ, v⟫` for `(u, v) ∈ graph T`
and `(φ, ψ) ∈ graph T†` upgrades to `⟪ψ, u⟫ = σ ⟪φ, v⟫`, by applying it also to `(i u, σ(i) v)`. -/
lemma IsSemilinear.inner_eq_of_mem_graph_adjoint [CompleteSpace E] {σ : ℂ →+* ℂ}
    [RingHomIsometric σ] (hT : IsSemilinear σ T) (hd : Dense (T.domain : Set E)) {u ψ : E}
    {v φ : F} (huv : (u, v) ∈ T.graph) (h : (φ, ψ) ∈ T†.graph) :
    ⟪ψ, u⟫_ℂ = σ ⟪φ, v⟫_ℂ := by
  rw [adjoint_graph_eq_graph_adjoint hd, Submodule.mem_adjoint_iff] at h
  have h₁ := h _ _ huv
  have h₂ := h _ _ (hT I u v huv)
  rw [sub_eq_zero, inner_real_eq_re_inner, inner_real_eq_re_inner] at h₁ h₂
  dsimp only at h₁ h₂
  rw [← inner_conj_symm ψ u, ← inner_conj_symm φ v]
  rcases RingHom.eq_id_or_conj_of_isometric σ with rfl | rfl
  · simp only [RingHom.id_apply, inner_smul_left, conj_I, neg_mul, neg_re, mul_re, I_re, I_im,
      zero_mul, one_mul, zero_sub, neg_inj] at h₂
    refine Complex.ext ?_ ?_
    · rw [RingHom.id_apply, conj_re, conj_re]
      exact h₁.symm
    · rw [RingHom.id_apply, conj_im, conj_im, h₂]
  · simp only [conj_I, inner_smul_left, conj_neg_I, mul_re, neg_re, neg_im, I_re, I_im, zero_mul,
      one_mul, zero_sub, neg_zero] at h₂
    refine Complex.ext ?_ ?_
    · rw [conj_conj, conj_re]
      exact h₁.symm
    · rw [conj_conj, conj_im]
      linarith

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
