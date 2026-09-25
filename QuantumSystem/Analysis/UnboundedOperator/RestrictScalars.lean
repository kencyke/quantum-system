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

/-!
# Real-linear operators on complex Hilbert spaces

A complex Hilbert space `E` is a real Hilbert space for the inner product `re ⟪x, y⟫`, Mathlib's
scoped instance `ClosedSubmodule.instInnerProductSpaceReal` (activated by `open ClosedSubmodule`).
Conjugate-linear unbounded operators, such as Tomita operators, are treated here as real-linear
`LinearPMap`s satisfying the predicate `LinearPMap.IsConjLinear`; the real adjoint and closure are
then Mathlib's, and composition is `LinearPMap.compNat`.

## Main definitions

* `LinearPMap.IsConjLinear T` — the graph of a real-linear `T` is invariant under
  `(x, y) ↦ (c x, c̄ y)` for every `c : ℂ`.
* `LinearPMap.IsComplexLinear T` — the graph is invariant under `(x, y) ↦ (c x, c y)`.
* `LinearPMap.IsComplexLinear.graphComplex` / `LinearPMap.IsComplexLinear.toComplex` — the graph of
  a complex-linear real `LinearPMap` as a complex submodule, and the operator as a complex one.

## Main results

* `LinearPMap.isClosed_restrictScalars_iff`, `LinearPMap.isClosable_restrictScalars_iff`,
  `LinearPMap.closure_restrictScalars`, `LinearPMap.topologicalClosure_graph_restrictScalars` —
  restricting scalars does not change the graph as a set, so closedness, closability and the
  closure are unaffected (for any rings `R`, `S`).
* `Submodule.adjoint_restrictScalars`, `LinearPMap.adjoint_restrictScalars` — the real adjoint of a
  complex operator is its complex adjoint.
* `LinearPMap.isComplexLinear_restrictScalars` — a complex operator is complex-linear as a real one;
  `LinearPMap.toComplex_restrictScalars` and `LinearPMap.IsComplexLinear.restrictScalars_toComplex`
  say that `toComplex` and `restrictScalars ℝ` are mutually inverse, with the same domain
  (`LinearPMap.IsComplexLinear.coe_domain_toComplex`).
* `LinearPMap.IsConjLinear.closure`, `LinearPMap.IsConjLinear.adjoint`, and the same for
  `IsComplexLinear` — both properties pass to the closure and the adjoint.
* `LinearPMap.IsConjLinear.compNat` — a composite of two conjugate-linear operators is
  complex-linear.
* `LinearPMap.IsComplexLinear.restrictScalars_toComplex`, `LinearPMap.IsComplexLinear.adjoint_toComplex`,
  `LinearPMap.IsComplexLinear.isSelfAdjoint_toComplex`,
  `LinearPMap.IsComplexLinear.isPositive_toComplex` — `toComplex` recovers the operator and
  transports adjoints, self-adjointness and positivity.
-/

@[expose] public section

namespace LinearPMap

section Topology

variable {R S E F : Type*} [CommRing R] [CommRing S] [SMul R S]
  [AddCommGroup E] [Module R E] [Module S E] [IsScalarTower R S E]
  [AddCommGroup F] [Module R F] [Module S F] [IsScalarTower R S F]
  [TopologicalSpace E] [TopologicalSpace F] {T : E →ₗ.[S] F}

/-- `T.restrictScalars R` is closed iff `T` is. -/
@[simp]
lemma isClosed_restrictScalars_iff : (T.restrictScalars R).IsClosed ↔ T.IsClosed := by
  rw [IsClosed, IsClosed, graph_restrictScalars, Submodule.coe_restrictScalars]

variable [ContinuousAdd E] [ContinuousAdd F]
  [TopologicalSpace R] [ContinuousSMul R E] [ContinuousSMul R F]
  [TopologicalSpace S] [ContinuousSMul S E] [ContinuousSMul S F]

/-- The closure of the graph commutes with restriction of scalars. -/
lemma topologicalClosure_graph_restrictScalars :
    (T.restrictScalars R).graph.topologicalClosure =
      T.graph.topologicalClosure.restrictScalars R := by
  refine SetLike.coe_injective ?_
  rw [Submodule.topologicalClosure_coe, Submodule.coe_restrictScalars,
    Submodule.topologicalClosure_coe, graph_restrictScalars, Submodule.coe_restrictScalars]

/-- `T.restrictScalars R` is closable iff `T` is. -/
@[simp]
lemma isClosable_restrictScalars_iff : (T.restrictScalars R).IsClosable ↔ T.IsClosable := by
  refine ⟨fun ⟨T', hT'⟩ => ?_, fun ⟨T', hT'⟩ => ⟨T'.restrictScalars R, ?_⟩⟩
  · refine ⟨T.graph.topologicalClosure.toLinearPMap, (Submodule.toLinearPMap_graph_eq _ ?_).symm⟩
    intro x hx hx0
    have : x ∈ T'.graph := by
      rw [← hT', topologicalClosure_graph_restrictScalars]
      exact hx
    exact T'.graph_fst_eq_zero_snd this hx0
  · rw [topologicalClosure_graph_restrictScalars, hT', graph_restrictScalars]

/-- The closure commutes with restriction of scalars. -/
lemma closure_restrictScalars : (T.restrictScalars R).closure = T.closure.restrictScalars R := by
  by_cases hT : T.IsClosable
  · refine eq_of_eq_graph ?_
    rw [← (isClosable_restrictScalars_iff.mpr hT).graph_closure_eq_closure_graph,
      topologicalClosure_graph_restrictScalars, hT.graph_closure_eq_closure_graph,
      graph_restrictScalars]
  · rw [closure_def' hT, closure_def' (mt isClosable_restrictScalars_iff.mp hT)]

end Topology

end LinearPMap

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

/-- A real-linear partially defined operator is **conjugate-linear** if its graph is invariant
under `(x, y) ↦ (c x, c̄ y)` for every `c : ℂ`: `c x ∈ dom T` and `T (c x) = c̄ T x`. -/
def IsConjLinear (T : E →ₗ.[ℝ] F) : Prop :=
  ∀ (c : ℂ) (x : E) (y : F), (x, y) ∈ T.graph → (c • x, conj c • y) ∈ T.graph

/-- A real-linear partially defined operator is **complex-linear** if its graph is invariant
under `(x, y) ↦ (c x, c y)` for every `c : ℂ`: `c x ∈ dom T` and `T (c x) = c T x`. -/
def IsComplexLinear (T : E →ₗ.[ℝ] F) : Prop :=
  ∀ (c : ℂ) (x : E) (y : F), (x, y) ∈ T.graph → (c • x, c • y) ∈ T.graph

variable {T : E →ₗ.[ℝ] F}

/-- A complex operator is complex-linear as a real operator. -/
lemma isComplexLinear_restrictScalars (T : E →ₗ.[ℂ] F) :
    IsComplexLinear (T.restrictScalars ℝ) := fun c x y h => by
  rw [mem_graph_restrictScalars] at h ⊢
  exact T.graph.smul_mem c h

/-- The closure of a conjugate-linear operator is conjugate-linear. -/
lemma IsConjLinear.closure (hT : IsConjLinear T) : IsConjLinear T.closure := by
  by_cases hc : T.IsClosable
  · intro c x y h
    rw [← hc.graph_closure_eq_closure_graph] at h ⊢
    exact map_mem_closure (f := fun p : E × F => (c • p.1, conj c • p.2)) (by fun_prop) h
      fun p hp => hT c p.1 p.2 hp
  · rwa [closure_def' hc]

/-- The closure of a complex-linear operator is complex-linear. -/
lemma IsComplexLinear.closure (hT : IsComplexLinear T) : IsComplexLinear T.closure := by
  by_cases hc : T.IsClosable
  · intro c x y h
    rw [← hc.graph_closure_eq_closure_graph] at h ⊢
    exact map_mem_closure (f := fun p : E × F => (c • p.1, c • p.2)) (by fun_prop) h
      fun p hp => hT c p.1 p.2 hp
  · rwa [closure_def' hc]

/-- The adjoint of a densely defined conjugate-linear operator is conjugate-linear. -/
lemma IsConjLinear.adjoint [CompleteSpace E] (hT : IsConjLinear T)
    (hd : Dense (T.domain : Set E)) : IsConjLinear T† := fun c y x h => by
  rw [adjoint_graph_eq_graph_adjoint hd, Submodule.mem_adjoint_iff] at h ⊢
  intro a b hab
  have := h (c • a) (conj c • b) (hT c a b hab)
  simp only [inner_real_eq_re_inner, inner_smul_left, inner_smul_right, conj_conj] at this ⊢
  exact this

/-- The adjoint of a densely defined complex-linear operator is complex-linear. -/
lemma IsComplexLinear.adjoint [CompleteSpace E] (hT : IsComplexLinear T)
    (hd : Dense (T.domain : Set E)) : IsComplexLinear T† := fun c y x h => by
  rw [adjoint_graph_eq_graph_adjoint hd, Submodule.mem_adjoint_iff] at h ⊢
  intro a b hab
  have := h (conj c • a) (conj c • b) (hT (conj c) a b hab)
  simp only [inner_real_eq_re_inner, inner_smul_left, inner_smul_right, conj_conj] at this ⊢
  exact this

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]

/-- A composite of two conjugate-linear operators is complex-linear. -/
lemma IsConjLinear.compNat {S : F →ₗ.[ℝ] G} (hS : IsConjLinear S) (hT : IsConjLinear T) :
    IsComplexLinear (S.compNat T) := fun c x z h => by
  obtain ⟨y, hxy, hyz⟩ := mem_graph_compNat.mp h
  have := hS (conj c) _ _ hyz
  rw [conj_conj] at this
  exact mem_graph_compNat.mpr ⟨_, hT c x y hxy, this⟩

/-- A composite of two complex-linear operators is complex-linear. -/
lemma IsComplexLinear.compNat {S : F →ₗ.[ℝ] G} (hS : IsComplexLinear S)
    (hT : IsComplexLinear T) : IsComplexLinear (S.compNat T) := fun c x z h => by
  obtain ⟨y, hxy, hyz⟩ := mem_graph_compNat.mp h
  exact mem_graph_compNat.mpr ⟨_, hT c x y hxy, hS c _ _ hyz⟩

/-- The graph of a complex-linear real operator, as a complex submodule. -/
def IsComplexLinear.graphComplex (hT : IsComplexLinear T) : Submodule ℂ (E × F) where
  carrier := T.graph
  add_mem' := T.graph.add_mem
  zero_mem' := T.graph.zero_mem
  smul_mem' c p hp := hT c p.1 p.2 hp

/-- A complex-linear real operator, regarded as a complex operator with the same graph. -/
noncomputable def IsComplexLinear.toComplex (hT : IsComplexLinear T) : E →ₗ.[ℂ] F :=
  hT.graphComplex.toLinearPMap

/-- The graph of `hT.toComplex` is the graph of `T`. -/
@[simp]
lemma IsComplexLinear.mem_graph_toComplex (hT : IsComplexLinear T) {p : E × F} :
    p ∈ hT.toComplex.graph ↔ p ∈ T.graph := by
  rw [IsComplexLinear.toComplex, Submodule.toLinearPMap_graph_eq]
  · rfl
  · exact fun x hx hx0 => T.graph_fst_eq_zero_snd hx hx0

/-- Regarding `hT.toComplex` as a real operator recovers `T`. -/
@[simp]
lemma IsComplexLinear.restrictScalars_toComplex (hT : IsComplexLinear T) :
    hT.toComplex.restrictScalars ℝ = T :=
  eq_of_eq_graph (Submodule.ext fun _ => mem_graph_restrictScalars.trans hT.mem_graph_toComplex)

/-- `toComplex` inverts restriction of scalars: a complex operator regarded as a real one and back
is itself. -/
@[simp]
lemma toComplex_restrictScalars (T : E →ₗ.[ℂ] F) :
    (isComplexLinear_restrictScalars T).toComplex = T :=
  restrictScalars_injective (R := ℝ) (IsComplexLinear.restrictScalars_toComplex _)

/-- The domain of `hT.toComplex` is the domain of `T`. -/
lemma IsComplexLinear.coe_domain_toComplex (hT : IsComplexLinear T) :
    (hT.toComplex.domain : Set E) = T.domain := by
  conv_rhs => rw [← hT.restrictScalars_toComplex]
  rfl

/-- The complex adjoint of `hT.toComplex` is the complex form of the real adjoint of `T`. -/
lemma IsComplexLinear.adjoint_toComplex [CompleteSpace E] (hT : IsComplexLinear T)
    (hd : Dense (T.domain : Set E)) : hT.toComplex† = (hT.adjoint hd).toComplex := by
  refine restrictScalars_injective (R := ℝ) ?_
  rw [IsComplexLinear.restrictScalars_toComplex, ← adjoint_restrictScalars
    (by rwa [hT.coe_domain_toComplex]), IsComplexLinear.restrictScalars_toComplex]

/-- A self-adjoint complex-linear real operator is self-adjoint as a complex operator. -/
lemma IsComplexLinear.isSelfAdjoint_toComplex [CompleteSpace E] {A : E →ₗ.[ℝ] E}
    (hA : IsComplexLinear A) (hsa : IsSelfAdjoint A) : IsSelfAdjoint hA.toComplex := by
  rw [isSelfAdjoint_def]
  refine restrictScalars_injective (R := ℝ) ?_
  rw [← adjoint_restrictScalars (by rw [hA.coe_domain_toComplex]; exact hsa.dense_domain),
    IsComplexLinear.restrictScalars_toComplex]
  exact isSelfAdjoint_def.mp hsa

/-- A positive complex-linear real operator is positive as a complex operator. -/
lemma IsComplexLinear.isPositive_toComplex {A : E →ₗ.[ℝ] E} (hA : IsComplexLinear A)
    (hpos : A.IsPositive) : hA.toComplex.IsPositive := by
  refine ⟨isFormalAdjoint_of_mem_graph fun u v u' v' h h' => ?_, fun x => ?_⟩
  · rw [hA.mem_graph_toComplex] at h h'
    have h₁ := hpos.1.inner_eq_of_mem_graph h h'
    have h₂ := hpos.1.inner_eq_of_mem_graph (hA I u v h) h'
    simp only [inner_real_eq_re_inner, inner_smul_left, conj_I, neg_mul, neg_re, mul_re, I_re,
      I_im, zero_mul, one_mul, zero_sub, neg_neg] at h₁ h₂
    exact Complex.ext h₁ h₂
  · obtain ⟨p, hp, hpx⟩ := (mem_graph_iff A).mp
      (hA.mem_graph_toComplex.mp (hA.toComplex.mem_graph x))
    have := hpos.2 p
    rw [inner_real_eq_re_inner, RCLike.re_to_real, hpx, hp] at this
    exact this

end LinearPMap
