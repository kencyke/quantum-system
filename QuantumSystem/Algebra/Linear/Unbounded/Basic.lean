/-
Copyright (c) 2026 QuantumSystem Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuantumSystem Contributors
-/
module

public import Mathlib.LinearAlgebra.LinearPMap
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Densely Defined Linear Maps

This file develops the theory of densely defined linear maps on Hilbert spaces,
which forms the foundation for unbounded operator theory.

## Main definitions

* `DenselyDefinedLinearMap`: A linear map defined on a dense submodule
* `DenselyDefinedLinearMap.graph`: The graph of a densely defined linear map

## Main results

* Properties of densely defined linear maps
* Extension properties

## Implementation notes

We build on Mathlib's `LinearPMap` (partially defined linear maps) and add the
density condition on the domain. This is the standard approach for unbounded
operator theory in functional analysis.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*][reed1980]
* [Kato, *Perturbation Theory for Linear Operators*][kato1995]
-/

@[expose] public section

open Submodule in
/-- A densely defined linear map from `E` to `F` is a linear map defined on a
dense submodule of `E`. This is the basic structure for unbounded operators.

For Hilbert spaces, this is typically denoted as `T : dom(T) → H` where `dom(T)`
is a dense subspace. -/
structure DenselyDefinedLinearMap (R : Type*) [Ring R] (E : Type*) [AddCommGroup E] [Module R E]
    [TopologicalSpace E] (F : Type*) [AddCommGroup F] [Module R F] extends E →ₗ.[R] F where
  /-- The domain is dense in E -/
  dense_domain : Dense (domain : Set E)

@[inherit_doc] notation:25 E " →ₗᴰ.[" R:25 "] " F:0 => DenselyDefinedLinearMap R E F

namespace DenselyDefinedLinearMap

variable {R : Type*} [Ring R]
variable {E : Type*} [AddCommGroup E] [Module R E] [TopologicalSpace E]
variable {F : Type*} [AddCommGroup F] [Module R F]
variable {G : Type*} [AddCommGroup G] [Module R G]

section Basic

/-- The domain of a densely defined linear map as a submodule (alias for `domain`). -/
abbrev dom (T : E →ₗᴰ.[R] F) : Submodule R E := T.toLinearPMap.domain

/-- Apply a densely defined linear map to an element of its domain. -/
@[coe]
def toFun' (T : E →ₗᴰ.[R] F) : T.dom → F := T.toLinearPMap.toFun

instance : CoeFun (E →ₗᴰ.[R] F) fun T : E →ₗᴰ.[R] F => T.dom → F :=
  ⟨toFun'⟩

@[simp]
theorem toFun_eq_coe (T : E →ₗᴰ.[R] F) (x : T.dom) : T.toLinearPMap.toFun x = T x := rfl

/-- The underlying `LinearPMap`. -/
abbrev toLinearPMap' (T : E →ₗᴰ.[R] F) : E →ₗ.[R] F := T.toLinearPMap

theorem dense_dom (T : E →ₗᴰ.[R] F) : Dense (T.dom : Set E) := T.dense_domain

@[simp]
theorem map_zero (T : E →ₗᴰ.[R] F) : T 0 = 0 := T.toLinearPMap.map_zero

theorem map_add (T : E →ₗᴰ.[R] F) (x y : T.dom) : T (x + y) = T x + T y :=
  T.toLinearPMap.map_add x y

theorem map_neg (T : E →ₗᴰ.[R] F) (x : T.dom) : T (-x) = -T x :=
  T.toLinearPMap.map_neg x

theorem map_sub (T : E →ₗᴰ.[R] F) (x y : T.dom) : T (x - y) = T x - T y :=
  T.toLinearPMap.map_sub x y

theorem map_smul (T : E →ₗᴰ.[R] F) (c : R) (x : T.dom) : T (c • x) = c • T x :=
  T.toLinearPMap.map_smul c x

/-- Two densely defined linear maps are equal if they have the same domain and
agree on all elements of the domain. -/
@[ext (iff := false)]
theorem ext {T S : E →ₗᴰ.[R] F} (h_dom : T.dom = S.dom)
    (h_fun : ∀ ⦃x : E⦄ ⦃hT : x ∈ T.dom⦄ ⦃hS : x ∈ S.dom⦄,
      T ⟨x, hT⟩ = S ⟨x, hS⟩) : T = S := by
  rcases T with ⟨⟨T_dom, T_fun⟩, T_dense⟩
  rcases S with ⟨⟨S_dom, S_fun⟩, S_dense⟩
  simp only [dom] at h_dom
  subst h_dom
  congr 1
  apply LinearPMap.ext' (LinearMap.ext fun x => h_fun (hT := x.2) (hS := x.2))

end Basic

section Graph

variable [TopologicalSpace F]

/-- The graph of a densely defined linear map as a submodule of `E × F`.
This is the set `{ (x, Tx) | x ∈ dom(T) }`. -/
def graph (T : E →ₗᴰ.[R] F) : Submodule R (E × F) := T.toLinearPMap.graph

omit [TopologicalSpace F] in
theorem mem_graph_iff (T : E →ₗᴰ.[R] F) {p : E × F} :
    p ∈ T.graph ↔ ∃ y : T.dom, (↑y : E) = p.1 ∧ T y = p.2 :=
  T.toLinearPMap.mem_graph_iff

omit [TopologicalSpace F] in
/-- A densely defined linear map is uniquely determined by its graph. -/
theorem eq_of_graph_eq {T S : E →ₗᴰ.[R] F} (h : T.graph = S.graph) : T = S := by
  have h_pmap : T.toLinearPMap = S.toLinearPMap := LinearPMap.eq_of_eq_graph h
  rcases T with ⟨T_pmap, T_dense⟩
  rcases S with ⟨S_pmap, S_dense⟩
  simp only at h_pmap
  subst h_pmap
  rfl

end Graph

section FromLinearMap

variable [TopologicalSpace F]

/-- Construct a densely defined linear map from a linear map on the whole space.
The domain is the entire space `E`. -/
def ofLinearMap (f : E →ₗ[R] F) (hE : Dense (Set.univ : Set E) := by exact dense_univ) :
    E →ₗᴰ.[R] F where
  toLinearPMap := ⟨⊤, f.comp (Submodule.subtype ⊤)⟩
  dense_domain := by
    simp only [Submodule.top_coe]
    exact hE

omit [TopologicalSpace F] in
theorem ofLinearMap_dom (f : E →ₗ[R] F) (hE : Dense (Set.univ : Set E)) :
    (ofLinearMap f hE).dom = ⊤ := rfl

omit [TopologicalSpace F] in
theorem ofLinearMap_apply (f : E →ₗ[R] F) (hE : Dense (Set.univ : Set E))
    (x : (⊤ : Submodule R E)) :
    (ofLinearMap f hE) x = f x := rfl

end FromLinearMap

section Restriction

/-- Restrict a densely defined linear map to a smaller (still dense) domain. -/
def restrict (T : E →ₗᴰ.[R] F) (S : Submodule R E) (hS : S ≤ T.dom)
    (hS_dense : Dense (S : Set E)) : E →ₗᴰ.[R] F where
  toLinearPMap := ⟨S, T.toLinearPMap.toFun.comp (Submodule.inclusion hS)⟩
  dense_domain := hS_dense

theorem restrict_dom (T : E →ₗᴰ.[R] F) (S : Submodule R E) (hS : S ≤ T.dom)
    (hS_dense : Dense (S : Set E)) : (T.restrict S hS hS_dense).dom = S := rfl

theorem restrict_apply (T : E →ₗᴰ.[R] F) (S : Submodule R E) (hS : S ≤ T.dom)
    (hS_dense : Dense (S : Set E)) (x : S) :
    (T.restrict S hS hS_dense) x = T ⟨x, hS x.2⟩ := rfl

end Restriction

section Extension

/-- A densely defined linear map `T` extends another `S` if `S.dom ≤ T.dom`
and `T` agrees with `S` on `S.dom`. -/
def Extends (T S : E →ₗᴰ.[R] F) : Prop :=
  ∃ (h : S.dom ≤ T.dom), ∀ x : S.dom, T ⟨x, h x.2⟩ = S x

/-- Extension is reflexive. -/
theorem Extends.refl (T : E →ₗᴰ.[R] F) : Extends T T :=
  ⟨le_refl _, fun _ => rfl⟩

/-- Extension is transitive. -/
theorem Extends.trans {T S U : E →ₗᴰ.[R] F} (hTS : Extends T S) (hSU : Extends S U) :
    Extends T U := by
  obtain ⟨hTS_dom, hTS_fun⟩ := hTS
  obtain ⟨hSU_dom, hSU_fun⟩ := hSU
  refine ⟨le_trans hSU_dom hTS_dom, fun y => ?_⟩
  have hy_S : (y : E) ∈ S.dom := hSU_dom y.2
  calc T ⟨y, hTS_dom (hSU_dom y.2)⟩
      = S ⟨y, hy_S⟩ := hTS_fun ⟨y, hy_S⟩
    _ = U y := hSU_fun y

end Extension

section HilbertSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- A densely defined linear map on a Hilbert space. This is the standard setting
for unbounded operators in quantum mechanics. -/
abbrev OnHilbertSpace (𝕜 : Type*) [RCLike 𝕜] (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] := H →ₗᴰ.[𝕜] H

/-- A symmetric (or Hermitian) operator: ⟨Tx, y⟩ = ⟨x, Ty⟩ for all x, y in the domain. -/
def IsSymmetric (T : OnHilbertSpace 𝕜 H) : Prop :=
  ∀ x y : T.dom, @inner 𝕜 H _ (T x) y = @inner 𝕜 H _ x (T y)

theorem IsSymmetric.inner_eq {T : OnHilbertSpace 𝕜 H} (hT : T.IsSymmetric)
    (x y : T.dom) : @inner 𝕜 H _ (T x) y = @inner 𝕜 H _ x (T y) := hT x y

/-- For a symmetric operator, ⟨Tx, x⟩ is real. -/
theorem IsSymmetric.inner_self_real [CompleteSpace H] {T : OnHilbertSpace 𝕜 H}
    (hT : T.IsSymmetric) (x : T.dom) : RCLike.im (@inner 𝕜 H _ (T x) x) = 0 := by
  have h := hT x x
  rw [RCLike.conj_eq_iff_im.mp]
  · rw [inner_conj_symm]
    exact h.symm

/-- A positive operator: ⟨Tx, x⟩ ≥ 0 for all x in the domain. -/
def IsPositive (T : OnHilbertSpace 𝕜 H) : Prop :=
  ∀ x : T.dom, 0 ≤ RCLike.re (@inner 𝕜 H _ (T x) x)

end HilbertSpace

end DenselyDefinedLinearMap
