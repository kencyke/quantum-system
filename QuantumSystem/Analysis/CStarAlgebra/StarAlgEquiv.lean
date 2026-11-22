/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Hom.ContinuousEval
public import QuantumSystem.ForMathlib.Topology.MetricSpace.PointwiseIsometry

/-!
# The topology of pointwise convergence on ⋆-algebra equivalences

The ⋆-algebra equivalences `A ≃⋆ₐ[R] B` into a topological ⋆-algebra `B` carry the **topology of
pointwise convergence** (`StarAlgEquiv.instTopologicalSpace`), induced by `A ≃⋆ₐ[R] B → (A → B)`:
a net `eᵢ` converges to `e` when `eᵢ a → e a` for every `a`, and a map `f : X → (A ≃⋆ₐ[R] B)` is
continuous when every `x ↦ f x a` is (`StarAlgEquiv.continuous_iff`). For C⋆-algebras it is the
**point-norm topology**. As the Krull topology on `L ≃ₐ[K] L` (`krullTopology`), it is a global
instance.

Between C⋆-algebras every ⋆-isomorphism is isometric (`StarAlgEquiv.isometry`), so the family of all
of them is equicontinuous, and pointwise convergence is better behaved than for arbitrary maps, by
the results on families of isometries of `QuantumSystem.ForMathlib.Topology.MetricSpace.PointwiseIsometry`:

* evaluation `(e, a) ↦ e a` is jointly continuous (`StarAlgEquiv.instContinuousEval`);
* the ⋆-automorphisms `A ≃⋆ₐ[ℂ] A` form a topological group
  (`StarAlgEquiv.instIsTopologicalGroup`), so a homomorphism into them is continuous as soon as
  it is continuous at `1` (`continuous_of_continuousAt_one`);
* continuity of `x ↦ f x a` on a dense set of `a` suffices (`StarAlgEquiv.continuous_of_dense`).

A continuous homomorphism `G →ₜ* (A ≃⋆ₐ[ℂ] A)` from a topological group is an action of `G` on `A`
by ⋆-automorphisms, continuous in the point-norm topology. The inner action of the unitary group,
`u ↦ (x ↦ u x u⋆)`, is one (`Unitary.continuousConjStarAlgAut`).

## Main definitions

* `StarAlgEquiv.instTopologicalSpace` — the topology of pointwise convergence on `A ≃⋆ₐ[R] B`.
* `Unitary.continuousConjStarAlgAut` — the inner action `unitary R →ₜ* (R ≃⋆ₐ[S] R)`.

## Main results

* `StarAlgEquiv.continuous_iff` — a map into `A ≃⋆ₐ[R] B` is continuous iff each evaluation is.
* `StarAlgEquiv.instContinuousEval` — evaluation is jointly continuous between C⋆-algebras.
* **`StarAlgEquiv.instIsTopologicalGroup`** — the ⋆-automorphisms of a C⋆-algebra form a
  topological group in the point-norm topology.
* `StarAlgEquiv.continuous_of_dense` — continuity on a dense set of points suffices.
* `Unitary.continuous_conjStarAlgAut` — the inner action of the unitary group is continuous.
-/

@[expose] public section

open Filter Topology

namespace StarAlgEquiv

section Pointwise

variable {X R A B : Type*} [Add A] [Mul A] [SMul R A] [Star A] [Add B] [Mul B] [SMul R B] [Star B]
  [TopologicalSpace B] [TopologicalSpace X]

/-- The **topology of pointwise convergence** on `A ≃⋆ₐ[R] B`, induced by the coercion to `A → B`
with the product topology. For C⋆-algebras it is the point-norm topology. -/
instance instTopologicalSpace : TopologicalSpace (A ≃⋆ₐ[R] B) :=
  .induced (fun e : A ≃⋆ₐ[R] B => (e : A → B)) Pi.topologicalSpace

/-- A map into `A ≃⋆ₐ[R] B` is continuous iff each of its evaluations `x ↦ f x a` is. -/
lemma continuous_iff {f : X → A ≃⋆ₐ[R] B} : Continuous f ↔ ∀ a, Continuous fun x => f x a :=
  continuous_induced_rng.trans continuous_pi_iff

/-- Evaluation at a fixed point is continuous in the topology of pointwise convergence. -/
instance instContinuousEvalConst : ContinuousEvalConst (A ≃⋆ₐ[R] B) A B where
  continuous_eval_const a := continuous_iff.mp continuous_id a

/-- The topology of pointwise convergence is induced by the coercion to `A → B`. -/
lemma isInducing_coe : IsInducing (fun e : A ≃⋆ₐ[R] B => (e : A → B)) :=
  ⟨rfl⟩

end Pointwise

section CStarAlgebra

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- Between C⋆-algebras, evaluation `(e, a) ↦ e a` is jointly continuous in the point-norm
topology, every ⋆-isomorphism being isometric (`Continuous.continuous_eval_of_isometry`). -/
instance instContinuousEval : ContinuousEval (A ≃⋆ₐ[ℂ] B) A B where
  continuous_eval := isInducing_coe.continuous.continuous_eval_of_isometry fun e => isometry e

/-- Between C⋆-algebras, a map `f : X → (A ≃⋆ₐ[ℂ] B)` is continuous as soon as `x ↦ f x a` is
continuous for every `a` in a dense set `D`, the values of `f` being isometric
(`Topology.IsInducing.continuous_of_dense_of_isometry`). -/
lemma continuous_of_dense {X : Type*} [TopologicalSpace X] {f : X → A ≃⋆ₐ[ℂ] B} {D : Set A}
    (hD : Dense D) (h : ∀ a ∈ D, Continuous fun x => f x a) : Continuous f :=
  isInducing_coe.continuous_of_dense_of_isometry (fun e => isometry e) hD h

end CStarAlgebra

section Group

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- **The ⋆-automorphisms of a C⋆-algebra form a topological group** in the point-norm topology:
they act on `A` by isometries (`Topology.IsInducing.isTopologicalGroup_of_isometry`). -/
instance instIsTopologicalGroup : IsTopologicalGroup (A ≃⋆ₐ[ℂ] A) :=
  isInducing_coe.isTopologicalGroup_of_isometry (fun e => isometry e) (fun _ _ _ => rfl)
    fun _ => rfl

end Group

end StarAlgEquiv

namespace Unitary

variable {S R : Type*} [Semiring R] [StarMul R] [SMul S R] [IsScalarTower S R R] [SMulCommClass S R R]
  [TopologicalSpace R] [ContinuousMul R] [ContinuousStar R]

/-- The inner action `u ↦ (x ↦ u x u⋆)` of the unitary group is continuous into the topology of
pointwise convergence. -/
lemma continuous_conjStarAlgAut : Continuous (conjStarAlgAut S R) :=
  StarAlgEquiv.continuous_iff.mpr fun a => by
    simp only [conjStarAlgAut_apply]
    fun_prop

variable (S R) in
/-- The **inner action** `u ↦ (x ↦ u x u⋆)` of the unitary group as a continuous homomorphism into
the ⋆-automorphisms with the topology of pointwise convergence. For a C⋆-algebra it is an action
continuous in the point-norm topology. -/
def continuousConjStarAlgAut : unitary R →ₜ* (R ≃⋆ₐ[S] R) :=
  ⟨conjStarAlgAut S R, continuous_conjStarAlgAut⟩

/-- The continuous inner action has the underlying function of `conjStarAlgAut`. -/
@[simp] lemma coe_continuousConjStarAlgAut :
    ⇑(continuousConjStarAlgAut S R) = ⇑(conjStarAlgAut S R) :=
  rfl

/-- The continuous inner action sends `x` to `u x u⋆`. -/
lemma continuousConjStarAlgAut_apply (u : unitary R) (x : R) :
    continuousConjStarAlgAut S R u x = u * x * (star u : R) :=
  rfl

end Unitary
