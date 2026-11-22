/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.MetricSpace.Isometry

/-!
# Pointwise convergence of isometries

A family `f : G → (E → F)` of isometries between pseudometric spaces is equicontinuous, so the
topology of pointwise convergence on it is better behaved than for arbitrary maps. Here `G` carries
a topology for which `f` is continuous, or inducing, into `E → F` with the product topology:

* evaluation `(g, a) ↦ f g a` is jointly continuous
  (`Continuous.continuous_eval_of_isometry`);
* a map `φ : X → G` is continuous as soon as `x ↦ f (φ x) a` is continuous for every `a` in a dense
  subset of `E` (`Topology.IsInducing.continuous_of_dense_of_isometry`);
* a group `G` acting on `E` by isometries, with the topology of pointwise convergence, is a
  topological group (`Topology.IsInducing.isTopologicalGroup_of_isometry`).

Examples are the ⋆-automorphisms of a C⋆-algebra with the point-norm topology and the unitary group
of a Hilbert space with the strong operator topology.
-/

@[expose] public section

open Filter Topology

variable {G E F : Type*} [TopologicalSpace G] [PseudoMetricSpace E] [PseudoMetricSpace F]
  {f : G → E → F}

namespace Continuous

/-- **Evaluation is jointly continuous on a family of isometries** carrying a topology finer than
that of pointwise convergence: `dist (f g a) (f g₀ a₀) ≤ dist a a₀ + dist (f g a₀) (f g₀ a₀)`, since
`f g` is isometric. -/
theorem continuous_eval_of_isometry (hf : Continuous f) (hiso : ∀ g, Isometry (f g)) :
    Continuous fun p : G × E => f p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨g₀, a₀⟩
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ => dist_nonneg) (g := fun p : G × E =>
    dist p.2 a₀ + dist (f p.1 a₀) (f g₀ a₀)) (fun p => ?_) ?_
  · calc dist (f p.1 p.2) (f g₀ a₀) ≤ dist (f p.1 p.2) (f p.1 a₀) + dist (f p.1 a₀) (f g₀ a₀) :=
          dist_triangle _ _ _
      _ = _ := by rw [(hiso p.1).dist_eq]
  · have h₁ := tendsto_iff_dist_tendsto_zero.mp (continuous_snd.tendsto (g₀, a₀))
    have h₂ := tendsto_iff_dist_tendsto_zero.mp
      ((((continuous_apply a₀).comp hf).comp continuous_fst).tendsto (g₀, a₀))
    simpa using h₁.add h₂

end Continuous

namespace Topology.IsInducing

/-- **Continuity into a family of isometries is checked on a dense set**: if the topology of `G` is
that of pointwise convergence, a map `φ : X → G` is continuous as soon as `x ↦ f (φ x) a` is
continuous for every `a` in a dense set `D`. The values of `f` are isometric, so an `ε / 3`
approximation of `a` by a point of `D` controls `f (φ x) a` uniformly in `x`. -/
theorem continuous_of_dense_of_isometry (hf : IsInducing f) (hiso : ∀ g, Isometry (f g))
    {X : Type*} [TopologicalSpace X] {φ : X → G} {D : Set E} (hD : Dense D)
    (h : ∀ a ∈ D, Continuous fun x => f (φ x) a) : Continuous φ := by
  refine hf.continuous_iff.mpr (continuous_pi fun a => Metric.continuous_iff'.mpr fun x₀ ε hε => ?_)
  obtain ⟨d, hd, hdD⟩ := Metric.dense_iff.mp hD a (ε / 3) (by positivity)
  rw [Metric.mem_ball] at hd
  filter_upwards [Metric.continuous_iff'.mp (h d hdD) x₀ (ε / 3) (by positivity)] with x hx
  calc dist (f (φ x) a) (f (φ x₀) a)
      ≤ dist (f (φ x) a) (f (φ x) d) + dist (f (φ x) d) (f (φ x₀) d) +
          dist (f (φ x₀) d) (f (φ x₀) a) :=
        dist_triangle4 _ _ _ _
    _ = dist d a + dist (f (φ x) d) (f (φ x₀) d) + dist d a := by
        rw [(hiso (φ x)).dist_eq, (hiso (φ x₀)).dist_eq, dist_comm a d]
    _ < ε / 3 + ε / 3 + ε / 3 := by gcongr
    _ = ε := by ring

/-- **A group acting by isometries is a topological group in the topology of pointwise
convergence.** Multiplication is continuous by the joint continuity of evaluation
(`Continuous.continuous_eval_of_isometry`), and inversion since
`dist (f g⁻¹ a) (f g₀⁻¹ a) = dist (f g b) (f g₀ b)` for `b = f g₀⁻¹ a`, as `f g` is isometric. -/
theorem isTopologicalGroup_of_isometry [Group G] {f : G → E → E} (hf : IsInducing f)
    (hiso : ∀ g, Isometry (f g)) (hmul : ∀ g h a, f (g * h) a = f g (f h a))
    (hone : ∀ a, f 1 a = a) : IsTopologicalGroup G where
  continuous_mul := hf.continuous_iff.mpr <| continuous_pi fun a => by
    simp only [Function.comp_apply, hmul]
    exact (hf.continuous.continuous_eval_of_isometry hiso).comp
      (continuous_fst.prodMk (((continuous_apply a).comp hf.continuous).comp continuous_snd))
  continuous_inv := by
    refine hf.continuous_iff.mpr <| continuous_pi fun a =>
      continuous_iff_continuousAt.mpr fun g₀ => ?_
    rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
    have h (g : G) : dist (f g⁻¹ a) (f g₀⁻¹ a) = dist (f g (f g₀⁻¹ a)) (f g₀ (f g₀⁻¹ a)) := by
      rw [← (hiso g).dist_eq, ← hmul, ← hmul, ← hmul, mul_inv_cancel, mul_inv_cancel, hone,
        dist_comm]
    simp only [Function.comp_apply, h]
    exact tendsto_iff_dist_tendsto_zero.mp
      ((((continuous_apply (f g₀⁻¹ a)).comp hf.continuous)).tendsto g₀)

end Topology.IsInducing
