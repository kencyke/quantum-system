/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.LocallyConvex.WeakDual
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual

/-!
# Scalar towers and local convexity of the weak-* dual

Mathlib equips the weak space `WeakSpace 𝕜 E` with `WeakSpace.instIsScalarTower`, and every weak
bilinear space `WeakBilin B` with `WeakBilin.instIsScalarTower` and
`WeakBilin.locallyConvexSpace`. Since `WeakDual 𝕜 E` is a type synonym that instance search does
not see through, neither instance reaches the weak-* dual. This file supplies the `WeakDual`
counterparts, so that for instance `WeakDual ℂ A` is a locally convex real space; this is what the
Krein–Milman argument for pure states of a C⋆-algebra needs.

## Main declarations

* `WeakDual.instIsScalarTower` — `IsScalarTower 𝕝 𝕜 (WeakDual 𝕜 E)`, the `WeakDual` version of
  `WeakSpace.instIsScalarTower`. In particular `LinearMap.CompatibleSMul (WeakDual ℂ A) ℂ ℝ ℂ`
  is then found by `IsScalarTower.compatibleSMul`.
* `WeakDual.instLocallyConvexSpace` — the weak-* dual is a locally convex real space, the
  `WeakDual` version of `WeakBilin.locallyConvexSpace`.

Upstreaming: the first instance belongs next to `WeakSpace.instIsScalarTower` in
`Mathlib.Topology.Algebra.Module.Spaces.WeakDual`, the second next to
`WeakBilin.locallyConvexSpace` in `Mathlib.Analysis.LocallyConvex.WeakDual`.
-/

@[expose] public section

namespace WeakDual

section Tower

variable {𝕝 𝕜 E : Type*} [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
  [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

/-- The weak-* dual inherits the scalar tower `𝕝 → 𝕜` of the scalar field, as the weak bilinear
space it is (`WeakBilin.instIsScalarTower`). -/
instance instIsScalarTower [CommSemiring 𝕝] [Module 𝕝 𝕜] [SMulCommClass 𝕜 𝕝 𝕜]
    [ContinuousConstSMul 𝕝 𝕜] [IsScalarTower 𝕝 𝕜 𝕜] :
    IsScalarTower 𝕝 𝕜 (WeakDual 𝕜 E) :=
  WeakBilin.instIsScalarTower _

end Tower

section LocallyConvex

variable {𝕜 E : Type*} [NormedField 𝕜] [NormedSpace ℝ 𝕜] [SMulCommClass 𝕜 ℝ 𝕜]
  [IsScalarTower ℝ 𝕜 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]

/-- **The weak-* dual is locally convex** over `ℝ`: its topology is induced by the seminorms
`φ ↦ ‖φ x‖`, as for every weak bilinear topology (`WeakBilin.locallyConvexSpace`). -/
instance instLocallyConvexSpace : LocallyConvexSpace ℝ (WeakDual 𝕜 E) :=
  WeakBilin.locallyConvexSpace

end LocallyConvex

end WeakDual
