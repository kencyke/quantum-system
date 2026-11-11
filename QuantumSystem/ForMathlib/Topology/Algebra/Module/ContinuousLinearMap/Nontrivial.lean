/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# A nonzero continuous linear map has a nontrivial codomain

Mathlib's `ContinuousLinearMap.uniqueOfRight` says that the only continuous linear map into a
subsingleton module is `0`. This file states the contrapositive as a way to obtain `Nontrivial`.

## Main results

* `ContinuousLinearMap.nontrivial_of_ne_zero` — the codomain of a nonzero continuous semilinear map
  is nontrivial.

## TODO

Upstream to `Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic`.
-/

@[expose] public section

namespace ContinuousLinearMap

variable {R₁ R₂ M₁ M₂ : Type*} [Semiring R₁] [Semiring R₂] {σ : R₁ →+* R₂}
  [TopologicalSpace M₁] [AddCommMonoid M₁] [Module R₁ M₁]
  [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R₂ M₂]

/-- The codomain of a nonzero continuous semilinear map is nontrivial. -/
lemma nontrivial_of_ne_zero {f : M₁ →SL[σ] M₂} (hf : f ≠ 0) : Nontrivial M₂ :=
  not_subsingleton_iff_nontrivial.mp fun _ => hf (Subsingleton.elim _ _)

end ContinuousLinearMap
