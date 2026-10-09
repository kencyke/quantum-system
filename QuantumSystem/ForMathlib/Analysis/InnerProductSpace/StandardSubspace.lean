/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.InnerProductSpace.StandardSubspace

/-!
# Standard subspaces as sets

Mathlib's `StandardSubspace H` bundles a closed real subspace `toClosedSubmodule` with the
separating and cyclic conditions, but has no `SetLike` instance, so membership must be written
`ξ ∈ K.toClosedSubmodule`. This file adds the instance, so that `ξ ∈ K` and `ξ ∈ K.symplComp`
(the textbook `ξ ∈ K'`) can be written as in the literature.

## Main declarations

* `StandardSubspace.instSetLike` — a standard subspace is a set of vectors.
* `StandardSubspace.mem_toClosedSubmodule` — `ξ ∈ K.toClosedSubmodule ↔ ξ ∈ K`.
-/

@[expose] public section

namespace StandardSubspace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A standard subspace is the set of vectors of its closed real subspace. -/
instance instSetLike : SetLike (StandardSubspace H) H where
  coe K := K.toClosedSubmodule
  coe_injective _ _ h := toClosedSubmodule_injective (SetLike.coe_injective h)

/-- Membership in a standard subspace is membership in its closed real subspace. -/
@[simp]
lemma mem_toClosedSubmodule {K : StandardSubspace H} {x : H} :
    x ∈ K.toClosedSubmodule ↔ x ∈ K :=
  Iff.rfl

end StandardSubspace
