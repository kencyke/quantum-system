/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.InnerProductSpace.Subspace

/-!
# Normed and inner product structures on a complex submodule over its own module structure

For a submodule `p : Submodule ℂ E`, Mathlib's `Submodule.normedSpace` and
`Submodule.innerProductSpace` reach `Module ℂ p` through `Submodule.module'` and
`InnerProductSpace.induced`, while `Module ℂ p` synthesized directly is `Submodule.module`. The two
are definitionally equal, but a type such as `A ⊗[ℂ] p` written by hand carries the latter, while
the same type produced by a construction over an arbitrary inner product space `K := p`
(`ContinuousLinearMap.rTensor`, `UniformSpace.Completion`) carries the former, and unifying the two
inside larger terms exceeds the heartbeat limit. The instances below give the same normed and inner
product structures with `toModule := p.module`, and with them the two types unify quickly. They are
stated for a normed `E`, so that the seminormed group of `p` is the one underlying
`Submodule.normedAddCommGroup`, as a Hilbert space `K` with `[NormedAddCommGroup K]` expects, and
over `ℂ`: stated over an `RCLike 𝕜`, they reach the normed field of `ℂ` through `RCLike`, a further
path that again unifies too slowly.

The instances are a workaround for elaboration speed, not a Mathlib candidate, so the file lives
outside `ForMathlib/`. They are scoped: a file that builds `Completion (A ⊗[ℂ] p)` activates them
with `open scoped Submodule`, and instance resolution on submodules is unchanged everywhere else.

## Main definitions

* `Submodule.normedSpaceSelf` — `Submodule.normedSpace` over `Submodule.module`.
* `Submodule.innerProductSpaceSelf` — `Submodule.innerProductSpace` over `Submodule.module`.

## TODO

Build Mathlib's `Submodule.normedSpace` (for `R = 𝕜`) and `Submodule.innerProductSpace` on
`Submodule.module`, which retires both instances, for every `RCLike 𝕜`.
-/

@[expose] public section

namespace Submodule

/-- The normed space structure of a submodule over its own module structure `Submodule.module`;
`Submodule.normedSpace` with `toModule := p.module`. -/
scoped instance (priority := high) normedSpaceSelf {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (p : Submodule ℂ E) : NormedSpace ℂ p :=
  { toModule := p.module, norm_smul_le := (Submodule.normedSpace p).norm_smul_le }

/-- The inner product space structure of a submodule over its own module structure
`Submodule.module`; `Submodule.innerProductSpace` with the normed space `normedSpaceSelf`. -/
noncomputable scoped instance (priority := high) innerProductSpaceSelf {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (p : Submodule ℂ E) : InnerProductSpace ℂ p :=
  { Submodule.innerProductSpace p with toNormedSpace := normedSpaceSelf p }

end Submodule
