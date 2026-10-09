/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Trace notation

The prefix notation `Tr` for the trace of a matrix and of a bounded operator on a
finite-dimensional space. Other notations of the project are declared, and documented, in the
modules that define the notions they abbreviate.

## `Tr` syntax

`Tr` is a prefix notation at max precedence, for the trace of a matrix (`open scoped Matrix`) or
of a bounded operator on a finite-dimensional space (`open scoped ContinuousLinearMap`); when both
scopes are open the argument's type selects the meaning. Use:
- `Tr A` for a simple argument
- `Tr (A * B)` for a complex expression (space before `(`)
- `(Tr A).re` when chaining dot notation on the result
-/

@[expose] public section

/-- `Tr A` is the trace of the matrix `A`. -/
scoped[Matrix] prefix:max "Tr " => Matrix.trace

/-- `Tr A` is the trace of the operator `A : H →L[𝕜] H` on a finite-dimensional space, Mathlib's
`LinearMap.trace 𝕜 H` applied to the underlying linear map. -/
scoped[ContinuousLinearMap] notation "Tr " A:max =>
  LinearMap.trace _ _ (ContinuousLinearMap.toLinearMap A)
