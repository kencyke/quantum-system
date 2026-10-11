/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Trace notation for bounded operators

The prefix notation `Tr A` for the trace of a bounded operator `A : H →L[𝕜] H` on a
finite-dimensional space, Mathlib's `LinearMap.trace 𝕜 H` applied to the underlying linear map,
scoped to `ContinuousLinearMap`. The same notation for the trace of a matrix is scoped to
`Matrix` (`QuantumSystem.ForMathlib.LinearAlgebra.Matrix.Trace`); when both scopes are open the
argument's type selects the meaning.

## `Tr` syntax

`Tr` is a prefix notation at max precedence. Use:
- `Tr A` for a simple argument
- `Tr (A * B)` for a complex expression (space before `(`)
- `(Tr A).re` when chaining dot notation on the result
-/

@[expose] public section

/-- `Tr A` is the trace of the operator `A : H →L[𝕜] H` on a finite-dimensional space, Mathlib's
`LinearMap.trace 𝕜 H` applied to the underlying linear map. -/
scoped[ContinuousLinearMap] notation "Tr " A:max =>
  LinearMap.trace _ _ (ContinuousLinearMap.toLinearMap A)
