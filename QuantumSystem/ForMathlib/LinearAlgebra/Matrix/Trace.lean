/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Trace notation for matrices

The prefix notation `Tr A` for the trace `Matrix.trace A` of a square matrix, scoped to
`Matrix`. The same notation for the trace of a bounded operator on a finite-dimensional space is
scoped to `ContinuousLinearMap` (`QuantumSystem.ForMathlib.LinearAlgebra.Trace`); when both
scopes are open the argument's type selects the meaning.

## `Tr` syntax

`Tr` is a prefix notation at max precedence. Use:
- `Tr A` for a simple argument
- `Tr (A * B)` for a complex expression (space before `(`)
- `(Tr A).re` when chaining dot notation on the result
-/

@[expose] public section

/-- `Tr A` is the trace of the matrix `A`. -/
scoped[Matrix] prefix:max "Tr " => Matrix.trace
