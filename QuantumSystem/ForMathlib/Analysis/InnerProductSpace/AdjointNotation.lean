module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section

/-!
# Dagger notation for the adjoint of a continuous linear map

This module introduces the postfix notation `T†` for `ContinuousLinearMap.adjoint T`,
the Hilbert-space adjoint of a continuous linear map between complex (or `RCLike`)
inner product spaces.

The dagger `†` is the standard symbol for the adjoint throughout the operator-algebra
and quantum-physics literature (Bratteli–Robinson, Takesaki, Haag), where one writes
`T†` rather than the long-form `ContinuousLinearMap.adjoint T`.  Keeping the formal
statements in this notation lets them read like the source texts.

The notation lives in the dedicated `Adjoint` scope, so it is opt-in: activate it with
`open scoped Adjoint`.

| Symbol | Expansion | How to activate |
|---|---|---|
| `T†` | `ContinuousLinearMap.adjoint T` | `open scoped Adjoint` |

`†` binds at maximum precedence, so it attaches to the immediately preceding atom:
write `(f ∘L g)†` and `(R.π a)†` with explicit parentheses, exactly as for `⁻¹`.
-/

namespace Adjoint

/-- `T†` denotes the Hilbert-space adjoint `ContinuousLinearMap.adjoint T`. -/
scoped postfix:max "†" => ContinuousLinearMap.adjoint

end Adjoint
