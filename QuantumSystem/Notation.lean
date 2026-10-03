/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Quantum Information Notation

Notations and abbreviations for quantum information theory.

<table>
<tr><th>Symbol</th><th>Expansion</th><th>How to activate</th><th>Defined in</th></tr>
<tr><td><code>Tr A</code></td><td><code>Matrix.trace A</code></td>
  <td>always available (prefix notation)</td><td>this file</td></tr>
<tr><td><code>S(ω)</code></td><td><code>vonNeumannEntropy ω</code></td>
  <td><code>open scoped QuantumInfo</code></td>
  <td><code>Analysis/Entropy/VonNeumann/Basic.lean</code></td></tr>
<tr><td><code>D(ψ ∥ φ)</code></td><td><code>umegakiEntropy ψ φ</code></td>
  <td><code>open scoped QuantumInfo</code></td>
  <td><code>Analysis/Entropy/Umegaki/Basic.lean</code></td></tr>
<tr><td><code>S⟦ψ ∥ φ⟧</code></td><td><code>VonNeumannAlgebra.arakiEntropy M ψ φ</code></td>
  <td><code>open scoped Araki</code></td>
  <td><code>Analysis/Entropy/Araki/Basic.lean</code></td></tr>
<tr><td><code>M′</code></td><td><code>VonNeumannAlgebra.commutant M</code></td>
  <td><code>open scoped VonNeumannAlgebra</code></td>
  <td><code>ForMathlib/Analysis/VonNeumannAlgebra/Commutant.lean</code></td></tr>
<tr><td><code>E →σw[𝕜] F</code></td><td><code>ContinuousLinearMapSigmaWeak 𝕜 E F</code></td>
  <td>always available</td>
  <td><code>ForMathlib/Analysis/LocallyConvex/SigmaWeakOperatorTopology.lean</code></td></tr>
<tr><td><code>𝐋 A</code>, <code>𝐑 B</code></td>
  <td><code>Matrix.leftMulMatrix A</code>, <code>Matrix.rightMulMatrix B</code></td>
  <td><code>open scoped Matrix</code></td>
  <td><code>Analysis/Matrix/Effros.lean</code></td></tr>
<tr><td><code>⟪X, Y⟫_HS</code></td><td><code>Matrix.hsInnerProduct X Y</code></td>
  <td><code>open scoped Matrix.QuantumInfo</code></td>
  <td><code>Analysis/Matrix/LiebConcavity.lean</code></td></tr>
</table>

## `Tr` syntax

`Tr` is a prefix notation at max precedence. Use:
- `Tr A` for a simple argument
- `Tr (A * B)` for a complex expression (space before `(`)
- `(Tr A).re` when chaining dot notation on the result
-/

@[expose] public section

-- `Tr A` is notation for `Matrix.trace A`.

prefix:max "Tr " => Matrix.trace
