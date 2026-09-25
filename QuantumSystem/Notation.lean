/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Quantum Information Notation

Notations and abbreviations for quantum information theory.

<table>
<tr><th>Symbol</th><th>Expansion</th><th>How to activate</th><th>Defined in</th></tr>
<tr><td><code>Tr A</code></td><td><code>Matrix.trace A</code></td>
  <td>always available (prefix notation)</td><td>this file</td></tr>
<tr><td><code>log ρ</code></td><td><code>DensityMatrix.log ρ</code></td>
  <td><code>open scoped Matrix.QuantumInfo</code></td><td><code>State.lean</code></td></tr>
<tr><td><code>S(ρ)</code></td><td><code>Matrix.vonNeumannEntropy ρ</code></td>
  <td><code>open scoped Matrix.QuantumInfo</code></td>
  <td><code>Analysis/Entropy/VonNeumann/Basic.lean</code></td></tr>
<tr><td><code>D(ρ ∥ σ)</code></td><td><code>Matrix.umegakiEntropy ρ σ</code></td>
  <td><code>open scoped Matrix.QuantumInfo</code></td>
  <td><code>Analysis/Entropy/Umegaki/Basic.lean</code></td></tr>
<tr><td><code>S⟦ψ ∥ φ⟧</code></td><td><code>VonNeumannAlgebra.arakiEntropy _ ψ φ</code></td>
  <td><code>open scoped Araki</code></td>
  <td><code>Analysis/Entropy/Araki/Basic.lean</code></td></tr>
<tr><td><code>M′</code></td><td><code>VonNeumannAlgebra.commutant M</code></td>
  <td><code>open scoped VonNeumannAlgebra</code></td>
  <td><code>ForMathlib/Analysis/VonNeumannAlgebra/Commutant.lean</code></td></tr>
<tr><td><code>E →σw[𝕜] F</code></td><td><code>ContinuousLinearMapSigmaWeak 𝕜 E F</code></td>
  <td>always available</td>
  <td><code>ForMathlib/Analysis/LocallyConvex/SigmaWeakOperatorTopology.lean</code></td></tr>
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

/-- Real part of the trace for complex matrices: `reTr A = Re(Tr A)`.
Useful for entropy definitions where the trace of a Hermitian product is real. -/
noncomputable abbrev Matrix.reTr {n : Type*} [Fintype n] (A : Matrix n n ℂ) : ℝ := (Tr A).re

-- `reTr A` is notation for `Matrix.reTr A`.

prefix:max "reTr " => Matrix.reTr
