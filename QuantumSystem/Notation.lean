module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section

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
  <td><code>Analysis/Entropy/VonNeumannEntropy.lean</code></td></tr>
<tr><td><code>D(ρ ∥ σ)</code></td><td><code>Matrix.relativeEntropy ρ σ</code></td>
  <td><code>open scoped Matrix.QuantumInfo</code></td>
  <td><code>Analysis/Entropy/RelativeEntropy.lean</code></td></tr>
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

-- `Tr A` is notation for `Matrix.trace A`.

prefix:max "Tr " => Matrix.trace

/-- Real part of the trace for complex matrices: `reTr A = Re(Tr A)`.
Useful for entropy definitions where the trace of a Hermitian product is real. -/
noncomputable abbrev Matrix.reTr {n : Type*} [Fintype n] (A : Matrix n n ℂ) : ℝ := (Tr A).re

-- `reTr A` is notation for `Matrix.reTr A`.

prefix:max "reTr " => Matrix.reTr
