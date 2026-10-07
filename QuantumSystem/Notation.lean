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
# Quantum Information Notation

Notations and abbreviations for quantum information theory.

<table>
<tr><th>Symbol</th><th>Expansion</th><th>How to activate</th><th>Defined in</th></tr>
<tr><td><code>Tr A</code></td><td><code>Matrix.trace A</code></td>
  <td><code>open scoped Matrix</code></td><td>this file</td></tr>
<tr><td><code>Tr A</code></td>
  <td><code>LinearMap.trace 𝕜 H (A : H →ₗ[𝕜] H)</code> for <code>A : H →L[𝕜] H</code></td>
  <td><code>open scoped ContinuousLinearMap</code></td><td>this file</td></tr>
<tr><td><code>S(ω)</code></td><td><code>vonNeumannEntropy ω</code></td>
  <td><code>open scoped QuantumInfo</code></td>
  <td><code>Analysis/Entropy/VonNeumann/Basic.lean</code></td></tr>
<tr><td><code>D(ψ ∥ φ)</code></td><td><code>umegakiEntropy ψ φ</code></td>
  <td><code>open scoped QuantumInfo</code></td>
  <td><code>Analysis/Entropy/Umegaki/Basic.lean</code></td></tr>
<tr><td><code>S⟦ψ ∥ φ⟧</code></td><td><code>VonNeumannAlgebra.arakiEntropy M ψ φ</code></td>
  <td><code>open scoped Araki</code></td>
  <td><code>Analysis/Entropy/Araki/Basic.lean</code></td></tr>
<tr><td><code>S[K]</code>, <code>Δ[K]</code>, <code>Δ[K]^{1/2}</code>, <code>J[K]</code>,
  <code>Δ[K]^{i t}</code></td>
  <td><code>StandardSubspace.tomita K</code>, <code>StandardSubspace.modular K</code>,
    <code>IsSelfAdjoint.sqrt (StandardSubspace.isSelfAdjoint_modular K)</code>,
    <code>StandardSubspace.modularConj K</code>,
    <code>(StandardSubspace.modularGroup K t : H →L[ℂ] H)</code></td>
  <td><code>open scoped StandardSubspace</code></td>
  <td><code>Analysis/StandardSubspace/Tomita.lean</code></td></tr>
<tr><td><code>S[M]⟦η, ξ⟧</code>, <code>Δ[M]⟦η, ξ⟧</code>, <code>μ[M]⟦η, ξ⟧</code></td>
  <td><code>VonNeumannAlgebra.relativeTomita M η ξ</code>,
    <code>VonNeumannAlgebra.relativeModular M η ξ</code>,
    <code>VonNeumannAlgebra.relativeModularMeasure M η ξ</code></td>
  <td><code>open scoped VonNeumannAlgebra</code></td>
  <td><code>Algebra/VonNeumannAlgebra/Modular/RelativeTomita.lean</code>,
    <code>RelativeModular.lean</code></td></tr>
<tr><td><code>M′</code></td><td><code>VonNeumannAlgebra.commutant M</code></td>
  <td><code>open scoped VonNeumannAlgebra</code></td>
  <td><code>ForMathlib/Analysis/VonNeumannAlgebra/Commutant.lean</code></td></tr>
<tr><td><code>E →σw[𝕜] F</code></td><td><code>ContinuousLinearMapSigmaWeak 𝕜 E F</code></td>
  <td>always available</td>
  <td><code>ForMathlib/Analysis/LocallyConvex/SigmaWeakOperatorTopology.lean</code></td></tr>
<tr><td><code>𝐋[H] B</code>, <code>𝐑[K] A</code></td>
  <td><code>HilbertSchmidt.leftMul H B</code>,
    <code>MulOpposite.unop (HilbertSchmidt.rightMul K A)</code></td>
  <td><code>open scoped HilbertSchmidt</code></td>
  <td><code>ForMathlib/Analysis/InnerProductSpace/HilbertSchmidt.lean</code></td></tr>
</table>

The relative modular theory (`Algebra/VonNeumannAlgebra/Modular/RelativeTomita.lean`,
`RelativeModular.lean`) also uses *local* notations `S⟦η, ξ⟧`, `Δ⟦η, ξ⟧`, `μ⟦η, ξ⟧` for
`S[M]⟦η, ξ⟧`, `Δ[M]⟦η, ξ⟧`, `μ[M]⟦η, ξ⟧` with the algebra `M` fixed by the file's `variable`, as
in the textbooks; they are not exported.

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
