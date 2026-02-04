module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

@[expose] public section

/-!
# Quantum Information Notation

Notations and abbreviations for quantum information theory.

| Symbol | Expansion | How to activate | Defined in |
|---|---|---|---|
| `Tr A` | `Matrix.trace A` | always available (prefix notation) | this file |
| `log ρ` | `DensityMatrix.log ρ` | `open scoped QuantumInfo` | `DensityMatrix.lean` |
| `S(ρ)` | `Matrix.vonNeumannEntropy ρ` | `open scoped QuantumInfo` | `VonNeumannEntropy.lean` |
| `D(ρ ∥ σ)` | `Matrix.relativeEntropy ρ σ` | `open scoped QuantumInfo` | `Entropy.lean` |
| `⟪X, Y⟫_HS` | `Matrix.hsInnerProduct X Y` | `open scoped QuantumInfo` | `LiebConcavity.lean` |

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
