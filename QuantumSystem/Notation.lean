module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section

/-!
# Quantum Information Notation

Notations and abbreviations for quantum information theory.

| Symbol | Expansion | How to activate | Defined in |
|---|---|---|---|
| `Tr A` | `Matrix.trace A` | always available (prefix notation) | this file |
| `log ρ` | `DensityMatrix.log ρ` | `open scoped Matrix.QuantumInfo` | `State.lean` |
| `S(ρ)` | `Matrix.vonNeumannEntropy ρ` | `open scoped Matrix.QuantumInfo` | `Analysis/Entropy/VonNeumannEntropy.lean` |
| `D(ρ ∥ σ)` | `Matrix.relativeEntropy ρ σ` | `open scoped Matrix.QuantumInfo` | `Analysis/Entropy/RelativeEntropy.lean` |
| `⟪X, Y⟫_HS` | `Matrix.hsInnerProduct X Y` | `open scoped Matrix.QuantumInfo` | `Analysis/Matrix/LiebConcavity.lean` |
| `ρ ↾ Λ` | `DensityMatrix.restrict (by …) ρ` | `open scoped LocalNet.QuantumInfo` | `Algebra/LocalNet.lean` |

`ρ ↾ Λ` is the AQFT-style **restriction of a density matrix to a sub-region** —
equivalently, the partial trace over the complementary region.
The subset proof `Λ ⊆ Λ_total` is auto-resolved by `Finset.subset_univ _`, `Finset.Subset.refl _`, or `decide`.
For complex hypotheses, write `DensityMatrix.restrict h ρ` directly.

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
