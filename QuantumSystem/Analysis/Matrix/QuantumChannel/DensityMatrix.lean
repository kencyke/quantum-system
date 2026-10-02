/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.Matrix.DensityMatrix.Basic
public import QuantumSystem.Analysis.Matrix.QuantumChannel.CPTP

/-!
# Action of a quantum channel on a density matrix

A quantum channel `Φ : QuantumChannel n m` sends a density matrix on `ℂⁿ` to one on `ℂᵐ` by
`ρ ↦ ρ.map Φ`, the matrix `Φ ρ` with its positivity and trace. Complete positivity gives
positive semidefiniteness and trace preservation gives trace one.

## Main definitions

* `DensityMatrix.map`: the induced map on density matrices. Unitary conjugation and reindexing
  are the channels `Matrix.QuantumChannel.ofStarAlgEquiv` and `Matrix.QuantumChannel.reindex`.

The coercion of `Φ` to a function is its action `M_n(ℂ) → M_m(ℂ)` on matrices (the `FunLike`
instance of `Matrix.QuantumChannel`), so the action on density matrices is spelled
`ρ.map Φ`.
-/

@[expose] public section

namespace DensityMatrix

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

open scoped ComplexOrder

/-- The image `Φ(ρ)` of a density matrix `ρ` under a quantum channel `Φ`.

Positivity and trace preservation alone already send density matrices to density matrices; the
map is nevertheless defined for channels only, since a physical operation on the system must send
the states of the system together with any environment `R` to states, i.e. `id_R ⊗ Φ` must be
positive as well, which is complete positivity. The transpose `ρ ↦ ρᵀ` is positive and
trace-preserving but not completely positive: `id ⊗ T` (the partial transpose) sends a maximally
entangled state to a matrix with a negative eigenvalue. -/
noncomputable def map (ρ : DensityMatrix n) (Φ : Matrix.QuantumChannel n m) :
    DensityMatrix m where
  toMatrix := Φ ↑ρ
  posSemidef := Φ.posSemidef_apply ρ.posSemidef
  trace_eq_one := by
    rw [Φ.trace_map]
    exact ρ.trace_eq_one

/-- The matrix of `ρ.map Φ` is `Φ` applied to the matrix of `ρ`. -/
@[simp] lemma map_toMatrix (ρ : DensityMatrix n) (Φ : Matrix.QuantumChannel n m) :
    (ρ.map Φ).toMatrix = Φ ρ.toMatrix :=
  rfl

end DensityMatrix
