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
`ρ ↦ Φ.val ρ`. Complete positivity gives positive semidefiniteness and trace preservation gives
trace one.

## Main definitions

* `Matrix.QuantumChannel.apply`: the induced map on density matrices.

## Instances

* `CoeFun (QuantumChannel n m) (fun _ => DensityMatrix n → DensityMatrix m)` lets a channel be
  written as a function on density matrices.
-/

@[expose] public section

namespace Matrix

variable {n m : Type*} [Fintype n] [Fintype m]

open scoped ComplexOrder

/-- Apply a quantum channel to a density matrix. -/
noncomputable def QuantumChannel.apply [DecidableEq n] [DecidableEq m]
    (Φ : QuantumChannel n m) (ρ : DensityMatrix n) :
    DensityMatrix m where
  toMatrix := Φ.val ↑ρ
  posSemidef := by
    classical
    obtain ⟨r, K, hK⟩ := Φ.property.completelyPositive
    rw [hK]
    apply posSemidef_sum
    intro i _
    exact ρ.posSemidef.mul_mul_conjTranspose_same (K i)
  trace_eq_one := by
    rw [Φ.property.tracePreserving]
    exact ρ.trace_eq_one

/-- Quantum channels can be applied as functions from density matrices to density matrices. -/
noncomputable instance [DecidableEq n] [DecidableEq m] : CoeFun (QuantumChannel n m)
    (fun _ => DensityMatrix n → DensityMatrix m) where
  coe := QuantumChannel.apply

end Matrix
