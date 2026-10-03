/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.Entropy.VonNeumann.MutualInformation
public import QuantumSystem.Analysis.Matrix.QuantumChannel.Kronecker

/-!
# Strong subadditivity of the von Neumann entropy

This file proves strong subadditivity (SSA) directly on plain product index types
`A × B × C`, with marginals taken by the partial traces `DensityMatrix.traceLeft` /
`DensityMatrix.traceRight`. It is representation-free — no net structure — the proof is the bare
finite-dimensional quantum-information argument

1. the mutual-information identity `DensityMatrix.umegakiEntropy_eq_mutualInformation`
   (applied to the `(A : B×C)` and `(A : B)` bipartitions), and
2. the data-processing inequality `DensityMatrix.umegakiEntropy_channel_le` for the
   trace-out-`C` channel `id_A ⊗ Tr_C = Matrix.QuantumChannel.id ⊗ Matrix.QuantumChannel.partialTraceRight`.

The AQFT companion — the same inequality stated over a local net with nested regions, using the
split property `LocalNet.SplitProperty` (`Algebra/LocalNet/SplitProperty.lean`) — is the planned
`LocalNet.SplitProperty.vonNeumannEntropy_strong_subadditivity`
(`Analysis/Entropy/VonNeumann/SplitSSA.lean`, not yet formalised), which will transport this result to the net.

## Main results

* `DensityMatrix.vonNeumannEntropy_strong_subadditivity` — SSA on `A × B × C` for an arbitrary
  density matrix. No regularisation is needed: the mutual-information identity holds for singular
  marginals.
-/

@[expose] public section

namespace DensityMatrix

open Matrix
open scoped Kronecker MatrixOrder ComplexOrder Matrix.QuantumInfo

/-! ### Strong subadditivity -/

variable {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]

/-- **Strong subadditivity.** For any density matrix `ρ = ρ_ABC` on `A × B × C`,

  `S(ρ_ABC) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC)`.

The marginals are spelled with the bipartite partial traces `DensityMatrix.traceRight` (`tr₂`)
and `DensityMatrix.traceLeft` (`tr₁`):

* `ρ_B = ρ.traceLeft.traceRight` — trace out `A`, then `C`;
* `ρ_AB = ρ.map (Matrix.QuantumChannel.id ⊗ Matrix.QuantumChannel.partialTraceRight)` — trace out `C` with the
  channel `id_A ⊗ Tr_C`;
* `ρ_BC = ρ.traceLeft` — trace out `A`.

Direct proof: the mutual-information identity `DensityMatrix.umegakiEntropy_eq_mutualInformation`
for the `(A : B×C)` and `(A : B)` bipartitions, followed by the data-processing inequality for the
trace-out-`C` channel `id_A ⊗ Tr_C`. -/
theorem vonNeumannEntropy_strong_subadditivity (ρ : DensityMatrix (A × B × C)) :
    S(ρ) + S(ρ.traceLeft.traceRight) ≤
      S(ρ.map (Matrix.QuantumChannel.id ⊗ Matrix.QuantumChannel.partialTraceRight)) + S(ρ.traceLeft) := by
  classical
  set ρ_ABC := ρ with hρ_ABC
  set ρ_A := ρ_ABC.traceRight with hρ_A
  set ρ_BC := ρ_ABC.traceLeft with hρ_BC
  set Φ : Matrix.QuantumChannel (A × B × C) (A × B) :=
    Matrix.QuantumChannel.id ⊗ Matrix.QuantumChannel.partialTraceRight with hΦ
  set ρ_AB := ρ_ABC.map Φ with hρ_AB
  set ρ_B := ρ_ABC.traceLeft.traceRight with hρ_B
  -- Mutual-information identity for the `(A : B×C)` split of `ρ_ABC`.
  have h_id1 : D(ρ_ABC.toMatrix ∥ (ρ_A ⊗ ρ_BC).toMatrix) =
      ((S(ρ_A) + S(ρ_BC) - S(ρ_ABC) : ℝ) : EReal) :=
    umegakiEntropy_eq_mutualInformation ρ_ABC
  -- Mutual-information identity for the `(A : B)` split of `ρ_AB`.
  have h_A : ρ_AB.traceRight = ρ_A := by
    apply DensityMatrix.ext
    rw [hρ_AB, hρ_A, traceRight_toMatrix, traceRight_toMatrix, DensityMatrix.map_toMatrix, hΦ,
      Matrix.QuantumChannel.traceRight_kronecker_apply, Matrix.QuantumChannel.id_apply]
  have h_B : ρ_AB.traceLeft = ρ_B := by
    apply DensityMatrix.ext
    rw [hρ_AB, hρ_B, traceLeft_toMatrix, traceRight_toMatrix, traceLeft_toMatrix,
      DensityMatrix.map_toMatrix, hΦ, Matrix.QuantumChannel.traceLeft_kronecker_apply,
      Matrix.QuantumChannel.partialTraceRight_apply]
  have h_id2 : D(ρ_AB.toMatrix ∥ (ρ_A ⊗ ρ_B).toMatrix) =
      ((S(ρ_A) + S(ρ_B) - S(ρ_AB) : ℝ) : EReal) := by
    rw [← h_A, ← h_B]
    exact umegakiEntropy_eq_mutualInformation ρ_AB
  -- Data-processing inequality for the trace-out-`C` channel.
  have h_Φσ : ((ρ_A ⊗ ρ_BC).map Φ).toMatrix = (ρ_A ⊗ ρ_B).toMatrix := by
    rw [DensityMatrix.map_toMatrix, hΦ, DensityMatrix.kronecker_toMatrix,
      DensityMatrix.kronecker_toMatrix, Matrix.QuantumChannel.kronecker_apply_kronecker,
      Matrix.QuantumChannel.id_apply, Matrix.QuantumChannel.partialTraceRight_apply]
    simp only [hρ_B, hρ_BC, traceRight_toMatrix, traceLeft_toMatrix]
  have h_dpi : D(ρ_AB.toMatrix ∥ ((ρ_A ⊗ ρ_BC).map Φ).toMatrix) ≤
      D(ρ_ABC.toMatrix ∥ (ρ_A ⊗ ρ_BC).toMatrix) :=
    DensityMatrix.umegakiEntropy_channel_le Φ ρ_ABC (ρ_A ⊗ ρ_BC)
  rw [h_Φσ, h_id2, h_id1] at h_dpi
  have h_real : S(ρ_A) + S(ρ_B) - S(ρ_AB) ≤ S(ρ_A) + S(ρ_BC) - S(ρ_ABC) := by
    exact_mod_cast h_dpi
  linarith

end DensityMatrix
