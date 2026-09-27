/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.Entropy.VonNeumann.MutualInformation
public import QuantumSystem.Analysis.Matrix.QuantumChannel.PartialTrace

/-!
# Strong subadditivity of the von Neumann entropy

This file proves strong subadditivity (SSA) directly on plain product index types
`A × B × C`, with marginals taken by the partial traces `DensityMatrix.traceLeft` /
`DensityMatrix.traceRight`. It is representation-free — no net structure — the proof is the bare
finite-dimensional quantum-information argument

1. the mutual-information identity `DensityMatrix.umegakiEntropy_eq_mutualInformation`
   (applied to the `(A : B×C)` and `(A : B)` bipartitions), and
2. the data-processing inequality `DensityMatrix.umegakiEntropy_channel_le` for the
   trace-out-`C` channel `Matrix.QuantumChannel.traceOutC`.

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

namespace Matrix

open scoped Kronecker MatrixOrder ComplexOrder QuantumInfo

/-! ### Associativity of iterated partial traces over `prodAssoc` -/

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

omit [Fintype A] in
/-- Tracing out `C` (after the associativity reindex to `(A×B)×C`) then `B` equals tracing out
`B × C` directly. -/
lemma traceRight_traceRight_submatrix_prodAssoc (M : Matrix (A × B × C) (A × B × C) ℂ) :
    Matrix.traceRight (Matrix.traceRight
        (M.submatrix (Equiv.prodAssoc A B C) (Equiv.prodAssoc A B C)))
      = Matrix.traceRight M := by
  ext a a'
  simp only [traceRight_apply, Matrix.submatrix_apply, Equiv.prodAssoc_apply]
  rw [Fintype.sum_prod_type]

omit [Fintype B] in
/-- Tracing out `C` (after the reindex) then `A` equals tracing out `C` of (trace out `A`). -/
lemma traceLeft_traceRight_submatrix_prodAssoc (M : Matrix (A × B × C) (A × B × C) ℂ) :
    Matrix.traceLeft (Matrix.traceRight
        (M.submatrix (Equiv.prodAssoc A B C) (Equiv.prodAssoc A B C)))
      = Matrix.traceRight (Matrix.traceLeft M) := by
  ext b b'
  simp only [traceLeft_apply, traceRight_apply, Matrix.submatrix_apply, Equiv.prodAssoc_apply]
  rw [Finset.sum_comm]

omit [Fintype A] [Fintype B] in
/-- Tracing out `C` of `(M_A ⊗ M_BC)` reassociated to `(A×B)×C` factors through `M_BC`. -/
lemma traceRight_submatrix_prodAssoc_kronecker (M_A : Matrix A A ℂ)
    (M_BC : Matrix (B × C) (B × C) ℂ) :
    Matrix.traceRight ((M_A ⊗ₖ M_BC).submatrix (Equiv.prodAssoc A B C) (Equiv.prodAssoc A B C))
      = M_A ⊗ₖ Matrix.traceRight M_BC := by
  ext p q
  simp only [traceRight_apply, Matrix.submatrix_apply, Equiv.prodAssoc_apply,
    Matrix.kroneckerMap_apply]
  rw [Finset.mul_sum]

end Matrix

namespace DensityMatrix

open Matrix
open scoped Kronecker MatrixOrder ComplexOrder Matrix.QuantumInfo

/-! ### Strong subadditivity -/

variable {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]

/-- **Strong subadditivity.** For any density matrix `ρ` on `A × B × C`,
`S(ρ) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC)`, where `ρ_AB` traces out `C` (after reassociating to
`(A × B) × C`), `ρ_BC = tr₁(ρ)` traces out `A`, and `ρ_B` traces out `A` and `C`. Direct proof: the
mutual-information identity `DensityMatrix.umegakiEntropy_eq_mutualInformation` for the
`(A : B×C)` and `(A : B)` bipartitions, followed by the data-processing inequality for the
trace-out-`C` channel. -/
theorem vonNeumannEntropy_strong_subadditivity (ρ : DensityMatrix (A × B × C)) :
    S(ρ) + S(ρ.traceLeft.traceRight) ≤
      S((ρ.mapEquiv (Equiv.prodAssoc A B C)).traceRight) + S(ρ.traceLeft) := by
  classical
  set ρ_ABC := ρ with hρ_ABC
  set ρ_A := ρ_ABC.traceRight with hρ_A
  set ρ_BC := ρ_ABC.traceLeft with hρ_BC
  set ρ_AB := (ρ_ABC.mapEquiv (Equiv.prodAssoc A B C)).traceRight with hρ_AB
  set ρ_B := ρ_ABC.traceLeft.traceRight with hρ_B
  -- Mutual-information identity for the `(A : B×C)` split of `ρ_ABC`.
  have h_id1 : D(ρ_ABC.toMatrix ∥ (ρ_A ⊗ ρ_BC).toMatrix) =
      ((S(ρ_A) + S(ρ_BC) - S(ρ_ABC) : ℝ) : EReal) :=
    umegakiEntropy_eq_mutualInformation ρ_ABC
  -- Mutual-information identity for the `(A : B)` split of `ρ_AB`.
  have h_A : ρ_AB.traceRight = ρ_A := by
    apply DensityMatrix.ext
    rw [hρ_AB, hρ_A, traceRight_toMatrix, traceRight_toMatrix, traceRight_toMatrix,
      DensityMatrix.mapEquiv_toMatrix]
    exact traceRight_traceRight_submatrix_prodAssoc ρ_ABC.toMatrix
  have h_B : ρ_AB.traceLeft = ρ_B := by
    apply DensityMatrix.ext
    rw [hρ_AB, hρ_B, traceLeft_toMatrix, traceRight_toMatrix, traceRight_toMatrix,
      traceLeft_toMatrix, DensityMatrix.mapEquiv_toMatrix]
    exact traceLeft_traceRight_submatrix_prodAssoc ρ_ABC.toMatrix
  have h_id2 : D(ρ_AB.toMatrix ∥ (ρ_A ⊗ ρ_B).toMatrix) =
      ((S(ρ_A) + S(ρ_B) - S(ρ_AB) : ℝ) : EReal) := by
    rw [← h_A, ← h_B]
    exact umegakiEntropy_eq_mutualInformation ρ_AB
  -- Data-processing inequality for the trace-out-`C` channel.
  set Φ := Matrix.QuantumChannel.traceOutC (A := A) (B := B) (C := C) with hΦ
  have h_Φρ_ABC : Φ ρ_ABC = ρ_AB := by
    apply DensityMatrix.ext
    change Φ.val ρ_ABC.toMatrix = ρ_AB.toMatrix
    rw [hΦ, Matrix.QuantumChannel.traceOutC_val_apply, hρ_AB, traceRight_toMatrix,
      DensityMatrix.mapEquiv_toMatrix, Matrix.reindex_apply, Equiv.symm_symm]
  have h_Φσ : Φ (ρ_A ⊗ ρ_BC) = ρ_A ⊗ ρ_B := by
    apply DensityMatrix.ext
    change Φ.val (ρ_A ⊗ ρ_BC).toMatrix = (ρ_A ⊗ ρ_B).toMatrix
    rw [hΦ, Matrix.QuantumChannel.traceOutC_val_apply, DensityMatrix.kronecker_toMatrix,
      DensityMatrix.kronecker_toMatrix, Matrix.reindex_apply, Equiv.symm_symm,
      Matrix.traceRight_submatrix_prodAssoc_kronecker]
    simp only [hρ_B, hρ_BC, traceRight_toMatrix, traceLeft_toMatrix]
  have h_dpi : D((Φ ρ_ABC).toMatrix ∥ (Φ (ρ_A ⊗ ρ_BC)).toMatrix) ≤
      D(ρ_ABC.toMatrix ∥ (ρ_A ⊗ ρ_BC).toMatrix) :=
    DensityMatrix.umegakiEntropy_channel_le Φ ρ_ABC (ρ_A ⊗ ρ_BC)
  rw [h_Φρ_ABC, h_Φσ, h_id2, h_id1] at h_dpi
  have h_real : S(ρ_A) + S(ρ_B) - S(ρ_AB) ≤ S(ρ_A) + S(ρ_BC) - S(ρ_ABC) := by
    exact_mod_cast h_dpi
  linarith

end DensityMatrix
