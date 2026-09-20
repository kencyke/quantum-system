module

public import QuantumSystem.Channel
public import QuantumSystem.Analysis.Entropy.MutualInformation

/-!
# Strong subadditivity of the von Neumann entropy

This file proves strong subadditivity (SSA) directly on plain product index types
`A × B × C`, with marginals taken by the positional partial traces `Matrix.traceLeft` /
`Matrix.traceRight`. It is representation-free — no net structure — the proof is the bare
finite-dimensional quantum-information argument

1. the mutual-information identity `Matrix.relativeEntropy_kronecker_marginals`
   (applied to the `(A : B×C)` and `(A : B)` bipartitions), and
2. the data-processing inequality `Matrix.relativeEntropy_channel_le` for the
   trace-out-`C` channel `Matrix.QuantumChannel.traceOutC`.

The AQFT companion — the same inequality stated over a local net with nested regions, using the
split property `LocalNet.SplitProperty` (`Algebra/LocalNet/SplitProperty.lean`) — is the planned
`LocalNet.SplitProperty.vonNeumannEntropy_SSA` (`Analysis/Entropy/SplitSSA.lean`, not yet
formalised), which will transport this result to the net.

## Main results

* `DensityMatrix.vonNeumannEntropy_SSA` — SSA on `A × B × C` for an arbitrary density
  matrix. No regularisation is needed: the mutual-information identity holds for singular
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

/-! ### Bundled partial-trace marginals -/

/-- Partial trace over the right factor of a density matrix: `DensityMatrix (X × Y) → DensityMatrix X`. -/
noncomputable def ptRight {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (ρ : DensityMatrix (X × Y)) : DensityMatrix X where
  toMatrix := Matrix.traceRight ρ.toMatrix
  posSemidef := Matrix.traceRight_posSemidef ρ.posSemidef
  trace_eq_one := by rw [Matrix.trace_traceRight]; exact ρ.trace_eq_one

@[simp] lemma ptRight_toMatrix {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (ρ : DensityMatrix (X × Y)) : (ρ.ptRight).toMatrix = Matrix.traceRight ρ.toMatrix := rfl

/-- Partial trace over the left factor of a density matrix: `DensityMatrix (X × Y) → DensityMatrix Y`. -/
noncomputable def ptLeft {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (ρ : DensityMatrix (X × Y)) : DensityMatrix Y where
  toMatrix := Matrix.traceLeft ρ.toMatrix
  posSemidef := Matrix.traceLeft_posSemidef ρ.posSemidef
  trace_eq_one := by rw [Matrix.trace_traceLeft]; exact ρ.trace_eq_one

@[simp] lemma ptLeft_toMatrix {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (ρ : DensityMatrix (X × Y)) : (ρ.ptLeft).toMatrix = Matrix.traceLeft ρ.toMatrix := rfl

/-! ### Strong subadditivity -/

variable {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]

/-- **Strong subadditivity.** For any density matrix `ρ` on `A × B × C`,
`S(ρ) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC)`. Direct proof: the mutual-information identity
`Matrix.relativeEntropy_kronecker_marginals` for the `(A : B×C)` and `(A : B)` bipartitions,
followed by the data-processing inequality for the trace-out-`C` channel. -/
theorem vonNeumannEntropy_SSA
    (ρ_ABC : DensityMatrix (A × B × C))
    (ρ_AB : DensityMatrix (A × B)) (ρ_BC : DensityMatrix (B × C)) (ρ_B : DensityMatrix B)
    (h_AB : ρ_AB = (ρ_ABC.mapEquiv (Equiv.prodAssoc A B C)).ptRight)
    (h_BC : ρ_BC = ρ_ABC.ptLeft) (h_B : ρ_B = ρ_ABC.ptLeft.ptRight) :
    S(ρ_ABC) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC) := by
  subst h_AB h_BC h_B
  classical
  set ρ_A := ρ_ABC.ptRight with hρ_A
  set ρ_BC := ρ_ABC.ptLeft with hρ_BC
  set ρ_AB := (ρ_ABC.mapEquiv (Equiv.prodAssoc A B C)).ptRight with hρ_AB
  set ρ_B := ρ_ABC.ptLeft.ptRight with hρ_B
  -- Mutual-information identity for the `(A : B×C)` split of `ρ_ABC`.
  have h_tr2 : tr₂(ρ_ABC.toMatrix) = ρ_A.toMatrix := rfl
  have h_tr1 : tr₁(ρ_ABC.toMatrix) = ρ_BC.toMatrix := rfl
  have h_id1 : D(ρ_ABC ∥ ρ_A ⊗ ρ_BC) = -S(ρ_ABC) + S(ρ_A) + S(ρ_BC) :=
    Matrix.relativeEntropy_kronecker_marginals ρ_ABC ρ_A ρ_BC h_tr2 h_tr1
  -- Mutual-information identity for the `(A : B)` split of `ρ_AB`.
  have h_tr2' : tr₂(ρ_AB.toMatrix) = ρ_A.toMatrix := by
    rw [hρ_AB, hρ_A, ptRight_toMatrix, ptRight_toMatrix, DensityMatrix.mapEquiv_toMatrix]
    exact traceRight_traceRight_submatrix_prodAssoc ρ_ABC.toMatrix
  have h_tr1' : tr₁(ρ_AB.toMatrix) = ρ_B.toMatrix := by
    rw [hρ_AB, hρ_B, ptRight_toMatrix, ptRight_toMatrix, ptLeft_toMatrix,
      DensityMatrix.mapEquiv_toMatrix]
    exact traceLeft_traceRight_submatrix_prodAssoc ρ_ABC.toMatrix
  have h_id2 : D(ρ_AB ∥ ρ_A ⊗ ρ_B) = -S(ρ_AB) + S(ρ_A) + S(ρ_B) :=
    Matrix.relativeEntropy_kronecker_marginals ρ_AB ρ_A ρ_B h_tr2' h_tr1'
  -- Data-processing inequality for the trace-out-`C` channel.
  set Φ := Matrix.QuantumChannel.traceOutC (A := A) (B := B) (C := C) with hΦ
  have h_Φρ_ABC : Φ ρ_ABC = ρ_AB := by
    apply DensityMatrix.ext
    change Φ.val ρ_ABC.toMatrix = ρ_AB.toMatrix
    rw [hΦ, Matrix.QuantumChannel.traceOutC_val_apply, hρ_AB, ptRight_toMatrix,
      DensityMatrix.mapEquiv_toMatrix, Matrix.reindex_apply, Equiv.symm_symm]
  have h_Φσ : Φ (ρ_A ⊗ ρ_BC) = ρ_A ⊗ ρ_B := by
    apply DensityMatrix.ext
    change Φ.val (ρ_A ⊗ ρ_BC).toMatrix = (ρ_A ⊗ ρ_B).toMatrix
    rw [hΦ, Matrix.QuantumChannel.traceOutC_val_apply, DensityMatrix.kronecker_toMatrix,
      DensityMatrix.kronecker_toMatrix, Matrix.reindex_apply, Equiv.symm_symm,
      Matrix.traceRight_submatrix_prodAssoc_kronecker]
    simp only [hρ_B, hρ_BC, ptRight_toMatrix, ptLeft_toMatrix]
  have h_dpi : D(Φ ρ_ABC ∥ Φ (ρ_A ⊗ ρ_BC)) ≤ D(ρ_ABC ∥ ρ_A ⊗ ρ_BC) :=
    Matrix.relativeEntropy_channel_le Φ ρ_ABC (ρ_A ⊗ ρ_BC)
  rw [h_Φρ_ABC, h_Φσ, h_id2, h_id1] at h_dpi
  have h_real : -S(ρ_AB) + S(ρ_A) + S(ρ_B) ≤ -S(ρ_ABC) + S(ρ_A) + S(ρ_BC) := by exact_mod_cast h_dpi
  linarith

end DensityMatrix
