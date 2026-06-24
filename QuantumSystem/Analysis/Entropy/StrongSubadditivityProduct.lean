module

public import QuantumSystem.Analysis.Channel.PartialTrace
public import QuantumSystem.Analysis.Entropy.MutualInfoProduct

/-!
# Strong subadditivity of the von Neumann entropy (product form, LocalNet-free)

This file proves strong subadditivity (SSA) directly on plain product index types
`A × B × C`, with marginals taken by the positional partial traces `Matrix.traceLeft` /
`Matrix.traceRight`. It uses NO `LocalNet`, `regionIdx`, `combineIdx`, `restrict`, or three-site
net: the proof is the bare finite-dimensional quantum-information argument

1. the mutual-information identity `Matrix.relativeEntropy_kronecker_marginals_product`
   (applied to the `(A : B×C)` and `(A : B)` bipartitions), and
2. the data-processing inequality `Matrix.relativeEntropy_channel_le` for the
   trace-out-`C` channel `Matrix.QuantumChannel.traceOutC`.

The `LocalNet`/AQFT companion — the same inequality stated over an abstract local net with
overlapping regions — is `DensityMatrix.vonNeumannEntropy_SSA_localNet`
(`StrongSubadditivityLocalNet.lean`).

## Main results

* `DensityMatrix.vonNeumannEntropy_SSA_product_posDef` — SSA on `A × B × C` for a positive
  definite density matrix.
* `DensityMatrix.vonNeumannEntropy_SSA_product` — SSA on `A × B × C` for an arbitrary density
  matrix (via regularisation).
-/

@[expose] public section

namespace Matrix

open scoped Kronecker MatrixOrder ComplexOrder QuantumInfo

/-! ### Bridges between `Matrix.partialTrace` and `Matrix.traceLeft`/`traceRight` -/

/-- `tr₂` (trace out the second factor) is `Matrix.traceRight`. -/
@[simp] lemma partialTrace_refl_eq_traceRight {X Y : Type*} [Fintype Y] (M : Matrix (X × Y) (X × Y) ℂ) :
    Matrix.partialTrace (Equiv.refl (X × Y)) M = Matrix.traceRight M := by
  ext i j; rw [Matrix.partialTrace_refl_apply, traceRight_apply]

/-- `tr₁` (trace out the first factor) is `Matrix.traceLeft`. -/
@[simp] lemma partialTrace_prodComm_eq_traceLeft {X Y : Type*} [Fintype X]
    (M : Matrix (X × Y) (X × Y) ℂ) :
    Matrix.partialTrace (Equiv.prodComm X Y) M = Matrix.traceLeft M := by
  ext i j; rw [Matrix.partialTrace_prodComm_apply, traceLeft_apply]

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

/-! ### Strong subadditivity (product form) -/

variable {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]

/-- **Strong subadditivity (product form, positive definite case).** For a positive definite
density matrix `ρ` on `A × B × C`, with all four marginals positive definite,
`S(ρ) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC)`. -/
private lemma vonNeumannEntropy_SSA_product_posDef
    (ρ_ABC : DensityMatrix (A × B × C))
    (ρ_A : DensityMatrix A) (ρ_AB : DensityMatrix (A × B))
    (ρ_BC : DensityMatrix (B × C)) (ρ_B : DensityMatrix B)
    (h_A : ρ_A = ρ_ABC.ptRight)
    (h_AB : ρ_AB = (ρ_ABC.mapEquiv (Equiv.prodAssoc A B C)).ptRight)
    (h_BC : ρ_BC = ρ_ABC.ptLeft) (h_B : ρ_B = ρ_ABC.ptLeft.ptRight)
    (hA : ρ_A.toMatrix.PosDef) (hBC : ρ_BC.toMatrix.PosDef) (hB : ρ_B.toMatrix.PosDef) :
    S(ρ_ABC) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC) := by
  subst h_A h_AB h_BC h_B
  classical
  set ρ_A := ρ_ABC.ptRight with hρ_A
  set ρ_BC := ρ_ABC.ptLeft with hρ_BC
  set ρ_AB := (ρ_ABC.mapEquiv (Equiv.prodAssoc A B C)).ptRight with hρ_AB
  set ρ_B := ρ_ABC.ptLeft.ptRight with hρ_B
  -- Mutual-information identity for the `(A : B×C)` split of `ρ_ABC`.
  have h_tr2 : tr₂(ρ_ABC.toMatrix) = ρ_A.toMatrix := by
    rw [hρ_A, ptRight_toMatrix]; exact partialTrace_refl_eq_traceRight ρ_ABC.toMatrix
  have h_tr1 : tr₁(ρ_ABC.toMatrix) = ρ_BC.toMatrix := by
    rw [hρ_BC, ptLeft_toMatrix]; exact partialTrace_prodComm_eq_traceLeft ρ_ABC.toMatrix
  have h_id1 : D(ρ_ABC ∥ ρ_A ⊗ ρ_BC) = -S(ρ_ABC) + S(ρ_A) + S(ρ_BC) :=
    Matrix.relativeEntropy_kronecker_marginals_product ρ_ABC ρ_A hA ρ_BC hBC h_tr2 h_tr1
  -- Mutual-information identity for the `(A : B)` split of `ρ_AB`.
  have h_tr2' : tr₂(ρ_AB.toMatrix) = ρ_A.toMatrix := by
    rw [hρ_AB, hρ_A, ptRight_toMatrix, ptRight_toMatrix, DensityMatrix.mapEquiv_toMatrix,
      partialTrace_refl_eq_traceRight]
    exact traceRight_traceRight_submatrix_prodAssoc ρ_ABC.toMatrix
  have h_tr1' : tr₁(ρ_AB.toMatrix) = ρ_B.toMatrix := by
    rw [hρ_AB, hρ_B, ptRight_toMatrix, ptRight_toMatrix, ptLeft_toMatrix,
      DensityMatrix.mapEquiv_toMatrix, partialTrace_prodComm_eq_traceLeft]
    exact traceLeft_traceRight_submatrix_prodAssoc ρ_ABC.toMatrix
  have h_id2 : D(ρ_AB ∥ ρ_A ⊗ ρ_B) = -S(ρ_AB) + S(ρ_A) + S(ρ_B) :=
    Matrix.relativeEntropy_kronecker_marginals_product ρ_AB ρ_A hA ρ_B hB h_tr2' h_tr1'
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

/-! ### Regularisation: commutation of marginals with `regularize` -/

/-- The right partial trace of the maximally mixed state is maximally mixed. -/
lemma traceRight_maximallyMixed {X Y : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y] :
    Matrix.traceRight (DensityMatrix.maximallyMixed (n := X × Y)).toMatrix
      = (DensityMatrix.maximallyMixed (n := X)).toMatrix := by
  rw [DensityMatrix.maximallyMixed_toMatrix, DensityMatrix.maximallyMixed_toMatrix,
    ← Matrix.partialTraceRightₗ_apply, map_smul, Matrix.partialTraceRightₗ_apply,
    Matrix.traceRight_one, smul_smul]
  congr 1
  rw [Fintype.card_prod]
  have hX : (Fintype.card X : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hY : (Fintype.card Y : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  push_cast
  field_simp

/-- The left partial trace of the maximally mixed state is maximally mixed. -/
lemma traceLeft_maximallyMixed {X Y : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y] :
    Matrix.traceLeft (DensityMatrix.maximallyMixed (n := X × Y)).toMatrix
      = (DensityMatrix.maximallyMixed (n := Y)).toMatrix := by
  rw [DensityMatrix.maximallyMixed_toMatrix, DensityMatrix.maximallyMixed_toMatrix,
    ← Matrix.partialTraceLeftₗ_apply, map_smul, Matrix.partialTraceLeftₗ_apply,
    Matrix.traceLeft_one, smul_smul]
  congr 1
  rw [Fintype.card_prod]
  have hX : (Fintype.card X : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hY : (Fintype.card Y : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  push_cast
  field_simp

variable {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]

/-- `ptRight` commutes with `regularize`. -/
lemma ptRight_regularize {X Y : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y] (ρ : DensityMatrix (X × Y)) {ε : ℝ}
    (hε : 0 ≤ ε) (hε' : ε ≤ 1) :
    (DensityMatrix.regularize ρ hε hε').ptRight = DensityMatrix.regularize ρ.ptRight hε hε' := by
  apply DensityMatrix.ext
  rw [ptRight_toMatrix, DensityMatrix.regularize_toMatrix, DensityMatrix.regularize_toMatrix,
    ptRight_toMatrix, ← Matrix.partialTraceRightₗ_apply, map_add, map_smul, map_smul,
    Matrix.partialTraceRightₗ_apply, Matrix.partialTraceRightₗ_apply, traceRight_maximallyMixed]

/-- `ptLeft` commutes with `regularize`. -/
lemma ptLeft_regularize {X Y : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y] (ρ : DensityMatrix (X × Y)) {ε : ℝ}
    (hε : 0 ≤ ε) (hε' : ε ≤ 1) :
    (DensityMatrix.regularize ρ hε hε').ptLeft = DensityMatrix.regularize ρ.ptLeft hε hε' := by
  apply DensityMatrix.ext
  rw [ptLeft_toMatrix, DensityMatrix.regularize_toMatrix, DensityMatrix.regularize_toMatrix,
    ptLeft_toMatrix, ← Matrix.partialTraceLeftₗ_apply, map_add, map_smul, map_smul,
    Matrix.partialTraceLeftₗ_apply, Matrix.partialTraceLeftₗ_apply, traceLeft_maximallyMixed]

/-- **Strong subadditivity (product form).** For any density matrix `ρ` on `A × B × C`,
`S(ρ) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC)`. Obtained from the positive-definite case by regularisation
and a limit. -/
theorem vonNeumannEntropy_SSA_product [Nonempty A] [Nonempty B] [Nonempty C]
    (ρ_ABC : DensityMatrix (A × B × C))
    (ρ_AB : DensityMatrix (A × B)) (ρ_BC : DensityMatrix (B × C)) (ρ_B : DensityMatrix B)
    (h_AB : ρ_AB = (ρ_ABC.mapEquiv (Equiv.prodAssoc A B C)).ptRight)
    (h_BC : ρ_BC = ρ_ABC.ptLeft) (h_B : ρ_B = ρ_ABC.ptLeft.ptRight) :
    S(ρ_ABC) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC) := by
  subst h_AB h_BC h_B
  set ρ_AB := (ρ_ABC.mapEquiv (Equiv.prodAssoc A B C)).ptRight with hρ_AB
  set ρ_BC := ρ_ABC.ptLeft with hρ_BC
  set ρ_B := ρ_ABC.ptLeft.ptRight with hρ_B
  let f_full : ℝ → ℝ := fun ε => ∑ i, Real.negMulLog
    ((1 - ε) * ρ_ABC.isHermitian.eigenvalues i + ε / Fintype.card (A × B × C))
  let f_B : ℝ → ℝ := fun ε => ∑ i, Real.negMulLog
    ((1 - ε) * ρ_B.isHermitian.eigenvalues i + ε / Fintype.card B)
  let f_AB : ℝ → ℝ := fun ε => ∑ i, Real.negMulLog
    ((1 - ε) * ρ_AB.isHermitian.eigenvalues i + ε / Fintype.card (A × B))
  let f_BC : ℝ → ℝ := fun ε => ∑ i, Real.negMulLog
    ((1 - ε) * ρ_BC.isHermitian.eigenvalues i + ε / Fintype.card (B × C))
  have h_ineq_pos : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → f_full ε + f_B ε ≤ f_AB ε + f_BC ε := by
    intro ε hε_pos hε_le
    have hA_pos : ((DensityMatrix.regularize ρ_ABC hε_pos.le hε_le).ptRight).toMatrix.PosDef := by
      rw [ptRight_regularize]; exact DensityMatrix.regularize_posDef _ hε_pos hε_le
    have hBC_pos : ((DensityMatrix.regularize ρ_ABC hε_pos.le hε_le).ptLeft).toMatrix.PosDef := by
      rw [ptLeft_regularize]; exact DensityMatrix.regularize_posDef _ hε_pos hε_le
    have hB_pos :
        ((DensityMatrix.regularize ρ_ABC hε_pos.le hε_le).ptLeft.ptRight).toMatrix.PosDef := by
      rw [ptLeft_regularize, ptRight_regularize]; exact DensityMatrix.regularize_posDef _ hε_pos hε_le
    have h_ssa := vonNeumannEntropy_SSA_product_posDef
      (DensityMatrix.regularize ρ_ABC hε_pos.le hε_le) _ _ _ _ rfl rfl rfl rfl
      hA_pos hBC_pos hB_pos
    rw [show (DensityMatrix.regularize ρ_ABC hε_pos.le hε_le).ptLeft.ptRight
          = DensityMatrix.regularize ρ_B hε_pos.le hε_le from by
        rw [ptLeft_regularize, ptRight_regularize, hρ_B],
      show ((DensityMatrix.regularize ρ_ABC hε_pos.le hε_le).mapEquiv (Equiv.prodAssoc A B C)).ptRight
          = DensityMatrix.regularize ρ_AB hε_pos.le hε_le from by
        rw [← DensityMatrix.regularize_mapEquiv, ptRight_regularize, hρ_AB],
      show (DensityMatrix.regularize ρ_ABC hε_pos.le hε_le).ptLeft
          = DensityMatrix.regularize ρ_BC hε_pos.le hε_le from by
        rw [ptLeft_regularize, hρ_BC]] at h_ssa
    rw [Matrix.vonNeumannEntropy_regularize_eq_negMulLog_sum ρ_ABC hε_pos.le hε_le,
        Matrix.vonNeumannEntropy_regularize_eq_negMulLog_sum ρ_B hε_pos.le hε_le,
        Matrix.vonNeumannEntropy_regularize_eq_negMulLog_sum ρ_AB hε_pos.le hε_le,
        Matrix.vonNeumannEntropy_regularize_eq_negMulLog_sum ρ_BC hε_pos.le hε_le] at h_ssa
    exact h_ssa
  have h_cont_full : Filter.Tendsto f_full (nhds 0) (nhds S(ρ_ABC)) :=
    Matrix.tendsto_negMulLog_regularize_sum_zero ρ_ABC
  have h_cont_B : Filter.Tendsto f_B (nhds 0) (nhds S(ρ_B)) :=
    Matrix.tendsto_negMulLog_regularize_sum_zero ρ_B
  have h_cont_AB : Filter.Tendsto f_AB (nhds 0) (nhds S(ρ_AB)) :=
    Matrix.tendsto_negMulLog_regularize_sum_zero ρ_AB
  have h_cont_BC : Filter.Tendsto f_BC (nhds 0) (nhds S(ρ_BC)) :=
    Matrix.tendsto_negMulLog_regularize_sum_zero ρ_BC
  have h_within : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      f_full ε + f_B ε ≤ f_AB ε + f_BC ε := by
    rw [eventually_nhdsWithin_iff]
    have h_le_one : ∀ᶠ ε in nhds (0 : ℝ), ε ≤ 1 :=
      Filter.eventually_of_mem (IsOpen.mem_nhds isOpen_Iio (by norm_num : (0 : ℝ) < 1))
        (fun ε hε => le_of_lt hε)
    filter_upwards [h_le_one] with ε hε_le_one hε_pos
    exact h_ineq_pos ε hε_pos hε_le_one
  have h_LHS_lim : Filter.Tendsto (fun ε => f_AB ε + f_BC ε) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (S(ρ_AB) + S(ρ_BC))) :=
    (h_cont_AB.add h_cont_BC).mono_left nhdsWithin_le_nhds
  have h_RHS_lim : Filter.Tendsto (fun ε => f_full ε + f_B ε) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (S(ρ_ABC) + S(ρ_B))) :=
    (h_cont_full.add h_cont_B).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto_of_tendsto h_RHS_lim h_LHS_lim h_within

end DensityMatrix
