module

public import QuantumSystem.Analysis.Entropy.VonNeumannEntropy
public import QuantumSystem.Analysis.Matrix.PartialTrace

/-!
# Regularization on a local net: compatibility with restriction

The structural definitions (`maximallyMixed`, `regularize`, `regularize_eq_cfc`,
`regularize_mapEquiv`) and the entropy identities for regularized states
(`vonNeumannEntropy_regularize_eq_negMulLog_sum`, `tendsto_negMulLog_regularize_sum_zero`,
`vonNeumannEntropy_mapEquiv`) live in `State.lean` and `VonNeumannEntropy.lean`.

This file specialises that infrastructure to a `LocalNet`. It proves compatibility of
regularization with restriction (partial trace), which is the key fact behind extending
PosDef-only theorems to PosSemidef. The cardinality factorisation for region indices now
lives next to `LocalNet.combineIdx` in `LocalNet.lean`.
-/

@[expose] public section

open scoped ComplexOrder

/-! ### Regularization commutes with restriction

The marginal of a regularized state equals the regularized marginal:
`restrict h (regularize ρ ε) = regularize (restrict h ρ) ε`.

This is the key fact behind the "regularization respects partial trace" property
used in extending PosDef-only theorems to PosSemidef. -/

namespace Matrix

/-- `Matrix.restrict h` of the maximally-mixed state at `Λ_total` equals the
    maximally-mixed state at `Λ`, after dimension cancellation. -/
theorem restrict_maximallyMixed {L : LocalNet} {Λ Λ_total : Finset L.sites}
    (h : Λ ⊆ Λ_total) [Nonempty (L.regionIdx Λ)] [Nonempty (L.regionIdx Λ_total)] :
    Matrix.restrict h (DensityMatrix.maximallyMixed (n := L.regionIdx Λ_total)).toMatrix =
      (DensityMatrix.maximallyMixed (n := L.regionIdx Λ)).toMatrix := by
  have hcomp_nonempty : Nonempty (L.regionIdx (Λ_total \ Λ)) := by
    obtain ⟨x⟩ := ‹Nonempty (L.regionIdx Λ_total)›
    exact ⟨((L.combineIdx h).symm x).2⟩
  rw [DensityMatrix.maximallyMixed_toMatrix,
      DensityMatrix.maximallyMixed_toMatrix]
  rw [Matrix.restrict_smul, Matrix.restrict_one]
  rw [smul_smul]
  congr 1
  have hdΛ : (Fintype.card (L.regionIdx Λ) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := L.regionIdx Λ)).ne'
  have hdComp : (Fintype.card (L.regionIdx (Λ_total \ Λ)) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := L.regionIdx (Λ_total \ Λ))).ne'
  rw [LocalNet.card_regionIdx_total (L := L) h]
  have h_inv_mul :
      ((((Fintype.card (L.regionIdx Λ) : ℂ) *
          (Fintype.card (L.regionIdx (Λ_total \ Λ)) : ℂ)))⁻¹) *
          (Fintype.card (L.regionIdx (Λ_total \ Λ)) : ℂ) =
        (Fintype.card (L.regionIdx Λ) : ℂ)⁻¹ := by
    field_simp [hdΛ, hdComp]
  simpa [Nat.cast_mul] using h_inv_mul

end Matrix

namespace DensityMatrix

/-- The regularization commutes with `restrict` (Matrix-level):
    `restrict h (regularize ρ ε).toMatrix = (regularize (restrict h ρ) ε).toMatrix`. -/
theorem regularize_restrict_toMatrix {L : LocalNet} {Λ Λ_total : Finset L.sites}
    (h : Λ ⊆ Λ_total) [Nonempty (L.regionIdx Λ)] [Nonempty (L.regionIdx Λ_total)]
    (ρ : L.densityMatrix Λ_total) {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1) :
    Matrix.restrict h (regularize ρ hε hε').toMatrix =
      (regularize (restrict h ρ) hε hε').toMatrix := by
  rw [regularize_toMatrix, regularize_toMatrix]
  rw [DensityMatrix.restrict_toMatrix]
  rw [(Matrix.restrict h).map_add]
  rw [(Matrix.restrict h).map_smul, (Matrix.restrict h).map_smul]
  rw [Matrix.restrict_maximallyMixed h]

/-- The regularization commutes with `restrict` (DensityMatrix-level):
    `(regularize ρ ε).restrict h = regularize (restrict h ρ) ε`. -/
theorem regularize_restrict {L : LocalNet} {Λ Λ_total : Finset L.sites}
    (h : Λ ⊆ Λ_total) [Nonempty (L.regionIdx Λ)] [Nonempty (L.regionIdx Λ_total)]
    (ρ : L.densityMatrix Λ_total) {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1) :
    restrict h (regularize ρ hε hε') =
      regularize (restrict h ρ) hε hε' := by
  apply ext
  rw [DensityMatrix.restrict_toMatrix]
  exact regularize_restrict_toMatrix h ρ hε hε'

end DensityMatrix
