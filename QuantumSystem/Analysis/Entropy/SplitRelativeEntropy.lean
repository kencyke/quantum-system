module

public import QuantumSystem.Analysis.Entropy.SplitTransport
public import QuantumSystem.Analysis.Entropy.RelativeEntropy

/-!
# Relative entropy on a split net

The **quantum relative entropy** of two states of a split net, stated representation-free on the
local C⋆-algebra. Since the split property makes each local algebra a type I factor (`act`), a state
is a density operator and the Araki relative entropy coincides with the density-operator relative
entropy `D(ρ ‖ σ) = Tr (ρ (log ρ - log σ))`; we obtain it by transporting to the matrix
representation `toMatrix` and reusing `Matrix.relativeEntropy`.

The key inequality (the **data-processing inequality** under the marginal `restrict`) is the engine
of strong subadditivity; it is established in `SplitSSA` via the transported quantum channel.
-/

@[expose] public section

open scoped MatrixOrder ComplexOrder

namespace LocalNet.Split

variable {sites : Type*} [DecidableEq sites] {N : LocalNet sites} {ℋ : Finset sites → Type*}
  [∀ Λ, NormedAddCommGroup (ℋ Λ)] [∀ Λ, InnerProductSpace ℂ (ℋ Λ)]
  [∀ Λ, FiniteDimensional ℂ (ℋ Λ)]
  (S : Split N ℋ)

/-- **Quantum relative entropy** `D(ρ ‖ σ)` of two states of the split net at region `Λ`, defined
by transporting to the matrix representation (`toDensityMatrix`) and reusing `Matrix.relativeEntropy`
(for the type I factor this is the Araki relative entropy). -/
noncomputable def relativeEntropy {Λ : Finset sites} {ρ σ : N.algebra Λ}
    (hρ : S.IsDensity ρ) (hσ : S.IsDensity σ) : EReal :=
  Matrix.relativeEntropy (S.toDensityMatrix hρ) (S.toDensityMatrix hσ)

/-- Relative entropy is **non-negative** (Klein's inequality), transported from the matrix result. -/
theorem relativeEntropy_nonneg {Λ : Finset sites} {ρ σ : N.algebra Λ}
    (hρ : S.IsDensity ρ) (hσ : S.IsDensity σ) :
    0 ≤ S.relativeEntropy hρ hσ :=
  Matrix.relativeEntropy_nonneg _ _

/-- The **transported marginal as a matrix map** `M ↦ toMatrix (restrict (toMatrix.symm M))`: the
partial-trace marginal `restrict h` read through the matrix representation of the type I factors. -/
noncomputable def restrictChannelMap {Λ Λ' : Finset sites} (h : Λ ⊆ Λ') :
    Matrix (Fin (Module.finrank ℂ (ℋ Λ'))) (Fin (Module.finrank ℂ (ℋ Λ'))) ℂ →ₗ[ℂ]
      Matrix (Fin (Module.finrank ℂ (ℋ Λ))) (Fin (Module.finrank ℂ (ℋ Λ))) ℂ where
  toFun M := S.toMatrix Λ (S.restrict h ((S.toMatrix Λ').symm M))
  map_add' M M' := by simp only [map_add]
  map_smul' c M := by simp only [map_smul, RingHom.id_apply]

@[simp] theorem restrictChannelMap_apply {Λ Λ' : Finset sites} (h : Λ ⊆ Λ')
    (M : Matrix (Fin (Module.finrank ℂ (ℋ Λ'))) (Fin (Module.finrank ℂ (ℋ Λ'))) ℂ) :
    S.restrictChannelMap h M = S.toMatrix Λ (S.restrict h ((S.toMatrix Λ').symm M)) :=
  rfl

/-- The transported marginal is a **quantum channel** (completely positive + trace preserving):
complete positivity from the matrix Kraus form `toMatrix_restrict_eq_sum_kraus`, trace preservation
from `trace_restrict`. This realises the partial trace as a CPTP map, as required for the
data-processing inequality. -/
theorem isQuantumChannel_restrictChannelMap {Λ Λ' : Finset sites} (h : Λ ⊆ Λ') :
    Matrix.IsQuantumChannel (S.restrictChannelMap h) where
  completelyPositive := by
    refine ⟨Module.finrank ℂ (ℋ (Λ' \ Λ)), S.restrictKraus h, fun M => ?_⟩
    rw [restrictChannelMap_apply, S.toMatrix_restrict_eq_sum_kraus h,
      StarAlgEquiv.apply_symm_apply]
  tracePreserving := by
    intro M
    rw [restrictChannelMap_apply, ← S.trace_eq_matrixTrace, S.trace_restrict h,
      S.trace_eq_matrixTrace, StarAlgEquiv.apply_symm_apply]

/-- The transported marginal packaged as a `QuantumChannel`. -/
noncomputable def restrictMatrixChannel {Λ Λ' : Finset sites} (h : Λ ⊆ Λ') :
    Matrix.QuantumChannel (Fin (Module.finrank ℂ (ℋ Λ'))) (Fin (Module.finrank ℂ (ℋ Λ))) :=
  ⟨S.restrictChannelMap h, S.isQuantumChannel_restrictChannelMap h⟩

/-- The matrix channel transports `toDensityMatrix` along the marginal: it sends the density matrix
of `ρ` to the density matrix of `restrict h ρ`. -/
theorem restrictMatrixChannel_apply {Λ Λ' : Finset sites} (h : Λ ⊆ Λ')
    {ρ : N.algebra Λ'} (hρ : S.IsDensity ρ) :
    S.restrictMatrixChannel h (S.toDensityMatrix hρ)
      = S.toDensityMatrix (S.restrict_isDensity h hρ) := by
  apply DensityMatrix.ext
  change S.restrictChannelMap h (S.toMatrix Λ' ρ) = S.toMatrix Λ (S.restrict h ρ)
  rw [restrictChannelMap_apply, StarAlgEquiv.symm_apply_apply]

/-- **Data-processing inequality for the marginal**: the quantum relative entropy of two states does
not increase under the marginal `restrict h`,
`D(restrict ρ ‖ restrict σ) ≤ D(ρ ‖ σ)`. This is monotonicity of relative entropy under the
partial-trace quantum channel `restrictMatrixChannel`; it is the analytic engine of strong
subadditivity, stated representation-free on the split net. -/
theorem relativeEntropy_restrict_le {Λ Λ' : Finset sites} (h : Λ ⊆ Λ')
    {ρ σ : N.algebra Λ'} (hρ : S.IsDensity ρ) (hσ : S.IsDensity σ) :
    S.relativeEntropy (S.restrict_isDensity h hρ) (S.restrict_isDensity h hσ)
      ≤ S.relativeEntropy hρ hσ := by
  have key := Matrix.relativeEntropy_channel_le (S.restrictMatrixChannel h)
    (S.toDensityMatrix hρ) (S.toDensityMatrix hσ)
  rw [S.restrictMatrixChannel_apply h hρ, S.restrictMatrixChannel_apply h hσ] at key
  exact key

end LocalNet.Split
