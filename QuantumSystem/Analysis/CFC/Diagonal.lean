module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import QuantumSystem.Analysis.Matrix.HermitianFunctionalCalculus

/-!
# Continuous functional calculus on diagonal matrices

For a diagonal matrix `diagonal (d : m → ℂ)` with strictly positive real entries,
the continuous functional calculus `cfc Real.log` reduces to the diagonal of the
entrywise logarithm. This is the `Real.log` analogue of `Matrix.diagonal_rpow`
in `QuantumSystem/ForMathlib/Analysis/Matrix/Basic.lean`.

## Main results

* `Matrix.cfc_log_diagonal_pos` — `cfc Real.log (diagonal d) = diagonal (Real.log ∘ d)`
  for `d : m → ℝ` with `0 < d i`.
* `Matrix.cfc_log_unitary_conj_diagonal` — `cfc Real.log` commutes with unitary
  conjugation of a positive real diagonal.
-/

@[expose] public section

namespace Matrix

open scoped ComplexOrder

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- `cfc Real.log` of a diagonal matrix with strictly positive real entries equals
the diagonal of the entrywise `Real.log`.

Proof outline:
1. `diagonal : (m → ℂ) →⋆ₐ[ℝ] Matrix m m ℂ` is a continuous star algebra
   homomorphism (constructed inline), so `StarAlgHomClass.map_cfc` moves the CFC
   inside: `cfc Real.log (diagonal dc) = diagonal (cfc Real.log dc)`.
2. In the commutative Pi C*-algebra `m → ℂ`, CFC is pointwise (`cfc_map_pi`),
   and each entry `(d i : ℂ) = algebraMap ℝ ℂ (d i)` gives
   `cfc Real.log (d i : ℂ) = (Real.log (d i) : ℝ) : ℂ` via `cfc_algebraMap`. -/
lemma cfc_log_diagonal_pos
    (d : m → ℝ) (hd : ∀ i, 0 < d i) :
    cfc Real.log (diagonal (fun i => (d i : ℂ)) : Matrix m m ℂ) =
      diagonal (fun i => ((Real.log (d i) : ℝ) : ℂ)) := by
  letI : NormedRing (Matrix m m ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℂ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra
  letI : CStarAlgebra (Matrix m m ℂ) := by
    simpa [CStarMatrix] using CStarMatrix.instCStarAlgebra (n := m) (A := ℂ)
  -- Provide CFC instances on `ℂ` and the Pi type `(m → ℂ)`.
  letI : ContinuousFunctionalCalculus ℂ ℂ IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  letI : ContinuousFunctionalCalculus ℝ ℂ IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  letI : CStarAlgebra (m → ℂ) := inferInstance
  letI : ContinuousFunctionalCalculus ℂ (m → ℂ) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  letI : ContinuousFunctionalCalculus ℝ (m → ℂ) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  -- Pi self-adjoint
  let dc : m → ℂ := fun i => (d i : ℂ)
  have hdc_sa : IsSelfAdjoint dc := by
    rw [IsSelfAdjoint, Pi.star_def]; ext i; simp [dc, Complex.conj_ofReal]
  -- `diagonal` as star algebra hom (m → ℂ) →⋆ₐ[ℝ] Matrix m m ℂ
  let φ : (m → ℂ) →⋆ₐ[ℝ] Matrix m m ℂ :=
    { Matrix.diagonalAlgHom (R := ℝ) with
      map_star' := fun v => by
        change diagonal (star v) = (diagonal v)ᴴ
        rw [diagonal_conjTranspose] }
  have hφ_cont : Continuous φ := by
    have : (φ : (m → ℂ) → Matrix m m ℂ) = fun v => diagonal v := rfl
    rw [show ⇑φ = fun v => diagonal v from this]
    exact Continuous.matrix_diagonal continuous_id
  have hφ_dc : φ dc = diagonal dc := rfl
  have hφdc_sa : IsSelfAdjoint (φ dc) := by
    rw [IsSelfAdjoint, ← map_star φ]; exact congr_arg φ hdc_sa.star_eq
  -- Each component is self-adjoint (real-valued in ℂ).
  have hdc_i_sa : ∀ i, IsSelfAdjoint (dc i) := by
    intro i; simp [dc, IsSelfAdjoint, Complex.conj_ofReal]
  -- spectrum ℝ (dc i) ⊆ {d i} by CFC.spectrum_algebraMap_subset.
  have hspec_i : ∀ i, spectrum ℝ (dc i) ⊆ {d i} := by
    intro i
    change spectrum ℝ ((d i : ℂ)) ⊆ {d i}
    rw [show ((d i : ℂ) : ℂ) = algebraMap ℝ ℂ (d i) from rfl]
    exact CFC.spectrum_algebraMap_subset (d i)
  -- Continuity of Real.log on ⋃ spectrum of each component.
  have hcont_union : ContinuousOn Real.log (⋃ i, spectrum ℝ (dc i)) := by
    refine Real.continuousOn_log.mono ?_
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
    have : x = d i := (hspec_i i) hxi
    rw [this]
    simp [ne_of_gt (hd i)]
  -- cfc on Pi computed componentwise.
  have h_pi_cfc : cfc Real.log dc = fun i : m => ((Real.log (d i) : ℝ) : ℂ) := by
    rw [cfc_map_pi (S := ℝ) Real.log dc hcont_union hdc_sa hdc_i_sa]
    funext i
    simp only [dc]
    rw [show (d i : ℂ) = algebraMap ℝ ℂ (d i) from rfl, cfc_algebraMap (A := ℂ) (d i) Real.log]
    rfl
  -- Apply StarAlgHom.map_cfc. Need ContinuousOn Real.log (spectrum ℝ dc).
  have hspec_dc : spectrum ℝ dc ⊆ ⋃ i, spectrum ℝ (dc i) := by
    rw [Pi.spectrum_eq]
  have hcont_dc : ContinuousOn Real.log (spectrum ℝ dc) := hcont_union.mono hspec_dc
  have h_map := StarAlgHomClass.map_cfc (R := ℝ) (S := ℝ)
    φ Real.log dc hcont_dc hφ_cont hdc_sa hφdc_sa
  rw [← hφ_dc, ← h_map, h_pi_cfc]
  rfl

/-- `cfc Real.log` commutes with unitary conjugation of a diagonal matrix with
strictly positive real entries. -/
lemma cfc_log_unitary_conj_diagonal
    {k : Type*} [Fintype k] [DecidableEq k]
    (W : unitary (Matrix k k ℂ)) (d : k → ℝ) (hd : ∀ i, 0 < d i) :
    cfc Real.log
        ((W : Matrix k k ℂ) *
          diagonal (fun i => ((d i : ℝ) : ℂ)) * (W : Matrix k k ℂ)ᴴ) =
      (W : Matrix k k ℂ) *
        diagonal (fun i => ((Real.log (d i) : ℝ) : ℂ)) * (W : Matrix k k ℂ)ᴴ := by
  letI : NormedRing (Matrix k k ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix k k ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℂ (Matrix k k ℂ) := Matrix.linftyOpNormedAlgebra
  letI : CStarAlgebra (Matrix k k ℂ) := by
    simpa [CStarMatrix] using CStarMatrix.instCStarAlgebra (n := k) (A := ℂ)
  letI : ContinuousFunctionalCalculus ℂ (Matrix k k ℂ) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  letI : ContinuousFunctionalCalculus ℝ (Matrix k k ℂ) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  have h_diag_sa : IsSelfAdjoint (diagonal (fun i => ((d i : ℝ) : ℂ))) := by
    rw [IsSelfAdjoint, star_eq_conjTranspose, diagonal_conjTranspose]
    congr 1
    funext i
    simp [Complex.conj_ofReal]
  have h_spec_sub : spectrum ℝ (diagonal (fun i => ((d i : ℝ) : ℂ)) : Matrix k k ℂ) ⊆
      {x : ℝ | x ≠ 0} := by
    intro x hx
    rw [← spectrum.preimage_algebraMap ℂ] at hx
    rw [Set.mem_preimage, _root_.spectrum_diagonal] at hx
    rcases hx with ⟨i, hxi⟩
    have hx_eq : (x : ℂ) = ((d i : ℝ) : ℂ) := by
      change (algebraMap ℝ ℂ x : ℂ) = ((d i : ℝ) : ℂ)
      exact hxi.symm
    have : x = d i := by
      exact_mod_cast hx_eq
    rw [this]
    simp [ne_of_gt (hd i)]
  have h_cont : ContinuousOn Real.log
      (spectrum ℝ (diagonal (fun i => ((d i : ℝ) : ℂ)))) :=
    Real.continuousOn_log.mono h_spec_sub
  have h_diag_conj_sa : IsSelfAdjoint
      ((Unitary.conjStarAlgAut ℝ (Matrix k k ℂ) W)
        (diagonal (fun i => ((d i : ℝ) : ℂ)))) := by
    rw [IsSelfAdjoint, ← map_star (Unitary.conjStarAlgAut ℝ (Matrix k k ℂ) W)]
    exact congr_arg (Unitary.conjStarAlgAut ℝ (Matrix k k ℂ) W) h_diag_sa.star_eq
  have h_cont_conj : Continuous (Unitary.conjStarAlgAut ℝ (Matrix k k ℂ) W) := by
    have happly : ∀ x, Unitary.conjStarAlgAut ℝ (Matrix k k ℂ) W x =
        (W : Matrix k k ℂ) * x * (W : Matrix k k ℂ)ᴴ := by
      intro x; simp [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose]
    rw [show (Unitary.conjStarAlgAut ℝ (Matrix k k ℂ) W : Matrix k k ℂ → Matrix k k ℂ) =
        fun x => (W : Matrix k k ℂ) * x * (W : Matrix k k ℂ)ᴴ from funext happly]
    exact (continuous_const.mul continuous_id).mul continuous_const
  have h_map := StarAlgHomClass.map_cfc (R := ℝ) (S := ℝ)
    (Unitary.conjStarAlgAut ℝ (Matrix k k ℂ) W) Real.log
    (diagonal (fun i => ((d i : ℝ) : ℂ))) h_cont h_cont_conj h_diag_sa h_diag_conj_sa
  rw [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose] at h_map
  calc
    cfc Real.log
        ((W : Matrix k k ℂ) *
          diagonal (fun i => ((d i : ℝ) : ℂ)) * (W : Matrix k k ℂ)ᴴ)
      = (W : Matrix k k ℂ) *
          cfc Real.log (diagonal (fun i => ((d i : ℝ) : ℂ))) * (W : Matrix k k ℂ)ᴴ :=
        h_map.symm
    _ = (W : Matrix k k ℂ) *
          diagonal (fun i => ((Real.log (d i) : ℝ) : ℂ)) * (W : Matrix k k ℂ)ᴴ := by
        rw [cfc_log_diagonal_pos d hd]

end Matrix
