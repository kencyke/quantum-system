/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import QuantumSystem.Analysis.Matrix.HermitianFunctionalCalculus

/-!
# Continuous functional calculus on diagonal matrices

For a real diagonal matrix `diagonal (fun i => (d i : ℂ))`, the continuous functional
calculus `cfc f` reduces to the diagonal of the entrywise `f`, for **any** `f : ℝ → ℝ`:
the spectrum is finite, so continuity on it is automatic. This is the general form of
`Matrix.diagonal_rpow` in `QuantumSystem/ForMathlib/Analysis/Matrix/Basic.lean`.

## Main results

* `Matrix.cfc_diagonal` — `cfc f (diagonal d) = diagonal (f ∘ d)` for `d : m → ℝ`.
* `Matrix.cfc_unitary_conj_diagonal` — `cfc f` commutes with unitary conjugation of a
  real diagonal: `cfc f (W · diag d · Wᴴ) = W · diag (f ∘ d) · Wᴴ`.
* `Matrix.trace_mul_cfc_unitary_conj_diagonal` —
  `Tr(ρ · f(W · diag d · Wᴴ)) = ∑ₖ f(dₖ) (Wᴴ ρ W)ₖₖ`.
-/

@[expose] public section

namespace Matrix

open scoped ComplexOrder

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- `cfc f` of a real diagonal matrix is the diagonal of the entrywise `f`, for **any**
`f : ℝ → ℝ`: the spectrum is finite, so no continuity hypothesis is needed.

Proof outline:
1. `diagonal : (m → ℂ) →⋆ₐ[ℝ] Matrix m m ℂ` is a continuous star algebra
   homomorphism (constructed inline), so `StarAlgHomClass.map_cfc` moves the CFC
   inside: `cfc f (diagonal dc) = diagonal (cfc f dc)`.
2. In the commutative Pi C*-algebra `m → ℂ`, CFC is pointwise (`cfc_map_pi`),
   and each entry `(d i : ℂ) = algebraMap ℝ ℂ (d i)` gives
   `cfc f (d i : ℂ) = (f (d i) : ℝ) : ℂ` via `cfc_algebraMap`. -/
lemma cfc_diagonal (f : ℝ → ℝ) (d : m → ℝ) :
    cfc f (diagonal (fun i => (d i : ℂ)) : Matrix m m ℂ) =
      diagonal (fun i => ((f (d i) : ℝ) : ℂ)) := by
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
  -- The union of the component spectra is finite, so `f` is continuous on it.
  have hcont_union : ContinuousOn f (⋃ i, spectrum ℝ (dc i)) := by
    refine ((Set.finite_range d).subset ?_).continuousOn f
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
    exact ⟨i, ((hspec_i i) hxi).symm⟩
  -- cfc on Pi computed componentwise.
  have h_pi_cfc : cfc f dc = fun i : m => ((f (d i) : ℝ) : ℂ) := by
    rw [cfc_map_pi (S := ℝ) f dc hcont_union hdc_sa hdc_i_sa]
    funext i
    simp only [dc]
    rw [show (d i : ℂ) = algebraMap ℝ ℂ (d i) from rfl, cfc_algebraMap (A := ℂ) (d i) f]
    rfl
  -- Apply StarAlgHom.map_cfc. Need ContinuousOn f (spectrum ℝ dc).
  have hspec_dc : spectrum ℝ dc ⊆ ⋃ i, spectrum ℝ (dc i) := by
    rw [Pi.spectrum_eq]
  have hcont_dc : ContinuousOn f (spectrum ℝ dc) := hcont_union.mono hspec_dc
  have h_map := StarAlgHomClass.map_cfc (R := ℝ) (S := ℝ)
    φ f dc hcont_dc hφ_cont hdc_sa hφdc_sa
  rw [← hφ_dc, ← h_map, h_pi_cfc]
  rfl

/-- `cfc f` commutes with unitary conjugation of a real diagonal matrix, for any
`f : ℝ → ℝ`: `cfc f (W · diag d · Wᴴ) = W · diag (f ∘ d) · Wᴴ`. -/
lemma cfc_unitary_conj_diagonal
    {k : Type*} [Fintype k] [DecidableEq k]
    (W : unitary (Matrix k k ℂ)) (f : ℝ → ℝ) (d : k → ℝ) :
    cfc f
        ((W : Matrix k k ℂ) *
          diagonal (fun i => ((d i : ℝ) : ℂ)) * (W : Matrix k k ℂ)ᴴ) =
      (W : Matrix k k ℂ) *
        diagonal (fun i => ((f (d i) : ℝ) : ℂ)) * (W : Matrix k k ℂ)ᴴ := by
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
      Set.range d := by
    intro x hx
    rw [← spectrum.preimage_algebraMap ℂ] at hx
    rw [Set.mem_preimage, _root_.spectrum_diagonal] at hx
    rcases hx with ⟨i, hxi⟩
    have hx_eq : (x : ℂ) = ((d i : ℝ) : ℂ) := by
      change (algebraMap ℝ ℂ x : ℂ) = ((d i : ℝ) : ℂ)
      exact hxi.symm
    exact ⟨i, by exact_mod_cast hx_eq.symm⟩
  have h_cont : ContinuousOn f
      (spectrum ℝ (diagonal (fun i => ((d i : ℝ) : ℂ)))) :=
    ((Set.finite_range d).subset h_spec_sub).continuousOn f
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
    (Unitary.conjStarAlgAut ℝ (Matrix k k ℂ) W) f
    (diagonal (fun i => ((d i : ℝ) : ℂ))) h_cont h_cont_conj h_diag_sa h_diag_conj_sa
  rw [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose] at h_map
  calc
    cfc f
        ((W : Matrix k k ℂ) *
          diagonal (fun i => ((d i : ℝ) : ℂ)) * (W : Matrix k k ℂ)ᴴ)
      = (W : Matrix k k ℂ) *
          cfc f (diagonal (fun i => ((d i : ℝ) : ℂ))) * (W : Matrix k k ℂ)ᴴ :=
        h_map.symm
    _ = (W : Matrix k k ℂ) *
          diagonal (fun i => ((f (d i) : ℝ) : ℂ)) * (W : Matrix k k ℂ)ᴴ := by
        rw [cfc_diagonal f d]

/-- **Trace against a unitary diagonalisation.** For `σ = W · diag d · Wᴴ` with `W` unitary,
`Tr(ρ · f(σ)) = ∑ₖ f(dₖ) · (Wᴴ ρ W)ₖₖ` for every `f : ℝ → ℝ` and every matrix `ρ`. -/
lemma trace_mul_cfc_unitary_conj_diagonal
    {k : Type*} [Fintype k] [DecidableEq k]
    (W : unitary (Matrix k k ℂ)) (f : ℝ → ℝ) (d : k → ℝ) (ρ : Matrix k k ℂ) :
    (ρ * cfc f
        ((W : Matrix k k ℂ) *
          diagonal (fun i => ((d i : ℝ) : ℂ)) * (W : Matrix k k ℂ)ᴴ)).trace =
      ∑ i, ((f (d i) : ℝ) : ℂ) * ((W : Matrix k k ℂ)ᴴ * ρ * (W : Matrix k k ℂ)) i i := by
  rw [cfc_unitary_conj_diagonal W f d]
  set Wm : Matrix k k ℂ := (W : Matrix k k ℂ)
  set D : Matrix k k ℂ := diagonal (fun i => ((f (d i) : ℝ) : ℂ)) with hD
  have h1 : ρ * (Wm * D * Wmᴴ) = (ρ * Wm * D) * Wmᴴ := by simp only [Matrix.mul_assoc]
  rw [h1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  simp only [Matrix.trace, Matrix.diag, hD, mul_diagonal]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end Matrix
