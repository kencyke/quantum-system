/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Algebra.CStarAlgebra.State
public import QuantumSystem.Analysis.Entropy.Umegaki.JointConvexity

/-!
# Von Neumann entropy

Let `H` be a finite-dimensional complex Hilbert space. The **von Neumann entropy** of a state `ω`
on `B(H) = H →L[ℂ] H` with density `ρ_ω` (`ContinuousLinearMap.density`, `ω(A) = tr(ρ_ω A)`) is
`S(ω) = -tr ρ_ω log ρ_ω`, and its core properties are derived from Umegaki's relative entropy
through `D(ω ‖ tr) = -S(ω)` (`State.umegakiEntropy_trace_eq_neg_vonNeumannEntropy`).

## Conventions

* Logarithms are natural, so the unit is the nat; `log` is Mathlib's `CFC.log`. With
  `Real.log 0 = 0`, the kernel of `ρ_ω` contributes `0 · log 0 = 0`, so `S(ω) = -Σᵢ λᵢ log λᵢ`
  over the eigenvalues `λᵢ` of `ρ_ω` (`State.vonNeumannEntropy_eq_sum_negMulLog`).
* `d = finrank ℂ H` is the dimension, and `τ = tr / d` the maximally mixed state
  (`State.maximallyMixed`).

## Main definitions

* `State.vonNeumannEntropy ω` — `S(ω) = -Re tr(ρ_ω log ρ_ω) ∈ ℝ`, with notation `S(ω)` in scope
  `QuantumInfo`.
* `State.maximallyMixed H` — the maximally mixed state `τ(A) = tr A / d`, for nontrivial `H`
  (`State.nontrivial`: every `H` carrying a state is nontrivial).

## Main results

* `State.vonNeumannEntropy_eq_neg_re_apply`, `State.re_apply_log_density` —
  `S(ω) = -Re ω(log ρ_ω)`.
* `State.umegakiEntropy_trace_eq_neg_vonNeumannEntropy` — `D(ω ‖ tr) = -S(ω)`;
  `State.umegakiEntropy_maximallyMixed` — `D(ω ‖ τ) = log d - S(ω)`.
* `State.vonNeumannEntropy_eq_sum_negMulLog` — `S(ω) = Σᵢ negMulLog λᵢ`.
* `State.vonNeumannEntropy_nonneg` — `0 ≤ S(ω)`.
* `State.vonNeumannEntropy_le_log_finrank` — `S(ω) ≤ log d`;
  `State.vonNeumannEntropy_maximallyMixed` — `S(τ) = log d`;
  `State.vonNeumannEntropy_eq_log_finrank_iff` — the maximum is attained only at `τ`.
* `State.vonNeumannEntropy_concave` — concavity `Σᵢ wᵢ S(ωᵢ) ≤ S(Σᵢ wᵢ ωᵢ)`.
* `State.vonNeumannEntropy_comp_starAlgEquiv` — invariance under `⋆`-isomorphisms, in particular
  unitary conjugations.

## Proofs

The upper bound and its equality case are Klein's inequality and faithfulness of `D(ω ‖ τ)`;
concavity is joint convexity of `D(· ‖ tr)` (`umegakiEntropy_jointly_convex`);
invariance is invariance of `D` together with that of the trace.
-/

@[expose] public section

open ContinuousLinearMap
open scoped InnerProductSpace ComplexOrder QuantumInfo NNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

namespace State

/-- The **von Neumann entropy** `S(ω) = -tr ρ_ω log ρ_ω` of a state on `B(H)`, with `ρ_ω` its
density. The trace is real, `ρ_ω log ρ_ω` being self-adjoint, so `.re` loses nothing. -/
noncomputable def vonNeumannEntropy (ω : State (H →L[ℂ] H)) : ℝ :=
  -(LinearMap.trace ℂ H (density ω ∘L CFC.log (density ω))).re

end State

/-- `S(ω)` is the von Neumann entropy `State.vonNeumannEntropy ω`. -/
scoped[QuantumInfo] notation "S(" ω ")" => State.vonNeumannEntropy ω

namespace State

variable (ω : State (H →L[ℂ] H))

/-- `S(ω) = -Re ω(log ρ_ω)`. -/
theorem vonNeumannEntropy_eq_neg_re_apply : S(ω) = -(ω (CFC.log (density ω))).re := by
  rw [vonNeumannEntropy, trace_density_comp]

/-- `Re ω(log ρ_ω) = -S(ω)`. -/
theorem re_apply_log_density : (ω (CFC.log (density ω))).re = -S(ω) := by
  rw [vonNeumannEntropy_eq_neg_re_apply, neg_neg]

/-- **Eigenvalue form**: `S(ω) = Σᵢ negMulLog λᵢ = -Σᵢ λᵢ log λᵢ` for an orthonormal eigenbasis
`b` of `ρ_ω` with eigenvalues `λ`. -/
theorem vonNeumannEntropy_eq_sum_negMulLog {ι : Type*} [Fintype ι] {b : OrthonormalBasis ι ℂ H}
    {r : ι → ℝ} (hb : ∀ i, density ω (b i) = (r i : ℂ) • b i) :
    S(ω) = ∑ i, Real.negMulLog (r i) := by
  have hsa := IsSelfAdjoint.of_nonneg (density_nonneg ω)
  rw [vonNeumannEntropy, CFC.log, trace_comp_cfc_eq_sum hsa b hb]
  have h : ∀ i, ⟪b i, density ω (b i)⟫_ℂ = r i := fun i => by
    rw [hb, inner_smul_right, b.inner_eq_one, mul_one]
  simp_rw [h, ← Complex.ofReal_mul, ← Complex.ofReal_sum, Complex.ofReal_re, Real.negMulLog,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Nonnegativity**: `0 ≤ S(ω)`, since the eigenvalues of `ρ_ω` lie in `[0, 1]`. -/
theorem vonNeumannEntropy_nonneg : 0 ≤ S(ω) := by
  obtain ⟨b, r, hr, hb⟩ := exists_orthonormalBasis_density_apply ω
  have hsum : ∑ i, r i = 1 := by
    have h := apply_one_eq_sum_of_density_apply ω b hb
    rw [apply_one] at h
    exact_mod_cast h.symm
  rw [vonNeumannEntropy_eq_sum_negMulLog ω hb]
  exact Finset.sum_nonneg fun i _ => Real.negMulLog_nonneg (hr i)
    (hsum ▸ Finset.single_le_sum (fun j _ => hr j) (Finset.mem_univ i))

/-- **`D(ω ‖ tr) = -S(ω)`**: the von Neumann entropy is minus the relative entropy with respect to
the trace, whose density is `1` and whose null ideal is trivial. -/
theorem umegakiEntropy_trace_eq_neg_vonNeumannEntropy :
    D(ω ∥ tracePositiveLinearMap ℂ H) = ((-S(ω) : ℝ) : EReal) := by
  have hnull : ∀ A : H →L[ℂ] H, tracePositiveLinearMap ℂ H (star A * A) = 0 →
      ω (star A * A) = 0 := fun A hA => by
    rw [tracePositiveLinearMap_apply, trace_star_mul_self_eq_zero_iff] at hA
    rw [hA, star_zero, mul_zero, map_zero]
  rw [umegakiEntropy_eq_re_apply hnull, density_tracePositiveLinearMap,
    CFC.log_one, sub_zero, vonNeumannEntropy_eq_neg_re_apply, neg_neg]

end State

/-! ### The maximally mixed state -/

namespace State

/-- A state on `B(H)` exists only if `H` is nontrivial: otherwise `1 = 0` in `B(H)`. -/
theorem nontrivial (ω : State (H →L[ℂ] H)) : Nontrivial H := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have h1 : (1 : H →L[ℂ] H) = 0 := ContinuousLinearMap.ext fun _ => Subsingleton.elim _ _
  have := ω.apply_one
  rw [h1, map_zero] at this
  exact zero_ne_one this

variable (H) in
/-- The **maximally mixed state** `τ(A) = tr A / d` on `B(H)`, `d = finrank ℂ H`, with density
`1 / d`. -/
noncomputable def maximallyMixed [Nontrivial H] : State (H →L[ℂ] H) :=
  ofPositiveLinearMap ((Module.finrank ℂ H : ℝ≥0)⁻¹ • tracePositiveLinearMap ℂ H) (by
    have hd : (Module.finrank ℂ H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
    simp [NNReal.smul_def, LinearMap.trace_one, hd])

variable [Nontrivial H]

/-- `τ(A) = tr A / d`. -/
theorem maximallyMixed_apply (A : H →L[ℂ] H) :
    maximallyMixed H A = (Module.finrank ℂ H : ℂ)⁻¹ * LinearMap.trace ℂ H A := by
  simp [maximallyMixed, NNReal.smul_def]

variable (ω : State (H →L[ℂ] H))

/-- **`D(ω ‖ τ) = log d - S(ω)`**. -/
theorem umegakiEntropy_maximallyMixed :
    D(ω ∥ maximallyMixed H) = ((Real.log (Module.finrank ℂ H) - S(ω) : ℝ) : EReal) := by
  have hd : (0 : ℝ≥0) < (Module.finrank ℂ H : ℝ≥0)⁻¹ :=
    inv_pos.mpr (Nat.cast_pos.mpr Module.finrank_pos)
  rw [umegakiEntropy_congr ω (maximallyMixed H) (ψ₁ := (ω : (H →L[ℂ] H) →ₚ[ℂ] ℂ))
      (φ₁ := (Module.finrank ℂ H : ℝ≥0)⁻¹ • tracePositiveLinearMap ℂ H) (fun _ => rfl)
      (fun _ => rfl), umegakiEntropy_smul_right hd,
    umegakiEntropy_congr (ω : (H →L[ℂ] H) →ₚ[ℂ] ℂ) (tracePositiveLinearMap ℂ H) (ψ₁ := ω)
      (φ₁ := tracePositiveLinearMap ℂ H) (fun _ => rfl) (fun _ => rfl),
    umegakiEntropy_trace_eq_neg_vonNeumannEntropy, coe_toPositiveLinearMap, apply_one,
    Complex.one_re, one_mul, NNReal.coe_inv, NNReal.coe_natCast, Real.log_inv, ← EReal.coe_sub]
  congr 1
  ring

/-- The maximally mixed state has the maximal entropy: `S(τ) = log d`. -/
theorem vonNeumannEntropy_maximallyMixed :
    S(maximallyMixed H) = Real.log (Module.finrank ℂ H) := by
  have h := umegakiEntropy_maximallyMixed (maximallyMixed H)
  rw [umegakiEntropy_self] at h
  have : (0 : ℝ) = Real.log (Module.finrank ℂ H) - S(maximallyMixed H) := by exact_mod_cast h
  linarith

/-- **The maximum is attained only at `τ`**: `S(ω) = log d` iff `ω` is maximally mixed, by
faithfulness of `D(ω ‖ τ)` (`umegakiEntropy_eq_zero_iff`). -/
theorem vonNeumannEntropy_eq_log_finrank_iff :
    S(ω) = Real.log (Module.finrank ℂ H) ↔ ω = maximallyMixed H := by
  have h := umegakiEntropy_eq_zero_iff (ψ := ω) (φ := maximallyMixed H) (by simp)
  rw [umegakiEntropy_maximallyMixed, EReal.coe_eq_zero, sub_eq_zero, eq_comm] at h
  exact h

end State

namespace State

/-- **Upper bound**: `S(ω) ≤ log d`, by Klein's inequality `0 ≤ D(ω ‖ τ)`. A state exists only
on a nontrivial space (`State.nontrivial`), so no nontriviality is assumed. -/
theorem vonNeumannEntropy_le_log_finrank (ω : State (H →L[ℂ] H)) :
    S(ω) ≤ Real.log (Module.finrank ℂ H) := by
  have := ω.nontrivial
  have h := umegakiEntropy_nonneg (ψ := ω) (φ := maximallyMixed H) (by simp)
  rw [umegakiEntropy_maximallyMixed] at h
  have : (0 : ℝ) ≤ Real.log (Module.finrank ℂ H) - S(ω) := by exact_mod_cast h
  linarith

end State

/-! ### Concavity and invariance -/

namespace State

/-- **Concavity** of the von Neumann entropy: `Σᵢ wᵢ S(ωᵢ) ≤ S(Σᵢ wᵢ ωᵢ)` for a convex
combination of states. With `S = -D(· ‖ tr)` and `tr = Σᵢ wᵢ tr`, this is joint convexity of
Umegaki's relative entropy (`umegakiEntropy_jointly_convex`). -/
theorem vonNeumannEntropy_concave {ι : Type*} (s : Finset ι) (w : ι → ℝ≥0)
    (hw : ∑ i ∈ s, w i = 1) (ω : ι → State (H →L[ℂ] H)) :
    ∑ i ∈ s, (w i : ℝ) * S(ω i) ≤ S(convexCombination s w hw ω) := by
  have htr : tracePositiveLinearMap ℂ H = ∑ i ∈ s, w i • tracePositiveLinearMap ℂ H := by
    rw [← Finset.sum_smul, hw, one_smul]
  have h := umegakiEntropy_jointly_convex s w (fun i => (ω i : _ →ₚ[ℂ] ℂ))
    (fun _ => tracePositiveLinearMap ℂ H)
  rw [← htr, umegakiEntropy_congr (∑ i ∈ s, w i • (ω i : _ →ₚ[ℂ] ℂ)) (tracePositiveLinearMap ℂ H)
    (ψ₁ := convexCombination s w hw ω) (φ₁ := tracePositiveLinearMap ℂ H) (fun _ => rfl)
    (fun _ => rfl), umegakiEntropy_trace_eq_neg_vonNeumannEntropy] at h
  have hi : ∀ i, D((ω i : (H →L[ℂ] H) →ₚ[ℂ] ℂ) ∥ tracePositiveLinearMap ℂ H) =
      ((-S(ω i) : ℝ) : EReal) := fun i => by
    rw [umegakiEntropy_congr (ω i : (H →L[ℂ] H) →ₚ[ℂ] ℂ) (tracePositiveLinearMap ℂ H)
      (ψ₁ := ω i) (φ₁ := tracePositiveLinearMap ℂ H) (fun _ => rfl) (fun _ => rfl),
      umegakiEntropy_trace_eq_neg_vonNeumannEntropy]
  simp_rw [hi, ← EReal.coe_mul] at h
  rw [← EReal.coe_finsetSum] at h
  have h' : -S(convexCombination s w hw ω) ≤ ∑ i ∈ s, (w i : ℝ) * -S(ω i) := by exact_mod_cast h
  simp only [mul_neg, Finset.sum_neg_distrib] at h'
  linarith

/-- **Invariance under `⋆`-isomorphisms**: `S(ω ∘ π) = S(ω)` for `π : B(K) ≃⋆ B(H)`, in particular
for unitary conjugations. Both `D` and the trace are invariant
(`umegakiEntropy_comp_starAlgEquiv`, `ContinuousLinearMap.trace_map`). -/
theorem vonNeumannEntropy_comp_starAlgEquiv {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [FiniteDimensional ℂ K] (π : (K →L[ℂ] K) ≃⋆ₐ[ℂ] (H →L[ℂ] H))
    (ω : State (H →L[ℂ] H)) : S(ω.comp π (map_one π)) = S(ω) := by
  have h := umegakiEntropy_comp_starAlgEquiv π (ψ₁ := ω.comp π (map_one π))
    (φ₁ := tracePositiveLinearMap ℂ K) (ψ := ω) (φ := tracePositiveLinearMap ℂ H) (fun _ => rfl)
    (fun X => (trace_map π X).symm)
  rw [umegakiEntropy_trace_eq_neg_vonNeumannEntropy, umegakiEntropy_trace_eq_neg_vonNeumannEntropy] at h
  have : -S(ω.comp π (map_one π)) = -S(ω) := by exact_mod_cast h
  linarith

end State
