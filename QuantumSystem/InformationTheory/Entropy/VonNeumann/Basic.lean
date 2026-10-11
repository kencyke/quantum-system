/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.CStarAlgebra.State.Basic
public import QuantumSystem.InformationTheory.Entropy.Umegaki.JointConvexity
public import QuantumSystem.ForMathlib.LinearAlgebra.Trace

/-!
# Von Neumann entropy

Let `H` be a finite-dimensional complex Hilbert space. The **von Neumann entropy** of a state `ω`
on `B(H) = H →L[ℂ] H` with density `ρ_ω`
(`ContinuousLinearMap.density`, `ω(A) = tr(ρ_ω A)`) is `S(ω) = -tr ρ_ω log ρ_ω`, and its core
properties are derived from Umegaki's relative entropy through `D(ω ‖ tr) = -S(ω)`
(`State.umegakiEntropy_trace_eq_neg_vonNeumannEntropy`). Concavity is stated with Mathlib's
`ConcaveOn` on the state space `StateSpace (H →L[ℂ] H)`, a convex subset of the dual; for this
`S` is defined as a total function on all linear functionals, its value being meaningful only for
positive ones (off the self-adjoint ones, `CFC.log` and hence `S` take the junk value `0`).

## Conventions

* Logarithms are natural, so the unit is the nat; `log` is Mathlib's `CFC.log`. With
  `Real.log 0 = 0`, the kernel of `ρ_ω` contributes `0 · log 0 = 0`, so `S(ω) = -Σᵢ λᵢ log λᵢ`
  over the eigenvalues `λᵢ` of `ρ_ω` (`vonNeumannEntropy_eq_sum_negMulLog`).
* `d = finrank ℂ H` is the dimension, and `τ = tr / d` the maximally mixed state
  (`State.maximallyMixed`).

## Main definitions

* `vonNeumannEntropy ω` — `S(ω) = -Re tr(ρ_ω log ρ_ω) ∈ ℝ`, meaningful for positive functionals
  `ω` on `B(H)` (a total function on all of them), with notation `S(ω)` in scope `QuantumInfo`.
* `State.maximallyMixed H` — the maximally mixed state `τ(A) = tr A / d`, for nontrivial `H`
  (`State.nontrivial`: every `H` carrying a state is nontrivial).

## Main results

* `vonNeumannEntropy_eq_neg_re_apply`, `re_apply_log_density` —
  `S(ω) = -Re ω(log ρ_ω)`.
* `State.umegakiEntropy_trace_eq_neg_vonNeumannEntropy` — `D(ω ‖ tr) = -S(ω)`;
  `State.umegakiEntropy_maximallyMixed` — `D(ω ‖ τ) = log d - S(ω)`.
* `vonNeumannEntropy_eq_sum_negMulLog` — `S(ω) = Σᵢ negMulLog λᵢ`.
* `State.vonNeumannEntropy_nonneg` — `0 ≤ S(ω)`.
* `State.vonNeumannEntropy_le_log_finrank` — `S(ω) ≤ log d`;
  `State.vonNeumannEntropy_maximallyMixed` — `S(τ) = log d`;
  `State.vonNeumannEntropy_eq_log_finrank_iff` — the maximum is attained only at `τ`.
* `StateSpace.concaveOn_vonNeumannEntropy` — `S` is concave on the state space
  `StateSpace (H →L[ℂ] H)`.
* `State.vonNeumannEntropy_comp_starAlgEquiv` — invariance under `⋆`-isomorphisms, in particular
  unitary conjugations.

## TODO

`State.maximallyMixed H` is the unique tracial state of `B(H)`; prove this characterisation once
tracial states are defined (see the TODO of `QuantumSystem.Analysis.CStarAlgebra.State.Basic`).

## Proofs

The upper bound and its equality case are Klein's inequality and faithfulness of `D(ω ‖ τ)`;
concavity is joint convexity of `D(· ‖ tr)` (`umegakiEntropy_jointly_convex`);
invariance is invariance of `D` together with that of the trace.

## Notation

`S(ω)` is `vonNeumannEntropy ω`; activate it with `open scoped QuantumInfo`.
-/

@[expose] public section

open ContinuousLinearMap
open scoped InnerProductSpace ComplexOrder QuantumInfo NNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

section Generic

variable {G : Type*} [FunLike G (H →L[ℂ] H) ℂ] [LinearMapClass G ℂ (H →L[ℂ] H) ℂ]

/-- The **von Neumann entropy** `S(ω) = -tr ρ_ω log ρ_ω` of a state `ω` on `B(H)`, with `ρ_ω` its
density (`ContinuousLinearMap.density`). The formula is meaningful for positive functionals: then
`ρ_ω log ρ_ω` is self-adjoint, the trace is real, and `.re` loses nothing. It is extended to every
linear functional only so that it is a total function on the dual `WeakDual ℂ (H →L[ℂ] H)`, whose
restriction to the state space is concave (`StateSpace.concaveOn_vonNeumannEntropy`); off the
positive functionals its value is junk. -/
noncomputable def vonNeumannEntropy (ω : G) : ℝ :=
  -(Tr (density ω ∘L CFC.log (density ω))).re

end Generic

/-- `S(ω)` is the von Neumann entropy `vonNeumannEntropy ω`. -/
scoped[QuantumInfo] notation "S(" ω ")" => vonNeumannEntropy ω

section Generic

variable {G : Type*} [FunLike G (H →L[ℂ] H) ℂ] [LinearMapClass G ℂ (H →L[ℂ] H) ℂ]

/-- The von Neumann entropy depends only on the values of the functional. -/
lemma vonNeumannEntropy_congr {G' : Type*} [FunLike G' (H →L[ℂ] H) ℂ]
    [LinearMapClass G' ℂ (H →L[ℂ] H) ℂ] {ω : G} {ω' : G'} (h : ∀ A, ω A = ω' A) :
    S(ω) = S(ω') := by
  rw [vonNeumannEntropy, vonNeumannEntropy, density_eq_density_iff.mpr h]

variable (ω : G)

/-- `S(ω) = -Re ω(log ρ_ω)`. -/
lemma vonNeumannEntropy_eq_neg_re_apply : S(ω) = -(ω (CFC.log (density ω))).re := by
  rw [vonNeumannEntropy, trace_density_comp]

/-- `Re ω(log ρ_ω) = -S(ω)`. -/
lemma re_apply_log_density : (ω (CFC.log (density ω))).re = -S(ω) := by
  rw [vonNeumannEntropy_eq_neg_re_apply, neg_neg]

/-- **Eigenvalue form**: `S(ω) = Σᵢ negMulLog λᵢ = -Σᵢ λᵢ log λᵢ` for a positive functional `ω`
and an orthonormal eigenbasis `b` of `ρ_ω` with eigenvalues `λ`. -/
lemma vonNeumannEntropy_eq_sum_negMulLog [OrderHomClass G (H →L[ℂ] H) ℂ] {ι : Type*} [Fintype ι]
    {b : OrthonormalBasis ι ℂ H} {r : ι → ℝ} (hb : ∀ i, density ω (b i) = (r i : ℂ) • b i) :
    S(ω) = ∑ i, Real.negMulLog (r i) := by
  have hsa := IsSelfAdjoint.of_nonneg (density_nonneg ω)
  rw [vonNeumannEntropy, CFC.log, trace_comp_cfc_eq_sum hsa b hb]
  have h : ∀ i, ⟪b i, density ω (b i)⟫_ℂ = r i := fun i => by
    rw [hb, inner_smul_right, b.inner_eq_one, mul_one]
  simp_rw [h, ← Complex.ofReal_mul, ← Complex.ofReal_sum, Complex.ofReal_re, Real.negMulLog,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

end Generic

namespace State

variable (ω : State (H →L[ℂ] H))

/-- The entropy of a state is that of its underlying element of the dual. -/
@[simp] lemma vonNeumannEntropy_val : S(ω.val) = S(ω) :=
  vonNeumannEntropy_congr fun _ => rfl

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
lemma umegakiEntropy_trace_eq_neg_vonNeumannEntropy :
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
lemma nontrivial (ω : State (H →L[ℂ] H)) : Nontrivial H := by
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
lemma maximallyMixed_apply (A : H →L[ℂ] H) :
    maximallyMixed H A = (Module.finrank ℂ H : ℂ)⁻¹ * Tr A := by
  simp [maximallyMixed, NNReal.smul_def]

variable (ω : State (H →L[ℂ] H))

/-- **`D(ω ‖ τ) = log d - S(ω)`**. -/
lemma umegakiEntropy_maximallyMixed :
    D(ω ∥ maximallyMixed H) = ((Real.log (Module.finrank ℂ H) - S(ω) : ℝ) : EReal) := by
  have hd : (0 : ℝ≥0) < (Module.finrank ℂ H : ℝ≥0)⁻¹ :=
    inv_pos.mpr (Nat.cast_pos.mpr Module.finrank_pos)
  rw [umegakiEntropy_congr ω (maximallyMixed H) (ψ₁ := PositiveLinearMap.ofClass ω)
      (φ₁ := (Module.finrank ℂ H : ℝ≥0)⁻¹ • tracePositiveLinearMap ℂ H) (fun _ => rfl)
      (fun _ => rfl), umegakiEntropy_smul_right hd,
    umegakiEntropy_congr (PositiveLinearMap.ofClass ω) (tracePositiveLinearMap ℂ H) (ψ₁ := ω)
      (φ₁ := tracePositiveLinearMap ℂ H) (fun _ => rfl) (fun _ => rfl),
    umegakiEntropy_trace_eq_neg_vonNeumannEntropy, PositiveLinearMap.coe_ofClass, apply_one,
    Complex.one_re, one_mul, NNReal.coe_inv, NNReal.coe_natCast, Real.log_inv, ← EReal.coe_sub]
  congr 1
  ring

/-- The maximally mixed state has the maximal entropy: `S(τ) = log d`. -/
lemma vonNeumannEntropy_maximallyMixed :
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

namespace StateSpace

/-- **Concavity** of the von Neumann entropy on the state space:
`S(a ω₁ + b ω₂) ≥ a S(ω₁) + b S(ω₂)`. With `S = -D(· ‖ tr)` and `tr = a tr + b tr`, this is joint
convexity of Umegaki's relative entropy (`umegakiEntropy_jointly_convex`). The finite form
`Σᵢ wᵢ S(ωᵢ) ≤ S(Σᵢ wᵢ ωᵢ)` is Jensen's inequality `ConcaveOn.le_map_sum`. -/
theorem concaveOn_vonNeumannEntropy :
    ConcaveOn ℝ (StateSpace (H →L[ℂ] H))
      (vonNeumannEntropy : WeakDual ℂ (H →L[ℂ] H) → ℝ) := by
  refine ⟨StateSpace.convex, fun x hx y hy a b ha hb hab => ?_⟩
  let ω : Fin 2 → State (H →L[ℂ] H) := ![⟨x, hx⟩, ⟨y, hy⟩]
  let w : Fin 2 → ℝ≥0 := ![⟨a, ha⟩, ⟨b, hb⟩]
  let ωc : State (H →L[ℂ] H) := ⟨a • x + b • y, StateSpace.convex hx hy ha hb hab⟩
  have hw : ∑ i, w i = 1 := by rw [Fin.sum_univ_two]; exact NNReal.eq hab
  have htr : tracePositiveLinearMap ℂ H = ∑ i, w i • tracePositiveLinearMap ℂ H := by
    rw [← Finset.sum_smul, hw, one_smul]
  have h := umegakiEntropy_jointly_convex Finset.univ w (fun i => PositiveLinearMap.ofClass (ω i))
    (fun _ => tracePositiveLinearMap ℂ H)
  rw [← htr, umegakiEntropy_congr (∑ i, w i • PositiveLinearMap.ofClass (ω i))
    (tracePositiveLinearMap ℂ H) (ψ₁ := ωc) (φ₁ := tracePositiveLinearMap ℂ H)
    (fun _ => by simp only [Fin.sum_univ_two]; rfl) (fun _ => rfl),
    State.umegakiEntropy_trace_eq_neg_vonNeumannEntropy] at h
  have hi : ∀ i, D(PositiveLinearMap.ofClass (ω i) ∥ tracePositiveLinearMap ℂ H) =
      ((-S(ω i) : ℝ) : EReal) := fun i => by
    rw [umegakiEntropy_congr (PositiveLinearMap.ofClass (ω i)) (tracePositiveLinearMap ℂ H)
      (ψ₁ := ω i) (φ₁ := tracePositiveLinearMap ℂ H) (fun _ => rfl) (fun _ => rfl),
      State.umegakiEntropy_trace_eq_neg_vonNeumannEntropy]
  simp_rw [hi, ← EReal.coe_mul] at h
  rw [← EReal.coe_finsetSum] at h
  have h' : -S(ωc) ≤ ∑ i, (w i : ℝ) * -S(ω i) := by exact_mod_cast h
  have hx' : S(x) = S(ω 0) := State.vonNeumannEntropy_val (ω 0)
  have hy' : S(y) = S(ω 1) := State.vonNeumannEntropy_val (ω 1)
  have hc : S(a • x + b • y) = S(ωc) := State.vonNeumannEntropy_val ωc
  have hw0 : ((w 0 : ℝ≥0) : ℝ) = a := rfl
  have hw1 : ((w 1 : ℝ≥0) : ℝ) = b := rfl
  simp only [Fin.sum_univ_two, mul_neg, hw0, hw1] at h'
  rw [smul_eq_mul, smul_eq_mul, hx', hy', hc]
  linarith

end StateSpace

namespace State

/-- **Invariance under `⋆`-isomorphisms**: `S(ω ∘ π) = S(ω)` for `π : B(K) ≃⋆ B(H)`, in particular
for unitary conjugations. Both `D` and the trace are invariant
(`umegakiEntropy_comp_starAlgEquiv`, `ContinuousLinearMap.trace_map`). -/
lemma vonNeumannEntropy_comp_starAlgEquiv {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [FiniteDimensional ℂ K] (π : (K →L[ℂ] K) ≃⋆ₐ[ℂ] (H →L[ℂ] H))
    (ω : State (H →L[ℂ] H)) : S(ω.comp π (map_one π)) = S(ω) := by
  have h := umegakiEntropy_comp_starAlgEquiv π (ψ₁ := ω.comp π (map_one π))
    (φ₁ := tracePositiveLinearMap ℂ K) (ψ := ω) (φ := tracePositiveLinearMap ℂ H) (fun _ => rfl)
    (fun X => (trace_map π X).symm)
  rw [umegakiEntropy_trace_eq_neg_vonNeumannEntropy, umegakiEntropy_trace_eq_neg_vonNeumannEntropy] at h
  have : -S(ω.comp π (map_one π)) = -S(ω) := by exact_mod_cast h
  linarith

end State
