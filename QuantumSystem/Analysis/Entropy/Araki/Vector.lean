/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Algebra.VonNeumannAlgebra.Modular.Spatial
public import QuantumSystem.ForMathlib.MeasureTheory.Integral.EReal

/-!
# Araki's relative entropy of vector functionals

For a von Neumann algebra `M` on `H` and `ξ, η ∈ H`, **Araki's relative entropy** of the vector
functionals `ω_ξ = ⟪ξ, (·) ξ⟫` and `ω_η` on `M` is
`S(ω_ξ ‖ ω_η) = -⟪ξ, log Δ_{η,ξ} ξ⟫ = -∫ log λ dμ_ξ(λ)`,
where `Δ_{η,ξ}` is the relative modular operator (`VonNeumannAlgebra.relativeModular`) and `μ_ξ` its
scalar spectral measure at `ξ`. The value lies in `EReal`, with `-log 0 = +∞`
(`MeasureTheory.negLogIntegral`). The states need not be faithful: supports enter through the
support projections `s(ξ) = VonNeumannAlgebra.supportProj M ξ`.

## Conventions

* **Argument order.** `arakiVec M ξ η` is `S(ω_ξ ‖ ω_η)`: the first argument `ω_ξ` is the state
  being measured, the second `ω_η` the reference. The relative modular operator takes them in the
  opposite order, `Δ_{η,ξ} = VonNeumannAlgebra.relativeModular M η ξ` (Ohya–Petz's `Δ(η, ξ)`).
* **Finite dimensions.** For `M = B(ℂⁿ)` acting as `1 ⊗ B(ℂⁿ)` on `K ⊗̂ ℂⁿ` and `ξ`, `η`
  purifications of density matrices `ρ`, `σ`, this is Umegaki's `Tr ρ (log ρ - log σ)`, in the same
  slot order as `Matrix.relativeEntropy ρ σ` (`D(ρ ∥ σ)`):
  `VonNeumannAlgebra.arakiVec_purification` (and, for any representing vectors,
  `VonNeumannAlgebra.arakiVec_eq_relativeEntropy`); for normal states,
  `VonNeumannAlgebra.arakiEntropy_normalState`.
* **Commutative algebras.** On the diagonal algebra it is the Kullback–Leibler divergence
  `Σᵢ pᵢ log (pᵢ / qᵢ)` (`VonNeumannAlgebra.arakiVec_diagonalVec`), which pins the order: the
  first argument carries the weights `pᵢ` outside the logarithm.
* **Sign.** `S ≥ 0` for two states (`VonNeumannAlgebra.arakiVec_nonneg_of_norm_le`), and `S = +∞`
  when the support of the first functional is not under that of the second.

The expression `-⟪ξ, log Δ ξ⟫` is *defined* here through the spectral measure; the operator
`log Δ_{η,ξ}` itself is not constructed (it needs the Borel functional calculus, which is not
formalised).

## Main definitions

* `VonNeumannAlgebra.arakiVec M ξ η` — `S(ω_ξ ‖ ω_η) = -∫ log λ dμ_ξ(λ)` for `μ_ξ` the spectral
  measure of `Δ_{η,ξ}` at `ξ`.

## Main results

* `VonNeumannAlgebra.arakiVec_ne_bot` — `S ≠ -∞`, since `∫ λ dμ_ξ ≤ ‖s(ξ) η‖² < ∞`.
* `VonNeumannAlgebra.arakiVec_eq_top_of_not_supportProj_le` — `S = +∞` unless `s(ξ) ≤ s(η)`.
  The converse fails in infinite dimensions (not formalised here; e.g. on `ℓ^∞(ℕ)` with faithful
  states, `S` is the Kullback–Leibler divergence of two full-support probability sequences, which
  can be `+∞`); it holds for finite-dimensional `H` (`VonNeumannAlgebra.arakiVec_eq_top_iff`).
  `VonNeumannAlgebra.arakiVec_eq_top_of_supportProj_apply_eq_zero` — `S = +∞` if
  `ξ ≠ 0` and `s(ξ) η = 0`.
* `VonNeumannAlgebra.arakiVec_eq_of_inner_eq` — `S` depends only on the vector functionals
  `ω_ξ, ω_η` on `M`, not on the representing vectors.
* `VonNeumannAlgebra.arakiVec_of_intertwiner` — invariance under intertwiners `V : H → K`
  (spatial isomorphisms, amplifications): `S_N(ω_{Vξ} ‖ ω_{Vη}) = S_M(ω_ξ ‖ ω_η)`.
* `VonNeumannAlgebra.arakiVec_self` — `S(ω_ξ ‖ ω_ξ) = 0`.
* `VonNeumannAlgebra.arakiVec_smul_left`, `VonNeumannAlgebra.arakiVec_smul_right` — scaling of the
  first and of the second functional: `S(|c|² ω_ξ ‖ ω_η) = |c|² (S(ω_ξ ‖ ω_η) + ‖ξ‖² log |c|²)` and
  `S(ω_ξ ‖ |a|² ω_η) = S(ω_ξ ‖ ω_η) - ‖ξ‖² log |a|²`; for real `c > 0`,
  `S(ω_ξ ‖ c ω_η) = S(ω_ξ ‖ ω_η) - ‖ξ‖² log c` (`VonNeumannAlgebra.arakiVec_sqrt_smul_right`).
* `VonNeumannAlgebra.norm_sq_mul_log_le_arakiVec` — the **Klein bound** in Araki's sharp form
  `‖ξ‖² log (‖ξ‖² / ‖s(ξ) η‖²) ≤ S(ω_ξ ‖ ω_η)`, i.e. `ψ(1) log (ψ(1) / φ(s(ψ))) ≤ S(ψ ‖ φ)`;
  `VonNeumannAlgebra.norm_sq_mul_log_le_arakiVec_of_le` allows any `b ≥ ‖s(ξ) η‖²` in place of
  `‖s(ξ) η‖²`, e.g. `b = ‖η‖²` (`VonNeumannAlgebra.norm_sq_mul_log_div_norm_sq_le_arakiVec`).
* `VonNeumannAlgebra.arakiVec_nonneg` — `0 ≤ S(ω_ξ ‖ ω_η)` when `ω_η(s(ξ)) ≤ ω_ξ(1)`, in
  particular when `ω_η(1) ≤ ω_ξ(1)` (`VonNeumannAlgebra.arakiVec_nonneg_of_norm_le`), e.g. for
  two states.

## References

* H. Araki, *Relative entropy of states of von Neumann algebras*, Publ. RIMS 11 (1976), 809–833.
* M. Ohya, D. Petz, *Quantum Entropy and Its Use*, Chapter 5.
-/

@[expose] public section

open Complex MeasureTheory
open scoped InnerProductSpace VonNeumannAlgebra

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (M : VonNeumannAlgebra H) (ξ η : H)

/-- **Araki's relative entropy** `S(ω_ξ ‖ ω_η) = -⟪ξ, log Δ_{η,ξ} ξ⟫ = -∫ log λ dμ_ξ(λ)` of the
vector functionals `ω_ξ, ω_η` on `M`, where `μ_ξ` is the spectral measure at `ξ` of the relative
modular operator `Δ_{η,ξ}`, and `-log 0 = +∞`. -/
noncomputable def arakiVec : EReal :=
  negLogIntegral ((isSelfAdjoint_relativeModular M η ξ).spectralMeasure ξ)

/-! ### The spectral measure of `Δ_{η,ξ}` at `ξ` -/

/-- The spectral measure of `Δ_{η,ξ}` at `ξ` has total mass `‖ξ‖²`. -/
lemma measureReal_spectralMeasure_relativeModular_univ :
    ((isSelfAdjoint_relativeModular M η ξ).spectralMeasure ξ).real Set.univ = ‖ξ‖ ^ 2 := by
  rw [measureReal_def, IsSelfAdjoint.spectralMeasure_univ, ENNReal.toReal_ofReal (by positivity)]

/-- The spectral measure of `Δ_{η,ξ}` at `ξ` lives on `[0, ∞)`. -/
lemma ae_nonneg_spectralMeasure_relativeModular :
    ∀ᵐ t ∂(isSelfAdjoint_relativeModular M η ξ).spectralMeasure ξ, 0 ≤ t :=
  (isSelfAdjoint_relativeModular M η ξ).ae_nonneg_spectralMeasure ξ
    (isPositive_relativeModular M η ξ)

/-! ### Basic properties -/

/-- Araki's relative entropy is never `-∞`. -/
theorem arakiVec_ne_bot : M.arakiVec ξ η ≠ ⊥ :=
  negLogIntegral_ne_bot_of_lintegral_ne_top
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top lintegral_spectralMeasure_relativeModular_le)

variable {M ξ η} in
/-- **Support condition.** `S(ω_ξ ‖ ω_η) = +∞` unless `s(ξ) ≤ s(η)`. -/
theorem arakiVec_eq_top_of_not_supportProj_le (h : ¬ M.supportProj ξ ≤ M.supportProj η) :
    M.arakiVec ξ η = ⊤ := by
  refine negLogIntegral_eq_top_of_measure_Iic_ne_zero (fun h0 => h ?_) (arakiVec_ne_bot M ξ η)
  exact spectralMeasure_relativeModular_singleton_zero_eq_zero_iff.mp
    (measure_mono_null (Set.singleton_subset_iff.mpr (Set.mem_Iic.mpr le_rfl)) h0)

variable {M ξ η} in
/-- `S(ω_ξ ‖ ω_η) = +∞` if `ξ ≠ 0` and `s(ξ) η = 0`: then `∫ λ dμ_ξ = 0`, so `μ_ξ` is concentrated
at `0`. -/
theorem arakiVec_eq_top_of_supportProj_apply_eq_zero (hξ : ξ ≠ 0) (h : M.supportProj ξ η = 0) :
    M.arakiVec ξ η = ⊤ := by
  refine negLogIntegral_eq_top_of_lintegral_eq_zero (fun hμ => hξ ?_) ?_
  · have := IsSelfAdjoint.spectralMeasure_univ (isSelfAdjoint_relativeModular M η ξ) ξ
    rw [hμ, Measure.coe_zero, Pi.zero_apply, eq_comm, ENNReal.ofReal_eq_zero] at this
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm this (by positivity)))
  · refine nonpos_iff_eq_zero.mp (lintegral_spectralMeasure_relativeModular_le.trans ?_)
    simp [h]

variable {M ξ η} in
/-- **Independence of the vector representatives.** `S(ω_ξ ‖ ω_η)` depends only on the vector
functionals `ω_ξ` and `ω_η` on `M`. -/
theorem arakiVec_eq_of_inner_eq {ξ' η' : H} (hξ : ∀ x ∈ M, ⟪ξ, x ξ⟫_ℂ = ⟪ξ', x ξ'⟫_ℂ)
    (hη : ∀ x ∈ M, ⟪η, x η⟫_ℂ = ⟪η', x η'⟫_ℂ) : M.arakiVec ξ' η' = M.arakiVec ξ η := by
  rw [arakiVec, arakiVec, spectralMeasure_relativeModular_eq_of_inner_eq hξ hη]

/-- **Invariance under intertwiners.** Let `V : H → K` be bounded with `V† V ξ = ξ`, such that
every `x ∈ M` is intertwined with some `y ∈ N` (`y V = V x`, `y⋆ V = V x⋆`) and every `x′ ∈ M′`
with some `y′ ∈ N′` (e.g. a spatial isomorphism, or an amplification). Then
`S_N(ω_{Vξ} ‖ ω_{Vη}) = S_M(ω_ξ ‖ ω_η)`. -/
theorem arakiVec_of_intertwiner {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] {N : VonNeumannAlgebra K} {V : H →L[ℂ] K}
    (hM : ∀ x ∈ M, ∃ y ∈ N, y ∘L V = V ∘L x ∧ star y ∘L V = V ∘L star x)
    (hM' : ∀ x ∈ M′, ∃ y ∈ N′, y ∘L V = V ∘L x ∧ star y ∘L V = V ∘L star x)
    (hV : ContinuousLinearMap.adjoint V (V ξ) = ξ) :
    N.arakiVec (V ξ) (V η) = M.arakiVec ξ η := by
  rw [arakiVec, arakiVec, spectralMeasure_relativeModular_of_intertwiner hM hM' hV]

/-- `S(ω_ξ ‖ ω_ξ) = 0`. -/
@[simp]
theorem arakiVec_self : M.arakiVec ξ ξ = 0 := by
  rw [arakiVec, spectralMeasure_relativeModular_self, negLogIntegral_smul, negLogIntegral_dirac,
    ENNReal.ofReal_one, ENNReal.log_one, neg_zero, mul_zero]

/-! ### Scaling -/

variable {ξ} in
/-- **Scaling the first functional.**
`S(|c|² ω_ξ ‖ ω_η) = |c|² (S(ω_ξ ‖ ω_η) + ‖ξ‖² log |c|²)`. At `c = 0` both sides are `0`, using
Mathlib's `log 0 = 0` and `0 * ⊤ = 0` in `EReal`. -/
theorem arakiVec_smul_left (c : ℂ) :
    M.arakiVec (c • ξ) η =
      ((‖c‖ ^ 2 : ℝ) : EReal) * (M.arakiVec ξ η + ((‖ξ‖ ^ 2 * Real.log (‖c‖ ^ 2) : ℝ) : EReal)) := by
  rw [arakiVec, spectralMeasure_relativeModular_smul_right, negLogIntegral_smul]
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  rw [negLogIntegral_map_mul (by positivity), measureReal_spectralMeasure_relativeModular_univ,
    Real.log_inv, mul_neg, EReal.coe_neg, sub_eq_add_neg, neg_neg, arakiVec]
  norm_cast

variable {η} in
/-- **Scaling the second functional.** For `a ≠ 0`,
`S(ω_ξ ‖ |a|² ω_η) = S(ω_ξ ‖ ω_η) - ‖ξ‖² log |a|²`. -/
theorem arakiVec_smul_right {a : ℂ} (ha : a ≠ 0) :
    M.arakiVec ξ (a • η) = M.arakiVec ξ η - ((‖ξ‖ ^ 2 * Real.log (‖a‖ ^ 2) : ℝ) : EReal) := by
  rw [arakiVec, spectralMeasure_relativeModular_smul_left ha,
    negLogIntegral_map_mul (by positivity), measureReal_spectralMeasure_relativeModular_univ,
    arakiVec]

variable {η} in
/-- **Scaling the second functional** by a real `c > 0`: since `ω_{√c η} = c ω_η`,
`S(ω_ξ ‖ c ω_η) = S(ω_ξ ‖ ω_η) - ‖ξ‖² log c`. -/
theorem arakiVec_sqrt_smul_right {c : ℝ} (hc : 0 < c) :
    M.arakiVec ξ ((Real.sqrt c : ℂ) • η) =
      M.arakiVec ξ η - ((‖ξ‖ ^ 2 * Real.log c : ℝ) : EReal) := by
  rw [arakiVec_smul_right M ξ (ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hc).ne'), norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg c), Real.sq_sqrt hc.le]

/-! ### The Klein bound -/

variable {η} in
/-- **Klein bound** with an arbitrary upper bound `b ≥ ‖s(ξ) η‖²`:
`‖ξ‖² log (‖ξ‖² / b) ≤ S(ω_ξ ‖ ω_η)`. -/
theorem norm_sq_mul_log_le_arakiVec_of_le {b : ℝ} (hb : ‖M.supportProj ξ η‖ ^ 2 ≤ b) :
    ((‖ξ‖ ^ 2 * Real.log (‖ξ‖ ^ 2 / b) : ℝ) : EReal) ≤ M.arakiVec ξ η := by
  have := mul_log_le_negLogIntegral
    (lintegral_spectralMeasure_relativeModular_le.trans (ENNReal.ofReal_le_ofReal hb))
  rwa [measureReal_spectralMeasure_relativeModular_univ] at this

/-- **Klein bound**, in Araki's sharp form: `‖ξ‖² log (‖ξ‖² / ‖s(ξ) η‖²) ≤ S(ω_ξ ‖ ω_η)`, that is
`ψ(1) log (ψ(1) / φ(s(ψ))) ≤ S(ψ ‖ φ)` for `ψ = ω_ξ`, `φ = ω_η`. With Mathlib's conventions the
left side is `0` when `ξ = 0` or `s(ξ) η = 0`; in the latter case with `ξ ≠ 0`, in fact `S = +∞`
(`VonNeumannAlgebra.arakiVec_eq_top_of_supportProj_apply_eq_zero`). -/
theorem norm_sq_mul_log_le_arakiVec :
    ((‖ξ‖ ^ 2 * Real.log (‖ξ‖ ^ 2 / ‖M.supportProj ξ η‖ ^ 2) : ℝ) : EReal) ≤ M.arakiVec ξ η :=
  norm_sq_mul_log_le_arakiVec_of_le M ξ le_rfl

/-- **Klein bound**: `‖ξ‖² log (‖ξ‖² / ‖η‖²) ≤ S(ω_ξ ‖ ω_η)`, i.e.
`ψ(1) log (ψ(1) / φ(1)) ≤ S(ψ ‖ φ)`. With Mathlib's conventions the left side is `0` when `ξ = 0`
or `η = 0`. -/
theorem norm_sq_mul_log_div_norm_sq_le_arakiVec :
    ((‖ξ‖ ^ 2 * Real.log (‖ξ‖ ^ 2 / ‖η‖ ^ 2) : ℝ) : EReal) ≤ M.arakiVec ξ η :=
  norm_sq_mul_log_le_arakiVec_of_le M ξ
    (pow_le_pow_left₀ (norm_nonneg _) (Submodule.norm_starProjection_apply_le _ η) 2)

variable {M ξ η} in
/-- **Positivity.** `0 ≤ S(ω_ξ ‖ ω_η)` when `ω_η(s(ξ)) ≤ ω_ξ(1)`. -/
theorem arakiVec_nonneg (h : ‖M.supportProj ξ η‖ ≤ ‖ξ‖) : 0 ≤ M.arakiVec ξ η := by
  refine le_trans ?_ (norm_sq_mul_log_le_arakiVec M ξ η)
  rw [← EReal.coe_zero, EReal.coe_le_coe_iff]
  refine mul_nonneg (by positivity) ?_
  rcases eq_or_ne (M.supportProj ξ η) 0 with h0 | h0
  · simp [h0]
  exact Real.log_nonneg ((one_le_div (by positivity)).mpr (pow_le_pow_left₀ (norm_nonneg _) h 2))

variable {M ξ η} in
/-- **Positivity.** `0 ≤ S(ω_ξ ‖ ω_η)` when `ω_η(1) ≤ ω_ξ(1)`; in particular for two states. -/
theorem arakiVec_nonneg_of_norm_le (h : ‖η‖ ≤ ‖ξ‖) : 0 ≤ M.arakiVec ξ η :=
  arakiVec_nonneg ((Submodule.norm_starProjection_apply_le _ η).trans h)

/-! ### Finite dimensions -/

variable {M ξ η} in
/-- In finite dimensions, `S(ω_ξ ‖ ω_η) = +∞` exactly when `s(ξ) ≰ s(η)`. -/
theorem arakiVec_eq_top_iff [FiniteDimensional ℂ H] :
    M.arakiVec ξ η = ⊤ ↔ ¬ M.supportProj ξ ≤ M.supportProj η := by
  refine ⟨fun htop hle => ?_, arakiVec_eq_top_of_not_supportProj_le⟩
  set μ := (isSelfAdjoint_relativeModular M η ξ).spectralMeasure ξ
  obtain ⟨F, hF, hFμ⟩ := (isSelfAdjoint_relativeModular M η ξ).exists_finite_spectralMeasure_compl_eq_zero
  have h0 : μ {0} = 0 := spectralMeasure_relativeModular_singleton_zero_eq_zero_iff.mpr hle
  -- `μ` lives on the finite set `F ∩ (0, ∞)`, which has a positive lower bound.
  set S := F ∩ Set.Ioi 0
  obtain ⟨δ, hδ, hδS⟩ : ∃ δ > 0, ∀ t ∈ S, δ ≤ t := by
    rcases S.eq_empty_or_nonempty with hS | hS
    · exact ⟨1, one_pos, by simp [hS]⟩
    have hSf : S.Finite := hF.inter_of_left _
    exact ⟨sInf S, (hS.csInf_mem hSf).2, fun t ht => csInf_le hSf.bddBelow ht⟩
  refine negLogIntegral_ne_top_of_ae_ge hδ ?_ htop
  have hS : ∀ᵐ t ∂μ, t ∈ S := by
    have hF' : ∀ᵐ t ∂μ, t ∈ F := measure_eq_zero_iff_ae_notMem.mp (hFμ ξ) |>.mono fun t ht => by
      simpa using ht
    have h0' : ∀ᵐ t ∂μ, t ≠ 0 := measure_eq_zero_iff_ae_notMem.mp h0
    filter_upwards [hF', h0', ae_nonneg_spectralMeasure_relativeModular M ξ η] with t htF ht0 htn
    exact ⟨htF, lt_of_le_of_ne htn (Ne.symm ht0)⟩
  exact hS.mono hδS

end VonNeumannAlgebra
