/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Algebra.VonNeumannAlgebra.Modular.Spatial
public import QuantumSystem.ForMathlib.Analysis.Normed.Module.FiniteDimension
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
  purifications of positive semidefinite matrices `ρ`, `σ`, this is Umegaki's
  `Tr ρ (log ρ - log σ)` (natural logarithm, unit nat), in the same
  slot order as Umegaki's relative entropy `Matrix.umegakiEntropy ρ σ` (`D(ρ ∥ σ)`), which is
  defined as `S(ω_ρ ‖ ω_σ)`: `VonNeumannAlgebra.arakiVec_purification` (and, for any representing
  vectors, `VonNeumannAlgebra.arakiVec_eq_umegakiEntropy`); for normal functionals,
  `VonNeumannAlgebra.arakiEntropy_normalFunctional`.
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
  can be `+∞`); it holds for finite-dimensional `M`, in particular for finite-dimensional `H`
  (`VonNeumannAlgebra.arakiVec_eq_top_iff`).
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
* `VonNeumannAlgebra.arakiVec_le_of_norm_sq_le` — the **domination bound**: if `ω_ξ ≤ c ω_η`
  on `M`, then `S(ω_ξ ‖ ω_η) ≤ ‖ξ‖² log c`.
* `VonNeumannAlgebra.exists_norm_sq_le_of_supportProj_le` — for finite-dimensional `M`,
  `s(ξ) ≤ s(η)` gives `ω_ξ ≤ c ω_η` for some `c > 0`.

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

/-! ### Domination -/

variable {M ξ η} in
/-- **Domination bound.** If `ω_ξ ≤ c ω_η` on `M`, in the form `‖x ξ‖² ≤ c ‖x η‖²` for every
`x ∈ M`, then `S(ω_ξ ‖ ω_η) ≤ ‖ξ‖² log c`, i.e. `ψ ≤ c φ ⇒ S(ψ ‖ φ) ≤ ψ(1) log c`.

With `η' = √c η`, every point `(a ξ + ζ, s(ξ) a⋆ η')` of the graph of `S_{η',ξ}` is dominated by
the point `(a ξ, s(ξ) a⋆ ξ)` of the graph of `S_{ξ,ξ}`, so the resolvents compare as
`⟪ξ, (t + Δ_{η',ξ})⁻¹ ξ⟫ ≤ ⟪ξ, (t + Δ_{ξ,ξ})⁻¹ ξ⟫` and `S(ω_ξ ‖ ω_{η'}) ≤ S(ω_ξ ‖ ω_ξ) = 0`. -/
theorem arakiVec_le_of_norm_sq_le {c : ℝ} (hc : 0 < c)
    (h : ∀ x ∈ M, ‖x ξ‖ ^ 2 ≤ c * ‖x η‖ ^ 2) :
    M.arakiVec ξ η ≤ ((‖ξ‖ ^ 2 * Real.log c : ℝ) : EReal) := by
  set η' : H := (Real.sqrt c : ℂ) • η
  have h' : ∀ x ∈ M, ‖x ξ‖ ≤ ‖x η'‖ := by
    intro x hx
    have hη' : ‖x η'‖ ^ 2 = c * ‖x η‖ ^ 2 := by
      rw [map_smul, norm_smul, mul_pow, norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt hc.le]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp (hη' ▸ h x hx)
  have hres : ∀ t : ℝ, 0 < t →
      ∫ s, (t + s)⁻¹ ∂(isSelfAdjoint_relativeModular M η' ξ).spectralMeasure ξ ≤
        ∫ s, (t + s)⁻¹ ∂(isSelfAdjoint_relativeModular M ξ ξ).spectralMeasure ξ := by
    intro t ht
    refine (isSelfAdjoint_relativeModular M ξ ξ).integral_inv_add_spectralMeasure_le_of_forall_mem_graph
      (restrictScalars_relativeModular M ξ ξ) (isSelfAdjoint_relativeModular M η' ξ)
      (isClosable_relativeTomita M η' ξ) (restrictScalars_relativeModular M η' ξ) ξ ξ ?_ ht
    intro w w' hw
    obtain ⟨a, ha, z, hz, hwz⟩ := mem_graph_relativeTomita.mp hw
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hwz
    have hK : a ξ ∈ (InnerProductSpace.cyclicSubspace (M : Set (H →L[ℂ] H)) ξ).toSubmodule :=
      InnerProductSpace.apply_mem_cyclicSubspace ξ ha
    have hK₁ : ξ ∈ (InnerProductSpace.cyclicSubspace (M : Set (H →L[ℂ] H)) ξ).toSubmodule :=
      self_mem_cyclicSubspace M ξ
    refine ⟨a ξ, M.supportProj ξ (star a ξ),
      mem_graph_closure_relativeTomita (apply_mem_graph_relativeTomita ha), ?_, ?_, ?_⟩
    · have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) (a ξ) z
        (Submodule.inner_right_of_mem_orthogonal hK hz)
      nlinarith [norm_nonneg (a ξ), norm_nonneg (a ξ + z), norm_nonneg z]
    · exact h' _ (mul_mem (M.supportProj_mem ξ) (star_mem ha))
    · rw [inner_add_right, Submodule.inner_right_of_mem_orthogonal hK₁ hz, add_zero]
  have hle := negLogIntegral_le_of_integral_inv_add_le
    (ae_nonneg_spectralMeasure_relativeModular M ξ η')
    (by rw [IsSelfAdjoint.spectralMeasure_univ, IsSelfAdjoint.spectralMeasure_univ])
    (arakiVec_ne_bot M ξ ξ) hres
  change M.arakiVec ξ η' ≤ M.arakiVec ξ ξ at hle
  rw [arakiVec_self, arakiVec_sqrt_smul_right M ξ hc] at hle
  exact EReal.sub_nonpos.mp hle

/-! ### Finite-dimensional algebras -/

variable {M ξ η} in
/-- If `M` is finite-dimensional and `s(ξ) ≤ s(η)`, then `ω_ξ ≤ c ω_η` for some `c > 0`, in the
form `‖x ξ‖² ≤ c ‖x η‖²` for every `x ∈ M`: the kernel of `x ↦ x η` lies in that of `x ↦ x ξ`,
and on the finite-dimensional `M` this is a norm domination. -/
theorem exists_norm_sq_le_of_supportProj_le [FiniteDimensional ℂ M]
    (hle : M.supportProj ξ ≤ M.supportProj η) :
    ∃ c > 0, ∀ x ∈ M, ‖x ξ‖ ^ 2 ≤ c * ‖x η‖ ^ 2 := by
  have hξ : M.supportProj η ξ = ξ :=
    (supportProj_le_iff (M.isStarProjection_supportProj η) (M.supportProj_mem η)).mp hle
  obtain ⟨C, hC⟩ := LinearMap.exists_norm_le_mul_norm_of_ker_le (M.applyₗ ξ) (M.applyₗ η)
    fun x hx => by
      change (x : H →L[ℂ] H) η = 0 at hx
      change (x : H →L[ℂ] H) ξ = 0
      calc (x : H →L[ℂ] H) ξ = ((x : H →L[ℂ] H) * M.supportProj η) ξ := by
            rw [mul_apply_eq_comp, hξ]
        _ = 0 := by rw [(mul_supportProj_eq_zero_iff x.2).mpr hx, zero_apply]
  refine ⟨C ^ 2 + 1, by positivity, fun x hx => ?_⟩
  have h1 : ‖x ξ‖ ≤ C * ‖x η‖ := hC ⟨x, hx⟩
  have h2 : ‖x ξ‖ ^ 2 ≤ (C * ‖x η‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg ‖x η‖]

variable {M ξ η} in
/-- **Support characterisation of `+∞`** for a finite-dimensional algebra: `S(ω_ξ ‖ ω_η) = +∞`
exactly when `s(ξ) ≰ s(η)`. When `s(ξ) ≤ s(η)`, `ω_ξ ≤ c ω_η` for some `c > 0`
(`VonNeumannAlgebra.exists_norm_sq_le_of_supportProj_le`), so `S ≤ ‖ξ‖² log c < ∞`
(`VonNeumannAlgebra.arakiVec_le_of_norm_sq_le`). This covers every finite-dimensional `H`. -/
theorem arakiVec_eq_top_iff [FiniteDimensional ℂ M] :
    M.arakiVec ξ η = ⊤ ↔ ¬ M.supportProj ξ ≤ M.supportProj η := by
  refine ⟨fun htop hle => ?_, arakiVec_eq_top_of_not_supportProj_le⟩
  obtain ⟨c, hc, h⟩ := exists_norm_sq_le_of_supportProj_le hle
  exact (arakiVec_le_of_norm_sq_le hc h).not_gt (htop ▸ EReal.coe_lt_top _)

end VonNeumannAlgebra
