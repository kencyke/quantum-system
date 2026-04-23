module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import QuantumSystem.Analysis.CFC.TraceClass.Basic

/-!
# Spectral formula for trace of CFC applied to trace-class operators

This file establishes the spectral trace formula for functions of trace-class
operators, via the continuous functional calculus (CFC).

## Main results

* `eigenvalue_mem_spectrum_real`: An eigenvalue of a self-adjoint bounded operator
  belongs to the real spectrum.
* `aeval_apply_eigenvector`: For a polynomial `q` and eigenvector `v` with
  `T v = μ • v`, we have `(aeval T q) v = q.eval μ • v`.
* `cfc_apply_eigenvector`: For continuous `f` and eigenvector `v` with
  `T v = μ • v`, we have `(cfc f T) v = f(μ) • v`.
* `trace_mul_cfc_eq_tsum`: For positive trace-class `T` with eigenbasis `b` and
  eigenvalues `σ`, `trace (T * cfc f T) = ∑' i, σ i * f(σ i)`.

## Implementation notes

The key technical lemma `cfc_apply_eigenvector` is proved by:
1. Polynomial induction for `aeval_apply_eigenvector`
2. `cfc_polynomial : cfc q.eval a = aeval a q` to connect CFC to polynomials
3. `polynomialFunctions.topologicalClosure` (Stone-Weierstrass) for density
4. `isometry_cfcHom` for norm convergence

This is the infinite-dimensional analogue of `trace_mul_matrixFunction` from
`QuantumSystem.Analysis.Matrix.HermitianFunctionalCalculus`.
-/

@[expose] public section

namespace ContinuousLinearMap

open scoped InnerProductSpace NNReal ContinuousFunctionalCalculus
open Complex Polynomial

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section EigenvectorCFC

variable {T : H →L[ℂ] H}

/-- An eigenvalue of a self-adjoint bounded operator on a Hilbert space
belongs to the real spectrum `σ ℝ T`. -/
lemma eigenvalue_mem_spectrum_real
    (_hsa : IsSelfAdjoint T) {μ : ℝ} {v : H} (hv : v ≠ 0) (hTv : T v = (μ : ℝ) • v) :
    μ ∈ spectrum ℝ T := by
  rw [spectrum.mem_iff]
  intro h_unit
  have h_apply : (algebraMap ℝ (H →L[ℂ] H) μ - T) v = 0 := by
    rw [ContinuousLinearMap.sub_apply, Algebra.algebraMap_eq_smul_one,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, hTv, sub_self]
  exact hv (by
    have h2 : (h_unit.unit⁻¹.val * (algebraMap ℝ (H →L[ℂ] H) μ - T)) v = 0 := by
      rw [ContinuousLinearMap.mul_apply, h_apply, map_zero]
    rwa [show h_unit.unit⁻¹.val * (algebraMap ℝ (H →L[ℂ] H) μ - T) = 1
      from h_unit.val_inv_mul, ContinuousLinearMap.one_apply] at h2)

/-- For a polynomial `q` and eigenvector satisfying `T v = μ • v`,
we have `(Polynomial.aeval T q) v = (Polynomial.eval μ q) • v`. -/
lemma aeval_apply_eigenvector
    {μ : ℝ} {v : H} (hTv : T v = (μ : ℝ) • v)
    (q : ℝ[X]) :
    (Polynomial.aeval T q) v = (q.eval μ : ℝ) • v := by
  induction q using Polynomial.induction_on' with
  | add p₁ p₂ ih₁ ih₂ =>
    simp only [map_add, ContinuousLinearMap.add_apply, eval_add, add_smul, ih₁, ih₂]
  | monomial n c =>
    simp only [aeval_monomial, eval_monomial]
    -- Goal: (algebraMap ℝ (H →L[ℂ] H) c * T ^ n) v = (c * μ ^ n) • v
    rw [ContinuousLinearMap.mul_apply]
    -- Need: T ^ n v = (μ ^ n : ℝ) • v
    have hTn : (T ^ n) v = (μ ^ n : ℝ) • v := by
      induction n with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, ContinuousLinearMap.mul_apply, hTv,
            ContinuousLinearMap.map_smul_of_tower, ih, smul_smul]
        congr 1; ring
    rw [hTn, ContinuousLinearMap.map_smul_of_tower,
        Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.one_apply, smul_smul, mul_comm c]

/-- **CFC eigenvector property**: For a self-adjoint operator `T` and eigenvector
satisfying `T v = μ • v`, the continuous functional calculus gives
`(cfc f T) v = f(μ) • v` for any continuous function `f` on the spectrum of `T`.

This is proved by polynomial approximation: the result holds for polynomials
(by `aeval_apply_eigenvector` and `cfc_polynomial`), and the general case
follows by density of polynomials in `C(σ ℝ T, ℝ)` (Stone-Weierstrass)
and the isometry of `cfcHom`. -/
lemma cfc_apply_eigenvector
    (hsa : IsSelfAdjoint T) {μ : ℝ} {v : H} (hv : v ≠ 0)
    (hTv : T v = (μ : ℝ) • v)
    (f : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ T)) :
    (cfc f T : H →L[ℂ] H) v = (f μ : ℝ) • v := by
  -- Step 1: μ is in the spectrum
  have hμ_spec : μ ∈ spectrum ℝ T := eigenvalue_mem_spectrum_real hsa hv hTv
  -- Step 2: The result holds for polynomials (via cfc_polynomial + aeval induction)
  have h_poly : ∀ q : ℝ[X],
      (cfc (fun x => q.eval x) T : H →L[ℂ] H) v = (q.eval μ : ℝ) • v := by
    intro q
    rw [show (fun x => q.eval x) = q.eval from rfl, cfc_polynomial q T hsa,
        aeval_apply_eigenvector hTv q]
  -- Step 3: Two continuous maps from C(σ ℝ T, ℝ) to H that agree on polynomials
  -- Φ₁(g) = cfcHom(g)(v) and Φ₂(g) = g(⟨μ, _⟩) • v
  -- Define the two maps: Φ₁(g) = cfcHom(g)(v) and Φ₂(g) = g(μ) • v
  -- We show they agree on polynomials, then by density on all of C(σ ℝ T, ℝ)
  let evAtV : (H →L[ℂ] H) →L[ℂ] H := ContinuousLinearMap.apply ℂ H v
  have hΦ₁_cont : Continuous (fun g : C(spectrum ℝ T, ℝ) =>
      evAtV (cfcHom (show IsSelfAdjoint T from hsa) g)) :=
    evAtV.continuous.comp (cfcHom_continuous (show IsSelfAdjoint T from hsa))
  have hΦ₂_cont : Continuous (fun g : C(spectrum ℝ T, ℝ) =>
      (g ⟨μ, hμ_spec⟩ : ℝ) • v) := by
    apply Continuous.smul _ continuous_const
    exact continuous_eval_const (⟨μ, hμ_spec⟩ : spectrum ℝ T)
  -- Polynomials agree
  have h_poly_agree : ∀ g ∈ (polynomialFunctions (spectrum ℝ T) : Set C(spectrum ℝ T, ℝ)),
      evAtV (cfcHom (show IsSelfAdjoint T from hsa) g) = (g ⟨μ, hμ_spec⟩ : ℝ) • v := by
    intro g hg
    rw [polynomialFunctions_coe] at hg
    obtain ⟨q, rfl⟩ := hg
    simp only [evAtV, ContinuousLinearMap.apply_apply]
    have hcfc : cfcHom (show IsSelfAdjoint T from hsa)
        (Polynomial.toContinuousMapOnAlgHom (spectrum ℝ T) q) =
        Polynomial.aeval T q := by
      rw [← cfc_polynomial q T hsa, cfc_apply (q.eval) T hsa]
      rfl
    rw [hcfc, aeval_apply_eigenvector hTv q]
    simp [Polynomial.toContinuousMapOnAlgHom, Polynomial.toContinuousMapOn]
  -- By density
  have h_dense : (polynomialFunctions (spectrum ℝ T)).topologicalClosure = ⊤ :=
    polynomialFunctions.topologicalClosure (spectrum ℝ T)
  have h_all_eq : ∀ g : C(spectrum ℝ T, ℝ),
      evAtV (cfcHom (show IsSelfAdjoint T from hsa) g) = (g ⟨μ, hμ_spec⟩ : ℝ) • v := by
    intro g
    have h_closed : IsClosed {g : C(spectrum ℝ T, ℝ) |
        evAtV (cfcHom (show IsSelfAdjoint T from hsa) g) = (g ⟨μ, hμ_spec⟩ : ℝ) • v} :=
      isClosed_eq hΦ₁_cont hΦ₂_cont
    have h_mem : g ∈ (polynomialFunctions (spectrum ℝ T)).topologicalClosure := by
      rw [h_dense]; trivial
    exact closure_minimal h_poly_agree h_closed h_mem
  -- Apply to f
  rw [cfc_apply f T hsa hf]
  exact h_all_eq ⟨fun x => f x.1, hf.restrict⟩

end EigenvectorCFC

section SpectralTraceFormula

variable {ι : Type u}

/-- Trace of a positive trace-class operator equals the sum of eigenvalues
over any eigenbasis. -/
lemma TraceClass.trace_eq_eigenvalue_tsum
    (T : TraceClass H)
    (hT_pos : 0 ≤ (T : H →L[ℂ] H))
    (b : HilbertBasis ι ℂ H) (σ : ι → ℝ)
    (hσ_eig : ∀ i, (T : H →L[ℂ] H) (b i) = (σ i : ℝ) • b i) :
    TraceClass.trace T = ∑' i, (σ i : ℂ) := by
  -- Use basis-independence: trace = ∑ᵢ ⟨bᵢ, T bᵢ⟩ for any basis
  unfold TraceClass.trace
  let ι' := Classical.choose (exists_hilbertBasis ℂ H)
  let b' : HilbertBasis ι' ℂ H := Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ H))
  -- The trace with b' equals the trace with b
  have h_eq := trace_sum_eq_of_nonneg hT_pos T.isTraceClass ι' b' ι b
  rw [h_eq]
  congr 1
  ext i
  rw [hσ_eig i]
  rw [← Complex.coe_smul, inner_smul_right, inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
  rw [b.orthonormal.1 i]
  simp

/-- For a positive trace-class operator `T` with eigenbasis `b` and eigenvalues `σ`,
and a continuous function `f` on `σ ℝ T` such that `T * cfc f T` is a positive
trace-class operator, we have `trace (T * cfc f T) = ∑' i, σ i * f(σ i)`. -/
lemma TraceClass.trace_mul_cfc_eq_tsum
    (T : TraceClass H)
    (hT_pos : 0 ≤ (T : H →L[ℂ] H))
    (b : HilbertBasis ι ℂ H) (σ : ι → ℝ)
    (hσ_eig : ∀ i, (T : H →L[ℂ] H) (b i) = (σ i : ℝ) • b i)
    (f : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ (T : H →L[ℂ] H)))
    (hTf : IsTraceClass ((T : H →L[ℂ] H) * cfc f (T : H →L[ℂ] H)))
    (hTf_pos : 0 ≤ (T : H →L[ℂ] H) * cfc f (T : H →L[ℂ] H)) :
    TraceClass.trace ⟨(T : H →L[ℂ] H) * cfc f (T : H →L[ℂ] H), hTf⟩ =
      ∑' i, ((σ i : ℂ) * (f (σ i) : ℝ)) := by
  -- T is self-adjoint (since positive)
  have hsa : IsSelfAdjoint (T : H →L[ℂ] H) := hT_pos.isSelfAdjoint
  -- cfc f T sends eigenvectors to eigenvectors with eigenvalue f(σ i)
  have hcfc_eig : ∀ i, (cfc f (T : H →L[ℂ] H)) (b i) = (f (σ i) : ℝ) • b i := by
    intro i
    by_cases hbi : b i = 0
    · simp [hbi]
    · exact cfc_apply_eigenvector hsa hbi (hσ_eig i) f hf
  -- Therefore (T * cfc f T)(bᵢ) = σᵢ * f(σᵢ) • bᵢ
  have h_prod_eig : ∀ i, ((T : H →L[ℂ] H) * cfc f (T : H →L[ℂ] H)) (b i) =
      ((σ i : ℂ) * (f (σ i) : ℝ)) • b i := by
    intro i
    rw [ContinuousLinearMap.mul_apply, hcfc_eig i,
        ContinuousLinearMap.map_smul_of_tower, hσ_eig i]
    simp only [← Complex.coe_smul, smul_smul]
    ring_nf
  -- Use basis-independence of trace for positive operators
  unfold TraceClass.trace
  let ι' := Classical.choose (exists_hilbertBasis ℂ H)
  let b' : HilbertBasis ι' ℂ H := Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ H))
  -- The trace with the chosen basis b' equals the trace with our eigenbasis b
  have h_inner : ∀ i, ⟪b i, ((T : H →L[ℂ] H) * cfc f (T : H →L[ℂ] H)) (b i)⟫_ℂ =
      ((σ i : ℂ) * (f (σ i) : ℝ)) := by
    intro i
    rw [h_prod_eig i, inner_smul_right, inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
    rw [b.orthonormal.1 i]
    simp
  rw [trace_sum_eq_of_nonneg hTf_pos hTf ι' b' ι b]
  exact tsum_congr h_inner

end SpectralTraceFormula

/-! ### Abbreviations for trace-class logarithm operations

These `abbrev`s hide repeated coercions `(ρ : H →L[ℂ] H)` and the `CFC.` prefix,
making theorem statements closer to mathematical notation. Since they are `abbrev`
(not `def`), they are transparent to `simp`, `rfl`, and definitional unfolding,
so existing proofs remain valid. -/

/-- Operator logarithm of a trace-class operator: `TraceClass.log ρ = CFC.log ↑ρ`. -/
noncomputable abbrev TraceClass.log (ρ : TraceClass H) : H →L[ℂ] H :=
  CFC.log (ρ : H →L[ℂ] H)

/-- The relative log difference `ρ(log ρ − log σ)` for trace-class operators. -/
noncomputable abbrev TraceClass.logDiff (ρ σ : TraceClass H) : H →L[ℂ] H :=
  (ρ : H →L[ℂ] H) * (TraceClass.log ρ - TraceClass.log σ)

/-- The self-log product `ρ · log ρ` for a trace-class operator. -/
noncomputable abbrev TraceClass.mulLog (ρ : TraceClass H) : H →L[ℂ] H :=
  (ρ : H →L[ℂ] H) * TraceClass.log ρ

/-! ### Typeclasses for trace-class logarithm conditions -/

/-- `HasLogTC ρ` asserts that `ρ · log ρ` is trace-class. -/
class TraceClass.HasLogTC (ρ : TraceClass H) : Prop where
  isTraceClass : IsTraceClass (TraceClass.mulLog ρ)

/-- `HasRelLogTC ρ σ` asserts that `ρ(log ρ − log σ)` is trace-class. -/
class TraceClass.HasRelLogTC (ρ σ : TraceClass H) : Prop where
  isTraceClass : IsTraceClass (TraceClass.logDiff ρ σ)

/-- D(ρ ‖ ρ) is always well-defined since log ρ − log ρ = 0. -/
instance TraceClass.hasRelLogTC_self (ρ : TraceClass H) : TraceClass.HasRelLogTC ρ ρ where
  isTraceClass := by
    show IsTraceClass (TraceClass.logDiff ρ ρ)
    simp only [TraceClass.logDiff, TraceClass.log, sub_self, mul_zero]
    exact zero_isTraceClass

end ContinuousLinearMap
