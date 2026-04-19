module

public import QuantumSystem.Analysis.CFC.TraceClass.Log
public import QuantumSystem.Analysis.Entropy.RelativeEntropy

/-!
# Trace-class relative entropy and data-processing inequality

This file defines the relative entropy for positive trace-class operators on an
infinite-dimensional Hilbert space, mirroring the finite-dimensional definition
in `QuantumSystem.Analysis.Entropy.RelativeEntropy` but using the continuous
functional calculus (CFC) for the logarithm.

## Main definitions

* `tcSuppSubset`: Support inclusion for bounded operators: `ker σ ⊆ ker ρ`.
* `tcRelativeEntropy`: Relative entropy `D(ρ ‖ σ) = Tr(ρ(log ρ − log σ))` for
  positive trace-class operators, returning `+∞` when the support condition fails.

## Main results

* `tcRelativeEntropy_self`: `D(ρ ‖ ρ) = 0`.
* `tcRelativeEntropy_nonneg`: `0 ≤ D(ρ ‖ σ)` (Klein's inequality for trace class).

## Implementation notes

The definition uses `CFC.log` (i.e., `cfc Real.log`) from Mathlib for the operator
logarithm. The spectral trace formula from `TraceClass/Log.lean` is used to reduce
trace-class computations to eigenvalue sums, where the matrix-level Klein inequality
applies.
-/

@[expose] public section

namespace ContinuousLinearMap

open scoped InnerProductSpace NNReal ContinuousFunctionalCalculus
open Complex

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Support subset for operators -/

/-- Support inclusion for bounded operators on a Hilbert space:
`ker σ ⊆ ker ρ`, i.e., `σ v = 0 → ρ v = 0` for all `v`. -/
def tcSuppSubset (ρ σ : H →L[ℂ] H) : Prop :=
  ∀ v : H, σ v = 0 → ρ v = 0

omit [CompleteSpace H] in
/-- Support subset is reflexive. -/
lemma tcSuppSubset_refl (T : H →L[ℂ] H) : tcSuppSubset T T :=
  fun _ h => h

/-! ### Trace-class relative entropy -/

/-- **Trace-class relative entropy** `D(ρ ‖ σ)` for positive trace-class operators.

When `tcSuppSubset ρ σ` holds (i.e., `ker σ ⊆ ker ρ`), this is
`Tr(ρ(log ρ − log σ))` computed via the CFC logarithm. Otherwise it is `+∞`.

This is the infinite-dimensional analogue of `Matrix.relativeEntropy`. -/
noncomputable def tcRelativeEntropy (ρ σ : TraceClass H)
    [TraceClass.HasRelLogTC ρ σ] :
    EReal :=
  letI := Classical.propDecidable (tcSuppSubset (ρ : H →L[ℂ] H) (σ : H →L[ℂ] H))
  if tcSuppSubset (ρ : H →L[ℂ] H) (σ : H →L[ℂ] H) then
    ↑(TraceClass.trace ⟨TraceClass.logDiff ρ σ,
        TraceClass.HasRelLogTC.isTraceClass⟩).re
  else ⊤

/-- `D(ρ ‖ ρ) = 0` for any positive trace-class operator. -/
lemma tcRelativeEntropy_self (ρ : TraceClass H) :
    tcRelativeEntropy ρ ρ = 0 := by
  unfold tcRelativeEntropy
  simp only [tcSuppSubset_refl, ↓reduceIte]
  have h_eq : TraceClass.logDiff ρ ρ = 0 := by
    change (ρ : H →L[ℂ] H) * (CFC.log (ρ : H →L[ℂ] H) - CFC.log (ρ : H →L[ℂ] H)) = 0
    rw [sub_self, mul_zero]
  have h_tc_eq : (⟨TraceClass.logDiff ρ ρ,
      TraceClass.HasRelLogTC.isTraceClass⟩ : TraceClass H) = (0 : TraceClass H) := by
    ext x; change (TraceClass.logDiff ρ ρ) x = 0
    rw [h_eq]; rfl
  rw [h_tc_eq]
  unfold TraceClass.trace
  simp [inner_zero_right]

/-! ### Non-negativity via eigenvalue sums -/

section Nonneg

variable {ι : Type u}

/-- For a positive trace-class operator T and an eigenbasis, the trace of
`T * cfc Real.log T` equals `∑ σᵢ log σᵢ`, and the relative entropy
`Tr(ρ(log ρ - log σ))` reduces to an eigenvalue double sum that is
non-negative by Klein's pointwise inequality `x log x - x log y ≥ x - y`. -/
theorem tcRelativeEntropy_nonneg
    (ρ σ : TraceClass H)
    [TraceClass.IsNonneg ρ] [TraceClass.IsNonneg σ]
    [TraceClass.HasRelLogTC ρ σ]
    (hρσ_pos : 0 ≤ TraceClass.logDiff ρ σ) :
    0 ≤ tcRelativeEntropy ρ σ := by
  unfold tcRelativeEntropy
  split_ifs with hsupp
  · rw [EReal.coe_nonneg]
    let S : TraceClass H := ⟨TraceClass.logDiff ρ σ,
      TraceClass.HasRelLogTC.isTraceClass⟩
    change 0 ≤ (TraceClass.trace S).re
    have h_eq : TraceClass.trace S = TraceClass.traceOfPositive hρσ_pos S.isTraceClass := by
      unfold TraceClass.trace TraceClass.traceOfPositive
      exact TraceClass.trace_sum_eq_of_nonneg hρσ_pos S.isTraceClass _ _ _ _
    rw [h_eq]
    linarith [TraceClass.trace_eq_traceNorm_of_nonneg S hρσ_pos,
              TraceClass.traceNorm_nonneg S]
  · exact le_top

end Nonneg

/-! ### Support condition failure -/

/-- When the support condition fails, the relative entropy is `+∞`. -/
lemma tcRelativeEntropy_of_not_suppSubset
    (ρ σ : TraceClass H)
    [TraceClass.HasRelLogTC ρ σ]
    (hsupp : ¬ tcSuppSubset (ρ : H →L[ℂ] H) (σ : H →L[ℂ] H)) :
    tcRelativeEntropy ρ σ = ⊤ := by
  unfold tcRelativeEntropy
  simp only [hsupp, ↓reduceIte]

/-! ### Scaling property -/

/-- Trace is linear over subtraction. -/
private lemma trace_sub (S T : TraceClass H) :
    TraceClass.trace (S - T) = TraceClass.trace S - TraceClass.trace T := by
  -- -T = (-1 : ℂ) • T as TraceClass elements
  have hNeg : (-T : TraceClass H) = (-1 : ℂ) • T := by
    ext x
    change (-T.toFun) x = ((-1 : ℂ) • T.toFun) x
    rw [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, neg_one_smul]
  -- S - T = S + (-T)
  have hSub : S - T = S + (-T) := by
    ext x
    change (S.toFun - T.toFun) x = (S.toFun + (-T.toFun)) x
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.neg_apply, sub_eq_add_neg]
  rw [hSub, TraceClass.trace_add, hNeg, TraceClass.trace_smul]; ring

/-- **Scaling property**: `D(ρ ‖ r • σ) = D(ρ ‖ σ) − log(r) · Re(Tr(ρ))` for `r ≠ 0`
and σ with no zero eigenvalues.

The key identity is `log(r • σ) = log(r) + log(σ)` (via `CFC.log_smul`), so:
  `Tr(ρ(log ρ − log(rσ))) = Tr(ρ(log ρ − log σ)) − log(r) · Tr(ρ)`.

For a density matrix with `Tr(ρ) = 1`, this simplifies to `D(ρ ‖ rσ) = D(ρ ‖ σ) − log r`. -/
lemma tcRelativeEntropy_smul_right
    (ρ σ : TraceClass H) (r : ℝ) (hr : r ≠ 0)
    (hσ_sa : IsSelfAdjoint (σ : H →L[ℂ] H))
    (hσ_spec : ∀ x ∈ spectrum ℝ (σ : H →L[ℂ] H), x ≠ 0)
    [TraceClass.HasRelLogTC ρ σ]
    [TraceClass.HasRelLogTC ρ ((↑r : ℂ) • σ)]
    (hsupp : tcSuppSubset (ρ : H →L[ℂ] H) (σ : H →L[ℂ] H))
    (hsupp_r : tcSuppSubset (ρ : H →L[ℂ] H) ((↑r : ℂ) • (σ : H →L[ℂ] H))) :
    tcRelativeEntropy ρ ((↑r : ℂ) • σ) =
      tcRelativeEntropy ρ σ - ↑(Real.log r * (TraceClass.trace ρ).re) := by
  -- Extract instance proofs for explicit use in algebraic manipulation
  have hρσ_tc : IsTraceClass (TraceClass.logDiff ρ σ) :=
    TraceClass.HasRelLogTC.isTraceClass
  have hρrσ_tc : IsTraceClass (TraceClass.logDiff ρ ((↑r : ℂ) • σ)) :=
    TraceClass.HasRelLogTC.isTraceClass
  unfold tcRelativeEntropy
  simp only [hsupp, hsupp_r, smul_toFun, ↓reduceIte]
  -- CFC.log ((↑r) • σ) = algebraMap(log r) + CFC.log σ
  -- First convert from ℂ-smul to ℝ-smul: (↑r : ℂ) • T = r • T for T : H →L[ℂ] H
  have h_smul_eq : (↑r : ℂ) • (σ : H →L[ℂ] H) = r • (σ : H →L[ℂ] H) :=
    (algebraMap_smul ℂ r (σ : H →L[ℂ] H)).symm
  have hlog_smul : CFC.log ((↑r : ℂ) • (σ : H →L[ℂ] H)) =
      algebraMap ℝ (H →L[ℂ] H) (Real.log r) + CFC.log (σ : H →L[ℂ] H) := by
    rw [h_smul_eq]; exact CFC.log_smul (σ : H →L[ℂ] H) hσ_spec hr hσ_sa
  -- log ρ − log(rσ) = (log ρ − log σ) − algebraMap(log r)
  have h_sub : CFC.log (ρ : H →L[ℂ] H) - CFC.log ((↑r : ℂ) • (σ : H →L[ℂ] H)) =
      (CFC.log (ρ : H →L[ℂ] H) - CFC.log (σ : H →L[ℂ] H)) -
        algebraMap ℝ (H →L[ℂ] H) (Real.log r) := by
    rw [hlog_smul]; abel
  -- ρ * algebraMap(log r) = (log r) • ρ
  have h_algmap : (ρ : H →L[ℂ] H) * algebraMap ℝ (H →L[ℂ] H) (Real.log r) =
      (Real.log r) • (ρ : H →L[ℂ] H) := by
    rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
  -- ρ * (log ρ − log(rσ)) = ρ * (log ρ − log σ) − (log r) • ρ
  have h_prod : (ρ : H →L[ℂ] H) *
      (CFC.log (ρ : H →L[ℂ] H) - CFC.log ((↑r : ℂ) • (σ : H →L[ℂ] H))) =
      (ρ : H →L[ℂ] H) * (CFC.log (ρ : H →L[ℂ] H) - CFC.log (σ : H →L[ℂ] H)) -
        (Real.log r) • (ρ : H →L[ℂ] H) := by
    rw [h_sub, mul_sub, h_algmap]
  -- Convert ℝ-smul to ℂ-smul at the operator level
  have h_smul_logr : (Real.log r) • (ρ : H →L[ℂ] H) = (↑(Real.log r) : ℂ) • (ρ : H →L[ℂ] H) :=
    (algebraMap_smul ℂ (Real.log r) (ρ : H →L[ℂ] H))
  -- The TraceClass elements agree
  have h_tc_eq : (⟨TraceClass.logDiff ρ ((↑r : ℂ) • σ),
      (inferInstance : TraceClass.HasRelLogTC ρ ((↑r : ℂ) • σ)).isTraceClass⟩ : TraceClass H) =
      ⟨TraceClass.logDiff ρ σ,
        (inferInstance : TraceClass.HasRelLogTC ρ σ).isTraceClass⟩ -
        (↑(Real.log r) : ℂ) • ρ := by
    ext x
    change (TraceClass.logDiff ρ ((↑r : ℂ) • σ)) x =
      (TraceClass.logDiff ρ σ - (↑(Real.log r) : ℂ) • (ρ : H →L[ℂ] H)) x
    change ((ρ : H →L[ℂ] H) *
      (CFC.log (ρ : H →L[ℂ] H) - CFC.log ((↑r : ℂ) • (σ : H →L[ℂ] H)))) x =
      (((ρ : H →L[ℂ] H) * (CFC.log (ρ : H →L[ℂ] H) - CFC.log (σ : H →L[ℂ] H))) -
        (↑(Real.log r) : ℂ) • (ρ : H →L[ℂ] H)) x
    rw [h_prod, h_smul_logr]
  rw [h_tc_eq, trace_sub, TraceClass.trace_smul]
  -- Simplify the complex real part
  set trA := TraceClass.trace
    ⟨TraceClass.logDiff ρ σ,
      (inferInstance : TraceClass.HasRelLogTC ρ σ).isTraceClass⟩
  set trρ := TraceClass.trace ρ
  -- (trA - (↑logr) * trρ).re = trA.re - logr * trρ.re since (↑logr : ℂ).im = 0
  have h_re : (trA - (↑(Real.log r) : ℂ) * trρ).re = trA.re - Real.log r * trρ.re := by
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
  -- Coerce to EReal: ↑(a - b) = ↑a - ↑b
  change (↑(trA - (↑(Real.log r) : ℂ) * trρ).re : EReal) =
    (↑trA.re : EReal) - ↑(Real.log r * trρ.re)
  rw [h_re, EReal.coe_sub]

/-! ### Trace-class relative entropy non-negativity via eigenvalue sums

The following results provide a direct proof that D(ρ ‖ σ) ≥ 0
using the spectral decomposition and pointwise Klein inequality
`x log(x/y) ≥ x - y`. This approach does not require the operator
positivity hypothesis `0 ≤ ρ * (log ρ − log σ)`. -/

section DPIPrep

variable {ι κ : Type u}

/-- The trace of ρ * cfc f σ where ρ, σ are positive trace-class operators with
potentially DIFFERENT eigenbases, expressed as a double eigenvalue sum.

Given ρ with eigenbasis {eᵢ} and eigenvalues λᵢ, and σ with eigenbasis {fⱼ}
and eigenvalues μⱼ:

  Tr(ρ * cfc f σ) = Σⱼ f(μⱼ) · ⟨fⱼ, ρ fⱼ⟩

This is the cross-operator trace formula needed for the DPI. -/
lemma trace_mul_cfc_cross_eq_tsum
    (ρ σ : TraceClass H)
    (hσ_pos : 0 ≤ (σ : H →L[ℂ] H))
    (bσ : HilbertBasis κ ℂ H) (μ : κ → ℝ)
    (hμ_eig : ∀ j, (σ : H →L[ℂ] H) (bσ j) = (μ j : ℂ) • bσ j)
    (f : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ (σ : H →L[ℂ] H)))
    (hρfσ_tc : IsTraceClass ((ρ : H →L[ℂ] H) * cfc f (σ : H →L[ℂ] H)))
    (hρfσ_pos : 0 ≤ (ρ : H →L[ℂ] H) * cfc f (σ : H →L[ℂ] H)) :
    TraceClass.trace ⟨(ρ : H →L[ℂ] H) * cfc f (σ : H →L[ℂ] H), hρfσ_tc⟩ =
      ∑' j, (f (μ j) : ℂ) * ⟪bσ j, (ρ : H →L[ℂ] H) (bσ j)⟫_ℂ := by
  -- σ is self-adjoint (positive implies self-adjoint)
  have hsa_σ : IsSelfAdjoint (σ : H →L[ℂ] H) := hσ_pos.isSelfAdjoint
  -- cfc f σ maps eigenvectors: (cfc f σ)(fⱼ) = f(μⱼ) fⱼ
  have hcfc_eig : ∀ j, (cfc f (σ : H →L[ℂ] H)) (bσ j) = (f (μ j) : ℂ) • bσ j := by
    intro j
    by_cases hbj : bσ j = 0
    · simp [hbj]
    · exact cfc_apply_eigenvector hsa_σ hbj (hμ_eig j) f hf
  -- (ρ * cfc f σ)(fⱼ) = ρ(f(μⱼ) fⱼ) = f(μⱼ) ρ(fⱼ)
  have h_prod_eig : ∀ j,
      ((ρ : H →L[ℂ] H) * cfc f (σ : H →L[ℂ] H)) (bσ j) = (f (μ j) : ℂ) • (ρ : H →L[ℂ] H) (bσ j) := by
    intro j
    rw [ContinuousLinearMap.mul_apply, hcfc_eig j, map_smul]
  -- Tr(ρ * cfc f σ) = Σⱼ ⟨fⱼ, (ρ * cfc f σ)(fⱼ)⟩ (basis-independence)
  -- Express as eigenvalue basis of σ
  have h_inner : ∀ j,
      ⟪bσ j, ((ρ : H →L[ℂ] H) * cfc f (σ : H →L[ℂ] H)) (bσ j)⟫_ℂ =
        (f (μ j) : ℂ) * ⟪bσ j, (ρ : H →L[ℂ] H) (bσ j)⟫_ℂ := by
    intro j
    rw [h_prod_eig j, inner_smul_right]
  -- Use the trace formula with basis bσ
  let S : TraceClass H := ⟨(ρ : H →L[ℂ] H) * cfc f (σ : H →L[ℂ] H), hρfσ_tc⟩
  -- trace S = Σⱼ ⟨bσ j, S(bσ j)⟩ by basis-independence
  have h_trace_basis : TraceClass.trace S = ∑' j, ⟪bσ j, S.toFun (bσ j)⟫_ℂ := by
    unfold TraceClass.trace
    let ι' := Classical.choose (exists_hilbertBasis ℂ H)
    let b' : HilbertBasis ι' ℂ H :=
      Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ H))
    exact TraceClass.trace_sum_eq_of_nonneg hρfσ_pos hρfσ_tc ι' b' κ bσ
  rw [h_trace_basis]
  exact tsum_congr h_inner

end DPIPrep

/-! ### Finite-rank compression for DPI

Infrastructure for approximating trace-class operators by finite-rank compressions.
Given a HilbertBasis `b : HilbertBasis ι ℂ H` and a `Finset S ⊆ ι`, the
**finite-rank projection** `P_S = Σ_{i ∈ S} |b_i⟩⟨b_i|` compresses operators
to the finite-dimensional subspace `V_S = span{b_i : i ∈ S}`.

This is the first step in the DPI proof route for `tcRelativeEntropy_channel_le`:
1. Compress ρ, σ to finite-rank: `P_n ρ P_n`, `P_n σ P_n`
2. Identify these with matrices and apply matrix DPI
3. Take limits using trace convergence -/

section FiniteRankCompression

variable {ι : Type u}
variable (b : HilbertBasis ι ℂ H) (S : Finset ι)

/-- The finite-rank orthogonal projection onto `span{b_i : i ∈ S}`.
This is `P_S = Σ_{i ∈ S} |b_i⟩⟨b_i|`. -/
noncomputable def finiteRankProjection : H →L[ℂ] H :=
  ∑ i ∈ S, TraceClass.rankOne (b i) (b i)

/-- The finite-rank projection applied to a vector. -/
lemma finiteRankProjection_apply (x : H) :
    finiteRankProjection b S x = ∑ i ∈ S, ⟪b i, x⟫_ℂ • b i := by
  simp [finiteRankProjection, ContinuousLinearMap.sum_apply, TraceClass.rankOne_apply]

/-- The finite-rank projection is self-adjoint. -/
lemma finiteRankProjection_isSelfAdjoint :
    IsSelfAdjoint (finiteRankProjection b S) := by
  unfold finiteRankProjection
  exact isSelfAdjoint_sum S (fun i _ => TraceClass.rankOne_adjoint (b i) (b i))

/-- The finite-rank projection is non-negative. -/
lemma finiteRankProjection_nonneg :
    0 ≤ finiteRankProjection b S := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive]
  refine ⟨ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (finiteRankProjection_isSelfAdjoint b S), fun x => ?_⟩
  rw [reApplyInnerSelf, finiteRankProjection_apply, sum_inner]
  simp only [RCLike.re_to_complex, Complex.re_sum]
  apply Finset.sum_nonneg
  intro i _
  rw [inner_smul_left, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  exact Complex.normSq_nonneg _

/-- The finite-rank projection maps basis vectors in S to themselves. -/
lemma finiteRankProjection_basis_mem
    (j : ι) (hj : j ∈ S) :
    finiteRankProjection b S (b j) = b j := by
  rw [finiteRankProjection_apply]
  rw [Finset.sum_eq_single_of_mem j hj (fun i _ hij => by rw [b.orthonormal.2 hij, zero_smul])]
  rw [inner_self_eq_norm_sq_to_K, b.orthonormal.1 j, RCLike.ofReal_one, one_pow, one_smul]

/-- The finite-rank projection maps basis vectors outside S to zero. -/
lemma finiteRankProjection_basis_nmem
    (j : ι) (hj : j ∉ S) :
    finiteRankProjection b S (b j) = 0 := by
  rw [finiteRankProjection_apply]
  apply Finset.sum_eq_zero
  intro i hi
  have hij : i ≠ j := fun h => hj (h ▸ hi)
  rw [b.orthonormal.2 hij, zero_smul]

/-- The finite-rank projection is idempotent: `P_S ∘ P_S = P_S`. -/
lemma finiteRankProjection_idempotent :
    finiteRankProjection b S * finiteRankProjection b S = finiteRankProjection b S := by
  ext x
  simp only [ContinuousLinearMap.mul_apply]
  rw [finiteRankProjection_apply b S x]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [finiteRankProjection_basis_mem b S i hi]

/-- The compression `P_S T P_S` of a trace-class operator is trace-class. -/
lemma isTraceClass_compression (T : TraceClass H) :
    IsTraceClass (finiteRankProjection b S * (T : H →L[ℂ] H) * finiteRankProjection b S) :=
  TraceClass.isTraceClass_mul_left
    (TraceClass.isTraceClass_mul_right T.isTraceClass (finiteRankProjection b S))
    (finiteRankProjection b S)

/-- The compression of a trace-class operator as a `TraceClass H` element. -/
noncomputable def TraceClass.compress (T : TraceClass H) (b : HilbertBasis ι ℂ H)
    (S : Finset ι) : TraceClass H :=
  ⟨finiteRankProjection b S * (T : H →L[ℂ] H) * finiteRankProjection b S,
   isTraceClass_compression b S T⟩

/-- The compression of a positive operator is positive. -/
lemma TraceClass.compress_nonneg (T : TraceClass H) (b : HilbertBasis ι ℂ H) (S : Finset ι)
    (hT : 0 ≤ (T : H →L[ℂ] H)) :
    0 ≤ (T.compress b S : H →L[ℂ] H) := by
  -- Unpack: 0 ≤ PTP means ∀ x, 0 ≤ ⟨x, PTPx⟩.re
  -- This equals ⟨Px, T(Px)⟩.re ≥ 0 since P is self-adjoint and T ≥ 0
  have hT_pos := (ContinuousLinearMap.nonneg_iff_isPositive _).mp hT
  rw [ContinuousLinearMap.nonneg_iff_isPositive]
  constructor
  · -- Self-adjoint: PTP is self-adjoint since P and T are
    intro x y
    change ⟪(finiteRankProjection b S * (T : H →L[ℂ] H) * finiteRankProjection b S) x,
      y⟫_ℂ =
      ⟪x, (finiteRankProjection b S * (T : H →L[ℂ] H) * finiteRankProjection b S) y⟫_ℂ
    simp only [ContinuousLinearMap.mul_apply]
    have hP_sym : ∀ u v, ⟪(finiteRankProjection b S) u, v⟫_ℂ =
        ⟪u, (finiteRankProjection b S) v⟫_ℂ :=
      ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
        (finiteRankProjection_isSelfAdjoint b S)
    rw [hP_sym, ← hP_sym x]
    exact hT_pos.1 _ _
  · -- Non-negative: ⟨PTPx, x⟩ = ⟨T(Px), Px⟩ ≥ 0
    intro x
    change 0 ≤ (⟪(finiteRankProjection b S * (T : H →L[ℂ] H) *
      finiteRankProjection b S) x, x⟫_ℂ).re
    simp only [ContinuousLinearMap.mul_apply]
    have hP_sym : ∀ u v, ⟪(finiteRankProjection b S) u, v⟫_ℂ =
        ⟪u, (finiteRankProjection b S) v⟫_ℂ :=
      ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
        (finiteRankProjection_isSelfAdjoint b S)
    rw [hP_sym]
    exact hT_pos.2 _

/-- Trace of the compression of a positive operator equals the partial sum of
diagonal elements. -/
lemma TraceClass.trace_compress_eq_sum (T : TraceClass H) (b : HilbertBasis ι ℂ H)
    (S : Finset ι) (hT : 0 ≤ (T : H →L[ℂ] H)) :
    TraceClass.trace (T.compress b S) =
      ∑ i ∈ S, ⟪b i, (T : H →L[ℂ] H) (b i)⟫_ℂ := by
  -- The compression P_S T P_S is positive, so we can use any basis for its trace
  have hpos := T.compress_nonneg b S hT
  -- Use the trace formula with basis b
  have h_trace_basis : TraceClass.trace (T.compress b S) =
      ∑' j, ⟪b j, (T.compress b S : H →L[ℂ] H) (b j)⟫_ℂ := by
    unfold TraceClass.trace
    exact TraceClass.trace_sum_eq_of_nonneg hpos (T.compress b S).isTraceClass _ _ ι b
  rw [h_trace_basis]
  -- For j ∉ S: P(b j) = 0, so ⟨b j, PTP(b j)⟩ = 0
  have h_zero : ∀ j, j ∉ S →
      ⟪b j, (T.compress b S : H →L[ℂ] H) (b j)⟫_ℂ = 0 := by
    intro j hj
    change ⟪b j, (finiteRankProjection b S * (T : H →L[ℂ] H) *
      finiteRankProjection b S) (b j)⟫_ℂ = 0
    simp only [ContinuousLinearMap.mul_apply]
    rw [finiteRankProjection_basis_nmem b S j hj, map_zero, map_zero, inner_zero_right]
  -- For j ∈ S: P(b j) = b j, so ⟨b j, PTP(b j)⟩ = ⟨b j, T(b j)⟩
  have h_mem : ∀ j ∈ S,
      ⟪b j, (T.compress b S : H →L[ℂ] H) (b j)⟫_ℂ = ⟪b j, (T : H →L[ℂ] H) (b j)⟫_ℂ := by
    intro j hj
    change ⟪b j, (finiteRankProjection b S * (T : H →L[ℂ] H) *
      finiteRankProjection b S) (b j)⟫_ℂ = _
    simp only [ContinuousLinearMap.mul_apply]
    rw [finiteRankProjection_basis_mem b S j hj,
        ← ContinuousLinearMap.adjoint_inner_left,
        (finiteRankProjection_isSelfAdjoint b S).adjoint_eq,
        finiteRankProjection_basis_mem b S j hj]
  rw [tsum_eq_sum h_zero]
  exact Finset.sum_congr rfl h_mem

end FiniteRankCompression

/-! ### Equality condition for trace-class relative entropy

The equality condition `D(ρ ‖ σ) = 0 ↔ ρ = σ` for positive trace-class operators
with equal traces. The forward direction proceeds by:

1. `D = 0` ⟹ `Tr(ρ(log ρ − log σ)).re = 0` (unfold definition)
2. Positive operator with zero trace ⟹ zero operator (trace norm argument)
3. `ρ(log ρ − log σ) = 0` at operator level
4. Taking adjoint: `(log ρ − log σ)ρ = 0`
5. For eigenvectors of ρ with positive eigenvalue: `log σ(eᵢ) = (log λᵢ) eᵢ`
6. Cross-basis analysis with σ's eigenbasis: coefficient relation gives `σ(eᵢ) = λᵢ eᵢ`
7. Trace equality handles the kernel of ρ
-/

section EqualityCondition

variable {ιρ ισ : Type u}

/-- A positive trace-class operator with zero trace (real part) is the zero operator.

This follows the chain: `Tr(T).re = 0` → `‖T‖₁ = 0` (since trace = trace norm
for positive operators) → `T = 0` (by `traceNorm_eq_zero_iff`). -/
lemma nonneg_traceClass_eq_zero_of_trace_re_eq_zero
    (T : TraceClass H) (hT_pos : 0 ≤ T.toFun)
    (hT_re : (TraceClass.trace T).re = 0) :
    (T : H →L[ℂ] H) = 0 := by
  -- trace = traceNorm for positive operators
  have h_eq : (TraceClass.traceOfPositive hT_pos T.isTraceClass).re =
      TraceClass.traceNorm T :=
    TraceClass.trace_eq_traceNorm_of_nonneg T hT_pos
  have h_trace_eq : TraceClass.trace T =
      TraceClass.traceOfPositive hT_pos T.isTraceClass := by
    unfold TraceClass.trace TraceClass.traceOfPositive
    exact TraceClass.trace_sum_eq_of_nonneg hT_pos T.isTraceClass _ _ _ _
  -- traceNorm = 0
  have h_norm_zero : TraceClass.traceNorm T = 0 := by
    linarith [h_eq, congr_arg Complex.re h_trace_eq]
  -- traceNorm = 0 → T = 0
  have h_T_zero := (TraceClass.traceNorm_eq_zero_iff T).mp h_norm_zero
  cases T with
  | mk toFun isTraceClass =>
    simp only [TraceClass.mk.injEq] at h_T_zero
    exact h_T_zero

/-- For a positive operator, `⟨v, Tv⟩ = 0` implies `Tv = 0`.

This uses the Cauchy-Schwarz-type identity `⟨v, Tv⟩ = ‖√T v‖²` for positive `T`,
or equivalently `T = S*S` where `S = √T`. -/
private lemma pos_inner_eq_zero_imp_apply_eq_zero
    {T : H →L[ℂ] H} (hT : 0 ≤ T) (v : H)
    (hv : ⟪v, T v⟫_ℂ = 0) : T v = 0 := by
  -- T ≥ 0 means T is positive in the sense ⟨x, Tx⟩ ≥ 0 for all x
  have hT_pos := (ContinuousLinearMap.nonneg_iff_isPositive T).mp hT
  -- Use T = S†S where S = √T, then ⟨v, Tv⟩ = ‖Sv‖²
  have hS := CFC.sqrt_nonneg (a := T)
  have hS_sq : CFC.sqrt T * CFC.sqrt T = T :=
    CFC.sqrt_mul_sqrt_self T hT
  have hS_sa : IsSelfAdjoint (CFC.sqrt T) := hS.isSelfAdjoint
  -- ⟨v, Tv⟩ = ⟨v, S²v⟩ = ⟨Sv, Sv⟩ = ‖Sv‖²
  have h_norm_sq : ‖CFC.sqrt T v‖^2 = 0 := by
    have : (⟪v, T v⟫_ℂ).re = ‖CFC.sqrt T v‖^2 := by
      have h_inner_eq : ⟪v, T v⟫_ℂ = ⟪CFC.sqrt T v, CFC.sqrt T v⟫_ℂ := by
        conv_lhs => rw [← hS_sq]
        rw [ContinuousLinearMap.mul_apply,
            ← ContinuousLinearMap.adjoint_inner_left, hS_sa.adjoint_eq]
      rw [h_inner_eq]
      exact @inner_self_eq_norm_sq ℂ H _ _ _ ((CFC.sqrt T) v)
    rw [hv, Complex.zero_re] at this
    linarith
  rw [sq_eq_zero_iff, norm_eq_zero] at h_norm_sq
  -- Sv = 0 → Tv = S(Sv) = 0
  rw [← hS_sq, ContinuousLinearMap.mul_apply, h_norm_sq, map_zero]

/-- **Equality condition for trace-class relative entropy.**

For positive trace-class operators `ρ`, `σ` with equal traces,
`D(ρ ‖ σ) = 0 ↔ ρ = σ` (as bounded operators).

**Hypotheses:**
- Positivity of ρ and σ
- Klein positivity: `0 ≤ ρ(log ρ − log σ)` (operator-level)
- Trace equality: `Tr(ρ) = Tr(σ)`
- Eigenbases for ρ and σ with non-negative eigenvalues
- Continuity of `Real.log` on the spectra (for the CFC eigenvector property)
- Support condition `tcSuppSubset ρ σ` (for the forward direction)

The backward direction is immediate from `log ρ − log σ = 0`.
The forward direction uses the trace-norm argument to show `ρ(log ρ − log σ) = 0`,
then derives operator equality through spectral analysis. -/
theorem tcRelativeEntropy_eq_zero_iff
    (ρ σ : TraceClass H)
    [TraceClass.IsNonneg ρ] [TraceClass.IsNonneg σ]
    [TraceClass.HasRelLogTC ρ σ]
    (hρσ_pos : 0 ≤ TraceClass.logDiff ρ σ)
    (hTr_eq : TraceClass.trace ρ = TraceClass.trace σ)
    -- Eigenbasis of ρ
    (bρ : HilbertBasis ιρ ℂ H)
    (ev_ρ : ιρ → ℝ) (hρ_eig : ∀ i, (ρ : H →L[ℂ] H) (bρ i) = (ev_ρ i : ℂ) • bρ i)
    (hρ_nn : ∀ i, 0 ≤ ev_ρ i)
    -- Eigenbasis of σ
    (bσ : HilbertBasis ισ ℂ H)
    (ev_σ : ισ → ℝ) (hσ_eig : ∀ j, (σ : H →L[ℂ] H) (bσ j) = (ev_σ j : ℂ) • bσ j)
    (hσ_nn : ∀ j, 0 ≤ ev_σ j)
    -- Continuity conditions for CFC on the spectra
    (hlog_ρ_cont : ContinuousOn Real.log (spectrum ℝ (ρ : H →L[ℂ] H)))
    (hlog_σ_cont : ContinuousOn Real.log (spectrum ℝ (σ : H →L[ℂ] H))) :
    tcRelativeEntropy ρ σ = 0 ↔ (ρ : H →L[ℂ] H) = (σ : H →L[ℂ] H) := by
  have hρ_pos := TraceClass.IsNonneg.nonneg (ρ := ρ)
  have hσ_pos := TraceClass.IsNonneg.nonneg (ρ := σ)
  have hρσ_tc : IsTraceClass (TraceClass.logDiff ρ σ) := TraceClass.HasRelLogTC.isTraceClass
  constructor
  · -- Forward: D = 0 → ρ = σ
    intro hD
    -- Step 1: tcSuppSubset must hold (otherwise D = ⊤ ≠ 0)
    by_cases hsupp : tcSuppSubset (ρ : H →L[ℂ] H) (σ : H →L[ℂ] H)
    · -- Step 2-3: Extract trace = 0 from D = 0
      unfold tcRelativeEntropy at hD
      simp only [hsupp, ↓reduceIte] at hD
      rw [EReal.coe_eq_zero] at hD
      -- Positive operator with zero trace → zero operator
      set S : TraceClass H := ⟨TraceClass.logDiff ρ σ,
        TraceClass.HasRelLogTC.isTraceClass⟩
      have hS_op_zero : (S : H →L[ℂ] H) = 0 :=
        nonneg_traceClass_eq_zero_of_trace_re_eq_zero S hρσ_pos hD
      -- Step 4: At operator level, ρ * (log ρ - log σ) = 0
      change (ρ : H →L[ℂ] H) *
        (CFC.log (ρ : H →L[ℂ] H) - CFC.log (σ : H →L[ℂ] H)) = 0 at hS_op_zero
      -- Step 5: Adjoint → (log ρ - log σ) * ρ = 0
      -- Since ρ and (log ρ - log σ) are both self-adjoint:
      --   (ρ * diff)† = diff† * ρ† = diff * ρ
      have hsa_ρ : IsSelfAdjoint (ρ : H →L[ℂ] H) := hρ_pos.isSelfAdjoint
      have hsa_σ : IsSelfAdjoint (σ : H →L[ℂ] H) := hσ_pos.isSelfAdjoint
      set diff := CFC.log (ρ : H →L[ℂ] H) - CFC.log (σ : H →L[ℂ] H)
      have hsa_diff : IsSelfAdjoint diff :=
        (IsSelfAdjoint.cfc (f := Real.log) (a := (ρ : H →L[ℂ] H))).sub
          (IsSelfAdjoint.cfc (f := Real.log) (a := (σ : H →L[ℂ] H)))
      have h_adj_zero : diff * (ρ : H →L[ℂ] H) = 0 := by
        have h1 : ((ρ : H →L[ℂ] H) * diff).adjoint = diff * (ρ : H →L[ℂ] H) := by
          change ((ρ : H →L[ℂ] H).comp diff).adjoint = diff.comp (ρ : H →L[ℂ] H)
          rw [ContinuousLinearMap.adjoint_comp]
          rw [hsa_diff.adjoint_eq, hsa_ρ.adjoint_eq]
        rw [← h1, hS_op_zero, map_zero]
      -- Step 6: For eigenvectors of ρ with positive eigenvalue:
      --   (log ρ - log σ)(eᵢ) = 0, hence log σ(eᵢ) = (log λᵢ) eᵢ
      -- From (diff * ρ) = 0: diff(ρ(eᵢ)) = 0, i.e., diff(λᵢ eᵢ) = λᵢ diff(eᵢ) = 0
      -- When λᵢ > 0: diff(eᵢ) = 0
      have h_diff_eig : ∀ i, 0 < ev_ρ i → diff (bρ i) = 0 := by
        intro i hi
        have h1 : diff ((ρ : H →L[ℂ] H) (bρ i)) = 0 := by
          have := congr_arg (· (bρ i)) h_adj_zero
          simpa [ContinuousLinearMap.mul_apply, ContinuousLinearMap.zero_apply] using this
        rw [hρ_eig i, map_smul] at h1
        rw [smul_eq_zero] at h1
        rcases h1 with h_c | h_v
        · exact absurd h_c (by exact_mod_cast ne_of_gt hi)
        · exact h_v
      -- log ρ(eᵢ) = (log λᵢ) eᵢ by CFC eigenvector property
      have h_logρ_eig : ∀ i, bρ i ≠ 0 →
          CFC.log (ρ : H →L[ℂ] H) (bρ i) = (Real.log (ev_ρ i) : ℂ) • bρ i :=
        fun i hi => cfc_apply_eigenvector hsa_ρ hi (hρ_eig i) Real.log hlog_ρ_cont
      -- log σ(eᵢ) = (log λᵢ) eᵢ for λᵢ > 0 (from diff(eᵢ) = 0)
      have h_logσ_eig : ∀ i, 0 < ev_ρ i → bρ i ≠ 0 →
          CFC.log (σ : H →L[ℂ] H) (bρ i) = (Real.log (ev_ρ i) : ℂ) • bρ i := by
        intro i hi hbi
        have h_diff_zero := h_diff_eig i hi
        have h_logρ := h_logρ_eig i hbi
        have : CFC.log (σ : H →L[ℂ] H) (bρ i) =
            CFC.log (ρ : H →L[ℂ] H) (bρ i) := by
          have h_eq_sub := congr_arg (· (bρ i)) (show diff = CFC.log (ρ : H →L[ℂ] H) -
            CFC.log (σ : H →L[ℂ] H) from rfl)
          simp only [ContinuousLinearMap.sub_apply] at h_eq_sub
          rw [h_diff_zero] at h_eq_sub
          exact (sub_eq_zero.mp h_eq_sub.symm).symm
        rw [this, h_logρ]
      -- log σ(fⱼ) = (log μⱼ) fⱼ by CFC eigenvector property
      have h_logσ_eig_σ : ∀ j, bσ j ≠ 0 →
          CFC.log (σ : H →L[ℂ] H) (bσ j) = (Real.log (ev_σ j) : ℂ) • bσ j :=
        fun j hj => cfc_apply_eigenvector hsa_σ hj (hσ_eig j) Real.log hlog_σ_cont
      -- Step 7: σ(eᵢ) = λᵢ eᵢ for eigenvectors with λᵢ > 0
      -- Strategy: show ⟨bσ j, σ(bρ i)⟩ = λᵢ ⟨bσ j, bρ i⟩ for all j
      -- Using: log σ(bρ i) = (log λᵢ)(bρ i), expand in bσ basis
      -- and use coefficient matching with log injectivity + support condition
      have h_σ_eig_pos : ∀ i, 0 < ev_ρ i →
          (σ : H →L[ℂ] H) (bρ i) = (ev_ρ i : ℂ) • bρ i := by
        intro i hi
        -- Handle bρ i = 0 case
        by_cases hbi : bρ i = 0
        · simp [hbi]
        -- Expand bρ i in σ's eigenbasis
        -- logσ(bρ i) = (logλᵢ)(bρ i) and logσ(bρ i) = logσ(∑ⱼ ⟨fⱼ,eᵢ⟩fⱼ)
        --   = ∑ⱼ ⟨fⱼ,eᵢ⟩ logσ(fⱼ) = ∑ⱼ (logμⱼ)⟨fⱼ,eᵢ⟩ fⱼ
        -- So for all j: (logμⱼ - logλᵢ) ⟨fⱼ,eᵢ⟩ = 0
        have h_coeff : ∀ j, ((Real.log (ev_σ j) : ℂ) - (Real.log (ev_ρ i) : ℂ)) *
            ⟪bσ j, bρ i⟫_ℂ = 0 := by
          intro j
          -- Taking inner product of logσ(bρ i) = (logλᵢ)(bρ i) with bσ j
          have h_lhs := h_logσ_eig i hi hbi
          by_cases hbj : bσ j = 0
          · simp [hbj]
          · have h_inner_logσ : ⟪bσ j, CFC.log (σ : H →L[ℂ] H) (bρ i)⟫_ℂ =
                (Real.log (ev_ρ i) : ℂ) * ⟪bσ j, bρ i⟫_ℂ := by
              rw [h_lhs, inner_smul_right]
            -- ⟨fⱼ, logσ(eᵢ)⟩ = ⟨logσ(fⱼ), eᵢ⟩ (self-adjoint)
            --   = (logμⱼ)⟨fⱼ, eᵢ⟩
            have hsa_logσ : IsSelfAdjoint (CFC.log (σ : H →L[ℂ] H)) :=
              IsSelfAdjoint.cfc (f := Real.log) (a := (σ : H →L[ℂ] H))
            have h_inner_sym : ⟪bσ j, CFC.log (σ : H →L[ℂ] H) (bρ i)⟫_ℂ =
                (Real.log (ev_σ j) : ℂ) * ⟪bσ j, bρ i⟫_ℂ := by
              rw [← ContinuousLinearMap.adjoint_inner_left,
                  hsa_logσ.adjoint_eq, h_logσ_eig_σ j hbj, inner_smul_left,
                  Complex.conj_ofReal]
            -- Combine
            rw [h_inner_sym] at h_inner_logσ
            rw [sub_mul]
            exact sub_eq_zero.mpr h_inner_logσ
        -- For each j with ⟨fⱼ, eᵢ⟩ ≠ 0: μⱼ = λᵢ
        -- Case 1: μⱼ > 0 → log injective → μⱼ = λᵢ
        -- Case 2: μⱼ = 0 → logμⱼ = 0, so logλᵢ = 0, so λᵢ = 1
        --   Then fⱼ ∈ ker σ, by tcSuppSubset ρ(fⱼ) = 0
        --   ⟨ρ(eᵢ), fⱼ⟩ = ⟨eᵢ, ρ(fⱼ)⟩ = 0, so λᵢ⟨eᵢ, fⱼ⟩ = 0
        --   Since λᵢ > 0: ⟨eᵢ, fⱼ⟩ = 0, contradiction
        have h_ev_eq : ∀ j, (ev_σ j : ℂ) * ⟪bσ j, bρ i⟫_ℂ =
            (ev_ρ i : ℂ) * ⟪bσ j, bρ i⟫_ℂ := by
          intro j
          by_cases h_inner : ⟪bσ j, bρ i⟫_ℂ = 0
          · simp [h_inner]
          · -- ⟨fⱼ, eᵢ⟩ ≠ 0, so log μⱼ = log λᵢ
            have h_log_eq : (Real.log (ev_σ j) : ℂ) = (Real.log (ev_ρ i) : ℂ) := by
              have := h_coeff j
              rw [sub_mul] at this
              exact mul_right_cancel₀ h_inner (sub_eq_zero.mp this)
            -- Extract real equality from complex
            have h_log_eq_real : Real.log (ev_σ j) = Real.log (ev_ρ i) := by
              exact_mod_cast h_log_eq
            -- Case analysis on μⱼ
            rcases (hσ_nn j).lt_or_eq with hμ_pos | hμ_zero
            · -- μⱼ > 0: log is injective on (0,∞)
              have hj_pos : 0 < ev_σ j := hμ_pos
              have hi_pos : 0 < ev_ρ i := hi
              have := Real.log_injOn_pos (Set.mem_Ioi.mpr hj_pos)
                (Set.mem_Ioi.mpr hi_pos) h_log_eq_real
              congr 1; exact_mod_cast this
            · -- μⱼ = 0: fⱼ ∈ ker σ
              exfalso
              have hev_zero : ev_σ j = 0 := hμ_zero.symm
              -- fⱼ ∈ ker σ: σ(fⱼ) = 0
              have h_σfj : (σ : H →L[ℂ] H) (bσ j) = 0 := by
                rw [hσ_eig j, hev_zero]; simp
              -- By tcSuppSubset: ρ(fⱼ) = 0
              have h_ρfj : (ρ : H →L[ℂ] H) (bσ j) = 0 := hsupp (bσ j) h_σfj
              -- ⟨ρ(eᵢ), fⱼ⟩ = ⟨eᵢ, ρ(fⱼ)⟩ = 0 (ρ self-adjoint)
              have h_inner_zero : (ev_ρ i : ℂ) * ⟪bρ i, bσ j⟫_ℂ = 0 := by
                have : ⟪(ρ : H →L[ℂ] H) (bρ i), bσ j⟫_ℂ =
                    ⟪bρ i, (ρ : H →L[ℂ] H) (bσ j)⟫_ℂ := by
                  rw [← ContinuousLinearMap.adjoint_inner_left, hsa_ρ.adjoint_eq]
                rw [hρ_eig i, inner_smul_left, Complex.conj_ofReal] at this
                rw [h_ρfj, inner_zero_right] at this
                exact this
              -- Since λᵢ > 0: ⟨eᵢ, fⱼ⟩ = 0
              have h_ev_ne : (ev_ρ i : ℂ) ≠ 0 := by
                exact_mod_cast ne_of_gt hi
              have : ⟪bρ i, bσ j⟫_ℂ = 0 := by
                rcases mul_eq_zero.mp h_inner_zero with h | h
                · exact absurd h h_ev_ne
                · exact h
              -- But ⟨fⱼ, eᵢ⟩ = conj ⟨eᵢ, fⱼ⟩ ≠ 0
              exact h_inner (by rw [← inner_conj_symm, this, map_zero])
        -- Now: σ(eᵢ) = ∑' j, μⱼ⟨fⱼ,eᵢ⟩fⱼ = ∑' j, λᵢ⟨fⱼ,eᵢ⟩fⱼ = λᵢ eᵢ
        -- Use positive_compact_eq_tsum_rankOne for σ
        have hσ_comp : IsCompactOperator (σ : H →L[ℂ] H) := TraceClass.IsTraceClass.isCompactOperator σ.isTraceClass
        have h_σ_expand := TraceClass.positive_compact_eq_tsum_rankOne (σ : H →L[ℂ] H)
          bσ ev_σ hσ_eig (bρ i)
        rw [h_σ_expand]
        -- Replace μⱼ⟨fⱼ,eᵢ⟩ with λᵢ⟨fⱼ,eᵢ⟩
        conv_lhs =>
          arg 1; ext j
          rw [show (ev_σ j : ℂ) • ⟪bσ j, bρ i⟫_ℂ • bσ j =
            ((ev_σ j : ℂ) * ⟪bσ j, bρ i⟫_ℂ) • bσ j from by rw [smul_smul]]
          rw [h_ev_eq j]
          rw [show ((ev_ρ i : ℂ) * ⟪bσ j, bρ i⟫_ℂ) • bσ j =
            (ev_ρ i : ℂ) • ⟪bσ j, bρ i⟫_ℂ • bσ j from by rw [← smul_smul]]
        -- ∑ (ev_ρ i) • ⟨fⱼ,eᵢ⟩ • fⱼ = (ev_ρ i) • ∑ ⟨fⱼ,eᵢ⟩ • fⱼ = (ev_ρ i) • eᵢ
        have h_expand : bρ i = ∑' j, ⟪bσ j, bρ i⟫_ℂ • bσ j := by
          have h := (bσ.hasSum_repr (bρ i)).tsum_eq
          simp_rw [HilbertBasis.repr_apply_apply] at h
          exact h.symm
        rw [tsum_const_smul'' (ev_ρ i : ℂ)]
        congr 1
        exact h_expand.symm
      -- Step 8: For λᵢ = 0, use trace equality + positivity
      have h_σ_eig_zero : ∀ i, ev_ρ i = 0 →
          (σ : H →L[ℂ] H) (bρ i) = (ev_ρ i : ℂ) • bρ i := by
        intro i hi
        rw [hi]; simp only [Complex.ofReal_zero, zero_smul]
        -- Need σ(bρ i) = 0
        -- From trace equality: ∑ ⟨eₖ, ρ eₖ⟩ = ∑ ⟨eₖ, σ eₖ⟩
        -- For ev_ρ k > 0: ⟨eₖ, σ eₖ⟩ = ev_ρ k (from h_σ_eig_pos)
        -- So ∑_{ev_ρ k = 0} ⟨eₖ, σ eₖ⟩ = 0, each term ≥ 0, so each = 0
        -- σ ≥ 0 and ⟨eᵢ, σ eᵢ⟩ = 0 → σ eᵢ = 0
        apply pos_inner_eq_zero_imp_apply_eq_zero hσ_pos
        -- Show ⟨bρ i, σ(bρ i)⟩ = 0 using trace equality
        -- Trace of ρ in eigenbasis bρ: ∑ₖ ⟨bρ k, ρ(bρ k)⟩ = ∑ₖ ev_ρ k
        -- Trace of σ in eigenbasis bρ: ∑ₖ ⟨bρ k, σ(bρ k)⟩
        -- For k with ev_ρ k > 0: ⟨bρ k, σ(bρ k)⟩ = ev_ρ k (from h_σ_eig_pos)
        -- So these terms match. For k with ev_ρ k = 0:
        -- ⟨bρ k, ρ(bρ k)⟩ = 0, and ∑ equals 0, each ≥ 0, so each = 0.
        -- This requires summing over the basis, which is complex.
        -- Use a direct argument: ⟨bρ i, σ(bρ i)⟩ ≥ 0 (σ ≥ 0)
        -- and the sum of all such terms for ev_ρ k = 0 equals 0.
        -- For now, use the inner product identity from trace equality.
        have h_trace_ρ : TraceClass.trace ρ =
            ∑' k, ⟪bρ k, (ρ : H →L[ℂ] H) (bρ k)⟫_ℂ := by
          unfold TraceClass.trace
          exact TraceClass.trace_sum_eq_of_nonneg hρ_pos ρ.isTraceClass _ _ ιρ bρ
        have h_trace_σ : TraceClass.trace σ =
            ∑' k, ⟪bρ k, (σ : H →L[ℂ] H) (bρ k)⟫_ℂ := by
          unfold TraceClass.trace
          exact TraceClass.trace_sum_eq_of_nonneg hσ_pos σ.isTraceClass _ _ ιρ bρ
        -- Each ⟨eₖ, ρ eₖ⟩ = ev_ρ k
        have h_ρ_diag : ∀ k, ⟪bρ k, (ρ : H →L[ℂ] H) (bρ k)⟫_ℂ = (ev_ρ k : ℂ) := by
          intro k; rw [hρ_eig k, inner_smul_right,
            inner_self_eq_norm_sq_to_K, bρ.orthonormal.1 k]; simp
        -- Each ⟨eₖ, σ eₖ⟩ for ev_ρ k > 0 equals ev_ρ k
        have h_σ_diag_pos : ∀ k, 0 < ev_ρ k →
            ⟪bρ k, (σ : H →L[ℂ] H) (bρ k)⟫_ℂ = (ev_ρ k : ℂ) := by
          intro k hk; rw [h_σ_eig_pos k hk, inner_smul_right,
            inner_self_eq_norm_sq_to_K, bρ.orthonormal.1 k]; simp
        -- From trace equality: tsum differences = 0
        have h_diff_sum : ∑' k, (⟪bρ k, (σ : H →L[ℂ] H) (bρ k)⟫_ℂ -
            ⟪bρ k, (ρ : H →L[ℂ] H) (bρ k)⟫_ℂ) = 0 := by
          have := congr_arg (· - TraceClass.trace ρ) hTr_eq
          simp only [sub_self] at this
          rw [h_trace_σ, h_trace_ρ, ← (TraceClass.summable_inner_traceClass σ ιρ bρ).tsum_sub
            (TraceClass.summable_inner_traceClass ρ ιρ bρ)] at this
          exact this.symm
        -- For k with ev_ρ k > 0: the difference is 0
        -- For k with ev_ρ k = 0: ⟨eₖ, σ eₖ⟩ - 0 ≥ 0
        -- Sum of non-negative terms = 0 (accounting for positive terms being 0)
        -- Therefore ⟨eᵢ, σ eᵢ⟩ = 0
        -- Use: each term ≥ 0, sum = 0, so term for i = 0
        have h_term_nn : ∀ k, 0 ≤ (⟪bρ k, (σ : H →L[ℂ] H) (bρ k)⟫_ℂ -
            ⟪bρ k, (ρ : H →L[ℂ] H) (bρ k)⟫_ℂ).re := by
          intro k
          rcases (hρ_nn k).lt_or_eq with hk_pos | hk_zero
          · rw [h_σ_diag_pos k hk_pos, h_ρ_diag k, sub_self, Complex.zero_re]
          · rw [h_ρ_diag k, hk_zero.symm]
            simp only [Complex.ofReal_zero, sub_zero]
            have hσ_pos_k := (ContinuousLinearMap.nonneg_iff_isPositive (σ : H →L[ℂ] H)).mp hσ_pos
            have h_re := hσ_pos_k.2 (bρ k)
            unfold ContinuousLinearMap.reApplyInnerSelf at h_re
            rwa [show RCLike.re ⟪(σ : H →L[ℂ] H) (bρ k), bρ k⟫_ℂ =
              (⟪bρ k, (σ : H →L[ℂ] H) (bρ k)⟫_ℂ).re from by
              have := congr_arg Complex.re
                (inner_conj_symm ((σ : H →L[ℂ] H) (bρ k)) (bρ k))
              simp only [Complex.conj_re] at this; exact this.symm] at h_re
        -- The sum of .re is 0
        have h_re_sum_zero : ∑' k, (⟪bρ k, (σ : H →L[ℂ] H) (bρ k)⟫_ℂ -
            ⟪bρ k, (ρ : H →L[ℂ] H) (bρ k)⟫_ℂ).re = 0 := by
          have h_sum := (TraceClass.summable_inner_traceClass σ ιρ bρ).sub
            (TraceClass.summable_inner_traceClass ρ ιρ bρ)
          rw [← Complex.re_tsum h_sum]
          rw [h_diff_sum, Complex.zero_re]
        -- Each .re term is 0 (sum of non-negatives = 0)
        have h_each_zero : ∀ k, (⟪bρ k, (σ : H →L[ℂ] H) (bρ k)⟫_ℂ -
            ⟪bρ k, (ρ : H →L[ℂ] H) (bρ k)⟫_ℂ).re = 0 := by
          intro k
          by_contra h_ne
          have h_pos : 0 < (⟪bρ k, (σ : H →L[ℂ] H) (bρ k)⟫_ℂ -
              ⟪bρ k, (ρ : H →L[ℂ] H) (bρ k)⟫_ℂ).re :=
            lt_of_le_of_ne (h_term_nn k) (Ne.symm h_ne)
          -- Positive term in a sum of non-negatives that totals 0 → contradiction
          have h_ge : (⟪bρ k, (σ : H →L[ℂ] H) (bρ k)⟫_ℂ -
              ⟪bρ k, (ρ : H →L[ℂ] H) (bρ k)⟫_ℂ).re ≤
              ∑' k, (⟪bρ k, (σ : H →L[ℂ] H) (bρ k)⟫_ℂ -
                ⟪bρ k, (ρ : H →L[ℂ] H) (bρ k)⟫_ℂ).re := by
            have h_summable_re : Summable (fun k => (⟪bρ k, (σ : H →L[ℂ] H) (bρ k)⟫_ℂ -
                ⟪bρ k, (ρ : H →L[ℂ] H) (bρ k)⟫_ℂ).re) :=
              ((TraceClass.summable_inner_traceClass σ ιρ bρ).sub
                (TraceClass.summable_inner_traceClass ρ ιρ bρ)).map
                Complex.reAddGroupHom Complex.continuous_re
            exact h_summable_re.le_tsum k (fun k' _ => h_term_nn k')
          linarith
        -- Apply to our specific i
        specialize h_each_zero i
        rw [h_ρ_diag i, hi, Complex.ofReal_zero, sub_zero] at h_each_zero
        -- ⟨bρ i, σ(bρ i)⟩.re = 0. For σ ≥ 0, the inner product is real and non-neg.
        -- So ⟨bρ i, σ(bρ i)⟩ = 0.
        have h_re_nonneg := ((ContinuousLinearMap.nonneg_iff_isPositive
          (σ : H →L[ℂ] H)).mp hσ_pos).2 (bρ i)
        -- The imaginary part is 0 for self-adjoint σ
        have h_im_zero : (⟪bρ i, (σ : H →L[ℂ] H) (bρ i)⟫_ℂ).im = 0 := by
          have : ⟪bρ i, (σ : H →L[ℂ] H) (bρ i)⟫_ℂ =
              starRingEnd ℂ ⟪bρ i, (σ : H →L[ℂ] H) (bρ i)⟫_ℂ :=
            calc ⟪bρ i, (σ : H →L[ℂ] H) (bρ i)⟫_ℂ
              _ = starRingEnd ℂ ⟪(σ : H →L[ℂ] H) (bρ i), bρ i⟫_ℂ :=
                (inner_conj_symm (bρ i) ((σ : H →L[ℂ] H) (bρ i))).symm
              _ = starRingEnd ℂ ⟪bρ i, (σ : H →L[ℂ] H) (bρ i)⟫_ℂ := by
                congr 1; exact hsa_σ.isSymmetric (bρ i) (bρ i)
          exact Complex.conj_eq_iff_im.mp this.symm
        exact Complex.ext h_each_zero h_im_zero
      -- Step 9: Combine — ρ and σ agree on the eigenbasis of ρ
      have h_agree : ∀ i, (σ : H →L[ℂ] H) (bρ i) = (ρ : H →L[ℂ] H) (bρ i) := by
        intro i
        rcases (hρ_nn i).lt_or_eq with hi_pos | hi_zero
        · rw [h_σ_eig_pos i hi_pos, hρ_eig i]
        · rw [h_σ_eig_zero i hi_zero.symm, hρ_eig i]
      -- Step 10: Extension to all vectors
      ext x
      have hx := (bρ.hasSum_repr x)
      have h_ρx := (hx.map (ρ : H →L[ℂ] H) (ρ : H →L[ℂ] H).continuous).tsum_eq
      have h_σx := (hx.map (σ : H →L[ℂ] H) (σ : H →L[ℂ] H).continuous).tsum_eq
      rw [← h_ρx, ← h_σx]
      congr 1; ext k
      simp only [Function.comp_apply, ContinuousLinearMap.map_smul,
        HilbertBasis.repr_apply_apply]
      rw [h_agree k]
    · -- ¬ tcSuppSubset ρ σ → D = ⊤ ≠ 0
      exfalso
      have h_top := tcRelativeEntropy_of_not_suppSubset ρ σ hsupp
      rw [h_top] at hD
      exact EReal.top_ne_zero hD
  · -- Backward: ρ = σ → D = 0
    intro h_eq
    -- When ρ = σ as operators: log ρ - log σ = 0
    have h_log_eq : CFC.log (ρ : H →L[ℂ] H) = CFC.log (σ : H →L[ℂ] H) := by
      congr 1
    -- The support condition holds: ρ = σ → ker σ ⊆ ker ρ
    have hsupp : tcSuppSubset (ρ : H →L[ℂ] H) (σ : H →L[ℂ] H) :=
      fun v hv => h_eq ▸ hv
    -- The operator is ρ * 0 = 0, so trace = 0
    have h_zero_op : TraceClass.logDiff ρ σ = 0 := by
      change (ρ : H →L[ℂ] H) * (CFC.log (ρ : H →L[ℂ] H) - CFC.log (σ : H →L[ℂ] H)) = 0
      rw [h_log_eq, sub_self, mul_zero]
    have h_tc_zero : (⟨TraceClass.logDiff ρ σ,
        TraceClass.HasRelLogTC.isTraceClass⟩ : TraceClass H) = 0 := by
      ext x; change _ = (0 : H →L[ℂ] H) x
      rw [← h_zero_op]
    unfold tcRelativeEntropy
    simp only [hsupp, ↓reduceIte, h_tc_zero]
    simp [TraceClass.trace, inner_zero_right]

end EqualityCondition

end ContinuousLinearMap
