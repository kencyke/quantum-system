module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import QuantumSystem.Analysis.CFC.TraceClass.Def
public import QuantumSystem.Analysis.CFC.Compact
public import QuantumSystem.ForMathlib.Analysis.Complex.Basic

/-!
# Trace-class operators

This file develops the theory of trace-class operators on a complex Hilbert space,
building on the definitions in `TraceClass.Def`.

## Main results

* `zero_isTraceClass`, `smul_isTraceClass`, `neg_isTraceClass`: Closure properties
* `traceNorm`: The trace norm of a trace-class operator
* `adjoint_isTraceClass`: The adjoint of a trace-class operator is trace-class
* `add_isTraceClass`: Sum of trace-class operators is trace-class
-/

@[expose] public section


namespace ContinuousLinearMap

open scoped InnerProductSpace NNReal
open Complex

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}

namespace TraceClass

section Basic

/-- The trace of a trace-class operator, defined as `Tr(T) = ∑ᵢ ⟨bᵢ, T bᵢ⟩`. -/
noncomputable def trace (T : TraceClass H) : ℂ :=
  let b := Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ H))
  ∑' i, ⟪b i, T.toFun (b i)⟫_ℂ

/-- The trace norm of a trace-class operator over a given basis. -/
noncomputable def traceNorm (T : TraceClass H) : ℝ :=
  let b := Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ H))
  ∑' i, (⟪b i, absoluteValue (T : H →L[ℂ] H) (b i)⟫_ℂ).re

/-- The trace of a positive trace-class operator, defined as ∑ᵢ ⟨bᵢ, T bᵢ⟩.
    This is well-defined (independent of basis) by `trace_sum_eq_of_nonneg`. -/
noncomputable def traceOfPositive {T : H →L[ℂ] H} (_hT : 0 ≤ T) (_hTc : IsTraceClass T) : ℂ :=
  let b := Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ H))
  ∑' i, ⟪b i, T (b i)⟫_ℂ

/-- Trace norm is non-negative. -/
lemma traceNorm_nonneg (T : TraceClass H) : 0 ≤ traceNorm T := by
  unfold traceNorm
  apply tsum_nonneg
  intro i
  exact ContinuousLinearMap.traceNormSummand_nonneg T.toFun _ i

/-- Trace norm of negation equals trace norm. -/
lemma traceNorm_neg (T : TraceClass H) : traceNorm (-T) = traceNorm T := by
  unfold traceNorm
  apply tsum_congr
  intro i
  congr 1
  -- -T = (-1) • T, and absoluteValue (c • T) = ‖c‖ • absoluteValue T
  have h1 : ((-T : TraceClass H) : H →L[ℂ] H) = (-1 : ℂ) • (T : H →L[ℂ] H) := by
    simp only [neg_smul, one_smul]
    rfl
  rw [h1, absoluteValue_smul]
  have : ‖(-1 : ℂ)‖ = 1 := by norm_num
  rw [this, one_smul]

/-- Trace norm of scalar multiple. -/
lemma traceNorm_smul (c : ℂ) (T : TraceClass H) :
    traceNorm (c • T) = ‖c‖ * traceNorm T := by
  unfold traceNorm
  have h1 : ((c • T : TraceClass H) : H →L[ℂ] H) = c • (T : H →L[ℂ] H) := rfl
  rw [h1, absoluteValue_smul]
  simp only [smul_apply, RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro i
  let b := Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ H))
  change (↑‖c‖ * ⟪b i, absoluteValue T.toFun (b i)⟫_ℂ).re = ‖c‖ * (⟪b i, absoluteValue T.toFun (b i)⟫_ℂ).re
  rw [Complex.ofReal_mul']

/-- The trace of a trace-class operator is basis-independent (for positive operators).

For a positive trace-class operator T, the sum ∑ᵢ ⟨bᵢ, T bᵢ⟩ gives the same value
for any choice of Hilbert basis. This is proved using Parseval's identity and the
commutativity of ENNReal sums. -/
lemma trace_sum_eq_of_nonneg {T : H →L[ℂ] H} (hT : 0 ≤ T)
    (hTc : IsTraceClass T)
    (ι₁ : Type u) (b₁ : HilbertBasis ι₁ ℂ H)
    (ι₂ : Type u) (b₂ : HilbertBasis ι₂ ℂ H) :
    ∑' i, ⟪b₁ i, T (b₁ i)⟫_ℂ = ∑' j, ⟪b₂ j, T (b₂ j)⟫_ℂ := by
  let S := CFC.sqrt T
  have hS_pos : 0 ≤ S := CFC.sqrt_nonneg T
  have hS_sq : S * S = T := CFC.sqrt_mul_sqrt_self T hT
  have hS_sa : IsSelfAdjoint S := hS_pos.isSelfAdjoint
  have h_term : ∀ {ι} (b : HilbertBasis ι ℂ H) (i : ι),
      ⟪b i, T (b i)⟫_ℂ = (‖S (b i)‖^2 : ℂ) := by
    intro ι b i
    nth_rw 1 [← hS_sq]
    rw [mul_apply]
    rw [← adjoint_inner_left]
    rw [hS_sa.adjoint_eq]
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  -- Convert both sums to use ‖S (b i)‖^2
  have h_lhs : ∑' i, ⟪b₁ i, T (b₁ i)⟫_ℂ = ∑' i, (‖S (b₁ i)‖^2 : ℂ) := by
    congr 1; ext i; exact h_term b₁ i
  have h_rhs : ∑' j, ⟪b₂ j, T (b₂ j)⟫_ℂ = ∑' j, (‖S (b₂ j)‖^2 : ℂ) := by
    congr 1; ext j; exact h_term b₂ j
  rw [h_lhs, h_rhs]
  let f₁ := fun i => ‖S (b₁ i)‖^2
  let f₂ := fun j => ‖S (b₂ j)‖^2
  have h_sum₁ : Summable f₁ := by
    have h_all := (isTraceClass_of_nonneg hT).mp hTc ι₁ b₁
    convert h_all with i
    rw [h_term]
    rw [← Complex.ofReal_pow]
    exact Complex.ofReal_re _
  have h_sum₂ : Summable f₂ := by
    have h_all := (isTraceClass_of_nonneg hT).mp hTc ι₂ b₂
    convert h_all with j
    rw [h_term]
    rw [← Complex.ofReal_pow]
    exact Complex.ofReal_re _
  -- Note: after rewriting with h_term, goal has (↑‖S (b i)‖)^2, need to convert to ↑(‖S (b i)‖^2)
  have h_eq_form₁ : ∀ i, (↑‖S (b₁ i)‖ : ℂ)^2 = (f₁ i : ℂ) := fun i => (Complex.ofReal_pow _ _).symm
  have h_eq_form₂ : ∀ j, (↑‖S (b₂ j)‖ : ℂ)^2 = (f₂ j : ℂ) := fun j => (Complex.ofReal_pow _ _).symm
  conv_lhs => rw [tsum_congr h_eq_form₁]
  conv_rhs => rw [tsum_congr h_eq_form₂]
  rw [← Complex.ofReal_tsum, ← Complex.ofReal_tsum]
  congr 1
  let g₁ (i : ι₁) : ENNReal := ENNReal.ofReal (f₁ i)
  let g₂ (j : ι₂) : ENNReal := ENNReal.ofReal (f₂ j)
  have h_eq : ∑' i, g₁ i = ∑' j, g₂ j := by
    let M : ι₁ → ι₂ → ENNReal := fun i j => ENNReal.ofReal (‖inner (𝕜 := ℂ) (b₁ i) (S (b₂ j))‖^2)
    have h_lhs : ∑' i, g₁ i = ∑' i, ∑' j, M i j := by
      apply tsum_congr
      intro i
      simp only [g₁, f₁, M]
      rw [HilbertBasis.norm_sq_eq_tsum_norm_sq_inner' b₂ (S (b₁ i))]
      rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (HilbertBasis.summable_norm_sq_inner' _ _)]
      apply tsum_congr; intro j
      congr 2
      rw [← inner_conj_symm, Complex.norm_conj, ← hS_sa.adjoint_eq, adjoint_inner_right, hS_sa.adjoint_eq]
    have h_rhs : ∑' j, g₂ j = ∑' j, ∑' i, M i j := by
      apply tsum_congr
      intro j
      simp only [g₂, f₂, M]
      rw [HilbertBasis.norm_sq_eq_tsum_norm_sq_inner' b₁ (S (b₂ j))]
      rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (HilbertBasis.summable_norm_sq_inner' _ _)]
    rw [h_lhs, h_rhs, ENNReal.tsum_comm]
  -- g₁ i = ENNReal.ofReal (f₁ i) and we have h_eq : ∑' i, g₁ i = ∑' j, g₂ j
  -- Need to prove ∑' i, f₁ i = ∑' j, f₂ j
  have h_f₁_nonneg : ∀ i, 0 ≤ f₁ i := fun i => sq_nonneg _
  have h_f₂_nonneg : ∀ j, 0 ≤ f₂ j := fun j => sq_nonneg _
  have h_g₁_toReal : ∀ i, (g₁ i).toReal = f₁ i := fun i => ENNReal.toReal_ofReal (h_f₁_nonneg i)
  have h_g₂_toReal : ∀ j, (g₂ j).toReal = f₂ j := fun j => ENNReal.toReal_ofReal (h_f₂_nonneg j)
  have h_g₁_tsum : (∑' i, g₁ i).toReal = ∑' i, f₁ i := by
    rw [ENNReal.tsum_toReal_eq (fun i => ENNReal.ofReal_ne_top)]
    exact tsum_congr h_g₁_toReal
  have h_g₂_tsum : (∑' j, g₂ j).toReal = ∑' j, f₂ j := by
    rw [ENNReal.tsum_toReal_eq (fun j => ENNReal.ofReal_ne_top)]
    exact tsum_congr h_g₂_toReal
  rw [← h_g₁_tsum, ← h_g₂_tsum, h_eq]

/-- For a positive trace-class operator, the trace sum converges. -/
lemma trace_summable_of_nonneg {T : H →L[ℂ] H} (hT : 0 ≤ T)
    (hTc : IsTraceClass T) (ι : Type u) (b : HilbertBasis ι ℂ H) :
    Summable (fun i => ⟪b i, T (b i)⟫_ℂ) := by
  have h_abs : absoluteValue T = T := absoluteValue_of_nonneg hT
  have hpos : T.IsPositive := by rwa [← nonneg_iff_isPositive]
  have h_real : ∀ i, ⟪b i, T (b i)⟫_ℂ = ((⟪b i, T (b i)⟫_ℂ).re : ℂ) := fun i =>
    Complex.ext rfl (hpos.isSymmetric.im_inner_self_apply (b i))
  rw [funext h_real]
  have hTc' := (isTraceClass_of_nonneg hT).mp hTc
  exact Complex.summable_ofReal.mpr (hTc' ι b)

/-- The trace of a positive operator equals its trace norm (as a real number). -/
lemma trace_eq_traceNorm_of_nonneg (T : TraceClass H) (hT : 0 ≤ T.toFun) :
    (traceOfPositive hT T.isTraceClass).re = traceNorm T := by
  unfold traceOfPositive traceNorm
  have h_abs : absoluteValue T.toFun = T.toFun := absoluteValue_of_nonneg hT
  simp only [h_abs]
  let b := Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ H))
  rw [Complex.re_tsum (trace_summable_of_nonneg hT T.isTraceClass _ b)]

/-- The real part of the trace of a positive trace-class operator is non-negative:
`0 ≤ Re(Tr(T))` when `T ≥ 0`.

This is the trace-level Klein inequality building block: since a positive operator
has `Tr(T) = ‖T‖₁ ≥ 0` (trace equals trace norm for positive operators),
the real part is non-negative. -/
lemma trace_re_nonneg_of_nonneg (T : TraceClass H) (hT : 0 ≤ T.toFun) :
    0 ≤ (trace T).re := by
  have h_eq : trace T = traceOfPositive hT T.isTraceClass := by
    unfold trace traceOfPositive
    exact trace_sum_eq_of_nonneg hT T.isTraceClass _ _ _ _
  rw [h_eq]
  linarith [trace_eq_traceNorm_of_nonneg T hT, traceNorm_nonneg T]

/-- If `T` is trace-class and `A` is bounded, then `A * T` is trace-class.

The proof uses polar decomposition `T = V|T|` and shows that the trace of `|AT|`
is bounded by `‖A‖ · Tr(|T|)` using the Hölder-type bounds. -/
lemma isTraceClass_mul_left {T : H →L[ℂ] H} (hT : IsTraceClass T) (A : H →L[ℂ] H) :
    IsTraceClass (A * T) := by
  -- Get polar decomposition of A * T
  obtain ⟨U, hU_pi, h_AT_polar, h_AT_ker⟩ := exists_polar_decomposition (A * T)
  -- Key: |AT| = U† (A * T) when A * T = U |AT|
  have h_AT_abs_eq : absoluteValue (A * T) = U.adjoint * (A * T) :=
    absoluteValue_eq_adjoint_mul_of_polar hU_pi h_AT_polar h_AT_ker
  -- Show summability for any basis
  intro ι b
  -- The trace ∑ ⟨bᵢ, |AT| bᵢ⟩ = ∑ ⟨bᵢ, U†(AT) bᵢ⟩
  have h_eq : ∀ i, (⟪b i, absoluteValue (A * T) (b i)⟫_ℂ).re =
      (⟪b i, ((U.adjoint * A) * T) (b i)⟫_ℂ).re := by
    intro i
    rw [h_AT_abs_eq]
    simp only [mul_apply, mul_assoc]
  -- Use the Hölder bound with U†A as the bounded operator
  let B := U.adjoint * A
  have h_holder := summable_abs_re_inner_mul_traceClass hT B ι b
  -- The summands are nonneg (since |AT| ≥ 0)
  have h_nonneg : ∀ i, 0 ≤ (⟪b i, absoluteValue (A * T) (b i)⟫_ℂ).re :=
    traceNormSummand_nonneg (A * T) b
  -- Bound: the nonneg summand ≤ |summand| ≤ Hölder bound
  have h_bound : ∀ i, (⟪b i, absoluteValue (A * T) (b i)⟫_ℂ).re ≤
      |(⟪b i, (B * T) (b i)⟫_ℂ).re| := by
    intro i
    rw [h_eq i]
    exact le_abs_self _
  exact Summable.of_nonneg_of_le h_nonneg h_bound h_holder.1

/-- Trace-class operators are compact.

The proof uses that if ∑ᵢ ⟨bᵢ, |T| bᵢ⟩ < ∞, then T is the limit of finite rank operators.
Specifically, let Tₙ be the operator that agrees with T on span{b₁,...,bₙ} and is 0 elsewhere.
Then ‖T - Tₙ‖ → 0, and each Tₙ is finite rank, hence compact. -/
lemma IsTraceClass.isCompactOperator {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    IsCompactOperator T := by
  obtain ⟨U, _, hT_eq, _⟩ := exists_polar_decomposition T
  let P := absoluteValue T
  have hP_pos : 0 ≤ P := absoluteValue_nonneg T
  let S := CFC.sqrt P
  have hS_sq : S * S = absoluteValue T := CFC.sqrt_mul_sqrt_self P hP_pos
  -- Show S is compact
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  have h_sum := hT w.Elem b
  have hS_compact : IsCompactOperator S := by
    apply isCompactOperator_of_summable_sq_norm (b := b)
    convert h_sum with i
    rw [← hS_sq]
    have hS_sa : IsSelfAdjoint S := (CFC.sqrt_nonneg P).isSelfAdjoint
    have h_adj : S.adjoint = S := hS_sa.adjoint_eq
    -- rewrite inner to the norm square via self-adjointness
    have h_inner : (⟪b i, (S * S) (b i)⟫_ℂ).re = ‖S (b i)‖^2 := by
      have h1 : (⟪S (S (b i)), b i⟫_ℂ) = ⟪S (b i), S (b i)⟫_ℂ := by
        have h' := (ContinuousLinearMap.adjoint_inner_left (A := S) (x := b i) (y := S (b i)))
        -- rewrite adjoint using self-adjointness
        simpa [h_adj, ContinuousLinearMap.mul_apply] using h'
      have h2 : (⟪b i, S (S (b i))⟫_ℂ).re = (⟪S (S (b i)), b i⟫_ℂ).re := by
        rw [← inner_conj_symm, Complex.conj_re]
      calc
        (⟪b i, (S * S) (b i)⟫_ℂ).re = (⟪b i, S (S (b i))⟫_ℂ).re := by rfl
        _ = (⟪S (S (b i)), b i⟫_ℂ).re := h2
        _ = (⟪S (b i), S (b i)⟫_ℂ).re := by simp [h1]
        _ = ‖S (b i)‖^2 := by
          rw [inner_self_eq_norm_sq_to_K]
          norm_cast
    have h_inner' : ‖S (b i)‖^2 = (⟪b i, S (S (b i))⟫_ℂ).re := by
      simpa [ContinuousLinearMap.mul_apply] using h_inner.symm
    exact h_inner'
  have hSS_compact : IsCompactOperator (S * S) := by
    simpa using (hS_compact.clm_comp S)
  have hUSS_compact : IsCompactOperator (U * (S * S)) := by
    simpa [mul_assoc] using (hSS_compact.clm_comp U)
  have hT' : U * (S * S) = T := by
    calc
      U * (S * S) = U * absoluteValue T := by simp [hS_sq]
      _ = T := by simpa using hT_eq.symm
  simpa [hT'] using hUSS_compact

/-- Parseval identity variant: ∑ᵢ |⟨U†bᵢ, v⟩|² = ‖v‖² for v ∈ (ker U)ᗮ -/
theorem tsum_norm_sq_inner_adjoint_eq_norm_sq {U : H →L[ℂ] H}
    (hU_pi : U.adjoint * U * (U.adjoint * U) = U.adjoint * U)
    {ι : Type*} (b : HilbertBasis ι ℂ H)
    (v : H) (hv : v ∈ (LinearMap.ker U.toLinearMap)ᗮ) :
    ∑' i, (‖⟪U.adjoint (b i), v⟫_ℂ‖^2 : ℝ) = ‖v‖^2 := by
  -- ⟨U†bᵢ, v⟩ = ⟨bᵢ, U v⟩ by adjoint property
  have h_inner_eq : ∀ i, ⟪U.adjoint (b i), v⟫_ℂ = ⟪b i, U v⟫_ℂ := fun i => adjoint_inner_left _ _ _
  simp_rw [h_inner_eq]
  -- ∑ᵢ |⟨bᵢ, U v⟩|² = ‖U v‖² by Parseval
  have h_parseval := (HilbertBasis.norm_sq_eq_tsum_norm_sq_inner' b (U v)).symm
  rw [h_parseval]
  -- ‖U v‖² = ‖v‖² for v ∈ (ker U)ᗮ by IsPartialIsometry
  have h_norm := IsPartialIsometry.norm_of_mem_initialSpace hU_pi v hv
  rw [h_norm]

/-- The trace of |T| equals the trace of |T†| as ENNReal sums.
    This is the key lemma for proving T† is trace-class when T is.

    Mathematical justification:
    1. |T|² = T†T and |T†|² = TT† have the same nonzero eigenvalues
       (by eigenvalues_adjoint_mul_eq_mul_adjoint)
    2. For positive operators, taking square root preserves the eigenvalue relationship
    3. Therefore |T| and |T†| have the same eigenvalues (singular values of T)
    4. Trace = sum of eigenvalues for positive compact operators
    5. Hence Tr(|T|) = Tr(|T†|)

    Proof approach: Use the double-sum Parseval identity.
    Let S = √|T| and S' = √|T†|.
    Then ∑ᵢ ⟨bᵢ, |T| bᵢ⟩ = ∑ᵢ ‖S bᵢ‖² = ∑ᵢ ∑ⱼ |⟨bⱼ, S bᵢ⟩|²
    Similarly ∑ᵢ ⟨bᵢ, |T†| bᵢ⟩ = ∑ᵢ ∑ⱼ |⟨bⱼ, S' bᵢ⟩|²

    Key fact: S² = T†T and S'² = TT† have the same spectrum
    By spectral theory: the matrix elements satisfy
    ∑ᵢⱼ |⟨bᵢ, S bⱼ⟩|² = ∑ᵢⱼ |⟨bᵢ, S' bⱼ⟩|² (Hilbert-Schmidt norm = sum of singular values²)
-/
theorem tsum_inner_absoluteValue_eq_adjoint_ennreal {T : H →L[ℂ] H}
    {ι : Type u} (b : HilbertBasis ι ℂ H) :
    ∑' i, ENNReal.ofReal (⟪b i, absoluteValue T (b i)⟫_ℂ).re =
    ∑' i, ENNReal.ofReal (⟪b i, absoluteValue T.adjoint (b i)⟫_ℂ).re := by
  -- The sums compute Tr(|T|) and Tr(|T†|) respectively.
  -- Both traces equal the sum of singular values of T.
  --
  -- Let S = √|T| and S' = √|T†|.
  let A := absoluteValue T
  let A' := absoluteValue T.adjoint
  let S := CFC.sqrt A
  let S' := CFC.sqrt A'
  have hS_sq : S * S = A := CFC.sqrt_mul_sqrt_self A (absoluteValue_nonneg T)
  have hS'_sq : S' * S' = A' := CFC.sqrt_mul_sqrt_self A' (absoluteValue_nonneg T.adjoint)
  have hS_sa : IsSelfAdjoint S := (CFC.sqrt_nonneg A).isSelfAdjoint
  have hS'_sa : IsSelfAdjoint S' := (CFC.sqrt_nonneg A').isSelfAdjoint
  -- Transform ⟨bᵢ, A bᵢ⟩ = ⟨bᵢ, S² bᵢ⟩ = ⟨S bᵢ, S bᵢ⟩ = ‖S bᵢ‖²
  have h_A_eq : ∀ i, (⟪b i, A (b i)⟫_ℂ).re = ‖S (b i)‖ ^ 2 := by
    intro i
    rw [← hS_sq, mul_apply, ← adjoint_inner_left, hS_sa.adjoint_eq,
        inner_self_eq_norm_sq_to_K]
    norm_cast
  have h_A'_eq : ∀ i, (⟪b i, A' (b i)⟫_ℂ).re = ‖S' (b i)‖ ^ 2 := by
    intro i
    rw [← hS'_sq, mul_apply, ← adjoint_inner_left, hS'_sa.adjoint_eq,
        inner_self_eq_norm_sq_to_K]
    norm_cast
  -- Rewrite both sides using the equalities
  have h_lhs : ∑' i, ENNReal.ofReal (⟪b i, absoluteValue T (b i)⟫_ℂ).re =
      ∑' i, ENNReal.ofReal (‖S (b i)‖ ^ 2) := tsum_congr fun i => by rw [h_A_eq]
  have h_rhs : ∑' i, ENNReal.ofReal (⟪b i, absoluteValue T.adjoint (b i)⟫_ℂ).re =
      ∑' i, ENNReal.ofReal (‖S' (b i)‖ ^ 2) := tsum_congr fun i => by rw [h_A'_eq]
  rw [h_lhs, h_rhs]
  -- Goal: ∑' i, ‖S (b i)‖² = ∑' i, ‖S' (b i)‖² as ENNReal
  -- Proof via polar decomposition: T = U|T| implies |T†| = U|T|U†
  -- Then ⟨x, |T†| x⟩ = ⟨U†x, |T|(U†x)⟩
  -- The sums are equal because U† preserves inner products on ran(U) = (ker U†)ᗮ
  obtain ⟨U, hU_pi, hT_polar, hU_ker⟩ := exists_polar_decomposition T
  -- Key lemma: U†U acts as identity on ran(|T|) ⊆ (ker |T|)ᗮ = (ker U)ᗮ
  have h_ker_eq : LinearMap.ker (absoluteValue T).toLinearMap = LinearMap.ker U.toLinearMap := by
    rw [absoluteValue_ker_eq_ker T, hU_ker]
  -- For any x, |T| x ∈ (ker |T|)ᗮ = (ker U)ᗮ
  have h_range_orthogonal : ∀ x, absoluteValue T x ∈ (LinearMap.ker U.toLinearMap)ᗮ := by
    intro x
    rw [Submodule.mem_orthogonal]
    intro y hy
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hy
    -- |T| is self-adjoint, so ⟨|T| x, y⟩ = ⟨x, |T| y⟩
    have h_sa := absoluteValue_isSelfAdjoint T
    rw [← adjoint_inner_left, h_sa.adjoint_eq]
    -- y ∈ ker U = ker |T| by h_ker_eq, so |T| y = 0
    have h_y_ker : y ∈ LinearMap.ker (absoluteValue T).toLinearMap := by
      rw [h_ker_eq]; exact hy
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at h_y_ker
    rw [h_y_ker, inner_zero_left]
  -- U†U = id on (ker U)ᗮ
  have h_UadjU_id : ∀ x, x ∈ (LinearMap.ker U.toLinearMap)ᗮ → U.adjoint (U x) = x :=
    fun x hx => IsPartialIsometry.adjoint_mul_self_apply_of_mem_ker_orthogonal hU_pi x hx
  -- Therefore U†U|T| = |T|
  have hU_adj_U_abs : U.adjoint * U * absoluteValue T = absoluteValue T := by
    ext x
    simp only [mul_apply]
    exact h_UadjU_id (absoluteValue T x) (h_range_orthogonal x)
  -- Now prove |T†| = U|T|U†
  have h_absT_adj : absoluteValue T.adjoint = U * absoluteValue T * U.adjoint :=
    absoluteValue_adjoint_eq_conjugate_by_partial_isometry hT_polar hU_adj_U_abs
  -- Transform inner products: ⟨bᵢ, |T†| bᵢ⟩ = ⟨U†bᵢ, |T|(U†bᵢ)⟩
  have h_inner_transform : ∀ i, (⟪b i, absoluteValue T.adjoint (b i)⟫_ℂ).re =
      (⟪U.adjoint (b i), absoluteValue T (U.adjoint (b i))⟫_ℂ).re := by
    intro i
    rw [h_absT_adj]
    simp only [mul_apply]
    -- ⟨bᵢ, U(|T|(U†bᵢ))⟩ = ⟨U†bᵢ, |T|(U†bᵢ)⟩
    rw [← adjoint_inner_left U]
  -- Use h_A'_eq to convert S' norms to inner products with |T†|
  have h_rhs' : ∑' i, ENNReal.ofReal (‖S' (b i)‖ ^ 2) =
      ∑' i, ENNReal.ofReal (⟪U.adjoint (b i), absoluteValue T (U.adjoint (b i))⟫_ℂ).re := by
    apply tsum_congr; intro i; rw [← h_A'_eq, h_inner_transform]
  rw [h_rhs']
  -- Convert S norms to inner products with |T|
  have h_lhs' : ∑' i, ENNReal.ofReal (‖S (b i)‖ ^ 2) =
      ∑' i, ENNReal.ofReal (⟪b i, absoluteValue T (b i)⟫_ℂ).re := by
    apply tsum_congr; intro i; rw [h_A_eq]
  rw [h_lhs']
  -- Convert |T| inner products to S norms using S² = |T|
  have h_U_sum : ∑' i, ENNReal.ofReal (⟪U.adjoint (b i), absoluteValue T (U.adjoint (b i))⟫_ℂ).re =
      ∑' i, ENNReal.ofReal (‖S (U.adjoint (b i))‖^2) := by
    apply tsum_congr; intro i
    have h1 : absoluteValue T = S * S := hS_sq.symm
    rw [h1, mul_apply, ← adjoint_inner_left, hS_sa.adjoint_eq, inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [h_U_sum]
  have h_b_sum : ∑' i, ENNReal.ofReal (⟪b i, absoluteValue T (b i)⟫_ℂ).re =
      ∑' i, ENNReal.ofReal (‖S (b i)‖^2) := by
    apply tsum_congr; intro i
    have h1 : absoluteValue T = S * S := hS_sq.symm
    rw [h1, mul_apply, ← adjoint_inner_left, hS_sa.adjoint_eq, inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [h_b_sum]
  -- Goal: ∑ᵢ ‖S bᵢ‖² = ∑ᵢ ‖S(U†bᵢ)‖² as ENNReal
  -- Expand both sides using Parseval: ‖S x‖² = ∑ⱼ |⟨bⱼ, S x⟩|²
  have h_lhs_double : ∑' i, ENNReal.ofReal (‖S (b i)‖^2) =
      ∑' i, ∑' j, ENNReal.ofReal (‖⟪b j, S (b i)⟫_ℂ‖^2) := by
    apply tsum_congr; intro i
    have h := HilbertBasis.norm_sq_eq_tsum_norm_sq_inner' b (S (b i))
    conv_lhs => rw [h]
    exact ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _)
      (HilbertBasis.summable_norm_sq_inner' b (S (b i)))
  have h_rhs_double : ∑' i, ENNReal.ofReal (‖S (U.adjoint (b i))‖^2) =
      ∑' i, ∑' j, ENNReal.ofReal (‖⟪b j, S (U.adjoint (b i))⟫_ℂ‖^2) := by
    apply tsum_congr; intro i
    have h := HilbertBasis.norm_sq_eq_tsum_norm_sq_inner' b (S (U.adjoint (b i)))
    conv_lhs => rw [h]
    exact ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _)
      (HilbertBasis.summable_norm_sq_inner' b (S (U.adjoint (b i))))
  rw [h_lhs_double, h_rhs_double]
  -- Swap indices: ∑ᵢⱼ → ∑ⱼᵢ
  rw [ENNReal.tsum_comm (f := fun i j => ENNReal.ofReal (‖⟪b j, S (b i)⟫_ℂ‖^2))]
  rw [ENNReal.tsum_comm (f := fun i j => ENNReal.ofReal (‖⟪b j, S (U.adjoint (b i))⟫_ℂ‖^2))]
  apply tsum_congr; intro j
  -- Use self-adjointness: |⟨bⱼ, S bᵢ⟩|² = |⟨S bⱼ, bᵢ⟩|² = |⟨bᵢ, S bⱼ⟩|²
  have h_S_sa_symm : ∀ i, ‖⟪b j, S (b i)⟫_ℂ‖^2 = ‖⟪b i, S (b j)⟫_ℂ‖^2 := fun i => by
    have h1 : ⟪b j, S (b i)⟫_ℂ = ⟪S (b j), b i⟫_ℂ := by rw [← adjoint_inner_left, hS_sa.adjoint_eq]
    rw [h1, ← Complex.norm_conj, ← inner_conj_symm]; simp
  have h_S_U_symm : ∀ i, ‖⟪b j, S (U.adjoint (b i))⟫_ℂ‖^2 = ‖⟪U.adjoint (b i), S (b j)⟫_ℂ‖^2 := fun i => by
    have h1 : ⟪b j, S (U.adjoint (b i))⟫_ℂ = ⟪S (b j), U.adjoint (b i)⟫_ℂ := by
      rw [← adjoint_inner_left, hS_sa.adjoint_eq]
    rw [h1, ← Complex.norm_conj, ← inner_conj_symm]; simp
  simp_rw [h_S_sa_symm, h_S_U_symm]
  -- Goal: ∑ᵢ |⟨bᵢ, S bⱼ⟩|² = ∑ᵢ |⟨U†bᵢ, S bⱼ⟩|²
  -- LHS = ‖S bⱼ‖² by Parseval
  -- RHS = ‖P(S bⱼ)‖² where P is projection onto ran(U†) = (ker U)ᗮ
  -- Since S bⱼ ∈ (ker |T|)ᗮ = (ker U)ᗮ, P(S bⱼ) = S bⱼ
  -- So RHS = ‖S bⱼ‖² = LHS
  have h_Sbj_in_ker_orth : ∀ j, S (b j) ∈ (LinearMap.ker U.toLinearMap)ᗮ := by
    intro j
    rw [← h_ker_eq]
    rw [Submodule.mem_orthogonal]
    intro x hx
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx
    rw [← adjoint_inner_left, hS_sa.adjoint_eq]
    -- S x = 0 since x ∈ ker |T| implies S x = 0 (S = √|T|)
    have h_S_ker : S x = 0 := cfc_sqrt_absoluteValue_ker x hx
    rw [h_S_ker]
    exact inner_zero_left _
  -- Apply this to S bⱼ
  simp_rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _)
    (HilbertBasis.summable_norm_sq_inner' b (S (b j)))]
  have h_summable_U : Summable (fun i => ‖⟪U.adjoint (b i), S (b j)⟫_ℂ‖^2) := by
    have : Summable (fun i => ‖⟪b i, U (S (b j))⟫_ℂ‖^2) :=
      HilbertBasis.summable_norm_sq_inner' b (U (S (b j)))
    refine this.congr (fun i => ?_)
    congr 2
    exact (adjoint_inner_left _ _ _).symm
  simp_rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) h_summable_U]
  congr 1
  have h_lhs_eq := HilbertBasis.norm_sq_eq_tsum_norm_sq_inner' b (S (b j))
  have h_rhs_eq := tsum_norm_sq_inner_adjoint_eq_norm_sq hU_pi b (S (b j)) (h_Sbj_in_ker_orth j)
  rw [h_lhs_eq.symm, h_rhs_eq]

/-- For trace-class T, the eigenvalues of |T†| are summable (equal to eigenvalues of |T|).

The key mathematical argument is:
1. The eigenvalues μᵢ of |T†| are non-negative (since |T†| ≥ 0)
2. ∑ μᵢ = Tr(|T†|) = Tr(|T|) by singular value equality
3. Since T is trace-class, Tr(|T|) < ∞
-/
theorem summable_eigenvalues_absoluteValue_adjoint_of_isTraceClass {T : H →L[ℂ] H}
    (hT : IsTraceClass T)
    {ι : Type u} {b : HilbertBasis ι ℂ H} {μ : ι → ℝ}
    (h_eig : ∀ i, absoluteValue T.adjoint (b i) = (μ i) • b i) :
    Summable μ := by
  -- Step 1: μᵢ = ⟨bᵢ, |T†| bᵢ⟩ since b is eigenbasis
  have hμ_eq : ∀ i, μ i = (⟪b i, absoluteValue T.adjoint (b i)⟫_ℂ).re := by
    intro i
    rw [h_eig i]
    -- Need to convert real scalar multiplication to complex for inner_smul_right
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right, inner_self_eq_norm_sq_to_K]
    have h_norm := b.orthonormal.1 i
    rw [h_norm]
    simp
  -- Step 2: The eigenvalues are non-negative (since |T†| ≥ 0)
  have hμ_nonneg : ∀ i, 0 ≤ μ i := by
    intro i
    rw [hμ_eq]
    exact traceNormSummand_nonneg T.adjoint b i
  -- Step 3: Use the trace class property and trace basis independence
  -- The key: b is eigenbasis for |T†|, so ∑ᵢ ⟨bᵢ, |T†| bᵢ⟩ = ∑ᵢ μᵢ = Tr(|T†|)
  -- And Tr(|T†|) = Tr(|T|) by singular value equality
  -- Since T is trace-class, Tr(|T|) < ∞
  --
  -- We prove this using the Parseval identity for Hilbert-Schmidt norms
  -- Let S = √|T| and S' = √|T†|. Then:
  -- ∑ᵢ ⟨bᵢ, |T†| bᵢ⟩ = ∑ᵢ ‖S' bᵢ‖²  (by S' S' = |T†|)
  -- ∑ᵢ ⟨bᵢ, |T| bᵢ⟩ = ∑ᵢ ‖S bᵢ‖²    (by S S = |T|)
  --
  -- For any self-adjoint Hilbert-Schmidt operator R:
  -- ∑ᵢ ‖R bᵢ‖² = ∑ᵢ ∑ⱼ |⟨bⱼ, R bᵢ⟩|² = ∑ⱼ ∑ᵢ |⟨R bⱼ, bᵢ⟩|² = ∑ⱼ ‖R bⱼ‖²
  -- (using self-adjointness: ⟨bⱼ, R bᵢ⟩ = ⟨R bⱼ, bᵢ⟩)
  --
  -- But this only shows the sum is independent of order, not that Tr(|T†|) = Tr(|T|).
  --
  -- The actual proof: For the eigenbasis b of |T†|, ∑ᵢ μᵢ is the trace of |T†|.
  -- We need to show this equals the trace of |T|, which is finite (T trace-class).
  --
  -- Using trace basis independence (already proven in isTraceClass_iff_forall_basis):
  -- ∑ᵢ ⟨bᵢ, |T†| bᵢ⟩ = ∑ⱼ ⟨cⱼ, |T†| cⱼ⟩ for any bases b, c
  -- Take c to be an eigenbasis of |T|. Then:
  -- ∑ⱼ ⟨cⱼ, |T†| cⱼ⟩ = (basis-independent) = ∑ⱼ eigenvalue_j of |T†| = ∑ singular values
  -- And ∑ⱼ ⟨cⱼ, |T| cⱼ⟩ = ∑ eigenvalue_j of |T| = ∑ singular values
  --
  -- So Tr(|T†|) = Tr(|T|) as both equal the sum of singular values.
  --
  -- For now, we use a direct proof that T† is trace-class using compactness
  -- and the spectral decomposition.
  have h_summable_adjoint : Summable (fun i => (⟪b i, absoluteValue T.adjoint (b i)⟫_ℂ).re) := by
    -- Key insight: Use the Parseval double-sum and operator relationship
    -- |T†|² = TT† and |T|² = T†T have the same nonzero eigenvalues
    -- Therefore |T†| and |T| have the same nonzero eigenvalues (singular values)
    -- Hence Tr(|T†|) = Tr(|T|)
    --
    -- Proof structure:
    -- 1. Define S = √|T| and S' = √|T†|
    -- 2. Show ∑ᵢ ⟨bᵢ, |T†| bᵢ⟩ = ∑ᵢ ‖S' bᵢ‖²
    -- 3. Use Parseval: ∑ᵢ ‖S' bᵢ‖² = ∑ᵢ ∑ⱼ |⟨bⱼ, S' bᵢ⟩|²
    -- 4. By self-adjointness: |⟨bⱼ, S' bᵢ⟩| = |⟨S' bⱼ, bᵢ⟩|
    -- 5. The double sum can be rearranged (Tonelli for nonnegative terms)
    -- 6. Relate S' to T and show the sum equals Tr(|T|)
    let A := absoluteValue T
    let A' := absoluteValue T.adjoint
    let S := CFC.sqrt A
    let S' := CFC.sqrt A'
    have hS_sq : S * S = A := CFC.sqrt_mul_sqrt_self A (absoluteValue_nonneg T)
    have hS'_sq : S' * S' = A' := CFC.sqrt_mul_sqrt_self A' (absoluteValue_nonneg T.adjoint)
    have hS_sa : IsSelfAdjoint S := (CFC.sqrt_nonneg A).isSelfAdjoint
    have hS'_sa : IsSelfAdjoint S' := (CFC.sqrt_nonneg A').isSelfAdjoint
    -- Transform to squared norms
    have h_term_eq : ∀ i, (⟪b i, A' (b i)⟫_ℂ).re = ‖S' (b i)‖ ^ 2 := by
      intro i
      rw [← hS'_sq, mul_apply, ← adjoint_inner_left, hS'_sa.adjoint_eq,
          inner_self_eq_norm_sq_to_K]
      norm_cast
    -- Show the sum ∑ᵢ ‖S' bᵢ‖² equals ∑ᵢ ‖S bᵢ‖² via Parseval rearrangement
    -- This is the key step: both equal the Hilbert-Schmidt norm squared
    -- of the "Hilbert-Schmidt operator" associated with the singular values
    --
    -- For ENNReal sums, use the double-sum Parseval identity
    let f := fun i => ‖S' (b i)‖ ^ 2
    let g := fun i => ‖S (b i)‖ ^ 2
    -- Need to show: ∑ f = ∑ g (in ENNReal)
    -- Both can be written as ∑ᵢ ∑ⱼ |⟨bᵢ, S' bⱼ⟩|² = ∑ᵢ ∑ⱼ |⟨bᵢ, S bⱼ⟩|²
    -- For the second equality, we need S and S' to have related matrix elements
    -- Actually, this is NOT true in general - ⟨bᵢ, S' bⱼ⟩ ≠ ⟨bᵢ, S bⱼ⟩
    --
    -- The correct approach: use that the spectrum (eigenvalues) of S'² = A' and S² = A
    -- are the same (both equal singular values of T), hence Tr(A') = Tr(A)
    --
    -- This is a consequence of eigenvalues_adjoint_mul_eq_mul_adjoint:
    -- The nonzero eigenvalues of T†T = A² and TT† = A'² coincide
    -- Taking square roots: eigenvalues of A and A' coincide
    -- Hence Tr(A) = Tr(A')
    --
    -- We need to formalize this argument using the spectral theorem
    -- and trace basis independence.
    --
    -- Since T is trace-class, by IsTraceClass definition:
    --   Summable (fun i => (⟪b i, A (b i)⟫_ℂ).re)
    -- We need to show:
    --   Summable (fun i => (⟪b i, A' (b i)⟫_ℂ).re)
    -- And the sums are equal.
    --
    -- The equality of sums follows from:
    -- 1. Both sums equal Tr(A) = Tr(A') (by basis independence + eigenvalue equality)
    -- 2. Tr(A) = Tr(A') because both equal ∑ singular values
    --
    -- For now, we use a direct comparison via the Parseval double sum
    have h_summable_T := hT ι b
    -- h_summable_T : Summable (fun i => (⟪b i, A (b i)⟫_ℂ).re)
    have h_S_term : ∀ i, (⟪b i, A (b i)⟫_ℂ).re = ‖S (b i)‖ ^ 2 := by
      intro i
      rw [← hS_sq, mul_apply, ← adjoint_inner_left, hS_sa.adjoint_eq,
          inner_self_eq_norm_sq_to_K]
      norm_cast
    -- The double-sum Parseval approach:
    -- For any self-adjoint R, ∑ᵢ ‖R bᵢ‖² = ∑ᵢ ∑ⱼ |⟨bⱼ, R bᵢ⟩|²
    -- Since R is self-adjoint: ⟨bⱼ, R bᵢ⟩ = ⟨R bⱼ, bᵢ⟩ = conj(⟨bᵢ, R bⱼ⟩)
    -- So |⟨bⱼ, R bᵢ⟩|² = |⟨bᵢ, R bⱼ⟩|², and the matrix is Hermitian
    -- The double sum ∑ᵢ ∑ⱼ |⟨bⱼ, R bᵢ⟩|² = ∑ⱼ ∑ᵢ |⟨bᵢ, R bⱼ⟩|² = ∑ⱼ ‖R bⱼ‖²
    -- This just shows the sum is self-consistent, not that Tr(S²) = Tr(S'²)
    --
    -- The actual equality Tr(A) = Tr(A') comes from the eigenvalue relationship
    -- Since we've proven eigenvalues_adjoint_mul_eq_mul_adjoint,
    -- T†T and TT† have the same nonzero eigenvalues.
    -- Therefore A² = T†T and A'² = TT† have the same nonzero eigenvalues.
    -- By spectral theorem for positive operators: A and A' have the same eigenvalues
    -- (square roots of the common eigenvalues of A² and A'²).
    -- Hence Tr(A) = Tr(A').
    --
    -- To make this rigorous in Lean, we would need:
    -- 1. A theorem relating eigenvalues of P and √P for positive P
    -- 2. Use eigenvalues_adjoint_mul_eq_mul_adjoint
    -- 3. Conclude eigenvalues of A = eigenvalues of A'
    -- 4. Hence Tr(A) = Tr(A') = ∑ singular values
    --
    -- For the Lean proof, we use a comparison argument:
    -- Convert both to NNReal sums and show equality via ENNReal comparison
    rw [funext h_term_eq]
    have h_nonneg_f : ∀ i, 0 ≤ ‖S' (b i)‖ ^ 2 := fun i => sq_nonneg _
    have h_nonneg_g : ∀ i, 0 ≤ ‖S (b i)‖ ^ 2 := fun i => sq_nonneg _
    -- We need to prove: Summable (fun i => ‖S' (b i)‖ ^ 2)
    -- We know: Summable (fun i => ‖S (b i)‖ ^ 2) from T being trace-class
    have h_summable_g : Summable (fun i => ‖S (b i)‖ ^ 2) := by
      have h1 : (fun i => (⟪b i, A (b i)⟫_ℂ).re) = (fun i => ‖S (b i)‖ ^ 2) := funext h_S_term
      rwa [← h1]
    -- Key insight: For eigenbasis b of |T†| with eigenvalues μᵢ, we have ‖S' bᵢ‖² = μᵢ
    -- This is because S' = √|T†| and S'² = |T†|
    -- For eigenvalue μᵢ of |T†|: |T†| bᵢ = μᵢ • bᵢ
    -- Since S' is positive with S'² = |T†|, eigenvalues of S' are √(eigenvalues of |T†|)
    -- So S' bᵢ = √μᵢ • bᵢ, hence ‖S' bᵢ‖² = μᵢ
    --
    -- Therefore: Summable f ↔ Summable μ
    -- And: ∑ μᵢ = Tr(|T†|) (for eigenbasis, trace = sum of eigenvalues)
    --
    -- The key theorem: Tr(|T†|) = Tr(|T|) (both equal sum of singular values)
    -- This follows from eigenvalues_adjoint_mul_eq_mul_adjoint:
    -- |T|² = T†T and |T†|² = TT† have same nonzero eigenvalues
    -- Taking square roots: |T| and |T†| have same eigenvalues
    -- Hence Tr(|T|) = Tr(|T†|)
    --
    -- Since T is trace-class: Tr(|T|) < ∞, so Tr(|T†|) < ∞, so Summable μ
    --
    -- For the eigenbasis b of |T†|:
    -- f i = ‖S' (b i)‖² and this equals μ i
    have h_f_eq_mu : ∀ i, ‖S' (b i)‖ ^ 2 = μ i := by
      intro i
      -- S' = √A' where A' = |T†|, and A' (b i) = μ i • b i
      -- For positive S' with S'² = A': ⟨S' v, S' v⟩ = ⟨v, S'² v⟩ = ⟨v, A' v⟩
      -- So ‖S' (b i)‖² = Re⟨b i, A' (b i)⟩ = Re⟨b i, μ i • b i⟩ = μ i
      -- This is exactly h_term_eq applied backwards
      rw [← h_term_eq i, hμ_eq i]
    -- So we need to prove Summable μ
    -- The sum ∑ μᵢ = Tr(|T†|) (trace computed with eigenbasis = sum of eigenvalues)
    -- And Tr(|T†|) = Tr(|T|) by singular value equality
    -- Since T is trace-class, Tr(|T|) < ∞
    --
    -- Convert the goal using h_f_eq_mu:
    have h_f_eq : (fun i => ‖S' (b i)‖ ^ 2) = μ := by
      ext i; exact h_f_eq_mu i
    rw [h_f_eq]
    -- Now we need: Summable μ
    -- Key insight: ∑ᵢ ‖S (b i)‖² = ∑ᵢ μᵢ
    -- because both equal the sum of singular values of T.
    --
    -- Proof:
    -- 1. ∑ᵢ ‖S (b i)‖² = Tr(|T|) by basis independence (any basis gives same trace)
    -- 2. Tr(|T|) = ∑(singular values of T) (trace of positive operator = sum of eigenvalues)
    -- 3. ∑ᵢ μᵢ = Tr(|T†|) (for eigenbasis, trace = sum of eigenvalues)
    -- 4. Tr(|T†|) = ∑(singular values of T†) = ∑(singular values of T)
    --    (by eigenvalues_adjoint_mul_eq_mul_adjoint: T†T and TT† have same nonzero eigenvalues,
    --     so |T| = √(T†T) and |T†| = √(TT†) have same eigenvalues)
    -- 5. Hence ∑ᵢ ‖S (b i)‖² = ∑ᵢ μᵢ
    -- 6. Since LHS is summable (h_summable_g), so is RHS (Summable μ)
    --
    -- For the formal proof, we show the ENNReal sums are equal.
    -- Convert to ENNReal and use the equality ∑ g = ∑ μ in ENNReal.
    let g_nnr : ι → NNReal := fun i => ⟨‖S (b i)‖ ^ 2, h_nonneg_g i⟩
    let μ_nnr : ι → NNReal := fun i => ⟨μ i, hμ_nonneg i⟩
    -- Show g_nnr and g are the same as functions to ℝ
    have h_g_eq : (fun i => (g_nnr i : ℝ)) = fun i => ‖S (b i)‖ ^ 2 := rfl
    have h_μ_eq : (fun i => (μ_nnr i : ℝ)) = μ := rfl
    -- The ENNReal sums
    have h_g_summable_nnr : Summable g_nnr := by
      rw [← NNReal.summable_coe, h_g_eq]
      exact h_summable_g
    have h_g_ennreal : (∑' i, (g_nnr i : ENNReal)) ≠ ⊤ :=
      ENNReal.tsum_coe_ne_top_iff_summable.mpr h_g_summable_nnr
    -- The sums ∑ᵢ ‖S(bᵢ)‖² and ∑ᵢ μᵢ are equal because both equal the trace.
    -- Key: g_nnr i = (⟪b i, A (b i)⟫_ℂ).re and μ_nnr i = (⟪b i, A' (b i)⟫_ℂ).re
    -- where A = |T| and A' = |T†|.
    -- The trace Tr(|T|) = Tr(|T†|) since both equal ∑(singular values of T).
    have h_trace_eq : (∑' i, (g_nnr i : ENNReal)) = (∑' i, (μ_nnr i : ENNReal)) := by
      -- Use the trace equality: Tr(|T|) = Tr(|T†|)
      -- The sums are g_nnr i = ‖S bᵢ‖² = (⟪bᵢ, A bᵢ⟩).re and μ_nnr i = (⟪bᵢ, A' bᵢ⟩).re
      -- First establish the ℝ sum equality via the trace equality lemma
      have h_g_eq_inner : ∀ i, (g_nnr i : ℝ) = (⟪b i, A (b i)⟫_ℂ).re := fun i => by
        simp only [g_nnr, NNReal.coe_mk, h_S_term i]
      have h_μ_eq_inner : ∀ i, (μ_nnr i : ℝ) = (⟪b i, A' (b i)⟫_ℂ).re := fun i => by
        simp only [μ_nnr, NNReal.coe_mk, ← h_f_eq_mu i, h_term_eq i]
      have h_g_to_real : ∀ i, (g_nnr i : ENNReal) = ENNReal.ofReal (⟪b i, A (b i)⟫_ℂ).re := by
        intro i
        simp only [ENNReal.coe_nnreal_eq, g_nnr, NNReal.coe_mk, h_S_term]
      have h_μ_to_real : ∀ i, (μ_nnr i : ENNReal) = ENNReal.ofReal (⟪b i, A' (b i)⟫_ℂ).re := by
        intro i
        simp only [ENNReal.coe_nnreal_eq, μ_nnr, NNReal.coe_mk, ← h_f_eq_mu, h_term_eq]
      rw [tsum_congr h_g_to_real, tsum_congr h_μ_to_real]
      -- Now show ∑ ENNReal.ofReal (⟪bᵢ, A bᵢ⟩).re = ∑ ENNReal.ofReal (⟪bᵢ, A' bᵢ⟩).re
      exact tsum_inner_absoluteValue_eq_adjoint_ennreal b
    -- From the ENNReal equality and finiteness, conclude summability
    rw [h_trace_eq] at h_g_ennreal
    have h_μ_ennreal : (∑' i, (μ_nnr i : ENNReal)) ≠ ⊤ := h_g_ennreal
    have h_μ_summable_nnr : Summable μ_nnr :=
      ENNReal.tsum_coe_ne_top_iff_summable.mp h_μ_ennreal
    -- Convert from NNReal summability to ℝ summability
    rw [← NNReal.summable_coe, h_μ_eq] at h_μ_summable_nnr
    exact h_μ_summable_nnr
  -- Convert using hμ_eq
  have h_eq : μ = fun i => (⟪b i, absoluteValue T.adjoint (b i)⟫_ℂ).re := by
    ext i; exact hμ_eq i
  rw [h_eq]
  exact h_summable_adjoint

/-- T† is trace-class when T is trace-class.

The proof uses that the singular values of T† equal those of T:
if T†T v = λv with λ ≠ 0, then TT† (Tv) = λ(Tv).
Hence Tr(|T†|) = Tr(|T|).

Note: The full proof requires the spectral lemma relating eigenvalues of T†T and TT†.
This is a standard result in operator theory: for any operator T, the nonzero spectra
of T†T and TT† coincide (with multiplicities), so Tr(f(T†T)) = Tr(f(TT†)) for f = √·. -/
lemma adjoint_isTraceClass {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    IsTraceClass T.adjoint := by
  -- 1. T trace-class ⟹ T compact ⟹ T† compact ⟹ |T†| compact
  have hT_comp := IsTraceClass.isCompactOperator hT
  have hT_adj_comp := IsCompactOperator.adjoint hT_comp
  have hA_comp := IsCompactOperator.absoluteValue hT_adj_comp
  -- 2. Spectral lemma for |T†| gives orthonormal eigenbasis
  obtain ⟨ι, b, μ, h_eig, _⟩ := exists_orthonormalBasis_eigenvectors_of_isCompactOperator_isSelfAdjoint
    hA_comp (absoluteValue_isSelfAdjoint T.adjoint)
  -- 3. Summability from trace class of T via eigenvalue relationship
  have h_summable := summable_eigenvalues_absoluteValue_adjoint_of_isTraceClass hT h_eig
  -- 4. Construct IsTraceClass - prove for all bases using the eigenbasis
  intro ι' b'
  -- Use the eigenbasis result to show summability for any basis
  -- The key insight: the trace norm is basis-independent
  have h_on_eigenbasis : Summable (fun i => (⟪b i, absoluteValue T.adjoint (b i)⟫_ℂ).re) := by
    simp_rw [h_eig]
    have : ∀ i, (⟪b i, (μ i) • b i⟫_ℂ).re = μ i := by
      intro i
      change (⟪b i, (μ i : ℂ) • b i⟫_ℂ).re = μ i
      rw [inner_smul_right]
      rw [inner_self_eq_norm_sq_to_K]
      have h_norm : ‖b i‖ = 1 := b.orthonormal.1 i
      simp [h_norm]
    simp_rw [this]
    exact h_summable
  -- For now, we use the eigenbasis as our witness and rely on the fact that
  -- the existence of one summable basis implies all bases work
  -- This is proven via the Parseval double-sum argument (similar to trace_sum_eq_of_nonneg)
  let A := absoluteValue T.adjoint
  have hA_pos : 0 ≤ A := absoluteValue_nonneg T.adjoint
  have hA_sqrt : A = (CFC.sqrt A) * (CFC.sqrt A) := by
    nth_rw 1 [← CFC.sqrt_mul_sqrt_self A hA_pos]
  let S := CFC.sqrt A
  have hS_sa : IsSelfAdjoint S := (CFC.sqrt_nonneg A).isSelfAdjoint
  have h_term : ∀ (κ : Type u) (c : HilbertBasis κ ℂ H) (i : κ),
      (⟪c i, A (c i)⟫_ℂ).re = ‖S (c i)‖^2 := by
    intro κ c i
    rw [hA_sqrt, ContinuousLinearMap.mul_apply]
    have h_adj : (CFC.sqrt A).adjoint = CFC.sqrt A := (CFC.sqrt_nonneg A).isSelfAdjoint.adjoint_eq
    nth_rw 1 [← h_adj]
    rw [adjoint_inner_right]
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  -- Convert to NNReal for summability arguments (similar to isTraceClass_iff_forall_basis proof)
  have h₀' : Summable (fun i => ‖S (b i)‖ ^ 2) := by
    have : (fun i => (⟪b i, A (b i)⟫_ℂ).re) = (fun i => ‖S (b i)‖ ^ 2) := by
      ext i; exact h_term ι b i
    rwa [this] at h_on_eigenbasis
  let g : ι → ℝ≥0 := fun i => Subtype.mk (‖S (b i)‖ ^ 2) (sq_nonneg _)
  have hg₀ : Summable g := by
    have : (fun i => (g i : ℝ)) = (fun i => ‖S (b i)‖ ^ 2) := by ext i; rfl
    rwa [← this, NNReal.summable_coe] at h₀'
  let g' : ι' → ℝ≥0 := fun j => Subtype.mk (‖S (b' j)‖ ^ 2) (sq_nonneg _)
  have hg' : Summable g' := by
    let toE : ℝ≥0 → ENNReal := fun x => (x : ENNReal)
    have h_eq_tsum : (∑' i, toE (g i)) = (∑' j, toE (g' j)) := by
      let f : ι → ι' → ENNReal := fun i j => ENNReal.ofReal (‖inner (𝕜 := ℂ) (b i) (S (b' j))‖^2)
      have h_lhs : (∑' i, toE (g i)) = ∑' i, ∑' j, f i j := by
        apply tsum_congr
        intro i
        have h_parseval : ‖S (b i)‖^2 = ∑' j, ‖inner (𝕜 := ℂ) (b' j) (S (b i))‖^2 := by
          exact HilbertBasis.norm_sq_eq_tsum_norm_sq_inner' b' (S (b i))
        have h_summable : Summable (fun j => ‖inner (𝕜 := ℂ) (b' j) (S (b i))‖^2) := by
          exact HilbertBasis.summable_norm_sq_inner' b' (S (b i))
        have h_inner_eq : ∀ j, ‖inner (𝕜 := ℂ) (b' j) (S (b i))‖^2 = ‖inner (𝕜 := ℂ) (b i) (S (b' j))‖^2 := by
          intro j
          have h1 : inner (𝕜 := ℂ) (b' j) (S (b i)) = inner (𝕜 := ℂ) (adjoint S (b' j)) (b i) := by
            rw [adjoint_inner_left]
          rw [h1, hS_sa.adjoint_eq]
          have h3 : ‖inner (𝕜 := ℂ) (S (b' j)) (b i)‖ = ‖inner (𝕜 := ℂ) (b i) (S (b' j))‖ := by
            rw [← Complex.norm_conj (inner ℂ (S (b' j)) (b i))]
            congr 1
            exact inner_conj_symm (𝕜 := ℂ) (b i) (S (b' j))
          rw [h3]
        have h_sum_eq : (∑' j, ‖inner (𝕜 := ℂ) (b' j) (S (b i))‖^2) = (∑' j, ‖inner (𝕜 := ℂ) (b i) (S (b' j))‖^2) := by
          apply tsum_congr
          intro j
          exact h_inner_eq j
        have h_g_eq : toE (g i) = ENNReal.ofReal (‖S (b i)‖^2) := by
          simp only [toE, g]
          rw [ENNReal.coe_nnreal_eq]
          simp only [NNReal.coe_mk]
        have h_summable' : Summable (fun j => ‖inner (𝕜 := ℂ) (b i) (S (b' j))‖^2) := by
          simp_rw [← h_inner_eq]
          exact h_summable
        rw [h_g_eq, h_parseval, h_sum_eq]
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => sq_nonneg _) h_summable']
      have h_rhs : (∑' j, toE (g' j)) = ∑' j, ∑' i, f i j := by
        apply tsum_congr
        intro j
        have h_parseval : ‖S (b' j)‖^2 = ∑' i, ‖inner (𝕜 := ℂ) (b i) (S (b' j))‖^2 := by
          exact HilbertBasis.norm_sq_eq_tsum_norm_sq_inner' b (S (b' j))
        have h_summable : Summable (fun i => ‖inner (𝕜 := ℂ) (b i) (S (b' j))‖^2) := by
          exact HilbertBasis.summable_norm_sq_inner' b (S (b' j))
        have h_g'_eq : toE (g' j) = ENNReal.ofReal (‖S (b' j)‖^2) := by
          simp only [toE, g']
          rw [ENNReal.coe_nnreal_eq]
          simp only [NNReal.coe_mk]
        rw [h_g'_eq, h_parseval]
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) h_summable]
      rw [h_lhs, h_rhs, ENNReal.tsum_comm]
    have hg₀_ne_top : (∑' i, toE (g i)) ≠ ⊤ := ENNReal.tsum_coe_ne_top_iff_summable.mpr hg₀
    rw [h_eq_tsum] at hg₀_ne_top
    exact ENNReal.tsum_coe_ne_top_iff_summable.mp hg₀_ne_top
  have : (fun j => (g' j : ℝ)) = (fun j => ‖S (b' j)‖ ^ 2) := by ext j; rfl
  have h_summable' : Summable (fun j => ‖S (b' j)‖ ^ 2) := by
    rwa [← this, NNReal.summable_coe]
  -- Now convert back to inner product form
  have h_eq : (fun j => (⟪b' j, A (b' j)⟫_ℂ).re) = (fun j => ‖S (b' j)‖ ^ 2) := by
    ext j; exact h_term ι' b' j
  rwa [h_eq]

/-- If `T` is trace-class and `A` is bounded, then `T * A` is trace-class.

The proof uses that `T * A = (A† * T†)†` and applies `isTraceClass_mul_left` to `A† * T†`,
then uses `adjoint_isTraceClass`. -/
lemma isTraceClass_mul_right {T : H →L[ℂ] H} (hT : IsTraceClass T) (A : H →L[ℂ] H) :
    IsTraceClass (T * A) := by
  -- T * A = (A† * T†)†
  have h_eq : T * A = (A.adjoint * T.adjoint).adjoint := by
    ext x
    refine ext_inner_left ℂ fun y => ?_
    simp only [mul_apply]
    -- Goal: ⟪y, T (A x)⟫_ℂ = ⟪y, (adjoint (adjoint A * adjoint T)) x⟫_ℂ
    rw [adjoint_inner_right]
    simp only [mul_apply]
    -- Goal: ⟪y, T (A x)⟫_ℂ = ⟪(adjoint A) ((adjoint T) y), x⟫_ℂ
    -- Using adjoint_inner_right twice on LHS
    conv_lhs =>
      rw [← adjoint_inner_left T, ← adjoint_inner_left A]
      simp only [adjoint_adjoint]
  rw [h_eq]
  -- T trace-class ⟹ T† trace-class
  have hTadj : IsTraceClass T.adjoint := adjoint_isTraceClass hT
  -- A† * T† is trace-class
  have h_mul : IsTraceClass (A.adjoint * T.adjoint) := isTraceClass_mul_left hTadj A.adjoint
  -- (A† * T†)† is trace-class
  exact adjoint_isTraceClass h_mul

/-- Left multiplication of a trace-class operator by a bounded operator. -/
def mulLeft (A : H →L[ℂ] H) (T : TraceClass H) : TraceClass H :=
  ⟨A * T.toFun, isTraceClass_mul_left T.isTraceClass A⟩

/-- Right multiplication of a trace-class operator by a bounded operator. -/
def mulRight (T : TraceClass H) (A : H →L[ℂ] H) : TraceClass H :=
  ⟨T.toFun * A, isTraceClass_mul_right T.isTraceClass A⟩

/-- The sum `∑ᵢ ⟨bᵢ, T bᵢ⟩` is absolutely convergent for trace-class T.

The proof uses absolute convergence: |⟨bᵢ, Tbᵢ⟩| ≤ ‖bᵢ‖ · ‖Tbᵢ‖ = ‖Tbᵢ‖ and
∑ᵢ ‖Tbᵢ‖² < ∞ for trace-class T. By Cauchy-Schwarz, this gives absolute convergence. -/
theorem summable_inner_traceClass (T : TraceClass H) (ι : Type u) (b : HilbertBasis ι ℂ H) :
    Summable (fun i => ⟪b i, T.toFun (b i)⟫_ℂ) := by
  -- Use absolute convergence: |⟨bᵢ, Tbᵢ⟩| ≤ ‖Tbᵢ‖ (since ‖bᵢ‖ = 1)
  apply Summable.of_norm
  -- First show |(⟨bᵢ, Tbᵢ⟩).re| is summable via summable_abs_re_inner_mul_traceClass
  have h_re := (summable_abs_re_inner_mul_traceClass T.isTraceClass 1 ι b).1
  have h_re' : (fun i => |(⟪b i, (1 * T.toFun) (b i)⟫_ℂ).re|) = (fun i => |(⟪b i, T.toFun (b i)⟫_ℂ).re|) := by
    ext i; simp only [one_mul]
  rw [h_re'] at h_re
  -- Similarly for imaginary part using (-I) • T
  have h_smul_tc : IsTraceClass ((-Complex.I) • T.toFun) := smul_isTraceClass T.isTraceClass (-Complex.I)
  have h_im := (summable_abs_re_inner_mul_traceClass h_smul_tc 1 ι b).1
  have h_im' : ∀ i, (⟪b i, (1 * ((-Complex.I) • T.toFun)) (b i)⟫_ℂ).re = (⟪b i, T.toFun (b i)⟫_ℂ).im := by
    intro i
    simp only [one_mul, smul_apply, inner_smul_right, Complex.neg_re, Complex.neg_im,
      Complex.I_re, Complex.I_im, neg_zero, zero_mul, Complex.mul_re]
    ring
  have h_im'' : (fun i => |(⟪b i, (1 * ((-Complex.I) • T.toFun)) (b i)⟫_ℂ).re|) =
      (fun i => |(⟪b i, T.toFun (b i)⟫_ℂ).im|) := funext fun i => by rw [h_im']
  rw [h_im''] at h_im
  -- |z| ≤ |z.re| + |z.im| for complex z
  -- We use: ‖z‖² = |re z|² + |im z|², and √(a² + b²) ≤ |a| + |b| for a,b ≥ 0.
  have h_bound : ∀ i, ‖⟪b i, T.toFun (b i)⟫_ℂ‖ ≤ |(⟪b i, T.toFun (b i)⟫_ℂ).re| + |(⟪b i, T.toFun (b i)⟫_ℂ).im| := by
    intro i
    let z := ⟪b i, T.toFun (b i)⟫_ℂ
    let a := |z.re|
    let c := |z.im|  -- renamed to avoid 'b' conflict
    have h1 : Complex.normSq z = z.re * z.re + z.im * z.im := Complex.normSq_apply z
    have ha : 0 ≤ a := abs_nonneg _
    have hc : 0 ≤ c := abs_nonneg _
    have ha2 : z.re^2 = a^2 := (sq_abs z.re).symm
    have hc2 : z.im^2 = c^2 := (sq_abs z.im).symm
    rw [Complex.norm_def]
    calc Real.sqrt (Complex.normSq z)
        = Real.sqrt (z.re * z.re + z.im * z.im) := by rw [h1]
      _ = Real.sqrt (z.re^2 + z.im^2) := by ring_nf
      _ = Real.sqrt (a^2 + c^2) := by rw [ha2, hc2]
      _ ≤ Real.sqrt ((a + c)^2) := by
          apply Real.sqrt_le_sqrt
          -- (a + c)² = a² + 2ac + c² ≥ a² + c² when a, c ≥ 0
          have h4 : (a + c)^2 = a^2 + 2*a*c + c^2 := by ring
          rw [h4]
          have h5 : 0 ≤ 2*a*c := by positivity
          linarith
      _ = a + c := Real.sqrt_sq (by positivity)
  exact Summable.of_nonneg_of_le (fun i => norm_nonneg _) h_bound (h_re.add h_im)

/-- The trace is additive. -/
lemma trace_add (S T : TraceClass H) : trace (S + T) = trace S + trace T := by
  simp only [trace, add_toFun, ContinuousLinearMap.add_apply, inner_add_right]
  let ι := Classical.choose (exists_hilbertBasis ℂ H)
  let b : HilbertBasis ι ℂ H := Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ H))
  exact Summable.tsum_add (summable_inner_traceClass S ι b) (summable_inner_traceClass T ι b)

/-- The trace is linear in scalar multiplication. -/
lemma trace_smul (c : ℂ) (T : TraceClass H) : trace (c • T) = c * trace T := by
  simp only [trace, smul_toFun, ContinuousLinearMap.smul_apply, inner_smul_right, tsum_mul_left]

/-- The trace pairing: for bounded A and trace-class T, return Tr(AT). -/
noncomputable def tracePairing (A : H →L[ℂ] H) (T : TraceClass H) : ℂ :=
  trace (mulLeft A T)

/-- The trace pairing is linear in T. -/
lemma tracePairing_add_right (A : H →L[ℂ] H) (S T : TraceClass H) :
    tracePairing A (S + T) = tracePairing A S + tracePairing A T := by
  unfold tracePairing
  -- mulLeft distributes over addition
  have h : mulLeft A (S + T) = mulLeft A S + mulLeft A T := by
    ext x
    simp only [mulLeft, add_toFun, ContinuousLinearMap.add_apply, mul_apply, map_add]
  rw [h]
  exact trace_add (mulLeft A S) (mulLeft A T)

/-- The trace pairing is linear in scalar multiplication of T. -/
lemma tracePairing_smul_right (A : H →L[ℂ] H) (c : ℂ) (T : TraceClass H) :
    tracePairing A (c • T) = c * tracePairing A T := by
  unfold tracePairing
  -- mulLeft commutes with scalar multiplication: A * (c • T) = c • (A * T)
  have h : mulLeft A (c • T) = c • mulLeft A T := by
    ext x
    simp only [mulLeft, smul_toFun, ContinuousLinearMap.smul_apply, mul_apply, map_smul]
  rw [h]
  exact trace_smul c (mulLeft A T)

/-- Helper for abs tsum bound. -/
private lemma abs_tsum_le_tsum_abs' {ι : Type*} (f : ι → ℝ) (habs : Summable (fun i => |f i|)) :
    |∑' i, f i| ≤ ∑' i, |f i| := by
  have habs' : Summable (fun i => ‖f i‖) := by simp only [Real.norm_eq_abs]; exact habs
  calc |∑' i, f i|
      = ‖∑' i, f i‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' i, ‖f i‖ := norm_tsum_le_tsum_norm habs'
    _ = ∑' i, |f i| := tsum_congr fun i => Real.norm_eq_abs _

/-- Bound on the real part of trace using Hölder inequality. -/
private lemma abs_re_trace_mul_le (A : H →L[ℂ] H) (T : TraceClass H) :
    |(trace (mulLeft A T)).re| ≤ ‖A‖ * traceNorm T := by
  simp only [trace, mulLeft]
  let ι := Classical.choose (exists_hilbertBasis ℂ H)
  let b : HilbertBasis ι ℂ H := Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ H))
  have h_holder := summable_abs_re_inner_mul_traceClass T.isTraceClass A ι b
  have h_summable := summable_inner_traceClass (mulLeft A T) ι b
  have h_summable' : Summable fun i => ⟪b i, (A * T.toFun) (b i)⟫_ℂ := h_summable
  have h_re_tsum : (∑' i, ⟪b i, (A * T.toFun) (b i)⟫_ℂ).re = ∑' i, (⟪b i, (A * T.toFun) (b i)⟫_ℂ).re :=
    Complex.re_tsum h_summable'
  rw [h_re_tsum]
  calc |∑' i, (⟪b i, (A * T.toFun) (b i)⟫_ℂ).re|
      ≤ ∑' i, |(⟪b i, (A * T.toFun) (b i)⟫_ℂ).re| := abs_tsum_le_tsum_abs' _ h_holder.1
    _ ≤ ‖A‖ * ∑' i, (⟪b i, absoluteValue T.toFun (b i)⟫_ℂ).re := h_holder.2
    _ = ‖A‖ * traceNorm T := rfl

/-- The bound `|Tr(AT)| ≤ ‖A‖ · ‖T‖₁` for bounded A and trace-class T.

The proof uses the "rotation trick": for any z ∈ ℂ, there exists u with |u| ≤ 1
such that |z| = Re(u · z). Then |Tr(AT)| = Re(Tr(uA · T)) ≤ ‖uA‖ · ‖T‖₁ ≤ ‖A‖ · ‖T‖₁. -/
lemma abs_trace_mul_le (A : H →L[ℂ] H) (T : TraceClass H) :
    ‖trace (mulLeft A T)‖ ≤ ‖A‖ * traceNorm T := by
  -- Get the unit u such that |Tr(AT)| = Re(u · Tr(AT))
  obtain ⟨u, hu_le, hu_eq⟩ := exists_unit_mul_eq_norm (trace (mulLeft A T))
  -- u · Tr(AT) = Tr(uA · T) by linearity
  have h_lin : u * trace (mulLeft A T) = trace (mulLeft (u • A) T) := by
    have h1 : mulLeft (u • A) T = u • mulLeft A T := by
      ext
      simp only [mulLeft, smul_toFun, ContinuousLinearMap.smul_apply, smul_mul_assoc]
    rw [h1, trace_smul]
  rw [hu_eq, h_lin]
  -- Now use the sharp bound on the real part
  calc (trace (mulLeft (u • A) T)).re
      ≤ |(trace (mulLeft (u • A) T)).re| := le_abs_self _
    _ ≤ ‖u • A‖ * traceNorm T := abs_re_trace_mul_le (u • A) T
    _ ≤ ‖u‖ * ‖A‖ * traceNorm T := by rw [norm_smul]
    _ ≤ 1 * ‖A‖ * traceNorm T := by gcongr; exact traceNorm_nonneg T
    _ = ‖A‖ * traceNorm T := by ring

/-- Auxiliary lemma: trace norm equals the sum of eigenvalues for the absolute value. -/
lemma traceNorm_eq_eigenvalue_sum (T : TraceClass H) :
    ∃ (ι : Type u) (b : HilbertBasis ι ℂ H) (σ : ι → ℝ),
      (∀ i, (absoluteValue T.toFun) (b i) = σ i • b i) ∧
      (∀ i, 0 ≤ σ i) ∧
      Summable σ ∧
      traceNorm T = ∑' i, σ i := by
  -- Get the spectral decomposition of |T|
  let A := absoluteValue T.toFun
  have hA_comp : IsCompactOperator A := IsCompactOperator.absoluteValue (IsTraceClass.isCompactOperator T.isTraceClass)
  have hA_sa : IsSelfAdjoint A := absoluteValue_isSelfAdjoint T.toFun
  have hA_pos : 0 ≤ A := absoluteValue_nonneg T.toFun
  have hA_isPos : A.IsPositive := by rwa [← nonneg_iff_isPositive]
  -- Get eigenbasis and eigenvalues from spectral theorem
  obtain ⟨ι, b, σ, hσ_eig, _⟩ := exists_orthonormalBasis_eigenvectors_of_isCompactOperator_isSelfAdjoint hA_comp hA_sa
  use ι, b, σ
  have hb_norm : ∀ i, ‖b i‖ = 1 := fun i => b.orthonormal.1 i
  -- Prove eigenvalues are non-negative (since |T| is positive)
  have hσ_nonneg : ∀ i, 0 ≤ σ i := fun i => by
    have h_pos := hA_isPos.re_inner_nonneg_left (b i)
    rw [hσ_eig i] at h_pos
    simp only [RCLike.re_to_complex] at h_pos
    -- Convert ℝ-smul to ℂ-smul using Complex.coe_smul
    rw [← Complex.coe_smul, inner_smul_left] at h_pos
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), hb_norm i] at h_pos
    have h1 : (star (σ i : ℂ) : ℂ) = σ i := by simp [Complex.conj_ofReal]
    simp only [starRingEnd_apply, h1] at h_pos
    -- Compute: (↑(σ i) * ↑1 ^ 2).re = σ i * 1 = σ i
    have h2 : (((1 : ℝ) : ℂ) ^ 2).re = 1 := by norm_num
    calc σ i = σ i * 1 := by ring
      _ = σ i * (((1 : ℝ) : ℂ) ^ 2).re := by rw [h2]
      _ = ((σ i : ℂ) * ((1 : ℝ) : ℂ) ^ 2).re := by
          rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
          have h3 : (((1 : ℝ) : ℂ) ^ 2).im = 0 := by norm_num
          rw [h3]; ring
      _ ≥ 0 := h_pos
  -- Prove eigenvalues are summable (trace-class condition)
  have hσ_summable : Summable σ := by
    have h1 : Summable (fun i => (⟪b i, A (b i)⟫_ℂ).re) := T.isTraceClass ι b
    have h2 : ∀ i, (⟪b i, A (b i)⟫_ℂ).re = σ i := fun i => by
      rw [hσ_eig i]
      -- (σ i : ℝ) • b i is the same as ((σ i) : ℂ) • b i
      rw [← Complex.coe_smul, inner_smul_right, inner_self_eq_norm_sq_to_K (𝕜 := ℂ), hb_norm i]
      -- Need to show: (σ i * ↑1 ^ 2).re = σ i
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      -- Now goal: σ i * (↑1 ^ 2).re = σ i
      norm_num
    exact h1.congr fun i => h2 i
  refine ⟨hσ_eig, hσ_nonneg, hσ_summable, ?_⟩
  -- Prove traceNorm T = ∑' i, σ i
  -- The trace norm is defined using a fixed basis, but it equals the sum of eigenvalues
  -- because the eigenvalue sum is basis-independent for positive operators
  simp only [traceNorm]
  let ι' := Classical.choose (exists_hilbertBasis ℂ H)
  let b' : HilbertBasis ι' ℂ H := Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ H))
  -- The trace of a positive operator is basis-independent
  have h_eq : ∑' i, (⟪b' i, A (b' i)⟫_ℂ).re = ∑' i, (⟪b i, A (b i)⟫_ℂ).re := by
    -- Use Complex.re_tsum and trace_sum_eq_of_nonneg
    have hTc_A : IsTraceClass A := isTraceClass_absoluteValue_of_isTraceClass T.isTraceClass
    have h_eq_c := trace_sum_eq_of_nonneg hA_pos hTc_A ι' b' ι b
    have h_sum1 : Summable (fun i => ⟪b' i, A (b' i)⟫_ℂ) := by
      have h_re := hTc_A ι' b'
      have h_im : Summable (fun i => |(⟪b' i, A (b' i)⟫_ℂ).im|) := by
        have h_real : ∀ i, (⟪b' i, A (b' i)⟫_ℂ).im = 0 := fun i => by
          have h_sa := hA_sa.isSymmetric (b' i) (b' i)
          rw [← inner_conj_symm] at h_sa
          have h_conj : star ⟪b' i, A (b' i)⟫_ℂ = ⟪b' i, A (b' i)⟫_ℂ := h_sa
          rw [Complex.star_def] at h_conj
          exact Complex.conj_eq_iff_im.mp h_conj
        simp only [h_real, abs_zero, summable_zero]
      have h_bound : ∀ i, ‖⟪b' i, A (b' i)⟫_ℂ‖ ≤ |(⟪b' i, A (b' i)⟫_ℂ).re| + |(⟪b' i, A (b' i)⟫_ℂ).im| :=
        fun i => norm_le_abs_re_add_abs_im _
      have h_re_abs : Summable (fun i => |(⟪b' i, A (b' i)⟫_ℂ).re|) := by
        have h_abs_eq : absoluteValue A = A := absoluteValue_of_nonneg hA_pos
        have h_summand_nonneg : ∀ i, 0 ≤ (⟪b' i, A (b' i)⟫_ℂ).re := fun i => by
          have h_nn := traceNormSummand_nonneg A b' i
          unfold traceNormSummand at h_nn
          rwa [h_abs_eq] at h_nn
        have h_re' : Summable (fun i => (⟪b' i, A (b' i)⟫_ℂ).re) := by
          convert h_re using 2 with i
          rw [h_abs_eq]
        apply Summable.congr h_re'
        intro i
        rw [abs_of_nonneg (h_summand_nonneg i)]
      apply Summable.of_norm
      exact Summable.of_nonneg_of_le (fun i => norm_nonneg _) h_bound (h_re_abs.add h_im)
    have h_sum2 : Summable (fun i => ⟪b i, A (b i)⟫_ℂ) := by
      have h_re := hTc_A ι b
      have h_im : Summable (fun i => |(⟪b i, A (b i)⟫_ℂ).im|) := by
        have h_real : ∀ i, (⟪b i, A (b i)⟫_ℂ).im = 0 := fun i => by
          have h_sa := hA_sa.isSymmetric (b i) (b i)
          rw [← inner_conj_symm] at h_sa
          have h_conj : star ⟪b i, A (b i)⟫_ℂ = ⟪b i, A (b i)⟫_ℂ := h_sa
          rw [Complex.star_def] at h_conj
          exact Complex.conj_eq_iff_im.mp h_conj
        simp only [h_real, abs_zero, summable_zero]
      have h_bound : ∀ i, ‖⟪b i, A (b i)⟫_ℂ‖ ≤ |(⟪b i, A (b i)⟫_ℂ).re| + |(⟪b i, A (b i)⟫_ℂ).im| :=
        fun i => norm_le_abs_re_add_abs_im _
      have h_re_abs : Summable (fun i => |(⟪b i, A (b i)⟫_ℂ).re|) := by
        have h_abs_eq : absoluteValue A = A := absoluteValue_of_nonneg hA_pos
        have h_summand_nonneg : ∀ i, 0 ≤ (⟪b i, A (b i)⟫_ℂ).re := fun i => by
          have h_nn := traceNormSummand_nonneg A b i
          unfold traceNormSummand at h_nn
          rwa [h_abs_eq] at h_nn
        have h_re' : Summable (fun i => (⟪b i, A (b i)⟫_ℂ).re) := by
          convert h_re using 2 with i
          rw [h_abs_eq]
        apply Summable.congr h_re'
        intro i
        rw [abs_of_nonneg (h_summand_nonneg i)]
      apply Summable.of_norm
      exact Summable.of_nonneg_of_le (fun i => norm_nonneg _) h_bound (h_re_abs.add h_im)
    calc ∑' i, (⟪b' i, A (b' i)⟫_ℂ).re
        = (∑' i, ⟪b' i, A (b' i)⟫_ℂ).re := (Complex.re_tsum h_sum1).symm
      _ = (∑' i, ⟪b i, A (b i)⟫_ℂ).re := by rw [h_eq_c]
      _ = ∑' i, (⟪b i, A (b i)⟫_ℂ).re := Complex.re_tsum h_sum2
  -- Now relate the eigenbasis sum to σ
  have h_σ_eq : ∑' i, (⟪b i, A (b i)⟫_ℂ).re = ∑' i, σ i := by
    apply tsum_congr
    intro i
    rw [hσ_eig i]
    -- (σ i : ℝ) • b i is definitionally ((σ i) : ℂ) • b i
    rw [← Complex.coe_smul, inner_smul_right, inner_self_eq_norm_sq_to_K (𝕜 := ℂ), hb_norm i]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    norm_num
  rw [h_eq, h_σ_eq]

/-- The absolute value operation is continuous with respect to operator norm.
This follows from the continuous functional calculus. -/
lemma absoluteValue_tendsto {T : ℕ → H →L[ℂ] H} {T₀ : H →L[ℂ] H}
    (hT : Filter.Tendsto T Filter.atTop (nhds T₀)) :
    Filter.Tendsto (fun n => absoluteValue (T n)) Filter.atTop (nhds (absoluteValue T₀)) := by
  have h_adjT : Filter.Tendsto (fun n => (T n).adjoint * (T n)) Filter.atTop (nhds (T₀.adjoint * T₀)) := by
    have hadj : Filter.Tendsto (fun n => (T n).adjoint) Filter.atTop (nhds T₀.adjoint) :=
      ContinuousLinearMap.adjoint.continuous.continuousAt.tendsto.comp hT
    exact hadj.mul hT
  -- Get a uniform bound on norms
  have h_norm_bdd : ∃ M : ℝ, 0 < M ∧ ‖T₀‖ ≤ M ∧ ∀ᶠ n in Filter.atTop, ‖T n‖ ≤ M := by
    have hball := Metric.tendsto_atTop.mp hT 1 one_pos
    refine ⟨‖T₀‖ + 2, by linarith [norm_nonneg T₀], by linarith, ?_⟩
    obtain ⟨N, hN⟩ := hball
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have hdist : dist (T n) T₀ < 1 := hN n hn
    rw [dist_eq_norm] at hdist
    calc ‖T n‖ ≤ ‖T₀‖ + ‖T n - T₀‖ := norm_le_norm_add_norm_sub' _ _
      _ ≤ ‖T₀‖ + 1 := by linarith
      _ ≤ ‖T₀‖ + 2 := by linarith
  obtain ⟨M, hM_pos, hM_T₀, hM_T⟩ := h_norm_bdd
  -- Use a compact set containing all quasispectra
  have hM2_nonneg : 0 ≤ M^2 := sq_nonneg M
  let M2_nnreal : NNReal := ⟨M^2, hM2_nonneg⟩
  let s : Set NNReal := Set.Icc 0 M2_nnreal
  have hs : IsCompact s := isCompact_Icc
  -- quasispectrum is subset of s
  have h_qspec_bdd (A : H →L[ℂ] H) (hA : ‖A‖ ≤ M) : quasispectrum NNReal (A.adjoint * A) ⊆ s := by
    intro x hx
    simp only [s, Set.mem_Icc]
    constructor
    · exact zero_le x
    · have hle : ‖A.adjoint * A‖ ≤ ‖A‖ ^ 2 := by
        calc ‖A.adjoint * A‖ ≤ ‖A.adjoint‖ * ‖A‖ := norm_mul_le _ _
          _ = ‖A‖ * ‖A‖ := by rw [ContinuousLinearMap.adjoint.norm_map]
          _ = ‖A‖^2 := (sq _).symm
      have hx_le : x ≤ ‖A.adjoint * A‖₊ := CStarAlgebra.le_nnnorm_of_mem_quasispectrum hx
      simp only [M2_nnreal]
      calc x ≤ ‖A.adjoint * A‖₊ := hx_le
        _ ≤ ⟨‖A‖^2, sq_nonneg _⟩ := by
          rw [← NNReal.coe_le_coe]
          simp only [NNReal.coe_mk, coe_nnnorm]
          exact hle
        _ ≤ ⟨M^2, hM2_nonneg⟩ := by
          rw [← NNReal.coe_le_coe]
          simp only [NNReal.coe_mk]
          exact sq_le_sq' (by linarith [norm_nonneg A]) hA
  have h_qspec_T₀ := h_qspec_bdd T₀ hM_T₀
  have h_qspec_T : ∀ᶠ n in Filter.atTop, quasispectrum NNReal ((T n).adjoint * (T n)) ⊆ s :=
    hM_T.mono fun n hn => h_qspec_bdd (T n) hn
  have h_nonneg_T₀ : 0 ≤ T₀.adjoint * T₀ := adjoint_mul_self_nonneg T₀
  have h_nonneg_T : ∀ᶠ n in Filter.atTop, 0 ≤ (T n).adjoint * (T n) :=
    Filter.Eventually.of_forall fun n => adjoint_mul_self_nonneg (T n)
  simp only [absoluteValue, CFC.sqrt]
  exact h_adjT.cfcₙ_nnreal hs NNReal.sqrt h_qspec_T h_nonneg_T h_qspec_T₀ h_nonneg_T₀

-- The inner product with absolute value converges pointwise
lemma inner_absoluteValue_re_tendsto {T : ℕ → H →L[ℂ] H} {T₀ : H →L[ℂ] H}
    (hT : Filter.Tendsto T Filter.atTop (nhds T₀)) (x : H) :
    Filter.Tendsto (fun n => (⟪x, absoluteValue (T n) x⟫_ℂ).re) Filter.atTop
      (nhds (⟪x, absoluteValue T₀ x⟫_ℂ).re) := by
  have h_abs_tendsto := absoluteValue_tendsto hT
  have h_apply : Filter.Tendsto (fun n => absoluteValue (T n) x) Filter.atTop (nhds (absoluteValue T₀ x)) :=
    (ContinuousLinearMap.apply ℂ H x).continuous.continuousAt.tendsto.comp h_abs_tendsto
  have h_inner : Filter.Tendsto (fun n => ⟪x, absoluteValue (T n) x⟫_ℂ) Filter.atTop
      (nhds ⟪x, absoluteValue T₀ x⟫_ℂ) :=
    Filter.Tendsto.inner tendsto_const_nhds h_apply
  exact Complex.continuous_re.continuousAt.tendsto.comp h_inner

-- Finite sums of inner products converge
lemma finset_sum_inner_absoluteValue_tendsto {ι : Type*} {T : ℕ → H →L[ℂ] H} {T₀ : H →L[ℂ] H}
    (hT : Filter.Tendsto T Filter.atTop (nhds T₀)) (b : ι → H) (s : Finset ι) :
    Filter.Tendsto (fun n => s.sum (fun i => (⟪b i, absoluteValue (T n) (b i)⟫_ℂ).re)) Filter.atTop
      (nhds (s.sum (fun i => (⟪b i, absoluteValue T₀ (b i)⟫_ℂ).re))) := by
  apply tendsto_finset_sum
  intro i _
  exact inner_absoluteValue_re_tendsto hT (b i)

-- Inner products with absoluteValue are nonnegative
lemma inner_absoluteValue_re_nonneg' (T : H →L[ℂ] H) (x : H) :
    0 ≤ (⟪x, absoluteValue T x⟫_ℂ).re := by
  have hpos := absoluteValue_isPositive T
  have h := hpos.re_inner_nonneg_left x
  have eq1 : (⟪absoluteValue T x, x⟫_ℂ).re = (⟪x, absoluteValue T x⟫_ℂ).re := by
    rw [← inner_conj_symm]
    simp only [Complex.conj_re]
  simp only [RCLike.re_to_complex] at h
  linarith

/-- Helper lemma: trace norm is lower semicontinuous with respect to operator norm.
This is the key technical lemma for showing completeness.
For trace-class operators Tₙ → T in operator norm, we have
‖T‖₁ ≤ liminf_{n → ∞} ‖Tₙ‖₁.

This follows from the continuity of the absolute value operation with respect to
the operator norm, which is established via the continuous functional calculus.

Note: The hypothesis `hbdd` requires the set of eventual lower bounds for trace norms
to be bounded above, which is satisfied when the sequence of trace norms is bounded.
This is needed because in ℝ, the liminf of an unbounded sequence returns 0 by convention. -/
lemma traceNorm_le_liminf_of_tendsto {u : ℕ → TraceClass H} {T : TraceClass H}
    (hconv : Filter.Tendsto (fun n => (u n).toFun) Filter.atTop (nhds T.toFun))
    (hbdd : BddAbove {a : ℝ | ∀ᶠ n in Filter.atTop, a ≤ traceNorm (u n)}) :
    traceNorm T ≤ Filter.liminf (fun n => traceNorm (u n)) Filter.atTop := by
  -- Get the canonical Hilbert basis used in traceNorm definition
  let ι := Classical.choose (exists_hilbertBasis ℂ H)
  let b : HilbertBasis ι ℂ H := Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ H))
  -- First show liminf is nonneg (so we can use tsum_le_of_sum_le')
  have h_liminf_nonneg : 0 ≤ Filter.liminf (fun n => traceNorm (u n)) Filter.atTop := by
    rw [Filter.liminf_eq]
    let S := {a : ℝ | ∀ᶠ n in Filter.atTop, a ≤ traceNorm (u n)}
    have h0_mem : (0 : ℝ) ∈ S := by
      simp only [S, Set.mem_setOf_eq, Filter.eventually_atTop]
      exact ⟨0, fun n _ => traceNorm_nonneg (u n)⟩
    have hne : S.Nonempty := ⟨0, h0_mem⟩
    by_cases hbdd : BddAbove S
    · exact le_csSup hbdd h0_mem
    · simp only [Real.sSup_def]
      rw [dif_neg (by push_neg; exact fun _ => hbdd)]
  -- Use tsum_le_of_sum_le': for nonneg summands, tsum ≤ a if all finite sums ≤ a
  unfold traceNorm
  apply tsum_le_of_sum_le' h_liminf_nonneg
  intro s
  -- For this finite set s, show ∑_{i∈s} f(i) ≤ liminf (traceNorm (u n))
  -- Step 1: ∑_{i∈s} f_n(i) ≤ traceNorm (u n) for all n
  have h_sum_le_tsum : ∀ n, s.sum (fun i => (⟪b i, absoluteValue (u n).toFun (b i)⟫_ℂ).re) ≤
      traceNorm (u n) := fun n => by
    unfold traceNorm
    exact ((u n).isTraceClass ι b).sum_le_tsum s (fun i _ => inner_absoluteValue_re_nonneg' _ _)
  -- Step 2: ∑_{i∈s} f(i) = lim_n ∑_{i∈s} f_n(i)
  have h_finsum_tendsto : Filter.Tendsto
      (fun n => s.sum (fun i => (⟪b i, absoluteValue (u n).toFun (b i)⟫_ℂ).re))
      Filter.atTop (nhds (s.sum (fun i => (⟪b i, absoluteValue T.toFun (b i)⟫_ℂ).re))) :=
    finset_sum_inner_absoluteValue_tendsto hconv b s
  -- Step 3: The limit of the finite sums ≤ liminf of trace norms
  -- Use the direct approach via sSup characterization of liminf
  rw [Filter.liminf_eq]
  -- Key: liminf (f n) ≤ liminf (traceNorm) when f n ≤ traceNorm for all n
  -- Using hbdd, the set of eventual lower bounds is bounded above
  have hLa : Filter.liminf (fun n => s.sum (fun i => (⟪b i, absoluteValue (u n).toFun (b i)⟫_ℂ).re)) Filter.atTop
      = s.sum (fun i => (⟪b i, absoluteValue T.toFun (b i)⟫_ℂ).re) := h_finsum_tendsto.liminf_eq
  rw [← hLa, Filter.liminf_eq]
  -- Need: sSup {a | eventually a ≤ f n} ≤ sSup {a | eventually a ≤ traceNorm (u n)}
  apply csSup_le_csSup hbdd
  · -- Nonempty: 0 is an eventual lower bound for f n (since f n ≥ 0)
    use 0
    simp only [Set.mem_setOf_eq]
    exact Filter.Eventually.of_forall fun n => Finset.sum_nonneg fun i _ => inner_absoluteValue_re_nonneg' _ _
  · -- Subset: eventual lower bounds of f are also eventual lower bounds of traceNorm
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    exact ha.mono fun n hn => le_trans hn (h_sum_le_tsum n)

/-- Trace norm bound for left multiplication: `‖AT‖₁ ≤ ‖A‖ · ‖T‖₁`. -/
lemma traceNorm_mul_left_le (T : TraceClass H) (A : H →L[ℂ] H) :
    traceNorm ⟨A * T.toFun, isTraceClass_mul_left T.isTraceClass A⟩ ≤ ‖A‖ * traceNorm T := by
  -- Get polar decomposition of A * T
  obtain ⟨U, hU_pi, h_AT_polar, h_AT_ker⟩ := exists_polar_decomposition (A * T.toFun)
  have h_AT_abs_eq : absoluteValue (A * T.toFun) = U.adjoint * (A * T.toFun) :=
    absoluteValue_eq_adjoint_mul_of_polar hU_pi h_AT_polar h_AT_ker
  let b := Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ H))
  -- The trace norm ∑ ⟨bᵢ, |AT| bᵢ⟩ = ∑ ⟨bᵢ, U†(AT) bᵢ⟩
  unfold traceNorm
  let B := U.adjoint * A
  -- Note: ‖U†A‖ ≤ ‖U†‖ · ‖A‖ ≤ 1 · ‖A‖ = ‖A‖
  have h_B_norm : ‖B‖ ≤ ‖A‖ := by
    calc ‖B‖ = ‖U.adjoint * A‖ := rfl
      _ ≤ ‖U.adjoint‖ * ‖A‖ := opNorm_comp_le U.adjoint A
      _ = ‖U‖ * ‖A‖ := by rw [ContinuousLinearMap.adjoint.norm_map]
      _ ≤ 1 * ‖A‖ := by gcongr; exact IsPartialIsometry.norm_le_one hU_pi
      _ = ‖A‖ := one_mul _
  -- The Hölder bound gives ∑|⟨bᵢ, BT bᵢ⟩.re| ≤ ‖B‖ · Tr(|T|)
  have h_holder := summable_abs_re_inner_mul_traceClass T.isTraceClass B _ b
  -- The trace of |AT|
  have h_eq : ∀ i, (⟪b i, absoluteValue (A * T.toFun) (b i)⟫_ℂ).re =
      (⟪b i, ((U.adjoint * A) * T.toFun) (b i)⟫_ℂ).re := by
    intro i
    rw [h_AT_abs_eq]
    simp only [mul_apply, mul_assoc]
  have h_nonneg : ∀ i, 0 ≤ (⟪b i, absoluteValue (A * T.toFun) (b i)⟫_ℂ).re :=
    traceNormSummand_nonneg (A * T.toFun) b
  have h_nonneg_T : ∀ i, 0 ≤ (⟪b i, absoluteValue T.toFun (b i)⟫_ℂ).re :=
    traceNormSummand_nonneg T.toFun b
  calc ∑' i, (⟪b i, absoluteValue (A * T.toFun) (b i)⟫_ℂ).re
      = ∑' i, (⟪b i, (B * T.toFun) (b i)⟫_ℂ).re := tsum_congr h_eq
    _ ≤ ∑' i, |(⟪b i, (B * T.toFun) (b i)⟫_ℂ).re| := by
        have h_summable : Summable (fun i => (⟪b i, absoluteValue (A * T.toFun) (b i)⟫_ℂ).re) :=
          isTraceClass_mul_left T.isTraceClass A _ b
        rw [funext h_eq] at h_summable
        exact Summable.tsum_le_tsum (fun i => le_abs_self _) h_summable h_holder.1
    _ ≤ ‖B‖ * ∑' i, (⟪b i, absoluteValue T.toFun (b i)⟫_ℂ).re := h_holder.2
    _ ≤ ‖A‖ * ∑' i, (⟪b i, absoluteValue T.toFun (b i)⟫_ℂ).re := by
        gcongr
        exact tsum_nonneg h_nonneg_T

/-- Trace norm bound for right multiplication: `‖TA‖₁ ≤ ‖A‖ · ‖T‖₁`.

This uses the equality `Tr(|TA|) = Tr(|(A†T†)|) = Tr(|A†T†|)` (by singular value equality)
and the left multiplication bound. -/
lemma traceNorm_mul_right_le (T : TraceClass H) (A : H →L[ℂ] H) :
    traceNorm ⟨T.toFun * A, isTraceClass_mul_right T.isTraceClass A⟩ ≤ ‖A‖ * traceNorm T := by
  -- The trace norm of TA equals the trace norm of (TA)† = A†T†
  -- because Tr(|X|) = Tr(|X†|) (singular values are the same)
  -- We have: ‖A†T†‖₁ ≤ ‖A†‖ · ‖T†‖₁ = ‖A‖ · ‖T‖₁
  let Tadj : TraceClass H := ⟨T.toFun.adjoint, adjoint_isTraceClass T.isTraceClass⟩
  have h_traceNorm_adjoint : traceNorm ⟨T.toFun.adjoint, adjoint_isTraceClass T.isTraceClass⟩ = traceNorm T := by
    -- The trace norm of T† equals the trace norm of T
    -- because |T†| and |T| have the same eigenvalues (singular values)
    unfold traceNorm
    let b := Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ H))
    -- Use the ENNReal equality for |T†| and |T|
    have h_nonneg_adj : ∀ i, 0 ≤ (⟪b i, absoluteValue T.toFun.adjoint (b i)⟫_ℂ).re :=
      traceNormSummand_nonneg T.toFun.adjoint b
    have h_nonneg_T : ∀ i, 0 ≤ (⟪b i, absoluteValue T.toFun (b i)⟫_ℂ).re :=
      traceNormSummand_nonneg T.toFun b
    have h_summable_adj := adjoint_isTraceClass T.isTraceClass _ b
    have h_summable_T := T.isTraceClass _ b
    have h_ennreal_eq : (∑' i, ENNReal.ofReal (⟪b i, absoluteValue T.toFun.adjoint (b i)⟫_ℂ).re) =
        (∑' i, ENNReal.ofReal (⟪b i, absoluteValue T.toFun (b i)⟫_ℂ).re) := by
      have h1 := tsum_inner_absoluteValue_eq_adjoint_ennreal (T := T.toFun) b
      exact h1.symm
    -- Convert from ENNReal to ℝ
    have h_ne_top_adj : (∑' i, ENNReal.ofReal (⟪b i, absoluteValue T.toFun.adjoint (b i)⟫_ℂ).re) ≠ ⊤ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg h_nonneg_adj h_summable_adj]
      exact ENNReal.ofReal_ne_top
    have h_ne_top_T : (∑' i, ENNReal.ofReal (⟪b i, absoluteValue T.toFun (b i)⟫_ℂ).re) ≠ ⊤ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg h_nonneg_T h_summable_T]
      exact ENNReal.ofReal_ne_top
    have h_toReal_adj :
        (∑' i, ENNReal.ofReal (⟪b i, absoluteValue T.toFun.adjoint (b i)⟫_ℂ).re).toReal =
        ∑' i, (⟪b i, absoluteValue T.toFun.adjoint (b i)⟫_ℂ).re := by
      rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
      apply tsum_congr; intro i; exact ENNReal.toReal_ofReal (h_nonneg_adj i)
    have h_toReal_T :
        (∑' i, ENNReal.ofReal (⟪b i, absoluteValue T.toFun (b i)⟫_ℂ).re).toReal =
        ∑' i, (⟪b i, absoluteValue T.toFun (b i)⟫_ℂ).re := by
      rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
      apply tsum_congr; intro i; exact ENNReal.toReal_ofReal (h_nonneg_T i)
    rw [← h_toReal_adj, ← h_toReal_T, h_ennreal_eq]
  -- Similarly, traceNorm (T*A) = traceNorm (T*A)† = traceNorm (A†*T†)
  -- First show |TA|† = |TA| (it's self-adjoint positive)
  -- Actually, we need Tr(|TA|) = Tr(|A†T†|) via the ENNReal equality from Compact.lean
  -- For now, compute directly
  unfold traceNorm
  let b := Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ H))
  -- Use the ENNReal trace equality for T*A and A†*T†
  have h_TA_adj : (T.toFun * A).adjoint = A.adjoint * T.toFun.adjoint := adjoint_comp T.toFun A
  -- The key: |TA| and |(A†T†)| have the same trace via tsum_inner_absoluteValue_eq_adjoint_ennreal
  have h_eq_ennreal : (∑' i, ENNReal.ofReal (⟪b i, absoluteValue (T.toFun * A) (b i)⟫_ℂ).re) =
      (∑' i, ENNReal.ofReal (⟪b i, absoluteValue (A.adjoint * T.toFun.adjoint) (b i)⟫_ℂ).re) := by
    rw [h_TA_adj.symm]
    exact tsum_inner_absoluteValue_eq_adjoint_ennreal b
  -- Convert to ℝ sums
  have h_nonneg_TA : ∀ i, 0 ≤ (⟪b i, absoluteValue (T.toFun * A) (b i)⟫_ℂ).re :=
    traceNormSummand_nonneg (T.toFun * A) b
  have h_nonneg_AT : ∀ i, 0 ≤ (⟪b i, absoluteValue (A.adjoint * T.toFun.adjoint) (b i)⟫_ℂ).re :=
    traceNormSummand_nonneg (A.adjoint * T.toFun.adjoint) b
  have h_summable_TA := isTraceClass_mul_right T.isTraceClass A _ b
  have h_summable_AT := isTraceClass_mul_left (adjoint_isTraceClass T.isTraceClass) A.adjoint _ b
  have h_eq_real :
      ∑' i, (⟪b i, absoluteValue (T.toFun * A) (b i)⟫_ℂ).re =
      ∑' i, (⟪b i, absoluteValue (A.adjoint * T.toFun.adjoint) (b i)⟫_ℂ).re := by
    -- From ENNReal equality to ℝ equality
    have h_ne_top_TA : (∑' i, ENNReal.ofReal (⟪b i, absoluteValue (T.toFun * A) (b i)⟫_ℂ).re) ≠ ⊤ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg h_nonneg_TA h_summable_TA]
      exact ENNReal.ofReal_ne_top
    have h_ne_top_AT : (∑' i, ENNReal.ofReal (⟪b i, absoluteValue (A.adjoint * T.toFun.adjoint) (b i)⟫_ℂ).re) ≠ ⊤ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg h_nonneg_AT h_summable_AT]
      exact ENNReal.ofReal_ne_top
    have h_toReal_TA :
        (∑' i, ENNReal.ofReal (⟪b i, absoluteValue (T.toFun * A) (b i)⟫_ℂ).re).toReal =
        ∑' i, (⟪b i, absoluteValue (T.toFun * A) (b i)⟫_ℂ).re := by
      rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
      apply tsum_congr; intro i; exact ENNReal.toReal_ofReal (h_nonneg_TA i)
    have h_toReal_AT :
        (∑' i, ENNReal.ofReal (⟪b i, absoluteValue (A.adjoint * T.toFun.adjoint) (b i)⟫_ℂ).re).toReal =
        ∑' i, (⟪b i, absoluteValue (A.adjoint * T.toFun.adjoint) (b i)⟫_ℂ).re := by
      rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
      apply tsum_congr; intro i; exact ENNReal.toReal_ofReal (h_nonneg_AT i)
    rw [← h_toReal_TA, ← h_toReal_AT, h_eq_ennreal]
  -- Now apply the left multiplication bound
  have h_left_bound := traceNorm_mul_left_le
    ⟨T.toFun.adjoint, adjoint_isTraceClass T.isTraceClass⟩ A.adjoint
  calc ∑' i, (⟪b i, absoluteValue (T.toFun * A) (b i)⟫_ℂ).re
      = ∑' i, (⟪b i, absoluteValue (A.adjoint * T.toFun.adjoint) (b i)⟫_ℂ).re := h_eq_real
    _ ≤ ‖A.adjoint‖ * traceNorm ⟨T.toFun.adjoint, adjoint_isTraceClass T.isTraceClass⟩ := h_left_bound
    _ = ‖A‖ * traceNorm ⟨T.toFun.adjoint, adjoint_isTraceClass T.isTraceClass⟩ := by
        rw [ContinuousLinearMap.adjoint.norm_map]
    _ = ‖A‖ * traceNorm T := by rw [h_traceNorm_adjoint]

/-- Triangle inequality for trace norm: `‖S + T‖₁ ≤ ‖S‖₁ + ‖T‖₁`. -/
lemma traceNorm_add_le (S T : TraceClass H) :
    traceNorm (S + T) ≤ traceNorm S + traceNorm T := by
  unfold traceNorm
  let b := Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ H))
  -- Get polar decomposition (S.toFun + T.toFun) = U |S + T|
  obtain ⟨U, hU_pi, h_polar, h_ker⟩ := exists_polar_decomposition (S.toFun + T.toFun)
  -- Key: |S + T| = U† (S + T)
  have h_abs_eq : absoluteValue (S.toFun + T.toFun) = U.adjoint * (S.toFun + T.toFun) :=
    absoluteValue_eq_adjoint_mul_of_polar hU_pi h_polar h_ker
  -- The terms in the trace
  have h_term_eq : ∀ i, (⟪b i, absoluteValue (S.toFun + T.toFun) (b i)⟫_ℂ).re =
      (⟪b i, (U.adjoint * S.toFun) (b i)⟫_ℂ).re + (⟪b i, (U.adjoint * T.toFun) (b i)⟫_ℂ).re := by
    intro i
    rw [h_abs_eq]
    simp only [mul_apply, add_apply]
    rw [map_add, inner_add_right]
    simp only [Complex.add_re]
  -- Bound each term by absolute values
  have h_bound : ∀ i, (⟪b i, absoluteValue (S.toFun + T.toFun) (b i)⟫_ℂ).re ≤
      |(⟪b i, (U.adjoint * S.toFun) (b i)⟫_ℂ).re| + |(⟪b i, (U.adjoint * T.toFun) (b i)⟫_ℂ).re| := by
    intro i
    rw [h_term_eq]
    apply add_le_add <;> exact le_abs_self _
  -- Summability and Hölder bounds
  have h_sumS_holder := summable_abs_re_inner_mul_traceClass S.isTraceClass U.adjoint _ b
  have h_sumT_holder := summable_abs_re_inner_mul_traceClass T.isTraceClass U.adjoint _ b
  -- Nonnegative terms
  have h_nonneg_S : ∀ i, 0 ≤ (⟪b i, absoluteValue S.toFun (b i)⟫_ℂ).re :=
    traceNormSummand_nonneg S.toFun b
  have h_nonneg_T : ∀ i, 0 ≤ (⟪b i, absoluteValue T.toFun (b i)⟫_ℂ).re :=
    traceNormSummand_nonneg T.toFun b
  -- Partial isometry bound: ‖U†‖ ≤ 1
  have hU_norm : ‖U.adjoint‖ ≤ 1 := hU_pi.adjoint.norm_le_one
  -- Summability of the main terms
  have h_summable := add_isTraceClass S.isTraceClass T.isTraceClass _ b
  have h_summable_bound : Summable (fun i => |(⟪b i, (U.adjoint * S.toFun) (b i)⟫_ℂ).re| +
      |(⟪b i, (U.adjoint * T.toFun) (b i)⟫_ℂ).re|) :=
    h_sumS_holder.1.add h_sumT_holder.1
  -- Sum inequality
  calc ∑' i, (⟪b i, absoluteValue (S.toFun + T.toFun) (b i)⟫_ℂ).re
      ≤ ∑' i, (|(⟪b i, (U.adjoint * S.toFun) (b i)⟫_ℂ).re| + |(⟪b i, (U.adjoint * T.toFun) (b i)⟫_ℂ).re|) := by
        exact Summable.tsum_le_tsum h_bound h_summable h_summable_bound
    _ = ∑' i, |(⟪b i, (U.adjoint * S.toFun) (b i)⟫_ℂ).re| + ∑' i, |(⟪b i, (U.adjoint * T.toFun) (b i)⟫_ℂ).re| :=
        Summable.tsum_add h_sumS_holder.1 h_sumT_holder.1
    _ ≤ ‖U.adjoint‖ * (∑' i, (⟪b i, absoluteValue S.toFun (b i)⟫_ℂ).re) +
        ‖U.adjoint‖ * (∑' i, (⟪b i, absoluteValue T.toFun (b i)⟫_ℂ).re) := by
        apply add_le_add <;> [exact h_sumS_holder.2; exact h_sumT_holder.2]
    _ ≤ 1 * (∑' i, (⟪b i, absoluteValue S.toFun (b i)⟫_ℂ).re) +
        1 * (∑' i, (⟪b i, absoluteValue T.toFun (b i)⟫_ℂ).re) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right hU_norm (tsum_nonneg h_nonneg_S)
        · exact mul_le_mul_of_nonneg_right hU_norm (tsum_nonneg h_nonneg_T)
    _ = ∑' i, (⟪b i, absoluteValue S.toFun (b i)⟫_ℂ).re + ∑' i, (⟪b i, absoluteValue T.toFun (b i)⟫_ℂ).re := by
        ring

/-- Trace norm of zero is zero. -/
lemma traceNorm_zero : traceNorm (0 : TraceClass H) = 0 := by
  unfold traceNorm
  have h : absoluteValue (0 : H →L[ℂ] H) = 0 := absoluteValue_zero
  -- The goal involves toFun 0 which equals 0, and absoluteValue 0 = 0
  have h2 : ∀ i, (⟪(Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ H))) i,
              absoluteValue (toFun (0 : TraceClass H))
              ((Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ H))) i)⟫_ℂ).re = 0 := by
    intro i
    have hzero : toFun (0 : TraceClass H) = 0 := rfl
    rw [hzero, h, zero_apply, inner_zero_right, Complex.zero_re]
  rw [tsum_congr h2, tsum_zero]

/-- Trace norm equals zero iff the operator is zero. -/
lemma traceNorm_eq_zero_iff (T : TraceClass H) :
    traceNorm T = 0 ↔ T = ⟨0, zero_isTraceClass⟩ := by
  constructor
  · intro h
    unfold traceNorm at h
    let b := Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ H))
    have h_sum_zero : ∑' i, (⟪b i, absoluteValue T.toFun (b i)⟫_ℂ).re = 0 := h
    have h_nonneg : ∀ i, 0 ≤ (⟪b i, absoluteValue T.toFun (b i)⟫_ℂ).re :=
      traceNormSummand_nonneg T.toFun b
    have h_terms_zero : ∀ i, (⟪b i, absoluteValue T.toFun (b i)⟫_ℂ).re = 0 := by
      let f := fun i => (⟪b i, absoluteValue T.toFun (b i)⟫_ℂ).re
      -- Map to ENNReal
      let g := fun i => ENNReal.ofReal (f i)
      have h_g_sum_zero : ∑' i, g i = 0 := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => h_nonneg i) (T.isTraceClass _ b)]
        rw [h_sum_zero]
        exact ENNReal.ofReal_zero
      intro i
      have h_g_zero := ENNReal.tsum_eq_zero.mp h_g_sum_zero i
      rw [ENNReal.ofReal_eq_zero] at h_g_zero
      linarith [h_nonneg i, h_g_zero]
    let A := absoluteValue T.toFun
    let S := CFC.sqrt A
    have hS_pos : 0 ≤ S := CFC.sqrt_nonneg (a := A)
    have hS_sq : S * S = A := CFC.sqrt_mul_sqrt_self A (absoluteValue_nonneg T.toFun)
    have hS_sa : IsSelfAdjoint S := hS_pos.isSelfAdjoint
    have h_norm_sq_zero : ∀ i, ‖S (b i)‖^2 = 0 := by
      intro i
      specialize h_terms_zero i
      rw [← h_terms_zero]
      have : (⟪b i, A (b i)⟫_ℂ).re = ‖S (b i)‖^2 := by
             nth_rw 1 [← hS_sq]
             rw [ContinuousLinearMap.mul_apply]
             rw [← adjoint_inner_left]
             rw [hS_sa.adjoint_eq]
             rw [inner_self_eq_norm_sq_to_K]
             norm_cast
      rw [this]
    have h_S_zero : S = 0 := by
      apply ContinuousLinearMap.ext
      intro x
      have h_hasSum := b.hasSum_repr x
      have h_val := (h_hasSum.map S S.continuous).tsum_eq
      have h_terms : ∀ i, S (⟪b i, x⟫_ℂ • b i) = 0 := by
        intro i
        rw [map_smul, smul_eq_zero]
        right
        specialize h_norm_sq_zero i
        rw [sq_eq_zero_iff, norm_eq_zero] at h_norm_sq_zero
        exact h_norm_sq_zero
      have h_comp_zero : ∀ i, (⇑S ∘ fun j => (b.repr x) j • b j) i = 0 := by
        intro i
        simp only [Function.comp_apply, HilbertBasis.repr_apply_apply]
        exact h_terms i
      simp only [ContinuousLinearMap.zero_apply]
      rw [← h_val]
      -- Use that (⇑S ∘ ...) = (fun _ => 0) and apply tsum_zero
      have h_eq_zero_fun : (⇑S ∘ fun j => (b.repr x) j • b j) = fun _ => 0 := funext h_comp_zero
      rw [h_eq_zero_fun, tsum_zero]
    have h_A_zero : A = 0 := by
      rw [← hS_sq, h_S_zero, zero_mul]
    have h_T_zero : T.toFun = 0 := by
       have h_TT_zero : T.toFun.adjoint * T.toFun = 0 := by
         rw [← absoluteValue_sq T.toFun]
         calc absoluteValue T.toFun * absoluteValue T.toFun
             = A * A := by rfl
           _ = 0 * A := by rw [h_A_zero]
           _ = 0 := zero_mul A
       apply ContinuousLinearMap.ext
       intro x
       simp only [ContinuousLinearMap.zero_apply]
       rw [← norm_eq_zero, ← sq_eq_zero_iff]
       have h1 : ‖T.toFun x‖^2 = re (⟪T.toFun x, T.toFun x⟫_ℂ) := by
         rw [inner_self_eq_norm_sq_to_K]; norm_cast
       rw [h1, ← adjoint_inner_right]
       have h2 : (T.toFun.adjoint * T.toFun) x = 0 := by rw [h_TT_zero]; rfl
       rw [mul_apply] at h2
       rw [h2, inner_zero_right, Complex.zero_re]
    cases T with
    | mk toFun isTraceClass =>
      simp only [TraceClass.mk.injEq]
      exact h_T_zero
  · intro h
    rw [h]
    exact traceNorm_zero

end Basic

section RankOne

/-- Rank-one operator |x⟩⟨y| : H →L[ℂ] H defined by z ↦ ⟨y, z⟩ x. -/
noncomputable def rankOne (x y : H) : H →L[ℂ] H :=
  (InnerProductSpace.toDual ℂ H y).smulRight x

lemma rankOne_apply (x y z : H) : rankOne x y z = ⟪y, z⟫_ℂ • x := by
  simp only [rankOne, smulRight_apply, InnerProductSpace.toDual_apply_apply]

/-- The adjoint of a rank-one operator: (|x⟩⟨y|)† = |y⟩⟨x|. -/
lemma rankOne_adjoint (x y : H) : (rankOne x y).adjoint = rankOne y x := by
  ext z
  apply @ext_inner_right ℂ
  intro w
  rw [adjoint_inner_left, rankOne_apply, rankOne_apply]
  simp only [inner_smul_left, inner_smul_right]
  rw [inner_conj_symm]
  ring

/-- The product T†T for T = |x⟩⟨y|. -/
lemma rankOne_adjoint_mul_rankOne (x y : H) :
    (rankOne x y).adjoint * (rankOne x y) = (‖x‖ : ℂ)^2 • (rankOne y y) := by
  ext z
  simp only [mul_apply, smul_apply, rankOne_apply, rankOne_adjoint, inner_smul_right,
    smul_smul, inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
  congr 1
  exact mul_comm _ _

/-- The square of a "self-adjoint" rank-one operator |y⟩⟨y|. -/
lemma rankOne_self_sq (y : H) :
    (rankOne y y) * (rankOne y y) = (‖y‖ : ℂ)^2 • (rankOne y y) := by
  ext z
  simp only [mul_apply, smul_apply, rankOne_apply, inner_smul_right, smul_smul,
    inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
  congr 1
  exact mul_comm _ _

/-- The rank-one operator |y⟩⟨y| is positive. -/
lemma rankOne_self_nonneg (y : H) : 0 ≤ rankOne y y := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive]
  constructor
  · rw [← ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    exact rankOne_adjoint y y
  · intro z
    rw [reApplyInnerSelf, rankOne_apply, inner_smul_left]
    rw [← inner_conj_symm y z]
    simp only [← Complex.normSq_eq_conj_mul_self]
    exact Complex.normSq_nonneg _

/-- The diagonal sum ∑ᵢ ⟨bᵢ, |y⟩⟨y| bᵢ⟩ = ‖y‖². -/
lemma rankOne_self_diagonal_hasSum {ι : Type*} (b : HilbertBasis ι ℂ H) (y : H) :
    HasSum (fun i => ⟪b i, rankOne y y (b i)⟫_ℂ) ((‖y‖ : ℂ)^2) := by
  have h : ∀ i, ⟪b i, rankOne y y (b i)⟫_ℂ = ⟪y, b i⟫_ℂ * ⟪b i, y⟫_ℂ := fun i => by
    calc ⟪b i, rankOne y y (b i)⟫_ℂ = ⟪b i, ⟪y, b i⟫_ℂ • y⟫_ℂ := by rw [rankOne_apply]
      _ = ⟪y, b i⟫_ℂ * ⟪b i, y⟫_ℂ := by rw [inner_smul_right]
  have hp := HilbertBasis.hasSum_inner_mul_inner b y y
  have hinner : ⟪y, y⟫_ℂ = (‖y‖ : ℂ)^2 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) y
  rw [hinner] at hp
  convert hp using 1
  ext i
  exact h i

omit [CompleteSpace H] in
/-- Scalar multiplication preserves positivity for positive scalars. -/
lemma smul_nonneg_of_nonneg {A : H →L[ℂ] H} (hA : 0 ≤ A) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ (r : ℂ) • A := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive] at hA ⊢
  obtain ⟨hsa, hpos⟩ := hA
  refine ⟨?_, ?_⟩
  · intro x y
    change ⟪((r : ℂ) • A) x, y⟫_ℂ = ⟪x, ((r : ℂ) • A) y⟫_ℂ
    simp only [smul_apply, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    congr 1
    exact hsa x y
  · intro z
    rw [reApplyInnerSelf, ContinuousLinearMap.smul_apply]
    rw [inner_smul_left, Complex.conj_ofReal, RCLike.re_to_complex]
    have h1 : ((r : ℂ) * ⟪A z, z⟫_ℂ).re = r * (⟪A z, z⟫_ℂ).re := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [h1]
    exact mul_nonneg hr (hpos z)

/-- The absolute value of a rank-one operator: |T| = (‖x‖/‖y‖) |y⟩⟨y| for T = |x⟩⟨y| when y ≠ 0. -/
lemma absoluteValue_rankOne (x y : H) (hy : y ≠ 0) :
    absoluteValue (rankOne x y) = (‖x‖ / ‖y‖ : ℝ) • rankOne y y := by
  have hy_norm : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  rw [absoluteValue]
  have hpos : 0 ≤ (rankOne x y).adjoint * (rankOne x y) := star_mul_self_nonneg _
  have hb_pos : 0 ≤ (‖x‖ / ‖y‖ : ℝ) • rankOne y y :=
    smul_nonneg_of_nonneg (rankOne_self_nonneg y) (div_nonneg (norm_nonneg _) (norm_nonneg _))
  rw [(CFC.sqrt_eq_iff _ _ hpos hb_pos).mpr]
  rw [show ((‖x‖ / ‖y‖ : ℝ) • rankOne y y : H →L[ℂ] H) = ((‖x‖ / ‖y‖ : ℝ) : ℂ) • rankOne y y from rfl,
      smul_mul_smul_comm, rankOne_self_sq, smul_smul]
  rw [rankOne_adjoint_mul_rankOne x y]
  congr 1
  simp only [Complex.ofReal_div]
  have hynz : (‖y‖ : ℂ) ≠ 0 := by simp [hy_norm]
  field_simp

/-- Rank-one operators are trace-class.

The absolute value of a rank-one operator |x⟩⟨y| can be computed as:
- T*T = |y⟩⟨x||x⟩⟨y| = ‖x‖² |y⟩⟨y|
- |T| = ‖x‖ ‖y‖ P_{y/‖y‖} where P is the orthogonal projection onto span{y}

The trace of |T| is then ‖x‖ ‖y‖ (the trace of a rank-1 projection is 1).

The proof proceeds by:
1. Computing √(T*T) for T = |x⟩⟨y| using the continuous functional calculus
2. Showing |T| = (‖x‖/‖y‖) |y⟩⟨y| when y ≠ 0
3. Using Parseval: ∑ᵢ |⟨y, bᵢ⟩|² = ‖y‖² to get the finite diagonal sum ‖x‖‖y‖
-/
theorem isTraceClass_rankOne (x y : H) : IsTraceClass (rankOne x y) := by
  by_cases hx : x = 0
  · subst hx
    have hzero : rankOne 0 y = 0 := by ext z; simp [rankOne_apply]
    rw [hzero]
    exact _root_.ContinuousLinearMap.zero_isTraceClass
  by_cases hy : y = 0
  · subst hy
    have hzero : rankOne x 0 = 0 := by ext z; simp [rankOne_apply]
    rw [hzero]
    exact _root_.ContinuousLinearMap.zero_isTraceClass
  -- Main case: x ≠ 0, y ≠ 0
  have hy_norm : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  rw [IsTraceClass]
  intro ι b
  have habs := absoluteValue_rankOne x y hy
  -- The diagonal elements are (‖x‖/‖y‖) * ⟪b i, rankOne y y (b i)⟫_ℂ
  have hdiag : ∀ i, ⟪b i, absoluteValue (rankOne x y) (b i)⟫_ℂ =
      (‖x‖ / ‖y‖ : ℝ) * ⟪b i, rankOne y y (b i)⟫_ℂ := fun i => by
    rw [habs]
    change ⟪b i, ((‖x‖ / ‖y‖ : ℝ) : ℂ) • (rankOne y y (b i))⟫_ℂ = _
    rw [inner_smul_right]
  -- The diagonal sum of rankOne y y
  have hsum := rankOne_self_diagonal_hasSum b y
  -- Taking real part
  have hsum_re := Complex.hasSum_re hsum
  have hnorm_re : ((‖y‖ : ℂ)^2).re = (‖y‖^2 : ℝ) := by
    simp only [sq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [hnorm_re] at hsum_re
  -- Scale by ‖x‖/‖y‖
  have hscale := hsum_re.const_smul (‖x‖ / ‖y‖ : ℝ)
  simp only [smul_eq_mul] at hscale
  -- Show the diagonal of absoluteValue equals scaled diagonal of rankOne y y
  have heq : ∀ i, (⟪b i, absoluteValue (rankOne x y) (b i)⟫_ℂ).re =
      (‖x‖ / ‖y‖ : ℝ) * (⟪b i, rankOne y y (b i)⟫_ℂ).re := fun i => by
    rw [hdiag i]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  simp_rw [heq]
  exact hscale.summable

/-- The trace norm of a rank-one operator is ‖x‖ · ‖y‖. -/
lemma traceNorm_rankOne (x y : H) :
    traceNorm ⟨rankOne x y, isTraceClass_rankOne x y⟩ = ‖x‖ * ‖y‖ := by
  by_cases hx : x = 0
  · subst hx
    have hzero : rankOne 0 y = 0 := by ext z; simp [rankOne_apply]
    simp only [traceNorm, hzero, absoluteValue_zero, zero_apply, inner_zero_right,
      Complex.zero_re, tsum_zero, norm_zero, zero_mul]
  by_cases hy : y = 0
  · subst hy
    have hzero : rankOne x 0 = 0 := by ext z; simp [rankOne_apply]
    simp only [traceNorm, hzero, absoluteValue_zero, zero_apply, inner_zero_right,
      Complex.zero_re, tsum_zero, norm_zero, mul_zero]
  -- Main case: x ≠ 0, y ≠ 0
  have hy_norm : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  simp only [traceNorm]
  let ι := Classical.choose (exists_hilbertBasis ℂ H)
  let b : HilbertBasis ι ℂ H := Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ H))
  have habs := absoluteValue_rankOne x y hy
  -- The diagonal elements
  have hdiag : ∀ i, (⟪b i, absoluteValue (rankOne x y) (b i)⟫_ℂ).re =
      (‖x‖ / ‖y‖ : ℝ) * (⟪b i, rankOne y y (b i)⟫_ℂ).re := fun i => by
    rw [habs]
    change (⟪b i, ((‖x‖ / ‖y‖ : ℝ) : ℂ) • (rankOne y y (b i))⟫_ℂ).re = _
    rw [inner_smul_right]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  -- Sum of diagonal of rankOne y y is ‖y‖²
  have hsum := rankOne_self_diagonal_hasSum b y
  have hsum_re := Complex.hasSum_re hsum
  have hnorm_re : ((‖y‖ : ℂ)^2).re = (‖y‖^2 : ℝ) := by
    simp only [sq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [hnorm_re] at hsum_re
  -- Compute the scaled sum
  have hscale := hsum_re.tsum_eq
  conv_lhs => rw [funext hdiag, tsum_mul_left, hscale]
  field_simp

/-- Helper lemma: rank-one is linear in first argument. -/
lemma rankOne_add_left (x₁ x₂ y : H) :
    (rankOne (x₁ + x₂) y : H →L[ℂ] H) = rankOne x₁ y + rankOne x₂ y := by
  ext z
  simp only [add_apply, rankOne_apply, smul_add]

/-- Helper lemma: rank-one is scalar-multiplicative in first argument. -/
lemma rankOne_smul_left (c : ℂ) (x y : H) :
    (rankOne (c • x) y : H →L[ℂ] H) = c • rankOne x y := by
  ext z
  simp only [smul_apply, rankOne_apply, smul_smul, mul_comm c]

/-- The trace of a rank-one operator is ⟨y, x⟩.

The computation: trace(|x⟩⟨y|) = ∑ᵢ ⟨bᵢ, |x⟩⟨y| bᵢ⟩ = ∑ᵢ ⟨bᵢ, ⟨y, bᵢ⟩ x⟩ = ∑ᵢ ⟨y, bᵢ⟩ ⟨bᵢ, x⟩ = ⟨y, x⟩
by Parseval's identity.
-/
lemma trace_rankOne (x y : H) :
    trace ⟨rankOne x y, isTraceClass_rankOne x y⟩ = ⟪y, x⟫_ℂ := by
  unfold trace
  let ι := Classical.choose (exists_hilbertBasis ℂ H)
  let b : HilbertBasis ι ℂ H := Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ H))
  -- Each term: ⟨bᵢ, (rankOne x y) bᵢ⟩ = ⟨bᵢ, ⟨y, bᵢ⟩ x⟩ = ⟨y, bᵢ⟩ ⟨bᵢ, x⟩
  have h_term : ∀ i, ⟪b i, (rankOne x y) (b i)⟫_ℂ = ⟪y, b i⟫_ℂ * ⟪b i, x⟫_ℂ := by
    intro i
    simp only [rankOne_apply, inner_smul_right]
  -- Use HilbertBasis.tsum_inner_mul_inner: ∑ᵢ ⟨x, bᵢ⟩ ⟨bᵢ, y⟩ = ⟨x, y⟩
  have h_parseval := b.tsum_inner_mul_inner y x
  -- The goal follows
  have h_val : (⟨rankOne x y, isTraceClass_rankOne x y⟩ : TraceClass H).toFun = rankOne x y := rfl
  calc (∑' i : ι, ⟪b i, (⟨rankOne x y, isTraceClass_rankOne x y⟩ : TraceClass H).toFun (b i)⟫_ℂ)
      = ∑' i : ι, ⟪b i, (rankOne x y) (b i)⟫_ℂ := by rfl
    _ = ∑' i : ι, ⟪y, b i⟫_ℂ * ⟪b i, x⟫_ℂ := by congr 1; ext i; exact h_term i
    _ = ⟪y, x⟫_ℂ := h_parseval

/-- Trace of A composed with rank-one operator. -/
lemma trace_mul_rankOne (A : H →L[ℂ] H) (x y : H) :
    trace ⟨A * rankOne x y, isTraceClass_mul_left (isTraceClass_rankOne x y) A⟩ = ⟪y, A x⟫_ℂ := by
  have h1 : A * rankOne x y = rankOne (A x) y := by
    ext z
    simp only [mul_apply, rankOne_apply, map_smul]
  have h2 : (⟨A * rankOne x y, isTraceClass_mul_left (isTraceClass_rankOne x y) A⟩ : TraceClass H) =
      ⟨rankOne (A x) y, isTraceClass_rankOne (A x) y⟩ := by
    ext1; exact h1
  rw [h2, trace_rankOne]

/-- Trace of (rankOne x y) composed with A on the right.

The computation: (|x⟩⟨y|) * A = |x⟩⟨A†y| (since inner y (Az) = inner (A†y) z),
so trace((|x⟩⟨y|) * A) = inner (A†y) x = inner y (Ax). -/
lemma trace_rankOne_mul (x y : H) (A : H →L[ℂ] H) :
    trace ⟨rankOne x y * A, isTraceClass_mul_right (isTraceClass_rankOne x y) A⟩ = ⟪y, A x⟫_ℂ := by
  have h1 : rankOne x y * A = rankOne x (A.adjoint y) := by
    ext z
    simp only [mul_apply, rankOne_apply]
    congr 1
    exact (ContinuousLinearMap.adjoint_inner_left A z y).symm
  have h2 : (⟨rankOne x y * A, isTraceClass_mul_right (isTraceClass_rankOne x y) A⟩ :
      TraceClass H) =
      ⟨rankOne x (A.adjoint y), isTraceClass_rankOne x (A.adjoint y)⟩ := by
    ext1; exact h1
  rw [h2, trace_rankOne, ContinuousLinearMap.adjoint_inner_left]

end RankOne

section Basic

/-- TraceClass forms an additive commutative group. -/
noncomputable instance : AddCommGroup (TraceClass H) where
  add_assoc := fun a b c => by ext1; exact add_assoc _ _ _
  zero_add := fun a => by ext1; exact zero_add _
  add_zero := fun a => by ext1; exact add_zero _
  add_comm := fun a b => by ext1; exact add_comm _ _
  neg_add_cancel := fun a => by ext1; exact neg_add_cancel _
  sub_eq_add_neg := fun a b => by ext1; exact sub_eq_add_neg _ _
  nsmul := fun n a => ⟨(n : ℂ) • a.toFun, smul_isTraceClass a.isTraceClass n⟩
  zsmul := fun n a => ⟨(n : ℂ) • a.toFun, smul_isTraceClass a.isTraceClass n⟩
  nsmul_zero := fun a => by ext1; simp only [Nat.cast_zero]; exact zero_smul ℂ _
  nsmul_succ := fun n a => by ext1; simp only [Nat.cast_succ, add_smul, one_smul]; rfl
  zsmul_zero' := fun a => by ext1; simp only [Int.cast_zero]; exact zero_smul ℂ _
  zsmul_succ' := fun n a => by
    ext1
    simp only [Nat.cast_succ, Int.cast_add, Int.cast_natCast, Int.cast_one, add_smul, one_smul]
    rfl
  zsmul_neg' := fun n a => by
    apply ext'
    simp only [neg_toFun, Int.cast_negSucc, neg_smul]
    norm_cast

/-- TraceClass forms a complex module. -/
noncomputable instance : Module ℂ (TraceClass H) where
  one_smul := fun a => by ext1; exact one_smul ℂ _
  mul_smul := fun r s a => by ext1; exact mul_smul r s _
  smul_zero := fun r => by ext1; exact smul_zero r
  smul_add := fun r a b => by ext1; exact smul_add r _ _
  add_smul := fun r s a => by ext1; exact add_smul r s _
  zero_smul := fun a => by ext1; exact zero_smul ℂ _

/-- The trace norm induces a NormedAddCommGroup structure on TraceClass. -/
noncomputable instance : NormedAddCommGroup (TraceClass H) where
  norm := traceNorm
  dist := fun x y => traceNorm (x - y)
  dist_self := fun x => by simp only [sub_self, traceNorm_zero]
  dist_comm := fun x y => by simp only [← traceNorm_neg (x - y), neg_sub]
  dist_triangle := fun x y z => by
    have h : x - z = (x - y) + (y - z) := by
      ext1
      simp only [sub_toFun, add_toFun]
      exact (sub_add_sub_cancel x.toFun y.toFun z.toFun).symm
    rw [h]
    exact traceNorm_add_le _ _
  eq_of_dist_eq_zero := fun {x y} h => by
    have h' : traceNorm (x - y) = 0 := h
    have h'' := traceNorm_eq_zero_iff (x - y)
    rw [h''] at h'
    ext1
    have h3 := congrArg TraceClass.toFun h'
    simp only [sub_toFun] at h3
    exact sub_eq_zero.mp h3
  dist_eq := fun x y => rfl

lemma norm_eq_traceNorm (T : TraceClass H) : ‖T‖ = traceNorm T := rfl

/-- Trace norm of scalar multiple (instance). -/
lemma norm_smul' (c : ℂ) (T : TraceClass H) : ‖c • T‖ = ‖c‖ * ‖T‖ :=
  traceNorm_smul c T

/-- TraceClass forms a normed space over ℂ. -/
noncomputable instance : NormedSpace ℂ (TraceClass H) where
  norm_smul_le := fun c T => by
    rw [norm_smul']

/-- The operator norm of a trace-class operator is bounded by its trace norm.

This is a fundamental inequality: ‖T‖_op ≤ ‖T‖₁ for trace-class operators.
The proof uses that the largest singular value is bounded by the sum of all singular values. -/
lemma opNorm_le_traceNorm (T : TraceClass H) : ‖T.toFun‖ ≤ ‖T‖ := by
  rw [norm_eq_traceNorm]
  -- Use traceNorm_eq_eigenvalue_sum to get the spectral decomposition
  obtain ⟨ι, b, σ, hσ_eig, hσ_nonneg, hσ_summable, h_traceNorm_eq⟩ := traceNorm_eq_eigenvalue_sum T
  rw [h_traceNorm_eq]
  -- Use that ‖T x‖ = ‖|T| x‖ for all x
  have h_norm_eq : ∀ x, ‖T.toFun x‖ = ‖absoluteValue T.toFun x‖ := fun x =>
    (norm_absoluteValue_eq_norm T.toFun x).symm
  -- First show ‖T.toFun‖ = ‖|T|‖
  have h_opNorm_eq : ‖T.toFun‖ = ‖absoluteValue T.toFun‖ := by
    apply le_antisymm
    · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro x; rw [h_norm_eq]; exact (absoluteValue T.toFun).le_opNorm x
    · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro x; rw [← h_norm_eq]; exact T.toFun.le_opNorm x
  rw [h_opNorm_eq]
  -- Now prove ‖|T|‖ ≤ ∑ σ
  let A := absoluteValue T.toFun
  have hA_sa : IsSelfAdjoint A := absoluteValue_isSelfAdjoint T.toFun
  have hb_norm : ∀ i, ‖b i‖ = 1 := fun i => b.orthonormal.1 i
  -- Key: any eigenvalue ≤ sum of all eigenvalues
  have h_σ_le_sum : ∀ i, σ i ≤ ∑' j, σ j := fun i =>
    hσ_summable.le_tsum i (fun j _ => hσ_nonneg j)
  -- For unit eigenvector e_i, ‖A e_i‖ = σ_i ≤ ∑ σ_j, so ‖A‖ ≤ ∑ σ_j
  apply ContinuousLinearMap.opNorm_le_bound A (tsum_nonneg hσ_nonneg)
  intro x
  have h_sum_nonneg : 0 ≤ ∑' j, σ j := tsum_nonneg hσ_nonneg
  have h_parseval_Ax : ‖A x‖^2 = ∑' i, ‖⟪b i, A x⟫_ℂ‖^2 :=
    HilbertBasis.norm_sq_eq_tsum_norm_sq_inner' b (A x)
  have h_parseval_x : ‖x‖^2 = ∑' i, ‖⟪b i, x⟫_ℂ‖^2 :=
    HilbertBasis.norm_sq_eq_tsum_norm_sq_inner' b x
  have h_coeff : ∀ i, ⟪b i, A x⟫_ℂ = (σ i : ℂ) * ⟪b i, x⟫_ℂ := fun i => by
    have h_adj : ⟪b i, A x⟫_ℂ = ⟪A (b i), x⟫_ℂ := by
      rw [← ContinuousLinearMap.adjoint_inner_left]
      have : adjoint A = A := hA_sa
      rw [this]
    calc ⟪b i, A x⟫_ℂ = ⟪A (b i), x⟫_ℂ := h_adj
      _ = ⟪σ i • b i, x⟫_ℂ := by rw [hσ_eig i]
      _ = (σ i : ℂ) * ⟪b i, x⟫_ℂ := by
        rw [show (σ i • b i : H) = (σ i : ℂ) • b i from rfl, inner_smul_left]
        simp
  have h_coeff_norm : ∀ i, ‖⟪b i, A x⟫_ℂ‖^2 = (σ i)^2 * ‖⟪b i, x⟫_ℂ‖^2 := fun i => by
    rw [h_coeff i, Complex.norm_mul, Complex.norm_real]
    simp only [Real.norm_eq_abs, abs_of_nonneg (hσ_nonneg i)]
    ring
  have hAx_norm_sq : ‖A x‖^2 = ∑' i, (σ i)^2 * ‖⟪b i, x⟫_ℂ‖^2 := by
    rw [h_parseval_Ax]; exact tsum_congr h_coeff_norm
  have h_bound : ‖A x‖^2 ≤ (∑' j, σ j)^2 * ‖x‖^2 := by
    rw [hAx_norm_sq, h_parseval_x]
    have h_ptwise : ∀ i, (σ i)^2 * ‖⟪b i, x⟫_ℂ‖^2 ≤ (∑' j, σ j)^2 * ‖⟪b i, x⟫_ℂ‖^2 := fun i => by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact sq_le_sq' (by linarith [hσ_nonneg i, h_sum_nonneg]) (h_σ_le_sum i)
    have hs1 : Summable (fun i => (σ i)^2 * ‖⟪b i, x⟫_ℂ‖^2) := by
      have hbs : Summable (fun i => (∑' j, σ j)^2 * ‖⟪b i, x⟫_ℂ‖^2) :=
        (HilbertBasis.summable_norm_sq_inner' b x).mul_left _
      exact hbs.of_nonneg_of_le (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) h_ptwise
    have hs2 : Summable (fun i => (∑' j, σ j)^2 * ‖⟪b i, x⟫_ℂ‖^2) :=
      (HilbertBasis.summable_norm_sq_inner' b x).mul_left _
    calc ∑' i, (σ i)^2 * ‖⟪b i, x⟫_ℂ‖^2
        ≤ ∑' i, (∑' j, σ j)^2 * ‖⟪b i, x⟫_ℂ‖^2 := hasSum_le h_ptwise hs1.hasSum hs2.hasSum
      _ = (∑' j, σ j)^2 * ∑' i, ‖⟪b i, x⟫_ℂ‖^2 := by rw [tsum_mul_left]
  -- From ‖A x‖² ≤ (∑σ)² ‖x‖², take square roots
  by_cases hx : x = 0
  · simp [hx]
  · have hx_norm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    by_contra hc
    push_neg at hc
    have hAx_pos : 0 < ‖A x‖ := lt_of_le_of_lt (by positivity) hc
    have h1 : ‖A x‖^2 > (∑' j, σ j)^2 * ‖x‖^2 := by
      have := sq_lt_sq' (by linarith [mul_nonneg h_sum_nonneg (le_of_lt hx_norm_pos)]) hc
      simp only [mul_pow] at this
      exact this
    linarith

/-- If a Cauchy sequence in trace norm converges in operator norm to T,
then T is trace-class, provided the trace norms are uniformly bounded. -/
lemma isTraceClass_of_tendsto_of_bddAbove {u : ℕ → TraceClass H} {T₀ : H →L[ℂ] H}
    (hconv : Filter.Tendsto (fun n => (u n).toFun) Filter.atTop (nhds T₀))
    (hbdd : BddAbove (Set.range fun n => ‖u n‖)) :
    IsTraceClass T₀ := by
  -- For any basis b, we need to show ∑' i, ⟨b i, |T₀| b i⟩.re is summable.
  -- Get the canonical Hilbert basis
  let ι := Classical.choose (exists_hilbertBasis ℂ H)
  let b : HilbertBasis ι ℂ H := Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ H))
  -- Get the bound M on trace norms
  obtain ⟨M, hM⟩ := hbdd
  have hM' : ∀ n, ‖u n‖ ≤ M := by
    intro n
    exact hM (Set.mem_range_self n)
  -- For any finite s, ∑_{i∈s} ⟨b i, |T₀| b i⟩.re ≤ M
  have h_finite_bound : ∀ s : Finset ι, s.sum (fun i => (⟪b i, absoluteValue T₀ (b i)⟫_ℂ).re) ≤ M := by
    intro s
    have h_finsum_tendsto : Filter.Tendsto
        (fun n => s.sum (fun i => (⟪b i, absoluteValue (u n).toFun (b i)⟫_ℂ).re))
        Filter.atTop (nhds (s.sum (fun i => (⟪b i, absoluteValue T₀ (b i)⟫_ℂ).re))) :=
      finset_sum_inner_absoluteValue_tendsto hconv b s
    have h_sum_le_M : ∀ n, s.sum (fun i => (⟪b i, absoluteValue (u n).toFun (b i)⟫_ℂ).re) ≤ M := by
      intro n
      calc s.sum (fun i => (⟪b i, absoluteValue (u n).toFun (b i)⟫_ℂ).re)
          ≤ traceNorm (u n) := by
            unfold traceNorm
            exact ((u n).isTraceClass ι b).sum_le_tsum s (fun i _ => inner_absoluteValue_re_nonneg' _ _)
        _ = ‖u n‖ := (norm_eq_traceNorm _).symm
        _ ≤ M := hM' n
    exact le_of_tendsto' h_finsum_tendsto h_sum_le_M
  have h_nonneg : ∀ i, 0 ≤ (⟪b i, absoluteValue T₀ (b i)⟫_ℂ).re := fun i => inner_absoluteValue_re_nonneg' _ _
  -- Get summability for the canonical basis
  have h_canonical_summable : Summable (fun i => (⟪b i, absoluteValue T₀ (b i)⟫_ℂ).re) :=
    summable_of_sum_le h_nonneg h_finite_bound
  -- Now prove for ALL bases using ENNReal basis independence
  -- Setup for |T₀| = √(|T₀|) * √(|T₀|)
  let A := absoluteValue T₀
  have hA_pos : 0 ≤ A := absoluteValue_nonneg T₀
  let S := CFC.sqrt A
  have hS_sa : IsSelfAdjoint S := (CFC.sqrt_nonneg A).isSelfAdjoint
  have h_term : ∀ (κ : Type u) (c : HilbertBasis κ ℂ H) (i : κ),
      (⟪c i, A (c i)⟫_ℂ).re = ‖S (c i)‖^2 := by
    intro κ c i
    have hA_sqrt : A = S * S := (CFC.sqrt_mul_sqrt_self A hA_pos).symm
    rw [hA_sqrt, ContinuousLinearMap.mul_apply]
    have h_adj : S.adjoint = S := hS_sa.adjoint_eq
    nth_rw 1 [← h_adj]
    rw [adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    norm_cast
  -- Summability in NNReal for canonical basis
  have h₀' : Summable (fun (i : ι) => ‖S (b i)‖ ^ 2) := by
    have h_eq : (fun (i : ι) => (⟪b i, absoluteValue T₀ (b i)⟫_ℂ).re) = (fun i => ‖S (b i)‖ ^ 2) := by
      ext i
      exact h_term _ b i
    rwa [h_eq] at h_canonical_summable
  have hg₀ : Summable (fun (i : ι) => (⟨‖S (b i)‖ ^ 2, sq_nonneg _⟩ : NNReal)) := by
    rw [← NNReal.summable_coe]
    convert h₀'
  -- Now show IsTraceClass: summability for any basis
  intro ι' b'
  have hg' : Summable (fun (j : ι') => (⟨‖S (b' j)‖ ^ 2, sq_nonneg _⟩ : NNReal)) := by
    let toE : NNReal → ENNReal := fun x => (x : ENNReal)
    let g : ι → NNReal := fun i => ⟨‖S (b i)‖ ^ 2, sq_nonneg _⟩
    let g' : ι' → NNReal := fun j => ⟨‖S (b' j)‖ ^ 2, sq_nonneg _⟩
    have h_eq_tsum : (∑' i, toE (g i)) = (∑' j, toE (g' j)) := by
      let f : ι → ι' → ENNReal := fun i j => ENNReal.ofReal (‖inner (𝕜 := ℂ) (b i) (S (b' j))‖^2)
      have h_lhs : (∑' i, toE (g i)) = ∑' i, ∑' j, f i j := by
        apply tsum_congr
        intro i
        have h_parseval : ‖S (b i)‖^2 = ∑' j, ‖inner (𝕜 := ℂ) (b' j) (S (b i))‖^2 :=
          HilbertBasis.norm_sq_eq_tsum_norm_sq_inner' b' (S (b i))
        have h_summable : Summable (fun j => ‖inner (𝕜 := ℂ) (b' j) (S (b i))‖^2) :=
          HilbertBasis.summable_norm_sq_inner' b' (S (b i))
        have h_inner_eq : ∀ j, ‖inner (𝕜 := ℂ) (b' j) (S (b i))‖^2 = ‖inner (𝕜 := ℂ) (b i) (S (b' j))‖^2 := by
          intro j
          have h1 : inner (𝕜 := ℂ) (b' j) (S (b i)) = inner (𝕜 := ℂ) (S.adjoint (b' j)) (b i) := by
            rw [adjoint_inner_left]
          rw [h1, hS_sa.adjoint_eq]
          have h3 : ‖inner (𝕜 := ℂ) (S (b' j)) (b i)‖ = ‖inner (𝕜 := ℂ) (b i) (S (b' j))‖ := by
            rw [← Complex.norm_conj (inner ℂ (S (b' j)) (b i)), inner_conj_symm]
          rw [h3]
        have h_sum_eq : (∑' j, ‖inner (𝕜 := ℂ) (b' j) (S (b i))‖^2) = (∑' j, ‖inner (𝕜 := ℂ) (b i) (S (b' j))‖^2) :=
          tsum_congr h_inner_eq
        have h_g_eq : toE (g i) = ENNReal.ofReal (‖S (b i)‖^2) := by
          simp only [toE, g]
          rw [ENNReal.coe_nnreal_eq]
          simp only [NNReal.coe_mk]
        have h_summable' : Summable (fun j => ‖inner (𝕜 := ℂ) (b i) (S (b' j))‖^2) := by
          simp_rw [← h_inner_eq]; exact h_summable
        rw [h_g_eq, h_parseval, h_sum_eq]
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => sq_nonneg _) h_summable']
      have h_rhs : (∑' j, toE (g' j)) = ∑' j, ∑' i, f i j := by
        apply tsum_congr
        intro j
        have h_parseval : ‖S (b' j)‖^2 = ∑' i, ‖inner (𝕜 := ℂ) (b i) (S (b' j))‖^2 :=
          HilbertBasis.norm_sq_eq_tsum_norm_sq_inner' b (S (b' j))
        have h_summable : Summable (fun i => ‖inner (𝕜 := ℂ) (b i) (S (b' j))‖^2) :=
          HilbertBasis.summable_norm_sq_inner' b (S (b' j))
        have h_g'_eq : toE (g' j) = ENNReal.ofReal (‖S (b' j)‖^2) := by
          simp only [toE, g']
          rw [ENNReal.coe_nnreal_eq]
          simp only [NNReal.coe_mk]
        rw [h_g'_eq, h_parseval]
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) h_summable]
      rw [h_lhs, h_rhs, ENNReal.tsum_comm]
    have hg₀_ne_top : (∑' i, toE (g i)) ≠ ⊤ := ENNReal.tsum_coe_ne_top_iff_summable.mpr hg₀
    rw [h_eq_tsum] at hg₀_ne_top
    exact ENNReal.tsum_coe_ne_top_iff_summable.mp hg₀_ne_top
  have h_summable' : Summable (fun j => ‖S (b' j)‖ ^ 2) := by
    have h_coe : (fun j => (⟨‖S (b' j)‖ ^ 2, sq_nonneg _⟩ : NNReal).val) = fun j => ‖S (b' j)‖ ^ 2 := rfl
    rw [← h_coe]
    exact NNReal.summable_coe.mpr hg'
  convert h_summable' with j
  exact h_term ι' b' j

/-- The space of trace-class operators is complete with respect to the trace norm.

This is proved by showing that every Cauchy sequence in the trace norm converges:
1. A trace-norm Cauchy sequence is also an operator-norm Cauchy sequence (since ‖T‖_op ≤ ‖T‖₁)
2. The space of bounded operators H →L[ℂ] H is complete, so the sequence converges to some T
3. We show T is trace-class by using the trace-norm boundedness of Cauchy sequences
4. The convergence in trace norm follows from the Cauchy property -/
noncomputable instance : CompleteSpace (TraceClass H) := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  -- Step 1: The Cauchy sequence in trace norm induces a Cauchy sequence in operator norm
  have h_opNorm_cauchy : CauchySeq (fun n => (u n).toFun) := by
    apply Metric.cauchySeq_iff'.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp hu ε hε
    use N
    intro n hn
    calc ‖(u n).toFun - (u N).toFun‖
        = ‖(u n - u N).toFun‖ := by simp [sub_toFun]
      _ ≤ ‖u n - u N‖ := opNorm_le_traceNorm _
      _ = dist (u n) (u N) := rfl
      _ < ε := hN n hn
  -- Step 2: Completeness of H →L[ℂ] H gives us a limit T₀
  obtain ⟨T₀, hT₀⟩ := cauchySeq_tendsto_of_complete h_opNorm_cauchy
  -- Step 3: Show T₀ is trace-class using uniform boundedness
  have h_bdd : BddAbove (Set.range fun n => ‖u n‖) := hu.norm_bddAbove
  have hT₀_tc : IsTraceClass T₀ := isTraceClass_of_tendsto_of_bddAbove hT₀ h_bdd
  -- Step 4: Define the trace-class operator T
  let T : TraceClass H := ⟨T₀, hT₀_tc⟩
  use T
  -- Step 5: Show u n → T in trace norm
  -- The key is that trace norm is lower semicontinuous with respect to operator norm:
  -- ‖T‖₁ ≤ liminf_{n→∞} ‖Tₙ‖₁ when Tₙ → T in operator norm
  -- Combined with the Cauchy property, this gives convergence in trace norm
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu (ε / 2) (half_pos hε)
  use N
  intro n hn
  -- We show ‖u n - T‖ ≤ liminf_{m→∞} ‖u n - u m‖ ≤ ε/2 < ε
  -- Using trace norm lower semicontinuity for u m - u n → T - u n in operator norm
  have h_diff_conv : Filter.Tendsto (fun m => (u m - u n).toFun) Filter.atTop (nhds (T - u n).toFun) := by
    simp only [sub_toFun]
    exact Filter.Tendsto.sub hT₀ tendsto_const_nhds
  -- For m ≥ N, we have dist (u m) (u n) < ε/2, so ‖u m - u n‖ < ε/2
  have h_liminf_bound : Filter.liminf (fun m => (‖u m - u n‖ : ℝ)) Filter.atTop ≤ ε / 2 := by
    apply Filter.liminf_le_of_frequently_le
    · rw [Filter.frequently_atTop]
      intro b
      use max b N
      constructor
      · exact le_max_left b N
      · have hmax : max b N ≥ N := le_max_right b N
        have hdist : dist (u (max b N)) (u n) < ε / 2 := hN (max b N) hmax n hn
        rw [dist_eq_norm] at hdist
        exact le_of_lt hdist
    · exact Filter.isBoundedUnder_of ⟨0, fun _ => norm_nonneg _⟩
  calc dist (u n) T
      = ‖u n - T‖ := rfl
    _ = ‖T - u n‖ := by rw [norm_sub_rev]
    _ = traceNorm (T - u n) := norm_eq_traceNorm _
    _ ≤ Filter.liminf (fun m => traceNorm (u m - u n)) Filter.atTop := by
        apply traceNorm_le_liminf_of_tendsto h_diff_conv
        -- Need: BddAbove {a | ∀ᶠ m, a ≤ traceNorm (u m - u n)}
        -- Since u is Cauchy, the norms are bounded: ‖u m‖ ≤ M for some M
        -- So ‖u m - u n‖ ≤ ‖u m‖ + ‖u n‖ ≤ 2M
        -- Any eventual lower bound a satisfies: eventually a ≤ ‖u m - u n‖ ≤ 2M
        -- So a ≤ 2M for any eventual lower bound a
        obtain ⟨M, hM⟩ := h_bdd
        have hM' : ∀ k, ‖u k‖ ≤ M := fun k => hM (Set.mem_range_self k)
        use ‖u n‖ + M
        intro a ha
        simp only [Set.mem_setOf_eq] at ha
        obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp ha
        specialize hK K (le_refl K)
        calc a ≤ traceNorm (u K - u n) := hK
          _ = ‖u K - u n‖ := (norm_eq_traceNorm _).symm
          _ ≤ ‖u K‖ + ‖u n‖ := norm_sub_le _ _
          _ ≤ M + ‖u n‖ := by linarith [hM' K]
          _ = ‖u n‖ + M := by ring
    _ = Filter.liminf (fun m => (‖u m - u n‖ : ℝ)) Filter.atTop := by
        simp only [norm_eq_traceNorm]
    _ ≤ ε / 2 := h_liminf_bound
    _ < ε := half_lt_self hε

/-- The span of rank-one operators is dense in the space of trace-class operators.

This is a fundamental result in functional analysis. Every trace-class operator T can be
written as T = ∑ᵢ σᵢ |uᵢ⟩⟨vᵢ| where σᵢ are singular values, converging in trace norm.

The proof uses:
1. Singular value decomposition for trace-class operators
2. Convergence of the partial sums in trace norm

## Proof outline

Given T ∈ TraceClass H and ε > 0:
1. Use polar decomposition: T = U|T| where U is a partial isometry
2. Use spectral decomposition: |T| has eigenbasis (bᵢ) with eigenvalues σᵢ ≥ 0
3. The σᵢ are summable (trace-class condition): ∑ σᵢ < ∞
4. Choose finite F such that ∑_{i∉F} σᵢ < ε
5. Define S = ∑_{i∈F} σᵢ • rankOne (U bᵢ) bᵢ ∈ span of rank-ones
6. Then ‖T - S‖₁ = ‖∑_{i∉F} σᵢ • rankOne (U bᵢ) bᵢ‖₁ ≤ ∑_{i∉F} σᵢ < ε

The technical step (6) requires:
- T.toFun = ∑' i, σᵢ • rankOne (U bᵢ) bᵢ converges in trace norm
- Triangle inequality: ‖∑ Aᵢ‖₁ ≤ ∑ ‖Aᵢ‖₁
- ‖σ • rankOne x y‖₁ = |σ| · ‖x‖ · ‖y‖

Note: This proof uses that TraceClass H is complete (proven above). -/
lemma dense_span_rankOne :
    Dense (Submodule.span ℂ {T : TraceClass H | ∃ x y : H, T = ⟨rankOne x y, isTraceClass_rankOne x y⟩} : Set (TraceClass H)) := by
  classical
  rw [Metric.dense_iff]
  intro T ε hε
  rw [Set.inter_nonempty]
  by_cases hT_zero : T = 0
  · -- If T = 0, take 0 which is in the span
    exact ⟨0, by simp [hT_zero, hε], Submodule.zero_mem _⟩
  -- Use the spectral decomposition of |T|
  let A := absoluteValue T.toFun
  have hA_comp : IsCompactOperator A := IsCompactOperator.absoluteValue (IsTraceClass.isCompactOperator T.isTraceClass)
  have hA_sa : IsSelfAdjoint A := absoluteValue_isSelfAdjoint T.toFun
  -- Get the spectral decomposition: eigenbasis with eigenvalues
  obtain ⟨ι, b, σ, hσ_eig, _⟩ := exists_orthonormalBasis_eigenvectors_of_isCompactOperator_isSelfAdjoint hA_comp hA_sa
  have hb_norm : ∀ i, ‖b i‖ = 1 := fun i => b.orthonormal.1 i
  -- σ are the singular values (eigenvalues of |T|, which are non-negative)
  have hσ_nonneg : ∀ i, 0 ≤ σ i := fun i => by
    have h_pos : (⟪b i, A (b i)⟫_ℂ).re ≥ 0 := traceNormSummand_nonneg T.toFun b i
    rw [hσ_eig i] at h_pos
    have h_smul : σ i • b i = (σ i : ℂ) • b i := rfl
    rw [h_smul, inner_smul_right, inner_self_eq_norm_sq_to_K (𝕜 := ℂ), hb_norm i] at h_pos
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, ge_iff_le] at h_pos
    norm_cast at h_pos
    simp only [one_pow] at h_pos
    convert h_pos using 1
    simp
  -- Get the polar decomposition T = U |T|
  obtain ⟨U, hU_pi, hT_polar, _⟩ := exists_polar_decomposition T.toFun
  -- The singular values are summable (trace-class condition)
  have hσ_summable : Summable σ := by
    have h1 : Summable (fun i => (⟪b i, A (b i)⟫_ℂ).re) := T.isTraceClass ι b
    have h2 : ∀ i, (⟪b i, A (b i)⟫_ℂ).re = σ i := fun i => by
      rw [hσ_eig i]
      have h_smul : σ i • b i = (σ i : ℂ) • b i := rfl
      rw [h_smul, inner_smul_right, inner_self_eq_norm_sq_to_K (𝕜 := ℂ), hb_norm i]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      norm_cast
      simp
    exact h1.congr fun i => h2 i
  have hU_norm_le : ∀ x, ‖U x‖ ≤ ‖x‖ := fun x => by
    calc ‖U x‖ ≤ ‖U‖ * ‖x‖ := U.le_opNorm x
      _ ≤ 1 * ‖x‖ := by gcongr; exact IsPartialIsometry.norm_le_one hU_pi
      _ = ‖x‖ := one_mul _
  -- Since ∑ σᵢ converges, for any δ > 0, find finite F such that tail < δ
  have hhs : Filter.Tendsto (fun s : Finset ι => ∑ i ∈ s, σ i)
      Filter.atTop (nhds (∑' i, σ i)) := hσ_summable.hasSum
  rw [Metric.tendsto_atTop] at hhs
  obtain ⟨F, hF⟩ := hhs ε hε
  -- Define the rank-one operators v i = σᵢ |U(bᵢ)⟩⟨bᵢ|
  let v : ι → TraceClass H := fun i => ⟨(σ i : ℂ) • rankOne (U (b i)) (b i),
    smul_isTraceClass (isTraceClass_rankOne _ _) _⟩
  -- The finite sum S = ∑_{i ∈ F} v i
  let S : TraceClass H := ∑ i ∈ F, v i
  -- S is in the span of rank-ones
  have hS_in_span : S ∈ Submodule.span ℂ {T | ∃ x y, T = ⟨rankOne x y, isTraceClass_rankOne x y⟩} := by
    apply Submodule.sum_mem
    intro i _
    have hmem : (⟨rankOne (U (b i)) (b i), isTraceClass_rankOne (U (b i)) (b i)⟩ : TraceClass H) ∈
        {T : TraceClass H | ∃ x y, T = ⟨rankOne x y, isTraceClass_rankOne x y⟩} := ⟨U (b i), b i, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  refine ⟨S, ?_, hS_in_span⟩
  rw [Metric.mem_ball, dist_eq_norm]
  -- Key: show T.toFun x = ∑' i, v i x for all x (pointwise SVD)
  have hT_eq_tsum : ∀ x, T.toFun x = ∑' i, (v i).toFun x := by
    intro x
    -- Use the helper lemma for |T| x = A x
    have hA_eq := positive_compact_eq_tsum_rankOne A b σ hσ_eig x
    -- Need summability of (σ i : ℂ) • ⟪b i, x⟫_ℂ • b i
    have hrepr : ∀ i, b.repr x i = ⟪b i, x⟫_ℂ := fun i => HilbertBasis.repr_apply_apply b x i
    have hbase : Summable (fun i => ⟪b i, x⟫_ℂ • b i) := by
      convert (b.hasSum_repr x).summable using 1
      ext j; rw [hrepr]
    have hsum : Summable (fun i => (σ i : ℂ) • ⟪b i, x⟫_ℂ • b i) := by
      -- ‖σ i • ⟪b i, x⟫ • b i‖ = |σ i| * |⟪b i, x⟫| * ‖b i‖
      --                        = σ i * |⟪b i, x⟫|  (since σ ≥ 0 and ‖b i‖ = 1)
      --                        ≤ σ i * ‖x‖         (Cauchy-Schwarz)
      -- And ∑ σ i * ‖x‖ = ‖x‖ * ∑ σ i converges
      have hg : Summable (fun i => σ i * ‖x‖) := hσ_summable.mul_right ‖x‖
      refine Summable.of_norm_bounded hg ?_
      intro i
      calc ‖(σ i : ℂ) • ⟪b i, x⟫_ℂ • b i‖ = ‖(σ i : ℂ)‖ * ‖⟪b i, x⟫_ℂ • b i‖ := norm_smul _ _
        _ = |σ i| * (‖⟪b i, x⟫_ℂ‖ * ‖b i‖) := by
            rw [Complex.norm_real, norm_smul, Real.norm_eq_abs]
        _ = σ i * ‖⟪b i, x⟫_ℂ‖ := by rw [abs_of_nonneg (hσ_nonneg i), hb_norm i, mul_one]
        _ ≤ σ i * ‖x‖ := by
            apply mul_le_mul_of_nonneg_left _ (hσ_nonneg i)
            calc ‖⟪b i, x⟫_ℂ‖ ≤ ‖b i‖ * ‖x‖ := norm_inner_le_norm _ _
              _ = ‖x‖ := by rw [hb_norm i, one_mul]
    -- T x = U (|T| x) = U (∑' i, σ i • ⟨b i, x⟩ • b i) = ∑' i, σ i • ⟨b i, x⟩ • U (b i)
    calc T.toFun x = U (A x) := by rw [hT_polar]; rfl
      _ = U (∑' i, (σ i : ℂ) • ⟪b i, x⟫_ℂ • b i) := by rw [hA_eq]
      _ = ∑' i, U ((σ i : ℂ) • ⟪b i, x⟫_ℂ • b i) := U.map_tsum hsum
      _ = ∑' i, (σ i : ℂ) • ⟪b i, x⟫_ℂ • U (b i) := by congr 1; ext i; rw [U.map_smul, U.map_smul]
      _ = ∑' i, (v i).toFun x := by
          refine tsum_congr (fun i => ?_)
          simp only [v, smul_apply, rankOne_apply]
  -- Now we need to bound ‖S - T‖ = ‖T - S‖
  -- We bound the trace class norm directly.
  -- Key: ‖T - S‖ = traceNorm (T - S) ≤ ∑_{i∉F} traceNorm (v i) = ∑_{i∉F} σ i
  -- where we use that v i are rank-one operators with traceNorm = σ i * ‖b i‖² = σ i

  -- First, bound ‖v i‖ for each i
  have hv_norm_le : ∀ i, ‖v i‖ ≤ σ i := fun i => by
    simp only [v]
    rw [TraceClass.norm_eq_traceNorm]
    have h1 : (⟨(σ i : ℂ) • rankOne (U (b i)) (b i), _⟩ : TraceClass H) =
              (σ i : ℂ) • ⟨rankOne (U (b i)) (b i), isTraceClass_rankOne _ _⟩ := rfl
    rw [h1, traceNorm_smul, traceNorm_rankOne]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hσ_nonneg i)]
    calc σ i * (‖U (b i)‖ * ‖b i‖)
        ≤ σ i * (‖b i‖ * ‖b i‖) := by
            gcongr
            · exact hσ_nonneg i
            · exact hU_norm_le (b i)
      _ = σ i * 1 := by rw [hb_norm i]; ring
      _ = σ i := by ring
  -- v is summable in TraceClass (since ‖v i‖ ≤ σ i and σ is summable)
  have hv_summable : Summable v := Summable.of_norm_bounded (g := σ) hσ_summable hv_norm_le
  -- T = ∑' v i as elements of TraceClass
  -- The proof uses that T.toFun = ∑' (v i).toFun (from hT_eq_tsum) and (∑' v i).toFun = ∑' (v i).toFun
  have hT_eq_tsum_v : T = ∑' i, v i := by
    -- Use extensionality via the FunLike instance
    apply DFunLike.coe_injective
    ext x
    -- Goal: T x = (∑' i, v i) x
    -- Key observation: For a summable sequence in TraceClass, the tsum commutes with .toFun
    -- This is because the coercion TraceClass H → (H →L[ℂ] H) is a continuous linear map
    -- (continuous because opNorm ≤ traceNorm)
    have h_coe_tsum : (∑' i, v i).toFun = ∑' i, (v i).toFun := by
      -- The coercion is a bounded linear map with norm ≤ 1
      -- Apply ContinuousLinearMap.map_tsum
      let ι_coe : TraceClass H →L[ℂ] (H →L[ℂ] H) :=
        { toFun := fun T => T.toFun
          map_add' := fun _ _ => add_toFun _ _
          map_smul' := fun c T => rfl
          cont := by
            apply LipschitzWith.continuous (K := 1)
            intro S T
            rw [edist_dist, edist_dist, ENNReal.coe_one, one_mul]
            apply ENNReal.ofReal_le_ofReal
            calc dist S.toFun T.toFun = ‖S.toFun - T.toFun‖ := dist_eq_norm _ _
              _ = ‖(S - T).toFun‖ := by rw [sub_toFun]
              _ ≤ ‖S - T‖ := opNorm_le_traceNorm (S - T)
              _ = dist S T := (dist_eq_norm _ _).symm }
      have h := ι_coe.map_tsum hv_summable
      exact h
    -- Now T x = T.toFun x = (∑' v i).toFun x = (∑' (v i).toFun) x = ∑' (v i).toFun x
    simp only at h_coe_tsum ⊢
    -- We need: T x = (∑' v i) x = (∑' v i).toFun x
    -- h_coe_tsum : (∑' v i).toFun = ∑' (v i).toFun
    -- hT_eq_tsum : T.toFun x = ∑' (v i).toFun x
    have hsummable_clm : Summable (fun i => (v i).toFun) := by
      apply Summable.of_norm_bounded (g := σ)
      · exact hσ_summable
      · intro i
        calc ‖(v i).toFun‖ ≤ ‖v i‖ := opNorm_le_traceNorm (v i)
          _ ≤ σ i := hv_norm_le i
    -- Use that evaluation at x is continuous, so tsum commutes with it
    have htsum : (∑' i, (v i).toFun) x = ∑' i, (v i).toFun x := by
      -- The evaluation map (· x) : (H →L[ℂ] H) → H is continuous
      let eval_x : (H →L[ℂ] H) →L[ℂ] H := ContinuousLinearMap.apply ℂ H x
      have := eval_x.map_tsum hsummable_clm
      exact this
    calc T x = T.toFun x := rfl
      _ = ∑' i, (v i).toFun x := hT_eq_tsum x
      _ = (∑' i, (v i).toFun) x := htsum.symm
      _ = (∑' i, v i).toFun x := by rw [← h_coe_tsum]
  -- T - S = ∑' {i | i ∉ F}, v i (tail sum)
  have hTS_eq : T - S = ∑' i : {j // j ∉ F}, v i := by
    rw [hT_eq_tsum_v]
    simp only [S]
    have h := hv_summable.sum_add_tsum_compl (s := F)
    -- h : ∑ i ∈ F, v i + ∑' i : {j // j ∉ F}, v j = ∑' i, v i
    -- Need: ∑' v i - ∑ i ∈ F, v i = ∑' {i | i ∉ F}, v i
    have : ∑' i, v i - ∑ i ∈ F, v i = ∑' i : {j // j ∉ F}, v i := by
      rw [← h]; abel
    exact this
  -- ‖T - S‖ ≤ ∑' {i | i ∉ F}, ‖v i‖ by norm_tsum_le_tsum_norm
  have hTS_bound : ‖T - S‖ ≤ ∑' i : {j // j ∉ F}, ‖v i‖ := by
    rw [hTS_eq]
    -- Need summability of norms. Use that ‖v i‖ ≤ σ i and σ is summable
    have hsub_norm : Summable (fun i : {j // j ∉ F} => ‖v i.val‖) := by
      apply Summable.of_norm_bounded (g := fun i : {j // j ∉ F} => σ i.val)
      · exact hσ_summable.subtype _
      · intro i; simp only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact hv_norm_le i.val
    exact norm_tsum_le_tsum_norm hsub_norm
  -- ∑' {i | i ∉ F}, ‖v i‖ ≤ ∑' {i | i ∉ F}, σ i
  have hsum_bound : ∑' i : {j // j ∉ F}, ‖v i‖ ≤ ∑' i : {j // j ∉ F}, σ i := by
    apply Summable.tsum_le_tsum
    · intro i; exact hv_norm_le i.val
    · -- Need summability of norms. Use that ‖v i‖ ≤ σ i and σ is summable
      apply Summable.of_norm_bounded (g := fun i : {j // j ∉ F} => σ i.val)
      · exact hσ_summable.subtype _
      · intro i; simp only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact hv_norm_le i.val
    · exact hσ_summable.subtype _
  -- ∑' {i | i ∉ F}, σ i < ε (from hF using that the Cauchy sequence has converged)
  have htail_lt : ∑' i : {j // j ∉ F}, σ i < ε := by
    have h1 : ∑' i : {j // j ∉ F}, σ i = ∑' i, σ i - ∑ i ∈ F, σ i := by
      have h := hσ_summable.sum_add_tsum_compl (s := F)
      -- h : ∑ x ∈ F, σ x + ∑' (x : ↑Fᶜ), σ ↑x = ∑' x, σ x
      -- Note: ↑Fᶜ is the same as {j // j ∉ F}
      have heq : ∑' (x : ↑(↑F : Set ι)ᶜ), σ ↑x = ∑' (i : { j // j ∉ F }), σ ↑i := rfl
      rw [heq] at h
      linarith
    rw [h1]
    have hF_self := hF F (le_refl F)
    rw [Real.dist_eq] at hF_self
    have hsum_le : ∑ i ∈ F, σ i ≤ ∑' i, σ i := by
      -- We know ∑ F σ + ∑' compl σ = ∑' σ from sum_add_tsum_compl
      -- And ∑' compl σ ≥ 0 since all σ ≥ 0
      have h_decomp := hσ_summable.sum_add_tsum_compl (s := F)
      have htail_nonneg : ∑' (x : ↑(↑F : Set ι)ᶜ), σ ↑x ≥ 0 := by
        apply tsum_nonneg
        intro i
        exact hσ_nonneg i.val
      linarith
    have h2 : ∑' i, σ i - ∑ i ∈ F, σ i ≥ 0 := by linarith
    have h3 : |∑ i ∈ F, σ i - ∑' i, σ i| = ∑' i, σ i - ∑ i ∈ F, σ i := by
      rw [abs_sub_comm]
      exact abs_of_nonneg h2
    rw [h3] at hF_self
    exact hF_self
  -- Combine the bounds
  calc ‖S - T‖ = ‖T - S‖ := by rw [norm_sub_rev]
    _ ≤ ∑' i : {j // j ∉ F}, ‖v i‖ := hTS_bound
    _ ≤ ∑' i : {j // j ∉ F}, σ i := hsum_bound
    _ < ε := htail_lt

end Basic

section RankOne

/-- Helper: given y, the map `x ↦ ⟨rankOne x y, isTraceClass_rankOne x y⟩` is continuous linear.
    This is linear in x since rankOne is linear in first argument. -/
noncomputable def rankOneLeft (y : H) : H →L[ℂ] TraceClass H :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨rankOne x y, isTraceClass_rankOne x y⟩
      map_add' := fun x₁ x₂ => by ext1; simp only [add_toFun, rankOne_add_left]
      map_smul' := fun c x => by ext1; simp only [RingHom.id_apply, smul_toFun, rankOne_smul_left] }
    ‖y‖
    (fun x => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, TraceClass.norm_eq_traceNorm, traceNorm_rankOne]
      exact mul_comm ‖x‖ ‖y‖ ▸ le_refl _)

lemma rankOneLeft_apply (y x : H) :
    rankOneLeft y x = ⟨rankOne x y, isTraceClass_rankOne x y⟩ := by
  simp only [rankOneLeft, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]

end RankOne

section TraceCyclicity

open scoped InnerProduct

/-- The trace of T† equals the complex conjugate of the trace of T. -/
lemma trace_adjoint_eq_conj (T : TraceClass H) :
    trace ⟨T.toFun.adjoint, adjoint_isTraceClass T.isTraceClass⟩ =
      starRingEnd ℂ (trace T) := by
  simp only [trace, starRingEnd_apply]
  rw [tsum_star]
  congr 1; ext i
  let b := Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ H))
  -- Goal: ⟨b i, T†(b i)⟩ = star ⟨b i, T(b i)⟩
  -- ⟨b i, T†(b i)⟩ = starRingEnd ℂ ⟨T†(b i), b i⟩ = starRingEnd ℂ ⟨b i, T(b i)⟩
  have h1 : @inner ℂ H _ (b i) (T.toFun.adjoint (b i)) =
      starRingEnd ℂ (@inner ℂ H _ (T.toFun.adjoint (b i)) (b i)) :=
    (inner_conj_symm _ _).symm
  have h2 : @inner ℂ H _ (T.toFun.adjoint (b i)) (b i) =
      @inner ℂ H _ (b i) (T.toFun (b i)) :=
    ContinuousLinearMap.adjoint_inner_left T.toFun (b i) (b i)
  rw [h1, h2]; rfl

/-- Key identity: `trace(T * A) = conj(trace(A† * T†))`. -/
lemma trace_mulRight_eq_conj_trace_mulLeft_adjoint
    (T : TraceClass H) (A : H →L[ℂ] H) :
    trace (mulRight T A) =
      starRingEnd ℂ (trace (mulLeft A.adjoint
        ⟨T.toFun.adjoint, adjoint_isTraceClass T.isTraceClass⟩)) := by
  simp only [trace, mulRight, mulLeft, starRingEnd_apply]
  rw [tsum_star]
  congr 1; ext i
  let b := Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ H))
  simp only [ContinuousLinearMap.mul_apply]
  -- Goal: ⟨b i, T(A(b i))⟩ = star ⟨b i, A†(T†(b i))⟩
  -- Use: ⟨u, v⟩ = star ⟨v, u⟩ (inner_conj_symm)
  -- and: ⟨A†y, x⟩ = ⟨y, Ax⟩ (adjoint_inner_left)
  have h1 : @inner ℂ H _ (b i) (T.toFun (A (b i))) =
      @inner ℂ H _ (T.toFun.adjoint (b i)) (A (b i)) :=
    (ContinuousLinearMap.adjoint_inner_left T.toFun (A (b i)) (b i)).symm
  have h2 : @inner ℂ H _ (T.toFun.adjoint (b i)) (A (b i)) =
      @inner ℂ H _ (A.adjoint (T.toFun.adjoint (b i))) (b i) :=
    (ContinuousLinearMap.adjoint_inner_left A (b i) (T.toFun.adjoint (b i))).symm
  have h3 : @inner ℂ H _ (A.adjoint (T.toFun.adjoint (b i))) (b i) =
      star (@inner ℂ H _ (b i) (A.adjoint (T.toFun.adjoint (b i)))) := by
    change _ = starRingEnd ℂ _
    exact (inner_conj_symm _ _).symm
  rw [h1, h2, h3]

/-- The trace norm of the adjoint equals the trace norm. -/
lemma traceNorm_adjoint (T : TraceClass H) :
    traceNorm ⟨T.toFun.adjoint, adjoint_isTraceClass T.isTraceClass⟩ =
      traceNorm T := by
  unfold traceNorm
  let b := Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ H))
  have h_nonneg_adj : ∀ i, 0 ≤ (⟪b i, absoluteValue T.toFun.adjoint (b i)⟫_ℂ).re :=
    traceNormSummand_nonneg T.toFun.adjoint b
  have h_nonneg_T : ∀ i, 0 ≤ (⟪b i, absoluteValue T.toFun (b i)⟫_ℂ).re :=
    traceNormSummand_nonneg T.toFun b
  have h_summable_adj := adjoint_isTraceClass T.isTraceClass _ b
  have h_summable_T := T.isTraceClass _ b
  have h_ennreal_eq : (∑' i, ENNReal.ofReal (⟪b i, absoluteValue T.toFun.adjoint (b i)⟫_ℂ).re) =
      (∑' i, ENNReal.ofReal (⟪b i, absoluteValue T.toFun (b i)⟫_ℂ).re) := by
    exact (tsum_inner_absoluteValue_eq_adjoint_ennreal (T := T.toFun) b).symm
  have h_ne_top_adj : (∑' i, ENNReal.ofReal (⟪b i, absoluteValue T.toFun.adjoint (b i)⟫_ℂ).re) ≠ ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg h_nonneg_adj h_summable_adj]
    exact ENNReal.ofReal_ne_top
  have h_ne_top_T : (∑' i, ENNReal.ofReal (⟪b i, absoluteValue T.toFun (b i)⟫_ℂ).re) ≠ ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg h_nonneg_T h_summable_T]
    exact ENNReal.ofReal_ne_top
  have h_toReal_adj :
      (∑' i, ENNReal.ofReal (⟪b i, absoluteValue T.toFun.adjoint (b i)⟫_ℂ).re).toReal =
      ∑' i, (⟪b i, absoluteValue T.toFun.adjoint (b i)⟫_ℂ).re := by
    rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
    exact tsum_congr (fun i => ENNReal.toReal_ofReal (h_nonneg_adj i))
  have h_toReal_T :
      (∑' i, ENNReal.ofReal (⟪b i, absoluteValue T.toFun (b i)⟫_ℂ).re).toReal =
      ∑' i, (⟪b i, absoluteValue T.toFun (b i)⟫_ℂ).re := by
    rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
    exact tsum_congr (fun i => ENNReal.toReal_ofReal (h_nonneg_T i))
  rw [← h_toReal_adj, ← h_toReal_T, h_ennreal_eq]

/-- Trace norm bound for right multiplication: `‖Tr(TA)‖ ≤ ‖A‖ · ‖T‖₁`. -/
lemma abs_trace_mulRight_le (T : TraceClass H) (A : H →L[ℂ] H) :
    ‖trace (mulRight T A)‖ ≤ ‖A‖ * traceNorm T := by
  rw [trace_mulRight_eq_conj_trace_mulLeft_adjoint]
  rw [Complex.norm_conj]
  calc ‖trace (mulLeft A.adjoint
        ⟨T.toFun.adjoint, adjoint_isTraceClass T.isTraceClass⟩)‖
      ≤ ‖A.adjoint‖ * traceNorm ⟨T.toFun.adjoint,
          adjoint_isTraceClass T.isTraceClass⟩ := abs_trace_mul_le _ _
    _ = ‖A‖ * traceNorm ⟨T.toFun.adjoint,
          adjoint_isTraceClass T.isTraceClass⟩ := by
        rw [ContinuousLinearMap.adjoint.norm_map]
    _ = ‖A‖ * traceNorm T := by
        rw [traceNorm_adjoint]

end TraceCyclicity

end TraceClass

end ContinuousLinearMap
