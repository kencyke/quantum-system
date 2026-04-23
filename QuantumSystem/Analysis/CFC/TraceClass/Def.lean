module

public import QuantumSystem.Analysis.CFC.PolarDecomposition
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.l2Space

/-!
# Trace-class operators: Definitions

This file defines the basic structures for trace-class operators on a complex Hilbert space.

## Main definitions

* `IsTraceClass`: A predicate asserting that a bounded linear operator is trace-class.
* `TraceClass`: The subtype of trace-class operators on a Hilbert space.

## Mathematical background

An operator `T : H →L[ℂ] H` is trace-class if for any orthonormal basis `(eᵢ)`,
the sum `∑ᵢ ⟨eᵢ, |T| eᵢ⟩` converges, where `|T| = √(T†T)` is the absolute value of `T`.

## References

* Reed, Simon. *Methods of Modern Mathematical Physics I: Functional Analysis*.
* Takesaki. *Theory of Operator Algebras I*.
-/

@[expose] public section


namespace ContinuousLinearMap

open scoped InnerProductSpace
open Complex

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}

section TraceClass

/-- An operator `T : H →L[ℂ] H` is trace-class if for any Hilbert basis `b`,
the sum `∑ᵢ ⟨b i, |T| (b i)⟩` converges.

More precisely, we require the real parts of these inner products to be summable.
Since `|T|` is positive, the inner products `⟨e, |T| e⟩` are non-negative real,
so summability of the real parts is equivalent to summability of the modulus. -/
def IsTraceClass (T : H →L[ℂ] H) : Prop :=
  ∀ (ι : Type u) (b : HilbertBasis ι ℂ H),
    Summable (fun i => (⟪b i, absoluteValue T (b i)⟫_ℂ).re)

/-- The structure of trace-class operators on a Hilbert space `H`.
This wraps the subtype to avoid diamond issues with topological instances. -/
structure TraceClass (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  toFun : H →L[ℂ] H
  isTraceClass : IsTraceClass toFun

instance : Coe (TraceClass H) (H →L[ℂ] H) := ⟨TraceClass.toFun⟩
instance : FunLike (TraceClass H) H H := ⟨fun T => T.toFun, fun T1 T2 h => by
  cases T1
  cases T2
  congr
  exact DFunLike.coe_injective h⟩

instance : ContinuousLinearMapClass (TraceClass H) ℂ H H :=
  { map_add := fun T x y => T.toFun.map_add x y,
    map_smulₛₗ := fun T c x => T.toFun.map_smulₛₗ c x,
    map_continuous := fun T => T.toFun.continuous }

/-- The zero operator is trace-class. -/
lemma zero_isTraceClass : IsTraceClass (0 : H →L[ℂ] H) := by
  intro ι b
  simp only [absoluteValue_zero, zero_apply, inner_zero_right, Complex.zero_re, summable_zero]

/-- Scalar multiplication preserves trace-class. -/
lemma smul_isTraceClass {T : H →L[ℂ] H} (hT : IsTraceClass T) (c : ℂ) :
    IsTraceClass (c • T) := by
  intro ι b
  rw [absoluteValue_smul]
  have : ∀ i, (⟪b i, (‖c‖ • absoluteValue T) (b i)⟫_ℂ).re = ‖c‖ * (⟪b i, absoluteValue T (b i)⟫_ℂ).re := by
    intro i
    rw [ContinuousLinearMap.smul_apply]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right]
    exact Complex.re_ofReal_mul ‖c‖ _
  simp_rw [this]
  exact Summable.mul_left _ (hT ι b)

/-- Negation preserves trace-class. -/
lemma neg_isTraceClass {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    IsTraceClass (-T) := by
  have : -T = (-1 : ℂ) • T := by simp
  rw [this]
  exact smul_isTraceClass hT (-1)



/-- The sum defining the trace norm over a given basis. -/
noncomputable def traceNormSummand (T : H →L[ℂ] H) (b : HilbertBasis ι ℂ H) (i : ι) : ℝ :=
  (⟪b i, absoluteValue T (b i)⟫_ℂ).re

/-- For a trace-class operator, the trace norm sum is non-negative. -/
lemma traceNormSummand_nonneg (T : H →L[ℂ] H) (b : HilbertBasis ι ℂ H) (i : ι) :
    0 ≤ traceNormSummand T b i := by
  unfold traceNormSummand
  -- Since |T| is positive, ⟨e, |T| e⟩ ≥ 0 for all e
  have hpos := absoluteValue_isPositive T
  -- For positive T: re ⟨T x, x⟩ ≥ 0
  have h := hpos.re_inner_nonneg_left (b i)
  -- re ⟨T x, x⟩ = re (conj ⟨x, T x⟩) = re ⟨x, T x⟩ (since re(conj z) = re z)
  have eq1 : (⟪absoluteValue T (b i), b i⟫_ℂ).re = (⟪b i, absoluteValue T (b i)⟫_ℂ).re := by
    rw [← inner_conj_symm]
    simp only [Complex.conj_re]
  -- RCLike.re and Complex.re are definitionally equal for ℂ
  simp only [RCLike.re_to_complex] at h
  linarith

/-- For a positive operator, the trace class condition simplifies:
    we can use `T` directly instead of `|T|`. -/
lemma isTraceClass_of_nonneg {T : H →L[ℂ] H} (hT : 0 ≤ T) :
    IsTraceClass T ↔
      ∀ (ι : Type u) (b : HilbertBasis ι ℂ H),
        Summable (fun i => (⟪b i, T (b i)⟫_ℂ).re) := by
  -- For positive T, we have |T| = T
  have h_abs : absoluteValue T = T := absoluteValue_of_nonneg hT
  simp only [IsTraceClass, h_abs]

/-! ### Hölder-type bounds for trace-class operators

These lemmas establish bounds of the form `∑ᵢ |⟨bᵢ, A T bᵢ⟩| ≤ ‖A‖ · Tr(|T|)`.
-/

/-- For a nonneg self-adjoint P = √Q, we have ⟨x, Q x⟩.re = ‖P x‖². -/
private lemma inner_nonneg_eq_norm_sq_sqrt {Q : H →L[ℂ] H} (hQ_pos : 0 ≤ Q) (x : H) :
    (⟪x, Q x⟫_ℂ).re = ‖CFC.sqrt Q x‖^2 := by
  let P := CFC.sqrt Q
  have hP_sq : P * P = Q := CFC.sqrt_mul_sqrt_self Q hQ_pos
  have hP_sa : IsSelfAdjoint P := (CFC.sqrt_nonneg Q).isSelfAdjoint
  have hPP : ⟪x, P (P x)⟫_ℂ = ⟪P x, P x⟫_ℂ := by
    calc ⟪x, P (P x)⟫_ℂ
        = ⟪P.adjoint x, P x⟫_ℂ := (adjoint_inner_left P (P x) x).symm
      _ = ⟪P x, P x⟫_ℂ := by rw [hP_sa.adjoint_eq]
  calc (⟪x, Q x⟫_ℂ).re
      = (⟪x, (P * P) x⟫_ℂ).re := by rw [hP_sq]
    _ = (⟪x, P (P x)⟫_ℂ).re := rfl
    _ = (⟪P x, P x⟫_ℂ).re := by rw [hPP]
    _ = ‖P x‖^2 := by rw [inner_self_eq_norm_sq_to_K]; norm_cast

/-- ENNReal bound: ∑ᵢ‖P(B†bᵢ)‖² ≤ ‖B‖² · ∑ⱼ‖P bⱼ‖² via Fubini for Parseval identity. -/
private lemma ennreal_bound_sqrt_conjugate {Q : H →L[ℂ] H} (_hQ_pos : 0 ≤ Q)
    (B : H →L[ℂ] H) (ι : Type u) (b : HilbertBasis ι ℂ H) :
    (∑' i, ENNReal.ofReal (‖CFC.sqrt Q (B.adjoint (b i))‖^2)) ≤
      ENNReal.ofReal (‖B‖^2) * ∑' j, ENNReal.ofReal (‖CFC.sqrt Q (b j)‖^2) := by
  let P := CFC.sqrt Q
  have hP_sa : IsSelfAdjoint P := (CFC.sqrt_nonneg Q).isSelfAdjoint
  let f : ι → ι → ENNReal := fun i j => ENNReal.ofReal (‖⟪b j, P (B.adjoint (b i))⟫_ℂ‖^2)
  have h_inner_eq : ∀ i j, ⟪b j, P (B.adjoint (b i))⟫_ℂ = ⟪B (P (b j)), b i⟫_ℂ := by
    intro i j
    calc ⟪b j, P (B.adjoint (b i))⟫_ℂ
        = ⟪P.adjoint (b j), B.adjoint (b i)⟫_ℂ := by rw [adjoint_inner_left]
      _ = ⟪P (b j), B.adjoint (b i)⟫_ℂ := by rw [hP_sa.adjoint_eq]
      _ = ⟪B (P (b j)), b i⟫_ℂ := by rw [adjoint_inner_right]
  have h_f_swap : ∀ i j, f i j = ENNReal.ofReal (‖⟪b i, B (P (b j))⟫_ℂ‖^2) := by
    intro i j; simp only [f]
    congr 1; congr 1
    rw [h_inner_eq, ← Complex.norm_conj, inner_conj_symm]
  have h_summable_inner_sq : ∀ i, Summable (fun j => ‖⟪b j, P (B.adjoint (b i))⟫_ℂ‖^2) :=
    fun i => HilbertBasis.summable_norm_sq_inner' b _
  have h_lhs_ennreal : (∑' i, ENNReal.ofReal (‖P (B.adjoint (b i))‖^2)) = ∑' i, ∑' j, f i j := by
    apply tsum_congr; intro i
    have h_parseval : ‖P (B.adjoint (b i))‖^2 = ∑' j, ‖⟪b j, P (B.adjoint (b i))⟫_ℂ‖^2 :=
      HilbertBasis.norm_sq_eq_tsum_norm_sq_inner' b _
    rw [h_parseval, ← ENNReal.ofReal_tsum_of_nonneg (fun j => sq_nonneg _) (h_summable_inner_sq i)]
  have h_rhs_ennreal : ∑' j, ∑' i, f i j = ∑' j, ENNReal.ofReal (‖B (P (b j))‖^2) := by
    apply tsum_congr; intro j
    have h_parseval : ‖B (P (b j))‖^2 = ∑' i, ‖⟪b i, B (P (b j))⟫_ℂ‖^2 :=
      HilbertBasis.norm_sq_eq_tsum_norm_sq_inner' b _
    have h_summable : Summable (fun i => ‖⟪b i, B (P (b j))⟫_ℂ‖^2) :=
      HilbertBasis.summable_norm_sq_inner' b _
    have h_eq_tsum : ∑' i, f i j = ∑' i, ENNReal.ofReal (‖⟪b i, B (P (b j))⟫_ℂ‖^2) := by
      apply tsum_congr; intro i; exact h_f_swap i j
    rw [h_eq_tsum, ← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) h_summable, h_parseval]
  have h_bound_BP : ∀ j, ‖B (P (b j))‖^2 ≤ ‖B‖^2 * ‖P (b j)‖^2 := by
    intro j
    have h1 : ‖B (P (b j))‖ ≤ ‖B‖ * ‖P (b j)‖ := B.le_opNorm _
    calc ‖B (P (b j))‖^2 = ‖B (P (b j))‖ * ‖B (P (b j))‖ := sq _
      _ ≤ (‖B‖ * ‖P (b j)‖) * (‖B‖ * ‖P (b j)‖) := by
          apply mul_le_mul h1 h1 (norm_nonneg _) (by positivity)
      _ = ‖B‖^2 * ‖P (b j)‖^2 := by ring
  calc ∑' i, ENNReal.ofReal (‖P (B.adjoint (b i))‖^2)
      = ∑' i, ∑' j, f i j := h_lhs_ennreal
    _ = ∑' j, ∑' i, f i j := ENNReal.tsum_comm
    _ = ∑' j, ENNReal.ofReal (‖B (P (b j))‖^2) := h_rhs_ennreal
    _ ≤ ∑' j, ENNReal.ofReal (‖B‖^2 * ‖P (b j)‖^2) := by
        apply ENNReal.tsum_le_tsum
        intro j; apply ENNReal.ofReal_le_ofReal; exact h_bound_BP j
    _ = ∑' j, (ENNReal.ofReal (‖B‖^2) * ENNReal.ofReal (‖P (b j)‖^2)) := by
        apply tsum_congr; intro j; rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    _ = ENNReal.ofReal (‖B‖^2) * ∑' j, ENNReal.ofReal (‖P (b j)‖^2) := ENNReal.tsum_mul_left

/-- Finiteness of the ENNReal sum for conjugate bound. -/
private lemma ennreal_finite_sqrt_conjugate {Q : H →L[ℂ] H} (hQ_pos : 0 ≤ Q)
    (hQ_tc : IsTraceClass Q) (B : H →L[ℂ] H) (ι : Type u) (b : HilbertBasis ι ℂ H) :
    (∑' i, ENNReal.ofReal (‖CFC.sqrt Q (B.adjoint (b i))‖^2)) < ⊤ := by
  let P := CFC.sqrt Q
  have hP_sq : P * P = Q := CFC.sqrt_mul_sqrt_self Q hQ_pos
  have hQ_tc_basis : Summable (fun i => (⟪b i, Q (b i)⟫_ℂ).re) :=
    (isTraceClass_of_nonneg hQ_pos).mp hQ_tc ι b
  have h_P_sq_trace : ∀ j, ‖P (b j)‖^2 = (⟪b j, Q (b j)⟫_ℂ).re := fun j =>
    (inner_nonneg_eq_norm_sq_sqrt hQ_pos (b j)).symm
  have h_summable_P : Summable (fun j => ‖P (b j)‖^2) := by
    have h1 : (fun j => ‖P (b j)‖^2) = (fun j => (⟪b j, Q (b j)⟫_ℂ).re) := funext h_P_sq_trace
    rw [h1]; exact hQ_tc_basis
  calc ∑' i, ENNReal.ofReal (‖P (B.adjoint (b i))‖^2)
      ≤ ENNReal.ofReal (‖B‖^2) * ∑' j, ENNReal.ofReal (‖P (b j)‖^2) :=
        ennreal_bound_sqrt_conjugate hQ_pos B ι b
    _ < ⊤ := by
      apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => sq_nonneg _) h_summable_P]
      exact ENNReal.ofReal_lt_top

/-- Summability of ‖P(B†bᵢ)‖² from finiteness of ENNReal sum. -/
private lemma summable_norm_sq_sqrt_conjugate {Q : H →L[ℂ] H} (hQ_pos : 0 ≤ Q)
    (hQ_tc : IsTraceClass Q) (B : H →L[ℂ] H) (ι : Type u) (b : HilbertBasis ι ℂ H) :
    Summable (fun i => ‖CFC.sqrt Q (B.adjoint (b i))‖^2) := by
  let P := CFC.sqrt Q
  have h_finite := ennreal_finite_sqrt_conjugate hQ_pos hQ_tc B ι b
  have h_nonneg : ∀ i, 0 ≤ ‖P (B.adjoint (b i))‖^2 := fun i => sq_nonneg _
  let g : ι → NNReal := fun i => ⟨‖P (B.adjoint (b i))‖^2, h_nonneg i⟩
  have h_eq : (fun i => (g i : ℝ)) = (fun i => ‖P (B.adjoint (b i))‖^2) := rfl
  rw [← h_eq]
  apply NNReal.summable_coe.mpr
  rw [← ENNReal.tsum_coe_ne_top_iff_summable]
  convert h_finite.ne using 1
  apply tsum_congr; intro i
  simp only [g, ENNReal.coe_nnreal_eq]
  rfl

/-- Real bound from ENNReal bound for conjugate. -/
private lemma real_bound_sqrt_conjugate {Q : H →L[ℂ] H} (hQ_pos : 0 ≤ Q)
    (hQ_tc : IsTraceClass Q) (B : H →L[ℂ] H) (ι : Type u) (b : HilbertBasis ι ℂ H) :
    ∑' i, ‖CFC.sqrt Q (B.adjoint (b i))‖^2 ≤ ‖B‖^2 * ∑' j, ‖CFC.sqrt Q (b j)‖^2 := by
  let P := CFC.sqrt Q
  have hP_sq : P * P = Q := CFC.sqrt_mul_sqrt_self Q hQ_pos
  have hQ_tc_basis : Summable (fun i => (⟪b i, Q (b i)⟫_ℂ).re) :=
    (isTraceClass_of_nonneg hQ_pos).mp hQ_tc ι b
  have h_P_sq_trace : ∀ j, ‖P (b j)‖^2 = (⟪b j, Q (b j)⟫_ℂ).re := fun j =>
    (inner_nonneg_eq_norm_sq_sqrt hQ_pos (b j)).symm
  have h_summable_P : Summable (fun j => ‖P (b j)‖^2) := by
    have h1 : (fun j => ‖P (b j)‖^2) = (fun j => (⟪b j, Q (b j)⟫_ℂ).re) := funext h_P_sq_trace
    rw [h1]; exact hQ_tc_basis
  have h_nonneg_lhs : ∀ i, 0 ≤ ‖P (B.adjoint (b i))‖^2 := fun i => sq_nonneg _
  have h_nonneg_rhs : ∀ j, 0 ≤ ‖P (b j)‖^2 := fun j => sq_nonneg _
  have h_finite := ennreal_finite_sqrt_conjugate hQ_pos hQ_tc B ι b
  have h_ennreal_bound := ennreal_bound_sqrt_conjugate hQ_pos B ι b
  have h_ne_top_lhs : (∑' i, ENNReal.ofReal (‖P (B.adjoint (b i))‖^2)) ≠ ⊤ := h_finite.ne
  have h_ne_top_rhs : ENNReal.ofReal (‖B‖^2) * ∑' j, ENNReal.ofReal (‖P (b j)‖^2) ≠ ⊤ := by
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    rw [← ENNReal.ofReal_tsum_of_nonneg h_nonneg_rhs h_summable_P]
    exact ENNReal.ofReal_ne_top
  have h_lhs_eq : (∑' i, ENNReal.ofReal (‖P (B.adjoint (b i))‖^2)).toReal =
      ∑' i, ‖P (B.adjoint (b i))‖^2 := by
    rw [ENNReal.tsum_toReal_eq (fun i => ENNReal.ofReal_ne_top)]
    apply tsum_congr; intro i; exact ENNReal.toReal_ofReal (h_nonneg_lhs i)
  have h_rhs_eq : (ENNReal.ofReal (‖B‖^2) * ∑' j, ENNReal.ofReal (‖P (b j)‖^2)).toReal =
      ‖B‖^2 * ∑' j, ‖P (b j)‖^2 := by
    rw [ENNReal.toReal_mul]
    rw [ENNReal.toReal_ofReal (sq_nonneg _)]
    congr 1
    rw [ENNReal.tsum_toReal_eq (fun j => ENNReal.ofReal_ne_top)]
    apply tsum_congr; intro j; exact ENNReal.toReal_ofReal (h_nonneg_rhs j)
  calc ∑' i, ‖P (B.adjoint (b i))‖^2
      = (∑' i, ENNReal.ofReal (‖P (B.adjoint (b i))‖^2)).toReal := h_lhs_eq.symm
    _ ≤ (ENNReal.ofReal (‖B‖^2) * ∑' j, ENNReal.ofReal (‖P (b j)‖^2)).toReal :=
        (ENNReal.toReal_le_toReal h_ne_top_lhs h_ne_top_rhs).mpr h_ennreal_bound
    _ = ‖B‖^2 * ∑' j, ‖P (b j)‖^2 := h_rhs_eq

/-- For positive trace-class Q and bounded B, the conjugate B Q B† has trace bounded by ‖B‖² Tr(Q).
    This is proven via the Parseval identity and operator norm bound. -/
theorem tsum_inner_conjugate_le_of_nonneg {Q : H →L[ℂ] H} (hQ_pos : 0 ≤ Q)
    (hQ_tc : IsTraceClass Q) (B : H →L[ℂ] H) (ι : Type u) (b : HilbertBasis ι ℂ H) :
    Summable (fun i => (⟪B.adjoint (b i), Q (B.adjoint (b i))⟫_ℂ).re) ∧
    ∑' i, (⟪B.adjoint (b i), Q (B.adjoint (b i))⟫_ℂ).re ≤
      ‖B‖^2 * ∑' i, (⟪b i, Q (b i)⟫_ℂ).re := by
  let P := CFC.sqrt Q
  have hP_sq : P * P = Q := CFC.sqrt_mul_sqrt_self Q hQ_pos
  have hQ_tc_basis : Summable (fun i => (⟪b i, Q (b i)⟫_ℂ).re) :=
    (isTraceClass_of_nonneg hQ_pos).mp hQ_tc ι b
  have h_eq_norm_sq : ∀ i, (⟪B.adjoint (b i), Q (B.adjoint (b i))⟫_ℂ).re =
      ‖P (B.adjoint (b i))‖^2 := fun i => inner_nonneg_eq_norm_sq_sqrt hQ_pos (B.adjoint (b i))
  have h_P_sq_trace : ∀ j, ‖P (b j)‖^2 = (⟪b j, Q (b j)⟫_ℂ).re := fun j =>
    (inner_nonneg_eq_norm_sq_sqrt hQ_pos (b j)).symm
  simp_rw [h_eq_norm_sq]
  constructor
  · exact summable_norm_sq_sqrt_conjugate hQ_pos hQ_tc B ι b
  · have h_real_bound := real_bound_sqrt_conjugate hQ_pos hQ_tc B ι b
    have h_P_sq_trace' : ∀ j, (⟪b j, Q (b j)⟫_ℂ).re = ‖P (b j)‖^2 := fun j => (h_P_sq_trace j).symm
    calc ∑' i, ‖P (B.adjoint (b i))‖^2
        ≤ ‖B‖^2 * ∑' j, ‖P (b j)‖^2 := h_real_bound
      _ = ‖B‖^2 * ∑' j, (⟪b j, Q (b j)⟫_ℂ).re := by rw [tsum_congr h_P_sq_trace']

/-- For trace-class T, the absolute value |T| is also trace-class. -/
lemma isTraceClass_absoluteValue_of_isTraceClass {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    IsTraceClass (absoluteValue T) := by
  let Q := absoluteValue T
  have hQ_pos : 0 ≤ Q := absoluteValue_nonneg T
  rw [isTraceClass_of_nonneg hQ_pos]
  intro ι' b'
  have h_abs : absoluteValue Q = Q := absoluteValue_of_nonneg hQ_pos
  exact hT ι' b'

/-- Inner product formula: ⟨bᵢ, AT bᵢ⟩ = ⟨P(AV)†bᵢ, Pbᵢ⟩ where T = V|T| and P = √|T|. -/
private lemma inner_AT_eq_inner_sqrt {T : H →L[ℂ] H} {A V : H →L[ℂ] H}
    (h_polar : T = V * absoluteValue T) (i : H) :
    let Q := absoluteValue T
    let P := CFC.sqrt Q
    have hQ_pos : 0 ≤ Q := absoluteValue_nonneg T
    have _hP_sq : P * P = Q := CFC.sqrt_mul_sqrt_self Q hQ_pos
    have _hP_sa : IsSelfAdjoint P := (CFC.sqrt_nonneg Q).isSelfAdjoint
    ⟪i, (A * T) i⟫_ℂ = ⟪P ((A * V).adjoint i), P i⟫_ℂ := by
  intro Q P hQ_pos hP_sq hP_sa
  have h_AT_eq : A * T = A * V * P * P := by
    rw [h_polar]
    simp only [mul_assoc]
    change A * (V * Q) = A * (V * (P * P))
    rw [hP_sq]
  rw [h_AT_eq]
  have h_mul_apply : ((A * V) * P * P) i = (A * V) (P (P i)) := rfl
  calc ⟪i, ((A * V) * P * P) i⟫_ℂ
      = ⟪i, (A * V) (P (P i))⟫_ℂ := by rw [h_mul_apply]
    _ = ⟪(A * V).adjoint i, P (P i)⟫_ℂ :=
        (adjoint_inner_left (A * V) (P (P i)) i).symm
    _ = ⟪P.adjoint ((A * V).adjoint i), P i⟫_ℂ :=
        (adjoint_inner_left P (P i) ((A * V).adjoint i)).symm
    _ = ⟪P ((A * V).adjoint i), P i⟫_ℂ := by rw [hP_sa.adjoint_eq]

/-- Norm of ‖P x‖² equals ⟨x, Q x⟩.re where P = √Q. -/
private lemma norm_sq_sqrt_eq_inner {Q : H →L[ℂ] H} (hQ_pos : 0 ≤ Q) (x : H) :
    let P := CFC.sqrt Q
    ‖P x‖^2 = (⟪x, Q x⟫_ℂ).re := by
  intro P
  have hP_sq : P * P = Q := CFC.sqrt_mul_sqrt_self Q hQ_pos
  have hP_sa : IsSelfAdjoint P := (CFC.sqrt_nonneg Q).isSelfAdjoint
  have h1 : ⟪P x, P x⟫_ℂ = ⟪x, P.adjoint (P x)⟫_ℂ := by
    rw [← adjoint_inner_right P x (P x)]
  have h2 : P.adjoint = P := hP_sa.adjoint_eq
  calc ‖P x‖^2 = (⟪P x, P x⟫_ℂ).re := by rw [inner_self_eq_norm_sq_to_K]; norm_cast
    _ = (⟪x, P.adjoint (P x)⟫_ℂ).re := by rw [h1]
    _ = (⟪x, P (P x)⟫_ℂ).re := by rw [h2]
    _ = (⟪x, (P * P) x⟫_ℂ).re := rfl
    _ = (⟪x, Q x⟫_ℂ).re := by rw [hP_sq]

/-- The final calculation for the Hölder bound. -/
private lemma holder_bound_calc {T : H →L[ℂ] H} (hT : IsTraceClass T) (A : H →L[ℂ] H)
    (ι : Type u) (b : HilbertBasis ι ℂ H)
    {V : H →L[ℂ] H} (hV_pi : IsPartialIsometry V) (_h_polar : T = V * absoluteValue T) :
    let Q := absoluteValue T
    let P := CFC.sqrt Q
    let B := A * V
    have hQ_pos : 0 ≤ Q := absoluteValue_nonneg T
    have hQ_tc : IsTraceClass Q := isTraceClass_absoluteValue_of_isTraceClass hT
    have h_eq_P : ∀ j, ‖P (b j)‖^2 = (⟪b j, Q (b j)⟫_ℂ).re := fun j => norm_sq_sqrt_eq_inner hQ_pos (b j)
    have h_summable_P_sq : Summable (fun j => ‖P (b j)‖^2) := by
      have h1 : (fun j => ‖P (b j)‖^2) = (fun j => (⟪b j, Q (b j)⟫_ℂ).re) := funext h_eq_P
      rw [h1]
      exact (isTraceClass_of_nonneg hQ_pos).mp hQ_tc ι b
    have h_conj_bound := tsum_inner_conjugate_le_of_nonneg hQ_pos hQ_tc B ι b
    have h_eq_PB : ∀ i, ‖P (B.adjoint (b i))‖^2 = (⟪B.adjoint (b i), Q (B.adjoint (b i))⟫_ℂ).re :=
      fun i => norm_sq_sqrt_eq_inner hQ_pos (B.adjoint (b i))
    have _h_summable_PB : Summable (fun i => (⟪B.adjoint (b i), Q (B.adjoint (b i))⟫_ℂ).re) := h_conj_bound.1
    have h_summable_PB_sq : Summable (fun i => ‖P (B.adjoint (b i))‖^2) := by
      have h1 : (fun i => ‖P (B.adjoint (b i))‖^2) = (fun i => (⟪B.adjoint (b i), Q (B.adjoint (b i))⟫_ℂ).re) := funext h_eq_PB
      rw [h1]; exact _h_summable_PB
    have _h_summable_product : Summable (fun i => ‖P (B.adjoint (b i))‖ * ‖P (b i)‖) :=
      Real.summable_mul_of_Lp_Lq_of_nonneg (p := 2) (q := 2) Real.HolderConjugate.two_two
        (fun i => norm_nonneg _) (fun i => norm_nonneg _)
        (by simpa [Real.rpow_natCast] using h_summable_PB_sq)
        (by simpa [Real.rpow_natCast] using h_summable_P_sq)
    have _h_bound_PB : ∑' i, (⟪B.adjoint (b i), Q (B.adjoint (b i))⟫_ℂ).re ≤ ‖B‖^2 * ∑' i, (⟪b i, Q (b i)⟫_ℂ).re := h_conj_bound.2
    have _hB_norm : ‖B‖ ≤ ‖A‖ := by
      calc ‖B‖ = ‖A * V‖ := rfl
        _ ≤ ‖A‖ * ‖V‖ := ContinuousLinearMap.opNorm_comp_le A V
        _ ≤ ‖A‖ * 1 := by gcongr; exact IsPartialIsometry.norm_le_one hV_pi
        _ = ‖A‖ := mul_one _
    (∑' i, ‖P (B.adjoint (b i))‖ * ‖P (b i)‖) ≤ ‖A‖ * ∑' i, (⟪b i, Q (b i)⟫_ℂ).re := by
  intro Q P B hQ_pos hQ_tc h_eq_P h_summable_P_sq h_conj_bound h_eq_PB _h_summable_PB h_summable_PB_sq
    _h_summable_product h_bound_PB _hB_norm
  have h_sum_product_bound : ∑' i, ‖P (B.adjoint (b i))‖ * ‖P (b i)‖ ≤
      Real.sqrt (∑' i, ‖P (B.adjoint (b i))‖^2) * Real.sqrt (∑' i, ‖P (b i)‖^2) := by
    have h := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg (p := 2) (q := 2) Real.HolderConjugate.two_two
      (fun i => norm_nonneg _) (fun i => norm_nonneg _)
      (by simpa [Real.rpow_natCast] using h_summable_PB_sq)
      (by simpa [Real.rpow_natCast] using h_summable_P_sq)
    simpa [Real.sqrt_eq_rpow, one_div, Real.rpow_natCast] using h.2
  have h_PB_bound : ∑' i, ‖P (B.adjoint (b i))‖^2 ≤ ‖B‖^2 * ∑' i, ‖P (b i)‖^2 := by
    simp_rw [h_eq_PB, h_eq_P]
    exact h_bound_PB
  calc ∑' i, ‖P (B.adjoint (b i))‖ * ‖P (b i)‖
      ≤ Real.sqrt (∑' i, ‖P (B.adjoint (b i))‖^2) * Real.sqrt (∑' i, ‖P (b i)‖^2) :=
          h_sum_product_bound
    _ ≤ Real.sqrt (‖B‖^2 * ∑' i, ‖P (b i)‖^2) * Real.sqrt (∑' i, ‖P (b i)‖^2) := by
        apply mul_le_mul_of_nonneg_right
        · exact Real.sqrt_le_sqrt h_PB_bound
        · exact Real.sqrt_nonneg _
    _ = ‖B‖ * Real.sqrt (∑' i, ‖P (b i)‖^2) * Real.sqrt (∑' i, ‖P (b i)‖^2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    _ = ‖B‖ * (Real.sqrt (∑' i, ‖P (b i)‖^2) * Real.sqrt (∑' i, ‖P (b i)‖^2)) := by ring
    _ = ‖B‖ * (∑' i, ‖P (b i)‖^2) := by
        have h_nonneg_sum : 0 ≤ ∑' i, ‖P (b i)‖^2 := tsum_nonneg (fun i => sq_nonneg _)
        rw [Real.mul_self_sqrt h_nonneg_sum]
    _ ≤ ‖A‖ * ∑' i, ‖P (b i)‖^2 := by gcongr
    _ = ‖A‖ * ∑' i, (⟪b i, Q (b i)⟫_ℂ).re := by rw [tsum_congr h_eq_P]

/-- Hölder-type bound: For trace-class T and bounded A,
    ∑ᵢ |Re⟨bᵢ, AT bᵢ⟩| ≤ ‖A‖ · Tr(|T|).

    This is a key lemma for proving that the sum of trace-class operators is trace-class. -/
theorem summable_abs_re_inner_mul_traceClass {T : H →L[ℂ] H} (hT : IsTraceClass T)
    (A : H →L[ℂ] H) (ι : Type u) (b : HilbertBasis ι ℂ H) :
    Summable (fun i => |(⟪b i, (A * T) (b i)⟫_ℂ).re|) ∧
    (∑' i, |(⟪b i, (A * T) (b i)⟫_ℂ).re|) ≤ ‖A‖ * ∑' i, (⟪b i, absoluteValue T (b i)⟫_ℂ).re := by
  obtain ⟨V, hV_pi, h_polar, h_ker⟩ := exists_polar_decomposition T
  let Q := absoluteValue T
  let P := CFC.sqrt Q
  let B := A * V
  have hQ_pos : 0 ≤ Q := absoluteValue_nonneg T
  have hQ_tc : IsTraceClass Q := isTraceClass_absoluteValue_of_isTraceClass hT
  have h_inner_eq : ∀ i, ⟪b i, (A * T) (b i)⟫_ℂ = ⟪P ((A * V).adjoint (b i)), P (b i)⟫_ℂ :=
    fun i => inner_AT_eq_inner_sqrt h_polar (b i)
  have h_CS_bound : ∀ i, |(⟪b i, (A * T) (b i)⟫_ℂ).re| ≤ ‖P (B.adjoint (b i))‖ * ‖P (b i)‖ := by
    intro i
    rw [h_inner_eq]
    calc |(⟪P ((A * V).adjoint (b i)), P (b i)⟫_ℂ).re|
        ≤ ‖⟪P ((A * V).adjoint (b i)), P (b i)⟫_ℂ‖ := Complex.abs_re_le_norm _
      _ ≤ ‖P ((A * V).adjoint (b i))‖ * ‖P (b i)‖ := norm_inner_le_norm _ _
  have h_eq_P : ∀ j, ‖P (b j)‖^2 = (⟪b j, Q (b j)⟫_ℂ).re := fun j => norm_sq_sqrt_eq_inner hQ_pos (b j)
  have h_summable_P_sq : Summable (fun j => ‖P (b j)‖^2) := by
    have h1 : (fun j => ‖P (b j)‖^2) = (fun j => (⟪b j, Q (b j)⟫_ℂ).re) := funext h_eq_P
    rw [h1]
    exact (isTraceClass_of_nonneg hQ_pos).mp hQ_tc ι b
  have h_conj_bound := tsum_inner_conjugate_le_of_nonneg hQ_pos hQ_tc B ι b
  have h_eq_PB : ∀ i, ‖P (B.adjoint (b i))‖^2 = (⟪B.adjoint (b i), Q (B.adjoint (b i))⟫_ℂ).re :=
    fun i => norm_sq_sqrt_eq_inner hQ_pos (B.adjoint (b i))
  have h_summable_PB : Summable (fun i => (⟪B.adjoint (b i), Q (B.adjoint (b i))⟫_ℂ).re) := h_conj_bound.1
  have h_summable_PB_sq : Summable (fun i => ‖P (B.adjoint (b i))‖^2) := by
    have h1 : (fun i => ‖P (B.adjoint (b i))‖^2) = (fun i => (⟪B.adjoint (b i), Q (B.adjoint (b i))⟫_ℂ).re) := funext h_eq_PB
    rw [h1]; exact h_summable_PB
  have h_summable_product : Summable (fun i => ‖P (B.adjoint (b i))‖ * ‖P (b i)‖) :=
    Real.summable_mul_of_Lp_Lq_of_nonneg (p := 2) (q := 2) Real.HolderConjugate.two_two
      (fun i => norm_nonneg _) (fun i => norm_nonneg _)
      (by simpa [Real.rpow_natCast] using h_summable_PB_sq)
      (by simpa [Real.rpow_natCast] using h_summable_P_sq)
  have h_summable_abs : Summable (fun i => |(⟪b i, (A * T) (b i)⟫_ℂ).re|) :=
    Summable.of_nonneg_of_le (fun i => abs_nonneg _) h_CS_bound h_summable_product
  constructor
  · exact h_summable_abs
  · calc ∑' i, |(⟪b i, (A * T) (b i)⟫_ℂ).re|
        ≤ ∑' i, ‖P (B.adjoint (b i))‖ * ‖P (b i)‖ :=
            Summable.tsum_le_tsum h_CS_bound h_summable_abs h_summable_product
      _ ≤ ‖A‖ * ∑' i, (⟪b i, Q (b i)⟫_ℂ).re :=
            holder_bound_calc hT A ι b hV_pi h_polar

/-- Sum of trace-class operators is trace-class.

The proof uses polar decomposition: S + T = U|S + T| where U is a partial isometry.
Then |S + T| = U†(S + T) and:
  ∑ ⟨b_i, |S+T| b_i⟩ = ∑ ⟨b_i, U†S b_i⟩ + ∑ ⟨b_i, U†T b_i⟩
The RHS terms are bounded by Tr(|S|) and Tr(|T|) using that ‖U†‖ ≤ 1. -/
lemma add_isTraceClass {S T : H →L[ℂ] H} (hS : IsTraceClass S) (hT : IsTraceClass T) :
    IsTraceClass (S + T) := by
  -- Get polar decomposition S + T = U |S + T|
  obtain ⟨U, hU_pi, h_polar, h_ker⟩ := exists_polar_decomposition (S + T)
  -- Key: |S + T| = U† (S + T) by the lemma above
  have h_abs_eq : absoluteValue (S + T) = U.adjoint * (S + T) :=
    absoluteValue_eq_adjoint_mul_of_polar hU_pi h_polar h_ker
  -- Show summability for S + T for any basis
  intro ι b
  -- The sum ∑ ⟨b_i, |S+T| b_i⟩ = ∑ ⟨b_i, U†(S+T) b_i⟩
  have h_term_eq : ∀ i, (⟪b i, absoluteValue (S + T) (b i)⟫_ℂ).re =
      (⟪b i, U.adjoint (S (b i))⟫_ℂ).re + (⟪b i, U.adjoint (T (b i))⟫_ℂ).re := by
    intro i
    rw [h_abs_eq]
    simp only [mul_apply, add_apply]
    rw [map_add, inner_add_right]
    simp only [Complex.add_re]
  -- The absolute value terms are nonneg
  have h_nonneg : ∀ i, 0 ≤ (⟪b i, absoluteValue (S + T) (b i)⟫_ℂ).re :=
    traceNormSummand_nonneg (S + T) b
  -- Bound each term by absolute values
  have h_bound : ∀ i, (⟪b i, absoluteValue (S + T) (b i)⟫_ℂ).re ≤
      |(⟪b i, U.adjoint (S (b i))⟫_ℂ).re| + |(⟪b i, U.adjoint (T (b i))⟫_ℂ).re| := by
    intro i
    rw [h_term_eq]
    apply add_le_add <;> exact le_abs_self _
  -- We need to bound ∑|⟨b_i, U†S b_i⟩.re| using summable_abs_re_inner_mul_traceClass
  -- First, note that U†S = U† * S where U† is a contraction (‖U†‖ ≤ 1)
  -- By summable_abs_re_inner_mul_traceClass: ∑|Re⟨bᵢ, (U†*S) bᵢ⟩| ≤ ‖U†‖ · Tr(|S|) ≤ Tr(|S|)
  -- Rewrite in terms of mul
  have h_UadjS_eq : ∀ i, U.adjoint (S (b i)) = (U.adjoint * S) (b i) := fun i => rfl
  have h_UadjT_eq : ∀ i, U.adjoint (T (b i)) = (U.adjoint * T) (b i) := fun i => rfl
  -- Summability and bounds from the Hölder lemma
  have h_sumS_holder := summable_abs_re_inner_mul_traceClass hS U.adjoint ι b
  have h_sumT_holder := summable_abs_re_inner_mul_traceClass hT U.adjoint ι b
  -- Summability of the bound
  have h_summable_bound : Summable (fun i => |(⟪b i, U.adjoint (S (b i))⟫_ℂ).re| +
      |(⟪b i, U.adjoint (T (b i))⟫_ℂ).re|) := by
    simp_rw [h_UadjS_eq, h_UadjT_eq]
    exact h_sumS_holder.1.add h_sumT_holder.1
  -- Summability of the trace term
  have h_summable : Summable (fun i => (⟪b i, absoluteValue (S + T) (b i)⟫_ℂ).re) := by
    apply Summable.of_nonneg_of_le h_nonneg h_bound h_summable_bound
  exact h_summable

instance : Zero (TraceClass H) := ⟨⟨0, zero_isTraceClass⟩⟩

instance : Neg (TraceClass H) where
  neg T := ⟨-T.toFun, neg_isTraceClass T.isTraceClass⟩

instance : Add (TraceClass H) where
  add S T := ⟨S.toFun + T.toFun, add_isTraceClass S.isTraceClass T.isTraceClass⟩

/-- Subtraction on TraceClass. -/
instance : Sub (TraceClass H) where
  sub S T := ⟨S.toFun - T.toFun, by
    have h : S.toFun - T.toFun = S.toFun + (-T.toFun) := sub_eq_add_neg S.toFun T.toFun
    rw [h]
    exact add_isTraceClass S.isTraceClass (neg_isTraceClass T.isTraceClass)⟩

instance : SMul ℂ (TraceClass H) where
  smul c T := ⟨c • T.toFun, smul_isTraceClass T.isTraceClass c⟩


/-- Extensionality for TraceClass: two trace-class operators are equal iff
    their underlying operators are equal. -/
@[ext]
lemma ext' {S T : TraceClass H} (h : S.toFun = T.toFun) : S = T := by
  cases S; cases T; simp only [TraceClass.mk.injEq]; exact h

@[simp]
lemma sub_toFun (S T : TraceClass H) : (S - T).toFun = S.toFun - T.toFun := rfl

-- Helper lemmas for algebraic laws
@[simp]
lemma add_toFun (S T : TraceClass H) : (S + T).toFun = S.toFun + T.toFun := rfl

@[simp]
lemma neg_toFun (T : TraceClass H) : (-T).toFun = -T.toFun := rfl

@[simp]
lemma zero_toFun : (0 : TraceClass H).toFun = 0 := rfl

@[simp]
lemma smul_toFun (c : ℂ) (T : TraceClass H) : (c • T).toFun = c • T.toFun := rfl

/-- `TraceClass.IsNonneg ρ` asserts that the underlying operator is non-negative. -/
class TraceClass.IsNonneg (ρ : TraceClass H) : Prop where
  nonneg : 0 ≤ (ρ : H →L[ℂ] H)

end TraceClass

end ContinuousLinearMap
