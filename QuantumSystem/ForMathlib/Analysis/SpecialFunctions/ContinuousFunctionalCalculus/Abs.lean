module

public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs

open scoped InnerProductSpace
open ContinuousLinearMap

@[expose] public section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Absolute value of an operator -/

section AbsoluteValue

/-- `T†T` is always a non-negative operator (in the Loewner order). -/
lemma adjoint_mul_self_nonneg (T : H →L[ℂ] H) : 0 ≤ T.adjoint * T := by
  rw [nonneg_iff_isPositive]
  exact isPositive_adjoint_comp_self T

/-- The absolute value of a bounded linear operator `T`, defined as `√(T†T)`.
This uses the continuous functional calculus for positive operators.
This equals `CFC.abs T` since `star T = T.adjoint` for ContinuousLinearMap. -/
noncomputable def absoluteValue (T : H →L[ℂ] H) : H →L[ℂ] H :=
  CFC.sqrt (T.adjoint * T)

lemma absoluteValue_eq_cfc_abs (T : H →L[ℂ] H) : absoluteValue T = CFC.abs T := by
  simp only [absoluteValue, CFC.abs, ContinuousLinearMap.star_eq_adjoint]

/-- The absolute value of an operator is non-negative. -/
lemma absoluteValue_nonneg (T : H →L[ℂ] H) : 0 ≤ absoluteValue T := by
  rw [absoluteValue_eq_cfc_abs]
  exact CFC.abs_nonneg T

/-- The absolute value of an operator is self-adjoint. -/
lemma absoluteValue_isSelfAdjoint (T : H →L[ℂ] H) : IsSelfAdjoint (absoluteValue T) := by
  have h := absoluteValue_nonneg T
  rw [nonneg_iff_isPositive] at h
  exact h.isSelfAdjoint

/-- The absolute value of an operator is positive (in the sense of IsPositive). -/
lemma absoluteValue_isPositive (T : H →L[ℂ] H) : (absoluteValue T).IsPositive := by
  rw [← nonneg_iff_isPositive]
  exact absoluteValue_nonneg T

/-- `|T|² = T†T` -/
lemma absoluteValue_sq (T : H →L[ℂ] H) : absoluteValue T * absoluteValue T = T.adjoint * T := by
  unfold absoluteValue
  exact CFC.sqrt_mul_sqrt_self _ (adjoint_mul_self_nonneg T)

/-- The absolute value of the zero operator is zero. -/
lemma absoluteValue_zero : absoluteValue (0 : H →L[ℂ] H) = 0 := by
  unfold absoluteValue
  have h : (0 : H →L[ℂ] H).adjoint = 0 := by ext; simp
  simp only [h, zero_mul]
  exact CFC.sqrt_zero

/-- For a positive operator T, the absolute value equals T itself. -/
lemma absoluteValue_of_nonneg {T : H →L[ℂ] H} (hT : 0 ≤ T) : absoluteValue T = T := by
  unfold absoluteValue
  have hpos : T.IsPositive := by rwa [← nonneg_iff_isPositive]
  have hsa : T.adjoint = T := hpos.isSelfAdjoint.adjoint_eq
  rw [hsa, ← sq]
  exact CFC.sqrt_sq T hT

lemma absoluteValue_smul (c : ℂ) (T : H →L[ℂ] H) :
    absoluteValue (c • T) = ‖c‖ • absoluteValue T := by
  rw [absoluteValue_eq_cfc_abs, absoluteValue_eq_cfc_abs]
  exact CFC.abs_smul c T

lemma norm_absoluteValue_eq_norm (T : H →L[ℂ] H) (x : H) : ‖absoluteValue T x‖ = ‖T x‖ := by
  have hP := absoluteValue_isSelfAdjoint T
  let P := absoluteValue T
  have h_inner : ‖P x‖^2 = ‖T x‖^2 := by
    simp only [← inner_self_eq_norm_sq (𝕜 := ℂ) _]
    change (⟪P x, P x⟫_ℂ).re = (⟪T x, T x⟫_ℂ).re
    calc (⟪P x, P x⟫_ℂ).re
        = (⟪P.adjoint (P x), x⟫_ℂ).re := by rw [adjoint_inner_left]
      _ = (⟪P (P x), x⟫_ℂ).re := by rw [hP.adjoint_eq]
      _ = (⟪(P * P) x, x⟫_ℂ).re := rfl
      _ = (⟪(T.adjoint * T) x, x⟫_ℂ).re := by rw [absoluteValue_sq]
      _ = (⟪T.adjoint (T x), x⟫_ℂ).re := rfl
      _ = (⟪T x, T x⟫_ℂ).re := by rw [adjoint_inner_left]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h_inner

lemma absoluteValue_ker_eq_ker (T : H →L[ℂ] H) :
    LinearMap.ker (absoluteValue T).toLinearMap = LinearMap.ker T.toLinearMap := by
  ext x
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  constructor
  · intro h
    rw [← norm_eq_zero, ← norm_absoluteValue_eq_norm, h, norm_zero]
  · intro h
    rw [← norm_eq_zero, norm_absoluteValue_eq_norm, h, norm_zero]

lemma absoluteValue_adjoint_sq (T : H →L[ℂ] H) :
    absoluteValue T.adjoint * absoluteValue T.adjoint = T * T.adjoint := by
  simpa [adjoint_adjoint] using (absoluteValue_sq (T := T.adjoint))

/-! ### Polar decomposition identities -/

/-- (U|T|U†)² = T·T† when T = U|T| and U†U|T| = |T| -/
lemma conjugate_abs_sq_eq {T U : H →L[ℂ] H}
    (hT_polar : T = U * absoluteValue T)
    (hU_adj_U_abs : U.adjoint * U * absoluteValue T = absoluteValue T) :
    (U * absoluteValue T * U.adjoint) * (U * absoluteValue T * U.adjoint) = T * T.adjoint := by
  have h2 : T.adjoint = absoluteValue T * U.adjoint := by
    have h_adj : (U * absoluteValue T).adjoint = (absoluteValue T).adjoint * U.adjoint := by
      change star (U * absoluteValue T) = star (absoluteValue T) * star U
      rw [star_mul]
    conv_lhs => rw [hT_polar]
    rw [h_adj, (absoluteValue_isSelfAdjoint T).adjoint_eq]
  set absT := absoluteValue T with h_absT_def
  -- (U|T|U†)² = U|T|(U†U)|T|U† = U|T|²U†
  have lhs_eq : (U * absT * U.adjoint) * (U * absT * U.adjoint)
      = U * absT * absT * U.adjoint := by
    have hU_adj_U_absT : U.adjoint * U * absT = absT := hU_adj_U_abs
    calc (U * absT * U.adjoint) * (U * absT * U.adjoint)
        = U * absT * (U.adjoint * U * absT) * U.adjoint := by simp only [mul_assoc]
      _ = U * absT * absT * U.adjoint := by rw [hU_adj_U_absT]
  -- T·T† = (U|T|)(|T|U†) = U|T|²U†
  have h2' : T.adjoint = absT * U.adjoint := h2
  have rhs_eq : T * T.adjoint = U * absT * absT * U.adjoint := by
    calc T * T.adjoint
        = T * (absT * U.adjoint) := by rw [h2']
      _ = (U * absT) * (absT * U.adjoint) := by rw [hT_polar]
      _ = U * absT * absT * U.adjoint := by simp only [mul_assoc]
  rw [lhs_eq, rhs_eq]

/-- U|T|U† is a positive operator when |T| is the absolute value -/
lemma conjugate_abs_nonneg {T U : H →L[ℂ] H} :
    0 ≤ U * absoluteValue T * U.adjoint := by
  set absT := absoluteValue T with h_absT_def
  rw [ContinuousLinearMap.le_def]
  constructor
  · -- Symmetry: (U|T|U†)† = U|T|†U†† = U|T|U†
    simp only [sub_zero]
    change ((U * absT * U.adjoint) : H →L[ℂ] H).toLinearMap.IsSymmetric
    have h_self_adj : IsSelfAdjoint (U * absT * U.adjoint) := by
      rw [isSelfAdjoint_iff']
      -- Need: (U * absT * U†)† = U * absT * U†
      have step1 : (U * absT * U.adjoint).adjoint = U.adjoint.adjoint * (U * absT).adjoint := by
        change star _ = star (adjoint U) * star (U * absT)
        rw [star_mul]
      have step2 : (U * absT).adjoint = absT.adjoint * U.adjoint := by
        change star _ = star absT * star U
        rw [star_mul]
      rw [step1, step2, ContinuousLinearMap.adjoint_adjoint]
      rw [h_absT_def, (absoluteValue_isSelfAdjoint T).adjoint_eq, ← h_absT_def]
      simp only [mul_assoc]
    exact h_self_adj.isSymmetric
  · intro x
    simp only [ContinuousLinearMap.reApplyInnerSelf, sub_zero, mul_apply]
    -- Goal: 0 ≤ re⟨U(|T|(U†x)), x⟩ = re⟨|T|(U†x), U†x⟩
    have eq : ⟪U (absT (U.adjoint x)), x⟫_ℂ = ⟪absT (U.adjoint x), U.adjoint x⟫_ℂ := by
      rw [← adjoint_inner_left U.adjoint, ContinuousLinearMap.adjoint_adjoint]
    rw [eq, h_absT_def]
    have h_abs_pos := absoluteValue_isPositive T
    rw [ContinuousLinearMap.isPositive_def] at h_abs_pos
    have h := h_abs_pos.2 (U.adjoint x)
    simp only [ContinuousLinearMap.reApplyInnerSelf_apply] at h
    exact h

/-- For polar decomposition T = U|T| with U partial isometry, |T†| = U|T|U† -/
lemma absoluteValue_adjoint_eq_conjugate_by_partial_isometry {T U : H →L[ℂ] H}
    (hT_polar : T = U * absoluteValue T)
    (hU_adj_U_abs : U.adjoint * U * absoluteValue T = absoluteValue T) :
    absoluteValue T.adjoint = U * absoluteValue T * U.adjoint := by
  set absT := absoluteValue T with h_absT_def
  have h_sq : (U * absT * U.adjoint) * (U * absT * U.adjoint) = T * T.adjoint :=
    conjugate_abs_sq_eq hT_polar hU_adj_U_abs
  have h_pos : 0 ≤ U * absT * U.adjoint := conjugate_abs_nonneg
  have h_absT_adj_sq : absoluteValue T.adjoint * absoluteValue T.adjoint = T * T.adjoint :=
    absoluteValue_adjoint_sq T
  have h_both_positive : 0 ≤ absoluteValue T.adjoint := absoluteValue_nonneg T.adjoint
  -- Both U|T|U† and |T†| are positive with same square, so equal by sqrt uniqueness
  calc absoluteValue T.adjoint
      = CFC.sqrt (absoluteValue T.adjoint * absoluteValue T.adjoint) :=
        (CFC.sqrt_sq (absoluteValue T.adjoint) h_both_positive).symm
    _ = CFC.sqrt (T * T.adjoint) := by rw [h_absT_adj_sq]
    _ = CFC.sqrt (U * absT * U.adjoint * (U * absT * U.adjoint)) := by
        rw [← h_sq]
    _ = U * absT * U.adjoint :=
        CFC.sqrt_sq (U * absT * U.adjoint) h_pos

/-- S x = 0 when x ∈ ker |T| and S = √|T| -/
lemma cfc_sqrt_absoluteValue_ker {T : H →L[ℂ] H}
    (x : H) (hx : absoluteValue T x = 0) :
    CFC.sqrt (absoluteValue T) x = 0 := by
  let S := CFC.sqrt (absoluteValue T)
  have hS_sq : S * S = absoluteValue T := CFC.sqrt_mul_sqrt_self _ (absoluteValue_nonneg T)
  have hS_sa : IsSelfAdjoint S := (CFC.sqrt_nonneg _).isSelfAdjoint
  have h_norm_sq : ‖S x‖^2 = (⟪absoluteValue T x, x⟫_ℂ).re := by
    have h1 : ‖S x‖^2 = Complex.re ⟪S x, S x⟫_ℂ := by
      rw [(inner_self_eq_norm_sq (𝕜 := ℂ) (S x)).symm]; simp
    calc ‖S x‖^2 = Complex.re ⟪S x, S x⟫_ℂ := h1
      _ = Complex.re ⟪S (S x), x⟫_ℂ := by rw [← adjoint_inner_left, hS_sa.adjoint_eq]
      _ = Complex.re ⟪(S * S) x, x⟫_ℂ := by rfl
      _ = Complex.re ⟪absoluteValue T x, x⟫_ℂ := by rw [hS_sq]
  rw [hx, inner_zero_left, Complex.zero_re] at h_norm_sq
  exact norm_eq_zero.mp (eq_zero_of_pow_eq_zero h_norm_sq)

end AbsoluteValue
