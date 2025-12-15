import QuantumSystem.Algebra.CStarAlgebra.State

section StateContinuous

open NNReal

variable (𝕜 : Type*) [RCLike 𝕜]

namespace State

variable {𝕜 A : Type*} [RCLike 𝕜] [NonUnitalCStarAlgebra A] [Module 𝕜 A]

/-- States are Lipschitz continuous with constant 1. -/
lemma lipschitzWith_one (ω : State 𝕜 A) : LipschitzWith 1 ω := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  simp only [NNReal.coe_one, one_mul]
  calc dist (ω x) (ω y)
      = ‖ω x - ω y‖ := dist_eq_norm _ _
    _ = ‖ω (x - y)‖ := by
        congr 1
        rw [map_sub]
    _ ≤ ‖x - y‖ := norm_le_norm ω _
    _ = dist x y := (dist_eq_norm _ _).symm

/-- States are continuous. -/
lemma continuous (ω : State 𝕜 A) : Continuous ω :=
  (lipschitzWith_one ω).continuous

/-- States are uniformly continuous. -/
lemma uniformContinuous (ω : State 𝕜 A) : UniformContinuous ω :=
  (lipschitzWith_one ω).uniformContinuous

end State

end StateContinuous

section ContinuousState

open NNReal

variable (𝕜 : Type*) [RCLike 𝕜]

/-- A continuous state on a non-unital C*-algebra: a positive continuous linear functional
with operator norm 1. -/
structure ContinuousState (A : Type*) [NonUnitalCStarAlgebra A] [NormedSpace 𝕜 A]
    extends A →L[𝕜] 𝕜 where
  positive : ∀ a : A, ∃ r : ℝ≥0, toContinuousLinearMap (star a * a) = RCLike.ofReal (r : ℝ)
  norm_eq_one: ‖toContinuousLinearMap‖ = 1

namespace ContinuousState

variable {𝕜 A : Type*} [RCLike 𝕜] [NonUnitalCStarAlgebra A] [NormedSpace 𝕜 A]

/-- `FunLike` instance to make continuous states callable like functions. -/
instance : FunLike (ContinuousState 𝕜 A) A 𝕜 where
  coe ω := ω.toContinuousLinearMap
  coe_injective' ω₁ ω₂ h := by
    cases ω₁
    cases ω₂
    congr
    exact DFunLike.coe_injective h

/-- Continuous states are continuous linear maps. -/
instance : ContinuousLinearMapClass (ContinuousState 𝕜 A) 𝕜 A 𝕜 where
  map_add ω := ω.toContinuousLinearMap.map_add
  map_smulₛₗ ω := ω.toContinuousLinearMap.map_smul
  map_continuous ω := ω.toContinuousLinearMap.cont

/-- Norm instance for continuous states. -/
noncomputable instance : Norm (ContinuousState 𝕜 A) where
  norm ω := ‖ω.toContinuousLinearMap‖

@[simp]
lemma toContinuousLinearMap_apply (ω : ContinuousState 𝕜 A) (a : A) :
    ω.toContinuousLinearMap a = ω a := rfl

@[ext]
lemma ext {ω₁ ω₂ : ContinuousState 𝕜 A} (h : ∀ a, ω₁ a = ω₂ a) : ω₁ = ω₂ :=
  DFunLike.ext ω₁ ω₂ h

lemma norm_def (ω : ContinuousState 𝕜 A) :
    ‖ω‖ = ‖ω.toContinuousLinearMap‖ := rfl

/-- Convert a `ContinuousState` to its underlying continuous linear map. -/
def toL (ω : ContinuousState 𝕜 A) : A →L[𝕜] 𝕜 := ω.toContinuousLinearMap

@[simp]
lemma toL_apply (ω : ContinuousState 𝕜 A) (a : A) : ω.toL a = ω a := rfl

/-- Continuous states are continuous. -/
lemma continuous (ω : ContinuousState 𝕜 A) : Continuous ω :=
  ω.toContinuousLinearMap.cont

/-- Continuous states are Lipschitz continuous with constant 1. -/
lemma lipschitzWith_one (ω : ContinuousState 𝕜 A) : LipschitzWith 1 ω := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  simp only [NNReal.coe_one, one_mul]
  calc dist (ω x) (ω y)
      = ‖ω x - ω y‖ := dist_eq_norm _ _
    _ = ‖ω (x - y)‖ := by
        congr 1
        rw [map_sub]
    _ = ‖ω.toContinuousLinearMap (x - y)‖ := rfl
    _ ≤ ‖ω.toContinuousLinearMap‖ * ‖x - y‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = 1 * ‖x - y‖ := by rw [ω.norm_eq_one]
    _ = ‖x - y‖ := one_mul _
    _ = dist x y := (dist_eq_norm _ _).symm

/-- Continuous states are uniformly continuous. -/
lemma uniformContinuous (ω : ContinuousState 𝕜 A) : UniformContinuous ω :=
  ω.toContinuousLinearMap.uniformContinuous

/-- Continuous states satisfy `‖ω a‖ ≤ ‖a‖` for all `a`. -/
lemma norm_le_norm (ω : ContinuousState 𝕜 A) (a : A) : ‖ω a‖ ≤ ‖a‖ := by
  calc ‖ω a‖
      = ‖ω.toContinuousLinearMap a‖ := rfl
    _ ≤ ‖ω.toContinuousLinearMap‖ * ‖a‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = 1 * ‖a‖ := by rw [ω.norm_eq_one]
    _ = ‖a‖ := one_mul _

/-- The canonical map from a continuous state to the weak dual. -/
def toWeakDual (ω : ContinuousState 𝕜 A) : WeakDual 𝕜 A :=
  StrongDual.toWeakDual ω.toContinuousLinearMap

end ContinuousState

end ContinuousState

namespace State

open NNReal

variable {𝕜 : Type*} [RCLike 𝕜]
variable {A : Type*} [NonUnitalCStarAlgebra A] [NormedSpace 𝕜 A]

/-- Convert a `State` to a `ContinuousLinearMap` using `mkContinuous`.
This avoids depending on internal ContinuousLinearMap definitions. -/
noncomputable def toContinuousLinearMap (ω : State 𝕜 A) : A →L[𝕜] 𝕜 :=
  ω.toLinearMap.mkContinuous 1 (fun a => by
    simp [toLinearMap_apply]
    exact norm_le_norm ω a)

@[simp]
lemma toContinuousLinearMap_apply (ω : State 𝕜 A) (a : A) :
    ω.toContinuousLinearMap a = ω a := rfl

/-- The operator norm of the continuous linear map equals 1. -/
lemma toContinuousLinearMap_norm (ω : State 𝕜 A) : ‖ω.toContinuousLinearMap‖ = 1 := by
  apply le_antisymm
  · exact LinearMap.mkContinuous_norm_le _ zero_le_one _
  · have h_norm : ‖ω‖ = 1 := ω.norm_eq_one
    rw [← h_norm, norm_def ω]
    apply csSup_le
    · by_contra h_empty
      push_neg at h_empty
      have : sSup {r : ℝ | ∃ a : A, a ≠ 0 ∧ r = ‖ω a‖ / ‖a‖} = 0 := by
        rw [Real.sSup_def]
        simp [h_empty]
      have h_norm_zero : ‖ω‖ = 0 := by rw [norm_def ω, this]
      have h_norm_one : ‖ω‖ = 1 := ω.norm_eq_one
      rw [h_norm_one] at h_norm_zero
      norm_num at h_norm_zero
    · intro r ⟨a, ha, hr⟩
      rw [hr]
      have h_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha
      rw [div_le_iff₀ h_pos, ← toContinuousLinearMap_apply]
      exact ContinuousLinearMap.le_opNorm _ _

/-- The algebraic norm equals the operator norm of the ContinuousLinearMap representation. -/
lemma norm_eq_toContinuousLinearMap_norm (ω : State 𝕜 A) :
    ‖ω‖ = ‖ω.toContinuousLinearMap‖ := by
  have h_norm : ‖ω‖ = 1 := ω.norm_eq_one
  rw [h_norm, toContinuousLinearMap_norm]

/-- Convert a `State` to a `ContinuousState`. -/
noncomputable def toContinuousState (ω : State 𝕜 A) : ContinuousState 𝕜 A where
  toContinuousLinearMap := ω.toContinuousLinearMap
  positive := ω.positive
  norm_eq_one := toContinuousLinearMap_norm ω

@[simp]
lemma toContinuousState_apply (ω : State 𝕜 A) (a : A) :
    ω.toContinuousState a = ω a := rfl

end State

namespace ContinuousState

variable {𝕜 : Type*} [RCLike 𝕜]
variable {A : Type*} [NonUnitalCStarAlgebra A] [NormedSpace 𝕜 A]

/-- Convert a `ContinuousState` to a `State`. -/
noncomputable def toState (ω : ContinuousState 𝕜 A) : State 𝕜 A where
  toLinearMap := ω.toContinuousLinearMap.toLinearMap
  positive := ω.positive
  norm_eq_one := by
    unfold linearOpNorm
    have h_op_norm : ‖ω.toContinuousLinearMap‖ = 1 := ω.norm_eq_one
    by_cases h_sub : Subsingleton A
    · have : ‖ω.toContinuousLinearMap‖ = 0 := ContinuousLinearMap.opNorm_subsingleton _
      rw [this] at h_op_norm
      norm_num at h_op_norm
    have ⟨a, ha⟩ : ∃ a : A, a ≠ 0 := by
      rw [not_subsingleton_iff_nontrivial] at h_sub
      exact exists_ne 0
    apply le_antisymm
    · apply csSup_le
      · exact ⟨‖ω.toContinuousLinearMap a‖ / ‖a‖, a, ha, rfl⟩
      · intro r ⟨b, hb, hr⟩
        subst hr
        by_cases h : b = 0
        · simp [h]
        · have h_pos : 0 < ‖b‖ := norm_pos_iff.mpr h
          calc ‖ω.toContinuousLinearMap b‖ / ‖b‖
              ≤ (‖ω.toContinuousLinearMap‖ * ‖b‖) / ‖b‖ := by
                  apply div_le_div_of_nonneg_right
                  · exact ContinuousLinearMap.le_opNorm _ _
                  · exact norm_nonneg _
            _ = ‖ω.toContinuousLinearMap‖ := by field_simp
            _ = 1 := h_op_norm
    · rw [← h_op_norm]
      apply ContinuousLinearMap.opNorm_le_bound
      · apply Real.sSup_nonneg
        intro r ⟨b, _, hr⟩
        rw [hr]
        apply div_nonneg <;> apply norm_nonneg
      · intro b
        by_cases hb : b = 0
        · simp [hb]
        · have h_mem : ‖ω.toContinuousLinearMap b‖ / ‖b‖ ∈
              {r : ℝ | ∃ c : A, c ≠ 0 ∧ r = ‖ω.toContinuousLinearMap c‖ / ‖c‖} := ⟨b, hb, rfl⟩
          have h_bdd : BddAbove {r : ℝ | ∃ c : A, c ≠ 0 ∧ r = ‖ω.toContinuousLinearMap c‖ / ‖c‖} := by
            use 1
            intro r ⟨c, hc, hr⟩
            subst hr
            have : 0 < ‖c‖ := norm_pos_iff.mpr hc
            calc ‖ω.toContinuousLinearMap c‖ / ‖c‖
                ≤ (‖ω.toContinuousLinearMap‖ * ‖c‖) / ‖c‖ := by
                    apply div_le_div_of_nonneg_right
                    · exact ContinuousLinearMap.le_opNorm _ _
                    · exact norm_nonneg _
              _ = ‖ω.toContinuousLinearMap‖ := by field_simp
              _ = 1 := h_op_norm
          calc ‖ω.toContinuousLinearMap b‖
              = (‖ω.toContinuousLinearMap b‖ / ‖b‖) * ‖b‖ := by field_simp
            _ ≤ sSup {r : ℝ | ∃ c : A, c ≠ 0 ∧ r = ‖ω.toContinuousLinearMap c‖ / ‖c‖} * ‖b‖ :=
                mul_le_mul_of_nonneg_right (le_csSup h_bdd h_mem) (norm_nonneg _)

@[simp]
lemma toState_apply (ω : ContinuousState 𝕜 A) (a : A) :
    ω.toState a = ω a := rfl

end ContinuousState
