/-
Copyright (c) 2025 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Algebra.CStarAlgebra.GNS.Representation
public import QuantumSystem.Algebra.CStarAlgebra.PureState

/-!
# Irreducibility of the GNS representation of a pure state

For a pure state `ψ`, the canonical GNS representation `GNS.Representation.canonical ψ.toState` is
irreducible (`GNS.Representation.pureState_gns_isIrreducible`): a closed invariant subspace
splits the cyclic vector, the two pieces define quasi-states summing to `ψ`, and purity forces
one of them to vanish.
-/

@[expose] public section


namespace GNS

namespace Representation

open scoped ComplexOrder ComplexConjugate CStarAlgebra InnerProduct NNReal ComplexHilbertSpace

local notation "⟪" x ", " y "⟫" => inner ℂ x y

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {ω : State A}

lemma inner_left_mem_right_pi_mem_orthogonal (T : GNS.Representation ω)
    (W : ClosedSubmodule ℂ T.H) (hW : W ∈ T.closedInvtSubmodule) (a : A) {w x : T.H}
    (hw : w ∈ W.toSubmodule) (hx : x ∈ W.toSubmoduleᗮ) :
    ⟪w, (T.π a) x⟫ = 0 := by
  have hx_map : (T.π a) x ∈ W.toSubmoduleᗮ :=
    CStarRep.apply_mem_of_mem_invtSubmodule (CStarRep.orthogonal_mem_invtSubmodule hW) a hx
  exact Submodule.inner_right_of_mem_orthogonal hw hx_map

lemma inner_left_mem_orthogonal_right_pi_mem (T : GNS.Representation ω)
    (W : ClosedSubmodule ℂ T.H) (hW : W ∈ T.closedInvtSubmodule) (a : A) {w x : T.H}
    (hx : x ∈ W.toSubmoduleᗮ) (hw : w ∈ W.toSubmodule) :
    ⟪x, (T.π a) w⟫ = 0 := by
  have hw_map : (T.π a) w ∈ W.toSubmodule := CStarRep.apply_mem_of_mem_invtSubmodule hW a hw
  have h0 : ⟪(T.π a) w, x⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hw_map hx
  exact (inner_eq_zero_symm (x := x) (y := (T.π a) w)).2 h0

/-- The cyclic vector splits along a closed submodule `W` and its orthogonal complement. -/
lemma cyclicVector_decomp (T : GNS.Representation ω) (W : ClosedSubmodule ℂ T.H) :
    ∃ v₁ v₂ : T.H, v₁ ∈ W.toSubmodule ∧ v₂ ∈ W.toSubmoduleᗮ ∧ T.ξ = v₁ + v₂ ∧ ⟪v₁, v₂⟫ = 0 := by
  -- A closed subspace of a Hilbert space is complete, so it has an orthogonal projection.
  have : CompleteSpace W.toSubmodule := W.isClosed.completeSpace_coe
  refine ⟨W.toSubmodule.starProjection T.ξ, T.ξ - W.toSubmodule.starProjection T.ξ, ?_, ?_, ?_, ?_⟩
  · exact Submodule.starProjection_apply_mem (U := W.toSubmodule) (x := T.ξ)
  · exact Submodule.sub_starProjection_mem_orthogonal (K := W.toSubmodule) (v := T.ξ)
  · simp [add_sub_cancel]
  · exact Submodule.inner_right_of_mem_orthogonal
      (Submodule.starProjection_apply_mem (U := W.toSubmodule) (x := T.ξ))
      (Submodule.sub_starProjection_mem_orthogonal (K := W.toSubmodule) (v := T.ξ))


noncomputable def vectorFunctional (T : GNS.Representation ω) (v : T.H) : WeakDual ℂ A :=
  (innerSL ℂ v).comp (T.orbit v)

@[simp]
lemma vectorFunctional_apply (T : GNS.Representation ω) (v : T.H) (a : A) :
    T.vectorFunctional v a = ⟪v, (T.π a) v⟫ := by
  rfl

/-- A vector functional `a ↦ ⟪v, π a v⟫` is positive: on `a* a` it is `‖π a v‖²`. -/
lemma vectorFunctional_nonneg (T : GNS.Representation ω) (v : T.H) :
    ∀ a : A, 0 ≤ a → 0 ≤ T.vectorFunctional v a := by
  refine fun _ => StarOrderedRing.map_nonneg_of_star_mul_self_nonneg _ fun a => ?_
  -- `⟪v, π(star a * a) v⟫ = ⟪π(a)v, π(a)v⟫ = ‖π(a)v‖^2`.
  have hmul : T.π (star a * a) = (T.π (star a)) * (T.π a) :=
    T.π.map_mul' (star a) a
  have h : T.vectorFunctional v (star a * a) = (‖(T.π a) v‖ : ℂ) ^ 2 := by
    calc
      T.vectorFunctional v (star a * a) = ⟪v, (T.π (star a * a)) v⟫ := by
        simp [vectorFunctional_apply]
      _ = ⟪v, ((T.π (star a)) * (T.π a)) v⟫ := by
        simp [hmul]
      _ = ⟪v, (T.π (star a)) ((T.π a) v)⟫ := by
        rfl
      _ = ⟪v, ((T.π a)†) ((T.π a) v)⟫ := by
        rw [← T.adjoint_π a]
      _ = ⟪(T.π a) v, (T.π a) v⟫ := by
        -- `⟪v, A† (A v)⟫ = ⟪A v, A v⟫`.
        exact
          (ContinuousLinearMap.adjoint_inner_right (A := (T.π a)) (x := v) (y := (T.π a) v))
      _ = (‖(T.π a) v‖ : ℂ) ^ 2 := by
        simp
  rw [h, ← Complex.ofReal_pow]
  exact Complex.zero_le_real.mpr (sq_nonneg _)

lemma opNorm_vectorFunctional_le (T : GNS.Representation ω) (v : T.H) :
    ‖WeakDual.toStrongDual (T.vectorFunctional v)‖ ≤ ‖v‖ ^ 2 := by
  -- Prove a pointwise bound and use `opNorm_le_bound`.
  refine ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg ‖v‖) ?_
  intro a
  -- `‖⟪v, π(a) v⟫‖ ≤ ‖v‖ * ‖π(a)v‖ ≤ ‖v‖ * (‖a‖ * ‖v‖)`.
  have hcs : ‖⟪v, (T.π a) v⟫‖ ≤ ‖v‖ * ‖(T.π a) v‖ := by
    simpa [mul_comm] using (norm_inner_le_norm v ((T.π a) v))
  have hop : ‖(T.π a) v‖ ≤ ‖a‖ * ‖v‖ := by
    -- From contractivity of `π` and the definition of operator norm.
    have h₁ : ‖(T.π a) v‖ ≤ ‖T.π a‖ * ‖v‖ := by
      simpa [mul_comm] using (T.π a).le_opNorm v
    have h₂ : ‖T.π a‖ ≤ ‖a‖ := by
      simpa using (NonUnitalStarAlgHom.norm_apply_le (φ := T.π) a)
    have h₃ : ‖T.π a‖ * ‖v‖ ≤ ‖a‖ * ‖v‖ := by
      gcongr
    exact h₁.trans h₃
  -- Combine.
  have : ‖⟪v, (T.π a) v⟫‖ ≤ (‖v‖ ^ 2) * ‖a‖ := by
    calc
      ‖⟪v, (T.π a) v⟫‖ ≤ ‖v‖ * ‖(T.π a) v‖ := hcs
      _ ≤ ‖v‖ * (‖a‖ * ‖v‖) := by gcongr
      _ = (‖v‖ ^ 2) * ‖a‖ := by
        simp [pow_two]
        ring_nf
  -- Unfold `WeakDual.toStrongDual` application.
  simpa [WeakDual.toStrongDual_apply, vectorFunctional_apply, mul_comm, mul_left_comm, mul_assoc] using this


lemma state_decomposition (T : GNS.Representation ω) (W : ClosedSubmodule ℂ T.H)
    (hW : W ∈ T.closedInvtSubmodule) (v₁ v₂ : T.H) (hv₁ : v₁ ∈ W.toSubmodule)
    (hv₂ : v₂ ∈ W.toSubmoduleᗮ) (hξ : T.ξ = v₁ + v₂) (a : A) :
    ω a = T.vectorFunctional v₁ a + T.vectorFunctional v₂ a := by
  rw [T.gns_condition, hξ]
  simp only [vectorFunctional_apply]
  have : (T.π a) (v₁ + v₂) = (T.π a) v₁ + (T.π a) v₂ := by
    exact ContinuousLinearMap.map_add (T.π a) v₁ v₂
  rw [this, inner_add_left, inner_add_right, inner_add_right]
  have h₁ : ⟪v₁, (T.π a) v₂⟫ = 0 :=
    inner_left_mem_right_pi_mem_orthogonal T W hW a hv₁ hv₂
  have h₂ : ⟪v₂, (T.π a) v₁⟫ = 0 :=
    inner_left_mem_orthogonal_right_pi_mem T W hW a hv₂ hv₁
  simp [h₁, h₂]

lemma norm_sq_decomposition (T : GNS.Representation ω) (v₁ v₂ : T.H) (hξ : T.ξ = v₁ + v₂)
    (horth : ⟪v₁, v₂⟫ = 0) :
    ‖v₁‖ ^ 2 + ‖v₂‖ ^ 2 = 1 := by
  have h₁ : ‖T.ξ‖ ^ 2 = ‖v₁ + v₂‖ ^ 2 := by rw [hξ]
  rw [T.norm_ξ, one_pow] at h₁
  have h₂ : ‖v₁ + v₂‖ ^ 2 = ‖v₁‖ ^ 2 + ‖v₂‖ ^ 2 := by
    have eq1 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (x := v₁ + v₂)
    have eq2 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (x := v₁)
    have eq3 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (x := v₂)
    rw [inner_add_left, inner_add_right, inner_add_right] at eq1
    simp only [horth, add_zero] at eq1
    have hconj : ⟪v₂, v₁⟫ = conj ⟪v₁, v₂⟫ := (inner_conj_symm v₂ v₁).symm
    rw [horth] at hconj
    simp [hconj] at eq1
    -- eq1 : ↑‖v₁‖ ^ 2 + ↑‖v₂‖ ^ 2 = ↑‖v₁ + v₂‖ ^ 2
    have : (‖v₁ + v₂‖ : ℂ) ^ 2 = (‖v₁‖ : ℂ) ^ 2 + (‖v₂‖ : ℂ) ^ 2 := eq1.symm
    exact Complex.ofReal_injective (by simpa [Complex.ofReal_pow] using this)
  linarith

lemma norm_sq_in_Icc (T : GNS.Representation ω) (v₁ v₂ : T.H) (hξ : T.ξ = v₁ + v₂)
    (horth : ⟪v₁, v₂⟫ = 0) :
    ‖v₁‖ ^ 2 ∈ Set.Icc (0 : ℝ) 1 := by
  have h := norm_sq_decomposition T v₁ v₂ hξ horth
  constructor
  · exact sq_nonneg _
  · linarith [sq_nonneg ‖v₂‖]


lemma vectorFunctional_mem_quasiStateSpace_of_norm_eq_one (T : GNS.Representation ω) (v : T.H)
    (hv : ‖v‖ = 1) :
    T.vectorFunctional v ∈ QuasiStateSpace A := by
  constructor
  · exact vectorFunctional_nonneg T v
  · simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
    calc ‖WeakDual.toStrongDual (T.vectorFunctional v)‖
        ≤ ‖v‖ ^ 2 := opNorm_vectorFunctional_le T v
      _ = 1 ^ 2 := by rw [hv]
      _ = 1 := one_pow 2

lemma normalized_vectorFunctional_mem_quasiStateSpace (T : GNS.Representation ω) (v : T.H)
    (hv : v ≠ 0) :
    (‖v‖ ^ 2 : ℂ)⁻¹ • T.vectorFunctional v ∈ QuasiStateSpace A := by
  constructor
  · -- Positivity
    intro a ha
    change 0 ≤ (‖v‖ ^ 2 : ℂ)⁻¹ * T.vectorFunctional v a
    refine mul_nonneg ?_ (vectorFunctional_nonneg T v a ha)
    rw [← Complex.ofReal_pow, ← Complex.ofReal_inv]
    exact Complex.zero_le_real.mpr (by positivity)
  · -- Norm bound
    rw [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
    rw [map_smul, norm_smul]
    rw [norm_inv]
    simp only [Complex.norm_real, norm_pow, norm_norm]
    rw [← div_eq_inv_mul, div_le_iff₀ (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv)), one_mul]
    exact T.opNorm_vectorFunctional_le v


lemma trichotomy_from_purity {ψ : PureState A}
    (W : ClosedSubmodule ℂ (GNS.Representation.canonical ψ.toState).H)
    (hW : W ∈ (GNS.Representation.canonical ψ.toState).closedInvtSubmodule)
    (v₁ v₂ : (GNS.Representation.canonical ψ.toState).H) (hv₁ : v₁ ∈ W.toSubmodule)
    (hv₂ : v₂ ∈ W.toSubmoduleᗮ)
    (hξ : (GNS.Representation.canonical ψ.toState).ξ = v₁ + v₂) (horth : ⟪v₁, v₂⟫ = 0) :
    ‖v₁‖ ^ 2 = 0 ∨ ‖v₁‖ ^ 2 = 1 := by
  let T := GNS.Representation.canonical ψ.toState
  by_contra h_contra
  push Not at h_contra
  have h_in_Icc := norm_sq_in_Icc T v₁ v₂ hξ horth
  have h_pos : 0 < ‖v₁‖ ^ 2 := lt_of_le_of_ne h_in_Icc.1 h_contra.1.symm
  have h_lt_one : ‖v₁‖ ^ 2 < 1 := lt_of_le_of_ne h_in_Icc.2 h_contra.2
  have h_v₁_nz : v₁ ≠ 0 := by
    intro h
    simp [h] at h_pos
  have h_normsq_ne_c : (‖v₁‖ ^ 2 : ℂ) ≠ 0 := by
    have ht : ‖v₁‖ ^ 2 ≠ 0 := ne_of_gt h_pos
    exact_mod_cast ht
  set t := ‖v₁‖ ^ 2
  have h_norm_v₂ : ‖v₂‖ ^ 2 = 1 - t := by
    have h_sum := norm_sq_decomposition T v₁ v₂ hξ horth
    linarith
  have hv₂_ne : v₂ ≠ 0 := by
    intro h
    simp [h] at h_norm_v₂
    linarith
  set φ := (t : ℂ)⁻¹ • T.vectorFunctional v₁
  set χ := ((1 - t) : ℂ)⁻¹ • T.vectorFunctional v₂
  have hφ_mem : φ ∈ QuasiStateSpace A := by
    dsimp only [φ]
    -- Here `t = ‖v₁‖^2`, so the scalar matches definitionally after rewriting.
    convert normalized_vectorFunctional_mem_quasiStateSpace (T := T) (v := v₁) h_v₁_nz
    simp [t]
  have hχ_mem : χ ∈ QuasiStateSpace A := by
    dsimp only [χ]
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← h_norm_v₂]
    convert normalized_vectorFunctional_mem_quasiStateSpace T v₂ hv₂_ne
    simp
  have h_sum : ψ.val = (t : ℝ) • φ + (1 - t) • χ := by
    have ht_ne : t ≠ 0 := h_pos.ne'
    have ht_ne_c : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht_ne
    have h1_sub_t_ne : 1 - t ≠ 0 := (sub_pos.mpr h_lt_one).ne'
    have h1_sub_t_ne_c : (1 - (t : ℂ)) ≠ 0 := by
      have : ((1 - t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h1_sub_t_ne
      simpa only [Complex.ofReal_one, Complex.ofReal_sub] using this
    have ht_smul : (t : ℝ) • φ = (t : ℂ) • φ := by
      apply ContinuousLinearMap.ext; intro a; rfl
    have h1_smul : (1 - t : ℝ) • χ = (1 - (t : ℂ)) • χ := by
      -- First show (1 - t) • χ = ↑(1 - t) • χ
      have step1 : (1 - t : ℝ) • χ = ((1 - t : ℝ) : ℂ) • χ := by
        apply ContinuousLinearMap.ext; intro a; rfl
      -- Then rewrite ↑(1 - t) as (1 - ↑t)
      rw [step1, Complex.ofReal_sub, Complex.ofReal_one]
    have h_sum_c : ψ.val = (t : ℂ) • φ + (1 - (t : ℂ)) • χ := by
      apply ContinuousLinearMap.ext
      intro a
      have h_state := state_decomposition T W hW v₁ v₂ hv₁ hv₂ hξ a
      change ψ.toState a = _
      rw [h_state]
      -- Now everything is ℂ-linear, so `smul_apply` works and the normalizations cancel.
      have hrhs :
          ((t : ℂ) • φ + (1 - (t : ℂ)) • χ) a =
            (T.vectorFunctional v₁) a + (T.vectorFunctional v₂) a := by
        change (t : ℂ) • φ a + (1 - (t : ℂ)) • χ a = _
        dsimp only [φ, χ]
        rw [show ((t : ℂ)⁻¹ • T.vectorFunctional v₁) a
              = (t : ℂ)⁻¹ • (T.vectorFunctional v₁) a from rfl,
          show ((1 - (t : ℂ))⁻¹ • T.vectorFunctional v₂) a
              = (1 - (t : ℂ))⁻¹ • (T.vectorFunctional v₂) a from rfl]
        rw [smul_smul, smul_smul]
        rw [mul_inv_cancel₀ ht_ne_c, mul_inv_cancel₀ h1_sub_t_ne_c]
        rw [one_smul, one_smul]
      exact hrhs.symm
    have rhs_eq : (t : ℂ) • φ + (1 - (t : ℂ)) • χ = (t : ℝ) • φ + (1 - t) • χ := by
      rw [← ht_smul, ← h1_smul]
    exact h_sum_c.trans rhs_eq
  -- ψ is an extreme point
  exfalso
  have h_ext : ψ.val ∈ Set.extremePoints ℝ (QuasiStateSpace A) := ψ.property.1
  have h_t_in_Ioo : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨h_pos, h_lt_one⟩
  -- ψ.val ∈ openSegment ℝ χ φ
  have h_in_seg : ψ.val ∈ openSegment ℝ χ φ :=
    ⟨1 - t, t, sub_pos.mpr h_lt_one, h_pos, by ring, by rw [h_sum, add_comm]⟩
  have h_ext_iff := mem_extremePoints.mp h_ext
  obtain ⟨h_eq1, h_eq2⟩ := h_ext_iff.2 χ hχ_mem φ hφ_mem h_in_seg
  -- φ = χ implies contradiction
  have h_eq : φ = χ := by rw [h_eq2, ← h_eq1]
  -- Contradiction via density
  have h_dense : Dense (Set.range (T.orbit T.ξ)) := T.cyclic
  have hv₁_mem_closure : v₁ ∈ closure (Set.range (T.orbit T.ξ)) := by
    rw [h_dense.closure_eq]
    exact Set.mem_univ v₁
  set K : ℝ := t⁻¹ * ‖v₁‖ + (1 - t)⁻¹ * ‖v₂‖ with hKdef
  have hv₁_norm_pos : 0 < ‖v₁‖ := norm_pos_iff.mpr h_v₁_nz
  have hv₂_norm_pos : 0 < ‖v₂‖ := norm_pos_iff.mpr hv₂_ne
  have hK_pos : 0 < K := by
    have : 0 < t⁻¹ * ‖v₁‖ + (1 - t)⁻¹ * ‖v₂‖ := by
      apply add_pos
      · exact mul_pos (inv_pos.mpr h_pos) hv₁_norm_pos
      · exact mul_pos (inv_pos.mpr (by linarith)) hv₂_norm_pos
    simpa [hKdef] using this
  let ε := 1 / (2 * K)
  have h_eps_pos : 0 < ε := div_pos zero_lt_one (mul_pos two_pos hK_pos)
  obtain ⟨_, ⟨a, rfl⟩, ha⟩ : ∃ b ∈ Set.range (T.orbit T.ξ), dist v₁ b < ε :=
    Metric.mem_closure_iff.mp hv₁_mem_closure ε h_eps_pos
  rw [dist_comm, dist_eq_norm] at ha
  -- Analyze φ a and χ a
  have h_norm_diff : ‖(T.π a) v₁ - v₁‖ < ε := by
    have h_orth : ‖(T.π a) T.ξ - v₁‖ ^ 2 = ‖(T.π a) v₁ - v₁‖ ^ 2 + ‖(T.π a) v₂‖ ^ 2 := by
      have h_decomp : (T.π a) T.ξ - v₁ = ((T.π a) v₁ - v₁) + (T.π a) v₂ := by
        rw [hξ, map_add]
        abel
      rw [h_decomp]
      have h1 : (T.π a) v₁ - v₁ ∈ W.toSubmodule :=
        Submodule.sub_mem _ (CStarRep.apply_mem_of_mem_invtSubmodule hW a hv₁) hv₁
      have h2 : (T.π a) v₂ ∈ W.toSubmoduleᗮ :=
        CStarRep.apply_mem_of_mem_invtSubmodule (CStarRep.orthogonal_mem_invtSubmodule hW) a hv₂
      have h_pythag := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
        ((T.π a) v₁ - v₁) ((T.π a) v₂) ((Submodule.mem_orthogonal _ _).mp h2 _ h1)
      rw [← sq, ← sq, ← sq] at h_pythag
      exact h_pythag
    have h_sq_le : ‖(T.π a) v₁ - v₁‖ ^ 2 ≤ ‖(T.π a) T.ξ - v₁‖ ^ 2 := by
      rw [h_orth]; linarith [sq_nonneg ‖(T.π a) v₂‖]
    rw [sq_le_sq, abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at h_sq_le
    exact lt_of_le_of_lt h_sq_le ha
  have h_norm_v2 : ‖(T.π a) v₂‖ < ε := by
    have h_orth : ‖(T.π a) T.ξ - v₁‖ ^ 2 = ‖(T.π a) v₁ - v₁‖ ^ 2 + ‖(T.π a) v₂‖ ^ 2 := by
      have h_decomp : (T.π a) T.ξ - v₁ = ((T.π a) v₁ - v₁) + (T.π a) v₂ := by
        rw [hξ, map_add]
        abel
      rw [h_decomp]
      have h1 : (T.π a) v₁ - v₁ ∈ W.toSubmodule :=
        Submodule.sub_mem _ (CStarRep.apply_mem_of_mem_invtSubmodule hW a hv₁) hv₁
      have h2 : (T.π a) v₂ ∈ W.toSubmoduleᗮ :=
        CStarRep.apply_mem_of_mem_invtSubmodule (CStarRep.orthogonal_mem_invtSubmodule hW) a hv₂
      have h_pythag := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
        ((T.π a) v₁ - v₁) ((T.π a) v₂) ((Submodule.mem_orthogonal _ _).mp h2 _ h1)
      rw [← sq, ← sq, ← sq] at h_pythag
      exact h_pythag
    have h_sq_le : ‖(T.π a) v₂‖ ^ 2 ≤ ‖(T.π a) T.ξ - v₁‖ ^ 2 := by
      rw [h_orth]; linarith [sq_nonneg ‖(T.π a) v₁ - v₁‖]
    rw [sq_le_sq, abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at h_sq_le
    exact lt_of_le_of_lt h_sq_le ha
  -- Contradiction
  have h_phi : ‖φ a - 1‖ < 1/2 := by
    dsimp only [φ]
    change ‖(t : ℂ)⁻¹ • (T.vectorFunctional v₁) a - 1‖ < 1/2
    have : (t : ℂ)⁻¹ • T.vectorFunctional v₁ a - 1 = (t : ℂ)⁻¹ * ⟪v₁, (T.π a) v₁ - v₁⟫ := by
      have ht_ne_c : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h_pos.ne'
      rw [vectorFunctional_apply]
      simp only [smul_eq_mul]
      -- Rewrite the difference using `inner_sub_right` and `⟪v₁,v₁⟫ = ‖v₁‖²`.
      calc
        (t : ℂ)⁻¹ * ⟪v₁, (T.π a) v₁⟫ - 1
            = (t : ℂ)⁻¹ * ⟪v₁, (T.π a) v₁⟫ - (t : ℂ)⁻¹ * (t : ℂ) := by
                rw [inv_mul_cancel₀ ht_ne_c]
        _ = (t : ℂ)⁻¹ * (⟪v₁, (T.π a) v₁⟫ - (t : ℂ)) := by
                exact (mul_sub (a := (t : ℂ)⁻¹) ⟪v₁, (T.π a) v₁⟫ (t : ℂ)).symm
        _ = (t : ℂ)⁻¹ * (⟪v₁, (T.π a) v₁⟫ - ⟪v₁, v₁⟫) := by
                simp [inner_self_eq_norm_sq_to_K, t]
        _ = (t : ℂ)⁻¹ * ⟪v₁, (T.π a) v₁ - v₁⟫ := by
                simp [inner_sub_right]
    rw [this, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h_pos]
    calc t⁻¹ * ‖⟪v₁, (T.π a) v₁ - v₁⟫‖
      _ ≤ t⁻¹ * (‖v₁‖ * ‖(T.π a) v₁ - v₁‖) := by
        apply mul_le_mul_of_nonneg_left
        · exact norm_inner_le_norm _ _
        · exact inv_nonneg.mpr (le_of_lt h_pos)
      _ < t⁻¹ * (‖v₁‖ * ε) := by
        apply mul_lt_mul_of_pos_left
        · apply mul_lt_mul_of_pos_left h_norm_diff hv₁_norm_pos
        · exact inv_pos.mpr h_pos
      _ = ε * (t⁻¹ * ‖v₁‖) := by ring
      _ ≤ ε * K := by
        gcongr; apply le_add_of_nonneg_right
        apply mul_nonneg (inv_nonneg.mpr (by linarith)) (norm_nonneg _)
      _ = 1/2 := by
        dsimp [ε]
        have hK_ne : K ≠ 0 := hK_pos.ne'
        have h2K_ne : (2 * K) ≠ 0 := mul_ne_zero (by norm_num) hK_ne
        calc
          1 / (2 * K) * K = (2 * K)⁻¹ * K := by simp [div_eq_mul_inv]
          _ = (2 * K)⁻¹ * ((2 * K) * (1 / 2)) := by ring
          _ = ((2 * K)⁻¹ * (2 * K)) * (1 / 2) := by ring
          _ = (1 : ℝ) * (1 / 2) := by
            rw [inv_mul_cancel₀ h2K_ne]
          _ = 1 / 2 := by simp
  have h_chi : ‖χ a‖ < 1/2 := by
    dsimp only [χ]
    change ‖(1 - (t : ℂ))⁻¹ • (T.vectorFunctional v₂) a‖ < 1/2
    rw [vectorFunctional_apply, smul_eq_mul]
    rw [norm_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith : 0 < 1 - t)]
    calc (1 - t)⁻¹ * ‖⟪v₂, (T.π a) v₂⟫‖
      _ ≤ (1 - t)⁻¹ * (‖v₂‖ * ‖(T.π a) v₂‖) := by
        apply mul_le_mul_of_nonneg_left
        · exact norm_inner_le_norm _ _
        · exact inv_nonneg.mpr (by linarith)
      _ < (1 - t)⁻¹ * (‖v₂‖ * ε) := by
        apply mul_lt_mul_of_pos_left
        · apply mul_lt_mul_of_pos_left h_norm_v2 hv₂_norm_pos
        · exact inv_pos.mpr (by linarith)
      _ = ε * ((1 - t)⁻¹ * ‖v₂‖) := by ring
      _ ≤ ε * K := by
        gcongr; apply le_add_of_nonneg_left
        apply mul_nonneg (inv_nonneg.mpr (by linarith)) (norm_nonneg _)
      _ = 1/2 := by
        dsimp [ε]
        have hK_ne : K ≠ 0 := hK_pos.ne'
        have h2K_ne : (2 * K) ≠ 0 := mul_ne_zero (by norm_num) hK_ne
        calc
          1 / (2 * K) * K = (2 * K)⁻¹ * K := by simp [div_eq_mul_inv]
          _ = (2 * K)⁻¹ * ((2 * K) * (1 / 2)) := by ring
          _ = ((2 * K)⁻¹ * (2 * K)) * (1 / 2) := by ring
          _ = (1 : ℝ) * (1 / 2) := by
            rw [inv_mul_cancel₀ h2K_ne]
          _ = 1 / 2 := by simp
  have h_eq_val : φ a = χ a := by rw [h_eq]
  have : (1 : ℝ) < 1 := calc
    (1 : ℝ) = ‖(1 : ℂ)‖ := by simp
    _ = ‖(1 - φ a) + φ a‖ := by ring_nf
    _ ≤ ‖1 - φ a‖ + ‖φ a‖ := norm_add_le _ _
    _ = ‖φ a - 1‖ + ‖χ a‖ := by rw [norm_sub_rev, h_eq_val]
    _ < 1/2 + 1/2 := add_lt_add h_phi h_chi
    _ = 1 := by norm_num
  exact lt_irrefl 1 this


lemma mem_of_norm_sq_eq_one (T : GNS.Representation ω) (v₁ v₂ : T.H)
    (hξ : T.ξ = v₁ + v₂) (horth : ⟪v₁, v₂⟫ = 0) (h : ‖v₁‖ ^ 2 = 1) :
    v₂ = 0 := by
  have h_sum := norm_sq_decomposition T v₁ v₂ hξ horth
  rw [h] at h_sum
  have : ‖v₂‖ ^ 2 = 0 := by linarith
  have : ‖v₂‖ = 0 := by nlinarith [sq_nonneg ‖v₂‖]
  exact norm_eq_zero.mp this

lemma mem_of_norm_sq_eq_zero (T : GNS.Representation ω) (v₁ : T.H)
    (h : ‖v₁‖ ^ 2 = 0) :
    v₁ = 0 := by
  have : ‖v₁‖ = 0 := by
    have := sq_nonneg ‖v₁‖
    nlinarith [sq_nonneg ‖v₁‖]
  exact norm_eq_zero.mp this

/-- If the component of `ξ` in a closed invariant submodule `W` has norm one, then `W = ⊤`:
`ξ ∈ W`, so `W` contains the dense orbit of `ξ`. -/
lemma eq_top_of_norm_sq_eq_one (T : GNS.Representation ω) (W : ClosedSubmodule ℂ T.H)
    (hW : W ∈ T.closedInvtSubmodule) (v₁ v₂ : T.H) (hv₁ : v₁ ∈ W.toSubmodule)
    (hξ : T.ξ = v₁ + v₂) (horth : ⟪v₁, v₂⟫ = 0) (h : ‖v₁‖ ^ 2 = 1) :
    W = ⊤ := by
  have hv₂_zero := mem_of_norm_sq_eq_one T v₁ v₂ hξ horth h
  have hξ_in_W : T.ξ ∈ W.toSubmodule := by rw [hξ, hv₂_zero, add_zero]; exact hv₁
  -- `W` is closed and contains the dense orbit of `ξ`, so it is everything.
  have h_orbit_le : Set.range (T.orbit T.ξ) ⊆ W := by
    rintro _ ⟨a, rfl⟩
    exact CStarRep.apply_mem_of_mem_invtSubmodule hW a hξ_in_W
  exact eq_top_iff.mpr fun x _ => closure_minimal h_orbit_le W.isClosed (T.cyclic x)

/-- If the component of `ξ` in a closed invariant submodule `W` vanishes, then `W = ⊥`:
`ξ ∈ Wᗮ`, so the closed invariant submodule `Wᗮ` contains the dense orbit of `ξ`. -/
lemma eq_bot_of_norm_sq_eq_zero (T : GNS.Representation ω) (W : ClosedSubmodule ℂ T.H)
    (hW : W ∈ T.closedInvtSubmodule) (v₁ v₂ : T.H) (hv₂ : v₂ ∈ W.toSubmoduleᗮ)
    (hξ : T.ξ = v₁ + v₂) (h : ‖v₁‖ ^ 2 = 0) :
    W = ⊥ := by
  have hv₁_zero : v₁ = 0 := mem_of_norm_sq_eq_zero T v₁ h
  have hξ_in_Wperp : T.ξ ∈ W.toSubmoduleᗮ := by rw [hξ, hv₁_zero, zero_add]; exact hv₂
  have hWperp_inv := CStarRep.orthogonal_mem_invtSubmodule (R := T.toCStarRep) hW
  -- `Wᗮ` is closed and contains the dense orbit of `ξ`, so it is everything.
  have h_orbit_le : Set.range (T.orbit T.ξ) ⊆ W.toSubmoduleᗮ := by
    rintro _ ⟨a, rfl⟩
    exact CStarRep.apply_mem_of_mem_invtSubmodule hWperp_inv a hξ_in_Wperp
  have : W.toSubmoduleᗮ = ⊤ := eq_top_iff.mpr fun x _ =>
    closure_minimal h_orbit_le (Submodule.isClosed_orthogonal _) (T.cyclic x)
  rw [Submodule.orthogonal_eq_top_iff] at this
  exact ClosedSubmodule.toSubmodule_injective this

/-- **Main Theorem**: The GNS representation of a pure state is irreducible. -/
theorem pureState_gns_isIrreducible {ψ : PureState A} :
    (GNS.Representation.canonical ψ.toState).IsIrreducible := by
  let T := GNS.Representation.canonical ψ.toState
  refine ⟨T.π_ne_zero, fun W hW => ?_⟩
  obtain ⟨v₁, v₂, hv₁, hv₂, hξ, horth⟩ := cyclicVector_decomp T W
  rcases trichotomy_from_purity W hW v₁ v₂ hv₁ hv₂ hξ horth with h_zero | h_one
  · exact Or.inl (eq_bot_of_norm_sq_eq_zero T W hW v₁ v₂ hv₂ hξ h_zero)
  · exact Or.inr (eq_top_of_norm_sq_eq_one T W hW v₁ v₂ hv₁ hξ horth h_one)

end Representation

end GNS
