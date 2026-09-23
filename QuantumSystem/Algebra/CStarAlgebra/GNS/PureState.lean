/-
Copyright (c) 2025 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Algebra.CStarAlgebra.GNS.Representation
public import QuantumSystem.Algebra.CStarAlgebra.PureState
public import QuantumSystem.Algebra.CStarAlgebra.Representation.VectorFunctional

/-!
# Irreducibility of the GNS representation of a pure state

For a pure state `ψ`, the canonical GNS representation
`GNS.Representation.canonical ψ.toState.toPositiveLinearMap` is
irreducible (`GNS.Representation.pureState_gns_isIrreducible`): a closed invariant subspace
splits the cyclic vector, the two pieces define quasi-states summing to `ψ`, and purity forces
one of them to vanish.

The splitting of the cyclic vector holds for a GNS triplet of any positive functional `f`: along
a closed invariant submodule `W`, `ξ = v₁ + v₂` with `v₁ ∈ W`, `v₂ ∈ Wᗮ`, `f` is the sum of the
vector functionals of `v₁` and `v₂` (`CStarRep.vectorFunctional`), `‖v₁‖² + ‖v₂‖² = ‖f‖ₒₚ`, and
`W = ⊥` or `W = ⊤` when `‖v₁‖²` is `0` or `‖f‖ₒₚ`.  Purity is used only in
`trichotomy_from_purity`.
-/

@[expose] public section

namespace GNS

namespace Representation

open scoped ComplexOrder ComplexConjugate CStarAlgebra InnerProduct NNReal ComplexHilbertSpace
open PositiveLinearMap

local notation "⟪" x ", " y "⟫" => inner ℂ x y

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {f : A →ₚ[ℂ] ℂ}

/-- The cyclic vector splits along a closed submodule `W` and its orthogonal complement. -/
lemma cyclicVector_decomp (T : Representation f) (W : ClosedSubmodule ℂ T.H) :
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

/-- Along a closed invariant submodule `W`, the functional splits as the sum of the vector
functionals of the two components `v₁ ∈ W`, `v₂ ∈ Wᗮ` of the cyclic vector. -/
lemma apply_eq_vectorFunctional_add (T : Representation f) (W : ClosedSubmodule ℂ T.H)
    (hW : W ∈ T.closedInvtSubmodule) (v₁ v₂ : T.H) (hv₁ : v₁ ∈ W.toSubmodule)
    (hv₂ : v₂ ∈ W.toSubmoduleᗮ) (hξ : T.ξ = v₁ + v₂) (a : A) :
    f a = T.vectorFunctional v₁ a + T.vectorFunctional v₂ a := by
  rw [T.gns_condition, ← CStarRep.vectorFunctional_apply, hξ,
    CStarRep.vectorFunctional_add_of_mem_orthogonal _ hW hv₁ hv₂]
  rfl

/-- Pythagoras for the two components of the cyclic vector: `‖v₁‖² + ‖v₂‖² = ‖f‖ₒₚ`. -/
lemma norm_sq_decomposition (T : Representation f) (v₁ v₂ : T.H) (hξ : T.ξ = v₁ + v₂)
    (horth : ⟪v₁, v₂⟫ = 0) :
    ‖v₁‖ ^ 2 + ‖v₂‖ ^ 2 = ‖f‖ₒₚ := by
  rw [← T.norm_ξ_sq, hξ]
  simpa [sq] using (norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero v₁ v₂ horth).symm

/-- The squared norm of a component of the cyclic vector lies in `[0, ‖f‖ₒₚ]`. -/
lemma norm_sq_in_Icc (T : Representation f) (v₁ v₂ : T.H) (hξ : T.ξ = v₁ + v₂)
    (horth : ⟪v₁, v₂⟫ = 0) :
    ‖v₁‖ ^ 2 ∈ Set.Icc (0 : ℝ) ‖f‖ₒₚ := by
  have h := norm_sq_decomposition T v₁ v₂ hξ horth
  exact ⟨sq_nonneg _, by linarith [sq_nonneg ‖v₂‖]⟩

lemma trichotomy_from_purity {ψ : PureState A}
    (W : ClosedSubmodule ℂ (GNS.Representation.canonical ψ.toState.toPositiveLinearMap).H)
    (hW : W ∈ (GNS.Representation.canonical ψ.toState.toPositiveLinearMap).closedInvtSubmodule)
    (v₁ v₂ : (GNS.Representation.canonical ψ.toState.toPositiveLinearMap).H)
    (hv₁ : v₁ ∈ W.toSubmodule)
    (hv₂ : v₂ ∈ W.toSubmoduleᗮ)
    (hξ : (GNS.Representation.canonical ψ.toState.toPositiveLinearMap).ξ = v₁ + v₂)
    (horth : ⟪v₁, v₂⟫ = 0) :
    ‖v₁‖ ^ 2 = 0 ∨ ‖v₁‖ ^ 2 = 1 := by
  let T := GNS.Representation.canonical ψ.toState.toPositiveLinearMap
  by_contra h_contra
  push Not at h_contra
  have hψ : ‖ψ.toState.toPositiveLinearMap‖ₒₚ = 1 := ψ.toState.norm_eq_one
  have h_in_Icc := hψ ▸ norm_sq_in_Icc T v₁ v₂ hξ horth
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
    have h_sum := hψ ▸ norm_sq_decomposition T v₁ v₂ hξ horth
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
    convert T.normalized_vectorFunctional_mem_quasiStateSpace (v := v₁) h_v₁_nz
    simp [t]
  have hχ_mem : χ ∈ QuasiStateSpace A := by
    dsimp only [χ]
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← h_norm_v₂]
    convert T.normalized_vectorFunctional_mem_quasiStateSpace v₂ hv₂_ne
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
      have h_state := apply_eq_vectorFunctional_add T W hW v₁ v₂ hv₁ hv₂ hξ a
      change ψ.toState.toPositiveLinearMap a = _
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
      rw [CStarRep.vectorFunctional_apply]
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
    rw [CStarRep.vectorFunctional_apply, smul_eq_mul]
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


/-- If one component of the cyclic vector carries the whole norm, `‖v₁‖² = ‖f‖ₒₚ`, the other
vanishes. -/
lemma eq_zero_of_norm_sq_eq_opNorm (T : Representation f) (v₁ v₂ : T.H)
    (hξ : T.ξ = v₁ + v₂) (horth : ⟪v₁, v₂⟫ = 0) (h : ‖v₁‖ ^ 2 = ‖f‖ₒₚ) :
    v₂ = 0 := by
  have h_sum := norm_sq_decomposition T v₁ v₂ hξ horth
  rw [h] at h_sum
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (by linarith))

/-- If the component of `ξ` in a closed invariant submodule `W` carries the whole norm,
`‖v₁‖² = ‖f‖ₒₚ`, then `W = ⊤`: `ξ ∈ W`, so `W` contains the dense orbit of `ξ`. -/
lemma eq_top_of_norm_sq_eq_opNorm (T : Representation f)
    (W : ClosedSubmodule ℂ T.H)
    (hW : W ∈ T.closedInvtSubmodule) (v₁ v₂ : T.H) (hv₁ : v₁ ∈ W.toSubmodule)
    (hξ : T.ξ = v₁ + v₂) (horth : ⟪v₁, v₂⟫ = 0) (h : ‖v₁‖ ^ 2 = ‖f‖ₒₚ) :
    W = ⊤ := by
  have hv₂_zero := eq_zero_of_norm_sq_eq_opNorm T v₁ v₂ hξ horth h
  have hξ_in_W : T.ξ ∈ W.toSubmodule := by rw [hξ, hv₂_zero, add_zero]; exact hv₁
  -- `W` is closed and contains the dense orbit of `ξ`, so it is everything.
  have h_orbit_le : Set.range (T.orbit T.ξ) ⊆ W := by
    rintro _ ⟨a, rfl⟩
    exact CStarRep.apply_mem_of_mem_invtSubmodule hW a hξ_in_W
  exact eq_top_iff.mpr fun x _ => closure_minimal h_orbit_le W.isClosed (T.cyclic x)

/-- If the component of `ξ` in a closed invariant submodule `W` vanishes, then `W = ⊥`:
`ξ ∈ Wᗮ`, so the closed invariant submodule `Wᗮ` contains the dense orbit of `ξ`. -/
lemma eq_bot_of_norm_sq_eq_zero (T : Representation f)
    (W : ClosedSubmodule ℂ T.H)
    (hW : W ∈ T.closedInvtSubmodule) (v₁ v₂ : T.H) (hv₂ : v₂ ∈ W.toSubmoduleᗮ)
    (hξ : T.ξ = v₁ + v₂) (h : ‖v₁‖ ^ 2 = 0) :
    W = ⊥ := by
  have hv₁_zero : v₁ = 0 := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h)
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
    (GNS.Representation.canonical ψ.toState.toPositiveLinearMap).IsIrreducible := by
  let T := GNS.Representation.canonical ψ.toState.toPositiveLinearMap
  refine ⟨T.π_ne_zero ψ.toState.toPositiveLinearMap_ne_zero, fun W hW => ?_⟩
  obtain ⟨v₁, v₂, hv₁, hv₂, hξ, horth⟩ := cyclicVector_decomp T W
  rcases trichotomy_from_purity W hW v₁ v₂ hv₁ hv₂ hξ horth with h_zero | h_one
  · exact Or.inl (eq_bot_of_norm_sq_eq_zero T W hW v₁ v₂ hv₂ hξ h_zero)
  · exact Or.inr (eq_top_of_norm_sq_eq_opNorm T W hW v₁ v₂ hv₁ hξ horth
      (h_one.trans ψ.toState.norm_eq_one.symm))

end Representation

end GNS
