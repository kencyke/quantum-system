import QuantumSystem.Algebra.CStarAlgebra.GNS.Representation
import QuantumSystem.Algebra.CStarAlgebra.PureState


namespace PureState

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- For each pure state, we get a canonical GNS representation. -/
noncomputable def gnsRepresentation (ψ : PureState A) : GNS.Representation (ψ.toState) :=
  GNS.Representation.canonical

end PureState

namespace GNS

namespace Representation

open scoped ComplexConjugate CStarAlgebra InnerProduct NNReal

local notation "⟪" x ", " y "⟫" => inner ℂ x y

variable {A : Type*} [NonUnitalCStarAlgebra A]

variable {ω : State ℂ A}

private lemma pi_adjoint (T : GNS.Representation ω) (a : A) :
    (T.π a)† = T.π (star a) := by
  -- `π(star a) = star (π a)` and `star = adjoint` on `𝓑(H)`.
  have h : T.π (star a) = star (T.π a) := by
    simpa using (T.π.map_star' a)
  -- Rewrite `star` as `adjoint`.
  -- Here `star_eq_adjoint` is expressed using the `†` notation.
  have hstar : star (T.π a) = (T.π a)† := by
    simpa using (ContinuousLinearMap.star_eq_adjoint (A := T.π a))
  -- Combine and flip.
  -- `T.π (star a) = star (T.π a) = (T.π a)†`.
  simpa [hstar] using h.symm

/-- For a *-representation, invariance of `W` implies invariance of `Wᗮ`.

This is the standard Hilbert-space argument using adjoints. -/
lemma isInvariant_orthogonal (T : GNS.Representation ω) (W : Submodule ℂ T.H)
    (hWinv : T.IsInvariant W) :
    T.IsInvariant Wᗮ := by
  intro a y hy
  -- Unfold `Submodule.map` membership: it suffices to show `x ∈ Wᗮ → π(a)x ∈ Wᗮ`.
  rcases hy with ⟨x, hx, rfl⟩
  -- Show `π(a) x ∈ Wᗮ` by the defining orthogonality condition.
  refine (W.mem_orthogonal ((T.π a) x)).2 ?_
  intro w hw
  have hw_map : (T.π (star a)) w ∈ W.map (T.π (star a)) :=
    ⟨w, hw, rfl⟩
  have hw' : (T.π (star a)) w ∈ W := (hWinv (star a)) hw_map
  have hx0 : ⟪(T.π (star a)) w, x⟫ = 0 := by
    -- `x ∈ Wᗮ` means it is orthogonal to every element of `W`.
    exact Submodule.inner_right_of_mem_orthogonal hw' hx
  -- Rewrite `⟪w, π(a) x⟫` using the adjoint.
  calc
    ⟪w, (T.π a) x⟫ = ⟪((T.π a)†) w, x⟫ := by
      -- `⟪(A†) w, x⟫ = ⟪w, A x⟫`
      simpa using (ContinuousLinearMap.adjoint_inner_left (A := (T.π a)) (x := x) (y := w)).symm
    _ = ⟪(T.π (star a)) w, x⟫ := by
      simp [pi_adjoint (T := T) (a := a)]
    _ = 0 := hx0

lemma inner_left_mem_right_pi_mem_orthogonal (T : GNS.Representation ω) (W : Submodule ℂ T.H)
    (hWinv : T.IsInvariant W) (a : A) {w x : T.H} (hw : w ∈ W) (hx : x ∈ Wᗮ) :
    ⟪w, (T.π a) x⟫ = 0 := by
  have hWperpInv : T.IsInvariant Wᗮ := isInvariant_orthogonal (T := T) (W := W) hWinv
  have hx_map : (T.π a) x ∈ Wᗮ := by
    exact (hWperpInv a) ⟨x, hx, rfl⟩
  exact Submodule.inner_right_of_mem_orthogonal hw hx_map

lemma inner_left_mem_orthogonal_right_pi_mem (T : GNS.Representation ω) (W : Submodule ℂ T.H)
    (hWinv : T.IsInvariant W) (a : A) {w x : T.H} (hx : x ∈ Wᗮ) (hw : w ∈ W) :
    ⟪x, (T.π a) w⟫ = 0 := by
  have hw_map : (T.π a) w ∈ W := by
    exact (hWinv a) ⟨w, hw, rfl⟩
  have h0 : ⟪(T.π a) w, x⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hw_map hx
  exact (inner_eq_zero_symm (x := x) (y := (T.π a) w)).2 h0

lemma cyclicVector_decomp_of_isClosed (T : GNS.Representation ω) (W : Submodule ℂ T.H)
    (hWclosed : IsClosed (W : Set T.H)) :
    ∃ v₁ v₂ : T.H, v₁ ∈ W ∧ v₂ ∈ Wᗮ ∧ T.ξ = v₁ + v₂ ∧ ⟪v₁, v₂⟫ = 0 := by
  classical
  -- Use closedness to obtain orthogonal projections onto `W`.
  letI : IsClosed (W : Set T.H) := hWclosed
  haveI : CompleteSpace (↥W) := by
    -- Closed subsets of complete spaces are complete.
    simpa using (IsClosed.completeSpace_coe (s := (W : Set T.H)))
  haveI : W.HasOrthogonalProjection := by
    -- Uses `HasOrthogonalProjection.ofCompleteSpace`.
    infer_instance

  refine ⟨W.starProjection T.ξ, T.ξ - W.starProjection T.ξ, ?_, ?_, ?_, ?_⟩
  · exact Submodule.starProjection_apply_mem (U := W) (x := T.ξ)
  · exact Submodule.sub_starProjection_mem_orthogonal (K := W) (v := T.ξ)
  · simp [add_sub_cancel]
  ·
    exact Submodule.inner_right_of_mem_orthogonal
      (Submodule.starProjection_apply_mem (U := W) (x := T.ξ))
      (Submodule.sub_starProjection_mem_orthogonal (K := W) (v := T.ξ))


noncomputable def pi_apply (T : GNS.Representation ω) (v : T.H) : A →L[ℂ] T.H :=
  (LinearMap.mkContinuous
    { toFun := fun a => (T.π a) v
      map_add' := by
        intro a b
        simp [map_add, ContinuousLinearMap.add_apply]
      map_smul' := by
        intro c a
        simp [map_smul, ContinuousLinearMap.smul_apply] }
    ‖v‖
    (by
      intro a
      -- `‖π(a) v‖ ≤ ‖π(a)‖ ‖v‖ ≤ ‖a‖ ‖v‖`.
      have h₁ : ‖(T.π a) v‖ ≤ ‖T.π a‖ * ‖v‖ := by
        exact (T.π a).le_opNorm v
      have h₂ : ‖T.π a‖ ≤ ‖a‖ := by
        -- norm-contractivity of *-homomorphisms between C⋆-algebras
        exact NonUnitalStarAlgHom.norm_apply_le (φ := T.π) a
      have h₃ : ‖T.π a‖ * ‖v‖ ≤ ‖a‖ * ‖v‖ := by
        gcongr
      exact (h₁.trans h₃).trans_eq (by ac_rfl)))

@[simp]
lemma pi_apply_apply (T : GNS.Representation ω) (v : T.H) (a : A) :
    (T.pi_apply v) a = (T.π a) v := rfl

noncomputable def vectorFunctional (T : GNS.Representation ω) (v : T.H) : WeakDual ℂ A :=
  (innerSL ℂ v).comp (T.pi_apply v)

@[simp]
lemma vectorFunctional_apply (T : GNS.Representation ω) (v : T.H) (a : A) :
    T.vectorFunctional v a = ⟪v, (T.π a) v⟫ := by
  rfl

lemma vectorFunctional_isPositive (T : GNS.Representation ω) (v : T.H) :
    IsPositive A (T.vectorFunctional v) := by
  intro a
  refine ⟨⟨‖(T.π a) v‖ ^ 2, sq_nonneg _⟩, ?_⟩
  -- `⟪v, π(star a * a) v⟫ = ⟪π(a)v, π(a)v⟫ = ‖π(a)v‖^2`.
  have hmul : T.π (star a * a) = (T.π (star a)) * (T.π a) :=
    T.π.map_mul' (star a) a
  have h : T.vectorFunctional v (star a * a) = RCLike.ofReal (‖(T.π a) v‖ ^ 2) := by
    calc
      T.vectorFunctional v (star a * a) = ⟪v, (T.π (star a * a)) v⟫ := by
        simp [vectorFunctional_apply]
      _ = ⟪v, ((T.π (star a)) * (T.π a)) v⟫ := by
        simp [hmul]
      _ = ⟪v, (T.π (star a)) ((T.π a) v)⟫ := by
        rfl
      _ = ⟪v, ((T.π a)†) ((T.π a) v)⟫ := by
        simp [pi_adjoint (T := T) (a := a)]
      _ = ⟪(T.π a) v, (T.π a) v⟫ := by
        -- `⟪v, A† (A v)⟫ = ⟪A v, A v⟫`.
        exact
          (ContinuousLinearMap.adjoint_inner_right (A := (T.π a)) (x := v) (y := (T.π a) v))
      _ = (‖(T.π a) v‖ : ℂ) ^ 2 := by
        simp
      _ = RCLike.ofReal (‖(T.π a) v‖ ^ 2) := by
        -- `((r : ℂ)^2) = ofReal (r^2)` for real `r`.
        rw [RCLike.ofReal_eq_complex_ofReal]
        exact (Complex.ofReal_pow ‖(T.π a) v‖ 2).symm
  -- Convert the RHS into the form expected by `IsPositive` (with an `ℝ≥0` witness).
  simp [h]

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


lemma state_decomposition (T : GNS.Representation ω) (W : Submodule ℂ T.H)
    (hWinv : T.IsInvariant W) (v₁ v₂ : T.H) (hv₁ : v₁ ∈ W) (hv₂ : v₂ ∈ Wᗮ)
    (hξ : T.ξ = v₁ + v₂) (a : A) :
    ω a = T.vectorFunctional v₁ a + T.vectorFunctional v₂ a := by
  rw [T.gns_condition, hξ]
  simp only [vectorFunctional_apply]
  have : (T.π a) (v₁ + v₂) = (T.π a) v₁ + (T.π a) v₂ := by
    exact ContinuousLinearMap.map_add (T.π a) v₁ v₂
  rw [this, inner_add_left, inner_add_right, inner_add_right]
  have h₁ : ⟪v₁, (T.π a) v₂⟫ = 0 :=
    inner_left_mem_right_pi_mem_orthogonal T W hWinv a hv₁ hv₂
  have h₂ : ⟪v₂, (T.π a) v₁⟫ = 0 :=
    inner_left_mem_orthogonal_right_pi_mem T W hWinv a hv₂ hv₁
  simp [h₁, h₂]

lemma norm_sq_decomposition (T : GNS.Representation ω) (v₁ v₂ : T.H) (hξ : T.ξ = v₁ + v₂)
    (horth : ⟪v₁, v₂⟫ = 0) :
    ‖v₁‖ ^ 2 + ‖v₂‖ ^ 2 = 1 := by
  have h₁ : ‖T.ξ‖ ^ 2 = ‖v₁ + v₂‖ ^ 2 := by rw [hξ]
  rw [T.unit_norm, one_pow] at h₁
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
  · exact vectorFunctional_isPositive T v
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
    have hpos := vectorFunctional_isPositive T v
    let c : ℝ≥0 := ⟨(‖v‖ ^ 2)⁻¹, inv_nonneg.mpr (sq_nonneg _)⟩
    have : (‖v‖ ^ 2 : ℂ)⁻¹ = (c : ℂ) := by simp [c, Complex.ofReal_inv]
    rw [this]
    change _ ∈ {φ | IsPositive A φ}
    have h_smul : (c : ℂ) • T.vectorFunctional v = c • T.vectorFunctional v := by
      apply ContinuousLinearMap.ext
      intro x
      simp
      rfl
    rw [h_smul]
    exact IsPositive.smul A hpos
  · -- Norm bound
    rw [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
    rw [map_smul, norm_smul]
    rw [norm_inv]
    simp only [Complex.norm_real, norm_pow, norm_norm]
    rw [← div_eq_inv_mul, div_le_iff₀ (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv)), one_mul]
    exact T.opNorm_vectorFunctional_le v


lemma trichotomy_from_purity {ψ : PureState A}
    (W : Submodule ℂ (PureState.gnsRepresentation ψ).H) (hWinv : (PureState.gnsRepresentation ψ).IsInvariant W) (_hWclosed : IsClosed (W : Set (PureState.gnsRepresentation ψ).H))
    (v₁ v₂ : (PureState.gnsRepresentation ψ).H) (hv₁ : v₁ ∈ W) (hv₂ : v₂ ∈ Wᗮ) (hξ : (PureState.gnsRepresentation ψ).ξ = v₁ + v₂) (horth : ⟪v₁, v₂⟫ = 0) :
    ‖v₁‖ ^ 2 = 0 ∨ ‖v₁‖ ^ 2 = 1 := by
  let T := PureState.gnsRepresentation ψ
  by_contra h_contra
  push_neg at h_contra
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
      simp [Complex.ofReal_one, Complex.ofReal_sub] at this
      exact this
    have ht_smul : (t : ℝ) • φ = (t : ℂ) • φ :=
      RCLike.real_smul_eq_coe_smul (K := ℂ) (E := WeakDual ℂ A) t φ
    have h1_smul : (1 - t : ℝ) • χ = (1 - (t : ℂ)) • χ := by
      -- First use RCLike lemma to get (1 - t) • χ = ↑(1 - t) • χ
      have step1 : (1 - t : ℝ) • χ = ((1 - t : ℝ) : ℂ) • χ :=
        RCLike.real_smul_eq_coe_smul (K := ℂ) (E := WeakDual ℂ A) (1 - t) χ
      -- Then rewrite ↑(1 - t) as (1 - ↑t)
      rw [step1, Complex.ofReal_sub, Complex.ofReal_one]

    have h_sum_c : ψ.val = (t : ℂ) • φ + (1 - (t : ℂ)) • χ := by
      apply ContinuousLinearMap.ext
      intro a
      have h_state := state_decomposition T W hWinv v₁ v₂ hv₁ hv₂ hξ a
      change ψ.toState a = _
      rw [h_state]
      -- Now everything is ℂ-linear, so `smul_apply` works and the normalizations cancel.
      have hrhs :
          ((t : ℂ) • φ + (1 - (t : ℂ)) • χ) a =
            (T.vectorFunctional v₁) a + (T.vectorFunctional v₂) a := by
        rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply]
        dsimp only [φ, χ]
        rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply]
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
  have h_in_seg : ψ.val ∈ openSegment ℝ χ φ := by
    rw [openSegment_eq_image, Set.mem_image]
    use t
    constructor
    · exact h_t_in_Ioo
    · simp [h_sum, sub_eq_add_neg]
      rw [add_comm]
  have h_ext_iff := mem_extremePoints.mp h_ext
  obtain ⟨h_eq1, h_eq2⟩ := h_ext_iff.2 χ hχ_mem φ hφ_mem h_in_seg
  -- φ = χ implies contradiction
  have h_eq : φ = χ := by rw [h_eq2, ← h_eq1]
  -- Contradiction via density
  have h_dense : Dense (Set.range (fun a => (T.π a) T.ξ)) := by
    change Dense (Set.range (T.pi_apply T.ξ))
    rw [← LinearMap.coe_range]
    rw [← Submodule.span_eq (LinearMap.range (T.pi_apply T.ξ))]
    exact T.cyclic
  have hv₁_mem_closure : v₁ ∈ closure (Set.range (fun a => (T.π a) T.ξ)) := by
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
  obtain ⟨_, ⟨a, rfl⟩, ha⟩ : ∃ b ∈ Set.range (fun a => (T.π a) T.ξ), dist v₁ b < ε :=
    Metric.mem_closure_iff.mp hv₁_mem_closure ε h_eps_pos
  rw [dist_comm, dist_eq_norm] at ha
  -- Analyze φ a and χ a
  have h_norm_diff : ‖(T.π a) v₁ - v₁‖ < ε := by
    have h_orth : ‖(T.π a) T.ξ - v₁‖ ^ 2 = ‖(T.π a) v₁ - v₁‖ ^ 2 + ‖(T.π a) v₂‖ ^ 2 := by
      have h_decomp : (T.π a) T.ξ - v₁ = ((T.π a) v₁ - v₁) + (T.π a) v₂ := by
        rw [hξ, map_add]
        abel
      rw [h_decomp]
      have h1 : (T.π a) v₁ - v₁ ∈ W := Submodule.sub_mem W (hWinv a ⟨v₁, hv₁, rfl⟩) hv₁
      have h2 : (T.π a) v₂ ∈ Wᗮ := isInvariant_orthogonal T W hWinv a ⟨v₂, hv₂, rfl⟩
      have h_pythag := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero ((T.π a) v₁ - v₁) ((T.π a) v₂) ((Submodule.mem_orthogonal W _).mp h2 _ h1)
      rw [← sq, ← sq, ← sq] at h_pythag
      exact h_pythag
    have h_sq_le : ‖(T.π a) v₁ - v₁‖ ^ 2 ≤ ‖(T.π a) T.ξ - v₁‖ ^ 2 := by rw [h_orth]; linarith [sq_nonneg ‖(T.π a) v₂‖]
    rw [sq_le_sq, abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at h_sq_le
    exact lt_of_le_of_lt h_sq_le ha
  have h_norm_v2 : ‖(T.π a) v₂‖ < ε := by
    have h_orth : ‖(T.π a) T.ξ - v₁‖ ^ 2 = ‖(T.π a) v₁ - v₁‖ ^ 2 + ‖(T.π a) v₂‖ ^ 2 := by
      have h_decomp : (T.π a) T.ξ - v₁ = ((T.π a) v₁ - v₁) + (T.π a) v₂ := by
        rw [hξ, map_add]
        abel
      rw [h_decomp]
      have h1 : (T.π a) v₁ - v₁ ∈ W := Submodule.sub_mem W (hWinv a ⟨v₁, hv₁, rfl⟩) hv₁
      have h2 : (T.π a) v₂ ∈ Wᗮ := isInvariant_orthogonal T W hWinv a ⟨v₂, hv₂, rfl⟩
      have h_pythag := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero ((T.π a) v₁ - v₁) ((T.π a) v₂) ((Submodule.mem_orthogonal W _).mp h2 _ h1)
      rw [← sq, ← sq, ← sq] at h_pythag
      exact h_pythag
    have h_sq_le : ‖(T.π a) v₂‖ ^ 2 ≤ ‖(T.π a) T.ξ - v₁‖ ^ 2 := by rw [h_orth]; linarith [sq_nonneg ‖(T.π a) v₁ - v₁‖]
    rw [sq_le_sq, abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at h_sq_le
    exact lt_of_le_of_lt h_sq_le ha
  -- Contradiction
  have h_phi : ‖φ a - 1‖ < 1/2 := by
    dsimp only [φ]
    rw [ContinuousLinearMap.smul_apply]
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
      _ ≤ ε * K := by gcongr; apply le_add_of_nonneg_right; apply mul_nonneg (inv_nonneg.mpr (by linarith)) (norm_nonneg _)
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
    rw [ContinuousLinearMap.smul_apply, vectorFunctional_apply, smul_eq_mul]
    rw [norm_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < 1 - t)]
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
      _ ≤ ε * K := by gcongr; apply le_add_of_nonneg_left; apply mul_nonneg (inv_nonneg.mpr (by linarith)) (norm_nonneg _)
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

lemma eq_top_of_norm_sq_eq_one (T : GNS.Representation ω) (W : Submodule ℂ T.H)
    (hWinv : T.IsInvariant W) (hWclosed : IsClosed (W : Set T.H))
    (v₁ v₂ : T.H) (hv₁ : v₁ ∈ W) (_hv₂ : v₂ ∈ Wᗮ) (hξ : T.ξ = v₁ + v₂)
    (horth : ⟪v₁, v₂⟫ = 0) (h : ‖v₁‖ ^ 2 = 1) :
    W = ⊤ := by
  have hv₂_zero := mem_of_norm_sq_eq_one T v₁ v₂ hξ horth h
  have hξ_in_W : T.ξ ∈ W := by rw [hξ, hv₂_zero, add_zero]; exact hv₁
  set S := Submodule.span ℂ (Set.range fun a => (T.π a) T.ξ)
  have h_span_le : S ≤ W := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact hWinv a ⟨T.ξ, hξ_in_W, rfl⟩
  have h_dense : Dense (S : Set T.H) := T.cyclic
  have h_closure_le : S.topologicalClosure ≤ W :=
    S.topologicalClosure_minimal h_span_le hWclosed
  have h_closure_eq_top : S.topologicalClosure = ⊤ := by
    ext x; simp only [Submodule.mem_top, iff_true]; exact h_dense x
  rw [h_closure_eq_top] at h_closure_le
  exact eq_top_iff.mpr h_closure_le

lemma eq_bot_of_norm_sq_eq_zero (T : GNS.Representation ω) (W : Submodule ℂ T.H)
    (hWinv : T.IsInvariant W) (_hWclosed : IsClosed (W : Set T.H))
    (v₁ v₂ : T.H) (_hv₁ : v₁ ∈ W) (_hv₂ : v₂ ∈ Wᗮ) (hξ : T.ξ = v₁ + v₂)
    (_horth : ⟪v₁, v₂⟫ = 0) (h : ‖v₁‖ ^ 2 = 0) :
    W = ⊥ := by
  have hv₁_zero : v₁ = 0 := by
    have : ‖v₁‖ = 0 := by nlinarith [sq_nonneg ‖v₁‖]
    exact norm_eq_zero.mp this
  have hξ_in_Wperp : T.ξ ∈ Wᗮ := by rw [hξ, hv₁_zero, zero_add]; exact _hv₂
  have hWperp_inv := isInvariant_orthogonal T W hWinv
  have hWperp_closed : IsClosed (Wᗮ : Set T.H) := Submodule.isClosed_orthogonal W
  set S := Submodule.span ℂ (Set.range fun a => (T.π a) T.ξ)
  have h_span_le : S ≤ Wᗮ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact hWperp_inv a ⟨T.ξ, hξ_in_Wperp, rfl⟩
  have h_dense : Dense (S : Set T.H) := T.cyclic
  have h_closure_le : S.topologicalClosure ≤ Wᗮ :=
    S.topologicalClosure_minimal h_span_le hWperp_closed
  have h_closure_eq_top : S.topologicalClosure = ⊤ := by
    ext x
    simp only [Submodule.mem_top, iff_true]
    exact h_dense x
  rw [h_closure_eq_top] at h_closure_le
  have : Wᗮ = ⊤ := eq_top_iff.mpr h_closure_le
  rw [← Submodule.orthogonal_eq_bot_iff] at this
  simpa using this

/-- **Main Theorem**: The GNS representation of a pure state is irreducible. -/
theorem pureState_gns_isIrreducible {ψ : PureState A} :
    IsIrreducible (PureState.gnsRepresentation ψ) := by
  let T := PureState.gnsRepresentation ψ
  intro W hWclosed hWinv
  obtain ⟨v₁, v₂, hv₁, hv₂, hξ, horth⟩ := cyclicVector_decomp_of_isClosed T W hWclosed
  have h_trichotomy := trichotomy_from_purity W hWinv hWclosed v₁ v₂ hv₁ hv₂ hξ horth
  cases h_trichotomy with
  | inl h_zero =>
    left
    exact eq_bot_of_norm_sq_eq_zero T W hWinv hWclosed v₁ v₂ hv₁ hv₂ hξ horth h_zero
  | inr h_one =>
    right
    exact eq_top_of_norm_sq_eq_one T W hWinv hWclosed v₁ v₂ hv₁ hv₂ hξ horth h_one

end Representation

end GNS
