import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.LocallyConvex.WeakDual
import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.Unital
import QuantumSystem.Algebra.CStarAlgebra.State
import QuantumSystem.Algebra.CStarAlgebra.QuasiState


variable {A : Type*} [NonUnitalCStarAlgebra A]
variable {B : Type*} [CStarAlgebra B] [Nontrivial B]

instance : LocallyConvexSpace ℝ (WeakDual ℂ A) := WeakBilin.locallyConvexSpace

/-- A pure state is an extreme point of the quasi-state space, excluding zero. -/
def IsPureState (φ : WeakDual ℂ A) : Prop :=
  φ ∈ Set.extremePoints ℝ (QuasiStateSpace A) ∧ φ ≠ 0


/-- A linear functional with norm 1 that maps 1 to 1 is necessarily positive. -/
private lemma isPositive_of_norm_eq_one_map_one
    (φ : WeakDual ℂ B) (h_norm : ‖WeakDual.toStrongDual φ‖ = 1) (h_one : φ 1 = 1) : IsPositive B φ := by
  intro a
  -- 1. φ is real on self-adjoint elements.
  have h_real : ∀ x : B, IsSelfAdjoint x → (φ x).im = 0 := by
    intro x hx
    by_contra h
    let t := (‖x‖^2 - ‖φ x‖^2 + 1) / (2 * (φ x).im)
    have : ‖φ (x + (Complex.I * t) • 1)‖^2 ≤ ‖x + (Complex.I * t) • 1‖^2 := by
      rw [sq_le_sq, abs_norm, abs_norm]
      exact (WeakDual.toStrongDual φ).le_opNorm _ |>.trans_eq (by rw [h_norm, one_mul])
    rw [UnitalCStarAlgebra.norm_sq_add_imaginary_unit_of_selfAdjoint x hx t] at this
    simp only [map_add, map_smul, h_one, smul_eq_mul, mul_one] at this
    rw [← Complex.normSq_eq_norm_sq] at this
    have h_expand : Complex.normSq (φ x + t * Complex.I) = Complex.normSq (φ x) + 2 * (φ x).im * t + t^2 := by
      simp [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
      ring
    rw [mul_comm Complex.I] at this
    rw [h_expand] at this
    rw [Complex.normSq_eq_norm_sq] at this
    simp only [add_le_add_iff_right] at this
    have h_im_ne : 2 * (φ x).im ≠ 0 := mul_ne_zero two_ne_zero h
    dsimp [t] at this
    field_simp [h_im_ne] at this
    linarith
  -- 2. Show φ(star a * a) ≥ 0
  let b := star a * a
  have hb_sa : IsSelfAdjoint b := IsSelfAdjoint.star_mul_self a
  obtain ⟨r, hr⟩ : ∃ r : ℝ, φ b = r := ⟨(φ b).re, Complex.ext rfl (h_real b hb_sa)⟩
  use ⟨r, ?_⟩
  · rw [hr]; rfl
  · by_contra h_neg
    have : ‖b‖ - r ≤ ‖b‖ := by
      let y := algebraMap ℝ B ‖b‖
      have hy : ‖y‖ = ‖b‖ := by simp [y, Algebra.algebraMap_eq_smul_one, norm_smul]
      have h_phi_y : φ y = ‖b‖ := by
        simp only [y, IsScalarTower.algebraMap_apply ℝ ℂ B]
        rw [Algebra.algebraMap_eq_smul_one, map_smul, h_one]
        simp
      have h1 : ‖b‖ - r = (φ (y - b)).re := by
        simp [map_sub, h_phi_y, hr, Complex.sub_re, Complex.ofReal_re]
      rw [h1]
      apply (Complex.re_le_norm _).trans
      apply ((WeakDual.toStrongDual φ).le_opNorm _).trans
      rw [h_norm, one_mul]
      rw [← hy]
      apply CStarAlgebra.norm_le_norm_of_nonneg_of_le
      · exact sub_nonneg.mpr (IsSelfAdjoint.le_algebraMap_norm_self hb_sa)
      · have : 0 ≤ b := StarOrderedRing.nonneg_iff.mpr (AddSubmonoid.subset_closure ⟨a, rfl⟩)
        exact sub_le_self y this
    linarith


/-- For any nonzero positive element `b`, there exists a state on the unitization
that has positive real part when applied to `b`. -/
private lemma exists_unitization_state_pos_re (b : A) (hb : 0 ≤ b) (hb_ne : b ≠ 0) :
    ∃ ψ : Unitization ℂ A →L[ℂ] ℂ, ‖ψ‖ = 1 ∧ ψ 1 = 1 ∧ (ψ (Unitization.inr b)).re > 0 := by
  let b' : Unitization ℂ A := Unitization.inr b
  have hb' : 0 ≤ b' := Unitization.inr_nonneg_iff.mpr hb
  have hb'_ne : b' ≠ 0 := Unitization.inr_injective.ne hb_ne
  -- ‖b'‖ is in the spectrum of b'
  have h_spec : (‖b'‖ : ℂ) ∈ spectrum ℂ b' := by
    obtain ⟨z, hz_mem, hz_abs⟩ := spectrum.exists_nnnorm_eq_spectralRadius (a := b')
    have hz_real : z = z.re := (IsSelfAdjoint.of_nonneg hb').mem_spectrum_eq_re hz_mem
    have hz_nonneg : 0 ≤ z.re := by
      have h_mem_real : z.re ∈ spectrum ℝ b' := by
        rw [← spectrum.algebraMap_mem_iff ℂ]
        convert hz_mem
        exact hz_real.symm
      exact spectrum_nonneg_of_nonneg hb' h_mem_real
    rw [IsSelfAdjoint.spectralRadius_eq_nnnorm (IsSelfAdjoint.of_nonneg hb'),
        hz_real, Complex.nnnorm_real, Real.nnnorm_of_nonneg hz_nonneg] at hz_abs
    have h_eq : z.re = ‖b'‖ := by
      rw [ENNReal.coe_inj] at hz_abs
      exact congr_arg Subtype.val hz_abs
    rw [← h_eq, ← hz_real]
    exact hz_mem
  -- By Gelfand duality, there exists a character φ on C*(b') such that φ(b') = ‖b'‖
  haveI : IsStarNormal b' := IsSelfAdjoint.isStarNormal (IsSelfAdjoint.of_nonneg hb')
  haveI : IsClosed (StarAlgebra.elemental ℂ b' : Set (Unitization ℂ A)) :=
    StarAlgebra.elemental.isClosed ℂ b'
  have h_spec_S : (‖b'‖ : ℂ) ∈ spectrum ℂ (⟨b', StarAlgebra.elemental.self_mem ℂ b'⟩ : StarAlgebra.elemental ℂ b') := by
    rwa [StarSubalgebra.spectrum_eq]
  obtain ⟨φ, hφ⟩ := WeakDual.CharacterSpace.mem_spectrum_iff_exists.mp h_spec_S
  -- Extend φ to a state ψ on Unitization ℂ A
  let φ_clm := WeakDual.toStrongDual φ.val
  obtain ⟨ψ, hψ_ext, hψ_norm⟩ := exists_extension_norm_eq (StarAlgebra.elemental ℂ b').toSubmodule φ_clm
  refine ⟨ψ, ?_, ?_, ?_⟩
  · rw [hψ_norm]
    exact UnitalCStarAlgebra.norm_character_eq_one φ
  · rw [hψ_ext ⟨1, (StarAlgebra.elemental ℂ b').one_mem⟩]
    show (WeakDual.toStrongDual φ.val) ⟨1, _⟩ = 1
    rw [WeakDual.toStrongDual_apply]
    change φ 1 = 1
    rw [map_one φ]
  · rw [hψ_ext ⟨b', StarAlgebra.elemental.self_mem ℂ b'⟩]
    show ((WeakDual.toStrongDual φ.val) ⟨b', _⟩).re > 0
    rw [WeakDual.toStrongDual_apply]
    change (φ ⟨b', StarAlgebra.elemental.self_mem ℂ b'⟩).re > 0
    rw [hφ]
    simp only [Complex.ofReal_re]
    exact norm_pos_iff.mpr hb'_ne


/-- For any nonzero positive element `b`, there exists a quasi-state with positive
real part when applied to `b`. -/
private lemma exists_quasiState_pos_re (b : A) (hb : 0 ≤ b) (hb_ne : b ≠ 0) :
    ∃ φ ∈ QuasiStateSpace A, (φ b).re > 0 := by
  haveI : Nontrivial A := nontrivial_of_ne b 0 hb_ne
  obtain ⟨ψ, hψ_norm_eq, hψ_one, hψ_pos_val⟩ := exists_unitization_state_pos_re b hb hb_ne
  have hψ_pos : IsPositive (Unitization ℂ A) ψ :=
    isPositive_of_norm_eq_one_map_one ψ hψ_norm_eq hψ_one

  let inrLM : A →ₗ[ℂ] Unitization ℂ A :=
    { toFun := Unitization.inr
      map_add' := map_add (Unitization.inrNonUnitalStarAlgHom ℂ A)
      map_smul' := map_smul (Unitization.inrNonUnitalStarAlgHom ℂ A) }
  let inrIso : A →ₗᵢ[ℂ] Unitization ℂ A :=
    { toLinearMap := inrLM
      norm_map' := Unitization.norm_inr }
  let inrCLM := inrIso.toContinuousLinearMap

  let φ := ψ.comp inrCLM
  have hφ_pos : IsPositive A φ := fun a => by
    obtain ⟨r, hr⟩ := hψ_pos (Unitization.inr a)
    use r
    dsimp only [ContinuousLinearMap.comp_apply, inrCLM, inrIso, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometry.coe_mk, inrLM, LinearMap.coe_mk, AddHom.coe_mk]
    change ψ (Unitization.inr (star a * a)) = _
    rw [Unitization.inr_mul, Unitization.inr_star]
    rw [← hr]
  have hφ_norm : ‖φ‖ ≤ 1 := by
    calc ‖φ‖ ≤ ‖ψ‖ * ‖inrCLM‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ = 1 * 1 := by
        rw [hψ_norm_eq]
        congr
        exact inrIso.norm_toContinuousLinearMap
      _ = 1 := mul_one _
  use φ
  refine ⟨⟨hφ_pos, ?_⟩, hψ_pos_val⟩
  simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
  exact hφ_norm


namespace IsPureState

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- Every pure state has operator norm equal to 1. -/
lemma norm_eq_one {φ : WeakDual ℂ A} (h : IsPureState φ) : ‖WeakDual.toStrongDual φ‖ = 1 := by
  obtain ⟨h_ext, h_ne_zero⟩ := h
  have h_mem : φ ∈ QuasiStateSpace A := h_ext.1
  have h_norm_le : ‖WeakDual.toStrongDual φ‖ ≤ 1 := by
    simpa [QuasiStateSpace] using h_mem.2
  have h_pos : IsPositive A φ := h_mem.1
  by_contra h_contra
  have h_norm_lt : ‖WeakDual.toStrongDual φ‖ < 1 := lt_of_le_of_ne h_norm_le h_contra
  have h_norm_pos : 0 < ‖WeakDual.toStrongDual φ‖ := norm_pos_iff.mpr (by
    intro h0
    apply h_ne_zero
    apply WeakDual.toStrongDual.injective
    simp [h0])

  let r := ‖WeakDual.toStrongDual φ‖
  let ψ := (r⁻¹ : ℂ) • φ

  have hψ_norm : ‖WeakDual.toStrongDual ψ‖ = 1 := by
    rw [map_smul, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (le_of_lt h_norm_pos)]
    field_simp [r, h_norm_pos.ne']

  have hψ_pos : IsPositive A ψ := by
    intro a
    obtain ⟨s, hs⟩ := h_pos a
    let s' : ℝ := (s : ℝ) * r⁻¹
    have hs' : 0 ≤ s' := mul_nonneg s.2 (inv_nonneg.mpr (le_of_lt h_norm_pos))
    use ⟨s', hs'⟩
    rw [ContinuousLinearMap.smul_apply]
    simp only [hs, smul_eq_mul]
    simp [s']
    rw [mul_comm]

  have hψ_mem : ψ ∈ QuasiStateSpace A := by
    refine ⟨hψ_pos, ?_⟩
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
    rw [hψ_norm]

  have h_eq : φ = (1 - r) • (0 : WeakDual ℂ A) + (r : ℂ) • ψ := by
    simp only [smul_zero, zero_add, ψ]
    rw [← smul_assoc]
    have hr_ne : (r : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact h_norm_pos.ne'
    have : (r : ℂ) * (r⁻¹ : ℂ) = 1 := mul_inv_cancel₀ hr_ne
    rw [smul_eq_mul]
    rw [this, one_smul]

  have h_not_ext : φ ∉ Set.extremePoints ℝ (QuasiStateSpace A) := by
    intro h_ext'
    have h_open_segment : φ ∈ openSegment ℝ (0 : WeakDual ℂ A) ψ := by
      use 1 - r, r
      refine ⟨?_, ?_, ?_, ?_⟩
      · linarith
      · linarith
      · linarith
      · rw [h_eq]
        simp

    have h_zero_mem : 0 ∈ QuasiStateSpace A := by
      refine ⟨IsPositive.zero A, ?_⟩
      simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
      rw [map_zero, norm_zero]
      exact zero_le_one

    have h_endpoints : 0 ∈ QuasiStateSpace A ∧ ψ ∈ QuasiStateSpace A := ⟨h_zero_mem, hψ_mem⟩
    have h_distinct : 0 ≠ ψ := by
      intro h0
      have : ‖WeakDual.toStrongDual ψ‖ = 0 := by rw [← h0]; simp
      linarith

    have h_seg := h_ext'.2 h_endpoints.1 h_endpoints.2 h_open_segment
    rcases h_seg with rfl | rfl
    exact h_ne_zero rfl

  exact h_not_ext h_ext

/-- Convert a pure state (defined as an extreme point) to a `State` structure. -/
noncomputable def toState {φ : WeakDual ℂ A} (h : IsPureState φ) : State ℂ A where
  toLinearMap := WeakDual.toStrongDual φ
  positive := by
    intro a
    obtain ⟨r, hr⟩ := h.1.1.1 a
    use r
    exact hr
  norm_eq_one := by
    have h_norm := norm_eq_one h
    unfold linearOpNorm
    apply le_antisymm
    · apply Real.sSup_le
      · rintro _ ⟨a, ha, rfl⟩
        rw [div_le_iff₀ (norm_pos_iff.mpr ha), one_mul]
        calc ‖(WeakDual.toStrongDual φ) a‖
            ≤ ‖WeakDual.toStrongDual φ‖ * ‖a‖ := (WeakDual.toStrongDual φ).le_opNorm a
          _ = 1 * ‖a‖ := by rw [h_norm]
          _ = ‖a‖ := one_mul _
      · linarith
    · -- We need 1 ≤ sSup { ‖φ a‖ / ‖a‖ | a ≠ 0 }
      -- This follows from the fact that ‖φ‖ = 1 and the operator norm is the sSup
      have h_ne_zero := h.2
      -- φ ≠ 0 means there exists a ≠ 0 such that φ a ≠ 0
      have h_exists : ∃ a : A, a ≠ 0 := by
        by_contra h_all_zero
        push_neg at h_all_zero
        have : (0 : WeakDual ℂ A) = φ := by
          apply WeakDual.toStrongDual.injective
          ext a
          simp [h_all_zero a]
        exact h_ne_zero this.symm
      obtain ⟨a₀, ha₀⟩ := h_exists
      have h_nonempty : { r : ℝ | ∃ a : A, a ≠ 0 ∧ r = ‖(WeakDual.toStrongDual φ) a‖ / ‖a‖ }.Nonempty :=
        ⟨‖(WeakDual.toStrongDual φ) a₀‖ / ‖a₀‖, a₀, ha₀, rfl⟩
      have h_bdd : BddAbove { r : ℝ | ∃ a : A, a ≠ 0 ∧ r = ‖(WeakDual.toStrongDual φ) a‖ / ‖a‖ } := by
        use ‖WeakDual.toStrongDual φ‖
        rintro _ ⟨a, ha, rfl⟩
        rw [div_le_iff₀ (norm_pos_iff.mpr ha)]
        exact (WeakDual.toStrongDual φ).le_opNorm a
      -- The operator norm equals the sSup
      have h_opNorm_eq : ‖WeakDual.toStrongDual φ‖ =
          sSup { r : ℝ | ∃ a : A, a ≠ 0 ∧ r = ‖(WeakDual.toStrongDual φ) a‖ / ‖a‖ } := by
        apply le_antisymm
        · have h_nonneg : 0 ≤ sSup { r : ℝ | ∃ a : A, a ≠ 0 ∧ r = ‖(WeakDual.toStrongDual φ) a‖ / ‖a‖ } := by
            apply Real.sSup_nonneg
            rintro _ ⟨a, _, rfl⟩
            exact div_nonneg (norm_nonneg _) (norm_nonneg _)
          apply ContinuousLinearMap.opNorm_le_bound _ h_nonneg
          intro a
          by_cases ha : a = 0
          · simp [ha]
          · rw [mul_comm]
            calc ‖(WeakDual.toStrongDual φ) a‖
                = ‖a‖ * (‖(WeakDual.toStrongDual φ) a‖ / ‖a‖) := by field_simp [norm_pos_iff.mpr ha]
              _ ≤ ‖a‖ * sSup { r : ℝ | ∃ a : A, a ≠ 0 ∧ r = ‖(WeakDual.toStrongDual φ) a‖ / ‖a‖ } := by
                  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
                  apply le_csSup h_bdd
                  exact ⟨a, ha, rfl⟩
        · apply csSup_le h_nonempty
          rintro _ ⟨a, ha, rfl⟩
          rw [div_le_iff₀ (norm_pos_iff.mpr ha)]
          exact (WeakDual.toStrongDual φ).le_opNorm a
      rw [h_norm] at h_opNorm_eq
      simp [h_opNorm_eq]


/-- For any non-zero element `a`, there exists a pure state `φ` such that `φ(star a * a) > 0`. -/
lemma exists_pos_re_of_ne_zero (a : A) (ha : a ≠ 0) :
    ∃ φ : WeakDual ℂ A, IsPureState φ ∧ (φ (star a * a)).re > 0 := by
  let b := star a * a
  have hb_ne_zero : b ≠ 0 := by
    rw [ne_eq, CStarRing.star_mul_self_eq_zero_iff]
    exact ha
  have hb_pos : 0 ≤ b := by
    apply StarOrderedRing.nonneg_iff.mpr
    apply AddSubmonoid.subset_closure
    use a

  obtain ⟨ω, hω_mem, hω_pos⟩ := exists_quasiState_pos_re b hb_pos hb_ne_zero

  let eval_b : WeakDual ℂ A →L[ℂ] ℂ := {
    toFun := fun φ => φ b
    map_add' := fun φ ψ => rfl
    map_smul' := fun c φ => rfl
    cont := WeakDual.eval_continuous b
  }
  let l : WeakDual ℂ A →L[ℝ] ℝ := Complex.reCLM.comp (eval_b.restrictScalars ℝ)
  let f : WeakDual ℂ A → ℝ := l
  let M := sSup (f '' QuasiStateSpace A)

  have hf : ContinuousOn f (QuasiStateSpace A) := Continuous.continuousOn l.continuous |>.mono (Set.subset_univ _)

  have h_M_pos : M > 0 := by
    apply lt_of_lt_of_le hω_pos
    apply le_csSup
    · exact ((QuasiStateSpace.compact A).image_of_continuousOn hf).bddAbove
    · exact Set.mem_image_of_mem f hω_mem

  -- Find a maximizer of f on the QuasiStateSpace
  obtain ⟨φ, hφ_mem, hφ_max⟩ := IsCompact.exists_isMaxOn (QuasiStateSpace.compact A) ⟨ω, hω_mem⟩ hf

  have hφ_val : f φ = M := by
    apply le_antisymm
    · apply le_csSup
      · exact ((QuasiStateSpace.compact A).image_of_continuousOn hf).bddAbove
      · exact Set.mem_image_of_mem f hφ_mem
    · apply csSup_le
      · use f ω
        use ω, hω_mem
      · intro r ⟨ψ, hψ_mem, hr⟩
        rw [← hr]
        exact hφ_max hψ_mem

  -- φ achieves the maximum M > 0
  have hφ_pos : (φ b).re > 0 := by
    calc (φ b).re = f φ := rfl
      _ = M := hφ_val
      _ > 0 := h_M_pos

  have hφ_ne_zero : φ ≠ 0 := by
    intro h
    have : (φ b).re = 0 := by
      rw [h]
      rfl
    linarith [hφ_pos]

  -- To show φ is a pure state (extreme point), we use convexity argument
  let S := QuasiStateSpace A
  let l' := l -- alias to avoid confusion if needed, but we use l
  have h_exposed : IsExposed ℝ S {x ∈ S | ∀ z ∈ S, l z ≤ l x} := fun _ => ⟨l, rfl⟩
  let F := {x ∈ S | ∀ z ∈ S, l z ≤ l x}
  have hF_nonempty : F.Nonempty := ⟨φ, hφ_mem, fun z hz => hφ_max hz⟩
  have hF_compact : IsCompact F := h_exposed.isCompact (QuasiStateSpace.compact A)
  obtain ⟨ψ, hψ_mem_F, hψ_ext⟩ := hF_compact.extremePoints_nonempty hF_nonempty
  have hψ_ext_S : IsPureState ψ := by
    constructor
    · exact h_exposed.isExtreme.extremePoints_subset_extremePoints ⟨hψ_mem_F, hψ_ext⟩
    · intro h
      have h_psi_zero : (ψ b).re = 0 := by rw [h]; rfl
      have h_psi_M : l ψ = M := by
        apply le_antisymm
        · apply le_csSup
          · exact ((QuasiStateSpace.compact A).image l.continuous).bddAbove
          · exact Set.mem_image_of_mem l hψ_mem_F.1
        · apply csSup_le
          · use l φ
            use φ, hφ_mem
          · intro r ⟨z, hz, hr⟩
            rw [← hr]
            exact hψ_mem_F.2 z hz
      change l ψ = 0 at h_psi_zero
      rw [h_psi_M] at h_psi_zero
      linarith [h_M_pos, h_psi_zero]
  use ψ
  constructor
  · exact hψ_ext_S
  · have : l ψ = M := by
      apply le_antisymm
      · apply le_csSup
        · exact ((QuasiStateSpace.compact A).image l.continuous).bddAbove
        · exact Set.mem_image_of_mem l hψ_mem_F.1
      · apply csSup_le
        · use l φ
          use φ, hφ_mem
        · intro r ⟨z, hz, hr⟩
          rw [← hr]
          exact hψ_mem_F.2 z hz
    change l ψ > 0
    rw [this]
    exact h_M_pos

end IsPureState


/-- The type of pure states on a non-unital C*-algebra `A`, packaged as a subtype
of `WeakDual ℂ A`. -/
def PureState (A : Type*) [NonUnitalCStarAlgebra A] :=
  { φ : WeakDual ℂ A // IsPureState φ }

namespace PureState

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- Convert a pure state to a State via the coercion instance. -/
noncomputable def toState (ψ : PureState A) : State ℂ A :=
  IsPureState.toState ψ.property

end PureState

/-- Coercion from pure states (as a subtype) to `State`. -/
noncomputable instance : CoeOut (PureState A) (State ℂ A) where
  coe φ := IsPureState.toState φ.property

@[simp]
lemma PureState.coe_apply (φ : PureState A) (a : A) :
    (φ : State ℂ A) a = φ.val a := rfl
