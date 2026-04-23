module

public import Mathlib.Analysis.Normed.Operator.Extend
public import QuantumSystem.ForMathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
public import QuantumSystem.ForMathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PartialIsometry

open scoped InnerProductSpace
open ContinuousLinearMap

@[expose] public section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Existence of Polar Decomposition for bounded operators on Hilbert space. -/
theorem exists_polar_decomposition (T : H →L[ℂ] H) :
    ∃ U : H →L[ℂ] H, IsPartialIsometry U ∧ T = U * absoluteValue T ∧
    LinearMap.ker U.toLinearMap = LinearMap.ker T.toLinearMap := by
  let P := absoluteValue T
  let M := LinearMap.range P.toLinearMap
  let kerP := LinearMap.ker P.toLinearMap
  let kerT := LinearMap.ker T.toLinearMap
  have h_ker : kerP = kerT := absoluteValue_ker_eq_ker T
  let T_desc : (H ⧸ kerP) →ₗ[ℂ] H :=
    Submodule.liftQ _ T.toLinearMap (h_ker.le)
  let P_iso := P.toLinearMap.quotKerEquivRange
  let V₀_lin : M →ₗ[ℂ] H := T_desc.comp P_iso.symm.toLinearMap
  have h_iso (y : M) : ‖V₀_lin y‖ = ‖(y : H)‖ := by
    obtain ⟨x, hx⟩ := (LinearMap.mem_range.mp y.prop)
    have hy_eq : P_iso (Submodule.Quotient.mk x) = y := by
      apply Subtype.ext
      have hcoe : ((P_iso (Submodule.Quotient.mk x)) : H) = P x := by
        simp [P_iso, LinearMap.quotKerEquivRange_apply_mk]
      simpa [hcoe] using hx
    have h_symm : P_iso.symm y = Submodule.Quotient.mk x := by
      rw [← hy_eq, LinearEquiv.symm_apply_apply]
    have h_norm : ‖T_desc (Submodule.Quotient.mk x)‖ = ‖P x‖ := by
      simpa [T_desc, Submodule.liftQ_apply] using (norm_absoluteValue_eq_norm T x).symm
    calc
      ‖T_desc (P_iso.symm y)‖ = ‖T_desc (Submodule.Quotient.mk x)‖ := by simp [h_symm]
      _ = ‖P x‖ := h_norm
      _ = ‖(y : H)‖ := by
        simpa using congrArg norm hx
  let V₀ : M →L[ℂ] H :=
    LinearMap.mkContinuous V₀_lin 1 (by
      intro y
      rw [one_mul]
      exact le_of_eq (h_iso y)
    )
  let K := Submodule.topologicalClosure M
  -- K is complete as a closed subspace of H
  haveI : IsClosed (K : Set H) := Submodule.isClosed_topologicalClosure M
  haveI : CompleteSpace K := IsClosed.completeSpace_coe
  -- K has orthogonal projection since it's a complete subspace
  haveI : K.HasOrthogonalProjection := inferInstance
  -- Inclusion M → K
  let ι' : M →ₗ[ℂ] K := Submodule.inclusion (Submodule.le_topologicalClosure M)
  let ι : M →L[ℂ] K :=
    LinearMap.mkContinuous ι' 1 (by
      intro y
      simp only [ι', Submodule.inclusion_apply, one_mul]
      exact le_rfl
    )
  have h_dense : DenseRange ι := by
    have hcl : (K : Set H) ⊆ closure (M : Set H) := by
      intro x hx
      simpa [Submodule.topologicalClosure_coe] using hx
    have h := (denseRange_inclusion_iff
      (s := (M : Set H)) (t := (K : Set H)) (Submodule.le_topologicalClosure M)).2 hcl
    simpa [ι, ι', LinearMap.mkContinuous_apply, Submodule.inclusion_apply] using h
  have h_isom_ι : Isometry ι := by
    apply AddMonoidHomClass.isometry_of_norm
    intro x
    simp only [ι, LinearMap.mkContinuous_apply, ι', Submodule.inclusion_apply]
    rfl
  have h_unip : IsUniformInducing ι :=
    (Isometry.isUniformEmbedding h_isom_ι).isUniformInducing
  let V_ext := ContinuousLinearMap.extend V₀ ι
  let V_ext := ContinuousLinearMap.extend V₀ ι
  -- U = V_ext ∘ P_K where P_K is orthogonal projection onto K
  let P_K_lin : H →ₗ[ℂ] K :=
    LinearMap.codRestrict K (K.starProjection.toLinearMap)
      (by
        intro x
        exact Submodule.starProjection_apply_mem (U := K) (x := x))
  let P_K : H →L[ℂ] K :=
    LinearMap.mkContinuous P_K_lin 1 (by
      intro x
      have h := Submodule.norm_starProjection_apply_le (K := K) x
      simpa [P_K_lin, LinearMap.codRestrict_apply, one_mul] using h
    )
  let U : H →L[ℂ] H := V_ext.comp P_K
  -- Proof of properties
  have h_isom_ext (k : K) : ‖V_ext k‖ = ‖k‖ := by
    refine DenseRange.induction_on h_dense k ?_ ?_
    · apply isClosed_eq
      · exact continuous_norm.comp V_ext.continuous
      · exact continuous_norm
    · intro m
      rw [ContinuousLinearMap.extend_eq (h_dense := h_dense) (h_e := h_unip)]
      simp only [V₀, LinearMap.mkContinuous_apply]
      rw [h_iso m]
      rfl
  have h_U_P : T = U * P := by
    ext x
    let Px : M := ⟨P x, LinearMap.mem_range_self _ _⟩
    have h_Px_in_K : P x ∈ K := Submodule.le_topologicalClosure M Px.prop
    have h_proj : K.starProjection (P x) = P x :=
      Submodule.starProjection_eq_self_iff.mpr h_Px_in_K
    -- rewrite starProjection on `P x`
    simp only [U, ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply]
    have h_P_K : P_K (P x) = ⟨P x, h_Px_in_K⟩ := by
      ext
      simp [P_K, P_K_lin, LinearMap.codRestrict_apply, LinearMap.mkContinuous_apply, h_proj]
    rw [h_P_K]
    -- Now V_ext ⟨P x, _⟩ = V₀ Px by density extension
    have h_Px_K : (⟨P x, h_Px_in_K⟩ : K) = ι Px := by
      simp only [ι, LinearMap.mkContinuous_apply, ι', Submodule.inclusion_apply]
      rfl
    rw [h_Px_K]
    rw [ContinuousLinearMap.extend_eq (h_dense := h_dense) (h_e := h_unip)]
    simp only [V₀, LinearMap.mkContinuous_apply, V₀_lin, LinearMap.comp_apply]
    have h_symm : P_iso.symm Px = Submodule.Quotient.mk x := by
      have h1 : P_iso (Submodule.Quotient.mk x) = Px := by
        ext
        change ((P_iso (Submodule.Quotient.mk x)) : H) = P x
        simp [P_iso, LinearMap.quotKerEquivRange_apply_mk]
      rw [← h1, LinearEquiv.symm_apply_apply]
    -- rewrite the quotient element
    change T x = T_desc (P_iso.symm Px)
    rw [h_symm, Submodule.liftQ_apply]
    simp
  have h_ker_U : LinearMap.ker U.toLinearMap = kerT := by
    ext x
    rw [← h_ker]
    simp only [kerP, LinearMap.mem_ker]
    constructor
    · intro h
      have h0 : P_K x = 0 := by
        have h1 : ‖V_ext (P_K x)‖ = 0 := by
          simpa [U] using congrArg norm h
        have h2 : ‖P_K x‖ = 0 := by
          simpa [h_isom_ext (P_K x)] using h1
        exact norm_eq_zero.mp h2
      have h_proj0 : K.starProjection x = 0 := by
        have hval : ((P_K x : K) : H) = 0 := by
          simpa using congrArg Subtype.val h0
        simpa [P_K, P_K_lin, LinearMap.codRestrict_apply, LinearMap.mkContinuous_apply] using hval
      have h_orth : x ∈ Kᗮ :=
        (Submodule.starProjection_apply_eq_zero_iff (K := K)).1 h_proj0
      have h_orth' : x ∈ Mᗮ := by
        simpa [K, Submodule.orthogonal_closure (K := M)] using h_orth
      have h_kerP' : P.adjoint x = 0 := by
        have h_eq : (LinearMap.range P.toLinearMap).orthogonal = LinearMap.ker P.adjoint := by
          simpa using (ContinuousLinearMap.orthogonal_range (T := P))
        have h_range : x ∈ (LinearMap.range P.toLinearMap).orthogonal := by
          simpa [M] using h_orth'
        have h_kerP : x ∈ LinearMap.ker P.adjoint := by
          rw [← h_eq]
          exact h_range
        simpa [LinearMap.mem_ker] using h_kerP
      have h_kerP'' : P x = 0 := by
        simpa [P, (absoluteValue_isSelfAdjoint T).adjoint_eq] using h_kerP'
      have h_kerP''' : x ∈ kerP := by
        simpa [kerP, LinearMap.mem_ker] using h_kerP''
      exact h_kerP'''
    · intro h
      have h_kerP : P x = 0 := by
        simpa using h
      have h_kerP' : P.adjoint x = 0 := by
        simpa [P, (absoluteValue_isSelfAdjoint T).adjoint_eq] using h_kerP
      have h_kerP'' : P.adjoint x = 0 := h_kerP'
      have h_orth : x ∈ (LinearMap.range P.toLinearMap).orthogonal := by
        have h_eq : (LinearMap.range P.toLinearMap).orthogonal = LinearMap.ker P.adjoint := by
          simpa using (ContinuousLinearMap.orthogonal_range (T := P))
        rw [h_eq]
        simpa [LinearMap.mem_ker] using h_kerP''
      have h_orth_K : x ∈ Kᗮ := by
        have h' : x ∈ Mᗮ := by simpa [M] using h_orth
        simpa [K, Submodule.orthogonal_closure (K := M)] using h'
      have h_proj : K.starProjection x = 0 :=
        (Submodule.starProjection_apply_eq_zero_iff (K := K)).2 h_orth_K
      have h_P_K : P_K x = 0 := by
        apply Subtype.ext
        simp [P_K, P_K_lin, LinearMap.codRestrict_apply, LinearMap.mkContinuous_apply, h_proj]
      simp [U, h_P_K]
  have h_pi : IsPartialIsometry U := by
    -- Show `U†U = K.starProjection` and use idempotence.
    have h_Vext : V_ext.adjoint ∘L V_ext = 1 := by
      have h :=
        (ContinuousLinearMap.norm_map_iff_adjoint_comp_self V_ext).mp
          (by intro x; exact h_isom_ext x)
      simpa using h
    have h_Vext_apply : ∀ y, V_ext.adjoint (V_ext y) = y := by
      intro y
      have h := congrArg (fun f => f y) h_Vext
      simpa [ContinuousLinearMap.comp_apply] using h
    have h_PK_adj : P_K.adjoint = Submodule.subtypeL K := by
      ext y
      apply ext_inner_right ℂ
      intro z
      have h_proj : ((P_K z : K) : H) = K.starProjection z := by
        simp [P_K, P_K_lin, LinearMap.codRestrict_apply, LinearMap.mkContinuous_apply]
      have h1 : ⟪P_K.adjoint y, z⟫_ℂ = ⟪y, P_K z⟫_ℂ := by
        simp [adjoint_inner_left]
      calc
        ⟪P_K.adjoint y, z⟫_ℂ = ⟪y, P_K z⟫_ℂ := h1
        _ = ⟪(y : H), K.starProjection z⟫_ℂ := by
          simp [h_proj]
        _ = ⟪(y : H), z⟫_ℂ := by
          -- use self-adjointness of starProjection
          have h2 : ⟪K.starProjection z, (y : H)⟫_ℂ = ⟪z, (y : H)⟫_ℂ := by
            simpa [Submodule.starProjection_eq_self_iff.mpr y.property] using
              (Submodule.inner_starProjection_left_eq_right (K := K) z (y : H))
          rw [← inner_conj_symm, h2, inner_conj_symm]
    have h_subtype_comp : (Submodule.subtypeL K).comp P_K = K.starProjection := by
      ext x
      simp [P_K, P_K_lin, LinearMap.codRestrict_apply, LinearMap.mkContinuous_apply]
    have h_UU : U.adjoint * U = K.starProjection := by
      ext x
      -- compute pointwise
      simp [U, ContinuousLinearMap.mul_apply, adjoint_comp, ContinuousLinearMap.comp_apply,
        h_Vext_apply, h_PK_adj, P_K, P_K_lin, LinearMap.codRestrict_apply,
        LinearMap.mkContinuous_apply, Submodule.subtypeL_apply]
    have h_idem : K.starProjection * K.starProjection = K.starProjection := by
      simpa [IsIdempotentElem] using (Submodule.isIdempotentElem_starProjection (K := K))
    -- now use idempotence on `U†U`
    dsimp [IsPartialIsometry]
    simpa [h_UU] using h_idem
  exact ⟨U, h_pi, h_U_P, h_ker_U⟩

/-- The absolute value satisfies |T| = U†T where T = U|T| from polar decomposition.
    This is a key fact: for partial isometry U with T = U|T| and ker U = ker T,
    we have U†U|T| = |T| since U†U is a projection onto (ker U)⟂ = (ker |T|)⟂
    and |T| maps into (ker |T|)⟂. -/
lemma absoluteValue_eq_adjoint_mul_of_polar {T : H →L[ℂ] H} {U : H →L[ℂ] H}
    (hU : IsPartialIsometry U) (h_polar : T = U * absoluteValue T)
    (h_ker : LinearMap.ker U.toLinearMap = LinearMap.ker T.toLinearMap) :
    absoluteValue T = U.adjoint * T := by
  have h_ker_abs : LinearMap.ker (absoluteValue T).toLinearMap = LinearMap.ker T.toLinearMap :=
    absoluteValue_ker_eq_ker T
  have h_ker_U_abs : LinearMap.ker U.toLinearMap = LinearMap.ker (absoluteValue T).toLinearMap := by
    rw [h_ker, h_ker_abs]
  -- P = U† U is idempotent (hU gives P * P = P)
  let P := U.adjoint * U
  have hP_idem : P * P = P := hU
  -- Need to show: |T| = U† T = U† U |T| = P |T|
  -- Using h_polar: T = U * |T|, so U† T = U† U |T| = P |T|
  -- We claim P acts as identity on range(|T|), so P |T| x = |T| x
  ext x
  -- Goal: |T| x = (U† * T) x = U† (T x)
  rw [mul_apply]
  -- Goal: |T| x = U† (T x) = U† (U (|T| x)) using h_polar
  conv_rhs => rw [h_polar]
  simp only [mul_apply]
  -- Goal: |T| x = U† (U (|T| x)) = P (|T| x)
  -- First show range(|T|) ⊆ (ker |T|)⟂
  have h_range_perp : LinearMap.range (absoluteValue T).toLinearMap ≤
      (LinearMap.ker (absoluteValue T).toLinearMap)ᗮ := by
    intro y hy
    rw [Submodule.mem_orthogonal]
    intro z hz
    rw [LinearMap.mem_ker] at hz
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hy
    rw [← hw]
    have hsa := absoluteValue_isSelfAdjoint T
    -- ⟪z, |T| w⟫ = ⟪|T| z, w⟫ = ⟪0, w⟫ = 0
    have hz' : (absoluteValue T) z = 0 := hz
    calc ⟪z, (absoluteValue T) w⟫_ℂ
        = ⟪(absoluteValue T) z, w⟫_ℂ := by rw [← adjoint_inner_left, hsa.adjoint_eq]
      _ = ⟪(0 : H), w⟫_ℂ := by rw [hz']
      _ = 0 := inner_zero_left _
  -- |T| x ∈ (ker |T|)⟂
  have h_in_perp : (absoluteValue T) x ∈ (LinearMap.ker (absoluteValue T).toLinearMap)ᗮ :=
    h_range_perp (LinearMap.mem_range_self _ x)
  -- Now show P = U†U acts as identity on (ker U)⟂ = (ker |T|)⟂
  -- ker P = ker U (standard fact for P = U†U)
  have h_kerP_eq_kerU : LinearMap.ker P.toLinearMap = LinearMap.ker U.toLinearMap := by
    ext y
    simp only [LinearMap.mem_ker]
    constructor
    · intro hy
      -- P y = U† U y = 0 ⇒ ‖U y‖² = ⟨U y, U y⟩ = ⟨y, U† U y⟩ = 0 ⇒ U y = 0
      have h0 : ‖U y‖ ^ 2 = 0 := by
        rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
        rw [← adjoint_inner_right]
        have hy' : U.adjoint (U y) = 0 := by simpa [P, mul_apply] using hy
        simp [hy']
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp h0)
    · intro hy
      -- U y = 0 implies P y = U† (U y) = U† 0 = 0
      -- hy : ↑U y = 0, i.e., U.toLinearMap y = 0
      have hy' : U y = 0 := hy
      change (U.adjoint) (U y) = 0
      rw [hy', map_zero]
  -- P is self-adjoint
  have h_sa : IsSelfAdjoint P := IsSelfAdjoint.star_mul_self U
  -- P is symmetric
  have hP_symm : (P : H →ₗ[ℂ] H).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 h_sa
  -- (range P)⟂ = ker P (from symmetry + idempotent)
  have h_orth : (LinearMap.range P.toLinearMap)ᗮ = LinearMap.ker P.toLinearMap :=
    (ContinuousLinearMap.IsIdempotentElem.isSymmetric_iff_orthogonal_range hP_idem).1 hP_symm
  -- range P is closed
  have h_range_closed : IsClosed (LinearMap.range P.toLinearMap : Set H) :=
    IsIdempotentElem.isClosed_range hP_idem
  -- (ker P)⟂ = range P
  have h_eq_range : (LinearMap.ker P.toLinearMap)ᗮ = LinearMap.range P.toLinearMap := by
    calc (LinearMap.ker P.toLinearMap)ᗮ = (LinearMap.range P.toLinearMap)ᗮᗮ := by simp [h_orth]
      _ = (LinearMap.range P.toLinearMap).topologicalClosure :=
        Submodule.orthogonal_orthogonal_eq_closure _
      _ = LinearMap.range P.toLinearMap :=
        IsClosed.submodule_topologicalClosure_eq h_range_closed
  -- |T| x ∈ (ker P)⟂ = range P
  have h_in_kerP_perp : (absoluteValue T) x ∈ (LinearMap.ker P.toLinearMap)ᗮ := by
    rw [h_kerP_eq_kerU, h_ker_U_abs]
    exact h_in_perp
  have h_in_range : (absoluteValue T) x ∈ LinearMap.range P.toLinearMap := by
    rw [← h_eq_range]
    exact h_in_kerP_perp
  -- P acts as identity on range P
  obtain ⟨y, hy⟩ := h_in_range
  -- hy : P y = |T| x
  -- We want: |T| x = U† (U (|T| x)) = P (|T| x)
  -- Since |T| x = P y and P is idempotent: P (|T| x) = P (P y) = P y = |T| x
  have h_Py_eq : P y = (absoluteValue T) x := hy
  calc (absoluteValue T) x = P y := hy.symm
    _ = (P * P) y := by rw [hP_idem]
    _ = P (P y) := rfl
    _ = P ((absoluteValue T) x) := by rw [h_Py_eq]
    _ = U.adjoint (U ((absoluteValue T) x)) := rfl
