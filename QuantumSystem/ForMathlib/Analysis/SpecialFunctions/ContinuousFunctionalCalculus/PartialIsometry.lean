module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section

open ContinuousLinearMap InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A continuous linear map `U` is a partial isometry if `U†U` is a projection. -/
def IsPartialIsometry (U : H →L[ℂ] H) : Prop :=
  U.adjoint * U * (U.adjoint * U) = U.adjoint * U

/-- Alternative characterization: U is a partial isometry iff UU†U = U. -/
lemma isPartialIsometry_iff (U : H →L[ℂ] H) :
    IsPartialIsometry U ↔ U * U.adjoint * U = U := by
  constructor
  · intro h
    -- U†U is a projection P.
    -- We want to show U P = U.
    -- Is equivalent to U (1 - P) = 0.
    -- || U (1 - P) x ||² = ⟨ (1-P)x, U† U (1-P) x ⟩ = ⟨ (1-P)x, P (1-P) x ⟩ = 0
    let P := U.adjoint * U
    have hP : P * P = P := h
    have h_orth : U * (1 - P) = 0 := by
      ext x
      refine norm_eq_zero.mp ?_
      have h0 : ‖(U * (1 - P)) x‖ ^ 2 = 0 := by
        rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (x := (U * (1 - P)) x)]
        change Complex.re ⟪U ((1 - P) x), U ((1 - P) x)⟫_ℂ = 0
        rw [← adjoint_inner_right]
        -- rewrite `U† (U ((1 - P) x))` as `P ((1 - P) x)`
        simp only [P]
        -- U† U (x - P x) = P (x - P x) = P x - P² x = P x - P x = 0
        have hPP : P (P x) = P x := by
          simpa [P, ContinuousLinearMap.mul_apply, mul_assoc] using
            congrArg (fun T => T x) hP
        have h1 : (1 - P) x = x - P x := by
          simp [sub_eq_add_neg]
        have h2 : P ((1 - P) x) = P x - P (P x) := by
          rw [h1, map_sub]
        have h3 : U.adjoint (U (x - P x)) = P (x - P x) := by rfl
        rw [h1, h3, map_sub, hPP, sub_self, inner_zero_right, Complex.zero_re]
      exact (sq_eq_zero_iff.mp h0)
    have h_orth' : U * (P - 1) = 0 := by
      calc
        U * (P - 1) = U * (-(1 - P)) := by
          simp [sub_eq_add_neg, add_comm]
        _ = - (U * (1 - P)) := by
          simp [sub_eq_add_neg, mul_add, mul_one, add_comm]
        _ = 0 := by simp [h_orth]
    -- `U * (P - 1) = 0` rewrites to `U * U† * U - U = 0`
    have h_orth'' : U * U.adjoint * U - U = 0 := by
      simpa [P, mul_sub, mul_assoc, mul_one] using h_orth'
    have h_eq : U * U.adjoint * U = U := by
      calc
        U * U.adjoint * U = (U * U.adjoint * U - U) + U := by abel
        _ = 0 + U := by simp [h_orth'']
        _ = U := by simp
    exact h_eq
  · intro h
    -- We want IsPartialIsometry U, i.e., U† U U† U = U† U
    have h_adj : U.adjoint * U * U.adjoint = U.adjoint := by
      -- take adjoint of `U * U† * U = U`
      simpa [mul_def, adjoint_comp, adjoint_adjoint, mul_assoc] using
        congrArg ContinuousLinearMap.adjoint h
    calc
      U.adjoint * U * (U.adjoint * U)
          = (U.adjoint * U * U.adjoint) * U := by simp [mul_assoc]
      _ = U.adjoint * U := by simp [h_adj]

/-- The adjoint of a partial isometry is a partial isometry. -/
lemma IsPartialIsometry.adjoint {U : H →L[ℂ] H} (hU : IsPartialIsometry U) :
    IsPartialIsometry U.adjoint := by
  rw [isPartialIsometry_iff] at hU ⊢
  -- We want U† U†† U† = U†.
  -- i.e., U† U U† = U†.
  rw [adjoint_adjoint]
  -- We know U U† U = U. Taking adjoint gives U† U U† = U†.
  -- take adjoint of `U * U† * U = U`
  simpa [mul_def, adjoint_comp, adjoint_adjoint, mul_assoc] using
    congrArg ContinuousLinearMap.adjoint hU

/-- A partial isometry is an isometry on the orthogonal complement of its kernel.
    Note: (ker U)ᗮ = range U†. -/
lemma IsPartialIsometry.norm_of_mem_initialSpace {U : H →L[ℂ] H}
    (hU : IsPartialIsometry U) (x : H) (hx : x ∈ (LinearMap.ker U.toLinearMap)ᗮ) :
    ‖U x‖ = ‖x‖ := by
  -- ‖U x‖² = ⟨x, U† U x⟩.
  -- If x ∈ (ker U)ᗮ, then x ∈ range U† (since range U† is closed? In finite dim yes.
  -- In general, (ker U)ᗮ = closure (range U†).
  -- Wait, U† U is a projection onto range U†.
  -- Let P = U† U. If hU, P is a projection.
  -- range P = range U† (standard fact for P = T* T? No, range P ⊆ range U†. Also range U† U ⊆ range U†.
  -- Actually range U† = range (U† U) because range U† U ⊆ range U†.
  -- And if y = U† z, U† U y = U† U U† z = U† z = y using U U† U = U.
  -- So range U† ⊆ range P. Thus range P = range U†.
  -- P is an orthogonal projection onto range U†.
  -- So for x ∈ range U†, P x = x.
  -- ‖U x‖² = ⟨x, P x⟩ = ⟨x, x⟩ = ‖x‖².

  -- But argument x is in (ker U)ᗮ.
  -- We need to know P is the projection onto (ker U)ᗮ.
  -- ker P = ker (U† U) = ker U.
  -- So range P = (ker P)ᗮ = (ker U)ᗮ.
  -- So x ∈ range P.
  let P := U.adjoint * U
  have hP_proj : P * P = P := hU
  -- We want to show ⟨x, P x⟩ = ⟨x, x⟩
  have h_P_mem : P x = x := by
    -- P is orthogonal projection onto range P.
    -- range P = (ker P)ᗮ = (ker U)ᗮ.
    -- Wait, P is self-adjoint idempotent, so it is orthogonal projection onto range P.
    -- range P = (ker P)ᗮ because P is self-adjoint.
    -- ker P = ker U?
    -- ker U ⊆ ker P: U x = 0 → U† U x = 0.
    -- ker P ⊆ ker U: U† U x = 0 → ⟨x, U† U x⟩ = 0 → ‖U x‖² = 0 → U x = 0.
    -- So ker P = ker U.
    -- Therefore range P = (ker U)ᗮ.
    -- Since x ∈ (ker U)ᗮ, x ∈ range P.
    -- So P x = x.

    -- Let's prove ker P = ker U formally.
    have h_ker : LinearMap.ker P.toLinearMap = LinearMap.ker U.toLinearMap := by
      ext y
      simp only [LinearMap.mem_ker] -- `P.toLinearMap y` is definitionaly `P y`
      constructor
      · intro hy
        -- U† U y = 0 ⇒ U y = 0
        have h0 : ‖U y‖ ^ 2 = 0 := by
          rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (x := U y)]
          rw [← adjoint_inner_right]
          -- `U† (U y) = P y = 0`
          have hy' : U.adjoint (U y) = 0 := by
            simpa [P, ContinuousLinearMap.mul_apply] using hy
          simp [hy', inner_zero_right]
        have h1 : ‖U y‖ = 0 := (sq_eq_zero_iff.mp h0)
        exact (norm_eq_zero.mp h1)
      · intro hy
        dsimp [P]
        calc
          (U.adjoint) (U y) = U.adjoint 0 := by
            have hy' : U y = 0 := by simpa using hy
            simp [hy']
          _ = 0 := by simp
    -- P is self-adjoint
    have h_sa : IsSelfAdjoint P := by
      -- `(U†U)† = U†U`
      simpa [P, star_eq_adjoint] using (IsSelfAdjoint.star_mul_self U)
    -- range P is closed?
    -- range P = ker(1-P). Since P is continuous, ker(1-P) is closed.
    -- So range P is closed.
    -- For orthogonal projection P, range P = (ker P)ᗮ.
    -- We need this fact from Mathlib. `LinearMap.isProj_iff_idempotent_and_...`?
    -- Actually `OrthogonalProjection` exists.
    -- But we defined IsPartialIsometry manually.

    -- Let's rely on P x = x iff x ∈ (ker P)ᗮ.
    -- Mathlib has `orthogonalProjection_eq_self_iff`.
    -- We can construct the `orthogonalProjection` structure from P.

    -- Or just prove manually:
    -- If x ∈ (ker P)ᗮ, then P x - x ∈ ?
    -- P(P x - x) = P x - P x = 0. So P x - x ∈ ker P.
    -- Also P x - x ∈ range P + x? No.
    -- P x ∈ range P = (ker P)ᗮ.
    -- So P x - x ∈ (ker P)ᗮ.
    -- The only vector in intersection of ker P and (ker P)ᗮ is 0.
    -- So P x = x.

    -- Use the idempotent+symmetry characterization to identify the range.
    have hP_idem : IsIdempotentElem P := hP_proj
    have hP_symm : (P : H →ₗ[ℂ] H).IsSymmetric :=
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).1 h_sa
    have h_orth : (LinearMap.range P.toLinearMap)ᗮ = LinearMap.ker P.toLinearMap :=
      (ContinuousLinearMap.IsIdempotentElem.isSymmetric_iff_orthogonal_range hP_idem).1 hP_symm
    have h_range_closed : IsClosed (LinearMap.range P.toLinearMap : Set H) :=
      (IsIdempotentElem.isClosed_range (p := P) hP_idem)
    -- Hence (ker P)ᗮ = range P
    have h_eq_range : (LinearMap.ker P.toLinearMap)ᗮ = LinearMap.range P.toLinearMap := by
      calc
        (LinearMap.ker P.toLinearMap)ᗮ = (LinearMap.range P.toLinearMap)ᗮᗮ := by
          simp [h_orth]
        _ = (LinearMap.range P.toLinearMap).topologicalClosure := by
          simpa using (Submodule.orthogonal_orthogonal_eq_closure
            (K := LinearMap.range P.toLinearMap))
        _ = LinearMap.range P.toLinearMap :=
          (IsClosed.submodule_topologicalClosure_eq h_range_closed)
    -- rewrite `hx` into membership in range P
    have hx' : x ∈ (LinearMap.ker P.toLinearMap)ᗮ := by
      simpa [h_ker] using hx
    have hx_range : x ∈ LinearMap.range P.toLinearMap := by
      simpa [h_eq_range] using hx'
    rcases hx_range with ⟨y, rfl⟩
    -- `P (P y) = P y`
    simpa [P, mul_assoc, ContinuousLinearMap.mul_apply] using
      congrArg (fun T => T y) hP_proj
  -- Now compute squared norms using `P x = x`.
  have hsq : ‖U x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (x := U x)]
    change Complex.re ⟪U x, U x⟫_ℂ = ‖x‖ ^ 2
    rw [← adjoint_inner_right]
    have hPx : U.adjoint (U x) = P x := by rfl
    rw [hPx, h_P_mem]
    simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) (x := x))
  have hnonneg1 : 0 ≤ ‖U x‖ := norm_nonneg _
  have hnonneg2 : 0 ≤ ‖x‖ := norm_nonneg _
  have hsq' : ‖U x‖ = ‖x‖ := by
    have h' := sq_eq_sq_iff_eq_or_eq_neg.mp (by simpa [pow_two] using hsq)
    cases h' with
    | inl h => exact h
    | inr h => nlinarith
  exact hsq'

/-- For a partial isometry U, U†U = id on (ker U)ᗮ -/
lemma IsPartialIsometry.adjoint_mul_self_apply_of_mem_ker_orthogonal {U : H →L[ℂ] H}
    (hU : IsPartialIsometry U)
    (x : H) (hx : x ∈ (LinearMap.ker U.toLinearMap)ᗮ) :
    U.adjoint (U x) = x := by
  let P := U.adjoint * U
  have hP_proj : P * P = P := hU
  have h_sa : IsSelfAdjoint P := IsSelfAdjoint.star_mul_self U
  have h_ker_P : LinearMap.ker P.toLinearMap = LinearMap.ker U.toLinearMap := by
    ext y
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    constructor
    · intro hy
      have h0 : ‖U y‖ ^ 2 = 0 := by
        rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← adjoint_inner_right]
        have : U.adjoint (U y) = P y := rfl
        rw [this, hy, inner_zero_right]
        rfl
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp h0)
    · intro hy
      change P y = 0
      calc P y = (U.adjoint * U) y := rfl
        _ = U.adjoint (U y) := rfl
        _ = U.adjoint 0 := by rw [hy]
        _ = 0 := map_zero _
  have hP_idem : IsIdempotentElem P := hP_proj
  have hP_symm : (P : H →ₗ[ℂ] H).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 h_sa
  have h_orth : (LinearMap.range P.toLinearMap)ᗮ = LinearMap.ker P.toLinearMap :=
    (ContinuousLinearMap.IsIdempotentElem.isSymmetric_iff_orthogonal_range hP_idem).1 hP_symm
  have h_range_closed : IsClosed (LinearMap.range P.toLinearMap : Set H) :=
    IsIdempotentElem.isClosed_range hP_idem
  have h_eq_range : (LinearMap.ker P.toLinearMap)ᗮ = LinearMap.range P.toLinearMap := by
    calc (LinearMap.ker P.toLinearMap)ᗮ = (LinearMap.range P.toLinearMap)ᗮᗮ := by simp [h_orth]
      _ = (LinearMap.range P.toLinearMap).topologicalClosure := by
        simpa using Submodule.orthogonal_orthogonal_eq_closure (K := LinearMap.range P.toLinearMap)
      _ = LinearMap.range P.toLinearMap := IsClosed.submodule_topologicalClosure_eq h_range_closed
  have hx' : x ∈ (LinearMap.ker P.toLinearMap)ᗮ := by rw [h_ker_P]; exact hx
  have hx_range : x ∈ LinearMap.range P.toLinearMap := by rw [h_eq_range] at hx'; exact hx'
  rcases hx_range with ⟨y, hy⟩
  calc U.adjoint (U x) = P x := rfl
    _ = P (P y) := by
      congr 1
      exact hy.symm
    _ = P y := by
      have := congrArg (· y) hP_proj
      simp only [mul_apply] at this
      exact this
    _ = x := hy

/-- A partial isometry has operator norm at most 1.
    This follows from ‖U x‖ = ‖x‖ on (ker U)ᗮ and ‖U x‖ = 0 on ker U. -/
lemma IsPartialIsometry.norm_le_one {U : H →L[ℂ] H} (hU : IsPartialIsometry U) :
    ‖U‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp only [one_mul]
  -- Use U†U is a self-adjoint idempotent (projection)
  let P := U.adjoint * U
  have hP_idem : P * P = P := hU
  have hP_sa : IsSelfAdjoint P := IsSelfAdjoint.star_mul_self U
  -- ‖U x‖² = ⟨x, U†U x⟩ = ⟨x, P x⟩
  have h_norm_sq : ‖U x‖ ^ 2 = (⟪x, P x⟫_ℂ).re := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
    change Complex.re ⟪U x, U x⟫_ℂ = (⟪x, P x⟫_ℂ).re
    rw [← adjoint_inner_right]
    rfl
  -- For self-adjoint idempotent P: 0 ≤ ⟨x, P x⟩ ≤ ⟨x, x⟩
  -- ⟨x, Px⟩ = ⟨Px, Px⟩ since P² = P and P = P†
  have h_Px_eq : (⟪x, P x⟫_ℂ).re = ‖P x‖ ^ 2 := by
    have hPsa : P.adjoint = P := hP_sa.adjoint_eq
    have hPPx : P (P x) = P x := by
      have := congrArg (fun T => T x) hP_idem
      simp only [mul_apply] at this
      exact this
    -- ⟨x, Px⟩ = ⟨x, PPx⟩ = ⟨P†x, Px⟩ = ⟨Px, Px⟩
    calc (⟪x, P x⟫_ℂ).re
      _ = (⟪x, P (P x)⟫_ℂ).re := by rw [hPPx]
      _ = (⟪P.adjoint x, P x⟫_ℂ).re := by rw [adjoint_inner_left]
      _ = (⟪P x, P x⟫_ℂ).re := by rw [hPsa]
      _ = ‖P x‖ ^ 2 := by rw [inner_self_eq_norm_sq_to_K]; norm_cast
  -- Similarly for 1 - P
  have h_1mP : (⟪x, (1 - P) x⟫_ℂ).re = ‖(1 - P) x‖ ^ 2 := by
    let Q := 1 - P
    have hQ_idem : Q * Q = Q := by
      ext y
      simp only [Q, mul_apply, sub_apply, one_apply]
      have hPPy : P (P y) = P y := by
        have := congrArg (fun T => T y) hP_idem
        simp only [mul_apply] at this
        exact this
      simp [hPPy]
    have hQ_sa : IsSelfAdjoint Q := by
      simp only [Q, IsSelfAdjoint, star_sub, star_one]
      rw [hP_sa.star_eq]
    have hQsa : Q.adjoint = Q := hQ_sa.adjoint_eq
    have hQQx : Q (Q x) = Q x := by
      have := congrArg (fun T => T x) hQ_idem
      simp only [mul_apply] at this
      exact this
    calc (⟪x, Q x⟫_ℂ).re
      _ = (⟪x, Q (Q x)⟫_ℂ).re := by rw [hQQx]
      _ = (⟪Q.adjoint x, Q x⟫_ℂ).re := by rw [adjoint_inner_left]
      _ = (⟪Q x, Q x⟫_ℂ).re := by rw [hQsa]
      _ = ‖Q x‖ ^ 2 := by rw [inner_self_eq_norm_sq_to_K]; norm_cast
  -- ⟨x, x⟩ = ⟨x, P x⟩ + ⟨x, (1-P) x⟩
  have h_decomp : (⟪x, x⟫_ℂ).re = (⟪x, P x⟫_ℂ).re + (⟪x, (1 - P) x⟫_ℂ).re := by
    have h1 : ⟪x, x⟫_ℂ = ⟪x, P x⟫_ℂ + ⟪x, (1 - P) x⟫_ℂ := by
      rw [← inner_add_right]
      congr 1
      simp [sub_apply]
    rw [h1, Complex.add_re]
  have h_Px_le : (⟪x, P x⟫_ℂ).re ≤ (⟪x, x⟫_ℂ).re := by
    rw [h_decomp, h_1mP]
    linarith [sq_nonneg ‖(1 - P) x‖]
  have h_inner_xx : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  -- ‖U x‖² ≤ ‖x‖²
  have h_sq_le : ‖U x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [h_norm_sq]
    calc (⟪x, P x⟫_ℂ).re ≤ (⟪x, x⟫_ℂ).re := h_Px_le
      _ = ‖x‖ ^ 2 := h_inner_xx
  -- ‖U x‖ ≤ ‖x‖
  have h_nonneg_Ux : 0 ≤ ‖U x‖ := norm_nonneg _
  have h_nonneg_x : 0 ≤ ‖x‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖U x‖ - ‖x‖), sq_nonneg (‖U x‖ + ‖x‖)]
