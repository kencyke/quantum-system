module

public import Mathlib.Analysis.Normed.Operator.Compact
public import QuantumSystem.Analysis.CFC.PolarDecomposition
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.Adjoint
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.l2Space

/-!
# Compact operators and spectral theory helpers

This file collects compact-operator infrastructure and spectral decomposition results
used by the trace-class development.
-/

@[expose] public section

open scoped InnerProductSpace
open Complex

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ContinuousLinearMap

namespace TraceClass

section SpectralDecomposition

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

open InnerProductSpace NNReal

omit [CompleteSpace E] in
/-- Conversion between IsCompactOperator and compactness of image of closed ball. -/
theorem isCompactOperator_iff_isCompact_image_closedBall (T : E →L[ℂ] E) :
    IsCompactOperator T ↔ IsCompact (closure (T '' Metric.closedBall 0 1)) := by
  constructor
  · intro h
    exact h.isCompact_closure_image_closedBall 1
  · intro h
    have h' : IsCompactOperator (T.toLinearMap : E →ₗ[ℂ] E) := by
      rw [isCompactOperator_iff_isCompact_closure_image_closedBall T.toLinearMap (by norm_num : (0 : ℝ) < 1)]
      exact h
    exact h'

omit [CompleteSpace E] in
/-- Compact operators are exactly those with relatively compact image of closed ball. -/
theorem isCompact_image_of_isCompactOperator {T : E →L[ℂ] E} (hT : IsCompactOperator T) :
    IsCompact (closure (T '' Metric.closedBall 0 1)) :=
  (isCompactOperator_iff_isCompact_image_closedBall T).mp hT

/-! ### Compact operator infrastructure -/

omit [CompleteSpace E] in
/-- A continuous linear map with finite dimensional range is a compact operator.

This is a standard result: a closed bounded set in a finite dimensional normed space
is compact (Heine-Borel), so the image of the closed unit ball (which is contained
in the closed finite dimensional range) has compact closure. -/
theorem isCompactOperator_of_finiteDimensional_range {T : E →L[ℂ] E}
    (h : FiniteDimensional ℂ (LinearMap.range T)) : IsCompactOperator T := by
  rw [isCompactOperator_iff_isCompact_image_closedBall]
  -- Lift to the range
  let F := LinearMap.range T
  haveI : FiniteDimensional ℂ F := h
  let T' : E →L[ℂ] F := T.codRestrict F (fun x => LinearMap.mem_range_self T x)
  -- The image of the ball under T'
  let B := Metric.closedBall (0 : E) 1
  let im' := T' '' B
  -- Boundedness
  have h_bound : Bornology.IsBounded im' := by
    rw [Metric.isBounded_iff_subset_ball 0]
    use ‖T'‖ + 1
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [Metric.mem_ball, dist_zero_right]
    simp only at hy
    rw [Metric.mem_closedBall, dist_zero_right] at hy
    calc ‖T' y‖ ≤ ‖T'‖ * ‖y‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖T'‖ * 1 := by gcongr
      _ = ‖T'‖ := mul_one _
      _ < ‖T'‖ + 1 := lt_add_one _
  -- In a finite dimensional space, bounded sets have compact closure
  have h_compact' : IsCompact (closure im') :=
    Bornology.IsBounded.isCompact_closure h_bound
  -- Map back to E
  let ι : F →L[ℂ] E := Submodule.subtypeL F
  have h_im_eq : T '' B = ι '' im' := by
    ext x
    simp only [Set.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨T' y, ⟨y, hy, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, rfl⟩
  rw [h_im_eq]
  -- ι is continuous, so image of compact matches
  let K := ι '' (closure im')
  have hK_compact : IsCompact K := h_compact'.image ι.continuous
  -- closure (ι '' im') ⊆ K because K is closed and ι '' im' ⊆ K
  have h_sub : closure (ι '' im') ⊆ K := by
    apply closure_minimal _ hK_compact.isClosed
    exact Set.image_mono subset_closure
  -- Closed subset of compact is compact
  exact IsCompact.of_isClosed_subset hK_compact isClosed_closure h_sub

/-- The range of the adjoint of an operator with finite dimensional range is finite dimensional. -/
lemma finiteDimensional_range_adjoint_of_finiteDimensional_range {T : E →L[ℂ] E}
    (h : FiniteDimensional ℂ (LinearMap.range T)) :
    FiniteDimensional ℂ (LinearMap.range T.adjoint) := by
  let F := LinearMap.range T
  haveI : FiniteDimensional ℂ F := h
  let T' : E →L[ℂ] F := T.codRestrict F (fun x => LinearMap.mem_range_self T x)
  let ι : F →L[ℂ] E := Submodule.subtypeL F
  have hT : T = ι.comp T' := by ext; rfl
  rw [hT, ContinuousLinearMap.adjoint_comp]
  -- ι† is the orthogonal projection onto F
  have h_adj_iota : ι.adjoint = Submodule.orthogonalProjection F := Submodule.adjoint_subtypeL F
  rw [h_adj_iota]
  -- Range of T† is image of F under T'†
  have h_le : LinearMap.range (T'.adjoint.comp (Submodule.orthogonalProjection F)) ≤ LinearMap.range T'.adjoint :=
    LinearMap.range_comp_le_range _ _
  exact Submodule.finiteDimensional_of_le h_le

omit [CompleteSpace E] in
/-- Compact operators can be approximated by finite-rank operators. -/
lemma exists_finiteDimensional_range_approx_of_isCompactOperator {T : E →L[ℂ] E}
    (hT : IsCompactOperator T) (ε : ℝ) (hε : 0 < ε) :
    ∃ (F : E →L[ℂ] E), FiniteDimensional ℂ (LinearMap.range F) ∧ ‖T - F‖ < ε := by
  -- The image of the closed unit ball has compact closure
  let K := closure (T '' Metric.closedBall 0 1)
  have hK : IsCompact K := (isCompactOperator_iff_isCompact_image_closedBall T).mp hT
  -- Cover K with ε/3 balls
  have h_metric := Metric.totallyBounded_iff.mp hK.totallyBounded
  obtain ⟨s, hs_fin, hs_cover⟩ := h_metric (ε / 3) (by linarith)
  -- Define the finite-dimensional subspace V spanned by the cover centers
  let V := Submodule.span ℂ s
  haveI : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ hs_fin
  -- Define P as projection onto V followed by inclusion
  let P := Submodule.starProjection V
  let F := P.comp T
  refine ⟨F, ?_, ?_⟩
  · -- Range of F ⊆ V
    have h_range : LinearMap.range F ≤ V := by
      rintro y ⟨x, rfl⟩
      exact Submodule.coe_mem _
    exact Submodule.finiteDimensional_of_le h_range
  · -- ‖T - F‖ < ε
    -- First prove ‖T - F‖ ≤ 2ε/3
    have hP_norm : ‖P‖ ≤ 1 := by
      simpa [P] using (Submodule.starProjection_norm_le (K := V))
    have h_bound : ‖T - F‖ ≤ 2 * (ε / 3) := by
      apply ContinuousLinearMap.opNorm_le_bound _ (by linarith)
      intro x
      by_cases hx0 : x = 0
      · simp [hx0]
      · -- Scale to the unit ball and use the covering estimate
        have hx_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
        have hx_ne' : (‖x‖ : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (ne_of_gt hx_pos)
        set u := (‖x‖⁻¹ : ℂ) • x with hu_def
        have hu_norm : ‖u‖ = 1 := by
          calc
            ‖u‖ = ‖(‖x‖⁻¹ : ℂ)‖ * ‖x‖ := by simp [hu_def, norm_smul]
            _ = (‖x‖)⁻¹ * ‖x‖ := by simp [norm_inv, Complex.norm_real]
            _ = 1 := by
              simpa using inv_mul_cancel₀ (ne_of_gt hx_pos)
        have hTu_in_K : T u ∈ K := subset_closure (Set.mem_image_of_mem T (by simp [hu_norm]))
        obtain ⟨y, hy_mem, hy_dist⟩ := Set.mem_iUnion₂.mp (hs_cover hTu_in_K)
        rw [Metric.mem_ball, dist_eq_norm] at hy_dist
        have hy_in_V : y ∈ V := Submodule.subset_span hy_mem
        have hPy : P y = y := by
          simpa [P] using (Submodule.starProjection_eq_self_iff (K := V) (v := y)).mpr hy_in_V
        have h_u_diff : ‖(T - F) u‖ ≤ 2 * (ε / 3) := by
          calc ‖(T - F) u‖
            _ = ‖T u - P (T u)‖ := by simp [F]
            _ = ‖(T u - y) - (P (T u) - y)‖ := by
              simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
            _ ≤ ‖T u - y‖ + ‖P (T u) - y‖ := norm_sub_le _ _
            _ = ‖T u - y‖ + ‖P (T u) - P y‖ := by rw [hPy]
            _ = ‖T u - y‖ + ‖P (T u - y)‖ := by rw [map_sub]
            _ ≤ ‖T u - y‖ + ‖P‖ * ‖T u - y‖ := by
              gcongr
              exact ContinuousLinearMap.le_opNorm P _
            _ ≤ ‖T u - y‖ + 1 * ‖T u - y‖ := by gcongr
            _ = 2 * ‖T u - y‖ := by ring
            _ ≤ 2 * (ε / 3) := by nlinarith
        have h_x_eq : x = (‖x‖ : ℂ) • u := by
          have h_x_eq' : (‖x‖ : ℂ) • u = x := by
            simp [hu_def, smul_smul, mul_inv_cancel₀ hx_ne']
          simp [h_x_eq']
        have h_x_eq_norm : ‖(T - F) x‖ = ‖(T - F) ((‖x‖ : ℂ) • u)‖ := by
          simpa using congrArg (fun z => ‖(T - F) z‖) h_x_eq
        calc ‖(T - F) x‖
          _ = ‖(T - F) ((‖x‖ : ℂ) • u)‖ := h_x_eq_norm
          _ = ‖(‖x‖ : ℂ) • (T - F) u‖ := by rw [map_smul]
          _ = ‖(‖x‖ : ℂ)‖ * ‖(T - F) u‖ := norm_smul _ _
          _ = ‖x‖ * ‖(T - F) u‖ := by simp [Complex.norm_real]
          _ ≤ ‖x‖ * (2 * (ε / 3)) := by gcongr
          _ = 2 * (ε / 3) * ‖x‖ := by ring
    linarith

omit [CompleteSpace H] in
/-- A key lemma: for a positive compact operator A with eigenbasis b and eigenvalues σ,
    A can be written as a sum of rank-one operators. -/
lemma positive_compact_eq_tsum_rankOne
    {ι : Type*} (A : H →L[ℂ] H)
    (b : HilbertBasis ι ℂ H) (σ : ι → ℝ) (hσ_eig : ∀ i, A (b i) = σ i • b i) :
    ∀ x, A x = ∑' i, (σ i : ℂ) • ⟪b i, x⟫_ℂ • b i := by
  intro x
  -- Use that x = ∑' i, ⟨b i, x⟩ b i by HilbertBasis
  have hrepr : ∀ i, b.repr x i = ⟪b i, x⟫_ℂ := fun i => HilbertBasis.repr_apply_apply b x i
  have hx : x = ∑' i, ⟪b i, x⟫_ℂ • b i := by
    convert (b.hasSum_repr x).tsum_eq.symm using 1
    congr 1
    ext i
    rw [hrepr]
  conv_lhs => rw [hx]
  -- A is continuous, so A (∑' ...) = ∑' A (...)
  have hsum : Summable (fun i => ⟪b i, x⟫_ℂ • b i) := by
    convert (b.hasSum_repr x).summable using 1
    ext i
    rw [hrepr]
  rw [A.map_tsum hsum]
  congr 1
  ext i
  rw [A.map_smul, hσ_eig i]
  -- Need: ⟪b i, x⟫_ℂ • σ i • b i = (σ i : ℂ) • ⟪b i, x⟫_ℂ • b i
  have h_smul_eq : σ i • b i = (σ i : ℂ) • b i := rfl
  rw [h_smul_eq, smul_smul, smul_smul, mul_comm]

/-- The adjoint of a compact operator is compact.

This is a standard result in functional analysis. The standard proof uses that compact operators
on a Hilbert space are norm limits of finite-rank operators (via approximation by finite-rank
projections), and the adjoint operation is a norm isometry that preserves finite rank.

**Proof strategy:**
1. Show that for any compact operator T and ε > 0, there exists a finite-rank operator F
   such that ‖T - F‖ < ε. This is done by:
   - Using that T(closedBall) has compact closure, hence is totally bounded
   - Covering T(closedBall) with finitely many ε/2-balls centered at y₁,...,yₙ
   - Taking P to be orthogonal projection onto span{y₁,...,yₙ}
   - Showing ‖PT - T‖ < ε via the triangle inequality

2. Show that the adjoint of a finite-rank operator is finite-rank:
   - If T has finite-dimensional range V, then T = ι ∘ T₀ where ι : V ↪ E is inclusion
   - Then T† = T₀† ∘ ι† = T₀† ∘ orthogonalProjection V
   - Range(T†) ⊆ V, so T† is finite-rank

3. Conclude T† is compact:
   - We have finite-rank Fₙ with ‖T - Fₙ‖ → 0
   - Then ‖T† - Fₙ†‖ = ‖(T - Fₙ)†‖ = ‖T - Fₙ‖ → 0 by isometry of adjoint
   - Fₙ† are finite-rank (step 2), hence compact
   - T† is the limit of compact operators, hence compact (by `isClosed_setOf_isCompactOperator`)
-/
theorem IsCompactOperator.adjoint {T : E →L[ℂ] E} (hT : IsCompactOperator T) :
    IsCompactOperator T.adjoint := by
  -- Approximation by finite rank
  have h_approx : ∀ (n : ℕ), ∃ (F : E →L[ℂ] E), IsCompactOperator F.adjoint ∧ ‖T.adjoint - F.adjoint‖ < (n + 1 : ℝ)⁻¹ := by
    intro n
    let ε := (n + 1 : ℝ)⁻¹
    have hε : 0 < ε := by
      simp only [ε]
      apply inv_pos.mpr
      norm_cast
      linarith
    obtain ⟨F, hF_dim, hF_dist⟩ := exists_finiteDimensional_range_approx_of_isCompactOperator hT ε hε
    refine ⟨F, ?_, ?_⟩
    · apply isCompactOperator_of_finiteDimensional_range
      apply finiteDimensional_range_adjoint_of_finiteDimensional_range
      exact hF_dim
    · rw [← map_sub, ContinuousLinearMap.adjoint.norm_map]
      exact hF_dist
  choose F hF_compact hF_dist using h_approx
  apply isCompactOperator_of_tendsto (l := Filter.atTop) (F := fun n => (F n).adjoint) (f := T.adjoint)
  · rw [Metric.tendsto_atTop]
    intro r hr
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hr
    use N
    intro n hn
    rw [dist_comm, dist_eq_norm]
    calc ‖T.adjoint - (F n).adjoint‖ < (n + 1 : ℝ)⁻¹ := hF_dist n
      _ ≤ (N + 1 : ℝ)⁻¹ := by
        have h2 : (0 : ℝ) < N + 1 := by linarith [Nat.zero_le N]
        have h3 : (N : ℝ) + 1 ≤ (n : ℝ) + 1 := by
          exact_mod_cast (Nat.succ_le_succ_iff.mpr hn)
        have h4 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
          one_div_le_one_div_of_le h2 h3
        simpa [one_div] using h4
      _ < r := by rw [one_div] at hN; exact hN
  · exact Filter.Eventually.of_forall hF_compact

/-- The absolute value of a compact operator is compact.
    This uses the polar decomposition: T = U|T| where U is a partial isometry.
    Since T is compact and equals U ∘ |T|, and U is bounded, |T| must be compact. -/
theorem IsCompactOperator.absoluteValue {T : E →L[ℂ] E} (hT : IsCompactOperator T) :
    IsCompactOperator (_root_.absoluteValue T) := by
  -- Use polar decomposition: T = U |T| where U is a partial isometry
  obtain ⟨U, hU_partial, hT_decomp, h_ker⟩ := exists_polar_decomposition T
  -- We have T = U |T| and T compact, need to show |T| compact
  -- Use adjoint: |T| = U† T is compact as composition of bounded U† with compact T
  have h_abs_eq : _root_.absoluteValue T = U.adjoint ∘L T := by
    ext x
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
    conv_rhs => rw [hT_decomp, ContinuousLinearMap.mul_apply]
    -- U†(U(|T| x)) = (U† U)(|T| x)
    -- For partial isometry U, U† U is projection onto (ker U)ᗮ
    -- Since ker U = ker T = ker |T|, we have |T| x ∈ (ker |T|)ᗮ
    -- Therefore (U† U)(|T| x) = |T| x
    let P := U.adjoint * U
    have hP_proj : P * P = P := hU_partial
    have h_ker_P : LinearMap.ker P.toLinearMap = LinearMap.ker U.toLinearMap := by
      ext y
      simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
      constructor
      · intro hy
        -- P y = 0 means (U† U) y = 0
        -- Then ‖U y‖² = ⟨U y, U y⟩ = ⟨y, U† U y⟩ = 0
        have h0 : ‖U y‖ ^ 2 = 0 := by
          rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (x := U y)]
          rw [← adjoint_inner_right]
          have : U.adjoint (U y) = P y := rfl
          rw [this, hy, inner_zero_right]
          rfl
        exact norm_eq_zero.mp (sq_eq_zero_iff.mp h0)
      · intro hy
        -- U y = 0 implies (U† U) y = U† 0 = 0
        have hy' : U y = 0 := by simpa using hy
        calc
          P y = U.adjoint (U y) := rfl
          _ = U.adjoint 0 := by simp [hy']
          _ = 0 := by simp
    have h_P_x_eq_x : P (_root_.absoluteValue T x) = _root_.absoluteValue T x := by
      -- P is orthogonal projection onto (ker U)ᗮ
      -- |T| x ∈ (ker |T|)ᗮ = (ker U)ᗮ (by h_ker)
      have h_sa : IsSelfAdjoint P :=
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr
          (IsSelfAdjoint.isSymmetric (IsSelfAdjoint.star_mul_self U))
      have hP_idem : IsIdempotentElem P := hP_proj
      have h_range_closed : IsClosed (LinearMap.range P.toLinearMap : Set E) :=
        IsIdempotentElem.isClosed_range hP_idem
      have h_orth : (LinearMap.range P.toLinearMap)ᗮ = LinearMap.ker P.toLinearMap :=
        (ContinuousLinearMap.IsIdempotentElem.isSymmetric_iff_orthogonal_range hP_idem).mp
          ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp h_sa)
      have h_eq_range : (LinearMap.ker P.toLinearMap)ᗮ = LinearMap.range P.toLinearMap := by
        calc
          (LinearMap.ker P.toLinearMap)ᗮ = (LinearMap.range P.toLinearMap)ᗮᗮ := by simp [h_orth]
          _ = (LinearMap.range P.toLinearMap).topologicalClosure := by
            simpa using Submodule.orthogonal_orthogonal_eq_closure (K := LinearMap.range P.toLinearMap)
          _ = LinearMap.range P.toLinearMap := IsClosed.submodule_topologicalClosure_eq h_range_closed
      have hx_memT : _root_.absoluteValue T x ∈ (LinearMap.ker T.toLinearMap)ᗮ := by
        intro y hy
        have hy' : _root_.absoluteValue T y = 0 := by
          have hyT : y ∈ LinearMap.ker T.toLinearMap := by
            simpa [LinearMap.mem_ker] using hy
          have hyA : y ∈ LinearMap.ker (_root_.absoluteValue T).toLinearMap := by
            simpa [absoluteValue_ker_eq_ker T] using hyT
          simpa [LinearMap.mem_ker] using hyA
        have hA : IsSelfAdjoint (_root_.absoluteValue T) := absoluteValue_isSelfAdjoint T
        calc
          ⟪y, _root_.absoluteValue T x⟫_ℂ
              = ⟪(_root_.absoluteValue T).adjoint y, x⟫_ℂ := by
                  simpa using
                    (adjoint_inner_left (A := _root_.absoluteValue T) (x := x) (y := y)).symm
          _ = ⟪_root_.absoluteValue T y, x⟫_ℂ := by simp [hA.adjoint_eq]
          _ = 0 := by simp [hy', inner_zero_left]
      have hx_mem : _root_.absoluteValue T x ∈ (LinearMap.ker U.toLinearMap)ᗮ := by
        simpa [h_ker] using hx_memT
      have hx_mem' : _root_.absoluteValue T x ∈ (LinearMap.ker P.toLinearMap)ᗮ := by
        simpa [h_ker_P] using hx_mem
      have hx_range : _root_.absoluteValue T x ∈ LinearMap.range P.toLinearMap := by
        simpa [h_eq_range] using hx_mem'
      obtain ⟨y, hy⟩ := hx_range
      rw [← hy]
      simpa [P, mul_assoc, ContinuousLinearMap.mul_apply] using congrArg (fun T => T y) hP_proj
    simpa [P, ContinuousLinearMap.mul_apply] using h_P_x_eq_x.symm
  rw [h_abs_eq]
  exact hT.clm_comp U.adjoint

/-! ### Trace-class implies compact -/

/-- An operator `T` is compact if `∑ ‖T eᵢ‖² < ∞` for some Hilbert basis `eᵢ`. -/
theorem isCompactOperator_of_summable_sq_norm {ι : Type*} {b : HilbertBasis ι ℂ E}
    {T : E →L[ℂ] E} (h : Summable (fun i => ‖T (b i)‖ ^ 2)) :
    IsCompactOperator T := by
  let F (s : Finset ι) : E →L[ℂ] E := ∑ i ∈ s, (innerSL ℂ (b i)).smulRight (T (b i))
  have hF : ∀ s, IsCompactOperator (F s) := fun s => by
    induction s using Finset.cons_induction with
    | empty =>
      simpa [F, Finset.sum_empty] using (isCompactOperator_zero : IsCompactOperator (0 : E →L[ℂ] E))
    | cons a s ha ih =>
      simp only [F, Finset.sum_cons] at *
      apply IsCompactOperator.add
      · apply isCompactOperator_of_finiteDimensional_range
        -- The range is contained in the span of `T (b a)` (rank-one operator).
        haveI : FiniteDimensional ℂ (Submodule.span ℂ ({T (b a)} : Set E)) :=
          FiniteDimensional.span_of_finite ℂ (Set.finite_singleton (T (b a)))
        have h_le : LinearMap.range ((innerSL ℂ (b a)).smulRight (T (b a))) ≤
            Submodule.span ℂ ({T (b a)} : Set E) := by
          intro y hy
          rcases hy with ⟨x, rfl⟩
          -- Show `(innerSL ℂ (b a)).smulRight (T (b a)) x` lies in `span {T (b a)}`.
          have hmem : T (b a) ∈ Submodule.span ℂ ({T (b a)} : Set E) := by
            exact Submodule.subset_span (by simp)
          have hsmul : ⟪b a, x⟫_ℂ • T (b a) ∈ Submodule.span ℂ ({T (b a)} : Set E) :=
            Submodule.smul_mem (Submodule.span ℂ ({T (b a)} : Set E)) _ hmem
          simpa [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply] using hsmul
        exact Submodule.finiteDimensional_of_le h_le
      · exact ih
  apply isCompactOperator_of_tendsto (l := Filter.atTop) (F := F) (f := T)
  · rw [Metric.tendsto_nhds]
    intro ε hε
    have hε2 : 0 < ε^2 := pow_pos hε 2
    obtain ⟨S, hS⟩ := summable_iff_vanishing_norm.mp h (ε^2 / 2) (half_pos hε2)
    rw [Filter.eventually_atTop]
    use S
    intro t ht_sup
    rw [dist_eq_norm]
    rw [← norm_neg, neg_sub]
    let s_compl := {i // i ∉ t}
    let tail_sq := ∑' i : s_compl, ‖T (b i)‖^2
    have h_tail_sum : tail_sq < ε^2 := by
      let f_sq (i : ι) := ‖T (b i)‖^2
      let f_sq_sub (i : s_compl) := f_sq i
      have h_sub_summable : Summable f_sq_sub := h.subtype _
      have h_bound : ∀ (t' : Finset s_compl), ∑ i ∈ t', f_sq_sub i ≤ ε^2 / 2 := by
        intro t'
        let t_mapped := t'.map (Function.Embedding.subtype _)
        have h_disj : Disjoint t_mapped S := by
          rw [Finset.disjoint_left]
          intro i hi_map hi_S
          rw [Finset.mem_map] at hi_map
          obtain ⟨j, _, rfl⟩ := hi_map
          exact j.property (ht_sup hi_S)
        specialize hS t_mapped h_disj
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hS
        rw [Finset.sum_map] at hS
        exact le_of_lt hS
      have h_le : tail_sq ≤ ε^2 / 2 := by
        apply tsum_le_of_sum_le' (by positivity)
        intro t'
        exact h_bound t'
      calc tail_sq ≤ ε^2 / 2 := h_le
        _ < ε^2 := half_lt_self hε2
    have h_norm_le : ‖T - F t‖ ≤ Real.sqrt tail_sq := by
      apply opNorm_le_bound _ (Real.sqrt_nonneg _)
      intro x
      by_cases hx : x = 0
      · simp [hx]
      -- set up the series representation
      let g : ι → E := fun i => ⟪b i, x⟫_ℂ • T (b i)
      have h_mul_summable : Summable (fun i : ι => ‖⟪b i, x⟫_ℂ‖ * ‖T (b i)‖) := by
        have hf : Summable (fun i : ι => ‖⟪b i, x⟫_ℂ‖ ^ (2 : ℝ)) := by
          simpa [Real.rpow_natCast] using (b.summable_norm_sq_inner' x)
        have hg : Summable (fun i : ι => ‖T (b i)‖ ^ (2 : ℝ)) := by
          simpa [Real.rpow_natCast] using h
        have hf_nonneg : ∀ i, 0 ≤ ‖⟪b i, x⟫_ℂ‖ := by intro i; exact norm_nonneg _
        have hg_nonneg : ∀ i, 0 ≤ ‖T (b i)‖ := by intro i; exact norm_nonneg _
        exact Real.summable_mul_of_Lp_Lq_of_nonneg (p := 2) (q := 2)
          (hpq := Real.HolderConjugate.two_two) hf_nonneg hg_nonneg hf hg
      have hg_summable : Summable g := by
        apply Summable.of_norm
        simpa [g, norm_smul] using h_mul_summable
      have hTx : T x = ∑' i, g i := by
        have h_repr' : (∑' i, b.repr x i • b i) = x := (b.hasSum_repr x).tsum_eq
        have hs : Summable (fun i => b.repr x i • b i) := (b.hasSum_repr x).summable
        calc
          T x = T (∑' i, b.repr x i • b i) := by
            simp [h_repr']
          _ = ∑' i, T (b.repr x i • b i) := by simpa using (T.map_tsum hs)
          _ = ∑' i, b.repr x i • T (b i) := by simp [map_smul]
          _ = ∑' i, ⟪b i, x⟫_ℂ • T (b i) := by
            refine tsum_congr ?_
            intro i
            simp [HilbertBasis.repr_apply_apply]
          _ = ∑' i, g i := by rfl
      have hFtx : F t x = ∑ i ∈ t, g i := by
        simp [F, g, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
          innerSL_apply_apply]
      have h_sum_diff : (T - F t) x = ∑' i : s_compl, g i := by
        have h_tsum_compl : (∑' i : s_compl, g i) = (∑' i, g i) - ∑ i ∈ t, g i := by
          apply (eq_sub_iff_add_eq).2
          simpa [add_comm] using (hg_summable.sum_add_tsum_compl (s := t))
        calc
          (T - F t) x = (∑' i, g i) - ∑ i ∈ t, g i := by
            simp [ContinuousLinearMap.sub_apply, hTx, hFtx]
          _ = ∑' i : s_compl, g i := by simp [h_tsum_compl]
      -- Cauchy-Schwarz on the series over the complement
      have h_mul_summable_sub : Summable (fun i : s_compl => ‖⟪b i, x⟫_ℂ‖ * ‖T (b i)‖) := by
        have hf : Summable (fun i : s_compl => ‖⟪b i, x⟫_ℂ‖ ^ (2 : ℝ)) := by
          simpa [s_compl, Real.rpow_natCast] using
            (b.summable_norm_sq_inner' x).subtype (s := fun i => i ∉ t)
        have hg : Summable (fun i : s_compl => ‖T (b i)‖ ^ (2 : ℝ)) := by
          simpa [s_compl, Real.rpow_natCast] using (h.subtype (s := fun i => i ∉ t))
        have hf_nonneg : ∀ i : s_compl, 0 ≤ ‖⟪b i, x⟫_ℂ‖ := by intro i; exact norm_nonneg _
        have hg_nonneg : ∀ i : s_compl, 0 ≤ ‖T (b i)‖ := by intro i; exact norm_nonneg _
        exact Real.summable_mul_of_Lp_Lq_of_nonneg (p := 2) (q := 2)
          (hpq := Real.HolderConjugate.two_two) hf_nonneg hg_nonneg hf hg
      have h_norm_summable : Summable (fun i : s_compl => ‖g i‖) := by
        simpa [g, norm_smul] using h_mul_summable_sub
      have h_bound_tsum :
          ∑' i : s_compl, ‖⟪b i, x⟫_ℂ‖ * ‖T (b i)‖
            ≤ Real.sqrt (∑' i : s_compl, ‖⟪b i, x⟫_ℂ‖^2) *
                Real.sqrt (∑' i : s_compl, ‖T (b i)‖^2) := by
        have hf : Summable (fun i : s_compl => ‖⟪b i, x⟫_ℂ‖ ^ (2 : ℝ)) := by
          simpa [s_compl, Real.rpow_natCast] using
            (b.summable_norm_sq_inner' x).subtype (s := fun i => i ∉ t)
        have hg : Summable (fun i : s_compl => ‖T (b i)‖ ^ (2 : ℝ)) := by
          simpa [s_compl, Real.rpow_natCast] using (h.subtype (s := fun i => i ∉ t))
        have hf_nonneg : ∀ i : s_compl, 0 ≤ ‖⟪b i, x⟫_ℂ‖ := by intro i; exact norm_nonneg _
        have hg_nonneg : ∀ i : s_compl, 0 ≤ ‖T (b i)‖ := by intro i; exact norm_nonneg _
        have h_cs := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg (p := 2) (q := 2)
          (hpq := Real.HolderConjugate.two_two) hf_nonneg hg_nonneg hf hg
        simpa [Real.sqrt_eq_rpow, Real.rpow_natCast, one_div] using h_cs.2
      have h_fsum_le : ∑' i : s_compl, ‖⟪b i, x⟫_ℂ‖^2 ≤ ‖x‖^2 := by
        refine tsum_le_of_sum_le' ?_ ?_
        · exact pow_nonneg (norm_nonneg _) 2
        · intro s
          classical
          let s' := s.map (Function.Embedding.subtype _)
          have h_le := (b.orthonormal.sum_inner_products_le (x := x) (s := s'))
          simpa [s', Finset.sum_map] using h_le
      have h_fsum_sqrt_le : Real.sqrt (∑' i : s_compl, ‖⟪b i, x⟫_ℂ‖^2) ≤ ‖x‖ := by
        have h := Real.sqrt_le_sqrt h_fsum_le
        simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using h
      calc
        ‖(T - F t) x‖ = ‖∑' i : s_compl, g i‖ := by simp [h_sum_diff]
        _ ≤ ∑' i : s_compl, ‖g i‖ := norm_tsum_le_tsum_norm h_norm_summable
        _ = ∑' i : s_compl, ‖⟪b i, x⟫_ℂ‖ * ‖T (b i)‖ := by
          refine tsum_congr ?_;
          intro i
          simp [g, norm_smul]
        _ ≤ Real.sqrt (∑' i : s_compl, ‖⟪b i, x⟫_ℂ‖^2) *
            Real.sqrt (∑' i : s_compl, ‖T (b i)‖^2) := h_bound_tsum
        _ ≤ ‖x‖ * Real.sqrt tail_sq := by
          have h_tail : Real.sqrt (∑' i : s_compl, ‖T (b i)‖^2) = Real.sqrt tail_sq := by rfl
          calc
            Real.sqrt (∑' i : s_compl, ‖⟪b i, x⟫_ℂ‖^2) *
                Real.sqrt (∑' i : s_compl, ‖T (b i)‖^2)
                ≤ ‖x‖ * Real.sqrt (∑' i : s_compl, ‖T (b i)‖^2) := by
                  gcongr
              _ = ‖x‖ * Real.sqrt tail_sq := by simp [h_tail]
        _ = Real.sqrt tail_sq * ‖x‖ := by simp [mul_comm]
    have h_tail_nonneg : 0 ≤ tail_sq := tsum_nonneg (fun _ => sq_nonneg _)
    apply lt_of_le_of_lt h_norm_le
    rw [Real.sqrt_lt h_tail_nonneg (le_of_lt hε)]
    exact h_tail_sum
  · exact Filter.Eventually.of_forall hF

omit [CompleteSpace E] in
/-- Compact operators form a two-sided ideal: if T is compact and S is bounded, then ST and TS are compact. -/
theorem IsCompactOperator.mul_left {S T : E →L[ℂ] E} (hT : IsCompactOperator T) :
    IsCompactOperator (S ∘L T) := hT.clm_comp S

omit [CompleteSpace E] in
/-- Compact operators form a two-sided ideal: if T is compact and S is bounded, then TS and ST are compact. -/
theorem IsCompactOperator.mul_right {S T : E →L[ℂ] E} (hT : IsCompactOperator T) :
    IsCompactOperator (T ∘L S) := hT.comp_clm S

/-! ### Spectral theorem for compact self-adjoint operators -/

/-- Auxiliary lemma: if T is self-adjoint and compact, and the supremum of
    T.reApplyInnerSelf on the unit sphere is M > 0, then M is an eigenvalue with
    a nonzero eigenvector. This lemma is parameterized by M so it can be applied
    to both T (when sup > 0) and -T (when inf < 0).

## Proof strategy:
1. Find a sequence xₙ on the unit sphere with ⟪Txₙ,xₙ⟫ → M
2. Use compactness: T(xₙ) has a convergent subsequence T(xₙ ∘ φ) → y
3. Show ‖T(xₙ φ n) - M•(xₙ φ n)‖ → 0 by variational characterization
4. Deduce that xₙ(φ n) → x₀ := M⁻¹•y and T x₀ = M•x₀
-/
theorem IsSelfAdjoint.hasEigenvector_of_sup_pos {T : E →L[ℂ] E} {M : ℝ}
    (hsa : IsSelfAdjoint T) (hT_comp : IsCompactOperator T)
    (h_sphere_nonempty : (Metric.sphere (0 : E) 1).Nonempty)
    (h_M_eq : M = ⨆ (x : Metric.sphere (0 : E) 1), T.reApplyInnerSelf x)
    (hM_pos : 0 < M) :
    ∃ (x : E), x ≠ 0 ∧ T x = M • x := by
  have h_sphere_subtype_nonempty : Nonempty (Metric.sphere (0 : E) 1) := h_sphere_nonempty.to_subtype
  have h_bdd : BddAbove (Set.range (fun z : Metric.sphere (0 : E) 1 => T.reApplyInnerSelf z)) := by
    use ‖T‖
    rintro _ ⟨z, _, rfl⟩
    have hz : ‖(z : E)‖ = 1 := mem_sphere_zero_iff_norm.mp z.2
    calc T.reApplyInnerSelf z = (⟪T z, z⟫_ℂ).re := rfl
      _ ≤ |(⟪T z, z⟫_ℂ).re| := le_abs_self _
      _ ≤ ‖⟪T z, z⟫_ℂ‖ := abs_re_le_norm _
      _ ≤ ‖T z‖ * ‖(z : E)‖ := norm_inner_le_norm _ _
      _ ≤ ‖T‖ * ‖(z : E)‖ * ‖(z : E)‖ := by nlinarith [T.le_opNorm z, norm_nonneg (z : E)]
      _ = ‖T‖ := by rw [hz]; ring
  have h_M_iSup : IsLUB (Set.range (fun z : Metric.sphere (0 : E) 1 => T.reApplyInnerSelf z)) M := by
    rw [h_M_eq]
    exact isLUB_ciSup h_bdd
  have h_range_nonempty : (Set.range (fun z : Metric.sphere (0 : E) 1 => T.reApplyInnerSelf z)).Nonempty := by
    obtain ⟨x, hx⟩ := h_sphere_nonempty
    let s : Metric.sphere (0 : E) 1 := ⟨x, hx⟩
    exact ⟨T.reApplyInnerSelf s, s, rfl⟩
  obtain ⟨fn, hfn_seq⟩ := exists_seq_tendsto_sSup h_range_nonempty h_bdd
  choose xn hxn using hfn_seq.2.2
  have hxn_tendsto : Filter.Tendsto (fun n => T.reApplyInnerSelf (xn n)) Filter.atTop (nhds M) := by
    have h_sup_eq : sSup (Set.range fun z : Metric.sphere (0 : E) 1 => T.reApplyInnerSelf z) = M := by
      rw [h_M_eq]; rfl
    rw [← h_sup_eq]
    convert hfn_seq.2.1 using 1
    funext n
    exact hxn n
  have hK : IsCompact (closure (T '' Metric.closedBall 0 1)) :=
    isCompact_image_of_isCompactOperator hT_comp
  have hxn_ball : ∀ n, (xn n : E) ∈ Metric.closedBall 0 1 := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_eq (mem_sphere_zero_iff_norm.mp (xn n).2)
  have hTxn_mem : ∀ n, T (xn n : E) ∈ T '' Metric.closedBall 0 1 := by
    intro n
    exact ⟨xn n, hxn_ball n, rfl⟩
  have hTxn_mem_closure : ∀ n, T (xn n : E) ∈ closure (T '' Metric.closedBall 0 1) := by
    intro n
    exact subset_closure (hTxn_mem n)
  have h_seq_compact : IsSeqCompact (closure (T '' Metric.closedBall 0 1)) :=
    IsCompact.isSeqCompact hK
  obtain ⟨y, _, φ, hφ_strict, hφ_tendsto⟩ := h_seq_compact hTxn_mem_closure
  have hxn_φ_tendsto : Filter.Tendsto (fun n => T.reApplyInnerSelf (xn (φ n))) Filter.atTop (nhds M) := by
    exact hxn_tendsto.comp hφ_strict.tendsto_atTop
  have hxn_φ_norm : ∀ n, ‖(xn (φ n) : E)‖ = 1 := by
    intro n
    exact mem_sphere_zero_iff_norm.mp (xn (φ n)).2
  have h_norm_diff : Filter.Tendsto (fun n => ‖T (xn (φ n) : E) - M • (xn (φ n) : E)‖^2) Filter.atTop (nhds 0) := by
    let A := (M : ℂ) • (1 : E →L[ℂ] E) - T
    have hA_sa : IsSelfAdjoint A := by
      have hM : IsSelfAdjoint (M : ℂ) := by simp [isSelfAdjoint_iff, RCLike.star_def]
      exact IsSelfAdjoint.sub (IsSelfAdjoint.smul hM (IsSelfAdjoint.one _)) hsa
    have hA_symm : LinearMap.IsSymmetric A.toLinearMap := hA_sa.isSymmetric
    have hA_pos : 0 ≤ A := by
      rw [nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff_complex]
      intro x
      constructor
      · have h_star : star ⟪A x, x⟫_ℂ = ⟪A x, x⟫_ℂ :=
          (LinearMap.isSymmetric_iff_inner_map_self_real A.toLinearMap).mp hA_symm x
        have h_re : (RCLike.re ⟪A x, x⟫_ℂ : ℂ) = ⟪A x, x⟫_ℂ :=
          (RCLike.conj_eq_iff_re).1 (by simpa [RCLike.star_def] using h_star)
        exact h_re
      · have h_le : T.reApplyInnerSelf x ≤ M * ‖x‖^2 := by
          by_cases hx : x = 0
          · simp [hx, ContinuousLinearMap.reApplyInnerSelf_apply]
          · let u : Metric.sphere (0 : E) 1 :=
              ⟨(‖x‖⁻¹ : ℂ) • x,
                mem_sphere_zero_iff_norm.mpr (by
                  simp [norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)])⟩
            have h_le := h_M_iSup.1 ⟨u, rfl⟩
            have h_le' : T.reApplyInnerSelf u ≤ M := by simpa using h_le
            have h_le'' : T.reApplyInnerSelf ((‖x‖⁻¹ : ℂ) • x) ≤ M := by simpa [u] using h_le'
            have h_le''' : ‖(‖x‖⁻¹ : ℂ)‖ ^ 2 * T.reApplyInnerSelf x ≤ M := by
              simpa [ContinuousLinearMap.reApplyInnerSelf_smul] using h_le''
            have h_mul : ‖(‖x‖⁻¹ : ℂ)‖ ^ 2 * T.reApplyInnerSelf x * ‖x‖ ^ 2 ≤ M * ‖x‖ ^ 2 := by
              exact mul_le_mul_of_nonneg_right h_le''' (sq_nonneg ‖x‖)
            have hnorm2_ne : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
            have hnorm_ne : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
            have hnorm_inv : ‖(‖x‖⁻¹ : ℂ)‖ = ‖x‖⁻¹ := by simp [norm_inv]
            simpa [hnorm_inv, mul_assoc, hnorm2_ne, inv_mul_cancel, mul_comm, mul_left_comm] using h_mul
        have h_nonneg : 0 ≤ M * ‖x‖^2 - T.reApplyInnerSelf x := by linarith
        have h_re : RCLike.re ⟪A x, x⟫_ℂ = M * ‖x‖^2 - T.reApplyInnerSelf x := by
          calc
            RCLike.re ⟪A x, x⟫_ℂ = (⟪(M : ℂ) • x, x⟫_ℂ).re - (⟪T x, x⟫_ℂ).re := by
              simp [A, inner_sub_left]
            _ = M * ‖x‖^2 - T.reApplyInnerSelf x := by
              have hMre : (⟪(M : ℂ) • x, x⟫_ℂ).re = M * ‖x‖^2 := by
                rw [inner_smul_left]
                simp only [Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
                  Complex.ofReal_im, inner_self_eq_norm_sq_to_K, sq]
                simp [Complex.ofReal_re, Complex.ofReal_im]
              simp only [ContinuousLinearMap.reApplyInnerSelf_apply, hMre, sub_right_inj]
              rfl
        simpa [h_re] using h_nonneg
    let S := CFC.sqrt A
    have hS_sq : S * S = A := CFC.sqrt_mul_sqrt_self A hA_pos
    have h_ineq : ∀ x, ‖A x‖^2 ≤ ‖S‖^2 * A.reApplyInnerSelf x := by
      intro x
      calc ‖A x‖^2 = ‖S (S x)‖^2 := by rw [← hS_sq]; rfl
        _ ≤ (‖S‖ * ‖S x‖)^2 := by gcongr; exact le_opNorm S (S x)
        _ = ‖S‖^2 * ‖S x‖^2 := by ring
        _ = ‖S‖^2 * (A.reApplyInnerSelf x) := by
          have hS_sa : IsSelfAdjoint S := (CFC.sqrt_nonneg A).isSelfAdjoint
          have h_adj : S.adjoint = S := hS_sa.adjoint_eq
          have h_re : A.reApplyInnerSelf x = ‖S x‖^2 := by
            rw [← hS_sq]
            simp only [ContinuousLinearMap.reApplyInnerSelf_apply, ContinuousLinearMap.mul_apply]
            have : ⟪S (S x), x⟫_ℂ = ⟪S x, S x⟫_ℂ := by
              rw [← h_adj, ContinuousLinearMap.adjoint_inner_right, h_adj]
            rw [this]
            exact inner_self_eq_norm_sq (𝕜 := ℂ) (S x)
          rw [h_re]
    have h_inner_tendsto : Filter.Tendsto (fun n => A.reApplyInnerSelf (xn (φ n))) Filter.atTop (nhds 0) := by
      have h1 : ∀ n, ‖(xn (φ n) : E)‖ = 1 := fun n => mem_sphere_zero_iff_norm.mp (xn (φ n)).2
      have h_eq : (fun n => A.reApplyInnerSelf (xn (φ n))) =
          fun n => M - T.reApplyInnerSelf (xn (φ n)) := by
        funext n
        have h1n := h1 n
        simp only [A, ContinuousLinearMap.reApplyInnerSelf_apply, ContinuousLinearMap.sub_apply,
          ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]
        have hM_inner : RCLike.re (⟪(M : ℂ) • (xn (φ n) : E), (xn (φ n) : E)⟫_ℂ) = M := by
          rw [inner_smul_left, inner_self_eq_norm_sq_to_K, h1n]
          simp
        simp only [inner_sub_left, map_sub]
        rw [hM_inner]
      have h_tendsto : Filter.Tendsto (fun n => M - T.reApplyInnerSelf (xn (φ n))) Filter.atTop (nhds (M - M)) :=
        tendsto_const_nhds.sub hxn_φ_tendsto
      simpa [h_eq] using h_tendsto
    have h_lim_zero : Filter.Tendsto (fun n => ‖S‖^2 * A.reApplyInnerSelf (xn (φ n))) Filter.atTop (nhds 0) := by
      convert Filter.Tendsto.const_mul (‖S‖^2) h_inner_tendsto
      simp
    have h_nonneg : ∀ n, 0 ≤ ‖T (xn (φ n) : E) - M • (xn (φ n) : E)‖^2 := fun n => sq_nonneg _
    have h_bound : ∀ n, ‖T (xn (φ n) : E) - M • (xn (φ n) : E)‖^2 ≤ ‖S‖^2 * A.reApplyInnerSelf (xn (φ n)) := by
      intro n
      have h_sub : T (xn (φ n)) - M • (xn (φ n) : E) = - A (xn (φ n)) := by
        simp only [A, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.one_apply, neg_sub]
        rfl
      simpa [h_sub, norm_neg] using (h_ineq (xn (φ n)))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (by simp only [tendsto_const_nhds]) h_lim_zero h_nonneg h_bound
  have h_M_smul_tendsto : Filter.Tendsto (fun n => M • (xn (φ n) : E)) Filter.atTop (nhds y) := by
    have h_norm_tendsto : Filter.Tendsto (fun n => ‖T (xn (φ n) : E) - M • (xn (φ n) : E)‖)
        Filter.atTop (nhds 0) := by
      have h_sqrt : Filter.Tendsto (fun n => Real.sqrt (‖T (xn (φ n) : E) - M • (xn (φ n) : E)‖^2))
          Filter.atTop (nhds (Real.sqrt 0)) := by
        exact Filter.Tendsto.comp (Continuous.tendsto Real.continuous_sqrt 0) h_norm_diff
      simp only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] at h_sqrt
      exact h_sqrt
    have h1 : Filter.Tendsto (fun n => T (xn (φ n) : E)) Filter.atTop (nhds y) := by
      simp only [Function.comp_def] at hφ_tendsto
      exact hφ_tendsto
    have h2 : Filter.Tendsto (fun n => T (xn (φ n) : E) - M • (xn (φ n) : E)) Filter.atTop (nhds 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr h_norm_tendsto
    have h_key : Filter.Tendsto (fun n => T (xn (φ n) : E) - (T (xn (φ n) : E) - M • (xn (φ n) : E)))
        Filter.atTop (nhds (y - 0)) := h1.sub h2
    simp only [sub_zero] at h_key
    convert h_key using 1
    ext n
    simp only [sub_sub_cancel]
  have h_M_ne_zero : M ≠ 0 := ne_of_gt hM_pos
  have h_xn_tendsto : Filter.Tendsto (fun n => (xn (φ n) : E)) Filter.atTop (nhds (M⁻¹ • y)) := by
    have : Filter.Tendsto (fun n => M⁻¹ • (M • (xn (φ n) : E))) Filter.atTop (nhds (M⁻¹ • y)) :=
      Filter.Tendsto.const_smul h_M_smul_tendsto M⁻¹
    simp only [inv_smul_smul₀ h_M_ne_zero] at this
    exact this
  have h_norm_limit : ‖M⁻¹ • y‖ = 1 := by
    have h_norm_tendsto : Filter.Tendsto (fun n => ‖(xn (φ n) : E)‖) Filter.atTop (nhds ‖M⁻¹ • y‖) :=
      Filter.Tendsto.norm h_xn_tendsto
    have h_all_one : ∀ n, ‖(xn (φ n) : E)‖ = 1 := hxn_φ_norm
    have h_const : Filter.Tendsto (fun (_ : ℕ) => (1 : ℝ)) Filter.atTop (nhds 1) := tendsto_const_nhds
    have h_eq : (fun n => ‖(xn (φ n) : E)‖) = (fun _ => 1) := by ext n; exact h_all_one n
    rw [h_eq] at h_norm_tendsto
    exact tendsto_nhds_unique h_norm_tendsto h_const
  let x₀ := M⁻¹ • y
  use x₀
  constructor
  · intro hx0
    simp only [x₀, hx0, norm_zero] at h_norm_limit
    exact one_ne_zero h_norm_limit.symm
  · have hT_cont : Continuous T := ContinuousLinearMap.continuous T
    have h_T_tendsto : Filter.Tendsto (fun n => T (xn (φ n) : E)) Filter.atTop (nhds (T x₀)) :=
      Filter.Tendsto.comp hT_cont.continuousAt h_xn_tendsto
    have h_T_tendsto' : Filter.Tendsto (fun n => T (xn (φ n) : E)) Filter.atTop (nhds y) := by
      simp only [Function.comp_def] at hφ_tendsto
      exact hφ_tendsto
    have h_Tx0_eq_y : T x₀ = y := tendsto_nhds_unique h_T_tendsto h_T_tendsto'
    have h_M_smul_x0 : M • x₀ = y := by
      simp only [x₀, smul_smul, mul_inv_cancel₀ h_M_ne_zero, one_smul]
    rw [h_Tx0_eq_y, h_M_smul_x0]

theorem IsSelfAdjoint.hasEigenvector_of_isCompactOperator {T : E →L[ℂ] E}
    (hsa : IsSelfAdjoint T) (hT_comp : IsCompactOperator T) (hT_ne : T ≠ 0) :
    ∃ (μ : ℝ) (x : E), x ≠ 0 ∧ T x = μ • x := by
  -- Since T ≠ 0, there exists x with ⟪Tx, x⟫ ≠ 0 (by eq_zero_of_inner_map_self_eq_zero')
  have h_exists_nonzero_inner : ∃ x, ⟪T x, x⟫_ℂ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hT_ne (IsSelfAdjoint.eq_zero_of_inner_map_self_eq_zero hsa h)
  -- Step 1: Define the Rayleigh quotient supremum M and infimum m on the unit sphere
  have h_sphere_nonempty : (Metric.sphere (0 : E) 1).Nonempty := by
    obtain ⟨x₀, hx₀⟩ := h_exists_nonzero_inner
    have hx₀_ne : x₀ ≠ 0 := fun h => by simp [h] at hx₀
    exact ⟨(‖x₀‖⁻¹) • x₀, by simp [norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx₀_ne)]⟩
  let M := ⨆ (x : Metric.sphere (0 : E) 1), T.reApplyInnerSelf x
  let m := ⨅ (x : Metric.sphere (0 : E) 1), T.reApplyInnerSelf x
  -- Step 2: Either M > 0 or m < 0 (since T ≠ 0 implies ⟪Tx, x⟫ ≠ 0 for some x)
  have h_not_both_zero : 0 < M ∨ m < 0 := by
    by_contra h
    push_neg at h
    obtain ⟨hM, hm⟩ := h
    -- M ≤ 0 and m ≥ 0, combined with m ≤ M, gives M = m = 0
    have h_bdd : BddAbove (Set.range fun x : Metric.sphere (0 : E) 1 => T.reApplyInnerSelf x) := by
      use ‖T‖
      intro r ⟨x, hx⟩
      rw [← hx]
      have hx_norm : ‖(x : E)‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
      calc T.reApplyInnerSelf x = (⟪T x, x⟫_ℂ).re := rfl
        _ ≤ |((⟪T x, x⟫_ℂ).re : ℝ)| := le_abs_self _
        _ ≤ ‖⟪T (x : E), (x : E)⟫_ℂ‖ := abs_re_le_norm _
        _ ≤ ‖T (x : E)‖ * ‖(x : E)‖ := norm_inner_le_norm (T x) x
        _ ≤ ‖T‖ * ‖(x : E)‖ * ‖(x : E)‖ := by
            apply mul_le_mul_of_nonneg_right
            · exact T.le_opNorm x
            · exact norm_nonneg (x : E)
        _ = ‖T‖ := by rw [hx_norm]; ring
    have h_bdd_below : BddBelow (Set.range fun x : Metric.sphere (0 : E) 1 => T.reApplyInnerSelf x) := by
      use -‖T‖
      intro r ⟨x, hx⟩
      rw [← hx]
      have hx_norm : ‖(x : E)‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
      have h' : -‖⟪T (x : E), (x : E)⟫_ℂ‖ ≤ (⟪T x, x⟫_ℂ).re := by
        have := abs_re_le_norm ⟪T (x : E), (x : E)⟫_ℂ
        have h_abs := le_abs_self (⟪T (x : E), (x : E)⟫_ℂ).re
        have h_neg_abs := neg_abs_le (⟪T (x : E), (x : E)⟫_ℂ).re
        linarith
      calc -‖T‖ = -‖T‖ * ‖(x : E)‖ * ‖(x : E)‖ := by rw [hx_norm]; ring
        _ ≤ -‖T (x : E)‖ * ‖(x : E)‖ := by
            have h1 : ‖T (x : E)‖ ≤ ‖T‖ * ‖(x : E)‖ := T.le_opNorm x
            have h2 : ‖(x : E)‖ ≥ 0 := norm_nonneg (x : E)
            nlinarith
        _ ≤ -‖⟪T (x : E), (x : E)⟫_ℂ‖ := by
            have h1 : ‖⟪T (x : E), (x : E)⟫_ℂ‖ ≤ ‖T (x : E)‖ * ‖(x : E)‖ := norm_inner_le_norm (T x) x
            nlinarith
        _ ≤ (⟪T x, x⟫_ℂ).re := h'
    -- m ≤ M
    have h_m_le_M : m ≤ M := by
      have h_ne : Nonempty (Metric.sphere (0 : E) 1) := h_sphere_nonempty.to_subtype
      exact ciInf_le_ciSup h_bdd_below h_bdd
    -- From hM : M ≤ 0 and hm : 0 ≤ m and m ≤ M, we get m = M = 0
    have hM_eq : M = 0 := le_antisymm hM (le_trans hm h_m_le_M)
    have hm_eq : m = 0 := le_antisymm (le_trans h_m_le_M hM) hm
    -- This means ⟪Tx, x⟫ = 0 for all x on the sphere
    have h_inner_sphere : ∀ x : Metric.sphere (0 : E) 1, T.reApplyInnerSelf x = 0 := by
      intro x
      have hle : T.reApplyInnerSelf x ≤ M := le_ciSup h_bdd ⟨x, x.2⟩
      have hge : m ≤ T.reApplyInnerSelf x := ciInf_le h_bdd_below ⟨x, x.2⟩
      linarith [hM_eq, hm_eq]
    -- This implies T = 0, contradiction
    have h_T_zero : T = 0 := by
      apply IsSelfAdjoint.eq_zero_of_inner_map_self_eq_zero hsa
      intro x
      by_cases hx : x = 0
      · simp only [hx, map_zero, inner_zero_right]
      · let u : Metric.sphere (0 : E) 1 := ⟨(‖x‖⁻¹) • x, by
          rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
            inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩
        have hu := h_inner_sphere u
        simp only [ContinuousLinearMap.reApplyInnerSelf_apply] at hu
        have hu_val : (u : E) = ‖x‖⁻¹ • x := rfl
        rw [hu_val] at hu
        have h_real_inner : (⟪T x, x⟫_ℂ).im = 0 := by
          have hsym := hsa.isSymmetric x x
          simp only [ContinuousLinearMap.coe_coe] at hsym
          rw [← inner_conj_symm x (T x)] at hsym
          exact Complex.conj_eq_iff_im.mp hsym.symm
        have h_linear : T (‖x‖⁻¹ • x) = ‖x‖⁻¹ • T x := ContinuousLinearMap.map_smul_of_tower T ‖x‖⁻¹ x
        have h_smul_eq : ∀ (r : ℝ) (y : E), (r : ℂ) • y = r • y :=
          fun r y => (RCLike.real_smul_eq_coe_smul (K := ℂ) r y).symm
        have h_inner_smul : ⟪T (‖x‖⁻¹ • x), ‖x‖⁻¹ • x⟫_ℂ = ((‖x‖⁻¹)^2 : ℝ) * ⟪T x, x⟫_ℂ := by
          rw [h_linear, ← h_smul_eq ‖x‖⁻¹ (T x), ← h_smul_eq ‖x‖⁻¹ x]
          rw [inner_smul_left, inner_smul_right]
          simp only [Complex.conj_ofReal, sq, Complex.ofReal_mul]
          ring
        rw [h_inner_smul] at hu
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
          RCLike.re_to_complex] at hu
        have h_inv_sq_pos : (0 : ℝ) < (‖x‖⁻¹)^2 := sq_pos_of_pos (inv_pos_of_pos (norm_pos_iff.mpr hx))
        have h_re_zero : (⟪T x, x⟫_ℂ).re = 0 := by
          have := mul_eq_zero.mp (by linarith [hu] : (‖x‖⁻¹ : ℝ)^2 * (⟪T x, x⟫_ℂ).re = 0)
          cases this with
          | inl h => linarith [h_inv_sq_pos]
          | inr h => exact h
        exact Complex.ext h_re_zero h_real_inner
    exact hT_ne h_T_zero
  have h_bdd : BddAbove (Set.range (fun z : Metric.sphere (0 : E) 1 => T.reApplyInnerSelf z)) := by
      use ‖T‖
      rintro _ ⟨z, _, rfl⟩
      have hz : ‖(z : E)‖ = 1 := mem_sphere_zero_iff_norm.mp z.2
      calc T.reApplyInnerSelf z = (⟪T z, z⟫_ℂ).re := rfl
        _ ≤ |(⟪T z, z⟫_ℂ).re| := le_abs_self _
        _ ≤ ‖⟪T z, z⟫_ℂ‖ := abs_re_le_norm _
        _ ≤ ‖T z‖ * ‖(z : E)‖ := norm_inner_le_norm _ _
        _ ≤ ‖T‖ * ‖(z : E)‖ * ‖(z : E)‖ := by nlinarith [T.le_opNorm z, norm_nonneg (z : E)]
        _ = ‖T‖ := by rw [hz]; ring
  have h_bdd_below : BddBelow (Set.range (fun z : Metric.sphere (0 : E) 1 => T.reApplyInnerSelf z)) := by
    use -‖T‖
    rintro _ ⟨z, _, rfl⟩
    have hz : ‖(z : E)‖ = 1 := mem_sphere_zero_iff_norm.mp z.2
    have h' : -‖⟪T (z : E), (z : E)⟫_ℂ‖ ≤ (⟪T z, z⟫_ℂ).re := by
      have := abs_re_le_norm ⟪T (z : E), (z : E)⟫_ℂ
      have h_abs := le_abs_self (⟪T (z : E), (z : E)⟫_ℂ).re
      have h_neg_abs := neg_abs_le (⟪T (z : E), (z : E)⟫_ℂ).re
      linarith
    calc -‖T‖ = -‖T‖ * ‖(z : E)‖ * ‖(z : E)‖ := by rw [hz]; ring
      _ ≤ -‖T (z : E)‖ * ‖(z : E)‖ := by
          have h1 : ‖T (z : E)‖ ≤ ‖T‖ * ‖(z : E)‖ := T.le_opNorm z
          have h2 : ‖(z : E)‖ ≥ 0 := norm_nonneg (z : E)
          nlinarith
      _ ≤ -‖⟪T (z : E), (z : E)⟫_ℂ‖ := by
          have h1 : ‖⟪T (z : E), (z : E)⟫_ℂ‖ ≤ ‖T (z : E)‖ * ‖(z : E)‖ := norm_inner_le_norm (T z) z
          nlinarith
      _ ≤ (⟪T z, z⟫_ℂ).re := h'
  -- Case split: either M > 0 or m < 0
  cases h_not_both_zero with
  | inl hM_pos =>
    -- Case M > 0: use the auxiliary lemma directly
    obtain ⟨x, hx_ne, hx_eig⟩ := IsSelfAdjoint.hasEigenvector_of_sup_pos hsa hT_comp h_sphere_nonempty rfl hM_pos
    exact ⟨M, x, hx_ne, hx_eig⟩
  | inr hm_neg =>
    -- Case m < 0: apply the auxiliary lemma to -T
    -- -T is self-adjoint and compact
    have hsa_neg : IsSelfAdjoint (-T) := IsSelfAdjoint.neg hsa
    have hT_comp_neg : IsCompactOperator (-T) := IsCompactOperator.neg hT_comp
    -- The supremum of (-T).reApplyInnerSelf on the unit sphere equals -m
    have h_sup_neg_T : -m = ⨆ (x : Metric.sphere (0 : E) 1), (-T).reApplyInnerSelf x := by
      have h_eq : ∀ x : Metric.sphere (0 : E) 1, (-T).reApplyInnerSelf x = -T.reApplyInnerSelf x := by
        intro x
        simp only [ContinuousLinearMap.reApplyInnerSelf_apply, ContinuousLinearMap.neg_apply,
          inner_neg_left, map_neg]
      simp_rw [h_eq]
      -- Use the fact that ⨆ x, -f(x) = -(⨅ x, f(x)) for bounded functions
      have h_bdd_above_neg : BddAbove (Set.range (fun x : Metric.sphere (0 : E) 1 => -T.reApplyInnerSelf x)) := by
        obtain ⟨c, hc⟩ := h_bdd_below
        use -c
        rintro _ ⟨x, rfl⟩
        have := hc (Set.mem_range_self x)
        linarith
      have h_sphere_ne : Nonempty (Metric.sphere (0 : E) 1) := h_sphere_nonempty.to_subtype
      -- Show -m = ⨆ x, -f(x) where m = ⨅ x, f(x)
      -- The key identity is ⨆ x, -f(x) = -(⨅ x, f(x)) via antisymmetry
      apply le_antisymm
      · -- -m ≤ ⨆ x, -f(x)
        -- We prove this by contradiction using the GLB property.
        -- If ⨆ x, -f(x) < -m, then for all x, -f(x) ≤ ⨆ y, -f(y) < -m
        -- so f(x) > m for all x. Since ⨆ x, -f(x) < -m, there exists δ > 0 such that
        -- f(x) ≥ m + δ for all x. But then m is not the infimum, contradiction.
        by_contra h_neg
        push_neg at h_neg
        -- h_neg : ⨆ x, -f(x) < -m
        -- This means: for all x, -f(x) ≤ sup < -m, so -f(x) < -m, i.e., f(x) > m
        -- There's a gap: -m - sup > 0
        set s := ⨆ x : Metric.sphere (0 : E) 1, -T.reApplyInnerSelf x with hs_def
        have h_gap : s < -m := h_neg
        have h_delta : -m - s > 0 := by linarith
        have h_lb : ∀ x : Metric.sphere (0 : E) 1, T.reApplyInnerSelf x ≥ m + (-m - s) / 2 := by
          intro x
          have h1 : -T.reApplyInnerSelf x ≤ s := le_ciSup h_bdd_above_neg x
          linarith
        -- So m + δ is a lower bound where δ = (-m - s)/2 > 0
        -- But m is the infimum (greatest lower bound), so m ≥ m + δ, contradiction
        have h_inf_ge : m ≥ m + (-m - s) / 2 := by
          have h_le : ∀ x : Metric.sphere (0 : E) 1, m + (-m - s) / 2 ≤ T.reApplyInnerSelf x :=
            fun x => h_lb x
          have := le_ciInf h_le
          exact this
        linarith
      · -- ⨆ x, -f(x) ≤ -m
        apply ciSup_le
        intro x
        have := ciInf_le h_bdd_below x
        linarith
    -- Since m < 0, we have -m > 0
    have h_neg_m_pos : 0 < -m := neg_pos.mpr hm_neg
    -- Apply the auxiliary lemma to -T with M' = -m
    obtain ⟨x, hx_ne, hx_eig⟩ := IsSelfAdjoint.hasEigenvector_of_sup_pos hsa_neg hT_comp_neg
      h_sphere_nonempty h_sup_neg_T h_neg_m_pos
    -- We have (-T) x = (-m) • x, which means T x = m • x
    use m, x, hx_ne
    simp only [ContinuousLinearMap.neg_apply] at hx_eig
    have h_neg : -T x = (-m) • x := hx_eig
    calc T x = -(-T x) := by simp
      _ = -((-m) • x) := by rw [h_neg]
      _ = m • x := by simp [neg_smul]

theorem exists_orthonormalBasis_eigenvectors_of_isCompactOperator_isSelfAdjoint
    {T : E →L[ℂ] E} (hT_comp : IsCompactOperator T) (hsa : IsSelfAdjoint T) :
    ∃ (ι : Type u) (b : HilbertBasis ι ℂ E) (μ : ι → ℝ),
      (∀ i, T (b i) = (μ i) • b i) ∧ (∀ i, μ i = 0 ∨ 0 < |μ i|) := by
  classical
  -- The proof proceeds by Zorn's lemma / transfinite recursion:
  let S := {s : Set E | Orthonormal ℂ ((↑) : s → E) ∧ ∀ v ∈ s, ∃ μ : ℝ, T v = μ • v}
  have hS_zorn : ∀ c ⊆ S, IsChain (· ⊆ ·) c → ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub := by
    intro c hcS hchain
    refine ⟨⋃₀ c, ?_, fun s hs => Set.subset_sUnion_of_mem hs⟩
    constructor
    · rw [orthonormal_iff_ite]
      intro u v
      obtain ⟨s₁, hs₁c, hus₁⟩ := Set.mem_sUnion.mp u.2
      obtain ⟨s₂, hs₂c, hvs₂⟩ := Set.mem_sUnion.mp v.2
      rcases hchain.total hs₁c hs₂c with h_sub | h_sub
      · -- s₁ ⊆ s₂
        have h_ortho : Orthonormal ℂ ((↑) : s₂ → E) := (hcS hs₂c).1
        rw [orthonormal_iff_ite] at h_ortho
        have eq1 : (u : E) = (⟨u.1, h_sub hus₁⟩ : s₂) := rfl
        have eq2 : (v : E) = (⟨v.1, hvs₂⟩ : s₂) := rfl
        rw [eq1, eq2, h_ortho]
        congr 1
        · ext1
          simp only [Subtype.mk.injEq]
          constructor
          · intro h; exact Subtype.ext h
          · intro h; exact congr_arg Subtype.val h
      · -- s₂ ⊆ s₁
        have h_ortho : Orthonormal ℂ ((↑) : s₁ → E) := (hcS hs₁c).1
        rw [orthonormal_iff_ite] at h_ortho
        have eq1 : (u : E) = (⟨u.1, hus₁⟩ : s₁) := rfl
        have eq2 : (v : E) = (⟨v.1, h_sub hvs₂⟩ : s₁) := rfl
        rw [eq1, eq2, h_ortho]
        congr 1
        · ext1
          simp only [Subtype.mk.injEq]
          constructor
          · intro h; exact Subtype.ext h
          · intro h; exact congr_arg Subtype.val h
    · intro v hv
      obtain ⟨s, hsc, hvs⟩ := Set.mem_sUnion.mp hv
      exact (hcS hsc).2 v hvs
  obtain ⟨K, ⟨hK_ortho, hK_eig⟩, hK_max⟩ := zorn_subset S hS_zorn
  let W : Submodule ℂ E := Submodule.span ℂ K
  let W_perp := Wᗮ
  have hTW : ∀ w ∈ W, T w ∈ W := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨μ, hμ⟩ := hK_eig v hv
      rw [hμ]
      exact W.smul_mem μ (Submodule.subset_span hv)
    | zero => simp [W.zero_mem]
    | add x y hx hy ihx ihy => rw [map_add]; exact W.add_mem ihx ihy
    | smul a x hx ihx => rw [map_smul]; exact W.smul_mem a ihx
  have hTW_perp : ∀ w ∈ W_perp, T w ∈ W_perp := by
    intro w hw
    rw [Submodule.mem_orthogonal] at hw ⊢
    intro u hu
    have hTu : T u ∈ W := hTW u hu
    rw [← ContinuousLinearMap.adjoint_inner_left, hsa.adjoint_eq]
    exact hw (T u) hTu
  -- Construct the restricted operator as a continuous linear map
  let T_perp : W_perp →L[ℂ] W_perp := {
    toLinearMap := (T : E →ₗ[ℂ] E).restrict hTW_perp
    cont := by
      have : Continuous (fun x : W_perp => (⟨T (x : E), hTW_perp x x.2⟩ : W_perp)) := by
        apply Continuous.subtype_mk
        exact T.continuous.comp continuous_subtype_val
      convert this
  }
  have hT_perp_comp : IsCompactOperator T_perp :=
    hT_comp.restrict hTW_perp (Submodule.isClosed_orthogonal _)
  have hT_perp_sa : IsSelfAdjoint T_perp := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro ⟨x, hx⟩ ⟨y, hy⟩
    simp only [T_perp, LinearMap.restrict_apply]
    exact hsa.isSymmetric x y
  have hT_perp_eq_zero : T_perp = 0 := by
    by_contra h_ne
    -- Apply IsSelfAdjoint.hasEigenvector_of_isCompactOperator to get an eigenvector v of T_perp
    obtain ⟨μ, v, hv_ne, hv_eig⟩ := IsSelfAdjoint.hasEigenvector_of_isCompactOperator hT_perp_sa hT_perp_comp h_ne
    -- v ∈ W_perp is an eigenvector of T with eigenvalue μ
    -- First normalize v to get a unit eigenvector
    have hv_norm_ne : ‖(v : E)‖ ≠ 0 := norm_ne_zero_iff.mpr (Subtype.coe_ne_coe.mpr hv_ne)
    let v' : W_perp := ⟨‖(v : E)‖⁻¹ • (v : E), W_perp.smul_mem _ v.2⟩
    have hv'_ne : v' ≠ 0 := by
      intro h
      have := congrArg Subtype.val h
      simp only [Submodule.coe_zero] at this
      rw [smul_eq_zero] at this
      cases this with
      | inl h => exact hv_norm_ne (inv_eq_zero.mp h)
      | inr h => exact hv_norm_ne (norm_eq_zero.mpr h)
    have hv'_norm : ‖(v' : E)‖ = 1 := by
      simp only [v', norm_smul, norm_inv, norm_norm]
      rw [inv_mul_cancel₀ hv_norm_ne]
    -- T v' = μ • v' in E (using that T_perp v = μ • v)
    have hv'_eig : T (v' : E) = μ • (v' : E) := by
      simp only [v']
      rw [ContinuousLinearMap.map_smul_of_tower]
      have hv_T : (T_perp v : E) = (μ • v : W_perp) := congrArg Subtype.val hv_eig
      simp only [T_perp, ContinuousLinearMap.coe_mk', LinearMap.restrict_apply,
        Submodule.coe_smul_of_tower] at hv_T
      -- hv_T : T (v : E) = μ • (v : E), but with coercion ↑T ↑v
      simp only [ContinuousLinearMap.coe_coe] at hv_T
      rw [hv_T, smul_comm]
    have hv'_in_perp : (v' : E) ∈ W_perp := v'.2
    have hv'_E_ne : (v' : E) ≠ 0 := fun h => hv'_ne (Subtype.ext h)
    have hv'_ortho_K : ∀ k ∈ K, ⟪k, (v' : E)⟫_ℂ = 0 := by
      intro k hk
      have hk_in_W : k ∈ W := Submodule.subset_span hk
      rw [Submodule.mem_orthogonal'] at hv'_in_perp
      rw [inner_eq_zero_symm]
      exact hv'_in_perp k hk_in_W
    -- The set K ∪ {v'} is still orthonormal and consists of eigenvectors
    -- This contradicts maximality of K
    have hK' : K ∪ {(v' : E)} ∈ S := by
      constructor
      · -- Orthonormality: the new vector v' is orthogonal to K and has norm 1
        rw [orthonormal_subtype_iff_ite]
        intro x hx y hy
        simp only [Set.mem_union, Set.mem_singleton_iff] at hx hy
        rcases hx with hx_K | hx_v'
        · rcases hy with hy_K | hy_v'
          · -- Both in K: use hK_ortho
            rw [orthonormal_subtype_iff_ite] at hK_ortho
            exact hK_ortho x hx_K y hy_K
          · -- x ∈ K, y = v'
            rw [hy_v']
            have h_ne : x ≠ (v' : E) := by
              intro h_eq
              rw [← h_eq] at hv'_in_perp
              have : x ∈ W := Submodule.subset_span hx_K
              rw [Submodule.mem_orthogonal'] at hv'_in_perp
              have := hv'_in_perp x this
              rw [inner_self_eq_zero] at this
              have hx_norm : ‖x‖ = 1 := hK_ortho.1 ⟨x, hx_K⟩
              rw [this] at hx_norm
              norm_num at hx_norm
            simp only [h_ne, ↓reduceIte]
            exact hv'_ortho_K x hx_K
        · rcases hy with hy_K | hy_v'
          · -- x = v', y ∈ K
            rw [hx_v']
            have h_ne : (v' : E) ≠ y := by
              intro h_eq
              rw [h_eq] at hv'_in_perp
              have : y ∈ W := Submodule.subset_span hy_K
              rw [Submodule.mem_orthogonal'] at hv'_in_perp
              have := hv'_in_perp y this
              rw [inner_self_eq_zero] at this
              have hy_norm : ‖y‖ = 1 := hK_ortho.1 ⟨y, hy_K⟩
              rw [this] at hy_norm
              norm_num at hy_norm
            simp only [h_ne, ↓reduceIte]
            rw [inner_eq_zero_symm]
            exact hv'_ortho_K y hy_K
          · -- Both x = v' and y = v'
            rw [hx_v', hy_v']
            simp only [↓reduceIte, inner_self_eq_norm_sq_to_K, hv'_norm, one_pow, RCLike.ofReal_one]
      · -- Eigenvector property
        intro u hu
        simp only [Set.mem_union, Set.mem_singleton_iff] at hu
        cases hu with
        | inl hu_K => exact hK_eig u hu_K
        | inr hu_v =>
          rw [hu_v]
          exact ⟨μ, hv'_eig⟩
    -- This contradicts maximality: K ⊊ K ∪ {v'}
    have hK_strict : K ⊂ K ∪ {(v' : E)} := by
      constructor
      · exact Set.subset_union_left
      · intro h_eq
        have hv'_in : (v' : E) ∈ K ∪ {(v' : E)} := Set.mem_union_right K rfl
        have hv'_in_K : (v' : E) ∈ K := h_eq hv'_in
        have := hv'_ortho_K (v' : E) hv'_in_K
        rw [inner_self_eq_zero] at this
        exact hv'_E_ne this
    -- hK_max says: if y ∈ S and K ⊆ y, then y ⊆ K
    -- We have hK' : K ∪ {v'} ∈ S and hK_strict.1 : K ⊆ K ∪ {v'}
    -- So hK_max hK' hK_strict.1 : K ∪ {v'} ⊆ K
    -- But this contradicts hK_strict.2 : ¬(K ∪ {v'} ⊆ K)
    exact hK_strict.2 (hK_max hK' hK_strict.1)
  -- W_perp has a Hilbert basis since it's a closed subspace
  obtain ⟨b_perp_index, b_perp, hb_perp⟩ := exists_hilbertBasis ℂ W_perp
  let ι' := K ⊕ b_perp_index
  let b' (i : ι') : E :=
    match i with
    | Sum.inl k => (k : E)
    | Sum.inr j => (b_perp j : E)
  have b'_ortho : Orthonormal ℂ b' := by
    rw [orthonormal_iff_ite]
    intro i j
    cases i with
    | inl ki =>
      cases j with
      | inl kj =>
        simp only [b']
        split_ifs with h
        · injection h with h_inj
          rw [h_inj]
          rw [inner_self_eq_norm_sq_to_K]
          have h_norm := hK_ortho.1 kj
          rw [h_norm]
          norm_num
        · have : ki ≠ kj := fun heq => h (by rw [heq])
          have hK_ortho' := hK_ortho.2 this
          simp [hK_ortho']
      | inr jj =>
        rw [if_neg Sum.inl_ne_inr]
        simp only [b']
        have : (b_perp jj : E) ∈ W_perp := (b_perp jj).2
        rw [Submodule.mem_orthogonal'] at this
        have h := this (ki : E) (Submodule.subset_span ki.2)
        rw [inner_eq_zero_symm]
        exact h
    | inr ii =>
      cases j with
      | inl kj =>
        rw [if_neg Sum.inr_ne_inl]
        simp only [b']
        have : (b_perp ii : E) ∈ W_perp := (b_perp ii).2
        rw [Submodule.mem_orthogonal'] at this
        exact this (kj : E) (Submodule.subset_span kj.2)
      | inr jj =>
        simp only [b']
        by_cases h : ii = jj
        · subst h
          simp only [↓reduceIte]
          rw [inner_self_eq_norm_sq_to_K]
          have h_norm : ‖(b_perp ii : W_perp)‖ = 1 := b_perp.orthonormal.1 ii
          simp only [Submodule.coe_norm] at h_norm
          rw [h_norm]
          norm_num
        · have h_ne : (Sum.inr ii : ι') ≠ Sum.inr jj := fun heq => h (Sum.inr.inj heq)
          simp only [h_ne, ↓reduceIte]
          have hb_ortho' := b_perp.orthonormal.2 h
          rw [← Submodule.coe_inner]
          exact hb_ortho'
  -- Define the eigenvalue function
  let μ : ι' → ℝ := fun i =>
    match i with
    | Sum.inl k => Classical.choose (hK_eig k.1 k.2)
    | Sum.inr _ => 0
  -- Prove that b' spans densely by showing its orthogonal complement is zero
  have hb'_span : (Submodule.span ℂ (Set.range b'))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [Submodule.mem_orthogonal] at hx
    -- x is orthogonal to all of b'
    -- Use the orthogonal decomposition: E = W ⊕ W_perp
    -- W is the span of K, so we can decompose x = x_W + x_perp
    have hx_to_K : ∀ k ∈ K, ⟪k, x⟫_ℂ = 0 := by
      intro k hk
      have h1 : k ∈ Set.range b' := ⟨Sum.inl ⟨k, hk⟩, rfl⟩
      have h2 := hx k (Submodule.subset_span h1)
      rw [← inner_conj_symm] at h2
      simpa using h2
    -- x is orthogonal to W = span K
    have hx_perp_W : x ∈ W_perp := by
      rw [Submodule.mem_orthogonal']
      intro y hy
      -- y is in span K, so we can write y as a linear combination of K
      -- and use hx_to_K
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
      · intro k hk
        rw [inner_eq_zero_symm]
        exact hx_to_K k hk
      · exact inner_zero_right (x := x)
      · intro u v _ _ hu hv
        rw [inner_add_right, hu, hv, add_zero]
      · intro c u _ hu
        rw [inner_smul_right, hu, mul_zero]
    -- x ∈ W_perp, and b_perp is a Hilbert basis for W_perp
    -- Show x is orthogonal to all of b_perp
    have hx_to_b_perp : ∀ j : b_perp_index, ⟪(b_perp j : W_perp), (⟨x, hx_perp_W⟩ : W_perp)⟫_ℂ = 0 := by
      intro j
      have h1 : (b_perp j : E) ∈ Set.range b' := ⟨Sum.inr j, rfl⟩
      have h2 := hx (b_perp j : E) (Submodule.subset_span h1)
      rw [← inner_conj_symm] at h2
      simp only [starRingEnd_apply, star_eq_zero] at h2
      rw [Submodule.coe_inner, inner_eq_zero_symm]
      exact h2
    -- Since b_perp spans W_perp, and x ∈ W_perp with ⟪b_perp j, x⟫ = 0 for all j, we have x = 0
    have hx_zero : (⟨x, hx_perp_W⟩ : W_perp) = 0 := by
      rw [← @inner_self_eq_zero ℂ W_perp _ _ _]
      have hx_expand := b_perp.tsum_inner_mul_inner (⟨x, hx_perp_W⟩ : W_perp) (⟨x, hx_perp_W⟩ : W_perp)
      simp only [hx_to_b_perp, mul_zero, tsum_zero] at hx_expand
      exact hx_expand.symm
    exact (Subtype.ext_iff.mp hx_zero : x = 0)
  let b'_hilbert := HilbertBasis.mkOfOrthogonalEqBot b'_ortho hb'_span
  have hb'_eq : ⇑b'_hilbert = b' := HilbertBasis.coe_mkOfOrthogonalEqBot b'_ortho hb'_span
  use ι', b'_hilbert, μ
  constructor
  · -- Eigenvector property
    intro i
    rw [hb'_eq]
    cases i with
    | inl k =>
      simp only [μ]
      exact Classical.choose_spec (hK_eig k.1 k.2)
    | inr j =>
      simp only [μ, zero_smul]
      have : T (b_perp j : E) = (T_perp (b_perp j) : E) := by
        rfl
      rw [this]
      have : T_perp (b_perp j) = 0 := by rw [hT_perp_eq_zero]; rfl
      simp [this]
  · -- Eigenvalue bounds
    intro i
    cases i with
    | inl k =>
      simp only [μ]
      let μ_k := Classical.choose (hK_eig k.1 k.2)
      by_cases h : μ_k = 0
      · left; exact h
      · right
        have hk_ne : (k : E) ≠ 0 := hK_ortho.ne_zero k
        have heig := Classical.choose_spec (hK_eig k.1 k.2)
        by_contra hneg
        have : μ_k = 0 := by
          have : |μ_k| ≤ 0 := le_of_not_gt hneg
          exact abs_nonpos_iff.mp this
        contradiction
    | inr j =>
      left
      simp only [μ]


/-- Legacy version for backward compatibility with existing code. -/
theorem exists_orthonormalBasis_eigenvectors_of_isCompact_isSelfAdjoint
    {T : E →L[ℂ] E}
    (hT_comp : IsCompact (T '' Metric.closedBall 0 1))
    (hsa : IsSelfAdjoint T) :
    ∃ (ι : Type u) (b : HilbertBasis ι ℂ E) (μ : ι → ℝ),
      ∀ i, T (b i) = (μ i) • b i := by
  -- Convert the compactness condition to IsCompactOperator
  have hT_compOp : IsCompactOperator T := by
    rw [isCompactOperator_iff_isCompact_image_closedBall]
    exact hT_comp.closure
  obtain ⟨ι, b, μ, h_eig, _⟩ := exists_orthonormalBasis_eigenvectors_of_isCompactOperator_isSelfAdjoint hT_compOp hsa
  exact ⟨ι, b, μ, h_eig⟩

/-- For a nonzero compact self-adjoint operator, there exists an eigenvector.
    This is an immediate corollary of the full spectral decomposition. -/
theorem exists_eigenvector_of_ne_zero_isCompactOperator_isSelfAdjoint
    {T : E →L[ℂ] E} (hT_ne : T ≠ 0) (hT_comp : IsCompactOperator T) (hsa : IsSelfAdjoint T) :
    ∃ (v : E) (μ : ℝ), v ≠ 0 ∧ T v = μ • v := by
  -- Extract from the full spectral decomposition
  obtain ⟨ι, b, μ, h_eig, h_bounds⟩ := exists_orthonormalBasis_eigenvectors_of_isCompactOperator_isSelfAdjoint hT_comp hsa
  -- Since T ≠ 0, there must exist a nonzero eigenvalue
  have : ∃ i, μ i ≠ 0 := by
    by_contra h_all_zero
    push_neg at h_all_zero
    apply hT_ne
    -- If all eigenvalues are zero, then T annihilates all basis vectors
    have h_zero_on_basis : ∀ i, T (b i) = 0 := by
      intro i
      rw [h_eig i, h_all_zero i]
      simp
    -- Therefore T = 0 everywhere by density
    have h_dense : Dense (↑(Submodule.span ℂ (Set.range b)) : Set E) :=
      Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span
    apply ContinuousLinearMap.ext_on h_dense
    intro v
    rintro ⟨i, rfl⟩
    exact h_zero_on_basis i
  obtain ⟨i, hi⟩ := this
  exact ⟨b i, μ i, b.orthonormal.ne_zero i, h_eig i⟩

/-! ### Eigenvalue relationship between T†T and TT† -/

/-- If v is an eigenvector of T†T with eigenvalue μ ≠ 0, then Tv is an eigenvector of TT† with the same eigenvalue.
    This is the key to showing |T| and |T†| have the same nonzero eigenvalues. -/
theorem eigenvector_adjoint_mul_self_gives_eigenvector_self_mul_adjoint
    {T : E →L[ℂ] E} {v : E} {mu : ℂ} (hmu : mu ≠ 0)
    (hv : (T.adjoint * T) v = mu • v) (hv_ne : v ≠ 0) :
    (T * T.adjoint) (T v) = mu • (T v) ∧ T v ≠ 0 := by
  constructor
  · -- (T T†) (T v) = T (T† T v) = T (μ v) = μ (T v)
    calc (T * T.adjoint) (T v)
        = T ((T.adjoint * T) v) := by simp [mul_apply]
      _ = T (mu • v) := by rw [hv]
      _ = mu • (T v) := by rw [map_smul]
  · -- T v ≠ 0 because T† T v = μ v with μ ≠ 0 and v ≠ 0
    intro h_Tv_zero
    have h : (T.adjoint * T) v = 0 := by simp [mul_apply, h_Tv_zero]
    rw [hv] at h
    simp [hmu, hv_ne] at h

/-- The nonzero eigenvalues of T†T and TT† coincide (with multiplicities).
    This implies the singular values of T and T† are the same. -/
theorem eigenvalues_adjoint_mul_eq_mul_adjoint {T : E →L[ℂ] E} {mu : ℂ} (hmu : mu ≠ 0) :
    Module.End.HasEigenvalue (T.adjoint * T).toLinearMap mu ↔
    Module.End.HasEigenvalue (T * T.adjoint).toLinearMap mu := by
  rw [Module.End.hasEigenvalue_iff, Module.End.hasEigenvalue_iff]
  constructor
  · intro h
    -- There exists nonzero v with T†T v = μ v
    rw [Submodule.ne_bot_iff] at h ⊢
    obtain ⟨v, hv_mem, hv_ne⟩ := h
    rw [Module.End.mem_eigenspace_iff] at hv_mem
    simp only [ContinuousLinearMap.coe_coe] at hv_mem
    -- Tv is eigenvector of TT† with eigenvalue μ
    obtain ⟨h_eig, h_ne⟩ := eigenvector_adjoint_mul_self_gives_eigenvector_self_mul_adjoint hmu hv_mem hv_ne
    exact ⟨T v, by rwa [Module.End.mem_eigenspace_iff], h_ne⟩
  · intro h
    -- There exists nonzero w with TT† w = μ w
    rw [Submodule.ne_bot_iff] at h ⊢
    obtain ⟨w, hw_mem, hw_ne⟩ := h
    rw [Module.End.mem_eigenspace_iff] at hw_mem
    simp only [ContinuousLinearMap.coe_coe] at hw_mem
    -- T†w is eigenvector of T†T with eigenvalue μ
    have h := eigenvector_adjoint_mul_self_gives_eigenvector_self_mul_adjoint (T := T.adjoint) hmu
      (by simp only [adjoint_adjoint]; exact hw_mem) hw_ne
    simp only [adjoint_adjoint] at h
    refine ⟨T.adjoint w, ?_, h.2⟩
    rw [Module.End.mem_eigenspace_iff]
    simp only [ContinuousLinearMap.coe_coe]
    exact h.1

end SpectralDecomposition

end TraceClass

end ContinuousLinearMap
