import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.InnerProductSpace.l2Space
import QuantumSystem.Algebra.CStarAlgebra.GNS.PureState

namespace GNS

namespace DirectSum

open ENNReal

variable {A : Type*} [NonUnitalCStarAlgebra A]


/-- The direct sum Hilbert space `⨁_{ψ : PureState A} H_ψ` is defined as the ℓ²-direct
sum of all GNS Hilbert spaces indexed by pure states, where `H ψ := (gnsRepresentation ψ).H`.

This is the space `lp (fun ψ : PureState A => H_ψ) 2`, which is a complex Hilbert space
when each component `H ψ` is a complex Hilbert space. -/
abbrev Hilbert (A : Type*) [NonUnitalCStarAlgebra A] :=
  ↥(lp (fun ψ : PureState A => (PureState.gnsRepresentation ψ).H) 2)


noncomputable instance : ComplexHilbertSpace (Hilbert A) where
  toNormedAddCommGroup := inferInstance
  toInnerProductSpace := inferInstance
  toCompleteSpace := inferInstance


/-- Maps an element `a : A` to the family of operators `{π_ψ(a)}` where `π_ψ` is the
GNS representation for each pure state `ψ`. This function returns, for each pure state,
the bounded operator on the corresponding GNS Hilbert space. -/
noncomputable def componentWiseMap (a : A) :
    ∀ (ψ : PureState A), 𝓑((PureState.gnsRepresentation ψ).H) :=
  fun ψ => (PureState.gnsRepresentation ψ).π a


/-- The component-wise map satisfies `‖π_ψ(a) v‖ ≤ ‖a‖ * ‖v‖` for each component `ψ`.
This follows from the fact that each GNS representation satisfies `‖π(a)‖ ≤ ‖a‖`. -/
lemma componentWiseMap_norm_le (a : A) (ψ : PureState A)
    (v : (PureState.gnsRepresentation ψ).H) :
    ‖componentWiseMap a ψ v‖ ≤ ‖a‖ * ‖v‖ :=
  calc ‖componentWiseMap a ψ v‖
    _ ≤ ‖componentWiseMap a ψ‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖a‖ * ‖v‖ := mul_le_mul_of_nonneg_right
        (GNS.Construction.πωStarHom_opNorm_le (ω := ψ.toState) a) (norm_nonneg _)



/-- Applying the component-wise map to an element of the direct sum Hilbert space
produces another element in ℓ² (i.e., the result has finite ℓ²-norm). -/
lemma componentWiseMap_memℓp (a : A) (x : Hilbert A) :
    Memℓp (fun ψ => componentWiseMap a ψ (x.val ψ)) 2 := by
  have hx : Memℓp x.val 2 := x.property
  rw [memℓp_gen_iff zero_lt_two] at hx ⊢
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  simp only [h2] at hx ⊢
  refine Summable.of_nonneg_of_le (fun ψ => by positivity) (fun ψ => ?_) (Summable.mul_left (‖a‖ ^ 2) hx)
  have h := componentWiseMap_norm_le a ψ (x.val ψ)
  show ‖componentWiseMap a ψ (x.val ψ)‖ ^ (2 : ℝ) ≤ ‖a‖ ^ 2 * ‖x.val ψ‖ ^ 2
  trans (‖a‖ * ‖x.val ψ‖) ^ (2 : ℝ)
  · gcongr
  · rw [Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    norm_cast


/-- The norm bound for the component-wise map. -/
lemma componentWiseMap_norm_bound (a : A) (x : Hilbert A) :
    ‖(⟨fun ψ => componentWiseMap a ψ (x.val ψ), componentWiseMap_memℓp a x⟩ : Hilbert A)‖ ≤ ‖a‖ * ‖x‖ := by
  have h2pos : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num

  rw [lp.norm_eq_tsum_rpow h2pos, lp.norm_eq_tsum_rpow h2pos]
  simp only [h2]

  have hsum1 : Summable fun ψ => ‖componentWiseMap a ψ (x.val ψ)‖ ^ (2 : ℝ) := by
    have := componentWiseMap_memℓp a x
    rw [memℓp_gen_iff zero_lt_two] at this
    simp only [h2] at this
    exact this

  have hsum2 : Summable fun ψ => ‖x.val ψ‖ ^ (2 : ℝ) := by
    have : Memℓp x.val 2 := x.property
    rw [memℓp_gen_iff zero_lt_two] at this
    simp only [h2] at this
    exact this

  have sum_ineq : ∑' ψ, ‖componentWiseMap a ψ (x.val ψ)‖ ^ (2 : ℝ) ≤ ‖a‖ ^ 2 * ∑' ψ, ‖x.val ψ‖ ^ (2 : ℝ) := by
    rw [← tsum_mul_left]
    apply tsum_le_of_sum_le' (by positivity)
    intro s
    calc ∑ ψ ∈ s, ‖componentWiseMap a ψ (x.val ψ)‖ ^ (2 : ℝ)
        _ ≤ ∑ ψ ∈ s, ‖a‖ ^ 2 * ‖x.val ψ‖ ^ (2 : ℝ) := by
          gcongr with ψ _
          have h := componentWiseMap_norm_le a ψ (x.val ψ)
          trans (‖a‖ * ‖x.val ψ‖) ^ (2 : ℝ)
          · gcongr
          · rw [Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
            norm_cast
        _ ≤ ∑' ψ, ‖a‖ ^ 2 * ‖x.val ψ‖ ^ (2 : ℝ) := by
          refine sum_le_hasSum _ (fun ψ _ => by positivity) (Summable.hasSum (Summable.mul_left _ hsum2))

  trans ((‖a‖ ^ 2 * ∑' ψ, ‖x.val ψ‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2))
  · gcongr
  rw [Real.mul_rpow (sq_nonneg _) (tsum_nonneg fun ψ => by positivity)]
  gcongr
  rw [← Real.rpow_natCast ‖a‖ 2, ← Real.rpow_mul (norm_nonneg _)]
  norm_num

/-- The linear map induced by the component-wise action of `a` on the direct sum
Hilbert space. This is the underlying linear map of `directSumCLM`. -/
noncomputable def directSumLinearMap (a : A) : Hilbert A →ₗ[ℂ] Hilbert A where
  toFun x := ⟨fun ψ => componentWiseMap a ψ (x.val ψ), componentWiseMap_memℓp a x⟩
  map_add' x y := by
    apply Subtype.ext
    funext ψ
    simp only [lp.coeFn_add, Pi.add_apply, map_add]
  map_smul' c x := by
    apply Subtype.ext
    funext ψ
    simp only [lp.coeFn_smul, Pi.smul_apply, map_smul, RingHom.id_apply]

/-- The bounded operator on the direct sum Hilbert space induced by `a : A`,
obtained by making `directSumLinearMap a` continuous with operator norm bound `‖a‖`. -/
noncomputable def directSumCLM (a : A) : 𝓑(Hilbert A) :=
  LinearMap.mkContinuous (directSumLinearMap a) ‖a‖ (componentWiseMap_norm_bound a)

/-- The adjoint of the direct sum operator equals the direct sum operator of the adjoint:
`(directSumCLM a)* = directSumCLM (star a)`. This follows from the *-homomorphism property
of each component GNS representation. -/
lemma directSumCLM_adjoint (a : A) :
    ContinuousLinearMap.adjoint (directSumCLM a) = directSumCLM (star a) := by
  refine ContinuousLinearMap.ext fun x => ?_
  apply ext_inner_right ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  -- Expand inner products to component-wise sums
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  -- Show: ∑_ψ ⟪π_ψ(a) (x ψ), y ψ⟫ = ∑_ψ ⟪x ψ, π_ψ(a*) (y ψ)⟫
  -- This holds because π_ψ(a)* = π_ψ(a*) for each ψ
  congr with ψ
  simp only [directSumCLM, LinearMap.mkContinuous_apply, directSumLinearMap,
    LinearMap.coe_mk, AddHom.coe_mk, componentWiseMap]
  -- Now we are at the component level
  -- ⟪π_ψ(a) (x ψ), y ψ⟫ = ⟪x ψ, (π_ψ(a))* (y ψ)⟫
  rw [← ContinuousLinearMap.adjoint_inner_left]
  -- And (π_ψ(a))* = π_ψ(a*) because π_ψ is a *-homomorphism
  rw [map_star]
  rw [ContinuousLinearMap.star_eq_adjoint]

/-- The direct sum representation as a non-unital *-algebra homomorphism from `A`
to bounded operators on the direct sum Hilbert space. This is the universal
representation used in the Gelfand-Naimark theorem. -/
noncomputable def directSumAlgHom : A →⋆ₙₐ[ℂ] 𝓑(Hilbert A) where
  toFun a := directSumCLM a
  map_mul' a b := by
    ext x : 1
    apply Subtype.ext
    funext ψ
    simp only [directSumCLM, LinearMap.mkContinuous_apply, directSumLinearMap,
      LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.mul_apply]
    rw [componentWiseMap, componentWiseMap, componentWiseMap]
    conv_lhs => rw [map_mul]
    rfl
  map_zero' := by
    ext x : 1
    apply Subtype.ext
    funext ψ
    simp only [directSumCLM, LinearMap.mkContinuous_apply, directSumLinearMap,
      LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.zero_apply]
    rw [componentWiseMap]
    rw [map_zero]
    rfl
  map_add' a b := by
    ext x : 1
    apply Subtype.ext
    funext ψ
    simp only [directSumCLM, LinearMap.mkContinuous_apply, directSumLinearMap,
      LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.add_apply, lp.coeFn_add, Pi.add_apply]
    rw [componentWiseMap, componentWiseMap, componentWiseMap]
    conv_lhs => rw [map_add]
    rfl
  map_smul' c a := by
    ext x : 1
    apply Subtype.ext
    funext ψ
    simp only [directSumCLM, LinearMap.mkContinuous_apply, directSumLinearMap,
      LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.smul_apply, lp.coeFn_smul,
      Pi.smul_apply]
    rw [componentWiseMap, componentWiseMap]
    conv_lhs => rw [map_smul]
    rfl
  map_star' a := by
    rw [← directSumCLM_adjoint]
    rfl


/-- The direct sum representation is injective (faithful).
This is the key property for the Gelfand-Naimark theorem.

The proof works by showing that if `a ≠ b`, there exists a pure state `ψ` such that
`ψ(star (a - b) * (a - b)) > 0`, which contradicts `directSumAlgHom a = directSumAlgHom b`
since this would imply `π_ψ(a - b) = 0` and hence `ψ(star (a - b) * (a - b)) = 0`. -/
theorem directSumAlgHom_injective : Function.Injective (directSumAlgHom (A := A)) := by
  intro a b hab
  by_contra h_ne
  -- If a ≠ b, then a - b ≠ 0
  have h_diff_ne_zero : a - b ≠ 0 := sub_ne_zero.mpr h_ne

  -- By exists_pureState_pos_of_ne_zero, there exists a pure state detecting a - b
  obtain ⟨φ, hφ_pure, hφ_pos⟩ := IsPureState.exists_pos_re_of_ne_zero (a - b) h_diff_ne_zero

  -- Package φ as a PureState
  let ψ : PureState A := ⟨φ, hφ_pure⟩

  -- From hab : directSumAlgHom a = directSumAlgHom b
  -- we get: directSumAlgHom (a - b) = 0
  have h_diff_zero : directSumAlgHom (a - b) = 0 := by
    rw [map_sub, hab, sub_self]

  -- This means directSumCLM (a - b) = 0
  have h_clm_zero : directSumCLM (a - b) = 0 := by
    -- directSumAlgHom's coercion is directSumCLM
    change directSumCLM (a - b) = 0
    have : directSumAlgHom (a - b) = 0 := h_diff_zero
    exact congr_arg (fun f => (f : 𝓑(Hilbert A))) this

  -- Therefore componentWiseMap (a - b) ψ = 0, i.e., π_ψ(a - b) = 0
  -- We'll show this leads to a contradiction with hφ_pos
  -- by proving φ(star(a-b) * (a-b)) = 0

  -- First, we claim that π_ψ(a - b) ξ = 0 where ξ is the cyclic vector
  have h_apply_xi : (PureState.gnsRepresentation ψ).π (a - b) ψ.gnsRepresentation.ξ = 0 := by
    -- From h_clm_zero, we have directSumCLM (a - b) = 0
    -- This means for all x : DirectSumHilbert A, (directSumCLM (a - b)) x = 0
    -- We'll construct x with x ψ = ξ and x ψ' = 0 for ψ' ≠ ψ
    have h_lin_zero : directSumLinearMap (a - b) = 0 := by
      have : (directSumCLM (a - b) : Hilbert A →ₗ[ℂ] Hilbert A) = directSumLinearMap (a - b) := rfl
      rw [h_clm_zero] at this
      simp only [ContinuousLinearMap.coe_zero] at this
      exact this.symm

    -- Construct the function that is ξ at ψ and 0 elsewhere
    classical
    let f : ∀ ψ' : PureState A, ψ'.gnsRepresentation.H :=
      fun ψ' => if h : ψ' = ψ then h ▸ ψ.gnsRepresentation.ξ else 0

    -- Show this is in ℓ²
    have hf_mem : Memℓp f 2 := by
      rw [memℓp_gen_iff zero_lt_two]
      have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
      simp only [h2]
      -- Only one term is nonzero: the ψ term
      have h_eq : (fun ψ' => ‖f ψ'‖ ^ (2 : ℝ)) = fun ψ' => if ψ' = ψ then ‖ψ.gnsRepresentation.ξ‖ ^ 2 else 0 := by
        ext ψ'
        simp only [f]
        by_cases h : ψ' = ψ
        · subst h
          simp
        · simp [dif_neg h]
          intro h'
          exact absurd h' h
      rw [h_eq]
      -- This is summable as it has support {ψ}
      apply summable_of_finite_support
      -- Show that the support is finite (in fact, it's {ψ})
      have : Function.support (fun ψ' => if ψ' = ψ then ‖ψ.gnsRepresentation.ξ‖ ^ 2 else 0) ⊆ {ψ} := by
        intro ψ' hψ'
        simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Set.mem_singleton_iff] at hψ' ⊢
        by_contra h
        simp [h] at hψ'
      exact Set.Finite.subset (Set.finite_singleton ψ) this

    let x : Hilbert A := ⟨f, hf_mem⟩

    -- x ψ = ξ
    have hx_ψ : x.val ψ = ψ.gnsRepresentation.ξ := by
      simp only [x, f]
      simp

    -- Apply h_lin_zero
    have : directSumLinearMap (a - b) x = 0 := by rw [h_lin_zero]; rfl
    have : (directSumLinearMap (a - b) x).val ψ = 0 := by rw [this]; rfl
    simp only [directSumLinearMap, LinearMap.coe_mk, AddHom.coe_mk] at this
    rw [hx_ψ] at this
    exact this

  -- Now we can proceed with the GNS condition argument

  -- By the GNS condition: ψ(c) = ⟨ξ, π(c)ξ⟩ for all c ∈ A
  have h_gns := (PureState.gnsRepresentation ψ).gns_condition (star (a - b) * (a - b))

  -- Use that π(star(a-b) * (a-b)) = π(star(a-b)) ∘ π(a-b)
  have h_comp : (ψ.gnsRepresentation.π (star (a - b) * (a - b))) ψ.gnsRepresentation.ξ =
      (ψ.gnsRepresentation.π (star (a - b))) ((ψ.gnsRepresentation.π (a - b)) ψ.gnsRepresentation.ξ) := by
    rw [map_mul]
    rfl

  rw [h_apply_xi, map_zero] at h_comp
  -- So the RHS of GNS condition becomes ⟨ξ, 0⟩ = 0

  -- This shows φ(star(a-b) * (a-b)) = 0, contradicting hφ_pos
  have hφ_zero : (φ (star (a - b) * (a - b))).re = 0 := by
    -- Note: ψ.toState and φ refer to the same functional
    have h_state_eq : (ψ.toState : A → ℂ) (star (a - b) * (a - b)) = φ (star (a - b) * (a - b)) := by
      rfl
    rw [← h_state_eq, h_gns, h_comp]
    simp only [inner_zero_right, Complex.zero_re]
  -- But this contradicts hφ_pos which says (φ (star (a - b) * (a - b))).re > 0
  rw [hφ_zero] at hφ_pos
  norm_num at hφ_pos

/-- The direct sum representation preserves norms: `‖directSumAlgHom a‖ = ‖a‖` for all `a : A`.
This follows from the general fact that injective *-homomorphisms between C*-algebras are isometric. -/
theorem directSumAlgHom_isometry (a : A) :
    ‖directSumAlgHom a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map directSumAlgHom directSumAlgHom_injective a

end DirectSum

end GNS
