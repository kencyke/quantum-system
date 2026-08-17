module

public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Data.Real.StarOrdered
public import QuantumSystem.Algebra.CStarAlgebra.Representation.Family
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.AdjointNotation

/-!
# Direct sum of a sector family

For a sector family `F : SectorFamily A` on a non-unital C\*-algebra
`A`, this file constructs:

* `F.directSumHilbert` — the `ℓ²`-direct sum Hilbert space
  `⨁_{α : F.Index} (F.rep α).H`.
* `F.directSumRep` — the block-diagonal universal representation
  `A →⋆ₙₐ[ℂ] 𝓑(F.directSumHilbert)`.
* `F.directSumRep_norm_le` — the operator-norm bound
  `‖F.directSumRep a‖ ≤ ‖a‖`.

The construction is criterion-agnostic: it depends only on the
indexed family of representations, not on any selection predicate
`P : CStarRep A → Prop`.  Faithfulness of `directSumRep` requires that
the family separates points (`F.SeparatesPoints`); see the
`directSumRep_injective_of` theorem.

## Comparison with `GNS.DirectSum`

`QuantumSystem.Algebra.CStarAlgebra.GNS.DirectSum.Hilbert A` is the
analogous `ℓ²`-direct sum indexed by *all* `PureState A`, with each
state contributing its GNS Hilbert space.  Two pure states whose GNS
representations are unitarily equivalent contribute the "same sector"
twice (once per state), so this "fat" direct sum is not a true sector
decomposition.  The skeleton version
(`PureState.sectorFamily` filtered to a skeleton in
`Sector/PureState/Family.lean`) avoids the over-counting.

## Main definitions

* `SectorFamily.directSumHilbert` — the direct-sum Hilbert space.
* `SectorFamily.sectorComponent` / `.sectorEmbed` — coordinate
  projection / embedding.
* `SectorFamily.directSumRep` — the block-diagonal universal
  `*`-representation.
-/

@[expose] public section

open ENNReal
open scoped Adjoint ComplexHilbertSpace

namespace SectorFamily

universe u v w

variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- The `ℓ²` direct-sum Hilbert space of the family. -/
noncomputable abbrev directSumHilbert (F : SectorFamily.{u, v, w} A) :=
  ↥(lp (fun α : F.Index => (F.rep α).H) 2)

noncomputable instance (F : SectorFamily.{u, v, w} A) :
    ComplexHilbertSpace F.directSumHilbert where
  toNormedAddCommGroup := inferInstance
  toInnerProductSpace := inferInstance
  toCompleteSpace := inferInstance

/-! ### Coordinate API

For each `α : F.Index`, the `α`-th coordinate of the direct-sum
Hilbert space is `(F.rep α).H`.  We provide:

* `sectorComponent F α` — coordinate projection
  `F.directSumHilbert →L[ℂ] (F.rep α).H`.
* `sectorEmbed F α` — coordinate embedding
  `(F.rep α).H →ₗᵢ[ℂ] F.directSumHilbert` (Mathlib `lp.single`
  packaged as a `LinearIsometry`).
-/

/-- The coordinate projection onto the `α`-th sector component, as a
continuous linear map. -/
noncomputable def sectorComponent (F : SectorFamily.{u, v, w} A)
    (α : F.Index) : F.directSumHilbert →L[ℂ] (F.rep α).H :=
  lp.evalCLM (𝕜 := ℂ) (fun α' : F.Index => (F.rep α').H) 2 α

/-- The coordinate embedding of `(F.rep α).H` into the direct-sum
Hilbert space at the `α`-th component, as a linear isometry. -/
noncomputable def sectorEmbed (F : SectorFamily.{u, v, w} A)
    (α : F.Index) : (F.rep α).H →ₗᵢ[ℂ] F.directSumHilbert :=
  letI : DecidableEq F.Index := Classical.decEq _
  { toLinearMap :=
      (lp.singleContinuousLinearMap (𝕜 := ℂ)
        (E := fun α' : F.Index => (F.rep α').H) 2 α).toLinearMap
    norm_map' := fun x =>
      lp.norm_single (E := fun α' : F.Index => (F.rep α').H)
        (by norm_num : (0 : ℝ≥0∞) < 2) α x }

@[simp] lemma sectorEmbed_apply_coord (F : SectorFamily.{u, v, w} A)
    (α : F.Index) (v : (F.rep α).H) :
    (sectorEmbed F α v).val α = v := by
  letI : DecidableEq F.Index := Classical.decEq _
  change (lp.single (E := fun α' : F.Index => (F.rep α').H) 2 α v) α = v
  exact lp.single_apply_self
    (E := fun α' : F.Index => (F.rep α').H) 2 α v

lemma sectorEmbed_apply_coord_ne (F : SectorFamily.{u, v, w} A)
    (α : F.Index) (v : (F.rep α).H)
    {α' : F.Index} (h : α' ≠ α) :
    (sectorEmbed F α v).val α' = 0 := by
  letI : DecidableEq F.Index := Classical.decEq _
  change (lp.single (E := fun α'' : F.Index => (F.rep α'').H) 2 α v) α' = 0
  exact lp.single_apply_ne
    (E := fun α'' : F.Index => (F.rep α'').H) 2 α v h

@[simp] lemma sectorComponent_sectorEmbed (F : SectorFamily.{u, v, w} A)
    (α : F.Index) (v : (F.rep α).H) :
    sectorComponent F α (sectorEmbed F α v) = v := by
  change (sectorEmbed F α v).val α = v
  exact sectorEmbed_apply_coord F α v

/-- Generic helper: from a `LinearIsometryEquiv` between a Hilbert space
`H` and the `α`-th fiber of the family, produce a `LinearIsometry`
embedding of `H` into the direct-sum Hilbert space.

Defined generically (the family `F` stays a variable so that the
costly `directSumHilbert`-family typeclass synthesis only fires here,
not at downstream specialized call sites). -/
noncomputable def sectorEmbedOfEquiv (F : SectorFamily.{u, v, w} A)
    (α : F.Index) {H : Type v} [ComplexHilbertSpace H]
    (eq : H ≃ₗᵢ[ℂ] (F.rep α).H) :
    H →ₗᵢ[ℂ] F.directSumHilbert :=
  (sectorEmbed F α).comp eq.toLinearIsometry

/-- The component-wise action of `a : A` on a fiber. -/
noncomputable def componentWiseMap (F : SectorFamily.{u, v, w} A) (a : A) :
    ∀ α : F.Index, 𝓑((F.rep α).H) :=
  fun α => (F.rep α).π a

/-- Norm bound on the component-wise action: each fibre is bounded by `‖a‖`. -/
lemma componentWiseMap_norm_le (F : SectorFamily.{u, v, w} A)
    (a : A) (α : F.Index) (v : (F.rep α).H) :
    ‖componentWiseMap F a α v‖ ≤ ‖a‖ * ‖v‖ := by
  -- `‖π_α(a) v‖ ≤ ‖π_α(a)‖ * ‖v‖ ≤ ‖a‖ * ‖v‖` since `‖π_α(a)‖ ≤ ‖a‖`
  -- for any C\*-algebra `*`-homomorphism into `𝓑(H)`.
  calc ‖componentWiseMap F a α v‖
      _ ≤ ‖componentWiseMap F a α‖ * ‖v‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖a‖ * ‖v‖ :=
        mul_le_mul_of_nonneg_right
          (NonUnitalStarAlgHom.norm_apply_le (φ := (F.rep α).π) a)
          (norm_nonneg _)

/-- The component-wise image of an `ℓ²` family stays in `ℓ²`. -/
lemma componentWiseMap_memℓp (F : SectorFamily.{u, v, w} A) (a : A)
    (x : F.directSumHilbert) :
    Memℓp (fun α => componentWiseMap F a α (x.val α)) 2 := by
  have hx : Memℓp x.val 2 := x.property
  rw [memℓp_gen_iff zero_lt_two] at hx ⊢
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  simp only [h2] at hx ⊢
  refine Summable.of_nonneg_of_le (fun α => by positivity) (fun α => ?_)
    (Summable.mul_left (‖a‖ ^ 2) hx)
  have h := componentWiseMap_norm_le F a α (x.val α)
  change ‖componentWiseMap F a α (x.val α)‖ ^ (2 : ℝ) ≤ ‖a‖ ^ 2 * ‖x.val α‖ ^ 2
  trans (‖a‖ * ‖x.val α‖) ^ (2 : ℝ)
  · gcongr
  · rw [Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    norm_cast

/-- The component-wise operator norm bound, summed in `ℓ²`. -/
lemma componentWiseMap_norm_bound (F : SectorFamily.{u, v, w} A) (a : A)
    (x : F.directSumHilbert) :
    ‖(⟨fun α => componentWiseMap F a α (x.val α),
        componentWiseMap_memℓp F a x⟩ : F.directSumHilbert)‖ ≤ ‖a‖ * ‖x‖ := by
  have h2pos : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [lp.norm_eq_tsum_rpow h2pos, lp.norm_eq_tsum_rpow h2pos]
  simp only [h2]
  have hsum1 : Summable fun α => ‖componentWiseMap F a α (x.val α)‖ ^ (2 : ℝ) := by
    have := componentWiseMap_memℓp F a x
    rw [memℓp_gen_iff zero_lt_two] at this
    simp only [h2] at this
    exact this
  have hsum2 : Summable fun α => ‖x.val α‖ ^ (2 : ℝ) := by
    have : Memℓp x.val 2 := x.property
    rw [memℓp_gen_iff zero_lt_two] at this
    simp only [h2] at this
    exact this
  have sum_ineq :
      ∑' α, ‖componentWiseMap F a α (x.val α)‖ ^ (2 : ℝ) ≤
        ‖a‖ ^ 2 * ∑' α, ‖x.val α‖ ^ (2 : ℝ) := by
    rw [← tsum_mul_left]
    apply tsum_le_of_sum_le' (by positivity)
    intro s
    calc ∑ α ∈ s, ‖componentWiseMap F a α (x.val α)‖ ^ (2 : ℝ)
        _ ≤ ∑ α ∈ s, ‖a‖ ^ 2 * ‖x.val α‖ ^ (2 : ℝ) := by
          gcongr with α _
          have h := componentWiseMap_norm_le F a α (x.val α)
          trans (‖a‖ * ‖x.val α‖) ^ (2 : ℝ)
          · gcongr
          · rw [Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
            norm_cast
        _ ≤ ∑' α, ‖a‖ ^ 2 * ‖x.val α‖ ^ (2 : ℝ) := by
          refine sum_le_hasSum _ (fun α _ => by positivity)
            (Summable.hasSum (Summable.mul_left _ hsum2))
  trans ((‖a‖ ^ 2 * ∑' α, ‖x.val α‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2))
  · gcongr
  rw [Real.mul_rpow (sq_nonneg _) (tsum_nonneg fun α => by positivity)]
  gcongr
  rw [← Real.rpow_natCast ‖a‖ 2, ← Real.rpow_mul (norm_nonneg _)]
  norm_num

/-- The linear-map version of the block-diagonal action of `a` on the
direct-sum Hilbert space. -/
noncomputable def directSumLinearMap (F : SectorFamily.{u, v, w} A) (a : A) :
    F.directSumHilbert →ₗ[ℂ] F.directSumHilbert where
  toFun x := ⟨fun α => componentWiseMap F a α (x.val α),
              componentWiseMap_memℓp F a x⟩
  map_add' x y := by
    apply Subtype.ext
    funext α
    simp only [lp.coeFn_add, Pi.add_apply, map_add]
  map_smul' c x := by
    apply Subtype.ext
    funext α
    simp only [lp.coeFn_smul, Pi.smul_apply, map_smul, RingHom.id_apply]

/-- The bounded-operator version of the block-diagonal action of `a`. -/
noncomputable def directSumCLM (F : SectorFamily.{u, v, w} A) (a : A) :
    𝓑(F.directSumHilbert) :=
  LinearMap.mkContinuous (F.directSumLinearMap a) ‖a‖
    (componentWiseMap_norm_bound F a)

/-- Block-diagonality is compatible with the `*`-structure. -/
lemma directSumCLM_adjoint (F : SectorFamily.{u, v, w} A) (a : A) :
    (F.directSumCLM a)† = F.directSumCLM (star a) := by
  refine ContinuousLinearMap.ext fun x => ?_
  apply ext_inner_right ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  congr with α
  simp only [directSumCLM, LinearMap.mkContinuous_apply, directSumLinearMap,
    LinearMap.coe_mk, AddHom.coe_mk, componentWiseMap]
  rw [← ContinuousLinearMap.adjoint_inner_left]
  rw [map_star]
  rw [ContinuousLinearMap.star_eq_adjoint]

/-- The block-diagonal universal `*`-representation associated with a
sector family. -/
noncomputable def directSumRep (F : SectorFamily.{u, v, w} A) :
    A →⋆ₙₐ[ℂ] 𝓑(F.directSumHilbert) where
  toFun a := F.directSumCLM a
  map_mul' a b := by
    ext x : 1
    apply Subtype.ext
    funext α
    simp only [directSumCLM, LinearMap.mkContinuous_apply, directSumLinearMap,
      LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.mul_apply]
    rw [componentWiseMap, componentWiseMap, componentWiseMap]
    conv_lhs => rw [map_mul]
    rfl
  map_zero' := by
    ext x : 1
    apply Subtype.ext
    funext α
    simp only [directSumCLM, LinearMap.mkContinuous_apply, directSumLinearMap,
      LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.zero_apply]
    rw [componentWiseMap]
    rw [map_zero]
    rfl
  map_add' a b := by
    ext x : 1
    apply Subtype.ext
    funext α
    simp only [directSumCLM, LinearMap.mkContinuous_apply, directSumLinearMap,
      LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.add_apply,
      lp.coeFn_add, Pi.add_apply]
    rw [componentWiseMap, componentWiseMap, componentWiseMap]
    conv_lhs => rw [map_add]
    rfl
  map_smul' c a := by
    ext x : 1
    apply Subtype.ext
    funext α
    simp only [directSumCLM, LinearMap.mkContinuous_apply, directSumLinearMap,
      LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.smul_apply,
      lp.coeFn_smul, Pi.smul_apply]
    rw [componentWiseMap, componentWiseMap]
    conv_lhs => rw [map_smul]
    rfl
  map_star' a := by
    rw [← directSumCLM_adjoint]
    rfl

/-- The operator-norm bound `‖F.directSumRep a‖ ≤ ‖a‖`. -/
lemma directSumRep_norm_le (F : SectorFamily.{u, v, w} A) (a : A) :
    ‖F.directSumRep a‖ ≤ ‖a‖ := by
  change ‖F.directSumCLM a‖ ≤ ‖a‖
  exact LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

/-- A sector family *separates points* if the family of representations
separates `A`: whenever every member annihilates `a`, we have `a = 0`. -/
def SeparatesPoints (F : SectorFamily.{u, v, w} A) : Prop :=
  ∀ a : A, (∀ α : F.Index, (F.rep α).π a = 0) → a = 0

/-- **Faithfulness of the direct-sum representation** under a
points-separation condition on the family: if the family separates `A`,
then `F.directSumRep` is injective. -/
theorem directSumRep_injective_of (F : SectorFamily.{u, v, w} A)
    (h_sep : F.SeparatesPoints) :
    Function.Injective F.directSumRep := by
  intro a b hab
  -- It suffices to show `a - b = 0`.
  rw [← sub_eq_zero]
  -- `F.directSumRep (a - b) = 0` from `hab` by linearity.
  have h_diff_zero : F.directSumRep (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  -- `F.directSumCLM (a - b) = 0` (the underlying bounded operator).
  have h_clm_zero : F.directSumCLM (a - b) = 0 := h_diff_zero
  -- Apply separation: every family member annihilates `a - b`.
  apply h_sep
  intro α
  ext v
  -- Goal: `(F.rep α).π (a - b) v = 0`.
  classical
  -- Construct the `δ_α`-vector in `directSumHilbert` carrying `v` in the
  -- `α`-th component and `0` elsewhere.
  let f : ∀ α' : F.Index, (F.rep α').H :=
    fun α' => if h : α' = α then h ▸ v else 0
  have hf_mem : Memℓp f 2 := by
    rw [memℓp_gen_iff zero_lt_two]
    have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    simp only [h2]
    have h_eq : (fun α' => ‖f α'‖ ^ (2 : ℝ)) =
        fun α' => if α' = α then ‖v‖ ^ 2 else 0 := by
      ext α'
      simp only [f]
      by_cases h : α' = α
      · subst h; simp
      · simp only [dif_neg h, if_neg h]; simp
    rw [h_eq]
    apply summable_of_hasFiniteSupport
    have :
        Function.support (fun α' => if α' = α then ‖v‖ ^ 2 else 0) ⊆ {α} := by
      intro α' hα'
      simp only [Function.mem_support, ne_eq, ite_eq_right_iff,
        Set.mem_singleton_iff] at hα' ⊢
      by_contra h
      simp [h] at hα'
    exact Set.Finite.subset (Set.finite_singleton α) this
  let x : F.directSumHilbert := ⟨f, hf_mem⟩
  have hx_α : x.val α = v := by
    simp only [x, f]; simp
  -- Apply `h_clm_zero` to `x`.
  have h0 : F.directSumCLM (a - b) x = 0 := by simp [h_clm_zero]
  have hα0 : (F.directSumCLM (a - b) x).val α = 0 := by
    simpa using congrArg (fun y : F.directSumHilbert => y.val α) h0
  -- Unfold the `α`-coordinate.
  have hcomp : componentWiseMap F (a - b) α (x.val α) = 0 := by
    simpa [directSumCLM, directSumLinearMap] using hα0
  simpa [componentWiseMap, hx_α] using hcomp

end SectorFamily
