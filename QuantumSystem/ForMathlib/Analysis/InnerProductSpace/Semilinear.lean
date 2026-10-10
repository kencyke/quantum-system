/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Semilinear maps between complex inner product spaces

The isometric ring endomorphisms of `ℂ` are the identity and the complex conjugation
(`Complex.ringHom_eq_id_or_conj_of_continuous`). For such a `σ`, this file develops the
inner-product theory of `σ`-semilinear maps: complex-linear maps (`σ = RingHom.id ℂ`) and
conjugate-linear maps (`σ = starRingEnd ℂ`) are treated uniformly.

* A `σ`-semilinear isometry `V` transforms inner products by `σ`: `⟪V x, V y⟫ = σ ⟪x, y⟫`. For
  `σ = id` this is Mathlib's `LinearIsometry.inner_map_map`; for the complex conjugation it is the
  defining property `⟪J x, J y⟫ = conj ⟪x, y⟫` of an antiunitary `J`.
* The adjoint of a bounded `σ`-semilinear `U : E →SL[σ] F` is the bounded `σ'`-semilinear
  `U.adjointₛₗ : F →SL[σ'] E` characterised by `⟪U.adjointₛₗ y, x⟫ = σ' ⟪y, U x⟫`.
* The adjoint of a partially defined `σ`-semilinear `T : E →ₛₗ.[σ] F` is the partially defined
  `σ'`-semilinear `T.adjointₛₗ : F →ₛₗ.[σ'] E`, with the same characterisation on its domain
  `{y | x ↦ ⟪y, T x⟫ is continuous on dom T}` when `dom T` is dense.

## Main definitions

* `ContinuousLinearMap.adjointₛₗ` — the adjoint of a bounded semilinear map.
* `LinearPMap.IsFormalAdjointₛₗ` — `⟪T x, y⟫ = σ ⟪x, S y⟫` on the domains.
* `LinearPMap.adjointₛₗ` — the adjoint of a semilinear partially defined map.

## Main results

* `RingHom.eq_id_or_conj_of_isometric`, `RingHom.eq_id_or_conj_of_ringHomIsometric` — an isometric
  ring endomorphism `σ` of `ℂ`, and its inverse `σ'`, are the identity or the conjugation.
* `RingHom.norm_apply_of_ringHomInvPair`, `RingHom.continuous_of_ringHomInvPair`,
  `RingHom.apply_ofReal_of_ringHomInvPair`, `RingHom.apply_I_of_ringHomIsometric` — consequences:
  `σ'` is isometric and continuous, fixes the reals, and `σ i = ± i`, `σ' i = ± i`.
* `RingHom.apply_ofReal_of_isometric`, `RingHom.apply_conj_of_isometric` — `σ` fixes the reals and
  commutes with the conjugation.
* `LinearIsometry.inner_map_mapₛₗ`, `LinearIsometryEquiv.inner_map_mapₛₗ` —
  `⟪V x, V y⟫ = σ ⟪x, y⟫`.
* `ContinuousLinearMap.adjointₛₗ_inner_left`, `ContinuousLinearMap.adjointₛₗ_apply_eq` — the
  defining property and the characterisation of the bounded adjoint.
* `LinearIsometryEquiv.adjointₛₗ_eq_symm` — the adjoint of an antiunitary (or unitary) is its
  inverse.
* `LinearPMap.inner_adjointₛₗ_apply`, `LinearPMap.adjointₛₗ_apply_eq` — the defining property and
  the characterisation of the unbounded adjoint.
* `LinearPMap.IsFormalAdjointₛₗ.le_adjointₛₗ` — a formal adjoint is a restriction of the adjoint.

## Implementation notes

Mathlib defines `ContinuousLinearMap.adjoint`, `LinearPMap.IsFormalAdjoint` and
`LinearPMap.adjoint` only for linear maps, so the conjugate-linear case (Tomita operators, modular
conjugations) has no home there. The constructions here follow Mathlib's linear ones verbatim, with
`σ'` inserted where conjugate-linearity enters. For `σ = RingHom.id ℂ` each notion agrees with
Mathlib's, recorded by exactly one compatibility lemma per notion:
`ContinuousLinearMap.adjointₛₗ_eq_adjoint`, `LinearPMap.isFormalAdjointₛₗ_iff_isFormalAdjoint` and
`LinearPMap.adjointₛₗ_eq_adjoint`.

## TODO

Upstream to Mathlib, generalising `ContinuousLinearMap.adjoint` and `LinearPMap.adjoint` to
semilinear maps so that the compatibility lemmas become definitional.
-/

@[expose] public section

open Complex
open scoped InnerProductSpace InnerProduct ComplexConjugate LinearPMap

/-! ### Isometric ring endomorphisms of `ℂ` -/

section RingHom

variable {σ σ' : ℂ →+* ℂ}

/-- An isometric ring endomorphism of `ℂ` is the identity or the complex conjugation. -/
lemma RingHom.eq_id_or_conj_of_isometric (σ : ℂ →+* ℂ) [RingHomIsometric σ] :
    σ = RingHom.id ℂ ∨ σ = starRingEnd ℂ :=
  Complex.ringHom_eq_id_or_conj_of_continuous
    (AddMonoidHomClass.isometry_of_norm σ fun _ => RingHomIsometric.norm_map).continuous

/-- An isometric ring endomorphism of `ℂ` with inverse `σ'` is the identity or the complex
conjugation, and so is `σ'`. -/
lemma RingHom.eq_id_or_conj_of_ringHomIsometric [RingHomInvPair σ σ'] [RingHomIsometric σ] :
    (σ = RingHom.id ℂ ∧ σ' = RingHom.id ℂ) ∨ (σ = starRingEnd ℂ ∧ σ' = starRingEnd ℂ) := by
  rcases RingHom.eq_id_or_conj_of_isometric σ with rfl | rfl
  · refine Or.inl ⟨rfl, RingHom.ext fun x => ?_⟩
    simpa using (RingHomInvPair.comp_apply_eq₂ (σ := RingHom.id ℂ) (σ' := σ') (x := x))
  · refine Or.inr ⟨rfl, RingHom.ext fun x => ?_⟩
    have h := congrArg (starRingEnd ℂ)
      (RingHomInvPair.comp_apply_eq₂ (σ := starRingEnd ℂ) (σ' := σ') (x := x))
    rwa [Complex.conj_conj] at h

/-- The inverse of an isometric ring endomorphism of `ℂ` is isometric. -/
lemma RingHom.norm_apply_of_ringHomInvPair (σ : ℂ →+* ℂ) [RingHomInvPair σ σ']
    [RingHomIsometric σ] (z : ℂ) : ‖σ' z‖ = ‖z‖ := by
  rcases RingHom.eq_id_or_conj_of_ringHomIsometric (σ := σ) (σ' := σ') with
    ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp

/-- The inverse of an isometric ring endomorphism of `ℂ` is continuous. -/
lemma RingHom.continuous_of_ringHomInvPair (σ : ℂ →+* ℂ) [RingHomInvPair σ σ']
    [RingHomIsometric σ] : Continuous σ' := by
  rcases RingHom.eq_id_or_conj_of_ringHomIsometric (σ := σ) (σ' := σ') with
    ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact continuous_id
  · exact Complex.continuous_conj

/-- The inverse of an isometric ring endomorphism of `ℂ` fixes the reals. -/
lemma RingHom.apply_ofReal_of_ringHomInvPair (σ : ℂ →+* ℂ) [RingHomInvPair σ σ']
    [RingHomIsometric σ] (r : ℝ) : σ' r = r := by
  rcases RingHom.eq_id_or_conj_of_ringHomIsometric (σ := σ) (σ' := σ') with
    ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp

/-- `σ i = ± i` and `σ' i = ± i` for an isometric ring endomorphism `σ` of `ℂ` with inverse
`σ'`. -/
lemma RingHom.apply_I_of_ringHomIsometric [RingHomInvPair σ σ'] [RingHomIsometric σ] :
    (σ Complex.I = Complex.I ∨ σ Complex.I = -Complex.I) ∧
      (σ' Complex.I = Complex.I ∨ σ' Complex.I = -Complex.I) := by
  rcases RingHom.eq_id_or_conj_of_ringHomIsometric (σ := σ) (σ' := σ') with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

/-- An isometric ring endomorphism of `ℂ` fixes the reals. -/
lemma RingHom.apply_ofReal_of_isometric (σ : ℂ →+* ℂ) [RingHomIsometric σ] (r : ℝ) : σ r = r := by
  rcases RingHom.eq_id_or_conj_of_isometric σ with rfl | rfl <;> simp

/-- An isometric ring endomorphism of `ℂ` fixes the real multiples of `1`; this is the hypothesis
of `LinearPMap.restrictScalars ℝ`. -/
lemma RingHom.apply_real_smul_one_of_isometric (σ : ℂ →+* ℂ) [RingHomIsometric σ] (r : ℝ) :
    σ (r • 1) = r • 1 := by
  rw [Complex.real_smul, mul_one, RingHom.apply_ofReal_of_isometric]

/-- An isometric ring endomorphism of `ℂ` commutes with the complex conjugation. -/
lemma RingHom.apply_conj_of_isometric (σ : ℂ →+* ℂ) [RingHomIsometric σ] (z : ℂ) :
    σ (conj z) = conj (σ z) := by
  rcases RingHom.eq_id_or_conj_of_isometric σ with rfl | rfl <;> simp

/-- The inverse of an isometric ring endomorphism of `ℂ` commutes with the complex conjugation. -/
lemma RingHom.apply_conj_of_ringHomInvPair (σ : ℂ →+* ℂ) [RingHomInvPair σ σ'] [RingHomIsometric σ]
    (z : ℂ) : σ' (conj z) = conj (σ' z) := by
  rcases RingHom.eq_id_or_conj_of_ringHomIsometric (σ := σ) (σ' := σ') with
    ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp

/-- The inverse of an isometric ring endomorphism of `ℂ` is isometric. -/
lemma RingHom.ringHomIsometric_of_ringHomInvPair (σ : ℂ →+* ℂ) [RingHomInvPair σ σ']
    [RingHomIsometric σ] : RingHomIsometric σ' :=
  ⟨fun {z} => RingHom.norm_apply_of_ringHomInvPair σ z⟩

end RingHom

/-! ### Inner products -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F]
  [InnerProductSpace ℂ F] {σ : ℂ →+* ℂ} [RingHomIsometric σ]

/-- A semilinear isometry for an isometric ring endomorphism `σ` of `ℂ` transforms inner products
by `σ`: `⟪V x, V y⟫ = σ ⟪x, y⟫`. -/
lemma LinearIsometry.inner_map_mapₛₗ (V : E →ₛₗᵢ[σ] F) (x y : E) :
    ⟪V x, V y⟫_ℂ = σ ⟪x, y⟫_ℂ := by
  rcases RingHom.eq_id_or_conj_of_isometric σ with rfl | rfl
  · exact V.inner_map_map x y
  · have hI : Complex.I • V y = V (-Complex.I • y) := by
      rw [V.map_smulₛₗ, map_neg, conj_I, neg_neg]
    have hre : (⟪V x, V y⟫_ℂ).re = (⟪x, y⟫_ℂ).re := by
      have h₁ := re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four (𝕜 := ℂ) (V x) (V y)
      have h₂ := re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four (𝕜 := ℂ) x y
      rw [← map_add, ← map_sub, V.norm_map, V.norm_map] at h₁
      simpa [← h₂] using h₁
    have him : (⟪V x, V y⟫_ℂ).im = -(⟪x, y⟫_ℂ).im := by
      have h₁ := im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four
        (𝕜 := ℂ) (V x) (V y)
      have h₂ := im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four
        (𝕜 := ℂ) x y
      simp only [RCLike.I_to_complex] at h₁ h₂
      rw [hI, ← map_sub, ← map_add, V.norm_map, V.norm_map, neg_smul, sub_neg_eq_add,
        ← sub_eq_add_neg] at h₁
      simp only [RCLike.im_to_complex] at h₁ h₂
      rw [h₁, h₂]
      ring
    apply Complex.ext
    · rw [conj_re]
      exact hre
    · rw [conj_im]
      exact him

/-- A semilinear isometric equivalence for an isometric ring endomorphism `σ` of `ℂ` transforms
inner products by `σ`: `⟪V x, V y⟫ = σ ⟪x, y⟫`. -/
lemma LinearIsometryEquiv.inner_map_mapₛₗ {σ' : ℂ →+* ℂ} [RingHomInvPair σ σ']
    [RingHomInvPair σ' σ] (V : E ≃ₛₗᵢ[σ] F) (x y : E) : ⟪V x, V y⟫_ℂ = σ ⟪x, y⟫_ℂ :=
  V.toLinearIsometry.inner_map_mapₛₗ x y

/-! ### Adjoints of bounded semilinear maps -/

namespace ContinuousLinearMap

variable {σ' : ℂ →+* ℂ} [RingHomInvPair σ σ']

/-- The bounded functional `x ↦ σ' ⟪y, U x⟫` on `E`, for a bounded `σ`-semilinear `U`; the adjoint
`U.adjointₛₗ y` is the vector representing it (`ContinuousLinearMap.adjointₛₗ_inner_left`). -/
noncomputable def adjointDualₛₗ (U : E →SL[σ] F) (y : F) : StrongDual ℂ E :=
  LinearMap.mkContinuous
    { toFun := fun x => σ' ⟪y, U x⟫_ℂ
      map_add' := fun x x' => by rw [map_add, inner_add_right, map_add]
      map_smul' := fun c x => by
        rw [map_smulₛₗ, inner_smul_right, map_mul, RingHomInvPair.comp_apply_eq, RingHom.id_apply,
          smul_eq_mul] }
    (‖y‖ * ‖U‖) fun x => by
      change ‖σ' ⟪y, U x⟫_ℂ‖ ≤ ‖y‖ * ‖U‖ * ‖x‖
      rw [RingHom.norm_apply_of_ringHomInvPair σ, mul_assoc]
      exact (norm_inner_le_norm (𝕜 := ℂ) y (U x)).trans
        (mul_le_mul_of_nonneg_left (U.le_opNorm x) (norm_nonneg y))

/-- The functional `x ↦ σ' ⟪y, U x⟫`. -/
@[simp]
lemma adjointDualₛₗ_apply (U : E →SL[σ] F) (y : F) (x : E) :
    U.adjointDualₛₗ (σ' := σ') y x = σ' ⟪y, U x⟫_ℂ :=
  rfl

variable [CompleteSpace E]

/-- The **adjoint** of a bounded `σ`-semilinear map `U : E → F` between complex Hilbert spaces, for
an isometric `σ` (the identity or the conjugation) with inverse `σ'`: the bounded `σ'`-semilinear
map `U†` with `⟪U† y, x⟫ = σ' ⟪y, U x⟫` (`ContinuousLinearMap.adjointₛₗ_inner_left`). For a
conjugate-linear `U` this is the antilinear adjoint `⟪U† y, x⟫ = conj ⟪y, U x⟫` of the literature;
for a complex-linear `U` it is Mathlib's `ContinuousLinearMap.adjoint`
(`ContinuousLinearMap.adjointₛₗ_eq_adjoint`). -/
noncomputable def adjointₛₗ (U : E →SL[σ] F) : F →SL[σ'] E :=
  LinearMap.mkContinuous
    { toFun := fun y => (InnerProductSpace.toDual ℂ E).symm (U.adjointDualₛₗ y)
      map_add' := fun y y' => ext_inner_right ℂ fun x => by
        simp only [InnerProductSpace.toDual_symm_apply, inner_add_left, adjointDualₛₗ_apply,
          map_add]
      map_smul' := fun c y => ext_inner_right ℂ fun x => by
        simp only [InnerProductSpace.toDual_symm_apply, inner_smul_left, adjointDualₛₗ_apply,
          map_mul]
        rw [RingHom.apply_conj_of_ringHomInvPair σ] }
    ‖U‖ fun y => by
      change ‖(InnerProductSpace.toDual ℂ E).symm (U.adjointDualₛₗ y)‖ ≤ ‖U‖ * ‖y‖
      rw [LinearIsometryEquiv.norm_map, mul_comm]
      exact LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- **The defining property of the adjoint**: `⟪U† y, x⟫ = σ' ⟪y, U x⟫`. -/
lemma adjointₛₗ_inner_left (U : E →SL[σ] F) (x : E) (y : F) :
    ⟪U.adjointₛₗ (σ' := σ') y, x⟫_ℂ = σ' ⟪y, U x⟫_ℂ :=
  InnerProductSpace.toDual_symm_apply

/-- `⟪x, U† y⟫ = σ' ⟪U x, y⟫`. -/
lemma adjointₛₗ_inner_right (U : E →SL[σ] F) (x : E) (y : F) :
    ⟪x, U.adjointₛₗ (σ' := σ') y⟫_ℂ = σ' ⟪U x, y⟫_ℂ := by
  rw [← inner_conj_symm, adjointₛₗ_inner_left, ← RingHom.apply_conj_of_ringHomInvPair σ,
    inner_conj_symm]

/-- The adjoint is characterised by its inner products: if `⟪w, x⟫ = σ' ⟪y, U x⟫` for all `x`,
then `U† y = w`. -/
lemma adjointₛₗ_apply_eq (U : E →SL[σ] F) {y : F} {w : E} (h : ∀ x, ⟪w, x⟫_ℂ = σ' ⟪y, U x⟫_ℂ) :
    U.adjointₛₗ y = w :=
  ext_inner_right ℂ fun x => by rw [adjointₛₗ_inner_left, h]

/-- The adjoint is a contraction relative to `U`: `‖U†‖ ≤ ‖U‖`. -/
lemma norm_adjointₛₗ_le (U : E →SL[σ] F) : ‖U.adjointₛₗ (σ' := σ')‖ ≤ ‖U‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

omit [RingHomIsometric σ] in
/-- For a complex-linear `U`, `ContinuousLinearMap.adjointₛₗ` is Mathlib's
`ContinuousLinearMap.adjoint`. -/
lemma adjointₛₗ_eq_adjoint [CompleteSpace F] (U : E →L[ℂ] F) : U.adjointₛₗ = U† :=
  ContinuousLinearMap.ext fun y => adjointₛₗ_apply_eq U fun x => by
    rw [ContinuousLinearMap.adjoint_inner_left, RingHom.id_apply]

end ContinuousLinearMap

/-- The adjoint of a semilinear isometric equivalence is its inverse: `V† = V⁻¹`. -/
lemma LinearIsometryEquiv.adjointₛₗ_eq_symm [CompleteSpace E] {σ' : ℂ →+* ℂ}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (V : E ≃ₛₗᵢ[σ] F) :
    (V : E →SL[σ] F).adjointₛₗ = (V.symm : F →SL[σ'] E) :=
  ContinuousLinearMap.ext fun y => ContinuousLinearMap.adjointₛₗ_apply_eq _ fun x => by
    have := RingHom.ringHomIsometric_of_ringHomInvPair (σ' := σ') σ
    have h := V.symm.inner_map_mapₛₗ y (V x)
    rw [V.symm_apply_apply] at h
    exact h

/-! ### Adjoints of semilinear partially defined maps -/

namespace LinearPMap

variable {σ' : ℂ →+* ℂ} [RingHomInvPair σ σ'] (T : E →ₛₗ.[σ] F)

/-- A `σ`-semilinear `T : E → F` and a `σ'`-semilinear `S : F → E` are **formal adjoints** if
`⟪T x, y⟫ = σ ⟪x, S y⟫` for `x ∈ dom T` and `y ∈ dom S`. For linear maps this is Mathlib's
`LinearPMap.IsFormalAdjoint` (`LinearPMap.isFormalAdjointₛₗ_iff_isFormalAdjoint`). -/
def IsFormalAdjointₛₗ {σ₁ σ₂ : ℂ →+* ℂ} (T : E →ₛₗ.[σ₁] F) (S : F →ₛₗ.[σ₂] E) : Prop :=
  ∀ (x : T.domain) (y : S.domain), ⟪T x, (y : F)⟫_ℂ = σ₁ ⟪(x : E), S y⟫_ℂ

/-- Formal adjointness is symmetric. -/
lemma IsFormalAdjointₛₗ.symm {T : E →ₛₗ.[σ] F} {S : F →ₛₗ.[σ'] E} (h : T.IsFormalAdjointₛₗ S) :
    S.IsFormalAdjointₛₗ T := fun y x => by
  rw [← inner_conj_symm, ← RingHomInvPair.comp_apply_eq (σ := σ) (σ' := σ') (x := ⟪(x : E), S y⟫_ℂ),
    ← h x y, ← RingHom.apply_conj_of_ringHomInvPair σ, inner_conj_symm]

/-- For linear maps, `LinearPMap.IsFormalAdjointₛₗ` is Mathlib's `LinearPMap.IsFormalAdjoint`. -/
lemma isFormalAdjointₛₗ_iff_isFormalAdjoint {T : E →ₗ.[ℂ] F} {S : F →ₗ.[ℂ] E} :
    T.IsFormalAdjointₛₗ S ↔ T.IsFormalAdjoint S :=
  forall₂_congr fun _ _ => by rw [RingHom.id_apply]

/-- The domain `{y | x ↦ ⟪y, T x⟫ is continuous on dom T}` of the adjoint of a semilinear
partially defined map.

This is an auxiliary definition; the preferred spelling is `T.adjointₛₗ.domain`. -/
def adjointDomainₛₗ : Submodule ℂ F where
  carrier := {y | Continuous fun x : T.domain => ⟪y, T x⟫_ℂ}
  zero_mem' := by
    change Continuous fun x : T.domain => ⟪(0 : F), T x⟫_ℂ
    simp_rw [inner_zero_left]
    exact continuous_const
  add_mem' {y y'} hy hy' := by
    change Continuous fun x : T.domain => ⟪y + y', T x⟫_ℂ
    simp_rw [inner_add_left]
    exact Continuous.add hy hy'
  smul_mem' c y hy := by
    change Continuous fun x : T.domain => ⟪c • y, T x⟫_ℂ
    simp_rw [inner_smul_left]
    exact continuous_const.mul hy

/-- The functional `x ↦ σ' ⟪y, T x⟫` on `dom T`, continuous for `y` in the adjoint domain. -/
noncomputable def adjointDomainMkCLMₛₗ (y : T.adjointDomainₛₗ) : StrongDual ℂ T.domain where
  toFun x := σ' ⟪(y : F), T x⟫_ℂ
  map_add' x x' := by rw [T.map_add, inner_add_right, _root_.map_add σ']
  map_smul' c x := by
    rw [T.map_smulₛₗ, inner_smul_right, map_mul, RingHomInvPair.comp_apply_eq, RingHom.id_apply,
      smul_eq_mul]
  cont := (RingHom.continuous_of_ringHomInvPair σ).comp
    (y.2 : Continuous fun x : T.domain => ⟪(y : F), T x⟫_ℂ)

/-- The unique continuous extension of `adjointDomainMkCLMₛₗ` to `E`. -/
noncomputable def adjointDomainMkCLMExtendₛₗ (y : T.adjointDomainₛₗ) : StrongDual ℂ E :=
  (T.adjointDomainMkCLMₛₗ (σ' := σ') y).extend (Submodule.subtypeL T.domain)

variable {T}

/-- The extension agrees with `x ↦ σ' ⟪y, T x⟫` on `dom T`. -/
lemma adjointDomainMkCLMExtendₛₗ_apply (hT : Dense (T.domain : Set E)) (y : T.adjointDomainₛₗ)
    (x : T.domain) : T.adjointDomainMkCLMExtendₛₗ (σ' := σ') y (x : E) = σ' ⟪(y : F), T x⟫_ℂ :=
  ContinuousLinearMap.extend_eq _ hT.denseRange_val isUniformEmbedding_subtype_val.isUniformInducing _

variable [CompleteSpace E]

/-- The adjoint as a semilinear map from its domain to `E`, for a densely defined `T`.

This is an auxiliary definition needed to define the adjoint as a partially defined map without
the assumption that `T` is densely defined. -/
noncomputable def adjointAuxₛₗ (hT : Dense (T.domain : Set E)) : T.adjointDomainₛₗ →ₛₗ[σ'] E where
  toFun y := (InnerProductSpace.toDual ℂ E).symm (T.adjointDomainMkCLMExtendₛₗ y)
  map_add' y y' := hT.eq_of_inner_left ℂ fun z hz => by
    simp only [InnerProductSpace.toDual_symm_apply, inner_add_left,
      adjointDomainMkCLMExtendₛₗ_apply hT _ ⟨z, hz⟩, Submodule.coe_add]
    exact _root_.map_add σ' _ _
  map_smul' c y := hT.eq_of_inner_left ℂ fun z hz => by
    simp only [InnerProductSpace.toDual_symm_apply, inner_smul_left,
      adjointDomainMkCLMExtendₛₗ_apply hT _ ⟨z, hz⟩, Submodule.coe_smul]
    rw [map_mul σ', RingHom.apply_conj_of_ringHomInvPair σ]

/-- `⟪T† y, x⟫ = σ' ⟪y, T x⟫` for the auxiliary adjoint. -/
lemma adjointAuxₛₗ_inner (hT : Dense (T.domain : Set E)) (y : T.adjointDomainₛₗ) (x : T.domain) :
    ⟪adjointAuxₛₗ (σ' := σ') hT y, x⟫_ℂ = σ' ⟪(y : F), T x⟫_ℂ := by
  simp [adjointAuxₛₗ, adjointDomainMkCLMExtendₛₗ_apply hT]

variable (T)

open scoped Classical in
/-- The **adjoint** `T†` of a `σ`-semilinear partially defined map `T : E → F` between complex
Hilbert spaces, for an isometric `σ` (the identity or the conjugation) with inverse `σ'`: the
`σ'`-semilinear partially defined map with `⟪T† y, x⟫ = σ' ⟪y, T x⟫` for `x ∈ dom T`
(`LinearPMap.inner_adjointₛₗ_apply`), defined on the `y` for which `x ↦ ⟪y, T x⟫` is continuous.
For a conjugate-linear `T` this is the antilinear adjoint `⟪T† y, x⟫ = conj ⟪y, T x⟫`, so that
`T†T` is complex-linear (`LinearPMap.compNat`); for a complex-linear `T` it is Mathlib's
`LinearPMap.adjoint` (`LinearPMap.adjointₛₗ_eq_adjoint`). If `T` is not densely defined, the
values are `0`, as for Mathlib's adjoint. -/
noncomputable def adjointₛₗ : F →ₛₗ.[σ'] E where
  domain := T.adjointDomainₛₗ
  toFun := if hT : Dense (T.domain : Set E) then adjointAuxₛₗ hT else 0

/-- The domain of the adjoint: `y ∈ dom T†` iff `x ↦ ⟪y, T x⟫` is continuous on `dom T`. -/
lemma mem_adjointₛₗ_domain_iff (y : F) :
    y ∈ (T.adjointₛₗ (σ' := σ')).domain ↔ Continuous fun x : T.domain => ⟪y, T x⟫_ℂ :=
  Iff.rfl

variable {T}

/-- A vector `y` with `σ' ⟪y, T x⟫ = ⟪w, x⟫` for some `w` lies in the domain of the adjoint. -/
lemma mem_adjointₛₗ_domain_of_exists (y : F)
    (h : ∃ w : E, ∀ x : T.domain, ⟪w, (x : E)⟫_ℂ = σ' ⟪y, T x⟫_ℂ) :
    y ∈ (T.adjointₛₗ (σ' := σ')).domain := by
  obtain ⟨w, hw⟩ := h
  rw [mem_adjointₛₗ_domain_iff]
  have hσ : Continuous σ :=
    (AddMonoidHomClass.isometry_of_norm σ fun _ => RingHomIsometric.norm_map).continuous
  have h' : (fun x : T.domain => ⟪y, T x⟫_ℂ) = fun x : T.domain => σ ⟪w, (x : E)⟫_ℂ :=
    funext fun x => by rw [hw, RingHomInvPair.comp_apply_eq₂]
  rw [h']
  fun_prop

/-- The values of the adjoint of a densely defined map. -/
lemma adjointₛₗ_apply_of_dense (hT : Dense (T.domain : Set E)) (y : (T.adjointₛₗ (σ' := σ')).domain) :
    T.adjointₛₗ y = adjointAuxₛₗ hT y := by
  classical
  change (if hT : Dense (T.domain : Set E) then adjointAuxₛₗ hT else 0) y = _
  simp only [hT, dite_eq_left]

/-- The adjoint of a map that is not densely defined vanishes. -/
lemma adjointₛₗ_apply_of_not_dense (hT : ¬Dense (T.domain : Set E))
    (y : (T.adjointₛₗ (σ' := σ')).domain) : T.adjointₛₗ y = 0 := by
  classical
  change (if hT : Dense (T.domain : Set E) then adjointAuxₛₗ hT else 0) y = _
  simp only [hT, dite_false]
  rfl

/-- **The defining property of the adjoint**: `⟪T† y, x⟫ = σ' ⟪y, T x⟫` for `x ∈ dom T`. -/
lemma inner_adjointₛₗ_apply (hT : Dense (T.domain : Set E))
    (y : (T.adjointₛₗ (σ' := σ')).domain) (x : T.domain) :
    ⟪T.adjointₛₗ y, (x : E)⟫_ℂ = σ' ⟪(y : F), T x⟫_ℂ := by
  rw [adjointₛₗ_apply_of_dense hT]
  exact adjointAuxₛₗ_inner hT y x

/-- The adjoint is characterised by its inner products with the domain of `T`. -/
lemma adjointₛₗ_apply_eq (hT : Dense (T.domain : Set E)) (y : (T.adjointₛₗ (σ' := σ')).domain)
    {w : E} (hw : ∀ x : T.domain, ⟪w, (x : E)⟫_ℂ = σ' ⟪(y : F), T x⟫_ℂ) : T.adjointₛₗ y = w :=
  hT.eq_of_inner_left ℂ fun v hv =>
    (inner_adjointₛₗ_apply hT y ⟨v, hv⟩).trans (hw ⟨v, hv⟩).symm

/-- **The defining property of the adjoint**, as a formal adjoint: `⟪T† y, x⟫ = σ' ⟪y, T x⟫`. -/
lemma adjointₛₗ_isFormalAdjointₛₗ (hT : Dense (T.domain : Set E)) :
    (T.adjointₛₗ (σ' := σ')).IsFormalAdjointₛₗ T :=
  inner_adjointₛₗ_apply hT

/-- **The adjoint is maximal**: every formal adjoint `S` of `T` is contained in `T†`. -/
lemma IsFormalAdjointₛₗ.le_adjointₛₗ (hT : Dense (T.domain : Set E)) {S : F →ₛₗ.[σ'] E}
    (h : T.IsFormalAdjointₛₗ S) : S ≤ T.adjointₛₗ :=
  ⟨fun y hy => mem_adjointₛₗ_domain_of_exists y ⟨S ⟨y, hy⟩, fun x => h.symm ⟨y, hy⟩ x⟩,
    fun y _ hyz => (adjointₛₗ_apply_eq hT _ fun x => by rw [← hyz]; exact h.symm y x).symm⟩

omit [RingHomIsometric σ] in
/-- For a complex-linear map, `LinearPMap.adjointₛₗ` is Mathlib's `LinearPMap.adjoint`. -/
lemma adjointₛₗ_eq_adjoint (T : E →ₗ.[ℂ] F) : T.adjointₛₗ = T† := by
  have hdom : T.adjointₛₗ.domain = T†.domain := Submodule.ext fun y => by
    rw [mem_adjointₛₗ_domain_iff, mem_adjoint_domain_iff]
    rfl
  refine eq_of_le_of_domain_eq ⟨hdom.le, fun y y' hyy' => ?_⟩ hdom
  by_cases hT : Dense (T.domain : Set E)
  · refine (adjoint_apply_eq hT y' fun x => ?_).symm
    rw [← hyy', inner_adjointₛₗ_apply hT y x, RingHom.id_apply]
  · rw [adjoint_apply_of_not_dense hT, adjointₛₗ_apply_of_not_dense hT]

end LinearPMap
