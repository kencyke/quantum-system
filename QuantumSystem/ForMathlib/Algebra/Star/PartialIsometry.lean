/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent

/-!
# Partial isometries in a star semigroup

A **partial isometry** in a semigroup with involution is an element `v` with `v * v⋆ * v = v`.
Its *source projection* `v⋆ * v` and *range projection* `v * v⋆` are then star projections.
Over a C⋆-ring the converse also holds: if *either* `v⋆ * v` or `v * v⋆` is a star projection,
then `v` is a partial isometry, so being a partial isometry is equivalent to each projection
condition. This equivalence is the algebraic backbone of Murray–von Neumann comparison theory
for von Neumann algebras.

## Main definitions

* `IsPartialIsometry v` — `v * star v * v = v`.

## Main results

* `IsPartialIsometry.isStarProjection_star_mul_self` / `isStarProjection_mul_star_self` — the
  source and range projections `v⋆v`, `vv⋆` are star projections.
* `IsPartialIsometry.star` — the adjoint of a partial isometry is a partial isometry.
* `IsPartialIsometry.mul_source` — `v (v⋆ v) = v`; `IsStarProjection.mul_eq_left_of_mul_eq_right` —
  for star projections, `e f = f` implies `f e = f`.
* `isPartialIsometry_of_isStarProjection_star_mul_self` /
  `isPartialIsometry_of_isStarProjection_mul_star_self` — the C⋆-ring converse: a star projection
  source or range projection forces `v` to be a partial isometry.
* `isPartialIsometry_iff_isStarProjection_star_mul_self` /
  `isPartialIsometry_iff_isStarProjection_mul_star_self` — the resulting equivalences.
* `IsPartialIsometry.sourceRangeEquiv` — on a Hilbert space, the isometric equivalence
  `range (v⋆v) ≃ₗᵢ range (vv⋆)`, with inverse `v⋆` (`IsPartialIsometry.coe_sourceRangeEquiv_symm`).
* `exists_isPartialIsometry_mem_centralizer_of_norm_eq` — two linear maps `f, g` into a Hilbert
  space with `‖f e‖ = ‖g e‖` are related by a partial isometry, `v ∘ f = g`, with source
  projection onto `closure (range f)` and range projection onto `closure (range g)`; for every
  star-closed set `S` of operators intertwining `f` and `g` it can be taken in the centralizer of
  `S` (and is in fact the same operator for every `S`). This is the partial isometry
  of the polar decomposition `x = v |x|` (`f = |x|`, `g = x`), and the one carrying `a ξ ↦ a η` for
  two vectors with the same vector functional on an operator algebra (`f = (· ξ)`, `g = (· η)`).
-/

@[expose] public section

section Mul

variable {R : Type*} [Mul R] [Star R]

/-- An element `v` of a semigroup with involution is a **partial isometry** when `v * v⋆ * v = v`.
For operators on a Hilbert space this is the usual notion: `v` restricts to an isometry on the
orthogonal complement of its kernel. -/
def IsPartialIsometry (v : R) : Prop := v * star v * v = v

/-- Every star projection is a partial isometry (with itself as source and range). -/
lemma IsStarProjection.isPartialIsometry {p : R} (hp : IsStarProjection p) :
    IsPartialIsometry p := by
  unfold IsPartialIsometry
  rw [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq, hp.isIdempotentElem.eq]

end Mul

section Semigroup

variable {R : Type*} [Semigroup R] [StarMul R]

namespace IsPartialIsometry

/-- The source projection `v⋆ * v` of a partial isometry is a star projection. -/
lemma isStarProjection_star_mul_self {v : R} (h : IsPartialIsometry v) :
    IsStarProjection (star v * v) :=
  ⟨by calc (star v * v) * (star v * v) = star v * (v * star v * v) := by simp only [mul_assoc]
        _ = star v * v := by rw [h],
   IsSelfAdjoint.star_mul_self v⟩

/-- The range projection `v * v⋆` of a partial isometry is a star projection. -/
lemma isStarProjection_mul_star_self {v : R} (h : IsPartialIsometry v) :
    IsStarProjection (v * star v) :=
  ⟨by calc (v * star v) * (v * star v) = (v * star v * v) * star v := by simp only [mul_assoc]
        _ = v * star v := by rw [h],
   IsSelfAdjoint.mul_star_self v⟩

/-- The source projection of a partial isometry acts as a right identity: `v (v⋆ v) = v`. -/
lemma mul_source {v : R} (h : IsPartialIsometry v) : v * (star v * v) = v := by
  rw [← mul_assoc]; exact h

end IsPartialIsometry

/-- For star projections, the subprojection relation `e * f = f` is left/right symmetric. -/
lemma IsStarProjection.mul_eq_left_of_mul_eq_right {e f : R} (he : IsStarProjection e)
    (hf : IsStarProjection f) (h : e * f = f) : f * e = f := by
  have := congrArg star h
  rwa [star_mul, he.isSelfAdjoint.star_eq, hf.isSelfAdjoint.star_eq] at this

/-- The adjoint of a partial isometry is a partial isometry. -/
protected lemma IsPartialIsometry.star {v : R} (h : IsPartialIsometry v) :
    IsPartialIsometry (star v) := by
  unfold IsPartialIsometry at *
  rw [star_star]
  calc Star.star v * v * Star.star v = Star.star (v * Star.star v * v) := by
        rw [star_mul, star_mul, star_star, mul_assoc]
    _ = Star.star v := by rw [h]

end Semigroup

section CStarRing

variable {R : Type*} [NonUnitalNormedRing R] [StarRing R] [CStarRing R]

/-- The C⋆-ring converse to `IsPartialIsometry.isStarProjection_star_mul_self`: if the source
projection `v⋆ * v` is a star projection, then `v` is a partial isometry. With `a := v - v v⋆ v`
the idempotence of `v⋆ * v` gives `a⋆ * a = 0`, and the C⋆-identity `‖a‖² = ‖a⋆ a‖` forces
`a = 0`. -/
lemma isPartialIsometry_of_isStarProjection_star_mul_self {v : R}
    (h : IsStarProjection (star v * v)) : IsPartialIsometry v := by
  have hidem : star v * v * (star v * v) = star v * v := h.isIdempotentElem.eq
  have hstar : star (v * star v * v) = star v * v * star v := by
    rw [star_mul, star_mul, star_star, mul_assoc]
  have key : star (v - v * star v * v) * (v - v * star v * v) = 0 := by
    rw [star_sub, hstar]
    have expand : (star v - star v * v * star v) * (v - v * star v * v) =
        star v * v - star v * v * (star v * v) - star v * v * (star v * v) +
          star v * v * (star v * v) * (star v * v) := by
      simp only [mul_sub, sub_mul, mul_assoc]
      abel
    rw [expand]
    simp only [hidem]
    abel
  have hnorm : ‖v - v * star v * v‖ = 0 := by
    have hmul := CStarRing.norm_star_mul_self (x := v - v * star v * v)
    rw [key, norm_zero] at hmul
    exact mul_self_eq_zero.mp hmul.symm
  have hzero : v - v * star v * v = 0 := norm_eq_zero.mp hnorm
  exact (sub_eq_zero.mp hzero).symm

/-- The C⋆-ring converse to `IsPartialIsometry.isStarProjection_mul_star_self`: if the range
projection `v * v⋆` is a star projection, then `v` is a partial isometry. This is the source
statement applied to `v⋆`. -/
lemma isPartialIsometry_of_isStarProjection_mul_star_self {v : R}
    (h : IsStarProjection (v * star v)) : IsPartialIsometry v := by
  have h' : IsStarProjection (star (star v) * star v) := by rwa [star_star]
  have hv := IsPartialIsometry.star (isPartialIsometry_of_isStarProjection_star_mul_self h')
  rwa [star_star] at hv

/-- In a C⋆-ring, `v` is a partial isometry iff its source projection `v⋆ * v` is a star
projection. -/
lemma isPartialIsometry_iff_isStarProjection_star_mul_self {v : R} :
    IsPartialIsometry v ↔ IsStarProjection (star v * v) :=
  ⟨IsPartialIsometry.isStarProjection_star_mul_self,
    isPartialIsometry_of_isStarProjection_star_mul_self⟩

/-- In a C⋆-ring, `v` is a partial isometry iff its range projection `v * v⋆` is a star
projection. -/
lemma isPartialIsometry_iff_isStarProjection_mul_star_self {v : R} :
    IsPartialIsometry v ↔ IsStarProjection (v * star v) :=
  ⟨IsPartialIsometry.isStarProjection_mul_star_self,
    isPartialIsometry_of_isStarProjection_mul_star_self⟩

end CStarRing

section Hilbert

/-! ### Partial isometries on a Hilbert space

A partial isometry `v` of `B(H)` is isometric on its source subspace `range (v⋆v)` and restricts to
a linear isometric equivalence `range (v⋆v) ≃ₗᵢ range (vv⋆)`. -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The range of a star projection, a closed subspace, is complete. -/
lemma IsStarProjection.completeSpace_range {p : H →L[ℂ] H} (hp : IsStarProjection p) :
    CompleteSpace (p.range) :=
  (ContinuousLinearMap.IsIdempotentElem.isClosed_range hp.isIdempotentElem).completeSpace_coe

namespace IsPartialIsometry

/-- For `x` in the source subspace (`p x = x` where `p = v⋆v`), the map preserves the norm:
`‖v x‖ = ‖x‖`. -/
lemma norm_apply {v : H →L[ℂ] H} {p : H →L[ℂ] H}
    (hsource : star v * v = p) {x : H} (hx : (p : H →L[ℂ] H) x = x) : ‖v x‖ = ‖x‖ := by
  have hinner : (inner ℂ (v x) (v x) : ℂ) = inner ℂ x x := by
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
      ← mul_apply_eq_comp, hsource, hx]
  have h2 : ‖v x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ)]
    exact congrArg RCLike.re hinner
  have h3 := congrArg Real.sqrt h2
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h3

/-- The image of any vector under a partial isometry lands in the range subspace: if `q = v v⋆`
then `q (v x) = v x`. -/
lemma apply_mem_range {v : H →L[ℂ] H} (hv : IsPartialIsometry v) {q : H →L[ℂ] H}
    (hrange : v * star v = q) (x : H) : (q : H →L[ℂ] H) (v x) = v x := by
  rw [← mul_apply_eq_comp, ← hrange, hv]

/-- A partial isometry `v` with source projection `star v * v = p` and range projection
`v * star v = q` restricts to a linear isometric equivalence from the source subspace
`range p` onto the range subspace `range q`. -/
noncomputable def sourceRangeEquiv {v : H →L[ℂ] H} (hv : IsPartialIsometry v)
    {p q : H →L[ℂ] H} (hsource : star v * v = p) (hrange : v * star v = q) :
    p.range ≃ₗᵢ[ℂ] q.range := by
  have hpidem : (p : H →L[ℂ] H) * p = p := by
    have := hv.isStarProjection_star_mul_self.isIdempotentElem
    rwa [hsource] at this
  have hqidem : (q : H →L[ℂ] H) * q = q := by
    have := hv.isStarProjection_mul_star_self.isIdempotentElem
    rwa [hrange] at this
  have hsvpi : star v * v * star v = star v := by
    have h : star v * star (star v) * star v = star v := IsPartialIsometry.star hv
    rwa [star_star] at h
  have hfix : ∀ {x : H}, x ∈ p.range → (p : H →L[ℂ] H) x = x := by
    rintro x ⟨z, rfl⟩
    rw [ContinuousLinearMap.coe_coe, ← mul_apply_eq_comp, hpidem]
  refine LinearIsometryEquiv.ofSurjective
    { toFun := fun ξ => ⟨v ξ.1, ⟨v ξ.1, by
        rw [ContinuousLinearMap.coe_coe]; exact hv.apply_mem_range hrange ξ.1⟩⟩
      map_add' := fun a b => by apply Subtype.ext; simp
      map_smul' := fun c a => by apply Subtype.ext; simp
      norm_map' := fun ξ => norm_apply hsource (hfix ξ.2) } ?_
  rintro ⟨η, hη⟩
  have hqfix : (q : H →L[ℂ] H) η = η := by
    obtain ⟨z, hz⟩ := hη
    rw [← hz, ContinuousLinearMap.coe_coe, ← mul_apply_eq_comp, hqidem]
  have hmem : star v η ∈ p.range := by
    refine ⟨star v η, ?_⟩
    rw [ContinuousLinearMap.coe_coe, show (p : H →L[ℂ] H) (star v η) = (p * star v) η from rfl,
      ← hsource, hsvpi]
  refine ⟨⟨star v η, hmem⟩, Subtype.ext ?_⟩
  change v (star v η) = η
  rw [← mul_apply_eq_comp, hrange, hqfix]

end IsPartialIsometry

/-- The inverse of the partial-isometry-induced equivalence acts as `v⋆`: for `η` in the range
subspace, `(sourceRangeEquiv v).symm η = v⋆ η`. -/
lemma IsPartialIsometry.coe_sourceRangeEquiv_symm {v : H →L[ℂ] H} (hv : IsPartialIsometry v)
    {p q : H →L[ℂ] H} (hsource : star v * v = p) (hrange : v * star v = q)
    (η : q.range) :
    ((hv.sourceRangeEquiv hsource hrange).symm η : H) = star v (η : H) := by
  have hsvpi : star v * v * star v = star v := by
    have h : star v * star (star v) * star v = star v := IsPartialIsometry.star hv
    rwa [star_star] at h
  have hq : IsStarProjection q := by rw [← hrange]; exact hv.isStarProjection_mul_star_self
  have hqfix : (q : H →L[ℂ] H) (η : H) = (η : H) := (LinearMap.IsIdempotentElem.mem_range_iff
    (ContinuousLinearMap.IsIdempotentElem.toLinearMap hq.isIdempotentElem)).mp η.2
  have hmem : star v (η : H) ∈ p.range :=
    ⟨star v (η : H), by
      rw [ContinuousLinearMap.coe_coe, ← hsource, ← mul_apply_eq_comp, hsvpi]⟩
  have hG : (hv.sourceRangeEquiv hsource hrange) ⟨star v (η : H), hmem⟩ = η := by
    apply Subtype.ext
    change v (star v (η : H)) = (η : H)
    rw [← mul_apply_eq_comp, hrange, hqfix]
  have hsymm : (hv.sourceRangeEquiv hsource hrange).symm η = ⟨star v (η : H), hmem⟩ :=
    (hv.sourceRangeEquiv hsource hrange).injective (by
      rw [LinearIsometryEquiv.apply_symm_apply]; exact hG.symm)
  rw [hsymm]

end Hilbert

section Extension

/-! ### Partial isometries extending an isometric correspondence

Two linear maps `f g : E →ₗ[ℂ] H` with `‖f e‖ = ‖g e‖` for every `e` define an isometry
`f e ↦ g e` from `range f` onto `range g`. It extends by continuity to `closure (range f)`
(`LinearMap.extendOfIsometry`) and by `0` to its orthogonal complement; the result is a partial
isometry `v` with `v ∘ f = g`. An operator `s` such that both `s` and `s⋆` intertwine the
correspondence, `s (f e) = f e'` and `s (g e) = g e'`, commutes with `v`: on `closure (range f)`
by density, and on its orthogonal complement, which `s` preserves, both `s v` and `v s` vanish. -/

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- **Partial isometry extending an isometric correspondence.** Let `f g : E →ₗ[ℂ] H` satisfy
`‖f e‖ = ‖g e‖` for every `e`, and let `S` be a star-closed set of operators intertwining the
correspondence: for `s ∈ S` and every `e`, some `e'` has `s (f e) = f e'` and `s (g e) = g e'`
(with `S = ∅` this is no constraint). Then there is a partial isometry `v` in the centralizer of
`S` with `v (f e) = g e`, source projection `v⋆ v` onto `closure (range f)` and range projection
`v v⋆` onto `closure (range g)`.

The statement is `∀ S, ∃ v`, but `v` does not depend on `S`: an operator with `v (f e) = g e` and
source projection onto `closure (range f)` is determined on `closure (range f)` by continuity and
vanishes on its orthogonal complement. For the polar decomposition (`f = |x|`, `g = x`) this
uniqueness is `ContinuousLinearMap.eq_of_eq_mul_cfcAbs`. -/
lemma exists_isPartialIsometry_mem_centralizer_of_norm_eq (f g : E →ₗ[ℂ] H)
    (h : ∀ e, ‖f e‖ = ‖g e‖) {S : Set (H →L[ℂ] H)} (hS : ∀ s ∈ S, star s ∈ S)
    (hfg : ∀ s ∈ S, ∀ e, ∃ e', s (f e) = f e' ∧ s (g e) = g e') :
    ∃ v ∈ S.centralizer, IsPartialIsometry v ∧ (∀ e, v (f e) = g e) ∧
      star v * v = (LinearMap.range f).topologicalClosure.starProjection ∧
      v * star v = (LinearMap.range g).topologicalClosure.starProjection := by
  set K := (LinearMap.range f).topologicalClosure
  set L := (LinearMap.range g).topologicalClosure
  -- `f` as a map into `K`, with dense range.
  let f' : E →ₗ[ℂ] K :=
    f.codRestrict K fun e => Submodule.le_topologicalClosure _ (LinearMap.mem_range_self f e)
  have hf' : DenseRange f' := by
    rw [DenseRange, Subtype.dense_iff]
    intro w hw
    rw [Submodule.topologicalClosure_coe] at hw
    refine closure_mono ?_ hw
    rintro _ ⟨e, rfl⟩
    exact ⟨_, ⟨e, rfl⟩, rfl⟩
  -- The isometry `K → H` extending `f e ↦ g e`, extended by `0` on `Kᗮ`.
  let U : K →ₗᵢ[ℂ] H := g.extendOfIsometry hf' fun e => (h e).symm
  set V : H →L[ℂ] H := U.toContinuousLinearMap ∘L K.orthogonalProjectionOnto
  have hVapp : ∀ w, V w = U (K.orthogonalProjectionOnto w) := fun _ => rfl
  -- `V` factors through `P_K`.
  have hVP : ∀ w, V w = V (K.starProjection w) := fun w => by
    rw [hVapp, hVapp, Submodule.starProjection_apply,
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  have hVf : ∀ e, V (f e) = g e := fun e => by
    rw [hVapp, show K.orthogonalProjectionOnto (f e) = f' e from
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (f' e)]
    exact LinearMap.extendOfIsometry_eq _ _ _ _
  have hnorm : ∀ w, ‖V w‖ = ‖K.starProjection w‖ := fun w => by
    rw [hVapp, LinearIsometry.norm_map]
    rfl
  -- Source projection: `V⋆ V = P_K`.
  have hstar : star V * V = K.starProjection := by
    refine ContinuousLinearMap.coe_inj.mp ((ext_inner_map _ _).mp fun w => ?_)
    change ⟪star V (V w), w⟫_ℂ = ⟪K.starProjection w, w⟫_ℂ
    have hw : ⟪K.starProjection w, w - K.starProjection w⟫_ℂ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (K.starProjection_apply_mem w)
        (K.sub_starProjection_mem_orthogonal w)
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left,
      inner_self_eq_norm_sq_to_K, hnorm, ← inner_self_eq_norm_sq_to_K, inner_sub_right,
      sub_eq_zero] at *
    exact hw.symm
  have hVV : V * (star V * V) = V := by
    rw [hstar]
    ext w
    exact (hVP w).symm
  -- `V` maps into `L`.
  have hrange : ∀ w, V w ∈ L := fun w => by
    rw [hVP]
    have hle : K ≤ L.comap (V : H →ₗ[ℂ] H) := by
      refine Submodule.topologicalClosure_minimal _ ?_ (by
        rw [Submodule.comap_coe]
        exact (LinearMap.range g).isClosed_topologicalClosure.preimage V.continuous)
      rintro _ ⟨e, rfl⟩
      simp only [Submodule.mem_comap, ContinuousLinearMap.coe_coe]
      rw [hVf]
      exact Submodule.le_topologicalClosure _ (LinearMap.mem_range_self g e)
    exact hle (K.starProjection_apply_mem w)
  -- Range projection: `V V⋆ = P_L`.
  have hfin : V * star V = L.starProjection := by
    have h₁ : ∀ u ∈ L, (V * star V) u = u := fun u hu => by
      have hle : L ≤ LinearMap.ker ((V * star V - 1 : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
        refine Submodule.topologicalClosure_minimal _ ?_ (V * star V - 1).isClosed_ker
        rintro _ ⟨e, rfl⟩
        simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
          sub_apply, one_apply_eq_self, sub_eq_zero]
        rw [← hVf, ← mul_apply_eq_comp, mul_assoc, hVV]
      simpa [sub_eq_zero] using hle hu
    have h₂ : ∀ u ∈ Lᗮ, star V u = 0 := fun u hu => by
      refine ext_inner_right ℂ fun w => ?_
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left,
        inner_zero_left]
      exact Submodule.inner_left_of_mem_orthogonal (hrange w) hu
    ext w
    conv_lhs => rw [← add_sub_cancel (L.starProjection w) w]
    rw [map_add, h₁ _ (L.starProjection_apply_mem w), mul_apply_eq_comp,
      h₂ _ (L.sub_starProjection_mem_orthogonal w), map_zero, add_zero]
  -- `V` commutes with every `s ∈ S`.
  have hcomm : V ∈ S.centralizer := by
    rw [Set.mem_centralizer_iff]
    intro s hs
    -- On `K`, by density.
    have hK : K ≤ LinearMap.ker ((s * V - V * s : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
      refine Submodule.topologicalClosure_minimal _ ?_ (s * V - V * s).isClosed_ker
      rintro _ ⟨e, rfl⟩
      obtain ⟨e', hfe, hge⟩ := hfg s hs e
      simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, sub_apply,
        mul_apply_eq_comp, sub_eq_zero]
      rw [hVf, hge, hfe, hVf]
    -- `s` preserves `Kᗮ`, because `s⋆` preserves `K`.
    have hsK : K ≤ K.comap ((star s : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
      refine Submodule.topologicalClosure_minimal _ ?_ (by
        rw [Submodule.comap_coe]
        exact (LinearMap.range f).isClosed_topologicalClosure.preimage (star s).continuous)
      rintro _ ⟨e, rfl⟩
      obtain ⟨e', hfe, -⟩ := hfg (star s) (hS s hs) e
      simp only [Submodule.mem_comap, ContinuousLinearMap.coe_coe]
      rw [hfe]
      exact Submodule.le_topologicalClosure _ (LinearMap.mem_range_self f e')
    have hsperp : ∀ u ∈ Kᗮ, s u ∈ Kᗮ := fun u hu => by
      refine (Submodule.mem_orthogonal _ _).mpr fun k hk => ?_
      have hk' : star s k ∈ K := hsK hk
      rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint]
      exact Submodule.inner_right_of_mem_orthogonal hk' hu
    have hV0 : ∀ u ∈ Kᗮ, V u = 0 := fun u hu => by
      rw [hVP, K.starProjection_apply_eq_zero_iff.mpr hu, map_zero]
    ext w
    have h₁ := hK (K.starProjection_apply_mem w)
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, sub_apply,
      mul_apply_eq_comp, sub_eq_zero] at h₁
    have h₂ := hsperp _ (K.sub_starProjection_mem_orthogonal w)
    change s (V w) = V (s w)
    calc s (V w) = V (s (K.starProjection w)) + V (s (w - K.starProjection w)) := by
          rw [hVP w, h₁, hV0 _ h₂, add_zero]
      _ = V (s w) := by rw [← map_add, ← map_add, add_sub_cancel]
  refine ⟨V, hcomm, ?_, hVf, hstar, hfin⟩
  rw [IsPartialIsometry, mul_assoc, hVV]

end Extension
