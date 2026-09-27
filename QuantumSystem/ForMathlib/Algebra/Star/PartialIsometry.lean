/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
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
* `isPartialIsometry_of_isStarProjection_star_mul_self` /
  `isPartialIsometry_of_isStarProjection_mul_star_self` — the C⋆-ring converse: a star projection
  source or range projection forces `v` to be a partial isometry.
* `isPartialIsometry_iff_isStarProjection_star_mul_self` /
  `isPartialIsometry_iff_isStarProjection_mul_star_self` — the resulting equivalences.
* `IsPartialIsometry.sourceRangeEquiv` — on a Hilbert space, the isometric equivalence
  `range (v⋆v) ≃ₗᵢ range (vv⋆)`, with inverse `v⋆` (`IsPartialIsometry.coe_sourceRangeEquiv_symm`).
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
theorem isStarProjection_star_mul_self {v : R} (h : IsPartialIsometry v) :
    IsStarProjection (star v * v) :=
  ⟨by calc (star v * v) * (star v * v) = star v * (v * star v * v) := by simp only [mul_assoc]
        _ = star v * v := by rw [h],
   IsSelfAdjoint.star_mul_self v⟩

/-- The range projection `v * v⋆` of a partial isometry is a star projection. -/
theorem isStarProjection_mul_star_self {v : R} (h : IsPartialIsometry v) :
    IsStarProjection (v * star v) :=
  ⟨by calc (v * star v) * (v * star v) = (v * star v * v) * star v := by simp only [mul_assoc]
        _ = v * star v := by rw [h],
   IsSelfAdjoint.mul_star_self v⟩

end IsPartialIsometry

/-- The adjoint of a partial isometry is a partial isometry. -/
protected theorem IsPartialIsometry.star {v : R} (h : IsPartialIsometry v) :
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
theorem isPartialIsometry_of_isStarProjection_star_mul_self {v : R}
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
theorem isPartialIsometry_of_isStarProjection_mul_star_self {v : R}
    (h : IsStarProjection (v * star v)) : IsPartialIsometry v := by
  have h' : IsStarProjection (star (star v) * star v) := by rwa [star_star]
  have hv := IsPartialIsometry.star (isPartialIsometry_of_isStarProjection_star_mul_self h')
  rwa [star_star] at hv

/-- In a C⋆-ring, `v` is a partial isometry iff its source projection `v⋆ * v` is a star
projection. -/
theorem isPartialIsometry_iff_isStarProjection_star_mul_self {v : R} :
    IsPartialIsometry v ↔ IsStarProjection (star v * v) :=
  ⟨IsPartialIsometry.isStarProjection_star_mul_self,
    isPartialIsometry_of_isStarProjection_star_mul_self⟩

/-- In a C⋆-ring, `v` is a partial isometry iff its range projection `v * v⋆` is a star
projection. -/
theorem isPartialIsometry_iff_isStarProjection_mul_star_self {v : R} :
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
    CompleteSpace (LinearMap.range (p : H →ₗ[ℂ] H)) :=
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
    LinearMap.range (p : H →ₗ[ℂ] H) ≃ₗᵢ[ℂ] LinearMap.range (q : H →ₗ[ℂ] H) := by
  have hpidem : (p : H →L[ℂ] H) * p = p := by
    have := hv.isStarProjection_star_mul_self.isIdempotentElem
    rwa [hsource] at this
  have hqidem : (q : H →L[ℂ] H) * q = q := by
    have := hv.isStarProjection_mul_star_self.isIdempotentElem
    rwa [hrange] at this
  have hsvpi : star v * v * star v = star v := by
    have h : star v * star (star v) * star v = star v := IsPartialIsometry.star hv
    rwa [star_star] at h
  have hfix : ∀ {x : H}, x ∈ LinearMap.range (p : H →ₗ[ℂ] H) → (p : H →L[ℂ] H) x = x := by
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
  have hmem : star v η ∈ LinearMap.range (p : H →ₗ[ℂ] H) := by
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
    (η : LinearMap.range (q : H →ₗ[ℂ] H)) :
    ((hv.sourceRangeEquiv hsource hrange).symm η : H) = star v (η : H) := by
  have hsvpi : star v * v * star v = star v := by
    have h : star v * star (star v) * star v = star v := IsPartialIsometry.star hv
    rwa [star_star] at h
  have hq : IsStarProjection q := by rw [← hrange]; exact hv.isStarProjection_mul_star_self
  have hqfix : (q : H →L[ℂ] H) (η : H) = (η : H) := (LinearMap.IsIdempotentElem.mem_range_iff
    (ContinuousLinearMap.IsIdempotentElem.toLinearMap hq.isIdempotentElem)).mp η.2
  have hmem : star v (η : H) ∈ LinearMap.range (p : H →ₗ[ℂ] H) :=
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
