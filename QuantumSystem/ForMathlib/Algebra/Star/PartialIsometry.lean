module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Analysis.CStarAlgebra.Basic

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
-/

@[expose] public section

section Mul

variable {R : Type*} [Mul R] [Star R]

/-- An element `v` of a semigroup with involution is a **partial isometry** when `v * v⋆ * v = v`.
For operators on a Hilbert space this is the usual notion: `v` restricts to an isometry on the
orthogonal complement of its kernel. -/
def IsPartialIsometry (v : R) : Prop := v * star v * v = v

/-- Every star projection is a partial isometry (with itself as source and range). -/
theorem IsStarProjection.isPartialIsometry {p : R} (hp : IsStarProjection p) :
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
