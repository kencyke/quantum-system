module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Algebra.Star.StarProjection

/-!
# Every idempotent in a C\*-algebra is similar to a projection

In a unital C\*-algebra `A`, an idempotent `e` (`e * e = e`, not necessarily
self-adjoint) is *similar* to a genuine **projection** (a self-adjoint idempotent)
with the same range.  The projection is

```
p = e e⋆ z⁻¹,   z = 1 + (e - e⋆)⋆ (e - e⋆) = 1 - (e - e⋆)²,
```

where `z ≥ 1` is positive and invertible and commutes with `e`.  It satisfies
`p * e = e` and `e * p = p`, exhibiting `e` and `p` as having the same range.

This is the standard C\*-algebra fact used to reduce the splitting of a general
(non-self-adjoint) idempotent to that of a self-adjoint projection — the analytic
input of the Doplicher–Roberts subobject theory.

## References

* Blackadar, *Operator Algebras*, II.3.2.
* Wegge-Olsen, *K-theory and C\*-algebras*, §3 (idempotents vs. projections).
-/

@[expose] public section

namespace CStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
/-- An element commuting with a unit commutes with its inverse. -/
private lemma commute_ringInverse {b : A} (x : A) (hb : IsUnit b) (h : x * b = b * x) :
    x * Ring.inverse b = Ring.inverse b * x := by
  have hbi : b * Ring.inverse b = 1 := Ring.mul_inverse_cancel b hb
  have hib : Ring.inverse b * b = 1 := Ring.inverse_mul_cancel b hb
  calc x * Ring.inverse b
      = Ring.inverse b * (b * x) * Ring.inverse b := by
        rw [show Ring.inverse b * (b * x) * Ring.inverse b
              = (Ring.inverse b * b) * (x * Ring.inverse b) from by noncomm_ring, hib, one_mul]
    _ = Ring.inverse b * (x * b) * Ring.inverse b := by rw [← h]
    _ = Ring.inverse b * x := by
        rw [show Ring.inverse b * (x * b) * Ring.inverse b
              = (Ring.inverse b * x) * (b * Ring.inverse b) from by noncomm_ring, hbi, mul_one]

/-- **An idempotent in a C\*-algebra is similar to a projection.**  For an
idempotent `e` (`e * e = e`) there is a star projection `p` (a self-adjoint
idempotent) with `p * e = e` and `e * p = p`, i.e. with the same range.
Concretely `p = e e⋆ z⁻¹` with `z = 1 + (e - e⋆)⋆ (e - e⋆)` positive and
invertible; the final clause records that `p` commutes with everything commuting
with both `e` and `e⋆` (so `p` inherits any intertwining property of `e`). -/
theorem exists_isStarProjection_similar_of_isIdempotentElem {e : A}
    (he : IsIdempotentElem e) :
    ∃ p : A, IsStarProjection p ∧ p * e = e ∧ e * p = p ∧
      ∀ x : A, x * e = e * x → x * star e = star e * x → x * p = p * x := by
  have hee : e * e = e := he
  have hss : star e * star e = star e := by
    have h := congrArg star hee; rwa [star_mul] at h
  -- the skew-adjoint difference `w = e - e⋆`
  set w : A := e - star e with hw
  have hsw : star w = -w := by rw [hw, star_sub, star_star]; noncomm_ring
  have hw2 : w * w = e - e * star e - star e * e + star e := by
    rw [hw,
      show (e - star e) * (e - star e)
          = e * e - e * star e - star e * e + star e * star e from by noncomm_ring,
      hee, hss]
  clear_value w
  -- the positive invertible element `z`
  set z : A := 1 + star w * w with hz
  have hzu : IsUnit z :=
    CStarAlgebra.isUnit_of_le 1 (le_add_of_nonneg_right (star_mul_self_nonneg w))
      isStrictlyPositive_one
  have hzsa : star z = z := by rw [hz, star_add, star_one, star_mul, star_star]
  have hzww : z = 1 - w * w := by rw [hz, hsw, neg_mul, ← sub_eq_add_neg]
  clear_value z
  -- `z` commutes with `e` and `star e`, and `z * e = e e⋆ e`
  have hwwe : w * w * e = e - e * star e * e := by
    rw [hw2,
      show (e - e * star e - star e * e + star e) * e
          = e * e - e * star e * e - star e * (e * e) + star e * e from by noncomm_ring, hee]
    abel
  have hewwe : e * (w * w) = e - e * star e * e := by
    rw [hw2,
      show e * (e - e * star e - star e * e + star e)
          = e * e - e * (e * star e) - e * (star e * e) + e * star e from by noncomm_ring, hee,
      show e * (e * star e) = e * star e from by rw [← mul_assoc, hee],
      show e * (star e * e) = e * star e * e from by rw [mul_assoc]]
    abel
  have hzefe : z * e = e * star e * e := by rw [hzww, sub_mul, one_mul, hwwe]; abel
  have hez : e * z = e * star e * e := by rw [hzww, mul_sub, mul_one, hewwe]; abel
  have hze : z * e = e * z := by rw [hzefe, hez]
  have hzse : z * star e = star e * z := by
    have h := congrArg star hze
    rw [star_mul, star_mul, hzsa] at h
    exact h.symm
  have hzf : z * (e * star e) = (e * star e) * z := by
    rw [← mul_assoc, hze, mul_assoc, hzse, ← mul_assoc]
  have hff : (e * star e) * (e * star e) = z * (e * star e) := by
    rw [show (e * star e) * (e * star e) = (e * star e * e) * star e from by noncomm_ring,
      ← hzefe, mul_assoc]
  -- the inverse and its commutations
  set zi : A := Ring.inverse z with hzi
  have hzzi : z * zi = 1 := Ring.mul_inverse_cancel z hzu
  have hziz : zi * z = 1 := Ring.inverse_mul_cancel z hzu
  have hzisa : star zi = zi := by rw [hzi, ← Ring.inverse_star, hzsa]
  clear_value zi
  have hzie : zi * e = e * zi := by
    have h1 : z * (e * zi) = e := by rw [← mul_assoc, hze, mul_assoc, hzzi, mul_one]
    calc zi * e = zi * (z * (e * zi)) := by rw [h1]
      _ = e * zi := by rw [← mul_assoc, hziz, one_mul]
  have hzif : zi * (e * star e) = (e * star e) * zi := by
    have h1 : z * ((e * star e) * zi) = e * star e := by
      rw [← mul_assoc, hzf, mul_assoc, hzzi, mul_one]
    calc zi * (e * star e) = zi * (z * ((e * star e) * zi)) := by rw [h1]
      _ = (e * star e) * zi := by rw [← mul_assoc, hziz, one_mul]
  have hzfzi : z * (e * star e) * zi = e * star e := by
    rw [hzf, mul_assoc, hzzi, mul_one]
  -- abbreviate the projection's "numerator" `f = e e⋆`
  set f : A := e * star e with hf
  have hfsa : star f = f := by rw [hf, star_mul, star_star]
  have hef : e * f = f := by rw [hf, ← mul_assoc, hee]
  clear_value f
  refine ⟨f * zi, ?_, ?_, ?_, ?_⟩
  · rw [isStarProjection_iff]
    refine ⟨?_, ?_⟩
    · change (f * zi) * (f * zi) = f * zi
      rw [show (f * zi) * (f * zi) = f * (zi * f) * zi from by noncomm_ring, hzif,
        show f * (f * zi) * zi = (f * f) * (zi * zi) from by noncomm_ring, hff,
        show z * f * (zi * zi) = (z * f * zi) * zi from by noncomm_ring, hzfzi]
    · change star (f * zi) = f * zi
      rw [star_mul, hzisa, hfsa, hzif]
  · change (f * zi) * e = e
    rw [show (f * zi) * e = f * (zi * e) from by noncomm_ring, hzie,
      show f * (e * zi) = (f * e) * zi from by noncomm_ring, ← hzefe,
      show (z * e) * zi = z * (e * zi) from by noncomm_ring, ← hzie,
      show z * (zi * e) = (z * zi) * e from by noncomm_ring, hzzi, one_mul]
  · change e * (f * zi) = f * zi
    rw [show e * (f * zi) = (e * f) * zi from by noncomm_ring, hef]
  · -- `p = f * zi` commutes with anything commuting with `e` and `star e`
    intro x hxe hxse
    have hxf : x * f = f * x := by
      rw [hf, ← mul_assoc, hxe, mul_assoc, hxse, ← mul_assoc]
    have hxw : x * w = w * x := by rw [hw, mul_sub, sub_mul, hxe, hxse]
    have hxsw : x * star w = star w * x := by rw [hsw, mul_neg, neg_mul, hxw]
    have hxz : x * z = z * x := by
      rw [hz, mul_add, add_mul, mul_one, one_mul, ← mul_assoc, hxsw, mul_assoc, hxw, ← mul_assoc]
    have hxzi : x * zi = zi * x := by rw [hzi]; exact commute_ringInverse x hzu hxz
    rw [← mul_assoc, hxf, mul_assoc, hxzi, ← mul_assoc]

end CStarAlgebra
