module

public import Mathlib.Algebra.Order.Star.Basic

/-!
# Positivity tested on `a* a`

In a star-ordered ring the positive cone is the closure of the elements `a* a` under addition
(`StarOrderedRing.nonneg_iff`).  Hence an additive map is positive as soon as it is nonnegative on
every `a* a`; this is the usual way positivity of a functional on a C\*-algebra is checked.
-/

@[expose] public section

namespace StarOrderedRing

variable {F A E : Type*} [NonUnitalSemiring A] [PartialOrder A] [StarRing A] [StarOrderedRing A]
  [AddCommMonoid E] [PartialOrder E] [IsOrderedAddMonoid E] [FunLike F A E]
  [AddMonoidHomClass F A E]

/-- An additive map that is nonnegative on every `a* a` is nonnegative on every positive element. -/
theorem map_nonneg_of_star_mul_self_nonneg (f : F) (hf : ∀ a, 0 ≤ f (star a * a)) {a : A}
    (ha : 0 ≤ a) : 0 ≤ f a := by
  rw [StarOrderedRing.nonneg_iff] at ha
  induction ha using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    exact hf s
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using add_nonneg hx hy

end StarOrderedRing
