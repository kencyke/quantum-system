module

public import QuantumSystem.Algebra.CStarAlgebra.State

/-!
# Faithful states

A state `ω` is *faithful* if `ω (a* a) = 0` forces `a = 0`.  Equivalently the GNS vector map
`a ↦ [a]` is injective (`State.isFaithful_iff_injective_gnsMk`).
-/

@[expose] public section

namespace State

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A state `ω` on a C\*-algebra `A` is faithful if `ω (a* a) = 0` implies `a = 0`. -/
def IsFaithful (ω : State A) : Prop :=
  ∀ a : A, ω (star a * a) = 0 → a = 0

/-- A state is faithful iff `ω (a* a) ≠ 0` for every `a ≠ 0`. -/
lemma isFaithful_iff (ω : State A) :
    ω.IsFaithful ↔ ∀ a : A, a ≠ 0 → ω (star a * a) ≠ 0 :=
  forall_congr' fun _ => not_imp_not.symm

/-- A faithful state is strictly positive on every `a* a` with `a ≠ 0`. -/
lemma IsFaithful.pos_of_nonzero {ω : State A} (hω : ω.IsFaithful) {a : A} (ha : a ≠ 0) :
    0 < (ω (star a * a)).re := by
  refine (ω.re_apply_star_mul_self_nonneg a).lt_of_ne fun h => ha (hω a ?_)
  rw [← ω.ofReal_re_apply_star_mul_self, ← h, Complex.ofReal_zero]

end State
