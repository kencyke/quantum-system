module

public import QuantumSystem.Algebra.CStarAlgebra.State

@[expose] public section

namespace State

variable {𝕜 : Type*} [RCLike 𝕜]
variable {A : Type*} [NonUnitalCStarAlgebra A] [Module 𝕜 A]

/-- A state ω on a C*-algebra A is faithful if ω(a*a) = 0 implies a = 0.

This is equivalent to saying the GNS kernel Nω is trivial, i.e., the GNS representation
is injective. -/
def IsFaithful (ω : State 𝕜 A) : Prop :=
  ∀ a : A, ω (star a * a) = 0 → a = 0

/-- Alternative characterization: a state is faithful iff a*a is not in the kernel
unless a = 0. -/
lemma isFaithful_iff (ω : State 𝕜 A) :
    ω.IsFaithful ↔ ∀ a : A, a ≠ 0 → ω (star a * a) ≠ 0 := by
  constructor
  · intro hf a ha h0
    exact ha (hf a h0)
  · intro h a h0
    by_contra ha
    exact h a ha h0

/-- Faithful states are positive definite on positive elements. -/
lemma IsFaithful.pos_of_nonzero {ω : State ℂ A} (hω : ω.IsFaithful) {a : A} (ha : a ≠ 0) :
    0 < (ω (star a * a)).re := by
  obtain ⟨r, hr⟩ := ω.positive a
  have hr' : ω (star a * a) = (r : ℂ) := by
    simpa [State.toLinearMap_apply] using hr
  rw [hr']
  simp only [Complex.ofReal_re]
  by_contra h_not_pos
  push_neg at h_not_pos
  have hr_nonneg : (0 : ℝ) ≤ r := r.property
  have hr_zero : (r : ℝ) = 0 := le_antisymm h_not_pos hr_nonneg
  have h0 : ω (star a * a) = 0 := by rw [hr', hr_zero]; simp
  exact ha (hω a h0)

end State
