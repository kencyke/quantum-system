/-
Copyright (c) 2025 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Analysis.CStarAlgebra.Classes

/-!
# The quasi-state space

The quasi-state space of a C\*-algebra `A` is the set of positive continuous linear functionals of
norm at most one, as a subset of the weak-\* dual.  A functional is *positive* when it sends the
positive cone to nonnegative numbers, `0 ≤ a → 0 ≤ φ a` — the defining condition of Mathlib's
positive linear maps `A →ₚ[ℂ] ℂ` (`PositiveLinearMap.mk₀`).  As in Mathlib, the order on `A` is a
type-class parameter; for a C\*-algebra with no preferred order, `CStarAlgebra.spectralOrder` can
be installed locally.  The quasi-state space is convex and
weak-\* compact, which is what the Krein–Milman argument for pure states needs.
-/

@[expose] public section

open scoped ComplexOrder

section QuasiStateSpace

variable (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A]

/-- The quasi-state space of a C\*-algebra `A`: the positive continuous linear functionals
(`0 ≤ a → 0 ≤ φ a`) with norm at most `1`. -/
def QuasiStateSpace : Set (WeakDual ℂ A) :=
  { φ | ∀ a : A, 0 ≤ a → 0 ≤ φ a } ∩ (WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 1)

namespace QuasiStateSpace

lemma convex : Convex ℝ (QuasiStateSpace A) := by
  apply Convex.inter
  · -- Positivity is preserved by convex combinations.
    intro x hx y hy s t hs ht _ a ha
    change 0 ≤ (s : ℂ) * x a + (t : ℂ) * y a
    exact add_nonneg (mul_nonneg (Complex.zero_le_real.mpr hs) (hx a ha))
      (mul_nonneg (Complex.zero_le_real.mpr ht) (hy a ha))
  · -- Unit ball is convex.  Use the real-linear identity from `WeakDual ℂ A` to
    -- `StrongDual ℂ A` to transport the convexity of the closed ball.
    let f : WeakDual ℂ A →ₗ[ℝ] StrongDual ℂ A :=
      { toFun := fun x => x
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have heq : (WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ A) 1) =
           f ⁻¹' Metric.closedBall (0 : StrongDual ℂ A) 1 := rfl
    rw [heq]
    exact (convex_closedBall (0 : StrongDual ℂ A) 1).linear_preimage f

/-- Positivity is a weak-\* closed condition. -/
lemma isClosed_setOf_nonneg : IsClosed { φ : WeakDual ℂ A | ∀ a : A, 0 ≤ a → 0 ≤ φ a } := by
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun a => isClosed_iInter fun _ =>
    isClosed_le continuous_const (WeakDual.eval_continuous a)

lemma compact : IsCompact (QuasiStateSpace A) := by
  rw [QuasiStateSpace, Set.inter_comm]
  exact (WeakDual.isCompact_closedBall (0 : StrongDual ℂ A) 1).inter_right
    (isClosed_setOf_nonneg A)

lemma non_empty : (0 : WeakDual ℂ A) ∈ QuasiStateSpace A := by
  constructor
  · intro a _
    exact le_rfl
  · simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
    norm_num

end QuasiStateSpace

end QuasiStateSpace
