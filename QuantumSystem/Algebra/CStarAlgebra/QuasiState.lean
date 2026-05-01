module

public import Mathlib.Analysis.Normed.Module.WeakDual
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.WeakDual

@[expose] public section


section QuasiStateSpace

variable (A : Type*) [NonUnitalCStarAlgebra A]

/-- The quasi-state space of a C*-algebra A, defined as the set of all positive continuous linear functionals
with norm at most 1. -/
def QuasiStateSpace : Set (WeakDual ℂ A) :=
  { φ | IsPositive A φ } ∩ (WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 1)

namespace QuasiStateSpace

lemma convex : Convex ℝ (QuasiStateSpace A) := by
  apply Convex.inter
  · -- Positivity is convex
    intro x hx y hy a b ha hb hab
    apply IsPositive.add
    · convert IsPositive.smul A hx (c := ⟨a, ha⟩)
    · convert IsPositive.smul A hy (c := ⟨b, hb⟩)
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

lemma compact : IsCompact (QuasiStateSpace A) := by
  rw [QuasiStateSpace, Set.inter_comm]
  apply IsCompact.inter_right
  · exact WeakDual.isCompact_closedBall (0 : StrongDual ℂ A) 1
  · exact IsPositive.isClosed A

lemma non_empty : (0 : WeakDual ℂ A) ∈ QuasiStateSpace A := by
  constructor
  · exact IsPositive.zero A
  · simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
    norm_num

end QuasiStateSpace

end QuasiStateSpace
