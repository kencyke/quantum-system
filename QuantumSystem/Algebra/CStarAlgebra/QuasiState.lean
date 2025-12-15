import Mathlib.Analysis.Normed.Module.WeakDual
import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.WeakDual


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
  · -- Unit ball is convex
    let f : WeakDual ℂ A →ₗ[ℂ] StrongDual ℂ A :=
      { toFun := fun x => x
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have : (WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ A) 1) =
           f ⁻¹' Metric.closedBall (0 : StrongDual ℂ A) 1 := rfl
    rw [this]
    apply Convex.linear_preimage (convex_closedBall (0 : StrongDual ℂ A) 1) (f.restrictScalars ℝ)

lemma compact : IsCompact (QuasiStateSpace A) := by
  rw [QuasiStateSpace, Set.inter_comm]
  apply IsCompact.inter_right
  · exact WeakDual.isCompact_closedBall ℂ (0 : StrongDual ℂ A) 1
  · exact IsPositive.isClosed A

lemma non_empty : (0 : WeakDual ℂ A) ∈ QuasiStateSpace A := by
  constructor
  · exact IsPositive.zero A
  · simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
    norm_num

end QuasiStateSpace

end QuasiStateSpace
