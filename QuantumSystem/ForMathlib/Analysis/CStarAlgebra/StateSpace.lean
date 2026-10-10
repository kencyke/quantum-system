/-
Copyright (c) 2025 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional

/-!
# The quasi-state space and the state space

The quasi-state space of a C\*-algebra `A` is the set of positive continuous linear functionals of
norm at most one, as a subset of the weak-\* dual.  A functional is *positive* when it sends the
positive cone to nonnegative numbers, `0 ≤ a → 0 ≤ φ a` — the defining condition of Mathlib's
positive linear maps `A →ₚ[ℂ] ℂ` (`PositiveLinearMap.mk₀`).  As in Mathlib, the order on `A` is a
type-class parameter; for a C\*-algebra with no preferred order, `CStarAlgebra.spectralOrder` can
be installed locally.  The quasi-state space is convex and
weak-\* compact (Banach–Alaoglu), which is what the Krein–Milman argument for pure states needs.

The **state space** `StateSpace A` is the subset of positive functionals of norm exactly one
(Bratteli–Robinson, §2.3.2). It is convex (`StateSpace.convex`): along an increasing approximate
unit `e`, a positive functional `φ` has `φ e → ‖φ‖` (`PositiveContinuousLinearMap.tendsto_nhds_opNorm`),
so `(sφ + tψ)(e) → s + t = 1` gives the norm of a convex combination, also for non-unital `A`.

## Main definitions

* `QuasiStateSpace A` — the positive functionals of norm at most one.
* `StateSpace A` — the positive functionals of norm one.

## Main results

* `QuasiStateSpace.convex`, `QuasiStateSpace.compact` — the quasi-state space is convex and
  weak-\* compact.
* `StateSpace.convex` — the state space is convex.
* `StateSpace.tendsto_approximateUnit` — `φ e → 1` along an increasing approximate unit.

## TODO

On a unital `A`, the state space is the set of positive functionals with `φ 1 = 1`, hence weak-\*
closed and compact; on a non-unital `A` it is in general not weak-\* closed. Add these when a
result needs them.
-/

@[expose] public section

open scoped ComplexOrder Topology
open Filter

section QuasiStateSpace

variable (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A]

/-- The quasi-state space of a C\*-algebra `A`: the positive continuous linear functionals
(`0 ≤ a → 0 ≤ φ a`) with norm at most `1`. -/
def QuasiStateSpace : Set (WeakDual ℂ A) :=
  { φ | ∀ a : A, 0 ≤ a → 0 ≤ φ a } ∩ (WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 1)

namespace QuasiStateSpace

/-- The quasi-state space is convex: positivity and the bound `‖φ‖ ≤ 1` are both preserved by
convex combinations. -/
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

/-- The quasi-state space is weak-\* compact: it is a weak-\* closed subset of the closed unit
ball, which is weak-\* compact by the Banach–Alaoglu theorem. -/
lemma compact : IsCompact (QuasiStateSpace A) := by
  rw [QuasiStateSpace, Set.inter_comm]
  exact (WeakDual.isCompact_closedBall (0 : StrongDual ℂ A) 1).inter_right
    (isClosed_setOf_nonneg A)

/-- The zero functional lies in the quasi-state space; in particular it is nonempty. -/
lemma non_empty : (0 : WeakDual ℂ A) ∈ QuasiStateSpace A := by
  constructor
  · intro a _
    exact le_rfl
  · simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
    norm_num

end QuasiStateSpace

end QuasiStateSpace

section StateSpace

variable (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A]

/-- The **state space** of a C\*-algebra `A`: the positive continuous linear functionals
(`0 ≤ a → 0 ≤ φ a`) with norm exactly `1` (Bratteli–Robinson, §2.3.2). -/
def StateSpace : Set (WeakDual ℂ A) :=
  { φ | ∀ a : A, 0 ≤ a → 0 ≤ φ a } ∩ (WeakDual.toStrongDual ⁻¹' Metric.sphere 0 1)

variable {A}

/-- `φ` is in the state space iff it is positive and of norm one. -/
lemma mem_stateSpace_iff {φ : WeakDual ℂ A} :
    φ ∈ StateSpace A ↔ (∀ a : A, 0 ≤ a → 0 ≤ φ a) ∧ ‖WeakDual.toStrongDual φ‖ = 1 := by
  simp [StateSpace]

namespace StateSpace

/-- Every state is a quasi-state. -/
lemma subset_quasiStateSpace : StateSpace A ⊆ QuasiStateSpace A :=
  fun _ hφ => ⟨hφ.1, Metric.sphere_subset_closedBall (α := StrongDual ℂ A) hφ.2⟩

variable [StarOrderedRing A]

/-- A state evaluated along an increasing approximate unit converges to `1`: `φ e → ‖φ‖ = 1`
(`PositiveContinuousLinearMap.tendsto_nhds_opNorm`). -/
lemma tendsto_approximateUnit {φ : WeakDual ℂ A} (hφ : φ ∈ StateSpace A) {l : Filter A}
    (hl : l.IsIncreasingApproximateUnit) : Tendsto (fun e : A => φ e) l (𝓝 1) := by
  have h : Tendsto (fun e : A => φ e) l (𝓝 (‖WeakDual.toStrongDual φ‖ : ℂ)) :=
    (PositiveContinuousLinearMap.mk₀ (WeakDual.toStrongDual φ) hφ.1).tendsto_nhds_opNorm hl
  rwa [(mem_stateSpace_iff.mp hφ).2, Complex.ofReal_one] at h

/-- **The state space is convex.** Along an increasing approximate unit `e`,
`(sφ + tψ)(e) → s + t = 1`, and the limit is the norm of the positive functional `sφ + tψ`; the
algebra need not be unital. -/
lemma convex : Convex ℝ (StateSpace A) := by
  intro φ hφ ψ hψ s t hs ht hst
  have hpos : ∀ a : A, 0 ≤ a → 0 ≤ (s • φ + t • ψ) a := fun a ha => by
    change 0 ≤ (s : ℂ) * φ a + (t : ℂ) * ψ a
    exact add_nonneg (mul_nonneg (Complex.zero_le_real.mpr hs) (hφ.1 a ha))
      (mul_nonneg (Complex.zero_le_real.mpr ht) (hψ.1 a ha))
  refine mem_stateSpace_iff.mpr ⟨hpos, ?_⟩
  have hl := CStarAlgebra.increasingApproximateUnit A
  have h1 : Tendsto (fun e : A => (s • φ + t • ψ) e) (CStarAlgebra.approximateUnit A)
      (𝓝 (‖WeakDual.toStrongDual (s • φ + t • ψ)‖ : ℂ)) :=
    (PositiveContinuousLinearMap.mk₀ (WeakDual.toStrongDual (s • φ + t • ψ)) hpos
      ).tendsto_nhds_opNorm hl
  have h2 : Tendsto (fun e : A => (s • φ + t • ψ) e) (CStarAlgebra.approximateUnit A) (𝓝 1) := by
    have h := ((tendsto_approximateUnit hφ hl).const_mul (s : ℂ)).add
      ((tendsto_approximateUnit hψ hl).const_mul (t : ℂ))
    rw [mul_one, mul_one, ← Complex.ofReal_add, hst, Complex.ofReal_one] at h
    exact h
  exact_mod_cast tendsto_nhds_unique h1 h2

end StateSpace

end StateSpace
