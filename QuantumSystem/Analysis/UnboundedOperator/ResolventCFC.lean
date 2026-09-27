/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import QuantumSystem.Analysis.UnboundedOperator.Resolvent

/-!
# The continuous functional calculus of a resolvent

For a self-adjoint operator `A` on a complex Hilbert space and `w` in its resolvent set (e.g.
`w = i`), the resolvent `R = (w - A)⁻¹` is a normal bounded operator, so Mathlib's continuous
functional calculus applies to it. Every other resolvent is a continuous function of `R`:
`(z - A)⁻¹ = cfc (ζ ↦ ζ / (1 - (w - z) ζ)) R`. This is the entry point of the spectral theory of
unbounded self-adjoint operators used here: functions of `A` are written as `cfc g R`, with
`g (ζ) = f (w - ζ⁻¹)`.

## Main results

* `IsSelfAdjoint.isStarNormal_resolvent` — `(w - A)⁻¹` is normal.
* `IsSelfAdjoint.resolvent_eq_cfc` — `(z - A)⁻¹ = cfc (ζ ↦ ζ / (1 - (w - z) ζ)) (w - A)⁻¹`.
-/

@[expose] public section

open scoped LinearPMap

namespace LinearPMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {A : E →ₗ.[ℂ] E} {z w : ℂ}

/-- For a self-adjoint operator, the resolvent `(w - A)⁻¹` is normal: its adjoint is the
resolvent at `w̄`, and resolvents commute. (Outside the resolvent set it is `0`.) -/
theorem _root_.IsSelfAdjoint.isStarNormal_resolvent (hA : IsSelfAdjoint A) (w : ℂ) :
    IsStarNormal (A.resolvent w) := by
  by_cases hw : w ∈ A.resolventSet
  · refine ⟨?_⟩
    rw [ContinuousLinearMap.star_eq_adjoint, hA.adjoint_resolvent hw]
    exact A.commute_resolvent _ _
  · rw [resolvent_of_notMem hw]
    exact ⟨Commute.zero_right _⟩

/-- For a self-adjoint operator and `z`, `w` in its resolvent set, the resolvent at `z` is a
continuous function of the resolvent at `w`:
`(z - A)⁻¹ = cfc (ζ ↦ ζ / (1 - (w - z) ζ)) (w - A)⁻¹`. -/
theorem _root_.IsSelfAdjoint.resolvent_eq_cfc (hA : IsSelfAdjoint A) (hw : w ∈ A.resolventSet)
    (hz : z ∈ A.resolventSet) :
    A.resolvent z = cfc (fun ζ => ζ / (1 - (w - z) * ζ)) (A.resolvent w) := by
  have : IsStarNormal (A.resolvent w) := hA.isStarNormal_resolvent w
  set R := A.resolvent w
  set c := w - z
  have hne : ∀ ζ ∈ spectrum ℂ R, 1 - c * ζ ≠ 0 := fun ζ hζ =>
    one_sub_mul_ne_zero_of_mem_spectrum hw hz hζ
  have hcont : ContinuousOn (fun ζ : ℂ => (1 - c * ζ)⁻¹) (spectrum ℂ R) :=
    ContinuousOn.inv₀ (by fun_prop) hne
  set B := cfc (fun ζ : ℂ => (1 - c * ζ)⁻¹) R
  have hlin : cfc (fun ζ : ℂ => 1 - c * ζ) R = 1 - c • R := by
    rw [cfc_sub (fun _ => (1 : ℂ)) (fun ζ => c * ζ), cfc_const_one ℂ R,
      cfc_const_mul c (fun ζ : ℂ => ζ) R, cfc_id' ℂ R]
  have hB : B * (1 - c • R) = 1 := by
    rw [← hlin, ← cfc_mul _ _ R hcont, ← cfc_one ℂ R]
    exact cfc_congr fun ζ hζ => inv_mul_cancel₀ (hne ζ hζ)
  have hid : R = (1 - c • R) * A.resolvent z := by
    have := resolvent_sub_resolvent hz hw
    rw [sub_mul, one_mul, smul_mul_assoc, ← this]
    abel
  calc A.resolvent z = B * R := by rw [hid, ← mul_assoc, hB, one_mul]
    _ = cfc (fun ζ : ℂ => (1 - c * ζ)⁻¹ * ζ) R := by rw [cfc_mul _ _ R hcont, cfc_id' ℂ R]
    _ = cfc (fun ζ => ζ / (1 - c * ζ)) R := cfc_congr fun ζ _ => by rw [div_eq_mul_inv, mul_comm]

end LinearPMap
