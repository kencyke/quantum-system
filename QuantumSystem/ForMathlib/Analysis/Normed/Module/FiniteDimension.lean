/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Kernel domination on a finite-dimensional space

If `f, g : G →ₗ[𝕜] F` are linear maps out of a finite-dimensional space with `ker g ≤ ker f`, then
`f` is dominated by `g` in norm: `‖f x‖ ≤ C ‖g x‖` for some constant `C`. The map `f` factors
through the range of `g`, a finite-dimensional normed space, on which every linear map is bounded.

## Main results

* `LinearMap.exists_norm_le_mul_norm_of_ker_le` — `ker g ≤ ker f → ∃ C, ∀ x, ‖f x‖ ≤ C * ‖g x‖`.
-/

@[expose] public section

namespace LinearMap

variable {𝕜 G F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [AddCommGroup G]
  [Module 𝕜 G] [FiniteDimensional 𝕜 G] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Kernel domination.** For linear maps `f, g` out of a finite-dimensional space with
`ker g ≤ ker f`, there is `C` with `‖f x‖ ≤ C * ‖g x‖` for every `x`. -/
theorem exists_norm_le_mul_norm_of_ker_le (f g : G →ₗ[𝕜] F) (h : ker g ≤ ker f) :
    ∃ C, ∀ x, ‖f x‖ ≤ C * ‖g x‖ := by
  let Q : range g →ₗ[𝕜] F := (ker g).liftQ f h ∘ₗ g.quotKerEquivRange.symm.toLinearMap
  have hQ : ∀ x, Q ⟨g x, mem_range_self g x⟩ = f x := fun x => by
    simp only [Q, coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    rw [show (⟨g x, mem_range_self g x⟩ : range g) = g.quotKerEquivRange (Submodule.Quotient.mk x)
      from rfl, LinearEquiv.symm_apply_apply, Submodule.liftQ_apply]
  refine ⟨‖LinearMap.toContinuousLinearMap Q‖, fun x => ?_⟩
  rw [← hQ x]
  exact (LinearMap.toContinuousLinearMap Q).le_opNorm _

end LinearMap
