module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Self-adjoint operators on inner product spaces

This file contains results about self-adjoint operators on inner product spaces.
-/

@[expose] public section

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

namespace ContinuousLinearMap

/-- For a self-adjoint operator T, if ⟪Tx, x⟫ = 0 for all x, then T = 0.
This is a corollary of the polarization identity `LinearMap.IsSymmetric.inner_map_self_eq_zero`. -/
theorem IsSelfAdjoint.eq_zero_of_inner_map_self_eq_zero {T : E →L[ℂ] E}
    (hsa : IsSelfAdjoint T) (h : ∀ x, ⟪T x, x⟫_ℂ = 0) : T = 0 := by
  have hT_sym : (T : E →ₗ[ℂ] E).IsSymmetric := hsa.isSymmetric
  have h' : (T : E →ₗ[ℂ] E) = 0 := hT_sym.inner_map_self_eq_zero.mp h
  ext x
  have := congrFun (congrArg DFunLike.coe h') x
  simp only [LinearMap.zero_apply, ContinuousLinearMap.coe_coe] at this
  exact this

end ContinuousLinearMap
