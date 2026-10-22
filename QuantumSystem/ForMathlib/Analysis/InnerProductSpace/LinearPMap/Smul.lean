/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# The adjoint of a scalar multiple of an unbounded operator

For a nonzero scalar `c`, the adjoint of `c • T` is `conj c • T†`: both have the domain of `T†`,
since `x ↦ ⟪y, c T x⟫` is continuous iff `x ↦ ⟪y, T x⟫` is, and they agree there by the defining
property of the adjoint. At `c = 0` the statement fails, since `0 • T` keeps the domain of `T`.

## Main results

* `LinearPMap.adjoint_smul` — `(c • T)† = conj c • T†` for `c ≠ 0`.
* `IsSelfAdjoint.ofReal_smul` — a nonzero real multiple of a self-adjoint operator is
  self-adjoint.
-/

@[expose] public section

open scoped InnerProductSpace LinearPMap

namespace LinearPMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace E]

/-- The adjoint of a nonzero scalar multiple: `(c • T)† = conj c • T†`. -/
theorem adjoint_smul {c : 𝕜} (hc : c ≠ 0) (T : E →ₗ.[𝕜] F) :
    (c • T)† = (starRingEnd 𝕜 c) • T† := by
  have hfun (y : F) : (innerₛₗ 𝕜 y).comp (c • T).toFun = c • (innerₛₗ 𝕜 y).comp T.toFun := by
    ext x
    simp [inner_smul_right]
  have hdom : (c • T)†.domain = ((starRingEnd 𝕜 c) • T†).domain := by
    ext y
    rw [smul_domain, mem_adjoint_domain_iff, mem_adjoint_domain_iff, hfun, LinearMap.coe_smul]
    exact ⟨fun h => by simpa [smul_smul, inv_mul_cancel₀ hc] using h.const_smul c⁻¹,
      fun h => h.const_smul c⟩
  refine ext hdom fun y hy hy' => ?_
  rw [smul_apply]
  by_cases hT : Dense (T.domain : Set E)
  · have hcT : Dense ((c • T).domain : Set E) := by rwa [smul_domain]
    refine adjoint_apply_eq hcT ⟨y, hy⟩ fun x => ?_
    rw [inner_smul_left, RCLike.conj_conj, smul_apply, inner_smul_right]
    exact congrArg (c * ·) (adjoint_isFormalAdjoint hT ⟨y, hy'⟩ ⟨x, x.2⟩)
  · have hcT : ¬Dense ((c • T).domain : Set E) := by rwa [smul_domain]
    rw [adjoint_apply_of_not_dense hcT, adjoint_apply_of_not_dense hT, smul_zero]

/-- A nonzero real multiple of a self-adjoint operator is self-adjoint. -/
theorem _root_.IsSelfAdjoint.ofReal_smul {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A) {r : ℝ}
    (hr : r ≠ 0) : IsSelfAdjoint ((r : 𝕜) • A) := by
  rw [isSelfAdjoint_def] at hA ⊢
  rw [adjoint_smul (by exact_mod_cast hr), RCLike.conj_ofReal, hA]

end LinearPMap
