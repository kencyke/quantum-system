/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import QuantumSystem.ForMathlib.LinearAlgebra.LinearPMap

/-!
# Adjoints of sums and composites of unbounded operators

Rules for the adjoint `T†` of a densely defined `LinearPMap` between Hilbert spaces under
perturbation and composition by bounded operators, following [Weidmann].

## Main results

* `LinearPMap.adjoint_vadd` — `(A + T)† = A† + T†` for a bounded, everywhere-defined `A`.
* `LinearPMap.adjoint_compNat_le` — `T† S† ⊆ (S T)†` for densely defined `S` whenever `S T` is
  densely defined.
* `LinearPMap.adjoint_compPMap` — `(B T)† = T† B†` for a bounded, everywhere-defined `B` on the
  left.
* `LinearPMap.adjoint_compNat_toPMap` — `(T B)† = B† T†` for a bounded `B` on the right, provided
  `T` factors through `B` via a bounded `C`: `B C` maps `dom T` into itself and `T (B C x) = T x`.
  The two standard instances are `B` invertible (`C = B⁻¹`) and `B` a partial isometry whose
  range projection `B B†` does not change `T` (`C = B†`).

All composites are taken on the natural domain (`LinearPMap.compNat`).

## References

* [J. Weidmann, *Linear Operators in Hilbert Spaces*][weidmann_linear]
-/

@[expose] public section

open scoped LinearPMap

namespace LinearPMap

variable {𝕜 E F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- **Bounded perturbation.** For a bounded, everywhere-defined `A` and a densely defined `T`,
`(A + T)† = A† + T†`; in particular the adjoint domain is unchanged. -/
theorem adjoint_vadd [CompleteSpace E] [CompleteSpace F] {T : E →ₗ.[𝕜] F}
    (hT : Dense (T.domain : Set E)) (A : E →L[𝕜] F) :
    ((A : E →ₗ[𝕜] F) +ᵥ T)† = ((ContinuousLinearMap.adjoint A : F →L[𝕜] E) : F →ₗ[𝕜] E) +ᵥ T† := by
  have hAT : Dense (((A : E →ₗ[𝕜] F) +ᵥ T).domain : Set E) := hT
  have hle : ((ContinuousLinearMap.adjoint A : F →L[𝕜] E) : F →ₗ[𝕜] E) +ᵥ T† ≤
      ((A : E →ₗ[𝕜] F) +ᵥ T)† := by
    refine IsFormalAdjoint.le_adjoint hAT fun x y => ?_
    rw [vadd_apply, vadd_apply]
    simp only [ContinuousLinearMap.coe_coe, inner_add_left, inner_add_right,
      ContinuousLinearMap.adjoint_inner_right]
    rw [(adjoint_isFormalAdjoint hT).symm x y]
  refine (eq_of_le_of_domain_eq hle (le_antisymm hle.1 fun y hy => ?_)).symm
  refine mem_adjoint_domain_of_exists y ⟨((A : E →ₗ[𝕜] F) +ᵥ T)† ⟨y, hy⟩ -
    ContinuousLinearMap.adjoint A y, fun x => ?_⟩
  rw [inner_sub_left, (adjoint_isFormalAdjoint hAT) ⟨y, hy⟩ x, vadd_apply, inner_add_right,
    ContinuousLinearMap.adjoint_inner_left]
  simp

/-- **Adjoint of a composite, general inclusion.** For densely defined `S` with `S T` densely
defined (on its natural domain; then `T` is densely defined too), `T† S† ⊆ (S T)†`. -/
theorem adjoint_compNat_le [CompleteSpace E] [CompleteSpace F] {T : E →ₗ.[𝕜] F}
    {S : F →ₗ.[𝕜] G} (hS : Dense (S.domain : Set F)) (hST : Dense ((S.compNat T).domain : Set E)) :
    T†.compNat S† ≤ (S.compNat T)† := by
  have hT : Dense (T.domain : Set E) := hST.mono compNat_domain_le
  refine IsFormalAdjoint.le_adjoint hST fun x y => ?_
  rw [compNat_apply, compNat_apply]
  exact ((adjoint_isFormalAdjoint hS).symm ⟨_, compNat_apply_mem x⟩ ⟨_, compNat_domain_le y.2⟩).trans
    ((adjoint_isFormalAdjoint hT).symm ⟨_, compNat_domain_le x.2⟩ ⟨_, compNat_apply_mem y⟩)

/-- **Adjoint of a composite with a bounded left factor.** For a bounded, everywhere-defined `B`
and a densely defined `T`, `(B T)† = T† B†`, the right-hand side on its natural domain
`{y | B† y ∈ dom T†}`. -/
theorem adjoint_compPMap [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]
    {T : E →ₗ.[𝕜] F} (hT : Dense (T.domain : Set E)) (B : F →L[𝕜] G) :
    ((B : F →ₗ[𝕜] G).compPMap T)† =
      T†.compNat (((ContinuousLinearMap.adjoint B : G →L[𝕜] F) : G →ₗ[𝕜] F).toPMap ⊤) := by
  have hBT : Dense (((B : F →ₗ[𝕜] G).compPMap T).domain : Set E) := hT
  have hle : T†.compNat (((ContinuousLinearMap.adjoint B : G →L[𝕜] F) : G →ₗ[𝕜] F).toPMap ⊤) ≤
      ((B : F →ₗ[𝕜] G).compPMap T)† := by
    refine IsFormalAdjoint.le_adjoint hBT fun x y => ?_
    rw [compNat_apply, ← (adjoint_isFormalAdjoint hT).symm ⟨_, x.2⟩]
    simp only [LinearMap.compPMap_apply, ContinuousLinearMap.coe_coe]
    exact (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
  refine (eq_of_le_of_domain_eq hle (le_antisymm hle.1 fun y hy => ?_)).symm
  refine mem_compNat_toPMap_domain.mpr (mem_adjoint_domain_of_exists _
    ⟨((B : F →ₗ[𝕜] G).compPMap T)† ⟨y, hy⟩, fun x => ?_⟩)
  rw [(adjoint_isFormalAdjoint hBT) ⟨y, hy⟩ x, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.adjoint_inner_left]
  rfl

/-- **Adjoint of a composite with a bounded right factor.** Let `B` be bounded and `T` densely
defined with `T B` densely defined, and suppose `T` factors through `B` via a bounded `C`: every
`(x, z)` in the graph of `T` gives `(B (C x), z)` in the graph of `T`. Then `(T B)† = B† T†`.

Without the factorisation only `B† T† ⊆ (T B)†` holds (this is `LinearPMap.adjoint_compNat_le`
combined with `ContinuousLinearMap.toPMap_adjoint_eq_adjoint_toPMap_of_dense`). The
hypothesis holds with `C = B⁻¹` for invertible `B`, and with `C = B†` for a partial isometry `B`
whose range projection `B B†` does not change `T`. -/
theorem adjoint_compNat_toPMap [CompleteSpace E] [CompleteSpace F] {T : E →ₗ.[𝕜] G}
    (hT : Dense (T.domain : Set E)) (B : F →L[𝕜] E)
    (hTB : Dense ((T.compNat ((B : F →ₗ[𝕜] E).toPMap ⊤)).domain : Set F)) (C : E →L[𝕜] F)
    (hBC : ∀ x z, (x, z) ∈ T.graph → (B (C x), z) ∈ T.graph) :
    (T.compNat ((B : F →ₗ[𝕜] E).toPMap ⊤))† =
      ((ContinuousLinearMap.adjoint B : E →L[𝕜] F) : E →ₗ[𝕜] F).compPMap T† := by
  have hle : ((ContinuousLinearMap.adjoint B : E →L[𝕜] F) : E →ₗ[𝕜] F).compPMap T† ≤
      (T.compNat ((B : F →ₗ[𝕜] E).toPMap ⊤))† := by
    refine IsFormalAdjoint.le_adjoint hTB fun x y => ?_
    rw [compNat_apply, (adjoint_isFormalAdjoint hT).symm _ y]
    simp only [LinearMap.compPMap_apply, ContinuousLinearMap.coe_coe]
    exact (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
  refine (eq_of_le_of_domain_eq hle (le_antisymm hle.1 fun y hy => ?_)).symm
  refine mem_adjoint_domain_of_exists _ ⟨ContinuousLinearMap.adjoint C
    ((T.compNat ((B : F →ₗ[𝕜] E).toPMap ⊤))† ⟨y, hy⟩), fun u => ?_⟩
  have hu : (B (C u), T u) ∈ T.graph := hBC _ _ (T.mem_graph u)
  have hCu : C u ∈ (T.compNat ((B : F →ₗ[𝕜] E).toPMap ⊤)).domain :=
    mem_compNat_toPMap_domain.mpr (mem_domain_of_mem_graph hu)
  rw [ContinuousLinearMap.adjoint_inner_left,
    (adjoint_isFormalAdjoint hTB) ⟨y, hy⟩ ⟨C u, hCu⟩, compNat_apply]
  exact congrArg _ ((image_iff _).mpr hu).symm

end LinearPMap
