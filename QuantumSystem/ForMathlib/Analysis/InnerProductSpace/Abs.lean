/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs

/-!
# The range projection and the absolute value of a bounded operator

For a bounded operator `x : E →L[𝕜] F` into a Hilbert space, the **range projection** `R(x)` is the
orthogonal projection of `F` onto the closure of the range of `x`. In operator-algebra language it
is the *left support* `l(x) = R(x)`, the least projection `p` with `p x = x`, while the *right
support* is `r(x) = R(x†)`, the projection onto `(ker x)ᗮ`. These are the range and source
projections of the partial isometry in the polar decomposition `x = v |x|`.

For a bounded operator `x` on a complex Hilbert space, the absolute value `|x| = (x⋆ x)^{1/2}` of
the continuous functional calculus (`CFC.abs x`) has the same norm as `x` on every vector,
`‖|x| η‖ = ‖x η‖`, because `|x|` is self-adjoint with `|x| |x| = x⋆ x`. Hence `|x|` and `x` have
the same kernel, and the closures of the ranges of `|x|` and of `x⋆` agree: both are the
orthogonal complement of `ker x`. These are the inputs of the polar decomposition `x = v |x|`, in
which `v` carries `|x| η ↦ x η`; they also make `v` unique once its source projection is fixed to
be the range projection `R(x⋆)`.

## Main definitions

* `ContinuousLinearMap.rangeProj x` — the range projection `R(x)`, the orthogonal projection onto
  `closure (ran x)`.

## Main results

* `ContinuousLinearMap.isStarProjection_rangeProj` — `R(x)` is a star projection.
* `ContinuousLinearMap.rangeProj_comp_self` — `R(x) x = x`.
* `ContinuousLinearMap.rangeProj_le_iff` — `R(x)` is the least projection fixing `x`:
  `R(x) ≤ p ↔ p x = x` for every star projection `p`.
* `ContinuousLinearMap.rangeProj_eq_zero_iff` — `R(x) = 0 ↔ x = 0`.
* `ContinuousLinearMap.rangeProj_adjoint` — `R(x†)` is the projection onto `(ker x)ᗮ`.
* `ContinuousLinearMap.rangeProj_mul_rangeProj_eq_zero` — if `x₁† x₂ = 0`, then
  `R(x₁) R(x₂) = 0`.
* `ContinuousLinearMap.norm_cfcAbs_apply` — `‖|x| η‖ = ‖x η‖`.
* `ContinuousLinearMap.ker_cfcAbs` — `ker |x| = ker x`.
* `ContinuousLinearMap.topologicalClosure_range_cfcAbs` — `closure (ran |x|) = closure (ran x⋆)`;
  equivalently `R(|x|) = R(x⋆)` for the range projections (`ContinuousLinearMap.rangeProj_cfcAbs`).
* `ContinuousLinearMap.eq_of_eq_mul_cfcAbs` — **uniqueness of the polar decomposition**: an
  operator `v` with `x = v |x|` and source projection `v⋆ v = R(x⋆)` is unique.

## Notation

| Symbol | Expansion | How to activate |
|---|---|---|
| `|x|` | `CFC.abs x` | `open scoped CFC` |

The operator-algebra literature writes `|x| = (x⋆ x)^{1/2}` for the absolute value of an element
of a C⋆-algebra, Mathlib's `CFC.abs x`; this file provides that notation. It is scoped because
Mathlib's lattice absolute value `|a|` uses the same bars: on a type carrying both a lattice and a
continuous functional calculus, such as `ℝ`, the two readings would be ambiguous. Open the scope
only where `|x|` means `CFC.abs`.

## Conventions

The adjoint `x†` (Mathlib's notation for `ContinuousLinearMap.adjoint x`, under
`open scoped InnerProduct`) is written for operators between two spaces, the star `x⋆` (`star x`)
for an element of the C⋆-algebra `H →L[ℂ] H`; the two agree by
`ContinuousLinearMap.star_eq_adjoint`.
-/

@[expose] public section

/-- `|x|` is the absolute value `CFC.abs x = (x⋆ x)^{1/2}` of the continuous functional calculus. -/
scoped[CFC] notation:max "|" x "|" => CFC.abs x

open scoped InnerProductSpace InnerProduct CFC

namespace ContinuousLinearMap

section RangeProj

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The **range projection** `R(x)` of a bounded operator `x`: the orthogonal projection onto the
closure of the range of `x`. For an operator on a Hilbert space it is the *left support*
`l(x) = R(x)` of the operator-algebra literature; the *right support* is `r(x) = R(x†)`, the
projection onto `(ker x)ᗮ` (`ContinuousLinearMap.rangeProj_adjoint`). -/
noncomputable def rangeProj (x : E →L[𝕜] F) : F →L[𝕜] F :=
  x.range.topologicalClosure.starProjection

/-- The range projection is a star projection. -/
lemma isStarProjection_rangeProj (x : E →L[𝕜] F) : IsStarProjection (rangeProj x) :=
  isStarProjection_starProjection

/-- The range of `R(x)` is the closure of the range of `x`. -/
lemma range_rangeProj (x : E →L[𝕜] F) :
    (rangeProj x).range = x.range.topologicalClosure :=
  Submodule.range_starProjection _

/-- `R(x)` fixes every vector of `closure (ran x)`. -/
lemma rangeProj_apply_eq_self {x : E →L[𝕜] F} {v : F}
    (hv : v ∈ x.range.topologicalClosure) : rangeProj x v = v :=
  Submodule.starProjection_eq_self_iff.mpr hv

/-- `R(x)` acts as the identity on the left of `x`: `R(x) x = x`. -/
@[simp]
lemma rangeProj_comp_self (x : E →L[𝕜] F) : (rangeProj x).comp x = x :=
  ext fun v => rangeProj_apply_eq_self (Submodule.le_topologicalClosure _ ⟨v, rfl⟩)

/-- **`R(x)` is the least projection fixing `x`.** For a star projection `p`, `R(x) ≤ p` iff
`p x = x`. -/
lemma rangeProj_le_iff (x : E →L[𝕜] F) {p : F →L[𝕜] F} (hp : IsStarProjection p) :
    rangeProj x ≤ p ↔ p.comp x = x := by
  obtain ⟨_, hpeq⟩ := isStarProjection_iff_eq_starProjection_range.mp hp
  have hcl : IsClosed (p.range : Set F) := IsIdempotentElem.isClosed_range hp.isIdempotentElem
  conv_lhs => rw [rangeProj, hpeq, Submodule.starProjection_le_starProjection_iff]
  rw [← coe_inj, toLinearMap_comp,
    LinearMap.IsIdempotentElem.comp_eq_right_iff (IsIdempotentElem.toLinearMap hp.isIdempotentElem)]
  exact ⟨(Submodule.le_topologicalClosure _).trans,
    fun h => Submodule.topologicalClosure_minimal _ h hcl⟩

/-- The range projection vanishes exactly on the zero operator: `R(x) = 0 ↔ x = 0`. -/
@[simp]
lemma rangeProj_eq_zero_iff {x : E →L[𝕜] F} : rangeProj x = 0 ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← rangeProj_comp_self x, h, zero_comp]
  · simp [rangeProj, h]

/-- The range projection of a nonzero operator is nonzero. -/
lemma rangeProj_ne_zero {x : E →L[𝕜] F} (hx : x ≠ 0) : rangeProj x ≠ 0 :=
  rangeProj_eq_zero_iff.not.mpr hx

variable [CompleteSpace E]

/-- **The right support.** The range projection of the adjoint, `R(x†)`, is the projection onto the
orthogonal complement of the kernel of `x`. -/
lemma rangeProj_adjoint (x : E →L[𝕜] F) : rangeProj (x†) = x.kerᗮ.starProjection := by
  simp only [rangeProj, orthogonal_ker]

/-- **Orthogonal range projections.** If `x₁† x₂ = 0`, the range projections of `x₁` and `x₂` are
orthogonal: `R(x₁) R(x₂) = 0`. -/
lemma rangeProj_mul_rangeProj_eq_zero {x₁ x₂ : E →L[𝕜] F} (h : x₁† ∘L x₂ = 0) :
    rangeProj x₁ * rangeProj x₂ = 0 := by
  rw [rangeProj, rangeProj, mul_def, Submodule.starProjection_comp_starProjection_eq_zero_iff,
    Submodule.isOrtho_comm, Submodule.isOrtho_iff_le]
  refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)
  rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.triorthogonal_eq_orthogonal,
    orthogonal_range]
  exact LinearMap.range_le_ker_iff.mpr (by rw [← toLinearMap_comp, h]; rfl)

end RangeProj

section Abs

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `|x|` and `x` have the same norm on every vector: `‖|x| η‖ = ‖x η‖`, because
`|x| |x| = x⋆ x` and `|x|` is self-adjoint. -/
lemma norm_cfcAbs_apply (x : H →L[ℂ] H) (η : H) : ‖|x| η‖ = ‖x η‖ := by
  have hsa : IsSelfAdjoint |x| := (CFC.abs_nonneg x).isSelfAdjoint
  have hinner : ⟪|x| η, |x| η⟫_ℂ = ⟪x η, x η⟫_ℂ := by
    rw [← adjoint_inner_right, ← star_eq_adjoint, hsa.star_eq, ← mul_apply_eq_comp,
      CFC.abs_mul_abs, mul_apply_eq_comp, star_eq_adjoint, adjoint_inner_right]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hinner
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by exact_mod_cast hinner)

/-- `|x|` and `x` have the same kernel (`ContinuousLinearMap.norm_cfcAbs_apply`). -/
lemma ker_cfcAbs (x : H →L[ℂ] H) : (|x|).ker = x.ker := by
  ext η
  simp only [LinearMap.mem_ker, coe_coe]
  rw [← norm_eq_zero, norm_cfcAbs_apply, norm_eq_zero]

/-- The closures of the ranges of `|x|` and of `x⋆` agree: both are the orthogonal complement of
`ker |x| = ker x` (`ContinuousLinearMap.ker_cfcAbs`). -/
lemma topologicalClosure_range_cfcAbs (x : H →L[ℂ] H) :
    (|x|).range.topologicalClosure = (star x).range.topologicalClosure := by
  have hsa : IsSelfAdjoint |x| := (CFC.abs_nonneg x).isSelfAdjoint
  rw [← Submodule.orthogonal_orthogonal_eq_closure, ← Submodule.orthogonal_orthogonal_eq_closure,
    orthogonal_range, orthogonal_range, ← star_eq_adjoint, ← star_eq_adjoint, hsa.star_eq,
    star_star, ker_cfcAbs]

/-- The range projections of `|x|` and of `x⋆` agree: `R(|x|) = R(x⋆)`
(`ContinuousLinearMap.topologicalClosure_range_cfcAbs`). -/
lemma rangeProj_cfcAbs (x : H →L[ℂ] H) : rangeProj |x| = rangeProj (star x) := by
  simp only [rangeProj, topologicalClosure_range_cfcAbs]

/-- An operator whose source projection `v⋆ v` is a star projection `p` satisfies `v p = v`: the
operator `e = v (1 - p)` has `e⋆ e = (1 - p) p (1 - p) = 0`. -/
private lemma mul_eq_self_of_star_mul_self_eq {v p : H →L[ℂ] H} (hp : IsStarProjection p)
    (hv : star v * v = p) : v * p = v := by
  have hq : star (1 - p) = 1 - p := by rw [star_sub, star_one, hp.isSelfAdjoint.star_eq]
  have hqp : (1 - p) * p = 0 := by rw [sub_mul, one_mul, hp.isIdempotentElem.eq, sub_self]
  have h0 : star (v * (1 - p)) * (v * (1 - p)) = 0 := by
    rw [star_mul, hq, mul_assoc, ← mul_assoc (star v), hv, ← mul_assoc, hqp, zero_mul]
  have h := (CStarRing.star_mul_self_eq_zero_iff _).mp h0
  rw [mul_sub, mul_one, sub_eq_zero] at h
  exact h.symm

/-- **Uniqueness of the polar decomposition.** If `x = v |x|` and `x = w |x|`, where the source
projections `v⋆ v` and `w⋆ w` are both the range projection `R(x⋆)`, then `v = w`: `v` and `w`
agree on the range of `|x|`, hence on its closure, which is the range of `R(x⋆)`
(`ContinuousLinearMap.rangeProj_cfcAbs`), and both vanish on its orthogonal complement. -/
lemma eq_of_eq_mul_cfcAbs {x v w : H →L[ℂ] H} (hv : x = v * |x|)
    (hvs : star v * v = rangeProj (star x)) (hw : x = w * |x|)
    (hws : star w * w = rangeProj (star x)) : v = w := by
  have hR := rangeProj_cfcAbs x
  -- `v - w` vanishes on the range of `|x|`, hence on its closure.
  have hle : (|x|).range.topologicalClosure ≤ (v - w).ker := by
    refine Submodule.topologicalClosure_minimal _ ?_ (v - w).isClosed_ker
    rintro _ ⟨η, rfl⟩
    change v (|x| η) - w (|x| η) = 0
    rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, ← hv, ← hw, sub_self]
  have hvw : v * rangeProj |x| = w * rangeProj |x| := ext fun η => by
    have h := hle (Submodule.starProjection_apply_mem _ η)
    rwa [LinearMap.mem_ker, coe_coe, sub_apply, sub_eq_zero] at h
  have hP := isStarProjection_rangeProj (star x)
  rw [← mul_eq_self_of_star_mul_self_eq hP hvs, ← mul_eq_self_of_star_mul_self_eq hP hws, ← hR,
    hvw]

end Abs

end ContinuousLinearMap
