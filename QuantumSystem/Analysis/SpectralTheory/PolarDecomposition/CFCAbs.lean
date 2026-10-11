/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.SpectralTheory.PolarDecomposition
public import QuantumSystem.ForMathlib.Algebra.Star.PartialIsometry
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.Abs

/-!
# Compatibility of the spectral and functional-calculus polar decompositions

The polar decomposition of a closed, densely defined operator `T`
(`QuantumSystem.Analysis.SpectralTheory.PolarDecomposition`) is built from the spectral measure of
`A = T†T`: `|T| = A^{1/2}` (`IsSelfAdjoint.sqrt`) and the partial isometry `U`
(`IsSelfAdjoint.polarIsometry`). For a bounded operator `x : H →L[ℂ] H` the absolute value has a
second, elementary construction, `|x| = (x⋆ x)^{1/2}` of the continuous functional calculus
(`CFC.abs x`, written `|x|` under `open scoped CFC`), from which the polar decomposition in a
von Neumann algebra (`VonNeumannAlgebra.exists_isPartialIsometry_eq_mul_cfcAbs`) is obtained. This
file shows that the two constructions agree for `T = x`, viewed as the everywhere-defined operator
`(x : H →ₗ[ℂ] H).toPMap ⊤`.

* `|T|` is `|x|` (`ContinuousLinearMap.sqrt_eq_toPMap_cfcAbs`).
* `U` is the partial isometry `v` of any factorisation `x = v |x|` with source projection the range
  projection `R(x⋆)` (`ContinuousLinearMap.polarIsometry_eq_of_eq_mul_cfcAbs`), in particular the
  one of `VonNeumannAlgebra.exists_isPartialIsometry_eq_mul_cfcAbs`.

Both theorems are stated for `A = T†T` itself, whose self-adjointness
(`ContinuousLinearMap.isSelfAdjoint_adjointₛₗ_toPMap_compNat_toPMap`) and the closedness of `T`
(`LinearPMap.isClosedₛₗ_toPMap`) hold for every bounded `x`, so they carry no hypotheses.

Both follow from the uniqueness of the polar decomposition
(`IsSelfAdjoint.eq_sqrt_of_eq_compPMap`, `IsSelfAdjoint.eq_polarIsometry_of_eq_compPMap`):
`x = v |x|` with `|x|` positive self-adjoint, `v` isometric on the range of `|x|`
(`ContinuousLinearMap.norm_cfcAbs_apply`) and `v` vanishing on `ker |x| = ker x`
(`ContinuousLinearMap.ker_cfcAbs`), since `ker x` is orthogonal to the range of the source
projection `R(x⋆)`.

For bounded operators `|x|` is the absolute value used throughout the project; the unbounded
construction is needed only for closed, densely defined operators, and the theorems here identify
the two where both apply.

## Main results

* `ContinuousLinearMap.adjointₛₗ_toPMap_compNat_toPMap` — `T†T = (x⋆ x).toPMap ⊤` for
  `T = x.toPMap ⊤`; `LinearPMap.isClosedₛₗ_toPMap` makes `T` closed, and
  `ContinuousLinearMap.isSelfAdjoint_adjointₛₗ_toPMap_compNat_toPMap` makes `T†T` self-adjoint.
* `ContinuousLinearMap.sqrt_eq_toPMap_cfcAbs` — **`|T| = |x|`** for bounded `x`.
* `ContinuousLinearMap.polarIsometry_eq_of_eq_mul_cfcAbs` — **the partial isometry of the polar
  decomposition of a bounded operator is the bounded one**: if `x = v |x|` and `v⋆ v = R(x⋆)`,
  then `U = v`.

## Notation

Inside this file the everywhere-defined operator `(y : H →ₗ[ℂ] H).toPMap ⊤` of a bounded `y` is
written `↑ₚ y` (a `local notation`).
-/

@[expose] public section

open scoped CFC InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `↑ₚ y` is the bounded operator `y`, viewed as the everywhere-defined operator
`(y : H →ₗ[ℂ] H).toPMap ⊤`. -/
local notation "↑ₚ" y:max => LinearMap.toPMap (ContinuousLinearMap.toLinearMap y) ⊤

namespace ContinuousLinearMap

/-- For a bounded `x` and `T = x.toPMap ⊤`, the composite `T†T` is the bounded operator `x⋆ x`,
as an everywhere-defined operator. -/
lemma adjointₛₗ_toPMap_compNat_toPMap (x : H →L[ℂ] H) :
    (↑ₚ x).adjointₛₗ.compNat (↑ₚ x) = ↑ₚ (star x * x) := by
  rw [LinearPMap.adjointₛₗ_eq_adjoint, toPMap_adjoint_eq_adjoint_toPMap_of_dense x (by simp),
    ← LinearPMap.toPMap_comp, star_eq_adjoint]
  rfl

/-- For a bounded `x` and `T = x.toPMap ⊤`, the composite `T†T` is self-adjoint: von Neumann's
theorem (`LinearPMap.isSelfAdjoint_adjointₛₗ_compNat_self`) applies, `T` being closed
(`LinearPMap.isClosedₛₗ_toPMap`) and everywhere defined. -/
lemma isSelfAdjoint_adjointₛₗ_toPMap_compNat_toPMap (x : H →L[ℂ] H) :
    IsSelfAdjoint ((↑ₚ x).adjointₛₗ.compNat (↑ₚ x)) :=
  LinearPMap.isSelfAdjoint_adjointₛₗ_compNat_self (LinearPMap.isClosedₛₗ_toPMap x) (by simp)

/-- `|x|` as an everywhere-defined operator is positive self-adjoint, and an operator `v` with
`x = v |x|` is isometric on its range and factors `x.toPMap ⊤ = v |x|`: the hypotheses of the
uniqueness of the polar decomposition. -/
private lemma toPMap_cfcAbs_spec {x v : H →L[ℂ] H} (hxv : ∀ η, v (|x| η) = x η) :
    IsSelfAdjoint (↑ₚ |x|) ∧ (↑ₚ |x|).IsPositive ∧
      (∀ y ∈ LinearMap.range (↑ₚ |x|).toFun, ‖v y‖ = ‖y‖) ∧
      ↑ₚ x = (v : H →ₗ[ℂ] H).compPMap (↑ₚ |x|) := by
  refine ⟨(CFC.abs_nonneg x).isSelfAdjoint.toPMap,
    LinearMap.IsPositive.toPMap (nonneg_iff_isPositive.mp (CFC.abs_nonneg x)), ?_, ?_⟩
  · rintro _ ⟨η, rfl⟩
    change ‖v (|x| η)‖ = ‖|x| η‖
    rw [hxv, norm_cfcAbs_apply]
  · rw [← LinearPMap.toPMap_compNat, ← LinearPMap.toPMap_comp]
    congr 1
    ext η
    exact (hxv η).symm

/-- **The absolute value of a bounded operator is `|x|`.** For bounded `x` and `T = x.toPMap ⊤`,
the square root `|T| = (T†T)^{1/2}` of the spectral theorem is the absolute value
`|x| = (x⋆ x)^{1/2}` of the continuous functional calculus, as an everywhere-defined operator. -/
theorem sqrt_eq_toPMap_cfcAbs (x : H →L[ℂ] H) :
    x.isSelfAdjoint_adjointₛₗ_toPMap_compNat_toPMap.sqrt = ↑ₚ |x| := by
  obtain ⟨v, -, -, hv, -, -⟩ := exists_isPartialIsometry_mem_centralizer_of_norm_eq
    (↑|x| : H →ₗ[ℂ] H) (x : H →ₗ[ℂ] H) (norm_cfcAbs_apply x) (S := ∅) (by simp) (by simp)
  obtain ⟨hB, hBpos, hV, hTVB⟩ := toPMap_cfcAbs_spec hv
  exact (x.isSelfAdjoint_adjointₛₗ_toPMap_compNat_toPMap.eq_sqrt_of_eq_compPMap rfl hB hBpos v hV
    hTVB).symm

/-- **The partial isometry of the polar decomposition of a bounded operator.** For bounded `x`,
`T = x.toPMap ⊤`, and any `v` with `x = v |x|` whose source projection `v⋆ v` is the range
projection `R(x⋆)` — such as the partial isometry of
`VonNeumannAlgebra.exists_isPartialIsometry_eq_mul_cfcAbs` — the partial isometry `U` of the polar
decomposition `T = U |T|` is `v`. -/
theorem polarIsometry_eq_of_eq_mul_cfcAbs {x v : H →L[ℂ] H} (hxv : x = v * |x|)
    (hsrc : star v * v = (star x).rangeProj) :
    x.isSelfAdjoint_adjointₛₗ_toPMap_compNat_toPMap.polarIsometry rfl
      (LinearPMap.isClosedₛₗ_toPMap x) = v := by
  have hxv' : ∀ η, v (|x| η) = x η := fun η => by
    rw [← mul_apply_eq_comp, ← hxv]
  obtain ⟨hB, hBpos, hV, hTVB⟩ := toPMap_cfcAbs_spec hxv'
  refine (x.isSelfAdjoint_adjointₛₗ_toPMap_compNat_toPMap.eq_polarIsometry_of_eq_compPMap rfl
    (LinearPMap.isClosedₛₗ_toPMap x) hB hBpos v hV ?_ hTVB).symm
  -- `v` vanishes on `ker |x| = ker x`, whose orthogonal complement is the range of `R(x⋆)`.
  rintro _ ⟨⟨η, hd⟩, hη, rfl⟩
  have hxη : η ∈ x.ker := by
    rw [← ker_cfcAbs]
    exact hη
  have hpi : IsPartialIsometry v := isPartialIsometry_of_isStarProjection_star_mul_self
    (hsrc ▸ (star x).isStarProjection_rangeProj)
  have hR : (star x).rangeProj = x.kerᗮ.starProjection := by
    rw [star_eq_adjoint, rangeProj_adjoint]
  change v η = 0
  rw [← hpi.mul_source, mul_apply_eq_comp, hsrc, hR,
    (Submodule.starProjection_apply_eq_zero_iff _).mpr (Submodule.le_orthogonal_orthogonal _ hxη),
    map_zero]

end ContinuousLinearMap
