/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# The cyclic vector of the GNS construction

For a positive linear functional `f` on a (possibly non-unital) C\*-algebra `A`, Mathlib's
`PositiveLinearMap.GNS` and `PositiveLinearMap.gnsNonUnitalStarAlgHom` give the GNS Hilbert space
`f.GNS` and the representation `π_f` of `A` on it.  This file constructs the cyclic vector, as
asked for by the TODO of `Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal`.

The vector `ξ_f` is the Riesz representative of the functional `[a] ↦ f a` on `f.GNS`.  That
functional is bounded, with norm `√‖f‖`, by the Cauchy–Schwarz inequality
`‖f a‖ ≤ √‖f‖ √‖f (a* a)‖` (`PositiveContinuousLinearMap.norm_map_le_sqrt_opNorm_mul`).  Here and
below `‖f‖` is the operator norm of `f`, viewed as a continuous linear map through
`PositiveContinuousLinearMap.ofClass f` (positive functionals on a C\*-algebra are automatically
continuous).

## Main definitions

* `PositiveLinearMap.gnsMk` — the canonical linear map `A →ₗ[ℂ] f.GNS`, `a ↦ [a]`.
* `PositiveLinearMap.gnsFunctional` — the bounded functional on `f.GNS` extending `[a] ↦ f a`.
* `PositiveLinearMap.gnsVector` — the cyclic vector `ξ_f`, its Riesz representative.

## Main results

* `PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_gnsVector` — `π_f a ξ_f = [a]`.
* `PositiveLinearMap.denseRange_gnsNonUnitalStarAlgHom_apply_gnsVector` — `ξ_f` is cyclic.
* `PositiveLinearMap.apply_eq_inner_gnsVector` — `f a = ⟪ξ_f, π_f a ξ_f⟫`.
* `PositiveLinearMap.norm_gnsVector_sq` — `‖ξ_f‖² = ‖f‖`.

## References

* Bratteli, Robinson, *Operator Algebras and Quantum Statistical Mechanics I*, Theorem 2.3.16.
-/

@[expose] public section

open scoped InnerProductSpace ComplexOrder InnerProduct
open UniformSpace Completion

namespace PositiveLinearMap

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (f : A →ₚ[ℂ] ℂ)

/-! ### The canonical map `a ↦ [a]` -/

/-- The canonical map `A →ₗ[ℂ] f.GNS`, `a ↦ [a]`, sending an element of the algebra to its class
in the GNS Hilbert space. -/
noncomputable def gnsMk : A →ₗ[ℂ] f.GNS :=
  (toComplₗᵢ : f.PreGNS →ₗᵢ[ℂ] f.GNS).toLinearMap ∘ₗ f.toPreGNS.toLinearMap

lemma gnsMk_apply (a : A) : f.gnsMk a = (f.toPreGNS a : f.GNS) := rfl

lemma gnsMk_ofPreGNS (x : f.PreGNS) : f.gnsMk (f.ofPreGNS x) = (x : f.GNS) := rfl

/-- The classes `[a]` are dense in `f.GNS`. -/
lemma denseRange_gnsMk : DenseRange f.gnsMk :=
  denseRange_coe.comp f.toPreGNS.surjective.denseRange (continuous_coe _)

/-- `⟪[a], [b]⟫ = f (a* b)`. -/
lemma inner_gnsMk (a b : A) : ⟪f.gnsMk a, f.gnsMk b⟫_ℂ = f (star a * b) := by
  rw [gnsMk_apply, gnsMk_apply, inner_coe, preGNS_inner_def]
  simp

/-- `‖[a]‖ = √‖f (a* a)‖`. -/
lemma norm_gnsMk (a : A) : ‖f.gnsMk a‖ = √‖f (star a * a)‖ := by
  rw [gnsMk_apply, norm_coe, preGNS_norm_def']
  rfl

/-- `‖[a]‖ ≤ √‖f‖ ‖a‖`. -/
lemma norm_gnsMk_le (a : A) :
    ‖f.gnsMk a‖ ≤ √‖(PositiveContinuousLinearMap.ofClass f : A →L[ℂ] ℂ)‖ * ‖a‖ := by
  rw [norm_gnsMk, ← Real.sqrt_sq (norm_nonneg a), ← Real.sqrt_mul (norm_nonneg _)]
  gcongr
  calc ‖f (star a * a)‖
      = ‖(PositiveContinuousLinearMap.ofClass f : A →L[ℂ] ℂ) (star a * a)‖ := rfl
    _ ≤ ‖(PositiveContinuousLinearMap.ofClass f : A →L[ℂ] ℂ)‖ * ‖star a * a‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = _ := by rw [CStarRing.norm_star_mul_self, sq]

/-- `[a] = 0` iff `f (a* a) = 0`. -/
lemma gnsMk_eq_zero_iff (a : A) : f.gnsMk a = 0 ↔ f (star a * a) = 0 := by
  rw [← norm_eq_zero, norm_gnsMk, Real.sqrt_eq_zero (norm_nonneg _), norm_eq_zero]

/-- `π_f a [b] = [a b]`. -/
@[simp] lemma gnsNonUnitalStarAlgHom_apply_gnsMk (a b : A) :
    f.gnsNonUnitalStarAlgHom a (f.gnsMk b) = f.gnsMk (a * b) := by
  simp [gnsMk_apply]

/-! ### The cyclic vector -/

/-- The bounded functional `[a] ↦ f a` on the pre-Hilbert space of the GNS construction; its
operator norm is at most `√‖f‖`. -/
noncomputable def gnsFunctional₀ : f.PreGNS →L[ℂ] ℂ :=
  (f.toLinearMap ∘ₗ f.ofPreGNS.toLinearMap).mkContinuous
    √‖(PositiveContinuousLinearMap.ofClass f : A →L[ℂ] ℂ)‖ fun x => by
      rw [preGNS_norm_def']
      exact (PositiveContinuousLinearMap.ofClass f).norm_map_le_sqrt_opNorm_mul _

lemma gnsFunctional₀_apply (x : f.PreGNS) : f.gnsFunctional₀ x = f (f.ofPreGNS x) := rfl

/-- The bounded functional `f.GNS →L[ℂ] ℂ` extending `[a] ↦ f a` by continuity. -/
noncomputable def gnsFunctional : f.GNS →L[ℂ] ℂ :=
  f.gnsFunctional₀.extend (toComplL : f.PreGNS →L[ℂ] f.GNS)

lemma gnsFunctional_coe (x : f.PreGNS) : f.gnsFunctional x = f (f.ofPreGNS x) :=
  ContinuousLinearMap.extend_eq _ denseRange_coe (isUniformInducing_coe _) x

@[simp] lemma gnsFunctional_gnsMk (a : A) : f.gnsFunctional (f.gnsMk a) = f a :=
  f.gnsFunctional_coe _

/-- The GNS functional has operator norm `√‖f‖`. -/
lemma norm_gnsFunctional :
    ‖f.gnsFunctional‖ = √‖(PositiveContinuousLinearMap.ofClass f : A →L[ℂ] ℂ)‖ := by
  set c := √‖(PositiveContinuousLinearMap.ofClass f : A →L[ℂ] ℂ)‖ with hc
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_) ?_
  · induction x using Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih x =>
      rw [gnsFunctional_coe, norm_coe]
      simpa [gnsFunctional₀_apply] using f.gnsFunctional₀.le_of_opNorm_le
        (LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg _) _) x
  · -- `‖f a‖ ≤ ‖F‖ ‖[a]‖ ≤ ‖F‖ c ‖a‖`, so `c² = ‖f‖ ≤ ‖F‖ c`.
    have h : c * c ≤ ‖f.gnsFunctional‖ * c := by
      rw [hc, Real.mul_self_sqrt (norm_nonneg _)]
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun a => ?_
      calc ‖(PositiveContinuousLinearMap.ofClass f : A →L[ℂ] ℂ) a‖
          = ‖f.gnsFunctional (f.gnsMk a)‖ := by simp
        _ ≤ ‖f.gnsFunctional‖ * ‖f.gnsMk a‖ := f.gnsFunctional.le_opNorm _
        _ ≤ ‖f.gnsFunctional‖ * (c * ‖a‖) := by gcongr; exact f.norm_gnsMk_le a
        _ = ‖f.gnsFunctional‖ * c * ‖a‖ := by ring
    rcases (Real.sqrt_nonneg _ : 0 ≤ c).eq_or_lt with h0 | hpos
    · rw [hc, ← h0]; exact norm_nonneg f.gnsFunctional
    · exact le_of_mul_le_mul_right h hpos

/-- The cyclic vector `ξ_f ∈ f.GNS`: the Riesz representative of the functional `[a] ↦ f a`. -/
noncomputable def gnsVector : f.GNS := (InnerProductSpace.toDual ℂ f.GNS).symm f.gnsFunctional

/-- Riesz identification: `⟪ξ_f, x⟫` is the GNS functional. -/
lemma inner_gnsVector (x : f.GNS) : ⟪f.gnsVector, x⟫_ℂ = f.gnsFunctional x :=
  InnerProductSpace.toDual_symm_apply

/-- `⟪ξ_f, [a]⟫ = f a`. -/
@[simp] lemma inner_gnsVector_gnsMk (a : A) : ⟪f.gnsVector, f.gnsMk a⟫_ℂ = f a := by
  rw [inner_gnsVector, gnsFunctional_gnsMk]

/-- The fundamental identity `π_f a ξ_f = [a]`. -/
@[simp] lemma gnsNonUnitalStarAlgHom_apply_gnsVector (a : A) :
    f.gnsNonUnitalStarAlgHom a f.gnsVector = f.gnsMk a := by
  refine ext_inner_right ℂ fun x => ?_
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x =>
    rw [← gnsMk_ofPreGNS, ← ContinuousLinearMap.adjoint_inner_right,
      ← ContinuousLinearMap.star_eq_adjoint, ← map_star, gnsNonUnitalStarAlgHom_apply_gnsMk,
      inner_gnsVector_gnsMk, inner_gnsMk]

/-- Cyclicity of `ξ_f`: the orbit `{π_f a ξ_f | a : A}` is dense in `f.GNS`. -/
lemma denseRange_gnsNonUnitalStarAlgHom_apply_gnsVector :
    DenseRange fun a => f.gnsNonUnitalStarAlgHom a f.gnsVector := by
  simpa only [gnsNonUnitalStarAlgHom_apply_gnsVector] using f.denseRange_gnsMk

/-- The GNS identity `f a = ⟪ξ_f, π_f a ξ_f⟫`. -/
lemma apply_eq_inner_gnsVector (a : A) :
    f a = ⟪f.gnsVector, f.gnsNonUnitalStarAlgHom a f.gnsVector⟫_ℂ := by
  simp

/-- `‖ξ_f‖ = √‖f‖`. -/
lemma norm_gnsVector :
    ‖f.gnsVector‖ = √‖(PositiveContinuousLinearMap.ofClass f : A →L[ℂ] ℂ)‖ := by
  rw [gnsVector, LinearIsometryEquiv.norm_map, norm_gnsFunctional]

/-- `‖ξ_f‖² = ‖f‖`. -/
lemma norm_gnsVector_sq :
    ‖f.gnsVector‖ ^ 2 = ‖(PositiveContinuousLinearMap.ofClass f : A →L[ℂ] ℂ)‖ := by
  rw [norm_gnsVector, Real.sq_sqrt (norm_nonneg _)]

end PositiveLinearMap
