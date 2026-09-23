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
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# The cyclic vector of the GNS construction

For a positive linear functional `f` on a (possibly non-unital) C\*-algebra `A`, Mathlib's
`PositiveLinearMap.GNS` and `PositiveLinearMap.gnsNonUnitalStarAlgHom` give the GNS Hilbert space
`f.GNS` and the representation `π_f` of `A` on it (`PositiveLinearMap.gnsStarAlgHom` in the
unital case).  This file constructs the cyclic vector, and its normalisation, as asked for by the
TODO of `Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal`, in both the unital and the
non-unital case.

The vector `ξ_f` is the Riesz representative of the functional `[a] ↦ f a` on `f.GNS`.  That
functional is bounded, with norm `√‖f‖ₒₚ`, by the Cauchy–Schwarz inequality
`‖f a‖ ≤ √‖f‖ₒₚ √‖f (a* a)‖` (`PositiveContinuousLinearMap.norm_map_le_sqrt_opNorm_mul`).  Here and
below `‖f‖ₒₚ` is the operator norm of `f`, viewed as a continuous linear map through
`PositiveContinuousLinearMap.ofClass f` (positive functionals on a C\*-algebra are automatically
continuous); the notation is scoped to `PositiveLinearMap`.

## Main definitions

* `PositiveLinearMap.gnsMk` — the canonical linear map `A →ₗ[ℂ] f.GNS`, `a ↦ [a]`.
* `PositiveLinearMap.gnsFunctional` — the bounded functional on `f.GNS` extending `[a] ↦ f a`.
* `PositiveLinearMap.gnsVector` — the cyclic vector `ξ_f`, its Riesz representative.

## Main results

* `PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_gnsVector` — `π_f a ξ_f = [a]`.
* `PositiveLinearMap.denseRange_gnsNonUnitalStarAlgHom_apply_gnsVector` — `ξ_f` is cyclic.
* `PositiveLinearMap.apply_eq_inner_gnsNonUnitalStarAlgHom_gnsVector` — `f a = ⟪ξ_f, π_f a ξ_f⟫`.
* `PositiveLinearMap.norm_gnsVector_sq` — `‖ξ_f‖² = ‖f‖ₒₚ`.
* `PositiveLinearMap.norm_normalize_gnsVector`, `PositiveLinearMap.inner_gnsNonUnitalStarAlgHom_normalize_gnsVector`,
  `PositiveLinearMap.denseRange_gnsNonUnitalStarAlgHom_apply_normalize_gnsVector` —
  `ζ_f = NormedSpace.normalize ξ_f` is cyclic and realises the normalised functional,
  `⟪ζ_f, π_f a ζ_f⟫ = ‖f‖ₒₚ⁻¹ f a`; it is a unit vector for `f ≠ 0`.  This is the unit cyclic vector asked for by the
  Mathlib TODO.
* Unital case: each `gnsNonUnitalStarAlgHom` lemma above has a `gnsStarAlgHom` counterpart of
  the same name (`PositiveLinearMap.gnsStarAlgHom_apply_gnsVector`,
  `PositiveLinearMap.apply_eq_inner_gnsStarAlgHom_gnsVector`, …); in addition
  `PositiveLinearMap.gnsVector_eq_gnsMk_one` (`ξ_f = [1]`) and
  `PositiveLinearMap.ofReal_norm_gnsVector_sq` (`‖ξ_f‖² = f 1`).

## References

* Bratteli, Robinson, *Operator Algebras and Quantum Statistical Mechanics I*, Theorem 2.3.16.
-/

@[expose] public section

open scoped InnerProductSpace ComplexOrder InnerProduct
open UniformSpace Completion

namespace PositiveLinearMap

/-- The operator norm `‖f‖ₒₚ` of a positive linear functional `f` on a C\*-algebra, taken through
`PositiveContinuousLinearMap.ofClass f` (positive functionals on a C\*-algebra are automatically
continuous).  This is the spelling Mathlib's norm lemmas, such as
`PositiveContinuousLinearMap.norm_map_le_sqrt_opNorm_mul`, are stated in. -/
scoped notation "‖" f "‖ₒₚ" =>
  ‖PositiveContinuousLinearMap.toContinuousLinearMap (PositiveContinuousLinearMap.ofClass f)‖

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (f : A →ₚ[ℂ] ℂ)

/-- `‖f‖ₒₚ = 0` iff `f = 0`. -/
lemma opNorm_eq_zero_iff : ‖f‖ₒₚ = 0 ↔ f = 0 := by
  rw [norm_eq_zero]
  constructor
  · intro h
    ext a
    exact DFunLike.congr_fun h a
  · rintro rfl
    ext a
    rfl

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

/-- `‖[a]‖ ≤ √‖f‖ₒₚ ‖a‖`. -/
lemma norm_gnsMk_le (a : A) :
    ‖f.gnsMk a‖ ≤ √‖f‖ₒₚ * ‖a‖ := by
  rw [norm_gnsMk, ← Real.sqrt_sq (norm_nonneg a), ← Real.sqrt_mul (norm_nonneg _)]
  gcongr
  calc ‖f (star a * a)‖
      = ‖(PositiveContinuousLinearMap.ofClass f : A →L[ℂ] ℂ) (star a * a)‖ := rfl
    _ ≤ ‖f‖ₒₚ * ‖star a * a‖ :=
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
operator norm is at most `√‖f‖ₒₚ`. -/
noncomputable def gnsFunctional₀ : f.PreGNS →L[ℂ] ℂ :=
  (f.toLinearMap ∘ₗ f.ofPreGNS.toLinearMap).mkContinuous
    √‖f‖ₒₚ fun x => by
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

/-- The GNS functional has operator norm `√‖f‖ₒₚ`. -/
lemma norm_gnsFunctional :
    ‖f.gnsFunctional‖ = √‖f‖ₒₚ := by
  set c := √‖f‖ₒₚ with hc
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_) ?_
  · induction x using Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih x =>
      rw [gnsFunctional_coe, norm_coe]
      simpa [gnsFunctional₀_apply] using f.gnsFunctional₀.le_of_opNorm_le
        (LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg _) _) x
  · -- `‖f a‖ ≤ ‖F‖ ‖[a]‖ ≤ ‖F‖ c ‖a‖`, so `c² = ‖f‖ₒₚ ≤ ‖F‖ c`.
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
lemma apply_eq_inner_gnsNonUnitalStarAlgHom_gnsVector (a : A) :
    f a = ⟪f.gnsVector, f.gnsNonUnitalStarAlgHom a f.gnsVector⟫_ℂ := by
  simp

/-- `‖ξ_f‖ = √‖f‖ₒₚ`. -/
lemma norm_gnsVector :
    ‖f.gnsVector‖ = √‖f‖ₒₚ := by
  rw [gnsVector, LinearIsometryEquiv.norm_map, norm_gnsFunctional]

/-- `‖ξ_f‖² = ‖f‖ₒₚ`. -/
lemma norm_gnsVector_sq :
    ‖f.gnsVector‖ ^ 2 = ‖f‖ₒₚ := by
  rw [norm_gnsVector, Real.sq_sqrt (norm_nonneg _)]

/-- `ξ_f = 0` iff `f = 0`. -/
lemma gnsVector_eq_zero_iff : f.gnsVector = 0 ↔ f = 0 := by
  rw [← norm_eq_zero, norm_gnsVector, Real.sqrt_eq_zero (norm_nonneg _), opNorm_eq_zero_iff]

/-! ### The normalised cyclic vector

The unit vector `ζ_f = ξ_f / ‖ξ_f‖` is Mathlib's `NormedSpace.normalize f.gnsVector`.  It realises
the normalised functional `‖f‖ₒₚ⁻¹ f`, a state when `f ≠ 0`. -/

/-- `ζ_f = ‖f‖ₒₚ^{-1/2} ξ_f`. -/
lemma normalize_gnsVector :
    NormedSpace.normalize f.gnsVector = (((√‖f‖ₒₚ)⁻¹ : ℝ) : ℂ) • f.gnsVector := by
  rw [NormedSpace.normalize, norm_gnsVector, Complex.coe_smul]

/-- `ζ_f` is a unit vector when `f ≠ 0`. -/
lemma norm_normalize_gnsVector (hf : f ≠ 0) : ‖NormedSpace.normalize f.gnsVector‖ = 1 :=
  NormedSpace.norm_normalize_eq_one_iff.mpr (f.gnsVector_eq_zero_iff.not.mpr hf)

/-- `⟪ζ_f, π_f a ζ_f⟫ = ‖f‖ₒₚ⁻¹ f a`: the vector state of `ζ_f` is the normalised functional.
Both sides vanish when `f = 0`. -/
lemma inner_gnsNonUnitalStarAlgHom_normalize_gnsVector (a : A) :
    ⟪NormedSpace.normalize f.gnsVector,
      f.gnsNonUnitalStarAlgHom a (NormedSpace.normalize f.gnsVector)⟫_ℂ =
      (‖f‖ₒₚ⁻¹ : ℝ) * f a := by
  rw [normalize_gnsVector, map_smul, inner_smul_left, inner_smul_right,
    ← apply_eq_inner_gnsNonUnitalStarAlgHom_gnsVector, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul,
    ← mul_inv, Real.mul_self_sqrt (norm_nonneg _)]

/-- Cyclicity of `ζ_f`: for `f ≠ 0` it is a nonzero multiple of the cyclic vector `ξ_f`, and for
`f = 0` the GNS space is `{0}`. -/
lemma denseRange_gnsNonUnitalStarAlgHom_apply_normalize_gnsVector :
    DenseRange fun a => f.gnsNonUnitalStarAlgHom a (NormedSpace.normalize f.gnsVector) := by
  refine f.denseRange_gnsMk.mono ?_
  rintro _ ⟨b, rfl⟩
  rcases eq_or_ne f 0 with rfl | hf
  · refine ⟨0, ?_⟩
    beta_reduce
    rw [map_zero, zero_apply, eq_comm, gnsMk_eq_zero_iff]
    rfl
  set c : ℂ := (((√‖f‖ₒₚ)⁻¹ : ℝ) : ℂ) with hc_def
  have hc : c ≠ 0 := by simpa [hc_def] using (f.opNorm_eq_zero_iff).not.mpr hf
  refine ⟨c⁻¹ • b, ?_⟩
  beta_reduce
  rw [normalize_gnsVector, ← hc_def, map_smul (f.gnsNonUnitalStarAlgHom (c⁻¹ • b)),
    gnsNonUnitalStarAlgHom_apply_gnsVector, ← map_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]

end NonUnital

/-! ### The unital case

For a unital C\*-algebra, Mathlib's unital representation `f.gnsStarAlgHom` has the same
underlying operators as `f.gnsNonUnitalStarAlgHom`, and the cyclic vector is the class `[1]` of
the unit, with `‖ξ_f‖² = f 1`. -/

section Unital

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (f : A →ₚ[ℂ] ℂ)

/-- On a unital algebra the non-unital GNS representation is unital: `π_f 1 = 1`. -/
lemma gnsNonUnitalStarAlgHom_one : f.gnsNonUnitalStarAlgHom 1 = 1 :=
  map_one f.gnsStarAlgHom

/-- `π_f a [b] = [a b]`, for the unital GNS representation. -/
lemma gnsStarAlgHom_apply_gnsMk (a b : A) :
    f.gnsStarAlgHom a (f.gnsMk b) = f.gnsMk (a * b) :=
  f.gnsNonUnitalStarAlgHom_apply_gnsMk a b

/-- `π_f a ξ_f = [a]`, for the unital GNS representation. -/
lemma gnsStarAlgHom_apply_gnsVector (a : A) :
    f.gnsStarAlgHom a f.gnsVector = f.gnsMk a :=
  f.gnsNonUnitalStarAlgHom_apply_gnsVector a

/-- In the unital case the cyclic vector is the class of the unit: `ξ_f = [1]`. -/
lemma gnsVector_eq_gnsMk_one : f.gnsVector = f.gnsMk 1 := by
  rw [← f.gnsStarAlgHom_apply_gnsVector 1, map_one, one_apply_eq_self]

/-- Cyclicity of `ξ_f` for the unital GNS representation. -/
lemma denseRange_gnsStarAlgHom_apply_gnsVector :
    DenseRange fun a => f.gnsStarAlgHom a f.gnsVector :=
  f.denseRange_gnsNonUnitalStarAlgHom_apply_gnsVector

/-- The GNS identity `f a = ⟪ξ_f, π_f a ξ_f⟫`, for the unital GNS representation. -/
lemma apply_eq_inner_gnsStarAlgHom_gnsVector (a : A) :
    f a = ⟪f.gnsVector, f.gnsStarAlgHom a f.gnsVector⟫_ℂ :=
  f.apply_eq_inner_gnsNonUnitalStarAlgHom_gnsVector a

/-- `⟪ζ_f, π_f a ζ_f⟫ = ‖f‖ₒₚ⁻¹ f a`, for the unital GNS representation. -/
lemma inner_gnsStarAlgHom_normalize_gnsVector (a : A) :
    ⟪NormedSpace.normalize f.gnsVector,
      f.gnsStarAlgHom a (NormedSpace.normalize f.gnsVector)⟫_ℂ = (‖f‖ₒₚ⁻¹ : ℝ) * f a :=
  f.inner_gnsNonUnitalStarAlgHom_normalize_gnsVector a

/-- Cyclicity of `ζ_f`, for the unital GNS representation. -/
lemma denseRange_gnsStarAlgHom_apply_normalize_gnsVector :
    DenseRange fun a => f.gnsStarAlgHom a (NormedSpace.normalize f.gnsVector) :=
  f.denseRange_gnsNonUnitalStarAlgHom_apply_normalize_gnsVector

/-- `‖f‖ₒₚ = f 1`: Mathlib's `PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one`. -/
lemma ofReal_opNorm_eq_map_one : (‖f‖ₒₚ : ℂ) = f 1 :=
  PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one _

/-- `‖ξ_f‖² = f 1`. -/
lemma ofReal_norm_gnsVector_sq : ((‖f.gnsVector‖ ^ 2 : ℝ) : ℂ) = f 1 := by
  rw [norm_gnsVector_sq, ofReal_opNorm_eq_map_one]

end Unital

end PositiveLinearMap
