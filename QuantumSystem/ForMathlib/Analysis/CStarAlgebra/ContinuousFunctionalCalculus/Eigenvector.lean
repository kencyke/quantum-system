/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# The continuous functional calculus on eigenvectors

For a normal operator `a` on a complex Hilbert space and an eigenvector `u` with `a u = ζ u`, the
continuous functional calculus acts on `u` as multiplication by the value at the eigenvalue:
`cfc f a u = f ζ • u`. The proof runs the Stone–Weierstrass induction over `C(σ(a), ℂ)`; the
`star` case uses that `u` is also an eigenvector of `a†`, for `ζ̄`, by normality.

For a self-adjoint operator the same holds for the real calculus, `cfc f a u = f r • u` with
`f : ℝ → ℝ`. On a finite-dimensional space the real spectrum is finite, so every `f` (in particular
`Real.log`, discontinuous at `0`) is continuous on it, and an orthonormal eigenbasis `b` of `a` with
eigenvalues `r` computes traces and quadratic forms: `tr (A ∘ cfc f a) = Σᵢ f(rᵢ) ⟪bᵢ, A bᵢ⟫` and
`⟪x, a x⟫ = Σᵢ rᵢ ‖⟪bᵢ, x⟫‖²`. The eigenbasis is arbitrary, not Mathlib's chosen
`LinearMap.IsSymmetric.eigenvectorBasis`, so that product and block bases can be used.

## Main results

* `ContinuousLinearMap.mem_spectrum_of_apply_eq_smul` — an eigenvalue lies in the spectrum.
* `IsStarNormal.sub_algebraMap` — `a - ζ` is normal for normal `a`.
* `ContinuousLinearMap.IsStarNormal.adjoint_apply_eq_conj_smul` — `a u = ζ u` implies
  `a† u = ζ̄ u` for normal `a`.
* `ContinuousLinearMap.cfc_apply_of_apply_eq_smul` — `a u = ζ u` implies `cfc f a u = f ζ • u`.
* `ContinuousLinearMap.cfc_apply_of_apply_eq_ofReal_smul` — the real calculus of a self-adjoint
  operator on an eigenvector.
* `ContinuousLinearMap.finite_spectrum_real` — a self-adjoint operator on a finite-dimensional space
  has finite real spectrum.
* `ContinuousLinearMap.inner_apply_self_eq_sum`, `ContinuousLinearMap.trace_comp_eq_sum`,
  `ContinuousLinearMap.trace_comp_cfc_eq_sum` — quadratic forms and traces in an orthonormal
  eigenbasis.
-/

@[expose] public section

open scoped ComplexConjugate InnerProductSpace

/-- A normal element of a star algebra over `ℂ`, shifted by a scalar, is normal. -/
theorem IsStarNormal.sub_algebraMap {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
    [StarModule ℂ A] {a : A} (ha : IsStarNormal a) (ζ : ℂ) :
    IsStarNormal (a - algebraMap ℂ A ζ) := by
  refine ⟨?_⟩
  rw [star_sub, ← algebraMap_star_comm]
  exact (ha.star_comm_self.sub_right (Algebra.commute_algebraMap_right _ _)).sub_left
    ((Algebra.commute_algebraMap_left _ _).sub_right (Algebra.commute_algebraMap_left _ _))

namespace ContinuousLinearMap

/-- An eigenvalue of a bounded operator lies in its spectrum. (On a Banach space this also
follows from `ContinuousLinearMap.spectrum_eq` and `Module.End.HasEigenvalue.mem_spectrum`; the
direct proof here needs no completeness.) -/
theorem mem_spectrum_of_apply_eq_smul {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {a : E →L[𝕜] E} {u : E} {ζ : 𝕜} (hu : a u = ζ • u)
    (hu0 : u ≠ 0) : ζ ∈ spectrum 𝕜 a := by
  rw [spectrum.mem_iff]
  intro hunit
  apply hu0
  have h0 : (algebraMap 𝕜 (E →L[𝕜] E) ζ - a) u = 0 := by
    rw [sub_apply, Algebra.algebraMap_eq_smul_one, smul_apply, one_apply_eq_self, hu, sub_self]
  calc u = (↑hunit.unit⁻¹ * (algebraMap 𝕜 (E →L[𝕜] E) ζ - a)) u := by
        rw [hunit.val_inv_mul, one_apply_eq_self]
    _ = 0 := by rw [mul_apply_eq_comp, h0, map_zero]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {a : E →L[ℂ] E} {u : E} {ζ : ℂ}

/-- An eigenvector of a normal operator `a` for `ζ` is an eigenvector of `a†` for `ζ̄`. -/
theorem IsStarNormal.adjoint_apply_eq_conj_smul (ha : IsStarNormal a) (hu : a u = ζ • u) :
    adjoint a u = conj ζ • u := by
  have hb := _root_.IsStarNormal.sub_algebraMap ha ζ
  have h0 : (a - algebraMap ℂ (E →L[ℂ] E) ζ) u = 0 := by
    rw [sub_apply, Algebra.algebraMap_eq_smul_one, smul_apply, one_apply_eq_self, hu, sub_self]
  have := (ContinuousLinearMap.IsStarNormal.adjoint_apply_eq_zero_iff hb u).mpr h0
  rw [← star_eq_adjoint, star_sub, ← algebraMap_star_comm, sub_apply, star_eq_adjoint,
    Algebra.algebraMap_eq_smul_one, smul_apply, one_apply_eq_self, sub_eq_zero] at this
  exact this

/-- For a normal operator `a` and an eigenvector `u` with eigenvalue `ζ`,
`cfcHom f u = f ζ • u` for every `f : C(σ(a), ℂ)`. -/
theorem cfcHom_apply_of_apply_eq_smul (ha : IsStarNormal a) (hu : a u = ζ • u)
    (hζ : ζ ∈ spectrum ℂ a) (f : C(spectrum ℂ a, ℂ)) : cfcHom ha f u = f ⟨ζ, hζ⟩ • u := by
  induction f using ContinuousMap.induction_on_of_compact with
  | const r =>
    rw [show ContinuousMap.const (spectrum ℂ a) r = algebraMap ℂ _ r from rfl, AlgHomClass.commutes,
      Algebra.algebraMap_eq_smul_one, smul_apply, one_apply_eq_self]
    rfl
  | id => rw [cfcHom_id ha, hu]; rfl
  | star_id =>
    rw [map_star, cfcHom_id ha, star_eq_adjoint, IsStarNormal.adjoint_apply_eq_conj_smul ha hu]
    rfl
  | add f g hf hg => rw [map_add, add_apply, hf, hg, ContinuousMap.add_apply, add_smul]
  | mul f g hf hg => rw [map_mul, mul_apply_eq_comp, hg, map_smul, hf, smul_smul,
      ContinuousMap.mul_apply, mul_comm]
  | frequently f hf =>
    have hcl : IsClosed {g : C(spectrum ℂ a, ℂ) | cfcHom ha g u = g ⟨ζ, hζ⟩ • u} :=
      isClosed_eq ((apply ℂ E u).continuous.comp (cfcHom_continuous ha))
        ((continuous_eval_const _).smul continuous_const)
    exact hcl.closure_subset (mem_closure_of_frequently_of_tendsto hf Filter.tendsto_id)

/-- For a normal operator `a` and an eigenvector `u` with eigenvalue `ζ`, `cfc f a u = f ζ • u`
for every `f` continuous on the spectrum of `a`. -/
theorem cfc_apply_of_apply_eq_smul (ha : IsStarNormal a) (hu : a u = ζ • u) {f : ℂ → ℂ}
    (hf : ContinuousOn f (spectrum ℂ a)) : cfc f a u = f ζ • u := by
  rcases eq_or_ne u 0 with rfl | hu0
  · rw [map_zero, smul_zero]
  rw [cfc_apply f a ha hf,
    cfcHom_apply_of_apply_eq_smul ha hu (mem_spectrum_of_apply_eq_smul hu hu0)]
  rfl

/-- For a self-adjoint operator `a` and an eigenvector `u` with real eigenvalue `r`,
`cfc f a u = f r • u` for every real function `f` continuous on the spectrum of `a`. -/
theorem cfc_apply_of_apply_eq_ofReal_smul (ha : IsSelfAdjoint a) {r : ℝ} (hu : a u = (r : ℂ) • u)
    {f : ℝ → ℝ} (hf : ContinuousOn f (spectrum ℝ a)) : cfc f a u = (f r : ℂ) • u := by
  rw [cfc_real_eq_complex f ha]
  have hmaps : Set.MapsTo Complex.re (spectrum ℂ a) (spectrum ℝ a) := fun x hx =>
    ha.spectrumRestricts.image ▸ Set.mem_image_of_mem _ hx
  refine (cfc_apply_of_apply_eq_smul ha.isStarNormal hu ?_).trans (by simp)
  exact Complex.continuous_ofReal.comp_continuousOn
    (hf.comp Complex.continuous_re.continuousOn hmaps)

/-- A self-adjoint operator on a finite-dimensional space has finite real spectrum; hence every
real function, `Real.log` included, is continuous on it (`Set.Finite.continuousOn`). -/
theorem finite_spectrum_real [FiniteDimensional ℂ E] (ha : IsSelfAdjoint a) :
    (spectrum ℝ a).Finite := by
  have h : (spectrum ℂ a).Finite := by
    rw [ContinuousLinearMap.spectrum_eq]
    exact Module.End.finite_spectrum _
  rw [← ha.spectrumRestricts.image]
  exact h.image _

variable {ι : Type*} [Fintype ι]

omit [CompleteSpace E] in
/-- In an orthonormal eigenbasis `b` of `a` with eigenvalues `r`, `⟪bᵢ, a x⟫ = rᵢ ⟪bᵢ, x⟫`. -/
theorem inner_apply_eq_mul (b : OrthonormalBasis ι ℂ E) {r : ι → ℝ}
    (hb : ∀ i, a (b i) = (r i : ℂ) • b i) (i : ι) (x : E) :
    ⟪b i, a x⟫_ℂ = (r i : ℂ) * ⟪b i, x⟫_ℂ := by
  conv_lhs => rw [← b.sum_repr' x]
  simp only [map_sum, map_smul, hb, smul_smul]
  rw [b.orthonormal.inner_right_sum _ (Finset.mem_univ i), mul_comm]

omit [CompleteSpace E] in
/-- The quadratic form in an orthonormal eigenbasis: `⟪x, a x⟫ = Σᵢ rᵢ ‖⟪bᵢ, x⟫‖²`. -/
theorem inner_apply_self_eq_sum (b : OrthonormalBasis ι ℂ E) {r : ι → ℝ}
    (hb : ∀ i, a (b i) = (r i : ℂ) • b i) (x : E) :
    ⟪x, a x⟫_ℂ = ((∑ i, r i * ‖⟪b i, x⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
  rw [← b.sum_inner_mul_inner x (a x)]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_apply_eq_mul b hb, ← inner_conj_symm, mul_left_comm, RCLike.conj_mul]
  simp

omit [CompleteSpace E] in
/-- The trace in an orthonormal eigenbasis: `tr (A ∘ a) = Σᵢ rᵢ ⟪bᵢ, A bᵢ⟫`. -/
theorem trace_comp_eq_sum [FiniteDimensional ℂ E] (b : OrthonormalBasis ι ℂ E) {r : ι → ℝ}
    (hb : ∀ i, a (b i) = (r i : ℂ) • b i) (A : E →L[ℂ] E) :
    LinearMap.trace ℂ E (A ∘L a) = ∑ i, (r i : ℂ) * ⟪b i, A (b i)⟫_ℂ := by
  rw [LinearMap.trace_eq_sum_inner _ b]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_coe, Function.comp_apply, hb,
    map_smul, inner_smul_right]

/-- The trace against the real functional calculus of a self-adjoint operator, in an orthonormal
eigenbasis: `tr (A ∘ cfc f a) = Σᵢ f(rᵢ) ⟪bᵢ, A bᵢ⟫`. No continuity of `f` is needed, the spectrum
being finite. -/
theorem trace_comp_cfc_eq_sum [FiniteDimensional ℂ E] (ha : IsSelfAdjoint a)
    (b : OrthonormalBasis ι ℂ E) {r : ι → ℝ} (hb : ∀ i, a (b i) = (r i : ℂ) • b i) (f : ℝ → ℝ)
    (A : E →L[ℂ] E) :
    LinearMap.trace ℂ E (A ∘L cfc f a) = ∑ i, (f (r i) : ℂ) * ⟪b i, A (b i)⟫_ℂ :=
  trace_comp_eq_sum b
    (fun i => cfc_apply_of_apply_eq_ofReal_smul ha (hb i) ((finite_spectrum_real ha).continuousOn f)) A

end ContinuousLinearMap
