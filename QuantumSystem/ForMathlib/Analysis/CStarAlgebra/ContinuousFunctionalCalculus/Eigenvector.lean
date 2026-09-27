/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# The continuous functional calculus on eigenvectors

For a normal operator `a` on a complex Hilbert space and an eigenvector `u` with `a u = ζ u`, the
continuous functional calculus acts on `u` as multiplication by the value at the eigenvalue:
`cfc f a u = f ζ • u`. The proof runs the Stone–Weierstrass induction over `C(σ(a), ℂ)`; the
`star` case uses that `u` is also an eigenvector of `a†`, for `ζ̄`, by normality.

## Main results

* `ContinuousLinearMap.mem_spectrum_of_apply_eq_smul` — an eigenvalue lies in the spectrum.
* `IsStarNormal.sub_algebraMap` — `a - ζ` is normal for normal `a`.
* `ContinuousLinearMap.IsStarNormal.adjoint_apply_eq_conj_smul` — `a u = ζ u` implies
  `a† u = ζ̄ u` for normal `a`.
* `ContinuousLinearMap.cfc_apply_of_apply_eq_smul` — `a u = ζ u` implies `cfc f a u = f ζ • u`.
-/

@[expose] public section

open scoped ComplexConjugate

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

end ContinuousLinearMap
