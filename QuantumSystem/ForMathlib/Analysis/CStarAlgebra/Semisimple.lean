/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Jacobson.Ideal

/-!
# Semisimplicity of C⋆-algebras

The Jacobson radical of a unital C⋆-algebra is zero: an element `x` of the radical makes `x⋆x`
quasi-nilpotent, and a self-adjoint element has norm equal to its spectral radius. A
finite-dimensional C⋆-algebra is Artinian, so it is a semisimple ring.

## Main results

* `Ring.isUnit_one_add_of_mem_jacobson`: `1 + u` is a unit for `u` in the Jacobson radical of a
  ring.
* **`CStarAlgebra.jacobson_eq_bot`**: the Jacobson radical of a C⋆-algebra is zero.
* `CStarAlgebra.isSemisimpleRing`: a finite-dimensional C⋆-algebra is a semisimple ring.
-/

@[expose] public section

/-- In any ring, `1 + u` is a unit for `u` in the Jacobson radical. -/
lemma Ring.isUnit_one_add_of_mem_jacobson {R : Type*} [Ring R] {u : R}
    (hu : u ∈ Ring.jacobson R) : IsUnit (1 + u) := by
  have key (v : R) (hv : v ∈ Ring.jacobson R) : ∃ z, z * (1 + v) = 1 := by
    have hv' : v ∈ (⊥ : Ideal R).jacobson := by
      simpa [Ideal.jacobson, Ring.jacobson_eq_sInf_isMaximal] using hv
    obtain ⟨z, hz⟩ := Ideal.mem_jacobson_iff.mp hv' 1
    refine ⟨z, ?_⟩
    rw [Ideal.mem_bot, sub_eq_zero] at hz
    rw [mul_add, mul_one, ← hz, mul_one, add_comm]
  -- a left inverse `z` of `1 + u` is itself of the form `1 + v`, so it has a left inverse
  obtain ⟨z, hz⟩ := key u hu
  obtain ⟨w, hw⟩ := key (-(z * u)) (neg_mem (Ideal.mul_mem_left _ z hu))
  have hz' : 1 + -(z * u) = z := by
    rw [← hz, mul_add, mul_one, add_neg_cancel_right]
  rw [hz'] at hw
  have hwu : w = 1 + u :=
    calc w = w * (z * (1 + u)) := by rw [hz, mul_one]
      _ = 1 + u := by rw [← mul_assoc, hw, one_mul]
  exact ⟨⟨1 + u, z, by rw [← hwu, hw], hz⟩, rfl⟩

/-- The Jacobson radical of a C⋆-algebra is zero. -/
theorem CStarAlgebra.jacobson_eq_bot (A : Type*) [CStarAlgebra A] : Ring.jacobson A = ⊥ := by
  refine eq_bot_iff.mpr fun x hx ↦ ?_
  rw [Ideal.mem_bot]
  have ha : star x * x ∈ Ring.jacobson A := Ideal.mul_mem_left _ _ hx
  have hspec : ∀ μ ∈ quasispectrum ℂ (star x * x), μ = 0 := by
    intro μ hμ
    by_contra h0
    rw [quasispectrum_eq_spectrum_union_zero, Set.mem_union, Set.mem_singleton_iff,
      or_iff_left h0] at hμ
    refine (spectrum.mem_iff.mp hμ) ?_
    have hu := Ring.isUnit_one_add_of_mem_jacobson
      (Ideal.mul_mem_left _ (algebraMap ℂ A (-μ⁻¹)) ha)
    have : algebraMap ℂ A μ - star x * x =
        algebraMap ℂ A μ * (1 + algebraMap ℂ A (-μ⁻¹) * (star x * x)) := by
      rw [mul_add, mul_one, ← mul_assoc, ← map_mul, mul_neg, mul_inv_cancel₀ h0, map_neg, map_one,
        neg_one_mul, sub_eq_add_neg]
    rw [this]
    exact ((isUnit_iff_ne_zero.mpr h0).map (algebraMap ℂ A)).mul hu
  have hr : spectralRadius ℂ (star x * x) = 0 :=
    le_antisymm (iSup₂_le fun μ hμ ↦ by simp [hspec μ hμ]) bot_le
  rw [(IsSelfAdjoint.star_mul_self x).spectralRadius_eq_nnnorm, ENNReal.coe_eq_zero,
    nnnorm_eq_zero] at hr
  exact star_mul_self_eq_zero.mp hr

/-- A finite-dimensional C⋆-algebra is a semisimple ring. -/
instance CStarAlgebra.isSemisimpleRing (A : Type*) [CStarAlgebra A] [FiniteDimensional ℂ A] :
    IsSemisimpleRing A :=
  have : IsArtinianRing A := IsArtinianRing.of_finite ℂ A
  IsArtinianRing.isSemisimpleRing_iff_jacobson.mpr (CStarAlgebra.jacobson_eq_bot A)
