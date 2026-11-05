/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.Unitization

/-!
# Positivity in a non-unital C⋆-algebra through the norm in the unitization

A self-adjoint `a` with `‖a‖ ≤ t` in a non-unital C⋆-algebra `A` is positive if and only if
`‖t - a‖ ≤ t` in the unitization `A⁺¹` (`CStarAlgebra.nonneg_iff_nnnorm_algebraMap_sub_inr_le`).
For positive `a`, it follows that `‖t s - a s‖ ≤ t ‖s‖` for every `s` in `A`
(`CStarAlgebra.nnnorm_smul_sub_mul_le`), as `t s - a s = (t - a) s` in `A⁺¹`. The bound tests the
positivity of `a` on a subspace through the products `a s` alone, which is what the Choi–Effros
product needs in `QuantumSystem.Analysis.CStarAlgebra.ChoiEffros`.

## Main results

* `CStarAlgebra.nonneg_iff_nnnorm_algebraMap_sub_inr_le` — positivity through the norm in the
  unitization.
* `CStarAlgebra.nnnorm_smul_sub_mul_le` — the bound `‖t s - a s‖ ≤ t ‖s‖` for positive `a`.
-/

@[expose] public section

open scoped CStarAlgebra NNReal

namespace CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- In a non-unital C⋆-algebra, a self-adjoint `a` with `‖a‖ ≤ t` is positive if and only if
`‖t - a‖ ≤ t` in the unitization: the spectrum of `a` lies in `[-t, t]`, and in `[0, t]` exactly when
that of `t - a` lies in `[0, t]`. -/
lemma nonneg_iff_nnnorm_algebraMap_sub_inr_le {a : A} (ha : IsSelfAdjoint a) {t : ℝ≥0}
    (ht : ‖a‖₊ ≤ t) : 0 ≤ a ↔ ‖algebraMap ℝ A⁺¹ t - a‖₊ ≤ t := by
  rw [← Unitization.inr_nonneg_iff, nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts,
    quasispectrumRestricts_iff_spectrumRestricts,
    ← SpectrumRestricts.nnreal_iff_nnnorm (ha.inr ℂ) (by rwa [Unitization.nnnorm_inr])]
  exact and_iff_right (ha.inr ℂ)

/-- For `0 ≤ a` with `‖a‖ ≤ t`, `‖t s - a s‖ ≤ t ‖s‖`: in the unitization, `t s - a s = (t - a) s`
and `‖t - a‖ ≤ t` (`CStarAlgebra.nonneg_iff_nnnorm_algebraMap_sub_inr_le`). -/
lemma nnnorm_smul_sub_mul_le {a : A} (ha : 0 ≤ a) {t : ℝ≥0} (ht : ‖a‖₊ ≤ t) (s : A) :
    ‖algebraMap ℝ ℂ t • s - a * s‖₊ ≤ t * ‖s‖₊ := by
  have h := (nonneg_iff_nnnorm_algebraMap_sub_inr_le (.of_nonneg ha) ht).mp ha
  have hs : ((algebraMap ℝ ℂ t • s - a * s : A) : A⁺¹) = (algebraMap ℝ A⁺¹ t - a) * s := by
    rw [sub_mul, Unitization.inr_sub, Unitization.inr_mul, Unitization.algebraMap_eq_inl_comp,
      Function.comp_apply, Unitization.inl_mul_inr]
  rw [← Unitization.nnnorm_inr (𝕜 := ℂ), hs, ← Unitization.nnnorm_inr (𝕜 := ℂ) s]
  exact (nnnorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right h (by simp))

end CStarAlgebra
