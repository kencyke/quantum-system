/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Unital contractions are positive

A linear map `φ` between unital C⋆-algebras with `φ 1 = 1` and `‖φ x‖ ≤ ‖x‖` for every `x` sends
self-adjoint elements to self-adjoint elements and positive elements to positive elements.

* **Self-adjointness.** For self-adjoint `a` and real `r`, `z = 1 + (I r) φ(a)` is `φ(1 + (I r) a)`,
  so `‖z‖² ≤ ‖1 + (I r) a‖² = ‖1 + r² a²‖ ≤ 1 + r² ‖a‖²`. On the other hand
  `z⋆ z = 1 - r d + r² φ(a)⋆ φ(a)` with `d = I (φ(a)⋆ - φ(a))` self-adjoint, so `-r d ≤ r² ‖a‖²` for
  every real `r`; dividing by `r → 0±` gives `d = 0`.
* **Positivity.** For `0 ≤ a`, `‖‖a‖ - φ(a)‖ = ‖φ(‖a‖ - a)‖ ≤ ‖‖a‖ - a‖ ≤ ‖a‖`, which for the
  self-adjoint `φ(a)` with `‖φ(a)‖ ≤ ‖a‖` means `0 ≤ φ(a)`.

## Main results

* `isSelfAdjoint_map_of_map_one_of_norm_apply_le` — a unital contraction preserves self-adjointness.
* `map_nonneg_of_map_one_of_norm_apply_le` — **a unital contraction is positive**.
-/

@[expose] public section

open scoped ComplexOrder

variable {F A₁ A₂ : Type*} [CStarAlgebra A₁] [CStarAlgebra A₂] [PartialOrder A₁] [PartialOrder A₂]
  [StarOrderedRing A₁] [StarOrderedRing A₂] [FunLike F A₁ A₂] [LinearMapClass F ℂ A₁ A₂]

/-- The unit of a C⋆-algebra has norm at most `1`; it is `1` unless the algebra is trivial. -/
private lemma norm_one_le_one {B : Type*} [CStarAlgebra B] : ‖(1 : B)‖ ≤ 1 := by
  nontriviality B
  simp

/-- `(1 + (I r) y)⋆ (1 + (I r) y) = 1 + (I r)(y - y⋆) + r² y⋆ y`. -/
private lemma star_one_add_I_smul_mul_self {B : Type*} [CStarAlgebra B] (r : ℝ) (y : B) :
    star (1 + (Complex.I * r) • y) * (1 + (Complex.I * r) • y) =
      1 + (Complex.I * r) • (y - star y) + ((r : ℂ) ^ 2) • (star y * y) := by
  have hI : Complex.I * r * -(Complex.I * r) = (r : ℂ) ^ 2 := by
    ring_nf; rw [Complex.I_sq]; ring
  simp only [star_add, star_one, star_smul, Complex.star_def, map_mul, Complex.conj_I,
    Complex.conj_ofReal, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
    smul_add, smul_smul, neg_mul, smul_sub]
  rw [hI]
  module

/-- An element below every positive multiple of a fixed scalar is nonpositive. -/
private lemma nonpos_of_forall_le_algebraMap {B : Type*} [CStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] {y : B} {c : ℝ} (h : ∀ ε : ℝ, 0 < ε → y ≤ algebraMap ℝ B (ε * c)) :
    y ≤ 0 := by
  have hlim : Filter.Tendsto (fun ε : ℝ => algebraMap ℝ B (ε * c)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
    have : Continuous fun ε : ℝ => algebraMap ℝ B (ε * c) :=
      (algebraMapCLM ℝ B).continuous.comp (continuous_id.mul continuous_const)
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε => h ε hε)

/-- From `ε y ≤ ε² c` for every `ε > 0`, `y ≤ 0`. -/
private lemma nonpos_of_forall_smul_le_algebraMap {B : Type*} [CStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] {y : B} {c : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ε • y ≤ algebraMap ℝ B (ε ^ 2 * c)) : y ≤ 0 := by
  refine nonpos_of_forall_le_algebraMap (c := c) fun ε hε => ?_
  have h := h ε hε
  rw [show ε ^ 2 * c = ε * (ε * c) by ring, Algebra.algebraMap_eq_smul_one, mul_smul,
    ← Algebra.algebraMap_eq_smul_one] at h
  exact (smul_le_smul_iff_of_pos_left hε).mp h

omit [PartialOrder A₁] [StarOrderedRing A₁] [PartialOrder A₂] [StarOrderedRing A₂] in
/-- **A unital contraction preserves self-adjointness.** A linear map `φ` between unital
C⋆-algebras with `φ 1 = 1` and `‖φ x‖ ≤ ‖x‖` sends self-adjoint elements to self-adjoint
elements. -/
lemma isSelfAdjoint_map_of_map_one_of_norm_apply_le (φ : F) (h₁ : φ 1 = 1)
    (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖) {a : A₁} (ha : IsSelfAdjoint a) : IsSelfAdjoint (φ a) := by
  let : PartialOrder A₂ := CStarAlgebra.spectralOrder A₂
  let : StarOrderedRing A₂ := CStarAlgebra.spectralOrderedRing A₂
  set x := φ a
  set d : A₂ := Complex.I • (star x - x) with hd_def
  -- `-r d ≤ r² ‖a‖²`, from `z⋆ z ≤ ‖z‖²` for `z = 1 + (I r) x = φ(1 + (I r) a)`.
  have key (r : ℝ) : r • (-d) ≤ algebraMap ℝ A₂ (r ^ 2 * ‖a‖ ^ 2) := by
    set z : A₂ := 1 + (Complex.I * r) • x
    have hz : z = φ (1 + (Complex.I * r) • a) := by simp [z, x, map_add, map_smul, h₁]
    have hnorm : ‖z‖ ^ 2 ≤ 1 + r ^ 2 * ‖a‖ ^ 2 := by
      calc ‖z‖ ^ 2 ≤ ‖(1 : A₁) + (Complex.I * r) • a‖ ^ 2 := by rw [hz]; gcongr; exact hφ _
        _ = ‖1 + ((r : ℂ) ^ 2) • (a * a)‖ := by
          rw [sq, ← CStarRing.norm_star_mul_self, star_one_add_I_smul_mul_self, ha.star_eq,
            sub_self, smul_zero, add_zero]
        _ ≤ ‖(1 : A₁)‖ + ‖((r : ℂ) ^ 2) • (a * a)‖ := norm_add_le _ _
        _ ≤ 1 + r ^ 2 * ‖a‖ ^ 2 := by
          gcongr
          · exact norm_one_le_one
          · rw [norm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, sq ‖a‖]
            gcongr
            exact norm_mul_le _ _
    have hxx : 0 ≤ ((r : ℂ) ^ 2) • (star x * x) := by
      rw [← Complex.ofReal_pow, Complex.coe_smul]
      exact smul_nonneg (sq_nonneg r) (star_mul_self_nonneg x)
    have hrd : r • (-d) = star z * z - 1 - ((r : ℂ) ^ 2) • (star x * x) := by
      rw [star_one_add_I_smul_mul_self, hd_def, ← Complex.coe_smul, smul_neg, smul_smul]
      module
    rw [hrd]
    calc star z * z - 1 - ((r : ℂ) ^ 2) • (star x * x) ≤ star z * z - 1 := sub_le_self _ hxx
      _ ≤ algebraMap ℝ A₂ (‖z‖ ^ 2) - algebraMap ℝ A₂ 1 := by
          rw [map_one]
          gcongr
          exact CStarAlgebra.star_mul_le_algebraMap_norm_sq z
      _ ≤ algebraMap ℝ A₂ (r ^ 2 * ‖a‖ ^ 2) := by
          rw [← map_sub, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
          exact smul_le_smul_of_nonneg_right (by linarith) zero_le_one
  have hd₁ : d ≤ 0 := nonpos_of_forall_smul_le_algebraMap (c := ‖a‖ ^ 2) fun ε hε => by
    simpa [neg_smul, smul_neg] using key (-ε)
  have hd₂ : -d ≤ 0 := nonpos_of_forall_smul_le_algebraMap (c := ‖a‖ ^ 2) fun ε hε => key ε
  have hd0 : d = 0 := le_antisymm hd₁ (neg_nonpos.mp hd₂)
  have : star x - x = 0 := by simpa [hd_def, Complex.I_ne_zero] using hd0
  exact sub_eq_zero.mp this

/-- **A unital contraction is positive.** A linear map `φ` between unital C⋆-algebras with
`φ 1 = 1` and `‖φ x‖ ≤ ‖x‖` sends positive elements to positive elements. -/
theorem map_nonneg_of_map_one_of_norm_apply_le (φ : F) (h₁ : φ 1 = 1)
    (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖) {a : A₁} (ha : 0 ≤ a) : 0 ≤ φ a := by
  have hsa := isSelfAdjoint_map_of_map_one_of_norm_apply_le φ h₁ hφ (IsSelfAdjoint.of_nonneg ha)
  have hmap (t : ℝ) : φ (algebraMap ℝ A₁ t) = algebraMap ℝ A₂ t := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul,
      ← Complex.coe_smul, map_smul, h₁]
  have hres := (nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts.mp ha).2
  rw [quasispectrumRestricts_iff_spectrumRestricts,
    SpectrumRestricts.nnreal_iff_nnnorm (IsSelfAdjoint.of_nonneg ha) le_rfl] at hres
  rw [nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts, quasispectrumRestricts_iff_spectrumRestricts,
    SpectrumRestricts.nnreal_iff_nnnorm hsa (show ‖φ a‖₊ ≤ ‖a‖₊ from hφ a)]
  refine ⟨hsa, ?_⟩
  calc ‖algebraMap ℝ A₂ ‖a‖₊ - φ a‖₊ = ‖φ (algebraMap ℝ A₁ ‖a‖₊ - a)‖₊ := by rw [map_sub, hmap]
    _ ≤ ‖algebraMap ℝ A₁ ‖a‖₊ - a‖₊ := hφ _
    _ ≤ ‖a‖₊ := hres
