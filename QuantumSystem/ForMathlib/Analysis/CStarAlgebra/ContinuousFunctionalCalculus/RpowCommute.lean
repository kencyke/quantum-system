/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-!
# Real powers of commuting elements via the exponential and the logarithm

For a strictly positive element `a` of a C⋆-algebra, `a ^ p = exp (p • log a)`. Through this
identity the multiplicativity of the exponential on commuting elements transfers to the CFC
logarithm and to real powers.

## Main results

* `CFC.rpow_eq_exp_smul_log`: `a ^ p = exp (p • log a)` for `a` strictly positive.
* `CFC.log_mul_of_commute`: `log (a * b) = log a + log b` for commuting strictly positive `a`, `b`
  (a `## TODO` of Mathlib's `ExpLog/Basic.lean`).
* `Commute.isStrictlyPositive_mul`: the product of commuting strictly positive elements is
  strictly positive.
* `CFC.mul_rpow_of_commute`: `(a * b) ^ p = a ^ p * b ^ p` for commuting strictly positive `a`,
  `b`.
* `CFC.smul_rpow`: `(c • a) ^ p = c ^ p • a ^ p` for `0 ≤ c`, `0 ≤ a` and every real `p`.
* `CFC.continuousOn_rpow_of_nonneg`: `a ↦ a ^ p` is continuous on the positive elements for
  `0 ≤ p`.
* `CFC.map_rpow`: a unital `⋆`-homomorphism commutes with real powers of strictly
  positive elements; `CFC.unop_map_rpow`: the same for a `⋆`-anti-homomorphism,
  written as `φ : A →⋆ₐ[ℂ] Bᵐᵒᵖ`.
-/

@[expose] public section

open NormedSpace

namespace CFC

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The exponential of a self-adjoint element is strictly positive. -/
lemma _root_.IsSelfAdjoint.isStrictlyPositive_exp {a : A} (ha : IsSelfAdjoint a) :
    IsStrictlyPositive (exp a) :=
  let +nondep : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  (isUnit_exp a).isStrictlyPositive ha.exp_nonneg

/-- Real powers of a strictly positive element through the exponential and the logarithm:
`a ^ p = exp (p • log a)`. -/
lemma rpow_eq_exp_smul_log {a : A} (p : ℝ) (ha : IsStrictlyPositive a := by cfc_tac) :
    a ^ p = exp (p • log a) := by
  conv_lhs => rw [← exp_log a]
  rw [← real_exp_eq_normedSpace_exp (a := log a), cfc_rpow (fun x _ => Real.exp_pos x),
    ← real_exp_eq_normedSpace_exp (a := p • log a), ← cfc_comp_smul p Real.exp (log a)]
  refine cfc_congr fun x _ => ?_
  rw [← Real.exp_mul, smul_eq_mul, mul_comm]

omit [PartialOrder A] [StarOrderedRing A] in
/-- Logarithms of commuting elements commute. -/
lemma commute_log_log {a b : A} (hab : Commute a b) : Commute (log a) (log b) :=
  (Commute.cfc_real (Commute.cfc_real hab Real.log).symm Real.log).symm

/-- The logarithm turns products of commuting strictly positive elements into sums. -/
lemma log_mul_of_commute {a b : A} (hab : Commute a b) (ha : IsStrictlyPositive a := by cfc_tac)
    (hb : IsStrictlyPositive b := by cfc_tac) : log (a * b) = log a + log b := by
  let +nondep : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  have hlog : Commute (log a) (log b) := commute_log_log hab
  rw [← log_exp (log a + log b), exp_add_of_commute hlog, exp_log a, exp_log b]

/-- The product of commuting strictly positive elements is strictly positive. -/
lemma _root_.Commute.isStrictlyPositive_mul {a b : A} (hab : Commute a b)
    (ha : IsStrictlyPositive a) (hb : IsStrictlyPositive b) : IsStrictlyPositive (a * b) :=
  (ha.isUnit.mul hb.isUnit).isStrictlyPositive (Commute.mul_nonneg ha.nonneg hb.nonneg hab)

/-- Real powers are multiplicative on commuting strictly positive elements. -/
lemma mul_rpow_of_commute {a b : A} (hab : Commute a b) (p : ℝ)
    (ha : IsStrictlyPositive a := by cfc_tac) (hb : IsStrictlyPositive b := by cfc_tac) :
    (a * b) ^ p = a ^ p * b ^ p := by
  let +nondep : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  have hlog : Commute (p • log a) (p • log b) :=
    ((commute_log_log hab).smul_left p).smul_right p
  rw [rpow_eq_exp_smul_log p (hab.isStrictlyPositive_mul ha hb), log_mul_of_commute hab, smul_add,
    exp_add_of_commute hlog, ← rpow_eq_exp_smul_log p, ← rpow_eq_exp_smul_log p]

/-- Continuity of `x ↦ xᵖ` on `ℝ≥0` passes to the dilations `d • S` of a set, `d > 0`, since
`(d x)ᵖ = dᵖ xᵖ`. -/
private lemma continuousOn_nnrpow_smul_image {p : ℝ} {d : NNReal} (hd : 0 < d) {S : Set NNReal}
    (h : ContinuousOn (fun x : NNReal => x ^ p) S) :
    ContinuousOn (fun x : NNReal => x ^ p) ((d • ·) '' S) := by
  have hg : ContinuousOn (fun y : NNReal => d ^ p * (d⁻¹ * y) ^ p) ((d • ·) '' S) :=
    continuousOn_const.mul (h.comp (continuous_const_mul _).continuousOn fun y ⟨x, hx, hxy⟩ => by
      simp only [← hxy, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hd.ne', one_mul]
      exact hx)
  refine hg.congr fun y ⟨x, _, hxy⟩ => ?_
  simp only [← hxy, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hd.ne', one_mul, NNReal.mul_rpow]

/-- Real powers are homogeneous: `(c • a) ^ p = c ^ p • a ^ p` for `0 ≤ c`, `0 ≤ a` and every real
`p`. -/
lemma smul_rpow {a : A} {c p : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a := by cfc_tac) :
    (c • a) ^ p = c ^ p • a ^ p := by
  rcases hc.eq_or_lt with rfl | hc
  · rcases eq_or_ne p 0 with rfl | hp
    · rw [zero_smul, Real.rpow_zero, one_smul, rpow_zero _ le_rfl, rpow_zero _ ha]
    · rw [zero_smul, Real.zero_rpow hp, zero_smul]
      exact zero_rpow hp
  lift c to NNReal using hc.le
  have hc' : (0 : NNReal) < c := by exact_mod_cast hc
  set f : NNReal → NNReal := fun x => x ^ p
  have hca : ((c : ℝ) • a) = c • a := (NNReal.smul_def c a).symm
  have hσ : spectrum NNReal (c • a) = (c • ·) '' spectrum NNReal a := by
    rw [Set.image_smul]
    simpa [Units.smul_def] using spectrum.unit_smul_eq_smul a (Units.mk0 c hc'.ne')
  rw [hca, rpow_def, rpow_def, ← NNReal.coe_rpow, ← NNReal.smul_def]
  by_cases h : ContinuousOn f (spectrum NNReal a)
  · rw [← cfc_comp_smul c f a (continuousOn_nnrpow_smul_image hc' h), ← cfc_const_mul _ f a h]
    exact cfc_congr fun x _ => NNReal.mul_rpow
  · have h' : ¬ ContinuousOn f (spectrum NNReal (c • a)) := fun h' => h <| by
      have := continuousOn_nnrpow_smul_image (inv_pos.2 hc') (hσ ▸ h')
      rwa [Set.image_image, show (fun x : NNReal => c⁻¹ • c • x) = id from funext fun x => by
        simp [← mul_assoc, inv_mul_cancel₀ hc'.ne'], Set.image_id] at this
    rw [cfc_apply_of_not_continuousOn _ h, cfc_apply_of_not_continuousOn _ h', smul_zero]

/-- Nonnegative real powers are continuous on the positive elements. -/
lemma continuousOn_rpow_of_nonneg {p : ℝ} (hp : 0 ≤ p) :
    ContinuousOn (fun a : A => a ^ p) {a | 0 ≤ a} := by
  rcases hp.eq_or_lt with rfl | hp
  · exact continuousOn_const.congr fun a ha => rpow_zero a ha
  · lift p to NNReal using hp.le
    exact (continuousOn_nnrpow p).congr fun a _ => (nnrpow_eq_rpow (by exact_mod_cast hp)).symm

/-- A unital `⋆`-homomorphism commutes with real powers of strictly positive
elements. -/
lemma map_rpow {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (φ : A →⋆ₐ[ℂ] B) (p : ℝ) {a : A}
    (ha : IsStrictlyPositive a := by cfc_tac) : φ (a ^ p) = φ a ^ p := by
  have hφ : Continuous φ := open scoped CStarAlgebra in map_continuous φ
  let +nondep : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  let +nondep : NormedAlgebra ℚ B := .restrictScalars ℚ ℂ B
  have hsa : IsSelfAdjoint (φ (log a)) := IsSelfAdjoint.log.map φ
  have hφa : φ a = exp (φ (log a)) := by rw [← map_exp φ hφ, exp_log a]
  have hlog : log (φ a) = φ (log a) := by rw [hφa, log_exp _ hsa]
  have hsmul : φ (p • log a) = p • φ (log a) := (φ.toLinearMap.restrictScalars ℝ).map_smul p _
  rw [rpow_eq_exp_smul_log p, map_exp φ hφ, hsmul,
    rpow_eq_exp_smul_log p (hφa ▸ hsa.isStrictlyPositive_exp), hlog]

/-- A `⋆`-anti-homomorphism, written as a `⋆`-homomorphism into the opposite algebra,
commutes with real powers of strictly positive elements. -/
lemma unop_map_rpow {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (φ : A →⋆ₐ[ℂ] Bᵐᵒᵖ) (p : ℝ) {a : A}
    (ha : IsStrictlyPositive a := by cfc_tac) :
    MulOpposite.unop (φ (a ^ p)) = MulOpposite.unop (φ a) ^ p := by
  have hφ : Continuous φ := open scoped CStarAlgebra in map_continuous φ
  let +nondep : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  let +nondep : NormedAlgebra ℚ B := .restrictScalars ℚ ℂ B
  let +nondep : NormedAlgebra ℚ Bᵐᵒᵖ := .restrictScalars ℚ ℂ Bᵐᵒᵖ
  have hexp : ∀ x : A, MulOpposite.unop (φ (exp x)) = exp (MulOpposite.unop (φ x)) := fun x => by
    rw [map_exp φ hφ, exp_unop]
  have hsa : IsSelfAdjoint (MulOpposite.unop (φ (log a))) := by
    simp [IsSelfAdjoint, ← MulOpposite.unop_star, ← map_star, IsSelfAdjoint.log.star_eq]
  have hφa : MulOpposite.unop (φ a) = exp (MulOpposite.unop (φ (log a))) := by
    rw [← hexp, exp_log a]
  have hlog : log (MulOpposite.unop (φ a)) = MulOpposite.unop (φ (log a)) := by
    rw [hφa, log_exp _ hsa]
  have hsmul : φ (p • log a) = p • φ (log a) := (φ.toLinearMap.restrictScalars ℝ).map_smul p _
  rw [rpow_eq_exp_smul_log p, hexp, hsmul, MulOpposite.unop_smul,
    rpow_eq_exp_smul_log p (hφa ▸ hsa.isStrictlyPositive_exp), hlog]

end CFC
