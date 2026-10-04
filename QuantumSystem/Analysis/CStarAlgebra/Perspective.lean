/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.CStarAlgebra.OperatorConvex
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.RpowCommute

/-!
# Joint convexity of the noncommutative perspective

For a real function `f` and elements `l`, `r` of a unital C⋆-algebra with `r` strictly positive,
the **(noncommutative) perspective** of `f` is
`P_f(l, r) = r^{1/2} f(r^{-1/2} l r^{-1/2}) r^{1/2}`.
For commuting `l` and `r` it reduces to the classical perspective `f(l r⁻¹) r` of `f`.

The perspective of an operator convex function is jointly convex. Effros (2009) proved this for
commuting `l` and `r`; Ebadian, Nikoufar and Eshaghi Gordji (2011) and Effros and Hansen (2014)
proved it without commutativity. With `f(t) = -tᵖ` and the commuting left and right
multiplication operators on the Hilbert–Schmidt operators, it yields Lieb's concavity theorem
(Effros 2009).

## Main definitions

* `CFC.perspective f l r`: the perspective `r^{1/2} f(r^{-1/2} l r^{-1/2}) r^{1/2}`.

## Main results

* `IsOperatorConvexOn.perspective_sum_le`: **joint convexity of the perspective**, Jensen's
  inequality for the
  perspective of an operator convex `f` over finite convex combinations of pairs `(lᵢ, rᵢ)`
  with `rᵢ` strictly positive.
* `IsOperatorConvexOn.perspective_sum_le_of_nonneg`: the case of `f` operator convex on `[0, ∞)`
  and `lᵢ` positive; `IsOperatorConvexOn.perspective_sum_le_of_isStrictlyPositive`: the case of
  `f` operator convex on `(0, ∞)` (such as `-log` and `t⁻¹`) and `lᵢ` strictly positive.
* `IsOperatorConvexOn.convexOn_perspective`: for `f` operator convex on `[0, ∞)`, the perspective
  is jointly convex on pairs `(l, r)` with `l` positive and `r` strictly positive.
* `CFC.perspective_neg_rpow_of_commute`: for commuting strictly positive `l` and `r`, the
  perspective of `-tᵖ` is `-(lᵖ r¹⁻ᵖ)`.

## Implementation notes

The proof is the one of Effros, through Jensen's operator inequality of Hansen and Pedersen; it
does not use commutativity and only uses the C⋆-algebra structure: with `r = ∑ wᵢ rᵢ` and
`aᵢ = √wᵢ rᵢ^{1/2} r^{-1/2}`, one has `∑ aᵢ⋆ aᵢ = 1` and
`∑ aᵢ⋆ (rᵢ^{-1/2} lᵢ rᵢ^{-1/2}) aᵢ = r^{-1/2} l r^{-1/2}`, so `IsOperatorConvexOn.cfc_sum_le`
applies, and conjugating by `r^{1/2}` gives the inequality.

## References

* E. G. Effros, *A matrix convexity approach to some celebrated quantum inequalities*,
  Proc. Natl. Acad. Sci. USA 106 (2009), 1006–1008
* A. Ebadian, I. Nikoufar, M. Eshaghi Gordji, *Perspectives of matrix convex functions*,
  Proc. Natl. Acad. Sci. USA 108 (2011), 7313–7314
* E. G. Effros, F. Hansen, *Non-commutative perspectives*, Ann. Funct. Anal. 5 (2014), 74–79
* F. Hansen, G. K. Pedersen, *Jensen's operator inequality*, Bull. London Math. Soc. 35 (2003),
  553–564
-/

@[expose] public section

open Set

universe u v

namespace CFC

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The **noncommutative perspective** `r^{1/2} f(r^{-1/2} l r^{-1/2}) r^{1/2}` of a real
function `f`, meaningful for `r` strictly positive (Effros–Hansen 2014). -/
noncomputable def perspective (f : ℝ → ℝ) (l r : A) : A :=
  r ^ (1 / 2 : ℝ) * cfc f (r ^ (-1 / 2 : ℝ) * l * r ^ (-1 / 2 : ℝ)) * r ^ (1 / 2 : ℝ)

/-- `r^{1/2} r^{1/2} = r` for `r` positive: Mathlib's `CFC.sqrt_mul_sqrt_self`. -/
lemma rpow_half_mul_rpow_half {r : A} (hr : 0 ≤ r) : r ^ (1 / 2 : ℝ) * r ^ (1 / 2 : ℝ) = r := by
  rw [← sqrt_eq_rpow, sqrt_mul_sqrt_self r hr]

/-- `r^{1/2} r^{-1/2} = 1` for `r` strictly positive. -/
lemma rpow_half_mul_rpow_neg_half {r : A} (hr : IsStrictlyPositive r) :
    r ^ (1 / 2 : ℝ) * r ^ (-1 / 2 : ℝ) = 1 := by
  rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring]
  exact rpow_mul_rpow_neg _ hr

/-- `r^{-1/2} r^{1/2} = 1` for `r` strictly positive. -/
lemma rpow_neg_half_mul_rpow_half {r : A} (hr : IsStrictlyPositive r) :
    r ^ (-1 / 2 : ℝ) * r ^ (1 / 2 : ℝ) = 1 := by
  rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring]
  exact rpow_neg_mul_rpow _ hr

/-- `r^{-1/2} r r^{-1/2} = 1` for `r` strictly positive. -/
lemma rpow_neg_half_mul_mul_rpow_neg_half {r : A} (hr : IsStrictlyPositive r) :
    r ^ (-1 / 2 : ℝ) * r * r ^ (-1 / 2 : ℝ) = 1 := by
  calc r ^ (-1 / 2 : ℝ) * r * r ^ (-1 / 2 : ℝ)
      = r ^ (-1 / 2 : ℝ) * (r ^ (1 / 2 : ℝ) * r ^ (1 / 2 : ℝ)) * r ^ (-1 / 2 : ℝ) := by
        rw [rpow_half_mul_rpow_half hr.nonneg]
    _ = (r ^ (-1 / 2 : ℝ) * r ^ (1 / 2 : ℝ)) * (r ^ (1 / 2 : ℝ) * r ^ (-1 / 2 : ℝ)) := by
        simp only [mul_assoc]
    _ = 1 := by rw [rpow_neg_half_mul_rpow_half hr, rpow_half_mul_rpow_neg_half hr, one_mul]

/-- A convex combination of strictly positive elements is strictly positive. -/
lemma _root_.IsStrictlyPositive.sum_smul {ι : Type*} [Fintype ι] {w : ι → ℝ} {r : ι → A}
    (hw : ∀ i, 0 ≤ w i) (hw₁ : ∑ i, w i = 1) (hr : ∀ i, IsStrictlyPositive (r i)) :
    IsStrictlyPositive (∑ i, w i • r i) := by
  classical
  obtain ⟨j, -, hj⟩ : ∃ j ∈ Finset.univ, w j ≠ 0 := by
    by_contra! h
    simp [Finset.sum_eq_zero h] at hw₁
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  exact ((hr j).smul (lt_of_le_of_ne (hw j) (Ne.symm hj))).add_nonneg
    (Finset.sum_nonneg fun i _ => smul_nonneg (hw i) (hr i).nonneg)

omit [PartialOrder A] [StarOrderedRing A] in
/-- Conjugating `star a * y * a` by `t` when `t a⋆ = c • u` and `a t = c • u`. -/
private lemma conj_star_mul_mul {t a u y : A} {c : ℝ} (h₁ : t * star a = c • u)
    (h₂ : a * t = c • u) : t * (star a * y * a) * t = (c * c) • (u * y * u) := by
  calc t * (star a * y * a) * t = (t * star a) * y * (a * t) := by simp only [mul_assoc]
    _ = (c * c) • (u * y * u) := by
      rw [h₁, h₂]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul]

end CFC

open CFC

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {s : Set ℝ} {f : ℝ → ℝ}

/-- **Joint convexity of the perspective** (Effros–Hansen 2014): the perspective
`P_f(l, r) = r^{1/2} f(r^{-1/2} l r^{-1/2}) r^{1/2}` of an operator convex function `f` satisfies
Jensen's inequality over finite convex combinations of pairs `(lᵢ, rᵢ)` with `rᵢ` strictly
positive and `rᵢ^{-1/2} lᵢ rᵢ^{-1/2}` in the domain of `f`. -/
theorem IsOperatorConvexOn.perspective_sum_le (hf : IsOperatorConvexOn.{v} s f) {ι : Type*}
    [Fintype ι] {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw₁ : ∑ i, w i = 1) {l r : ι → A}
    (hr : ∀ i, IsStrictlyPositive (r i))
    (hl : ∀ i, r i ^ (-1 / 2 : ℝ) * l i * r i ^ (-1 / 2 : ℝ) ∈
      {b : A | IsSelfAdjoint b ∧ spectrum ℝ b ⊆ s}) :
    perspective f (∑ i, w i • l i) (∑ i, w i • r i) ≤ ∑ i, w i • perspective f (l i) (r i) := by
  set R := ∑ i, w i • r i
  have hR : IsStrictlyPositive R := IsStrictlyPositive.sum_smul hw hw₁ hr
  have hsa : ∀ (x : A) (y : ℝ), star (x ^ y) = x ^ y := fun x y =>
    (IsSelfAdjoint.of_nonneg rpow_nonneg).star_eq
  set a : ι → A := fun i => Real.sqrt (w i) • (r i ^ (1 / 2 : ℝ) * R ^ (-1 / 2 : ℝ))
  set x : ι → A := fun i => r i ^ (-1 / 2 : ℝ) * l i * r i ^ (-1 / 2 : ℝ)
  have hstar : ∀ i, star (a i) = Real.sqrt (w i) • (R ^ (-1 / 2 : ℝ) * r i ^ (1 / 2 : ℝ)) :=
    fun i => by simp [a, star_smul, hsa]
  have hsqrt : ∀ i, Real.sqrt (w i) * Real.sqrt (w i) = w i := fun i => Real.mul_self_sqrt (hw i)
  have hsum : ∑ i, star (a i) * a i = 1 := by
    calc ∑ i, star (a i) * a i = ∑ i, w i • (R ^ (-1 / 2 : ℝ) * r i * R ^ (-1 / 2 : ℝ)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hstar, smul_mul_smul_comm, hsqrt]
          congr 1
          rw [mul_assoc, ← mul_assoc (r i ^ (1 / 2 : ℝ)), rpow_half_mul_rpow_half (hr i).nonneg,
            ← mul_assoc]
      _ = R ^ (-1 / 2 : ℝ) * R * R ^ (-1 / 2 : ℝ) := by
          rw [Finset.mul_sum, Finset.sum_mul]
          simp only [mul_smul_comm, smul_mul_assoc]
      _ = 1 := rpow_neg_half_mul_mul_rpow_neg_half hR
  have hinner : ∑ i, star (a i) * x i * a i =
      R ^ (-1 / 2 : ℝ) * (∑ i, w i • l i) * R ^ (-1 / 2 : ℝ) := by
    calc ∑ i, star (a i) * x i * a i = ∑ i, w i • (R ^ (-1 / 2 : ℝ) * l i * R ^ (-1 / 2 : ℝ)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [hstar, a, x, smul_mul_assoc, mul_smul_comm, smul_smul, hsqrt]
          congr 1
          simp only [mul_assoc]
          rw [← mul_assoc (r i ^ (1 / 2 : ℝ)), rpow_half_mul_rpow_neg_half (hr i), one_mul,
            ← mul_assoc (r i ^ (-1 / 2 : ℝ)), rpow_neg_half_mul_rpow_half (hr i), one_mul]
      _ = R ^ (-1 / 2 : ℝ) * (∑ i, w i • l i) * R ^ (-1 / 2 : ℝ) := by
          rw [Finset.mul_sum, Finset.sum_mul]
          simp only [mul_smul_comm, smul_mul_assoc]
  have hJ := ((isOperatorConvexOn_congr_universe.{v, u}).1 hf).cfc_sum_le a x hl hsum
  rw [hinner] at hJ
  have hconj := star_left_conjugate_le_conjugate hJ (R ^ (1 / 2 : ℝ))
  rw [hsa] at hconj
  refine hconj.trans_eq ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [conj_star_mul_mul (u := r i ^ (1 / 2 : ℝ)) (c := Real.sqrt (w i)), hsqrt]
  · rfl
  · rw [hstar, mul_smul_comm, ← mul_assoc, rpow_half_mul_rpow_neg_half hR, one_mul]
  · simp only [a, smul_mul_assoc, mul_assoc, rpow_neg_half_mul_rpow_half hR, mul_one]

/-- **Joint convexity of the perspective** for `f` operator convex on `[0, ∞)`: Jensen's
inequality for the perspective over finite convex combinations of pairs `(lᵢ, rᵢ)` with `lᵢ`
positive and `rᵢ` strictly positive. -/
theorem IsOperatorConvexOn.perspective_sum_le_of_nonneg (hf : IsOperatorConvexOn.{v} (Ici 0) f)
    {ι : Type*} [Fintype ι] {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw₁ : ∑ i, w i = 1) {l r : ι → A}
    (hl : ∀ i, 0 ≤ l i) (hr : ∀ i, IsStrictlyPositive (r i)) :
    perspective f (∑ i, w i • l i) (∑ i, w i • r i) ≤ ∑ i, w i • perspective f (l i) (r i) := by
  refine hf.perspective_sum_le hw hw₁ hr fun i => ?_
  have h0 : 0 ≤ r i ^ (-1 / 2 : ℝ) * l i * r i ^ (-1 / 2 : ℝ) := by
    simpa [(IsSelfAdjoint.of_nonneg (rpow_nonneg (a := r i) (y := -1 / 2))).star_eq] using
      star_left_conjugate_nonneg (hl i) (r i ^ (-1 / 2 : ℝ))
  exact ⟨IsSelfAdjoint.of_nonneg h0, fun x hx => spectrum_nonneg_of_nonneg h0 hx⟩

/-- **Joint convexity of the perspective** for `f` operator convex on `(0, ∞)`, such as `-log`
and `t⁻¹`: Jensen's inequality for the perspective over finite convex combinations of pairs
`(lᵢ, rᵢ)` of strictly positive elements. -/
theorem IsOperatorConvexOn.perspective_sum_le_of_isStrictlyPositive
    (hf : IsOperatorConvexOn.{v} (Ioi 0) f) {ι : Type*} [Fintype ι] {w : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hw₁ : ∑ i, w i = 1) {l r : ι → A}
    (hl : ∀ i, IsStrictlyPositive (l i)) (hr : ∀ i, IsStrictlyPositive (r i)) :
    perspective f (∑ i, w i • l i) (∑ i, w i • r i) ≤ ∑ i, w i • perspective f (l i) (r i) := by
  refine hf.perspective_sum_le hw hw₁ hr fun i => ?_
  have hpos : IsStrictlyPositive (r i ^ (-1 / 2 : ℝ) * l i * r i ^ (-1 / 2 : ℝ)) :=
    IsStrictlyPositive.conjugate_of_isUnit_of_isSelfAdjoint _ _
      (IsStrictlyPositive.rpow (r i) _ (hr i)).isUnit
      (IsSelfAdjoint.of_nonneg rpow_nonneg) (hl i)
  exact ⟨hpos.isSelfAdjoint, fun x hx => hpos.spectrum_pos hx⟩

/-- **Joint convexity of the perspective** (Effros–Hansen 2014): for `f` operator convex on
`[0, ∞)`, `(l, r) ↦ r^{1/2} f(r^{-1/2} l r^{-1/2}) r^{1/2}` is jointly convex on pairs with `l`
positive and `r` strictly positive. -/
theorem IsOperatorConvexOn.convexOn_perspective (hf : IsOperatorConvexOn.{v} (Ici 0) f) :
    ConvexOn ℝ {x : A × A | 0 ≤ x.1 ∧ IsStrictlyPositive x.2} (fun x => perspective f x.1 x.2) := by
  have hw {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : ∀ i, 0 ≤ (![a, b] : Fin 2 → ℝ) i := by
    intro i; fin_cases i <;> simpa
  refine ⟨fun x hx y hy a b ha hb hab => ⟨?_, ?_⟩, fun x hx y hy a b ha hb hab => ?_⟩
  · exact add_nonneg (smul_nonneg ha hx.1) (smul_nonneg hb hy.1)
  · simpa [Fin.sum_univ_two] using IsStrictlyPositive.sum_smul (w := ![a, b]) (r := ![x.2, y.2])
      (hw ha hb) (by simpa using hab) fun i => by fin_cases i <;> simp [hx.2, hy.2]
  have := hf.perspective_sum_le_of_nonneg (w := ![a, b]) (l := ![x.1, y.1]) (r := ![x.2, y.2])
    (hw ha hb) (by simpa using hab) (fun i => by fin_cases i <;> simp [hx.1, hy.1])
    fun i => by fin_cases i <;> simp [hx.2, hy.2]
  simpa [Fin.sum_univ_two] using this

namespace CFC

/-- For commuting strictly positive `l` and `r`, the perspective of `f(t) = -tᵖ` is the
two-variable power `-(lᵖ r¹⁻ᵖ)`. -/
lemma perspective_neg_rpow_of_commute {l r : A} (hlr : Commute l r) (p : ℝ)
    (hl : IsStrictlyPositive l) (hr : IsStrictlyPositive r) :
    perspective (fun t => -t ^ p) l r = -(l ^ p * r ^ (1 - p)) := by
  have hcomm : ∀ y : ℝ, Commute l (r ^ y) := fun y => (Commute.cfc_nnreal hlr.symm _).symm
  have hrr : r ^ (-1 / 2 : ℝ) * r ^ (-1 / 2 : ℝ) = r ^ (-1 : ℝ) := by
    rw [← rpow_add hr.isUnit]; norm_num
  have hx : r ^ (-1 / 2 : ℝ) * l * r ^ (-1 / 2 : ℝ) = l * r ^ (-1 : ℝ) := by
    rw [(hcomm _).symm.eq, mul_assoc, hrr]
  have hpos : IsStrictlyPositive (l * r ^ (-1 : ℝ)) :=
    Commute.isStrictlyPositive_mul (hcomm _) hl (IsStrictlyPositive.rpow r _ hr)
  have hpow : (l * r ^ (-1 : ℝ)) ^ p = l ^ p * r ^ (-p) := by
    rw [mul_rpow_of_commute (hcomm _) p hl (IsStrictlyPositive.rpow r _ hr),
      rpow_rpow r _ _ (by norm_num) hr, neg_one_mul]
  have hcfc : cfc (fun t : ℝ => -t ^ p) (l * r ^ (-1 : ℝ)) = -(l * r ^ (-1 : ℝ)) ^ p := by
    rw [cfc_neg (fun t : ℝ => t ^ p), rpow_eq_cfc_real hpos.nonneg]
  have hcommp : Commute (l ^ p) (r ^ (1 / 2 : ℝ)) := Commute.cfc_nnreal (hcomm _) _
  rw [perspective, hx, hcfc, hpow, mul_neg, neg_mul, ← mul_assoc, hcommp.symm.eq]
  simp only [mul_assoc]
  rw [← rpow_add hr.isUnit, ← rpow_add hr.isUnit]
  congr 3
  ring

end CFC
