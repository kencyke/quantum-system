/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.CStarAlgebra.Perspective
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.HilbertSchmidt
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.TraceDual
public import QuantumSystem.Notation

/-!
# Lieb's concavity theorem

For finite-dimensional complex Hilbert spaces `H` and `K`, an operator `T : H →L[ℂ] K` and
exponents `0 ≤ p`, `0 ≤ q` with `p + q ≤ 1`, the map
`(A, B) ↦ Tr (Aᵖ T† Bᑫ T)`
is jointly concave on pairs of positive operators `A` on `H` and `B` on `K` (Lieb 1973,
Theorem 1).

The trace is complex-valued and the inequalities are in the order of `ℂ` (`open scoped
ComplexOrder`): `z ≤ w` means `z.re ≤ w.re` and `z.im = w.im`. The traces here are real, since
`Tr (Aᵖ T† Bᑫ T) ≥ 0` (`ContinuousLinearMap.trace_rpow_comp_rpow_nonneg`,
`ContinuousLinearMap.trace_rpow_comp_rpow_eq_re`), so the statements are the textbook ones with
real traces.

## Main results

* `ContinuousLinearMap.lieb_concaveOn`: **Lieb's concavity theorem**.
* `ContinuousLinearMap.lieb_concavity_weighted`: its form for finite convex combinations.
* `ContinuousLinearMap.lieb_superadditive`: for `q = 1 - p`, the map is superadditive.
* `ContinuousLinearMap.trace_rpow_comp_rpow_nonneg`,
  `ContinuousLinearMap.trace_rpow_comp_rpow_eq_re`: `Tr (Aᵖ T† Bᑫ T)` is nonnegative and real.
* `ContinuousLinearMap.trace_smul_rpow_comp_smul_rpow`: the map is homogeneous of degree `p + q`.

## Notation

`Tr A` is the trace of an operator `A` (`QuantumSystem/Notation.lean`) and `T†` the adjoint
(Mathlib, `open scoped InnerProduct`). Composition `∘L` and the real power `^` have the same
precedence, so the powers are parenthesised: `(A ^ p) ∘L T† ∘L (B ^ q) ∘L T` is `Aᵖ T† Bᑫ T`.

## Proof outline

The proof follows Effros (2009).
1. On the Hilbert–Schmidt space `HilbertSchmidt H K` the right multiplication
   `𝐑[K] A : X ↦ X A` and the left multiplication `𝐋[H] B : X ↦ B X` are commuting positive
   operators that commute with real powers, and `⟪T, 𝐑[K] (Aᵖ) 𝐋[H] (Bᑫ) T⟫ = Tr (Aᵖ T† Bᑫ T)`.
2. For `q = 1 - p` and strictly positive `A`, `B`, the perspective of the operator convex `-tᵖ`
   at the commuting pair `(𝐑[K] A, 𝐋[H] B)` is `-(𝐑[K] A)ᵖ (𝐋[H] B)¹⁻ᵖ`, so the joint convexity
   of the perspective (`IsOperatorConvexOn.perspective_sum_le_of_nonneg`) gives the concavity.
3. Positive `A`, `B` are reached as the limits of `A + ε`, `B + ε`.
4. For `p + q = s ≤ 1`, the case `q = 1 - p` applied to `Aˢ`, `Bˢ` at the exponent `p / s`
   combines with the operator concavity of `t ↦ tˢ` and the Löwner–Heinz inequality.

## TODO

Extend the theorem to the trace-class operators on an infinite-dimensional Hilbert space, once
Mathlib has the trace class.

## References

* E. H. Lieb, *Convex trace functions and the Wigner–Yanase–Dyson conjecture*, Adv. Math. 11
  (1973), 267–288
* E. G. Effros, *A matrix convexity approach to some celebrated quantum inequalities*,
  Proc. Natl. Acad. Sci. USA 106 (2009), 1006–1008
-/

@[expose] public section

open Set Filter Topology CFC HilbertSchmidt
open scoped InnerProductSpace InnerProduct ComplexOrder

namespace ContinuousLinearMap

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]

/-! ### Left and right multiplication on the Hilbert–Schmidt space -/

section Multiplication

private lemma leftMul_nonneg {B : K →L[ℂ] K} (hB : 0 ≤ B) : 0 ≤ 𝐋[H] B := by
  obtain ⟨S, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB
  rw [map_mul, map_star]
  exact star_mul_self_nonneg _

private lemma unop_rightMul_nonneg {A : H →L[ℂ] H} (hA : 0 ≤ A) : 0 ≤ 𝐑[K] A := by
  obtain ⟨S, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA
  rw [map_mul, MulOpposite.unop_mul, map_star, MulOpposite.unop_star]
  exact mul_star_self_nonneg _

private lemma isStrictlyPositive_leftMul {B : K →L[ℂ] K} (hB : IsStrictlyPositive B) :
    IsStrictlyPositive (𝐋[H] B) :=
  (hB.isUnit.map (leftMul H)).isStrictlyPositive (leftMul_nonneg hB.nonneg)

private lemma isStrictlyPositive_unop_rightMul {A : H →L[ℂ] H} (hA : IsStrictlyPositive A) :
    IsStrictlyPositive (𝐑[K] A) :=
  (hA.isUnit.map (rightMul K)).unop.isStrictlyPositive (unop_rightMul_nonneg hA.nonneg)

private lemma leftMul_smul (r : ℝ) (B : K →L[ℂ] K) : 𝐋[H] (r • B) = r • 𝐋[H] B :=
  ((leftMul H : (K →L[ℂ] K) →⋆ₐ[ℂ] _).toLinearMap.restrictScalars ℝ).map_smul r B

private lemma unop_rightMul_smul (r : ℝ) (A : H →L[ℂ] H) : 𝐑[K] (r • A) = r • 𝐑[K] A := by
  rw [← MulOpposite.unop_smul]
  exact congrArg MulOpposite.unop
    (((rightMul K : (H →L[ℂ] H) →⋆ₐ[ℂ] _).toLinearMap.restrictScalars ℝ).map_smul r A)

/-- The Hilbert–Schmidt matrix coefficient of `𝐑[K] A * 𝐋[H] B` at `T` is `Tr (A T† B T)`. -/
private lemma inner_unop_rightMul_leftMul (T : H →L[ℂ] K) (A : H →L[ℂ] H) (B : K →L[ℂ] K) :
    ⟪ofCLM H K T, (𝐑[K] A * 𝐋[H] B) (ofCLM H K T)⟫_ℂ = Tr (A ∘L T† ∘L B ∘L T) := by
  rw [mul_apply_eq_comp, leftMul_ofCLM, unop_rightMul_ofCLM, inner_ofCLM_ofCLM,
    trace_comp_comm' (T† ∘L B ∘L T) A]
  simp only [comp_assoc]

/-- The quadratic form of an operator is monotone in the operator. -/
private lemma inner_le_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {X Y : E →L[ℂ] E} (h : X ≤ Y) (x : E) : ⟪x, X x⟫_ℂ ≤ ⟪x, Y x⟫_ℂ := by
  have := (nonneg_iff_isPositive.1 (sub_nonneg.2 h)).inner_nonneg_right x
  rwa [sub_apply, inner_sub_right, sub_nonneg] at this

end Multiplication

/-! ### The Lieb functional -/

section Lieb

/-- A complex inequality between nonnegative numbers follows from the inequality of real parts. -/
private lemma le_of_re_le_of_nonneg {z w : ℂ} (hz : 0 ≤ z) (hw : 0 ≤ w) (h : z.re ≤ w.re) :
    z ≤ w :=
  Complex.le_def.2 ⟨h, ((Complex.nonneg_iff.1 hz).2).symm.trans (Complex.nonneg_iff.1 hw).2⟩

/-- `Tr (X T† Y T) ≥ 0` for positive `X` and `Y`. -/
private lemma trace_comp_adjoint_comp_nonneg (T : H →L[ℂ] K) {X : H →L[ℂ] H} {Y : K →L[ℂ] K}
    (hX : 0 ≤ X) (hY : 0 ≤ Y) : 0 ≤ Tr (X ∘L T† ∘L Y ∘L T) :=
  trace_comp_nonneg hX (nonneg_iff_isPositive.2 ((nonneg_iff_isPositive.1 hY).adjoint_conj T))

/-- `Tr (X T† Y T)` is monotone in positive `X` and `Y`. -/
private lemma trace_comp_adjoint_comp_mono (T : H →L[ℂ] K) {X X' : H →L[ℂ] H}
    {Y Y' : K →L[ℂ] K} (hX : 0 ≤ X) (hXX' : X ≤ X') (hY : 0 ≤ Y) (hYY' : Y ≤ Y') :
    Tr (X ∘L T† ∘L Y ∘L T) ≤ Tr (X' ∘L T† ∘L Y' ∘L T) := by
  have h₁ : Tr (X ∘L T† ∘L Y ∘L T) ≤ Tr (X' ∘L T† ∘L Y ∘L T) := by
    have := trace_comp_adjoint_comp_nonneg T (sub_nonneg.2 hXX') hY
    rwa [sub_comp, toLinearMap_sub, map_sub, sub_nonneg] at this
  have h₂ : Tr (X' ∘L T† ∘L Y ∘L T) ≤ Tr (X' ∘L T† ∘L Y' ∘L T) := by
    have := trace_comp_adjoint_comp_nonneg T (hX.trans hXX') (sub_nonneg.2 hYY')
    rwa [sub_comp, comp_sub, comp_sub, toLinearMap_sub, map_sub, sub_nonneg] at this
  exact h₁.trans h₂

/-- The perspective of `-tᵖ` at the commuting pair `(𝐑[K] A, 𝐋[H] B)` is
`-(𝐑[K] (Aᵖ) * 𝐋[H] (B¹⁻ᵖ))`. -/
private lemma perspective_neg_rpow_rightMul_leftMul (p : ℝ) {A : H →L[ℂ] H} {B : K →L[ℂ] K}
    (hA : IsStrictlyPositive A) (hB : IsStrictlyPositive B) :
    perspective (fun t => -(t ^ p)) (𝐑[K] A) (𝐋[H] B) =
      -(𝐑[K] (A ^ p) * 𝐋[H] (B ^ (1 - p))) := by
  rw [perspective_neg_rpow_of_commute (commute_leftMul_rightMul B A).symm p
    (isStrictlyPositive_unop_rightMul hA) (isStrictlyPositive_leftMul hB),
    unop_map_rpow (rightMul K) p hA, map_rpow (leftMul H) (1 - p) hB]

/-- Lieb's concavity for `q = 1 - p` and strictly positive arguments, from the joint convexity of
the perspective. -/
private lemma sum_le_of_isStrictlyPositive (T : H →L[ℂ] K) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {ι : Type*} [Fintype ι] {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw₁ : ∑ i, w i = 1)
    {A : ι → H →L[ℂ] H} {B : ι → K →L[ℂ] K} (hA : ∀ i, IsStrictlyPositive (A i))
    (hB : ∀ i, IsStrictlyPositive (B i)) :
    ∑ i, w i • Tr ((A i ^ p) ∘L T† ∘L (B i ^ (1 - p)) ∘L T) ≤
      Tr (((∑ i, w i • A i) ^ p) ∘L T† ∘L ((∑ i, w i • B i) ^ (1 - p)) ∘L T) := by
  set l : ι → HilbertSchmidt H K →L[ℂ] HilbertSchmidt H K := fun i => 𝐑[K] (A i)
  set r : ι → HilbertSchmidt H K →L[ℂ] HilbertSchmidt H K := fun i => 𝐋[H] (B i)
  have hl : ∀ i, IsStrictlyPositive (l i) := fun i => isStrictlyPositive_unop_rightMul (hA i)
  have hr : ∀ i, IsStrictlyPositive (r i) := fun i => isStrictlyPositive_leftMul (hB i)
  have hP := (isOperatorConvexOn_neg_rpow.{0} hp0 hp1).perspective_sum_le_of_nonneg hw hw₁
    (fun i => (hl i).nonneg) hr
  have hlsum : ∑ i, w i • l i = 𝐑[K] (∑ i, w i • A i) := by
    simp only [l, map_sum, Finset.unop_sum, unop_rightMul_smul]
  have hrsum : ∑ i, w i • r i = 𝐋[H] (∑ i, w i • B i) := by
    simp only [r, map_sum, leftMul_smul]
  have hAs := IsStrictlyPositive.sum_smul hw hw₁ hA
  have hBs := IsStrictlyPositive.sum_smul hw hw₁ hB
  rw [hlsum, hrsum, perspective_neg_rpow_rightMul_leftMul p hAs hBs] at hP
  simp only [l, r, perspective_neg_rpow_rightMul_leftMul p (hA _) (hB _)] at hP
  have hq := inner_le_inner hP (ofCLM H K T)
  simp only [neg_apply, inner_neg_right, sum_apply, smul_apply, inner_sum,
    inner_smul_right_eq_smul, inner_unop_rightMul_leftMul, smul_neg, Finset.sum_neg_distrib,
    neg_le_neg_iff] at hq
  simpa only [comp_assoc] using hq

/-- `X + ε` is strictly positive for positive `X` and `ε > 0`. -/
private lemma isStrictlyPositive_add_smul_one {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {X : E →L[ℂ] E} (hX : 0 ≤ X) {ε : ℝ} (hε : 0 < ε) :
    IsStrictlyPositive (X + ε • (1 : E →L[ℂ] E)) := by
  rw [add_comm]
  exact (isStrictlyPositive_one.smul hε).add_nonneg hX

/-- `(Xˢ)^{a/s} = Xᵃ` for positive `X`, `0 ≤ a` and `0 < s`. -/
private lemma rpow_rpow_div {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {X : E →L[ℂ] E} (hX : 0 ≤ X) {a s : ℝ} (ha : 0 ≤ a) (hs : 0 < s) :
    (X ^ s) ^ (a / s) = X ^ a := by
  rw [rpow_rpow_of_exponent_nonneg X s (a / s) hs.le (div_nonneg ha hs.le) hX,
    mul_div_cancel₀ a hs.ne']

/-- `Re Tr (Xᵖ T† Yᑫ T)` is continuous on pairs of positive operators for `0 ≤ p`, `0 ≤ q`. -/
private lemma continuousOn_re_trace (T : H →L[ℂ] K) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    ContinuousOn (fun x : (H →L[ℂ] H) × (K →L[ℂ] K) =>
      (Tr ((x.1 ^ p) ∘L T† ∘L (x.2 ^ q) ∘L T)).re) (Ici 0 ×ˢ Ici 0) := by
  let tr : (H →L[ℂ] H) →ₗ[ℂ] ℂ := LinearMap.trace ℂ H ∘ₗ coeLM ℂ
  have htr : Continuous tr := LinearMap.continuous_of_finiteDimensional tr
  have h₁ : ContinuousOn (fun x : (H →L[ℂ] H) × (K →L[ℂ] K) => x.1 ^ p) (Ici 0 ×ˢ Ici 0) :=
    (continuousOn_rpow_of_nonneg hp).comp continuousOn_fst fun x hx => hx.1
  have h₂ : ContinuousOn (fun x : (H →L[ℂ] H) × (K →L[ℂ] K) => x.2 ^ q) (Ici 0 ×ˢ Ici 0) :=
    (continuousOn_rpow_of_nonneg hq).comp continuousOn_snd fun x hx => hx.2
  exact Complex.continuous_re.comp_continuousOn <| htr.comp_continuousOn <|
    h₁.clm_comp (continuousOn_const.clm_comp (h₂.clm_comp continuousOn_const))

/-- Lieb's concavity for `q = 1 - p` and positive arguments: the limit `ε → 0⁺` of the strictly
positive case at `A + ε`, `B + ε`. -/
private lemma sum_le_one_sub (T : H →L[ℂ] K) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {ι : Type*} [Fintype ι] {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw₁ : ∑ i, w i = 1)
    {A : ι → H →L[ℂ] H} {B : ι → K →L[ℂ] K} (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i) :
    ∑ i, w i • Tr ((A i ^ p) ∘L T† ∘L (B i ^ (1 - p)) ∘L T) ≤
      Tr (((∑ i, w i • A i) ^ p) ∘L T† ∘L ((∑ i, w i • B i) ^ (1 - p)) ∘L T) := by
  set F : (H →L[ℂ] H) × (K →L[ℂ] K) → ℝ :=
    fun x => (Tr ((x.1 ^ p) ∘L T† ∘L (x.2 ^ (1 - p)) ∘L T)).re
  have hF := continuousOn_re_trace T hp0 (sub_nonneg.2 hp1)
  -- the regularised pairs `(X + ε, Y + ε)`
  let reg (X : H →L[ℂ] H) (Y : K →L[ℂ] K) (ε : ℝ) : (H →L[ℂ] H) × (K →L[ℂ] K) :=
    (X + ε • (1 : H →L[ℂ] H), Y + ε • (1 : K →L[ℂ] K))
  have hreg_mem {X : H →L[ℂ] H} {Y : K →L[ℂ] K} (hX : 0 ≤ X) (hY : 0 ≤ Y) {ε : ℝ}
      (hε : 0 ≤ ε) : reg X Y ε ∈ Ici 0 ×ˢ Ici 0 :=
    ⟨add_nonneg hX (smul_nonneg hε zero_le_one), add_nonneg hY (smul_nonneg hε zero_le_one)⟩
  have hreg_tendsto {X : H →L[ℂ] H} {Y : K →L[ℂ] K} (hX : 0 ≤ X) (hY : 0 ≤ Y) :
      Tendsto (fun ε => F (reg X Y ε)) (𝓝[>] 0) (𝓝 (F (X, Y))) := by
    have hc : ContinuousWithinAt (reg X Y) (Ici 0) 0 := by fun_prop
    have h0 : reg X Y 0 = (X, Y) := by simp [reg]
    have hcont : ContinuousWithinAt (fun ε => F (reg X Y ε)) (Ici 0) 0 :=
      (hF.continuousWithinAt (hreg_mem hX hY le_rfl)).comp hc fun ε hε => hreg_mem hX hY hε
    have := hcont.tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    simpa only [h0] using this
  have hsum_reg (ε : ℝ) :
      (∑ i, w i • (reg (A i) (B i) ε).1, ∑ i, w i • (reg (A i) (B i) ε).2) =
        reg (∑ i, w i • A i) (∑ i, w i • B i) ε := by
    simp only [reg, smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hw₁, one_smul]
  have hlim_left : Tendsto (fun ε => ∑ i, w i * F (reg (A i) (B i) ε)) (𝓝[>] 0)
      (𝓝 (∑ i, w i * F (A i, B i))) :=
    tendsto_finsetSum _ fun i _ => (hreg_tendsto (hA i) (hB i)).const_mul (w i)
  have hAs : 0 ≤ ∑ i, w i • A i := Finset.sum_nonneg fun i _ => smul_nonneg (hw i) (hA i)
  have hBs : 0 ≤ ∑ i, w i • B i := Finset.sum_nonneg fun i _ => smul_nonneg (hw i) (hB i)
  have hlim_right := hreg_tendsto hAs hBs
  -- the real inequality in the limit
  have hre : ∑ i, w i * F (A i, B i) ≤ F (∑ i, w i • A i, ∑ i, w i • B i) := by
    refine le_of_tendsto_of_tendsto hlim_left hlim_right ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have := sum_le_of_isStrictlyPositive T hp0 hp1 hw hw₁ (A := fun i => (reg (A i) (B i) ε).1)
      (B := fun i => (reg (A i) (B i) ε).2) (fun i => isStrictlyPositive_add_smul_one (hA i) hε)
      (fun i => isStrictlyPositive_add_smul_one (hB i) hε)
    rw [show (∑ i, w i • (reg (A i) (B i) ε).1) = (reg (∑ i, w i • A i) (∑ i, w i • B i) ε).1
        from congrArg Prod.fst (hsum_reg ε),
      show (∑ i, w i • (reg (A i) (B i) ε).2) = (reg (∑ i, w i • A i) (∑ i, w i • B i) ε).2
        from congrArg Prod.snd (hsum_reg ε)] at this
    have := (Complex.le_def.1 this).1
    simpa only [F, Complex.re_sum, Complex.smul_re, smul_eq_mul] using this
  -- lift it to `ℂ`: both sides are nonnegative
  refine le_of_re_le_of_nonneg (Finset.sum_nonneg fun i _ => smul_nonneg (hw i)
    (trace_comp_adjoint_comp_nonneg T rpow_nonneg rpow_nonneg))
    (trace_comp_adjoint_comp_nonneg T rpow_nonneg rpow_nonneg) ?_
  simpa only [F, Complex.re_sum, Complex.smul_re, smul_eq_mul] using hre

/-- **Lieb's concavity theorem** for finite convex combinations: for `0 ≤ p`, `0 ≤ q`,
`p + q ≤ 1` and positive `Aᵢ`, `Bᵢ`,
`∑ᵢ wᵢ Tr (Aᵢᵖ T† Bᵢᑫ T) ≤ Tr ((∑ᵢ wᵢ Aᵢ)ᵖ T† (∑ᵢ wᵢ Bᵢ)ᑫ T)`. -/
theorem lieb_concavity_weighted (T : H →L[ℂ] K) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpq : p + q ≤ 1) {ι : Type*} [Fintype ι] {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hw₁ : ∑ i, w i = 1) {A : ι → H →L[ℂ] H} {B : ι → K →L[ℂ] K} (hA : ∀ i, 0 ≤ A i)
    (hB : ∀ i, 0 ≤ B i) :
    ∑ i, w i • Tr ((A i ^ p) ∘L T† ∘L (B i ^ q) ∘L T) ≤
      Tr (((∑ i, w i • A i) ^ p) ∘L T† ∘L ((∑ i, w i • B i) ^ q) ∘L T) := by
  have hAs : 0 ≤ ∑ i, w i • A i := Finset.sum_nonneg fun i _ => smul_nonneg (hw i) (hA i)
  have hBs : 0 ≤ ∑ i, w i • B i := Finset.sum_nonneg fun i _ => smul_nonneg (hw i) (hB i)
  set s := p + q with hs
  rcases (add_nonneg hp hq).eq_or_lt with hs0 | hs0
  · -- `p = q = 0`: the functional is constant on positive operators
    obtain ⟨rfl, rfl⟩ : p = 0 ∧ q = 0 := ⟨by linarith, by linarith⟩
    simp only [rpow_zero _ (hA _), rpow_zero _ (hB _), rpow_zero _ hAs, rpow_zero _ hBs]
    rw [← Finset.sum_smul, hw₁, one_smul]
  -- reduce to the exponents `p / s` and `1 - p / s = q / s` at `Aˢ`, `Bˢ`
  have hs1 : s ≤ 1 := hpq
  have hps : p / s ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hp hs0.le, (div_le_one hs0).2 (by linarith)⟩
  have hqs : 1 - p / s = q / s := by
    rw [eq_div_iff hs0.ne', sub_mul, div_mul_cancel₀ p hs0.ne', one_mul]
    ring
  have hqs' : q / s ∈ Icc (0 : ℝ) 1 := hqs ▸ ⟨by linarith [hps.2], by linarith [hps.1]⟩
  have hkey := sum_le_one_sub T hps.1 hps.2 hw hw₁ (A := fun i => A i ^ s) (B := fun i => B i ^ s)
    (fun i => rpow_nonneg) (fun i => rpow_nonneg)
  have hA' : ∀ i, (A i ^ s) ^ (p / s) = A i ^ p := fun i => rpow_rpow_div (hA i) hp hs0
  have hB' : ∀ i, (B i ^ s) ^ (q / s) = B i ^ q := fun i => rpow_rpow_div (hB i) hq hs0
  simp only [hqs, hA', hB'] at hkey
  refine hkey.trans ?_
  -- the operator concavity of `t ↦ tˢ` and the Löwner–Heinz inequality
  have hcA : ∑ i, w i • A i ^ s ≤ (∑ i, w i • A i) ^ s :=
    (concaveOn_rpow ⟨hs0.le, hs1⟩).le_map_sum (fun i _ => hw i) (by simpa using hw₁)
      fun i _ => hA i
  have hcB : ∑ i, w i • B i ^ s ≤ (∑ i, w i • B i) ^ s :=
    (concaveOn_rpow ⟨hs0.le, hs1⟩).le_map_sum (fun i _ => hw i) (by simpa using hw₁)
      fun i _ => hB i
  have := trace_comp_adjoint_comp_mono T rpow_nonneg (rpow_le_rpow hps hcA) rpow_nonneg
    (rpow_le_rpow hqs' hcB)
  rwa [rpow_rpow_div hAs hp hs0, rpow_rpow_div hBs hq hs0] at this

/-- **Lieb's concavity theorem** (Lieb 1973, Theorem 1): for `T : H →L[ℂ] K`, `0 ≤ p`, `0 ≤ q`
and `p + q ≤ 1`, the map `(A, B) ↦ Tr (Aᵖ T† Bᑫ T)` is jointly concave on pairs of positive
operators. -/
theorem lieb_concaveOn (T : H →L[ℂ] K) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q ≤ 1) :
    ConcaveOn ℝ (Ici 0 ×ˢ Ici 0) fun (A, B) ↦ Tr ((A ^ p) ∘L T† ∘L (B ^ q) ∘L T) := by
  refine ⟨(convex_Ici _).prod (convex_Ici _), ?_⟩
  rintro ⟨A₁, B₁⟩ ⟨hA₁, hB₁⟩ ⟨A₂, B₂⟩ ⟨hA₂, hB₂⟩ a b ha hb hab
  have := lieb_concavity_weighted T hp hq hpq (w := ![a, b]) (A := ![A₁, A₂]) (B := ![B₁, B₂])
    (fun i => by fin_cases i <;> simpa) (by simpa using hab)
    (fun i => by fin_cases i <;> simpa) (fun i => by fin_cases i <;> simpa)
  simpa [Fin.sum_univ_two] using this

/-- The trace `Tr (Aᵖ T† Bᑫ T)` is nonnegative. -/
theorem trace_rpow_comp_rpow_nonneg (T : H →L[ℂ] K) (A : H →L[ℂ] H) (B : K →L[ℂ] K)
    (p q : ℝ) : 0 ≤ Tr ((A ^ p) ∘L T† ∘L (B ^ q) ∘L T) :=
  trace_comp_adjoint_comp_nonneg T rpow_nonneg rpow_nonneg

/-- The trace `Tr (Aᵖ T† Bᑫ T)` is real: it equals its real part. -/
theorem trace_rpow_comp_rpow_eq_re (T : H →L[ℂ] K) (A : H →L[ℂ] H) (B : K →L[ℂ] K)
    (p q : ℝ) :
    Tr ((A ^ p) ∘L T† ∘L (B ^ q) ∘L T) = ((Tr ((A ^ p) ∘L T† ∘L (B ^ q) ∘L T)).re : ℂ) :=
  Complex.ext (by simp) (by
    simpa using (Complex.nonneg_iff.1 (trace_rpow_comp_rpow_nonneg T A B p q)).2.symm)

/-- The Lieb functional is homogeneous of degree `p + q`:
`Tr ((c A)ᵖ T† (c B)ᑫ T) = c ^ (p + q) Tr (Aᵖ T† Bᑫ T)` for `0 ≤ c` and positive `A`, `B`. -/
theorem trace_smul_rpow_comp_smul_rpow (T : H →L[ℂ] K) {A : H →L[ℂ] H} {B : K →L[ℂ] K}
    (hA : 0 ≤ A) (hB : 0 ≤ B) {c p q : ℝ} (hc : 0 ≤ c) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    Tr (((c • A) ^ p) ∘L T† ∘L ((c • B) ^ q) ∘L T) =
      c ^ (p + q) • Tr ((A ^ p) ∘L T† ∘L (B ^ q) ∘L T) := by
  have key (r : ℝ) (M : H →L[ℂ] H) : Tr (r • M) = r • Tr M :=
    (LinearMap.trace ℂ H ∘ₗ coeLM ℂ).map_smul_of_tower r M
  rw [smul_rpow hc hA, smul_rpow hc hB, Real.rpow_add_of_nonneg hc hp hq]
  simp only [smul_comp, comp_smul, smul_smul]
  rw [key, mul_comm]

/-- For `q = 1 - p` the Lieb functional is **superadditive**:
`∑ᵢ Tr (Aᵢᵖ T† Bᵢ¹⁻ᵖ T) ≤ Tr ((∑ᵢ Aᵢ)ᵖ T† (∑ᵢ Bᵢ)¹⁻ᵖ T)`, since it is concave and homogeneous
of degree one. -/
theorem lieb_superadditive (T : H →L[ℂ] K) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {ι : Type*}
    [Fintype ι] {A : ι → H →L[ℂ] H} {B : ι → K →L[ℂ] K} (hA : ∀ i, 0 ≤ A i)
    (hB : ∀ i, 0 ≤ B i) :
    ∑ i, Tr ((A i ^ p) ∘L T† ∘L (B i ^ (1 - p)) ∘L T) ≤
      Tr (((∑ i, A i) ^ p) ∘L T† ∘L ((∑ i, B i) ^ (1 - p)) ∘L T) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simpa using trace_rpow_comp_rpow_nonneg T 0 0 p (1 - p)
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  set c : ℝ := (Fintype.card ι : ℝ)⁻¹
  have hc : 0 < c := inv_pos.2 hn
  have hw₁ : ∑ _i : ι, c = 1 := by simp [c, hn.ne']
  have := lieb_concavity_weighted T hp0 (sub_nonneg.2 hp1) (by linarith) (fun _ => hc.le) hw₁ hA hB
  rw [← Finset.smul_sum, ← Finset.smul_sum, ← Finset.smul_sum,
    trace_smul_rpow_comp_smul_rpow T (Finset.sum_nonneg fun i _ => hA i)
      (Finset.sum_nonneg fun i _ => hB i) hc.le hp0 (sub_nonneg.2 hp1),
    add_sub_cancel, Real.rpow_one] at this
  have := smul_le_smul_of_nonneg_left this (inv_nonneg.2 hc.le)
  rwa [smul_smul, smul_smul, inv_mul_cancel₀ hc.ne', one_smul, one_smul] at this

end Lieb

end ContinuousLinearMap
