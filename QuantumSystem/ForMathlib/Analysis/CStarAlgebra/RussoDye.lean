/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.Unitary.Span
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs

/-!
# The Russo–Dye theorem

The **Russo–Dye theorem** (Russo–Dye 1966): in a unital C⋆-algebra `A` the closed unit ball is
the closed convex hull of the unitary group, `closedConvexHull ℝ (unitary A) = closedBall 0 1`.
We prove it in the quantitative form of Kadison–Pedersen (1985), along the elementary argument of
Gardner (1984): an element with `‖x‖ < 1 - 2 / n` is the mean `(u₁ + ⋯ + uₙ) / n` of `n`
unitaries.

1. A self-adjoint contraction `b` is the mean of the unitaries `b ± i √(1 - b²)`
   (`selfAdjoint.unitarySelfAddISMul`).
2. An invertible `z` has the polar decomposition `z = w |z|` with `w = z |z|⁻¹` unitary and
   `|z| = √(z⋆ z)` (`CFC.abs z`). So an invertible contraction is the mean of the two unitaries
   `w (|z| ± i √(1 - |z|²))`.
3. If `‖x‖ < 1` and `u` is unitary, `u + x = u (1 + u⋆ x)` is invertible with
   `‖(u + x) / 2‖ ≤ 1`, so `u + x` is the sum of two unitaries. Iterating, `k x + u` is the sum of
   `k + 1` unitaries.
4. For `n ≥ 3` put `a = n x / (n - 2)`, so `‖a‖ < 1`; then `n x = ((n - 2) a + 1) - 1` is the sum
   of `n` unitaries.

## Main results

* `IsUnit.exists_mem_unitary_eq_mul_cfcAbs` — the polar decomposition `z = w |z|`, `w` unitary,
  of an invertible element.
* `CStarAlgebra.exists_unitary_eq_mean_of_norm_lt` — **Kadison–Pedersen**: if
  `‖x‖ < 1 - 2 / n`, then `x = (u₁ + ⋯ + uₙ) / n` for unitaries `uᵢ`.
* `CStarAlgebra.ball_subset_convexHull_unitary` — the open unit ball lies in the convex hull of the
  unitaries.
* `CStarAlgebra.closedConvexHull_unitary` — **Russo–Dye**: the closed convex hull of the
  unitaries is the closed unit ball.

## References

* B. Russo, H. A. Dye, *A note on unitary operators in C⋆-algebras*, Duke Math. J. 33 (1966),
  413–416.
* L. T. Gardner, *An elementary proof of the Russo–Dye theorem*, Proc. Amer. Math. Soc. 90
  (1984), 171.
* R. V. Kadison, G. K. Pedersen, *Means and convex combinations of unitary operators*, Math.
  Scand. 57 (1985), 249–266.
-/

@[expose] public section

open Metric
open scoped Topology

variable {A : Type*} [CStarAlgebra A]

section Ordered

variable [PartialOrder A] [StarOrderedRing A]

/-- The **polar decomposition** of an invertible element of a unital C⋆-algebra: `z = w |z|` with
`w` unitary, where `|z| = √(z⋆ z)` (`CFC.abs z`). The square `|z| |z| = z⋆ z` is invertible, hence
so is `|z|`; `w = z |z|⁻¹` has `w⋆ w = |z|⁻¹ z⋆ z |z|⁻¹ = 1`, and `w` is invertible, so also
`w w⋆ = 1`. -/
lemma IsUnit.exists_mem_unitary_eq_mul_cfcAbs {z : A} (hz : IsUnit z) :
    ∃ w ∈ unitary A, z = w * CFC.abs z := by
  have hsa : IsSelfAdjoint (CFC.abs z) := (CFC.abs_nonneg z).isSelfAdjoint
  obtain ⟨c, hc⟩ : IsUnit (CFC.abs z) :=
    isUnit_mul_self_iff.mp (CFC.abs_mul_abs z ▸ hz.star.mul hz)
  obtain ⟨W, hW⟩ := hz.mul (c⁻¹).isUnit
  have hzc : z = W * CFC.abs z := by rw [hW, ← hc, mul_assoc, Units.inv_mul, mul_one]
  have hstar : star (W : A) * W = 1 := by
    have h₁ : star ((c⁻¹ : Aˣ) : A) * CFC.abs z = 1 := by
      rw [← hsa.star_eq, ← star_mul, ← hc, Units.mul_inv, star_one]
    calc star (W : A) * W = star ((c⁻¹ : Aˣ) : A) * (star z * z) * (c⁻¹ : Aˣ) := by
          rw [hW, star_mul]; noncomm_ring
      _ = star ((c⁻¹ : Aˣ) : A) * CFC.abs z * (CFC.abs z * (c⁻¹ : Aˣ)) := by
          rw [← CFC.abs_mul_abs z]; noncomm_ring
      _ = 1 := by rw [h₁, ← hc, Units.mul_inv, one_mul]
  refine ⟨W, Unitary.mem_iff.2 ⟨hstar, ?_⟩, hzc⟩
  rw [← Units.inv_eq_of_mul_eq_one_left hstar, Units.mul_inv]

end Ordered

namespace CStarAlgebra

/-- An invertible contraction `z` of a unital C⋆-algebra is the mean of two unitaries. With the
polar decomposition `z = w |z|` (`IsUnit.exists_mem_unitary_eq_mul_cfcAbs`), the self-adjoint
contraction `|z|` is the mean of the unitaries `v = |z| + i √(1 - |z|²)` and `v⋆`, so
`2 z = w v + w v⋆`. -/
private lemma exists_unitary_add_eq_two_smul_of_isUnit {z : A} (hz : IsUnit z) (hz₁ : ‖z‖ ≤ 1) :
    ∃ u₁ u₂ : unitary A, (u₁ : A) + u₂ = (2 : ℝ) • z := by
  let _ := CStarAlgebra.spectralOrder A
  let _ := CStarAlgebra.spectralOrderedRing A
  obtain ⟨w, hw, hzw⟩ := hz.exists_mem_unitary_eq_mul_cfcAbs
  let s : selfAdjoint A := ⟨CFC.abs z, (CFC.abs_nonneg z).isSelfAdjoint⟩
  have hs : ‖s‖ ≤ 1 := by
    change ‖CFC.abs z‖ ≤ 1
    rwa [CFC.norm_abs]
  let v := selfAdjoint.unitarySelfAddISMul s hs
  let w' : unitary A := ⟨w, hw⟩
  refine ⟨w' * v, w' * star v, ?_⟩
  have hv : (v : A) + (star v : unitary A) = (2 : ℝ) • (s : A) := by
    rw [Unitary.coe_star, selfAdjoint.star_coe_unitarySelfAddISMul,
      selfAdjoint.unitarySelfAddISMul_coe]
    module
  rw [Submonoid.coe_mul, Submonoid.coe_mul, ← mul_add, hv, hzw, mul_smul_comm]

/-- If `‖x‖ < 1` and `u` is unitary, then `x + u` is the sum of two unitaries:
`u + x = u (1 + u⋆ x)` is invertible since `‖u⋆ x‖ = ‖x‖ < 1`, and `‖(x + u) / 2‖ ≤ 1`, so
`CStarAlgebra.exists_unitary_add_eq_two_smul_of_isUnit` applies to `(x + u) / 2`. -/
private lemma exists_unitary_add_eq_add_unitary {x : A} (hx : ‖x‖ < 1) (u : unitary A) :
    ∃ u₁ u₂ : unitary A, x + u = u₁ + u₂ := by
  have hux : x + u = u * (1 + star (u : A) * x) := by
    rw [mul_add, mul_one, ← mul_assoc, Unitary.mul_star_self_of_mem u.2, one_mul, add_comm]
  have h₁ : IsUnit (1 + star (u : A) * x) := by
    have h : ‖-(star (u : A) * x)‖ < 1 := by
      rwa [norm_neg, ← Unitary.coe_star, CStarRing.norm_coe_unitary_mul]
    simpa using (Units.oneSub _ h).isUnit
  have hunit : IsUnit ((2⁻¹ : ℝ) • (x + u)) := by
    rw [hux]
    exact (Unitary.isUnit_coe.mul h₁).smul (Units.mk0 (2⁻¹ : ℝ) (by norm_num))
  have hnorm : ‖(2⁻¹ : ℝ) • (x + u)‖ ≤ 1 := by
    have hu : ‖(u : A)‖ ≤ 1 := by
      nontriviality A
      rw [CStarRing.norm_coe_unitary]
    rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
    calc 2⁻¹ * ‖x + u‖ ≤ 2⁻¹ * (‖x‖ + ‖(u : A)‖) := by gcongr; exact norm_add_le _ _
      _ ≤ 1 := by linarith
  obtain ⟨u₁, u₂, h⟩ := exists_unitary_add_eq_two_smul_of_isUnit hunit hnorm
  refine ⟨u₁, u₂, ?_⟩
  rw [h, smul_smul]
  norm_num

/-- If `‖x‖ < 1`, then `k x + u` is the sum of `k + 1` unitaries for every unitary `u`: by
induction, `(k + 1) x + u = u₁ + (k x + u₂)` with `x + u = u₁ + u₂`
(`CStarAlgebra.exists_unitary_add_eq_add_unitary`). -/
private lemma exists_unitary_sum_eq_nsmul_add {x : A} (hx : ‖x‖ < 1) (k : ℕ) (u : unitary A) :
    ∃ v : Fin (k + 1) → unitary A, (k : ℝ) • x + u = ∑ i, (v i : A) := by
  induction k generalizing u with
  | zero => exact ⟨fun _ => u, by simp⟩
  | succ k ih =>
    obtain ⟨u₁, u₂, h⟩ := exists_unitary_add_eq_add_unitary hx u
    obtain ⟨v, hv⟩ := ih u₂
    refine ⟨Fin.cons u₁ v, ?_⟩
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← hv, Nat.cast_succ, add_smul, one_smul, add_assoc, h]
    abel

/-- **Kadison–Pedersen**: in a unital C⋆-algebra, an element with `‖x‖ < 1 - 2 / n` is the mean
`(u₁ + ⋯ + uₙ) / n` of `n` unitaries (Kadison–Pedersen 1985, after Gardner 1984). Together with
`0 < n`, the norm bound forces `n ≥ 3`, since `1 - 2 / n ≤ 0` for `n ∈ {1, 2}`. For
`a = n x / (n - 2)`, `‖a‖ < 1`, and `(n - 2) a + 1` is the sum of `n - 1` unitaries (by
induction, `x + u` being the sum of two unitaries for `‖x‖ < 1` and `u` unitary); adding the
unitary `-1` gives `n x`. -/
theorem exists_unitary_eq_mean_of_norm_lt {x : A} {n : ℕ} (hn : 0 < n) (hx : ‖x‖ < 1 - 2 / n) :
    ∃ u : Fin n → unitary A, x = (n : ℝ)⁻¹ • ∑ i, (u i : A) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := by
    refine ⟨n - 3, ?_⟩
    by_contra h
    obtain rfl | rfl : n = 1 ∨ n = 2 := by omega
    all_goals norm_num at hx; linarith [norm_nonneg x]
  have hk : (0 : ℝ) < k + 1 := by positivity
  set a : A := ((k + 3 : ℝ) / (k + 1)) • x with ha_def
  have ha : ‖a‖ < 1 := by
    rw [ha_def, norm_smul, Real.norm_of_nonneg (by positivity)]
    push_cast at hx
    calc (k + 3 : ℝ) / (k + 1) * ‖x‖ < (k + 3) / (k + 1) * (1 - 2 / (k + 3)) := by gcongr
      _ = 1 := by field_simp; ring
  obtain ⟨v, hv⟩ := exists_unitary_sum_eq_nsmul_add ha (k + 1) 1
  have hxa : ((k + 1 : ℕ) : ℝ) • a = ((k + 3 : ℕ) : ℝ) • x := by
    rw [ha_def, smul_smul]
    congr 1
    push_cast
    field_simp
  refine ⟨Fin.cons (-1) v, ?_⟩
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [← hv, hxa, Unitary.coe_neg, OneMemClass.coe_one, neg_add_cancel_comm_assoc, smul_smul,
    inv_mul_cancel₀ (by positivity), one_smul]

/-- The open unit ball of a unital C⋆-algebra lies in the convex hull of the unitaries: an element
with `‖x‖ < 1` has `‖x‖ < 1 - 2 / n` for large `n`, and is then the mean of `n` unitaries
(`CStarAlgebra.exists_unitary_eq_mean_of_norm_lt`). -/
lemma ball_subset_convexHull_unitary : ball (0 : A) 1 ⊆ convexHull ℝ (unitary A : Set A) := by
  intro x hx
  rw [mem_ball_zero_iff] at hx
  have h₁ : 0 < 1 - ‖x‖ := sub_pos.2 hx
  obtain ⟨n, hn⟩ := exists_nat_gt (2 / (1 - ‖x‖))
  have hn₀ : (0 : ℝ) < n := (div_pos two_pos h₁).trans hn
  have hxn : ‖x‖ < 1 - 2 / n := by
    rw [div_lt_iff₀ h₁] at hn
    rw [lt_sub_iff_add_lt, ← lt_sub_iff_add_lt', div_lt_iff₀ hn₀]
    linarith
  obtain ⟨u, rfl⟩ := exists_unitary_eq_mean_of_norm_lt (Nat.cast_pos.1 hn₀) hxn
  rw [Finset.smul_sum]
  refine (convex_convexHull ℝ _).sum_mem (fun _ _ => by positivity) ?_
    fun i _ => subset_convexHull ℝ _ (u i).2
  simp [hn₀.ne']

/-- The **Russo–Dye theorem** (Russo–Dye 1966): the closed convex hull of the unitaries of a
unital C⋆-algebra is its closed unit ball. Unitaries have norm at most `1`, and the closed ball is
closed and convex; conversely, an `x` with `‖x‖ ≤ 1` is the limit of `t x` as `t → 1⁻`, which lie
in the open unit ball and hence in the convex hull
(`CStarAlgebra.ball_subset_convexHull_unitary`). -/
theorem closedConvexHull_unitary : closedConvexHull ℝ (unitary A : Set A) = closedBall 0 1 := by
  rw [closedConvexHull_eq_closure_convexHull]
  refine subset_antisymm (closure_minimal (convexHull_min ?_ (convex_closedBall 0 1))
    isClosed_closedBall) ?_
  · intro u hu
    rw [mem_closedBall_zero_iff]
    nontriviality A
    rw [CStarRing.norm_of_mem_unitary hu]
  · intro x hx
    rw [mem_closedBall_zero_iff] at hx
    have ht : Filter.Tendsto (fun t : ℝ => t • x) (𝓝[<] 1) (𝓝 x) := by
      simpa using
        ((Filter.tendsto_id (x := 𝓝[<] (1 : ℝ))).mono_right nhdsWithin_le_nhds).smul_const x
    refine mem_closure_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht
    apply ball_subset_convexHull_unitary
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg ht.1.le]
    calc t * ‖x‖ ≤ t * 1 := by gcongr; exact ht.1.le
      _ < 1 := by linarith [ht.2]

end CStarAlgebra
