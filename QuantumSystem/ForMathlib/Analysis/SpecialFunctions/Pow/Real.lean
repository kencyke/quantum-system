module

public import Mathlib.Analysis.MeanInequalities

/-!
# Inequalities for Real Power Functions

This file proves scalar inequalities about `Real.rpow` used in the proof of
Lieb's joint concavity theorem.

## Main results

- `Real.convexCombo_rpow_mul_rpow_le`: joint concavity of (x, y) ↦ xᵖ y¹⁻ᵖ
  for 0 < p < 1.
-/

@[expose] public section

namespace Real

/-- Joint concavity of (x, y) ↦ xᵖ · y¹⁻ᵖ for 0 < p < 1:
the convex combination of values is at most the value at the convex combination. -/
lemma convexCombo_rpow_mul_rpow_le {p t x₁ x₂ y₁ y₂ : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂) (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂) :
    t * (x₁ ^ p * y₁ ^ (1 - p)) + (1 - t) * (x₂ ^ p * y₂ ^ (1 - p)) ≤
    (t * x₁ + (1 - t) * x₂) ^ p * (t * y₁ + (1 - t) * y₂) ^ (1 - p) := by
  have h1p : 0 < 1 - p := by linarith
  have hconj : p + (1 - p) = 1 := by ring
  -- Handle boundary cases for t
  rcases eq_or_lt_of_le ht0 with rfl | ht0'
  · simp
  rcases eq_or_lt_of_le ht1 with rfl | ht1'
  · simp
  have h1t : 0 < 1 - t := by linarith
  have htne : t ≠ 0 := ne_of_gt ht0'
  have h1tne : 1 - t ≠ 0 := ne_of_gt h1t
  -- Handle zero cases
  by_cases hsum_x_zero : t * x₁ + (1 - t) * x₂ = 0
  · -- If the x-sum is zero, both t*x₁ and (1-t)*x₂ must be zero
    have htx₁ : t * x₁ = 0 := by
      have h1 := mul_nonneg (le_of_lt ht0') hx₁
      have h2 := mul_nonneg (le_of_lt h1t) hx₂
      linarith
    have hx₁_zero : x₁ = 0 := (mul_eq_zero.mp htx₁).resolve_left htne
    have htx₂ : (1 - t) * x₂ = 0 := by linarith
    have hx₂_zero : x₂ = 0 := (mul_eq_zero.mp htx₂).resolve_left h1tne
    -- LHS = 0 + 0 = 0, RHS = 0^p * (...)^(1-p) ≥ 0
    simp only [hx₁_zero, hx₂_zero, Real.zero_rpow (ne_of_gt hp0), mul_zero, zero_mul, add_zero]
    exact le_refl 0
  by_cases hsum_y_zero : t * y₁ + (1 - t) * y₂ = 0
  · -- If the y-sum is zero, both t*y₁ and (1-t)*y₂ must be zero
    have hty₁ : t * y₁ = 0 := by
      have h1 := mul_nonneg (le_of_lt ht0') hy₁
      have h2 := mul_nonneg (le_of_lt h1t) hy₂
      linarith
    have hy₁_zero : y₁ = 0 := (mul_eq_zero.mp hty₁).resolve_left htne
    have hty₂ : (1 - t) * y₂ = 0 := by linarith
    have hy₂_zero : y₂ = 0 := (mul_eq_zero.mp hty₂).resolve_left h1tne
    -- LHS = 0 + 0 = 0, RHS = (...)^p * 0^(1-p) ≥ 0
    simp only [hy₁_zero, hy₂_zero, Real.zero_rpow (ne_of_gt h1p), mul_zero, add_zero]
    exact le_refl 0
  -- Main case: both sums are positive
  have hsum_x_pos : 0 < t * x₁ + (1 - t) * x₂ := by
    have := add_nonneg (mul_nonneg (le_of_lt ht0') hx₁) (mul_nonneg (le_of_lt h1t) hx₂)
    exact lt_of_le_of_ne this (Ne.symm hsum_x_zero)
  have hsum_y_pos : 0 < t * y₁ + (1 - t) * y₂ := by
    have := add_nonneg (mul_nonneg (le_of_lt ht0') hy₁) (mul_nonneg (le_of_lt h1t) hy₂)
    exact lt_of_le_of_ne this (Ne.symm hsum_y_zero)
  -- Define normalized weights
  set X := t * x₁ + (1 - t) * x₂ with hX_def
  set Y := t * y₁ + (1 - t) * y₂ with hY_def
  set α := (t * x₁) / X with hα_def
  set β := (t * y₁) / Y with hβ_def
  have hX_ne : X ≠ 0 := ne_of_gt hsum_x_pos
  have hY_ne : Y ≠ 0 := ne_of_gt hsum_y_pos
  have hα_nonneg : 0 ≤ α := div_nonneg (mul_nonneg (le_of_lt ht0') hx₁) (le_of_lt hsum_x_pos)
  have hα_le_one : α ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact le_add_of_nonneg_right (mul_nonneg (le_of_lt h1t) hx₂)
  have hβ_nonneg : 0 ≤ β := div_nonneg (mul_nonneg (le_of_lt ht0') hy₁) (le_of_lt hsum_y_pos)
  have hβ_le_one : β ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact le_add_of_nonneg_right (mul_nonneg (le_of_lt h1t) hy₂)
  have h1α_nonneg : 0 ≤ 1 - α := by linarith
  have h1β_nonneg : 0 ≤ 1 - β := by linarith
  -- Key identities
  have htx₁_eq : t * x₁ = α * X := by
    rw [hα_def]
    exact (div_mul_cancel₀ (t * x₁) hX_ne).symm
  have htx₂_eq : (1 - t) * x₂ = (1 - α) * X := by
    have h : (1 - t) * x₂ = X - t * x₁ := by rw [hX_def]; ring
    rw [h, htx₁_eq]; ring
  have hty₁_eq : t * y₁ = β * Y := by
    rw [hβ_def]
    exact (div_mul_cancel₀ (t * y₁) hY_ne).symm
  have hty₂_eq : (1 - t) * y₂ = (1 - β) * Y := by
    have h : (1 - t) * y₂ = Y - t * y₁ := by rw [hY_def]; ring
    rw [h, hty₁_eq]; ring
  -- Use weighted AM-GM to bound the sum of geometric means
  have hAMGM1 := geom_mean_le_arith_mean2_weighted (le_of_lt hp0) (le_of_lt h1p) hα_nonneg hβ_nonneg hconj
  have hAMGM2 := geom_mean_le_arith_mean2_weighted (le_of_lt hp0) (le_of_lt h1p) h1α_nonneg h1β_nonneg hconj
  have hbound : α ^ p * β ^ (1 - p) + (1 - α) ^ p * (1 - β) ^ (1 - p) ≤ 1 := by
    calc α ^ p * β ^ (1 - p) + (1 - α) ^ p * (1 - β) ^ (1 - p)
        ≤ (p * α + (1 - p) * β) + (p * (1 - α) + (1 - p) * (1 - β)) := add_le_add hAMGM1 hAMGM2
      _ = p * (α + (1 - α)) + (1 - p) * (β + (1 - β)) := by ring
      _ = p * 1 + (1 - p) * 1 := by simp
      _ = 1 := by ring
  -- Key calculation: Express products in terms of α, β
  have hprod1 : (t * x₁) ^ p * (t * y₁) ^ (1 - p) = α ^ p * β ^ (1 - p) * X ^ p * Y ^ (1 - p) := by
    rw [htx₁_eq, hty₁_eq]
    rw [Real.mul_rpow hα_nonneg (le_of_lt hsum_x_pos)]
    rw [Real.mul_rpow hβ_nonneg (le_of_lt hsum_y_pos)]
    ring
  have hprod2 : ((1 - t) * x₂) ^ p * ((1 - t) * y₂) ^ (1 - p) =
      (1 - α) ^ p * (1 - β) ^ (1 - p) * X ^ p * Y ^ (1 - p) := by
    rw [htx₂_eq, hty₂_eq]
    rw [Real.mul_rpow h1α_nonneg (le_of_lt hsum_x_pos)]
    rw [Real.mul_rpow h1β_nonneg (le_of_lt hsum_y_pos)]
    ring
  -- Show t * (x₁ ^ p * y₁ ^ (1 - p)) = (t * x₁) ^ p * (t * y₁) ^ (1 - p)
  have ht_rpow : t ^ p * t ^ (1 - p) = t := by
    rw [← Real.rpow_add ht0', hconj, Real.rpow_one]
  have h1t_rpow : (1 - t) ^ p * (1 - t) ^ (1 - p) = 1 - t := by
    rw [← Real.rpow_add h1t, hconj, Real.rpow_one]
  have hfinal1 : t * (x₁ ^ p * y₁ ^ (1 - p)) = (t * x₁) ^ p * (t * y₁) ^ (1 - p) := by
    rw [Real.mul_rpow (le_of_lt ht0') hx₁, Real.mul_rpow (le_of_lt ht0') hy₁]
    have h : t ^ p * x₁ ^ p * (t ^ (1 - p) * y₁ ^ (1 - p)) =
        t ^ p * t ^ (1 - p) * x₁ ^ p * y₁ ^ (1 - p) := by ring
    rw [h, ht_rpow, mul_assoc]
  have hfinal2 : (1 - t) * (x₂ ^ p * y₂ ^ (1 - p)) = ((1 - t) * x₂) ^ p * ((1 - t) * y₂) ^ (1 - p) := by
    rw [Real.mul_rpow (le_of_lt h1t) hx₂, Real.mul_rpow (le_of_lt h1t) hy₂]
    have h : (1 - t) ^ p * x₂ ^ p * ((1 - t) ^ (1 - p) * y₂ ^ (1 - p)) =
        (1 - t) ^ p * (1 - t) ^ (1 - p) * x₂ ^ p * y₂ ^ (1 - p) := by ring
    rw [h, h1t_rpow, mul_assoc]
  -- Combine everything
  calc t * (x₁ ^ p * y₁ ^ (1 - p)) + (1 - t) * (x₂ ^ p * y₂ ^ (1 - p))
      = (t * x₁) ^ p * (t * y₁) ^ (1 - p) + ((1 - t) * x₂) ^ p * ((1 - t) * y₂) ^ (1 - p) := by
        rw [hfinal1, hfinal2]
    _ = α ^ p * β ^ (1 - p) * X ^ p * Y ^ (1 - p) +
        (1 - α) ^ p * (1 - β) ^ (1 - p) * X ^ p * Y ^ (1 - p) := by
        rw [hprod1, hprod2]
    _ = X ^ p * Y ^ (1 - p) * (α ^ p * β ^ (1 - p) + (1 - α) ^ p * (1 - β) ^ (1 - p)) := by ring
    _ ≤ X ^ p * Y ^ (1 - p) * 1 := by
        apply mul_le_mul_of_nonneg_left hbound
        apply mul_nonneg
        · exact Real.rpow_nonneg (le_of_lt hsum_x_pos) _
        · exact Real.rpow_nonneg (le_of_lt hsum_y_pos) _
    _ = X ^ p * Y ^ (1 - p) := mul_one _

end Real
