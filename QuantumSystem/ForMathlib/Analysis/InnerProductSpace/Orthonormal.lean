/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# Compression to the span of a finite orthonormal family

For a finite orthonormal family `e`, the compression `w ↦ ∑ᵢ ⟪eᵢ, w⟫ eᵢ` does not increase norms
(`Orthonormal.norm_sum_inner_smul_le`), by Bessel's inequality.
-/

@[expose] public section

open scoped InnerProductSpace

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- **Bessel's inequality** for the compression `w ↦ ∑ᵢ ⟪eᵢ, w⟫ eᵢ` onto the span of a finite
orthonormal family: it does not increase norms. -/
lemma Orthonormal.norm_sum_inner_smul_le {ι : Type*} [Fintype ι] {e : ι → H}
    (he : Orthonormal 𝕜 e) (w : H) : ‖∑ i, ⟪e i, w⟫_𝕜 • e i‖ ≤ ‖w‖ := by
  have h : ‖∑ i, ⟪e i, w⟫_𝕜 • e i‖ ^ 2 = ∑ i, ‖⟪e i, w⟫_𝕜‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner 𝕜, he.inner_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RCLike.conj_mul]
    norm_cast
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), h]
  exact he.sum_inner_products_le w
