/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Bessel's inequality for an orthogonal family of subspaces

For an orthogonal family `(V i)` of subspaces of an inner product space `E`, each admitting an
orthogonal projection, the orthogonal projections of a vector `x` satisfy **Bessel's inequality**
`∑ᵢ ‖P_{V i} x‖² ≤ ‖x‖²`. Mathlib states Bessel's inequality for orthonormal families of vectors
(`Orthonormal.sum_inner_products_le`); this is its form for orthogonal families of subspaces, the
case of the one-dimensional subspaces `𝕜 eᵢ` being the vector version.

The proof uses only the Pythagorean identity of `OrthogonalFamily.norm_sum`: for
`y = ∑_{i ∈ s} P_{V i} x`, `‖y‖² = ∑_{i ∈ s} ‖P_{V i} x‖² = re ⟪y, x⟫ ≤ ‖y‖ ‖x‖`.

## Main results

* `OrthogonalFamily.sum_norm_sq_starProjection_le` — **Bessel's inequality**
  `∑_{i ∈ s} ‖P_{V i} x‖² ≤ ‖x‖²` over every finite set `s`.
* `OrthogonalFamily.summable_norm_sq_starProjection`,
  `OrthogonalFamily.tsum_norm_sq_starProjection_le` — its infinite form `∑ᵢ ‖P_{V i} x‖² ≤ ‖x‖²`.
* `OrthogonalFamily.summable_starProjection` — in a complete space, `∑ᵢ P_{V i} x` converges.
-/

@[expose] public section

open scoped InnerProductSpace

namespace OrthogonalFamily

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {V : ι → Submodule 𝕜 E} [∀ i, (V i).HasOrthogonalProjection]

/-- **Bessel's inequality** for an orthogonal family of subspaces: the orthogonal projections of
`x` onto the members of the family satisfy `∑_{i ∈ s} ‖P_{V i} x‖² ≤ ‖x‖²` for every finite `s`. -/
theorem sum_norm_sq_starProjection_le
    (hV : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) (x : E) (s : Finset ι) :
    ∑ i ∈ s, ‖(V i).starProjection x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  set y := ∑ i ∈ s, (V i).starProjection x with hy
  have hy2 : ‖y‖ ^ 2 = ∑ i ∈ s, ‖(V i).starProjection x‖ ^ 2 :=
    hV.norm_sum (fun i => ⟨(V i).starProjection x, (V i).starProjection_apply_mem x⟩) s
  have hre : RCLike.re ⟪y, x⟫_𝕜 = ‖y‖ ^ 2 := by
    rw [hy2, hy, sum_inner, map_sum]
    exact Finset.sum_congr rfl fun i _ => (V i).re_inner_starProjection_eq_normSq x
  have hle : ‖y‖ ^ 2 ≤ ‖y‖ * ‖x‖ :=
    hre ▸ (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  rw [← hy2]
  nlinarith [norm_nonneg y, norm_nonneg x]

/-- For an orthogonal family of subspaces, `i ↦ ‖P_{V i} x‖²` is summable (Bessel). -/
lemma summable_norm_sq_starProjection
    (hV : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) (x : E) :
    Summable fun i => ‖(V i).starProjection x‖ ^ 2 :=
  summable_of_sum_le (fun _ => sq_nonneg _) (hV.sum_norm_sq_starProjection_le x)

/-- **Bessel's inequality**, infinite form: `∑ᵢ ‖P_{V i} x‖² ≤ ‖x‖²` for an orthogonal family of
subspaces. -/
lemma tsum_norm_sq_starProjection_le
    (hV : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) (x : E) :
    ∑' i, ‖(V i).starProjection x‖ ^ 2 ≤ ‖x‖ ^ 2 :=
  (hV.summable_norm_sq_starProjection x).tsum_le_of_sum_le (hV.sum_norm_sq_starProjection_le x)

/-- In a complete space, the orthogonal projections of `x` onto an orthogonal family of subspaces
are summable: `∑ᵢ P_{V i} x` converges. -/
lemma summable_starProjection [CompleteSpace E]
    (hV : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) (x : E) :
    Summable fun i => (V i).starProjection x :=
  (hV.summable_iff_norm_sq_summable
    fun i => ⟨(V i).starProjection x, (V i).starProjection_apply_mem x⟩).mpr
    (hV.summable_norm_sq_starProjection x)

end OrthogonalFamily
