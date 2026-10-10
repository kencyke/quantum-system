/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.VonNeumannAlgebra.PolarDecomposition
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.OrthogonalFamily
public import QuantumSystem.ForMathlib.Analysis.LocallyConvex.StrongOperatorTopology

/-!
# The comparison theorem for factors

Any two projections `p, q` of a factor `N` are comparable in the Murray–von Neumann order:
`p ≼[N] q` or `q ≼[N] p` (`IsFactor.mvNSub_or_mvNSub`). The minimal-projection case
(`IsMinimalProjection.mvNSub_of_isFactor`, in `QuantumSystem.Analysis.VonNeumannAlgebra.Basic`)
needs only a scaling argument; the general case rests on two further ingredients.

1. **Orthogonal sums of partial isometries**, in any von Neumann algebra. A family of partial
   isometries of `N` with pairwise orthogonal source projections and pairwise orthogonal range
   projections has a strong sum, which is again a partial isometry of `N`; its source and range
   projections are the strong sums of the sources and of the ranges. Summability comes from
   Bessel's inequality for the orthogonal source projections
   (`OrthogonalFamily.sum_norm_sq_starProjection_le`) together with the Pythagorean identity for
   the orthogonal ranges. Consequently Murray–von Neumann equivalence is additive
   over orthogonal families.
2. **Local comparison**, in a factor. Nonzero projections `p, q` of a factor have nonzero
   equivalent subprojections: the central-support lemma `IsFactor.exists_mul_ne` gives `a ∈ N`
   with `x = q a p ≠ 0`, and the polar decomposition of `x`
   (`QuantumSystem.Analysis.VonNeumannAlgebra.PolarDecomposition`) makes the range projection
   `R(x⋆) ≤ p` equivalent to the range projection `R(x) ≤ q`.

The theorem then follows from Zorn's lemma, applied to orthogonal families of partial isometries
running from under `p` to under `q`: the strong sum of a maximal family has source `p` or range
`q`, since otherwise local comparison of the two remainders would enlarge the family.

## Conventions

A strong sum `w = ∑ᵢ v_i` is a `HasSum` in the strong operator topology, Mathlib's
`H →Lₚₜ[ℂ] H`, of the operators carried over by `ContinuousLinearMap.toSOT`, written
`HasSum (fun i => ↑ₚₜ (v i)) (↑ₚₜ w)` under `open scoped StrongOperatorTopology`, as in the
resolution of the identity `OrthEquivFam.hasSum_resolutionOfIdentity`. The proofs
evaluate it at vectors, `∀ x, HasSum (fun i => v i x) (w x)`, through
`PointwiseConvergenceCLM.hasSum_toSOT_iff`.

## Main results

* `VonNeumannAlgebra.exists_hasSum_isPartialIsometry` — the strong sum of a family of partial
  isometries of `N` with orthogonal sources and orthogonal ranges is a partial isometry of `N`,
  whose source and range projections are the strong sums of the sources and of the ranges.
* `VonNeumannAlgebra.mvNEquiv_of_hasSum` — **additivity of Murray–von Neumann equivalence**: if
  `p_i ∼[N] q_i` for orthogonal families `(p_i)`, `(q_i)`, then `∑ᵢ p_i ∼[N] ∑ᵢ q_i`.
* `VonNeumannAlgebra.IsFactor.exists_mvNEquiv_le` — local comparison in a factor.
* `VonNeumannAlgebra.IsFactor.mvNSub_or_mvNSub` — **the comparison theorem for factors**.

## TODO

* The comparison theorem for an arbitrary von Neumann algebra (Kadison–Ringrose §6.2, Takesaki
  V.1.8): for projections `p, q ∈ N` there is a central projection `z` of `N` with
  `p z ≼[N] q z` and `q (1 - z) ≼[N] p (1 - z)`; the factor case above is then its corollary at
  `z ∈ {0, 1}`. Only local comparison is factor-specific — orthogonal sums and the polar
  decomposition already hold in any `N` — and it needs the **central support** (central carrier)
  `C_p` of a projection, the least central projection above `p`, together with the general form of
  `IsFactor.exists_mul_ne`: `q N p ≠ 0` iff `C_p C_q ≠ 0`. Neither is developed yet.

## References

* R. V. Kadison, J. R. Ringrose, *Fundamentals of the Theory of Operator Algebras II*, §6.1
  (additivity of equivalence) and §6.2 (the comparison theorem, of which the factor case is the
  statement here).
* M. Takesaki, *Theory of Operator Algebras I*, Theorem V.1.8 (the comparability theorem, of which
  the factor case is the statement here).
-/

@[expose] public section

open scoped InnerProductSpace VonNeumannAlgebra StrongOperatorTopology
open PointwiseConvergenceCLM (hasSum_toSOT_iff)

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Orthogonal families of projections -/

section OrthogonalFamily

variable {ι : Type*} {P : ι → H →L[ℂ] H}

/-- The ranges of pairwise orthogonal star projections form an orthogonal family of subspaces. -/
private lemma orthogonalFamily_range (hP : ∀ i, IsStarProjection (P i))
    (horth : Pairwise fun i j => P i * P j = 0) :
    OrthogonalFamily ℂ (fun i => (P i).range) (fun i => ((P i).range).subtypeₗᵢ) := by
  rintro i j hij ⟨_, u, rfl⟩ ⟨_, w, rfl⟩
  change ⟪P i u, P j w⟫_ℂ = 0
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
    (hP i).isSelfAdjoint.star_eq, ← mul_apply_eq_comp, horth hij, zero_apply, inner_zero_right]

/-- If the strong sum of pairwise orthogonal star projections `P_i` is `R`, then each `P_j` is a
subprojection of `R`: `R P_j = P_j`. -/
private lemma mul_eq_of_hasSum (hP : ∀ i, IsStarProjection (P i))
    (horth : Pairwise fun i j => P i * P j = 0) {R : H →L[ℂ] H}
    (hR : ∀ x, HasSum (fun i => P i x) (R x)) (j : ι) : R * P j = P j := by
  refine ContinuousLinearMap.ext fun x => ?_
  have h := hasSum_single (f := fun i => P i (P j x)) j fun i hij => by
    rw [← mul_apply_eq_comp, horth hij, zero_apply]
  rw [← mul_apply_eq_comp, (hP j).isIdempotentElem.eq] at h
  exact (hR _).unique h

end OrthogonalFamily

/-! ### Orthogonal sums of partial isometries -/

section OrthogonalSum

variable {ι : Type*} {v : ι → H →L[ℂ] H}

/-- Partial isometries with orthogonal range projections satisfy `v_i⋆ v_j = 0` for `i ≠ j`. -/
private lemma star_mul_eq_zero_of_ne (hv : ∀ i, IsPartialIsometry (v i))
    (hrng : Pairwise fun i j => v i * star (v i) * (v j * star (v j)) = 0) {i j : ι}
    (hij : i ≠ j) : star (v i) * v j = 0 := by
  have hsv : star (v i) * v i * star (v i) = star (v i) := by
    have h : star (v i) * star (star (v i)) * star (v i) = star (v i) := (hv i).star
    rwa [star_star] at h
  calc star (v i) * v j = (star (v i) * v i * star (v i)) * (v j * star (v j) * v j) := by
        rw [hsv, hv j]
    _ = star (v i) * (v i * star (v i) * (v j * star (v j))) * v j := by simp only [mul_assoc]
    _ = 0 := by rw [hrng hij, mul_zero, zero_mul]

/-- Partial isometries with orthogonal source projections satisfy `v_i v_j⋆ = 0` for `i ≠ j`. -/
private lemma mul_star_eq_zero_of_ne (hv : ∀ i, IsPartialIsometry (v i))
    (hsrc : Pairwise fun i j => star (v i) * v i * (star (v j) * v j) = 0) {i j : ι}
    (hij : i ≠ j) : v i * star (v j) = 0 := by
  have h := star_mul_eq_zero_of_ne (v := fun i => star (v i)) (fun i => (hv i).star)
    (by simpa only [star_star] using hsrc) hij
  simpa only [star_star] using h

/-- A family of partial isometries with orthogonal source projections and orthogonal range
projections is strongly summable. -/
private lemma exists_hasSum_apply (hv : ∀ i, IsPartialIsometry (v i))
    (hsrc : Pairwise fun i j => star (v i) * v i * (star (v j) * v j) = 0)
    (hrng : Pairwise fun i j => v i * star (v i) * (v j * star (v j)) = 0) :
    ∃ w : H →L[ℂ] H, ∀ x, HasSum (fun i => v i x) (w x) := by
  have hP : ∀ i, IsStarProjection (star (v i) * v i) := fun i =>
    (hv i).isStarProjection_star_mul_self
  have hQ : ∀ i, IsStarProjection (v i * star (v i)) := fun i =>
    (hv i).isStarProjection_mul_star_self
  have hO := orthogonalFamily_range hQ hrng
  have hnorm : ∀ i x, ‖v i x‖ = ‖(star (v i) * v i) x‖ := fun i x => by
    have h := IsPartialIsometry.norm_apply (v := v i) rfl
      (x := (star (v i) * v i) x) (by rw [← mul_apply_eq_comp, (hP i).isIdempotentElem.eq])
    rwa [← mul_apply_eq_comp, (hv i).mul_source] at h
  have hmem : ∀ i x, v i x ∈ (v i * star (v i)).range := fun i x =>
    ⟨v i x, by rw [ContinuousLinearMap.coe_coe, ← mul_apply_eq_comp, hv i]⟩
  have hsum_le : ∀ x (s : Finset ι), ∑ i ∈ s, ‖v i x‖ ^ 2 ≤ ‖x‖ ^ 2 := fun x s => by
    choose _ hPeq using fun i => isStarProjection_iff_eq_starProjection_range.mp (hP i)
    have h := (orthogonalFamily_range hP hsrc).sum_norm_sq_starProjection_le x s
    simpa only [hnorm, ← hPeq] using h
  have hsummable : ∀ x, Summable fun i => v i x := fun x =>
    (hO.summable_iff_norm_sq_summable fun i => ⟨v i x, hmem i x⟩).mpr
      (summable_of_sum_le (fun i => sq_nonneg _) (hsum_le x))
  have hbound : ∀ x, ‖∑' i, v i x‖ ≤ ‖x‖ := fun x => by
    refine le_of_tendsto' (hsummable x).hasSum.norm fun s => ?_
    have h := hO.norm_sum (fun i => ⟨v i x, hmem i x⟩) s
    have h' : ‖∑ i ∈ s, v i x‖ ^ 2 ≤ ‖x‖ ^ 2 := (le_of_eq h).trans (hsum_le x s)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h'
  let f : H →ₗ[ℂ] H :=
    { toFun := fun x => ∑' i, v i x
      map_add' := fun x y => by
        simp only [map_add]
        exact (hsummable x).tsum_add (hsummable y)
      map_smul' := fun c x => by
        simp only [map_smul, RingHom.id_apply]
        exact (hsummable x).tsum_const_smul c }
  exact ⟨f.mkContinuous 1 fun x => by rw [one_mul]; exact hbound x,
    fun x => (hsummable x).hasSum⟩

/-- If `w` is the strong sum of the family `v`, then `v_j⋆ w = v_j⋆ v_j`: the other summands are
annihilated by `v_j⋆`. -/
private lemma star_apply_eq_of_hasSum (hv : ∀ i, IsPartialIsometry (v i))
    (hrng : Pairwise fun i j => v i * star (v i) * (v j * star (v j)) = 0) {w : H →L[ℂ] H}
    (hw : ∀ x, HasSum (fun i => v i x) (w x)) (j : ι) (x : H) :
    star (v j) (w x) = (star (v j) * v j) x := by
  have h : HasSum (fun i => star (v j) (v i x)) ((star (v j) * v j) x) :=
    hasSum_single j fun i hij => by
      rw [← mul_apply_eq_comp, star_mul_eq_zero_of_ne hv hrng hij.symm, zero_apply]
  exact ((hw x).mapL (star (v j))).unique h

/-- If `w` is the strong sum of the family `v`, then `w` extends each `v_j`:
`w (v_j⋆ v_j) = v_j`. -/
private lemma apply_source_eq_of_hasSum (hv : ∀ i, IsPartialIsometry (v i))
    (hsrc : Pairwise fun i j => star (v i) * v i * (star (v j) * v j) = 0) {w : H →L[ℂ] H}
    (hw : ∀ x, HasSum (fun i => v i x) (w x)) (j : ι) (x : H) :
    w ((star (v j) * v j) x) = v j x := by
  have h : HasSum (fun i => v i ((star (v j) * v j) x)) (v j x) := by
    have h₀ := hasSum_single (f := fun i => v i ((star (v j) * v j) x)) j fun i hij => by
      rw [← mul_apply_eq_comp, ← mul_assoc, mul_star_eq_zero_of_ne hv hsrc hij, zero_mul,
        zero_apply]
    rwa [← mul_apply_eq_comp, (hv j).mul_source] at h₀
  exact (hw _).unique h

/-- **Orthogonal sums of partial isometries.** A family `(v_i)` of partial isometries in `N` with
pairwise orthogonal source projections `v_i⋆ v_i` and pairwise orthogonal range projections
`v_i v_i⋆` has a strong sum `w = ∑ᵢ v_i`, a `HasSum` in the strong operator topology
`H →Lₚₜ[ℂ] H`, which is again a partial isometry in `N`; its source and range
projections are the strong sums `w⋆ w = ∑ᵢ v_i⋆ v_i` and `w w⋆ = ∑ᵢ v_i v_i⋆`. -/
lemma exists_hasSum_isPartialIsometry {N : VonNeumannAlgebra H} (hvN : ∀ i, v i ∈ N)
    (hv : ∀ i, IsPartialIsometry (v i))
    (hsrc : Pairwise fun i j => star (v i) * v i * (star (v j) * v j) = 0)
    (hrng : Pairwise fun i j => v i * star (v i) * (v j * star (v j)) = 0) :
    ∃ w ∈ N, IsPartialIsometry w ∧
      HasSum (fun i => ↑ₚₜ (v i)) (↑ₚₜ w) ∧
      HasSum (fun i => ↑ₚₜ (star (v i) * v i)) (↑ₚₜ (star w * w)) ∧
      HasSum (fun i => ↑ₚₜ (v i * star (v i))) (↑ₚₜ (w * star w)) := by
  have hv' : ∀ i, IsPartialIsometry (star (v i)) := fun i => (hv i).star
  have hsrc' : Pairwise fun i j =>
      star (star (v i)) * star (v i) * (star (star (v j)) * star (v j)) = 0 := by
    simpa only [star_star] using hrng
  have hrng' : Pairwise fun i j =>
      star (v i) * star (star (v i)) * (star (v j) * star (star (v j))) = 0 := by
    simpa only [star_star] using hsrc
  obtain ⟨w, hw⟩ := exists_hasSum_apply hv hsrc hrng
  obtain ⟨w', hw'⟩ := exists_hasSum_apply (v := fun i => star (v i)) hv' hsrc' hrng'
  -- The adjoint of the sum is the sum of the adjoints.
  have hstar : star w = w' := by
    rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    have h₁ : HasSum (fun i => ⟪star (v i) x, y⟫_ℂ) ⟪w' x, y⟫_ℂ := by
      simpa only [innerSLFlip_apply_apply] using (hw' x).mapL (innerSLFlip ℂ y)
    have h₂ : HasSum (fun i => ⟪x, v i y⟫_ℂ) ⟪x, w y⟫_ℂ := by
      simpa only [innerSL_apply_apply] using (hw y).mapL (innerSL ℂ x)
    refine h₁.unique ?_
    simpa only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
      using h₂
  have hsw := star_apply_eq_of_hasSum hv hrng hw
  have hsw' := star_apply_eq_of_hasSum hv' hrng' hw'
  simp only [star_star] at hsw'
  have hP : ∀ x, HasSum (fun i => (star (v i) * v i) x) ((star w * w) x) := fun x => by
    have h := hw' (w x)
    simp only [hsw] at h
    rwa [mul_apply_eq_comp, hstar]
  have hQ : ∀ x, HasSum (fun i => (v i * star (v i)) x) ((w * star w) x) := fun x => by
    have h := hw (w' x)
    simp only [hsw'] at h
    rwa [mul_apply_eq_comp, hstar]
  have hpi : IsPartialIsometry w := by
    refine ContinuousLinearMap.ext fun x => ?_
    have h := (hP x).mapL w
    simp only [apply_source_eq_of_hasSum hv hsrc hw] at h
    rw [mul_apply_eq_comp]
    exact h.unique (hw x)
  have hwN : w ∈ N := by
    rw [← N.commutant_commutant, mem_commutant_iff]
    intro y hy
    refine ContinuousLinearMap.ext fun x => ?_
    have h := (hw x).mapL y
    have hcomm : ∀ i, y (v i x) = v i (y x) := fun i => by
      rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, mem_commutant_iff.mp hy (v i) (hvN i)]
    simp only [hcomm] at h
    rw [mul_apply_eq_comp, mul_apply_eq_comp]
    exact h.unique (hw (y x))
  exact ⟨w, hwN, hpi, hasSum_toSOT_iff.mpr hw, hasSum_toSOT_iff.mpr hP,
    hasSum_toSOT_iff.mpr hQ⟩

/-- **Additivity of Murray–von Neumann equivalence.** If `p_i ∼[N] q_i` for families of pairwise
orthogonal projections `(p_i)` and `(q_i)`, then their strong sums, `HasSum`s in the strong
operator topology `H →Lₚₜ[ℂ] H`, are equivalent: `∑ᵢ p_i ∼[N] ∑ᵢ q_i`. The
implementing partial isometry is the strong sum of the partial isometries implementing the
`p_i ∼[N] q_i` (`exists_hasSum_isPartialIsometry`). -/
theorem mvNEquiv_of_hasSum {N : VonNeumannAlgebra H} {p q : ι → H →L[ℂ] H}
    (h : ∀ i, p i ∼[N] q i) (hp : Pairwise fun i j => p i * p j = 0)
    (hq : Pairwise fun i j => q i * q j = 0) {P Q : H →L[ℂ] H}
    (hP : HasSum (fun i => ↑ₚₜ (p i)) (↑ₚₜ P)) (hQ : HasSum (fun i => ↑ₚₜ (q i)) (↑ₚₜ Q)) :
    P ∼[N] Q := by
  rw [hasSum_toSOT_iff] at hP hQ
  choose v hvN hv hvp hvq using h
  obtain ⟨w, hwN, hw, -, hsrc, hrng⟩ := exists_hasSum_isPartialIsometry hvN hv
    (by simpa only [hvp] using hp) (by simpa only [hvq] using hq)
  rw [hasSum_toSOT_iff] at hsrc hrng
  refine ⟨w, hwN, hw, ContinuousLinearMap.ext fun x => ?_, ContinuousLinearMap.ext fun x => ?_⟩
  · exact (hsrc x).unique (by simpa only [hvp] using hP x)
  · exact (hrng x).unique (by simpa only [hvq] using hQ x)

end OrthogonalSum

/-! ### Comparison of projections in a factor -/

variable {N : VonNeumannAlgebra H}

/-- **Local comparison in a factor.** Two nonzero projections `p, q` of a factor `N` have nonzero
Murray–von Neumann equivalent subprojections `p' ≤ p`, `q' ≤ q`. The central-support lemma
`IsFactor.exists_mul_ne` supplies `a ∈ N` with `x = q a p ≠ 0`, and the polar decomposition of `x`
makes the range projections `R(x⋆) ≤ p` and `R(x) ≤ q` equivalent (`mvNEquiv_rangeProj`). -/
lemma IsFactor.exists_mvNEquiv_le (hN : IsFactor N) {p q : H →L[ℂ] H}
    (hp : IsStarProjection p) (hpN : p ∈ N) (hp0 : p ≠ 0)
    (hq : IsStarProjection q) (hqN : q ∈ N) (hq0 : q ≠ 0) :
    ∃ p' q' : H →L[ℂ] H, p' ≠ 0 ∧ p' ≤ p ∧ q' ≤ q ∧ p' ∼[N] q' := by
  obtain ⟨a, haN, hx0⟩ := hN.exists_mul_ne hpN hp0 hq0
  set x := q * a * p with hx
  have hxN : x ∈ N := mul_mem (mul_mem hqN haN) hpN
  have hqx : q * x = x := by rw [hx, ← mul_assoc, ← mul_assoc, hq.isIdempotentElem.eq]
  have hpx : p * star x = star x := by
    rw [hx, star_mul, star_mul, hp.isSelfAdjoint.star_eq, ← mul_assoc p p,
      hp.isIdempotentElem.eq]
  exact ⟨_, _, ContinuousLinearMap.rangeProj_ne_zero (star_ne_zero.mpr hx0),
    ((star x).rangeProj_le_iff hp).mpr hpx, (x.rangeProj_le_iff hq).mpr hqx, mvNEquiv_rangeProj hxN⟩

/-- **Comparison theorem for factors.** Any two projections `p, q` of a factor `N` are comparable
in the Murray–von Neumann order: `p ≼[N] q` or `q ≼[N] p`.

By Zorn's lemma take a maximal set `S` of nonzero partial isometries `v ∈ N` with source under `p`
(`v p = v`) and range under `q` (`q v = v`), with pairwise orthogonal sources and pairwise
orthogonal ranges. Their strong sum `w` (`exists_hasSum_isPartialIsometry`) is a partial isometry
in `N` with source `p₀ = w⋆ w ≤ p` and range `q₀ = w w⋆ ≤ q`. If both `p - p₀` and `q - q₀` were
nonzero, local comparison (`IsFactor.exists_mvNEquiv_le`) would produce a nonzero partial
isometry from under `p - p₀` to under `q - q₀`, orthogonal to every member of `S`, contradicting
maximality. Hence `p₀ = p`, so `p ∼[N] q₀ ≤ q`, or `q₀ = q`, so `q ∼[N] p₀ ≤ p`. -/
theorem IsFactor.mvNSub_or_mvNSub (hN : IsFactor N) {p q : H →L[ℂ] H}
    (hp : IsStarProjection p) (hpN : p ∈ N) (hq : IsStarProjection q) (hqN : q ∈ N) :
    p ≼[N] q ∨ q ≼[N] p := by
  have hsymm : ∀ {a b : H →L[ℂ] H}, IsSelfAdjoint a → IsSelfAdjoint b → a * b = 0 →
      b * a = 0 := fun ha hb h => by
    simpa only [star_mul, ha.star_eq, hb.star_eq, star_zero] using congrArg star h
  -- Zorn: a maximal orthogonal family of partial isometries from under `p` to under `q`.
  obtain ⟨S, ⟨hSmem, hSorth⟩, hSmax⟩ := zorn_subset
    {S : Set (H →L[ℂ] H) | (∀ v ∈ S, v ∈ N ∧ IsPartialIsometry v ∧ v ≠ 0 ∧ v * p = v ∧ q * v = v) ∧
      S.Pairwise fun v w => star v * v * (star w * w) = 0 ∧ v * star v * (w * star w) = 0}
    (by
      intro c hc hchain
      refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
      · rintro v ⟨s, hsc, hvs⟩
        exact (hc hsc).1 v hvs
      · rintro v ⟨s, hsc, hvs⟩ w ⟨t, htc, hwt⟩ hvw
        rcases hchain.total hsc htc with h | h
        · exact (hc htc).2 (h hvs) hwt hvw
        · exact (hc hsc).2 hvs (h hwt) hvw)
  have hsrcS : Pairwise fun i j : S =>
      star (i : H →L[ℂ] H) * i * (star (j : H →L[ℂ] H) * j) = 0 :=
    fun i j hij => (hSorth i.2 j.2 (Subtype.coe_ne_coe.mpr hij)).1
  have hrngS : Pairwise fun i j : S =>
      (i : H →L[ℂ] H) * star (i : H →L[ℂ] H) * ((j : H →L[ℂ] H) * star (j : H →L[ℂ] H)) = 0 :=
    fun i j hij => (hSorth i.2 j.2 (Subtype.coe_ne_coe.mpr hij)).2
  -- The strong sum `w` of the family.
  obtain ⟨w, hwN, hw, hwsum, hP₀sum, hQ₀sum⟩ :=
    exists_hasSum_isPartialIsometry (v := fun i : S => (i : H →L[ℂ] H))
      (fun i => (hSmem i i.2).1) (fun i => (hSmem i i.2).2.1) hsrcS hrngS
  rw [hasSum_toSOT_iff] at hwsum hP₀sum hQ₀sum
  set P₀ := star w * w with hP₀def
  set Q₀ := w * star w with hQ₀def
  have hP₀ : IsStarProjection P₀ := hw.isStarProjection_star_mul_self
  have hQ₀ : IsStarProjection Q₀ := hw.isStarProjection_mul_star_self
  have hP₀N : P₀ ∈ N := mul_mem (star_mem hwN) hwN
  have hQ₀N : Q₀ ∈ N := mul_mem hwN (star_mem hwN)
  have hwp : w * p = w := ContinuousLinearMap.ext fun x => by
    have h := hwsum (p x)
    have hvp : ∀ i : S, (i : H →L[ℂ] H) (p x) = (i : H →L[ℂ] H) x := fun i => by
      rw [← mul_apply_eq_comp, (hSmem i i.2).2.2.2.1]
    simp only [hvp] at h
    exact h.unique (hwsum x)
  have hqw : q * w = w := ContinuousLinearMap.ext fun x => by
    have h := (hwsum x).mapL q
    have hqv : ∀ i : S, q ((i : H →L[ℂ] H) x) = (i : H →L[ℂ] H) x := fun i => by
      rw [← mul_apply_eq_comp, (hSmem i i.2).2.2.2.2]
    simp only [hqv] at h
    exact h.unique (hwsum x)
  have hpP₀ : p * P₀ = P₀ := by
    have h := congrArg star (show P₀ * p = P₀ by rw [hP₀def, mul_assoc, hwp])
    rwa [star_mul, hp.isSelfAdjoint.star_eq, hP₀.isSelfAdjoint.star_eq] at h
  have hqQ₀ : q * Q₀ = Q₀ := by rw [hQ₀def, ← mul_assoc, hqw]
  by_cases hPp : P₀ = p
  · exact Or.inl ⟨Q₀, hQ₀N, (hQ₀.le_iff_mul_eq_right hq).mpr hqQ₀, w, hwN, hw, hPp, rfl⟩
  by_cases hQq : Q₀ = q
  · refine Or.inr ⟨P₀, hP₀N, (hP₀.le_iff_mul_eq_right hp).mpr hpP₀, star w, star_mem hwN, hw.star,
      ?_, ?_⟩
    · rw [star_star]
      exact hQq
    · rw [star_star]
  -- Otherwise the remainders `r = p - P₀` and `s = q - Q₀` are nonzero projections of `N`.
  exfalso
  set r := p - P₀ with hr
  set s := q - Q₀ with hs
  have hrproj : IsStarProjection r := hP₀.sub_of_mul_eq_right hp hpP₀
  have hsproj : IsStarProjection s := hQ₀.sub_of_mul_eq_right hq hqQ₀
  have hr0 : r ≠ 0 := fun h => hPp (sub_eq_zero.mp h).symm
  have hs0 : s ≠ 0 := fun h => hQq (sub_eq_zero.mp h).symm
  obtain ⟨p', q', hp'0, hrp', hsq', u, huN, hu, hup', huq'⟩ :=
    hN.exists_mvNEquiv_le hrproj (sub_mem hpN hP₀N) hr0 hsproj (sub_mem hqN hQ₀N) hs0
  have hp' : IsStarProjection p' := hup' ▸ hu.isStarProjection_star_mul_self
  have hq'' : IsStarProjection q' := huq' ▸ hu.isStarProjection_mul_star_self
  replace hrp' : r * p' = p' := (hp'.le_iff_mul_eq_right hrproj).mp hrp'
  replace hsq' : s * q' = q' := (hq''.le_iff_mul_eq_right hsproj).mp hsq'
  have hpr : p * r = r := by rw [hr, mul_sub, hp.isIdempotentElem.eq, hpP₀]
  have hqs : q * s = s := by rw [hs, mul_sub, hq.isIdempotentElem.eq, hqQ₀]
  have hpp' : p * p' = p' := by rw [← hrp', ← mul_assoc, hpr]
  have hqq' : q * q' = q' := by rw [← hsq', ← mul_assoc, hqs]
  have hp'p : p' * p = p' := hp.mul_eq_left_of_mul_eq_right hp' hpp'
  have hp'r : p' * r = p' := hrproj.mul_eq_left_of_mul_eq_right hp' hrp'
  have hq's : q' * s = q' := hsproj.mul_eq_left_of_mul_eq_right hq'' hsq'
  -- The new partial isometry `u` runs from under `p` to under `q` ...
  have hu0 : u ≠ 0 := fun h => hp'0 (by rw [← hup', h, star_zero, zero_mul])
  have hup : u * p = u := by
    calc u * p = u * (star u * u) * p := by rw [hu.mul_source]
      _ = u * (p' * p) := by rw [hup', mul_assoc]
      _ = u := by rw [hp'p, ← hup', hu.mul_source]
  have hqu : q * u = u := by
    have hu' : u * star u * u = u := hu
    calc q * u = q * (u * star u * u) := by rw [hu']
      _ = u := by rw [huq', ← mul_assoc, hqq', ← huq', hu']
  -- ... and is orthogonal to every member of `S`.
  have hP₀v : ∀ v ∈ S, P₀ * (star v * v) = star v * v := fun v hv =>
    mul_eq_of_hasSum (P := fun i : S => star (i : H →L[ℂ] H) * (i : H →L[ℂ] H))
      (fun i => (hSmem i i.2).2.1.isStarProjection_star_mul_self) hsrcS hP₀sum ⟨v, hv⟩
  have hQ₀v : ∀ v ∈ S, Q₀ * (v * star v) = v * star v := fun v hv =>
    mul_eq_of_hasSum (P := fun i : S => (i : H →L[ℂ] H) * star (i : H →L[ℂ] H))
      (fun i => (hSmem i i.2).2.1.isStarProjection_mul_star_self) hrngS hQ₀sum ⟨v, hv⟩
  have hpv : ∀ v ∈ S, p * (star v * v) = star v * v := fun v hv => by
    have h := congrArg star (show star v * v * p = star v * v by
      rw [mul_assoc, (hSmem v hv).2.2.2.1])
    rwa [star_mul, hp.isSelfAdjoint.star_eq, (IsSelfAdjoint.star_mul_self v).star_eq] at h
  have hqv : ∀ v ∈ S, q * (v * star v) = v * star v := fun v hv => by
    rw [← mul_assoc, (hSmem v hv).2.2.2.2]
  have horth : ∀ v ∈ S, star u * u * (star v * v) = 0 ∧ u * star u * (v * star v) = 0 :=
    fun v hv => by
      constructor
      · rw [hup', ← hp'r, mul_assoc, hr, sub_mul, hpv v hv, hP₀v v hv, sub_self, mul_zero]
      · rw [huq', ← hq's, mul_assoc, hs, sub_mul, hqv v hv, hQ₀v v hv, sub_self, mul_zero]
  have hmem : insert u S ∈ {S : Set (H →L[ℂ] H) |
      (∀ v ∈ S, v ∈ N ∧ IsPartialIsometry v ∧ v ≠ 0 ∧ v * p = v ∧ q * v = v) ∧
        S.Pairwise fun v w => star v * v * (star w * w) = 0 ∧ v * star v * (w * star w) = 0} := by
    refine ⟨?_, hSorth.insert fun v hv _ => ⟨horth v hv, ?_, ?_⟩⟩
    · rintro v (rfl | hv)
      · exact ⟨huN, hu, hu0, hup, hqu⟩
      · exact hSmem v hv
    · exact hsymm (IsSelfAdjoint.star_mul_self u) (IsSelfAdjoint.star_mul_self v) (horth v hv).1
    · exact hsymm (IsSelfAdjoint.mul_star_self u) (IsSelfAdjoint.mul_star_self v) (horth v hv).2
  -- Maximality puts `u` into `S`, where it is orthogonal to itself: `p' = 0`.
  have huS : u ∈ S := hSmax hmem (Set.subset_insert u S) (Set.mem_insert u S)
  have h₁ : P₀ * p' = p' := by rw [← hup']; exact hP₀v u huS
  exact hp'0 (by rw [← hrp', hr, sub_mul, hpp', h₁, sub_self])

end VonNeumannAlgebra
