/-
Copyright (c) 2025 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.VonNeumannAlgebra.MinimalProjection
public import QuantumSystem.ForMathlib.Algebra.Star.PartialIsometry

/-!
# Murray–von Neumann equivalence and the comparison of minimal projections

The comparison theory of projections in a von Neumann algebra `N`, the foundation of the type
classification: the **Murray–von Neumann equivalence** `p ∼[N] q` (a partial isometry `v ∈ N` with
`v⋆v = p`, `vv⋆ = q`), the **subordination** `p ≼[N] q` (`p` is equivalent to a subprojection of
`q`), the calculus of partial isometries, and the comparison theorem for minimal projections
(`IsMinimalProjection.mvNSub_of_isFactor`).

The comparison theorem for arbitrary projections of a factor, `IsFactor.mvNSub_or_mvNSub`,
combines the central-support lemma `IsFactor.exists_mul_ne` with the polar decomposition
(`QuantumSystem.Analysis.VonNeumannAlgebra.PolarDecomposition`) and the additivity of
Murray–von Neumann equivalence over orthogonal families, and is proved in
`QuantumSystem.Analysis.VonNeumannAlgebra.Comparison`. The minimal-projection case here
needs neither, and is the form the type I structure theorem uses.

## Main definitions

* `VonNeumannAlgebra.MvNEquiv N p q` — `p` and `q` are Murray–von Neumann equivalent inside `N`:
  there is a partial isometry `v ∈ N` with source `v⋆v = p` and range `vv⋆ = q`. Written `p ∼[N] q`.
* `VonNeumannAlgebra.MvNSub N p q` — `p ≼[N] q`: `p` is Murray–von Neumann equivalent to a
  subprojection of `q`.

## Main results

* `VonNeumannAlgebra.MvNEquiv.refl` / `symm` / `trans` — Murray–von Neumann equivalence is an
  equivalence relation on the projections of `N`.
* `VonNeumannAlgebra.MvNEquiv.ne_zero`, `VonNeumannAlgebra.IsMinimalProjection.of_mvNEquiv` —
  nonzeroness and minimality transport along Murray–von Neumann equivalence.
* `VonNeumannAlgebra.MvNSub.refl` / `MvNSub.trans` — subordination is a preorder on projections.
* `VonNeumannAlgebra.mvNSub_of_posCorner` — the scaling step of the comparison theorem: a positive
  scalar corner `(q a e)⋆(q a e) = c • e`, `c > 0`, yields `e ≼[N] q`.
* `VonNeumannAlgebra.IsMinimalProjection.mvNSub_of_isFactor` — the comparison theorem for minimal
  projections: in a factor, a minimal projection is subordinate to every nonzero projection.

## Notation

The symbols of the operator-algebra literature live in the opt-in `VonNeumannAlgebra` scope;
activate them with `open scoped VonNeumannAlgebra`.

| Symbol | Expansion | How to activate |
|---|---|---|
| `p ∼[N] q` | `VonNeumannAlgebra.MvNEquiv N p q` | `open scoped VonNeumannAlgebra` |
| `p ≼[N] q` | `VonNeumannAlgebra.MvNSub N p q` | `open scoped VonNeumannAlgebra` |
-/

@[expose] public section

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Murray–von Neumann equivalence -/

/-- **Murray–von Neumann equivalence** of projections inside `N`: there is a partial isometry
`v ∈ N` with source projection `v⋆v = p` and range projection `vv⋆ = q`. -/
def MvNEquiv (N : VonNeumannAlgebra H) (p q : H →L[ℂ] H) : Prop :=
  ∃ v : H →L[ℂ] H, v ∈ N ∧ IsPartialIsometry v ∧ star v * v = p ∧ v * star v = q

/-- `p ∼[N] q` denotes Murray–von Neumann equivalence `MvNEquiv N p q` of projections inside `N`. -/
scoped notation:50 p:51 " ∼[" N "] " q:51 => MvNEquiv N p q

/-- Murray–von Neumann equivalence is reflexive on projections of `N`. -/
lemma MvNEquiv.refl {N : VonNeumannAlgebra H} {p : H →L[ℂ] H}
    (hp : IsStarProjection p) (hpN : p ∈ N) : p ∼[N] p :=
  ⟨p, hpN, hp.isPartialIsometry, by rw [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq],
    by rw [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]⟩

/-- Murray–von Neumann equivalence is symmetric. -/
lemma MvNEquiv.symm {N : VonNeumannAlgebra H} {p q : H →L[ℂ] H}
    (h : p ∼[N] q) : q ∼[N] p := by
  obtain ⟨v, hv, hpi, hvp, hvq⟩ := h
  exact ⟨star v, star_mem hv, IsPartialIsometry.star hpi, by rw [star_star, hvq],
    by rw [star_star, hvp]⟩

/-- Murray–von Neumann equivalence is transitive. -/
lemma MvNEquiv.trans {N : VonNeumannAlgebra H} {p q r : H →L[ℂ] H}
    (hpq : p ∼[N] q) (hqr : q ∼[N] r) : p ∼[N] r := by
  obtain ⟨v, hv, hvpi, hvp, hvq⟩ := hpq
  obtain ⟨w, hw, hwpi, hwq, hwr⟩ := hqr
  have hq : IsStarProjection q := hvq ▸ hvpi.isStarProjection_mul_star_self
  refine ⟨w * v, mul_mem hw hv, ?_, ?_, ?_⟩
  · unfold IsPartialIsometry
    calc w * v * star (w * v) * (w * v)
        = w * (v * star v) * (star w * w) * v := by simp only [star_mul, mul_assoc]
      _ = w * q * q * v := by rw [hvq, hwq]
      _ = w * q * v := by rw [mul_assoc w q q, hq.isIdempotentElem]
      _ = w * (star w * w) * v := by rw [hwq]
      _ = w * v := by rw [← mul_assoc w (star w) w, hwpi]
  · calc star (w * v) * (w * v) = star v * (star w * w) * v := by simp only [star_mul, mul_assoc]
      _ = star v * (v * star v) * v := by rw [hwq, hvq]
      _ = (star v * v) * (star v * v) := by simp only [mul_assoc]
      _ = star v * v := hvpi.isStarProjection_star_mul_self.isIdempotentElem
      _ = p := hvp
  · calc (w * v) * star (w * v) = w * (v * star v) * star w := by simp only [star_mul, mul_assoc]
      _ = w * (star w * w) * star w := by rw [hvq, ← hwq]
      _ = (w * star w) * (w * star w) := by simp only [mul_assoc]
      _ = w * star w := hwpi.isStarProjection_mul_star_self.isIdempotentElem
      _ = r := hwr

/-! ### Comparison of projections -/

/-- The source projection of a Murray–von Neumann equivalence is a star projection. -/
lemma MvNEquiv.isStarProjection_left {N : VonNeumannAlgebra H} {p q : H →L[ℂ] H}
    (h : p ∼[N] q) : IsStarProjection p := by
  obtain ⟨v, _, hpi, hvp, _⟩ := h; exact hvp ▸ hpi.isStarProjection_star_mul_self

/-- The range projection of a Murray–von Neumann equivalence is a star projection. -/
lemma MvNEquiv.isStarProjection_right {N : VonNeumannAlgebra H} {p q : H →L[ℂ] H}
    (h : p ∼[N] q) : IsStarProjection q := by
  obtain ⟨v, _, hpi, _, hvq⟩ := h; exact hvq ▸ hpi.isStarProjection_mul_star_self

/-- The range projection of a Murray–von Neumann equivalence with nonzero source is nonzero. -/
lemma MvNEquiv.ne_zero {N : VonNeumannAlgebra H} {p q : H →L[ℂ] H}
    (h : p ∼[N] q) (hp : p ≠ 0) : q ≠ 0 := by
  obtain ⟨v, _, hvpi, hvp, hvq⟩ := h
  intro hq0
  apply hp
  have hv0 : v = 0 := by
    have hpi : v * star v * v = v := hvpi
    rw [hvq, hq0, zero_mul] at hpi
    exact hpi.symm
  rw [← hvp, hv0]; simp

/-- **Minimality transports along Murray–von Neumann equivalence.** If `e` is a minimal projection
and `e ∼[N] p`, then `p` is minimal: with `v⋆v = e` and `vv⋆ = p`, the corner computes as
`p a p = v (e (v⋆ a v) e) v⋆ = c • v e v⋆ = c • p`. -/
lemma IsMinimalProjection.of_mvNEquiv {N : VonNeumannAlgebra H} {e p : H →L[ℂ] H}
    (he : IsMinimalProjection N e) (h : e ∼[N] p) : IsMinimalProjection N p := by
  have hpproj : IsStarProjection p := h.isStarProjection_right
  have hp0 : p ≠ 0 := h.ne_zero he.2.2.1
  obtain ⟨v, hvN, hvpi, hvp, hvq⟩ := h
  have hpN : p ∈ N := by rw [← hvq]; exact mul_mem hvN (star_mem hvN)
  have hve : v * e = v := by rw [← hvp]; exact hvpi.mul_source
  have hev : e * star v = star v := by
    have := congrArg star hve
    rwa [star_mul, he.1.isSelfAdjoint.star_eq] at this
  refine ⟨hpproj, hpN, hp0, fun a haN => ?_⟩
  obtain ⟨c, hc⟩ := he.2.2.2 (star v * a * v) (mul_mem (mul_mem (star_mem hvN) haN) hvN)
  refine ⟨c, ?_⟩
  calc p * a * p
      = (v * star v) * a * (v * star v) := by rw [hvq]
    _ = (v * e) * (star v * a * v) * (e * star v) := by
        rw [hve, hev]; simp only [mul_assoc]
    _ = v * (e * (star v * a * v) * e) * star v := by simp only [mul_assoc]
    _ = v * (c • e) * star v := by rw [hc]
    _ = c • (v * e * star v) := by simp only [mul_smul_comm, smul_mul_assoc]
    _ = c • p := by rw [hve, hvq]

/-- `p ≼ q` in `N`: `p` is Murray–von Neumann equivalent to a subprojection `q' ≤ q` of `q` in
`N`, the order being the operator order of `H →L[ℂ] H`. -/
def MvNSub (N : VonNeumannAlgebra H) (p q : H →L[ℂ] H) : Prop :=
  ∃ q' ∈ N, q' ≤ q ∧ p ∼[N] q'

/-- `p ≼[N] q` denotes the subordination relation `MvNSub N p q`: `p` is Murray–von Neumann
equivalent to a subprojection of `q` inside `N`. -/
scoped notation:50 p:51 " ≼[" N "] " q:51 => MvNSub N p q

/-- Subordination is reflexive on projections of `N`. -/
lemma MvNSub.refl {N : VonNeumannAlgebra H} {p : H →L[ℂ] H}
    (hp : IsStarProjection p) (hpN : p ∈ N) : p ≼[N] p :=
  ⟨p, hpN, le_rfl, MvNEquiv.refl hp hpN⟩

/-- An equivalence `q ∼[N] r'` transports a subprojection `q' ≤ q` to a subprojection `r'' ≤ r'`
that is Murray–von Neumann equivalent to `q'`. -/
lemma MvNEquiv.exists_le_mvNEquiv {N : VonNeumannAlgebra H} {q r' q' : H →L[ℂ] H}
    (hqr : q ∼[N] r') (hq' : IsStarProjection q') (hq'N : q' ∈ N) (hle : q' ≤ q) :
    ∃ r'' : H →L[ℂ] H, IsStarProjection r'' ∧ r'' ∈ N ∧ r'' ≤ r' ∧ q' ∼[N] r'' := by
  have hsub : q * q' = q' := (hq'.le_iff_mul_eq_right hqr.isStarProjection_left).mp hle
  have hr' : IsStarProjection r' := hqr.isStarProjection_right
  obtain ⟨w, hwN, hwpi, hwq, hwr⟩ := hqr
  have hproj : IsStarProjection (w * q' * star w) := by
    refine ⟨?_, ?_⟩
    · change (w * q' * star w) * (w * q' * star w) = w * q' * star w
      simp only [mul_assoc]
      rw [← mul_assoc (star w) w (q' * star w), hwq, ← mul_assoc q q' (star w), hsub,
        ← mul_assoc q' q' (star w), hq'.isIdempotentElem]
    · change star (w * q' * star w) = w * q' * star w
      rw [star_mul, star_mul, star_star, hq'.isSelfAdjoint.star_eq, mul_assoc]
  refine ⟨w * q' * star w, hproj, mul_mem (mul_mem hwN hq'N) (star_mem hwN),
    (hproj.le_iff_mul_eq_right hr').mpr ?_, ?_⟩
  · rw [← hwr]
    simp only [mul_assoc]
    rw [← mul_assoc (star w) w (q' * star w), hwq, ← mul_assoc q q' (star w), hsub]
  · refine ⟨w * q', mul_mem hwN hq'N, ?_, ?_, ?_⟩
    · change (w * q') * star (w * q') * (w * q') = w * q'
      rw [star_mul, hq'.isSelfAdjoint.star_eq]
      simp only [mul_assoc]
      rw [← mul_assoc (star w) w q', hwq, hsub, hq'.isIdempotentElem, hq'.isIdempotentElem]
    · rw [star_mul, hq'.isSelfAdjoint.star_eq, mul_assoc, ← mul_assoc (star w) w q', hwq, hsub,
        hq'.isIdempotentElem]
    · rw [star_mul, hq'.isSelfAdjoint.star_eq]
      simp only [mul_assoc]
      rw [← mul_assoc q' q' (star w), hq'.isIdempotentElem]

/-- Subordination is transitive: `≼` is a preorder on the projections of `N`. -/
lemma MvNSub.trans {N : VonNeumannAlgebra H} {p q r : H →L[ℂ] H}
    (hpq : p ≼[N] q) (hqr : q ≼[N] r) : p ≼[N] r := by
  obtain ⟨q', hq'N, hqsub, hpq'⟩ := hpq
  obtain ⟨r', hr'N, hrsub, hqr'⟩ := hqr
  obtain ⟨r'', _, hr''N, hr'sub, hq'r''⟩ :=
    hqr'.exists_le_mvNEquiv hpq'.isStarProjection_right hq'N hqsub
  exact ⟨r'', hr''N, hr'sub.trans hrsub, hpq'.trans hq'r''⟩

/-- **Scaling step of the comparison theorem.** If the positive corner element
`(q a e)⋆ (q a e)` equals a positive scalar multiple `c • e` of `e` (with `c > 0`), then `e` is
subordinate to `q`: the normalised element `(√c)⁻¹ • (q a e)` is a partial isometry with source
`e` and range a subprojection of `q`. The hypotheses isolate the two analytic inputs of the
comparison theorem — the corner being scalar (minimality) and its positivity. -/
lemma mvNSub_of_posCorner {N : VonNeumannAlgebra H} {e q a : H →L[ℂ] H}
    (he : IsStarProjection e) (hq : IsStarProjection q)
    (heN : e ∈ N) (hqN : q ∈ N) (haN : a ∈ N)
    {c : ℝ} (hc : 0 < c)
    (hcorner : star (q * a * e) * (q * a * e) = (c : ℂ) • e) :
    e ≼[N] q := by
  set γ : ℂ := ((Real.sqrt c)⁻¹ : ℂ) with hγ
  set v : H →L[ℂ] H := γ • (q * a * e) with hv
  have hvN : v ∈ N := SMulMemClass.smul_mem γ (mul_mem (mul_mem hqN haN) heN)
  have hsrc : star v * v = e := by
    rw [hv, star_smul, smul_mul_smul_comm, hcorner, smul_smul]
    have hstar : star γ = γ := by rw [hγ, star_inv₀, ← starRingEnd_apply, Complex.conj_ofReal]
    rw [hstar, hγ, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt hc.le,
      inv_mul_cancel₀ (by exact_mod_cast hc.ne'), one_smul]
  have hve : v * e = v := by
    rw [hv, smul_mul_assoc, mul_assoc (q * a) e e, he.isIdempotentElem]
  have hvpi : IsPartialIsometry v := by
    unfold IsPartialIsometry
    rw [mul_assoc, hsrc, hve]
  refine ⟨v * star v, mul_mem hvN (star_mem hvN),
    (hvpi.isStarProjection_mul_star_self.le_iff_mul_eq_right hq).mpr ?_, ⟨v, hvN, hvpi, hsrc, rfl⟩⟩
  have hqv : q * v = v := by
    rw [hv, mul_smul_comm, ← mul_assoc, ← mul_assoc, hq.isIdempotentElem]
  rw [← mul_assoc, hqv]

/-- **Positivity of the corner scalar.** For a minimal projection `e` and `a ∈ N` with
`q a e ≠ 0`, the corner element `(q a e)⋆ (q a e) = e (a⋆ q a) e` equals a *strictly positive
real* scalar multiple of `e`. (Reality comes from self-adjointness; strict positivity from
evaluating on a nonzero vector of `e H` on which `q a e` does not vanish.) -/
lemma IsMinimalProjection.posCorner {N : VonNeumannAlgebra H} {e : H →L[ℂ] H}
    (he : IsMinimalProjection N e) {q a : H →L[ℂ] H} (hq : IsStarProjection q)
    (hqN : q ∈ N) (haN : a ∈ N) (hne : q * a * e ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ star (q * a * e) * (q * a * e) = (c : ℂ) • e := by
  set x := q * a * e with hx
  have hxx : star x * x = e * (star a * q * a) * e := by
    rw [hx, star_mul, star_mul, he.1.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq]
    rw [mul_assoc, mul_assoc, mul_assoc, ← mul_assoc q q, hq.isIdempotentElem]
    simp only [mul_assoc]
  obtain ⟨c', hc'⟩ := he.2.2.2 (star a * q * a) (mul_mem (mul_mem (star_mem haN) hqN) haN)
  rw [← hxx] at hc'
  have hconj : (starRingEnd ℂ) c' = c' := by
    have hsa : star (star x * x) = star x * x := by rw [star_mul, star_star]
    rw [hc', star_smul, he.1.isSelfAdjoint.star_eq] at hsa
    rw [starRingEnd_apply]; exact smul_left_injective ℂ he.2.2.1 hsa
  have hxe : x * e = x := by rw [hx, mul_assoc, he.1.isIdempotentElem]
  obtain ⟨η, hη⟩ : ∃ η, x η ≠ 0 := by
    by_contra h
    exact hne (by ext η; exact not_not.mp (not_exists.mp h η))
  set ξ := e η with hξ
  have hxξ : x ξ ≠ 0 := by
    rw [hξ, ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, hxe]; exact hη
  have heξ : e ξ = ξ := by
    rw [hξ, ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, he.1.isIdempotentElem]
  have hξne : ξ ≠ 0 := fun h => hxξ (by rw [h, map_zero])
  have hinner : ‖x ξ‖ ^ 2 = c'.re * ‖ξ‖ ^ 2 := by
    have e1 : inner ℂ ((star x * x) ξ) ξ = inner ℂ (x ξ) (x ξ) := by
      rw [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_left]
    have e2 : inner ℂ ((star x * x) ξ) ξ = (starRingEnd ℂ) c' * inner ℂ ξ ξ := by
      rw [hc', smul_apply, heξ, inner_smul_left]
    have e3 : inner ℂ (x ξ) (x ξ) = (starRingEnd ℂ) c' * inner ℂ ξ ξ := e1.symm.trans e2
    have hre := congrArg RCLike.re e3
    rw [inner_self_eq_norm_sq, inner_self_eq_norm_sq_to_K] at hre
    simp only [RCLike.mul_re, RCLike.mul_im, RCLike.conj_re, RCLike.conj_im, RCLike.ofReal_re,
      RCLike.ofReal_im, pow_two, mul_zero, zero_mul, add_zero, sub_zero] at hre
    rw [show RCLike.re c' = c'.re from rfl] at hre
    nlinarith [hre]
  have hξpos : 0 < ‖ξ‖ ^ 2 := pow_pos (norm_pos_iff.mpr hξne) 2
  have hxξpos : 0 < ‖x ξ‖ ^ 2 := pow_pos (norm_pos_iff.mpr hxξ) 2
  have hcre : c' = (c'.re : ℂ) := (Complex.conj_eq_iff_re.mp hconj).symm
  refine ⟨c'.re, by nlinarith [hinner, hξpos, hxξpos], ?_⟩
  rw [hc']; exact congrArg (· • e) hcre

/-- A minimal projection is subordinate to any projection it "meets": if some `a ∈ N` has
`q a e ≠ 0`, then `e ≼ q`. Combined with central supports (which guarantee `q a e ≠ 0` for every
nonzero `q` in a factor) this yields the comparison theorem `minimal e ≼ q`. -/
lemma IsMinimalProjection.mvNSub_of_ne {N : VonNeumannAlgebra H} {e : H →L[ℂ] H}
    (he : IsMinimalProjection N e) {q a : H →L[ℂ] H} (hq : IsStarProjection q)
    (hqN : q ∈ N) (haN : a ∈ N) (hne : q * a * e ≠ 0) : e ≼[N] q := by
  obtain ⟨c, hcpos, hcorner⟩ := he.posCorner hq hqN haN hne
  exact mvNSub_of_posCorner he.1 hq he.2.1 hqN haN hcpos hcorner

/-- **Comparison theorem (minimal projection case).** In a factor, a minimal projection `e` is
Murray–von Neumann subordinate to *every* nonzero projection `q`: `e ≼ q`. This combines the
scaling lemma (via `mvNSub_of_ne`) with the central-support input
(`IsFactor.exists_mul_ne`, which supplies an `a ∈ N` with `q a e ≠ 0`). It is the form of
comparison needed to show a maximal orthogonal family of minimal projections exhausts the
identity. The comparison of two arbitrary projections of a factor is `IsFactor.mvNSub_or_mvNSub`
(`QuantumSystem.Analysis.VonNeumannAlgebra.Comparison`). -/
theorem IsMinimalProjection.mvNSub_of_isFactor {N : VonNeumannAlgebra H}
    (hN : IsFactor N) {e : H →L[ℂ] H} (he : IsMinimalProjection N e)
    {q : H →L[ℂ] H} (hq : IsStarProjection q) (hqN : q ∈ N) (hq0 : q ≠ 0) :
    e ≼[N] q := by
  have : Nontrivial H := he.nontrivial
  obtain ⟨a, haN, hane⟩ := hN.exists_mul_ne he.2.1 he.2.2.1 hq0
  exact he.mvNSub_of_ne hq hqN haN hane

end VonNeumannAlgebra
