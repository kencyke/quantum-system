module

public import QuantumSystem.Algebra.VonNeumannAlgebra.CentralProjection

/-!
# Comparison of projections in a von Neumann algebra

Building on `Factor.lean`, this file develops the basic calculus underlying Murray–von Neumann
comparison theory: the source/range identities of partial isometries, the symmetry of the
subprojection relation, and the subordination relation `MvNSub N p q` ("`p` is equivalent to a
subprojection of `q`").

The full comparison theorem (any two projections in a factor are comparable) requires central
supports and polar decomposition; it is developed in subsequent steps.

## Main definitions

* `VonNeumannAlgebra.MvNSub N p q` — `p ≼[N] q`: `p` is Murray–von Neumann equivalent to a
  subprojection of `q`.

## Main results

* `MvNEquiv.isStarProjection_left` / `isStarProjection_right` — the endpoints of an equivalence
  are star projections.
* `isStarProjection_subproj_comm` — the subprojection relation `e * f = f` is left/right symmetric
  for projections.
* `IsPartialIsometry.range_mul_self` / `mul_source` — the range and source projections act as
  one-sided identities.
* `MvNEquiv.exists_subproj_equiv` — an equivalence `q ∼[N] r'` transports a subprojection
  `q' ≤ q` to a subprojection of `r'` equivalent to `q'`.
* `MvNSub.refl` / `MvNSub.trans` — subordination is a preorder on projections.
* `mvNSub_of_posCorner` — the scaling step of the comparison theorem: a positive scalar corner
  `(q a e)⋆(q a e) = c • e`, `c > 0`, yields `e ≼[N] q`.

## Notation

The subordination symbol lives in the opt-in `VonNeumannAlgebra` scope (alongside `∼[N]` from
`Factor.lean`); activate it with `open scoped VonNeumannAlgebra`.

| Symbol | Expansion | How to activate |
|---|---|---|
| `p ≼[N] q` | `VonNeumannAlgebra.MvNSub N p q` | `open scoped VonNeumannAlgebra` |
-/

@[expose] public section

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The source projection of a Murray–von Neumann equivalence is a star projection. -/
theorem MvNEquiv.isStarProjection_left {N : VonNeumannAlgebra H} {p q : H →L[ℂ] H}
    (h : p ∼[N] q) : IsStarProjection p := by
  obtain ⟨v, _, hpi, hvp, _⟩ := h; exact hvp ▸ hpi.isStarProjection_star_mul_self

/-- The range projection of a Murray–von Neumann equivalence is a star projection. -/
theorem MvNEquiv.isStarProjection_right {N : VonNeumannAlgebra H} {p q : H →L[ℂ] H}
    (h : p ∼[N] q) : IsStarProjection q := by
  obtain ⟨v, _, hpi, _, hvq⟩ := h; exact hvq ▸ hpi.isStarProjection_mul_star_self

/-- For projections, the subprojection relation `e * f = f` is left/right symmetric. -/
theorem isStarProjection_subproj_comm {R : Type*} [Ring R] [StarRing R] {e f : R}
    (he : IsStarProjection e) (hf : IsStarProjection f) (h : e * f = f) : f * e = f := by
  have := congrArg star h
  rwa [star_mul, he.isSelfAdjoint.star_eq, hf.isSelfAdjoint.star_eq] at this

/-- The range projection of a partial isometry acts as a left identity. -/
theorem IsPartialIsometry.range_mul_self {R : Type*} [Monoid R] [StarMul R] {v : R}
    (h : IsPartialIsometry v) : (v * star v) * v = v := h

/-- The source projection of a partial isometry acts as a right identity. -/
theorem IsPartialIsometry.mul_source {R : Type*} [Monoid R] [StarMul R] {v : R}
    (h : IsPartialIsometry v) : v * (star v * v) = v := by rw [← mul_assoc]; exact h

/-- `p ≼ q` in `N`: `p` is Murray–von Neumann equivalent to a subprojection of `q`. -/
def MvNSub (N : VonNeumannAlgebra H) (p q : H →L[ℂ] H) : Prop :=
  ∃ q' : H →L[ℂ] H, q' ∈ N ∧ q * q' = q' ∧ p ∼[N] q'

/-- `p ≼[N] q` denotes the subordination relation `MvNSub N p q`: `p` is Murray–von Neumann
equivalent to a subprojection of `q` inside `N`. -/
scoped notation:50 p:51 " ≼[" N "] " q:51 => MvNSub N p q

/-- Subordination is reflexive on projections of `N`. -/
theorem MvNSub.refl {N : VonNeumannAlgebra H} {p : H →L[ℂ] H}
    (hp : IsStarProjection p) (hpN : p ∈ N) : p ≼[N] p :=
  ⟨p, hpN, hp.isIdempotentElem, MvNEquiv.refl hp hpN⟩

/-- An equivalence `q ∼[N] r'` transports a subprojection `q' ≤ q` to a subprojection of `r'` that
is Murray–von Neumann equivalent to `q'`. -/
theorem MvNEquiv.exists_subproj_equiv {N : VonNeumannAlgebra H} {q r' q' : H →L[ℂ] H}
    (hqr : q ∼[N] r') (hq' : IsStarProjection q') (hq'N : q' ∈ N) (hsub : q * q' = q') :
    ∃ r'' : H →L[ℂ] H, IsStarProjection r'' ∧ r'' ∈ N ∧ r' * r'' = r'' ∧ q' ∼[N] r'' := by
  obtain ⟨w, hwN, hwpi, hwq, hwr⟩ := hqr
  refine ⟨w * q' * star w, ⟨?_, ?_⟩, mul_mem (mul_mem hwN hq'N) (star_mem hwN), ?_, ?_⟩
  · change (w * q' * star w) * (w * q' * star w) = w * q' * star w
    simp only [mul_assoc]
    rw [← mul_assoc (star w) w (q' * star w), hwq, ← mul_assoc q q' (star w), hsub,
      ← mul_assoc q' q' (star w), hq'.isIdempotentElem]
  · change star (w * q' * star w) = w * q' * star w
    rw [star_mul, star_mul, star_star, hq'.isSelfAdjoint.star_eq, mul_assoc]
  · rw [← hwr]
    simp only [mul_assoc]
    rw [← mul_assoc (star w) w (q' * star w), hwq, ← mul_assoc q q' (star w), hsub]
  · refine ⟨w * q', mul_mem hwN hq'N, ?_, ?_, ?_⟩
    · change (w * q') * star (w * q') * (w * q') = w * q'
      rw [star_mul, hq'.isSelfAdjoint.star_eq]
      simp only [mul_assoc]
      rw [← mul_assoc (star w) w q', hwq, hsub, hq'.isIdempotentElem, hq'.isIdempotentElem]
    · change star (w * q') * (w * q') = q'
      rw [star_mul, hq'.isSelfAdjoint.star_eq, mul_assoc, ← mul_assoc (star w) w q', hwq, hsub,
        hq'.isIdempotentElem]
    · change (w * q') * star (w * q') = w * q' * star w
      rw [star_mul, hq'.isSelfAdjoint.star_eq]
      simp only [mul_assoc]
      rw [← mul_assoc q' q' (star w), hq'.isIdempotentElem]

/-- Subordination is transitive: `≼` is a preorder on the projections of `N`. -/
theorem MvNSub.trans {N : VonNeumannAlgebra H} {p q r : H →L[ℂ] H}
    (hpq : p ≼[N] q) (hqr : q ≼[N] r) : p ≼[N] r := by
  obtain ⟨q', hq'N, hqsub, hpq'⟩ := hpq
  obtain ⟨r', hr'N, hrsub, hqr'⟩ := hqr
  obtain ⟨r'', _, hr''N, hr'sub, hq'r''⟩ :=
    hqr'.exists_subproj_equiv hpq'.isStarProjection_right hq'N hqsub
  refine ⟨r'', hr''N, ?_, hpq'.trans hq'r''⟩
  calc r * r'' = r * (r' * r'') := by rw [hr'sub]
    _ = (r * r') * r'' := by rw [mul_assoc]
    _ = r' * r'' := by rw [hrsub]
    _ = r'' := hr'sub

/-- **Scaling step of the comparison theorem.** If the positive corner element
`(q a e)⋆ (q a e)` equals a positive scalar multiple `c • e` of `e` (with `c > 0`), then `e` is
subordinate to `q`: the normalised element `(√c)⁻¹ • (q a e)` is a partial isometry with source
`e` and range a subprojection of `q`. The hypotheses isolate the two analytic inputs of the
comparison theorem — the corner being scalar (minimality) and its positivity. -/
theorem mvNSub_of_posCorner {N : VonNeumannAlgebra H} {e q a : H →L[ℂ] H}
    (he : IsStarProjection e) (hq : IsStarProjection q)
    (heN : e ∈ N) (hqN : q ∈ N) (haN : a ∈ N)
    {c : ℝ} (hc : 0 < c)
    (hcorner : star (q * a * e) * (q * a * e) = (c : ℂ) • e) :
    e ≼[N] q := by
  set γ : ℂ := ((Real.sqrt c)⁻¹ : ℂ) with hγ
  set v : H →L[ℂ] H := γ • (q * a * e) with hv
  have hvN : v ∈ N := smul_mem γ (mul_mem (mul_mem hqN haN) heN)
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
  refine ⟨v * star v, mul_mem hvN (star_mem hvN), ?_, ⟨v, hvN, hvpi, hsrc, rfl⟩⟩
  have hqv : q * v = v := by
    rw [hv, mul_smul_comm, ← mul_assoc, ← mul_assoc, hq.isIdempotentElem]
  rw [← mul_assoc, hqv]

/-- **Positivity of the corner scalar.** For a minimal projection `e` and `a ∈ N` with
`q a e ≠ 0`, the corner element `(q a e)⋆ (q a e) = e (a⋆ q a) e` equals a *strictly positive
real* scalar multiple of `e`. (Reality comes from self-adjointness; strict positivity from
evaluating on a nonzero vector of `e H` on which `q a e` does not vanish.) -/
theorem IsMinimalProjection.posCorner {N : VonNeumannAlgebra H} {e : H →L[ℂ] H}
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
      rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_left]
    have e2 : inner ℂ ((star x * x) ξ) ξ = (starRingEnd ℂ) c' * inner ℂ ξ ξ := by
      rw [hc', ContinuousLinearMap.smul_apply, heξ, inner_smul_left]
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
theorem IsMinimalProjection.mvNSub_of_ne {N : VonNeumannAlgebra H} {e : H →L[ℂ] H}
    (he : IsMinimalProjection N e) {q a : H →L[ℂ] H} (hq : IsStarProjection q)
    (hqN : q ∈ N) (haN : a ∈ N) (hne : q * a * e ≠ 0) : e ≼[N] q := by
  obtain ⟨c, hcpos, hcorner⟩ := he.posCorner hq hqN haN hne
  exact mvNSub_of_posCorner he.1 hq he.2.1 hqN haN hcpos hcorner

/-- **Comparison theorem (minimal projection case).** In a factor, a minimal projection `e` is
Murray–von Neumann subordinate to *every* nonzero projection `q`: `e ≼ q`. This combines the
scaling lemma (via `mvNSub_of_ne`) with the central-support input
(`IsFactor.exists_mul_ne`, which supplies an `a ∈ N` with `q a e ≠ 0`). It is the form of
comparison needed to show a maximal orthogonal family of minimal projections exhausts the
identity. -/
theorem IsMinimalProjection.mvNSub_of_isFactor [Nontrivial H] {N : VonNeumannAlgebra H}
    (hN : IsFactor N) {e : H →L[ℂ] H} (he : IsMinimalProjection N e)
    {q : H →L[ℂ] H} (hq : IsStarProjection q) (hqN : q ∈ N) (hq0 : q ≠ 0) :
    e ≼[N] q := by
  obtain ⟨a, haN, hane⟩ := hN.exists_mul_ne he.2.1 he.2.2.1 hq0
  exact he.mvNSub_of_ne hq hqN haN hane

end VonNeumannAlgebra
