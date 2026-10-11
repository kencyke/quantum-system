/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
public import Mathlib.LinearAlgebra.Complex.Module
public import QuantumSystem.Analysis.VonNeumannAlgebra.Factor
public import QuantumSystem.ForMathlib.Algebra.Star.PartialIsometry
public import QuantumSystem.ForMathlib.Analysis.VonNeumannAlgebra.Commutant
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.Abs

/-!
# Minimal projections of a von Neumann algebra

The **minimal projections** of a von Neumann algebra `N` (`IsMinimalProjection`: a nonzero star
projection with trivial corner `p N p = ℂ p`), the **abelian projections** (`IsAbelianProjection`:
a star projection with commutative corner `p N p`), and criteria for minimality.

* **Definitions and invariance.** A minimal projection is order-minimal
  (`IsMinimalProjection.no_proper_subprojection`) and abelian; both notions are invariant under
  spatial isomorphisms `N ↦ U N U⋆` and, being intrinsic to the `⋆`-algebra, under abstract
  `⋆`-isomorphisms `N ≃⋆ₐ M`.

* **Order-minimality forces the trivial corner.** A nonzero projection `p ∈ N` with no proper
  nonzero subprojection in `N` is minimal. The positive/negative parts of a self-adjoint corner
  element (non-unital continuous functional calculus inside the norm-closed corner subalgebra)
  yield an order dichotomy, and a Dedekind-cut argument on `{c : ℝ | 0 ≤ x - c • p}` pins each
  self-adjoint corner element to a real multiple of `p`.
* **In a factor, abelian projections are minimal.** An abelian projection of a factor is
  order-minimal, by a corner-commutation argument through the central-support lemma
  `IsFactor.exists_mul_ne`; hence it is minimal.
* **The minimal projections of `B(H)` are the rank-one projections** `|u⟩⟨u|`, `‖u‖ = 1`;
  equivalently, the star projections with one-dimensional range.

These are the ingredients of the minimal-projection characterisation of type I factors
(`QuantumSystem.Analysis.VonNeumannAlgebra.TypeI.Defs`).

## Main definitions

* `VonNeumannAlgebra.IsMinimalProjection N e` — `e` is a nonzero star projection in `N` with
  trivial corner `e N e = ℂ e`. This implies the order-theoretic minimality (no proper nonzero
  subprojection in `N`: any projection `f ∈ N` with `f ≤ e` is `0` or `e`), recorded as
  `IsMinimalProjection.no_proper_subprojection`.
* `VonNeumannAlgebra.IsAbelianProjection N p` — `p` is a star projection in `N` with commutative
  corner `p N p`.
* `VonNeumannAlgebra.cornerNonUnitalStarSubalgebra N hp` — the norm-closed corner `{y ∈ N | p y
  = y = y p}`.

## Main results

* `VonNeumannAlgebra.isMinimalProjection_conj_iff`,
  `VonNeumannAlgebra.isMinimalProjection_starAlgEquiv_iff` — minimal projections are invariant
  under spatial isomorphisms `N ↦ U N U⋆` and under abstract `⋆`-isomorphisms `N ≃⋆ₐ M`
  (`VonNeumannAlgebra.isMinimalProjection_coe_iff`).
* `VonNeumannAlgebra.IsFactor.subprojection_eq_of_isAbelianProjection` — in a factor, an abelian
  projection has no proper nonzero subprojection.
* `VonNeumannAlgebra.rangeProj_mem` — the range projection `R(x)` of `x ∈ N` lies in `N`.
* `VonNeumannAlgebra.isMinimalProjection_of_forall_subprojection` — order-minimality implies the
  trivial corner.
* `VonNeumannAlgebra.IsFactor.isMinimalProjection_of_isAbelianProjection` — in a factor, a
  nonzero abelian projection is minimal.
* `VonNeumannAlgebra.isMinimalProjection_rankOne_boundedLinearOperators`,
  `VonNeumannAlgebra.exists_isMinimalProjection_boundedLinearOperators` — rank-one projections are
  minimal in `B(H)`, which therefore has a minimal projection when `H ≠ 0`.
* `VonNeumannAlgebra.isMinimalProjection_boundedLinearOperators_iff`,
  `VonNeumannAlgebra.isMinimalProjection_boundedLinearOperators_iff_finrank` — conversely, every
  minimal projection of `B(H)` is a rank-one projection `|u⟩⟨u|`, `‖u‖ = 1`; equivalently, the
  minimal projections of `B(H)` are the star projections with one-dimensional range.
-/

@[expose] public section

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


/-! ### Minimal and abelian projections -/

/-- A **minimal projection** of `N`: a nonzero star projection `e ∈ N` whose corner is trivial,
`e N e = ℂ e`. This is the conventional operator-algebraic definition (Takesaki, Kadison–Ringrose);
it implies minimality in the order sense (no proper nonzero subprojection), recorded as
`IsMinimalProjection.no_proper_subprojection`. The corner formulation is the one that
supports comparison theory without invoking Borel functional calculus. -/
def IsMinimalProjection (N : VonNeumannAlgebra H) (e : H →L[ℂ] H) : Prop :=
  IsStarProjection e ∧ e ∈ N ∧ e ≠ 0 ∧ ∀ a ∈ N, ∃ c : ℂ, e * a * e = c • e

/-- A von Neumann algebra with a minimal projection acts on a nonzero space: the minimal
projection is nonzero, so it sends some vector to a nonzero vector, witnessing `Nontrivial H`. -/
lemma IsMinimalProjection.nontrivial {N : VonNeumannAlgebra H} {e : H →L[ℂ] H}
    (he : IsMinimalProjection N e) : Nontrivial H :=
  nontrivial_of_ne_zero he.2.2.1

/-- A minimal projection has no proper nonzero subprojection in `N`: if a projection `f ∈ N`
satisfies `f ≤ e` (the operator order, equivalently the range inclusion `ran f ⊆ ran e`), then
`f = 0` or `f = e`. This recovers the order-theoretic form of minimality from the corner definition
`e N e = ℂ e`. -/
lemma IsMinimalProjection.no_proper_subprojection {N : VonNeumannAlgebra H}
    {e : H →L[ℂ] H} (he : IsMinimalProjection N e)
    {f : H →L[ℂ] H} (hf : IsStarProjection f) (hfN : f ∈ N) (hle : f ≤ e) :
    f = 0 ∨ f = e := by
  have hsub : e * f = f := (hf.le_iff_mul_eq_right he.1).mp hle
  have hfe : f * e = f := by
    have := congrArg star hsub
    rwa [star_mul, he.1.isSelfAdjoint.star_eq, hf.isSelfAdjoint.star_eq] at this
  have hefe : e * f * e = f := by rw [hsub, hfe]
  obtain ⟨c, hc⟩ := he.2.2.2 f hfN
  rw [hefe] at hc
  have hidem : f * f = f := hf.isIdempotentElem
  rw [hc] at hidem
  have h2 : (c • e) * (c • e) = (c * c) • (e : H →L[ℂ] H) := by
    rw [smul_mul_smul_comm, he.1.isIdempotentElem]
  have hcc : (c * c) • (e : H →L[ℂ] H) = c • e := by rw [← h2, hidem]
  have hc2 : c * c = c := smul_left_injective ℂ he.2.2.1 hcc
  have h0 : c * (c - 1) = 0 := by rw [mul_sub, mul_one, hc2, sub_self]
  rcases mul_eq_zero.mp h0 with h | h
  · exact Or.inl (by rw [hc, h, zero_smul])
  · exact Or.inr (by rw [hc, sub_eq_zero.mp h, one_smul])

/-- An **abelian projection** of `N`: a star projection `p ∈ N` whose corner `p N p` is
commutative. Minimal projections are abelian (`IsMinimalProjection.isAbelianProjection`); the
general type I property (`IsTypeI`) is phrased through abelian projections. -/
def IsAbelianProjection (N : VonNeumannAlgebra H) (p : H →L[ℂ] H) : Prop :=
  IsStarProjection p ∧ p ∈ N ∧
    ∀ a ∈ N, ∀ b ∈ N, (p * a * p) * (p * b * p) = (p * b * p) * (p * a * p)

/-- A minimal projection is abelian: its corner `e N e = ℂ e` is one-dimensional, hence
commutative. -/
lemma IsMinimalProjection.isAbelianProjection {N : VonNeumannAlgebra H} {e : H →L[ℂ] H}
    (he : IsMinimalProjection N e) : IsAbelianProjection N e := by
  refine ⟨he.1, he.2.1, fun a haN b hbN => ?_⟩
  obtain ⟨c, hc⟩ := he.2.2.2 a haN
  obtain ⟨d, hd⟩ := he.2.2.2 b hbN
  rw [hc, hd, smul_mul_smul_comm, smul_mul_smul_comm, mul_comm c d]

section Conj

variable {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']

/-- **Minimal projections are spatially invariant**: if `e` is a minimal projection of `N`, then
`U e U⋆` is a minimal projection of `U N U⋆`. -/
lemma IsMinimalProjection.conj {N : VonNeumannAlgebra H} {e : H →L[ℂ] H}
    (he : IsMinimalProjection N e) (U : H ≃ₗᵢ[ℂ] H') :
    IsMinimalProjection (conj U N) (U.conjStarAlgEquiv e) := by
  obtain ⟨hp, hmem, hne, hcorner⟩ := he
  refine ⟨hp.map U.conjStarAlgEquiv, (conjStarAlgEquiv_mem_conj_iff U N).mpr hmem,
    fun h => hne (U.conjStarAlgEquiv.injective (h.trans (map_zero _).symm)), fun a ha => ?_⟩
  rw [mem_conj_iff] at ha
  obtain ⟨c, hc⟩ := hcorner _ ha
  refine ⟨c, ?_⟩
  have := congrArg U.conjStarAlgEquiv hc
  rwa [map_mul, map_mul, StarAlgEquiv.apply_symm_apply, map_smul] at this

/-- `U e U⋆` is a minimal projection of `U N U⋆` iff `e` is a minimal projection of `N`. -/
lemma isMinimalProjection_conj_iff {N : VonNeumannAlgebra H} {e : H →L[ℂ] H}
    (U : H ≃ₗᵢ[ℂ] H') :
    IsMinimalProjection (conj U N) (U.conjStarAlgEquiv e) ↔ IsMinimalProjection N e := by
  refine ⟨fun h => ?_, fun h => h.conj U⟩
  obtain ⟨hp, hmem, hne, hcorner⟩ := h
  refine ⟨?_, (conjStarAlgEquiv_mem_conj_iff U N).mp hmem, ?_, fun a ha => ?_⟩
  · have := hp.map U.conjStarAlgEquiv.symm
    rwa [StarAlgEquiv.symm_apply_apply] at this
  · rintro rfl; exact hne (map_zero _)
  · obtain ⟨c, hc⟩ := hcorner _ ((conjStarAlgEquiv_mem_conj_iff U N).mpr ha)
    refine ⟨c, ?_⟩
    have := congrArg U.conjStarAlgEquiv.symm hc
    rwa [map_mul, map_mul, StarAlgEquiv.symm_apply_apply, StarAlgEquiv.symm_apply_apply,
      map_smul, StarAlgEquiv.symm_apply_apply] at this

end Conj

/-! ### Invariance under abstract `⋆`-isomorphisms

Being a minimal projection is a property of the abstract `⋆`-algebra `N`: the corner condition
`e N e = ℂ e` only involves products inside `N`, so it is carried along any `⋆`-algebra
isomorphism `N ≃⋆ₐ M` between von Neumann algebras on possibly different Hilbert spaces. -/

section StarAlgEquiv

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {N : VonNeumannAlgebra H} {M : VonNeumannAlgebra K}

/-- **Minimality is intrinsic to the `⋆`-algebra.** For `x ∈ N`, being a minimal projection of `N`
is the algebraic condition that `x` is a nonzero star projection of the `⋆`-algebra `N` with trivial
corner `x N x = ℂ x`, computed inside `N`. -/
lemma isMinimalProjection_coe_iff {x : N} :
    IsMinimalProjection N (x : H →L[ℂ] H) ↔
      IsStarProjection x ∧ x ≠ 0 ∧ ∀ a : N, ∃ c : ℂ, x * a * x = c • x := by
  have hproj : IsStarProjection (x : H →L[ℂ] H) ↔ IsStarProjection x := by
    simp only [isStarProjection_iff, IsIdempotentElem, isSelfAdjoint_iff, Subtype.ext_iff]
    rfl
  simp only [IsMinimalProjection, hproj, x.2, true_and, ne_eq, Subtype.ext_iff]
  refine and_congr_right fun _ => and_congr_right fun _ => ⟨fun h a => ?_, fun h a ha => ?_⟩
  · exact h a a.2
  · exact h ⟨a, ha⟩

/-- **Minimal projections are carried along `⋆`-isomorphisms**: if `x` is a minimal projection of
`N` and `φ : N ≃⋆ₐ M`, then `φ x` is a minimal projection of `M`. The corner condition at `φ x`
against `a ∈ M` is the image under `φ` of the corner condition at `x` against `φ⁻¹ a`. -/
lemma IsMinimalProjection.map_starAlgEquiv {x : N} (hx : IsMinimalProjection N (x : H →L[ℂ] H))
    (φ : N ≃⋆ₐ[ℂ] M) : IsMinimalProjection M (φ x : K →L[ℂ] K) := by
  rw [isMinimalProjection_coe_iff] at hx ⊢
  obtain ⟨hp, hne, hcorner⟩ := hx
  refine ⟨hp.map φ, (map_ne_zero_iff φ (EquivLike.injective φ)).mpr hne, fun a => ?_⟩
  obtain ⟨c, hc⟩ := hcorner (φ.symm a)
  refine ⟨c, ?_⟩
  have := congrArg φ hc
  rwa [map_mul, map_mul, StarAlgEquiv.apply_symm_apply, map_smul] at this

/-- **Minimal projections are invariant under `⋆`-isomorphisms**: for `φ : N ≃⋆ₐ M`, `φ x` is a
minimal projection of `M` iff `x` is a minimal projection of `N`. -/
lemma isMinimalProjection_starAlgEquiv_iff (φ : N ≃⋆ₐ[ℂ] M) {x : N} :
    IsMinimalProjection M (φ x : K →L[ℂ] K) ↔ IsMinimalProjection N (x : H →L[ℂ] H) := by
  refine ⟨fun h => ?_, fun h => h.map_starAlgEquiv φ⟩
  have := h.map_starAlgEquiv φ.symm
  rwa [StarAlgEquiv.symm_apply_apply] at this

end StarAlgEquiv

/-- **In a factor, an abelian projection is order-minimal**: a projection `q ∈ N` with `q ≤ p`
is `0` or `p`.

The proof avoids corner-commutant theory and polar decomposition: if `0 ≠ q ≠ p`, then
`r := p - q` is a nonzero projection under `p` orthogonal to `q`, and the central-support lemma
`IsFactor.exists_mul_ne` produces `a ∈ N` with `z := r a q ≠ 0`. Both `z` and `z⋆` are corner
elements of `p`, so they commute by abelianness; but `q z = 0` and `q z⋆ = z⋆` force
`z⋆ z = q (z z⋆) = (q z) z⋆ = 0`, and the C⋆-identity gives `z = 0` — a contradiction. -/
lemma IsFactor.subprojection_eq_of_isAbelianProjection {N : VonNeumannAlgebra H}
    (hN : IsFactor N) {p : H →L[ℂ] H} (hp : IsAbelianProjection N p)
    {q : H →L[ℂ] H} (hq : IsStarProjection q) (hqN : q ∈ N) (hle : q ≤ p) :
    q = 0 ∨ q = p := by
  have hsub : p * q = q := (hq.le_iff_mul_eq_right hp.1).mp hle
  by_cases hq0 : q = 0
  · exact Or.inl hq0
  have : Nontrivial H := nontrivial_of_ne_zero hq0
  by_cases hqp : q = p
  · exact Or.inr hqp
  exfalso
  have hqmul : q * p = q := hp.1.mul_eq_left_of_mul_eq_right hq hsub
  set r : H →L[ℂ] H := p - q with hr
  have hpr : p * r = r := by
    rw [hr, mul_sub, hp.1.isIdempotentElem, hsub]
  have hqr : q * r = 0 := by
    rw [hr, mul_sub, hqmul, hq.isIdempotentElem, sub_self]
  have hrsa : star r = r := by
    rw [hr, star_sub, hp.1.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq]
  have hrN : r ∈ N := sub_mem hp.2.1 hqN
  have hr0 : r ≠ 0 := fun h0 => hqp (by rw [hr, sub_eq_zero] at h0; exact h0.symm)
  obtain ⟨a, haN, hz0⟩ := hN.exists_mul_ne hqN hq0 hr0
  set z : H →L[ℂ] H := r * a * q with hz
  have hzN : z ∈ N := mul_mem (mul_mem hrN haN) hqN
  have hzcorner : p * z * p = z := by
    rw [hz]
    calc p * (r * a * q) * p
        = (p * r) * a * (q * p) := by simp only [mul_assoc]
      _ = r * a * q := by rw [hpr, hqmul]
  have hzstar : star z = q * (star a * r) := by
    rw [hz, star_mul, star_mul, hrsa, hq.isSelfAdjoint.star_eq]
  have hcomm : z * star z = star z * z := by
    have hzc : p * star z * p = star z := by
      have h2 := congrArg star hzcorner
      rw [star_mul, star_mul, hp.1.isSelfAdjoint.star_eq] at h2
      rw [mul_assoc]
      exact h2
    have h1 := hp.2.2 z hzN (star z) (star_mem hzN)
    rwa [hzcorner, hzc] at h1
  have hqz : q * z = 0 := by
    rw [hz, ← mul_assoc, ← mul_assoc, hqr, zero_mul, zero_mul]
  have hqstarz : q * star z = star z := by
    rw [hzstar, ← mul_assoc, hq.isIdempotentElem]
  have hzz0 : star z * z = 0 := by
    have h6 : q * (z * star z) = q * (star z * z) := by rw [hcomm]
    rw [← mul_assoc, hqz, zero_mul] at h6
    rw [← mul_assoc, hqstarz] at h6
    exact h6.symm
  have hznorm : ‖z‖ = 0 := by
    have hmul := CStarRing.norm_star_mul_self (x := z)
    rw [hzz0, norm_zero] at hmul
    exact mul_self_eq_zero.mp hmul.symm
  exact hz0 (norm_eq_zero.mp hznorm)

/-! ### The corner subalgebra

The elements of `N` supported on a star projection `p` on both sides form a norm-closed
non-unital star subalgebra. Norm-closedness is what lets the non-unital continuous functional
calculus (`cfcₙ_mem`) operate inside the corner: the positive and negative parts of a
self-adjoint corner element stay in the corner. -/

/-- The **corner** of `N` at a star projection `p`: the elements of `N` supported on `p` on
both sides, as a non-unital star subalgebra of `B(H)`. -/
def cornerNonUnitalStarSubalgebra (N : VonNeumannAlgebra H) {p : H →L[ℂ] H}
    (hp : IsStarProjection p) : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H) where
  carrier := {y | y ∈ N ∧ p * y = y ∧ y * p = y}
  add_mem' := by
    rintro y z ⟨hyN, hpy, hyp⟩ ⟨hzN, hpz, hzp⟩
    exact ⟨add_mem hyN hzN, by rw [mul_add, hpy, hpz], by rw [add_mul, hyp, hzp]⟩
  zero_mem' := ⟨zero_mem _, mul_zero p, zero_mul p⟩
  mul_mem' := by
    rintro y z ⟨hyN, hpy, hyp⟩ ⟨hzN, hpz, hzp⟩
    exact ⟨mul_mem hyN hzN, by rw [← mul_assoc, hpy], by rw [mul_assoc, hzp]⟩
  smul_mem' := by
    rintro c y ⟨hyN, hpy, hyp⟩
    exact ⟨SMulMemClass.smul_mem c hyN, by rw [mul_smul_comm, hpy], by rw [smul_mul_assoc, hyp]⟩
  star_mem' := by
    rintro y ⟨hyN, hpy, hyp⟩
    refine ⟨star_mem hyN, ?_, ?_⟩
    · have h := congrArg star hyp
      rwa [star_mul, hp.isSelfAdjoint.star_eq] at h
    · have h := congrArg star hpy
      rwa [star_mul, hp.isSelfAdjoint.star_eq] at h

/-- Membership in the corner subalgebra, unfolded. -/
lemma mem_cornerNonUnitalStarSubalgebra_iff {N : VonNeumannAlgebra H} {p : H →L[ℂ] H}
    {hp : IsStarProjection p} {y : H →L[ℂ] H} :
    y ∈ cornerNonUnitalStarSubalgebra N hp ↔ y ∈ N ∧ p * y = y ∧ y * p = y :=
  Iff.rfl

/-- The corner subalgebra is norm-closed: it is the intersection of the (double-centralizer,
hence closed) carrier of `N` with the closed support conditions `p * y = y` and `y * p = y`. -/
lemma isClosed_cornerNonUnitalStarSubalgebra (N : VonNeumannAlgebra H) {p : H →L[ℂ] H}
    (hp : IsStarProjection p) :
    IsClosed ((cornerNonUnitalStarSubalgebra N hp : Set (H →L[ℂ] H))) := by
  have hset : (cornerNonUnitalStarSubalgebra N hp : Set (H →L[ℂ] H))
      = (N : Set (H →L[ℂ] H)) ∩ ({y | p * y = y} ∩ {y | y * p = y}) := by
    ext y
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩⟩
  rw [hset]
  refine N.isClosed_coe.inter (IsClosed.inter ?_ ?_)
  · exact isClosed_eq (continuous_const.mul continuous_id) continuous_id
  · exact isClosed_eq (continuous_id.mul continuous_const) continuous_id

/-- The positive part of a corner element stays in the corner. -/
lemma posPart_mem_cornerNonUnitalStarSubalgebra {N : VonNeumannAlgebra H} {p : H →L[ℂ] H}
    (hp : IsStarProjection p) {d : H →L[ℂ] H}
    (hd : d ∈ cornerNonUnitalStarSubalgebra N hp) :
    d⁺ ∈ cornerNonUnitalStarSubalgebra N hp := by
  have : IsClosed ((cornerNonUnitalStarSubalgebra N hp : Set (H →L[ℂ] H))) :=
    isClosed_cornerNonUnitalStarSubalgebra N hp
  have : IsScalarTower ℝ ℂ (H →L[ℂ] H) := IsScalarTower.complexToReal
  rw [CFC.posPart_def]
  exact cfcₙ_mem _ hd

/-- The negative part of a corner element stays in the corner. -/
lemma negPart_mem_cornerNonUnitalStarSubalgebra {N : VonNeumannAlgebra H} {p : H →L[ℂ] H}
    (hp : IsStarProjection p) {d : H →L[ℂ] H}
    (hd : d ∈ cornerNonUnitalStarSubalgebra N hp) :
    d⁻ ∈ cornerNonUnitalStarSubalgebra N hp := by
  have : IsClosed ((cornerNonUnitalStarSubalgebra N hp : Set (H →L[ℂ] H))) :=
    isClosed_cornerNonUnitalStarSubalgebra N hp
  have : IsScalarTower ℝ ℂ (H →L[ℂ] H) := IsScalarTower.complexToReal
  rw [CFC.negPart_def]
  exact cfcₙ_mem _ hd

/-! ### Range projections -/

/-- The range projection `R(x)` of `x ∈ N` lies in `N`, because the closure of the range of `x` is
invariant under the commutant. -/
lemma rangeProj_mem {N : VonNeumannAlgebra H} {x : H →L[ℂ] H} (hx : x ∈ N) :
    x.rangeProj ∈ N := by
  rw [IsStarProjection.mem_iff (x.isStarProjection_rangeProj) N]
  intro y hyN'
  rw [ContinuousLinearMap.range_rangeProj]
  have hcl : IsClosed ((x.range.topologicalClosure.comap (y : H →ₗ[ℂ] H)) : Set H) := by
    rw [Submodule.comap_coe]
    exact (x.range.isClosed_topologicalClosure).preimage y.continuous
  refine Submodule.topologicalClosure_minimal _ ?_ hcl
  rintro z ⟨v, rfl⟩
  simp only [Submodule.mem_comap, ContinuousLinearMap.coe_coe]
  have hxy : x * y = y * x := mem_commutant_iff.mp hyN' x hx
  rw [show y (x v) = (y * x) v from rfl, ← hxy]
  exact Submodule.le_topologicalClosure _ ⟨y v, rfl⟩

/-! ### Order-minimality implies corner triviality

The dichotomy: a self-adjoint corner element of an order-minimal projection is comparable to `0`
in the Loewner order, because its positive and negative parts would otherwise produce two
orthogonal nonzero subprojections of `p`. A Dedekind-cut argument on
`{c : ℝ | 0 ≤ x - c • p}` then pins every self-adjoint corner element to `x = c₀ • p`. -/

/-- **Dichotomy.** If `p` has no proper nonzero subprojection in `N`, every self-adjoint corner
element `d` satisfies `0 ≤ d` or `d ≤ 0`. -/
lemma nonneg_or_nonpos_of_forall_subprojection {N : VonNeumannAlgebra H}
    {p : H →L[ℂ] H} (hp : IsStarProjection p) (hp0 : p ≠ 0)
    (hmin : ∀ q, IsStarProjection q → q ∈ N → q ≤ p → q = 0 ∨ q = p)
    {d : H →L[ℂ] H} (hdsa : IsSelfAdjoint d)
    (hd : d ∈ cornerNonUnitalStarSubalgebra N hp) :
    0 ≤ d ∨ d ≤ 0 := by
  have hdplus := posPart_mem_cornerNonUnitalStarSubalgebra hp hd
  have hdminus := negPart_mem_cornerNonUnitalStarSubalgebra hp hd
  have hsub : d⁺ - d⁻ = d := CFC.posPart_sub_negPart d hdsa
  by_cases hplus0 : d⁺ = 0
  · right
    rw [← hsub, hplus0, zero_sub]
    exact neg_nonpos.mpr (CFC.negPart_nonneg d)
  by_cases hminus0 : d⁻ = 0
  · left
    rw [← hsub, hminus0, sub_zero]
    exact CFC.posPart_nonneg d
  exfalso
  have hPplus := hmin _ (d⁺).isStarProjection_rangeProj (rangeProj_mem hdplus.1)
    (((d⁺).rangeProj_le_iff hp).mpr hdplus.2.1)
  have hPminus := hmin _ (d⁻).isStarProjection_rangeProj (rangeProj_mem hdminus.1)
    (((d⁻).rangeProj_le_iff hp).mpr hdminus.2.1)
  rcases hPplus with h | hPp
  · exact ContinuousLinearMap.rangeProj_ne_zero hplus0 h
  rcases hPminus with h | hPm
  · exact ContinuousLinearMap.rangeProj_ne_zero hminus0 h
  have horth := ContinuousLinearMap.rangeProj_mul_rangeProj_eq_zero (x₁ := d⁺) (x₂ := d⁻) (by
    rw [← ContinuousLinearMap.star_eq_adjoint, (CFC.posPart_nonneg d).isSelfAdjoint.star_eq]
    exact CFC.posPart_mul_negPart d)
  rw [hPp, hPm, hp.isIdempotentElem] at horth
  exact hp0 horth

/-- **Cut.** If `p` has no proper nonzero subprojection in `N`, every self-adjoint corner
element is a real multiple of `p`: the supremum `c₀` of `{c : ℝ | 0 ≤ x - c • p}` (nonempty,
bounded, closed) satisfies `x = c₀ • p`, since by the dichotomy `x - c • p ≤ 0` for every
`c > c₀`. -/
lemma exists_real_smul_eq_of_forall_subprojection {N : VonNeumannAlgebra H}
    {p : H →L[ℂ] H} (hp : IsStarProjection p) (hpN : p ∈ N) (hp0 : p ≠ 0)
    (hmin : ∀ q, IsStarProjection q → q ∈ N → q ≤ p → q = 0 ∨ q = p)
    {x : H →L[ℂ] H} (hxsa : IsSelfAdjoint x)
    (hx : x ∈ cornerNonUnitalStarSubalgebra N hp) :
    ∃ c : ℝ, x = (c : ℂ) • p := by
  obtain ⟨hxN, hpx, hxp⟩ := hx
  -- positivity of a self-adjoint operator through diagonal inner products
  have hpos_iff : ∀ T : H →L[ℂ] H, IsSelfAdjoint T →
      (0 ≤ T ↔ ∀ v, 0 ≤ RCLike.re (inner ℂ (T v) v)) := by
    intro T hT
    rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_def']
    simp only [ContinuousLinearMap.reApplyInnerSelf_apply]
    exact ⟨fun h => h.2, fun h => ⟨hT, h⟩⟩
  have hsa_c : ∀ c : ℝ, IsSelfAdjoint (x - (c : ℂ) • p) := by
    intro c
    rw [IsSelfAdjoint, star_sub, star_smul, hxsa.star_eq, hp.isSelfAdjoint.star_eq,
      Complex.star_def, Complex.conj_ofReal]
  have hcalc : ∀ (c : ℝ) (v : H), RCLike.re (inner ℂ ((x - (c : ℂ) • p) v) v)
      = RCLike.re (inner ℂ (x v) v) - c * RCLike.re (inner ℂ (p v) v) := by
    intro c v
    rw [sub_apply, smul_apply, inner_sub_left,
      inner_smul_left, Complex.conj_ofReal, map_sub,
      show RCLike.re ((c : ℂ) * inner ℂ (p v) v) = c * RCLike.re (inner ℂ (p v) v) from
        RCLike.re_ofReal_mul c _]
  have hpvv : ∀ v, RCLike.re (inner ℂ (p v) v) = ‖p v‖ ^ 2 := by
    intro v
    have h1 : inner ℂ (p v) v = inner ℂ (p v) (p v) := by
      calc inner ℂ (p v) v = inner ℂ (p (p v)) v := by
            rw [show p (p v) = (p * p) v from rfl, hp.isIdempotentElem]
        _ = inner ℂ (ContinuousLinearMap.adjoint p (p v)) v := by
            rw [hp.isSelfAdjoint.adjoint_eq]
        _ = inner ℂ (p v) (p v) := ContinuousLinearMap.adjoint_inner_left p v (p v)
    rw [h1, inner_self_eq_norm_sq]
  -- the cut set
  set A : Set ℝ := {c : ℝ | 0 ≤ x - (c : ℂ) • p} with hA
  have hmemA : ∀ c : ℝ, c ∈ A ↔
      ∀ v, c * ‖p v‖ ^ 2 ≤ RCLike.re (inner ℂ (x v) v) := by
    intro c
    rw [hA, Set.mem_ofPred_eq, hpos_iff _ (hsa_c c)]
    constructor
    · intro h v
      have := h v
      rw [hcalc, hpvv, sub_nonneg] at this
      exact this
    · intro h v
      rw [hcalc, hpvv, sub_nonneg]
      exact h v
  -- `x` is supported on the corner: `re ⟪x v, v⟫ = re ⟪x (p v), p v⟫`
  have hxvv : ∀ v, RCLike.re (inner ℂ (x v) v) = RCLike.re (inner ℂ (x (p v)) (p v)) := by
    intro v
    have h1 : x v = x (p v) := by rw [← mul_apply_eq_comp, hxp]
    have h2 : x (p v) = p (x (p v)) := by
      rw [show p (x (p v)) = (p * x) (p v) from rfl, hpx]
    calc RCLike.re (inner ℂ (x v) v) = RCLike.re (inner ℂ (p (x (p v))) v) := by
          conv_lhs => rw [h1, h2]
      _ = RCLike.re (inner ℂ (x (p v)) (p v)) := by
          have h3 : inner ℂ (p (x (p v))) v = inner ℂ (x (p v)) (p v) := by
            conv_lhs => rw [show p (x (p v)) = ContinuousLinearMap.adjoint p (x (p v)) by
              rw [hp.isSelfAdjoint.adjoint_eq]]
            exact ContinuousLinearMap.adjoint_inner_left p v (x (p v))
          rw [h3]
  -- nonempty: `-‖x‖ ∈ A`
  have hAne : A.Nonempty := by
    refine ⟨-‖x‖, (hmemA _).mpr fun v => ?_⟩
    rw [hxvv]
    have hbound : |RCLike.re (inner ℂ (x (p v)) (p v))| ≤ ‖x‖ * ‖p v‖ ^ 2 := by
      calc |RCLike.re (inner ℂ (x (p v)) (p v))| ≤ ‖inner ℂ (x (p v)) (p v)‖ :=
            RCLike.abs_re_le_norm _
        _ ≤ ‖x (p v)‖ * ‖p v‖ := norm_inner_le_norm _ _
        _ ≤ (‖x‖ * ‖p v‖) * ‖p v‖ :=
            mul_le_mul_of_nonneg_right (x.le_opNorm _) (norm_nonneg _)
        _ = ‖x‖ * ‖p v‖ ^ 2 := by ring
    calc -‖x‖ * ‖p v‖ ^ 2 = -(‖x‖ * ‖p v‖ ^ 2) := by ring
      _ ≤ RCLike.re (inner ℂ (x (p v)) (p v)) := neg_le_of_abs_le hbound
  -- bounded above
  have hAbdd : BddAbove A := by
    obtain ⟨w, hw⟩ : ∃ w, p w ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hp0 (ContinuousLinearMap.ext fun w => by simp [hcon w])
    refine ⟨RCLike.re (inner ℂ (x w) w) / ‖p w‖ ^ 2, fun c hc => ?_⟩
    have h1 := (hmemA c).mp hc w
    have h2 : (0 : ℝ) < ‖p w‖ ^ 2 := by positivity
    exact (le_div_iff₀ h2).mpr h1
  -- closed
  have hAclosed : IsClosed A := by
    have hAeq : A = ⋂ v : H,
        {c : ℝ | c * ‖p v‖ ^ 2 ≤ RCLike.re (inner ℂ (x v) v)} := by
      ext c
      simp only [Set.mem_iInter, Set.mem_ofPred_eq, ← hmemA c]
    rw [hAeq]
    exact isClosed_iInter fun v =>
      isClosed_le (continuous_id.mul continuous_const) continuous_const
  set c₀ : ℝ := sSup A with hc₀
  have hc₀A : c₀ ∈ A := hAclosed.csSup_mem hAne hAbdd
  refine ⟨c₀, ?_⟩
  -- for every `c > c₀`, the dichotomy forces `x - c • p ≤ 0`
  have hpmem : p ∈ cornerNonUnitalStarSubalgebra N hp :=
    ⟨hpN, hp.isIdempotentElem, hp.isIdempotentElem⟩
  have hupper : ∀ ε : ℝ, 0 < ε → x - ((c₀ + ε : ℝ) : ℂ) • p ≤ 0 := by
    intro ε hε
    have hnotA : (c₀ + ε) ∉ A := fun hmem =>
      absurd (le_csSup hAbdd hmem) (by rw [← hc₀]; linarith)
    have hdmem : x - ((c₀ + ε : ℝ) : ℂ) • p ∈ cornerNonUnitalStarSubalgebra N hp :=
      sub_mem ⟨hxN, hpx, hxp⟩ (SMulMemClass.smul_mem _ hpmem)
    rcases nonneg_or_nonpos_of_forall_subprojection hp hp0 hmin (hsa_c _) hdmem with h | h
    · exact absurd h hnotA
    · exact h
  -- `{c | x - c • p ≤ 0}` is pointwise-characterised, hence closed; it contains `(c₀, ∞)`,
  -- hence its closure point `c₀`
  have hnegpos_iff : ∀ c : ℝ, (x - (c : ℂ) • p ≤ 0) ↔
      ∀ v, RCLike.re (inner ℂ (x v) v) ≤ c * ‖p v‖ ^ 2 := by
    intro c
    have hsa' : IsSelfAdjoint ((c : ℂ) • p - x) := by
      rw [IsSelfAdjoint, star_sub, star_smul, hxsa.star_eq, hp.isSelfAdjoint.star_eq,
        Complex.star_def, Complex.conj_ofReal]
    rw [ContinuousLinearMap.le_def, zero_sub, neg_sub,
      ← ContinuousLinearMap.nonneg_iff_isPositive, hpos_iff _ hsa']
    have hstep : ∀ v, RCLike.re (inner ℂ (((c : ℂ) • p - x) v) v)
        = c * ‖p v‖ ^ 2 - RCLike.re (inner ℂ (x v) v) := by
      intro v
      rw [sub_apply, smul_apply, inner_sub_left,
        inner_smul_left, Complex.conj_ofReal, map_sub,
        show RCLike.re ((c : ℂ) * inner ℂ (p v) v) = c * RCLike.re (inner ℂ (p v) v) from
          RCLike.re_ofReal_mul c _, hpvv]
    constructor
    · intro h v
      have := h v
      rw [hstep, sub_nonneg] at this
      exact this
    · intro h v
      rw [hstep, sub_nonneg]
      exact h v
  have hBclosed : IsClosed {c : ℝ | x - (c : ℂ) • p ≤ 0} := by
    have hBeq : {c : ℝ | x - (c : ℂ) • p ≤ 0}
        = ⋂ v : H, {c : ℝ | RCLike.re (inner ℂ (x v) v) ≤ c * ‖p v‖ ^ 2} := by
      ext c
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, hnegpos_iff c]
    rw [hBeq]
    exact isClosed_iInter fun v =>
      isClosed_le continuous_const (continuous_id.mul continuous_const)
  have hIoi : Set.Ioi c₀ ⊆ {c : ℝ | x - (c : ℂ) • p ≤ 0} := by
    intro c hc
    have h := hupper (c - c₀) (sub_pos.mpr hc)
    rw [show c₀ + (c - c₀) = c by ring] at h
    exact h
  have hc₀B : x - (c₀ : ℂ) • p ≤ 0 := by
    have h1 : Set.Ici c₀ ⊆ {c : ℝ | x - (c : ℂ) • p ≤ 0} := by
      rw [← closure_Ioi]
      exact closure_minimal hIoi hBclosed
    exact h1 Set.self_mem_Ici
  have hge : (0 : H →L[ℂ] H) ≤ x - (c₀ : ℂ) • p := hc₀A
  exact sub_eq_zero.mp (le_antisymm hc₀B hge)

/-- **Order-minimality implies corner triviality**: a nonzero star projection `p ∈ N` with no
proper nonzero subprojection in `N` is a minimal projection, i.e. `p N p = ℂ p`. Self-adjoint
corner elements are real multiples of `p` by the cut lemma
(`exists_real_smul_eq_of_forall_subprojection`); a general corner element decomposes into real
and imaginary self-adjoint parts. -/
lemma isMinimalProjection_of_forall_subprojection {N : VonNeumannAlgebra H}
    {p : H →L[ℂ] H} (hp : IsStarProjection p) (hpN : p ∈ N) (hp0 : p ≠ 0)
    (hmin : ∀ q, IsStarProjection q → q ∈ N → q ≤ p → q = 0 ∨ q = p) :
    IsMinimalProjection N p := by
  refine ⟨hp, hpN, hp0, fun a haN => ?_⟩
  have hymem : p * a * p ∈ cornerNonUnitalStarSubalgebra N hp := by
    refine ⟨mul_mem (mul_mem hpN haN) hpN, ?_, ?_⟩
    · calc p * (p * a * p) = (p * p) * a * p := by simp only [mul_assoc]
        _ = p * a * p := by rw [hp.isIdempotentElem]
    · rw [mul_assoc (p * a) p p, hp.isIdempotentElem]
  set s : H →L[ℂ] H := star (p * a * p) with hs
  have hsmem : s ∈ cornerNonUnitalStarSubalgebra N hp := star_mem hymem
  have hy₁mem : (2⁻¹ : ℂ) • (p * a * p + s) ∈ cornerNonUnitalStarSubalgebra N hp :=
    SMulMemClass.smul_mem _ (add_mem hymem hsmem)
  have hy₂mem : (-(Complex.I) * 2⁻¹ : ℂ) • (p * a * p - s)
      ∈ cornerNonUnitalStarSubalgebra N hp :=
    SMulMemClass.smul_mem _ (sub_mem hymem hsmem)
  have hy₁sa : IsSelfAdjoint ((2⁻¹ : ℂ) • (p * a * p + s)) := by
    rw [IsSelfAdjoint, star_smul, star_add, hs, star_star,
      show star (2⁻¹ : ℂ) = (2⁻¹ : ℂ) by simp, add_comm]
  have hy₂sa : IsSelfAdjoint ((-(Complex.I) * 2⁻¹ : ℂ) • (p * a * p - s)) := by
    rw [IsSelfAdjoint, star_smul, star_sub, hs, star_star,
      show star (-(Complex.I) * 2⁻¹ : ℂ) = (Complex.I * 2⁻¹ : ℂ) by simp,
      ← neg_sub (p * a * p) (star (p * a * p)), smul_neg, neg_mul, neg_smul]
  obtain ⟨c₁, hc₁⟩ := exists_real_smul_eq_of_forall_subprojection hp hpN hp0 hmin hy₁sa hy₁mem
  obtain ⟨c₂, hc₂⟩ := exists_real_smul_eq_of_forall_subprojection hp hpN hp0 hmin hy₂sa hy₂mem
  refine ⟨(c₁ : ℂ) + Complex.I * (c₂ : ℂ), ?_⟩
  have hrec : (2⁻¹ : ℂ) • (p * a * p + s)
      + Complex.I • ((-(Complex.I) * 2⁻¹ : ℂ) • (p * a * p - s)) = p * a * p := by
    rw [smul_smul, show Complex.I * (-(Complex.I) * 2⁻¹) = (2⁻¹ : ℂ) by
        rw [← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul],
      smul_add, smul_sub]
    calc (2⁻¹ : ℂ) • (p * a * p) + (2⁻¹ : ℂ) • s
          + ((2⁻¹ : ℂ) • (p * a * p) - (2⁻¹ : ℂ) • s)
        = (2⁻¹ : ℂ) • (p * a * p) + (2⁻¹ : ℂ) • (p * a * p) := by abel
      _ = ((2⁻¹ : ℂ) + 2⁻¹) • (p * a * p) := (add_smul _ _ _).symm
      _ = p * a * p := by norm_num
  calc p * a * p
      = (2⁻¹ : ℂ) • (p * a * p + s)
        + Complex.I • ((-(Complex.I) * 2⁻¹ : ℂ) • (p * a * p - s)) := hrec.symm
    _ = (c₁ : ℂ) • p + Complex.I • ((c₂ : ℂ) • p) := by rw [hc₁, hc₂]
    _ = ((c₁ : ℂ) + Complex.I * (c₂ : ℂ)) • p := by rw [smul_smul, ← add_smul]

/-- **In a factor, a nonzero abelian projection is minimal**: it is order-minimal
(`subprojection_eq_of_isAbelianProjection`), and order-minimality forces the trivial corner
(`isMinimalProjection_of_forall_subprojection`). -/
theorem IsFactor.isMinimalProjection_of_isAbelianProjection
    {N : VonNeumannAlgebra H} (hN : IsFactor N) {p : H →L[ℂ] H}
    (hp : IsAbelianProjection N p) (hp0 : p ≠ 0) : IsMinimalProjection N p :=
  isMinimalProjection_of_forall_subprojection hp.1 hp.2.1 hp0 fun _ hq hqN hsub =>
    hN.subprojection_eq_of_isAbelianProjection hp hq hqN hsub

/-! ### Minimal projections of `B(H)` -/

section BoundedLinearOperators

open InnerProductSpace

/-- **A rank-one projection is minimal in `B(H)`.** For a unit vector `u`, the rank-one orthogonal
projection `|u⟩⟨u|` is a minimal projection of `𝓑(H)`: it is a star projection, nonzero, and its corner
is trivial because `|u⟩⟨u| ∘ a ∘ |u⟩⟨u| = ⟪u, a u⟫ • |u⟩⟨u|`. -/
lemma isMinimalProjection_rankOne_boundedLinearOperators {u : H} (hu : ‖u‖ = 1) :
    IsMinimalProjection 𝓑(H) (rankOne ℂ u u) := by
  have hu_ne : u ≠ 0 := by rw [← norm_pos_iff, hu]; norm_num
  refine ⟨⟨isIdempotentElem_rankOne_self hu, ?_⟩, mem_boundedLinearOperators _,
    rankOne_ne_zero hu_ne hu_ne, fun a _ => ?_⟩
  · rw [isSelfAdjoint_iff, ContinuousLinearMap.star_eq_adjoint, adjoint_rankOne]
  · exact ⟨inner ℂ u (a u), by
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.comp_assoc, comp_rankOne, rankOne_comp_rankOne]⟩

omit [CompleteSpace H] in
/-- A normalised nonzero vector of a nontrivial space, packaged as a unit vector. -/
private lemma exists_unit_vector [Nontrivial H] : ∃ u : H, ‖u‖ = 1 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  exact ⟨(‖v‖⁻¹ : ℂ) • v, by
    rw [norm_smul, norm_inv, Complex.norm_real, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]⟩

/-- **`B(H)` has a minimal projection** (a rank-one projection). Needs `H` nonzero. -/
theorem exists_isMinimalProjection_boundedLinearOperators [Nontrivial H] :
    ∃ e : H →L[ℂ] H, IsMinimalProjection 𝓑(H) e :=
  let ⟨u, hu⟩ := exists_unit_vector (H := H)
  ⟨rankOne ℂ u u, isMinimalProjection_rankOne_boundedLinearOperators hu⟩

/-- **The minimal projections of `B(H)` are exactly the rank-one projections** `|u⟩⟨u|`,
`‖u‖ = 1`. The converse direction is `isMinimalProjection_rankOne_boundedLinearOperators`. For the
forward direction pick a unit vector `u` in the range of the minimal projection `e`, so `e u = u`;
the corner condition against `a = |u⟩⟨u|` reads `|u⟩⟨u| = e |u⟩⟨u| e = c • e`, and evaluating at
`u` forces `c = 1`. -/
lemma isMinimalProjection_boundedLinearOperators_iff {e : H →L[ℂ] H} :
    IsMinimalProjection 𝓑(H) e ↔ ∃ u : H, ‖u‖ = 1 ∧ e = rankOne ℂ u u := by
  refine ⟨fun he => ?_, fun ⟨u, hu, he⟩ => he ▸ isMinimalProjection_rankOne_boundedLinearOperators hu⟩
  obtain ⟨hp, -, hne, hcorner⟩ := he
  obtain ⟨v, hv⟩ := ContinuousLinearMap.exists_ne_zero hne
  set u : H := (‖e v‖⁻¹ : ℂ) • e v with hu_def
  have hu : ‖u‖ = 1 := by
    rw [hu_def, norm_smul, norm_inv, Complex.norm_real, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
  have heu : e u = u := by
    rw [hu_def, map_smul, show e (e v) = (e * e) v from rfl, hp.isIdempotentElem]
  obtain ⟨c, hc⟩ := hcorner (rankOne ℂ u u) (mem_boundedLinearOperators _)
  rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def, comp_rankOne, heu, rankOne_comp,
    hp.isSelfAdjoint.adjoint_eq, heu] at hc
  have hc1 : c = 1 := by
    have h := congrArg (fun T : H →L[ℂ] H => T u) hc
    simp only [rankOne_apply, smul_apply, heu, inner_self_eq_norm_sq_to_K, hu] at h
    norm_num at h
    exact (smul_left_injective ℂ (ne_zero_of_norm_ne_zero (hu ▸ one_ne_zero))
      (show (1 : ℂ) • u = c • u by rw [one_smul]; exact h)).symm
  exact ⟨u, hu, by rw [hc, hc1, one_smul]⟩

/-- **The minimal projections of `B(H)` are exactly the star projections of rank one**: a star
projection `e` is minimal in `𝓑(H)` iff its range is one-dimensional. Through
`isMinimalProjection_boundedLinearOperators_iff` this is the statement that a star projection is
determined by its range (`ContinuousLinearMap.IsStarProjection.ext_iff`), the range of `|u⟩⟨u|`
being the line `ℂ u`. -/
lemma isMinimalProjection_boundedLinearOperators_iff_finrank {e : H →L[ℂ] H} :
    IsMinimalProjection 𝓑(H) e ↔ IsStarProjection e ∧ Module.finrank ℂ e.range = 1 := by
  have hrange : ∀ {u : H}, ‖u‖ = 1 → (rankOne ℂ u u : H →L[ℂ] H).range = ℂ ∙ u := fun {u} hu => by
    rw [rankOne_def, ContinuousLinearMap.range_smulRight_apply]
    intro h
    have := congrArg (fun f : H →L[ℂ] ℂ => f u) h
    simp only [innerSL_apply_apply, inner_self_eq_norm_sq_to_K, hu, zero_apply] at this
    norm_num at this
  rw [isMinimalProjection_boundedLinearOperators_iff]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨isStarProjection_rankOne_self hu, by
      rw [hrange hu, finrank_span_singleton (ne_zero_of_norm_ne_zero (hu ▸ one_ne_zero))]⟩
  · rintro ⟨hp, hrank⟩
    obtain ⟨w, hw0, hw⟩ := finrank_eq_one_iff'.mp hrank
    have hw0' : (w : H) ≠ 0 := fun h => hw0 (Subtype.ext h)
    set u : H := (‖(w : H)‖⁻¹ : ℂ) • (w : H) with hu_def
    have hu : ‖u‖ = 1 := by
      rw [hu_def, norm_smul, norm_inv, Complex.norm_real, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw0')]
    have hspan : e.range = ℂ ∙ u := by
      refine le_antisymm (fun z hz => ?_) ((Submodule.span_singleton_le_iff_mem _ _).mpr
        (Submodule.smul_mem _ _ w.2))
      obtain ⟨c, hc⟩ := hw ⟨z, hz⟩
      rw [Submodule.mem_span_singleton]
      refine ⟨c * ‖(w : H)‖, ?_⟩
      rw [hu_def, smul_smul, mul_assoc, mul_inv_cancel₀ (by exact_mod_cast norm_ne_zero_iff.mpr hw0'),
        mul_one]
      exact congrArg Subtype.val hc
    exact ⟨u, hu, ContinuousLinearMap.IsStarProjection.ext hp (isStarProjection_rankOne_self hu)
      (hspan.trans (hrange hu).symm)⟩

end BoundedLinearOperators

end VonNeumannAlgebra
