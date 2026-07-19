module

public import Mathlib.Analysis.VonNeumannAlgebra.Basic
public import QuantumSystem.ForMathlib.Algebra.Star.PartialIsometry

/-!
# Factors, minimal projections and Murray–von Neumann equivalence

This file sets up the basic vocabulary of the comparison theory of projections in a von Neumann
algebra, the foundation of the type classification (and, downstream, of the type I factor
structure theorem).

## Main definitions

* `VonNeumannAlgebra.IsFactor N` — `N` has trivial centre: every element of `N ∩ N'` is a scalar.
* `VonNeumannAlgebra.IsMinimalProjection N e` — `e` is a nonzero star projection in `N` with
  trivial corner `e N e = ℂ e`. This implies the order-theoretic minimality (no proper nonzero
  subprojection in `N`, expressed algebraically as: any projection `f ∈ N` with `e * f = f`, i.e.
  the Loewner relation `f ≤ e`, is `0` or `e`), recorded as
  `IsMinimalProjection.no_proper_subprojection`.
* `VonNeumannAlgebra.MvNEquiv N p q` — `p` and `q` are Murray–von Neumann equivalent inside `N`:
  there is a partial isometry `v ∈ N` with source `v⋆v = p` and range `vv⋆ = q`. Written `p ∼[N] q`.

## Main results

* `VonNeumannAlgebra.MvNEquiv.refl` / `symm` / `trans` — Murray–von Neumann equivalence is an
  equivalence relation on the projections of `N`.

## Notation

The equivalence relation symbol of the operator-algebra literature lives in the opt-in
`VonNeumannAlgebra` scope; activate it with `open scoped VonNeumannAlgebra`.

| Symbol | Expansion | How to activate |
|---|---|---|
| `p ∼[N] q` | `VonNeumannAlgebra.MvNEquiv N p q` | `open scoped VonNeumannAlgebra` |
-/

@[expose] public section

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A von Neumann algebra is closed under scalar multiplication. -/
lemma smul_mem {N : VonNeumannAlgebra H} (c : ℂ) {x : H →L[ℂ] H} (hx : x ∈ N) : c • x ∈ N := by
  rw [Algebra.smul_def]
  exact mul_mem (algebraMap_mem N.toStarSubalgebra c) hx

/-- A von Neumann algebra `N` is a **factor** when its centre is trivial: every operator lying in
both `N` and its commutant is a scalar multiple of the identity. -/
def IsFactor (N : VonNeumannAlgebra H) : Prop :=
  ∀ x : H →L[ℂ] H, x ∈ N → x ∈ N.commutant → ∃ c : ℂ, x = c • 1

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
  let ⟨x, hx⟩ := ContinuousLinearMap.exists_ne_zero he.2.2.1
  ⟨⟨e x, 0, hx⟩⟩

/-- A minimal projection has no proper nonzero subprojection in `N`: if a projection `f ∈ N`
satisfies `f ≤ e` (the Loewner order on projections, equivalently the range inclusion
`ran f ⊆ ran e`, written algebraically as `e * f = f`), then `f = 0` or `f = e`. This recovers the
order-theoretic form of minimality from the corner definition `e N e = ℂ e`. -/
lemma IsMinimalProjection.no_proper_subprojection {N : VonNeumannAlgebra H}
    {e : H →L[ℂ] H} (he : IsMinimalProjection N e)
    {f : H →L[ℂ] H} (hf : IsStarProjection f) (hfN : f ∈ N) (hsub : e * f = f) :
    f = 0 ∨ f = e := by
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

/-- A **type I factor**: a factor possessing a minimal projection. This is the mathematically
conventional, intrinsic definition; the spatial decomposition `N ≅ B(H₁) ⊗̄ 1` is then a theorem,
not part of the definition. The equivalence with the general abelian-projection definition
`IsTypeI` is `isTypeIFactor_iff_isFactor_and_isTypeI`. -/
def IsTypeIFactor (N : VonNeumannAlgebra H) : Prop :=
  IsFactor N ∧ ∃ e : H →L[ℂ] H, IsMinimalProjection N e

/-- **Murray–von Neumann equivalence** of projections inside `N`: there is a partial isometry
`v ∈ N` with source projection `v⋆v = p` and range projection `vv⋆ = q`. -/
def MvNEquiv (N : VonNeumannAlgebra H) (p q : H →L[ℂ] H) : Prop :=
  ∃ v : H →L[ℂ] H, v ∈ N ∧ IsPartialIsometry v ∧ star v * v = p ∧ v * star v = q

/-- `p ∼[N] q` denotes Murray–von Neumann equivalence `MvNEquiv N p q` of projections inside `N`. -/
scoped notation:50 p:51 " ∼[" N "] " q:51 => MvNEquiv N p q

/-- Murray–von Neumann equivalence is reflexive on projections of `N`. -/
theorem MvNEquiv.refl {N : VonNeumannAlgebra H} {p : H →L[ℂ] H}
    (hp : IsStarProjection p) (hpN : p ∈ N) : p ∼[N] p :=
  ⟨p, hpN, hp.isPartialIsometry, by rw [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq],
    by rw [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]⟩

/-- Murray–von Neumann equivalence is symmetric. -/
theorem MvNEquiv.symm {N : VonNeumannAlgebra H} {p q : H →L[ℂ] H}
    (h : p ∼[N] q) : q ∼[N] p := by
  obtain ⟨v, hv, hpi, hvp, hvq⟩ := h
  exact ⟨star v, star_mem hv, IsPartialIsometry.star hpi, by rw [star_star, hvq],
    by rw [star_star, hvp]⟩

/-- Murray–von Neumann equivalence is transitive. -/
theorem MvNEquiv.trans {N : VonNeumannAlgebra H} {p q r : H →L[ℂ] H}
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

end VonNeumannAlgebra
