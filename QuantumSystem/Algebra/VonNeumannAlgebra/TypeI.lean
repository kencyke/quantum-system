module

public import QuantumSystem.Algebra.VonNeumannAlgebra.Comparison

/-!
# Type I von Neumann algebras

The general **type I** property, phrased as in the literature (Takesaki V.1, Blackadar III.1.5):
every nonzero central projection dominates a nonzero abelian projection. For a *factor* this is
equivalent to the existence of a minimal projection, i.e. to `IsTypeIFactor`; this file proves
the easy direction (minimal ⇒ abelian ⇒ type I) and the order-minimality of abelian projections
in a factor, the first half of the converse. The remaining half (order-minimal ⇒ corner-scalar)
and the assembled equivalence `IsFactor N → (IsTypeI N ↔ ∃ e, IsMinimalProjection N e)` are the
subject of the continuous-functional-calculus development that follows.

## Main definitions

* `VonNeumannAlgebra.IsTypeI N` — every nonzero central projection of `N` dominates a nonzero
  abelian projection.

## Main results

* `VonNeumannAlgebra.IsFactor.isTypeI_of_exists_isMinimalProjection` — a factor with a minimal
  projection is type I.
* `VonNeumannAlgebra.IsFactor.subprojection_eq_of_isAbelianProjection` — in a factor, an abelian
  projection has no proper nonzero subprojection.
-/

@[expose] public section

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Type I von Neumann algebra**: every nonzero central projection dominates a nonzero abelian
projection. The subprojection relation `p ≤ z` is written algebraically as `z * p = p`, as
everywhere in this development. -/
def IsTypeI (N : VonNeumannAlgebra H) : Prop :=
  ∀ z : H →L[ℂ] H, IsCentralProjection N z → z ≠ 0 →
    ∃ p : H →L[ℂ] H, IsAbelianProjection N p ∧ p ≠ 0 ∧ z * p = p

/-- A factor with a minimal projection is type I: the only nonzero central projection of a factor
is `1` (`central_projection_eq`), and it dominates the minimal projection, which is abelian and
nonzero. -/
theorem IsFactor.isTypeI_of_exists_isMinimalProjection [Nontrivial H] {N : VonNeumannAlgebra H}
    (hN : IsFactor N) (h : ∃ e : H →L[ℂ] H, IsMinimalProjection N e) : IsTypeI N := by
  obtain ⟨e, he⟩ := h
  intro z hz hz0
  rcases hN.central_projection_eq hz with h0 | h1
  · exact absurd h0 hz0
  · exact ⟨e, he.isAbelianProjection, he.2.2.1, by rw [h1, one_mul]⟩

/-- **In a factor, an abelian projection is order-minimal**: a projection `q ∈ N` with `q ≤ p`
(written `p * q = q`) is `0` or `p`.

The proof avoids corner-commutant theory and polar decomposition: if `0 ≠ q ≠ p`, then
`r := p - q` is a nonzero projection under `p` orthogonal to `q`, and the central-support lemma
`IsFactor.exists_mul_ne` produces `a ∈ N` with `z := r a q ≠ 0`. Both `z` and `z⋆` are corner
elements of `p`, so they commute by abelianness; but `q z = 0` and `q z⋆ = z⋆` force
`z⋆ z = q (z z⋆) = (q z) z⋆ = 0`, and the C⋆-identity gives `z = 0` — a contradiction. -/
theorem IsFactor.subprojection_eq_of_isAbelianProjection [Nontrivial H] {N : VonNeumannAlgebra H}
    (hN : IsFactor N) {p : H →L[ℂ] H} (hp : IsAbelianProjection N p)
    {q : H →L[ℂ] H} (hq : IsStarProjection q) (hqN : q ∈ N) (hsub : p * q = q) :
    q = 0 ∨ q = p := by
  by_cases hq0 : q = 0
  · exact Or.inl hq0
  by_cases hqp : q = p
  · exact Or.inr hqp
  exfalso
  have hqmul : q * p = q := isStarProjection_subproj_comm hp.1 hq hsub
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

end VonNeumannAlgebra
