/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.RingTheory.Idempotents
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Orthogonal idempotents on a finite-dimensional space

A family of pairwise orthogonal idempotent endomorphisms `p i` of a vector space `V`
(`OrthogonalIdempotents p`: `p i * p i = p i` and `p i * p j = 0` for `i ≠ j`) splits off
independent pieces of `V`: nonzero vectors `v i` chosen in the ranges of the `p i` are linearly
independent, since applying `p i` to a vanishing linear combination isolates its `i`-th term. On a
finite-dimensional `V` a family of *nonzero* orthogonal idempotents is therefore finite, with at
most `finrank V` members.

For operator algebras this is the statement that `B(ℂⁿ)` has at most `n` pairwise orthogonal
nonzero projections — the finiteness that separates the type `I_n` factors from the type `I_∞`
ones.

## Main results

* `OrthogonalIdempotents.linearIndependent` — nonzero vectors in the ranges of orthogonal
  idempotents are linearly independent.
* `OrthogonalIdempotents.finite_of_ne_zero`, `OrthogonalIdempotents.natCard_le_finrank` — on a
  finite-dimensional space a family of nonzero orthogonal idempotents is finite, with at most
  `finrank K V` members.
* `ContinuousLinearMap.finite_of_orthogonalIdempotents`,
  `ContinuousLinearMap.natCard_le_finrank_of_orthogonalIdempotents` — the same for continuous
  linear endomorphisms.
-/

@[expose] public section

namespace OrthogonalIdempotents

variable {K V ι : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] {p : ι → Module.End K V}

/-- **Nonzero vectors in the ranges of orthogonal idempotents are linearly independent.** If
`p i (v i) = v i` and `v i ≠ 0` for every `i`, then the family `v` is linearly independent:
applying `p i` to a vanishing linear combination `∑ⱼ gⱼ • vⱼ = 0` kills every term with `j ≠ i`
(as `p i (v j) = (p i * p j) (v j) = 0`) and leaves `gᵢ • vᵢ = 0`. -/
lemma linearIndependent (hp : OrthogonalIdempotents p) {v : ι → V}
    (hv : ∀ i, p i (v i) = v i) (hv0 : ∀ i, v i ≠ 0) : LinearIndependent K v := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h := congrArg (p i) hg
  rw [map_sum, map_zero, Finset.sum_eq_single i (fun j _ hji => ?_) (fun h => absurd hi h),
    map_smul, hv] at h
  · exact (smul_eq_zero.mp h).resolve_right (hv0 i)
  · rw [map_smul, ← hv j, ← Module.End.mul_apply, hp.ortho hji.symm, LinearMap.zero_apply,
      smul_zero]

/-- A family of nonzero orthogonal idempotents admits a nonzero vector fixed by each member. -/
private lemma exists_vector (hp : OrthogonalIdempotents p) (hp0 : ∀ i, p i ≠ 0) :
    ∃ v : ι → V, (∀ i, p i (v i) = v i) ∧ ∀ i, v i ≠ 0 := by
  have h : ∀ i, ∃ w, p i w ≠ 0 := fun i => by
    by_contra! h
    exact hp0 i (LinearMap.ext h)
  choose w hw using h
  refine ⟨fun i => p i (w i), fun i => ?_, hw⟩
  rw [← Module.End.mul_apply, (hp.idem i).eq]

/-- **On a finite-dimensional space a family of nonzero orthogonal idempotents is finite**, being
witnessed by a linearly independent family of vectors (`linearIndependent`). -/
lemma finite_of_ne_zero [Module.Finite K V] (hp : OrthogonalIdempotents p)
    (hp0 : ∀ i, p i ≠ 0) : Finite ι :=
  let ⟨_, hv, hv0⟩ := hp.exists_vector hp0
  (hp.linearIndependent hv hv0).finite

/-- **On a finite-dimensional space a family of nonzero orthogonal idempotents has at most
`finrank K V` members**, being witnessed by a linearly independent family of vectors
(`linearIndependent`). Finiteness of the family itself is `finite_of_ne_zero`; without it the
bound would be vacuous, `Nat.card` being `0` on infinite types. -/
lemma natCard_le_finrank [Module.Finite K V] (hp : OrthogonalIdempotents p)
    (hp0 : ∀ i, p i ≠ 0) : Nat.card ι ≤ Module.finrank K V := by
  obtain ⟨v, hv, hv0⟩ := hp.exists_vector hp0
  have hli := hp.linearIndependent hv hv0
  have : Finite ι := hli.finite
  have : Fintype ι := Fintype.ofFinite ι
  rw [Nat.card_eq_fintype_card]
  exact hli.fintype_card_le_finrank

end OrthogonalIdempotents

namespace ContinuousLinearMap

variable {K V ι : Type*} [DivisionRing K] [TopologicalSpace V] [AddCommGroup V] [ContinuousAdd V]
  [Module K V] [Module.Finite K V] {p : ι → V →L[K] V}

/-- **On a finite-dimensional space a family of nonzero orthogonal continuous idempotents is
finite.** This is `OrthogonalIdempotents.finite_of_ne_zero` transported along the injective ring
homomorphism `toLinearMapRingHom`. -/
lemma finite_of_orthogonalIdempotents (hp : OrthogonalIdempotents p) (hp0 : ∀ i, p i ≠ 0) :
    Finite ι :=
  (hp.map toLinearMapRingHom).finite_of_ne_zero fun i h => hp0 i (coe_injective h)

/-- **On a finite-dimensional space a family of nonzero orthogonal continuous idempotents has at
most `finrank K V` members** — in operator-algebraic terms, `B(ℂⁿ)` has at most `n` pairwise
orthogonal nonzero projections. This is `OrthogonalIdempotents.natCard_le_finrank` transported
along the injective ring homomorphism `toLinearMapRingHom`. -/
lemma natCard_le_finrank_of_orthogonalIdempotents (hp : OrthogonalIdempotents p)
    (hp0 : ∀ i, p i ≠ 0) : Nat.card ι ≤ Module.finrank K V :=
  (hp.map toLinearMapRingHom).natCard_le_finrank fun i h => hp0 i (coe_injective h)

end ContinuousLinearMap
