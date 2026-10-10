/-
Copyright (c) 2025 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.CStarAlgebra.GNS.Irreducible
public import QuantumSystem.Analysis.CStarAlgebra.Representation.DirectSum

/-!
# The direct sum of the GNS representations of all pure states

The GNS representations `π_ψ` of the pure states `ψ` of a C\*-algebra `A` form a sector family
`pureStateFamily A`, and its `ℓ²`-direct sum `rep A` is the representation witnessing the
Gelfand–Naimark theorem (`CStarRep.exists_isometric`).  Everything is an instance of the generic
direct sum of `CStarAlgebra/Representation/DirectSum.lean`; the only input specific to pure
states is that the family separates points (`pureStateFamily_separatesPoints`), which is the
existence of enough pure states (`State.exists_isPure_pos_of_ne_zero`).

Summing over *pure* states — rather than over all states — makes this a (non-reduced form of
the) **atomic representation**; it is not the universal representation.  The index type is the
subtype `{ω : State A // ω.IsPure}` of all pure states, not a set of unitary equivalence classes,
so the same class is repeated once per pure state realising it.

## Main results

* `GNS.DirectSum.rep_injective`, `rep_isometry`, `rep_isClosed_range` — `rep A` is a faithful,
  isometric representation with norm-closed image.
* `GNS.DirectSum.repRangeEquiv` — `A` is `*`-isomorphic onto that image.
* `GNS.DirectSum.rep_actsNondegenerately` — `rep A` is non-degenerate.
* `GNS.DirectSum.rep_π_one`, `GNS.DirectSum.repStarAlgHom` — for unital `A`, `rep A` is unital,
  hence a faithful isometric unital `*`-homomorphism `A →⋆ₐ[ℂ] (H →L[ℂ] H)`.
-/

@[expose] public section

open scoped ComplexOrder InnerProductSpace

universe u

namespace GNS

namespace DirectSum

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (A) in
/-- The sector family of GNS representations of all pure states, indexed by the pure states
`{ω : State A // ω.IsPure}`. -/
noncomputable def pureStateFamily : SectorFamily.{u, u, u} A where
  Index := {ω : State A // ω.IsPure}
  rep ω := (GNS.Representation.canonical (PositiveLinearMap.ofClass ω.1)).toCStarRep

variable (A) in
/-- **The pure states separate points.**  If `a ≠ 0`, some pure state `ω` has
`0 < ω (a* a) = ⟪ξ_ω, π_ω(a*) π_ω(a) ξ_ω⟫`, so `π_ω(a) ≠ 0`. -/
theorem pureStateFamily_separatesPoints : (pureStateFamily A).SeparatesPoints := by
  intro a ha
  by_contra hne
  obtain ⟨ω, hω_pure, hω_pos⟩ := State.exists_isPure_pos_of_ne_zero a hne
  have hπ : (GNS.Representation.canonical (PositiveLinearMap.ofClass ω)).π a = 0 := ha ⟨ω, hω_pure⟩
  have hzero : ω (star a * a) = 0 := by
    rw [← PositiveLinearMap.coe_ofClass,
      (GNS.Representation.canonical (PositiveLinearMap.ofClass ω)).gns_condition]
    simp [hπ]
  exact hω_pos.ne' hzero

variable (A) in
/-- The direct sum of the GNS representations of all pure states, bundled as a `CStarRep A`.
This is the representation that witnesses the Gelfand–Naimark theorem
(`CStarRep.exists_isometric`). -/
noncomputable def rep : CStarRep A := (pureStateFamily A).toCStarRep

/-- The action of `GNS.DirectSum.rep A` unfolds to the block-diagonal representation
`(pureStateFamily A).directSumRep`. -/
@[simp] lemma rep_π : (rep A).π = (pureStateFamily A).directSumRep := rfl

/-- The direct sum representation is faithful. -/
lemma rep_injective : Function.Injective (rep A).π :=
  (pureStateFamily A).directSumRep_injective_of (pureStateFamily_separatesPoints A)

/-- The direct sum representation is isometric. -/
lemma rep_isometry : Isometry (rep A).π :=
  (pureStateFamily A).directSumRep_isometry_of (pureStateFamily_separatesPoints A)

/-- The image of `A` under the direct sum representation is norm closed in `H →L[ℂ] H`, so it is a
C\*-subalgebra. -/
lemma rep_isClosed_range :
    IsClosed (NonUnitalStarAlgHom.range (rep A).π : Set ((rep A).H →L[ℂ] (rep A).H)) :=
  (pureStateFamily A).directSumRep_isClosed_range_of (pureStateFamily_separatesPoints A)

/-- The direct sum representation acts non-degenerately, since each GNS representation is
cyclic, hence non-degenerate (`GNS.Representation.actsNondegenerately`).

The non-unital Gelfand–Naimark theorem (`CStarRep.exists_isometric`) does not use this —
`CStarRep` carries no non-degeneracy requirement — but the unital form does: for unital `A`
non-degeneracy is the only input to `rep_π_one`, hence to
`CStarRep.exists_isometric_unital`. -/
lemma rep_actsNondegenerately :
    InnerProductSpace.ActsNondegenerately (Set.range ((rep A).π : A → ((rep A).H →L[ℂ] (rep A).H))) :=
  (pureStateFamily A).directSumRep_actsNondegenerately_of fun ω =>
    (GNS.Representation.canonical (PositiveLinearMap.ofClass ω.1)).actsNondegenerately

variable (A) in
/-- The direct sum representation, corestricted to its image, is a `*`-isomorphism
of `A` onto the C\*-subalgebra `NonUnitalStarAlgHom.range (rep A).π` of `H →L[ℂ] H`. -/
noncomputable def repRangeEquiv : A ≃⋆ₐ[ℂ] NonUnitalStarAlgHom.range (rep A).π :=
  StarAlgEquiv.ofBijective (NonUnitalStarAlgHom.rangeRestrict (rep A).π)
    ⟨fun _ _ h => rep_injective (congrArg Subtype.val h), by rintro ⟨_, x, rfl⟩; exact ⟨x, rfl⟩⟩

/-- The `*`-isomorphism of `A` onto the image of the direct sum representation is
isometric: it preserves the norm inherited from `H →L[ℂ] H`. -/
lemma norm_repRangeEquiv (a : A) :
    ‖((repRangeEquiv A a : NonUnitalStarAlgHom.range (rep A).π) : ((rep A).H →L[ℂ] (rep A).H))‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map _ rep_injective a

section Unital

open ContinuousLinearMap

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- For a unital `A`, the direct sum representation is unital, since it acts non-degenerately
(`rep_actsNondegenerately`): `π a (x - π 1 x) = 0` for every `a`, so `π 1 x = x`. -/
lemma rep_π_one : (rep A).π 1 = 1 := by
  ext x
  have h := rep_actsNondegenerately (A := A) (x - (rep A).π 1 x) (by
    rintro _ ⟨a, rfl⟩
    rw [map_sub, ← mul_apply_eq_comp, ← map_mul, mul_one, sub_self])
  rw [one_apply_eq_self, ← sub_eq_zero.1 h]

variable (A) in
/-- For a unital `A`, the direct sum representation as a unital `*`-homomorphism
(`rep_π_one`).

The order `[PartialOrder A] [StarOrderedRing A]` is a parameter, as for `State A` and `rep A`:
each `StarOrderedRing` order on `A` yields its own representation, and `rep A` for distinct
orders need not be definitionally equal.  `CStarAlgebra.spectralOrder` is the default choice,
and the existence theorems (`CStarRep.exists_isometric_unital`) fix it internally, so their
statements do not depend on an order. -/
noncomputable def repStarAlgHom : A →⋆ₐ[ℂ] ((rep A).H →L[ℂ] (rep A).H) :=
  { (rep A).π with
    map_one' := rep_π_one
    commutes' := fun r => by
      change (rep A).π (algebraMap ℂ A r) = algebraMap ℂ _ r
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, map_smul, rep_π_one] }

/-- The unital ⋆-homomorphism `repStarAlgHom A` acts as the direct sum representation. -/
@[simp] lemma repStarAlgHom_apply (a : A) : repStarAlgHom A a = (rep A).π a := rfl

/-- The unital direct sum representation is faithful. -/
lemma repStarAlgHom_injective : Function.Injective (repStarAlgHom A) :=
  rep_injective

/-- The unital direct sum representation is isometric. -/
lemma repStarAlgHom_isometry : Isometry (repStarAlgHom A) :=
  rep_isometry

end Unital

end DirectSum

end GNS
