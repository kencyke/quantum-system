module

public import QuantumSystem.Algebra.CStarAlgebra.Representation.UnitaryEquiv

/-!
# Sector families

A *sector family* `F : SectorFamily A` for a non-unital C\*-algebra `A`
is an indexed family of `CStarRep`s.  In sector theory the typical
intent is that `F` enumerates a *complete system of representatives*
for the unitary-equivalence classes of representations satisfying some
physical selection condition `P` (DHR, KMS, cone-localised, ...): for
every physical representation `R` there is some index `α` with
`R ≃ F.rep α`, and indices give pairwise inequivalent representations.

The selection condition `P` and the completeness/skeleton conditions are
*separate* structures (`SectorFamily.IsComplete`, `IsSkeleton`), so the
basic `SectorFamily` data carries no condition — it is just an indexed
family of representations.  The direct sum
`SectorFamily.directSumHilbert` (in `CStarAlgebra/Representation/DirectSum.lean`) and its
universal `*`-representation `directSumRep` need only the family data.

## Design rationale

Compared to a quotient-first API such as
`Sector 𝒞 := Quotient 𝒞.equiv`, the family-first API avoids
`Classical.choice` / `Quotient.out` at the representative-selection level.
Sector representatives are explicit values of `F.rep α`, not output of
`Quotient.out`.  This is the natural form used in the
Doplicher–Haag–Roberts and Naaijkens literature, where DHR sectors are
first constructed from localized endomorphisms and only *afterwards*
identified up to unitary equivalence.

## Main definitions

* `SectorFamily A` — an indexed family of `CStarRep`s.
* `SectorFamily.IsPhysical` — every member satisfies `P`.
* `SectorFamily.IsComplete` — every `P`-representation is unitarily
  equivalent to some `F.rep α`.
* `SectorFamily.IsSkeleton` — `IsComplete` and pairwise non-equivalent.
-/

@[expose] public section

universe u v w

/-- An indexed family of `CStarRep`s of a non-unital C\*-algebra `A`,
parametrised by an arbitrary index type. -/
structure SectorFamily (A : Type u) [NonUnitalCStarAlgebra A] where
  /-- The index type. -/
  Index : Type w
  /-- The representation at each index. -/
  rep : Index → CStarRep.{u, v} A

namespace SectorFamily

variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- Every member of the family satisfies the predicate `P`. -/
structure IsPhysical (F : SectorFamily.{u, v, w} A)
    (P : CStarRep.{u, v} A → Prop) : Prop where
  /-- Each `F.rep α` is physical. -/
  isPhysical : ∀ α, P (F.rep α)

/-- The family `F` is a *complete system of physical representatives*:
every representation satisfying `P` is unitarily equivalent to some
`F.rep α`. -/
structure IsComplete (F : SectorFamily.{u, v, w} A)
    (P : CStarRep.{u, v} A → Prop) : Prop extends F.IsPhysical P where
  /-- Every `P`-representation is unitarily equivalent to some `F.rep α`. -/
  complete : ∀ R : CStarRep.{u, v} A, P R → ∃ α,
    Nonempty (CStarRep.UnitaryEquiv R (F.rep α))

/-- The family `F` is a *skeleton* for the `P`-representations: it is
complete and any two indices give non-equivalent representations. -/
structure IsSkeleton (F : SectorFamily.{u, v, w} A)
    (P : CStarRep.{u, v} A → Prop) : Prop extends F.IsComplete P where
  /-- Distinct indices give non-equivalent representations. -/
  pairwise : ∀ α β,
    Nonempty (CStarRep.UnitaryEquiv (F.rep α) (F.rep β)) → α = β

end SectorFamily
