/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.CStarAlgebra.Representation.UnitaryEquiv

/-!
# Sector families

A *sector family* `F : SectorFamily A` for a non-unital C\*-algebra `A`
is an indexed family of `CStarRep`s.  In sector theory the typical
intent is that `F` enumerates a *complete system of representatives*
for the unitary-equivalence classes of representations satisfying some
physical selection condition `P` (DHR, KMS, cone-localised, ...): for
every physical representation `R` there is some index `α` with
`R ≃ F.rep α`, and indices give pairwise inequivalent representations.

The selection condition `P` and the completeness of the family are not part of the data: the
basic `SectorFamily` carries no condition — it is just an indexed family of representations, and
any such condition is stated as a hypothesis where a result needs it.  The direct sum
`SectorFamily.directSumHilbert` (in
`QuantumSystem.Analysis.CStarAlgebra.Representation.DirectSum`) and its universal
`*`-representation `directSumRep` need only the family data.

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
