module

public import QuantumSystem.Algebra.CStarAlgebra.Representation.Family
public import QuantumSystem.Algebra.CStarAlgebra.Representation.Irreducible
public import QuantumSystem.Algebra.CStarAlgebra.GNS.PureState

/-!
# Pure-state sector family

This file packages the GNS construction of pure states as a
`SectorFamily`.  For each pure state `ψ : PureState A`, the GNS
representation `(PureState.gnsRepresentation ψ).toCStarRep` is an
irreducible `CStarRep A`; the family

```text
α  ↦  ψ.toCStarRep
```

indexed by `PureState A` collects them.

This family is *not* a skeleton: two unitarily equivalent pure states
contribute the "same" sector twice, so two indices may give unitarily
equivalent representations.  The skeleton statement — every irreducible
`CStarRep A` is unitarily equivalent to the GNS representation of some
pure state — is the content of the Gelfand–Naimark–Segal theorem and is
not proved here.

## Main definitions

* `PureState.toCStarRep` — the GNS representation of a pure state as
  a `CStarRep`.
* `PureState.toCStarRep_isIrreducible` — bridge between
  `GNS.Representation.IsIrreducible` and `CStarRep.IsIrreducible`.
* `PureState.sectorFamily A` — the sector family indexed by
  `PureState A`.
-/

@[expose] public section

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A]

namespace PureState

/-- The GNS representation of a pure state, viewed as a `CStarRep`. -/
noncomputable def toCStarRep (ψ : PureState A) : CStarRep A :=
  (PureState.gnsRepresentation ψ).toCStarRep

/-- The CStarRep version of GNS irreducibility on pure states:
`ψ.toCStarRep` is irreducible as a `CStarRep`. -/
lemma toCStarRep_isIrreducible (ψ : PureState A) :
    ψ.toCStarRep.IsIrreducible :=
  GNS.Representation.pureState_gns_isIrreducible (ψ := ψ)

/-- The sector family of pure states: each pure state `ψ` contributes
its GNS representation as a `CStarRep A`.

Caveat: this family is not a skeleton — two unitarily equivalent pure
states give unitarily equivalent representations, so two distinct
indices may give the "same sector". -/
noncomputable def sectorFamily (A : Type u) [NonUnitalCStarAlgebra A] :
    SectorFamily.{u, u, u} A where
  Index := PureState A
  rep := fun ψ => ψ.toCStarRep

@[simp] lemma sectorFamily_rep (ψ : PureState A) :
    (sectorFamily A).rep ψ = ψ.toCStarRep := rfl

/-- The pure-state sector family is *physical* for the irreducibility
predicate: every member is an irreducible representation. -/
lemma sectorFamily_isPhysical_isIrreducible :
    (sectorFamily A).IsPhysical CStarRep.IsIrreducible where
  isPhysical ψ := toCStarRep_isIrreducible ψ

end PureState
