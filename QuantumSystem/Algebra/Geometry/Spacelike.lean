module

public import QuantumSystem.Algebra.Geometry.Cone

/-!
# Spacelike geometry: the causal layer over the cones

The dimension-dependent statistics of DHR sectors — braided in `d ≤ 2`, symmetric
in `d ≥ 3` — and the very *existence* of charge transports rest on causal/geometric
facts about cones (spacelike separation, connectivity of the complement, existence
of spacelike cones) that are properties of the underlying spacetime, not of the net.

This file is the **causal layer** `SpacelikeGeometry L`: it refines the abstract
cone geometry (`Geometry/Cone.lean`) with a spacelike-separation relation, a notion
of *proper* (admissible) cone, and the existence of spacelike proper cones.  It is
independent of `LocalNetLike` and of any algebra — the net is defined *on top of*
this geometry.

No metric or topology on `L` is required: concrete `d ≥ 3` models provide an
instance, while lattice models such as the qubit chain (`L = ℤ`) simply omit it.

## On proper and bounded regions

`IsProper` distinguishes the admissible spacelike cones from degenerate regions
(e.g. the empty region, where localization forces the identity).  DHR
transportability targets are required to be **proper** — the empty cone is not a
legitimate target for transporting a nontrivial sector.

`IsBounded` is the class of regions a sector may be *localized* in: it contains the
empty region and is closed under finite unions (so it is closed under the fusion of
sectors), and crucially every bounded region admits a **proper cone spacelike to
it** (`exists_spacelike_of_bounded`) — the room needed to transport a second sector
clear of the first.  Proper cones are bounded; unions of proper cones (the
localization regions of fused sectors) are bounded but not proper.

## References

* Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §6.
* Fredenhagen, Rehren, Schroer, *Superselection sectors with braid group
  statistics and exchange algebras I*, Comm. Math. Phys. 125 (1989).
-/

@[expose] public section

namespace LocalNetLike

/-- **Spacelike geometry** on the index type `L`: an abstract causal structure on
cones, independent of `LocalNetLike` (the net is defined *on top of* this layer).

* `Spacelike Λ₁ Λ₂` — the abstract shadow of spacelike separation; symmetric and
  refining region-disjointness.
* `IsProper Λ` — `Λ` is an admissible (proper) spacelike cone (a transport target).
* `IsBounded Λ` — `Λ` is a bounded region (a localization region); contains the
  empty region and is closed under union.
* `exists_spacelike_of_bounded` — every bounded region has a proper cone spacelike
  to it.  This is the **cone-existence axiom**: it guarantees room to transport a
  sector clear of a given bounded localization region (the geometric input to the
  braiding).

Concrete high-dimensional (`d ≥ 3`) models instantiate this — including the
connectivity of the spacelike complement that makes the statistics symmetric —
while lattice models omit it. -/
class SpacelikeGeometry (L : Type*) where
  /-- Spacelike separation of cones. -/
  Spacelike : Cone L → Cone L → Prop
  /-- Admissible (proper) spacelike cones — the transport targets. -/
  IsProper : Cone L → Prop
  /-- Bounded regions — the localization regions. -/
  IsBounded : Cone L → Prop
  /-- Spacelike separation is symmetric. -/
  spacelike_symm : ∀ {Λ₁ Λ₂ : Cone L}, Spacelike Λ₁ Λ₂ → Spacelike Λ₂ Λ₁
  /-- Spacelike-separated cones have disjoint regions (the lattice shadow). -/
  spacelike_separated :
    ∀ {Λ₁ Λ₂ : Cone L}, Spacelike Λ₁ Λ₂ → Disjoint Λ₁.region Λ₂.region
  /-- The empty region is bounded (the localization region of the vacuum). -/
  isBounded_empty : IsBounded { region := (∅ : Set L) }
  /-- Bounded regions are closed under union (fusion of sectors). -/
  isBounded_union :
    ∀ {Λ₁ Λ₂ : Cone L}, IsBounded Λ₁ → IsBounded Λ₂ → IsBounded (Λ₁.union Λ₂)
  /-- **Cone existence.**  Every bounded region admits a proper cone spacelike to
  it — there is always room to transport a sector clear of a bounded region. -/
  exists_spacelike_of_bounded :
    ∀ {Λ : Cone L}, IsBounded Λ → ∃ Λ', IsProper Λ' ∧ Spacelike Λ Λ'

end LocalNetLike
