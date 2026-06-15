module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Set.Lattice

/-!
# Cones: the abstract region geometry of a lattice

A **cone** of the lattice `L` is an abstract subset of sites
(`Cone L := { region : Set L }`).  This is the *pure-geometry* layer: it depends
only on the index type `L`, with no algebra, no net (`LocalNetLike`), and no
Hilbert space.  The net and the quasi-local algebra are defined *on top of* this
layer; the cone→subalgebra bridge (`localConeSubalg`, `complementConeSubalg`) lives
in `QuasiLocalAlgebra/ConeSubalgebra.lean`, and the causal/spacelike refinement in
`Geometry/Spacelike.lean`.

In concrete geometric models (`L = ℤ²` with wedges, spacelike cones, …) the cone is
the lattice intersection of a half-plane or wedge; the abstract version here keeps
the DHR infrastructure free of any specific geometry.

## Main definitions

* `LocalNetLike.Cone L` — a cone, presented as a `Set L`.
* `LocalNetLike.Cone.ofFinset` — `Finset L → Cone L`.
* `LocalNetLike.Cone.union` — union of cones.
* `LocalNetLike.Cone.Separated` — region-disjointness, the lattice shadow of
  spacelike separation.

## References

* Ogata, Pérez-García, Ruiz-de-Alarcón, *Haag Duality for 2D Quantum Spin
  Systems*, arXiv:2509.23734v1, §1.
* Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §1.3.
-/

@[expose] public section

namespace LocalNetLike

/-- A **cone** of the lattice `L`: a subset of sites.  Abstract — concrete
geometric cones (ℝ² wedges, spacelike cones, …) are supplied by individual lattice
instances via constructors like `Cone.ofWedge`. -/
structure Cone (L : Type*) where
  /-- The region of sites covered by the cone. -/
  region : Set L

namespace Cone

variable {L : Type*}

/-- Embed a finite region as a cone with that finite region as its support.
Provides the bridge between the bounded-region (`Finset L`) and cone (`Set L`)
APIs. -/
def ofFinset (Λ : Finset L) : Cone L where
  region := (↑Λ : Set L)

@[simp] lemma region_ofFinset (Λ : Finset L) :
    (Cone.ofFinset (L := L) Λ).region = (↑Λ : Set L) := rfl

/-- A cone is determined by its region. -/
@[ext] lemma ext {Λ₁ Λ₂ : Cone L} (h : Λ₁.region = Λ₂.region) : Λ₁ = Λ₂ := by
  cases Λ₁; cases Λ₂; cases h; rfl

/-- The **union** of two cones: the cone whose region is the union of the two
regions.  Used to combine the localisation regions of two cone-localised
endomorphisms when landing an intertwiner. -/
def union (Λ₁ Λ₂ : Cone L) : Cone L where
  region := Λ₁.region ∪ Λ₂.region

@[simp] lemma union_region (Λ₁ Λ₂ : Cone L) :
    (Λ₁.union Λ₂).region = Λ₁.region ∪ Λ₂.region := rfl

lemma subset_union_left (Λ₁ Λ₂ : Cone L) :
    Λ₁.region ⊆ (Λ₁.union Λ₂).region := Set.subset_union_left

lemma subset_union_right (Λ₁ Λ₂ : Cone L) :
    Λ₂.region ⊆ (Λ₁.union Λ₂).region := Set.subset_union_right

/-- Union of cones is commutative. -/
lemma union_comm (Λ₁ Λ₂ : Cone L) : Λ₁.union Λ₂ = Λ₂.union Λ₁ :=
  Cone.ext (Set.union_comm _ _)

/-- Union of cones is associative. -/
lemma union_assoc (Λ₁ Λ₂ Λ₃ : Cone L) :
    (Λ₁.union Λ₂).union Λ₃ = Λ₁.union (Λ₂.union Λ₃) :=
  Cone.ext (Set.union_assoc _ _ _)

/-- Two cones are **separated** when their regions are disjoint.  This is the
lattice shadow of spacelike separation: charges localised in separated cones
commute (`LocalNetLike.commutes_of_separated`).  In concrete ℝ²-wedge models it is
implied by, but weaker than, geometric spacelike separation of the wedges. -/
def Separated (Λ₁ Λ₂ : Cone L) : Prop := Disjoint Λ₁.region Λ₂.region

/-- Separation of cones is symmetric. -/
lemma Separated.symm {Λ₁ Λ₂ : Cone L} (h : Separated Λ₁ Λ₂) : Separated Λ₂ Λ₁ :=
  Disjoint.symm h

@[simp] lemma separated_iff_disjoint {Λ₁ Λ₂ : Cone L} :
    Separated Λ₁ Λ₂ ↔ Disjoint Λ₁.region Λ₂.region := Iff.rfl

end Cone

end LocalNetLike
