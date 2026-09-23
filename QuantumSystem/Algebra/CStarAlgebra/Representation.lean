/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.HilbertSpace

/-!
# Bundled `*`-representations of a C\*-algebra on a complex Hilbert space

This file introduces the type `CStarRep A` of (non-unital) `*`-representations
of a non-unital C\*-algebra `A` on a complex Hilbert space, packaged as the
pair `(H, π)` of a carrier and a non-unital star-algebra homomorphism into
the C\*-algebra of bounded linear operators `𝓑(H)`.

`CStarRep A` is a foundational, sector-agnostic notion: it is the generic
data of a C\*-algebra representation, with no choice of cyclic vector or
attachment to a state.  Both the GNS construction and the abstract
representation-theoretic layer are built on top of it:

* `CStarAlgebra/GNS/Representation.lean` adds a cyclic vector and a state to
  obtain a GNS triplet (`GNS.Representation` extends `CStarRep`);
* `CStarAlgebra/Representation/UnitaryEquiv.lean` defines unitary equivalence
  between two `CStarRep`s as the existence of an intertwining unitary map (no
  cyclic vector compatibility, contrary to `GNS.Representation.UnitaryEquiv`
  which is the same-state GNS uniqueness statement);
* `CStarAlgebra/Representation/Irreducible.lean` lifts the irreducibility
  predicate to the general `CStarRep` setting;
* `CStarAlgebra/Representation/Family.lean` packages indexed families of
  representatives (`SectorFamily`), on which a superselection sector theory
  imposes its selection criteria (DHR, KMS, ...) as separate predicates;
* `CStarAlgebra/Representation/DirectSum.lean` forms the `ℓ²`-direct sum of
  such a family.

## Relation to Mathlib

Mathlib's `Representation` (in `Mathlib.RepresentationTheory.Basic`) is the
group/monoid representation type `G →* (V →ₗ[k] V)` and does not match
the C\*-algebra / Hilbert-space setting.  The GNS construction in
`Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal` exposes the Hilbert
space (`f.GNS`) and the homomorphism (`f.gnsNonUnitalStarAlgHom`, or
`f.gnsStarAlgHom` in the unital case) as separate artifacts; there is no
bundled `(H, π)` structure in Mathlib.  The canonical GNS triplet
`GNS.Representation.canonical` bundles exactly these two Mathlib objects.

## Relation to `GNS.Representation`

`GNS.Representation ω` (defined in
`QuantumSystem/Algebra/CStarAlgebra/GNS/Representation.lean`) is the GNS
triplet `(H, π, ξ)` for a specific state `ω : State A`, adding a
cyclic unit vector `ξ` and the GNS identity
`ω a = ⟪ξ, π a ξ⟫` on top of the data of a `CStarRep A`.
A GNS triplet is a `CStarRep` with extra data: the structure projection
`GNS.Representation.toCStarRep` forgets the cyclic vector, so every notion
defined for `CStarRep` (invariance, irreducibility, unitary equivalence)
applies to GNS triplets directly.

## Main definitions

* `CStarRep A` — a bundled non-unital `*`-representation
  `π : A →⋆ₙₐ[ℂ] 𝓑(H)` together with the carrier `H` and its
  `ComplexHilbertSpace` instance.
-/

@[expose] public section

open scoped ComplexHilbertSpace

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- A bundled non-unital `*`-representation of a non-unital C\*-algebra
`A` on a complex Hilbert space.

Fields:

* `H` — the underlying type of the Hilbert space.
* `[hilbert]` — evidence that `H` is a complex Hilbert space.
* `π` — a non-unital `*`-representation `A →⋆ₙₐ[ℂ] 𝓑(H)`.

This is the underlying data of a representation without any choice of a
cyclic vector or attachment to a particular state.  For a GNS triplet
attached to a fixed state, see `GNS.Representation`. -/
structure CStarRep (A : Type u) [NonUnitalCStarAlgebra A] where
  /-- The Hilbert space on which the representation acts. -/
  H : Type v
  /-- The complex Hilbert space structure on `H`. -/
  [hilbert : ComplexHilbertSpace H]
  /-- The non-unital `*`-representation `A →⋆ₙₐ[ℂ] 𝓑(H)`. -/
  π : A →⋆ₙₐ[ℂ] 𝓑(H)

attribute [instance] CStarRep.hilbert
