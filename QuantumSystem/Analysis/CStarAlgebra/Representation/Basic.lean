/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.InvariantSubspace

/-!
# Bundled `*`-representations of a C\*-algebra on a complex Hilbert space

This file introduces the type `CStarRep A` of (non-unital) `*`-representations
of a non-unital C\*-algebra `A` on a complex Hilbert space, packaged as the
pair `(H, π)` of a carrier and a non-unital star-algebra homomorphism into
the C\*-algebra of bounded linear operators `H →L[ℂ] H`.

`CStarRep A` is a foundational, sector-agnostic notion: it is the generic
data of a C\*-algebra representation, with no choice of cyclic vector or
attachment to a state or positive functional.  Both the GNS construction and the abstract
representation-theoretic layer are built on top of it:

* `CStarAlgebra/GNS/Representation.lean` adds a cyclic vector and a positive
  functional to obtain a GNS triplet (`GNS.Representation` extends `CStarRep`);
* `CStarAlgebra/Representation/UnitaryEquiv.lean` defines unitary equivalence
  between two `CStarRep`s as the existence of an intertwining unitary map (no
  cyclic vector compatibility, contrary to `GNS.Representation.UnitaryEquiv`
  which is the same-functional GNS uniqueness statement);
* `CStarAlgebra/Representation/Irreducible.lean` lifts the irreducibility
  predicate to the general `CStarRep` setting;
* `CStarAlgebra/Representation/VectorFunctional.lean` defines the vector
  functionals `a ↦ ⟪v, π a v⟫` of a `CStarRep` and their quasi-state bounds;
* `CStarAlgebra/Representation/SectorFamily.lean` packages indexed families of
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
bundled `(H, π)` structure in Mathlib.  `PositiveLinearMap.gnsCStarRep` bundles exactly these
two Mathlib objects, and the canonical GNS triplet `GNS.Representation.canonical` extends it.

## Relation to `GNS.Representation`

`GNS.Representation f` (defined in
`QuantumSystem/Analysis/CStarAlgebra/GNS/Representation.lean`) is the GNS
triplet `(H, π, ξ)` for a specific positive functional `f : A →ₚ[ℂ] ℂ` (a
state `ω` being the case `f = PositiveLinearMap.ofClass ω`), adding a cyclic
vector `ξ` and the GNS identity `f a = ⟪ξ, π a ξ⟫` on top of the data of a
`CStarRep A`.
A GNS triplet is a `CStarRep` with extra data: the structure projection
`GNS.Representation.toCStarRep` forgets the cyclic vector, so every notion
defined for `CStarRep` (invariance, irreducibility, unitary equivalence)
applies to GNS triplets directly.

## Main definitions

* `CStarRep A` — a bundled non-unital `*`-representation
  `π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)` together with the carrier `H` and its complex Hilbert space
  structure.
* `CStarRep.adjoint_π` — `(π a)† = π (a*)`.
* `CStarRep.orbit R v` — the orbit map `a ↦ π a v` of a vector, as a
  continuous linear map `A →L[ℂ] H`.
-/

@[expose] public section

open scoped InnerProduct

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- A bundled non-unital `*`-representation of a non-unital C\*-algebra
`A` on a complex Hilbert space.

Fields:

* `H` — the underlying type of the Hilbert space.
* `[normedAddCommGroup]`, `[innerProductSpace]`, `[completeSpace]` — the complex Hilbert space
  structure of `H`, as Mathlib's unbundled instances.
* `π` — a non-unital `*`-representation `A →⋆ₙₐ[ℂ] (H →L[ℂ] H)`.

This is the underlying data of a representation without any choice of a
cyclic vector or attachment to a particular state.  For a GNS triplet
attached to a fixed positive functional, see `GNS.Representation`. -/
structure CStarRep (A : Type u) [NonUnitalCStarAlgebra A] where
  /-- The Hilbert space on which the representation acts. -/
  H : Type v
  /-- The norm of `H`. -/
  [normedAddCommGroup : NormedAddCommGroup H]
  /-- The complex inner product of `H`. -/
  [innerProductSpace : InnerProductSpace ℂ H]
  /-- The completeness of `H`. -/
  [completeSpace : CompleteSpace H]
  /-- The non-unital `*`-representation `A →⋆ₙₐ[ℂ] (H →L[ℂ] H)`. -/
  π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)

attribute [instance] CStarRep.normedAddCommGroup CStarRep.innerProductSpace
  CStarRep.completeSpace

namespace CStarRep

/-- A `*`-representation sends adjoints to adjoints: `(π a)† = π (a*)`. -/
lemma adjoint_π (R : CStarRep A) (a : A) : (R.π a)† = R.π (star a) := by
  rw [map_star, ContinuousLinearMap.star_eq_adjoint]

/-- The orbit map `a ↦ π a v` of a vector `v`, as a continuous linear map `A →L[ℂ] H`.
It is bounded by `‖v‖`, since `*`-homomorphisms of C\*-algebras are contractive. -/
noncomputable def orbit (R : CStarRep A) (v : R.H) : A →L[ℂ] R.H :=
  LinearMap.mkContinuous
    { toFun := fun a => R.π a v
      map_add' := fun a b => by simp
      map_smul' := fun c a => by simp }
    ‖v‖
    fun a => ((R.π a).le_opNorm v).trans <| by
      rw [mul_comm]
      gcongr
      exact NonUnitalStarAlgHom.norm_apply_le R.π a

/-- The orbit map evaluates as `a ↦ π a v`. -/
@[simp] lemma orbit_apply (R : CStarRep A) (v : R.H) (a : A) : R.orbit v a = R.π a v := rfl

/-- The orbit map of `v` has operator norm at most `‖v‖`. -/
lemma norm_orbit_le (R : CStarRep A) (v : R.H) : ‖R.orbit v‖ ≤ ‖v‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg v) _

/-- `v` is a cyclic vector for the operators `π(A)` (`InnerProductSpace.IsCyclicVector`) iff its
orbit `{π a v | a ∈ A}` is dense: the orbit is the range of the linear map `R.orbit v`, hence
already a linear subspace, so the closure of its span is its closure. -/
lemma isCyclicVector_iff_denseRange_orbit (R : CStarRep A) (v : R.H) :
    InnerProductSpace.IsCyclicVector (Set.range (R.π : A → R.H →L[ℂ] R.H)) v ↔
      DenseRange (R.orbit v) := by
  have hrange : (Set.range fun T : Set.range (R.π : A → R.H →L[ℂ] R.H) =>
      (T : R.H →L[ℂ] R.H) v) = (LinearMap.range (R.orbit v : A →ₗ[ℂ] R.H) : Set R.H) := by
    ext y
    simp [eq_comm]
  rw [InnerProductSpace.isCyclicVector_iff, InnerProductSpace.cyclicSubspace, hrange,
    Submodule.span_eq, ← SetLike.coe_set_eq, ClosedSubmodule.coe_top, DenseRange,
    dense_iff_closure_eq]
  rfl

end CStarRep
