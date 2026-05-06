module

public import QuantumSystem.Algebra.LocalNetLike
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Hilbert spaces over a `LocalNetLike` (Phase 5'a steps 1–2)

Naaijkens 2012 §1.3 and §3.5 build the quasi-local algebra of an infinite
quantum lattice system as the norm closure of the union of subalgebras
`𝔄(Λ) ↪ B(H_Λ)` indexed by finite regions `Λ`.  This file launches that
construction by providing:

* the **per-site Hilbert space** `siteHilbert s` at each lattice point;
* the **finite-region Hilbert space** `regionHilbert Λ`, realised as the
  Euclidean space indexed by tuples `(s : Λ) → localIdx s`.

For finite tensor products of finite-dimensional Hilbert spaces one has the
canonical isomorphism
`⊗_{s ∈ Λ} ℂ^{n_s} ≅ ℂ^{∏_{s ∈ Λ} n_s} = EuclideanSpace ℂ ((s : Λ) → localIdx s)`,
so realising `regionHilbert Λ` as the right-hand side gives an honest Hilbert
space directly via the `EuclideanSpace` API and avoids the missing
`InnerProductSpace` instance for `PiTensorProduct`.  The `tprod`-style
multilinear-map structure is recovered later via the `Matrix`/`Pi.basisFun`
correspondence.

The infinite-site limit `globalHilbert : Type` and the isometric embeddings
`regionHilbert Λ →ₗᵢ globalHilbert` for varying `Λ` are introduced in
`QuantumSystem/Algebra/LocalNet/QuasiLocalAlgebra/GlobalHilbert.lean`
following Naaijkens §3.5 / Bratteli–Robinson §2.7.2.

## Main definitions

* `LocalNetLike.siteHilbert s` — finite-dimensional Hilbert space at a site
  `s : L`, realised as `EuclideanSpace ℂ (LocalNetLike.localIdx s)`.
* `LocalNetLike.regionIdx Λ` — basis index type for the region Hilbert
  space at the finite region `Λ`, namely the `Pi`-type
  `(s : Λ) → localIdx s`.
* `LocalNetLike.regionHilbert Λ` — finite-dimensional Hilbert space at the
  finite region `Λ`, realised as `EuclideanSpace ℂ (regionIdx Λ)`.

## References

* Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §1.3 and §3.5.
* Bratteli, Robinson, *Operator Algebras and Quantum Statistical Mechanics II*,
  §2.7.2.
-/

@[expose] public section

namespace LocalNetLike

variable {L : Type*} [DecidableEq L] [LocalNetLike L]

/-- The single-site Hilbert space at site `s : L`, realised as
`EuclideanSpace ℂ (localIdx s)`.  The chosen finite index type
`localIdx s` is the same one used by the local algebra at `s`. -/
abbrev siteHilbert (s : L) : Type _ :=
  EuclideanSpace ℂ (LocalNetLike.localIdx (L := L) s)

/-- Basis index for the finite-region Hilbert space at `Λ : Finset L`:
the dependent product type `(s : Λ) → localIdx s` enumerating one local
basis index per site in `Λ`. -/
abbrev regionIdx (Λ : Finset L) : Type _ :=
  (s : Λ) → LocalNetLike.localIdx (L := L) s.1

/-- The Hilbert space attached to a finite region `Λ : Finset L`.

Realised as `EuclideanSpace ℂ (regionIdx Λ)`, this is the basis-indexed model
of the tensor product `⨂_{s ∈ Λ} siteHilbert s`.  The two are canonically
isomorphic in finite dimension, and the basis-indexed presentation has the
advantage of inheriting `NormedAddCommGroup`, `InnerProductSpace ℂ`,
`FiniteDimensional ℂ` and `CompleteSpace` instances directly from
`EuclideanSpace`. -/
abbrev regionHilbert (Λ : Finset L) : Type _ :=
  EuclideanSpace ℂ (regionIdx (L := L) Λ)

end LocalNetLike

/-- Optional mixin: realise the abstract local algebra `LocalNetLike.localAlgebra Λ`
as an honest `*`-algebra of operators on `regionHilbert Λ`.  This is the bridge
that ties the kinematic abstraction `LocalNetLike` to the basis-indexed
operator-algebra construction underlying the Haag–Kastler quasi-local algebra.

Concrete instances should provide `localRep Λ` whenever the abstract algebra
is intended to be identified with a sub-algebra of the matrix algebra on
`regionHilbert Λ`. -/
class LocalNetLike.HasLocalRepresentation
    (L : Type*) [DecidableEq L] [LocalNetLike L] where
  /-- A bundled `*`-algebra hom from the abstract local algebra to the
  operator algebra on `regionHilbert Λ`. -/
  localRep (Λ : Finset L) :
    LocalNetLike.localAlgebra (L := L) Λ →⋆ₐ[ℂ]
      (LocalNetLike.regionHilbert (L := L) Λ
        →L[ℂ] LocalNetLike.regionHilbert (L := L) Λ)

/-- Optional refinement: `HasLocalRepresentation` is *faithful*, i.e. the
representation `localRep Λ` is injective.  Whenever this holds, the abstract
local algebra is identified up to isomorphism with a sub-`*`-algebra of the
finite-dimensional C⋆-algebra `regionHilbert Λ →L[ℂ] regionHilbert Λ`, hence
inherits a canonical (finite-dim) C⋆-structure via that embedding.

This is the abstract-level analogue of the existing `LocalNetLike.IsotonyInjective`
mixin and is the cleanest way to record that the kinematic data is non-degenerate
without wedging a full `CStarAlgebra` instance directly onto the abstract
`localAlgebra` field, which would conflict with the basic `Semiring/Algebra`
instances bundled into `LocalNetLike`. -/
class LocalNetLike.HasFaithfulLocalRepresentation
    (L : Type*) [DecidableEq L] [LocalNetLike L]
    [LocalNetLike.HasLocalRepresentation L] : Prop where
  localRep_injective (Λ : Finset L) :
    Function.Injective
      (LocalNetLike.HasLocalRepresentation.localRep (L := L) Λ)
