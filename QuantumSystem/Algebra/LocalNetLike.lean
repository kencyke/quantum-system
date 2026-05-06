module

public import QuantumSystem.Algebra.LocalNet

/-!
# `LocalNetLike`: a typeclass abstraction of finite-region local net data

This file introduces a `LocalNetLike` typeclass for the finite-region, lattice-style
part of a local net.  The region family is `Finset L`, so the intended concrete
models are finite-dimensional `LocalNet`s and infinite-lattice quantum spin systems
whose local regions are finite subsets.  Continuous-spacetime AQFT, where regions
are double cones or other open sets and causality is spacelike separation, is kept
in a separate interface.

The motivation is to formulate isotony and disjoint-region locality once over an
abstract site carrier rather than threading type-specific bridge lemmas through
downstream lattice/spin-system proofs.

## Design

The class bundles the following pieces for finite lattice regions:

* per-site Hilbert-space index types,
* a region-indexed family of `*`-algebras over `ℂ` (presented as separate
  `Semiring`, `Algebra ℂ`, `StarRing`, `StarModule ℂ` fields since Mathlib does
  not bundle these into a single `StarAlgebra` class),
* the **isotony embedding** `𝔄(Λ) →⋆ₐ[ℂ] 𝔄(Λ')` for `Λ ⊆ Λ'` together with the
  functor identity law (identity on `Subset.refl`),
* the **locality** axiom: disjoint sub-regions give commuting images.

Covariance and invariant-state predicates are deferred to follow-up mixin classes
(`LocalNetLike.HasGroupAction` and `LocalNetLike.HasInvariantState`) so that this base
class can be instantiated by carriers without a chosen group action.
-/

@[expose] public section

/-- **Finite-region local net of `*`-algebras** as a typeclass over a site type `L`.

    The carrier `L` itself is required only to have decidable equality on sites; in
    particular it need not be a `Fintype`.  The local algebra family is presented
    abstractly as `Finset L → Type*` so that both concrete matrix realisations
    (`LocalNet`) and lattice quasi-local constructions can share notation. -/
class LocalNetLike (L : Type*) [DecidableEq L] where
  /-- Local Hilbert-space index type at each site. -/
  localIdx : L → Type*
  [localFintype : ∀ s, Fintype (localIdx s)]
  [localDecEq : ∀ s, DecidableEq (localIdx s)]
  /-- Local algebra carrier at a region. -/
  localAlgebra : Finset L → Type*
  [localAlgebraSemiring : ∀ Λ, Semiring (localAlgebra Λ)]
  [localAlgebraAlgebra : ∀ Λ, Algebra ℂ (localAlgebra Λ)]
  [localAlgebraStarRing : ∀ Λ, StarRing (localAlgebra Λ)]
  [localAlgebraStarModule : ∀ Λ, StarModule ℂ (localAlgebra Λ)]
  /-- **Isotony embedding** `𝔄(Λ) ↪ 𝔄(Λ')` for finite regions. -/
  isotony {Λ Λ' : Finset L} (h : Λ ⊆ Λ') :
    localAlgebra Λ →⋆ₐ[ℂ] localAlgebra Λ'
  /-- Functoriality (identity): the isotony embedding along `Subset.refl` is the
      identity `*`-algebra homomorphism.  The composition law along `Subset.trans`
      is provided separately by the optional mixin `LocalNetLike.IsFunctorial`. -/
  isotony_refl (Λ : Finset L) :
    isotony (Finset.Subset.refl Λ) = StarAlgHom.id ℂ (localAlgebra Λ)
    /-- **Disjoint-region locality** for the lattice/spin setting: the images of two
      disjoint finite subregions commute inside the larger algebra. -/
  isLocal {Λ₁ Λ₂ Λ_total : Finset L} (h₁ : Λ₁ ⊆ Λ_total) (h₂ : Λ₂ ⊆ Λ_total)
      (hd : Disjoint Λ₁ Λ₂) (a : localAlgebra Λ₁) (b : localAlgebra Λ₂) :
    Commute (isotony h₁ a) (isotony h₂ b)

namespace LocalNetLike

variable {L : Type*} [DecidableEq L] [LocalNetLike L]

instance instFintypeLocalIdx (s : L) :
    Fintype (LocalNetLike.localIdx (L := L) s) :=
  LocalNetLike.localFintype s

instance instDecidableEqLocalIdx (s : L) :
    DecidableEq (LocalNetLike.localIdx (L := L) s) :=
  LocalNetLike.localDecEq s

instance instSemiringLocalAlgebra (Λ : Finset L) :
    Semiring (LocalNetLike.localAlgebra (L := L) Λ) :=
  LocalNetLike.localAlgebraSemiring Λ

instance instAlgebraLocalAlgebra (Λ : Finset L) :
    Algebra ℂ (LocalNetLike.localAlgebra (L := L) Λ) :=
  LocalNetLike.localAlgebraAlgebra Λ

instance instStarRingLocalAlgebra (Λ : Finset L) :
    StarRing (LocalNetLike.localAlgebra (L := L) Λ) :=
  LocalNetLike.localAlgebraStarRing Λ

instance instStarModuleLocalAlgebra (Λ : Finset L) :
    StarModule ℂ (LocalNetLike.localAlgebra (L := L) Λ) :=
  LocalNetLike.localAlgebraStarModule Λ

/-! ### Optional exactness properties for finite-region nets -/

/-- Optional property: every finite-region isotony map is injective.

This is kept as a mixin because the base `LocalNetLike` class is also used for
lightweight kinematic data.  Concrete spin-system instances should provide this
when the local fibres are nonempty. -/
class IsotonyInjective (L : Type*) [DecidableEq L] [LocalNetLike L] : Prop where
  isotony_injective {Λ Λ' : Finset L} (h : Λ ⊆ Λ') :
    Function.Injective (LocalNetLike.isotony (L := L) h)

/-- Optional property: finite-region isotony is functorial under inclusion.

The base class already contains the identity law.  This mixin records the
composition law needed to regard the finite-region net as an honest functor from
the inclusion preorder to `*`-algebras. -/
class IsFunctorial (L : Type*) [DecidableEq L] [LocalNetLike L] : Prop where
  isotony_comp {Λ₁ Λ₂ Λ₃ : Finset L} (h₁₂ : Λ₁ ⊆ Λ₂) (h₂₃ : Λ₂ ⊆ Λ₃) :
    LocalNetLike.isotony (L := L) (h₁₂.trans h₂₃) =
      (LocalNetLike.isotony (L := L) h₂₃).comp (LocalNetLike.isotony (L := L) h₁₂)

end LocalNetLike
