module

public import QuantumSystem.Algebra.LocalNet

/-!
# `LocalNetLike`: a typeclass abstraction of Haag–Kastler local net data

This file introduces a `LocalNetLike` typeclass that captures the structural data of a
Haag–Kastler local net independently of the concrete carrier of sites.  Both the existing
finite-dimensional `LocalNet` (sites are `Fintype`) and the future `QuasiLocalNet`
(infinite lattices) will be instances.  The motivation is to formulate locality, covariance,
and invariant-state predicates once over the abstract carrier rather than threading
type-specific bridge lemmas through downstream proofs.

## Design

The class bundles the following pieces (Verch 2025 §1.2 axioms (i) and (ii)):

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

/-- **Local net of `*`-algebras** as a typeclass over a site type `L`.

    The carrier `L` itself is required only to have decidable equality on sites; in
    particular it need not be a `Fintype`.  The local algebra family is presented
    abstractly as `Finset L → Type*` so that both concrete matrix realisations
    (`LocalNet`) and inductive-limit-style carriers (`QuasiLocalAlgebra`) fit. -/
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
  /-- **Isotony embedding** `𝔄(Λ) ↪ 𝔄(Λ')` (Verch 2025 §1.2 axiom (i)). -/
  isotony {Λ Λ' : Finset L} (h : Λ ⊆ Λ') :
    localAlgebra Λ →⋆ₐ[ℂ] localAlgebra Λ'
  /-- Functoriality (identity): the isotony embedding along `Subset.refl` is the
      identity `*`-algebra homomorphism.  The composition law along `Subset.trans`
      is provided separately by the optional mixin `LocalNetLike.IsFunctorial`. -/
  isotony_refl (Λ : Finset L) :
    isotony (Finset.Subset.refl Λ) = StarAlgHom.id ℂ (localAlgebra Λ)
  /-- **Locality** (Verch 2025 §1.2 axiom (ii) / Haag–Kastler): the images of two
      disjoint subregions commute inside the larger algebra. -/
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

end LocalNetLike

