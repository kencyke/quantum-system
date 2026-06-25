module

public import QuantumSystem.ForMathlib.Algebra.Colimit.DirectLimitStar
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.DirectLimit
public import QuantumSystem.ForMathlib.Topology.Algebra.CStarCompletion

/-!
# Local nets of C⋆-algebras

This file reifies the **net** of an AQFT system as a first-class object: a *local net of
C⋆-algebras* over the finite regions of a site set is the assignment `Λ ↦ 𝔄(Λ)` of a
C⋆-algebra to each finite region `Λ : Finset sites`, together with the **isotony embeddings**
`𝔄(Λ) ↪ 𝔄(Λ')` for `Λ ⊆ Λ'`, which are *functorial* (compose, and the identity inclusion is
the identity) and satisfy **locality** (observables in disjoint regions commute). This is the
data of a Haag–Kastler net specialised to a lattice of sites (Naaijkens 2012 §1.3, Verch 2025
§1.2, Bratteli–Robinson Vol.2 §6.2).

The structure is genuinely abstract: it does not commit to any concrete realisation of the
local algebras. The finite-dimensional matrix net `𝔄(Λ) = ⊗_{x ∈ Λ} M_{n_x}(ℂ)` is one
instance, built from a `SiteIndexSystem` via `SiteIndexSystem.toLocalNet`
(`LocalNet.QuasiLocal`).

On any local net this file builds, once and for all:

* the **directed system** of `*`-algebras (`directedSystem`), via functoriality;
* the **algebra of local observables** `quasiLocalAlgebra` (the algebraic inductive limit) with
  cocone `ιLocal`, exhaustion `exists_ιLocal`, and locality `ιLocal_commute_of_disjoint`;
* for a **faithful** net (`Faithful`: all inclusions injective — the standard AQFT
  non-degeneracy condition), the C⋆-norm and the **quasi-local C⋆-algebra**
  `quasiLocalCStarAlgebra` (its completion), with dense embeddings `ιLocalCStar`;
* the **covariance** of the net: `Symmetry` (the AQFT covariance datum `β(𝔄(Λ)) = 𝔄(σΛ)`, natural
  with respect to isotony), which form a **group** under composition (`Group N.Symmetry`, with
  `Symmetry.id`/`Symmetry.comp`/`Symmetry.inv`), and the purely algebraic action
  `Symmetry.quasiLocalRelabel` on the algebra of local observables, which is a monoid homomorphism
  out of that group (`quasiLocalRelabel_one`/`quasiLocalRelabel_mul`) — so a group `G` acting on
  the net (a hom `G →* N.Symmetry`) acts on the local observables by `*`-endomorphisms. Since each
  `β` is a `*`-isomorphism this action is in fact by `*`-algebra automorphisms:
  `Symmetry.quasiLocalRelabelStarEquiv` packages each symmetry as a `*`-algebra automorphism
  `𝔄_loc ≃⋆ₐ[ℂ] 𝔄_loc` and `Symmetry.quasiLocalRelabelStarHom` bundles them into a group
  homomorphism into its `*`-automorphism group. For a **faithful** net the action is isometric, so
  `Symmetry.quasiLocalCStarRelabel` extends it to a `*`-automorphism `𝔄 ≃⋆ₐ[ℂ] 𝔄` of the quasi-local
  C⋆-algebra and `Symmetry.quasiLocalCStarRelabelHom` to a group homomorphism — the genuine AQFT
  covariant automorphic action.

The injectivity needed for the C⋆-norm is carried by the separate `Faithful` typeclass rather
than a structure field, so that the purely algebraic constructions (`quasiLocalAlgebra`,
`ιLocal`, and the covariance action `Symmetry.quasiLocalRelabel`) need no non-degeneracy hypothesis.
-/

@[expose] public section

/-- A **local net of C⋆-algebras** over the finite regions of a site set `sites`: the assignment
    `Λ ↦ 𝔄(Λ)` together with isotony embeddings `incl : 𝔄(Λ) →⋆ₐ[ℂ] 𝔄(Λ')` for `Λ ⊆ Λ'`,
    functorial (`incl_refl`/`incl_trans`) and local (`locality`). This is the Haag–Kastler net
    structure for a lattice of sites; the matrix lattice net is one instance via
    `SiteIndexSystem.toLocalNet`. -/
structure LocalNet (sites : Type*) [DecidableEq sites] where
  /-- The local C⋆-algebra `𝔄(Λ)` assigned to a finite region. -/
  algebra : Finset sites → Type*
  /-- Each local algebra is a (complex) C⋆-algebra. -/
  [algebraCStar : ∀ Λ, CStarAlgebra (algebra Λ)]
  /-- **Isotony**: for `Λ ⊆ Λ'` an inclusion of local algebras as a unital `*`-homomorphism. -/
  incl : ∀ {Λ Λ' : Finset sites}, Λ ⊆ Λ' → (algebra Λ →⋆ₐ[ℂ] algebra Λ')
  /-- The identity inclusion `Λ ⊆ Λ` acts as the identity. -/
  incl_refl : ∀ {Λ : Finset sites} (x : algebra Λ), incl (Finset.Subset.refl Λ) x = x
  /-- **Functoriality**: the inclusions compose, so the net is a directed system. -/
  incl_trans : ∀ {Λ₁ Λ₂ Λ₃ : Finset sites} (h₁₂ : Λ₁ ⊆ Λ₂) (h₂₃ : Λ₂ ⊆ Λ₃) (x : algebra Λ₁),
      incl h₂₃ (incl h₁₂ x) = incl (h₁₂.trans h₂₃) x
  /-- **Locality** (microcausality): observables localised in *disjoint* regions commute inside
      any common larger region. For a lattice net this is locality *in space* — the kinematical
      (equal-time) analogue of relativistic Einstein causality, with spatial disjointness in place
      of spacelike separation (Naaijkens 2012 §3.4). -/
  locality : ∀ {Λ₁ Λ₂ Λ : Finset sites} (h₁ : Λ₁ ⊆ Λ) (h₂ : Λ₂ ⊆ Λ),
      Disjoint Λ₁ Λ₂ → ∀ (x : algebra Λ₁) (y : algebra Λ₂),
        Commute (incl h₁ x) (incl h₂ y)

namespace LocalNet

attribute [instance] algebraCStar

variable {sites : Type*} [DecidableEq sites] (N : LocalNet sites)

/-- The net forms a directed system of `*`-algebras: the isotony embeddings compose and the
    identity inclusion is the identity. -/
instance directedSystem :
    DirectedSystem N.algebra (fun _ _ h => ⇑(N.incl h)) where
  map_self _ x := N.incl_refl x
  map_map _ _ _ hij hjk x := N.incl_trans hij hjk x

/-- The **algebra of local observables** of the net: the algebraic inductive limit of the local
    algebras along the isotony embeddings. Its C⋆-completion is the quasi-local algebra. -/
noncomputable abbrev quasiLocalAlgebra : Type _ :=
  DirectLimit N.algebra (fun _ _ h => N.incl h)

/-- Componentwise behaviour of the involution on the algebra of local observables. The
    `Star`, `StarRing`, `Algebra ℂ` and `StarModule ℂ` instances come from the general
    direct-limit constructions, since each `algebra Λ` is a `ℂ`-`*`-algebra and `incl` is a
    `*`-algebra homomorphism. -/
@[simp] theorem star_mk {Λ : Finset sites} (X : N.algebra Λ) :
    star (⟦⟨Λ, X⟩⟧ : N.quasiLocalAlgebra) = ⟦⟨Λ, star X⟩⟧ := rfl

/-- The canonical embedding `𝔄(Λ) ↪ 𝔄_loc` of a local algebra into the algebra of local
    observables, as a unital ring homomorphism (the cocone of the inductive limit). -/
noncomputable def ιLocal (Λ : Finset sites) :
    N.algebra Λ →+* N.quasiLocalAlgebra :=
  DirectLimit.Ring.of N.algebra (fun _ _ h => N.incl h) Λ

/-- Compatibility of the cocone with the isotony embeddings: including `X` from `Λ` into the
    larger region `Λ'` and then into `𝔄_loc` is the same as including `X` directly. -/
@[simp] theorem ιLocal_incl {Λ Λ' : Finset sites} (h : Λ ⊆ Λ') (X : N.algebra Λ) :
    N.ιLocal Λ' (N.incl h X) = N.ιLocal Λ X :=
  DirectLimit.Ring.of_f (G := N.algebra) (f := fun _ _ h => N.incl h) h X

/-- The cocone is a `*`-homomorphism: it intertwines the local and quasi-local involutions. -/
@[simp] theorem ιLocal_star {Λ : Finset sites} (X : N.algebra Λ) :
    N.ιLocal Λ (star X) = star (N.ιLocal Λ X) :=
  (star_mk (N := N) X).symm

/-- **Exhaustion**: every element of the algebra of local observables is the image of a local
    observable from some finite region — the union of the local algebras is the whole limit. -/
theorem exists_ιLocal (z : N.quasiLocalAlgebra) :
    ∃ (Λ : Finset sites) (X : N.algebra Λ), z = N.ιLocal Λ X := by
  induction z using DirectLimit.induction with
  | _ Λ X => exact ⟨Λ, X, rfl⟩

/-- **Locality in the algebra of local observables**: observables localised in disjoint regions
    commute inside `𝔄_loc`. Lifts the net's `locality` along the ring-hom cocone. -/
theorem ιLocal_commute_of_disjoint {Λ₁ Λ₂ : Finset sites} (hd : Disjoint Λ₁ Λ₂)
    (X : N.algebra Λ₁) (Y : N.algebra Λ₂) :
    Commute (N.ιLocal Λ₁ X) (N.ιLocal Λ₂ Y) := by
  have h1 : N.ιLocal Λ₁ X
      = N.ιLocal (Λ₁ ∪ Λ₂) (N.incl Finset.subset_union_left X) :=
    (N.ιLocal_incl Finset.subset_union_left X).symm
  have h2 : N.ιLocal Λ₂ Y
      = N.ιLocal (Λ₁ ∪ Λ₂) (N.incl Finset.subset_union_right Y) :=
    (N.ιLocal_incl Finset.subset_union_right Y).symm
  rw [h1, h2]
  exact (N.locality Finset.subset_union_left Finset.subset_union_right hd X Y).map
    (N.ιLocal (Λ₁ ∪ Λ₂))

/-! ### Faithful nets and the quasi-local C⋆-algebra

A net is *faithful* when its isotony embeddings are injective (the standard AQFT non-degeneracy
condition). For a faithful net the connecting maps are isometric, so the algebra of local
observables carries a C⋆-norm whose completion is the quasi-local C⋆-algebra `𝔄 = ‾⋃_Λ 𝔄(Λ)`
(Naaijkens 2012 §1.3, Bratteli–Robinson Vol.2 §6.2). -/

/-- A local net is **faithful** when all its isotony embeddings are injective. In the standard
    AQFT definition the isotony embeddings are *injective* unital `*`-homomorphisms (Naaijkens 2012
    §3.4), so a faithful local net — `LocalNet` together with `Faithful` — is the literature's net;
    this is the non-degeneracy condition that makes the inclusions genuine and the C⋆-norm on the
    algebra of local observables well defined. Carried as a typeclass (rather than a structure
    field) so the purely algebraic constructions stay free of any non-degeneracy hypothesis. -/
class Faithful {sites : Type*} [DecidableEq sites] (N : LocalNet sites) : Prop where
  /-- Every isotony embedding of the net is injective. -/
  incl_injective : ∀ {Λ Λ' : Finset sites} (h : Λ ⊆ Λ'), Function.Injective (N.incl h)

section CStar

variable [N.Faithful]

/-- The algebra of local observables is a normed ring under the C⋆-norm of the inductive limit
    (the inclusions are injective, hence isometric). -/
noncomputable instance : NormedRing N.quasiLocalAlgebra :=
  DirectLimit.cstarNormedRing (fun _ _ h => Faithful.incl_injective h)

@[simp] theorem norm_mk {Λ : Finset sites} (X : N.algebra Λ) :
    ‖(⟦⟨Λ, X⟩⟧ : N.quasiLocalAlgebra)‖ = ‖X‖ := rfl

/-- The C⋆-norm is compatible with the `ℂ`-algebra structure. -/
noncomputable instance : NormedAlgebra ℂ N.quasiLocalAlgebra where
  norm_smul_le c x := by
    induction x using DirectLimit.induction with
    | _ Λ X => rw [DirectLimit.smul_def, norm_mk, norm_mk]; exact norm_smul_le c X

/-- `star` is isometric on the algebra of local observables. -/
instance : NormedStarGroup N.quasiLocalAlgebra where
  norm_star_le x := by
    induction x using DirectLimit.induction with
    | _ Λ X => rw [star_mk, norm_mk, norm_mk]; exact (norm_star X).le

/-- The C⋆-identity holds on the algebra of local observables. -/
instance : CStarRing N.quasiLocalAlgebra where
  norm_mul_self_le x := by
    induction x using DirectLimit.induction with
    | _ Λ X => rw [star_mk, DirectLimit.mul_def, norm_mk, norm_mk]
               exact CStarRing.norm_mul_self_le X

/-- The **quasi-local C⋆-algebra** of a faithful net: the completion of the algebra of local
    observables. This is the AQFT quasi-local algebra `𝔄 = ‾⋃_Λ 𝔄(Λ)` (Naaijkens 2012 §1.3,
    Bratteli–Robinson Vol.2 §6.2). -/
noncomputable abbrev quasiLocalCStarAlgebra : Type _ :=
  UniformSpace.Completion N.quasiLocalAlgebra

noncomputable example : CStarAlgebra N.quasiLocalCStarAlgebra := inferInstance

/-- The canonical embedding `𝔄(Λ) → 𝔄` of a local algebra into the quasi-local C⋆-algebra,
    as the completion coercion composed with the inductive-limit cocone. Its range is dense. -/
noncomputable def ιLocalCStar (Λ : Finset sites) :
    N.algebra Λ → N.quasiLocalCStarAlgebra :=
  (↑) ∘ N.ιLocal Λ

/-- The local algebras are dense in the quasi-local C⋆-algebra: every element is a norm-limit of
    local observables. -/
theorem denseRange_iUnion_ιLocalCStar :
    Dense (⋃ Λ : Finset sites, Set.range (N.ιLocalCStar Λ)) := by
  refine UniformSpace.Completion.denseRange_coe.mono ?_
  rintro _ ⟨z, rfl⟩
  obtain ⟨Λ, X, rfl⟩ := N.exists_ιLocal z
  exact Set.mem_iUnion.2 ⟨Λ, X, rfl⟩

end CStar

/-! ### Covariance: symmetries of the net

A **symmetry** of a local net is a site permutation `σ` together with, for each finite region, a
`*`-isomorphism `β_Λ : 𝔄(Λ) ≃⋆ₐ[ℂ] 𝔄(σΛ)` of local algebras that is natural with respect to the
isotony embeddings. This realises the AQFT covariance axiom `β(𝔄(Λ)) = 𝔄(σΛ)` at the abstract net
level (Naaijkens 2012 §3.2, Verch 2025 §1.2). Being purely algebraic, the induced action on the
algebra of local observables needs no faithfulness hypothesis. -/

/-- Transport a local algebra along an equality of regions, as a `*`-isomorphism. Used to identify
    `𝔄(σ₁σ₂Λ)` along the functoriality of the region map when composing symmetries. -/
def algebraCongr {Λ Λ' : Finset sites} (h : Λ = Λ') : N.algebra Λ ≃⋆ₐ[ℂ] N.algebra Λ' := by
  subst h; exact StarAlgEquiv.refl

@[simp] theorem algebraCongr_apply {Λ : Finset sites} (x : N.algebra Λ) :
    N.algebraCongr (rfl : Λ = Λ) x = x := rfl

/-- The cocone of the inductive limit absorbs the region-equality transport. -/
@[simp] theorem ιLocal_algebraCongr {Λ Λ' : Finset sites} (h : Λ = Λ') (x : N.algebra Λ) :
    N.ιLocal Λ' (N.algebraCongr h x) = N.ιLocal Λ x := by
  subst h; rfl

/-- The isotony embeddings are natural with respect to the region-equality transport. -/
theorem incl_algebraCongr {Λ₁ Λ₂ Λ₁' Λ₂' : Finset sites} (e₁ : Λ₁ = Λ₁') (e₂ : Λ₂ = Λ₂')
    (h : Λ₁ ⊆ Λ₂) (h' : Λ₁' ⊆ Λ₂') (x : N.algebra Λ₁) :
    N.algebraCongr e₂ (N.incl h x) = N.incl h' (N.algebraCongr e₁ x) := by
  subst e₁; subst e₂; rfl

/-- Transports along composable region equalities compose. -/
@[simp] theorem algebraCongr_trans {Λ₁ Λ₂ Λ₃ : Finset sites} (h₁ : Λ₁ = Λ₂) (h₂ : Λ₂ = Λ₃)
    (x : N.algebra Λ₁) :
    N.algebraCongr h₂ (N.algebraCongr h₁ x) = N.algebraCongr (h₁.trans h₂) x := by
  subst h₁; subst h₂; rfl

/-- A transport along a reflexive region equality is the identity. -/
@[simp] theorem algebraCongr_self {Λ : Finset sites} (h : Λ = Λ) (x : N.algebra Λ) :
    N.algebraCongr h x = x := by
  rw [Subsingleton.elim h rfl]; rfl

/-- Cancelling a transport against a target value moves it to the other side. -/
theorem algebraCongr_eq_iff {Λ Λ' : Finset sites} (h : Λ = Λ') (x : N.algebra Λ)
    (y : N.algebra Λ') : N.algebraCongr h x = y ↔ x = N.algebraCongr h.symm y := by
  subst h; simp

/-- A **symmetry** of a local net `N`: a site permutation `σ` together with, for every finite
    region `Λ`, a `*`-isomorphism `β Λ : 𝔄(Λ) ≃⋆ₐ[ℂ] 𝔄(σΛ)`, natural with respect to the isotony
    embeddings (`β_incl`). This is the AQFT covariance datum at the abstract net level — one element
    of a covariant group action (Naaijkens 2012 §3.2, Verch 2025 §1.2). -/
structure Symmetry where
  /-- The underlying site permutation; its image map `Λ ↦ σΛ` carries the region map. -/
  σ : sites ≃ sites
  /-- The covariance `*`-isomorphism `β_Λ : 𝔄(Λ) ≃⋆ₐ[ℂ] 𝔄(σΛ)` on each region. -/
  β : ∀ Λ : Finset sites, N.algebra Λ ≃⋆ₐ[ℂ] N.algebra (Λ.map σ.toEmbedding)
  /-- **Naturality / covariance**: `β` intertwines the isotony embeddings, so it maps the net to
      itself compatibly with inclusions — the AQFT covariance axiom `β(𝔄(Λ)) = 𝔄(σΛ)`. -/
  β_incl : ∀ {Λ Λ' : Finset sites} (h : Λ ⊆ Λ') (x : N.algebra Λ),
      β Λ' (N.incl h x) = N.incl (Finset.map_subset_map.mpr h) (β Λ x)

namespace Symmetry

variable {N} (a : N.Symmetry)

/-- The image `σΛ` of a region under the symmetry. -/
def region (Λ : Finset sites) : Finset sites := Λ.map a.σ.toEmbedding

/-- **Extensionality** for symmetries: two symmetries with the same site permutation and the same
    local `*`-isomorphisms (compared along the induced region equality) are equal. The naturality
    field `β_incl` is a proposition, hence irrelevant. -/
@[ext (iff := false)] theorem ext {s t : N.Symmetry} (hσ : s.σ = t.σ)
    (hβ : ∀ (Λ : Finset sites) (x : N.algebra Λ) (e : s.region Λ = t.region Λ),
      N.algebraCongr e (s.β Λ x) = t.β Λ x) : s = t := by
  revert hσ hβ
  obtain ⟨sσ, sβ, -⟩ := s
  obtain ⟨tσ, tβ, -⟩ := t
  rintro rfl hβ
  have hβ' : sβ = tβ := by
    funext Λ
    ext x
    simpa using hβ Λ x rfl
  subst hβ'
  rfl

/-- Naturality of the inverse local `*`-isomorphisms with respect to isotony. -/
theorem β_symm_incl {Λ Λ' : Finset sites} (h : Λ ⊆ Λ') (y : N.algebra (Λ.map a.σ.toEmbedding)) :
    (a.β Λ').symm (N.incl (Finset.map_subset_map.mpr h) y) = N.incl h ((a.β Λ).symm y) := by
  have key := a.β_incl h ((a.β Λ).symm y)
  rw [StarAlgEquiv.apply_symm_apply] at key
  rw [← key, StarAlgEquiv.symm_apply_apply]

/-- The local `*`-isomorphisms commute with the region-equality transport. -/
theorem β_algebraCongr {Λ Λ' : Finset sites} (e : Λ = Λ') (x : N.algebra Λ) :
    a.β Λ' (N.algebraCongr e x) = N.algebraCongr (by rw [e]) (a.β Λ x) := by
  subst e; simp

/-- The **covariance action** `β_a ⟦⟨Λ, X⟩⟧ = ⟦⟨σΛ, β_Λ X⟩⟧` of a symmetry on the algebra of local
    observables, as a ring homomorphism. Well-defined by naturality (`β_incl`). -/
noncomputable def quasiLocalRelabel : N.quasiLocalAlgebra →+* N.quasiLocalAlgebra :=
  DirectLimit.Ring.lift N.algebra (fun _ _ h => N.incl h) N.quasiLocalAlgebra
    (fun Λ => (N.ιLocal (a.region Λ)).comp (a.β Λ).toAlgEquiv.toAlgHom.toRingHom)
    (fun Λ Λ' h X => by
      change N.ιLocal (a.region Λ') (a.β Λ' (N.incl h X)) = N.ιLocal (a.region Λ) (a.β Λ X)
      rw [a.β_incl h]
      exact N.ιLocal_incl _ _)

@[simp] theorem quasiLocalRelabel_mk {Λ : Finset sites} (X : N.algebra Λ) :
    a.quasiLocalRelabel (⟦⟨Λ, X⟩⟧ : N.quasiLocalAlgebra) = ⟦⟨a.region Λ, a.β Λ X⟩⟧ :=
  rfl

variable (N) in
/-- The **identity symmetry**: the identity site permutation with the identity local
    `*`-isomorphisms (transported along `Λ = σ_id Λ`). -/
def id : N.Symmetry where
  σ := Equiv.refl sites
  β Λ := N.algebraCongr (by simp)
  β_incl h x := N.incl_algebraCongr _ _ h _ x

/-- **Composition of symmetries**: apply `b`, then `a`. The site permutations compose; the local
    `*`-isomorphisms compose and are transported along the region-map functoriality
    `(σ_a ∘ σ_b) Λ = σ_a (σ_b Λ)`. -/
def comp (a b : N.Symmetry) : N.Symmetry where
  σ := b.σ.trans a.σ
  β Λ := ((b.β Λ).trans (a.β (Λ.map b.σ.toEmbedding))).trans
    (N.algebraCongr (by simp [Finset.map_map, Equiv.trans_toEmbedding]))
  β_incl h x := by
    simp only [StarAlgEquiv.trans_apply]
    rw [b.β_incl h, a.β_incl (Finset.map_subset_map.mpr h)]
    exact N.incl_algebraCongr _ _ _ _ _

/-- The **inverse symmetry**: the inverse site permutation with the inverse local
    `*`-isomorphisms, transported along the region-map functoriality `σ⁻¹σ Λ = Λ`. -/
def inv (a : N.Symmetry) : N.Symmetry where
  σ := a.σ.symm
  β Λ := (N.algebraCongr (show (Λ.map a.σ.symm.toEmbedding).map a.σ.toEmbedding = Λ by
      simp [Finset.map_map]).symm).trans
      (a.β (Λ.map a.σ.symm.toEmbedding)).symm
  β_incl h x := by
    simp only [StarAlgEquiv.trans_apply]
    rw [N.incl_algebraCongr _ _ h (Finset.map_subset_map.mpr (Finset.map_subset_map.mpr h)),
      a.β_symm_incl]

@[simp] theorem id_β_apply (Λ : Finset sites) (x : N.algebra Λ) :
    (Symmetry.id N).β Λ x =
      N.algebraCongr (show Λ = Λ.map (Equiv.refl sites).toEmbedding by simp) x :=
  rfl

@[simp] theorem comp_β_apply (a b : N.Symmetry) (Λ : Finset sites) (x : N.algebra Λ) :
    (a.comp b).β Λ x = N.algebraCongr (show (Λ.map b.σ.toEmbedding).map a.σ.toEmbedding
        = Λ.map (b.σ.trans a.σ).toEmbedding by simp [Finset.map_map, Equiv.trans_toEmbedding])
      (a.β (Λ.map b.σ.toEmbedding) (b.β Λ x)) :=
  rfl

@[simp] theorem inv_β_apply (a : N.Symmetry) (Λ : Finset sites) (x : N.algebra Λ) :
    (Symmetry.inv a).β Λ x = (a.β (Λ.map a.σ.symm.toEmbedding)).symm
      (N.algebraCongr (show (Λ.map a.σ.symm.toEmbedding).map a.σ.toEmbedding = Λ by
        simp [Finset.map_map]).symm x) :=
  rfl

@[simp] theorem region_id (Λ : Finset sites) : (Symmetry.id N).region Λ = Λ := by
  simp [region, Symmetry.id]

@[simp] theorem region_comp (a b : N.Symmetry) (Λ : Finset sites) :
    (a.comp b).region Λ = a.region (b.region Λ) := by
  simp [region, Symmetry.comp, Finset.map_map, Equiv.trans_toEmbedding]

/-- The covariance action of the identity symmetry is the identity: `β_{id} = id`. -/
@[simp] theorem quasiLocalRelabel_id :
    (Symmetry.id N).quasiLocalRelabel = RingHom.id N.quasiLocalAlgebra := by
  refine RingHom.ext fun z => ?_
  induction z using DirectLimit.induction with
  | _ Λ X => rw [quasiLocalRelabel_mk, RingHom.id_apply]; exact N.ιLocal_algebraCongr _ X

/-- **Functoriality of the covariance action**: composing symmetries composes their actions,
    `β_{a∘b} = β_a ∘ β_b`. With `quasiLocalRelabel_id` this exhibits `a ↦ β_a` as a functorial
    (monoid-homomorphic) assignment, so a group acting on the net acts on the algebra of local
    observables by `*`-endomorphisms. -/
@[simp] theorem quasiLocalRelabel_comp (a b : N.Symmetry) :
    (a.comp b).quasiLocalRelabel = a.quasiLocalRelabel.comp b.quasiLocalRelabel := by
  refine RingHom.ext fun z => ?_
  induction z using DirectLimit.induction with
  | _ Λ X =>
    simp only [RingHom.comp_apply, quasiLocalRelabel_mk]
    exact N.ιLocal_algebraCongr _ _

theorem id_comp (a : N.Symmetry) : (Symmetry.id N).comp a = a := by
  refine Symmetry.ext ?_ fun Λ x e => ?_
  · simp [Symmetry.comp, Symmetry.id]
  · rw [algebraCongr_eq_iff]
    simp only [comp_β_apply, id_β_apply]
    erw [algebraCongr_trans]
    rfl

theorem comp_id (a : N.Symmetry) : a.comp (Symmetry.id N) = a := by
  refine Symmetry.ext ?_ fun Λ x e => ?_
  · simp [Symmetry.comp, Symmetry.id]
  · rw [algebraCongr_eq_iff]
    simp only [comp_β_apply, id_β_apply]
    erw [a.β_algebraCongr, algebraCongr_trans]
    rfl

theorem comp_assoc (a b c : N.Symmetry) : (a.comp b).comp c = a.comp (b.comp c) := by
  refine Symmetry.ext ?_ fun Λ x e => ?_
  · simp [Symmetry.comp, Equiv.trans_assoc]
  · rw [algebraCongr_eq_iff]
    simp only [comp_β_apply]
    erw [a.β_algebraCongr, algebraCongr_trans, algebraCongr_trans, algebraCongr_trans]
    rfl

theorem inv_comp (a : N.Symmetry) : (Symmetry.inv a).comp a = Symmetry.id N := by
  refine Symmetry.ext ?_ fun Λ x e => ?_
  · simp [Symmetry.comp, Symmetry.inv, Symmetry.id, Equiv.self_trans_symm]
  · rw [algebraCongr_eq_iff]
    simp only [comp_β_apply, inv_β_apply, id_β_apply]
    erw [← a.β_algebraCongr, StarAlgEquiv.symm_apply_apply, algebraCongr_trans,
      algebraCongr_trans]
    · rfl
    · simp [Finset.map_map]

/-- The symmetries of a local net form a **group** under composition, with `Symmetry.id` the unit
    and `Symmetry.inv` the inverse. A covariant action of a group `G` on the net is then a
    homomorphism `G →* N.Symmetry`. -/
noncomputable instance : Group N.Symmetry where
  mul a b := a.comp b
  one := Symmetry.id N
  inv a := a.inv
  mul_assoc := Symmetry.comp_assoc
  one_mul := Symmetry.id_comp
  mul_one := Symmetry.comp_id
  inv_mul_cancel := Symmetry.inv_comp

/-- The group multiplication is composition of symmetries. -/
theorem mul_def (a b : N.Symmetry) : a * b = a.comp b := rfl

/-- The group unit is the identity symmetry. -/
theorem one_def : (1 : N.Symmetry) = Symmetry.id N := rfl

/-- The group inverse is the inverse symmetry. -/
theorem inv_def (a : N.Symmetry) : a⁻¹ = a.inv := rfl

/-- The covariance action sends the unit symmetry to the identity: `β_1 = id`. -/
@[simp] theorem quasiLocalRelabel_one :
    (1 : N.Symmetry).quasiLocalRelabel = RingHom.id N.quasiLocalAlgebra := by
  rw [one_def, quasiLocalRelabel_id]

/-- The covariance action is multiplicative: `β_{a·b} = β_a ∘ β_b`. With `quasiLocalRelabel_one`
    this exhibits `a ↦ β_a` as a monoid homomorphism from the symmetry group into the
    `*`-endomorphisms of the algebra of local observables. -/
theorem quasiLocalRelabel_mul (a b : N.Symmetry) :
    (a * b).quasiLocalRelabel = a.quasiLocalRelabel.comp b.quasiLocalRelabel := by
  rw [mul_def, quasiLocalRelabel_comp]

/-! #### The covariance action as a `*`-automorphism

The ring endomorphism `quasiLocalRelabel` is in fact `ℂ`-linear and `*`-preserving, since each
covariance isomorphism `β` is a `*`-isomorphism. Recording this upgrades the action to a genuine
`*`-algebra automorphism `≃⋆ₐ[ℂ]` and the assignment to a group homomorphism into the
`*`-automorphism group — the AQFT covariance action on the algebra of local observables. -/

/-- The covariance action is `ℂ`-linear: `β_a (c • z) = c • β_a z`, since each `β` is. -/
theorem quasiLocalRelabel_smul (c : ℂ) (z : N.quasiLocalAlgebra) :
    a.quasiLocalRelabel (c • z) = c • a.quasiLocalRelabel z := by
  induction z using DirectLimit.induction with
  | _ Λ X =>
    rw [DirectLimit.smul_def, quasiLocalRelabel_mk, quasiLocalRelabel_mk, DirectLimit.smul_def,
      map_smul]
    rfl

/-- The covariance action preserves the involution: `β_a (star z) = star (β_a z)`, since each `β`
    is a `*`-isomorphism. -/
theorem quasiLocalRelabel_star (z : N.quasiLocalAlgebra) :
    a.quasiLocalRelabel (star z) = star (a.quasiLocalRelabel z) := by
  induction z using DirectLimit.induction with
  | _ Λ X =>
    rw [star_mk, quasiLocalRelabel_mk, quasiLocalRelabel_mk, star_mk, map_star]
    rfl

/-- The **covariance action** of a symmetry as a `*`-algebra automorphism `𝔄_loc ≃⋆ₐ[ℂ] 𝔄_loc` of
    the algebra of local observables, with the action of the inverse symmetry `a⁻¹` as its inverse.
    This is the AQFT covariance automorphism at the level of the (incomplete) algebra of local
    observables; its continuous extension to the quasi-local C⋆-algebra is `quasiLocalCStarRelabel`
    (for a faithful net). -/
noncomputable def quasiLocalRelabelStarEquiv :
    N.quasiLocalAlgebra ≃⋆ₐ[ℂ] N.quasiLocalAlgebra where
  toFun := a.quasiLocalRelabel
  invFun := a⁻¹.quasiLocalRelabel
  left_inv z := by
    rw [← RingHom.comp_apply, ← quasiLocalRelabel_mul, inv_mul_cancel, quasiLocalRelabel_one,
      RingHom.id_apply]
  right_inv z := by
    rw [← RingHom.comp_apply, ← quasiLocalRelabel_mul, mul_inv_cancel, quasiLocalRelabel_one,
      RingHom.id_apply]
  map_mul' := map_mul a.quasiLocalRelabel
  map_add' := map_add a.quasiLocalRelabel
  map_smul' := a.quasiLocalRelabel_smul
  map_star' := a.quasiLocalRelabel_star

@[simp] theorem quasiLocalRelabelStarEquiv_apply (z : N.quasiLocalAlgebra) :
    a.quasiLocalRelabelStarEquiv z = a.quasiLocalRelabel z := rfl

@[simp] theorem quasiLocalRelabelStarEquiv_symm_apply (z : N.quasiLocalAlgebra) :
    a.quasiLocalRelabelStarEquiv.symm z = a⁻¹.quasiLocalRelabel z := rfl

/-- A symmetry of the net acts on the algebra of local observables by `*`-algebra automorphisms,
    assembled as a **group homomorphism** into the `*`-automorphism group `𝔄_loc ≃⋆ₐ[ℂ] 𝔄_loc`.
    This is the covariance action of the symmetry group, upgrading the monoid-homomorphic
    endomorphism action (`quasiLocalRelabel_one`/`quasiLocalRelabel_mul`) to a group action by
    automorphisms that tracks the `ℂ`-linear and `*`-structure. -/
noncomputable def quasiLocalRelabelStarHom :
    N.Symmetry →* (N.quasiLocalAlgebra ≃⋆ₐ[ℂ] N.quasiLocalAlgebra) where
  toFun a := a.quasiLocalRelabelStarEquiv
  map_one' := by
    ext z
    simp only [quasiLocalRelabelStarEquiv_apply, quasiLocalRelabel_one, RingHom.id_apply,
      StarAlgEquiv.one_apply]
  map_mul' a b := by
    ext z
    simp only [quasiLocalRelabelStarEquiv_apply, quasiLocalRelabel_mul, RingHom.comp_apply,
      StarAlgEquiv.mul_apply]

@[simp] theorem quasiLocalRelabelStarHom_apply (z : N.quasiLocalAlgebra) :
    quasiLocalRelabelStarHom a z = a.quasiLocalRelabel z := rfl

/-! #### The covariance automorphism of the quasi-local C⋆-algebra

For a **faithful** net the covariance action is *isometric* — each `β` is a `*`-isomorphism of
C⋆-algebras, hence norm-preserving (`StarAlgEquiv.norm_map`) — so `quasiLocalRelabelStarEquiv` is
uniformly continuous and extends, by the functoriality of completion (`mapStarAlgEquiv`), to a
`*`-automorphism of the quasi-local C⋆-algebra `𝔄`. This is the genuine AQFT covariance
automorphism on `𝔄`, and the assignment is a group homomorphism. -/

section CStarCovariance

variable [N.Faithful]

/-- The covariance action is **isometric** on the algebra of local observables: each `β` is a
    `*`-isomorphism of C⋆-algebras, hence norm-preserving. -/
theorem quasiLocalRelabel_norm (z : N.quasiLocalAlgebra) :
    ‖a.quasiLocalRelabel z‖ = ‖z‖ := by
  induction z using DirectLimit.induction with
  | _ Λ X =>
    rw [quasiLocalRelabel_mk, norm_mk, norm_mk]
    exact StarAlgEquiv.norm_map _ X

/-- The covariance automorphism of the algebra of local observables is uniformly continuous (it is
    an isometry), so it extends to the C⋆-completion. -/
theorem quasiLocalRelabelStarEquiv_uniformContinuous :
    UniformContinuous a.quasiLocalRelabelStarEquiv :=
  (AddMonoidHomClass.isometry_of_norm _ (fun z => by
    rw [quasiLocalRelabelStarEquiv_apply]; exact a.quasiLocalRelabel_norm z)).uniformContinuous

/-- The inverse covariance automorphism is uniformly continuous as well (the action of `a⁻¹` is
    also an isometry). -/
theorem quasiLocalRelabelStarEquiv_symm_uniformContinuous :
    UniformContinuous a.quasiLocalRelabelStarEquiv.symm := by
  have h : ∀ z, ‖a.quasiLocalRelabelStarEquiv.symm z‖ = ‖z‖ := fun z => by
    rw [quasiLocalRelabelStarEquiv_symm_apply]; exact a⁻¹.quasiLocalRelabel_norm z
  exact (AddMonoidHomClass.isometry_of_norm _ h).uniformContinuous

/-- The **covariance automorphism of the quasi-local C⋆-algebra** `𝔄 ≃⋆ₐ[ℂ] 𝔄`: the continuous
    extension of `quasiLocalRelabelStarEquiv` to the completion. This is the AQFT covariant
    `*`-automorphism on the quasi-local C⋆-algebra of a faithful net (Naaijkens 2012 §3.2,
    Bratteli–Robinson Vol.2 §6.2). -/
noncomputable def quasiLocalCStarRelabel :
    N.quasiLocalCStarAlgebra ≃⋆ₐ[ℂ] N.quasiLocalCStarAlgebra :=
  UniformSpace.Completion.mapStarAlgEquiv a.quasiLocalRelabelStarEquiv
    a.quasiLocalRelabelStarEquiv_uniformContinuous
    a.quasiLocalRelabelStarEquiv_symm_uniformContinuous

@[simp] theorem quasiLocalCStarRelabel_coe (z : N.quasiLocalAlgebra) :
    a.quasiLocalCStarRelabel (↑z : N.quasiLocalCStarAlgebra) = ↑(a.quasiLocalRelabel z) :=
  UniformSpace.Completion.mapStarAlgEquiv_coe _ _ _ z

theorem quasiLocalCStarRelabel_continuous :
    Continuous (⇑a.quasiLocalCStarRelabel) :=
  UniformSpace.Completion.continuous_map

/-- A symmetry of a faithful net acts on the quasi-local C⋆-algebra by `*`-automorphisms,
    assembled as a **group homomorphism** into the `*`-automorphism group `𝔄 ≃⋆ₐ[ℂ] 𝔄`. This is the
    covariance action of the symmetry group on the quasi-local C⋆-algebra — the AQFT covariant
    automorphic action. -/
noncomputable def quasiLocalCStarRelabelHom :
    N.Symmetry →* (N.quasiLocalCStarAlgebra ≃⋆ₐ[ℂ] N.quasiLocalCStarAlgebra) where
  toFun a := a.quasiLocalCStarRelabel
  map_one' := by
    refine StarAlgEquiv.ext fun z => ?_
    rw [StarAlgEquiv.one_apply]
    refine UniformSpace.Completion.induction_on z
      (isClosed_eq (1 : N.Symmetry).quasiLocalCStarRelabel_continuous continuous_id) ?_
    intro w
    simp only [quasiLocalCStarRelabel_coe, quasiLocalRelabel_one, RingHom.id_apply]
  map_mul' a b := by
    refine StarAlgEquiv.ext fun z => ?_
    rw [StarAlgEquiv.mul_apply]
    refine UniformSpace.Completion.induction_on z
      (isClosed_eq (a * b).quasiLocalCStarRelabel_continuous
        (a.quasiLocalCStarRelabel_continuous.comp b.quasiLocalCStarRelabel_continuous)) ?_
    intro w
    simp only [quasiLocalCStarRelabel_coe, quasiLocalRelabel_mul, RingHom.comp_apply]

@[simp] theorem quasiLocalCStarRelabelHom_apply
    (z : N.quasiLocalCStarAlgebra) :
    quasiLocalCStarRelabelHom a z = a.quasiLocalCStarRelabel z := rfl

end CStarCovariance

end Symmetry

end LocalNet
