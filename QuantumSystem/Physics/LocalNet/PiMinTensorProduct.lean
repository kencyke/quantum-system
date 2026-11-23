/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.CStarAlgebra.TensorProduct.InfiniteMinimal
public import QuantumSystem.Physics.LocalNet.Automorphism.SitePerm
public import QuantumSystem.Physics.LocalNet.Subnet

/-!
# The net of minimal tensor products of a family of C⋆-algebras

For a family `A` of unital C⋆-algebras indexed by a type of sites, the net
`GradedLocalNet.piMinTensorProduct` assigns to a finite region `Λ` the minimal tensor product `⨂ₘᵢₙ x : Λ, A x` of
the algebras over its sites, with the isotony embeddings `z ↦ z ⊗ 1` (`PiMinTensorProduct.extend`).
It is a local net: elements over disjoint regions commute once embedded in a common one
(`PiMinTensorProduct.commute_extend_of_disjoint`). When every `A x` is nontrivial its embeddings are
isometric (`PiMinTensorProduct.norm_extend`), so it is faithful. For `A x` the algebra of a single
spin at every site it is the net of a quantum spin system on the sites.

A family `g` of `*`-automorphisms `g x` of the `A x` acts site by site, by `⨂ g x` on each local
algebra (`PiMinTensorProduct.congr`): the **on-site action** of `g`, an automorphism leaving every
region in place. The family may depend on the site; a C⋆-dynamical system on a single algebra acts
at every site through `ContinuousMonoidHom.constOnSite`. The on-site action is continuous from the product of the
point-norm topologies (`GradedLocalNet.continuous_quasiLocalCStarAutomorphismHom_onSiteAutomorphism`): on a
local observable of `Λ` it depends only on the `g x` for `x ∈ Λ`, through
`PiMinTensorProduct.continuous_congr`. So a C⋆-dynamical system `ψ : G →ₜ* (Π x, A x ≃⋆ₐ[ℂ] A x)`
acts on the quasi-local C⋆-algebra of nontrivial algebras as a C⋆-dynamical system
(`GradedLocalNet.onSiteDynamicalSystem`).

On copies of one algebra `B`, a permutation `σ` of the sites (a translation, a reflection) is an
automorphism that moves the regions, `Λ ↦ σ Λ`, and the local algebras along `σ`
(`PiMinTensorProduct.reindex`), compatibly with the isotony embeddings
(`GradedLocalNet.sitePermAutomorphism`).

## Main definitions

* `GradedLocalNet.piMinTensorProduct sites A` — the net of minimal tensor products of `A` over the
  finite regions of `sites`.
* `GradedLocalNet.onSiteAutomorphism g` — the on-site action of a family `g` of `*`-automorphisms, as an
  automorphism; `GradedLocalNet.onSiteAutomorphismHom sites A` — as a homomorphism into the automorphisms.
* `GradedLocalNet.sitePermAutomorphism B σ` — the automorphism of a permutation `σ` of the sites on the
  net of minimal tensor products of copies of `B`, moving the regions.
* `GradedLocalNet.onSiteDynamicalSystem sites ψ` — the C⋆-dynamical system on the quasi-local C⋆-algebra of
  a C⋆-dynamical system `ψ` acting site by site.

## Main results

* **`GradedLocalNet.continuous_quasiLocalCStarAutomorphismHom_onSiteAutomorphism`** — the on-site action is
  continuous on the quasi-local C⋆-algebra.
* The local algebras of the net of minimal tensor products of finite-dimensional factors are
  finite-dimensional factors (the `Algebra.IsCentral` instance on
  `(piMinTensorProduct sites A).algebra Λ`).
-/

@[expose] public section

open scoped TensorProduct PiMinTensorProduct

universe u

/-! The constant family of a C⋆-dynamical system and the restriction of a permutation to a finite
set involve no net; they are stated in the namespaces of their types. -/

namespace ContinuousMonoidHom

variable {G : Type*} [Monoid G] [TopologicalSpace G]

variable (sites : Type*) in
/-- A C⋆-dynamical system on one C⋆-algebra `B`, as the constant family over `sites`: the same
`*`-automorphism at every site. -/
noncomputable def constOnSite {B : Type*} [CStarAlgebra B] (ψ : G →ₜ* (B ≃⋆ₐ[ℂ] B)) :
    G →ₜ* (sites → B ≃⋆ₐ[ℂ] B) :=
  ⟨(Pi.constMonoidHom sites _).comp ψ.toMonoidHom, continuous_pi fun _ => ψ.continuous⟩

/-- The constant on-site system acts by `ψ g` at every site. -/
@[simp] lemma constOnSite_apply {sites B : Type*} [CStarAlgebra B] (ψ : G →ₜ* (B ≃⋆ₐ[ℂ] B))
    (g : G) (x : sites) : constOnSite sites ψ g x = ψ g :=
  rfl

end ContinuousMonoidHom

namespace Equiv

/-- A permutation `σ` of the sites, restricted to a finite set `Λ`: the bijection of `Λ` onto its
image `Λ.map σ`. -/
def restrictFinsetMap {sites : Type*} (σ : sites ≃ sites) (Λ : Finset sites) :
    Λ ≃ Λ.map σ.toEmbedding :=
  σ.subtypeEquiv fun _ => (Finset.mem_map' σ.toEmbedding).symm

end Equiv

namespace PiMinTensorProduct

/-- Moving the sites along `σ` commutes with the isotony embeddings `z ↦ z ⊗ 1`. -/
lemma reindex_extend_restrictFinsetMap {sites : Type*} [DecidableEq sites] {B : Type u}
    [CStarAlgebra B] (σ : sites ≃ sites) {Λ Λ' : Finset sites} (h : Λ ⊆ Λ')
    (z : ⨂ₘᵢₙ _ : Λ, B) :
    PiMinTensorProduct.reindex (fun _ : Λ' => B) (Equiv.restrictFinsetMap σ Λ')
        (PiMinTensorProduct.extend (A := fun _ : sites => B) h z) =
      PiMinTensorProduct.extend (A := fun _ : sites => B) (Finset.map_subset_map.mpr h)
        (PiMinTensorProduct.reindex (fun _ : Λ => B) (Equiv.restrictFinsetMap σ Λ) z) := by
  induction z using PiMinTensorProduct.denseRange_of.induction_on with
  | hp =>
    exact isClosed_eq ((map_continuous _).comp (map_continuous _))
      ((map_continuous _).comp (map_continuous _))
  | ih x =>
    rw [PiMinTensorProduct.extend_of, PiMinTensorProduct.reindex_of,
      PiMinTensorProduct.reindex_of, PiMinTensorProduct.extend_of]
    congr 1
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r a =>
      simp only [map_smul, PiTensorProduct.extendAlgHom_tprod,
        PiTensorProduct.reindexStarAlgEquiv_tprod]
      congr 2
      funext k
      by_cases hk : σ.symm k ∈ Λ
      · simp [PiTensorProduct.extendFun, Equiv.restrictFinsetMap, hk]
        rfl
      · simp [PiTensorProduct.extendFun, Equiv.restrictFinsetMap, hk]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

end PiMinTensorProduct

namespace GradedLocalNet

variable (sites : Type*) [DecidableEq sites] (A : sites → Type u) [∀ x, CStarAlgebra (A x)]

/-- The **net of minimal tensor products** of a family `A` of unital C⋆-algebras over the finite
regions of `sites`: the local algebra of `Λ` is the minimal tensor product `⨂ₘᵢₙ x : Λ, A x`, the isotony
embeddings are `z ↦ z ⊗ 1`, and elements over disjoint regions commute. -/
noncomputable def piMinTensorProduct : GradedLocalNet (Finset sites) :=
  ofLocality
    { algebra := fun Λ => ⨂ₘᵢₙ x : Λ, A x
      incl := fun h => PiMinTensorProduct.extend (A := A) h
      incl_refl := fun x => (PiMinTensorProduct.directedSystem (A := A)).map_self x
      incl_trans := fun h₁₂ h₂₃ x =>
        (PiMinTensorProduct.directedSystem (A := A)).map_map h₁₂ h₂₃ x }
    fun _ _ _ h₁ h₂ hd x y => PiMinTensorProduct.commute_extend_of_disjoint (A := A) h₁ h₂ hd x y

/-- The net of minimal tensor products is local: elements over disjoint regions commute. -/
instance : (piMinTensorProduct sites A).IsTriviallyGraded :=
  instIsTriviallyGradedOfLocality _ _

/-- The local algebra of a region `Λ` is the minimal tensor product of the `A x` over `Λ`. -/
lemma piMinTensorProduct_algebra (Λ : Finset sites) : (piMinTensorProduct sites A).algebra Λ = ⨂ₘᵢₙ x : Λ, A x :=
  rfl

/-- The net of minimal tensor products of nontrivial algebras is faithful: its embeddings
`z ↦ z ⊗ 1` are isometric. -/
instance [∀ x, Nontrivial (A x)] : (piMinTensorProduct sites A).Faithful where
  incl_injective h := (AddMonoidHomClass.isometry_of_norm (PiMinTensorProduct.extend (A := A) h)
    (PiMinTensorProduct.norm_extend (A := A) h)).injective

/-- The local algebras of the net of minimal tensor products of nontrivial algebras are nontrivial. -/
instance [∀ x, Nontrivial (A x)] (Λ : Finset sites) : Nontrivial ((piMinTensorProduct sites A).algebra Λ) :=
  inferInstanceAs (Nontrivial (⨂ₘᵢₙ x : Λ, A x))

/-- The local algebras of the net of minimal tensor products of finite-dimensional algebras are
finite-dimensional. -/
instance [∀ x, FiniteDimensional ℂ (A x)] (Λ : Finset sites) :
    FiniteDimensional ℂ ((piMinTensorProduct sites A).algebra Λ) :=
  inferInstanceAs (FiniteDimensional ℂ (⨂ₘᵢₙ x : Λ, A x))

/-- The local algebras of the net of minimal tensor products of finite-dimensional factors are
factors (`PiMinTensorProduct.isCentral`). -/
instance [∀ x, FiniteDimensional ℂ (A x)] [∀ x, Algebra.IsCentral ℂ (A x)] (Λ : Finset sites) :
    Algebra.IsCentral ℂ ((piMinTensorProduct sites A).algebra Λ) :=
  inferInstanceAs (Algebra.IsCentral ℂ (⨂ₘᵢₙ x : Λ, A x))

variable {sites A}

/-- The **on-site action** of a family `g` of `*`-automorphisms of the `A x`: the automorphism of the
net of minimal tensor products that leaves every region in place and acts by `⨂ g x` on each local
algebra. -/
noncomputable def onSiteAutomorphism (g : Π x, A x ≃⋆ₐ[ℂ] A x) :
    (piMinTensorProduct sites A).Automorphism where
  σ := OrderIso.refl _
  map_orthogonal_iff _ _ := Iff.rfl
  β Λ := PiMinTensorProduct.congr fun x : Λ => g x
  β_incl h z := (PiMinTensorProduct.extend_congr h g z).symm
  β_parity _ x := (piMinTensorProduct sites A).map_parity _ x

/-- The on-site action of `g` is `⨂ g x` on each local algebra. -/
lemma onSiteAutomorphism_β (g : Π x, A x ≃⋆ₐ[ℂ] A x) (Λ : Finset sites)
    (z : (piMinTensorProduct sites A).algebra Λ) :
    (onSiteAutomorphism g).β Λ z = PiMinTensorProduct.congr (fun x : Λ => g x) z :=
  rfl

variable (sites A) in
/-- The families of `*`-automorphisms of the `A x` act on the net of minimal tensor products site by
site, by internal automorphisms: a group of internal symmetries. -/
noncomputable def onSiteSymmetry :
    (Π x, A x ≃⋆ₐ[ℂ] A x) →* Automorphism.internal (piMinTensorProduct sites A) where
  toFun g := ⟨onSiteAutomorphism g, rfl⟩
  map_one' := Subtype.ext <| Automorphism.ext rfl fun Λ z e =>
    ((piMinTensorProduct sites A).algebraCongr_self e _).trans
      (PiMinTensorProduct.congr_refl_apply (A := fun x : Λ => A x) z)
  map_mul' g f := Subtype.ext <| Automorphism.ext rfl fun Λ z e =>
    ((piMinTensorProduct sites A).algebraCongr_self e _).trans
      (PiMinTensorProduct.congr_congr (fun x : Λ => g x) (fun x : Λ => f x) z).symm

variable (sites A) in
/-- The families of `*`-automorphisms act on the net of minimal tensor products by their on-site
actions. -/
noncomputable def onSiteAutomorphismHom :
    (Π x, A x ≃⋆ₐ[ℂ] A x) →* (piMinTensorProduct sites A).Automorphism :=
  (Automorphism.internal _).subtype.comp (onSiteSymmetry sites A)

variable [∀ x, Nontrivial (A x)]

/-- **The on-site action is continuous**, for nontrivial `A x`, from the product of the point-norm
topologies of the `A x ≃⋆ₐ[ℂ] A x` to the point-norm topology of the `*`-automorphisms of the
quasi-local C⋆-algebra: on a local observable `z` of `Λ` it is `g ↦ ι_Λ ((⨂ g x) z)`, continuous by
`PiMinTensorProduct.continuous_congr`. -/
theorem continuous_quasiLocalCStarAutomorphismHom_onSiteAutomorphism :
    Continuous fun g : Π x, A x ≃⋆ₐ[ℂ] A x =>
      GradedLocalNet.Automorphism.quasiLocalCStarAutomorphismHom (onSiteAutomorphism (sites := sites) g) :=
  GradedLocalNet.Automorphism.continuous_quasiLocalCStarAutomorphismHom_comp_iff.mpr fun Λ z =>
    ((piMinTensorProduct sites A).isometry_ιLocalCStar Λ).continuous.comp
      ((continuous_eval_const z).comp
        ((PiMinTensorProduct.continuous_congr (A := fun x : Λ => A x) (B := fun x : Λ => A x)).comp
          (continuous_pi fun x => continuous_apply (x : sites))))

variable {G : Type*} [Monoid G] [TopologicalSpace G]

variable (sites) in
/-- **A C⋆-dynamical system acting site by site acts on the quasi-local C⋆-algebra of the net of
minimal tensor products** of nontrivial algebras as a C⋆-dynamical system, by its on-site actions. -/
noncomputable def onSiteDynamicalSystem (ψ : G →ₜ* (Π x, A x ≃⋆ₐ[ℂ] A x)) :
    G →ₜ* ((piMinTensorProduct sites A).quasiLocalCStarAlgebra ≃⋆ₐ[ℂ]
      (piMinTensorProduct sites A).quasiLocalCStarAlgebra) :=
  GradedLocalNet.Automorphism.quasiLocalCStarDynamicalSystem
    ((onSiteAutomorphismHom sites A).comp ψ.toMonoidHom)
    ((continuous_quasiLocalCStarAutomorphismHom_onSiteAutomorphism (sites := sites) (A := A)).comp
      ψ.continuous :)

/-- On a local observable the on-site dynamical system acts by `⨂ ψ g x`. -/
@[simp] lemma onSiteDynamicalSystem_ιLocalCStar (ψ : G →ₜ* (Π x, A x ≃⋆ₐ[ℂ] A x)) (g : G)
    (Λ : Finset sites) (z : (piMinTensorProduct sites A).algebra Λ) :
    onSiteDynamicalSystem sites ψ g ((piMinTensorProduct sites A).ιLocalCStar Λ z) =
      (piMinTensorProduct sites A).ιLocalCStar Λ (PiMinTensorProduct.congr (fun x : Λ => ψ g x) z) := by
  exact GradedLocalNet.Automorphism.quasiLocalCStarAutomorphismEquiv_ιLocalCStar
    (onSiteAutomorphism (ψ g)) Λ z

/-- On an elementary tensor `⨂ aₓ` the on-site dynamical system acts site by site:
`⨂ aₓ ↦ ⨂ ψ g x aₓ`. -/
lemma onSiteDynamicalSystem_ιLocalCStar_of_tprod (ψ : G →ₜ* (Π x, A x ≃⋆ₐ[ℂ] A x)) (g : G)
    (Λ : Finset sites) (a : Π x : Λ, A x) :
    onSiteDynamicalSystem sites ψ g
        ((piMinTensorProduct sites A).ιLocalCStar Λ (PiMinTensorProduct.of (fun x : Λ => A x) (⨂ₜ[ℂ] x, a x))) =
      (piMinTensorProduct sites A).ιLocalCStar Λ
        (PiMinTensorProduct.of (fun x : Λ => A x) (⨂ₜ[ℂ] x, ψ g x (a x))) := by
  refine (onSiteDynamicalSystem_ιLocalCStar ψ g Λ _).trans (congrArg _ ?_)
  rw [PiMinTensorProduct.congr_of, PiTensorProduct.mapStarAlgHom_tprod]
  rfl

/-- A local observable is fixed by the on-site dynamical system at `g` iff it is fixed by
`⨂ ψ g x`. -/
lemma onSiteDynamicalSystem_ιLocalCStar_eq_iff (ψ : G →ₜ* (Π x, A x ≃⋆ₐ[ℂ] A x)) (g : G)
    (Λ : Finset sites) (z : ⨂ₘᵢₙ x : Λ, A x) :
    onSiteDynamicalSystem sites ψ g ((piMinTensorProduct sites A).ιLocalCStar Λ z) =
        (piMinTensorProduct sites A).ιLocalCStar Λ z ↔
      PiMinTensorProduct.congr (A := fun x : Λ => A x) (B := fun x : Λ => A x)
        (fun x => ψ g x) z = z := by
  exact (Eq.congr_left (onSiteDynamicalSystem_ιLocalCStar ψ g Λ z)).trans
    ((piMinTensorProduct sites A).ιLocalCStar_injective Λ).eq_iff

/-! ### Automorphism under permutations of the sites -/

section SitePerm

variable {B : Type u} [CStarAlgebra B]

variable (B) in
/-- **The automorphism of a permutation of the sites** on the net of minimal tensor products of
copies of `B` (a translation or a reflection of a lattice): it moves every region `Λ` to `σ Λ` and its local
algebra along `σ` (`PiMinTensorProduct.reindex`). -/
noncomputable def sitePermAutomorphism (σ : sites ≃ sites) :
    (piMinTensorProduct sites fun _ => B).Automorphism :=
  GradedLocalNet.Automorphism.ofSitePerm σ
    (fun Λ => PiMinTensorProduct.reindex (fun _ : Λ => B) (Equiv.restrictFinsetMap σ Λ))
    (fun h z => PiMinTensorProduct.reindex_extend_restrictFinsetMap σ h z)
    fun _ _ => (piMinTensorProduct sites _).map_parity _ _

/-- The automorphism of `σ` moves the elementary tensor `⨂ aₓ` over `Λ` to `⨂ a_{σ⁻¹ y}` over
`σ Λ`. -/
lemma sitePermAutomorphism_β_of_tprod (σ : sites ≃ sites) (Λ : Finset sites) (a : Λ → B) :
    (sitePermAutomorphism B σ).β Λ (PiMinTensorProduct.of (fun _ : Λ => B) (⨂ₜ[ℂ] x, a x)) =
      PiMinTensorProduct.of (fun _ : Λ.map σ.toEmbedding => B)
        (⨂ₜ[ℂ] y, a ((Equiv.restrictFinsetMap σ Λ).symm y)) :=
  (PiMinTensorProduct.reindex_of _ _).trans
    (congrArg _ (PiTensorProduct.reindexStarAlgEquiv_tprod _ a))

end SitePerm

end GradedLocalNet
