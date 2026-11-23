/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.CStarAlgebra.TensorProduct.InfiniteMinimal
public import QuantumSystem.Physics.LocalNet.Covariance.SitePerm
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

A family `g` of ⋆-automorphisms `g x` of the `A x` acts site by site, by `⨂ g x` on each local
algebra (`PiMinTensorProduct.congr`): the **on-site action** of `g`, a covariance leaving every
region in place. The family may depend on the site; a C⋆-dynamical system on a single algebra acts
at every site through `GradedLocalNet.constOnSite`. The on-site action is continuous from the product of the
point-norm topologies (`GradedLocalNet.continuous_quasiLocalCStarCovarianceHom_onSiteCovariance`): on a
local observable of `Λ` it depends only on the `g x` for `x ∈ Λ`, through
`PiMinTensorProduct.continuous_congr`. So a C⋆-dynamical system `ψ : G →ₜ* (Π x, A x ≃⋆ₐ[ℂ] A x)`
acts on the quasi-local C⋆-algebra of nontrivial algebras as a C⋆-dynamical system
(`GradedLocalNet.onSiteDynamicalSystem`).

On copies of one algebra `B`, a permutation `σ` of the sites (a translation, a reflection) is a
covariance that moves the regions, `Λ ↦ σ Λ`, and the local algebras along `σ`
(`PiMinTensorProduct.reindex`), compatibly with the isotony embeddings
(`GradedLocalNet.sitePermCovariance`).

## Main definitions

* `GradedLocalNet.piMinTensorProduct sites A` — the net of minimal tensor products of `A` over the
  finite regions of `sites`.
* `GradedLocalNet.onSiteCovariance g` — the on-site action of a family `g` of ⋆-automorphisms, as a
  covariance; `GradedLocalNet.onSiteCovarianceHom sites A` — as a homomorphism into the covariances.
* `GradedLocalNet.sitePermCovariance B σ` — the covariance of a permutation `σ` of the sites on the
  net of minimal tensor products of copies of `B`, moving the regions.
* `GradedLocalNet.onSiteDynamicalSystem sites ψ` — the C⋆-dynamical system on the quasi-local C⋆-algebra of
  a C⋆-dynamical system `ψ` acting site by site.

## Main results

* `GradedLocalNet.continuous_quasiLocalCStarCovarianceHom_onSiteCovariance` — the on-site action is
  continuous on the quasi-local C⋆-algebra.
* The local algebras of the net of minimal tensor products of finite-dimensional factors are
  finite-dimensional factors (the `Algebra.IsCentral` instance on
  `(piMinTensorProduct sites A).algebra Λ`).
-/

@[expose] public section

open scoped TensorProduct PiMinTensorProduct

universe u

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
instance : (piMinTensorProduct sites A).IsLocal :=
  instIsLocalOfLocality _ _

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

variable (sites A) in
/-- The families of ⋆-automorphisms of the `A x` act on the net of minimal tensor products site by
site, by `⨂ g x` on each local algebra: an internal symmetry. -/
noncomputable def onSiteSymmetry :
    (piMinTensorProduct sites A).InternalSymmetry (Π x, A x ≃⋆ₐ[ℂ] A x) where
  act Λ :=
    { toFun g := PiMinTensorProduct.congr fun x : Λ => g x
      map_one' := StarAlgEquiv.ext fun z => PiMinTensorProduct.congr_refl_apply (A := fun x : Λ => A x) z
      map_mul' g f := StarAlgEquiv.ext fun z =>
        (PiMinTensorProduct.congr_congr (fun x : Λ => g x) (fun x : Λ => f x) z).symm }
  act_incl h g z := (PiMinTensorProduct.extend_congr h g z).symm

/-- The **on-site action** of a family `g` of ⋆-automorphisms of the `A x`: the covariance of the
net of minimal tensor products that leaves every region in place and acts by `⨂ g x` on each local algebra. -/
noncomputable def onSiteCovariance (g : Π x, A x ≃⋆ₐ[ℂ] A x) : (piMinTensorProduct sites A).Covariance :=
  (onSiteSymmetry sites A).toCovariance (fun _ _ x => (piMinTensorProduct sites A).map_parity _ x) g

/-- The on-site action of `g` is `⨂ g x` on each local algebra. -/
lemma onSiteCovariance_β (g : Π x, A x ≃⋆ₐ[ℂ] A x) (Λ : Finset sites)
    (z : (piMinTensorProduct sites A).algebra Λ) :
    (onSiteCovariance g).β Λ z = PiMinTensorProduct.congr (fun x : Λ => g x) z :=
  rfl

variable (sites A) in
/-- The families of ⋆-automorphisms act on the net of minimal tensor products by their on-site
actions. -/
noncomputable def onSiteCovarianceHom : (Π x, A x ≃⋆ₐ[ℂ] A x) →* (piMinTensorProduct sites A).Covariance :=
  (onSiteSymmetry sites A).toCovarianceHom fun _ _ x => (piMinTensorProduct sites A).map_parity _ x

variable [∀ x, Nontrivial (A x)]

/-- **The on-site action is continuous**, for nontrivial `A x`, from the product of the point-norm
topologies of the `A x ≃⋆ₐ[ℂ] A x` to the point-norm topology of the ⋆-automorphisms of the
quasi-local C⋆-algebra: on a local observable `z` of `Λ` it is `g ↦ ι_Λ ((⨂ g x) z)`, continuous by
`PiMinTensorProduct.continuous_congr`. -/
theorem continuous_quasiLocalCStarCovarianceHom_onSiteCovariance :
    Continuous fun g : Π x, A x ≃⋆ₐ[ℂ] A x =>
      GradedLocalNet.Covariance.quasiLocalCStarCovarianceHom (onSiteCovariance (sites := sites) g) :=
  GradedLocalNet.Covariance.continuous_quasiLocalCStarCovarianceHom_comp_iff.mpr fun Λ z =>
    ((piMinTensorProduct sites A).isometry_ιLocalCStar Λ).continuous.comp
      ((continuous_eval_const z).comp
        ((PiMinTensorProduct.continuous_congr (A := fun x : Λ => A x) (B := fun x : Λ => A x)).comp
          (continuous_pi fun x => continuous_apply (x : sites))))

variable {G : Type*} [Monoid G] [TopologicalSpace G]

omit [DecidableEq sites] in
variable (sites) in
/-- A C⋆-dynamical system on one C⋆-algebra `B`, acting by the same ⋆-automorphism at every site. -/
noncomputable def constOnSite {B : Type u} [CStarAlgebra B] (ψ : G →ₜ* (B ≃⋆ₐ[ℂ] B)) :
    G →ₜ* (sites → B ≃⋆ₐ[ℂ] B) :=
  ⟨(Pi.constMonoidHom sites _).comp ψ.toMonoidHom, continuous_pi fun _ => ψ.continuous⟩

omit [DecidableEq sites] in
@[simp] lemma constOnSite_apply {B : Type u} [CStarAlgebra B] (ψ : G →ₜ* (B ≃⋆ₐ[ℂ] B)) (g : G)
    (x : sites) : constOnSite sites ψ g x = ψ g :=
  rfl

variable (sites) in
/-- **A C⋆-dynamical system acting site by site acts on the quasi-local C⋆-algebra of the net of
minimal tensor products** of nontrivial algebras as a C⋆-dynamical system, by its on-site actions. -/
noncomputable def onSiteDynamicalSystem (ψ : G →ₜ* (Π x, A x ≃⋆ₐ[ℂ] A x)) :
    G →ₜ* ((piMinTensorProduct sites A).quasiLocalCStarAlgebra ≃⋆ₐ[ℂ]
      (piMinTensorProduct sites A).quasiLocalCStarAlgebra) :=
  GradedLocalNet.Covariance.quasiLocalCStarDynamicalSystem
    ((onSiteCovarianceHom sites A).comp ψ.toMonoidHom)
    ((continuous_quasiLocalCStarCovarianceHom_onSiteCovariance (sites := sites) (A := A)).comp
      ψ.continuous :)

/-- On a local observable the on-site dynamical system acts by `⨂ ψ g x`. -/
@[simp] lemma onSiteDynamicalSystem_ιLocalCStar (ψ : G →ₜ* (Π x, A x ≃⋆ₐ[ℂ] A x)) (g : G)
    (Λ : Finset sites) (z : (piMinTensorProduct sites A).algebra Λ) :
    onSiteDynamicalSystem sites ψ g ((piMinTensorProduct sites A).ιLocalCStar Λ z) =
      (piMinTensorProduct sites A).ιLocalCStar Λ (PiMinTensorProduct.congr (fun x : Λ => ψ g x) z) := by
  exact GradedLocalNet.Covariance.quasiLocalCStarCovarianceEquiv_ιLocalCStar
    (onSiteCovariance (ψ g)) Λ z

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

/-! ### Covariance under permutations of the sites -/

section SitePerm

variable {B : Type u} [CStarAlgebra B]

/-- A permutation `σ` of the sites, restricted to a region `Λ`: the bijection of `Λ` onto `σ Λ`. -/
def sitePermEquiv (σ : sites ≃ sites) (Λ : Finset sites) : Λ ≃ Λ.map σ.toEmbedding :=
  σ.subtypeEquiv fun _ => (Finset.mem_map' σ.toEmbedding).symm

/-- Moving the sites along `σ` commutes with the isotony embeddings `z ↦ z ⊗ 1`. -/
lemma reindex_extend_sitePermEquiv (σ : sites ≃ sites) {Λ Λ' : Finset sites} (h : Λ ⊆ Λ')
    (z : ⨂ₘᵢₙ _ : Λ, B) :
    PiMinTensorProduct.reindex (fun _ : Λ' => B) (sitePermEquiv σ Λ')
        (PiMinTensorProduct.extend (A := fun _ : sites => B) h z) =
      PiMinTensorProduct.extend (A := fun _ : sites => B) (Finset.map_subset_map.mpr h)
        (PiMinTensorProduct.reindex (fun _ : Λ => B) (sitePermEquiv σ Λ) z) := by
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
      · simp [PiTensorProduct.extendFun, sitePermEquiv, hk]
        rfl
      · simp [PiTensorProduct.extendFun, sitePermEquiv, hk]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

variable (B) in
/-- **The covariance of a permutation of the sites** on the net of minimal tensor products of
copies of `B` (a translation or a reflection of a lattice): it moves every region `Λ` to `σ Λ` and its local
algebra along `σ` (`PiMinTensorProduct.reindex`). -/
noncomputable def sitePermCovariance (σ : sites ≃ sites) :
    (piMinTensorProduct sites fun _ => B).Covariance :=
  GradedLocalNet.Covariance.ofSitePerm σ
    (fun Λ => PiMinTensorProduct.reindex (fun _ : Λ => B) (sitePermEquiv σ Λ))
    (fun h z => reindex_extend_sitePermEquiv σ h z) fun _ _ => (piMinTensorProduct sites _).map_parity _ _

/-- The covariance of `σ` moves the elementary tensor `⨂ aₓ` over `Λ` to `⨂ a_{σ⁻¹ y}` over
`σ Λ`. -/
lemma sitePermCovariance_β_of_tprod (σ : sites ≃ sites) (Λ : Finset sites) (a : Λ → B) :
    (sitePermCovariance B σ).β Λ (PiMinTensorProduct.of (fun _ : Λ => B) (⨂ₜ[ℂ] x, a x)) =
      PiMinTensorProduct.of (fun _ : Λ.map σ.toEmbedding => B)
        (⨂ₜ[ℂ] y, a ((sitePermEquiv σ Λ).symm y)) :=
  (PiMinTensorProduct.reindex_of _ _).trans
    (congrArg _ (PiTensorProduct.reindexStarAlgEquiv_tprod _ a))

end SitePerm

end GradedLocalNet
