/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.CStarAlgebra.TensorProduct.InfiniteMinimal
public import QuantumSystem.Physics.LocalNet.QuasiLocalAlgebra

/-!
# The tensor product net of a C⋆-algebra

For a unital C⋆-algebra `B` and a type of sites, the **tensor product net** `LocalNet.tensorNet`
assigns to a finite region `Λ` the minimal tensor product `⨂ₘᵢₙ x : Λ, B` of copies of `B` over its
sites, with the isotony embeddings `z ↦ z ⊗ 1` (`PiMinTensorProduct.extend`). It is a local net:
elements over disjoint regions commute once embedded in a common one
(`PiMinTensorProduct.commute_extend_of_disjoint`). For a nontrivial `B` its embeddings are isometric
(`PiMinTensorProduct.norm_extend`), so it is faithful. For `B` the algebra of a single spin it is the
net of a quantum spin system on the sites.

A ⋆-automorphism `e` of `B` acts on every site at once, by `⨂ e` on each local algebra
(`PiMinTensorProduct.congr`): the **on-site action** of `e`, a covariance leaving every region in
place. It is continuous from the point-norm topology of `B ≃⋆ₐ[ℂ] B`
(`LocalNet.continuous_quasiLocalCStarCovarianceHom_onSiteCovariance`): on an elementary tensor
`⨂ aₓ` it is `e ↦ ⨂ e aₓ`, which is continuous since `‖⨂ aₓ‖ ≤ ∏ ‖aₓ‖`
(`PiMinTensorProduct.norm_of_tprod_le`), and the elementary tensors span a dense subspace on which
the isometric `⨂ e` are equicontinuous (`StarAlgEquiv.continuous_of_dense`). So a C⋆-dynamical
system `ψ : G →ₜ* (B ≃⋆ₐ[ℂ] B)` acts on the quasi-local C⋆-algebra as a C⋆-dynamical system
(`LocalNet.onSiteDynamicalSystem`).

## Main definitions

* `LocalNet.tensorNet sites B` — the tensor product net of `B` over the finite regions of `sites`.
* `LocalNet.onSiteCovariance e` — the on-site action of a ⋆-automorphism `e` of `B`, as a covariance;
  `LocalNet.onSiteCovarianceHom sites B` — as a homomorphism into the covariances.
* `LocalNet.onSiteDynamicalSystem sites ψ` — the C⋆-dynamical system on the quasi-local C⋆-algebra of a
  C⋆-dynamical system `ψ` on `B`.

## Main results

* `LocalNet.continuous_quasiLocalCStarCovarianceHom_onSiteCovariance` — the on-site action is
  continuous on the quasi-local C⋆-algebra.
-/

@[expose] public section

open scoped TensorProduct PiMinTensorProduct

universe u

namespace LocalNet

variable (sites : Type*) [DecidableEq sites] (B : Type u) [CStarAlgebra B]

/-- The **tensor product net** of a unital C⋆-algebra `B` over the finite regions of `sites`: the
local algebra of `Λ` is the minimal tensor product `⨂ₘᵢₙ x : Λ, B`, the isotony embeddings are
`z ↦ z ⊗ 1`, and elements over disjoint regions commute. -/
noncomputable def tensorNet : LocalNet (Finset sites) :=
  LocalNet.ofLocality (fun Λ => ⨂ₘᵢₙ _ : Λ, B)
    (fun h => PiMinTensorProduct.extend (A := fun _ : sites => B) h)
    (fun x => (PiMinTensorProduct.directedSystem (A := fun _ : sites => B)).map_self x)
    (fun h₁₂ h₂₃ x =>
      (PiMinTensorProduct.directedSystem (A := fun _ : sites => B)).map_map h₁₂ h₂₃ x)
    fun h₁ h₂ hd x y =>
      PiMinTensorProduct.commute_extend_of_disjoint (A := fun _ : sites => B) h₁ h₂ hd x y

/-- The local algebra of a region `Λ` is the minimal tensor product of copies of `B` over `Λ`. -/
lemma tensorNet_algebra (Λ : Finset sites) : (tensorNet sites B).algebra Λ = ⨂ₘᵢₙ _ : Λ, B :=
  rfl

/-- The tensor product net of a nontrivial `B` is faithful: its embeddings `z ↦ z ⊗ 1` are
isometric. -/
instance [Nontrivial B] : (tensorNet sites B).Faithful where
  incl_injective h := (AddMonoidHomClass.isometry_of_norm
    (PiMinTensorProduct.extend (A := fun _ : sites => B) h)
    (PiMinTensorProduct.norm_extend (A := fun _ : sites => B) h)).injective

variable {sites B}

/-- The **on-site action** of a ⋆-automorphism `e` of `B`: the covariance of the tensor product net
that leaves every region in place and acts by `⨂ e` on each local algebra. -/
noncomputable def onSiteCovariance (e : B ≃⋆ₐ[ℂ] B) : (tensorNet sites B).Covariance :=
  GradedLocalNet.Covariance.mk' (tensorNet sites B) (OrderIso.refl _) (fun _ _ => Iff.rfl)
    (fun Λ => PiMinTensorProduct.congr fun _ : Λ => e)
    fun h x => (PiMinTensorProduct.extend_congr h (fun _ => e) x).symm

/-- The on-site action of `e` is `⨂ e` on each local algebra. -/
lemma onSiteCovariance_β (e : B ≃⋆ₐ[ℂ] B) (Λ : Finset sites) (z : (tensorNet sites B).algebra Λ) :
    (onSiteCovariance e).β Λ z = PiMinTensorProduct.congr (fun _ : Λ => e) z :=
  rfl

variable (sites B) in
/-- The ⋆-automorphisms of `B` act on the tensor product net by their on-site actions. -/
noncomputable def onSiteCovarianceHom : (B ≃⋆ₐ[ℂ] B) →* (tensorNet sites B).Covariance where
  toFun := onSiteCovariance
  map_one' := by
    refine GradedLocalNet.Covariance.ext rfl fun Λ z h => ?_
    exact ((tensorNet sites B).algebraCongr_self h _).trans
      (PiMinTensorProduct.congr_refl_apply (A := fun _ : Λ => B) z)
  map_mul' e f := by
    refine GradedLocalNet.Covariance.ext rfl fun Λ z h => ?_
    exact ((tensorNet sites B).algebraCongr_self h _).trans
      (PiMinTensorProduct.congr_congr (fun _ : Λ => e) (fun _ : Λ => f) z).symm

variable [Nontrivial B]

/-- **The on-site action is continuous** from the point-norm topology of `B ≃⋆ₐ[ℂ] B` to that of the
⋆-automorphisms of the quasi-local C⋆-algebra: on a local observable `z` of `Λ` it is
`e ↦ ι_Λ ((⨂ e) z)`, continuous by `PiMinTensorProduct.continuous_congr`. -/
theorem continuous_quasiLocalCStarCovarianceHom_onSiteCovariance :
    Continuous fun e : B ≃⋆ₐ[ℂ] B =>
      GradedLocalNet.Covariance.quasiLocalCStarCovarianceHom (onSiteCovariance (sites := sites) e) :=
  GradedLocalNet.Covariance.continuous_quasiLocalCStarCovarianceHom_comp_iff.mpr fun Λ z =>
    ((tensorNet sites B).isometry_ιLocalCStar Λ).continuous.comp
      ((continuous_eval_const z).comp
        ((PiMinTensorProduct.continuous_congr (A := fun _ : Λ => B) (B := fun _ : Λ => B)).comp
          (continuous_pi fun _ => continuous_id)))

variable {G : Type*} [Monoid G] [TopologicalSpace G]

variable (sites) in
/-- **A C⋆-dynamical system on `B` acts on the quasi-local C⋆-algebra of the tensor product net**
as a C⋆-dynamical system, by its on-site actions. -/
noncomputable def onSiteDynamicalSystem (ψ : G →ₜ* (B ≃⋆ₐ[ℂ] B)) :
    G →ₜ* ((tensorNet sites B).quasiLocalCStarAlgebra ≃⋆ₐ[ℂ]
      (tensorNet sites B).quasiLocalCStarAlgebra) :=
  GradedLocalNet.Covariance.quasiLocalCStarDynamicalSystem
    ((onSiteCovarianceHom sites B).comp ψ.toMonoidHom)
    ((continuous_quasiLocalCStarCovarianceHom_onSiteCovariance (sites := sites) (B := B)).comp
      ψ.continuous :)

/-- On a local observable the on-site dynamical system acts by `⨂ ψ g`. -/
@[simp] lemma onSiteDynamicalSystem_ιLocalCStar (ψ : G →ₜ* (B ≃⋆ₐ[ℂ] B)) (g : G) (Λ : Finset sites)
    (z : (tensorNet sites B).algebra Λ) :
    onSiteDynamicalSystem sites ψ g ((tensorNet sites B).ιLocalCStar Λ z) =
      (tensorNet sites B).ιLocalCStar Λ (PiMinTensorProduct.congr (A := fun _ : Λ => B)
        (B := fun _ : Λ => B) (fun _ => ψ g) z) := by
  exact GradedLocalNet.Covariance.quasiLocalCStarCovarianceEquiv_ιLocalCStar
    (onSiteCovariance (ψ g)) Λ z

/-- On an elementary tensor `⨂ aₓ` the on-site dynamical system acts site by site:
`⨂ aₓ ↦ ⨂ ψ g aₓ`. -/
lemma onSiteDynamicalSystem_ιLocalCStar_of_tprod (ψ : G →ₜ* (B ≃⋆ₐ[ℂ] B)) (g : G)
    (Λ : Finset sites) (a : Λ → B) :
    onSiteDynamicalSystem sites ψ g
        ((tensorNet sites B).ιLocalCStar Λ (PiMinTensorProduct.of (fun _ : Λ => B) (⨂ₜ[ℂ] x, a x))) =
      (tensorNet sites B).ιLocalCStar Λ
        (PiMinTensorProduct.of (fun _ : Λ => B) (⨂ₜ[ℂ] x, ψ g (a x))) := by
  refine (onSiteDynamicalSystem_ιLocalCStar ψ g Λ _).trans (congrArg _ ?_)
  rw [PiMinTensorProduct.congr_of, PiTensorProduct.mapStarAlgHom_tprod]
  rfl

/-- A local observable is fixed by the on-site dynamical system at `g` iff it is fixed by `⨂ ψ g`. -/
lemma onSiteDynamicalSystem_ιLocalCStar_eq_iff (ψ : G →ₜ* (B ≃⋆ₐ[ℂ] B)) (g : G)
    (Λ : Finset sites) (z : ⨂ₘᵢₙ _ : Λ, B) :
    onSiteDynamicalSystem sites ψ g ((tensorNet sites B).ιLocalCStar Λ z) =
        (tensorNet sites B).ιLocalCStar Λ z ↔
      PiMinTensorProduct.congr (A := fun _ : Λ => B) (B := fun _ : Λ => B) (fun _ => ψ g) z = z := by
  exact (Eq.congr_left (onSiteDynamicalSystem_ιLocalCStar ψ g Λ z)).trans
    ((tensorNet sites B).ιLocalCStar_injective Λ).eq_iff

end LocalNet
