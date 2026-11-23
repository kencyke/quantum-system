/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Data.Finset.Grade
public import QuantumSystem.Physics.LocalNet.Automorphism.Basic

/-!
# Automorphisms of a lattice net: permutations of the sites

For lattice nets (`K = Finset sites`, with `⟂ = Disjoint`) the symmetry group of the index set is
the group of permutations of the sites: an automorphism is induced by a site permutation via
`GradedLocalNet.Automorphism.ofSitePerm`, and conversely every automorphism of a lattice net arises this
way (`GradedLocalNet.Automorphism.exists_eq_ofSitePerm`), since an order automorphism of
`Finset sites` maps atoms to atoms and the atoms are the singletons.

## Main definitions and results

* `GradedLocalNet.Automorphism.ofSitePerm σ β …` — the automorphism of a site permutation `σ`.
* `GradedLocalNet.Automorphism.sitePerm e` — the site permutation underlying an order automorphism
  `e` of the lattice regions; `GradedLocalNet.Automorphism.map_sitePerm` — `e` is its image map.
* **`GradedLocalNet.Automorphism.exists_eq_ofSitePerm`** — every automorphism of a lattice net comes
  from a site permutation.
-/

@[expose] public section

namespace GradedLocalNet.Automorphism

/-! ### Lattice automorphisms from site permutations -/

/-- Build an automorphism of a lattice net (`K = Finset sites`) from a **site permutation**: the
    induced region automorphism is `Λ ↦ Λ.map σ`, which preserves disjointness. This recovers the
    site-permutation automorphisms of spin-system nets. Conversely every
    automorphism of a lattice net arises this way — that is `exists_eq_ofSitePerm`, proved below via
    the fact that an order automorphism of `Finset sites` preserves atoms (singletons) and is
    therefore induced by a permutation of the sites. -/
def ofSitePerm {sites : Type*} {N : GradedLocalNet (Finset sites)} (σ : sites ≃ sites)
    (β : ∀ Λ : Finset sites, N.algebra Λ ≃⋆ₐ[ℂ] N.algebra (Λ.map σ.toEmbedding))
    (β_incl : ∀ {Λ Λ' : Finset sites} (h : Λ ⊆ Λ') (x : N.algebra Λ),
      β Λ' (N.incl h x) = N.incl (Finset.map_subset_map.mpr h) (β Λ x))
    (β_parity : ∀ (Λ : Finset sites) (x : N.algebra Λ),
      β Λ (N.parity Λ x) = N.parity (Λ.map σ.toEmbedding) (β Λ x)) :
    N.Automorphism where
  σ := { toEquiv := σ.finsetCongr, map_rel_iff' := Finset.map_subset_map }
  map_orthogonal_iff _ _ := Finset.disjoint_map _
  β := β
  β_incl h x := β_incl h x
  β_parity := β_parity

/-! #### Every lattice automorphism comes from a site permutation

An order automorphism of `Finset sites` maps atoms to atoms, and the atoms of `Finset sites` are
exactly the singletons; so it is determined by a permutation of the sites, and the automorphism it
belongs to is `ofSitePerm` of that permutation.
-/

end GradedLocalNet.Automorphism

/-! The site permutation of an order automorphism of `Finset sites` involves no net, and is
stated in the namespace `OrderIso`. -/

namespace OrderIso

/-- The image of a singleton region under an order automorphism is again a singleton: order
    isomorphisms preserve atoms (`OrderIso.isAtom_iff`), and the atoms of `Finset sites` are the
    singletons (`Finset.isAtom_iff`). -/
lemma exists_singleton_image {sites : Type*} (e : Finset sites ≃o Finset sites) (x : sites) :
    ∃ y, e {x} = {y} :=
  Finset.isAtom_iff.1 ((e.isAtom_iff _).2 (Finset.isAtom_singleton x))

open Classical in
/-- The site that an order automorphism of lattice regions sends `x` to. -/
noncomputable def sitePermFun {sites : Type*} (e : Finset sites ≃o Finset sites) (x : sites) :
    sites :=
  (exists_singleton_image e x).choose

/-- Defining property of `sitePermFun`: `e {x} = {sitePermFun e x}`. -/
lemma sitePermFun_spec {sites : Type*} (e : Finset sites ≃o Finset sites) (x : sites) :
    e {x} = {sitePermFun e x} := (exists_singleton_image e x).choose_spec

/-- **The site permutation underlying an order automorphism of lattice regions.** Its inverse is
    the site map of the inverse automorphism, the two being mutually inverse because `e.symm` undoes
    `e` on singletons. -/
noncomputable def sitePerm {sites : Type*} (e : Finset sites ≃o Finset sites) : sites ≃ sites where
  toFun := sitePermFun e
  invFun := sitePermFun e.symm
  left_inv x := by
    have h2 := sitePermFun_spec e.symm (sitePermFun e x)
    rw [← sitePermFun_spec e x, e.symm_apply_apply] at h2
    exact (Finset.singleton_inj.1 h2).symm
  right_inv y := by
    have h2 := sitePermFun_spec e (sitePermFun e.symm y)
    rw [← sitePermFun_spec e.symm y, e.apply_symm_apply] at h2
    exact (Finset.singleton_inj.1 h2).symm

/-- **An order automorphism of lattice regions is the image map of its site permutation.**
    Membership in `e Λ` is tested one site at a time: `y ∈ e Λ` iff `{y} ≤ e Λ` iff
    `e.symm {y} ≤ Λ` iff `sitePerm e ⁻¹ y ∈ Λ`. -/
lemma map_sitePerm {sites : Type*} (e : Finset sites ≃o Finset sites) (Λ : Finset sites) :
    e Λ = Λ.map (sitePerm e).toEmbedding := by
  ext y
  rw [Finset.mem_map]
  have key : y ∈ e Λ ↔ sitePermFun e.symm y ∈ Λ := by
    rw [← Finset.singleton_subset_iff, ← Finset.singleton_subset_iff,
      ← sitePermFun_spec e.symm y]
    exact (e.symm_apply_le).symm
  rw [key]
  constructor
  · intro h
    exact ⟨sitePermFun e.symm y, h, (sitePerm e).right_inv y⟩
  · rintro ⟨x, hx, rfl⟩
    rwa [show sitePermFun e.symm ((sitePerm e).toEmbedding x) = x from (sitePerm e).left_inv x]

end OrderIso

namespace GradedLocalNet.Automorphism

variable {sites : Type*} {N : GradedLocalNet (Finset sites)}

/-- **The region automorphism of a lattice automorphism is induced by a site permutation.** -/
lemma exists_sitePerm (a : N.Automorphism) :
    ∃ σ : sites ≃ sites, ∀ Λ : Finset sites, a.σ Λ = Λ.map σ.toEmbedding :=
  ⟨a.σ.sitePerm, a.σ.map_sitePerm⟩

/-- **Every automorphism of a lattice net arises from a site permutation** — the converse of
    `ofSitePerm`, and the statement its docstring advertises. The region automorphism is the image
    map of a site permutation `σ` (`exists_sitePerm`); transporting the local `*`-isomorphisms
    along that identification of regions produces the `β` data, whose naturality is `a`'s own
    naturality composed with `incl_algebraCongr`. -/
theorem exists_eq_ofSitePerm (a : N.Automorphism) :
    ∃ (σ : sites ≃ sites)
      (β : ∀ Λ : Finset sites, N.algebra Λ ≃⋆ₐ[ℂ] N.algebra (Λ.map σ.toEmbedding))
      (β_incl : ∀ {Λ Λ' : Finset sites} (h : Λ ⊆ Λ') (x : N.algebra Λ),
        β Λ' (N.incl h x) = N.incl (Finset.map_subset_map.mpr h) (β Λ x))
      (β_parity : ∀ (Λ : Finset sites) (x : N.algebra Λ),
        β Λ (N.parity Λ x) = N.parity (Λ.map σ.toEmbedding) (β Λ x)),
      a = Automorphism.ofSitePerm σ β β_incl β_parity := by
  obtain ⟨σ, hσ⟩ := a.exists_sitePerm
  refine ⟨σ, fun Λ => (a.β Λ).trans (N.algebraCongr (hσ Λ)), ?_, ?_, ?_⟩
  · intro Λ Λ' h x
    simp only [StarAlgEquiv.trans_apply]
    rw [a.β_incl h]
    exact N.incl_algebraCongr (hσ Λ) (hσ Λ') (a.σ.monotone h) (Finset.map_subset_map.mpr h) _
  · intro Λ x
    simp only [StarAlgEquiv.trans_apply]
    rw [a.β_parity, N.parity_algebraCongr]
  · exact Automorphism.ext (OrderIso.ext (funext hσ)) fun Λ x e => rfl

end GradedLocalNet.Automorphism
