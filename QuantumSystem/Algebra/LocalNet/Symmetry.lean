module

public import QuantumSystem.Algebra.LocalNet.Net

/-!
# Symmetries of a local net

A **symmetry** of a local net is a site permutation `σ` together with, for every finite region
`Λ`, a `*`-isomorphism `β_Λ : 𝔄(Λ) ≃⋆ₐ[ℂ] 𝔄(σΛ)` of local algebras that is natural with respect
to the isotony embeddings. This realises the AQFT covariance datum `β(𝔄(Λ)) = 𝔄(σΛ)` at the
abstract net level (Naaijkens 2012 §3.2, Verch 2025 §1.2).

Symmetries compose: the identity and composition below, together with the inverse, make the
symmetries of a net a `Group`. This file carries only the symmetry *group* — purely algebraic data
depending on the net axioms. The induced **covariance action** of a symmetry on the algebra of
local observables (and its C⋆-completion) lives in `LocalNet.Covariance`.
-/

@[expose] public section

namespace LocalNet

variable {sites : Type*} [DecidableEq sites] (N : LocalNet sites)

/-! ### Symmetries of the net

A **symmetry** of a local net is a site permutation `σ` together with, for each finite region, a
`*`-isomorphism `β_Λ : 𝔄(Λ) ≃⋆ₐ[ℂ] 𝔄(σΛ)` of local algebras that is natural with respect to the
isotony embeddings. This realises the AQFT covariance axiom `β(𝔄(Λ)) = 𝔄(σΛ)` at the abstract net
level. Being purely algebraic, the symmetry group needs no faithfulness hypothesis.
-/

/-- A **symmetry** of a local net `N`: a site permutation `σ` together with, for every finite
    region `Λ`, a `*`-isomorphism `β Λ : 𝔄(Λ) ≃⋆ₐ[ℂ] 𝔄(σΛ)`, natural with respect to the isotony
    embeddings (`β_incl`). This is the AQFT covariance datum at the abstract net level. -/
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
    and `Symmetry.inv` the inverse. -/
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

end Symmetry

end LocalNet
