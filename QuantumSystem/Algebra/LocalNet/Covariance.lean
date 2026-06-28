module

public import QuantumSystem.Algebra.LocalNet.Net

/-!
# Covariance data for a local net

A **covariance** of a local net is a site permutation `σ` together with, for every finite region
`Λ`, a `*`-isomorphism `β_Λ : 𝔄(Λ) ≃⋆ₐ[ℂ] 𝔄(σΛ)` of local algebras that is natural with respect
to the isotony embeddings. The naturality field `β_incl` is the AQFT covariance axiom
`β(𝔄(Λ)) = 𝔄(σΛ)` compatibly with inclusions (Naaijkens 2012 §3.2, Verch 2025 §1.2). These
covariances form a `Group` under composition (`Covariance.id`, `Covariance.comp`, `Covariance.inv`).

This file isolates the abstract covariance *data* and its group structure. Its *action* on the
quasi-local algebra — assembling the per-region `*`-isomorphisms into a `*`-automorphism
`quasiLocalCovariance` and (for a `Faithful` net) its continuous extension to the quasi-local
C⋆-algebra — is built in `LocalNet.QuasiLocalAlgebra`. A symmetry group `G` acts on the net by
supplying a group homomorphism `G →* N.Covariance` (whose `σ`-component is the geometric action
`G → sites ≃ sites`); composing it with `quasiLocalCovarianceHom` — or, for a `Faithful` net,
`quasiLocalCStarCovarianceHom` — yields the automorphic action of `G` on the (quasi-local) algebra.
-/

@[expose] public section

namespace LocalNet

variable {sites : Type*} [DecidableEq sites] (N : LocalNet sites)

/-! ### Covariances of the net

A covariance of a local net is a site permutation `σ` together with, for each finite region, a
`*`-isomorphism `β_Λ : 𝔄(Λ) ≃⋆ₐ[ℂ] 𝔄(σΛ)` of local algebras that is natural with respect to the
isotony embeddings. This realises the AQFT covariance axiom `β(𝔄(Λ)) = 𝔄(σΛ)` at the abstract net
level. Being purely algebraic, the covariance group needs no faithfulness hypothesis.
-/

/-- A **covariance** of a local net `N`: a site permutation `σ` together with, for every finite
    region `Λ`, a `*`-isomorphism `β Λ : 𝔄(Λ) ≃⋆ₐ[ℂ] 𝔄(σΛ)`, natural with respect to the isotony
    embeddings (`β_incl`). This is the AQFT covariance datum at the abstract net level. -/
structure Covariance where
  /-- The underlying site permutation; its image map `Λ ↦ σΛ` carries the region map. -/
  σ : sites ≃ sites
  /-- The covariance `*`-isomorphism `β_Λ : 𝔄(Λ) ≃⋆ₐ[ℂ] 𝔄(σΛ)` on each region. -/
  β : ∀ Λ : Finset sites, N.algebra Λ ≃⋆ₐ[ℂ] N.algebra (Λ.map σ.toEmbedding)
  /-- **Naturality / covariance**: `β` intertwines the isotony embeddings, so it maps the net to
      itself compatibly with inclusions — the AQFT covariance axiom `β(𝔄(Λ)) = 𝔄(σΛ)`. -/
  β_incl : ∀ {Λ Λ' : Finset sites} (h : Λ ⊆ Λ') (x : N.algebra Λ),
      β Λ' (N.incl h x) = N.incl (Finset.map_subset_map.mpr h) (β Λ x)

namespace Covariance

variable {N} (a : N.Covariance)

/-- The image `σΛ` of a region under the covariance. -/
def region (Λ : Finset sites) : Finset sites := Λ.map a.σ.toEmbedding

/-- **Extensionality** for covariances: two covariances with the same site permutation and the same
    local `*`-isomorphisms (compared along the induced region equality) are equal. The naturality
    field `β_incl` is a proposition, hence irrelevant. -/
@[ext (iff := false)] theorem ext {s t : N.Covariance} (hσ : s.σ = t.σ)
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
/-- The **identity covariance**: the identity site permutation with the identity local
    `*`-isomorphisms (transported along `Λ = σ_id Λ`). -/
def id : N.Covariance where
  σ := Equiv.refl sites
  β Λ := N.algebraCongr (by simp)
  β_incl h x := N.incl_algebraCongr _ _ h _ x

/-- **Composition of covariances**: apply `b`, then `a`. The site permutations compose; the local
    `*`-isomorphisms compose and are transported along the region-map functoriality
    `(σ_a ∘ σ_b) Λ = σ_a (σ_b Λ)`. -/
def comp (a b : N.Covariance) : N.Covariance where
  σ := b.σ.trans a.σ
  β Λ := ((b.β Λ).trans (a.β (Λ.map b.σ.toEmbedding))).trans
    (N.algebraCongr (by simp [Finset.map_map, Equiv.trans_toEmbedding]))
  β_incl h x := by
    simp only [StarAlgEquiv.trans_apply]
    rw [b.β_incl h, a.β_incl (Finset.map_subset_map.mpr h)]
    exact N.incl_algebraCongr _ _ _ _ _

/-- The **inverse covariance**: the inverse site permutation with the inverse local
    `*`-isomorphisms, transported along the region-map functoriality `σ⁻¹σ Λ = Λ`. -/
def inv (a : N.Covariance) : N.Covariance where
  σ := a.σ.symm
  β Λ := (N.algebraCongr (show (Λ.map a.σ.symm.toEmbedding).map a.σ.toEmbedding = Λ by
      simp [Finset.map_map]).symm).trans
      (a.β (Λ.map a.σ.symm.toEmbedding)).symm
  β_incl h x := by
    simp only [StarAlgEquiv.trans_apply]
    rw [N.incl_algebraCongr _ _ h (Finset.map_subset_map.mpr (Finset.map_subset_map.mpr h)),
      a.β_symm_incl]

@[simp] theorem id_β_apply (Λ : Finset sites) (x : N.algebra Λ) :
    (Covariance.id N).β Λ x =
      N.algebraCongr (show Λ = Λ.map (Equiv.refl sites).toEmbedding by simp) x :=
  rfl

@[simp] theorem comp_β_apply (a b : N.Covariance) (Λ : Finset sites) (x : N.algebra Λ) :
    (a.comp b).β Λ x = N.algebraCongr (show (Λ.map b.σ.toEmbedding).map a.σ.toEmbedding
        = Λ.map (b.σ.trans a.σ).toEmbedding by simp [Finset.map_map, Equiv.trans_toEmbedding])
      (a.β (Λ.map b.σ.toEmbedding) (b.β Λ x)) :=
  rfl

@[simp] theorem inv_β_apply (a : N.Covariance) (Λ : Finset sites) (x : N.algebra Λ) :
    (Covariance.inv a).β Λ x = (a.β (Λ.map a.σ.symm.toEmbedding)).symm
      (N.algebraCongr (show (Λ.map a.σ.symm.toEmbedding).map a.σ.toEmbedding = Λ by
        simp [Finset.map_map]).symm x) :=
  rfl

@[simp] theorem region_id (Λ : Finset sites) : (Covariance.id N).region Λ = Λ := by
  simp [region, Covariance.id]

@[simp] theorem region_comp (a b : N.Covariance) (Λ : Finset sites) :
    (a.comp b).region Λ = a.region (b.region Λ) := by
  simp [region, Covariance.comp, Finset.map_map, Equiv.trans_toEmbedding]

theorem id_comp (a : N.Covariance) : (Covariance.id N).comp a = a := by
  refine Covariance.ext ?_ fun Λ x e => ?_
  · simp [Covariance.comp, Covariance.id]
  · rw [algebraCongr_eq_iff]
    simp only [comp_β_apply, id_β_apply]
    erw [algebraCongr_trans]
    rfl

theorem comp_id (a : N.Covariance) : a.comp (Covariance.id N) = a := by
  refine Covariance.ext ?_ fun Λ x e => ?_
  · simp [Covariance.comp, Covariance.id]
  · rw [algebraCongr_eq_iff]
    simp only [comp_β_apply, id_β_apply]
    erw [a.β_algebraCongr, algebraCongr_trans]
    rfl

theorem comp_assoc (a b c : N.Covariance) : (a.comp b).comp c = a.comp (b.comp c) := by
  refine Covariance.ext ?_ fun Λ x e => ?_
  · simp [Covariance.comp, Equiv.trans_assoc]
  · rw [algebraCongr_eq_iff]
    simp only [comp_β_apply]
    erw [a.β_algebraCongr, algebraCongr_trans, algebraCongr_trans, algebraCongr_trans]
    rfl

theorem inv_comp (a : N.Covariance) : (Covariance.inv a).comp a = Covariance.id N := by
  refine Covariance.ext ?_ fun Λ x e => ?_
  · simp [Covariance.comp, Covariance.inv, Covariance.id, Equiv.self_trans_symm]
  · rw [algebraCongr_eq_iff]
    simp only [comp_β_apply, inv_β_apply, id_β_apply]
    erw [← a.β_algebraCongr, StarAlgEquiv.symm_apply_apply, algebraCongr_trans,
      algebraCongr_trans]
    · rfl
    · simp [Finset.map_map]

/-- The covariances of a local net form a **group** under composition, with `Covariance.id` the
    unit and `Covariance.inv` the inverse. -/
noncomputable instance : Group N.Covariance where
  mul a b := a.comp b
  one := Covariance.id N
  inv a := a.inv
  mul_assoc := Covariance.comp_assoc
  one_mul := Covariance.id_comp
  mul_one := Covariance.comp_id
  inv_mul_cancel := Covariance.inv_comp

/-- The group multiplication is composition of covariances. -/
theorem mul_def (a b : N.Covariance) : a * b = a.comp b := rfl

/-- The group unit is the identity covariance. -/
theorem one_def : (1 : N.Covariance) = Covariance.id N := rfl

/-- The group inverse is the inverse covariance. -/
theorem inv_def (a : N.Covariance) : a⁻¹ = a.inv := rfl

end Covariance

end LocalNet
