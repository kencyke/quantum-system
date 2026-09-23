module

public import QuantumSystem.Algebra.LocalNet.Net
public import Mathlib.Data.Finset.Grade

/-!
# Covariance data for a local net

A **covariance** of a local net over a causal index set `K` is an order automorphism `σ : K ≃o K`
of the regions preserving causal orthogonality, together with, for every region `O`, a
`*`-isomorphism `β_O : 𝔄(O) ≃⋆ₐ[ℂ] 𝔄(σO)` of local algebras that is natural with respect to the
isotony embeddings. The naturality field `β_incl` is the AQFT covariance axiom
`β(𝔄(O)) = 𝔄(σO)` compatibly with inclusions (Naaijkens, *Anyons in Infinite Quantum Systems*,
2012, §3.2; Verch, *Lecture Notes on Operator Algebras and Quantum Field Theory*,
arXiv:2507.00900, 2025, §1.2). These
covariances form a `Group` under composition (`Covariance.id`, `Covariance.comp`,
`Covariance.inv`). For lattice nets (`K = Finset sites`) a covariance is induced by a site
permutation via `Covariance.ofSitePerm`, and conversely every covariance of a lattice net arises
this way (`Covariance.exists_eq_ofSitePerm`), since an order automorphism of `Finset sites` maps
atoms to atoms and the atoms are the singletons.

This file isolates the abstract covariance *data* and its group structure. Its *action* on the
quasi-local algebra — assembling the per-region `*`-isomorphisms into a `*`-automorphism
`localObservableCovariance` and (for a `Faithful` net) its continuous extension to the quasi-local
C⋆-algebra — is built in `LocalNet.QuasiLocalAlgebra`. A symmetry group `G` acts on the net by
supplying a group homomorphism `G →* N.Covariance` (whose `σ`-component is the geometric action
`G → K ≃o K`); composing it with `localObservableCovarianceHom` — or, for a `Faithful` net,
`quasiLocalCStarCovarianceHom` — yields the automorphic action of `G` on the (quasi-local) algebra.

## Notation

`𝔄(O)` and `𝓡(O)` in the prose above are documentation shorthand for the local C⋆-algebra
`N.algebra O` and the local von Neumann algebra `N.localVonNeumannAlgebra R O`; the convention —
and why neither is a Lean notation — is stated in full in `QuantumSystem.Algebra.LocalNet.Net`.
-/

@[expose] public section

namespace LocalNet

open scoped CausalOrthogonality

variable {K : Type*} [Preorder K] [CausalOrthogonality K] (N : LocalNet K)

/-! ### Covariances of the net

A covariance of a local net is a causal order automorphism `σ` of the index set together with,
for each region, a `*`-isomorphism `β_O : 𝔄(O) ≃⋆ₐ[ℂ] 𝔄(σO)` of local algebras that is natural
with respect to the isotony embeddings. This realises the AQFT covariance axiom `β(𝔄(O)) = 𝔄(σO)`
at the abstract net level. Being purely algebraic, the covariance group needs no faithfulness
hypothesis.
-/

/-- A **covariance** of a local net `N`: an order automorphism `σ` of the causal index set
    preserving causal orthogonality (`map_orthogonal_iff`), together with, for every region `O`,
    a `*`-isomorphism `β O : 𝔄(O) ≃⋆ₐ[ℂ] 𝔄(σO)`, natural with respect to the isotony embeddings
    (`β_incl`). This is the AQFT covariance datum at the abstract net level. -/
structure Covariance where
  /-- The underlying automorphism of the causal index set, carrying the region map `O ↦ σO`. -/
  σ : K ≃o K
  /-- The region automorphism preserves causal orthogonality. Stated as an `iff` so that the
      inverse covariance is again a covariance. -/
  map_orthogonal_iff : ∀ ⦃O₁ O₂ : K⦄, σ O₁ ⟂ σ O₂ ↔ O₁ ⟂ O₂
  /-- The covariance `*`-isomorphism `β_O : 𝔄(O) ≃⋆ₐ[ℂ] 𝔄(σO)` on each region. -/
  β : ∀ O : K, N.algebra O ≃⋆ₐ[ℂ] N.algebra (σ O)
  /-- **Naturality / covariance**: `β` intertwines the isotony embeddings, so it maps the net to
      itself compatibly with inclusions — the AQFT covariance axiom `β(𝔄(O)) = 𝔄(σO)`. -/
  β_incl : ∀ {O O' : K} (h : O ≤ O') (x : N.algebra O),
      β O' (N.incl h x) = N.incl (σ.monotone h) (β O x)

namespace Covariance

variable {N} (a : N.Covariance)

/-- **Extensionality** for covariances: two covariances with the same region automorphism and the
    same local `*`-isomorphisms (compared along the induced region equality) are equal. The
    remaining fields are propositions, hence irrelevant. -/
@[ext (iff := false)] lemma ext {s t : N.Covariance} (hσ : s.σ = t.σ)
    (hβ : ∀ (O : K) (x : N.algebra O) (e : s.σ O = t.σ O),
      N.algebraCongr e (s.β O x) = t.β O x) : s = t := by
  revert hσ hβ
  obtain ⟨sσ, -, sβ, -⟩ := s
  obtain ⟨tσ, -, tβ, -⟩ := t
  rintro rfl hβ
  have hβ' : sβ = tβ := by
    funext O
    ext x
    simpa using hβ O x rfl
  subst hβ'
  rfl

/-- Naturality of the inverse local `*`-isomorphisms with respect to isotony. -/
lemma β_symm_incl {O O' : K} (h : O ≤ O') (y : N.algebra (a.σ O)) :
    (a.β O').symm (N.incl (a.σ.monotone h) y) = N.incl h ((a.β O).symm y) := by
  have key := a.β_incl h ((a.β O).symm y)
  rw [StarAlgEquiv.apply_symm_apply] at key
  rw [← key, StarAlgEquiv.symm_apply_apply]

/-- The local `*`-isomorphisms commute with the region-equality transport. -/
lemma β_algebraCongr {O O' : K} (e : O = O') (x : N.algebra O) :
    a.β O' (N.algebraCongr e x) = N.algebraCongr (by rw [e]) (a.β O x) := by
  subst e; simp

variable (N) in
/-- The **identity covariance**: the identity region automorphism with the identity local
    `*`-isomorphisms. -/
def id : N.Covariance where
  σ := OrderIso.refl K
  map_orthogonal_iff _ _ := Iff.rfl
  β _ := StarAlgEquiv.refl
  β_incl _ _ := rfl

/-- **Composition of covariances**: apply `b`, then `a`. The region automorphisms compose, and
    the local `*`-isomorphisms compose along them. -/
def comp (a b : N.Covariance) : N.Covariance where
  σ := b.σ.trans a.σ
  map_orthogonal_iff O₁ O₂ :=
    (a.map_orthogonal_iff (O₁ := b.σ O₁) (O₂ := b.σ O₂)).trans
      (b.map_orthogonal_iff (O₁ := O₁) (O₂ := O₂))
  β O := (b.β O).trans (a.β (b.σ O))
  β_incl h x := by
    simp only [StarAlgEquiv.trans_apply]
    rw [b.β_incl h]
    exact a.β_incl (b.σ.monotone h) ((b.β _) x)

/-- The **inverse covariance**: the inverse region automorphism with the inverse local
    `*`-isomorphisms, transported along `σ(σ⁻¹O) = O`. -/
def inv (a : N.Covariance) : N.Covariance where
  σ := a.σ.symm
  map_orthogonal_iff O₁ O₂ := by
    rw [← a.map_orthogonal_iff, a.σ.apply_symm_apply, a.σ.apply_symm_apply]
  β O := (N.algebraCongr (a.σ.apply_symm_apply O).symm).trans (a.β (a.σ.symm O)).symm
  β_incl h x := by
    simp only [StarAlgEquiv.trans_apply]
    rw [N.incl_algebraCongr _ _ h (a.σ.monotone (a.σ.symm.monotone h)), a.β_symm_incl]

/-- The identity covariance acts as the identity on every local algebra. -/
@[simp] lemma id_β_apply (O : K) (x : N.algebra O) : (Covariance.id N).β O x = x :=
  rfl

/-- The composite covariance acts by composing the local `*`-isomorphisms along the region maps. -/
@[simp] lemma comp_β_apply (a b : N.Covariance) (O : K) (x : N.algebra O) :
    (a.comp b).β O x = a.β (b.σ O) (b.β O x) :=
  rfl

/-- The inverse covariance acts by the inverse local `*`-isomorphism, after transporting the
    argument along the region equality `σ(σ⁻¹O) = O`. -/
@[simp] lemma inv_β_apply (a : N.Covariance) (O : K) (x : N.algebra O) :
    (Covariance.inv a).β O x = (a.β (a.σ.symm O)).symm
      (N.algebraCongr (a.σ.apply_symm_apply O).symm x) :=
  rfl

/-- The identity covariance fixes every region. -/
@[simp] lemma id_σ_apply (O : K) : (Covariance.id N).σ O = O :=
  rfl

/-- Composing covariances composes their region maps. -/
@[simp] lemma comp_σ_apply (a b : N.Covariance) (O : K) :
    (a.comp b).σ O = a.σ (b.σ O) :=
  rfl

/-- The identity covariance is a left unit for composition. -/
lemma id_comp (a : N.Covariance) : (Covariance.id N).comp a = a := by
  refine Covariance.ext ?_ fun O x e => ?_
  · exact OrderIso.ext rfl
  · exact N.algebraCongr_self e _

/-- The identity covariance is a right unit for composition. -/
lemma comp_id (a : N.Covariance) : a.comp (Covariance.id N) = a := by
  refine Covariance.ext ?_ fun O x e => ?_
  · exact OrderIso.ext rfl
  · exact N.algebraCongr_self e _

/-- Composition of covariances is associative. -/
lemma comp_assoc (a b c : N.Covariance) : (a.comp b).comp c = a.comp (b.comp c) := by
  refine Covariance.ext ?_ fun O x e => ?_
  · exact OrderIso.ext rfl
  · exact N.algebraCongr_self e _

/-- The inverse covariance is a left inverse for composition; together with the three laws above
    this is what makes the covariances a group. -/
lemma inv_comp (a : N.Covariance) : (Covariance.inv a).comp a = Covariance.id N := by
  refine Covariance.ext ?_ fun O x e => ?_
  · exact OrderIso.ext (funext fun O => a.σ.symm_apply_apply O)
  · rw [algebraCongr_eq_iff]
    simp only [comp_β_apply, inv_β_apply, id_β_apply]
    rw [← a.β_algebraCongr, StarAlgEquiv.symm_apply_apply]
    rfl

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
lemma mul_def (a b : N.Covariance) : a * b = a.comp b := rfl

/-- The group unit is the identity covariance. -/
lemma one_def : (1 : N.Covariance) = Covariance.id N := rfl

/-- The group inverse is the inverse covariance. -/
lemma inv_def (a : N.Covariance) : a⁻¹ = a.inv := rfl

/-! ### Lattice covariances from site permutations -/

/-- Build a covariance of a lattice net (`K = Finset sites`) from a **site permutation**: the
    induced region automorphism is `Λ ↦ Λ.map σ`, which preserves disjointness. This recovers the
    site-permutation covariances of spin-system nets (Naaijkens, *Anyons in Infinite Quantum
    Systems*, 2012, §3.2). Conversely every
    covariance of a lattice net arises this way — that is `exists_eq_ofSitePerm`, proved below via
    the fact that an order automorphism of `Finset sites` preserves atoms (singletons) and is
    therefore induced by a permutation of the sites. -/
def ofSitePerm {sites : Type*} {N : LocalNet (Finset sites)} (σ : sites ≃ sites)
    (β : ∀ Λ : Finset sites, N.algebra Λ ≃⋆ₐ[ℂ] N.algebra (Λ.map σ.toEmbedding))
    (β_incl : ∀ {Λ Λ' : Finset sites} (h : Λ ⊆ Λ') (x : N.algebra Λ),
      β Λ' (N.incl h x) = N.incl (Finset.map_subset_map.mpr h) (β Λ x)) :
    N.Covariance where
  σ := { toEquiv := σ.finsetCongr, map_rel_iff' := Finset.map_subset_map }
  map_orthogonal_iff _ _ := Finset.disjoint_map _
  β := β
  β_incl h x := β_incl h x

/-! #### Every lattice covariance comes from a site permutation

An order automorphism of `Finset sites` maps atoms to atoms, and the atoms of `Finset sites` are
exactly the singletons; so it is determined by a permutation of the sites, and the covariance it
belongs to is `ofSitePerm` of that permutation.
-/

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

variable {sites : Type*} {N : LocalNet (Finset sites)}

/-- **The region automorphism of a lattice covariance is induced by a site permutation.** -/
theorem exists_sitePerm (a : N.Covariance) :
    ∃ σ : sites ≃ sites, ∀ Λ : Finset sites, a.σ Λ = Λ.map σ.toEmbedding :=
  ⟨sitePerm a.σ, map_sitePerm a.σ⟩

/-- **Every covariance of a lattice net arises from a site permutation** — the converse of
    `ofSitePerm`, and the statement its docstring advertises. The region automorphism is the image
    map of a site permutation `σ` (`exists_sitePerm`); transporting the local `*`-isomorphisms
    along that identification of regions produces the `β` data, whose naturality is `a`'s own
    naturality composed with `incl_algebraCongr`. -/
theorem exists_eq_ofSitePerm (a : N.Covariance) :
    ∃ (σ : sites ≃ sites)
      (β : ∀ Λ : Finset sites, N.algebra Λ ≃⋆ₐ[ℂ] N.algebra (Λ.map σ.toEmbedding))
      (β_incl : ∀ {Λ Λ' : Finset sites} (h : Λ ⊆ Λ') (x : N.algebra Λ),
        β Λ' (N.incl h x) = N.incl (Finset.map_subset_map.mpr h) (β Λ x)),
      a = Covariance.ofSitePerm σ β β_incl := by
  obtain ⟨σ, hσ⟩ := a.exists_sitePerm
  refine ⟨σ, fun Λ => (a.β Λ).trans (N.algebraCongr (hσ Λ)), ?_, ?_⟩
  · intro Λ Λ' h x
    simp only [StarAlgEquiv.trans_apply]
    rw [a.β_incl h]
    exact N.incl_algebraCongr (hσ Λ) (hσ Λ') (a.σ.monotone h) (Finset.map_subset_map.mpr h) _
  · exact Covariance.ext (OrderIso.ext (funext hσ)) fun Λ x e => rfl

end Covariance

end LocalNet
