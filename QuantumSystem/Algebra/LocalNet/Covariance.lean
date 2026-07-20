module

public import QuantumSystem.Algebra.LocalNet.Net

/-!
# Covariance data for a local net

A **covariance** of a local net over a causal index set `K` is an order automorphism `σ : K ≃o K`
of the regions preserving causal orthogonality, together with, for every region `O`, a
`*`-isomorphism `β_O : 𝔄(O) ≃⋆ₐ[ℂ] 𝔄(σO)` of local algebras that is natural with respect to the
isotony embeddings. The naturality field `β_incl` is the AQFT covariance axiom
`β(𝔄(O)) = 𝔄(σO)` compatibly with inclusions (Naaijkens 2012 §3.2, Verch 2025 §1.2). These
covariances form a `Group` under composition (`Covariance.id`, `Covariance.comp`,
`Covariance.inv`). For lattice nets (`K = Finset sites`) a covariance is induced by a site
permutation via `Covariance.ofSitePerm` — and every covariance of a lattice net arises this way,
since an order automorphism of `Finset sites` is determined by its action on singletons.

This file isolates the abstract covariance *data* and its group structure. Its *action* on the
quasi-local algebra — assembling the per-region `*`-isomorphisms into a `*`-automorphism
`quasiLocalCovariance` and (for a `Faithful` net) its continuous extension to the quasi-local
C⋆-algebra — is built in `LocalNet.QuasiLocalAlgebra`. A symmetry group `G` acts on the net by
supplying a group homomorphism `G →* N.Covariance` (whose `σ`-component is the geometric action
`G → K ≃o K`); composing it with `quasiLocalCovarianceHom` — or, for a `Faithful` net,
`quasiLocalCStarCovarianceHom` — yields the automorphic action of `G` on the (quasi-local) algebra.
-/

@[expose] public section

namespace LocalNet

open scoped CausalOrthogonality

variable {K : Type*} [PartialOrder K] [CausalOrthogonality K] (N : LocalNet K)

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

/-- The image `σO` of a region under the covariance. -/
def region (O : K) : K := a.σ O

/-- **Extensionality** for covariances: two covariances with the same region automorphism and the
    same local `*`-isomorphisms (compared along the induced region equality) are equal. The
    remaining fields are propositions, hence irrelevant. -/
@[ext (iff := false)] lemma ext {s t : N.Covariance} (hσ : s.σ = t.σ)
    (hβ : ∀ (O : K) (x : N.algebra O) (e : s.region O = t.region O),
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

@[simp] lemma id_β_apply (O : K) (x : N.algebra O) : (Covariance.id N).β O x = x :=
  rfl

@[simp] lemma comp_β_apply (a b : N.Covariance) (O : K) (x : N.algebra O) :
    (a.comp b).β O x = a.β (b.σ O) (b.β O x) :=
  rfl

@[simp] lemma inv_β_apply (a : N.Covariance) (O : K) (x : N.algebra O) :
    (Covariance.inv a).β O x = (a.β (a.σ.symm O)).symm
      (N.algebraCongr (a.σ.apply_symm_apply O).symm x) :=
  rfl

@[simp] lemma region_id (O : K) : (Covariance.id N).region O = O :=
  rfl

@[simp] lemma region_comp (a b : N.Covariance) (O : K) :
    (a.comp b).region O = a.region (b.region O) :=
  rfl

lemma id_comp (a : N.Covariance) : (Covariance.id N).comp a = a := by
  refine Covariance.ext ?_ fun O x e => ?_
  · exact OrderIso.ext rfl
  · exact N.algebraCongr_self e _

lemma comp_id (a : N.Covariance) : a.comp (Covariance.id N) = a := by
  refine Covariance.ext ?_ fun O x e => ?_
  · exact OrderIso.ext rfl
  · exact N.algebraCongr_self e _

lemma comp_assoc (a b c : N.Covariance) : (a.comp b).comp c = a.comp (b.comp c) := by
  refine Covariance.ext ?_ fun O x e => ?_
  · exact OrderIso.ext rfl
  · exact N.algebraCongr_self e _

lemma inv_comp (a : N.Covariance) : (Covariance.inv a).comp a = Covariance.id N := by
  refine Covariance.ext ?_ fun O x e => ?_
  · exact OrderIso.ext (funext fun O => a.σ.symm_apply_apply O)
  · rw [algebraCongr_eq_iff]
    simp only [comp_β_apply, inv_β_apply, id_β_apply]
    erw [← a.β_algebraCongr, StarAlgEquiv.symm_apply_apply]
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
    site-permutation covariances of spin-system nets (Naaijkens 2012 §3.2); conversely, every
    covariance of a lattice net arises this way, since an order automorphism of `Finset sites`
    preserves atoms (singletons) and is therefore induced by a permutation of the sites. -/
def ofSitePerm {sites : Type*} {N : LocalNet (Finset sites)} (σ : sites ≃ sites)
    (β : ∀ Λ : Finset sites, N.algebra Λ ≃⋆ₐ[ℂ] N.algebra (Λ.map σ.toEmbedding))
    (β_incl : ∀ {Λ Λ' : Finset sites} (h : Λ ⊆ Λ') (x : N.algebra Λ),
      β Λ' (N.incl h x) = N.incl (Finset.map_subset_map.mpr h) (β Λ x)) :
    N.Covariance where
  σ := { toEquiv := σ.finsetCongr, map_rel_iff' := Finset.map_subset_map }
  map_orthogonal_iff _ _ := Finset.disjoint_map _
  β := β
  β_incl h x := β_incl h x

end Covariance

end LocalNet
