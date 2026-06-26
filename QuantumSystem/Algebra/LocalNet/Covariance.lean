module

public import QuantumSystem.Algebra.LocalNet.QuasiLocal

/-!
# Covariance data and action for a local net

A **covariance** of a local net is a site permutation `σ` together with, for every finite region
`Λ`, a `*`-isomorphism `β_Λ : 𝔄(Λ) ≃⋆ₐ[ℂ] 𝔄(σΛ)` of local algebras that is natural with respect
to the isotony embeddings. The naturality field `β_incl` is the AQFT covariance axiom
`β(𝔄(Λ)) = 𝔄(σΛ)` compatibly with inclusions (Naaijkens 2012 §3.2, Verch 2025 §1.2).

Such covariance data acts on the **algebra of local observables** by
`β_a ⟦⟨Λ, X⟩⟧ = ⟦⟨σΛ, β_Λ X⟩⟧`. The per-region `*`-isomorphisms assemble into a
`*`-endomorphism `quasiLocalCovariance` of the quasi-local algebra. This action is functorial in the
covariance group, `ℂ`-linear and `*`-preserving, hence a `*`-automorphism; for a `Faithful` net it
is isometric and extends to a `*`-automorphism of the quasi-local C⋆-algebra.

A **covariance** of a `SiteIndexSystem` is a permutation `σ` of the sites together with, for each
site, an equivalence `localIdx s ≃ localIdx (σ s)` matching the local dimensions. Such data induces
a `*`-isomorphism `β : 𝔄(Λ) ≃⋆ₐ[ℂ] 𝔄(σ Λ)` (`localCovariance`), assembling into an abstract
`LocalNet.Covariance` of the generated net (`toLocalNetCovariance`) and hence inheriting the
action above.
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

/-! ### The induced covariance action -/

/-- The **covariance action** `β_a ⟦⟨Λ, X⟩⟧ = ⟦⟨σΛ, β_Λ X⟩⟧` of a covariance on the algebra of local
    observables, as a ring homomorphism. Well-defined by naturality (`β_incl`). -/
noncomputable def quasiLocalCovariance : N.quasiLocalAlgebra →+* N.quasiLocalAlgebra :=
  DirectLimit.Ring.lift N.algebra (fun _ _ h => N.incl h) N.quasiLocalAlgebra
    (fun Λ => (N.ιLocal (a.region Λ)).comp (a.β Λ).toAlgEquiv.toAlgHom.toRingHom)
    (fun Λ Λ' h X => by
      change N.ιLocal (a.region Λ') (a.β Λ' (N.incl h X)) = N.ιLocal (a.region Λ) (a.β Λ X)
      rw [a.β_incl h]
      exact N.ιLocal_incl _ _)

@[simp] theorem quasiLocalCovariance_mk {Λ : Finset sites} (X : N.algebra Λ) :
  a.quasiLocalCovariance (⟦⟨Λ, X⟩⟧ : N.quasiLocalAlgebra) = ⟦⟨a.region Λ, a.β Λ X⟩⟧ :=
  rfl

/-- The covariance action of the identity covariance is the identity: `β_{id} = id`. -/
@[simp] theorem quasiLocalCovariance_id :
  (Covariance.id N).quasiLocalCovariance = RingHom.id N.quasiLocalAlgebra := by
  refine RingHom.ext fun z => ?_
  induction z using DirectLimit.induction with
  | _ Λ X => rw [quasiLocalCovariance_mk, RingHom.id_apply]; exact N.ιLocal_algebraCongr _ X

/-- **Functoriality of the covariance action**: composing covariances composes their actions,
    `β_{a∘b} = β_a ∘ β_b`. -/
@[simp] theorem quasiLocalCovariance_comp (a b : N.Covariance) :
  (a.comp b).quasiLocalCovariance = a.quasiLocalCovariance.comp b.quasiLocalCovariance := by
  refine RingHom.ext fun z => ?_
  induction z using DirectLimit.induction with
  | _ Λ X =>
    simp only [RingHom.comp_apply, quasiLocalCovariance_mk]
    exact N.ιLocal_algebraCongr _ _

/-- The covariance action sends the unit covariance to the identity: `β_1 = id`. -/
@[simp] theorem quasiLocalCovariance_one :
    (1 : N.Covariance).quasiLocalCovariance = RingHom.id N.quasiLocalAlgebra := by
  rw [one_def, quasiLocalCovariance_id]

/-- The covariance action is multiplicative: `β_{a·b} = β_a ∘ β_b`. -/
theorem quasiLocalCovariance_mul (a b : N.Covariance) :
    (a * b).quasiLocalCovariance = a.quasiLocalCovariance.comp b.quasiLocalCovariance := by
  rw [mul_def, quasiLocalCovariance_comp]

/-! #### The covariance action as a `*`-automorphism -/

/-- The covariance action is `ℂ`-linear: `β_a (c • z) = c • β_a z`, since each `β` is. -/
theorem quasiLocalCovariance_smul (c : ℂ) (z : N.quasiLocalAlgebra) :
  a.quasiLocalCovariance (c • z) = c • a.quasiLocalCovariance z := by
  induction z using DirectLimit.induction with
  | _ Λ X =>
    rw [DirectLimit.smul_def, quasiLocalCovariance_mk, quasiLocalCovariance_mk, DirectLimit.smul_def,
      map_smul]
    rfl

/-- The covariance action preserves the involution: `β_a (star z) = star (β_a z)`, since each `β`
    is a `*`-isomorphism. -/
theorem quasiLocalCovariance_star (z : N.quasiLocalAlgebra) :
  a.quasiLocalCovariance (star z) = star (a.quasiLocalCovariance z) := by
  induction z using DirectLimit.induction with
  | _ Λ X =>
    rw [star_mk, quasiLocalCovariance_mk, quasiLocalCovariance_mk, star_mk, map_star]
    rfl

/-- The covariance action as a `*`-algebra automorphism of the algebra of local observables, with
  the action of the inverse covariance `a⁻¹` as its inverse. -/
noncomputable def quasiLocalCovarianceEquiv :
    N.quasiLocalAlgebra ≃⋆ₐ[ℂ] N.quasiLocalAlgebra where
  toFun := a.quasiLocalCovariance
  invFun := a⁻¹.quasiLocalCovariance
  left_inv z := by
    rw [← RingHom.comp_apply, ← quasiLocalCovariance_mul, inv_mul_cancel, quasiLocalCovariance_one,
      RingHom.id_apply]
  right_inv z := by
    rw [← RingHom.comp_apply, ← quasiLocalCovariance_mul, mul_inv_cancel, quasiLocalCovariance_one,
      RingHom.id_apply]
  map_mul' := map_mul a.quasiLocalCovariance
  map_add' := map_add a.quasiLocalCovariance
  map_smul' := a.quasiLocalCovariance_smul
  map_star' := a.quasiLocalCovariance_star

@[simp] theorem quasiLocalCovarianceEquiv_apply (z : N.quasiLocalAlgebra) :
    a.quasiLocalCovarianceEquiv z = a.quasiLocalCovariance z := rfl

@[simp] theorem quasiLocalCovarianceEquiv_symm_apply (z : N.quasiLocalAlgebra) :
    a.quasiLocalCovarianceEquiv.symm z = a⁻¹.quasiLocalCovariance z := rfl

/-- A covariance of the net acts on the algebra of local observables by `*`-algebra automorphisms,
    assembled as a group homomorphism into the `*`-automorphism group. -/
noncomputable def quasiLocalCovarianceHom :
    N.Covariance →* (N.quasiLocalAlgebra ≃⋆ₐ[ℂ] N.quasiLocalAlgebra) where
  toFun a := a.quasiLocalCovarianceEquiv
  map_one' := by
    ext z
    simp only [quasiLocalCovarianceEquiv_apply, quasiLocalCovariance_one, RingHom.id_apply,
      StarAlgEquiv.one_apply]
  map_mul' a b := by
    ext z
    simp only [quasiLocalCovarianceEquiv_apply, quasiLocalCovariance_mul, RingHom.comp_apply,
      StarAlgEquiv.mul_apply]

@[simp] theorem quasiLocalCovarianceHom_apply (z : N.quasiLocalAlgebra) :
    quasiLocalCovarianceHom a z = a.quasiLocalCovariance z := rfl

/-! #### The covariance automorphism of the quasi-local C⋆-algebra -/

section CStarCovariance

variable [N.Faithful]

/-- The covariance action is **isometric** on the algebra of local observables: each `β` is a
    `*`-isomorphism of C⋆-algebras, hence norm-preserving. -/
theorem quasiLocalCovariance_norm (z : N.quasiLocalAlgebra) :
  ‖a.quasiLocalCovariance z‖ = ‖z‖ := by
  induction z using DirectLimit.induction with
  | _ Λ X =>
    rw [quasiLocalCovariance_mk, norm_mk, norm_mk]
    exact StarAlgEquiv.norm_map _ X

/-- The covariance automorphism of the algebra of local observables is uniformly continuous (it is
    an isometry), so it extends to the C⋆-completion. -/
theorem quasiLocalCovarianceEquiv_uniformContinuous :
    UniformContinuous a.quasiLocalCovarianceEquiv :=
  (AddMonoidHomClass.isometry_of_norm _ (fun z => by
    rw [quasiLocalCovarianceEquiv_apply]; exact a.quasiLocalCovariance_norm z)).uniformContinuous

/-- The inverse covariance automorphism is uniformly continuous as well (the action of `a⁻¹` is
    also an isometry). -/
theorem quasiLocalCovarianceEquiv_symm_uniformContinuous :
    UniformContinuous a.quasiLocalCovarianceEquiv.symm := by
  have h : ∀ z, ‖a.quasiLocalCovarianceEquiv.symm z‖ = ‖z‖ := fun z => by
    rw [quasiLocalCovarianceEquiv_symm_apply]; exact a⁻¹.quasiLocalCovariance_norm z
  exact (AddMonoidHomClass.isometry_of_norm _ h).uniformContinuous

/-- The covariance automorphism of the quasi-local C⋆-algebra: the continuous extension of
    `quasiLocalCovarianceEquiv` to the completion. -/
noncomputable def quasiLocalCStarCovarianceEquiv :
    N.quasiLocalCStarAlgebra ≃⋆ₐ[ℂ] N.quasiLocalCStarAlgebra :=
  UniformSpace.Completion.mapStarAlgEquiv a.quasiLocalCovarianceEquiv
    a.quasiLocalCovarianceEquiv_uniformContinuous
    a.quasiLocalCovarianceEquiv_symm_uniformContinuous

@[simp] theorem quasiLocalCStarCovarianceEquiv_coe (z : N.quasiLocalAlgebra) :
    a.quasiLocalCStarCovarianceEquiv (↑z : N.quasiLocalCStarAlgebra) =
      ↑(a.quasiLocalCovariance z) :=
  UniformSpace.Completion.mapStarAlgEquiv_coe _ _ _ z

theorem quasiLocalCStarCovarianceEquiv_continuous :
    Continuous (⇑a.quasiLocalCStarCovarianceEquiv) :=
  UniformSpace.Completion.continuous_map

/-- A covariance of a faithful net acts on the quasi-local C⋆-algebra by `*`-automorphisms,
    assembled as a group homomorphism into the `*`-automorphism group. -/
noncomputable def quasiLocalCStarCovarianceHom :
    N.Covariance →* (N.quasiLocalCStarAlgebra ≃⋆ₐ[ℂ] N.quasiLocalCStarAlgebra) where
  toFun a := a.quasiLocalCStarCovarianceEquiv
  map_one' := by
    refine StarAlgEquiv.ext fun z => ?_
    rw [StarAlgEquiv.one_apply]
    refine UniformSpace.Completion.induction_on z
      (isClosed_eq (1 : N.Covariance).quasiLocalCStarCovarianceEquiv_continuous
        continuous_id) ?_
    intro w
    simp only [quasiLocalCStarCovarianceEquiv_coe, quasiLocalCovariance_one, RingHom.id_apply]
  map_mul' a b := by
    refine StarAlgEquiv.ext fun z => ?_
    rw [StarAlgEquiv.mul_apply]
    refine UniformSpace.Completion.induction_on z
      (isClosed_eq (a * b).quasiLocalCStarCovarianceEquiv_continuous
        (a.quasiLocalCStarCovarianceEquiv_continuous.comp
          b.quasiLocalCStarCovarianceEquiv_continuous)) ?_
    intro w
    simp only [quasiLocalCStarCovarianceEquiv_coe, quasiLocalCovariance_mul, RingHom.comp_apply]

@[simp] theorem quasiLocalCStarCovarianceHom_apply
    (z : N.quasiLocalCStarAlgebra) :
  quasiLocalCStarCovarianceHom a z = a.quasiLocalCStarCovarianceEquiv z := rfl

end CStarCovariance

end Covariance

end LocalNet

namespace SiteIndexSystem

/-- Pointwise value of the complement projection of `combineIdx.symm` (holds by `rfl`). -/
@[simp] theorem combineIdx_symm_snd_apply {L : SiteIndexSystem} {Λ Λ_total : Finset L.sites}
    (h : Λ ⊆ Λ_total) (f : L.regionIdx Λ_total) (w : ↥(Λ_total \ Λ)) :
    ((L.combineIdx h).symm f).2 w = f ⟨w.val, (Finset.mem_sdiff.mp w.property).1⟩ := rfl

/-- A covariance datum for a site-index system: a site permutation together with
  dimension-matching equivalences on the local index types. -/
structure Covariance (L : SiteIndexSystem) where
  /-- The underlying permutation of the sites. -/
  σ : L.sites ≃ L.sites
  /-- Dimension-matching equivalence of the local index type at each site. -/
  idx : ∀ s, L.localIdx s ≃ L.localIdx (σ s)

namespace Covariance

variable {L : SiteIndexSystem} (a : L.Covariance)

/-- The image of a region under a covariance. -/
def region (Λ : Finset L.sites) : Finset L.sites := Λ.map a.σ.toEmbedding

variable (L) in
/-- The identity covariance. -/
def id : L.Covariance where
  σ := Equiv.refl _
  idx _ := Equiv.refl _

/-- Composition of covariances: apply `b`, then `a`. The per-site equivalences compose, with the
    intermediate site type aligning definitionally. -/
def comp (a b : L.Covariance) : L.Covariance where
  σ := b.σ.trans a.σ
  idx s := (b.idx s).trans (a.idx (b.σ s))

@[simp] theorem region_id (Λ : Finset L.sites) : (Covariance.id L).region Λ = Λ := by
  simp [region, Covariance.id]

@[simp] theorem region_comp (a b : L.Covariance) (Λ : Finset L.sites) :
    (a.comp b).region Λ = a.region (b.region Λ) := by
  simp [region, comp, Finset.map_map, Equiv.trans_toEmbedding]

/-- Equivalence of region index types induced by the site permutation and the per-site dimension
  equivalences. -/
def regionIdxEquiv (Λ : Finset L.sites) :
    L.regionIdx Λ ≃ L.regionIdx (a.region Λ) :=
  Equiv.piCongr
    (Equiv.subtypeEquiv a.σ (fun _ => (Finset.mem_map' a.σ.toEmbedding).symm))
    (fun s => a.idx s.val)

/-- The **covariance `*`-isomorphism** `β_a : 𝔄(Λ) ≃⋆ₐ[ℂ] 𝔄(a Λ)`, obtained by reindexing the
    matrix algebra along `regionIdxEquiv`. Realises `β_a(𝔄(Λ)) = 𝔄(a Λ)`. -/
noncomputable def localCovariance (Λ : Finset L.sites) :
    L.localAlgebra Λ ≃⋆ₐ[ℂ] L.localAlgebra (a.region Λ) :=
  StarAlgEquiv.ofAlgEquiv (Matrix.reindexAlgEquiv ℂ ℂ (a.regionIdxEquiv Λ))
    (fun X => by
      simp only [Matrix.reindexAlgEquiv_apply, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_reindex])

@[simp] theorem localCovariance_apply (Λ : Finset L.sites) (X : L.localAlgebra Λ) :
  a.localCovariance Λ X = Matrix.reindex (a.regionIdxEquiv Λ) (a.regionIdxEquiv Λ) X :=
  rfl

/-- The `Λ`-coordinate of decomposing a transported index equals the corresponding transported
  `aΛ`-coordinate: `regionIdxEquiv` commutes with the isotony split `combineIdx`. Holds
  definitionally. -/
private theorem regionIdxEquiv_symm_combineIdx_fst {Λ Λ' : Finset L.sites} (h : Λ ⊆ Λ')
    (t : L.regionIdx (a.region Λ')) :
  ((L.combineIdx h).symm ((a.regionIdxEquiv Λ').symm t)).1 =
    (a.regionIdxEquiv Λ).symm ((L.combineIdx (Finset.map_subset_map.mpr h)).symm t).1 := by
  funext u
  rfl

/-- **Covariance / naturality**: the covariance `*`-isomorphism intertwines the isotony
    embeddings, so `β_a` is an automorphism of the *net* — `β_a(𝔄(Λ)) = 𝔄(a Λ)` compatibly with
    inclusions (Naaijkens 2012 §3.2 covariance axiom). -/
theorem localCovariance_includeAlgebra {Λ Λ' : Finset L.sites} (h : Λ ⊆ Λ')
    (X : L.localAlgebra Λ) :
    a.localCovariance Λ' (L.includeAlgebra h X) =
      L.includeAlgebra (Finset.map_subset_map.mpr h) (a.localCovariance Λ X) := by
  ext s s'
  simp only [localCovariance_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    includeAlgebra_apply]
  rw [a.regionIdxEquiv_symm_combineIdx_fst h s, a.regionIdxEquiv_symm_combineIdx_fst h s']
  have key2 : (((L.combineIdx h).symm ((a.regionIdxEquiv Λ').symm s)).2 =
        ((L.combineIdx h).symm ((a.regionIdxEquiv Λ').symm s')).2)
      ↔ (((L.combineIdx (Finset.map_subset_map.mpr h)).symm s).2 =
        ((L.combineIdx (Finset.map_subset_map.mpr h)).symm s').2) := by
    constructor
    · intro H
      funext v
      obtain ⟨vv, hvv⟩ := v
      have hv := Finset.mem_sdiff.mp hvv
      have hΛ' : a.σ.symm vv ∈ Λ' := Finset.mem_map_equiv.mp hv.1
      have hΛ : a.σ.symm vv ∉ Λ := fun hc => hv.2 (Finset.mem_map_equiv.mpr hc)
      have hcong := congrFun H ⟨a.σ.symm vv, Finset.mem_sdiff.mpr ⟨hΛ', hΛ⟩⟩
      simp only [combineIdx_symm_snd_apply, regionIdxEquiv, Equiv.piCongr_symm_apply,
        Equiv.subtypeEquiv_apply, EmbeddingLike.apply_eq_iff_eq] at hcong
      change s ⟨vv, (Finset.mem_sdiff.mp hvv).1⟩ = s' ⟨vv, (Finset.mem_sdiff.mp hvv).1⟩
      convert hcong using 2 <;>
        first
          | exact (a.σ.apply_symm_apply vv).symm
          | exact Subtype.ext (a.σ.apply_symm_apply vv).symm
    · intro H
      funext w
      have hw := Finset.mem_sdiff.mp w.property
      have hv : a.σ w.val ∈ a.region Λ' \ a.region Λ := Finset.mem_sdiff.mpr
        ⟨Finset.mem_map' _ |>.mpr hw.1, fun hc => hw.2 (Finset.mem_map' _ |>.mp hc)⟩
      have hcong := congrFun H ⟨a.σ w.val, hv⟩
      simpa [combineIdx_symm_snd_apply, regionIdxEquiv, Equiv.piCongr_symm_apply,
        Equiv.subtypeEquiv_apply, Equiv.symm_apply_apply,
        EmbeddingLike.apply_eq_iff_eq] using hcong
  by_cases hc : ((L.combineIdx (Finset.map_subset_map.mpr h)).symm s).2 =
      ((L.combineIdx (Finset.map_subset_map.mpr h)).symm s').2
  · rw [if_pos (key2.mpr hc), if_pos hc]
  · rw [if_neg (fun hcc => hc (key2.mp hcc)), if_neg hc]

/-! ### Covariance action on the quasi-local algebra

The per-region covariance `*`-isomorphisms, being natural with respect to isotony
(`localCovariance_includeAlgebra`), assemble a covariance `toLocalNetCovariance` of the abstract net
`toLocalNet`. Its covariance action `β_a ⟦⟨Λ, X⟩⟧ = ⟦⟨a Λ, β_a X⟩⟧` on the algebra of local
observables is therefore inherited from the net-level `LocalNet.Covariance.quasiLocalCovariance`. -/

/-- The covariance of the generated local net `toLocalNet` induced by a lattice covariance: the same
    site permutation, with the local `*`-isomorphisms `localCovariance` as its covariance maps and
    `localCovariance_includeAlgebra` as the isotony naturality. This exhibits the concrete
    covariance as an instance of the abstract `LocalNet.Covariance`. -/
noncomputable def toLocalNetCovariance : L.toLocalNet.Covariance where
  σ := a.σ
  β := a.localCovariance
  β_incl h x := a.localCovariance_includeAlgebra h x

/-- The action of a covariance on the algebra of local observables, as a ring homomorphism:
    `β_a ⟦⟨Λ, X⟩⟧ = ⟦⟨a Λ, β_a X⟩⟧`. Inherited from the abstract net-level covariance action
    `LocalNet.Covariance.quasiLocalCovariance` on `toLocalNet`. -/
noncomputable def quasiLocalCovariance : L.quasiLocalAlgebra →+* L.quasiLocalAlgebra :=
  a.toLocalNetCovariance.quasiLocalCovariance

@[simp] theorem quasiLocalCovariance_mk {Λ : Finset L.sites} (X : L.localAlgebra Λ) :
    a.quasiLocalCovariance (⟦⟨Λ, X⟩⟧ : L.quasiLocalAlgebra) =
      ⟦⟨a.region Λ, a.localCovariance Λ X⟩⟧ :=
  rfl

end Covariance

end SiteIndexSystem
