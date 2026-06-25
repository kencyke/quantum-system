module

public import QuantumSystem.Algebra.LocalNet.QuasiLocal
public import QuantumSystem.Algebra.LocalNet.Symmetry

/-!
# Covariance action of a local net symmetry

A symmetry of a local net (`LocalNet.Symmetry`, defined in `LocalNet.Symmetry`) acts on the
**algebra of local observables** by `β_a ⟦⟨Λ, X⟩⟧ = ⟦⟨σΛ, β_Λ X⟩⟧`. The per-region
`*`-isomorphisms are natural with respect to isotony (`β_incl`), so they assemble into a
`*`-endomorphism `quasiLocalRelabel` of the quasi-local algebra (the covariance action). This
action is functorial in the symmetry group, `ℂ`-linear and `*`-preserving, hence a
`*`-automorphism; for a `Faithful` net it is isometric and extends to a `*`-automorphism of the
quasi-local C⋆-algebra (Naaijkens 2012 §3.2, Verch 2025 §1.2).

A **symmetry** of a `SiteIndexSystem` is a permutation `σ` of the sites together with, for each
site, an equivalence `localIdx s ≃ localIdx (σ s)` matching the local dimensions. Such data induces
a `*`-isomorphism `β : 𝔄(Λ) ≃⋆ₐ[ℂ] 𝔄(σ Λ)` (`relabelAlgebra`), assembling into an abstract
`LocalNet.Symmetry` of the generated net (`toLocalNetSymmetry`) and hence inheriting the covariance
action above.
-/

@[expose] public section

namespace LocalNet

variable {sites : Type*} [DecidableEq sites] (N : LocalNet sites)

namespace Symmetry

variable {N} (a : N.Symmetry)

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

/-- The covariance action of the identity symmetry is the identity: `β_{id} = id`. -/
@[simp] theorem quasiLocalRelabel_id :
    (Symmetry.id N).quasiLocalRelabel = RingHom.id N.quasiLocalAlgebra := by
  refine RingHom.ext fun z => ?_
  induction z using DirectLimit.induction with
  | _ Λ X => rw [quasiLocalRelabel_mk, RingHom.id_apply]; exact N.ιLocal_algebraCongr _ X

/-- **Functoriality of the covariance action**: composing symmetries composes their actions,
    `β_{a∘b} = β_a ∘ β_b`. -/
@[simp] theorem quasiLocalRelabel_comp (a b : N.Symmetry) :
    (a.comp b).quasiLocalRelabel = a.quasiLocalRelabel.comp b.quasiLocalRelabel := by
  refine RingHom.ext fun z => ?_
  induction z using DirectLimit.induction with
  | _ Λ X =>
    simp only [RingHom.comp_apply, quasiLocalRelabel_mk]
    exact N.ιLocal_algebraCongr _ _

/-- The covariance action sends the unit symmetry to the identity: `β_1 = id`. -/
@[simp] theorem quasiLocalRelabel_one :
    (1 : N.Symmetry).quasiLocalRelabel = RingHom.id N.quasiLocalAlgebra := by
  rw [one_def, quasiLocalRelabel_id]

/-- The covariance action is multiplicative: `β_{a·b} = β_a ∘ β_b`. -/
theorem quasiLocalRelabel_mul (a b : N.Symmetry) :
    (a * b).quasiLocalRelabel = a.quasiLocalRelabel.comp b.quasiLocalRelabel := by
  rw [mul_def, quasiLocalRelabel_comp]

/-! #### The covariance action as a `*`-automorphism -/

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

/-- The covariance action of a symmetry as a `*`-algebra automorphism of the algebra of local
    observables, with the action of the inverse symmetry `a⁻¹` as its inverse. -/
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
    assembled as a group homomorphism into the `*`-automorphism group. -/
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

/-! #### The covariance automorphism of the quasi-local C⋆-algebra -/

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

/-- The covariance automorphism of the quasi-local C⋆-algebra: the continuous extension of
    `quasiLocalRelabelStarEquiv` to the completion. -/
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
    assembled as a group homomorphism into the `*`-automorphism group. -/
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

namespace SiteIndexSystem

/-- Pointwise value of the complement projection of `combineIdx.symm` (holds by `rfl`). -/
@[simp] theorem combineIdx_symm_snd_apply {L : SiteIndexSystem} {Λ Λ_total : Finset L.sites}
    (h : Λ ⊆ Λ_total) (f : L.regionIdx Λ_total) (w : ↥(Λ_total \ Λ)) :
    ((L.combineIdx h).symm f).2 w = f ⟨w.val, (Finset.mem_sdiff.mp w.property).1⟩ := rfl

/-- A symmetry of a local net: a site permutation together with dimension-matching equivalences
    on the local index types. A group acting on the net is a homomorphism into these. -/
structure Symmetry (L : SiteIndexSystem) where
  /-- The underlying permutation of the sites. -/
  σ : L.sites ≃ L.sites
  /-- Dimension matching: relabel the local index type at each site. -/
  idx : ∀ s, L.localIdx s ≃ L.localIdx (σ s)

namespace Symmetry

variable {L : SiteIndexSystem} (a : L.Symmetry)

/-- The image of a region under a symmetry. -/
def region (Λ : Finset L.sites) : Finset L.sites := Λ.map a.σ.toEmbedding

variable (L) in
/-- The identity symmetry. -/
def id : L.Symmetry where
  σ := Equiv.refl _
  idx _ := Equiv.refl _

/-- Composition of symmetries: apply `b`, then `a`. The per-site equivalences compose, with the
    intermediate site type aligning definitionally. -/
def comp (a b : L.Symmetry) : L.Symmetry where
  σ := b.σ.trans a.σ
  idx s := (b.idx s).trans (a.idx (b.σ s))

@[simp] theorem region_id (Λ : Finset L.sites) : (Symmetry.id L).region Λ = Λ := by
  simp [region, Symmetry.id]

@[simp] theorem region_comp (a b : L.Symmetry) (Λ : Finset L.sites) :
    (a.comp b).region Λ = a.region (b.region Λ) := by
  simp [region, comp, Finset.map_map, Equiv.trans_toEmbedding]

/-- Relabelling of region indices: transport along the site permutation and the per-site
    dimension equivalences. -/
def relabelRegionIdx (Λ : Finset L.sites) :
    L.regionIdx Λ ≃ L.regionIdx (a.region Λ) :=
  Equiv.piCongr
    (Equiv.subtypeEquiv a.σ (fun _ => (Finset.mem_map' a.σ.toEmbedding).symm))
    (fun s => a.idx s.val)

/-- The **covariance `*`-isomorphism** `β_a : 𝔄(Λ) ≃⋆ₐ[ℂ] 𝔄(a Λ)`, obtained by reindexing the
    matrix algebra along `relabelRegionIdx`. Realises `β_a(𝔄(Λ)) = 𝔄(a Λ)`. -/
noncomputable def relabelAlgebra (Λ : Finset L.sites) :
    L.localAlgebra Λ ≃⋆ₐ[ℂ] L.localAlgebra (a.region Λ) :=
  StarAlgEquiv.ofAlgEquiv (Matrix.reindexAlgEquiv ℂ ℂ (a.relabelRegionIdx Λ))
    (fun X => by
      simp only [Matrix.reindexAlgEquiv_apply, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_reindex])

@[simp] theorem relabelAlgebra_apply (Λ : Finset L.sites) (X : L.localAlgebra Λ) :
    a.relabelAlgebra Λ X = Matrix.reindex (a.relabelRegionIdx Λ) (a.relabelRegionIdx Λ) X :=
  rfl

/-- The `Λ`-coordinate of decomposing a relabelled index equals relabelling the `aΛ`-coordinate:
    `relabelRegionIdx` commutes with the isotony split `combineIdx`. Holds definitionally. -/
private theorem relabelRegionIdx_symm_combineIdx_fst {Λ Λ' : Finset L.sites} (h : Λ ⊆ Λ')
    (t : L.regionIdx (a.region Λ')) :
    ((L.combineIdx h).symm ((a.relabelRegionIdx Λ').symm t)).1 =
      (a.relabelRegionIdx Λ).symm ((L.combineIdx (Finset.map_subset_map.mpr h)).symm t).1 := by
  funext u
  rfl

/-- **Covariance / naturality**: the symmetry `*`-isomorphism intertwines the isotony
    embeddings, so `β_a` is an automorphism of the *net* — `β_a(𝔄(Λ)) = 𝔄(a Λ)` compatibly with
    inclusions (Naaijkens 2012 §3.2 covariance axiom). -/
theorem relabelAlgebra_includeAlgebra {Λ Λ' : Finset L.sites} (h : Λ ⊆ Λ')
    (X : L.localAlgebra Λ) :
    a.relabelAlgebra Λ' (L.includeAlgebra h X) =
      L.includeAlgebra (Finset.map_subset_map.mpr h) (a.relabelAlgebra Λ X) := by
  ext s s'
  simp only [relabelAlgebra_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    includeAlgebra_apply]
  rw [a.relabelRegionIdx_symm_combineIdx_fst h s, a.relabelRegionIdx_symm_combineIdx_fst h s']
  have key2 : (((L.combineIdx h).symm ((a.relabelRegionIdx Λ').symm s)).2 =
        ((L.combineIdx h).symm ((a.relabelRegionIdx Λ').symm s')).2)
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
      simp only [combineIdx_symm_snd_apply, relabelRegionIdx, Equiv.piCongr_symm_apply,
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
      simpa [combineIdx_symm_snd_apply, relabelRegionIdx, Equiv.piCongr_symm_apply,
        Equiv.subtypeEquiv_apply, Equiv.symm_apply_apply,
        EmbeddingLike.apply_eq_iff_eq] using hcong
  by_cases hc : ((L.combineIdx (Finset.map_subset_map.mpr h)).symm s).2 =
      ((L.combineIdx (Finset.map_subset_map.mpr h)).symm s').2
  · rw [if_pos (key2.mpr hc), if_pos hc]
  · rw [if_neg (fun hcc => hc (key2.mp hcc)), if_neg hc]

/-! ### Covariance action on the quasi-local algebra

The per-region symmetry `*`-isomorphisms, being natural with respect to isotony
(`relabelAlgebra_includeAlgebra`), assemble a symmetry `toLocalNetSymmetry` of the abstract net
`toLocalNet`. Its covariance action `β_a ⟦⟨Λ, X⟩⟧ = ⟦⟨a Λ, β_a X⟩⟧` on the algebra of local
observables is therefore inherited from the net-level `LocalNet.Symmetry.quasiLocalRelabel`. -/

/-- The symmetry of the generated local net `toLocalNet` induced by a lattice symmetry: the same
    site permutation, with the reindexing `*`-isomorphisms `relabelAlgebra` as its covariance maps
    and `relabelAlgebra_includeAlgebra` as the isotony naturality. This exhibits the concrete
    covariance as an instance of the abstract `LocalNet.Symmetry`. -/
noncomputable def toLocalNetSymmetry : L.toLocalNet.Symmetry where
  σ := a.σ
  β := a.relabelAlgebra
  β_incl h x := a.relabelAlgebra_includeAlgebra h x

/-- The action of a symmetry on the algebra of local observables, as a ring homomorphism:
    `β_a ⟦⟨Λ, X⟩⟧ = ⟦⟨a Λ, relabel X⟩⟧`. Inherited from the abstract net-level covariance action
    `LocalNet.Symmetry.quasiLocalRelabel` on `toLocalNet`. -/
noncomputable def quasiLocalRelabel : L.quasiLocalAlgebra →+* L.quasiLocalAlgebra :=
  a.toLocalNetSymmetry.quasiLocalRelabel

@[simp] theorem quasiLocalRelabel_mk {Λ : Finset L.sites} (X : L.localAlgebra Λ) :
    a.quasiLocalRelabel (⟦⟨Λ, X⟩⟧ : L.quasiLocalAlgebra) = ⟦⟨a.region Λ, a.relabelAlgebra Λ X⟩⟧ :=
  rfl

end Symmetry

end SiteIndexSystem
