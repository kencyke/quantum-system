module

public import QuantumSystem.Algebra.LocalNet.QuasiLocal

/-!
# Covariance of the local net

A **symmetry** of a `LocalNet` is a permutation `σ` of the sites together with, for each site,
an equivalence `localIdx s ≃ localIdx (σ s)` matching the local dimensions. Such data induces a
`*`-isomorphism `β : 𝔄(Λ) ≃⋆ₐ[ℂ] 𝔄(σ Λ)` between the local algebras of a region and its image,
realising the AQFT covariance axiom `β(𝔄(Λ)) = 𝔄(σ Λ)` (Naaijkens 2012 §3.2, Verch 2025 §1.2).

Symmetries compose (identity and composition below), so any group acting on the sites with
matching local dimensions acts on the net by `*`-isomorphisms. The per-region isomorphisms are
natural with respect to isotony (`relabelAlgebra_includeAlgebra`), so they assemble into a
`*`-endomorphism `quasiLocalRelabel` of the quasi-local algebra (the covariance action).
-/

@[expose] public section

namespace LocalNet

/-- Pointwise value of the complement projection of `combineIdx.symm` (holds by `rfl`). -/
@[simp] theorem combineIdx_symm_snd_apply {L : LocalNet} {Λ Λ_total : Finset L.sites}
    (h : Λ ⊆ Λ_total) (f : L.regionIdx Λ_total) (w : ↥(Λ_total \ Λ)) :
    ((L.combineIdx h).symm f).2 w = f ⟨w.val, (Finset.mem_sdiff.mp w.property).1⟩ := rfl

/-- A symmetry of a local net: a site permutation together with dimension-matching equivalences
    on the local index types. A group acting on the net is a homomorphism into these. -/
structure Symmetry (L : LocalNet) where
  /-- The underlying permutation of the sites. -/
  σ : L.sites ≃ L.sites
  /-- Dimension matching: relabel the local index type at each site. -/
  idx : ∀ s, L.localIdx s ≃ L.localIdx (σ s)

namespace Symmetry

variable {L : LocalNet} (a : L.Symmetry)

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

The per-region symmetry `*`-isomorphisms, being natural with respect to isotony, assemble into
a `*`-endomorphism of the algebra of local observables `β_a ⟦⟨Λ, X⟩⟧ = ⟦⟨a Λ, β_a X⟩⟧`.
Well-definedness is exactly `relabelAlgebra_includeAlgebra`. This is the AQFT covariance action
on the (pre-completion) quasi-local algebra. -/

/-- The action of a symmetry on the algebra of local observables, as a ring homomorphism:
    `β_a ⟦⟨Λ, X⟩⟧ = ⟦⟨a Λ, relabel X⟩⟧`. Well-defined by net-covariance
    (`relabelAlgebra_includeAlgebra`). -/
noncomputable def quasiLocalRelabel : L.quasiLocalAlgebra →+* L.quasiLocalAlgebra :=
  DirectLimit.Ring.lift (fun Λ : Finset L.sites => L.localAlgebra Λ)
    (fun _ _ h => L.includeAlgebra h) L.quasiLocalAlgebra
    (fun Λ => (L.ιLocal (a.region Λ)).comp
      ((a.relabelAlgebra Λ).toAlgEquiv.toAlgHom.toRingHom))
    (fun Λ Λ' h X => by
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        AlgEquiv.coe_algHom, StarAlgEquiv.coe_toAlgEquiv, a.relabelAlgebra_includeAlgebra h]
      exact L.ιLocal_includeAlgebra _ _)

@[simp] theorem quasiLocalRelabel_mk {Λ : Finset L.sites} (X : L.localAlgebra Λ) :
    a.quasiLocalRelabel (⟦⟨Λ, X⟩⟧ : L.quasiLocalAlgebra) = ⟦⟨a.region Λ, a.relabelAlgebra Λ X⟩⟧ :=
  rfl

end Symmetry

end LocalNet
