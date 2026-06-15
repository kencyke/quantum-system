module

public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import QuantumSystem.Algebra.Sector.Net.TransportExistence
public import QuantumSystem.Algebra.Sector.Net.Transportable

/-!
# DHR locality: spacelike-separated localized sectors commute

The geometric heart of the braided structure: two **localized** sectors whose
localization cones are **spacelike-separated** (region-disjoint) commute as
endomorphisms,

```
ρ ∘ σ = σ ∘ ρ      (CategoryTheory.StarEndo.Commutes ρ σ).
```

For *inner* sectors `Ad u` this is elementary (`Net/Inner.lean`); for *general*
localized sectors it is structure-theorem content, requiring strong **Haag
duality** (to control the spread of support under an endomorphism) and **net
additivity** (to reduce to single-site generators).

The proof has four steps, carried out natively on `sectorCat L Ω` objects:

* `sectorEndo_apply_mem_localConeSubalg` — *support spreading*: `θ(a)` for a
  finite-region `a` lands in `𝔄(Λa ∪ Λθ)` (Haag-duality centralizer argument, the
  single-endomorphism shadow of `intertwiningOp_mem_quasiLocal`);
* `commutes_apply_of_single_site` — the commutation on a single-site generator,
  by separating which cone the site avoids;
* `commutes_eqOn_adjoin` — the two composites agree on the single-site-generated
  `*`-subalgebra (`StarAlgHom.adjoin_le_equalizer`);
* `commutes_of_separated` — the full commutation, by density (net additivity) and
  continuity of the composites.

This discharges the `Commutes` hypothesis of the statistics operator from geometry
(spacelike separation) alone — the key input for the braided structure on the DHR
sector category.

## References

* Doplicher, Haag, Roberts, *Local observables and particle statistics I*,
  Comm. Math. Phys. 23 (1971), §3.
* Roberts, *Local cohomology and superselection structure*, Comm. Math. Phys. 51 (1976).
* Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §3–4.
-/

@[expose] public section

open scoped LocalNetLike

/-- A non-unital `*`-homomorphism between (non-unital) C\*-algebras is continuous
(it is contractive, `NonUnitalStarAlgHom.norm_apply_le`).  Stated abstractly so the
`ContinuousMapClass`/bound synthesis runs against clean instances rather than the
expensive `↥(quasiLocal L Ω)` structure at the use site. -/
lemma nonUnitalStarAlgHom_continuous {A B : Type*}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] (φ : A →⋆ₙₐ[ℂ] B) :
    Continuous ⇑φ :=
  AddMonoidHomClass.continuous_of_bound φ 1 fun a => by
    rw [one_mul]; exact NonUnitalStarAlgHom.norm_apply_le φ a

namespace LocalNetLike

open CategoryTheory CategoryTheory.StarEndo CategoryTheory.MonoidalCategory

variable {L : Type*} [DecidableEq L] [LocalNetLike L]
  {Ω : (s : L) → LocalNetLike.localIdx (L := L) s}

/-- **Support spreading.**  For a localized sector `θ` (localized in `Λθ`) and an
operator `a` localized in a finite region `Λa`, the image `θ(a)` is localized in
the cone `Λa ∪ Λθ`.  Proof: `θ(a)` centralises every operator localised outside
`Λa ∪ Λθ` (such operators are fixed by `θ` and commute with `a`), and strong Haag
duality identifies that centralizer with `𝔄(Λa ∪ Λθ)`. -/
lemma sectorEndo_apply_mem_localConeSubalg (hHaag : HaagDuality L Ω)
    {θ : sectorCat L Ω} {Λθ : Cone L} (hθ : IsLocalizedIn Λθ θ)
    {Λa : Finset L} {a : ↥(quasiLocal L Ω)} (ha : a.val ∈ localSubalgebra (Ω := Ω) Λa) :
    (θ.endo a).val ∈ localConeSubalg L Ω { region := (↑Λa : Set L) ∪ Λθ.region } := by
  set C : Cone L := { region := (↑Λa : Set L) ∪ Λθ.region } with hC
  have h_local_le_centralizer :
      ∀ (Λt : Finset L), Disjoint (↑Λt : Set L) C.region →
        localSubalgebra (Ω := Ω) Λt ≤ StarSubalgebra.centralizer ℂ {(θ.endo a).val} := by
    intro Λt hd
    have hd_a : Disjoint (↑Λt : Set L) (↑Λa : Set L) := hd.mono_right Set.subset_union_left
    have hd_aF : Disjoint Λa Λt := (Finset.disjoint_coe.mp hd_a).symm
    have hd_θ : Disjoint (↑Λt : Set L) Λθ.region := hd.mono_right Set.subset_union_right
    intro T hT
    rw [StarSubalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    have hT_qL : T ∈ quasiLocal L Ω := localSubalgebra_le_quasiLocal L Ω Λt hT
    have h_t_comp : (⟨T, hT_qL⟩ : ↥(quasiLocal L Ω)).val ∈ complementConeSubalg L Ω Λθ :=
      localSubalgebra_mem_complementConeSubalg hd_θ hT
    have h_θt : θ.endo ⟨T, hT_qL⟩ = ⟨T, hT_qL⟩ := hθ _ h_t_comp
    have hcomm : ∀ (b : ↥(quasiLocal L Ω)),
        b * ⟨T, hT_qL⟩ = ⟨T, hT_qL⟩ * b →
        θ.endo b * ⟨T, hT_qL⟩ = ⟨T, hT_qL⟩ * θ.endo b := fun b h_bt => by
      calc θ.endo b * ⟨T, hT_qL⟩
          = θ.endo b * θ.endo ⟨T, hT_qL⟩ := by rw [h_θt]
        _ = θ.endo (b * ⟨T, hT_qL⟩) := (map_mul θ.endo b ⟨T, hT_qL⟩).symm
        _ = θ.endo (⟨T, hT_qL⟩ * b) := by rw [h_bt]
        _ = θ.endo ⟨T, hT_qL⟩ * θ.endo b := map_mul θ.endo ⟨T, hT_qL⟩ b
        _ = ⟨T, hT_qL⟩ * θ.endo b := by rw [h_θt]
    have h_at : a * ⟨T, hT_qL⟩ = ⟨T, hT_qL⟩ * a := quasiLocal_commute_of_disjoint hd_aF ha hT
    refine ⟨congrArg Subtype.val (hcomm a h_at), ?_⟩
    have h_sa : (star a).val ∈ localSubalgebra (Ω := Ω) Λa := star_mem ha
    have h2 := hcomm (star a) (quasiLocal_commute_of_disjoint hd_aF h_sa hT)
    rw [map_star θ.endo a] at h2
    exact congrArg Subtype.val h2
  have h_closure_le : complementConeSubalg L Ω C ≤
      StarSubalgebra.centralizer ℂ {(θ.endo a).val} :=
    StarSubalgebra.topologicalClosure_minimal
      (iSup_le fun Λt => iSup_le fun hd => h_local_le_centralizer Λt hd)
      (Set.isClosed_centralizer _)
  have h_central : (θ.endo a).val ∈ Set.centralizer ((complementConeSubalg L Ω C :
        StarSubalgebra ℂ (globalHilbert L Ω →L[ℂ] globalHilbert L Ω)) : Set _) := by
    intro m hm
    have hm_in : m ∈ StarSubalgebra.centralizer ℂ {(θ.endo a).val} := h_closure_le hm
    rw [StarSubalgebra.mem_centralizer_iff] at hm_in
    obtain ⟨h1, _⟩ := hm_in (θ.endo a).val (Set.mem_singleton _)
    exact h1.symm
  rw [hHaag C] at h_central
  exact h_central

/-- **Commutation on a single-site generator.**  For `b ∈ 𝔄({x})`, separation of
the localization cones forces `ρ(σ(b)) = σ(ρ(b))`: the site `x` lies outside at
least one cone, and support spreading keeps the relevant image away from the
other cone, so both composites collapse to the same operator. -/
lemma commutes_apply_of_single_site (hHaag : HaagDuality L Ω)
    {ρ σ : sectorCat L Ω} {Λρ Λσ : Cone L}
    (hρ : IsLocalizedIn Λρ ρ) (hσ : IsLocalizedIn Λσ σ)
    (hsep : Disjoint Λρ.region Λσ.region)
    {x : L} {b : ↥(quasiLocal L Ω)} (hx : b.val ∈ localSubalgebra (Ω := Ω) {x}) :
    ρ.endo (σ.endo b) = σ.endo (ρ.endo b) := by
  by_cases hxσ : x ∈ Λσ.region
  · have hxρ : x ∉ Λρ.region := Set.disjoint_right.mp hsep hxσ
    have hdρ : Disjoint (↑({x} : Finset L) : Set L) Λρ.region := by
      rw [Finset.coe_singleton]; exact Set.disjoint_singleton_left.mpr hxρ
    have hb_compρ : b.val ∈ complementConeSubalg L Ω Λρ :=
      localSubalgebra_mem_complementConeSubalg hdρ hx
    have hρb : ρ.endo b = b := hρ b hb_compρ
    have hσb_mem : (σ.endo b).val ∈
        localConeSubalg L Ω { region := (↑({x} : Finset L) : Set L) ∪ Λσ.region } :=
      sectorEndo_apply_mem_localConeSubalg hHaag hσ hx
    have hdisj : Disjoint ((↑({x} : Finset L) : Set L) ∪ Λσ.region) Λρ.region :=
      Set.disjoint_union_left.mpr ⟨hdρ, Disjoint.symm hsep⟩
    have hσb_compρ : (σ.endo b).val ∈ complementConeSubalg L Ω Λρ :=
      localConeSubalg_le_complementConeSubalg L Ω hdisj hσb_mem
    have hρσb : ρ.endo (σ.endo b) = σ.endo b := hρ _ hσb_compρ
    rw [hρσb, hρb]
  · have hdσ : Disjoint (↑({x} : Finset L) : Set L) Λσ.region := by
      rw [Finset.coe_singleton]; exact Set.disjoint_singleton_left.mpr hxσ
    have hb_compσ : b.val ∈ complementConeSubalg L Ω Λσ :=
      localSubalgebra_mem_complementConeSubalg hdσ hx
    have hσb : σ.endo b = b := hσ b hb_compσ
    have hρb_mem : (ρ.endo b).val ∈
        localConeSubalg L Ω { region := (↑({x} : Finset L) : Set L) ∪ Λρ.region } :=
      sectorEndo_apply_mem_localConeSubalg hHaag hρ hx
    have hdisj : Disjoint ((↑({x} : Finset L) : Set L) ∪ Λρ.region) Λσ.region :=
      Set.disjoint_union_left.mpr ⟨hdσ, hsep⟩
    have hρb_compσ : (ρ.endo b).val ∈ complementConeSubalg L Ω Λσ :=
      localConeSubalg_le_complementConeSubalg L Ω hdisj hρb_mem
    have hσρb : σ.endo (ρ.endo b) = ρ.endo b := hσ _ hρb_compσ
    rw [hσb, hσρb]

/-- The two composites `ρ ∘ σ` and `σ ∘ ρ` agree on the `*`-subalgebra generated
by the single-site local algebras: by `StarAlgHom.adjoin_le_equalizer` it suffices
to check the single-site generators (`commutes_apply_of_single_site`); the algebra,
unit and `*` cases are handled by the `*`-homomorphism structure. -/
lemma commutes_eqOn_adjoin (hHaag : HaagDuality L Ω)
    {ρ σ : sectorCat L Ω} {Λρ Λσ : Cone L}
    (hρ : IsLocalizedIn Λρ ρ) (hσ : IsLocalizedIn Λσ σ)
    (hsep : Disjoint Λρ.region Λσ.region) :
    Set.EqOn ⇑(ρ.endo.comp σ.endo) ⇑(σ.endo.comp ρ.endo)
      (↑(StarAlgebra.adjoin ℂ
          {a : ↥(quasiLocal L Ω) | ∃ x : L, a.val ∈ localSubalgebra (Ω := Ω) {x}}) :
        Set ↥(quasiLocal L Ω)) := by
  have hsingle : Set.EqOn ⇑(ρ.endo.comp σ.endo) ⇑(σ.endo.comp ρ.endo)
      {a : ↥(quasiLocal L Ω) | ∃ x : L, a.val ∈ localSubalgebra (Ω := Ω) {x}} := by
    rintro b ⟨x, hx⟩
    simp only [StarAlgHom.comp_apply]
    exact commutes_apply_of_single_site hHaag hρ hσ hsep hx
  intro a ha
  exact (StarAlgHom.mem_equalizer _ _ a).mp (StarAlgHom.adjoin_le_equalizer _ _ hsingle ha)

/-- **DHR locality (commutation theorem).**  Localized sectors with
spacelike-separated (region-disjoint) localization cones commute, given strong
Haag duality and net additivity.  The two composites are continuous `*`-endomorphisms
agreeing on the (dense) single-site-generated subalgebra, hence agree everywhere. -/
theorem commutes_of_separated (hHaag : HaagDuality L Ω) (hAdd : NetAdditive L Ω)
    {ρ σ : sectorCat L Ω} {Λρ Λσ : Cone L}
    (hρ : IsLocalizedIn Λρ ρ) (hσ : IsLocalizedIn Λσ σ)
    (hsep : Disjoint Λρ.region Λσ.region) :
    Commutes ρ σ := by
  have hcont : Continuous ⇑(ρ.endo.comp σ.endo) :=
    (nonUnitalStarAlgHom_continuous ρ.endo.toNonUnitalStarAlgHom).comp'
      (nonUnitalStarAlgHom_continuous σ.endo.toNonUnitalStarAlgHom)
  have hcont' : Continuous ⇑(σ.endo.comp ρ.endo) :=
    (nonUnitalStarAlgHom_continuous σ.endo.toNonUnitalStarAlgHom).comp'
      (nonUnitalStarAlgHom_continuous ρ.endo.toNonUnitalStarAlgHom)
  have hFG := Continuous.ext_on hAdd hcont hcont' (commutes_eqOn_adjoin hHaag hρ hσ hsep)
  exact fun a => congrFun hFG a

/-! ### Transport independence

An intertwiner between two localized sectors is localized in the union of their
cones (Haag-duality centralizer argument); hence the statistics operator is
independent of the choice of transport — even to *different* spacelike cones,
since their union is still spacelike to `ρ` (strong Haag duality at the union,
the `d ≥ 3` regime). -/

/-- **Intertwiner localization.**  An intertwiner `w : σ₁' ⟶ σ₂'` between sectors
localized in `Λ₁'`, `Λ₂'` is itself localized in the union `Λ₁' ∪ Λ₂'`: it commutes
with every operator localised outside both cones (which both `σ₁'`, `σ₂'` fix), so
strong Haag duality lands it in `localConeSubalg (Λ₁' ∪ Λ₂')`. -/
lemma crossIntertwiner_mem_localConeSubalg (hHaag : HaagDuality L Ω)
    {σ₁' σ₂' : sectorCat L Ω} {Λ₁' Λ₂' : Cone L}
    (hσ₁' : IsLocalizedIn Λ₁' σ₁') (hσ₂' : IsLocalizedIn Λ₂' σ₂')
    {w : ↥(quasiLocal L Ω)} (hw : ∀ a : ↥(quasiLocal L Ω), w * σ₁'.endo a = σ₂'.endo a * w) :
    w.val ∈ localConeSubalg L Ω (Λ₁'.union Λ₂') := by
  have hw_star : ∀ a : ↥(quasiLocal L Ω), star w * σ₂'.endo a = σ₁'.endo a * star w := by
    intro a
    have h := congrArg star (hw (star a))
    rw [star_mul, star_mul, ← map_star σ₁'.endo, ← map_star σ₂'.endo, star_star] at h
    exact h.symm
  have h_local_le_centralizer : ∀ (Λt : Finset L),
      Disjoint (↑Λt : Set L) (Λ₁'.union Λ₂').region →
      localSubalgebra (Ω := Ω) Λt ≤ StarSubalgebra.centralizer ℂ {w.val} := by
    intro Λt hd T hT
    rw [StarSubalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    have hT_qL : T ∈ quasiLocal L Ω := localSubalgebra_le_quasiLocal L Ω Λt hT
    have h_t_comp : (⟨T, hT_qL⟩ : ↥(quasiLocal L Ω)).val ∈
        complementConeSubalg L Ω (Λ₁'.union Λ₂') :=
      localSubalgebra_mem_complementConeSubalg hd hT
    have h_σ₁'t : σ₁'.endo ⟨T, hT_qL⟩ = ⟨T, hT_qL⟩ :=
      hσ₁' _ (complementConeSubalg_union_le_left L Ω Λ₁' Λ₂' h_t_comp)
    have h_σ₂'t : σ₂'.endo ⟨T, hT_qL⟩ = ⟨T, hT_qL⟩ :=
      hσ₂' _ (complementConeSubalg_union_le_right L Ω Λ₁' Λ₂' h_t_comp)
    refine ⟨?_, ?_⟩
    · have h := hw ⟨T, hT_qL⟩
      rw [h_σ₁'t, h_σ₂'t] at h
      exact congrArg Subtype.val h
    · have h := hw_star ⟨T, hT_qL⟩
      rw [h_σ₁'t, h_σ₂'t] at h
      exact congrArg Subtype.val h
  have h_closure_le : complementConeSubalg L Ω (Λ₁'.union Λ₂') ≤
      StarSubalgebra.centralizer ℂ {w.val} :=
    StarSubalgebra.topologicalClosure_minimal
      (iSup_le fun Λt => iSup_le fun hd => h_local_le_centralizer Λt hd)
      (Set.isClosed_centralizer _)
  have h_central : w.val ∈ Set.centralizer ((complementConeSubalg L Ω (Λ₁'.union Λ₂') :
      StarSubalgebra ℂ (globalHilbert L Ω →L[ℂ] globalHilbert L Ω)) : Set _) := by
    intro m hm
    have hm_in : m ∈ StarSubalgebra.centralizer ℂ {w.val} := h_closure_le hm
    rw [StarSubalgebra.mem_centralizer_iff] at hm_in
    obtain ⟨h1, _⟩ := hm_in w.val (Set.mem_singleton _)
    exact h1.symm
  rw [hHaag (Λ₁'.union Λ₂')] at h_central
  exact h_central

/-- **Transport independence.**  For `ρ` localized in `Λρ`, two transports
`u₁ : σ ⟶ σ₁'`, `u₂ : σ ⟶ σ₂'` of `σ` to (possibly different) cones `Λ₁'`, `Λ₂'`
both spacelike-separated from `Λρ` give the *same* statistics operator.  The
intertwiner `w = u₂ · u₁⋆ : σ₁' ⟶ σ₂'` is localized in `Λ₁' ∪ Λ₂'` (spacelike to
`ρ`), hence fixed by `ρ`, discharging the hypothesis of
`statisticsOperator_indep_of_transporter`.  This is the well-definedness of the DHR
braiding (strong Haag duality, the `d ≥ 3` regime). -/
lemma braiding_indep_of_transport (hHaag : HaagDuality L Ω)
    {ρ σ σ₁' σ₂' : sectorCat L Ω} {Λρ Λ₁' Λ₂' : Cone L}
    (hρ : IsLocalizedIn Λρ ρ) (hσ₁' : IsLocalizedIn Λ₁' σ₁') (hσ₂' : IsLocalizedIn Λ₂' σ₂')
    (hsep₁ : Disjoint Λρ.region Λ₁'.region) (hsep₂ : Disjoint Λρ.region Λ₂'.region)
    (hcomm₁ : Commutes ρ σ₁') (hcomm₂ : Commutes ρ σ₂')
    (u₁ : σ ⟶ σ₁') (u₂ : σ ⟶ σ₂') (hu₁ : IsUnitary u₁) (hu₂ : IsUnitary u₂) :
    statisticsOperator ρ u₁ hu₁ hcomm₁ = statisticsOperator ρ u₂ hu₂ hcomm₂ := by
  refine statisticsOperator_indep_of_transporter ρ u₁ u₂ hu₁ hu₂ hcomm₁ hcomm₂ ?_
  have hw : ∀ a : ↥(quasiLocal L Ω),
      (u₂.t * star u₁.t) * σ₁'.endo a = σ₂'.endo a * (u₂.t * star u₁.t) := by
    intro a
    rw [mul_assoc, star_intertwines u₁ hu₁, ← mul_assoc, u₂.intertwines, mul_assoc]
  have hdisj : Disjoint (Λ₁'.union Λ₂').region Λρ.region := by
    rw [Cone.union_region]
    exact Set.disjoint_union_left.mpr ⟨hsep₁.symm, hsep₂.symm⟩
  have hwcomp : (u₂.t * star u₁.t).val ∈ complementConeSubalg L Ω Λρ :=
    localConeSubalg_le_complementConeSubalg L Ω hdisj
      (crossIntertwiner_mem_localConeSubalg hHaag hσ₁' hσ₂' hw)
  exact hρ (u₂.t * star u₁.t) hwcomp

/-! ### Naturality of the statistics operator (net level)

The first-argument naturality of the braiding, with the locality hypothesis of
`statisticsOperator_naturality_left` discharged: an intertwiner `f : ρ ⟶ ρ'` is
localized in `Λρ ∪ Λρ'` (`crossIntertwiner_mem`), so a transport target spacelike
to that union fixes it. -/

/-- **Naturality in the first argument (net level).**  For an intertwiner
`f : ρ ⟶ ρ'` between sectors localized in `Λρ`, `Λρ'`, and a transport `u` of `σ`
to a target `σ'` localized spacelike to `Λρ ∪ Λρ'`,

```
(f ▷ σ) ≫ ε(ρ', σ) = ε(ρ, σ) ≫ (σ ◁ f).
```

The transport target fixes `f` (it is localized in `Λρ ∪ Λρ'`, spacelike to `σ'`),
discharging the hypothesis of `statisticsOperator_naturality_left`. -/
lemma statisticsOperator_natural_left (hHaag : HaagDuality L Ω)
    {ρ ρ' σ σ' : sectorCat L Ω} {Λρ Λρ' Λσ' : Cone L}
    (f : ρ ⟶ ρ') (hρ : IsLocalizedIn Λρ ρ) (hρ' : IsLocalizedIn Λρ' ρ')
    (hσ' : IsLocalizedIn Λσ' σ')
    (hsep : Disjoint (Λρ.union Λρ').region Λσ'.region)
    (u : σ ⟶ σ') (hu : IsUnitary u) (hcomm : Commutes ρ σ') (hcomm' : Commutes ρ' σ') :
    (f ▷ σ) ≫ statisticsOperator ρ' u hu hcomm'
      = statisticsOperator ρ u hu hcomm ≫ (σ ◁ f) := by
  apply statisticsOperator_naturality_left
  exact hσ' f.t (localConeSubalg_le_complementConeSubalg L Ω hsep
    (crossIntertwiner_mem_localConeSubalg hHaag hρ hρ' f.intertwines))

/-- **Naturality in the second argument (net level).**  For a spectator `X`
localized in `ΛX`, an intertwiner `g : Y ⟶ Z`, and transports `uY : Y ⟶ Y'`,
`uZ : Z ⟶ Z'` of `Y`, `Z` to cones spacelike to `ΛX`,

```
(X ◁ g) ≫ ε(X, Z) = ε(X, Y) ≫ (g ▷ X).
```

The transported intertwiner `g' = uZ · g · uY⋆ : Y' ⟶ Z'` — the `.t` of the
composite `(uY)† ≫ g ≫ uZ` — is localized in `ΛY' ∪ ΛZ'` (`crossIntertwiner_mem`),
spacelike to `X`, hence fixed by `X`; the statistics-operator identity then follows
by pure `.t`-algebra (unitarity of the transporters). -/
lemma statisticsOperator_natural_right (hHaag : HaagDuality L Ω)
    {X Y Y' Z Z' : sectorCat L Ω} {ΛX ΛY' ΛZ' : Cone L}
    (g : Y ⟶ Z) (hX : IsLocalizedIn ΛX X)
    (uY : Y ⟶ Y') (huY : IsUnitary uY) (hY' : IsLocalizedIn ΛY' Y') (hcommY : Commutes X Y')
    (uZ : Z ⟶ Z') (huZ : IsUnitary uZ) (hZ' : IsLocalizedIn ΛZ' Z') (hcommZ : Commutes X Z')
    (hsep : Disjoint (ΛY'.union ΛZ').region ΛX.region) :
    (X ◁ g) ≫ statisticsOperator X uZ huZ hcommZ
      = statisticsOperator X uY huY hcommY ≫ (g ▷ X) := by
  have hgt : (homDagger uY ≫ g ≫ uZ).t = uZ.t * g.t * star uY.t := by
    simp only [comp_t, homDagger_t]
  have hg'fix : X.endo (uZ.t * g.t * star uY.t) = uZ.t * g.t * star uY.t := by
    refine hX _ (localConeSubalg_le_complementConeSubalg L Ω hsep ?_)
    rw [← hgt]
    exact crossIntertwiner_mem_localConeSubalg hHaag hY' hZ'
      (homDagger uY ≫ g ≫ uZ).intertwines
  obtain ⟨hua, _⟩ := Unitary.mem_iff.mp huZ
  obtain ⟨hXc, _⟩ := Unitary.mem_iff.mp (endo_mem_unitary X huY)
  have E : X.endo uZ.t * X.endo g.t * star (X.endo uY.t) = uZ.t * g.t * star uY.t := by
    have h := hg'fix
    rw [map_mul, map_mul, map_star] at h
    exact h
  have key : X.endo uZ.t * X.endo g.t = uZ.t * g.t * star uY.t * X.endo uY.t := by
    have h := congrArg (· * X.endo uY.t) E
    simpa [mul_assoc, hXc] using h
  apply Intertwiner.ext
  simp only [comp_t, whiskerLeft_t, whiskerRight_t, statisticsOperator_t]
  rw [mul_assoc (star uZ.t), key, ← mul_assoc (star uZ.t), ← mul_assoc (star uZ.t),
    ← mul_assoc (star uZ.t), hua, one_mul, mul_assoc]

end LocalNetLike
