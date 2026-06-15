module

public import QuantumSystem.Algebra.Sector.Category.Inner
public import QuantumSystem.Algebra.Sector.Net.Localized
public import QuantumSystem.Algebra.QuasiLocalAlgebra.Locality

/-!
# Inner sectors of a local net: localisation and the inner locality theorem

The inner endomorphisms `Ad u` (`Sector/Category/Inner.lean`) realise concrete
DHR sectors of a local net: for `u` localised in a finite region `Λ`, `Ad u` is
**localized** (in the cone of `Λ`), and two inner sectors localised in **disjoint
regions commute** — the inner case of the locality theorem, which is elementary
(the underlying unitaries commute by net locality).  This discharges the
`Commutes` hypothesis of the statistics operator, so inner sectors in disjoint
regions carry an unconditional braiding (exhibiting the framework as non-vacuous).

For *general* localized sectors the disjoint-locality theorem is the deep
structure content (Haag duality + transportability); only the inner case is
elementary.
-/

@[expose] public section

open scoped LocalNetLike

namespace LocalNetLike

open CategoryTheory.StarEndo CategoryTheory.MonoidalCategory

variable {L : Type*} [DecidableEq L] [LocalNetLike L]
  {Ω : (s : L) → LocalNetLike.localIdx (L := L) s}

/-- A unitary `u` localised in `Λ` commutes with every operator localised in the
spacelike complement of `Λ`: it commutes with each disjoint local subalgebra
(net locality), and the centralizer is closed, so the property passes to the
closure. -/
lemma commute_of_mem_complementConeSubalg {Λ : Finset L}
    {u a : globalHilbert L Ω →L[ℂ] globalHilbert L Ω}
    (hu : u ∈ localSubalgebra (Ω := Ω) Λ)
    (ha : a ∈ complementConeSubalg L Ω (Cone.ofFinset Λ)) : Commute u a := by
  have hle : complementConeSubalg L Ω (Cone.ofFinset Λ) ≤
      StarSubalgebra.centralizer ℂ {u} := by
    refine StarSubalgebra.topologicalClosure_minimal ?_ (Set.isClosed_centralizer _)
    refine iSup_le fun Λ' => iSup_le fun hd => ?_
    have hd' : Disjoint Λ Λ' := by
      rw [Cone.region_ofFinset] at hd
      exact (Finset.disjoint_coe.mp hd).symm
    intro T hT
    rw [StarSubalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact ⟨(localSubalgebra_commute_of_disjoint hd' hu hT).eq,
      (localSubalgebra_commute_of_disjoint hd' (star_mem hu) hT).eq⟩
  have hmem : a ∈ StarSubalgebra.centralizer ℂ {u} := hle ha
  rw [StarSubalgebra.mem_centralizer_iff] at hmem
  exact (hmem u (Set.mem_singleton _)).1

/-- The inner sector `Ad u` is **localized** in (the cone of) any finite region
containing `u`. -/
lemma innerEndo_isLocalized (u : ↥(quasiLocal L Ω))
    (hu : u ∈ unitary ↥(quasiLocal L Ω)) {Λ : Finset L}
    (hloc : u.val ∈ localSubalgebra (Ω := Ω) Λ) :
    IsLocalized L Ω (innerEndo u hu) := by
  refine ⟨Cone.ofFinset Λ, fun a ha => ?_⟩
  rw [innerEndo_endo_apply]
  have hcomm : u * a = a * u :=
    Subtype.ext (commute_of_mem_complementConeSubalg hloc ha).eq
  rw [hcomm, mul_assoc, (_root_.Unitary.mem_iff.mp hu).2, mul_one]

/-- **Locality theorem (inner case).**  Two inner sectors localised in disjoint
regions commute: the underlying unitaries commute by net locality, and the
abstract `commutes_innerEndo_of_commute` then gives `Commutes (Ad u) (Ad v)`. -/
theorem commutes_innerEndo {u v : ↥(quasiLocal L Ω)}
    (hu : u ∈ unitary ↥(quasiLocal L Ω)) (hv : v ∈ unitary ↥(quasiLocal L Ω))
    {Λu Λv : Finset L} (hlocu : u.val ∈ localSubalgebra (Ω := Ω) Λu)
    (hlocv : v.val ∈ localSubalgebra (Ω := Ω) Λv) (hd : Disjoint Λu Λv) :
    Commutes (innerEndo u hu) (innerEndo v hv) :=
  commutes_innerEndo_of_commute hu hv
    (Subtype.ext (localSubalgebra_commute_of_disjoint hd hlocu hlocv).eq)

/-- **Unconditional braiding of inner sectors.**  Two inner sectors localised in
disjoint regions carry a unitary statistics operator (braiding intertwiner)
`Ad u ⊗ Ad v ⟶ Ad v ⊗ Ad u`, with no extra hypothesis: they commute
(`commutes_innerEndo`), so the transport is trivial and the braiding is the B1
statistics operator. -/
noncomputable def innerBraiding {u v : ↥(quasiLocal L Ω)}
    (hu : u ∈ unitary ↥(quasiLocal L Ω)) (hv : v ∈ unitary ↥(quasiLocal L Ω))
    {Λu Λv : Finset L} (hlocu : u.val ∈ localSubalgebra (Ω := Ω) Λu)
    (hlocv : v.val ∈ localSubalgebra (Ω := Ω) Λv) (hd : Disjoint Λu Λv) :
    (innerEndo u hu ⊗ innerEndo v hv) ⟶ (innerEndo v hv ⊗ innerEndo u hu) :=
  (Transport.ofCommutes (commutes_innerEndo hu hv hlocu hlocv hd)).braiding

lemma innerBraiding_isUnitary {u v : ↥(quasiLocal L Ω)}
    (hu : u ∈ unitary ↥(quasiLocal L Ω)) (hv : v ∈ unitary ↥(quasiLocal L Ω))
    {Λu Λv : Finset L} (hlocu : u.val ∈ localSubalgebra (Ω := Ω) Λu)
    (hlocv : v.val ∈ localSubalgebra (Ω := Ω) Λv) (hd : Disjoint Λu Λv) :
    IsUnitary (innerBraiding hu hv hlocu hlocv hd) :=
  (Transport.ofCommutes (commutes_innerEndo hu hv hlocu hlocv hd)).braiding_isUnitary

end LocalNetLike
