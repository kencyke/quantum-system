module

public import QuantumSystem.Algebra.Sector.Net.Braiding
public import QuantumSystem.Algebra.Sector.Net.DHRCategory

/-!
# The braiding on the DHR sector category

With transport existence (`exists_transport_of_separable`) and transport
independence (`braiding_indep_of_transport`) in hand, the DHR statistics operator
defines a genuine **braiding** `β X Y : X ⊗ Y ≅ Y ⊗ X` on the DHR sector category
`dhrSectorCat (L := L) (Ω := Ω)` (boundedly localized + transportable sectors), and
assembles into a full `CategoryTheory.BraidedCategory` instance.

## The choice of transport and its independence

For DHR objects `X` (boundedly localized in some cone) and `Y` (transportable), a
transport of `Y` to a proper cone spacelike to a canonical localization cone of `X`
exists; the resulting unitary statistics operator, an isomorphism by `isoOfUnitary`,
is lifted to the full subcategory.  The choice of transport is made by
`Classical.choice`, but the *value* of the braiding is independent of it: this is
the content of `braiding_indep_of_transport`, packaged here as `dhrBraiding_eq`,
which lets every braiding appearing in the structure axioms be rewritten in terms
of a *common* transport.  That reduction turns the four `BraidedCategory` axioms
into the net-level statistics core lemmas (`statisticsOperator_natural_left/right`,
`statisticsOperator_tensor_right/left`).

To run the independence argument the chosen transport must remember the proper cone
where the second sector lands (spacelike to `X`); this is recorded in the enriched
datum `DHRTransport`.

## References

* Doplicher, Haag, Roberts, *Local observables and particle statistics I, II*,
  Comm. Math. Phys. 23 (1971), 35 (1974).
* Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §6.
-/

@[expose] public section

open scoped LocalNetLike

namespace LocalNetLike

open CategoryTheory CategoryTheory.StarEndo CategoryTheory.MonoidalCategory

variable {L : Type*} [DecidableEq L] [LocalNetLike L] [SpacelikeGeometry L]
  {Ω : (s : L) → LocalNetLike.localIdx (L := L) s}

/-! ### Canonical localization cone of a DHR object -/

/-- A **canonical bounded localization cone** of a DHR object, chosen from the
`IsBoundedlyLocalized` witness.  Fixing one cone per object lets the independence
argument compare transports against a common reference. -/
noncomputable def dhrLocCone (X : dhrSectorCat (L := L) (Ω := Ω)) : Cone L :=
  X.property.1.choose

/-- The canonical localization cone is bounded. -/
lemma dhrLocCone_isBounded (X : dhrSectorCat (L := L) (Ω := Ω)) :
    SpacelikeGeometry.IsBounded (dhrLocCone X) :=
  X.property.1.choose_spec.1

/-- `X.obj` is localized in its canonical localization cone. -/
lemma dhrLocCone_isLocalizedIn (X : dhrSectorCat (L := L) (Ω := Ω)) :
    IsLocalizedIn (dhrLocCone X) X.obj :=
  X.property.1.choose_spec.2

/-! ### Enriched transport remembering the landing cone -/

/-- An **enriched transport** of `Y` away from `X` for DHR objects: a transport of
`Y.obj` together with the proper cone where it lands, recorded as being spacelike
to (region-disjoint from) the canonical localization cone of `X`.  The cone data is
what the transport-independence argument (`dhrBraiding_eq`) needs. -/
structure DHRTransport (X Y : dhrSectorCat (L := L) (Ω := Ω)) where
  /-- The cone where `Y` is transported. -/
  cone : Cone L
  /-- The underlying abstract transport. -/
  tr : Transport X.obj Y.obj
  /-- The transported sector is localized in `cone`. -/
  tgt_loc : IsLocalizedIn cone tr.tgt
  /-- `cone` is spacelike to the canonical localization cone of `X`. -/
  sep : SpacelikeGeometry.Spacelike (dhrLocCone X) cone

/-- **Existence of an enriched transport.**  A proper cone spacelike to the
canonical localization cone of `X` exists (cone-existence axiom); transporting `Y`
there (transportability) and using DHR locality for the commutation gives a
`DHRTransport`. -/
lemma nonempty_dhrTransport (hHaag : HaagDuality L Ω) (hAdd : NetAdditive L Ω)
    (X Y : dhrSectorCat (L := L) (Ω := Ω)) : Nonempty (DHRTransport X Y) := by
  obtain ⟨Λ', hΛ'proper, hsp⟩ :=
    SpacelikeGeometry.exists_spacelike_of_bounded (dhrLocCone_isBounded X)
  obtain ⟨Y', hY'loc, u, hu⟩ := Y.property.2 Λ' hΛ'proper
  have hcomm : Commutes X.obj Y' :=
    commutes_of_separated hHaag hAdd (dhrLocCone_isLocalizedIn X) hY'loc
      (SpacelikeGeometry.spacelike_separated hsp)
  exact ⟨⟨Λ', ⟨Y', u, hu, hcomm⟩, hY'loc, hsp⟩⟩

/-- A **chosen enriched transport** of `Y` away from `X`. -/
noncomputable def dhrTransport (hHaag : HaagDuality L Ω) (hAdd : NetAdditive L Ω)
    (X Y : dhrSectorCat (L := L) (Ω := Ω)) : DHRTransport X Y :=
  (nonempty_dhrTransport hHaag hAdd X Y).some

/-- The **braiding** `β X Y : X ⊗ Y ≅ Y ⊗ X` on the DHR sector category, given by
the (unitary) statistics operator of a chosen transport, lifted to the full
subcategory. -/
noncomputable def dhrBraiding (hHaag : HaagDuality L Ω) (hAdd : NetAdditive L Ω)
    (X Y : dhrSectorCat (L := L) (Ω := Ω)) : (X ⊗ Y) ≅ (Y ⊗ X) :=
  (IsDHR (L := L) (Ω := Ω)).isoMk
    (isoOfUnitary (dhrTransport hHaag hAdd X Y).tr.braiding
      (dhrTransport hHaag hAdd X Y).tr.braiding_isUnitary)

/-- The underlying intertwiner of the braiding is the chosen statistics operator. -/
@[simp] lemma dhrBraiding_hom_hom (hHaag : HaagDuality L Ω) (hAdd : NetAdditive L Ω)
    (X Y : dhrSectorCat (L := L) (Ω := Ω)) :
    (dhrBraiding hHaag hAdd X Y).hom.hom = (dhrTransport hHaag hAdd X Y).tr.braiding := by
  simp [dhrBraiding]

/-- **Transport independence of the braiding.**  The underlying intertwiner of the
braiding equals the statistics operator of *any* transport `tr` of `Y.obj` whose
target is localized in a cone spacelike to the canonical localization cone of `X`.
This is the well-definedness used throughout the structure assembly. -/
lemma dhrBraiding_eq (hHaag : HaagDuality L Ω) (hAdd : NetAdditive L Ω)
    (X Y : dhrSectorCat (L := L) (Ω := Ω)) (tr : Transport X.obj Y.obj) {Λ' : Cone L}
    (htgt : IsLocalizedIn Λ' tr.tgt)
    (hsep : Disjoint (dhrLocCone X).region Λ'.region) :
    (dhrBraiding hHaag hAdd X Y).hom.hom = tr.braiding := by
  rw [dhrBraiding_hom_hom]
  exact braiding_indep_of_transport hHaag (dhrLocCone_isLocalizedIn X)
    (dhrTransport hHaag hAdd X Y).tgt_loc htgt
    (SpacelikeGeometry.spacelike_separated (dhrTransport hHaag hAdd X Y).sep) hsep
    (dhrTransport hHaag hAdd X Y).tr.commutes tr.commutes
    (dhrTransport hHaag hAdd X Y).tr.hom tr.hom
    (dhrTransport hHaag hAdd X Y).tr.unitary tr.unitary

/-- **The DHR braiding is unitary.**  Built from the unitary statistics operator
via `isoOfUnitary`, the braiding's dagger is its inverse, so it is a unitary
morphism — the `symmetry_unitary` input of the abstract target
`RigidSymmetricDaggerCategory`. -/
lemma dhrBraiding_isUnitary (hHaag : HaagDuality L Ω) (hAdd : NetAdditive L Ω)
    (X Y : dhrSectorCat (L := L) (Ω := Ω)) :
    Unitary (dhrBraiding hHaag hAdd X Y).hom := by
  have hdag : (dhrBraiding hHaag hAdd X Y).hom† = (dhrBraiding hHaag hAdd X Y).inv := by
    apply ObjectProperty.hom_ext
    change ((dhrBraiding hHaag hAdd X Y).hom).hom† = (dhrBraiding hHaag hAdd X Y).inv.hom
    rw [dhrBraiding_hom_hom]
    simp only [dhrBraiding, ObjectProperty.isoMk_inv, ObjectProperty.homMk_hom, isoOfUnitary_inv]
    rfl
  exact ⟨by rw [hdag]; exact (dhrBraiding hHaag hAdd X Y).hom_inv_id,
    by rw [hdag]; exact (dhrBraiding hHaag hAdd X Y).inv_hom_id⟩

/-! ### The four `BraidedCategory` axioms -/

/-- **Naturality in the first argument.**  For `f : X ⟶ Y` and a spectator `Z`,
`f ▷ Z ≫ β Y Z = β X Z ≫ Z ◁ f`.  A common transport of `Z` clear of both `X` and
`Y` reduces this to `statisticsOperator_natural_left`. -/
lemma dhrBraiding_naturality_left (hHaag : HaagDuality L Ω) (hAdd : NetAdditive L Ω)
    {X Y : dhrSectorCat (L := L) (Ω := Ω)} (f : X ⟶ Y) (Z : dhrSectorCat (L := L) (Ω := Ω)) :
    f ▷ Z ≫ (dhrBraiding hHaag hAdd Y Z).hom
      = (dhrBraiding hHaag hAdd X Z).hom ≫ Z ◁ f := by
  obtain ⟨Λ', hΛ'proper, hsp⟩ := SpacelikeGeometry.exists_spacelike_of_bounded
    (SpacelikeGeometry.isBounded_union (dhrLocCone_isBounded X) (dhrLocCone_isBounded Y))
  obtain ⟨Z', hZ'loc, u, hu⟩ := Z.property.2 Λ' hΛ'proper
  have hdisj : Disjoint ((dhrLocCone X).union (dhrLocCone Y)).region Λ'.region :=
    SpacelikeGeometry.spacelike_separated hsp
  rw [Cone.union_region] at hdisj
  have hdisjX : Disjoint (dhrLocCone X).region Λ'.region := hdisj.mono_left Set.subset_union_left
  have hdisjY : Disjoint (dhrLocCone Y).region Λ'.region := hdisj.mono_left Set.subset_union_right
  have hcommX : Commutes X.obj Z' :=
    commutes_of_separated hHaag hAdd (dhrLocCone_isLocalizedIn X) hZ'loc hdisjX
  have hcommY : Commutes Y.obj Z' :=
    commutes_of_separated hHaag hAdd (dhrLocCone_isLocalizedIn Y) hZ'loc hdisjY
  apply ObjectProperty.hom_ext
  change (f.hom ▷ Z.obj) ≫ (dhrBraiding hHaag hAdd Y Z).hom.hom
    = (dhrBraiding hHaag hAdd X Z).hom.hom ≫ (Z.obj ◁ f.hom)
  rw [dhrBraiding_eq hHaag hAdd Y Z ⟨Z', u, hu, hcommY⟩ hZ'loc hdisjY,
      dhrBraiding_eq hHaag hAdd X Z ⟨Z', u, hu, hcommX⟩ hZ'loc hdisjX]
  exact statisticsOperator_natural_left hHaag f.hom (dhrLocCone_isLocalizedIn X)
    (dhrLocCone_isLocalizedIn Y) hZ'loc (by rw [Cone.union_region]; exact hdisj) u hu hcommX hcommY

/-- **Naturality in the second argument.**  For a spectator `X` and `f : Y ⟶ Z`,
`X ◁ f ≫ β X Z = β X Y ≫ f ▷ X`.  Common transports of `Y` and `Z` clear of `X`
reduce this to `statisticsOperator_natural_right`. -/
lemma dhrBraiding_naturality_right (hHaag : HaagDuality L Ω) (hAdd : NetAdditive L Ω)
    (X : dhrSectorCat (L := L) (Ω := Ω)) {Y Z : dhrSectorCat (L := L) (Ω := Ω)} (f : Y ⟶ Z) :
    X ◁ f ≫ (dhrBraiding hHaag hAdd X Z).hom
      = (dhrBraiding hHaag hAdd X Y).hom ≫ f ▷ X := by
  obtain ⟨Λ', hΛ'proper, hsp⟩ :=
    SpacelikeGeometry.exists_spacelike_of_bounded (dhrLocCone_isBounded X)
  obtain ⟨Y', hY'loc, uY, huY⟩ := Y.property.2 Λ' hΛ'proper
  obtain ⟨Z', hZ'loc, uZ, huZ⟩ := Z.property.2 Λ' hΛ'proper
  have hdisjX : Disjoint (dhrLocCone X).region Λ'.region :=
    SpacelikeGeometry.spacelike_separated hsp
  have hcommY : Commutes X.obj Y' :=
    commutes_of_separated hHaag hAdd (dhrLocCone_isLocalizedIn X) hY'loc hdisjX
  have hcommZ : Commutes X.obj Z' :=
    commutes_of_separated hHaag hAdd (dhrLocCone_isLocalizedIn X) hZ'loc hdisjX
  apply ObjectProperty.hom_ext
  change (X.obj ◁ f.hom) ≫ (dhrBraiding hHaag hAdd X Z).hom.hom
    = (dhrBraiding hHaag hAdd X Y).hom.hom ≫ (f.hom ▷ X.obj)
  rw [dhrBraiding_eq hHaag hAdd X Z ⟨Z', uZ, huZ, hcommZ⟩ hZ'loc hdisjX,
      dhrBraiding_eq hHaag hAdd X Y ⟨Y', uY, huY, hcommY⟩ hY'loc hdisjX]
  refine statisticsOperator_natural_right hHaag f.hom (dhrLocCone_isLocalizedIn X)
    uY huY hY'loc hcommY uZ huZ hZ'loc hcommZ ?_
  rw [Cone.union_region]
  exact Set.disjoint_union_left.mpr ⟨hdisjX.symm, hdisjX.symm⟩

/-- **First hexagon identity.**  Transporting `Y` and `Z` to a common cone clear of
`X` and using `Transport.braiding_tensor` (the fusion of the statistics operator in
the second argument) discharges the hexagon. -/
lemma dhrBraiding_hexagon_forward (hHaag : HaagDuality L Ω) (hAdd : NetAdditive L Ω)
    (X Y Z : dhrSectorCat (L := L) (Ω := Ω)) :
    (α_ X Y Z).hom ≫ (dhrBraiding hHaag hAdd X (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom
      = ((dhrBraiding hHaag hAdd X Y).hom ▷ Z) ≫ (α_ Y X Z).hom
          ≫ (Y ◁ (dhrBraiding hHaag hAdd X Z).hom) := by
  obtain ⟨Λ', hΛ'proper, hsp⟩ :=
    SpacelikeGeometry.exists_spacelike_of_bounded (dhrLocCone_isBounded X)
  obtain ⟨Y', hY'loc, uσ, huσ⟩ := Y.property.2 Λ' hΛ'proper
  obtain ⟨Z', hZ'loc, uτ, huτ⟩ := Z.property.2 Λ' hΛ'proper
  have hdisjX : Disjoint (dhrLocCone X).region Λ'.region :=
    SpacelikeGeometry.spacelike_separated hsp
  have hcommσ : Commutes X.obj Y' :=
    commutes_of_separated hHaag hAdd (dhrLocCone_isLocalizedIn X) hY'loc hdisjX
  have hcommτ : Commutes X.obj Z' :=
    commutes_of_separated hHaag hAdd (dhrLocCone_isLocalizedIn X) hZ'loc hdisjX
  apply ObjectProperty.hom_ext
  change (α_ X.obj Y.obj Z.obj).hom ≫ (dhrBraiding hHaag hAdd X (Y ⊗ Z)).hom.hom
      ≫ (α_ Y.obj Z.obj X.obj).hom
    = ((dhrBraiding hHaag hAdd X Y).hom.hom ▷ Z.obj) ≫ (α_ Y.obj X.obj Z.obj).hom
        ≫ (Y.obj ◁ (dhrBraiding hHaag hAdd X Z).hom.hom)
  rw [dhrBraiding_eq hHaag hAdd X Y ⟨Y', uσ, huσ, hcommσ⟩ hY'loc hdisjX,
      dhrBraiding_eq hHaag hAdd X Z ⟨Z', uτ, huτ, hcommτ⟩ hZ'loc hdisjX,
      dhrBraiding_eq hHaag hAdd X (Y ⊗ Z)
        (Transport.tensor ⟨Y', uσ, huσ, hcommσ⟩ ⟨Z', uτ, huτ, hcommτ⟩)
        (isLocalizedIn_tensor hY'loc hZ'loc) hdisjX,
      Transport.braiding_tensor]
  apply Intertwiner.ext
  simp

/-- **Second hexagon identity.**  Transporting `Z` to a common cone clear of `X`,
`Y` and `X ⊗ Y`, and using `statisticsOperator_tensor_left` (the fusion of the
statistics operator in the first argument) discharges the hexagon. -/
lemma dhrBraiding_hexagon_reverse (hHaag : HaagDuality L Ω) (hAdd : NetAdditive L Ω)
    (X Y Z : dhrSectorCat (L := L) (Ω := Ω)) :
    (α_ X Y Z).inv ≫ (dhrBraiding hHaag hAdd (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv
      = (X ◁ (dhrBraiding hHaag hAdd Y Z).hom) ≫ (α_ X Z Y).inv
          ≫ ((dhrBraiding hHaag hAdd X Z).hom ▷ Y) := by
  obtain ⟨Λ', hΛ'proper, hsp⟩ := SpacelikeGeometry.exists_spacelike_of_bounded
    (SpacelikeGeometry.isBounded_union
      (SpacelikeGeometry.isBounded_union (dhrLocCone_isBounded (X ⊗ Y))
        (dhrLocCone_isBounded X)) (dhrLocCone_isBounded Y))
  obtain ⟨Z', hZ'loc, u, hu⟩ := Z.property.2 Λ' hΛ'proper
  have hdisj : Disjoint
      (((dhrLocCone (X ⊗ Y)).union (dhrLocCone X)).union (dhrLocCone Y)).region Λ'.region :=
    SpacelikeGeometry.spacelike_separated hsp
  rw [Cone.union_region, Cone.union_region] at hdisj
  have hdisjXY : Disjoint (dhrLocCone (X ⊗ Y)).region Λ'.region :=
    hdisj.mono_left (Set.subset_union_left.trans Set.subset_union_left)
  have hdisjX : Disjoint (dhrLocCone X).region Λ'.region :=
    hdisj.mono_left (Set.subset_union_right.trans Set.subset_union_left)
  have hdisjY : Disjoint (dhrLocCone Y).region Λ'.region :=
    hdisj.mono_left Set.subset_union_right
  have hcommX : Commutes X.obj Z' :=
    commutes_of_separated hHaag hAdd (dhrLocCone_isLocalizedIn X) hZ'loc hdisjX
  have hcommY : Commutes Y.obj Z' :=
    commutes_of_separated hHaag hAdd (dhrLocCone_isLocalizedIn Y) hZ'loc hdisjY
  apply ObjectProperty.hom_ext
  change (α_ X.obj Y.obj Z.obj).inv ≫ (dhrBraiding hHaag hAdd (X ⊗ Y) Z).hom.hom
      ≫ (α_ Z.obj X.obj Y.obj).inv
    = (X.obj ◁ (dhrBraiding hHaag hAdd Y Z).hom.hom) ≫ (α_ X.obj Z.obj Y.obj).inv
        ≫ ((dhrBraiding hHaag hAdd X Z).hom.hom ▷ Y.obj)
  rw [dhrBraiding_eq hHaag hAdd Y Z ⟨Z', u, hu, hcommY⟩ hZ'loc hdisjY,
      dhrBraiding_eq hHaag hAdd X Z ⟨Z', u, hu, hcommX⟩ hZ'loc hdisjX,
      dhrBraiding_eq hHaag hAdd (X ⊗ Y) Z ⟨Z', u, hu, hcommX.tensor_left hcommY⟩ hZ'loc hdisjXY]
  simp only [Transport.braiding]
  have hkey : statisticsOperator (X ⊗ Y).obj u hu (hcommX.tensor_left hcommY)
      = (X.obj ◁ statisticsOperator Y.obj u hu hcommY)
          ≫ (statisticsOperator X.obj u hu hcommX ▷ Y.obj) :=
    statisticsOperator_tensor_left X.obj Y.obj u hu hcommX hcommY
  rw [hkey]
  apply Intertwiner.ext
  simp

/-! ### The braided structure -/

/-- **The DHR sector category is braided.**  The statistics operator, well-defined
up to choice of transport (`dhrBraiding_eq`), supplies a braiding satisfying both
naturality conditions and both hexagon identities.  Since the braiding is built
from the geometric/Haag-duality data (`hHaag`, `hAdd`) this is a *parametrized*
instance rather than a global one. -/
@[reducible] noncomputable def dhrBraidedCategory
    (hHaag : HaagDuality L Ω) (hAdd : NetAdditive L Ω) :
    BraidedCategory (dhrSectorCat (L := L) (Ω := Ω)) where
  braiding := dhrBraiding hHaag hAdd
  braiding_naturality_right := dhrBraiding_naturality_right hHaag hAdd
  braiding_naturality_left := dhrBraiding_naturality_left hHaag hAdd
  hexagon_forward := dhrBraiding_hexagon_forward hHaag hAdd
  hexagon_reverse := dhrBraiding_hexagon_reverse hHaag hAdd

end LocalNetLike
