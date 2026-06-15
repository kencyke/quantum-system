module

public import QuantumSystem.Algebra.Sector.Net.Localized
public import QuantumSystem.Algebra.Sector.Net.Transportable

/-!
# The DHR sector category: localized and transportable sectors

The genuine carrier of the DHR superselection structure (braiding, symmetry,
conjugates, reconstruction) is the full subcategory of sectors that are both
**localized** (`IsLocalized`) and **transportable** (`IsTransportable`).
Transportability is what lets the statistics operator be defined on *every* pair
(a transport of one sector away from the other always exists), so it is the right
domain for the eventual `BraidedCategory`/`SymmetricCategory` structure.

This file records the object property `IsDHR := IsLocalized ∧ IsTransportable`,
shows it contains the unit and is closed under tensor (so it is
`ObjectProperty.IsMonoidal`), and defines the full subcategory `dhrSectorCat`,
which inherits the strict monoidal and dagger-monoidal structure.

The braiding/symmetry on `dhrSectorCat` is built on top, using transport existence
(`isTransportable_of_isDHRTransportable`) and the statistics operator.
-/

@[expose] public section

open scoped LocalNetLike

namespace LocalNetLike

open CategoryTheory CategoryTheory.StarEndo CategoryTheory.MonoidalCategory

variable {L : Type*} [DecidableEq L] [LocalNetLike L]
  {Ω : (s : L) → LocalNetLike.localIdx (L := L) s}

/-! ### Closure of localization and transportability under tensor -/

/-- Localization in a *fixed* cone is closed under tensor (= composition): if both
`ρ` and `σ` act trivially on the complement of `Λ`, so does `ρ ⊗ σ`. -/
lemma isLocalizedIn_tensor {Λ : Cone L} {ρ σ : sectorCat L Ω}
    (hρ : IsLocalizedIn Λ ρ) (hσ : IsLocalizedIn Λ σ) :
    IsLocalizedIn Λ (ρ ⊗ σ) := by
  intro a ha
  change ρ.endo (σ.endo a) = a
  rw [hσ a ha, hρ a ha]

variable [SpacelikeGeometry L]

/-- The identity (vacuum) sector is transportable: it is localized in every cone,
so it transports to itself by the identity. -/
lemma isTransportable_id : IsTransportable (𝟙_ (sectorCat L Ω)) := fun Λ _ =>
  ⟨𝟙_ (sectorCat L Ω), isLocalizedIn_id Λ, 𝟙 _, id_isUnitary _⟩

/-- Transportability is closed under tensor: transporting `ρ` and `σ` into a common
proper cone `Λ` and tensoring the transporters transports `ρ ⊗ σ` into `Λ`. -/
lemma IsTransportable.tensor {ρ σ : sectorCat L Ω}
    (hρ : IsTransportable ρ) (hσ : IsTransportable σ) :
    IsTransportable (ρ ⊗ σ) := by
  intro Λ hΛ
  obtain ⟨ρ', hρ'loc, u, hu⟩ := hρ Λ hΛ
  obtain ⟨σ', hσ'loc, v, hv⟩ := hσ Λ hΛ
  exact ⟨ρ' ⊗ σ', isLocalizedIn_tensor hρ'loc hσ'loc, u ⊗ₘ v, hu.tensorHom hv⟩

/-! ### The DHR object property and full subcategory -/

/-- A sector is **boundedly localized** if it acts trivially outside some *bounded*
region.  This refines `IsLocalized` (localization in *some* cone) to a region that
admits a spacelike proper cone — the room needed to transport another sector clear
of it for the braiding.  Bounded regions are closed under union, so this is closed
under fusion. -/
def IsBoundedlyLocalized (ρ : sectorCat L Ω) : Prop :=
  ∃ Λ : Cone L, SpacelikeGeometry.IsBounded Λ ∧ IsLocalizedIn Λ ρ

/-- A boundedly localized sector is in particular localized. -/
lemma IsBoundedlyLocalized.isLocalized {ρ : sectorCat L Ω} (h : IsBoundedlyLocalized ρ) :
    IsLocalized L Ω ρ := by
  obtain ⟨Λ, _, hl⟩ := h
  exact isLocalized_of_isLocalizedIn hl

/-- The **DHR object property**: a sector is *boundedly localized* and
*transportable*.  This is the carrier of the superselection structure. -/
def IsDHR : ObjectProperty (sectorCat L Ω) :=
  fun ρ => IsBoundedlyLocalized ρ ∧ IsTransportable ρ

instance : (IsDHR (L := L) (Ω := Ω)).ContainsUnit where
  prop_unit :=
    ⟨⟨{ region := (∅ : Set L) }, SpacelikeGeometry.isBounded_empty, isLocalizedIn_id _⟩,
      isTransportable_id⟩

instance : (IsDHR (L := L) (Ω := Ω)).TensorLE (IsDHR (L := L) (Ω := Ω))
    (IsDHR (L := L) (Ω := Ω)) where
  prop_tensor X₁ X₂ h₁ h₂ := by
    obtain ⟨Λ₁, hb₁, hl₁⟩ := h₁.1
    obtain ⟨Λ₂, hb₂, hl₂⟩ := h₂.1
    refine ⟨⟨Λ₁.union Λ₂, SpacelikeGeometry.isBounded_union hb₁ hb₂, fun a ha => ?_⟩,
      h₁.2.tensor h₂.2⟩
    change X₁.endo (X₂.endo a) = a
    rw [hl₂ a (complementConeSubalg_union_le_right L Ω Λ₁ Λ₂ ha),
      hl₁ a (complementConeSubalg_union_le_left L Ω Λ₁ Λ₂ ha)]

instance : (IsDHR (L := L) (Ω := Ω)).IsMonoidal where

/-- The **DHR sector category**: the full monoidal subcategory of localized,
transportable endomorphisms.  It inherits the strict monoidal and dagger-monoidal
structure; the braiding/symmetry and rigidity are built on top. -/
noncomputable abbrev dhrSectorCat : Type _ := (IsDHR (L := L) (Ω := Ω)).FullSubcategory

noncomputable example : MonoidalCategory (dhrSectorCat (L := L) (Ω := Ω)) := inferInstance

noncomputable example : DaggerMonoidalCategory (dhrSectorCat (L := L) (Ω := Ω)) := inferInstance

end LocalNetLike
