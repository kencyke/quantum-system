module

public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import QuantumSystem.Algebra.QuasiLocalAlgebra.ConeSubalgebra
public import QuantumSystem.Algebra.Sector.Net.Construction

/-!
# The localized full subcategory of the sector category

The genuine DHR sector category is not all of `End(quasiLocal L Ω)` but the
full subcategory of **localized** endomorphisms: those acting trivially on
operators localised outside some cone.

* `LocalNetLike.IsLocalized` — the object property "trivial on the complement
  of some cone".
* It is closed under tensor (= composition; localisation regions take a union)
  and contains the unit, so it is `ObjectProperty.IsMonoidal`; hence the full
  subcategory `localizedSectorCat L Ω` inherits a `MonoidalCategory` instance
  from Mathlib's `fullMonoidalSubcategory`.

This is the substrate on which the *symmetric* (high-dimensional) and *rigid*
(conjugates) refinements are built.
-/

@[expose] public section

namespace LocalNetLike

open CategoryTheory MonoidalCategory

variable (L : Type*) [DecidableEq L] [LocalNetLike L]
    (Ω : (s : L) → LocalNetLike.localIdx (L := L) s)

/-- An endomorphism of the quasi-local algebra is **localized** if it acts as
the identity on every operator localised outside some cone `Λ`. -/
def IsLocalized : ObjectProperty (sectorCat L Ω) :=
  fun ρ => ∃ Λ : Cone L, ∀ a : ↥(quasiLocal L Ω),
    a.val ∈ complementConeSubalg L Ω Λ → ρ.endo a = a

instance : (IsLocalized L Ω).ContainsUnit where
  prop_unit := ⟨⟨(∅ : Set L)⟩, fun _ _ => rfl⟩

instance : (IsLocalized L Ω).TensorLE (IsLocalized L Ω) (IsLocalized L Ω) where
  prop_tensor ρ σ h₁ h₂ := by
    obtain ⟨Λ₁, hΛ₁⟩ := h₁
    obtain ⟨Λ₂, hΛ₂⟩ := h₂
    refine ⟨Λ₁.union Λ₂, fun a ha => ?_⟩
    have ha1 := complementConeSubalg_union_le_left L Ω Λ₁ Λ₂ ha
    have ha2 := complementConeSubalg_union_le_right L Ω Λ₁ Λ₂ ha
    change ρ.endo (σ.endo a) = a
    rw [hΛ₂ a ha2, hΛ₁ a ha1]

instance : (IsLocalized L Ω).IsMonoidal where

/-- The **localized DHR sector category**: the full monoidal subcategory of
localized endomorphisms, with the inherited (strict) monoidal structure. -/
noncomputable abbrev localizedSectorCat : Type _ :=
  (IsLocalized L Ω).FullSubcategory

noncomputable example : MonoidalCategory (localizedSectorCat L Ω) := inferInstance

noncomputable example : DaggerMonoidalCategory (localizedSectorCat L Ω) := inferInstance

end LocalNetLike
