module

public import QuantumSystem.Algebra.Geometry.Spacelike
public import QuantumSystem.Algebra.Sector.Category.Statistics
public import QuantumSystem.Algebra.Sector.Net.Localized

/-!
# Transportability of localized sectors

The **DHR transportability** part of the superselection criterion: a localized
endomorphism `ρ` is *transportable* if it can be moved — by a unitary intertwiner
inside the quasi-local algebra — to a sector localized in any prescribed cone.
Together with localization this is the definition of a DHR sector.

* `IsLocalizedIn Λ ρ` — `ρ` acts trivially on the spacelike complement of the
  *specific* cone `Λ` (so `IsLocalized = ∃ Λ, IsLocalizedIn Λ`).
* `IsTransportable ρ` — for every cone `Λ` there is a sector localized in `Λ` and
  a unitary intertwiner from `ρ` to it.

Transportability is the geometric/selection input; its *existence* for concrete
sectors is established from Haag duality (the landing core
`intertwiningOp_mem_quasiLocal`).  Here we record the predicates and the
elementary facts; the deep existence theorem is developed on top.
-/

@[expose] public section

open scoped LocalNetLike

namespace LocalNetLike

open CategoryTheory.StarEndo CategoryTheory.MonoidalCategory

variable {L : Type*} [DecidableEq L] [LocalNetLike L]
  {Ω : (s : L) → LocalNetLike.localIdx (L := L) s}

/-- `ρ` is **localized in the cone `Λ`**: it acts as the identity on every operator
localised in the spacelike complement of `Λ`. -/
def IsLocalizedIn (Λ : Cone L) (ρ : sectorCat L Ω) : Prop :=
  ∀ a : ↥(quasiLocal L Ω), a.val ∈ complementConeSubalg L Ω Λ → ρ.endo a = a

/-- Localization in a specific cone implies localization. -/
lemma isLocalized_of_isLocalizedIn {Λ : Cone L} {ρ : sectorCat L Ω}
    (h : IsLocalizedIn Λ ρ) : IsLocalized L Ω ρ := ⟨Λ, h⟩

/-- The identity sector is localized in every cone. -/
lemma isLocalizedIn_id (Λ : Cone L) :
    IsLocalizedIn Λ (𝟙_ (CategoryTheory.StarEndoCat ↥(quasiLocal L Ω))) :=
  fun _ _ => rfl

variable [SpacelikeGeometry L]

/-- **DHR transportability.**  `ρ` can be transported, by a unitary intertwiner,
to a sector localized in any prescribed **proper** cone `Λ`.  The restriction to
proper cones is essential: the empty cone would force the transported sector to be
the identity (`complementConeSubalg {region := ∅} = quasiLocal`), so quantifying
over it would make the predicate false for every nontrivial sector. -/
def IsTransportable (ρ : sectorCat L Ω) : Prop :=
  ∀ Λ : Cone L, SpacelikeGeometry.IsProper Λ →
    ∃ σ : sectorCat L Ω, IsLocalizedIn Λ σ ∧ ∃ u : ρ ⟶ σ, IsUnitary u

/-- A transportable sector can be moved to any prescribed proper cone. -/
lemma IsTransportable.exists_transport {ρ : sectorCat L Ω} (h : IsTransportable ρ)
    {Λ : Cone L} (hΛ : SpacelikeGeometry.IsProper Λ) :
    ∃ σ : sectorCat L Ω, IsLocalizedIn Λ σ ∧ ∃ u : ρ ⟶ σ, IsUnitary u :=
  h Λ hΛ

end LocalNetLike
