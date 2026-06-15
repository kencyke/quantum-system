module

public import QuantumSystem.Algebra.Sector.Category.DirectSum
public import QuantumSystem.Algebra.Sector.Category.Subobject
public import QuantumSystem.Algebra.Sector.Net.DHRCategory

/-!
# C\*-completeness of the DHR category: closure under direct sums and subobjects

A C\*-tensor category of DHR sectors must be closed under direct sums and
subobjects (Müger §1.5–1.6) — this is the C\*-completeness required by the
Doplicher–Roberts reconstruction.  The *internal* constructions live at the
abstract level (`Category/DirectSum.lean`, `Category/Subobject.lean`): a Cuntz pair
realises a binary direct sum `ρ ⊕ σ`, and split data for a projection realises a
subobject `ρ_e`.  This file establishes that, at the **net level**, these
constructions stay inside the DHR object property — they are again *localized* and
*transportable*, so the direct sum (and subobject) of DHR sectors is a DHR sector.

## The locality of the isometries is irreducible

For `ρ ⊕ σ = v₁ ρ(·) v₁⋆ + v₂ σ(·) v₂⋆` to be localized in `Λ` it is **not** enough
that `ρ`, `σ` are: the Cuntz isometries `v₁, v₂` must themselves be localized in
`Λ` (commute with the spacelike complement), otherwise the direct sum spreads the
charge.  This is captured by `CommutesComplement`, the operator-level shadow of
`vᵢ ∈ 𝔄(Λ)`.  Transportability of `ρ ⊕ σ` further needs a local Cuntz pair *in
every proper target cone* (`HasLocalCuntzPairs`), the properly-infinite-locally
property of the quasi-local algebra — a net existence input discharged
model-by-model (R8).

## References

* Müger, *Abstract Duality Theory for Symmetric Tensor ∗-Categories*, §1.5–1.6.
* Doplicher, Roberts, *A new duality theory for compact groups*, Invent. Math.
  98 (1989).
-/

@[expose] public section

open scoped LocalNetLike

namespace LocalNetLike

open CategoryTheory CategoryTheory.StarEndo CategoryTheory.MonoidalCategory

variable {L : Type*} [DecidableEq L] [LocalNetLike L]
  {Ω : (s : L) → LocalNetLike.localIdx (L := L) s}

/-- An operator `x` of the quasi-local algebra is **localized in the cone `Λ`** in
the operator sense: it commutes with every operator localized in the spacelike
complement of `Λ`.  This is the operator-level shadow of `x ∈ 𝔄(Λ)` (by
microcausality a genuinely `Λ`-local operator commutes with `𝔄(Λᶜ)`); it is the
property the Cuntz/split isometries must have to keep direct sums and subobjects
localized in `Λ`. -/
def CommutesComplement (Λ : Cone L) (x : ↥(quasiLocal L Ω)) : Prop :=
  ∀ a : ↥(quasiLocal L Ω), a.val ∈ complementConeSubalg L Ω Λ → x * a = a * x

/-! ### Localization is closed under direct sums and subobjects -/

/-- **Direct sums preserve localization.**  If `ρ`, `σ` are localized in `Λ` and the
Cuntz isometries are localized in `Λ` (commute with the complement), the direct sum
`ρ ⊕ σ` is localized in `Λ`. -/
lemma IsLocalizedIn.directSum {Λ : Cone L} {ρ σ : sectorCat L Ω}
    (p : IsometryPair ↥(quasiLocal L Ω))
    (hv₁ : CommutesComplement (Ω := Ω) Λ p.v₁) (hv₂ : CommutesComplement (Ω := Ω) Λ p.v₂)
    (hρ : IsLocalizedIn Λ ρ) (hσ : IsLocalizedIn Λ σ) :
    IsLocalizedIn Λ (p.directSum ρ σ) := by
  intro a ha
  rw [IsometryPair.directSum_endo_apply, hρ a ha, hσ a ha, hv₁ a ha, hv₂ a ha,
    mul_assoc, mul_assoc, ← mul_add, p.complete, mul_one]

/-- **Subobjects preserve localization.**  If `ρ` is localized in `Λ` and the split
isometry `w` is localized in `Λ`, the subobject `ρ_e` is localized in `Λ`. -/
lemma IsLocalizedIn.subEndo {Λ : Cone L} {ρ : sectorCat L Ω} {e : ρ ⟶ ρ}
    (s : SplitData e) (hw : CommutesComplement (Ω := Ω) Λ s.w)
    (hρ : IsLocalizedIn Λ ρ) :
    IsLocalizedIn Λ s.subEndo := by
  intro a ha
  rw [SplitData.subEndo_endo_apply, hρ a ha, mul_assoc, ← hw a ha, ← mul_assoc,
    s.isom, one_mul]

variable [SpacelikeGeometry L]

/-- **Direct sums preserve bounded localization.**  With a Cuntz pair localized in a
bounded cone `Λ` containing both `ρ` and `σ`, the direct sum is boundedly
localized. -/
lemma IsBoundedlyLocalized.directSum {Λ : Cone L} {ρ σ : sectorCat L Ω}
    (p : IsometryPair ↥(quasiLocal L Ω)) (hΛ : SpacelikeGeometry.IsBounded Λ)
    (hv₁ : CommutesComplement (Ω := Ω) Λ p.v₁) (hv₂ : CommutesComplement (Ω := Ω) Λ p.v₂)
    (hρ : IsLocalizedIn Λ ρ) (hσ : IsLocalizedIn Λ σ) :
    IsBoundedlyLocalized (p.directSum ρ σ) :=
  ⟨Λ, hΛ, IsLocalizedIn.directSum p hv₁ hv₂ hρ hσ⟩

/-- **Subobjects preserve bounded localization.** -/
lemma IsBoundedlyLocalized.subEndo {Λ : Cone L} {ρ : sectorCat L Ω} {e : ρ ⟶ ρ}
    (s : SplitData e) (hΛ : SpacelikeGeometry.IsBounded Λ)
    (hw : CommutesComplement (Ω := Ω) Λ s.w) (hρ : IsLocalizedIn Λ ρ) :
    IsBoundedlyLocalized s.subEndo :=
  ⟨Λ, hΛ, IsLocalizedIn.subEndo s hw hρ⟩

/-! ### Transportability is closed under direct sums -/

/-- **Existence of local Cuntz pairs.**  For every proper cone `Λ` there is a Cuntz
pair whose isometries are localized in `Λ`.  This is the
*properly-infinite-locally* property of the quasi-local algebra: a binary direct
sum can be formed inside `𝔄(Λ)` for any prescribed proper cone `Λ`.  It is the net
existence input behind transportability of direct sums, discharged
model-by-model (R8). -/
def HasLocalCuntzPairs : Prop :=
  ∀ Λ : Cone L, SpacelikeGeometry.IsProper Λ →
    ∃ p : IsometryPair ↥(quasiLocal L Ω),
      CommutesComplement (Ω := Ω) Λ p.v₁ ∧ CommutesComplement (Ω := Ω) Λ p.v₂

/-- **Direct sums preserve transportability.**  Transporting `ρ` and `σ` into a
common proper cone `Λ`, forming a *local* direct sum there (a local Cuntz pair
exists by `HasLocalCuntzPairs`), and mapping the source direct sum to it by the
unitary `directSumMap` of the two transporters transports `ρ ⊕ σ` into `Λ`. -/
lemma IsTransportable.directSum (p : IsometryPair ↥(quasiLocal L Ω))
    {ρ σ : sectorCat L Ω} (hloc : HasLocalCuntzPairs (Ω := Ω))
    (hρ : IsTransportable ρ) (hσ : IsTransportable σ) :
    IsTransportable (p.directSum ρ σ) := by
  intro Λ hΛ
  obtain ⟨ρ', hρ'loc, u, hu⟩ := hρ Λ hΛ
  obtain ⟨σ', hσ'loc, v, hv⟩ := hσ Λ hΛ
  obtain ⟨q, hq₁, hq₂⟩ := hloc Λ hΛ
  exact ⟨q.directSum ρ' σ', IsLocalizedIn.directSum q hq₁ hq₂ hρ'loc hσ'loc,
    IsometryPair.directSumMap p q u v, IsometryPair.directSumMap_isUnitary p q hu hv⟩

/-! ### The DHR property is closed under direct sums -/

/-- **The DHR object property is closed under direct sums.**  Given DHR sectors `ρ`,
`σ` localized in a common bounded cone `Λ` and a Cuntz pair localized in `Λ`, the
direct sum `ρ ⊕ σ` is again a DHR sector (boundedly localized and transportable),
provided local Cuntz pairs exist in every proper cone (`HasLocalCuntzPairs`).  This
is the direct-sum half of the C\*-completeness of `dhrSectorCat`. -/
lemma IsDHR.directSum {Λ : Cone L} {ρ σ : sectorCat L Ω}
    (p : IsometryPair ↥(quasiLocal L Ω)) (hloc : HasLocalCuntzPairs (Ω := Ω))
    (hΛ : SpacelikeGeometry.IsBounded Λ)
    (hv₁ : CommutesComplement (Ω := Ω) Λ p.v₁) (hv₂ : CommutesComplement (Ω := Ω) Λ p.v₂)
    (hρl : IsLocalizedIn Λ ρ) (hσl : IsLocalizedIn Λ σ)
    (hρ : IsDHR ρ) (hσ : IsDHR σ) :
    IsDHR (p.directSum ρ σ) :=
  ⟨IsBoundedlyLocalized.directSum p hΛ hv₁ hv₂ hρl hσl,
    IsTransportable.directSum p hloc hρ.2 hσ.2⟩

end LocalNetLike
