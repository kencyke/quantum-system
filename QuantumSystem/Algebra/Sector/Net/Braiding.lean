module

public import QuantumSystem.Algebra.Sector.Net.Commutation

/-!
# Existence of the braiding (statistics operator) for DHR pairs

With the geometric and locality inputs now in place, the DHR **statistics operator**
exists for every pair of suitable sectors.  Given a sector `ρ` localized in a
*proper* cone `Λρ` and a *transportable* sector `σ`, the cone-existence axiom
(`SpacelikeGeometry.exists_spacelike_proper`) supplies a proper cone `Λ'` spacelike
to `Λρ`; transporting `σ` there (`IsTransportable`) yields `σ'` localized in `Λ'`,
which commutes with `ρ` by DHR locality (`commutes_of_separated`).  This is exactly
the datum of a `Transport ρ σ`, whence the unitary braiding
`ε(ρ,σ) : ρ ⊗ σ ⟶ σ ⊗ ρ`.

This packages the *per-pair* braiding.  Assembling it into a `BraidedCategory`
instance on the DHR sector category additionally requires:
* localization of the objects in *proper* cones (a refinement of the object
  property), and
* **transport independence** — the statistics operator is independent of the
  auxiliary transport choice (a further Haag-duality theorem) — which makes the
  braiding well-defined and natural.

## References

* Doplicher, Haag, Roberts, *Local observables and particle statistics I*,
  Comm. Math. Phys. 23 (1971), §4.
* Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §6.
-/

@[expose] public section

open scoped LocalNetLike

namespace LocalNetLike

open CategoryTheory CategoryTheory.StarEndo CategoryTheory.MonoidalCategory

variable {L : Type*} [DecidableEq L] [LocalNetLike L] [SpacelikeGeometry L]
  {Ω : (s : L) → LocalNetLike.localIdx (L := L) s}

/-- **Transport existence for a DHR pair.**  If `ρ` is localized in a bounded
region `Λρ` and `σ` is transportable, then there is a transport of `σ` away from
`ρ`: a sector `σ'` localized in a proper cone spacelike to `Λρ`, unitarily
equivalent to `σ`, and commuting with `ρ`.  Uses strong Haag duality, net
additivity, and the cone-existence axiom of the spacelike geometry. -/
lemma exists_transport_of_separable (hHaag : HaagDuality L Ω) (hAdd : NetAdditive L Ω)
    {ρ σ : sectorCat L Ω} {Λρ : Cone L}
    (hρ : IsLocalizedIn Λρ ρ) (hρbdd : SpacelikeGeometry.IsBounded Λρ)
    (hσtr : IsTransportable σ) :
    Nonempty (Transport ρ σ) := by
  obtain ⟨Λ', hΛ'proper, hsp⟩ := SpacelikeGeometry.exists_spacelike_of_bounded hρbdd
  obtain ⟨σ', hσ'loc, u, hu⟩ := hσtr Λ' hΛ'proper
  have hcomm : Commutes ρ σ' :=
    commutes_of_separated hHaag hAdd hρ hσ'loc (SpacelikeGeometry.spacelike_separated hsp)
  exact ⟨⟨σ', u, hu, hcomm⟩⟩

/-- **Existence of the braiding for a DHR pair.**  Under the hypotheses of
`exists_transport_of_separable`, there is a unitary statistics operator
`ε(ρ,σ) : ρ ⊗ σ ⟶ σ ⊗ ρ`. -/
lemma exists_braiding (hHaag : HaagDuality L Ω) (hAdd : NetAdditive L Ω)
    {ρ σ : sectorCat L Ω} {Λρ : Cone L}
    (hρ : IsLocalizedIn Λρ ρ) (hρbdd : SpacelikeGeometry.IsBounded Λρ)
    (hσtr : IsTransportable σ) :
    ∃ b : (ρ ⊗ σ) ⟶ (σ ⊗ ρ), IsUnitary b := by
  obtain ⟨tr⟩ := exists_transport_of_separable hHaag hAdd hρ hρbdd hσtr
  exact ⟨tr.braiding, tr.braiding_isUnitary⟩

end LocalNetLike
