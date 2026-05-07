module

public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import QuantumSystem.Algebra.QuasiLocalAlgebra.InfiniteTensor.RegionDirectedOmega

/-!
# Complete (full) infinite tensor product as a sector direct sum

Following Bratteli–Robinson II §2.7.2, the *complete* infinite tensor product
${\bigotimes^*_{s \in L} \mathcal H_s}$ of a family of single-site Hilbert
spaces is built by direct-summing the *incomplete* sectors
`globalHilbertOmega L Ω hΩ` over all equivalence classes of unit-vector
reference families.

This file packages the construction at the level of an `lp 2` direct sum
indexed by unit families and exhibits each `globalHilbertOmega L Ω hΩ` as one
direct summand (`sector_decomp`).  The `Setoid` recording the "agreement off
a finite set" coarsening of unit families — sufficient for sectoring the
tensor product — is also provided as `referenceEquiv`.

Note: the C₀-equivalence of Bratteli–Robinson (where Ω, Ω' are equivalent
iff `∑_s (1 - |⟪Ω s, Ω' s⟫|) < ∞`) is coarser than `referenceEquiv`; the lp
2-direct-sum here is therefore a *covering* of the BR complete tensor
product, with multiple summands corresponding to the same C₀-class.

## Main definitions

* `LocalNetLike.UnitFamily L` — bundled unit-vector site families
  `{ Ω : (s : L) → siteHilbert s // ∀ s, ‖Ω s‖ = 1 }`.
* `LocalNetLike.referenceEquiv` — the "agree off a finite set" equivalence
  on `UnitFamily L`.
* `LocalNetLike.fullInfTensorHilbert L` — the `lp 2`-direct sum of
  `globalHilbertOmega L Ω hΩ` over `Ω : UnitFamily L`, the *complete*
  infinite tensor product (covering version).
* `LocalNetLike.sectorEmbed Ω` — the canonical isometric embedding of a
  single incomplete sector `globalHilbertOmega L Ω.1 Ω.2` into
  `fullInfTensorHilbert L`.

## References

* Bratteli, Robinson, *Operator Algebras and Quantum Statistical Mechanics II*,
  §2.7.2 (complete infinite tensor product).
-/

@[expose] public section

open scoped LocalNetLike InnerProductSpace

namespace LocalNetLike

variable {L : Type*} [DecidableEq L] [LocalNetLike L]

/-! ### Unit-vector site families -/

/-- Bundled unit-vector site families.  An element packs a function
`Ω : (s : L) → siteHilbert s` with the per-site unit-norm hypothesis
`∀ s, ‖Ω s‖ = 1`. -/
structure UnitFamily (L : Type*) [DecidableEq L] [LocalNetLike L] where
  /-- The site-by-site unit vectors. -/
  fam : (s : L) → siteHilbert (L := L) s
  /-- Each site vector has unit norm. -/
  norm_fam : ∀ s, ‖fam s‖ = 1

/-! ### Sectoring `Setoid` on unit families -/

/-- The "agreement off a finite set" equivalence on unit-vector families.
Two families `Ω, Ω' : UnitFamily L` are equivalent iff
`{ s | Ω.fam s ≠ Ω'.fam s }` is finite.

This is a strictly finer equivalence than the C₀-equivalence of
Bratteli–Robinson (so each C₀-class is a union of `referenceEquiv`-classes),
but it suffices for the basis-indexed sector decomposition. -/
def referenceEquiv : Setoid (UnitFamily L) where
  r Ω Ω' := Set.Finite { s : L | Ω.fam s ≠ Ω'.fam s }
  iseqv :=
    { refl := fun Ω => by
        simp only [ne_eq, not_true_eq_false, Set.setOf_false, Set.finite_empty]
      symm := fun {Ω Ω'} h => by
        have : { s : L | Ω.fam s ≠ Ω'.fam s } = { s : L | Ω'.fam s ≠ Ω.fam s } := by
          ext s
          exact ⟨fun hs heq => hs heq.symm, fun hs heq => hs heq.symm⟩
        rwa [this] at h
      trans := fun {Ω Ω' Ω''} h₁ h₂ => by
        refine (h₁.union h₂).subset ?_
        intro s hs
        rw [Set.mem_setOf_eq, ne_eq] at hs
        rw [Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq]
        by_contra hns
        push Not at hns
        exact hs (hns.1.trans hns.2) }

/-! ### The complete (full) infinite tensor product -/

/-- Classical decidable equality on `UnitFamily L`, needed to apply
`lp.single` and related index-pointed constructions. -/
noncomputable instance : DecidableEq (UnitFamily L) := Classical.decEq _

/-- The Hilbert space at the index `Ω : UnitFamily L`, defined as the
Cauchy completion of the algebraic colimit `tensorPreHilbertΩ L Ω.fam`.
Equal up to `abbrev`-unfolding to `globalHilbertOmega L Ω.fam Ω.norm_fam`,
but stated in this `Completion`-form to keep instance synthesis from having
to chase reducibility through dependent indices in the `lp` direct sum. -/
abbrev SectorHilbert (Ω : UnitFamily L) : Type _ :=
  UniformSpace.Completion (tensorPreHilbertΩ L Ω.fam Ω.norm_fam)

/-- Helper: the sector-level `NormedAddCommGroup` instance is recovered from
the `Completion` instance applied to `tensorPreHilbertΩ`'s `NormedAddCommGroup`. -/
noncomputable instance instNormedAddCommGroupSectorHilbert (Ω : UnitFamily L) :
    NormedAddCommGroup (SectorHilbert Ω) :=
  inferInstanceAs (NormedAddCommGroup
    (UniformSpace.Completion (tensorPreHilbertΩ L Ω.fam Ω.norm_fam)))

noncomputable instance instInnerProductSpaceSectorHilbert (Ω : UnitFamily L) :
    InnerProductSpace ℂ (SectorHilbert Ω) :=
  inferInstanceAs (InnerProductSpace ℂ
    (UniformSpace.Completion (tensorPreHilbertΩ L Ω.fam Ω.norm_fam)))

/-- The complete (Bratteli–Robinson §2.7.2) infinite tensor product of the
single-site Hilbert spaces, realised as the `lp 2`-direct sum of the
incomplete sectors `SectorHilbert Ω` indexed by all unit-vector reference
families `Ω : UnitFamily L`.

This is a covering of the BR complete tensor product: distinct
`UnitFamily` representatives of the same C₀-equivalence class give isomorphic
direct summands here.  The genuine BR object is the quotient of this
direct sum by that redundancy. -/
noncomputable def fullInfTensorHilbert (L : Type*) [DecidableEq L]
    [LocalNetLike L] : Type _ :=
  lp (fun Ω : UnitFamily L => SectorHilbert Ω) 2

noncomputable instance : NormedAddCommGroup (fullInfTensorHilbert L) :=
  inferInstanceAs (NormedAddCommGroup
    (lp (fun Ω : UnitFamily L => SectorHilbert Ω) 2))

noncomputable instance : InnerProductSpace ℂ (fullInfTensorHilbert L) :=
  inferInstanceAs (InnerProductSpace ℂ
    (lp (fun Ω : UnitFamily L => SectorHilbert Ω) 2))

noncomputable instance : CompleteSpace (fullInfTensorHilbert L) :=
  inferInstanceAs (CompleteSpace
    (lp (fun Ω : UnitFamily L => SectorHilbert Ω) 2))

/-! ### Sector embedding `sector_decomp` -/

open Classical in
/-- The canonical isometric embedding of the incomplete sector
`SectorHilbert Ω` (= `globalHilbertOmega L Ω.fam Ω.norm_fam`) into the
complete tensor product `fullInfTensorHilbert L`, sending a vector `x` to
the `lp 2`-tuple equal to `x` at index `Ω` and zero elsewhere. -/
noncomputable def sectorEmbed (Ω : UnitFamily L) :
    SectorHilbert Ω →ₗᵢ[ℂ] fullInfTensorHilbert L where
  toLinearMap := lp.lsingle 2 Ω
  norm_map' x := lp.norm_single (by norm_num : (0 : ENNReal) < 2) Ω x

/-- `sector_decomp`: every incomplete sector `globalHilbertOmega L Ω hΩ`
appears as one direct-summand in the complete tensor product
`fullInfTensorHilbert L`. -/
theorem sector_decomp (Ω : UnitFamily L) :
    ∃ φ : SectorHilbert Ω →ₗᵢ[ℂ] fullInfTensorHilbert L,
      ∀ x : SectorHilbert Ω, ‖φ x‖ = ‖x‖ :=
  ⟨sectorEmbed Ω, fun x => (sectorEmbed Ω).norm_map x⟩

end LocalNetLike
