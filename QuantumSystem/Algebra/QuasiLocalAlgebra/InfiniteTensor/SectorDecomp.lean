module

public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import QuantumSystem.Algebra.QuasiLocalAlgebra.InfiniteTensor.RegionDirectedOmega
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.C0Triangle

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

/-! ### Strong (ℓ²) equivalence on unit families -/

/-- The strong (ℓ²) equivalence on unit-vector families: `Ω ≈ Ω'` iff
`∑_s ‖Ω.fam s - Ω'.fam s‖² < ∞`.

This is strictly finer than the canonical Bratteli–Robinson C₀-equivalence
`∑_s (1 - |⟪Ω s, Ω' s⟫|) < ∞` (because `1 - |⟪u, v⟫| ≤ ‖u - v‖² / 2` for unit
vectors, so ℓ² summability implies C₀ summability), but its iseqv proof is
elementary via the parallelogram-style bound
`‖a - c‖² ≤ 2 ‖a - b‖² + 2 ‖b - c‖²`. -/
def strongEquiv : Setoid (UnitFamily L) where
  r Ω Ω' := Summable fun s : L => ‖Ω.fam s - Ω'.fam s‖ ^ 2
  iseqv :=
    { refl := fun Ω => by
        simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
          not_false_eq_true, zero_pow]
        exact summable_zero
      symm := fun {Ω Ω'} h => by
        have hpt : (fun s : L => ‖Ω'.fam s - Ω.fam s‖ ^ 2)
            = fun s => ‖Ω.fam s - Ω'.fam s‖ ^ 2 := by
          funext s; rw [norm_sub_rev]
        rwa [hpt]
      trans := fun {Ω Ω' Ω''} h₁ h₂ => by
        -- `‖a - c‖² ≤ 2 ‖a - b‖² + 2 ‖b - c‖²` pointwise; both summands
        -- summable, so by comparison `∑ ‖Ω - Ω''‖²` is summable too.
        refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) ?bound
          ((h₁.mul_left 2).add (h₂.mul_left 2))
        intro s
        have hT : ‖Ω.fam s - Ω''.fam s‖
            ≤ ‖Ω.fam s - Ω'.fam s‖ + ‖Ω'.fam s - Ω''.fam s‖ := by
          have hsplit : Ω.fam s - Ω''.fam s
              = (Ω.fam s - Ω'.fam s) + (Ω'.fam s - Ω''.fam s) :=
            (sub_add_sub_cancel _ _ _).symm
          rw [hsplit]
          exact norm_add_le _ _
        have hsq : ‖Ω.fam s - Ω''.fam s‖ ^ 2
            ≤ (‖Ω.fam s - Ω'.fam s‖ + ‖Ω'.fam s - Ω''.fam s‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hT 2
        have hexpand : (‖Ω.fam s - Ω'.fam s‖ + ‖Ω'.fam s - Ω''.fam s‖) ^ 2
            ≤ 2 * ‖Ω.fam s - Ω'.fam s‖ ^ 2 + 2 * ‖Ω'.fam s - Ω''.fam s‖ ^ 2 := by
          nlinarith [sq_nonneg
            (‖Ω.fam s - Ω'.fam s‖ - ‖Ω'.fam s - Ω''.fam s‖)]
        linarith }

/-- Agreement off a finite set implies ℓ² summability of the per-site
difference, since the relevant sequence vanishes off a finite set. -/
theorem referenceEquiv_le_strongEquiv {Ω Ω' : UnitFamily L}
    (h : referenceEquiv.r Ω Ω') : strongEquiv.r Ω Ω' := by
  -- `h : Set.Finite { s | Ω.fam s ≠ Ω'.fam s }`, so the sequence
  -- `s ↦ ‖Ω.fam s - Ω'.fam s‖²` has finite support and is summable.
  refine summable_of_ne_finset_zero (s := h.toFinset) ?_
  intro s hs
  have hagree : Ω.fam s = Ω'.fam s := by
    by_contra hne
    apply hs
    exact Set.Finite.mem_toFinset h |>.mpr hne
  rw [hagree, sub_self, norm_zero]
  simp

/-! ### Bratteli–Robinson canonical C₀-relation -/

/-- The canonical Bratteli–Robinson C₀-relation on unit-vector families:
`Ω ≈_C₀ Ω'` iff `∑_s (1 - ‖⟪Ω.fam s, Ω'.fam s⟫_ℂ‖) < ∞`.

This is the equivalence relation by which the genuine BR complete infinite
tensor product decomposes into sectors.  Reflexivity and symmetry are proved
here; transitivity in the Setoid sense requires a phase-aligned triangle
inequality (`1 - |⟨u, w⟩| ≤ 2(1 - |⟨u, v⟩|) + 2(1 - |⟨v, w⟩|)`) and is left
to a follow-up. -/
def c0Rel (Ω Ω' : UnitFamily L) : Prop :=
  Summable fun s : L => 1 - ‖⟪Ω.fam s, Ω'.fam s⟫_ℂ‖

/-- The C₀-relation is reflexive on unit families: the per-site default
sequence is the zero sequence. -/
theorem c0Rel.refl (Ω : UnitFamily L) : c0Rel Ω Ω := by
  have h0 : ∀ s : L, 1 - ‖⟪Ω.fam s, Ω.fam s⟫_ℂ‖ = 0 := by
    intro s
    rw [inner_self_eq_norm_sq_to_K, Ω.norm_fam s]
    simp
  unfold c0Rel
  simp_rw [h0]
  exact summable_zero

/-- The C₀-relation is symmetric: `‖⟪u, v⟫_ℂ‖ = ‖⟪v, u⟫_ℂ‖`. -/
theorem c0Rel.symm {Ω Ω' : UnitFamily L} (h : c0Rel Ω Ω') : c0Rel Ω' Ω := by
  have hpt : (fun s : L => 1 - ‖⟪Ω'.fam s, Ω.fam s⟫_ℂ‖)
      = fun s => 1 - ‖⟪Ω.fam s, Ω'.fam s⟫_ℂ‖ := by
    funext s
    rw [← inner_conj_symm, RCLike.norm_conj]
  unfold c0Rel
  rwa [hpt]

/-- The C₀-relation is transitive on unit families, via the phase-aligned
triangle inequality `1 - ‖⟪u, w⟫_ℂ‖ ≤ 2 (1 - ‖⟪u, v⟫_ℂ‖) + 2 (1 - ‖⟪v, w⟫_ℂ‖)`
for unit vectors. -/
theorem c0Rel.trans {Ω Ω' Ω'' : UnitFamily L}
    (h₁ : c0Rel Ω Ω') (h₂ : c0Rel Ω' Ω'') : c0Rel Ω Ω'' := by
  unfold c0Rel
  refine Summable.of_nonneg_of_le ?nonneg ?bound
    ((h₁.mul_left 2).add (h₂.mul_left 2))
  · intro s
    have hub : ‖⟪Ω.fam s, Ω''.fam s⟫_ℂ‖ ≤ 1 := by
      calc ‖⟪Ω.fam s, Ω''.fam s⟫_ℂ‖
          ≤ ‖Ω.fam s‖ * ‖Ω''.fam s‖ := norm_inner_le_norm _ _
        _ = 1 := by rw [Ω.norm_fam s, Ω''.norm_fam s]; ring
    linarith
  · intro s
    exact ForMathlib.c0_triangle (Ω.fam s) (Ω'.fam s) (Ω''.fam s)
      (Ω.norm_fam s) (Ω'.norm_fam s) (Ω''.norm_fam s)

/-- The Bratteli–Robinson C₀-equivalence on unit-vector families, packaged as
a `Setoid`.  This is the canonical equivalence by which the genuine BR
complete infinite tensor product decomposes into sectors.

ℓ²-equivalence (`strongEquiv`) is strictly finer; the BR equivalence is
the canonical one. -/
def c0Equiv : Setoid (UnitFamily L) where
  r := c0Rel
  iseqv := ⟨c0Rel.refl, c0Rel.symm, c0Rel.trans⟩

/-- Strong (ℓ²) equivalence implies the canonical Bratteli–Robinson
C₀-relation, via the pointwise bound
`1 - ‖⟪u, v⟫_ℂ‖ ≤ ‖u - v‖² / 2` for unit vectors. -/
theorem strongEquiv_le_c0Rel {Ω Ω' : UnitFamily L}
    (h : strongEquiv.r Ω Ω') : c0Rel Ω Ω' := by
  unfold c0Rel
  refine Summable.of_nonneg_of_le ?nonneg ?bound (h.mul_left (1 / 2))
  · intro s
    have hub : ‖⟪Ω.fam s, Ω'.fam s⟫_ℂ‖ ≤ 1 := by
      calc ‖⟪Ω.fam s, Ω'.fam s⟫_ℂ‖
          ≤ ‖Ω.fam s‖ * ‖Ω'.fam s‖ := norm_inner_le_norm _ _
        _ = 1 := by rw [Ω.norm_fam s, Ω'.norm_fam s]; ring
    linarith
  · intro s
    -- For unit u, v in a complex IPS,
    --   ‖u - v‖² = 2 - 2 Re ⟪u, v⟫_ℂ ≥ 2(1 - ‖⟪u, v⟫_ℂ‖)
    -- since Re z ≤ ‖z‖ for any complex z.
    have hsub : ‖Ω.fam s - Ω'.fam s‖ ^ 2
        = 2 - 2 * RCLike.re ⟪Ω.fam s, Ω'.fam s⟫_ℂ := by
      rw [@norm_sub_sq ℂ _ _ _ _ (Ω.fam s) (Ω'.fam s), Ω.norm_fam s,
          Ω'.norm_fam s]
      ring
    have hre_le_abs :
        RCLike.re (⟪Ω.fam s, Ω'.fam s⟫_ℂ) ≤ ‖⟪Ω.fam s, Ω'.fam s⟫_ℂ‖ :=
      RCLike.re_le_norm _
    linarith

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

/-! ### Canonical (quotient) variant of the complete tensor product -/

/-- Classical decidable equality on `Quotient strongEquiv`. -/
noncomputable instance : DecidableEq (Quotient (strongEquiv (L := L))) :=
  Classical.decEq _

/-- The Hilbert space attached to a `strongEquiv`-class via its `Quotient.out`
representative. -/
abbrev SectorHilbertOfClass (c : Quotient (strongEquiv (L := L))) : Type _ :=
  SectorHilbert (Quotient.out c)

noncomputable instance instNormedAddCommGroupSectorHilbertOfClass
    (c : Quotient (strongEquiv (L := L))) :
    NormedAddCommGroup (SectorHilbertOfClass c) :=
  inferInstanceAs (NormedAddCommGroup (SectorHilbert (Quotient.out c)))

noncomputable instance instInnerProductSpaceSectorHilbertOfClass
    (c : Quotient (strongEquiv (L := L))) :
    InnerProductSpace ℂ (SectorHilbertOfClass c) :=
  inferInstanceAs (InnerProductSpace ℂ (SectorHilbert (Quotient.out c)))

/-- The canonical Bratteli–Robinson §2.7.2 complete infinite tensor product:
the `lp 2`-direct sum of the canonical sector Hilbert spaces, indexed by
`strongEquiv`-equivalence classes (instead of all unit families).  This
collapses the redundancy in `fullInfTensorHilbert L` (where multiple unit
families representing the same class give distinct summands) by picking one
representative per class via `Quotient.out`.

Built relative to `strongEquiv` (ℓ²-equivalence): the BR canonical
C₀-equivalence is coarser, so this is still a covering of the BR object,
but the redundancy is now controlled by the strict-vs-C₀ gap rather than
all distinct unit families. -/
noncomputable def fullInfTensorHilbertCanonical (L : Type*)
    [DecidableEq L] [LocalNetLike L] : Type _ :=
  lp (fun c : Quotient (strongEquiv (L := L)) => SectorHilbertOfClass c) 2

noncomputable instance :
    NormedAddCommGroup (fullInfTensorHilbertCanonical L) :=
  inferInstanceAs (NormedAddCommGroup
    (lp (fun c : Quotient (strongEquiv (L := L)) => SectorHilbertOfClass c) 2))

noncomputable instance :
    InnerProductSpace ℂ (fullInfTensorHilbertCanonical L) :=
  inferInstanceAs (InnerProductSpace ℂ
    (lp (fun c : Quotient (strongEquiv (L := L)) => SectorHilbertOfClass c) 2))

noncomputable instance : CompleteSpace (fullInfTensorHilbertCanonical L) :=
  inferInstanceAs (CompleteSpace
    (lp (fun c : Quotient (strongEquiv (L := L)) => SectorHilbertOfClass c) 2))

/-- The canonical isometric embedding of the representative sector at a
class `c` into the canonical complete tensor product. -/
noncomputable def sectorEmbedOfClass (c : Quotient (strongEquiv (L := L))) :
    SectorHilbertOfClass c →ₗᵢ[ℂ] fullInfTensorHilbertCanonical L where
  toLinearMap := lp.lsingle 2 c
  norm_map' x := lp.norm_single (by norm_num : (0 : ENNReal) < 2) c x

/-! ### Genuine BR canonical complete tensor product via `c0Equiv` -/

/-- Classical decidable equality on `Quotient c0Equiv`. -/
noncomputable instance : DecidableEq (Quotient (c0Equiv (L := L))) :=
  Classical.decEq _

/-- The Hilbert space attached to a `c0Equiv`-class via its `Quotient.out`
representative.  This is the canonical Bratteli–Robinson sector. -/
abbrev SectorHilbertOfBRClass (c : Quotient (c0Equiv (L := L))) : Type _ :=
  SectorHilbert (Quotient.out c)

noncomputable instance instNormedAddCommGroupSectorHilbertOfBRClass
    (c : Quotient (c0Equiv (L := L))) :
    NormedAddCommGroup (SectorHilbertOfBRClass c) :=
  inferInstanceAs (NormedAddCommGroup (SectorHilbert (Quotient.out c)))

noncomputable instance instInnerProductSpaceSectorHilbertOfBRClass
    (c : Quotient (c0Equiv (L := L))) :
    InnerProductSpace ℂ (SectorHilbertOfBRClass c) :=
  inferInstanceAs (InnerProductSpace ℂ (SectorHilbert (Quotient.out c)))

/-- The genuine Bratteli–Robinson §2.7.2 canonical complete infinite tensor
product: the `lp 2`-direct sum of canonical sector Hilbert spaces indexed by
`c0Equiv` (BR C₀)-equivalence classes.

Unlike `fullInfTensorHilbertCanonical L` (which uses the strictly finer
`strongEquiv`), this object has exactly one direct summand per BR
equivalence class. -/
noncomputable def fullInfTensorHilbertBR (L : Type*)
    [DecidableEq L] [LocalNetLike L] : Type _ :=
  lp (fun c : Quotient (c0Equiv (L := L)) => SectorHilbertOfBRClass c) 2

noncomputable instance :
    NormedAddCommGroup (fullInfTensorHilbertBR L) :=
  inferInstanceAs (NormedAddCommGroup
    (lp (fun c : Quotient (c0Equiv (L := L)) => SectorHilbertOfBRClass c) 2))

noncomputable instance :
    InnerProductSpace ℂ (fullInfTensorHilbertBR L) :=
  inferInstanceAs (InnerProductSpace ℂ
    (lp (fun c : Quotient (c0Equiv (L := L)) => SectorHilbertOfBRClass c) 2))

noncomputable instance : CompleteSpace (fullInfTensorHilbertBR L) :=
  inferInstanceAs (CompleteSpace
    (lp (fun c : Quotient (c0Equiv (L := L)) => SectorHilbertOfBRClass c) 2))

/-- The canonical isometric embedding of the BR-representative sector at a
class `c` into the BR canonical complete tensor product. -/
noncomputable def sectorEmbedOfBRClass (c : Quotient (c0Equiv (L := L))) :
    SectorHilbertOfBRClass c →ₗᵢ[ℂ] fullInfTensorHilbertBR L where
  toLinearMap := lp.lsingle 2 c
  norm_map' x := lp.norm_single (by norm_num : (0 : ENNReal) < 2) c x

end LocalNetLike
