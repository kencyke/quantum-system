module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import QuantumSystem.Analysis.InfiniteTensor.Completion
public import QuantumSystem.Analysis.InfiniteTensor.SectorEquiv
public import QuantumSystem.Analysis.InfiniteTensor.SectorIsometry

/-!
# Bratteli–Robinson sector decomposition Hilbert space

For a Hilbert family `H : ι → Type*` (finite-dim per factor), this file
assembles the sectorwise Hilbert spaces `ITPSector H Ω` (Phase 2) into the
**Bratteli–Robinson sector decomposition Hilbert space**

```
decomposableTensorProduct H : Type*
```

defined as the `ℓ²` direct sum of one `ITPSector` per `c0Equiv`-class of
unit-vector reference families:

```
decomposableTensorProduct H := lp (fun q : Quotient c0Equiv => ITPSector H q.out) 2
```

## Caveats

This is **not** the von Neumann complete infinite tensor product (which is
non-separable and decomposes into uncountably many sectors).  Following the
migration plan, `decomposableTensorProduct H` is the *separable* sector
decomposition indexed by the Bratteli–Robinson C₀-equivalence classes
(`c0Equiv`).

The use of `Quotient.out` to pick a canonical representative for each class
is non-canonical (relies on `Classical.choice`).  The Hilbert-space
*structure* on `decomposableTensorProduct H` is independent of this choice
— this is the content of the (still-pending) sector-isometry theorem
`sectorEquivOfEquivalent` (Phase 3a) which, together with the fiberwise
lift (Phase 6b), would package the canonical structure intrinsically.  At
the present level, the type itself depends on `Quotient.out`'s choice; only
its norm structure (via `regionEmbedLeIsom`-isometry on each fiber) is
canonical.

## Main definitions

* `InfiniteTensor.decomposableTensorProduct H` — the Hilbert sector
  decomposition.
* Hilbert-space instances (`NormedAddCommGroup`, `InnerProductSpace ℂ`,
  `CompleteSpace`) inherited from `lp G 2`.

## References

* Bratteli, Robinson, *Operator Algebras and Quantum Statistical
  Mechanics II*, §2.7.2 (sector decomposition).
* Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §3.5.
-/

@[expose] public section

open scoped InnerProductSpace

namespace InfiniteTensor

variable {ι : Type*} [DecidableEq ι] (H : ι → Type*)
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
  [∀ i, FiniteDimensional ℂ (H i)]

/-- The **Bratteli–Robinson sector decomposition Hilbert space** of `H`.

Defined as the `ℓ²` direct sum of `ITPSector H q.out` over the BR
C₀-equivalence classes `q : Quotient c0Equiv`, where `Quotient.out` picks a
representative of each class.

This is the *separable* sector decomposition (one summand per `c0Equiv`
class), **not** the non-separable von Neumann complete tensor product.

Declared `abbrev` so that `lp`-level lemmas (`lp.norm_single`,
`lp.lsingle`, …) apply transparently to elements of
`decomposableTensorProduct H` without manual `unfold`. -/
noncomputable abbrev decomposableTensorProduct : Type _ :=
  lp (fun q : Quotient (UnitFamily.c0Equiv (H := H)) =>
        UnitFamily.ITPSector (H := H) q.out) 2

namespace decomposableTensorProduct

noncomputable instance instNormedAddCommGroup :
    NormedAddCommGroup (decomposableTensorProduct H) :=
  inferInstanceAs (NormedAddCommGroup (lp _ 2))

noncomputable instance instNormedSpace :
    NormedSpace ℂ (decomposableTensorProduct H) :=
  inferInstanceAs (NormedSpace ℂ (lp _ 2))

noncomputable instance instInnerProductSpace :
    InnerProductSpace ℂ (decomposableTensorProduct H) :=
  inferInstanceAs (InnerProductSpace ℂ (lp _ 2))

instance instCompleteSpace : CompleteSpace (decomposableTensorProduct H) :=
  inferInstanceAs (CompleteSpace (lp _ 2))

end decomposableTensorProduct

/-- Classical decidable equality on `c0Equiv` classes, required for downstream
`lp.single`-based constructions. -/
noncomputable instance instDecidableEqQuotient :
    DecidableEq (Quotient (UnitFamily.c0Equiv (H := H))) := Classical.decEq _

/-! ## Per-sector embeddings into the decomposable space

The sector embedding `sectorEmbed Ω : ITPSector H Ω →ₗᵢ[ℂ]
decomposableTensorProduct H` is built in two stages:

* **Representative case** (`sectorEmbedRepr q`).  For `Ω = q.out` (the
  chosen representative of its `c0Equiv`-class), the embedding is
  `lp.lsingle 2 q` packaged as a `LinearIsometry` via `lp.norm_single`.
* **General case** (`sectorEmbed Ω`).  Any `Ω` is first transported to its
  representative `(⟦Ω⟧ : Quotient c0Equiv).out` via
  `sectorEquivOfEquivalent` (`SectorIsometry.lean`, Route 2,
  non-canonical), then handed to the representative case.

The construction is non-canonical: `sectorEquivOfEquivalent` consumes
per-site rotations via `Classical.choice`.  The norm preservation
property (and hence the type of `sectorEmbed`) is canonical. -/

open UnitFamily in
/-- The sector embedding `sectorEmbed Ω : ITPSector H Ω →ₗᵢ[ℂ]
decomposableTensorProduct H`.

The construction composes two stages:

* **Sector transport** (non-canonical, `Classical.choice`-based):
  `sectorEquivOfEquivalent` maps `ITPSector H Ω` isometrically to
  `ITPSector H q.out`, where `q = ⟦Ω⟧ : Quotient c0Equiv`.
* **Representative case**: `lp.lsingle 2 q` packaged as a `LinearIsometry`
  via `lp.norm_single`, injecting `ITPSector H q.out` into the
  `q`-summand of `decomposableTensorProduct H = lp (fun q' => ITPSector
  H q'.out) 2`.

**Non-canonical**: the per-site rotations inside
`sectorEquivOfEquivalent` are chosen via `Classical.choice`.  The
isometry property (norm preservation) is canonical regardless. -/
noncomputable def sectorEmbed (Ω : UnitFamily H) :
    UnitFamily.ITPSector (H := H) Ω →ₗᵢ[ℂ] decomposableTensorProduct H := by
  let E : Quotient (UnitFamily.c0Equiv (H := H)) → Type _ :=
    fun q' => UnitFamily.ITPSector (H := H) q'.out
  let q : Quotient (UnitFamily.c0Equiv (H := H)) := Quotient.mk'' Ω
  have hrel : UnitFamily.c0Rel Ω q.out :=
    UnitFamily.c0Rel.symm
      (Quotient.mk_out (s := UnitFamily.c0Equiv (H := H)) Ω)
  let g : UnitFamily.ITPSector (H := H) Ω →ₗᵢ[ℂ] E q :=
    (UnitFamily.sectorEquivOfEquivalent Ω q.out hrel).toLinearIsometry
  let f : E q →ₗᵢ[ℂ] lp E 2 := by
    refine ⟨(lp.lsingle 2 q : E q →ₗ[ℂ] lp E 2), ?_⟩
    intro x
    have hp : (0 : ENNReal) < 2 := by norm_num
    exact lp.norm_single (E := E) hp q x
  exact f.comp g

end InfiniteTensor
