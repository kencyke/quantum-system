module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import QuantumSystem.Analysis.InfiniteTensor.Completion
public import QuantumSystem.Analysis.InfiniteTensor.SectorEquiv

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
class), **not** the non-separable von Neumann complete tensor product. -/
noncomputable def decomposableTensorProduct : Type _ :=
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

/-! ## Pending: per-sector embeddings into the decomposable space

The natural sector-embedding `sectorEmbed Ω : ITPSector H Ω →ₗᵢ[ℂ]
decomposableTensorProduct H` is split into two cases:

* For `Ω = q.out` (the chosen representative of its `c0Equiv`-class), the
  embedding is `lp.single` on slot `q`.
* For general `Ω` in a class, the embedding requires the sector-isometry
  `sectorEquivOfEquivalent : c0Equiv.r Ω q.out → ITPSector H Ω ≃ₗᵢ[ℂ]
  ITPSector H q.out` from Phase 3a (currently pending), composed with the
  representative-case embedding.

The representative-case embedding is structurally `lp.lsingle 2 q`; its
packaging as a `LinearIsometry` is folded into the Phase 3a deliverable so
that the general-`Ω` and representative-`Ω` cases share a single API. -/

end InfiniteTensor
