module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import QuantumSystem.Algebra.LocalNetLike

/-!
# Sector-parametrised concrete lattice representation

The infinite-site Hilbert space here is the concrete sector of an incomplete
infinite tensor product attached to a chosen basis tuple
`Ω : (s : L) → localIdx s` (Naaijkens 2012 §3.5 / Bratteli–Robinson Vol. 2
§2.7.2).  Every API takes `Ω` as an explicit argument, so distinct choices
give distinct sectors.

This file is a **concrete representation layer** for the lattice model; the
AQFT superselection-sector API (where sectors are equivalence classes of
representations) sits at a different abstraction level and the semantic
alias `concreteLatticeRepresentation L Ω` records this role.

## Comparison with von Neumann's infinite tensor product

The classical construction starts from arbitrary unit vectors `Ω_s ∈ ℋ_s`,
takes formal tensors `⊗_s ξ_s` with `ξ_s = Ω_s` outside a finite set, and
completes.  This file deviates in three ways:

* the sector vector at each site is restricted to a basis index `Ω s`
  rather than an arbitrary unit vector;
* the Hilbert space is realised as `lp (fun _ : globalIdx L Ω => ℂ) 2`,
  isometrically isomorphic to the metric completion of formal tensors
  but without `⊗_s ξ_s` notation;
* the tensor-product structure (finite-region embeddings, action of
  local algebras) lives in `LocalEmbed.lean`.

The Hilbert-space structure is inherited from `lp.instInnerProductSpace`
in `Mathlib.Analysis.InnerProductSpace.l2Space`.

## Main definitions

* `LocalNetLike.globalIdx L Ω` — basis tuples agreeing with `Ω` outside a
  finite region.
* `LocalNetLike.globalHilbert L Ω` — the Ω-sector Hilbert space
  `↥(lp (fun _ : globalIdx L Ω => ℂ) 2)`.
* `LocalNetLike.concreteLatticeRepresentation L Ω` — semantic alias for
  `globalHilbert L Ω`.

## References

* Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §3.5.
* Bratteli, Robinson, *Operator Algebras and Quantum Statistical Mechanics II*,
  §2.7.2.
-/

@[expose] public section

namespace LocalNetLike

variable (L : Type*) [DecidableEq L] [LocalNetLike L]

/-- Index type for the Ω-sector: basis tuples that agree with the chosen
sector tuple `Ω` outside a finite set of sites. -/
def globalIdx (Ω : (s : L) → LocalNetLike.localIdx (L := L) s) : Type _ :=
  { f : (s : L) → LocalNetLike.localIdx (L := L) s //
      ∃ Λ : Finset L, ∀ s ∉ Λ, f s = Ω s }

/-- The Ω-sector infinite-site Hilbert space
`↥(lp (fun _ : globalIdx L Ω => ℂ) 2)`: the concrete ℓ² model of the
incomplete infinite tensor product sector selected by `Ω`.

`InnerProductSpace ℂ` and `CompleteSpace` instances are inherited from
`lp.instInnerProductSpace` / `lp.completeSpace` in `Mathlib`. -/
noncomputable abbrev globalHilbert
    (Ω : (s : L) → LocalNetLike.localIdx (L := L) s) : Type _ :=
  ↥(lp (fun _ : globalIdx L Ω => ℂ) 2)

/-- Semantic alias for `globalHilbert L Ω` when used as a concrete lattice
representation of the observable algebra; definitionally equal to it. -/
noncomputable abbrev concreteLatticeRepresentation
    (Ω : (s : L) → LocalNetLike.localIdx (L := L) s) : Type _ :=
  globalHilbert L Ω

end LocalNetLike
