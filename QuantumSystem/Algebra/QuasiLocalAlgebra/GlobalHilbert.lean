module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import QuantumSystem.Algebra.LocalNetLike

/-!
# Reference-sector infinite-site Hilbert space

Following Naaijkens 2012 §3.5 / Bratteli–Robinson Vol. 2 §2.7.2, the
infinite-site Hilbert space used here is the concrete reference sector of an
incomplete infinite tensor product.  It is built from a fixed reference basis
tuple `Ω : (s : L) → localIdx s` and the basis tuples that differ from `Ω` at
only finitely many sites.

This file does not introduce a separate bundled infinite tensor product object
or prove a universal property for one.  Instead it constructs the standard
basis-indexed model for that reference sector.

## Comparison with von Neumann's infinite tensor product

The classical construction (Naaijkens §3.5; Bratteli–Robinson II §2.7.2)
starts from an arbitrary unit vector `Ω_s ∈ ℋ_s` at each site, takes formal
tensors `⊗_s ξ_s` with `ξ_s = Ω_s` outside a finite set, and completes the
resulting pre-Hilbert space.  The full infinite tensor product so obtained
decomposes into mutually inequivalent sectors indexed by equivalence classes
of reference choices.

The construction in this file deviates in four deliberate ways:

* the reference vector at each site is restricted to a basis index
  `referenceBasis L s : localIdx s` rather than an arbitrary unit vector —
  no loss of Hilbert-space generality (a basis change reduces to this case),
  but the freedom is removed at the type level;
* the Hilbert space is realised as `lp (fun _ : globalIdx L => ℂ) 2` over
  the ONB index set, not as the metric completion of formal tensors; the
  two are isometrically isomorphic, but no `⊗_s ξ_s` notation is exposed
  here;
* only the single sector selected by `referenceBasis L` is built; the other
  sectors of the incomplete infinite tensor product are out of scope;
* the tensor-product structure (finite-region embeddings, the action of
  local algebras) is not constructed in this file — see `LocalEmbed.lean`.

Concretely we:

1. fix `referenceBasis L s : localIdx s` via the assumed
   `Nonempty (localIdx s)` instance (`Nonempty.some`);
2. define `globalIdx L` as the subtype of basis tuples that agree with
   `referenceBasis L` outside some finite set; and
3. take `globalHilbert L := ↥(lp (fun _ : globalIdx L => ℂ) 2)`, which
   inherits its Hilbert-space structure from `lp.instInnerProductSpace`
   in `Mathlib.Analysis.InnerProductSpace.l2Space`.

The finite-region tuple extensions and the represented local-algebra embeddings
into `B(globalHilbert L)` are introduced in
`QuantumSystem/Algebra/QuasiLocalAlgebra/LocalEmbed.lean`.

## Main definitions

* `LocalNetLike.referenceBasis L s` — chosen reference basis index at site
  `s`, supplied by the per-site `Nonempty` assumption.
* `LocalNetLike.globalIdx L` — the index type for the reference sector:
  basis tuples that agree with `referenceBasis L` outside a finite region.
* `LocalNetLike.globalHilbert L` — the reference-sector infinite-site Hilbert
  space, realised as `↥(lp (fun _ : globalIdx L => ℂ) 2)`.

## References

* Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §3.5.
* Bratteli, Robinson, *Operator Algebras and Quantum Statistical Mechanics II*,
  §2.7.2.
-/

@[expose] public section

namespace LocalNetLike

variable (L : Type*) [DecidableEq L] [LocalNetLike L]
    [hL : ∀ s : L, Nonempty (LocalNetLike.localIdx (L := L) s)]

/-- A chosen reference basis index at each site, used to build the reference
sector as the ℓ² completion of finite-variation tuples. -/
noncomputable def referenceBasis (s : L) : LocalNetLike.localIdx (L := L) s :=
  (hL s).some

/-- Index type for the reference sector: basis tuples that agree with
`referenceBasis L` outside a finite set of sites. -/
def globalIdx : Type _ :=
  { f : (s : L) → LocalNetLike.localIdx (L := L) s //
      ∃ Λ : Finset L, ∀ s ∉ Λ, f s = referenceBasis L s }

/-- The reference-sector infinite-site Hilbert space, realised as
`↥(lp (fun _ : globalIdx L => ℂ) 2)`.

This is the concrete ℓ² model of the incomplete infinite tensor product sector
selected by `referenceBasis L`; no separate tensor-product object is bundled
here.

The `InnerProductSpace ℂ` and `CompleteSpace` instances are inherited from
`lp.instInnerProductSpace` and `lp.completeSpace` in
`Mathlib.Analysis.InnerProductSpace.l2Space`. -/
noncomputable abbrev globalHilbert : Type _ :=
  ↥(lp (fun _ : globalIdx L => ℂ) 2)

end LocalNetLike
