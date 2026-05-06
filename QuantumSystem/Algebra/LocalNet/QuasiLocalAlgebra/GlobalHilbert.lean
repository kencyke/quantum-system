module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import QuantumSystem.Algebra.LocalNetLike

/-!
# Infinite-site Hilbert space

Following Naaijkens 2012 §3.5 / Bratteli–Robinson Vol. 2 §2.7.2, the
infinite-site Hilbert space of a quantum lattice system is built from a
fixed reference basis tuple `Ω : (s : L) → localIdx s` together with the
ℓ²-summable variations.

Concretely we:

1. fix `referenceBasis L s : localIdx s` via the assumed
   `Nonempty (localIdx s)` instance (`Nonempty.some`);
2. define `globalIdx L` as the subtype of basis tuples that agree with
   `referenceBasis L` outside some finite set; and
3. take `globalHilbert L := ↥(lp (fun _ : globalIdx L => ℂ) 2)`, which
   inherits its Hilbert-space structure from `lp.instInnerProductSpace`
   in `Mathlib.Analysis.InnerProductSpace.l2Space`.

The isometric embeddings `regionHilbert Λ →ₗᵢ globalHilbert L` for varying
`Λ` are introduced in
`QuantumSystem/Algebra/LocalNet/QuasiLocalAlgebra/Embedding.lean`
(Phase 5'a step 4).

## Main definitions

* `LocalNetLike.referenceBasis L s` — chosen reference basis index at site
  `s`, supplied by the per-site `Nonempty` assumption.
* `LocalNetLike.globalIdx L` — the index type for the infinite-site
  Hilbert space: basis tuples that agree with `referenceBasis L` outside a
  finite region.
* `LocalNetLike.globalHilbert L` — the infinite-site Hilbert space,
  realised as `↥(lp (fun _ : globalIdx L => ℂ) 2)`.

## References

* Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §3.5.
* Bratteli, Robinson, *Operator Algebras and Quantum Statistical Mechanics II*,
  §2.7.2.
-/

@[expose] public section

namespace LocalNetLike

variable (L : Type*) [DecidableEq L] [LocalNetLike L]
    [hL : ∀ s : L, Nonempty (LocalNetLike.localIdx (L := L) s)]

/-- A chosen reference basis index at each site, used to build the
infinite-site Hilbert space as the ℓ² completion of finite-variation
tuples. -/
noncomputable def referenceBasis (s : L) : LocalNetLike.localIdx (L := L) s :=
  (hL s).some

/-- Index type for the infinite-site Hilbert space: basis tuples that
agree with `referenceBasis L` outside a finite set of sites. -/
def globalIdx : Type _ :=
  { f : (s : L) → LocalNetLike.localIdx (L := L) s //
      ∃ Λ : Finset L, ∀ s ∉ Λ, f s = referenceBasis L s }

/-- The infinite-site Hilbert space, realised as
`↥(lp (fun _ : globalIdx L => ℂ) 2)`.

The `InnerProductSpace ℂ` and `CompleteSpace` instances are inherited from
`lp.instInnerProductSpace` and `lp.completeSpace` in
`Mathlib.Analysis.InnerProductSpace.l2Space`. -/
noncomputable abbrev globalHilbert : Type _ :=
  ↥(lp (fun _ : globalIdx L => ℂ) 2)

end LocalNetLike
