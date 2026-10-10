/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.CStarAlgebra.GNS.Construction
public import QuantumSystem.Physics.LocalNet.InfiniteRegion

/-!
# The split property of a state and the half-chain split property

The lattice literature's split property is a statement about a *state* on the quasi-local algebra
and about **infinite** regions (`QuantumSystem.Physics.LocalNet.InfiniteRegion`):

* `LocalNet.IsSplitPairAt ω S₁ S₂` is the split property of a *state* `ω` on the quasi-local
  algebra for a pair of regions, in the GNS representation of `ω`, and
  `LocalNet.HasHalfChainSplit ω` is the **half-chain split property** in its split-inclusion
  form, the pair `(-∞, 0]`, `[1, ∞)` of the integer chain. Matsui's own definition is the
  quasi-equivalence of `ω` with the product `ω_L ⊗ ω_R` of its half-chain restrictions. The
  split-inclusion form implies it for every state, and the two agree for pure (more generally
  factor) states; their agreement for an arbitrary state is not claimed here.

## What is and is not expressible

Both half-chain forms are expressible. The *gapped* form follows from the nested split property:
on the integer chain with `ofCThickening ℤ 1`, `Set.Iic 0 ⋐ Set.Iic 2`, and
`VonNeumannNet.SplitProperty.isSplitPair` against `Set.Ici 3` gives `𝓡(Iic 0) ≤ 𝔑 ≤ 𝓡(Ici 3)′`
(`LocalNet.IsSplitPairAt.of_splitProperty`). Matsui's *gap-free* form, between `𝓡(Iic 0)` and
`𝓡(Ici 1)′`, cannot come from `⋐`, since `⋐` is irreflexive; it is stated directly as a split pair
(`VonNeumannNet.IsSplitPair`, `LocalNet.HasHalfChainSplit`).

Matsui's defining form — `ω` quasi-equivalent to `ω_L ⊗ ω_R` — is not expressible yet: it needs
the identification of the chain's quasi-local algebra with `𝔄_L ⊗ 𝔄_R` and product states on it,
neither of which is built. Its equivalence with the split-inclusion form is therefore not proved
either.

What is also not proved is Matsui's characterisation for pure states — the half-chain split
property holds iff `𝓡(Iic 0)` is a type I factor. The representation-theoretic input is
available — the GNS representation of a pure state is irreducible
(`GNS.Representation.isPure_iff_isIrreducible`) and so has commutant `ℂ1`
(`CStarRep.isIrreducible_iff_centralizer`) — but the argument also needs
joins of von Neumann algebras, which the development does not have yet. Cones need a cone region
type and are not built here. No spin net is built either, so no non-trivial positive model of the
infinite-region split property exists yet;
`QuantumSystem.Physics.LocalNet.Examples` has refuters and one-dimensional witnesses.

## TODO

* Matsui's quasi-equivalence form of the half-chain split property, once `𝔄 ≅ 𝔄_L ⊗ 𝔄_R` and
  product states are available, with the implication from `LocalNet.HasHalfChainSplit` (valid for
  every state) and the converse for pure, more generally factor, states.
* Settle the converse for an arbitrary, possibly mixed, state: whether quasi-equivalence of `ω`
  with `ω_L ⊗ ω_R` yields a type I factor `𝔑` with `𝓡_ω((-∞, 0]) ≤ 𝔑 ≤ 𝓡_ω([1, ∞))′` in the GNS
  representation of `ω` itself. Quasi-equivalence gives such a factor only after amplification,
  and it is not checked here whether it can be compressed back to the GNS space; until then the
  two forms are not asserted to agree beyond factor states.

## Notation

`𝓡(S)` in the prose above is documentation shorthand for `vnNet.extend.algebra S`, following the
convention stated in `QuantumSystem.Physics.LocalNet.Basic`.
-/

@[expose] public section

open scoped ProperContainment VonNeumannAlgebra ComplexOrder GNS

namespace LocalNet

variable {α : Type*} (N : LocalNet (Finset α)) [N.Faithful]

/-! ### The split property of a state -/

section State

variable [PartialOrder N.quasiLocalCStarAlgebra] [StarOrderedRing N.quasiLocalCStarAlgebra]

/-- **The split property of a state for a pair of regions**: in the GNS representation of the
    state `ω` on the quasi-local algebra, the regions `S₁` and `S₂` form a split pair
    (`VonNeumannNet.IsSplitPair`), `𝓡_ω(S₁) ≤ 𝔑 ≤ 𝓡_ω(S₂)′` with `𝔑` a type I factor. The regions
    may be infinite; `𝓡_ω` is `N.vonNeumannNetSet` at the GNS representation
    `GNS[ω].toCStarRep`.

    The order on the quasi-local algebra is a parameter rather than a fixed choice, because
    `State` needs one and the quasi-local algebra carries none; the spectral order
    `CStarAlgebra.spectralOrder` is the canonical instance. -/
def IsSplitPairAt (ω : State N.quasiLocalCStarAlgebra) (S₁ S₂ : Set α) : Prop :=
  (N.vonNeumannNetSet GNS[ω].toCStarRep).IsSplitPair S₁ S₂

/-- **The nested split property yields split pairs with a gap**: if the GNS net of `ω` has the
    split property and `S₁ ⋐ S₂` with `S₃` disjoint from `S₂`, then `(S₁, S₃)` is a split pair
    of `ω`. On the integer chain with `ofCThickening ℤ 1` this gives the gapped half-chain pair
    `(Iic 0, Ici 3)` from `Iic 0 ⋐ Iic 2`; the gap-free pair `(Iic 0, Ici 1)` is not reachable. -/
theorem IsSplitPairAt.of_splitProperty [ProperContainment (Set α)]
    {ω : State N.quasiLocalCStarAlgebra}
    (hs : (N.vonNeumannNetSet GNS[ω].toCStarRep).SplitProperty)
    {S₁ S₂ S₃ : Set α} (h : S₁ ⋐ S₂) (hd : Disjoint S₂ S₃) : N.IsSplitPairAt ω S₁ S₃ :=
  VonNeumannNet.SplitProperty.isSplitPair hs h hd

/-- **Every multiplicative state splits every pair of regions**, trivially: its GNS
    representation acts by scalars (`GNS.Representation.π_eq_smul_one_of_map_mul`), so every local
    algebra lies in the scalar algebra `ℂ1 = 𝓑(H)′`, which is a type I factor
    (`VonNeumannAlgebra.isTypeIFactor_commutant_boundedLinearOperators`) commuting with everything.
    This is the degenerate end of the split property, as the one-dimensional case is for nets. -/
theorem IsSplitPairAt.of_map_mul {ω : State N.quasiLocalCStarAlgebra}
    (hω : ∀ a b, ω (a * b) = ω a * ω b) (S₁ S₂ : Set α) : N.IsSplitPairAt ω S₁ S₂ := by
  refine ⟨_, VonNeumannAlgebra.isTypeIFactor_commutant_boundedLinearOperators, ?_, ?_⟩
  · refine VonNeumannAlgebra.generated_le fun x hx => ?_
    obtain ⟨Λ, -, hx⟩ := VonNeumannNet.mem_finiteLocalOperators.1 hx
    refine VonNeumannAlgebra.generated_le
      (M := (𝓑(GNS[ω].H))′) ?_ hx
    rintro _ ⟨a, rfl⟩
    simp only
    rw [GNS[ω].π_eq_smul_one_of_map_mul hω]
    exact SetLike.mem_coe.2 (SMulMemClass.smul_mem _ (one_mem _))
  · intro x hx
    obtain ⟨c, rfl⟩ := VonNeumannAlgebra.exists_eq_smul_one_of_mem_commutant_boundedLinearOperators hx
    exact VonNeumannAlgebra.mem_commutant_iff.2 fun g _ =>
      (mul_smul_one c g).trans (smul_one_mul c g).symm

end State

section HalfChain

variable (N : LocalNet (Finset ℤ)) [N.Faithful]
variable [PartialOrder N.quasiLocalCStarAlgebra] [StarOrderedRing N.quasiLocalCStarAlgebra]

/-- The **half-chain split property** of a state `ω` on the quasi-local algebra of a chain, in
    split-inclusion form: the left half-chain `(-∞, 0]` and the right half-chain `[1, ∞)` form a
    split pair in the GNS representation of `ω`,

      `𝓡_ω((-∞, 0]) ≤ 𝔑 ≤ 𝓡_ω([1, ∞))′`, with `𝔑` a type I factor.

    The half-chains are adjacent: there is no gap, so this is not a consequence of any nested split
    property through `⋐`.

    Matsui (*The split property and the symmetry breaking of the quantum spin chain*, Comm. Math.
    Phys. 218, 2001) *defines* the split property as the quasi-equivalence of `ω` with
    `ω_L ⊗ ω_R`, the product of its restrictions to the two half-chains. The split inclusion above
    implies that quasi-equivalence for every state, and conversely for pure (more generally
    factor) states; for a pure state both are equivalent to `𝓡_ω((-∞, 0])` being a type I factor.
    Neither the quasi-equivalence form nor these equivalences are formalised (see the module
    docstring). -/
def HasHalfChainSplit (ω : State N.quasiLocalCStarAlgebra) : Prop :=
  N.IsSplitPairAt ω (Set.Iic 0) (Set.Ici 1)

end HalfChain

end LocalNet
