/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.CStarAlgebra.GNS.Automorphism
public import QuantumSystem.Analysis.CStarAlgebra.GNS.Construction
public import QuantumSystem.Physics.LocalNet.Automorphism.QuasiLocal
public import QuantumSystem.Physics.LocalNet.InfiniteRegion

/-!
# The split property of a state and the half-chain split property

The lattice literature's split property is a statement about a *state* on the quasi-local algebra
and about **infinite** regions (`QuantumSystem.Physics.LocalNet.InfiniteRegion`). For a graded-local
net it is stated for an **even** state `ω`, one invariant under the quasi-local parity: the parity is
then implemented on the GNS space of `ω` by a selfadjoint unitary `Γ_ω` fixing the cyclic vector
(`GradedLocalNet.gnsParity`, from `GNS.Representation.exists_implementing`), which grades the GNS
net (`GradedLocalNet.gnsGrading`), and the net is graded-local with that grading
(`GradedLocalNet.isGradedLocal_gnsGrading`).

* `GradedLocalNet.IsSplitPairAt ω S₁ S₂` is the split property of an even state `ω` for a pair
  of regions: a type I factor between `𝓡_ω(S₁)` and the *twisted* commutant `Z 𝓡_ω(S₂)′ Z⋆`
  (`VonNeumannNet.Grading.IsSplitPair`). For a local net every state is even, `Γ_ω = 1`, and this
  is the commutant form `𝓡_ω(S₁) ≤ 𝔑 ≤ 𝓡_ω(S₂)′` (`GradedLocalNet.isSplitPairAt_iff_of_isTriviallyGraded`).
  The commutant itself would be the wrong target for a net with fermions: odd elements of disjoint
  regions anticommute, so `𝓡_ω(S₁) ≤ 𝓡_ω(S₂)′` fails whenever such a product is nonzero.
* `GradedLocalNet.HasHalfChainSplit ω` is the **half-chain split property** in its
  split-inclusion form, the pair `(-∞, 0]`, `[1, ∞)` of the integer chain. Another form is the
  quasi-equivalence of `ω` with the product `ω_L ⊗ ω_R` of its half-chain restrictions. For a local
  net, the split-inclusion form implies it for every state, and the two agree for pure (more
  generally factor) states; their agreement for an arbitrary state is not claimed here.

## What is and is not expressible

Both half-chain forms are expressible. The *gapped* form follows from the nested split property:
on the integer chain with `ofCThickening ℤ 1`, `Set.Iic 0 ⋐ Set.Iic 2`, and
`VonNeumannNet.SplitProperty.isGradedSplitPair` against `Set.Ici 3` gives
`𝓡_ω(Iic 0) ≤ 𝔑 ≤ Z 𝓡_ω(Ici 3)′ Z⋆` (`GradedLocalNet.IsSplitPairAt.of_splitProperty`). The
*gap-free* form, between `𝓡_ω(Iic 0)` and `Z 𝓡_ω(Ici 1)′ Z⋆`, cannot come from `⋐`, since `⋐` is
irreflexive; it is stated directly as a graded split pair (`GradedLocalNet.HasHalfChainSplit`).

The quasi-equivalence form — `ω` quasi-equivalent to `ω_L ⊗ ω_R` — is not expressible yet: it needs
the identification of the chain's quasi-local algebra with `𝔄_L ⊗ 𝔄_R` and product states on it,
neither of which is built. Its equivalence with the split-inclusion form is therefore not proved
either.

What is also not proved is the characterisation for pure states — the half-chain split
property of a local net holds iff `𝓡_ω(Iic 0)` is a type I factor. The representation-theoretic
input is available — the GNS representation of a pure state is irreducible
(`GNS.Representation.isPure_iff_isIrreducible`) and so has commutant `ℂ1`
(`CStarRep.isIrreducible_iff_centralizer`) — but the argument also needs
joins of von Neumann algebras, which the development does not have yet. Cones need a cone region
type and are not built here. The split property of the spin chain (`GradedLocalNet.piMinTensorProduct`) on
infinite regions is not proved either: `QuantumSystem.Physics.LocalNet.Examples` proves it on finite
regions, where it is automatic in a unital representation, and for a single site against a
half-chain. The only states shown here to have the half-chain split property are the even
multiplicative ones (`GradedLocalNet.HasHalfChainSplit.of_map_mul`), where it is degenerate; none
is shown to lack it.

## TODO

* The quasi-equivalence form of the half-chain split property, once `𝔄 ≅ 𝔄_L ⊗ 𝔄_R` and
  product states are available, with the implication from `GradedLocalNet.HasHalfChainSplit` (valid for
  every state of a local net) and the converse for pure, more generally factor, states.
* Settle the converse for an arbitrary, possibly mixed, state: whether quasi-equivalence of `ω`
  with `ω_L ⊗ ω_R` yields a type I factor `𝔑` with `𝓡_ω((-∞, 0]) ≤ 𝔑 ≤ 𝓡_ω([1, ∞))′` in the GNS
  representation of `ω` itself. Quasi-equivalence gives such a factor only after amplification,
  and it is not checked here whether it can be compressed back to the GNS space; until then the
  two forms are not asserted to agree beyond factor states.

## Notation

`𝓡_ω(S)` in the prose is documentation shorthand for `(N.vonNeumannNetSet GNS[ω].toCStarRep).algebra S`,
the local von Neumann algebra of a possibly infinite region `S` in the GNS representation of `ω`,
and `Z` for the twist of the grading `N.gnsGrading ω`.

`𝔑` denotes an interpolating type I factor.
-/

@[expose] public section

open scoped ProperContainment VonNeumannAlgebra ComplexOrder GNS CausalOrthogonality

namespace GradedLocalNet

variable {α : Type*} (N : GradedLocalNet (Finset α)) [N.Faithful]

/-! ### The split property of a state -/

section State

variable [PartialOrder N.quasiLocalCStarAlgebra] [StarOrderedRing N.quasiLocalCStarAlgebra]

/-- An **even state** on the quasi-local algebra of a graded-local net: a state invariant under the
    quasi-local parity. Whether a state is even depends on the state; every state of a local net is
    even (`GradedLocalNet.instIsEvenStateOfIsTriviallyGraded`). -/
class IsEvenState (ω : State N.quasiLocalCStarAlgebra) : Prop where
  /-- The state is invariant under the quasi-local parity. -/
  map_quasiLocalParity : ∀ a, ω (N.quasiLocalParity a) = ω a

/-- The **parity on the GNS space of an even state** `ω`: the selfadjoint unitary implementing the
    quasi-local parity in the GNS representation of `ω`, fixing the cyclic vector
    (`GNS.Representation.implementing`). -/
noncomputable def gnsParity (ω : State N.quasiLocalCStarAlgebra)
    [N.IsEvenState ω] : GNS[ω].H →L[ℂ] GNS[ω].H :=
  GNS[ω].implementing N.quasiLocalParity N.quasiLocalParity_quasiLocalParity
    IsEvenState.map_quasiLocalParity

variable {N} in
/-- The GNS parity implements the parity of the local algebras: `π(γ a) = Γ_ω π(a) Γ_ω`. -/
lemma ofQuasiLocal_gns_π_parity (ω : State N.quasiLocalCStarAlgebra)
    [N.IsEvenState ω] (O : Finset α) (a : N.algebra O) :
    (CStarNet.Rep.ofQuasiLocal N.toCStarNet GNS[ω].toCStarRep).π O (N.parity O a) =
      N.gnsParity ω * (CStarNet.Rep.ofQuasiLocal N.toCStarNet GNS[ω].toCStarRep).π O a *
        N.gnsParity ω := by
  rw [CStarNet.Rep.ofQuasiLocal_π_apply, CStarNet.Rep.ofQuasiLocal_π_apply,
    ← quasiLocalParity_ιLocalCStar]
  exact GNS[ω].π_apply_eq_implementing_mul _ _ _ _

/-- The **grading of the GNS net of an even state**: the GNS parity grades the local von Neumann
    algebras of the finite regions (`CStarNet.Rep.vonNeumannGrading`) and hence of all regions
    (`VonNeumannNet.Grading.extend`). -/
noncomputable def gnsGrading (ω : State N.quasiLocalCStarAlgebra)
    [N.IsEvenState ω] :
    (N.vonNeumannNetSet GNS[ω].toCStarRep).Grading :=
  ((CStarNet.Rep.ofQuasiLocal N.toCStarNet GNS[ω].toCStarRep).vonNeumannGrading N.toGrading
    (N.gnsParity ω) (GNS[ω].isSelfAdjoint_implementing _ _ _)
    (GNS[ω].implementing_mul_implementing _ _ _) (ofQuasiLocal_gns_π_parity ω)).extend

/-- The grading unitary of the GNS grading is the GNS parity. -/
@[simp] lemma gnsGrading_Γ (ω : State N.quasiLocalCStarAlgebra)
    [N.IsEvenState ω] : (N.gnsGrading ω).Γ = N.gnsParity ω :=
  rfl

/-- **The GNS net of an even state is graded-local**: graded locality of the net passes to its
    representation (`CStarNet.Rep.isGradedLocal_vonNeumannGrading`), disjoint finite regions having
    the common upper bound `Λ₁ ∪ Λ₂`, and then to all regions
    (`VonNeumannNet.Grading.IsGradedLocal.extend`). -/
lemma isGradedLocal_gnsGrading (ω : State N.quasiLocalCStarAlgebra)
    [N.IsEvenState ω] : (N.gnsGrading ω).IsGradedLocal := by
  classical
  refine VonNeumannNet.Grading.IsGradedLocal.extend ?_
  refine CStarNet.Rep.isGradedLocal_vonNeumannGrading _ _ N.toIsGradedLocal ?_ _ _ _ _
  intro Λ₁ Λ₂ hd
  exact ⟨hd, Λ₁ ∪ Λ₂, Finset.subset_union_left, Finset.subset_union_right⟩

/-- For a local net the GNS parity is `1`: the quasi-local parity is the identity
    (`GradedLocalNet.quasiLocalParity_apply_of_isTriviallyGraded`). -/
lemma gnsParity_eq_one [N.IsTriviallyGraded] (ω : State N.quasiLocalCStarAlgebra)
    [N.IsEvenState ω] : N.gnsParity ω = 1 :=
  GNS[ω].implementing_eq_one _ _ _ N.quasiLocalParity_apply_of_isTriviallyGraded

/-- **The split property of an even state for a pair of regions**: in the GNS representation of
    the even state `ω` on the quasi-local algebra, the regions `S₁` and `S₂` form a graded split
    pair (`VonNeumannNet.Grading.IsSplitPair`) for the GNS grading,
    `𝓡_ω(S₁) ≤ 𝔑 ≤ Z 𝓡_ω(S₂)′ Z⋆` with `𝔑` a type I factor. The regions may be infinite; `𝓡_ω` is
    `N.vonNeumannNetSet` at the GNS representation `GNS[ω].toCStarRep`. For a local net this is the
    split pair `𝓡_ω(S₁) ≤ 𝔑 ≤ 𝓡_ω(S₂)′` (`GradedLocalNet.isSplitPairAt_iff_of_isTriviallyGraded`).

    The order on the quasi-local algebra is a parameter rather than a fixed choice, because
    `State` needs one and the quasi-local algebra carries none; the spectral order
    `CStarAlgebra.spectralOrder` is the canonical instance. -/
def IsSplitPairAt (ω : State N.quasiLocalCStarAlgebra) [N.IsEvenState ω]
    (S₁ S₂ : Set α) : Prop :=
  (N.gnsGrading ω).IsSplitPair S₁ S₂

/-- **For a local net the split property of a state is the commutant form**: every state is even,
    the GNS parity is `1`, and the twisted commutant is the commutant. -/
lemma isSplitPairAt_iff_of_isTriviallyGraded [N.IsTriviallyGraded] {ω : State N.quasiLocalCStarAlgebra}
    [N.IsEvenState ω] {S₁ S₂ : Set α} :
    N.IsSplitPairAt ω S₁ S₂ ↔ (N.vonNeumannNetSet GNS[ω].toCStarRep).IsSplitPair S₁ S₂ :=
  VonNeumannNet.Grading.isSplitPair_iff_of_Γ_eq_one (G := N.gnsGrading ω)
    (N.gnsParity_eq_one ω)

/-- **Every state on the quasi-local algebra of a local net is even**: the quasi-local parity is
    the identity (`GradedLocalNet.quasiLocalParity_apply_of_isTriviallyGraded`). -/
instance instIsEvenStateOfIsTriviallyGraded [N.IsTriviallyGraded] (ω : State N.quasiLocalCStarAlgebra) :
    N.IsEvenState ω :=
  ⟨fun a => congrArg ω (N.quasiLocalParity_apply_of_isTriviallyGraded a)⟩

/-- **The nested split property yields split pairs with a gap**: if the GNS net of the even state
    `ω` has the split property and `S₁ ⋐ S₂` with `S₃` disjoint from `S₂`, then `(S₁, S₃)` is a
    split pair of `ω` (`VonNeumannNet.SplitProperty.isGradedSplitPair`). On the integer chain with
    `ofCThickening ℤ 1` this gives the gapped half-chain pair `(Iic 0, Ici 3)` from
    `Iic 0 ⋐ Iic 2`; the gap-free pair `(Iic 0, Ici 1)` is not reachable. -/
lemma IsSplitPairAt.of_splitProperty [ProperContainment (Set α)]
    {ω : State N.quasiLocalCStarAlgebra} [N.IsEvenState ω]
    (hs : (N.vonNeumannNetSet GNS[ω].toCStarRep).SplitProperty)
    {S₁ S₂ S₃ : Set α} (h : S₁ ⋐ S₂) (hd : Disjoint S₂ S₃) : N.IsSplitPairAt ω S₁ S₃ :=
  VonNeumannNet.SplitProperty.isGradedSplitPair (N.isGradedLocal_gnsGrading ω) hs h hd

/-- For a multiplicative state, the local von Neumann algebras of the GNS representation consist
    of scalars: they lie in `𝓑(H)′`. -/
private lemma localVonNeumannAlgebra_le_commutant_of_map_mul {ω : State N.quasiLocalCStarAlgebra}
    (hω : ∀ a b, ω (a * b) = ω a * ω b) (Λ : Finset α) :
    N.localVonNeumannAlgebra GNS[ω].toCStarRep Λ ≤ (𝓑(GNS[ω].H))′ := by
  rw [CStarNet.localVonNeumannAlgebra]
  refine VonNeumannAlgebra.generated_le (M := (𝓑(GNS[ω].H))′) ?_
  rintro _ ⟨a, rfl⟩
  exact VonNeumannAlgebra.mem_commutant_boundedLinearOperators_iff.mpr
    ⟨_, GNS[ω].π_eq_smul_one_of_map_mul hω _⟩

/-- For a multiplicative state, the operators localised in the finite regions inside `S` are
    scalars in the GNS representation. -/
private lemma localOperatorsAlong_subset_commutant_of_map_mul
    {ω : State N.quasiLocalCStarAlgebra} (hω : ∀ a b, ω (a * b) = ω a * ω b) (S : Set α) :
    (N.vonNeumannNet GNS[ω].toCStarRep).localOperatorsAlong (↑) S ⊆
      ((𝓑(GNS[ω].H))′ : Set (GNS[ω].H →L[ℂ] GNS[ω].H)) := fun x hx => by
  obtain ⟨Λ, -, hx⟩ := VonNeumannNet.mem_localOperatorsAlong.1 hx
  exact N.localVonNeumannAlgebra_le_commutant_of_map_mul hω Λ hx

/-- **Every even multiplicative state splits every pair of regions**, trivially: its GNS
    representation acts by scalars (`GNS.Representation.π_eq_smul_one_of_map_mul`), so every local
    algebra lies in the scalar algebra `ℂ1 = 𝓑(H)′`, which is a type I factor
    (`VonNeumannAlgebra.isTypeIFactor_commutant_boundedLinearOperators`) contained in every von
    Neumann algebra. This is the degenerate end of the split property, as the one-dimensional case
    is for nets. -/
lemma IsSplitPairAt.of_map_mul {ω : State N.quasiLocalCStarAlgebra}
    [N.IsEvenState ω] (hmul : ∀ a b, ω (a * b) = ω a * ω b)
    (S₁ S₂ : Set α) : N.IsSplitPairAt ω S₁ S₂ := by
  refine ⟨_, VonNeumannAlgebra.isTypeIFactor_commutant_boundedLinearOperators, ?_, ?_⟩
  · exact VonNeumannAlgebra.generated_le
      (N.localOperatorsAlong_subset_commutant_of_map_mul hmul S₁)
  · intro x hx
    obtain ⟨c, rfl⟩ := VonNeumannAlgebra.mem_commutant_boundedLinearOperators_iff.mp hx
    exact SMulMemClass.smul_mem c (one_mem _)

end State

section HalfChain

variable (N : GradedLocalNet (Finset ℤ)) [N.Faithful]
variable [PartialOrder N.quasiLocalCStarAlgebra] [StarOrderedRing N.quasiLocalCStarAlgebra]

/-- The **half-chain split property** of an even state `ω` on the quasi-local algebra of a chain,
    in split-inclusion form: the left half-chain `(-∞, 0]` and the right half-chain `[1, ∞)` form a
    graded split pair in the GNS representation of `ω`,

      `𝓡_ω((-∞, 0]) ≤ 𝔑 ≤ Z 𝓡_ω([1, ∞))′ Z⋆`, with `𝔑` a type I factor,

    which for a local net is `𝓡_ω((-∞, 0]) ≤ 𝔑 ≤ 𝓡_ω([1, ∞))′`
    (`GradedLocalNet.isSplitPairAt_iff_of_isTriviallyGraded`). The half-chains are adjacent: there is no gap,
    so this is not a consequence of any nested split property through `⋐`.

    For a local net, the split inclusion above implies the quasi-equivalence of `ω` with
    `ω_L ⊗ ω_R`, the product of its restrictions to the two half-chains, for every state, and
    conversely for pure (more generally factor) states; for a pure state both are equivalent to
    `𝓡_ω((-∞, 0])` being a type I factor. Neither the quasi-equivalence form nor these equivalences
    are formalised (see the module docstring). -/
def HasHalfChainSplit (ω : State N.quasiLocalCStarAlgebra)
    [N.IsEvenState ω] : Prop :=
  N.IsSplitPairAt ω (Set.Iic 0) (Set.Ici 1)

/-- **Every even multiplicative state has the half-chain split property**, trivially: the case
    `(Iic 0, Ici 1)` of `GradedLocalNet.IsSplitPairAt.of_map_mul`. -/
lemma HasHalfChainSplit.of_map_mul {ω : State N.quasiLocalCStarAlgebra}
    [N.IsEvenState ω] (hmul : ∀ a b, ω (a * b) = ω a * ω b) :
    N.HasHalfChainSplit ω :=
  IsSplitPairAt.of_map_mul N hmul _ _

end HalfChain

end GradedLocalNet
