# Roadmap notes

The Roadmap in `README.md` states what each item is to prove. This file keeps, for each item under its
README name, the design questions that are open before the item can be stated at the generality the README
asks for. What the repository already has is in the module docs, not here. No citations here: those belong in the README
and the module docs, where `/citation-check` checks them.

## Tensor products

Hilbert spaces are tensored with Mathlib's algebraic `H ⊗[ℂ] K` (the channel and entropy files) and its
completion `UniformSpace.Completion (H ⊗[ℂ] K)` (the von Neumann algebra files), on which operators act by
`ContinuousLinearMap.rTensor`/`lTensor` and `ContinuousLinearMap.completion`. In finite dimensions the two
coincide; the results on the algebraic tensor product are still to be shown to be the finite-dimensional
case of those on the completion. The minimal tensor product of C⋆-algebras is built on the completion.

## Dynamical systems

`LocalNet.Covariance` carries no topology, so the covariance action states no continuity; the modular
groups are unitary groups on `H`, not actions on an algebra. The action interface is stated so that both
are instances: a group homomorphism into the ⋆-automorphisms, continuous for the point-norm (C⋆) or
point-σ-weak (W⋆) topology.

## Tensor C⋆-categories

Mathlib has monoidal, braided and symmetric categories, but no dagger or C⋆-category. `CStarRep.Hom` has
no `Category` instance. Once it has one, `CategoryTheory.Iso` stands beside `CStarRep.UnitaryEquiv`; how
the two relate is settled before the C⋆-category structure is introduced, so that one of them is the
notion every result is stated in.

## Von Neumann algebras

- Everything is stated for Mathlib's concrete `VonNeumannAlgebra H`; Mathlib's abstract `WStarAlgebra` is
  not used yet. Sakai's characterization is where the two meet.
- Matrix algebras are spelt three ways: `Matrix n n ℂ`, `CStarMatrix` (`M_[n](ℂ)`) and operators on
  `ℂⁿ`. This item and *Averaging* settle on one.

## Tomita–Takesaki theory

The module doc of `Analysis/VonNeumannAlgebra/Modular/RelativeModular.lean` lists what is not formalized.
The modular automorphism group σ^φ is an action of ℝ on the algebra, so it is stated with the action
interface of *Dynamical systems*.

## Standard form

The natural cone is not defined.

## Reversibility

`VonNeumannAlgebra.arakiEntropy` is defined through the amplification of the algebra to
`Completion (ℓ²(ℕ) ⊗[ℂ] H)`, in place of the missing standard form. Once *Standard form* lands, the
natural-cone formula is proved as a theorem about this definition, not given as a second one.

## Averaging

Unitary representations exist only as `AddChar G (unitary (H →L[ℂ] H))`, for additive groups. A compact
group need not be commutative, so its unitary representations need a spelling of which the additive case
is an instance, not a second spelling beside it.

## Duality

Mathlib's `TannakaDuality.FiniteGroup.equiv` is for finite groups and without ⋆-structure. Rests on
*Tensor C⋆-categories* and on the representations of *Averaging*.
