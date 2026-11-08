# Roadmap notes

The Roadmap in `README.md` states what each item is to prove. This file keeps, for each item under its
README name, the design questions that are open before the item can be stated at the generality the README
asks for, and, for an item in progress, its split into pull requests that each land without `sorry`. What
the repository already has is in the module docs, not here. No citations here: those belong in the README
and the module docs, where `/citation-check` checks them.

## Tensor products

- **Open.** Operators on a tensor product are spelt two ways: on the algebraic `H ⊗[ℂ] K` (the channel
  and entropy files) and on its completion `HilbertTensor H K` (the von Neumann algebra files). The
  minimal tensor product is built on one of them, and the other's results either move to it or are
  shown to be its finite-dimensional case.

## Dynamical systems

- **Open.** `LocalNet.Covariance` carries no topology, so the covariance action states no continuity;
  the modular groups are unitary groups on `H`, not actions on an algebra. The action interface is
  stated so that both are instances: a group homomorphism into the ⋆-automorphisms, continuous for the
  point-norm (C⋆) or point-σ-weak (W⋆) topology.

## Tensor C⋆-categories

- **Open.** Mathlib has monoidal, braided and symmetric categories, but no dagger or C⋆-category.
  `CStarRep.Hom` has no `Category` instance. Once it has one, `CategoryTheory.Iso` stands
  beside `CStarRep.UnitaryEquiv`; how the two relate is settled before the C⋆-category structure is
  introduced, so that one of them is the notion every result is stated in.

## Von Neumann algebras

- **Open.**
  - Everything is stated for Mathlib's concrete `VonNeumannAlgebra H`; Mathlib's abstract
    `WStarAlgebra` is not used yet. Sakai's characterization is where the two meet.
  - Nothing yet links a finite-dimensional factor to `IsSimpleRing`, which the matrix-algebra statement
    needs.
  - Matrix algebras are spelt three ways: `Matrix n n ℂ`, `CStarMatrix` (`M_[n](ℂ)`) and operators on
    `ℂⁿ`. This item and *Averaging* settle on one.
- **Pull requests.**
  1. Kaplansky density for a ⋆-subalgebra of `B(H)`: the strong closure of the unit ball, of its
     self-adjoint part and of its positive part is the unit ball, its self-adjoint part and its
     positive part of the strong closure.
  2. Kaplansky density for unitaries, once a unitary of a von Neumann algebra is the exponential of a
     self-adjoint element of it.
  3. A finite-dimensional factor is a simple ring, hence `≃⋆ₐ[ℂ] M_[n](ℂ)`; matrix algebras are stated
     as `CStarMatrix`, the spelling of the structure theorem.
  4. The matrix sizes of the structure theorem are unique up to order.

## Tomita–Takesaki theory

- **Open.** The module doc of `Analysis/VonNeumannAlgebra/Modular/RelativeModular.lean` lists what is
  not formalized. The modular automorphism group σ^φ is an action of ℝ on the algebra, so it is stated with
  the action interface of *Dynamical systems*.

## Standard form

- **Open.** The natural cone is not defined.

## Reversibility

- **Open.** `VonNeumannAlgebra.arakiEntropy` is defined through the amplification of the algebra to
  `ℓ²(ℕ) ⊗̂ H`, in place of the missing standard form. Once *Standard form* lands, the natural-cone
  formula is proved as a theorem about this definition, not given as a second one.

## Averaging

- **Open.** Unitary representations exist only as `AddChar G (unitary (H →L[ℂ] H))`, for additive
  groups. A compact group need not be commutative, so its unitary representations need a spelling of
  which the additive case is an instance, not a second spelling beside it.

## Duality

- **Open.** Mathlib's `TannakaDuality.FiniteGroup.equiv` is for finite groups and without ⋆-structure.
  Rests on *Tensor C⋆-categories* and on the representations of *Averaging*.
