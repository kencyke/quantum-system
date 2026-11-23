# Roadmap notes

The Roadmap in `README.md` states what each item is to prove. This file keeps, for each item under its
README name, the design questions that are open before the item can be stated at the generality the README
asks for. What the repository already has is in the module docs, not here. No citations here: those belong in the README
and the module docs, where `/citation-check` checks them.

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
- The permanence of nuclearity under quotients can be stated now. Its proof passes through the bidual:
  `A` is nuclear exactly when the von Neumann algebra `A**` is injective, and `(A/J)**` is a direct
  summand of `A**`. The bidual of a C⋆-algebra is not defined, and the passage from an injective bidual
  back to nuclearity is not formalized. The bidual meets the first bullet: as a `VonNeumannAlgebra` it is
  the double commutant of the universal representation, as a `WStarAlgebra` its predual is the dual of
  `A`.
- The inductive limit along ⋆-homomorphisms that need not be injective has no C⋆-algebra yet:
  `NormedDirectLimit` asks isometric connecting maps, which is why the quasi-local algebra of a net
  (`CStarNet.quasiLocalCStarAlgebra`) needs a faithful net. The C⋆-limit of an arbitrary directed
  system — the completion of the algebraic limit in the seminorm `lim_j ‖φ_{ij} x‖` — removes that
  hypothesis and is what the permanence of nuclearity under such limits is stated for. Settle whether
  it generalizes `NormedDirectLimit` or stands beside it, so that one of them is the notion the
  quasi-local algebra is built from.

## Tomita–Takesaki theory

The module doc of `Analysis/VonNeumannAlgebra/Modular/RelativeModular.lean` lists what is not formalized.
The modular automorphism group σ^φ is a W⋆-dynamical system of `ℝ`, a
`ContinuousAddChar ℝ (M.sigmaWeak ≃⋆ₐ[ℂ] M.sigmaWeak)`: `UnitaryRepresentation.conjSigmaWeakAut` of the
modular unitary group, taken as a representation of `Multiplicative ℝ` by
`ContinuousAddChar.toContinuousMonoidHom`; its hypothesis that the unitaries normalize `M` is
`Δ^{it} M Δ^{-it} = M`.

## Standard form

The natural cone is not defined.

## Reversibility

`VonNeumannAlgebra.arakiEntropy` is defined through the amplification of the algebra to
`Completion (ℓ²(ℕ) ⊗[ℂ] H)`, in place of the missing standard form. Once *Standard form* lands, the
natural-cone formula is proved as a theorem about this definition, not given as a second one.

## Duality

Mathlib's `TannakaDuality.FiniteGroup.equiv` is for finite groups and without ⋆-structure. Rests on
*Tensor C⋆-categories* and on the representations of *Averaging*.

## Subnets of nets of von Neumann algebras

The internal symmetries and the fixed-point subnet exist only for nets of C⋆-algebras
(`GradedLocalNet.Automorphism.internal`, `GradedLocalNet.fixedPointNet`), whose locality
binds only pairs of regions with a common upper bound; over a non-directed index set such as the
intervals of `S¹` the fixed-point subnet has to be a `VonNeumannNet`. Before the subnet relation is
introduced, settle whether the C⋆-level constructions become instances of the von Neumann-level ones
(through a representation) or stay beside them, so that one of them is the notion every result is
stated in.
