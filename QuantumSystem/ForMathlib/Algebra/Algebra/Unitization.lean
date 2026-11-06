/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Algebra.Algebra.Unitization
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Prod

/-!
# Finiteness of the unitization

The unitization `Unitization R A` is `R × A` as a module, so it is a finite module whenever `R`
and `A` are.

## Main results

* `Unitization.instModuleFinite`: if `R` and `A` are finite `S`-modules, so is `Unitization R A`.
-/

@[expose] public section

/-- If `R` and `A` are finite `S`-modules, so is the unitization `Unitization R A`. -/
instance Unitization.instModuleFinite {S R A : Type*} [Semiring S] [AddCommMonoid R]
    [AddCommMonoid A] [Module S R] [Module S A] [Module.Finite S R] [Module.Finite S A] :
    Module.Finite S (Unitization R A) :=
  Module.Finite.equiv (Unitization.linearEquiv S R A).symm
