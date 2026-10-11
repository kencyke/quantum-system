/-
Copyright (c) 2025 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.VonNeumannAlgebra.Basic
public import QuantumSystem.ForMathlib.Analysis.VonNeumannAlgebra.Commutant

/-!
# The von Neumann algebra `𝓑(H)` of all bounded operators

Mathlib's bundled `VonNeumannAlgebra H` provides no distinguished element for the algebra of *all*
bounded operators — the object the literature writes `B(H)`. This file supplies it as
`𝓑(H) = VonNeumannAlgebra.boundedLinearOperators H`, with carrier `Set.univ`, together with the
canonical `⋆`-isomorphism `boundedLinearOperators.starAlgEquiv : 𝓑(H) ≃⋆ₐ[ℂ] (H →L[ℂ] H)` that
identifies the bundled von Neumann algebra with the operator type.

It also records the one-dimensional case: on `ℂ` every bounded operator is a scalar, so `𝓑(ℂ)` is
the only von Neumann algebra (`eq_boundedLinearOperators_complex`). This is what makes
one-dimensional witnesses of downstream properties both easy and uninformative.

## Main definitions

* `VonNeumannAlgebra.boundedLinearOperators H` — the algebra of all bounded operators, with carrier
  `Set.univ`, denoted `𝓑(H)` (`VonNeumannAlgebra.coe_boundedLinearOperators` /
  `VonNeumannAlgebra.mem_boundedLinearOperators`).
* `VonNeumannAlgebra.boundedLinearOperators.starAlgEquiv` — the canonical `⋆`-isomorphism
  `𝓑(H) ≃⋆ₐ[ℂ] (H →L[ℂ] H)` identifying the bundled von Neumann algebra with the operator type
  (the `⋆`-algebra analogue of `Subalgebra.topEquiv`).

## Main results

* `VonNeumannAlgebra.eq_boundedLinearOperators_complex` — on the one-dimensional Hilbert space
  `𝓑(ℂ)` is the *only* von Neumann algebra, every bounded operator on `ℂ` being a scalar
  (`VonNeumannAlgebra.apply_eq_mul_apply_one`, `VonNeumannAlgebra.mul_comm_complex`).

## Notation

| Symbol | Expansion | How to activate |
|---|---|---|
| `𝓑(H)` | `VonNeumannAlgebra.boundedLinearOperators H` | `open scoped VonNeumannAlgebra` |

The von Neumann algebra `𝓑(H)` and the operator type `H →L[ℂ] H` denote the same object B(H) at
different levels and are related by `boundedLinearOperators.starAlgEquiv`.
-/

@[expose] public section

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### The full algebra `𝓑(H)` of all bounded operators -/

/-- The von Neumann algebra `𝓑(H)` of **all bounded linear operators** on `H` — the object the
literature writes `B(H)`. Its carrier is `Set.univ`; the double-commutant property is the
bicommutant inclusion `s ⊆ s''` applied to `s = univ`, together with `univ` being the largest set.
Mathlib's bundled `VonNeumannAlgebra H` provides no such distinguished element, so this file
supplies it. -/
noncomputable def boundedLinearOperators (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] : VonNeumannAlgebra H where
  toStarSubalgebra := ⊤
  centralizer_centralizer' :=
    Set.Subset.antisymm (Set.subset_univ _) Set.subset_centralizer_centralizer

/-- `𝓑(H)` denotes the von Neumann algebra of all bounded operators on `H`
(`VonNeumannAlgebra.boundedLinearOperators H`). It and the operator type `H →L[ℂ] H` denote the
same mathematical object B(H) at different levels (the bundled *von Neumann algebra* of all
operators vs. the operator *type*), related by the canonical `⋆`-isomorphism
`boundedLinearOperators.starAlgEquiv`. -/
scoped notation:max "𝓑(" H ")" => VonNeumannAlgebra.boundedLinearOperators H

/-- The carrier of `𝓑(H)` is all of `H →L[ℂ] H`. -/
@[simp] lemma coe_boundedLinearOperators :
    ((𝓑(H) : VonNeumannAlgebra H) : Set (H →L[ℂ] H)) = Set.univ := rfl

/-- Every bounded operator lies in `𝓑(H)`. -/
@[simp] lemma mem_boundedLinearOperators (x : H →L[ℂ] H) : x ∈ (𝓑(H) : VonNeumannAlgebra H) :=
  Set.mem_univ x

/-- **The two levels of `𝓑(H)` agree.** The underlying `⋆`-subalgebra of the bundled von Neumann
algebra `𝓑(H)`, coerced to a type, is canonically `⋆`-isomorphic to the operator type
`H →L[ℂ] H`.
This is the `⋆`-algebra analogue of `Subalgebra.topEquiv` / `Submodule.topEquiv`, making explicit
that the notation overload denotes one and the same object B(H). The equivalence is phrased on
`(𝓑(H)).toStarSubalgebra` because Mathlib equips the `⋆`-subalgebra — not the bundled
`VonNeumannAlgebra` — with the `ℂ`-algebra structure. -/
noncomputable def boundedLinearOperators.starAlgEquiv :
    (𝓑(H) : VonNeumannAlgebra H).toStarSubalgebra ≃⋆ₐ[ℂ] (H →L[ℂ] H) :=
  StarAlgEquiv.ofStarAlgHom
    (𝓑(H) : VonNeumannAlgebra H).toStarSubalgebra.subtype
    ({ toFun := fun x => ⟨x, StarSubalgebra.mem_top⟩
       map_one' := rfl
       map_mul' := fun _ _ => rfl
       map_zero' := rfl
       map_add' := fun _ _ => rfl
       commutes' := fun _ => rfl
       map_star' := fun _ => rfl } :
      (H →L[ℂ] H) →⋆ₐ[ℂ] (𝓑(H) : VonNeumannAlgebra H).toStarSubalgebra)
    (StarAlgHom.ext fun _ => rfl) (StarAlgHom.ext fun _ => rfl)

/-- The inverse of `boundedLinearOperators.starAlgEquiv` sends an operator `x` to itself, viewed
as a member of `𝓑(H)`; coercing back to `H →L[ℂ] H` recovers `x`. -/
@[simp] lemma boundedLinearOperators.coe_starAlgEquiv_symm_apply (x : H →L[ℂ] H) :
    ((boundedLinearOperators.starAlgEquiv (H := H)).symm x : H →L[ℂ] H) = x := rfl

/-! ### The one-dimensional case

On `ℂ` every bounded operator is a scalar, so there is exactly one von Neumann algebra. This is
what makes one-dimensional witnesses of net- and inclusion-level properties go through without
computing any generated algebra — and, read the other way, what makes them evidence of
inhabitation only: on `ℂ` no algebra, no net and no representation is distinguished from any
other.
-/

/-- A bounded operator on `ℂ` is multiplication by its value at `1`. -/
lemma apply_eq_mul_apply_one (x : ℂ →L[ℂ] ℂ) (w : ℂ) : x w = w * x 1 := by
  rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]

/-- **Bounded operators on `ℂ` commute.** Each is multiplication by a scalar
(`apply_eq_mul_apply_one`), and scalars commute. -/
lemma mul_comm_complex (x y : ℂ →L[ℂ] ℂ) : x * y = y * x := by
  refine ContinuousLinearMap.ext fun z => ?_
  rw [mul_apply_eq_comp, mul_apply_eq_comp,
    apply_eq_mul_apply_one x (y z), apply_eq_mul_apply_one y (x z),
    apply_eq_mul_apply_one y z, apply_eq_mul_apply_one x z]
  ring

/-- **On `ℂ` there is only one von Neumann algebra.** Every von Neumann algebra on the
one-dimensional Hilbert space is `𝓑(ℂ)`: it contains `1` and is closed under scalars, while
every bounded operator on `ℂ` is a scalar multiple of `1` (`apply_eq_mul_apply_one`). -/
lemma eq_boundedLinearOperators_complex (N : VonNeumannAlgebra ℂ) : N = 𝓑(ℂ) := by
  refine SetLike.ext fun x => ⟨fun _ => mem_boundedLinearOperators x, fun _ => ?_⟩
  have hx : x = (x 1) • (1 : ℂ →L[ℂ] ℂ) := by
    refine ContinuousLinearMap.ext fun z => ?_
    rw [smul_apply, one_apply_eq_self, smul_eq_mul,
      apply_eq_mul_apply_one x z, mul_comm]
  rw [hx]
  exact SMulMemClass.smul_mem _ (one_mem N)

end VonNeumannAlgebra
