/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.ForMathlib.Analysis.VonNeumannAlgebra.Commutant
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The diagonal von Neumann algebra on `ℓ²(ι)`

For an arbitrary index type `ι`, the **diagonal algebra** on `ℓ²(ι)` is the commutant of the
coordinate projections `|eᵢ⟩⟨eᵢ|`, i.e. the operators diagonal in the standard basis
`eᵢ = lp.single 2 i 1`. It is commutative and maximal abelian: its commutant is itself.

It is informally written `ℓ^∞(ι)`, the algebra of multiplication operators by bounded functions on
`ι`. That identification is not formalised here: this file only shows that each member acts
diagonally on the basis vectors, `x eᵢ = (x eᵢ)ᵢ eᵢ`.

## Main definitions

* `VonNeumannAlgebra.coordProjection i` — the rank-one projection `|eᵢ⟩⟨eᵢ|`.
* `VonNeumannAlgebra.diagonalAlgebra ι` — the commutant of the coordinate projections.

## Main results

* `VonNeumannAlgebra.coordProjection_apply_single` — `Pᵢ eⱼ = δᵢⱼ eⱼ`.
* `VonNeumannAlgebra.coordProjection_mul` — `Pᵢ Pⱼ = δᵢⱼ Pᵢ`.
* `VonNeumannAlgebra.coordProjection_ne_smul_one` — `Pᵢ` is not a scalar when `ι` has two indices.
* `VonNeumannAlgebra.coordProjection_mem`, `VonNeumannAlgebra.coordProjection_mem_commutant` —
  every coordinate projection lies both in `ℓ^∞(ι)` and in its commutant.
* `VonNeumannAlgebra.apply_single_of_mem_diagonalAlgebra` — every `x ∈ ℓ^∞(ι)` is diagonal:
  `x eᵢ = (x eᵢ)ᵢ eᵢ`.
* `VonNeumannAlgebra.commutant_diagonalAlgebra` — `ℓ^∞(ι)` is maximal abelian: `ℓ^∞(ι)′ = ℓ^∞(ι)`.
-/

@[expose] public section

open InnerProductSpace
open scoped InnerProductSpace VonNeumannAlgebra lp

namespace VonNeumannAlgebra

variable {ι : Type*} [DecidableEq ι]

/-- The **coordinate projection** `|eᵢ⟩⟨eᵢ|` onto the `i`-th standard basis vector of `ℓ²(ι)`. -/
noncomputable def coordProjection (i : ι) : ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ) :=
  rankOne ℂ (lp.single 2 i (1 : ℂ)) (lp.single 2 i (1 : ℂ))

variable (ι) in
/-- The **diagonal algebra** on `ℓ²(ι)`, informally `ℓ^∞(ι)`: the commutant of the coordinate
projections, that is, the operators diagonal in the standard basis. -/
noncomputable def diagonalAlgebra : VonNeumannAlgebra ℓ²(ι, ℂ) :=
  commutantSet (Set.range coordProjection)

/-- The coordinate projection is self-adjoint. -/
lemma star_coordProjection (i : ι) : star (coordProjection i) = coordProjection i := by
  rw [coordProjection, ContinuousLinearMap.star_eq_adjoint, adjoint_rankOne]

/-- The coordinate projection acts as `v ↦ vᵢ • eᵢ`. -/
lemma coordProjection_apply (i : ι) (v : ℓ²(ι, ℂ)) :
    coordProjection i v = v i • lp.single 2 i (1 : ℂ) := by
  rw [coordProjection, rankOne_apply, lp.inner_single_left, RCLike.inner_apply, map_one, mul_one]

/-- `Pᵢ eⱼ = δᵢⱼ eⱼ`. -/
lemma coordProjection_apply_single (i j : ι) :
    coordProjection i (lp.single 2 j (1 : ℂ)) =
      if i = j then lp.single 2 j (1 : ℂ) else 0 := by
  rw [coordProjection_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

/-- `Pᵢ Pⱼ = δᵢⱼ Pᵢ`. -/
lemma coordProjection_mul (i j : ι) :
    coordProjection i * coordProjection j = if i = j then coordProjection i else 0 := by
  ext1 v
  rw [mul_apply_eq_comp, coordProjection_apply j, map_smul,
    coordProjection_apply_single]
  by_cases h : i = j
  · subst h; simp [coordProjection_apply]
  · simp [h]

/-- Coordinate projections commute. -/
lemma coordProjection_mul_comm (i j : ι) :
    coordProjection i * coordProjection j = coordProjection j * coordProjection i := by
  rw [coordProjection_mul, coordProjection_mul]
  by_cases h : i = j
  · subst h; rfl
  · simp [h, Ne.symm h]

/-- A coordinate projection is not a scalar once `ι` has a second index: it fixes `eᵢ` and kills
`eⱼ`, so `c • 1` would force `c = 1` and `c = 0` at once. -/
lemma coordProjection_ne_smul_one {i j : ι} (hij : i ≠ j) (c : ℂ) : coordProjection i ≠ c • 1 := by
  intro h
  have hi := congrArg (fun T => T (lp.single 2 i (1 : ℂ)) i) h
  have hj := congrArg (fun T => T (lp.single 2 j (1 : ℂ)) j) h
  simp [coordProjection_apply_single, hij] at hi hj
  exact one_ne_zero (hi.trans hj.symm)

/-- Every coordinate projection lies in the diagonal algebra. -/
lemma coordProjection_mem (i : ι) : coordProjection i ∈ diagonalAlgebra ι := by
  rw [diagonalAlgebra, mem_commutantSet_iff]
  rintro g ⟨j, rfl⟩
  exact ⟨coordProjection_mul_comm j i, by rw [star_coordProjection, coordProjection_mul_comm]⟩

/-- Every coordinate projection lies in the commutant of the diagonal algebra: every member of
the diagonal algebra commutes with it by definition. -/
lemma coordProjection_mem_commutant (i : ι) : coordProjection i ∈ (diagonalAlgebra ι)′ := by
  rw [mem_commutant_iff]
  intro g hg
  rw [diagonalAlgebra, mem_commutantSet_iff] at hg
  exact (hg (coordProjection i) ⟨i, rfl⟩).1.symm

/-- **Members of `ℓ^∞(ι)` are diagonal**: `x eᵢ = (x eᵢ)ᵢ eᵢ`, since
`x eᵢ = x Pᵢ eᵢ = Pᵢ x eᵢ`. -/
lemma apply_single_of_mem_diagonalAlgebra {x : ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ)}
    (hx : x ∈ diagonalAlgebra ι) (i : ι) :
    x (lp.single 2 i (1 : ℂ)) = x (lp.single 2 i (1 : ℂ)) i • lp.single 2 i (1 : ℂ) := by
  rw [diagonalAlgebra, mem_commutantSet_iff] at hx
  have h := congrArg (fun T => T (lp.single 2 i (1 : ℂ))) (hx (coordProjection i) ⟨i, rfl⟩).1
  simp only [mul_apply_eq_comp, coordProjection_apply_single, ite_true] at h
  conv_lhs => rw [← h]
  rw [coordProjection_apply]

/-- `ℓ^∞(ι)` is commutative: two diagonal operators agree after composition in either order on
the basis vectors, hence everywhere by density of their span. -/
lemma mul_comm_of_mem_diagonalAlgebra {x y : ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ)}
    (hx : x ∈ diagonalAlgebra ι) (hy : y ∈ diagonalAlgebra ι) : x * y = y * x := by
  refine ContinuousLinearMap.ext_on lp.dense_span_single ?_
  rintro _ ⟨i, rfl⟩
  have hx' := apply_single_of_mem_diagonalAlgebra hx i
  have hy' := apply_single_of_mem_diagonalAlgebra hy i
  generalize x (lp.single 2 i (1 : ℂ)) i = a at hx'
  generalize y (lp.single 2 i (1 : ℂ)) i = b at hy'
  simp only [mul_apply_eq_comp]
  rw [hy', map_smul, hx', map_smul, hy', smul_smul, smul_smul, mul_comm]

/-- **`ℓ^∞(ι)` is maximal abelian**: `ℓ^∞(ι)′ = ℓ^∞(ι)`. The inclusion `ℓ^∞(ι)′ ≤ ℓ^∞(ι)` holds
because `ℓ^∞(ι)` contains the coordinate projections, and `ℓ^∞(ι) ≤ ℓ^∞(ι)′` is commutativity. -/
theorem commutant_diagonalAlgebra : (diagonalAlgebra ι)′ = diagonalAlgebra ι := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · rw [mem_commutant_iff] at hx
    rw [diagonalAlgebra, mem_commutantSet_iff]
    rintro g ⟨i, rfl⟩
    rw [star_coordProjection]
    exact ⟨hx _ (coordProjection_mem i), hx _ (coordProjection_mem i)⟩
  · rw [mem_commutant_iff]
    exact fun g hg => mul_comm_of_mem_diagonalAlgebra hg hx

end VonNeumannAlgebra
