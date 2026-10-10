/-
Copyright (c) 2025 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Diagonal amplification of operators on Hilbert spaces

This file develops the theory of diagonal amplification: given an operator `T : H →L[ℂ] H`,
we construct its diagonal action on `H^n = Fin n → H` (with the L2 inner product).

This is a key ingredient in the von Neumann double commutant theorem: amplification allows
reducing the general case to the case with a cyclic vector.

## Main definitions

* `Hn n`: the Hilbert space `H^n` as `PiLp 2 (Fin n → H)`.
* `single i`: the injection from `H` to the `i`-th component of `H^n`; the projection onto the
  `i`-th component is Mathlib's `PiLp.proj 2 _ i`.
* `diagonal T`: the diagonal action of `T` on `H^n`, i.e., `T` applied componentwise.
* `matrixComponent S i j`: the `(i, j)`-th matrix entry of an operator `S` on `H^n`.
* `diagonalStarAlgHom n`: the diagonal embedding as a `StarAlgHom`.

## Main results

* `commute_diagonal_iff`: `S` commutes with `diagonal T` iff all matrix components of `S`
  commute with `T`.
* `mem_commutant_diagonal_iff`: characterization of the commutant of the diagonal algebra.
* `diagonal_mem_double_commutant`: if `T ∈ A''`, then `diagonal T ∈ (diagonal '' A)''`.
* `diagonal_star`: diagonal commutes with the star operation.
-/

@[expose] public section

namespace InnerProductSpace

open scoped ENNReal

section NoComplete

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable (H) in
/-- The Hilbert space `H^n` as `Fin n → H` with the L2 inner product. -/
abbrev Hn (n : ℕ) := PiLp (2 : ℝ≥0∞) (fun _ : Fin n => H)

/-- The injection from `H` to the `i`-th component of `H^n`: Mathlib's `ContinuousLinearMap.single`
transported to the `L²` type copy `PiLp`. The `i`-th projection is `PiLp.proj 2 _ i`. -/
noncomputable def single {n : ℕ} (i : Fin n) : H →L[ℂ] Hn H n :=
  (PiLp.continuousLinearEquiv (2 : ℝ≥0∞) ℂ (fun _ : Fin n => H)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.single ℂ (fun _ : Fin n => H) i

@[simp]
lemma single_apply {n : ℕ} (i : Fin n) (v : H) :
    single i v = PiLp.single 2 i v := rfl

/-- Diagonal action of an operator `T : H →L[ℂ] H` on `H^n`. -/
noncomputable def diagonal {n : ℕ} (T : H →L[ℂ] H) : Hn H n →L[ℂ] Hn H n := by
  classical
  exact ∑ i : Fin n, single i ∘L (T ∘L PiLp.proj 2 (fun _ : Fin n => H) i)

@[simp]
lemma diagonal_apply {n : ℕ} (T : H →L[ℂ] H) (x : Hn H n) (i : Fin n) :
    (diagonal T x).ofLp i = T (x.ofLp i) := by
  classical
  simp [diagonal, WithLp.ofLp_sum, Finset.sum_apply, Pi.single_apply]

/-- The projection of an operator `S` on `H^n` to its `(i, j)`-th component in `B(H)`. -/
noncomputable def matrixComponent {n : ℕ} (S : Hn H n →L[ℂ] Hn H n)
    (i j : Fin n) : H →L[ℂ] H :=
  PiLp.proj 2 (fun _ : Fin n => H) i ∘L (S ∘L single j)

@[simp]
lemma matrixComponent_apply {n : ℕ} (S : Hn H n →L[ℂ] Hn H n)
    (i j : Fin n) (v : H) :
    matrixComponent S i j v = (S (single j v)).ofLp i := by
  rfl

lemma diagonal_single {n : ℕ} (T : H →L[ℂ] H) (j : Fin n) (v : H) :
    diagonal T (single j v) =
    single j (T v) := by
  classical
  refine PiLp.ext fun k => ?_
  rw [diagonal_apply]
  simp [apply_ite T]

lemma single_sum_eq {n : ℕ} (x : Hn H n) :
    x = ∑ j : Fin n, single j (x.ofLp j) := by
  classical
  refine PiLp.ext fun l => ?_
  simp [WithLp.ofLp_sum, Finset.sum_apply, Pi.single_apply]

/-- If `S` commutes with `diagonal T`, then its components satisfy a commutation relation. -/
lemma commute_diagonal_iff {n : ℕ} (S : Hn H n →L[ℂ] Hn H n) (T : H →L[ℂ] H) :
    S * (diagonal T) = (diagonal T) * S ↔
    ∀ i j, (matrixComponent S i j) * T =
           T * (matrixComponent S i j) := by
  constructor
  · intro h i j
    ext v
    simp only [mul_apply_eq_comp, matrixComponent_apply]
    have h_eq := congrArg (fun A => (A (single j v)).ofLp i) h
    simp only [mul_apply_eq_comp] at h_eq
    rw [diagonal_single] at h_eq
    rw [diagonal_apply] at h_eq
    exact h_eq
  · intro h
    ext x k
    simp only [mul_apply_eq_comp]
    rw [diagonal_apply]
    conv_lhs => rw [single_sum_eq x]
    conv_rhs => rw [single_sum_eq x]
    simp only [map_sum, WithLp.ofLp_sum, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [diagonal_single]
    simp only [← matrixComponent_apply, ← mul_apply_eq_comp]
    have := congrArg (fun f => f (x.ofLp j)) (h k j)
    simp only [mul_apply_eq_comp] at this
    exact this

/-- Characterization of the commutant of the diagonal algebra. -/
lemma mem_commutant_diagonal_iff {n : ℕ}
    (S : Hn H n →L[ℂ] Hn H n) (A : Set (H →L[ℂ] H)) :
    S ∈ (diagonal '' A).centralizer ↔
      ∀ i j, matrixComponent S i j ∈ A.centralizer := by
  constructor
  · intro hS i j T hT
    simp only [Set.mem_centralizer_iff] at hS
    have h := hS (diagonal T) ⟨T, hT, rfl⟩
    rw [eq_comm, commute_diagonal_iff] at h
    exact (h i j).symm
  · intro hS S' hS'
    simp only [Set.mem_image] at hS'
    obtain ⟨T, hT, rfl⟩ := hS'
    rw [eq_comm, commute_diagonal_iff]
    intro i j
    exact (hS i j T hT).symm

/-- If `T` is in the double commutant of `A`, then `diagonal T` is in the double commutant of
`diagonal A`. -/
lemma diagonal_mem_double_commutant {n : ℕ} {A : Set (H →L[ℂ] H)} {T : H →L[ℂ] H}
    (hT : T ∈ A.centralizer.centralizer) :
    diagonal (n := n) T ∈ (diagonal (n := n) '' A).centralizer.centralizer := by
  intro S hS
  rw [mem_commutant_diagonal_iff (n := n)] at hS
  rw [commute_diagonal_iff (n := n)]
  intro i j
  -- We need matrixComponent S i j * T = T * matrixComponent S i j
  -- We know matrixComponent S i j ∈ A.centralizer
  -- And T ∈ A.centralizer.centralizer
  have hij : matrixComponent S i j ∈ A.centralizer := hS i j
  exact hT (matrixComponent S i j) hij

end NoComplete

section WithComplete

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The diagonal operator commutes with the star operation. -/
lemma diagonal_star {n : ℕ} (T : H →L[ℂ] H) :
    diagonal (n := n) (star T) = star (diagonal (n := n) T) := by
  classical
  -- `star` on bounded operators is the adjoint.
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint]
  -- Characterize adjoints via inner products.
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  -- Expand the `PiLp` inner products and use the defining property of the adjoint.
  simp only [PiLp.inner_apply, diagonal_apply]
  refine Finset.sum_congr rfl ?_
  intro i _
  simpa using
    (ContinuousLinearMap.adjoint_inner_left (A := T) (x := y.ofLp i) (y := x.ofLp i))

/-- `diagonal` as a `StarAlgHom` (so we can map `StarSubalgebra`s). -/
noncomputable def diagonalStarAlgHom (n : ℕ) :
    (H →L[ℂ] H) →⋆ₐ[ℂ] (Hn H n →L[ℂ] Hn H n) where
  toFun := fun T => diagonal T
  map_one' := by
    ext x i
    simp [diagonal]
  map_mul' := by
    intro T U
    ext x i
    simp [diagonal_apply, mul_apply_eq_comp]
  map_zero' := by
    ext x i
    simp [diagonal_apply]
  map_add' := by
    intro T U
    ext x i
    simp [diagonal_apply]
  commutes' := by
    intro c
    ext x i
    simp [diagonal_apply, Algebra.algebraMap_eq_smul_one]
  map_star' := fun T => diagonal_star T

end WithComplete

end InnerProductSpace
