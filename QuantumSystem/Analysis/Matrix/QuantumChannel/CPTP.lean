/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import Mathlib.Analysis.Matrix.Order
public import QuantumSystem.Notation

/-!
# Quantum channels (completely positive trace-preserving maps)

This file defines quantum channels on finite-dimensional matrix algebras. A quantum channel is a
linear map `Φ : M_n(ℂ) → M_m(ℂ)` that is
1. completely positive (CP): `id_k ⊗ Φ` is positive for every `k`;
2. trace preserving (TP): `Tr (Φ A) = Tr A` for all `A`.

## Main definitions

* `Matrix.IsTracePreserving`: a linear map preserves trace.
* `Matrix.IsCompletelyPositive`: a linear map is completely positive.
* `Matrix.IsCompletelyPositive.toCompletelyPositiveMap`: a CP map as Mathlib's bundled
  `CompletelyPositiveMap`.
* `Matrix.IsQuantumChannel`: a linear map is both CP and TP.
* `Matrix.QuantumChannel n m`: the subtype of CPTP maps `M_n(ℂ) → M_m(ℂ)`.

## Main statements

* `Matrix.isCompletelyPositive_id`, `Matrix.IsCompletelyPositive.comp`: the identity is CP, and
  CP maps compose.
* `Matrix.isQuantumChannel_id`, `Matrix.QuantumChannel.comp`: identity and composition.
* `Matrix.IsCompletelyPositive.isHermitian_map`, `Matrix.IsCompletelyPositive.posSemidef_map`:
  CP maps preserve Hermitian and positive semidefinite matrices.

## Mathematical Background

Complete positivity is Mathlib's `CompletelyPositiveMap` condition: applying `Φ` entrywise to a
`k × k` block matrix `M` with entries in `M_n(ℂ)` preserves nonnegativity, for every `k`. Here
`M_n(ℂ)` is the C⋆-algebra of `Matrix.Norms.L2Operator`, ordered by `MatrixOrder`, and the block
matrices form the C⋆-algebra `CStarMatrix (Fin k) (Fin k) (Matrix n n ℂ)`; by
`CStarMatrix.nonneg_iff_posSemidef_comp` its order is positive semidefiniteness of the flattened
`kn × kn` matrix, which is the physicists' condition that `id_k ⊗ Φ` be positive
(`Matrix.isCompletelyPositive_iff_posSemidef_comp_map` in `Choi.lean`).

By the Choi–Kraus theorem (`QuantumSystem/Analysis/Matrix/QuantumChannel/Choi.lean`) complete
positivity is equivalent to positive semidefiniteness of the Choi matrix and to the existence of a
Kraus representation `Φ(ρ) = Σᵢ Kᵢ ρ Kᵢᴴ`. The completeness relation `Σᵢ Kᵢᴴ Kᵢ = I` for
trace-preserving maps is in `QuantumSystem/Analysis/Matrix/QuantumChannel/Kraus.lean`.

## References

* Nielsen, Chuang, *Quantum Computation and Quantum Information*, Chapter 8
* Watrous, *The Theory of Quantum Information*, Chapter 2
-/
@[expose] public section

namespace Matrix

variable {n m k : Type*} [Fintype n] [Fintype m] [Fintype k]

open scoped ComplexOrder CStarAlgebra

/-! ### Trace-Preserving Maps -/

/-- A linear map is trace-preserving if Tr(Φ(A)) = Tr(A) for all A. -/
def IsTracePreserving (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Prop :=
  ∀ A : Matrix n n ℂ, Tr (Φ A) = Tr A

/-! ### Completely Positive Maps -/

variable [DecidableEq n] [DecidableEq m] [DecidableEq k]

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- A linear map `Φ : M_n(ℂ) → M_m(ℂ)` is completely positive if applying it entrywise to a
nonnegative `r × r` block matrix with entries in `M_n(ℂ)` gives a nonnegative block matrix, for
every `r`; that is, `id_r ⊗ Φ` is positive for every `r`
(`Matrix.isCompletelyPositive_iff_posSemidef_comp_map`).

This is verbatim the field of Mathlib's `CompletelyPositiveMap`, for the C⋆-algebra structure
`Matrix.Norms.L2Operator` and the order `MatrixOrder` on `M_n(ℂ)`
(`IsCompletelyPositive.toCompletelyPositiveMap`). -/
def IsCompletelyPositive (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Prop :=
  ∀ (r : ℕ) (M : CStarMatrix (Fin r) (Fin r) (Matrix n n ℂ)), 0 ≤ M → 0 ≤ M.map Φ

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- A completely positive map on matrix algebras as Mathlib's bundled `CompletelyPositiveMap`. -/
def IsCompletelyPositive.toCompletelyPositiveMap {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ}
    (hΦ : IsCompletelyPositive Φ) : Matrix n n ℂ →CP Matrix m m ℂ :=
  ⟨Φ, hΦ⟩

@[simp]
lemma IsCompletelyPositive.coe_toCompletelyPositiveMap {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ}
    (hΦ : IsCompletelyPositive Φ) : ⇑hΦ.toCompletelyPositiveMap = Φ :=
  rfl

/-- The identity map is completely positive. -/
lemma isCompletelyPositive_id :
    IsCompletelyPositive (LinearMap.id : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) :=
  fun _ M hM => by simpa using hM

/-- A composition of completely positive maps is completely positive. -/
lemma IsCompletelyPositive.comp {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ}
    {Ψ : Matrix m m ℂ →ₗ[ℂ] Matrix k k ℂ} (hΨ : IsCompletelyPositive Ψ)
    (hΦ : IsCompletelyPositive Φ) : IsCompletelyPositive (Ψ ∘ₗ Φ) :=
  fun r M hM => hΨ r _ (hΦ r M hM)

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- A completely positive map sends positive semidefinite matrices to positive semidefinite
matrices. -/
lemma IsCompletelyPositive.posSemidef_map {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ}
    (hΦ : IsCompletelyPositive Φ) {A : Matrix n n ℂ} (hA : A.PosSemidef) : (Φ A).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (map_nonneg hΦ.toCompletelyPositiveMap hA.nonneg)

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- A completely positive map preserves Hermitianity of matrices: it is positive, and positive
ℂ-linear maps between C⋆-algebras preserve `⋆`. -/
lemma IsCompletelyPositive.isHermitian_map {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ}
    (hΦ : IsCompletelyPositive Φ) {A : Matrix n n ℂ} (hA : A.IsHermitian) : (Φ A).IsHermitian :=
  (map_star hΦ.toCompletelyPositiveMap A).symm.trans (congrArg _ hA)

/-! ### Quantum Channels -/

/-- A quantum channel is a completely positive trace-preserving (CPTP) map.
These are the physically realizable operations on quantum states. -/
structure IsQuantumChannel (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Prop where
  /-- The map is completely positive -/
  completelyPositive : IsCompletelyPositive Φ
  /-- The map preserves trace -/
  tracePreserving : IsTracePreserving Φ

/-- Quantum channel as a subtype for cleaner API. -/
abbrev QuantumChannel (n : Type*) (m : Type*) [Fintype n] [Fintype m] [DecidableEq n]
    [DecidableEq m] :=
  { Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ // IsQuantumChannel Φ }

/-- The identity map is a quantum channel. -/
lemma isQuantumChannel_id : IsQuantumChannel (LinearMap.id : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) where
  completelyPositive := isCompletelyPositive_id
  tracePreserving := fun _ => rfl

/-- Composition of quantum channels is a quantum channel: `Ψ.comp Φ` is `Ψ ∘ Φ`, applying `Φ`
first. -/
noncomputable def QuantumChannel.comp
    (Ψ : QuantumChannel m k) (Φ : QuantumChannel n m) : QuantumChannel n k where
  val := Ψ.val.comp Φ.val
  property.completelyPositive := Ψ.property.completelyPositive.comp Φ.property.completelyPositive
  property.tracePreserving := by
    intro A
    simp only [LinearMap.comp_apply]
    rw [Ψ.property.tracePreserving, Φ.property.tracePreserving]

end Matrix
