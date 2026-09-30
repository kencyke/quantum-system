/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import Mathlib.Analysis.Matrix.Order
public import QuantumSystem.Notation

/-!
# Quantum channels (completely positive trace-preserving maps)

This file defines quantum channels on finite-dimensional matrix algebras. A quantum channel is a
map `Φ : M_n(ℂ) → M_m(ℂ)` that is
1. completely positive (CP): `id_k ⊗ Φ` is positive for every `k`;
2. trace preserving (TP): `Tr (Φ A) = Tr A` for all `A`.

Completely positive maps are Mathlib's bundled `CompletelyPositiveMap`
(`Matrix n n ℂ →CP Matrix m m ℂ`); their identity and composition are
`CompletelyPositiveMap.id` and `CompletelyPositiveMap.comp`
(`QuantumSystem/ForMathlib/Analysis/CStarAlgebra/CompletelyPositiveMap.lean`).

## Main definitions

* `Matrix.IsTracePreserving`: a map preserves trace.
* `Matrix.QuantumChannel n m`: the subtype of trace-preserving completely positive maps
  `M_n(ℂ) → M_m(ℂ)`.
* `Matrix.QuantumChannel.toLinearMap`: the underlying linear map of a quantum channel.
* `Matrix.QuantumChannel.id`, `Matrix.QuantumChannel.comp`: identity and composition.

## Main statements

* `CompletelyPositiveMap.isHermitian_map`, `CompletelyPositiveMap.posSemidef_map`: CP maps
  preserve Hermitian and positive semidefinite matrices.

## Mathematical Background

Complete positivity is Mathlib's `CompletelyPositiveMap` condition: applying `Φ` entrywise to a
`k × k` block matrix `M` with entries in `M_n(ℂ)` preserves nonnegativity, for every `k`. Here
`M_n(ℂ)` is the C⋆-algebra of `Matrix.Norms.L2Operator`, ordered by `MatrixOrder`, and the block
matrices form the C⋆-algebra `CStarMatrix (Fin k) (Fin k) (Matrix n n ℂ)`; by
`CStarMatrix.nonneg_iff_posSemidef_comp` its order is positive semidefiniteness of the flattened
`kn × kn` matrix, which is the physicists' condition that `id_k ⊗ Φ` be positive
(`CompletelyPositiveMap.posSemidef_comp_map` in `Choi.lean`).

This file specialises that general notion to the matrix algebras `M_n(ℂ)`. The general theory is
used beyond matrices elsewhere: the Kadison–Schwarz inequality
`φ(a)⋆ φ(a) ≤ ‖φ 1‖ • φ(a⋆ a)` for `2`-positive, in particular completely positive, maps between
arbitrary unital C⋆-algebras is `KPositiveMapClass.le_norm_smul_map_star_mul`, and its normalised
form `φ(a)⋆ φ(a) ≤ φ(a⋆ a)` under `φ 1 ≤ 1` is `KPositiveMapClass.le_map_star_mul`
(`QuantumSystem/ForMathlib/Analysis/CStarAlgebra/KPositiveMap.lean`); and the trace dual of a channel
is a Schwarz map on `B(ℂᵐ)` (`QuantumSystem/Analysis/Matrix/QuantumChannel/Dual.lean`).

By the Choi–Kraus theorem (`QuantumSystem/Analysis/Matrix/QuantumChannel/Choi.lean`) complete
positivity is equivalent to positive semidefiniteness of the Choi matrix and to the existence of a
Kraus representation `Φ(ρ) = Σᵢ Kᵢ ρ Kᵢᴴ`. The completeness relation `Σᵢ Kᵢᴴ Kᵢ = I` for
trace-preserving maps is in `QuantumSystem/Analysis/Matrix/QuantumChannel/Kraus.lean`. By
Stinespring's theorem (`QuantumSystem/Analysis/Matrix/QuantumChannel/Stinespring.lean`) a map is a
quantum channel iff it is `ρ ↦ tr₁(V ρ Vᴴ)` for an isometry `V`, the partial trace `tr₁` removing
the environment (`Matrix.QuantumChannel.exists_toLinearMap_eq_iff_exists_stinespring`).

## References

* Nielsen, Chuang, *Quantum Computation and Quantum Information*, Chapter 8
* Watrous, *The Theory of Quantum Information*, Chapter 2
-/
@[expose] public section

namespace Matrix

variable {n m k : Type*} [Fintype n] [Fintype m] [Fintype k]

open scoped ComplexOrder CStarAlgebra

/-! ### Trace-Preserving Maps -/

variable {F : Type*} [FunLike F (Matrix n n ℂ) (Matrix m m ℂ)]

/-- A map `Φ : M_n(ℂ) → M_m(ℂ)` is trace-preserving if `Tr (Φ A) = Tr A` for all `A`. It is
stated for any `FunLike` type, so that it applies to linear maps and to completely positive maps
alike. -/
def IsTracePreserving (Φ : F) : Prop :=
  ∀ A : Matrix n n ℂ, Tr (Φ A) = Tr A

/-! ### Quantum Channels -/

variable [DecidableEq n] [DecidableEq m] [DecidableEq k]

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- A **quantum channel** is a completely positive trace-preserving (CPTP) map
`M_n(ℂ) → M_m(ℂ)`: a completely positive map in Mathlib's sense (`CompletelyPositiveMap`, for the
C⋆-algebra structure `Matrix.Norms.L2Operator` and the order `MatrixOrder`) that preserves the
trace. These are the physically realizable operations on quantum states.

The instances `Matrix.Norms.L2Operator` and `MatrixOrder` are scoped, so writing
`Matrix n n ℂ →CP Matrix m m ℂ` directly needs
`open scoped CStarAlgebra Matrix.Norms.L2Operator MatrixOrder`. The type `QuantumChannel n m`
itself carries them: stating and using channels needs no `open`, through the application `Φ.val A`
and the API of this namespace (`QuantumChannel.toLinearMap`, `QuantumChannel.id`,
`QuantumChannel.comp`). Only calls into the `CompletelyPositiveMap` API on `Φ.val` that re-synthesise
the C⋆-structure of `Matrix n n ℂ`, such as `Φ.val.toLinearMap` or `Ψ.val.comp Φ.val`, need the
scoped instances. -/
abbrev QuantumChannel (n m : Type*) [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] :=
  { φ : Matrix n n ℂ →CP Matrix m m ℂ // IsTracePreserving φ }

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- The underlying linear map `M_n(ℂ) →ₗ[ℂ] M_m(ℂ)` of a quantum channel. -/
noncomputable def QuantumChannel.toLinearMap (Φ : QuantumChannel n m) :
    Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ :=
  Φ.val.toLinearMap

/-- The linear map of a quantum channel `Φ` is `Φ` as a function. -/
@[simp] lemma QuantumChannel.toLinearMap_apply (Φ : QuantumChannel n m) (A : Matrix n n ℂ) :
    Φ.toLinearMap A = Φ.val A :=
  rfl

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- The identity map is a quantum channel. -/
noncomputable def QuantumChannel.id : QuantumChannel n n :=
  ⟨CompletelyPositiveMap.id _, fun _ => rfl⟩

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- Composition of quantum channels is a quantum channel: `Ψ.comp Φ` is `Ψ ∘ Φ`, applying `Φ`
first. -/
noncomputable def QuantumChannel.comp (Ψ : QuantumChannel m k) (Φ : QuantumChannel n m) : QuantumChannel n k :=
  ⟨Ψ.val.comp Φ.val, fun A => (Ψ.property (Φ.val A)).trans (Φ.property A)⟩

end Matrix

/-! ### Completely positive maps on matrix algebras -/

namespace CompletelyPositiveMap

open Matrix
open scoped ComplexOrder CStarAlgebra

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- A completely positive map sends positive semidefinite matrices to positive semidefinite
matrices. -/
lemma posSemidef_map (φ : Matrix n n ℂ →CP Matrix m m ℂ) {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    (φ A).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (map_nonneg φ hA.nonneg)

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- A completely positive map preserves Hermitianity of matrices: it is positive, and positive
ℂ-linear maps between C⋆-algebras preserve `⋆`. -/
lemma isHermitian_map (φ : Matrix n n ℂ →CP Matrix m m ℂ) {A : Matrix n n ℂ}
    (hA : A.IsHermitian) : (φ A).IsHermitian :=
  (map_star φ A).symm.trans (congrArg _ hA)

end CompletelyPositiveMap
