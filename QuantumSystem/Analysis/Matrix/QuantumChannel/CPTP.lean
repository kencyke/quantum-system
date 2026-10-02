/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import Mathlib.Analysis.Matrix.Order
public import QuantumSystem.ForMathlib.LinearAlgebra.Matrix.StarAlgEquiv
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
* `Matrix.QuantumChannel n m`: trace-preserving completely positive maps `M_n(ℂ) → M_m(ℂ)`,
  extending a `CompletelyPositiveMap` by trace preservation, with `FunLike`, `LinearMapClass` and
  `CompletelyPositiveMapClass` instances; its underlying linear map is the coercion
  `(Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)`.
* `Matrix.QuantumChannel.id`, `Matrix.QuantumChannel.comp`: identity and composition.
* `Matrix.QuantumChannel.ofStarAlgEquiv`, `Matrix.QuantumChannel.reindex`: a `⋆`-algebra
  equivalence of matrix algebras (unitary conjugation) and, as the special case
  `Matrix.reindexStarAlgEquiv`, conjugation by an index equivalence, as channels.

## Main statements

* `Matrix.QuantumChannel.isTracePreserving`, `Matrix.QuantumChannel.trace_map`: a quantum channel
  preserves the trace.
* `Matrix.QuantumChannel.posSemidef_apply`: a quantum channel preserves positive semidefinite
  matrices.
* `Matrix.QuantumChannel.ext`: quantum channels agreeing on every matrix are equal.
* `Matrix.QuantumChannel.coe_comp`, `Matrix.QuantumChannel.comp_apply`: the composite channel
  `Ψ.comp Φ` is the composite function `Ψ ∘ Φ`.

## Mathematical Background

Complete positivity is Mathlib's `CompletelyPositiveMap` condition: applying `Φ` entrywise to a
`k × k` block matrix `M` with entries in `M_n(ℂ)` preserves nonnegativity, for every `k`. Here
`M_n(ℂ)` is the C⋆-algebra of `Matrix.Norms.L2Operator`, ordered by `MatrixOrder`, and the block
matrices form the C⋆-algebra `CStarMatrix (Fin k) (Fin k) (Matrix n n ℂ)`; by
`CStarMatrix.nonneg_iff_posSemidef_comp` its order is positive semidefiniteness of the flattened
`kn × kn` matrix, which is the physicists' condition that `id_k ⊗ Φ` be positive
(`Matrix.posSemidef_comp_map` in `Choi.lean`).

This file specialises that general notion to the matrix algebras `M_n(ℂ)`. The general theory is
used beyond matrices elsewhere: the Kadison–Schwarz inequality
`φ(a)⋆ φ(a) ≤ ‖φ 1‖ • φ(a⋆ a)` for `2`-positive, in particular completely positive, maps on an
arbitrary unital C⋆-algebra, into a possibly non-unital one, is
`KPositiveMapClass.le_norm_smul_map_star_mul`; on a non-unital domain `‖φ‖` replaces `‖φ 1‖`
(`KPositiveMapClass.le_opNorm_smul_map_star_mul`), and the normalised form
`φ(a)⋆ φ(a) ≤ φ(a⋆ a)` under `φ 1 ≤ 1` between unital C⋆-algebras is
`KPositiveMapClass.le_map_star_mul`
(`QuantumSystem/ForMathlib/Analysis/CStarAlgebra/KPositiveMap.lean`); and the trace dual of a channel
is a Schwarz map on `B(ℂᵐ)` (`QuantumSystem/Analysis/Matrix/QuantumChannel/Dual.lean`).

By the Choi–Kraus theorem (`QuantumSystem/Analysis/Matrix/QuantumChannel/Choi.lean`) complete
positivity is equivalent to positive semidefiniteness of the Choi matrix and to the existence of a
Kraus representation `Φ(ρ) = Σᵢ Kᵢ ρ Kᵢᴴ`. The completeness relation `Σᵢ Kᵢᴴ Kᵢ = I` for
trace-preserving maps is in `QuantumSystem/Analysis/Matrix/QuantumChannel/Kraus.lean`. By
Stinespring's theorem (`QuantumSystem/Analysis/Matrix/QuantumChannel/Stinespring.lean`) a map is a
quantum channel iff it is `ρ ↦ tr₂(V ρ Vᴴ)` for an isometry `V`, the partial trace `tr₂` removing
the environment (`Matrix.QuantumChannel.exists_coe_eq_iff_exists_stinespringMatrix`).

## Implementation notes

The instances `Matrix.Norms.L2Operator` and `MatrixOrder` are scoped, so writing
`Matrix n n ℂ →CP Matrix m m ℂ` directly needs
`open scoped CStarAlgebra Matrix.Norms.L2Operator MatrixOrder`. The type `QuantumChannel n m`
itself carries them: stating and using channels needs none of these scopes, through the
application `Φ A`, the linear map `(Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)`, the API of this
namespace (`QuantumChannel.trace_map`, `QuantumChannel.id`, `QuantumChannel.comp`,
`QuantumChannel.posSemidef_apply`), and every lemma stated for
the concrete type `Matrix n n ℂ →CP Matrix m m ℂ`, applied to the parent
`Φ.toCompletelyPositiveMap`. Positive semidefiniteness of complex matrices needs the order on `ℂ`
(`open scoped ComplexOrder`), as everywhere for `Matrix.PosSemidef`. Only API generic in the
C⋆-algebra, whose instances are re-synthesised for `Matrix n n ℂ` — the `CompletelyPositiveMapClass`
instance of `QuantumChannel n m` and the generic `CompletelyPositiveMap` operations such as
`CompletelyPositiveMap.toLinearMap` or `CompletelyPositiveMap.comp` — needs the scoped instances.

The lemmas of this namespace are therefore not a second copy of the generic class API: they state
its consequences in Mathlib's scope-free matrix vocabulary (`Tr`, `Matrix.PosSemidef`), so that a
channel can be used without the scopes. Passing a channel to a lemma stated for a positivity
class, such as `Matrix.umegakiEntropy_le_of_kPositiveMap`, needs
`open scoped Matrix.Norms.L2Operator MatrixOrder in` at that one call site. Making the instances
global in this project is not an option: `Analysis/Matrix/HermitianFunctionalCalculus.lean`
works with the local `Matrix.linftyOpNormedRing` instances, which would then collide.

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

The type carries the scoped instances `Matrix.Norms.L2Operator` and `MatrixOrder`, so stating and
using channels needs no `open scoped`; see the implementation notes of this file. -/
structure QuantumChannel (n m : Type*) [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    extends Matrix n n ℂ →CP Matrix m m ℂ where
  /-- A quantum channel preserves the trace. -/
  isTracePreserving' : IsTracePreserving toCompletelyPositiveMap

namespace QuantumChannel

open scoped Matrix.Norms.L2Operator MatrixOrder

/-- A quantum channel is applied as its underlying completely positive map. -/
instance : FunLike (QuantumChannel n m) (Matrix n n ℂ) (Matrix m m ℂ) where
  coe Φ := Φ.toCompletelyPositiveMap
  coe_injective Φ Ψ h := by
    cases Φ
    cases Ψ
    congr
    exact DFunLike.coe_injective h

/-- A quantum channel is a `ℂ`-linear map, giving the coercion
`(Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)`. -/
instance : LinearMapClass (QuantumChannel n m) ℂ (Matrix n n ℂ) (Matrix m m ℂ) where
  map_add Φ := map_add Φ.toCompletelyPositiveMap
  map_smulₛₗ Φ := map_smulₛₗ Φ.toCompletelyPositiveMap

/-- A quantum channel is completely positive, so the API of `CompletelyPositiveMapClass` (and of
`OrderHomClass`) applies to it. -/
instance : CompletelyPositiveMapClass (QuantumChannel n m) (Matrix n n ℂ) (Matrix m m ℂ) where
  map_cstarMatrix_nonneg' Φ := Φ.toCompletelyPositiveMap.map_cstarMatrix_nonneg'

/-- The underlying completely positive map of `Φ` is `Φ` as a function. -/
@[simp] lemma coe_toCompletelyPositiveMap (Φ : QuantumChannel n m) :
    ⇑Φ.toCompletelyPositiveMap = Φ :=
  rfl

/-- The quantum channel built from `φ` is `φ` as a function. -/
@[simp] lemma coe_mk (φ : Matrix n n ℂ →CP Matrix m m ℂ) (h : IsTracePreserving φ) :
    ⇑(⟨φ, h⟩ : QuantumChannel n m) = φ :=
  rfl

/-- Two quantum channels agreeing on every matrix are equal. -/
@[ext] lemma ext {Φ Ψ : QuantumChannel n m} (h : ∀ A, Φ A = Ψ A) : Φ = Ψ :=
  DFunLike.ext _ _ h

/-- A quantum channel is trace-preserving. -/
lemma isTracePreserving (Φ : QuantumChannel n m) : IsTracePreserving Φ :=
  Φ.isTracePreserving'

/-- A quantum channel preserves the trace: `Tr (Φ A) = Tr A`. -/
@[simp] lemma trace_map (Φ : QuantumChannel n m) (A : Matrix n n ℂ) : Tr (Φ A) = Tr A :=
  Φ.isTracePreserving' A

/-- The identity map is a quantum channel. -/
protected noncomputable def id : QuantumChannel n n where
  toCompletelyPositiveMap := CompletelyPositiveMap.id _
  isTracePreserving' _ := rfl

/-- The identity channel is the identity function. -/
@[simp] lemma coe_id : ⇑(QuantumChannel.id : QuantumChannel n n) = id :=
  rfl

/-- The identity channel fixes every matrix. -/
lemma id_apply (A : Matrix n n ℂ) : QuantumChannel.id A = A :=
  rfl

/-- Composition of quantum channels is a quantum channel: `Ψ.comp Φ` is `Ψ ∘ Φ`, applying `Φ`
first. -/
noncomputable def comp (Ψ : QuantumChannel m k) (Φ : QuantumChannel n m) : QuantumChannel n k where
  toCompletelyPositiveMap := Ψ.toCompletelyPositiveMap.comp Φ.toCompletelyPositiveMap
  isTracePreserving' A := (Ψ.trace_map (Φ A)).trans (Φ.trace_map A)

/-- The composite channel `Ψ.comp Φ` is the composite function `Ψ ∘ Φ`. -/
@[simp] lemma coe_comp (Ψ : QuantumChannel m k) (Φ : QuantumChannel n m) : ⇑(Ψ.comp Φ) = Ψ ∘ Φ :=
  rfl

/-- The composite channel `Ψ.comp Φ` sends `A` to `Ψ (Φ A)`. -/
lemma comp_apply (Ψ : QuantumChannel m k) (Φ : QuantumChannel n m) (A : Matrix n n ℂ) :
    Ψ.comp Φ A = Ψ (Φ A) :=
  rfl

/-- A quantum channel sends positive semidefinite matrices to positive semidefinite matrices
(`Matrix.PosSemidef.map` for the completely positive map `Φ`). -/
lemma posSemidef_apply (Φ : QuantumChannel n m) {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    (Φ A).PosSemidef :=
  hA.map Φ

/-- A `⋆`-algebra equivalence `φ : M_n(ℂ) ≃⋆ₐ M_m(ℂ)` is a quantum channel: it is completely
positive as a `⋆`-homomorphism (`NonUnitalStarAlgHomClass.instCompletelyPositiveMapClass`) and
preserves the trace (`Matrix.trace_map`). By Skolem–Noether every such `φ` is conjugation by a
unitary, so these are the unitary channels. -/
noncomputable def ofStarAlgEquiv (φ : Matrix n n ℂ ≃⋆ₐ[ℂ] Matrix m m ℂ) : QuantumChannel n m where
  toLinearMap := φ
  map_cstarMatrix_nonneg' := CompletelyPositiveMapClass.map_cstarMatrix_nonneg' φ
  isTracePreserving' := Matrix.trace_map φ

/-- The channel of a `⋆`-algebra equivalence `φ` is `φ` as a function. -/
@[simp] lemma coe_ofStarAlgEquiv (φ : Matrix n n ℂ ≃⋆ₐ[ℂ] Matrix m m ℂ) :
    ⇑(ofStarAlgEquiv φ) = φ :=
  rfl

/-- Conjugation by an index equivalence `e : n ≃ m`, `A ↦ A.reindex e e`, as a quantum channel: the
channel of `Matrix.reindexStarAlgEquiv e`. -/
noncomputable def reindex (e : n ≃ m) : QuantumChannel n m :=
  ofStarAlgEquiv (Matrix.reindexStarAlgEquiv (R := ℂ) e)

/-- The reindexing channel acts as `Matrix.reindex e e`. -/
@[simp] lemma reindex_apply (e : n ≃ m) (A : Matrix n n ℂ) : reindex e A = A.reindex e e :=
  rfl

end QuantumChannel

end Matrix
