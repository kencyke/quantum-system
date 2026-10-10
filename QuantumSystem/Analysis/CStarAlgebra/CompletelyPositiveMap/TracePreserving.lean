/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.Adjoint
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.TraceDual
public import QuantumSystem.Notation

/-!
# Quantum channels on bounded operators

Let `H` and `K` be finite-dimensional complex Hilbert spaces. A **quantum channel**
`Φ : B(H) → B(K)` on the C⋆-algebras `B(H) = H →L[ℂ] H` and `B(K)` is a map that is
1. completely positive (CP): `id_k ⊗ Φ` is positive for every `k`;
2. trace preserving (TP): `tr (Φ A) = tr A` for all `A`.

Complete positivity is Mathlib's `CompletelyPositiveMap` condition (`(H →L[ℂ] H) →CP (K →L[ℂ] K)`)
for the C⋆-algebra structure and the Loewner order of `H →L[ℂ] H`, both global instances of
Mathlib, and the trace is Mathlib's `LinearMap.trace ℂ H`, written `Tr`. These are the physically
realizable operations on the states of a finite quantum system; matrix algebras are the case
`H = EuclideanSpace ℂ n`.

## Main definitions

* `IsTracePreserving Φ`: a map `Φ : B(H) → B(K)` preserves the trace.
* `QuantumChannel H K`: trace-preserving completely positive maps `B(H) → B(K)`, extending a
  `CompletelyPositiveMap` by trace preservation, with `FunLike`, `LinearMapClass` and
  `CompletelyPositiveMapClass` instances.
* `QuantumChannel.id`, `QuantumChannel.comp`: identity and composition.
* `QuantumChannel.ofStarAlgEquiv`: a `⋆`-algebra equivalence `B(H) ≃⋆ₐ B(K)` as a channel.
* `QuantumChannel.ofLinearIsometryEquiv`: the unitary channel `A ↦ U A U†` of a unitary
  `U : H ≃ K`.

## Main statements

* `isTracePreserving_iff_traceDual_one`: a linear map is trace preserving iff its trace dual
  `ContinuousLinearMap.traceDual Φ` is unital.
* `QuantumChannel.trace_map`: a quantum channel preserves the trace.
* `QuantumChannel.ext`: quantum channels agreeing on every operator are equal.

## References

* Nielsen, Chuang, *Quantum Computation and Quantum Information*, Chapter 8
* Watrous, *The Theory of Quantum Information*, Chapter 2
-/

@[expose] public section

open scoped CStarAlgebra ContinuousLinearMap InnerProduct

variable {H K L : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L]

/-! ### Trace-preserving maps -/

section IsTracePreserving

variable {F : Type*} [FunLike F (H →L[ℂ] H) (K →L[ℂ] K)]

/-- A map `Φ : B(H) → B(K)` between the operator algebras of finite-dimensional Hilbert spaces is
**trace preserving** if `tr (Φ A) = tr A` for all `A`. It is stated for any `FunLike` type, so
that it applies to linear maps and to completely positive maps alike. -/
def IsTracePreserving [FiniteDimensional ℂ H] [FiniteDimensional ℂ K] (Φ : F) : Prop :=
  ∀ A : H →L[ℂ] H, Tr (Φ A) = Tr A

variable [FiniteDimensional ℂ H] [FiniteDimensional ℂ K]

/-- A linear map is trace preserving iff its trace dual is unital
(`ContinuousLinearMap.traceDual_one_iff`). -/
theorem isTracePreserving_iff_traceDual_one [LinearMapClass F ℂ (H →L[ℂ] H) (K →L[ℂ] K)]
    {Φ : F} : IsTracePreserving Φ ↔ ContinuousLinearMap.traceDual Φ 1 = 1 :=
  ContinuousLinearMap.traceDual_one_iff.symm

end IsTracePreserving

variable [FiniteDimensional ℂ H] [FiniteDimensional ℂ K] [FiniteDimensional ℂ L]

/-! ### Quantum channels -/

variable (H K) in
/-- A **quantum channel** is a completely positive trace-preserving (CPTP) map `B(H) → B(K)`
between the operator algebras of finite-dimensional Hilbert spaces: a completely positive map in
Mathlib's sense (`CompletelyPositiveMap`) that preserves the trace. -/
structure QuantumChannel extends (H →L[ℂ] H) →CP (K →L[ℂ] K) where
  /-- A quantum channel preserves the trace. -/
  isTracePreserving' : IsTracePreserving toCompletelyPositiveMap

namespace QuantumChannel

/-- A quantum channel is applied as its underlying completely positive map. -/
instance : FunLike (QuantumChannel H K) (H →L[ℂ] H) (K →L[ℂ] K) where
  coe Φ := Φ.toCompletelyPositiveMap
  coe_injective Φ Ψ h := by
    cases Φ
    cases Ψ
    congr
    exact DFunLike.coe_injective h

/-- A quantum channel is a `ℂ`-linear map, giving the coercion
`(Φ : (H →L[ℂ] H) →ₗ[ℂ] (K →L[ℂ] K))`. -/
instance : LinearMapClass (QuantumChannel H K) ℂ (H →L[ℂ] H) (K →L[ℂ] K) where
  map_add Φ := map_add Φ.toCompletelyPositiveMap
  map_smulₛₗ Φ := map_smulₛₗ Φ.toCompletelyPositiveMap

/-- A quantum channel is completely positive, so the API of `CompletelyPositiveMapClass` (and of
`OrderHomClass`) applies to it. -/
instance : CompletelyPositiveMapClass (QuantumChannel H K) (H →L[ℂ] H) (K →L[ℂ] K) where
  map_cstarMatrix_nonneg' Φ := Φ.toCompletelyPositiveMap.map_cstarMatrix_nonneg'

/-- The underlying completely positive map of `Φ` is `Φ` as a function. -/
@[simp] lemma coe_toCompletelyPositiveMap (Φ : QuantumChannel H K) :
    ⇑Φ.toCompletelyPositiveMap = Φ :=
  rfl

/-- The quantum channel built from `φ` is `φ` as a function. -/
@[simp] lemma coe_mk (φ : (H →L[ℂ] H) →CP (K →L[ℂ] K)) (h : IsTracePreserving φ) :
    ⇑(⟨φ, h⟩ : QuantumChannel H K) = φ :=
  rfl

/-- Two quantum channels agreeing on every operator are equal. -/
@[ext] lemma ext {Φ Ψ : QuantumChannel H K} (h : ∀ A, Φ A = Ψ A) : Φ = Ψ :=
  DFunLike.ext _ _ h

/-- A quantum channel is trace preserving. -/
lemma isTracePreserving (Φ : QuantumChannel H K) : IsTracePreserving Φ :=
  Φ.isTracePreserving'

/-- A quantum channel preserves the trace: `tr (Φ A) = tr A`. -/
@[simp] lemma trace_map (Φ : QuantumChannel H K) (A : H →L[ℂ] H) :
    Tr (Φ A) = Tr A :=
  Φ.isTracePreserving' A

/-- The trace dual of a quantum channel is unital. -/
lemma traceDual_one (Φ : QuantumChannel H K) : ContinuousLinearMap.traceDual Φ 1 = 1 :=
  isTracePreserving_iff_traceDual_one.1 Φ.isTracePreserving

variable (H) in
/-- The identity map is a quantum channel. -/
protected noncomputable def id : QuantumChannel H H where
  toCompletelyPositiveMap := CompletelyPositiveMap.id _
  isTracePreserving' _ := rfl

/-- The identity channel is the identity function. -/
@[simp] lemma coe_id : ⇑(QuantumChannel.id H) = id :=
  rfl

/-- The identity channel fixes every operator. -/
lemma id_apply (A : H →L[ℂ] H) : QuantumChannel.id H A = A :=
  rfl

/-- Composition of quantum channels is a quantum channel: `Ψ.comp Φ` is `Ψ ∘ Φ`, applying `Φ`
first. -/
noncomputable def comp (Ψ : QuantumChannel K L) (Φ : QuantumChannel H K) : QuantumChannel H L where
  toCompletelyPositiveMap := Ψ.toCompletelyPositiveMap.comp Φ.toCompletelyPositiveMap
  isTracePreserving' A := (Ψ.trace_map (Φ A)).trans (Φ.trace_map A)

/-- The composite channel `Ψ.comp Φ` is the composite function `Ψ ∘ Φ`. -/
@[simp] lemma coe_comp (Ψ : QuantumChannel K L) (Φ : QuantumChannel H K) : ⇑(Ψ.comp Φ) = Ψ ∘ Φ :=
  rfl

/-- The composite channel `Ψ.comp Φ` sends `A` to `Ψ (Φ A)`. -/
lemma comp_apply (Ψ : QuantumChannel K L) (Φ : QuantumChannel H K) (A : H →L[ℂ] H) :
    Ψ.comp Φ A = Ψ (Φ A) :=
  rfl

/-- A `⋆`-algebra equivalence `φ : B(H) ≃⋆ₐ B(K)` is a quantum channel: it is completely
positive as a `⋆`-homomorphism (`NonUnitalStarAlgHomClass.instCompletelyPositiveMapClass`), and
it preserves the trace as an algebra isomorphism (`ContinuousLinearMap.trace_map`). By
Skolem–Noether every such `φ` is conjugation by a unitary, so these are the unitary channels; that
characterisation is not formalised here. -/
noncomputable def ofStarAlgEquiv (φ : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (K →L[ℂ] K)) : QuantumChannel H K where
  toCompletelyPositiveMap := CompletelyPositiveMapClass.toCompletelyPositiveLinearMap φ
  isTracePreserving' := ContinuousLinearMap.trace_map φ

/-- The channel of a `⋆`-algebra equivalence `φ` is `φ` as a function. -/
@[simp] lemma coe_ofStarAlgEquiv (φ : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (K →L[ℂ] K)) :
    ⇑(ofStarAlgEquiv φ) = φ :=
  rfl

/-- The **unitary channel** `A ↦ U A U†` of a unitary `U : H ≃ K`: the channel of the
`⋆`-algebra equivalence `LinearIsometryEquiv.conjStarAlgEquiv U`. -/
noncomputable def ofLinearIsometryEquiv (U : H ≃ₗᵢ[ℂ] K) : QuantumChannel H K :=
  ofStarAlgEquiv U.conjStarAlgEquiv

/-- The unitary channel of `U` acts as `A ↦ U A U†`. -/
lemma ofLinearIsometryEquiv_apply (U : H ≃ₗᵢ[ℂ] K) (A : H →L[ℂ] H) :
    ofLinearIsometryEquiv U A =
      (U : H →L[ℂ] K) ∘L A ∘L (U : H →L[ℂ] K)† := by
  rw [U.adjoint_eq_symm]
  rfl

end QuantumChannel
