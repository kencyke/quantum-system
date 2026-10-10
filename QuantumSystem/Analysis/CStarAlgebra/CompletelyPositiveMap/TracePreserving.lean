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
# Completely positive trace-preserving maps on bounded operators

Let `H` and `K` be finite-dimensional complex Hilbert spaces. A **completely positive
trace-preserving (CPTP) map** `Φ : B(H) → B(K)` on the C⋆-algebras `B(H) = H →L[ℂ] H` and `B(K)`
is a map that is
1. completely positive (CP): `id_k ⊗ Φ` is positive for every `k`;
2. trace preserving (TP): `tr (Φ A) = tr A` for all `A`.

Complete positivity is Mathlib's `CompletelyPositiveMap` condition (`(H →L[ℂ] H) →CP (K →L[ℂ] K)`)
for the C⋆-algebra structure and the Loewner order of `H →L[ℂ] H`, both global instances of
Mathlib, and the trace is Mathlib's `LinearMap.trace ℂ H`, written `Tr`. In quantum information
these are the *quantum channels*, the physically realizable operations on the states of a finite
quantum system; matrix algebras are the case `H = EuclideanSpace ℂ n`.

## Main definitions

* `IsTracePreserving Φ`: a map `Φ : B(H) → B(K)` preserves the trace.
* `CPTPMap H K`: trace-preserving completely positive maps `B(H) → B(K)`, extending a
  `CompletelyPositiveMap` by trace preservation, with `FunLike`, `LinearMapClass` and
  `CompletelyPositiveMapClass` instances.
* `CPTPMap.id`, `CPTPMap.comp`: identity and composition.
* `CPTPMap.ofStarAlgEquiv`: a `⋆`-algebra equivalence `B(H) ≃⋆ₐ B(K)` as a CPTP map.
* `CPTPMap.ofLinearIsometryEquiv`: the unitary conjugation `A ↦ U A U†` of a unitary
  `U : H ≃ K` as a CPTP map.

## Main statements

* `isTracePreserving_iff_traceDual_one`: a linear map is trace preserving iff its trace dual
  `ContinuousLinearMap.traceDual Φ` is unital.
* `CPTPMap.trace_map`: a CPTP map preserves the trace.
* `CPTPMap.ext`: CPTP maps agreeing on every operator are equal.

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

/-! ### Completely positive trace-preserving maps -/

variable (H K) in
/-- A **CPTP map** `B(H) → B(K)` between the operator algebras of finite-dimensional Hilbert
spaces is a completely positive map in Mathlib's sense (`CompletelyPositiveMap`) that preserves
the trace. -/
structure CPTPMap extends (H →L[ℂ] H) →CP (K →L[ℂ] K) where
  /-- A CPTP map preserves the trace. -/
  isTracePreserving' : IsTracePreserving toCompletelyPositiveMap

namespace CPTPMap

/-- A CPTP map is applied as its underlying completely positive map. -/
instance : FunLike (CPTPMap H K) (H →L[ℂ] H) (K →L[ℂ] K) where
  coe Φ := Φ.toCompletelyPositiveMap
  coe_injective Φ Ψ h := by
    cases Φ
    cases Ψ
    congr
    exact DFunLike.coe_injective h

/-- A CPTP map is a `ℂ`-linear map, giving the coercion
`(Φ : (H →L[ℂ] H) →ₗ[ℂ] (K →L[ℂ] K))`. -/
instance : LinearMapClass (CPTPMap H K) ℂ (H →L[ℂ] H) (K →L[ℂ] K) where
  map_add Φ := map_add Φ.toCompletelyPositiveMap
  map_smulₛₗ Φ := map_smulₛₗ Φ.toCompletelyPositiveMap

/-- A CPTP map is completely positive, so the API of `CompletelyPositiveMapClass` (and of
`OrderHomClass`) applies to it. -/
instance : CompletelyPositiveMapClass (CPTPMap H K) (H →L[ℂ] H) (K →L[ℂ] K) where
  map_cstarMatrix_nonneg' Φ := Φ.toCompletelyPositiveMap.map_cstarMatrix_nonneg'

/-- The underlying completely positive map of `Φ` is `Φ` as a function. -/
@[simp] lemma coe_toCompletelyPositiveMap (Φ : CPTPMap H K) :
    ⇑Φ.toCompletelyPositiveMap = Φ :=
  rfl

/-- The CPTP map built from `φ` is `φ` as a function. -/
@[simp] lemma coe_mk (φ : (H →L[ℂ] H) →CP (K →L[ℂ] K)) (h : IsTracePreserving φ) :
    ⇑(⟨φ, h⟩ : CPTPMap H K) = φ :=
  rfl

/-- Two CPTP maps agreeing on every operator are equal. -/
@[ext] lemma ext {Φ Ψ : CPTPMap H K} (h : ∀ A, Φ A = Ψ A) : Φ = Ψ :=
  DFunLike.ext _ _ h

/-- A CPTP map is trace preserving. -/
lemma isTracePreserving (Φ : CPTPMap H K) : IsTracePreserving Φ :=
  Φ.isTracePreserving'

/-- A CPTP map preserves the trace: `tr (Φ A) = tr A`. -/
@[simp] lemma trace_map (Φ : CPTPMap H K) (A : H →L[ℂ] H) :
    Tr (Φ A) = Tr A :=
  Φ.isTracePreserving' A

/-- The trace dual of a CPTP map is unital. -/
lemma traceDual_one (Φ : CPTPMap H K) : ContinuousLinearMap.traceDual Φ 1 = 1 :=
  isTracePreserving_iff_traceDual_one.1 Φ.isTracePreserving

variable (H) in
/-- The identity map is a CPTP map. -/
protected noncomputable def id : CPTPMap H H where
  toCompletelyPositiveMap := CompletelyPositiveMap.id _
  isTracePreserving' _ := rfl

/-- The identity CPTP map is the identity function. -/
@[simp] lemma coe_id : ⇑(CPTPMap.id H) = id :=
  rfl

/-- The identity CPTP map fixes every operator. -/
lemma id_apply (A : H →L[ℂ] H) : CPTPMap.id H A = A :=
  rfl

/-- Composition of CPTP maps is a CPTP map: `Ψ.comp Φ` is `Ψ ∘ Φ`, applying `Φ`
first. -/
noncomputable def comp (Ψ : CPTPMap K L) (Φ : CPTPMap H K) : CPTPMap H L where
  toCompletelyPositiveMap := Ψ.toCompletelyPositiveMap.comp Φ.toCompletelyPositiveMap
  isTracePreserving' A := (Ψ.trace_map (Φ A)).trans (Φ.trace_map A)

/-- The composite CPTP map `Ψ.comp Φ` is the composite function `Ψ ∘ Φ`. -/
@[simp] lemma coe_comp (Ψ : CPTPMap K L) (Φ : CPTPMap H K) : ⇑(Ψ.comp Φ) = Ψ ∘ Φ :=
  rfl

/-- The composite CPTP map `Ψ.comp Φ` sends `A` to `Ψ (Φ A)`. -/
lemma comp_apply (Ψ : CPTPMap K L) (Φ : CPTPMap H K) (A : H →L[ℂ] H) :
    Ψ.comp Φ A = Ψ (Φ A) :=
  rfl

/-- A `⋆`-algebra equivalence `φ : B(H) ≃⋆ₐ B(K)` is a CPTP map: it is completely
positive as a `⋆`-homomorphism (`NonUnitalStarAlgHomClass.instCompletelyPositiveMapClass`), and
it preserves the trace as an algebra isomorphism (`ContinuousLinearMap.trace_map`). By
Skolem–Noether every such `φ` is conjugation by a unitary, so these are the unitary CPTP maps; that
characterisation is not formalised here. -/
noncomputable def ofStarAlgEquiv (φ : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (K →L[ℂ] K)) : CPTPMap H K where
  toCompletelyPositiveMap := CompletelyPositiveMapClass.toCompletelyPositiveLinearMap φ
  isTracePreserving' := ContinuousLinearMap.trace_map φ

/-- The CPTP map of a `⋆`-algebra equivalence `φ` is `φ` as a function. -/
@[simp] lemma coe_ofStarAlgEquiv (φ : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (K →L[ℂ] K)) :
    ⇑(ofStarAlgEquiv φ) = φ :=
  rfl

/-- The **unitary conjugation** `A ↦ U A U†` by a unitary `U : H ≃ K` as a CPTP map: the CPTP map
of the `⋆`-algebra equivalence `LinearIsometryEquiv.conjStarAlgEquiv U`. -/
noncomputable def ofLinearIsometryEquiv (U : H ≃ₗᵢ[ℂ] K) : CPTPMap H K :=
  ofStarAlgEquiv U.conjStarAlgEquiv

/-- The unitary conjugation by `U` acts as `A ↦ U A U†`. -/
lemma ofLinearIsometryEquiv_apply (U : H ≃ₗᵢ[ℂ] K) (A : H →L[ℂ] H) :
    ofLinearIsometryEquiv U A =
      (U : H →L[ℂ] K) ∘L A ∘L (U : H →L[ℂ] K)† := by
  rw [U.adjoint_eq_symm]
  rfl

end CPTPMap
