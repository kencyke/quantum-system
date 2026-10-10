/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.CStarAlgebra.CompletelyPositiveMap.TracePreserving
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.Stinespring

/-!
# Kraus maps

A finite family of operators `Tₐ : H →L[ℂ] K` defines the **Kraus map**
`A ↦ Σₐ Tₐ A Tₐ†` from `B(H)` to `B(K)`. It is completely positive
(`CompletelyPositiveMap.ofKraus`): applied entrywise to a block matrix `M`, its quadratic form is
`Σₐ Σᵢⱼ ⟪Tₐ† ξᵢ, Mᵢⱼ Tₐ† ξⱼ⟫`, nonnegative for `0 ≤ M`
(`CStarMatrix.nonneg_iff_sum_inner_apply_nonneg`). A map with Kraus operators `Tₐ` is trace
preserving iff the completeness relation `Σₐ Tₐ† Tₐ = 1` holds
(`isTracePreserving_iff_sum_adjoint_comp_eq_one`), since its trace dual is `B ↦ Σₐ Tₐ† B Tₐ`; so
a Kraus map with `Σₐ Tₐ† Tₐ = 1` is a CPTP map (`CPTPMap.ofKraus`).

Conversely every completely positive map between the operator algebras of finite-dimensional
Hilbert spaces is a Kraus map (`QuantumSystem/Analysis/CStarAlgebra/CompletelyPositiveMap/Choi.lean`), with
as few as `rank J(Φ)` operators
(`QuantumSystem/Analysis/CStarAlgebra/CompletelyPositiveMap/Stinespring.lean`).

## Main definitions

* `CompletelyPositiveMap.ofKraus T`: the Kraus map `A ↦ Σₐ Tₐ A Tₐ†` as a completely positive map.
* `CPTPMap.ofKraus T hT`: the Kraus map of a family with `Σₐ Tₐ† Tₐ = 1` as a CPTP map.

## Main statements

* `isTracePreserving_iff_sum_adjoint_comp_eq_one`: a map with Kraus operators `Tₐ` is trace
  preserving iff `Σₐ Tₐ† Tₐ = 1`.

## References

* Nielsen, Chuang, *Quantum Computation and Quantum Information*, §8.2.3 and Theorem 8.1 (there for
  trace non-increasing operations, `Σₐ Eₐ† Eₐ ≤ 1`)
* Watrous, *The Theory of Quantum Information*, Corollary 2.27
-/

@[expose] public section

open ContinuousLinearMap
open scoped CStarAlgebra InnerProductSpace ComplexOrder

/-! ### Kraus maps are completely positive -/

namespace CompletelyPositiveMap

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The **Kraus map** `A ↦ Σₐ Tₐ A Tₐ†` of a finite family `T : ι → H →L[ℂ] K` is completely
positive: applied entrywise to a block matrix `M`, its quadratic form is
`Σᵢⱼ ⟪ξᵢ, Σₐ Tₐ Mᵢⱼ Tₐ† ξⱼ⟫ = Σₐ Σᵢⱼ ⟪Tₐ† ξᵢ, Mᵢⱼ Tₐ† ξⱼ⟫ ≥ 0`
(`CStarMatrix.nonneg_iff_sum_inner_apply_nonneg`). The spaces need not be finite-dimensional. -/
noncomputable def ofKraus {ι : Type*} [Fintype ι] (T : ι → H →L[ℂ] K) :
    (H →L[ℂ] H) →CP (K →L[ℂ] K) where
  toFun A := ∑ a, T a ∘L A ∘L adjoint (T a)
  map_add' A B := by simp [add_comp, comp_add, Finset.sum_add_distrib]
  map_smul' c A := by simp [smul_comp, Finset.smul_sum]
  map_cstarMatrix_nonneg' k M hM := by
    classical
    rw [CStarMatrix.nonneg_iff_sum_inner_apply_nonneg] at hM ⊢
    intro ξ
    change 0 ≤ ∑ i, ∑ j, ⟪ξ i, (∑ a, T a ∘L M i j ∘L adjoint (T a)) (ξ j)⟫_ℂ
    have h (i j : Fin k) : ⟪ξ i, (∑ a, T a ∘L M i j ∘L adjoint (T a)) (ξ j)⟫_ℂ =
        ∑ a, ⟪adjoint (T a) (ξ i), M i j (adjoint (T a) (ξ j))⟫_ℂ := by
      simp [adjoint_inner_left]
    calc (0 : ℂ) ≤ ∑ a, ∑ i, ∑ j, ⟪adjoint (T a) (ξ i), M i j (adjoint (T a) (ξ j))⟫_ℂ :=
          Finset.sum_nonneg fun a _ => hM _
      _ = _ := by
          simp only [h]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

/-- The Kraus map `CompletelyPositiveMap.ofKraus T` sends `A` to `Σₐ Tₐ A Tₐ†`. -/
lemma ofKraus_apply {ι : Type*} [Fintype ι] (T : ι → H →L[ℂ] K) (A : H →L[ℂ] H) :
    ofKraus T A = ∑ a, T a ∘L A ∘L adjoint (T a) :=
  rfl

end CompletelyPositiveMap

/-! ### Trace preservation and the completeness relation -/

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]

/-- A map with Kraus operators `Tₐ`, `Φ(A) = Σₐ Tₐ A Tₐ†`, is trace preserving iff the Kraus
operators satisfy the **completeness relation** `Σₐ Tₐ† Tₐ = 1`: its trace dual is
`B ↦ Σₐ Tₐ† B Tₐ` (`ContinuousLinearMap.traceDual_eq_sum_of_kraus`), and `Φ` is trace preserving
iff the trace dual is unital (`isTracePreserving_iff_traceDual_one`). -/
lemma isTracePreserving_iff_sum_adjoint_comp_eq_one {F : Type*}
    [FunLike F (H →L[ℂ] H) (K →L[ℂ] K)] [LinearMapClass F ℂ (H →L[ℂ] H) (K →L[ℂ] K)] {Φ : F}
    {ι : Type*} [Fintype ι] {T : ι → H →L[ℂ] K} (hT : ∀ A, Φ A = ∑ a, T a ∘L A ∘L adjoint (T a)) :
    IsTracePreserving Φ ↔ ∑ a, adjoint (T a) ∘L T a = 1 := by
  rw [isTracePreserving_iff_traceDual_one, traceDual_eq_sum_of_kraus hT]
  simp only [one_def, id_comp]

namespace CPTPMap

/-- The **CPTP map of a Kraus representation**: the Kraus map `A ↦ Σₐ Tₐ A Tₐ†` of a family
satisfying the completeness relation `Σₐ Tₐ† Tₐ = 1`. -/
noncomputable def ofKraus {ι : Type*} [Fintype ι] (T : ι → H →L[ℂ] K)
    (hT : ∑ a, adjoint (T a) ∘L T a = 1) : CPTPMap H K where
  toCompletelyPositiveMap := CompletelyPositiveMap.ofKraus T
  isTracePreserving' := (isTracePreserving_iff_sum_adjoint_comp_eq_one fun _ => rfl).2 hT

/-- The CPTP map `CPTPMap.ofKraus T hT` sends `A` to `Σₐ Tₐ A Tₐ†`. -/
lemma ofKraus_apply {ι : Type*} [Fintype ι] (T : ι → H →L[ℂ] K)
    (hT : ∑ a, adjoint (T a) ∘L T a = 1) (A : H →L[ℂ] H) :
    ofKraus T hT A = ∑ a, T a ∘L A ∘L adjoint (T a) :=
  rfl

end CPTPMap
