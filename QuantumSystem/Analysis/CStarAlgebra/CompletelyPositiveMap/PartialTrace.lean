/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.CStarAlgebra.CompletelyPositiveMap.TraceDual
public import QuantumSystem.Analysis.InnerProductSpace.PartialTrace

/-!
# The partial trace as a completely positive trace-preserving map

The partial traces `tr₂ = ContinuousLinearMap.traceRight H K : B(H ⊗ K) → B(H)` and
`tr₁ = ContinuousLinearMap.traceLeft H K : B(H ⊗ K) → B(K)` are the trace duals of the unital
⋆-homomorphisms `A ↦ A ⊗ 1` and `B ↦ 1 ⊗ B`. The trace dual of a completely positive map is
completely positive (`CompletelyPositiveMap.traceDual`), and the partial traces preserve the trace
(`ContinuousLinearMap.trace_traceRight`, `ContinuousLinearMap.trace_traceLeft`), so both are CPTP
maps with no further proof.

## Main definitions

* `CPTPMap.traceRight H K`: the partial trace `B(H ⊗ K) → B(H)` as a CPTP map.
* `CPTPMap.traceLeft H K`: the partial trace `B(H ⊗ K) → B(K)` over the left factor as a
  CPTP map.
-/

@[expose] public section

open scoped TensorProduct InnerProductSpace ContinuousLinearMap
open TensorProduct

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]

namespace CPTPMap

variable (H K) in
/-- The **partial trace** `tr₂ : B(H ⊗ K) → B(H)` as a CPTP map: as the trace dual of the
unital ⋆-homomorphism `A ↦ A ⊗ 1` it is completely positive (`CompletelyPositiveMap.traceDual`),
and it preserves the trace (`ContinuousLinearMap.trace_traceRight`). -/
noncomputable def traceRight : CPTPMap (H ⊗[ℂ] K) H where
  toCompletelyPositiveMap :=
    CompletelyPositiveMap.traceDual (ContinuousLinearMap.rTensorStarAlgHom ℂ H K)
  isTracePreserving' := ContinuousLinearMap.trace_traceRight

/-- The partial-trace CPTP map acts as the partial trace. -/
@[simp] lemma traceRight_apply (X : H ⊗[ℂ] K →L[ℂ] H ⊗[ℂ] K) :
    traceRight H K X = ContinuousLinearMap.traceRight H K X :=
  rfl

variable (H K) in
/-- The **partial trace** `tr₁ : B(H ⊗ K) → B(K)` over the left factor as a CPTP map: the
trace dual of the unital ⋆-homomorphism `B ↦ 1 ⊗ B`. -/
noncomputable def traceLeft : CPTPMap (H ⊗[ℂ] K) K where
  toCompletelyPositiveMap :=
    CompletelyPositiveMap.traceDual (ContinuousLinearMap.lTensorStarAlgHom ℂ K H)
  isTracePreserving' := ContinuousLinearMap.trace_traceLeft

/-- The partial-trace CPTP map over the left factor acts as the partial trace. -/
@[simp] lemma traceLeft_apply (X : H ⊗[ℂ] K →L[ℂ] H ⊗[ℂ] K) :
    traceLeft H K X = ContinuousLinearMap.traceLeft H K X :=
  rfl

end CPTPMap
