/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.TensorProduct
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.TraceDual
public import QuantumSystem.ForMathlib.LinearAlgebra.Trace

/-!
# The partial trace

For finite-dimensional complex Hilbert spaces `H` and `K`, the **partial trace** over the right
factor `tr₂ = ContinuousLinearMap.traceRight H K : B(H ⊗ K) → B(H)` is the trace dual of the
ampliation `A ↦ A ⊗ 1` (`ContinuousLinearMap.rTensorStarAlgHom`):
`tr(A ∘ tr₂(X)) = tr((A ⊗ 1) ∘ X)` (`ContinuousLinearMap.trace_comp_traceRight`). On operator
tensors it is `tr₂(A ⊗ B) = tr(B) • A` (`ContinuousLinearMap.traceRight_mapL`). As the trace dual
of a unital ⋆-homomorphism it is completely positive and trace preserving with no further proof:
it is a CPTP map (`CPTPMap.traceRight`, in
`QuantumSystem.Analysis.CStarAlgebra.CompletelyPositiveMap.PartialTrace`). For an orthonormal
basis `(eₐ)` of `K` it is the Kraus map `X ↦ Σₐ ιₐ† X ιₐ` of the insertions `ιₐ : x ↦ x ⊗ eₐ`
(`ContinuousLinearMap.traceRight_eq_sum`). The partial trace over the left factor
`tr₁ = ContinuousLinearMap.traceLeft H K : B(H ⊗ K) → B(K)` is, likewise, the trace dual of
`B ↦ 1 ⊗ B` (`ContinuousLinearMap.trace_comp_traceLeft`).

For an operator `V : H → K ⊗ E`, the Heisenberg picture `Φ*(B) = V† (B ⊗ 1) V` and the Schrödinger
picture `Φ(A) = tr₂(V A V†)` of a map `Φ : B(H) → B(K)` are equivalent
(`ContinuousLinearMap.traceDual_eq_iff_traceRight`); this is how Stinespring's theorem passes
between the two pictures.

## Conventions

The partial trace `tr₂` of the Stinespring form traces out the **right** factor. This is the
convention of Watrous's Stinespring form `Φ(X) = Tr_Z (A X A*)` with `A : X → Y ⊗ Z`, and of the
matrix partial trace `Matrix.traceRight`.

## Main definitions

* `ContinuousLinearMap.traceRight H K`: the partial trace `B(H ⊗ K) → B(H)`.
* `ContinuousLinearMap.traceLeft H K`: the partial trace `B(H ⊗ K) → B(K)` over the left factor.

## Main statements

* `ContinuousLinearMap.trace_comp_traceRight`: the defining duality
  `tr(A ∘ tr₂(X)) = tr((A ⊗ 1) ∘ X)`.
* `ContinuousLinearMap.traceRight_mapL`: `tr₂(A ⊗ B) = tr(B) • A`.
* `ContinuousLinearMap.trace_traceRight`: `tr(tr₂(X)) = tr(X)`.
* `ContinuousLinearMap.traceLeft_mapL`: `tr₁(A ⊗ B) = tr(A) • B`.
* `ContinuousLinearMap.traceRight_eq_sum`: `tr₂(X) = Σₐ ιₐ† X ιₐ`.
* `ContinuousLinearMap.traceDual_eq_iff_traceRight`: `Φ*(B) = V† (B ⊗ 1) V` for all `B` iff
  `Φ(A) = tr₂(V A V†)` for all `A`.

## References

* Nielsen, Chuang, *Quantum Computation and Quantum Information*, §2.4.3
* Watrous, *The Theory of Quantum Information*, §1.1.2
-/

@[expose] public section

open scoped TensorProduct InnerProductSpace ContinuousLinearMap
open TensorProduct

variable {H K E : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

namespace ContinuousLinearMap

variable (H K) in
/-- The **partial trace** `tr₂ : B(H ⊗ K) → B(H)` over the right factor: the trace dual of the
ampliation `A ↦ A ⊗ 1`, so that `tr(A ∘ tr₂(X)) = tr((A ⊗ 1) ∘ X)`
(`ContinuousLinearMap.trace_comp_traceRight`). -/
noncomputable def traceRight : (H ⊗[ℂ] K →L[ℂ] H ⊗[ℂ] K) →ₗ[ℂ] (H →L[ℂ] H) :=
  traceDual (rTensorStarAlgHom ℂ H K)

/-- **The defining duality** of the partial trace: `tr(A ∘ tr₂(X)) = tr((A ⊗ 1) ∘ X)`. -/
lemma trace_comp_traceRight (A : H →L[ℂ] H) (X : H ⊗[ℂ] K →L[ℂ] H ⊗[ℂ] K) :
    Tr (A ∘L traceRight H K X) =
      Tr (A.rTensor K ∘L X) :=
  (trace_comp_traceDual (rTensorStarAlgHom ℂ H K) A X).symm

/-- The partial trace is characterised by its duality: `Y = tr₂(X)` iff
`tr(A ∘ Y) = tr((A ⊗ 1) ∘ X)` for all `A`. -/
lemma eq_traceRight_iff (X : H ⊗[ℂ] K →L[ℂ] H ⊗[ℂ] K) (Y : H →L[ℂ] H) :
    Y = traceRight H K X ↔ ∀ A : H →L[ℂ] H,
      Tr (A ∘L Y) = Tr (A.rTensor K ∘L X) :=
  eq_traceDual_iff (rTensorStarAlgHom ℂ H K) X Y

/-- The partial trace of an operator tensor: `tr₂(A ⊗ B) = tr(B) • A`. -/
lemma traceRight_mapL (A : H →L[ℂ] H) (B : K →L[ℂ] K) :
    traceRight H K (mapL A B) = Tr B • A := by
  rw [eq_comm, eq_traceRight_iff]
  intro C
  rw [comp_smul, toLinearMap_smul, map_smul, rTensor_comp_mapL, toLinearMap_mapL,
    LinearMap.trace_tensorProduct', smul_eq_mul, mul_comm]

/-- The partial trace preserves the trace: `tr(tr₂(X)) = tr(X)`. -/
@[simp] lemma trace_traceRight (X : H ⊗[ℂ] K →L[ℂ] H ⊗[ℂ] K) :
    Tr (traceRight H K X) = Tr X := by
  have h := trace_comp_traceRight (1 : H →L[ℂ] H) X
  rwa [rTensor_one, ← mul_def, ← mul_def, one_mul, one_mul] at h

/-- The trace dual of the partial trace is the ampliation, `tr₂* (A) = A ⊗ 1`
(`ContinuousLinearMap.traceDual_traceDual`). -/
@[simp] lemma traceDual_traceRight (A : H →L[ℂ] H) :
    traceDual (traceRight H K) A = A.rTensor K :=
  traceDual_traceDual (rTensorStarAlgHom ℂ H K) A

/-- For an orthonormal basis `(eₐ)` of `K`, the ampliation is `A ⊗ 1 = Σₐ ιₐ A ιₐ†` with the
insertions `ιₐ : x ↦ x ⊗ eₐ`. -/
lemma rTensor_eq_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ K) (A : H →L[ℂ] H) :
    A.rTensor K = ∑ a, (mkL ℂ H K).flip (b a) ∘L A ∘L adjoint ((mkL ℂ H K).flip (b a)) := by
  refine ContinuousLinearMap.coe_inj.mp <| TensorProduct.ext' fun x y => ?_
  simp only [coe_coe, rTensor_tmul, toLinearMap_sum, LinearMap.coe_sum, Finset.sum_apply,
    coe_comp, Function.comp_apply, adjoint_flip_mkL_apply_tmul, map_smul, flip_apply,
    mkL_apply_apply]
  conv_lhs => rw [← b.sum_repr' y, tmul_sum]
  simp_rw [tmul_smul]

/-- The partial trace is the Kraus map `tr₂(X) = Σₐ ιₐ† X ιₐ` of the insertions
`ιₐ : x ↦ x ⊗ eₐ` along an orthonormal basis `(eₐ)` of `K`: its trace dual is
`A ↦ Σₐ ιₐ A ιₐ† = A ⊗ 1` (`ContinuousLinearMap.rTensor_eq_sum`). -/
lemma traceRight_eq_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ K)
    (X : H ⊗[ℂ] K →L[ℂ] H ⊗[ℂ] K) :
    traceRight H K X =
      ∑ a, adjoint ((mkL ℂ H K).flip (b a)) ∘L X ∘L (mkL ℂ H K).flip (b a) := by
  rw [eq_comm, eq_traceRight_iff]
  intro A
  rw [rTensor_eq_sum b, finsetSum_comp, toLinearMap_sum, map_sum, comp_finsetSum, toLinearMap_sum,
    map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show A ∘L adjoint ((mkL ℂ H K).flip (b a)) ∘L X ∘L (mkL ℂ H K).flip (b a) =
    (A ∘L adjoint ((mkL ℂ H K).flip (b a)) ∘L X) ∘L (mkL ℂ H K).flip (b a) by
      simp only [comp_assoc], trace_comp_comm']
  simp only [comp_assoc]

/-- **Heisenberg and Schrödinger pictures** of conjugation by `V : H → K ⊗ E`: the trace dual of
`Φ : B(H) → B(K)` is `Φ*(B) = V† (B ⊗ 1) V` for all `B` iff `Φ(A) = tr₂(V A V†)` for all `A`. Both
say `tr(Φ(A) B) = tr(V A V† (B ⊗ 1))`, by cyclicity of the trace. -/
lemma traceDual_eq_iff_traceRight {F : Type*} [FunLike F (H →L[ℂ] H) (K →L[ℂ] K)]
    [LinearMapClass F ℂ (H →L[ℂ] H) (K →L[ℂ] K)] {Φ : F} (V : H →L[ℂ] K ⊗[ℂ] E) :
    (∀ B : K →L[ℂ] K, traceDual Φ B = adjoint V ∘L B.rTensor E ∘L V) ↔
      ∀ A : H →L[ℂ] H, Φ A = traceRight K E (V ∘L A ∘L adjoint V) := by
  have key (A : H →L[ℂ] H) (B : K →L[ℂ] K) :
      Tr (A ∘L adjoint V ∘L B.rTensor E ∘L V) =
        Tr (B ∘L traceRight K E (V ∘L A ∘L adjoint V)) := by
    rw [trace_comp_traceRight,
      show A ∘L adjoint V ∘L B.rTensor E ∘L V = (A ∘L adjoint V ∘L B.rTensor E) ∘L V by
        simp only [comp_assoc], trace_comp_comm',
      show V ∘L A ∘L adjoint V ∘L B.rTensor E = (V ∘L A ∘L adjoint V) ∘L B.rTensor E by
        simp only [comp_assoc], trace_comp_comm']
  constructor
  · intro h A
    refine ext_iff_trace_comp_left.2 fun B => ?_
    rw [← key, ← h, trace_comp_comm' (Φ A), trace_comp_traceDual]
  · intro h B
    rw [eq_comm, eq_traceDual_iff]
    intro A
    rw [h, key, trace_comp_comm']

variable (H K) in
/-- The **partial trace** `tr₁ : B(H ⊗ K) → B(K)` over the left factor: the trace dual of the
ampliation `B ↦ 1 ⊗ B`, so that `tr(B ∘ tr₁(X)) = tr((1 ⊗ B) ∘ X)`
(`ContinuousLinearMap.trace_comp_traceLeft`). -/
noncomputable def traceLeft : (H ⊗[ℂ] K →L[ℂ] H ⊗[ℂ] K) →ₗ[ℂ] (K →L[ℂ] K) :=
  traceDual (lTensorStarAlgHom ℂ K H)

/-- **The defining duality** of the partial trace over the left factor:
`tr(B ∘ tr₁(X)) = tr((1 ⊗ B) ∘ X)`. -/
lemma trace_comp_traceLeft (B : K →L[ℂ] K) (X : H ⊗[ℂ] K →L[ℂ] H ⊗[ℂ] K) :
    Tr (B ∘L traceLeft H K X) =
      Tr (B.lTensor H ∘L X) :=
  (trace_comp_traceDual (lTensorStarAlgHom ℂ K H) B X).symm

/-- The partial trace over the left factor is characterised by its duality: `Y = tr₁(X)` iff
`tr(B ∘ Y) = tr((1 ⊗ B) ∘ X)` for all `B`. -/
lemma eq_traceLeft_iff (X : H ⊗[ℂ] K →L[ℂ] H ⊗[ℂ] K) (Y : K →L[ℂ] K) :
    Y = traceLeft H K X ↔ ∀ B : K →L[ℂ] K,
      Tr (B ∘L Y) = Tr (B.lTensor H ∘L X) :=
  eq_traceDual_iff (lTensorStarAlgHom ℂ K H) X Y

/-- The partial trace over the left factor of an operator tensor: `tr₁(A ⊗ B) = tr(A) • B`. -/
lemma traceLeft_mapL (A : H →L[ℂ] H) (B : K →L[ℂ] K) :
    traceLeft H K (mapL A B) = Tr A • B := by
  rw [eq_comm, eq_traceLeft_iff]
  intro C
  rw [comp_smul, toLinearMap_smul, map_smul, lTensor_comp_mapL, toLinearMap_mapL,
    LinearMap.trace_tensorProduct', smul_eq_mul]

/-- The partial trace over the left factor preserves the trace: `tr(tr₁(X)) = tr(X)`. -/
@[simp] lemma trace_traceLeft (X : H ⊗[ℂ] K →L[ℂ] H ⊗[ℂ] K) :
    Tr (traceLeft H K X) = Tr X := by
  have h := trace_comp_traceLeft (1 : K →L[ℂ] K) X
  rwa [lTensor_one, ← mul_def, ← mul_def, one_mul, one_mul] at h

/-- The trace dual of the partial trace over the left factor is the ampliation,
`tr₁* (B) = 1 ⊗ B` (`ContinuousLinearMap.traceDual_traceDual`). -/
@[simp] lemma traceDual_traceLeft (B : K →L[ℂ] K) :
    traceDual (traceLeft H K) B = B.lTensor H :=
  traceDual_traceDual (lTensorStarAlgHom ℂ K H) B

end ContinuousLinearMap
