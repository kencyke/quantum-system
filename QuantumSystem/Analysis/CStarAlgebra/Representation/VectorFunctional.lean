/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.CStarAlgebra.Representation.Irreducible
public import QuantumSystem.ForMathlib.Algebra.Order.Star.Basic
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.StateSpace

/-!
# Vector functionals of a `CStarRep`

For a representation `R : CStarRep A` and vectors `v`, `w ∈ R.H`, the *matrix coefficient*
`a ↦ ⟪v, π a w⟫` is a continuous linear functional of norm at most `‖v‖ ‖w‖`. Its diagonal case
`w = v` is the *vector functional* `a ↦ ⟪v, π a v⟫`, which is positive.  Nothing here
uses a cyclic vector or a state; the GNS triplets `GNS.Representation f` use it through their
underlying `CStarRep`.

## Main definitions

* `CStarRep.matrixCoeff R v w` — the functional `a ↦ ⟪v, π a w⟫`, in the weak-\* dual.
* `CStarRep.vectorFunctional R v` — the functional `a ↦ ⟪v, π a v⟫`, the matrix coefficient
  `R.matrixCoeff v v`.

## Main results

* `CStarRep.opNorm_matrixCoeff_le` — `‖⟪v, π(·) w⟫‖ ≤ ‖v‖ ‖w‖`.
* `CStarRep.vectorFunctional_nonneg` — vector functionals are positive.
* `CStarRep.opNorm_vectorFunctional_le` — `‖⟪v, π(·) v⟫‖ ≤ ‖v‖²`.
* `CStarRep.normalized_vectorFunctional_mem_quasiStateSpace` — `‖v‖⁻² ⟪v, π(·) v⟫` is a
  quasi-state for `v ≠ 0`.
* `CStarRep.vectorFunctional_add_of_mem_orthogonal` — along an invariant submodule `W`, the
  vector functional of `v₁ + v₂` with `v₁ ∈ W`, `v₂ ∈ Wᗮ` splits as the sum of the two.
-/

@[expose] public section

namespace CStarRep

open scoped ComplexOrder InnerProductSpace InnerProduct

variable {A : Type*} [NonUnitalCStarAlgebra A] (R : CStarRep A)

/-- The matrix coefficient `a ↦ ⟪v, π a w⟫` of two vectors `v`, `w` of a representation, a
continuous linear functional. For `w = v` it is the vector functional `CStarRep.vectorFunctional`. -/
noncomputable def matrixCoeff (v w : R.H) : WeakDual ℂ A :=
  (innerSL ℂ v).comp (R.orbit w)

/-- `matrixCoeff v w a = ⟪v, π a w⟫`. -/
@[simp]
lemma matrixCoeff_apply (v w : R.H) (a : A) :
    R.matrixCoeff v w a = ⟪v, R.π a w⟫_ℂ :=
  rfl

/-- The matrix coefficient of `v` and `w` has norm at most `‖v‖ ‖w‖`: `‖⟪v, π a w⟫‖ ≤ ‖v‖ ‖π a‖ ‖w‖`
and `π` is contractive. -/
lemma opNorm_matrixCoeff_le (v w : R.H) :
    ‖WeakDual.toStrongDual (R.matrixCoeff v w)‖ ≤ ‖v‖ * ‖w‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun a => ?_
  calc ‖⟪v, R.π a w⟫_ℂ‖
      ≤ ‖v‖ * ‖R.π a w‖ := norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖a‖ * ‖w‖) := by
        gcongr
        exact ((R.π a).le_opNorm w).trans
          (mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le _ a) (norm_nonneg _))
    _ = ‖v‖ * ‖w‖ * ‖a‖ := by ring

/-- The vector functional `a ↦ ⟪v, π a v⟫` of a vector `v` of a representation: the matrix
coefficient `CStarRep.matrixCoeff` of `v` and `v`. -/
noncomputable def vectorFunctional (v : R.H) : WeakDual ℂ A :=
  R.matrixCoeff v v

/-- The matrix coefficient of `v` and `v` is the vector functional of `v`. -/
lemma matrixCoeff_self (v : R.H) : R.matrixCoeff v v = R.vectorFunctional v :=
  rfl

/-- `vectorFunctional v a = ⟪v, π a v⟫`. -/
@[simp]
lemma vectorFunctional_apply (v : R.H) (a : A) :
    R.vectorFunctional v a = ⟪v, R.π a v⟫_ℂ :=
  rfl

/-- The vector functional of `v` has norm at most `‖v‖²`, the case `w = v` of
`CStarRep.opNorm_matrixCoeff_le`. -/
lemma opNorm_vectorFunctional_le (v : R.H) :
    ‖WeakDual.toStrongDual (R.vectorFunctional v)‖ ≤ ‖v‖ ^ 2 :=
  (R.opNorm_matrixCoeff_le v v).trans_eq (sq ‖v‖).symm

/-- Along an invariant submodule `W`, the vector functional of `v₁ + v₂` with `v₁ ∈ W` and
`v₂ ∈ Wᗮ` is the sum of the two vector functionals: the cross terms `⟪v₁, π a v₂⟫` and
`⟪v₂, π a v₁⟫` vanish. -/
lemma vectorFunctional_add_of_mem_orthogonal {W : Submodule ℂ R.H} (hW : W ∈ R.invtSubmodule)
    {v₁ v₂ : R.H} (hv₁ : v₁ ∈ W) (hv₂ : v₂ ∈ Wᗮ) :
    R.vectorFunctional (v₁ + v₂) = R.vectorFunctional v₁ + R.vectorFunctional v₂ := by
  refine ContinuousLinearMap.ext fun a => ?_
  change ⟪v₁ + v₂, R.π a (v₁ + v₂)⟫_ℂ = ⟪v₁, R.π a v₁⟫_ℂ + ⟪v₂, R.π a v₂⟫_ℂ
  rw [map_add, inner_add_left, inner_add_right, inner_add_right,
    inner_apply_eq_zero_of_mem_of_mem_orthogonal hW a hv₁ hv₂,
    inner_apply_eq_zero_of_mem_orthogonal_of_mem hW a hv₂ hv₁, add_zero, zero_add]

section Positivity

variable [PartialOrder A] [StarOrderedRing A]

/-- A vector functional `a ↦ ⟪v, π a v⟫` is positive: on `a* a` it is `‖π a v‖²`. -/
lemma vectorFunctional_nonneg (v : R.H) :
    ∀ a : A, 0 ≤ a → 0 ≤ R.vectorFunctional v a := by
  refine fun _ => StarOrderedRing.map_nonneg_of_star_mul_self_nonneg _ fun a => ?_
  have h : R.vectorFunctional v (star a * a) = ((‖R.π a v‖ ^ 2 : ℝ) : ℂ) := by
    rw [vectorFunctional_apply, map_mul, ← R.adjoint_π]
    change ⟪v, ((R.π a)†) (R.π a v)⟫_ℂ = _
    rw [ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    simp
  rw [h]
  exact Complex.zero_le_real.mpr (sq_nonneg _)

/-- The vector functional of a unit vector is a quasi-state. -/
lemma vectorFunctional_mem_quasiStateSpace_of_norm_eq_one (v : R.H) (hv : ‖v‖ = 1) :
    R.vectorFunctional v ∈ QuasiStateSpace A := by
  refine ⟨R.vectorFunctional_nonneg v, ?_⟩
  simpa [hv] using R.opNorm_vectorFunctional_le v

/-- The normalised vector functional `‖v‖⁻² ⟪v, π(·) v⟫` of a nonzero vector is a quasi-state. -/
lemma normalized_vectorFunctional_mem_quasiStateSpace (v : R.H) (hv : v ≠ 0) :
    (‖v‖ ^ 2 : ℂ)⁻¹ • R.vectorFunctional v ∈ QuasiStateSpace A := by
  constructor
  · intro a ha
    change 0 ≤ (‖v‖ ^ 2 : ℂ)⁻¹ * R.vectorFunctional v a
    refine mul_nonneg ?_ (R.vectorFunctional_nonneg v a ha)
    rw [← Complex.ofReal_pow, ← Complex.ofReal_inv]
    exact Complex.zero_le_real.mpr (by positivity)
  · rw [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, map_smul, norm_smul, norm_inv]
    simp only [Complex.norm_real, norm_pow, norm_norm]
    rw [← div_eq_inv_mul, div_le_iff₀ (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv)), one_mul]
    exact R.opNorm_vectorFunctional_le v

end Positivity

end CStarRep
