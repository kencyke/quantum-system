/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.OperatorSpace.CompletelyBounded

/-!
# Completely positive maps are completely bounded

A completely positive map `φ : S → B` from an operator subsystem `S` of a unital C⋆-algebra into a
C⋆-algebra is completely bounded, with cb norm `‖φ 1‖`
(`CompletelyPositiveMap'.norm_toCompletelyBoundedMap`); in particular so is every completely positive
map on a unital C⋆-algebra (`CompletelyPositiveMap.norm_toCompletelyBoundedMap`).

For a matrix `X` over `S` of norm at most `1`, the block matrix `!![1, X; X⋆, 1]` is positive
(`CStarMatrix.nonneg_one_star_one_iff`), hence so is its image `!![φₖ(1), φₖ(X); φₖ(X)⋆, φₖ(1)]` under
the complete positivity of `φ` at level `2k`, and then `‖φₖ(X)‖ ≤ ‖φₖ(1)‖ = ‖φ 1‖`
(`CStarMatrix.norm_sq_le_of_nonneg`).

## Main definitions

* `CompletelyPositiveMap'.toCompletelyBoundedMap` — a completely positive map on an operator
  subsystem of a unital C⋆-algebra, as a completely bounded map.
* `CompletelyPositiveMap.toCompletelyBoundedMap` — the same for a unital C⋆-algebra.
* `ContinuousLinearMap.compressionCP V` — the compression `T ↦ V† T V` of operators, a completely
  positive map.

## Main results

* `CompletelyPositiveMap'.norm_toCompletelyBoundedMap`, `CompletelyPositiveMap.norm_toCompletelyBoundedMap`
  — the cb norm of a completely positive map is `‖φ 1‖`.
-/

@[expose] public noncomputable section

open scoped CStarAlgebra ComplexOrder
open CStarMatrix

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

namespace OperatorSubsystem

variable {S : OperatorSubsystem A}

omit [PartialOrder A] [StarOrderedRing A] in
/-- The entrywise inclusion of the identity matrix over `S` is the identity matrix over `A`. -/
private lemma map_val_one {k : ℕ} :
    (1 : CStarMatrix (Fin k) (Fin k) S).map Subtype.val = 1 := by
  refine CStarMatrix.ext fun i j => ?_
  change ((if i = j then (1 : S) else 0 : S) : A) = if i = j then 1 else 0
  split_ifs <;> rfl

/-- **Completely positive maps are completely bounded.** A completely positive map `φ : S → B` on
an operator subsystem of a unital C⋆-algebra satisfies `‖X.map φ‖ ≤ ‖φ 1‖ ‖X‖` at every level. -/
theorem _root_.CompletelyPositiveMap'.norm_map_cstarMatrix_le (φ : S →CP' B) {k : ℕ}
    (X : CStarMatrix (Fin k) (Fin k) S) :
    ‖X.map φ‖ ≤ ‖φ 1‖ * ‖X‖ := by
  classical
  -- the matrix level norms of `S` are those of `A`
  have hnorm : ‖X‖ = ‖X.map Subtype.val‖ := rfl
  rcases (norm_nonneg (X.map Subtype.val)).eq_or_lt with hX | hX
  · have : X = 0 := CStarMatrix.ext fun i j => Subtype.val_injective (by
      have := norm_eq_zero.mp hX.symm
      exact congrFun (congrFun this i) j)
    subst this
    rw [show (0 : CStarMatrix (Fin k) (Fin k) S).map φ = 0 from CStarMatrix.ext fun i j => map_zero φ,
      norm_zero]
    exact mul_nonneg (norm_nonneg _) (OperatorSpace.norm_nonneg _)
  -- normalize `X` to norm `1`
  set r := ‖X.map Subtype.val‖
  let Y : CStarMatrix (Fin k) (Fin k) S := (r⁻¹ : ℂ) • X
  have hY : Y.map Subtype.val = (r⁻¹ : ℂ) • X.map Subtype.val := rfl
  have hYn : ‖Y.map Subtype.val‖ ≤ 1 := by
    rw [hY, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hX.le,
      inv_mul_cancel₀ hX.ne']
  -- the block matrix `!![1, Y; Y⋆, 1]` over `S` is positive
  let N : CStarMatrix (Fin 2) (Fin 2) (CStarMatrix (Fin k) (Fin k) S) := ofMatrix !![1, Y; star Y, 1]
  have hNA : N.map (·.map Subtype.val) =
      ofMatrix !![1, Y.map Subtype.val; star (Y.map Subtype.val), 1] := by
    refine CStarMatrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j
    · exact map_val_one
    · rfl
    · rfl
    · exact map_val_one
  have hN : 0 ≤ flatten N := by
    rw [cstarMatrix_nonneg_iff, ← flatten_map, ← flattenStarAlgEquiv_apply, ← map_zero
      (flattenStarAlgEquiv 2 k A), map_le_map_iff, hNA]
    exact nonneg_one_star_one_iff.mpr hYn
  -- its image under `φ` at level `2k` is positive
  have hNφ : 0 ≤ N.map (·.map φ) := by
    have h := φ.map_cstarMatrix_nonneg hN
    rw [← flatten_map, ← flattenStarAlgEquiv_apply] at h
    rwa [← map_zero (flattenStarAlgEquiv 2 k B), map_le_map_iff] at h
  set M := N.map (·.map φ)
  have hM : M = ofMatrix !![M 0 0, M 0 1; star (M 0 1), M 1 1] := by
    have hsa := (IsSelfAdjoint.of_nonneg hNφ).star_eq
    refine CStarMatrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j
    · rfl
    · rfl
    · change M 1 0 = star (M 0 1)
      calc M 1 0 = (star M) 1 0 := by rw [hsa]
        _ = star (M 0 1) := rfl
    · rfl
  rw [hM] at hNφ
  have hsq := norm_sq_le_of_nonneg hNφ
  -- the diagonal blocks are `diag (φ 1)`
  have hP : M 0 0 = diagonalNonUnitalStarAlgHom (φ 1) := by
    refine CStarMatrix.ext fun i j => ?_
    change φ (if i = j then 1 else 0) = if i = j then φ 1 else 0
    split_ifs <;> simp
  have hP' : M 1 1 = M 0 0 := rfl
  have hPn : ‖M 0 0‖ ≤ ‖φ 1‖ := hP ▸ NonUnitalStarAlgHom.norm_apply_le _ _
  have hYφ : ‖M 0 1‖ ≤ ‖φ 1‖ := by
    rw [hP'] at hsq
    nlinarith [norm_nonneg (M 0 1), norm_nonneg (M 0 0), norm_nonneg (φ 1)]
  -- undo the normalization
  have hXY : X.map φ = (r : ℂ) • M 0 1 := by
    refine CStarMatrix.ext fun i j => ?_
    change φ (X i j) = (r : ℂ) • φ ((r⁻¹ : ℂ) • X i j)
    rw [map_smul, smul_smul, ← Complex.ofReal_inv, ← Complex.ofReal_mul, mul_inv_cancel₀ hX.ne',
      Complex.ofReal_one, one_smul]
  rw [hXY, norm_smul, Complex.norm_real, Real.norm_of_nonneg hX.le, mul_comm, hnorm]
  exact mul_le_mul_of_nonneg_right hYφ hX.le

end OperatorSubsystem

namespace CompletelyPositiveMap'

variable {S : OperatorSubsystem A}

/-- A completely positive map on an operator subsystem of a unital C⋆-algebra, as a completely
bounded map. -/
def toCompletelyBoundedMap (φ : S →CP' B) : S →CB B where
  toLinearMap := φ.toLinearMap
  exists_bound' := ⟨‖φ 1‖, fun _ X => CompletelyPositiveMap'.norm_map_cstarMatrix_le φ X⟩

/-- A completely positive map as a completely bounded map is the same function. -/
@[simp] lemma coe_toCompletelyBoundedMap (φ : S →CP' B) : ⇑φ.toCompletelyBoundedMap = φ := rfl

/-- **The cb norm of a completely positive map** on an operator subsystem of a unital C⋆-algebra is
`‖φ 1‖`. -/
theorem norm_toCompletelyBoundedMap (φ : S →CP' B) : ‖φ.toCompletelyBoundedMap‖ = ‖φ 1‖ := by
  refine le_antisymm (CompletelyBoundedMap.norm_le_bound _ (norm_nonneg _)
    fun _ X => CompletelyPositiveMap'.norm_map_cstarMatrix_le φ X) ?_
  have h := φ.toCompletelyBoundedMap.norm_apply_le 1
  have h₁ : ‖(1 : S)‖ ≤ 1 := by
    change ‖(1 : A)‖ ≤ 1
    rcases subsingleton_or_nontrivial A with hA | hA
    · rw [Subsingleton.elim (1 : A) 0, norm_zero]
      exact zero_le_one
    · rw [norm_one]
  exact h.trans (mul_le_of_le_one_right (CompletelyBoundedMap.norm_nonneg' _) h₁)

end CompletelyPositiveMap'

namespace CompletelyPositiveMap

/-- A completely positive map between C⋆-algebras with unital domain, as a completely bounded map:
it is the completely positive map on the operator subsystem `⊤` of `A`. -/
def toCompletelyBoundedMap (ψ : A →CP B) : A →CB B where
  toLinearMap := ψ.toLinearMap
  exists_bound' := ⟨‖ψ 1‖, fun _ X => by
    have h := CompletelyPositiveMap'.norm_map_cstarMatrix_le
      ((CompletelyPositiveMap'.equivCompletelyPositiveMap.symm ψ).restrict ⊤)
      (X.map fun a => (⟨a, OperatorSubsystem.mem_top a⟩ : (⊤ : OperatorSubsystem A)))
    exact h⟩

/-- A completely positive map as a completely bounded map is the same function. -/
@[simp] lemma coe_toCompletelyBoundedMap (ψ : A →CP B) : ⇑ψ.toCompletelyBoundedMap = ψ := rfl

/-- **The cb norm of a completely positive map** with unital domain is `‖ψ 1‖`. -/
theorem norm_toCompletelyBoundedMap (ψ : A →CP B) : ‖ψ.toCompletelyBoundedMap‖ = ‖ψ 1‖ := by
  refine le_antisymm (CompletelyBoundedMap.norm_le_bound _ (norm_nonneg _) fun _ X => ?_) ?_
  · exact CompletelyPositiveMap'.norm_map_cstarMatrix_le
      ((CompletelyPositiveMap'.equivCompletelyPositiveMap.symm ψ).restrict ⊤)
      (X.map fun a => (⟨a, OperatorSubsystem.mem_top a⟩ : (⊤ : OperatorSubsystem A)))
  · have h := ψ.toCompletelyBoundedMap.norm_apply_le 1
    have h₁ : ‖(1 : A)‖ ≤ 1 := by
      rcases subsingleton_or_nontrivial A with hA | hA
      · rw [Subsingleton.elim (1 : A) 0, norm_zero]
        exact zero_le_one
      · rw [norm_one]
    exact h.trans (mul_le_of_le_one_right (CompletelyBoundedMap.norm_nonneg' _) h₁)

end CompletelyPositiveMap

namespace ContinuousLinearMap

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

open scoped InnerProductSpace in
/-- The compression `T ↦ V† T V` of operators on `K` to operators on `H` is completely positive: the
quadratic form `∑ᵢⱼ ⟪ξᵢ, V† Tᵢⱼ V ξⱼ⟫` is `∑ᵢⱼ ⟪V ξᵢ, Tᵢⱼ V ξⱼ⟫`. -/
def compressionCP (V : H →L[ℂ] K) : (K →L[ℂ] K) →CP (H →L[ℂ] H) where
  toLinearMap := (compressionCB V V).toLinearMap
  map_cstarMatrix_nonneg' k M hM := by
    classical
    rw [CStarMatrix.nonneg_iff_sum_inner_apply_nonneg] at hM ⊢
    intro ξ
    simpa [compressionCB_apply, adjoint_inner_right] using hM fun i => V (ξ i)

/-- `compressionCP V` sends `T` to `V† T V`. -/
@[simp] lemma compressionCP_apply (V : H →L[ℂ] K) (T : K →L[ℂ] K) :
    compressionCP V T = adjoint V ∘L T ∘L V :=
  rfl

end ContinuousLinearMap
