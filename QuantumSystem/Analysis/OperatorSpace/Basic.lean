/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.CStarMatrix
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.KPositiveMap
public import QuantumSystem.ForMathlib.Analysis.OperatorSystem.Basic

/-!
# Operator spaces

An **operator space** is a complex normed space `V` with a norm on each matrix space
`CStarMatrix (Fin k) (Fin k) V` satisfying Ruan's axioms (`OperatorSpace`): every level satisfies
the triangle inequality, `‖α X β‖ ≤ ‖α‖ ‖X‖ ‖β‖` for square scalar matrices `α`, `β` of the size of
`X`, the block diagonal matrix `X ⊕ Y` has norm `max ‖X‖ ‖Y‖`, and the norm at level `1` is the
norm of `V`.

As for matrix-ordered spaces (`MatrixOrdered`), the matrix norms are instance arguments rather than
data of the class, so that a C⋆-algebra uses the norm Mathlib puts on `CStarMatrix (Fin k) (Fin k) A`:
every C⋆-algebra is an operator space (`CStarAlgebra.instOperatorSpace`), and so is every subspace of
an operator space, with the restricted matrix norms (`Submodule.instOperatorSpace`,
`OperatorSubsystem.instOperatorSpace`).

That the level norms are nonnegative, vanish at `0` and are homogeneous follows from the axioms
(`OperatorSpace.norm_nonneg`, `OperatorSpace.norm_smul`).

## Main definitions

* `OperatorSpace V` — complex normed spaces with matrix norms satisfying Ruan's axioms.

## Main results

* `CStarAlgebra.instOperatorSpace` — C⋆-algebras are operator spaces.
* `Submodule.instOperatorSpace`, `OperatorSubsystem.instOperatorSpace` — so are their subspaces.
-/

@[expose] public section

open scoped CStarAlgebra ComplexOrder
open CStarMatrix

/-- An **operator space**: a complex normed space `V` with norms on the matrix spaces
`CStarMatrix (Fin k) (Fin k) V`, supplied as instances, satisfying Ruan's axioms: the triangle
inequality at every level, `‖α X β‖ ≤ ‖α‖ ‖X‖ ‖β‖` for square scalar matrices `α`, `β` of the size
of `X`,
`‖X ⊕ Y‖ = max ‖X‖ ‖Y‖`, and `‖v‖` as the norm at level `1`. -/
class OperatorSpace (V : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V]
    [∀ k, Norm (CStarMatrix (Fin k) (Fin k) V)] : Prop where
  /-- The triangle inequality at each level. -/
  norm_add_le {k : ℕ} (X Y : CStarMatrix (Fin k) (Fin k) V) : ‖X + Y‖ ≤ ‖X‖ + ‖Y‖
  /-- Multiplication by scalar matrices on both sides is bounded by their norms. -/
  norm_scalarMul_le {k : ℕ} (α β : CStarMatrix (Fin k) (Fin k) ℂ) (X : CStarMatrix (Fin k) (Fin k) V) :
    ‖scalarMul (ofMatrix.symm α) (ofMatrix.symm β) X‖ ≤ ‖α‖ * ‖X‖ * ‖β‖
  /-- A block diagonal matrix has the larger norm of its blocks. -/
  norm_directSum {k l : ℕ} (X : CStarMatrix (Fin k) (Fin k) V) (Y : CStarMatrix (Fin l) (Fin l) V) :
    ‖directSum X Y‖ = max ‖X‖ ‖Y‖
  /-- The norm at level `1` is the norm of `V`. -/
  norm_single₁ (v : V) : ‖single₁ v‖ = ‖v‖

namespace OperatorSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [∀ k, Norm (CStarMatrix (Fin k) (Fin k) V)] [OperatorSpace V]

omit [∀ k, Norm (CStarMatrix (Fin k) (Fin k) V)] [OperatorSpace V] in
/-- `scalarMul (c • 1) 1 X = c • X`. -/
lemma scalarMul_smul_one_one {k : ℕ} (c : ℂ) (X : CStarMatrix (Fin k) (Fin k) V) :
    scalarMul (ofMatrix.symm (c • 1 : CStarMatrix (Fin k) (Fin k) ℂ))
      (ofMatrix.symm (1 : CStarMatrix (Fin k) (Fin k) ℂ)) X = c • X := by
  classical
  ext i j
  simp [scalarMul_apply, CStarMatrix.one_apply, mul_ite, ite_smul]

omit [∀ k, Norm (CStarMatrix (Fin k) (Fin k) V)] [OperatorSpace V] in
/-- The identity scalar matrix has norm at most `1` (it is `0` at level `0`). -/
private lemma norm_one_le {k : ℕ} : ‖(1 : CStarMatrix (Fin k) (Fin k) ℂ)‖ ≤ 1 := by
  rcases isEmpty_or_nonempty (Fin k) with hk | hk
  · rw [show (1 : CStarMatrix (Fin k) (Fin k) ℂ) = 0 from ext fun i => isEmptyElim i,
      _root_.norm_zero]
    exact zero_le_one
  · exact CStarRing.norm_one.le

/-- The norm of a scalar multiple `c • X` at level `k` is at most `‖c‖ ‖1‖² ‖X‖`. -/
private lemma norm_smul_le_aux {k : ℕ} (c : ℂ) (X : CStarMatrix (Fin k) (Fin k) V) :
    ‖c • X‖ ≤ ‖c‖ * ‖(1 : CStarMatrix (Fin k) (Fin k) ℂ)‖ * ‖X‖ *
      ‖(1 : CStarMatrix (Fin k) (Fin k) ℂ)‖ := by
  have := norm_scalarMul_le (c • 1 : CStarMatrix (Fin k) (Fin k) ℂ) 1 X
  rwa [scalarMul_smul_one_one, _root_.norm_smul c (1 : CStarMatrix (Fin k) (Fin k) ℂ)] at this

/-- The zero matrix has norm `0`. -/
@[simp]
lemma norm_zero {k : ℕ} : ‖(0 : CStarMatrix (Fin k) (Fin k) V)‖ = 0 := by
  have h₁ := norm_smul_le_aux (0 : ℂ) (0 : CStarMatrix (Fin k) (Fin k) V)
  rw [zero_smul, _root_.norm_zero, zero_mul, zero_mul, zero_mul] at h₁
  have h₂ := norm_add_le (0 : CStarMatrix (Fin k) (Fin k) V) 0
  rw [add_zero] at h₂
  linarith

/-- The level norms are nonnegative. -/
lemma norm_nonneg {k : ℕ} (X : CStarMatrix (Fin k) (Fin k) V) : 0 ≤ ‖X‖ := by
  have h₁ := norm_add_le X (-X)
  rw [add_neg_cancel, norm_zero] at h₁
  have h₂ := norm_smul_le_aux (-1 : ℂ) X
  rw [neg_one_smul, _root_.norm_neg, norm_one, one_mul] at h₂
  have h₃ := norm_one_le (k := k)
  have h₀ := _root_.norm_nonneg (1 : CStarMatrix (Fin k) (Fin k) ℂ)
  by_contra hX
  rw [not_le] at hX
  have h₄ : ‖(1 : CStarMatrix (Fin k) (Fin k) ℂ)‖ * ‖X‖ * ‖(1 : CStarMatrix (Fin k) (Fin k) ℂ)‖ ≤ 0 := by
    rw [mul_right_comm]
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg h₀ h₀) hX.le
  linarith

/-- The level norms are homogeneous. -/
lemma norm_smul {k : ℕ} (c : ℂ) (X : CStarMatrix (Fin k) (Fin k) V) : ‖c • X‖ = ‖c‖ * ‖X‖ := by
  have h₁ : ∀ (c : ℂ) (X : CStarMatrix (Fin k) (Fin k) V), ‖c • X‖ ≤ ‖c‖ * ‖X‖ := fun c X => by
    have h := norm_smul_le_aux c X
    have h₃ := norm_one_le (k := k)
    have h₀ := _root_.norm_nonneg (1 : CStarMatrix (Fin k) (Fin k) ℂ)
    have hc := _root_.norm_nonneg c
    have hX := norm_nonneg X
    calc ‖c • X‖ ≤ ‖c‖ * ‖(1 : CStarMatrix (Fin k) (Fin k) ℂ)‖ * ‖X‖ *
          ‖(1 : CStarMatrix (Fin k) (Fin k) ℂ)‖ := h
      _ ≤ ‖c‖ * 1 * ‖X‖ * 1 := by gcongr
      _ = ‖c‖ * ‖X‖ := by ring
  refine le_antisymm (h₁ c X) ?_
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · have := h₁ c⁻¹ (c • X)
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul, norm_inv] at this
    rwa [← div_eq_inv_mul, le_div_iff₀' (norm_pos_iff.mpr hc)] at this

end OperatorSpace

/-! ### C⋆-algebras as operator spaces -/

namespace CStarMatrix

variable {C : Type*} [CStarAlgebra C] {k : ℕ}

/-- Over a unital C⋆-algebra, `α X β` is the product `ofScalar α * X * ofScalar β`. -/
lemma scalarMul_eq_ofScalar_mul_mul (α β : CStarMatrix (Fin k) (Fin k) ℂ)
    (X : CStarMatrix (Fin k) (Fin k) C) :
    scalarMul (ofMatrix.symm α) (ofMatrix.symm β) X = ofScalar C k α * X * ofScalar C k β := by
  ext i j
  simp only [scalarMul_apply, CStarMatrix.mul_apply, Finset.sum_mul, ofScalar_apply]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
    mul_smul_comm, mul_one, smul_smul, mul_comm (β q j)]
  rfl

end CStarMatrix

namespace CStarAlgebra

/-- Over a unital C⋆-algebra, `α X β` is the product of `X` with the images of `α` and `β` under the
⋆-homomorphism of scalar matrices, which is contractive. -/
private lemma norm_scalarMul_le_of_unital {C : Type*} [CStarAlgebra C] [PartialOrder C]
    [StarOrderedRing C] {k : ℕ} (α β : CStarMatrix (Fin k) (Fin k) ℂ)
    (X : CStarMatrix (Fin k) (Fin k) C) :
    ‖scalarMul (ofMatrix.symm α) (ofMatrix.symm β) X‖ ≤ ‖α‖ * ‖X‖ * ‖β‖ := by
  rw [scalarMul_eq_ofScalar_mul_mul]
  calc ‖ofScalar C k α * X * ofScalar C k β‖ ≤ ‖ofScalar C k α‖ * ‖X‖ * ‖ofScalar C k β‖ := by
        refine (norm_mul_le _ _).trans ?_
        gcongr
        exact norm_mul_le _ _
    _ ≤ ‖α‖ * ‖X‖ * ‖β‖ := by
        gcongr
        · exact NonUnitalStarAlgHom.norm_apply_le _ α
        · exact NonUnitalStarAlgHom.norm_apply_le _ β

/-- A (possibly non-unital) C⋆-algebra, with the norms Mathlib puts on `CStarMatrix (Fin k) (Fin k) A`,
is an operator space. The scalar bound passes to the unitization, which is isometrically embedded
at every matrix level. -/
instance instOperatorSpace {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] : OperatorSpace A where
  norm_add_le X Y := _root_.norm_add_le X Y
  norm_scalarMul_le {k} α β X := by
    let ι := Unitization.inrNonUnitalStarAlgHom ℂ A
    have hinj : Function.Injective (mapₙₐ (n := Fin k) ι) := fun M N h =>
      ext fun i j => Unitization.inr_injective (congrFun (congrFun h i) j)
    have hX := NonUnitalStarAlgHom.norm_map (mapₙₐ (n := Fin k) ι) hinj X
    rw [← NonUnitalStarAlgHom.norm_map (mapₙₐ (n := Fin k) ι) hinj, ← hX]
    have : mapₙₐ ι (scalarMul (ofMatrix.symm α) (ofMatrix.symm β) X) =
        scalarMul (ofMatrix.symm α) (ofMatrix.symm β) (mapₙₐ ι X) :=
      scalarMul_map _ _ X (ι : A →ₗ[ℂ] Unitization ℂ A)
    rw [this]
    exact norm_scalarMul_le_of_unital α β _
  norm_directSum X Y := CStarMatrix.norm_directSum X Y
  norm_single₁ a := by
    have hinj : Function.Injective (singleNonUnitalStarAlgHom (A := A) (0 : Fin 1)) := fun a b h =>
      by simpa [singleNonUnitalStarAlgHom] using congrFun (congrFun h 0) 0
    rw [show single₁ a = singleNonUnitalStarAlgHom (0 : Fin 1) a from ext fun i j => by
      rw [Subsingleton.elim i 0, Subsingleton.elim j 0]; simp [singleNonUnitalStarAlgHom]]
    exact NonUnitalStarAlgHom.norm_map _ hinj a

end CStarAlgebra

/-! ### Subspaces of operator spaces -/

namespace Submodule

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [∀ k, Norm (CStarMatrix (Fin k) (Fin k) V)] (E : Submodule ℂ V)

/-- The matrix norms of a subspace are those of the ambient space. -/
instance instNormCStarMatrix (k : ℕ) : Norm (CStarMatrix (Fin k) (Fin k) E) :=
  ⟨fun X => ‖X.map Subtype.val‖⟩

variable {E}

/-- The norm of a matrix over a subspace is that of its entrywise inclusion. -/
lemma norm_cstarMatrix_def {k : ℕ} (X : CStarMatrix (Fin k) (Fin k) E) : ‖X‖ = ‖X.map Subtype.val‖ :=
  rfl

/-- A subspace of an operator space is an operator space with the restricted matrix norms: every
axiom transfers along the entrywise inclusion. -/
instance instOperatorSpace [OperatorSpace V] : OperatorSpace E where
  norm_add_le X Y := OperatorSpace.norm_add_le (X.map Subtype.val) (Y.map Subtype.val)
  norm_scalarMul_le α β X := by
    rw [norm_cstarMatrix_def, norm_cstarMatrix_def,
      show (scalarMul (ofMatrix.symm α) (ofMatrix.symm β) X).map Subtype.val =
        scalarMul (ofMatrix.symm α) (ofMatrix.symm β) (X.map Subtype.val) from
          scalarMul_map _ _ X E.subtype]
    exact OperatorSpace.norm_scalarMul_le α β _
  norm_directSum X Y := by
    rw [norm_cstarMatrix_def, norm_cstarMatrix_def, norm_cstarMatrix_def,
      ← OperatorSpace.norm_directSum]
    congr 1
    ext i j
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨t, rfl⟩ := finSumFinEquiv.surjective j
    cases s <;> cases t <;> simp [directSum, ofMatrix_apply]
  norm_single₁ v := OperatorSpace.norm_single₁ (v : V)

end Submodule

namespace OperatorSubsystem

variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℂ T] [StarAddMonoid T] [One T]
  [∀ k, Norm (CStarMatrix (Fin k) (Fin k) T)] (S : OperatorSubsystem T)

/-- The matrix norms of an operator subsystem are those of its underlying subspace. -/
instance instNormCStarMatrix (k : ℕ) : Norm (CStarMatrix (Fin k) (Fin k) S) :=
  inferInstanceAs (Norm (CStarMatrix (Fin k) (Fin k) S.toSubmodule))

/-- An operator subsystem of an operator space is an operator space, as its underlying subspace. -/
instance instOperatorSpace [OperatorSpace T] : OperatorSpace S :=
  inferInstanceAs (OperatorSpace S.toSubmodule)

end OperatorSubsystem
