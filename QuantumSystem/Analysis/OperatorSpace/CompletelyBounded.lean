/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.OperatorSpace.Basic
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.Stinespring

/-!
# Completely bounded maps

A linear map `φ : V → W` between spaces with matrix norms is **completely bounded** if the maps
`φₖ : X ↦ X.map φ` on `k × k` matrices are bounded uniformly in `k` (`CompletelyBoundedMap`,
`V →CB W`). Its **cb norm** `‖φ‖ = sup_k ‖φₖ‖` is the smallest uniform bound, defined as Mathlib
defines the operator norm, and makes `V →CB W` a normed space when `V` and `W` are operator spaces.

## Main definitions

* `CompletelyBoundedMap V W` — completely bounded maps, written `V →CB W` under
  `open scoped CStarAlgebra`, with the cb norm as their norm.
* `CompletelyBoundedMap.comp`, `CompletelyBoundedMap.id`, `CompletelyBoundedMap.restrict` — composition,
  identity and restriction to a subspace.
* `NonUnitalStarAlgHom.toCompletelyBoundedMap` — ⋆-homomorphisms of C⋆-algebras.
* `ContinuousLinearMap.compressionCB V₁ V₂` — the compression `T ↦ V₁† T V₂` of operators.

## Main results

* `CompletelyBoundedMap.norm_map_cstarMatrix_le` — `‖X.map φ‖ ≤ ‖φ‖ ‖X‖` at every level.
* `CompletelyBoundedMap.norm_comp_le` — the cb norm is submultiplicative.
* `ContinuousLinearMap.norm_compressionCB_le` — `‖T ↦ V₁† T V₂‖_cb ≤ ‖V₁‖ ‖V₂‖`.
-/

@[expose] public noncomputable section

open scoped CStarAlgebra ComplexOrder InnerProductSpace
open CStarMatrix

/-- A linear map `φ : V → W` between complex vector spaces with matrix norms is **completely
bounded** if `‖X.map φ‖ ≤ C ‖X‖` for every square matrix `X` over `V`, with `C` independent of the
size of `X`. -/
structure CompletelyBoundedMap (V : Type*) (W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [∀ k, Norm (CStarMatrix (Fin k) (Fin k) V)]
    [∀ k, Norm (CStarMatrix (Fin k) (Fin k) W)] extends V →ₗ[ℂ] W where
  exists_bound' : ∃ C : ℝ, ∀ (k : ℕ) (X : CStarMatrix (Fin k) (Fin k) V),
    ‖X.map toLinearMap‖ ≤ C * ‖X‖

/-- Notation for a `CompletelyBoundedMap`. -/
scoped[CStarAlgebra] notation:25 V " →CB " W:0 => CompletelyBoundedMap V W

namespace CompletelyBoundedMap

section Basic

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [∀ k, Norm (CStarMatrix (Fin k) (Fin k) V)] [∀ k, Norm (CStarMatrix (Fin k) (Fin k) W)]

instance : FunLike (V →CB W) V W where
  coe φ := φ.toFun
  coe_injective φ ψ h := by
    cases φ
    cases ψ
    congr
    exact DFunLike.coe_injective h

instance : LinearMapClass (V →CB W) ℂ V W where
  map_add φ := map_add φ.toLinearMap
  map_smulₛₗ φ := map_smulₛₗ φ.toLinearMap

/-- The underlying linear map of `φ` is `φ` as a function. -/
@[simp] lemma coe_toLinearMap (φ : V →CB W) : ⇑φ.toLinearMap = φ := rfl

/-- Completely bounded maps are equal if they agree at every point. -/
@[ext] lemma ext {φ ψ : V →CB W} (h : ∀ v, φ v = ψ v) : φ = ψ := DFunLike.ext _ _ h

/-- A completely bounded map is determined by its underlying linear map. -/
lemma toLinearMap_injective : Function.Injective (toLinearMap : (V →CB W) → V →ₗ[ℂ] W) :=
  fun _ _ h => ext fun v => LinearMap.congr_fun h v

end Basic

section OperatorSpace

variable {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [∀ k, Norm (CStarMatrix (Fin k) (Fin k) V)] [OperatorSpace V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [∀ k, Norm (CStarMatrix (Fin k) (Fin k) W)]
  [OperatorSpace W]
  [NormedAddCommGroup U] [NormedSpace ℂ U] [∀ k, Norm (CStarMatrix (Fin k) (Fin k) U)]
  [OperatorSpace U]

omit [OperatorSpace W] in
/-- A completely bounded map has a nonnegative uniform bound. -/
lemma exists_nonneg_bound (φ : V →CB W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (X : CStarMatrix (Fin k) (Fin k) V), ‖X.map φ‖ ≤ C * ‖X‖ := by
  obtain ⟨C, hC⟩ := φ.exists_bound'
  exact ⟨max C 0, le_max_right _ _, fun k X => (hC k X).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (OperatorSpace.norm_nonneg X))⟩

/-- The **cb norm** `‖φ‖ = sup_k ‖φₖ‖`, the smallest uniform bound of the maps `X ↦ X.map φ`. -/
instance : Norm (V →CB W) :=
  ⟨fun φ => sInf {c | 0 ≤ c ∧ ∀ (k : ℕ) (X : CStarMatrix (Fin k) (Fin k) V), ‖X.map φ‖ ≤ c * ‖X‖}⟩

omit [OperatorSpace V] [OperatorSpace W] in
/-- The cb norm is the infimum of the nonnegative uniform bounds. -/
lemma norm_def (φ : V →CB W) :
    ‖φ‖ = sInf {c | 0 ≤ c ∧ ∀ (k : ℕ) (X : CStarMatrix (Fin k) (Fin k) V), ‖X.map φ‖ ≤ c * ‖X‖} :=
  rfl

omit [OperatorSpace W] in
private lemma bounds_nonempty (φ : V →CB W) :
    ∃ c, c ∈ {c | 0 ≤ c ∧ ∀ (k : ℕ) (X : CStarMatrix (Fin k) (Fin k) V), ‖X.map φ‖ ≤ c * ‖X‖} :=
  φ.exists_nonneg_bound

omit [OperatorSpace V] [OperatorSpace W] in
private lemma bounds_bddBelow (φ : V →CB W) :
    BddBelow {c | 0 ≤ c ∧ ∀ (k : ℕ) (X : CStarMatrix (Fin k) (Fin k) V), ‖X.map φ‖ ≤ c * ‖X‖} :=
  ⟨0, fun _ hc => hc.1⟩

omit [OperatorSpace V] [OperatorSpace W] in
/-- The cb norm is nonnegative. -/
lemma norm_nonneg' (φ : V →CB W) : 0 ≤ ‖φ‖ :=
  Real.sInf_nonneg fun _ hc => hc.1

omit [OperatorSpace V] [OperatorSpace W] in
/-- The cb norm is at most any nonnegative uniform bound. -/
lemma norm_le_bound (φ : V →CB W) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ (k : ℕ) (X : CStarMatrix (Fin k) (Fin k) V), ‖X.map φ‖ ≤ C * ‖X‖) : ‖φ‖ ≤ C :=
  csInf_le φ.bounds_bddBelow ⟨hC, h⟩

omit [OperatorSpace W] in
/-- `‖X.map φ‖ ≤ ‖φ‖ ‖X‖` at every level. -/
theorem norm_map_cstarMatrix_le (φ : V →CB W) {k : ℕ} (X : CStarMatrix (Fin k) (Fin k) V) :
    ‖X.map φ‖ ≤ ‖φ‖ * ‖X‖ := by
  rcases (OperatorSpace.norm_nonneg X).eq_or_lt with hX | hX
  · obtain ⟨C, -, hC⟩ := φ.exists_nonneg_bound
    have := hC k X
    rw [← hX, mul_zero] at this ⊢
    exact this
  · rw [← div_le_iff₀ hX]
    exact le_csInf φ.bounds_nonempty fun c hc => (div_le_iff₀ hX).mpr (hc.2 k X)

/-- `‖φ v‖ ≤ ‖φ‖ ‖v‖`: the bound at level `1`. -/
lemma norm_apply_le (φ : V →CB W) (v : V) : ‖φ v‖ ≤ ‖φ‖ * ‖v‖ := by
  have := φ.norm_map_cstarMatrix_le (single₁ v)
  rwa [show (single₁ v).map φ = single₁ (φ v) from rfl, OperatorSpace.norm_single₁,
    OperatorSpace.norm_single₁] at this

/-! #### The normed space of completely bounded maps -/

instance : Zero (V →CB W) :=
  ⟨⟨0, 0, fun k X => by
    rw [show X.map (0 : V →ₗ[ℂ] W) = 0 from rfl, OperatorSpace.norm_zero, zero_mul]⟩⟩

instance : Add (V →CB W) :=
  ⟨fun φ ψ => ⟨φ.toLinearMap + ψ.toLinearMap, by
    obtain ⟨C, hC, h⟩ := φ.exists_nonneg_bound
    obtain ⟨D, hD, h'⟩ := ψ.exists_nonneg_bound
    refine ⟨C + D, fun k X => ?_⟩
    rw [show X.map (φ.toLinearMap + ψ.toLinearMap) = X.map φ + X.map ψ from rfl, add_mul]
    exact (OperatorSpace.norm_add_le _ _).trans (add_le_add (h k X) (h' k X))⟩⟩

instance : SMul ℂ (V →CB W) :=
  ⟨fun c φ => ⟨c • φ.toLinearMap, by
    obtain ⟨C, hC, h⟩ := φ.exists_nonneg_bound
    refine ⟨‖c‖ * C, fun k X => ?_⟩
    rw [show X.map (c • φ.toLinearMap) = c • X.map φ from rfl, OperatorSpace.norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h k X) (_root_.norm_nonneg c)⟩⟩

instance : Neg (V →CB W) := ⟨fun φ => (-1 : ℂ) • φ⟩

instance : Sub (V →CB W) := ⟨fun φ ψ => φ + -ψ⟩

instance : SMul ℕ (V →CB W) := ⟨fun n φ => (n : ℂ) • φ⟩

instance : SMul ℤ (V →CB W) := ⟨fun n φ => (n : ℂ) • φ⟩

omit [OperatorSpace V] in
/-- The zero map as a function. -/
@[simp] lemma coe_zero : ⇑(0 : V →CB W) = 0 := rfl

/-- The sum of completely bounded maps as a function. -/
@[simp] lemma coe_add (φ ψ : V →CB W) : ⇑(φ + ψ) = φ + ψ := rfl

/-- A scalar multiple of a completely bounded map as a function. -/
@[simp] lemma coe_smul (c : ℂ) (φ : V →CB W) : ⇑(c • φ) = c • ⇑φ := rfl

instance : AddCommGroup (V →CB W) :=
  toLinearMap_injective.addCommGroup _ rfl (fun _ _ => rfl)
    (fun φ => neg_one_smul ℂ φ.toLinearMap)
    (fun φ ψ => by
      change φ.toLinearMap + (-1 : ℂ) • ψ.toLinearMap = φ.toLinearMap - ψ.toLinearMap
      rw [neg_one_smul, sub_eq_add_neg])
    (fun φ n => Nat.cast_smul_eq_nsmul ℂ n φ.toLinearMap)
    (fun φ n => Int.cast_smul_eq_zsmul ℂ n φ.toLinearMap)

instance : Module ℂ (V →CB W) :=
  toLinearMap_injective.module ℂ ⟨⟨toLinearMap, rfl⟩, fun _ _ => rfl⟩ fun _ _ => rfl

/-- The cb norm as a `NormedSpace.Core`. -/
lemma normedSpaceCore : NormedSpace.Core ℂ (V →CB W) where
  norm_nonneg := norm_nonneg'
  norm_smul c φ := by
    refine le_antisymm (norm_le_bound _ (mul_nonneg (_root_.norm_nonneg c) φ.norm_nonneg')
      fun k X => ?_) ?_
    · rw [show X.map (c • φ) = c • X.map φ from rfl, OperatorSpace.norm_smul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (φ.norm_map_cstarMatrix_le X) (_root_.norm_nonneg c)
    · rcases eq_or_ne c 0 with rfl | hc
      · rw [_root_.norm_zero, zero_mul]
        exact norm_nonneg' _
      · have h : ‖φ‖ ≤ ‖c⁻¹‖ * ‖c • φ‖ := norm_le_bound _
          (mul_nonneg (_root_.norm_nonneg _) (norm_nonneg' _)) fun k X => by
            have := (c • φ).norm_map_cstarMatrix_le X
            rw [show X.map φ = c⁻¹ • X.map (c • φ) by
              rw [show X.map (c • φ) = c • X.map φ from rfl, smul_smul, inv_mul_cancel₀ hc,
                one_smul], OperatorSpace.norm_smul, mul_assoc]
            exact mul_le_mul_of_nonneg_left this (_root_.norm_nonneg _)
        rw [norm_inv] at h
        rwa [← div_eq_inv_mul, le_div_iff₀' (norm_pos_iff.mpr hc)] at h
  norm_triangle φ ψ := norm_le_bound _ (add_nonneg φ.norm_nonneg' ψ.norm_nonneg') fun k X => by
    rw [show X.map (φ + ψ) = X.map φ + X.map ψ from rfl, add_mul]
    exact (OperatorSpace.norm_add_le _ _).trans
      (add_le_add (φ.norm_map_cstarMatrix_le X) (ψ.norm_map_cstarMatrix_le X))
  norm_eq_zero_iff φ := by
    constructor
    · intro h
      ext v
      have := φ.norm_apply_le v
      rw [h, zero_mul] at this
      simpa using norm_le_zero_iff.mp this
    · rintro rfl
      exact le_antisymm (norm_le_bound _ le_rfl fun k X => by
        rw [show X.map (0 : V →CB W) = 0 from rfl, OperatorSpace.norm_zero, zero_mul])
        (norm_nonneg' _)

/-- The cb norm vanishes exactly at `0`. -/
lemma norm_eq_zero_iff' (φ : V →CB W) : ‖φ‖ = 0 ↔ φ = 0 :=
  normedSpaceCore.norm_eq_zero_iff φ

/-- The cb norm of `0` is `0`. -/
lemma norm_zero' : ‖(0 : V →CB W)‖ = 0 :=
  (norm_eq_zero_iff' 0).mpr rfl

/-- The cb norm is homogeneous. -/
lemma norm_smul' (c : ℂ) (φ : V →CB W) : ‖c • φ‖ = ‖c‖ * ‖φ‖ :=
  normedSpaceCore.norm_smul c φ

/-- The cb norm of a nonzero map is positive. -/
lemma norm_pos' {φ : V →CB W} (hφ : φ ≠ 0) : 0 < ‖φ‖ :=
  lt_of_le_of_ne φ.norm_nonneg' fun h => hφ ((norm_eq_zero_iff' φ).mp h.symm)

instance : NormedAddCommGroup (V →CB W) := .ofCore normedSpaceCore

instance : NormedSpace ℂ (V →CB W) := .ofCore normedSpaceCore

/-! #### Composition and restriction -/

/-- The composition of completely bounded maps is completely bounded. -/
def comp (ψ : W →CB U) (φ : V →CB W) : V →CB U where
  toLinearMap := ψ.toLinearMap ∘ₗ φ.toLinearMap
  exists_bound' := by
    obtain ⟨C, hC, h⟩ := ψ.exists_nonneg_bound
    obtain ⟨D, hD, h'⟩ := φ.exists_nonneg_bound
    exact ⟨C * D, fun k X => ((h k (X.map φ)).trans (mul_le_mul_of_nonneg_left (h' k X) hC)).trans_eq
      (mul_assoc _ _ _).symm⟩

omit [OperatorSpace U] in
/-- The composition `ψ.comp φ` sends `v` to `ψ (φ v)`. -/
@[simp] lemma comp_apply (ψ : W →CB U) (φ : V →CB W) (v : V) : ψ.comp φ v = ψ (φ v) := rfl

omit [OperatorSpace U] in
/-- The cb norm is submultiplicative. -/
theorem norm_comp_le (ψ : W →CB U) (φ : V →CB W) : ‖ψ.comp φ‖ ≤ ‖ψ‖ * ‖φ‖ :=
  norm_le_bound _ (mul_nonneg ψ.norm_nonneg' φ.norm_nonneg') fun _ X =>
    ((ψ.norm_map_cstarMatrix_le (X.map φ)).trans
      (mul_le_mul_of_nonneg_left (φ.norm_map_cstarMatrix_le X) ψ.norm_nonneg')).trans_eq
      (mul_assoc _ _ _).symm

variable (V) in
/-- The identity map is completely bounded. -/
protected def id : V →CB V where
  toLinearMap := LinearMap.id
  exists_bound' := ⟨1, fun k X => by rw [one_mul]; exact le_rfl⟩

omit [OperatorSpace V] in
/-- The identity completely bounded map is the identity function. -/
@[simp] lemma coe_id : ⇑(CompletelyBoundedMap.id V) = id := rfl

omit [OperatorSpace V] in
/-- The identity map has cb norm at most `1`. -/
lemma norm_id_le : ‖CompletelyBoundedMap.id V‖ ≤ 1 :=
  norm_le_bound _ zero_le_one fun k X => by rw [one_mul]; exact le_rfl

end OperatorSpace

end CompletelyBoundedMap

namespace Submodule

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [∀ k, Norm (CStarMatrix (Fin k) (Fin k) V)] [OperatorSpace V] (E : Submodule ℂ V)

/-- The inclusion of a subspace is completely bounded, with cb norm at most `1`: the matrix norms of
`E` are those of `V`. -/
def subtypeCB : E →CB V where
  toLinearMap := E.subtype
  exists_bound' := ⟨1, fun k X => by rw [one_mul]; exact le_rfl⟩

omit [OperatorSpace V] in
/-- The inclusion of a subspace is `Subtype.val`. -/
@[simp] lemma coe_subtypeCB : ⇑E.subtypeCB = Subtype.val := rfl

omit [OperatorSpace V] in
/-- The inclusion of a subspace has cb norm at most `1`. -/
lemma norm_subtypeCB_le : ‖E.subtypeCB‖ ≤ 1 :=
  CompletelyBoundedMap.norm_le_bound _ zero_le_one fun k X => by rw [one_mul]; exact le_rfl

end Submodule

namespace CompletelyBoundedMap

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [∀ k, Norm (CStarMatrix (Fin k) (Fin k) V)] [OperatorSpace V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [∀ k, Norm (CStarMatrix (Fin k) (Fin k) W)]
  [OperatorSpace W]

/-- The restriction of a completely bounded map to a subspace. -/
def restrict (φ : V →CB W) (E : Submodule ℂ V) : E →CB W := φ.comp E.subtypeCB

omit [OperatorSpace W] in
/-- The restriction of `φ` to `E` sends `v` to `φ v`. -/
@[simp] lemma restrict_apply (φ : V →CB W) (E : Submodule ℂ V) (v : E) : φ.restrict E v = φ v :=
  rfl

omit [OperatorSpace W] in
/-- Restricting does not increase the cb norm. -/
lemma norm_restrict_le (φ : V →CB W) (E : Submodule ℂ V) : ‖φ.restrict E‖ ≤ ‖φ‖ :=
  (norm_comp_le _ _).trans ((mul_le_mul_of_nonneg_left E.norm_subtypeCB_le φ.norm_nonneg').trans_eq
    (mul_one _))

end CompletelyBoundedMap

/-! ### ⋆-homomorphisms and compressions -/

namespace NonUnitalStarAlgHom

variable {A B : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- A ⋆-homomorphism of C⋆-algebras is completely bounded, with cb norm at most `1`: at every level it
is a ⋆-homomorphism of C⋆-algebras of matrices, hence contractive. -/
def toCompletelyBoundedMap (π : A →⋆ₙₐ[ℂ] B) : A →CB B where
  toLinearMap := { toFun := π, map_add' := map_add π, map_smul' := map_smul π }
  exists_bound' := ⟨1, fun k X => by
    rw [one_mul]
    exact NonUnitalStarAlgHom.norm_apply_le (mapₙₐ π) X⟩

/-- A ⋆-homomorphism as a completely bounded map is the same function. -/
@[simp] lemma coe_toCompletelyBoundedMap (π : A →⋆ₙₐ[ℂ] B) : ⇑π.toCompletelyBoundedMap = π := rfl

/-- A ⋆-homomorphism has cb norm at most `1`. -/
lemma norm_toCompletelyBoundedMap_le (π : A →⋆ₙₐ[ℂ] B) : ‖π.toCompletelyBoundedMap‖ ≤ 1 :=
  CompletelyBoundedMap.norm_le_bound _ zero_le_one fun k X => by
    rw [one_mul]
    exact NonUnitalStarAlgHom.norm_apply_le (mapₙₐ π) X

end NonUnitalStarAlgHom

namespace ContinuousLinearMap

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] [CompleteSpace K] in
/-- Applying `V` to every component of a vector of `Hᵏ` multiplies its norm by at most `‖V‖`. -/
lemma norm_toLp_map_le {k : ℕ} (V : H →L[ℂ] K) (x : PiLp 2 (fun _ : Fin k => H)) :
    ‖(WithLp.toLp 2 (fun i => V (x.ofLp i)) : PiLp 2 (fun _ : Fin k => K))‖ ≤ ‖V‖ * ‖x‖ := by
  rw [← sq_le_sq₀ (_root_.norm_nonneg _) (by positivity), mul_pow, PiLp.norm_sq_eq_of_L2,
    PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (_root_.norm_nonneg _) (V.le_opNorm _) 2

/-- The compression `T ↦ V₁† T V₂` applied entrywise multiplies the norm of a matrix of operators by
at most `‖V₁‖ ‖V₂‖`. As operators on `Hᵏ` and `Kᵏ`, `⟪A ξ, A ξ⟫ = ⟪η, B ζ⟫` for the entrywise images
`η = V₁ (A ξ)` and `ζ = V₂ ξ`, and applying `V` entrywise multiplies norms by at most `‖V‖`. -/
lemma norm_map_compression_le (V₁ V₂ : H →L[ℂ] K) {k : ℕ}
    (X : CStarMatrix (Fin k) (Fin k) (K →L[ℂ] K)) :
    ‖X.map fun T => adjoint V₁ ∘L T ∘L V₂‖ ≤ ‖V₁‖ * ‖V₂‖ * ‖X‖ := by
  rw [← NonUnitalStarAlgHom.norm_map (toPiLpStarAlgEquiv (Fin k) H)
      (toPiLpStarAlgEquiv (Fin k) H).injective,
    ← NonUnitalStarAlgHom.norm_map (toPiLpStarAlgEquiv (Fin k) K)
      (toPiLpStarAlgEquiv (Fin k) K).injective]
  set B := toPiLpStarAlgEquiv (Fin k) K X
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun ξ => ?_
  set Aξ := toPiLpStarAlgEquiv (Fin k) H (X.map fun T => adjoint V₁ ∘L T ∘L V₂) ξ
  let η : PiLp 2 (fun _ : Fin k => K) := WithLp.toLp 2 fun i => V₁ (Aξ.ofLp i)
  let ζ : PiLp 2 (fun _ : Fin k => K) := WithLp.toLp 2 fun j => V₂ (ξ.ofLp j)
  have hinner : ⟪Aξ, Aξ⟫_ℂ = ⟪η, B ζ⟫_ℂ := by
    simp only [PiLp.inner_apply, Aξ, η, ζ, B, toPiLpStarAlgEquiv_apply, inner_sum,
      CStarMatrix.map_apply, ContinuousLinearMap.comp_apply, adjoint_inner_right]
  have h₁ : ‖Aξ‖ ^ 2 ≤ ‖η‖ * (‖B‖ * ‖ζ‖) := by
    rw [← @inner_self_eq_norm_sq ℂ, hinner]
    exact (RCLike.re_le_norm _).trans ((norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (B.le_opNorm ζ) (_root_.norm_nonneg _)))
  have h₂ : ‖Aξ‖ ^ 2 ≤ ‖V₁‖ * ‖Aξ‖ * (‖B‖ * (‖V₂‖ * ‖ξ‖)) :=
    h₁.trans (mul_le_mul (norm_toLp_map_le V₁ _) (mul_le_mul_of_nonneg_left
      (norm_toLp_map_le V₂ ξ) (_root_.norm_nonneg _)) (by positivity) (by positivity))
  change ‖Aξ‖ ≤ ‖V₁‖ * ‖V₂‖ * ‖B‖ * ‖ξ‖
  rcases (_root_.norm_nonneg Aξ).eq_or_lt with h | h
  · rw [← h]
    positivity
  · have h₃ : ‖Aξ‖ * ‖Aξ‖ ≤ ‖Aξ‖ * (‖V₁‖ * ‖V₂‖ * ‖B‖ * ‖ξ‖) := by
      rw [← sq]
      exact h₂.trans_eq (by ring)
    exact le_of_mul_le_mul_left h₃ h

/-- The compression `T ↦ V₁† T V₂` of operators on `K` to operators on `H`. -/
def compressionCB (V₁ V₂ : H →L[ℂ] K) : (K →L[ℂ] K) →CB (H →L[ℂ] H) where
  toLinearMap :=
    { toFun := fun T => adjoint V₁ ∘L T ∘L V₂
      map_add' := fun T T' => by ext; simp
      map_smul' := fun c T => by ext; simp }
  exists_bound' := ⟨‖V₁‖ * ‖V₂‖, fun _ X => norm_map_compression_le V₁ V₂ X⟩

/-- `compressionCB V₁ V₂` sends `T` to `V₁† T V₂`. -/
@[simp] lemma compressionCB_apply (V₁ V₂ : H →L[ℂ] K) (T : K →L[ℂ] K) :
    compressionCB V₁ V₂ T = adjoint V₁ ∘L T ∘L V₂ :=
  rfl

/-- The compression `T ↦ V₁† T V₂` has cb norm at most `‖V₁‖ ‖V₂‖`. -/
theorem norm_compressionCB_le (V₁ V₂ : H →L[ℂ] K) : ‖compressionCB V₁ V₂‖ ≤ ‖V₁‖ * ‖V₂‖ :=
  CompletelyBoundedMap.norm_le_bound _ (by positivity) fun _ X => norm_map_compression_le V₁ V₂ X

end ContinuousLinearMap
