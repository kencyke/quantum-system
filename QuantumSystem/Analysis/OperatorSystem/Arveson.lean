/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.Stinespring
public import QuantumSystem.ForMathlib.Analysis.Convex.Cone.Extension
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.Orthonormal
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.WeakOperatorTopology
public import QuantumSystem.ForMathlib.Analysis.OperatorSystem.Basic

/-!
# Arveson's extension theorem

A completely positive map `φ : S → B(H)` on an operator subsystem `S` of an operator system `T`
extends to a completely positive map `T → B(H)` (`OperatorSubsystem.exists_extension_completelyPositiveMap`);
for `T` a unital C⋆-algebra the extension is one of Mathlib's completely positive maps
(`CompletelyPositiveMap.exists_extension_of_operatorSubsystem`).

The proof first compresses to finite-dimensional subspaces of `H`. For orthonormal vectors
`e₁, …, eₙ`, completely positive maps into `B(H)` compressed to their span correspond to positive
functionals on `n × n` matrices: `φ` gives `X ↦ ∑ᵢⱼ ⟪eᵢ, φ(Xᵢⱼ) eⱼ⟫` on the matrices over `S`, and a
positive functional `F` on the matrices over `T` gives `a ↦ ∑ᵢⱼ F(Eᵢⱼ a) |eᵢ⟩⟨eⱼ|`, completely
positive because the scalar conjugations `X ↦ β⋆ X β` preserve positivity. The identity matrix is an
order unit of the matrices over `T` and lies in the matrices over `S`, so the functional of `φ`
extends positively (`exists_extension_nonneg_of_orderUnit`), which is the finite step
(`OperatorSubsystem.exists_completelyPositiveMap_of_orthonormal`).

The finite steps along the finite subsets of `H` form a net of completely positive maps whose values
at each `a ∈ T` are bounded uniformly, by a multiple of `‖φ 1‖` read off the order unit
(`OperatorSystem.norm_apply_le_orderBound`). Balls of operators are compact in the weak operator
topology (`ContinuousLinearMapWOT.isCompact_closedBall`), so the net has a cluster point in the
product of these balls; linearity, complete positivity and agreement with `φ` are closed conditions
on the matrix coefficients `⟪x, ψ(a) y⟫`, which the net eventually satisfies.

## Main definitions

* `OperatorSubsystem.vectorFunctional φ e` — the positive functional `X ↦ ∑ᵢⱼ ⟪eᵢ, φ(Xᵢⱼ) eⱼ⟫` on the
  matrices over `S`.
* `OperatorSystem.completelyPositiveMapOfFunctional F hF e` — the completely positive map
  `a ↦ ∑ᵢⱼ F(Eᵢⱼ a) |eᵢ⟩⟨eⱼ|` of a positive functional `F` on the matrices over `T`.

## Main results

* `OperatorSubsystem.exists_completelyPositiveMap_of_orthonormal` — the finite step.
* `OperatorSubsystem.exists_extension_completelyPositiveMap` — **Arveson's extension theorem** for
  operator systems.
* `CompletelyPositiveMap.exists_extension_of_operatorSubsystem` — its form for a unital C⋆-algebra.
-/

@[expose] public noncomputable section

open scoped CStarAlgebra InnerProductSpace ComplexOrder ComplexStarModule
open CStarMatrix Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable [CompleteSpace H]

namespace OperatorSubsystem

variable {T : Type*} [AddCommGroup T] [Module ℂ T] [StarAddMonoid T] [One T]

variable (S : OperatorSubsystem T)

/-- The `n × n` matrices over `T` with entries in the operator subsystem `S`. -/
def matrixSubmodule (n : ℕ) : Submodule ℂ (CStarMatrix (Fin n) (Fin n) T) where
  carrier := {X | ∀ i j, X i j ∈ S}
  add_mem' hX hY i j := add_mem (hX i j) (hY i j)
  zero_mem' _ _ := zero_mem S
  smul_mem' c _ hX i j := SMulMemClass.smul_mem c (hX i j)

variable {S}

/-- The matrices with entries in `S` are closed under the conjugate transpose. -/
lemma star_mem_matrixSubmodule {n : ℕ} {X : CStarMatrix (Fin n) (Fin n) T}
    (hX : X ∈ S.matrixSubmodule n) : star X ∈ S.matrixSubmodule n :=
  fun i j => StarMemClass.star_mem (hX j i)

/-- The identity matrix has its entries in `S`, which contains `0` and `1`. -/
lemma one_mem_matrixSubmodule (n : ℕ) : (1 : CStarMatrix (Fin n) (Fin n) T) ∈ S.matrixSubmodule n :=
  fun i j => by
    change (if i = j then (1 : T) else 0) ∈ S
    split_ifs
    · exact OneMemClass.one_mem S
    · exact zero_mem S

/-- A matrix over `T` with entries in `S`, as a matrix over `S`. -/
def restrictEntries {n : ℕ} (X : S.matrixSubmodule n) : CStarMatrix (Fin n) (Fin n) S :=
  ofMatrix (Matrix.of fun i j => ⟨X.1 i j, X.2 i j⟩)

/-- `restrictEntries X` is `X` as a matrix over `T`. -/
lemma map_val_restrictEntries {n : ℕ} (X : S.matrixSubmodule n) :
    (restrictEntries X).map Subtype.val = X.1 :=
  rfl

variable [∀ k, PartialOrder (CStarMatrix (Fin k) (Fin k) T)]

/-- The positive functional `X ↦ ∑ᵢⱼ ⟪eᵢ, φ(Xᵢⱼ) eⱼ⟫` on the matrices over `S`, attached to a map
`φ : S → B(H)` and vectors `e₁, …, eₙ`. -/
def vectorFunctional (φ : S →CP' (H →L[ℂ] H)) {n : ℕ} (e : Fin n → H) :
    S.matrixSubmodule n →ₗ[ℂ] ℂ where
  toFun X := ∑ i, ∑ j, ⟪e i, φ ⟨X.1 i j, X.2 i j⟩ (e j)⟫_ℂ
  map_add' X Y := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← inner_add_right, ← _root_.add_apply, ← map_add]
    rfl
  map_smul' c X := by
    simp only [RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← inner_smul_right, ← _root_.smul_apply, ← map_smul]
    rfl

/-- The value `∑ᵢⱼ ⟪eᵢ, φ(Xᵢⱼ) eⱼ⟫` of `vectorFunctional φ e` at `X`. -/
lemma vectorFunctional_apply (φ : S →CP' (H →L[ℂ] H)) {n : ℕ} (e : Fin n → H)
    (X : S.matrixSubmodule n) :
    vectorFunctional φ e X = ∑ i, ∑ j, ⟪e i, φ ⟨X.1 i j, X.2 i j⟩ (e j)⟫_ℂ :=
  rfl

/-- The functional `X ↦ ∑ᵢⱼ ⟪eᵢ, φ(Xᵢⱼ) eⱼ⟫` is positive when `φ` is completely positive. -/
lemma vectorFunctional_nonneg (φ : S →CP' (H →L[ℂ] H)) {n : ℕ} (e : Fin n → H)
    (X : S.matrixSubmodule n) (hX : 0 ≤ (X : CStarMatrix (Fin n) (Fin n) T)) :
    0 ≤ vectorFunctional φ e X := by
  have h := φ.map_cstarMatrix_nonneg (M := restrictEntries X)
    (cstarMatrix_nonneg_iff.mpr (by rwa [map_val_restrictEntries]))
  exact CStarMatrix.nonneg_iff_sum_inner_apply_nonneg.mp h e

end OperatorSubsystem

namespace OperatorSystem

variable {T : Type*} [AddCommGroup T] [Module ℂ T]

/-- The functional `a ↦ F (Eᵢⱼ a)` on `T` read off a functional `F` on the `n × n` matrices over `T`,
where `Eᵢⱼ a` is the matrix with the single nonzero entry `a` at `(i, j)`. -/
def entryFunctional {n : ℕ} (F : CStarMatrix (Fin n) (Fin n) T →ₗ[ℂ] ℂ) (i j : Fin n) : T →ₗ[ℂ] ℂ :=
  F ∘ₗ (ofMatrixₗ : Matrix (Fin n) (Fin n) T ≃ₗ[ℂ] CStarMatrix (Fin n) (Fin n) T).toLinearMap ∘ₗ
    Matrix.singleLinearMap ℂ i j

/-- `entryFunctional F i j` evaluates `F` at the matrix unit `Eᵢⱼ a`. -/
lemma entryFunctional_apply {n : ℕ} (F : CStarMatrix (Fin n) (Fin n) T →ₗ[ℂ] ℂ) (i j : Fin n)
    (a : T) : entryFunctional F i j a = F (ofMatrix (Matrix.single i j a)) :=
  rfl

/-- A functional on matrices is the sum of its values on the entries. -/
lemma apply_eq_sum_entryFunctional {n : ℕ} (F : CStarMatrix (Fin n) (Fin n) T →ₗ[ℂ] ℂ)
    (X : CStarMatrix (Fin n) (Fin n) T) : F X = ∑ i, ∑ j, entryFunctional F i j (X i j) := by
  conv_lhs => rw [show X = ∑ i, ∑ j, ofMatrix (Matrix.single i j (X i j)) from
    Matrix.matrix_eq_sum_single X]
  simp only [map_sum, entryFunctional_apply]

/-- The map `a ↦ ∑ᵢⱼ F (Eᵢⱼ a) |eᵢ⟩⟨eⱼ|` into `B(H)` attached to a functional `F` on the `n × n`
matrices over `T` and vectors `e₁, …, eₙ` of `H`. -/
def mapOfFunctional {n : ℕ} (F : CStarMatrix (Fin n) (Fin n) T →ₗ[ℂ] ℂ) (e : Fin n → H) :
    T →ₗ[ℂ] (H →L[ℂ] H) :=
  ∑ i, ∑ j, (entryFunctional F i j).smulRight (InnerProductSpace.rankOne ℂ (e i) (e j))

omit [CompleteSpace H] in
/-- The matrix coefficients `⟪x, ψ(a) y⟫ = ∑ᵢⱼ F(Eᵢⱼ a) ⟪x, eᵢ⟫ ⟪eⱼ, y⟫` of
`mapOfFunctional F e`. -/
lemma inner_mapOfFunctional_apply {n : ℕ} (F : CStarMatrix (Fin n) (Fin n) T →ₗ[ℂ] ℂ)
    (e : Fin n → H) (a : T) (x y : H) :
    ⟪x, mapOfFunctional F e a y⟫_ℂ =
      ∑ i, ∑ j, entryFunctional F i j a * (⟪x, e i⟫_ℂ * ⟪e j, y⟫_ℂ) := by
  simp only [mapOfFunctional, LinearMap.sum_apply, LinearMap.smulRight_apply, _root_.sum_apply,
    _root_.smul_apply, InnerProductSpace.rankOne_apply, inner_sum, inner_smul_right]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

variable [StarAddMonoid T] [StarModule ℂ T] [PartialOrder T]
  [∀ k, PartialOrder (CStarMatrix (Fin k) (Fin k) T)] [MatrixOrdered T]

/-- The map `a ↦ ∑ᵢⱼ F (Eᵢⱼ a) |eᵢ⟩⟨eⱼ|` of a positive functional `F` is completely positive: the
quadratic form `∑ₚ_q ⟪ξₚ, ψ(Xₚ_q) ξ_q⟫` of a matrix `X` is `F (β⋆ X β)` for the scalar matrix
`β q j = ⟪eⱼ, ξ_q⟫`. -/
def completelyPositiveMapOfFunctional {n : ℕ} (F : CStarMatrix (Fin n) (Fin n) T →ₗ[ℂ] ℂ)
    (hF : ∀ X, 0 ≤ X → 0 ≤ F X) (e : Fin n → H) : T →CP' (H →L[ℂ] H) where
  toLinearMap := mapOfFunctional F e
  map_cstarMatrix_nonneg' k X hX := by
    rw [CStarMatrix.nonneg_iff_sum_inner_apply_nonneg]
    intro ξ
    let β : Matrix (Fin k) (Fin n) ℂ := Matrix.of fun q j => ⟪e j, ξ q⟫_ℂ
    have key : ∑ p, ∑ q, ⟪ξ p, X.map (mapOfFunctional F e) p q (ξ q)⟫_ℂ =
        F (scalarConj β X) := by
      rw [apply_eq_sum_entryFunctional]
      simp only [scalarConj_apply, map_sum, map_smul, smul_eq_mul, β, Matrix.of_apply,
        ]
      change ∑ p, ∑ q, ⟪ξ p, mapOfFunctional F e (X p q) (ξ q)⟫_ℂ = _
      simp only [inner_mapOfFunctional_apply]
      rw [Finset.sum_congr rfl fun p _ => Finset.sum_comm]
      rw [Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun p _ =>
        Finset.sum_congr rfl fun q _ => ?_
      rw [Complex.star_def, inner_conj_symm]
      ring
    rw [key]
    exact hF _ (MatrixOrdered.scalarConj_nonneg β hX)

end OperatorSystem

namespace OperatorSubsystem

variable {T : Type*} [AddCommGroup T] [Module ℂ T] [StarAddMonoid T] [StarModule ℂ T]
  [PartialOrder T] [∀ k, PartialOrder (CStarMatrix (Fin k) (Fin k) T)] [One T] [OperatorSystem T]
  {S : OperatorSubsystem T}

open OperatorSystem

/-- **Arveson's extension theorem, finite step.** For orthonormal vectors `e₁, …, eₙ`, a completely
positive map `φ : S → B(H)` on an operator subsystem has a completely positive extension
`ψ : T → B(H)` up to compression to the span of the `eᵢ`: `⟪x, ψ(s) y⟫ = ⟪x, φ(s) y⟫` for `s ∈ S` and
`x, y` in the span, and `‖ψ 1‖ ≤ ‖φ 1‖`. The positive functional `X ↦ ∑ᵢⱼ ⟪eᵢ, φ(Xᵢⱼ) eⱼ⟫` on the
matrices over `S` extends to the matrices over `T` (`exists_extension_nonneg_of_orderUnit`), and
`ψ(a) = ∑ᵢⱼ F(Eᵢⱼ a) |eᵢ⟩⟨eⱼ|` (`OperatorSystem.completelyPositiveMapOfFunctional`). -/
theorem exists_completelyPositiveMap_of_orthonormal (φ : S →CP' (H →L[ℂ] H)) {n : ℕ}
    {e : Fin n → H} (he : Orthonormal ℂ e) :
    ∃ ψ : T →CP' (H →L[ℂ] H), ‖ψ 1‖ ≤ ‖φ 1‖ ∧
      ∀ (s : S), ∀ x ∈ Submodule.span ℂ (Set.range e), ∀ y ∈ Submodule.span ℂ (Set.range e),
        ⟪x, ψ s y⟫_ℂ = ⟪x, φ s y⟫_ℂ := by
  classical
  have hrepr : ∀ x ∈ Submodule.span ℂ (Set.range e), ∑ i, ⟪e i, x⟫_ℂ • e i = x := fun x hx => by
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hx
    simp_rw [he.inner_right_fintype]
  obtain ⟨F, hFf, hF⟩ := exists_extension_nonneg_of_orderUnit
    (E := CStarMatrix (Fin n) (Fin n) T)
    (fun _ hX => MatrixOrdered.isSelfAdjoint_of_cstarMatrix_nonneg hX)
    (fun _ _ hc hX => MatrixOrdered.smul_nonneg_of_nonneg hc hX)
    (OperatorSystem.one_nonneg n) (fun _ hX => OperatorSystem.exists_le_smul_one_of_isSelfAdjoint hX)
    (S.matrixSubmodule n) (fun _ hX => star_mem_matrixSubmodule hX) (one_mem_matrixSubmodule n)
    (vectorFunctional φ e) (vectorFunctional_nonneg φ e)
  -- on a matrix unit with entry in `S`, `F` is a matrix coefficient of `φ`
  have hFs : ∀ (s : S) i j, entryFunctional F i j s = ⟪e i, φ s (e j)⟫_ℂ := by
    intro s i j
    have hsingle : ∀ k l, Matrix.single i j (s : T) k l = ((Matrix.single i j s k l : S) : T) :=
      fun k l => by simp only [Matrix.single_apply]; split_ifs <;> rfl
    have hmem : ofMatrix (Matrix.single i j (s : T)) ∈ S.matrixSubmodule n := fun k l => by
      change Matrix.single i j (s : T) k l ∈ S
      rw [hsingle]
      exact (Matrix.single i j s k l).2
    rw [entryFunctional_apply]
    refine (hFf ⟨_, hmem⟩).trans ?_
    rw [vectorFunctional_apply]
    have hφ : ∀ k l (h : (⟨_, hmem⟩ : S.matrixSubmodule n).1 k l ∈ S), φ ⟨_, h⟩ =
        if i = k ∧ j = l then φ s else 0 := fun k l h => by
      rw [show (⟨_, h⟩ : S) = Matrix.single i j s k l from Subtype.ext (hsingle k l),
        Matrix.single_apply]
      split_ifs <;> simp
    simp only [hφ]
    rw [Finset.sum_eq_single i (fun k _ hk => Finset.sum_eq_zero fun l _ => by simp [Ne.symm hk])
      (by simp), Finset.sum_eq_single j (fun l _ hl => by simp [Ne.symm hl]) (by simp)]
    simp
  have hψ : ∀ (s : S) (x y : H), ⟪x, mapOfFunctional F e s y⟫_ℂ =
      ∑ i, ∑ j, ⟪x, e i⟫_ℂ * ⟪e i, φ s (e j)⟫_ℂ * ⟪e j, y⟫_ℂ := fun s x y => by
    rw [inner_mapOfFunctional_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hFs]
    ring
  refine ⟨completelyPositiveMapOfFunctional F hF e, ?_, fun s x hx y hy => ?_⟩
  · -- `ψ 1` is the compression of `φ 1` to the span of the `eᵢ`
    let P : H → H := fun w => ∑ i, ⟪e i, w⟫_ℂ • e i
    have hP : ∀ z, mapOfFunctional F e (1 : T) z = P (φ 1 (P z)) := fun z =>
      ext_inner_left ℂ fun x => by
        have := hψ 1 x z
        rw [show ((1 : S) : T) = 1 from rfl] at this
        rw [this]
        simp only [P, map_sum, map_smul, inner_sum, inner_smul_right]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun z => ?_
    change ‖mapOfFunctional F e (1 : T) z‖ ≤ _
    rw [hP]
    calc ‖P (φ 1 (P z))‖ ≤ ‖φ 1 (P z)‖ := he.norm_sum_inner_smul_le _
      _ ≤ ‖φ 1‖ * ‖P z‖ := (φ 1).le_opNorm _
      _ ≤ ‖φ 1‖ * ‖z‖ := by gcongr; exact he.norm_sum_inner_smul_le z
  · change ⟪x, mapOfFunctional F e s y⟫_ℂ = _
    rw [hψ]
    conv_rhs => rw [← hrepr x hx, ← hrepr y hy]
    simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
      inner_conj_symm, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

end OperatorSubsystem

namespace OperatorSystem

variable {T : Type*} [AddCommGroup T] [Module ℂ T] [StarAddMonoid T] [StarModule ℂ T]
  [PartialOrder T] [∀ k, PartialOrder (CStarMatrix (Fin k) (Fin k) T)] [One T] [OperatorSystem T]

/-- A bound `r(ℜ a) + r(ℑ a)` for an element `a` of an operator system, where `r(h) ≥ 0` is a chosen
constant with `-r(h) • 1 ≤ h ≤ r(h) • 1` for self-adjoint `h`. -/
def orderBound (a : T) : ℝ :=
  (exists_abs_le_smul_one' (ℜ a).2).choose + (exists_abs_le_smul_one' (ℑ a).2).choose

/-- The bound `orderBound a` is nonnegative. -/
lemma orderBound_nonneg (a : T) : 0 ≤ orderBound a :=
  add_nonneg (exists_abs_le_smul_one' (ℜ a).2).choose_spec.1
    (exists_abs_le_smul_one' (ℑ a).2).choose_spec.1

/-- A completely positive map into `B(H)` is bounded on an element between `-r • 1` and `r • 1`
by `3 r ‖ψ 1‖`: `ψ(r • 1 ∓ a)` are positive, so `‖ψ(r • 1 - a)‖ ≤ ‖2 r ψ 1‖`. -/
lemma norm_apply_le_of_abs_le (ψ : T →CP' (H →L[ℂ] H)) {a : T} {r : ℝ} (hr : 0 ≤ r)
    (h₁ : -((r : ℂ) • 1) ≤ a) (h₂ : a ≤ (r : ℂ) • 1) : ‖ψ a‖ ≤ 3 * r * ‖ψ 1‖ := by
  have hA : 0 ≤ ψ ((r : ℂ) • 1 - a) := map_nonneg ψ (sub_nonneg.mpr h₂)
  have hB : 0 ≤ ψ ((r : ℂ) • 1 + a) := map_nonneg ψ (neg_le_iff_add_nonneg'.mp h₁)
  have hAB : ψ ((r : ℂ) • 1 - a) + ψ ((r : ℂ) • 1 + a) = ((2 * r : ℝ) : ℂ) • ψ 1 := by
    rw [← map_add, sub_add_add_cancel, ← add_smul, map_smul]
    push_cast
    ring_nf
  have hnorm : ∀ (c : ℝ) (x : H →L[ℂ] H), 0 ≤ c → ‖(c : ℂ) • x‖ = c * ‖x‖ := fun c x hc => by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hc]
  have hA' : ‖ψ ((r : ℂ) • 1 - a)‖ ≤ 2 * r * ‖ψ 1‖ := by
    rw [← hnorm _ _ (by positivity), ← hAB]
    exact CStarAlgebra.norm_le_norm_of_le_of_nonneg (le_add_of_nonneg_right hB) hA
  have ha : ψ a = (r : ℂ) • ψ 1 - ψ ((r : ℂ) • 1 - a) := by
    rw [map_sub, map_smul, sub_sub_cancel]
  rw [ha]
  calc ‖(r : ℂ) • ψ 1 - ψ ((r : ℂ) • 1 - a)‖
      ≤ ‖(r : ℂ) • ψ 1‖ + ‖ψ ((r : ℂ) • 1 - a)‖ := norm_sub_le _ _
    _ ≤ r * ‖ψ 1‖ + 2 * r * ‖ψ 1‖ := by rw [hnorm _ _ hr]; gcongr
    _ = 3 * r * ‖ψ 1‖ := by ring

/-- A completely positive map into `B(H)` satisfies `‖ψ a‖ ≤ 3 (r(ℜ a) + r(ℑ a)) ‖ψ 1‖`, a bound
that depends on `ψ` only through `‖ψ 1‖`. -/
lemma norm_apply_le_orderBound (ψ : T →CP' (H →L[ℂ] H)) (a : T) :
    ‖ψ a‖ ≤ 3 * orderBound a * ‖ψ 1‖ := by
  obtain ⟨hr₁, h₁, h₂⟩ := (exists_abs_le_smul_one' (ℜ a).2).choose_spec
  obtain ⟨hs₁, k₁, k₂⟩ := (exists_abs_le_smul_one' (ℑ a).2).choose_spec
  have hre := norm_apply_le_of_abs_le ψ hr₁ h₁ h₂
  have him := norm_apply_le_of_abs_le ψ hs₁ k₁ k₂
  conv_lhs => rw [← realPart_add_I_smul_imaginaryPart a]
  rw [map_add, map_smul]
  calc ‖ψ (ℜ a : T) + Complex.I • ψ (ℑ a : T)‖ ≤ ‖ψ (ℜ a : T)‖ + ‖ψ (ℑ a : T)‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, Complex.norm_I, one_mul]
    _ ≤ 3 * orderBound a * ‖ψ 1‖ := by
        rw [orderBound]
        linarith

end OperatorSystem

namespace OperatorSubsystem

variable {T : Type*} [AddCommGroup T] [Module ℂ T] [StarAddMonoid T] [StarModule ℂ T]
  [PartialOrder T] [∀ k, PartialOrder (CStarMatrix (Fin k) (Fin k) T)] [One T] [OperatorSystem T]
  {S : OperatorSubsystem T}

open OperatorSystem ContinuousLinearMapWOT

/-- **Arveson's extension theorem.** A completely positive map `φ : S → B(H)` on an operator
subsystem `S` of an operator system `T` extends to a completely positive map `ψ : T → B(H)`.

For each finite set `t ⊆ H`, the finite step (`exists_completelyPositiveMap_of_orthonormal`), with
an orthonormal basis of the span of `t`, gives a completely positive `ψₜ : T → B(H)` that agrees
with `φ` on `S` in the matrix coefficients `⟪x, · y⟫`, `x, y ∈ t`, with `‖ψₜ a‖` bounded independently
of `t` (`OperatorSystem.norm_apply_le_orderBound`). In the weak operator topology the bounded
families of operators form a compact set (`ContinuousLinearMapWOT.isCompact_closedBall`), so the
net `(ψₜ)ₜ` has a cluster point; linearity, complete positivity and agreement with `φ` are closed
conditions that the `ψₜ` eventually satisfy, so the cluster point satisfies them. -/
theorem exists_extension_completelyPositiveMap (φ : S →CP' (H →L[ℂ] H)) :
    ∃ ψ : T →CP' (H →L[ℂ] H), ψ.restrict S = φ := by
  classical
  -- the finite step on the span of each finite set of vectors
  have hfin : ∀ t : Finset H, ∃ ψ : T →CP' (H →L[ℂ] H), ‖ψ 1‖ ≤ ‖φ 1‖ ∧
      ∀ s : S, ∀ x ∈ t, ∀ y ∈ t, ⟪x, ψ s y⟫_ℂ = ⟪x, φ s y⟫_ℂ := by
    intro t
    let K := Submodule.span ℂ (t : Set H)
    let b := stdOrthonormalBasis ℂ K
    let e : Fin _ → H := fun i => (b i : H)
    have he : Orthonormal ℂ e := b.orthonormal.comp_linearIsometry K.subtypeₗᵢ
    have hspan : Submodule.span ℂ (Set.range e) = K := by
      rw [show Set.range e = K.subtype '' Set.range b from (Set.range_comp _ _),
        Submodule.span_image, ← b.coe_toBasis, b.toBasis.span_eq, Submodule.map_subtype_top]
    obtain ⟨ψ, hψ1, hψ⟩ := exists_completelyPositiveMap_of_orthonormal φ he
    refine ⟨ψ, hψ1, fun s x hx y hy => hψ s x ?_ y ?_⟩ <;> rw [hspan] <;>
      exact Submodule.subset_span ‹_›
  choose ψ hψ1 hψ using hfin
  -- the cluster point of the net `t ↦ ψ t` in the product of weak operator topologies
  let Ψ : Finset H → T → (H →WOT[ℂ] H) := fun t a => ofCLM (ψ t a)
  let C : T → ℝ := fun a => 3 * orderBound a * ‖φ 1‖
  have hK : IsCompact (Set.univ.pi fun a => (toCLM ⁻¹' Metric.closedBall 0 (C a) :
      Set (H →WOT[ℂ] H))) :=
    isCompact_univ_pi fun a => isCompact_closedBall 0 (C a)
  have hΨK : ∀ t, Ψ t ∈ Set.univ.pi fun a => (toCLM ⁻¹' Metric.closedBall 0 (C a) :
      Set (H →WOT[ℂ] H)) := fun t a _ => by
    change ψ t a ∈ Metric.closedBall 0 (C a)
    rw [mem_closedBall_zero_iff]
    exact (norm_apply_le_orderBound (ψ t) a).trans
      (mul_le_mul_of_nonneg_left (hψ1 t) (mul_nonneg zero_le_three (orderBound_nonneg a)))
  obtain ⟨ψ₀, -, hψ₀⟩ := hK.exists_mapClusterPt (f := atTop)
    (tendsto_principal.mpr (Eventually.of_forall hΨK))
  have key : ∀ s : Set (T → H →WOT[ℂ] H), IsClosed s → (∀ t, Ψ t ∈ s) → ψ₀ ∈ s :=
    fun s hs h => hs.mem_of_mapClusterPt hψ₀ (Eventually.of_forall h)
  have hinner : ∀ (a : T) (x y : H),
      Continuous fun g : T → H →WOT[ℂ] H => ⟪x, g a y⟫_ℂ := fun a x y =>
    (continuous_iff.mp (continuous_apply a)) y x
  -- the closed conditions inherited from the `ψ t`
  have hadd : ∀ a b x y, ⟪x, ψ₀ (a + b) y⟫_ℂ = ⟪x, ψ₀ a y⟫_ℂ + ⟪x, ψ₀ b y⟫_ℂ := fun a b x y =>
    key {g | ⟪x, g (a + b) y⟫_ℂ = ⟪x, g a y⟫_ℂ + ⟪x, g b y⟫_ℂ}
      (isClosed_eq (hinner _ x y) ((hinner a x y).add (hinner b x y)))
      fun t => by
        change ⟪x, ψ t (a + b) y⟫_ℂ = ⟪x, ψ t a y⟫_ℂ + ⟪x, ψ t b y⟫_ℂ
        rw [map_add, _root_.add_apply, inner_add_right]
  have hsmul : ∀ (c : ℂ) a x y, ⟪x, ψ₀ (c • a) y⟫_ℂ = c * ⟪x, ψ₀ a y⟫_ℂ := fun c a x y =>
    key {g | ⟪x, g (c • a) y⟫_ℂ = c * ⟪x, g a y⟫_ℂ}
      (isClosed_eq (hinner _ x y) (continuous_const.mul (hinner a x y)))
      fun t => by
        change ⟪x, ψ t (c • a) y⟫_ℂ = c * ⟪x, ψ t a y⟫_ℂ
        rw [map_smul, _root_.smul_apply, inner_smul_right]
  have hcp : ∀ (k : ℕ) (X : CStarMatrix (Fin k) (Fin k) T), 0 ≤ X → ∀ ξ : Fin k → H,
      0 ≤ ∑ p, ∑ q, ⟪ξ p, ψ₀ (X p q) (ξ q)⟫_ℂ := fun k X hX ξ =>
    key {g | 0 ≤ ∑ p, ∑ q, ⟪ξ p, g (X p q) (ξ q)⟫_ℂ}
      (isClosed_le continuous_const (continuous_finsetSum _ fun p _ =>
        continuous_finsetSum _ fun q _ => hinner _ _ _))
      fun t => CStarMatrix.nonneg_iff_sum_inner_apply_nonneg.mp
        ((ψ t).map_cstarMatrix_nonneg hX) ξ
  have hext : ∀ (s : S) (x y : H), ⟪x, ψ₀ s y⟫_ℂ = ⟪x, φ s y⟫_ℂ := fun s x y => by
    refine (isClosed_eq (hinner s x y) continuous_const).mem_of_mapClusterPt hψ₀ ?_
    filter_upwards [eventually_ge_atTop {x, y}] with t ht
    exact hψ t s x (ht (by simp)) y (ht (by simp))
  -- the cluster point is a completely positive extension of `φ`
  let ψ' : T →ₗ[ℂ] (H →L[ℂ] H) :=
    { toFun := fun a => toCLM (ψ₀ a)
      map_add' := fun a b => ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => by
        rw [_root_.add_apply, inner_add_right]
        exact hadd a b x y
      map_smul' := fun c a => ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => by
        rw [RingHom.id_apply, _root_.smul_apply, inner_smul_right]
        exact hsmul c a x y }
  refine ⟨⟨ψ', fun k X hX => CStarMatrix.nonneg_iff_sum_inner_apply_nonneg.mpr (hcp k X hX)⟩, ?_⟩
  refine CompletelyPositiveMap'.ext fun s => ContinuousLinearMap.ext fun y =>
    ext_inner_left ℂ fun x => hext s x y

end OperatorSubsystem

/-- **Arveson's extension theorem** for an operator subsystem `S` of a unital C⋆-algebra `A`: a
completely positive map `φ : S → B(H)` extends to a completely positive map `A → B(H)`, in the
sense of Mathlib's `CompletelyPositiveMap`. -/
theorem CompletelyPositiveMap.exists_extension_of_operatorSubsystem {A : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {S : OperatorSubsystem A} (φ : S →CP' (H →L[ℂ] H)) :
    ∃ ψ : A →CP (H →L[ℂ] H), ∀ s : S, ψ s = φ s := by
  obtain ⟨ψ, hψ⟩ := OperatorSubsystem.exists_extension_completelyPositiveMap φ
  exact ⟨CompletelyPositiveMap'.equivCompletelyPositiveMap ψ, fun s => by
    rw [← hψ]
    rfl⟩
