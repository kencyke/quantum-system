/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.OperatorSpace.CompletelyPositive

/-!
# The Paulsen system of a subspace

For a subspace `E` of a unital C⋆-algebra `A`, the **Paulsen system** is the operator subsystem
`{!![λ 1, x; y⋆, μ 1] : λ, μ ∈ ℂ, x, y ∈ E}` of `M₂(A)` (`Submodule.paulsenSystem`). A linear map
`φ : E → B` into a unital C⋆-algebra induces `!![λ 1, x; y⋆, μ 1] ↦ !![λ 1, φ x; (φ y)⋆, μ 1]`
(`Submodule.paulsenMap`), and this map is completely positive when `φ` is completely contractive
(`Submodule.paulsenCompletelyPositiveMap`).

After exchanging the outer and inner indices, a matrix over the Paulsen system is a `2 × 2` block
matrix `!![α 1, X; X⋆, β 1]` with scalar matrices `α`, `β`; when `α`, `β` are strictly positive it is
positive exactly when `‖α^{-1/2} X β^{-1/2}‖ ≤ 1` (`CStarMatrix.nonneg_star_mul_self_block_iff` with
`s = α^{1/2}`, `t = β^{1/2}`), a condition that a complete contraction preserves. Adding `ε • 1`
reduces positivity to this case.

## Main definitions

* `Submodule.paulsenSystem E` — the Paulsen system of `E`.
* `Submodule.paulsenMap φ` — the map induced by `φ` on the Paulsen system.

## Main results

* `Submodule.paulsenMap_nonneg` — **Paulsen's lemma**: `Submodule.paulsenMap φ` is completely
  positive when `‖φ‖_cb ≤ 1`; `Submodule.paulsenCompletelyPositiveMap` bundles it.
-/

@[expose] public noncomputable section

open scoped CStarAlgebra ComplexOrder
open CStarMatrix

namespace CStarMatrix

variable {C : Type*} [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C] {n : ℕ}

/-- For a strictly positive scalar matrix `α`, the square root `s = α^{1/2}` and its inverse
`γ = α^{-1/2}` are self-adjoint, `s γ = γ s = 1` and `s s = α`. -/
private lemma sqrt_facts {α : CStarMatrix (Fin n) (Fin n) ℂ} (hα : IsStrictlyPositive α) :
    CFC.sqrt α * Ring.inverse (CFC.sqrt α) = 1 ∧ Ring.inverse (CFC.sqrt α) * CFC.sqrt α = 1 ∧
      CFC.sqrt α * CFC.sqrt α = α ∧ IsSelfAdjoint (Ring.inverse (CFC.sqrt α)) ∧
      IsSelfAdjoint (CFC.sqrt α) :=
  have hu := hα.isUnit_cfcSqrt
  ⟨Ring.mul_inverse_cancel _ hu, Ring.inverse_mul_cancel _ hu, CFC.sqrt_mul_sqrt_self α hα.nonneg,
    (hα.sqrt.ringInverse).isSelfAdjoint, (CFC.sqrt_nonneg α).isSelfAdjoint⟩

/-- For strictly positive scalar matrices `α`, `β`, the block matrix `!![α 1, X; X⋆, β 1]` is positive
exactly when `‖α^{-1/2} X β^{-1/2}‖ ≤ 1`: `CStarMatrix.nonneg_star_mul_self_block_iff` with the units
`α^{1/2}`, `β^{1/2}`. -/
private lemma ofScalar_block_nonneg_iff_norm_le_one {α β : CStarMatrix (Fin n) (Fin n) ℂ}
    (hα : IsStrictlyPositive α) (hβ : IsStrictlyPositive β) (x : CStarMatrix (Fin n) (Fin n) C) :
    0 ≤ (ofMatrix !![ofScalar C n α, x; star x, ofScalar C n β] :
        CStarMatrix (Fin 2) (Fin 2) (CStarMatrix (Fin n) (Fin n) C)) ↔
      ‖ofScalar C n (Ring.inverse (CFC.sqrt α)) * x *
        ofScalar C n (Ring.inverse (CFC.sqrt β))‖ ≤ 1 := by
  obtain ⟨hα₁, hα₂, hα₃, hα₄, hα₅⟩ := sqrt_facts hα
  obtain ⟨hβ₁, hβ₂, hβ₃, hβ₄, hβ₅⟩ := sqrt_facts hβ
  let ι := ofScalar C n
  let u : (CStarMatrix (Fin n) (Fin n) C)ˣ := ⟨ι (CFC.sqrt α), ι (Ring.inverse (CFC.sqrt α)),
    by rw [← map_mul, hα₁, map_one], by rw [← map_mul, hα₂, map_one]⟩
  let v : (CStarMatrix (Fin n) (Fin n) C)ˣ := ⟨ι (CFC.sqrt β), ι (Ring.inverse (CFC.sqrt β)),
    by rw [← map_mul, hβ₁, map_one], by rw [← map_mul, hβ₂, map_one]⟩
  have h := nonneg_star_mul_self_block_iff u v x
  have hu : star (u : CStarMatrix (Fin n) (Fin n) C) * u = ι α := by
    change star (ι _) * ι _ = _
    rw [← map_star, hα₅.star_eq, ← map_mul, hα₃]
  have hv : star (v : CStarMatrix (Fin n) (Fin n) C) * v = ι β := by
    change star (ι _) * ι _ = _
    rw [← map_star, hβ₅.star_eq, ← map_mul, hβ₃]
  have hu' : star (↑u⁻¹ : CStarMatrix (Fin n) (Fin n) C) = ι (Ring.inverse (CFC.sqrt α)) := by
    change star (ι _) = _
    rw [← map_star, hα₄.star_eq]
  rw [hu, hv, hu'] at h
  exact h

end CStarMatrix

namespace Submodule

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] (E : Submodule ℂ A)

omit [PartialOrder A] [StarOrderedRing A] in
/-- The span of `1` is closed under `star`. -/
lemma star_mem_span_one {x : A} (hx : x ∈ ℂ ∙ (1 : A)) : star x ∈ ℂ ∙ (1 : A) := by
  obtain ⟨c, rfl⟩ := mem_span_singleton.mp hx
  rw [star_smul, star_one]
  exact smul_mem _ _ (mem_span_singleton_self 1)

/-- The **Paulsen system** of a subspace `E` of a unital C⋆-algebra `A`: the operator subsystem of
`M₂(A)` of the matrices `!![λ 1, x; y⋆, μ 1]` with `λ, μ ∈ ℂ` and `x, y ∈ E`. -/
def paulsenSystem : OperatorSubsystem (CStarMatrix (Fin 2) (Fin 2) A) where
  carrier := {M | M 0 0 ∈ ℂ ∙ (1 : A) ∧ M 0 1 ∈ E ∧ star (M 1 0) ∈ E ∧ M 1 1 ∈ ℂ ∙ (1 : A)}
  add_mem' := fun {M N} hM hN => ⟨add_mem hM.1 hN.1, add_mem hM.2.1 hN.2.1,
    by rw [show (M + N) 1 0 = M 1 0 + N 1 0 from rfl, star_add]; exact add_mem hM.2.2.1 hN.2.2.1,
    add_mem hM.2.2.2 hN.2.2.2⟩
  zero_mem' := by
    refine ⟨zero_mem _, zero_mem _, ?_, zero_mem _⟩
    rw [show (0 : CStarMatrix (Fin 2) (Fin 2) A) 1 0 = 0 from rfl, star_zero]
    exact zero_mem _
  smul_mem' := fun c {M} hM => ⟨smul_mem _ c hM.1, smul_mem _ c hM.2.1,
    by rw [show (c • M) 1 0 = c • M 1 0 from rfl, star_smul]; exact smul_mem _ _ hM.2.2.1,
    smul_mem _ c hM.2.2.2⟩
  star_mem' := fun {M} hM => ⟨star_mem_span_one hM.1, hM.2.2.1,
    by rw [show (star M) 1 0 = star (M 0 1) from rfl, star_star]; exact hM.2.1,
    star_mem_span_one hM.2.2.2⟩
  one_mem' := ⟨mem_span_singleton_self 1, zero_mem _,
    by rw [show (1 : CStarMatrix (Fin 2) (Fin 2) A) 1 0 = 0 from rfl, star_zero]; exact zero_mem _,
    mem_span_singleton_self 1⟩

omit [PartialOrder A] [StarOrderedRing A] in
/-- Membership in the Paulsen system. -/
lemma mem_paulsenSystem {M : CStarMatrix (Fin 2) (Fin 2) A} :
    M ∈ E.paulsenSystem ↔
      M 0 0 ∈ ℂ ∙ (1 : A) ∧ M 0 1 ∈ E ∧ star (M 1 0) ∈ E ∧ M 1 1 ∈ ℂ ∙ (1 : A) :=
  Iff.rfl

variable [Nontrivial A]

omit [PartialOrder A] [StarOrderedRing A] in
/-- The coefficient `λ` of `λ 1 ∈ ℂ ∙ 1`. -/
abbrev coeffOne : (ℂ ∙ (1 : A)) →ₗ[ℂ] ℂ :=
  (LinearEquiv.toSpanNonzeroSingleton ℂ A 1 one_ne_zero).symm.toLinearMap

omit [PartialOrder A] [StarOrderedRing A] in
/-- `coeffOne x • 1 = x`. -/
lemma coeffOne_smul_one (x : ℂ ∙ (1 : A)) : coeffOne x • (1 : A) = x :=
  LinearEquiv.toSpanNonzeroSingleton_symm_apply_smul ℂ A 1 one_ne_zero x

variable {E}

/-- The map induced on the Paulsen system by a linear map `φ : E → B`:
`!![λ 1, x; y⋆, μ 1] ↦ !![λ 1, φ x; (φ y)⋆, μ 1]`. -/
def paulsenMap (φ : E →ₗ[ℂ] B) : E.paulsenSystem →ₗ[ℂ] CStarMatrix (Fin 2) (Fin 2) B where
  toFun M := ofMatrix !![coeffOne ⟨M.1 0 0, M.2.1⟩ • (1 : B), φ ⟨M.1 0 1, M.2.2.1⟩;
    star (φ ⟨star (M.1 1 0), M.2.2.2.1⟩), coeffOne ⟨M.1 1 1, M.2.2.2.2⟩ • (1 : B)]
  map_add' M N := by
    have h₀₀ : (⟨(M + N).1 0 0, (M + N).2.1⟩ : ℂ ∙ (1 : A)) = ⟨M.1 0 0, M.2.1⟩ + ⟨N.1 0 0, N.2.1⟩ :=
      rfl
    have h₀₁ : (⟨(M + N).1 0 1, (M + N).2.2.1⟩ : E) = ⟨M.1 0 1, M.2.2.1⟩ + ⟨N.1 0 1, N.2.2.1⟩ := rfl
    have h₁₀ : (⟨star ((M + N).1 1 0), (M + N).2.2.2.1⟩ : E) =
        ⟨star (M.1 1 0), M.2.2.2.1⟩ + ⟨star (N.1 1 0), N.2.2.2.1⟩ :=
      Subtype.ext (star_add _ _)
    have h₁₁ : (⟨(M + N).1 1 1, (M + N).2.2.2.2⟩ : ℂ ∙ (1 : A)) =
        ⟨M.1 1 1, M.2.2.2.2⟩ + ⟨N.1 1 1, N.2.2.2.2⟩ :=
      rfl
    rw [h₀₀, h₀₁, h₁₀, h₁₁, map_add, map_add, map_add, map_add, add_smul, add_smul, star_add]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  map_smul' c M := by
    have h₀₀ : (⟨(c • M).1 0 0, (c • M).2.1⟩ : ℂ ∙ (1 : A)) = c • ⟨M.1 0 0, M.2.1⟩ := rfl
    have h₀₁ : (⟨(c • M).1 0 1, (c • M).2.2.1⟩ : E) = c • ⟨M.1 0 1, M.2.2.1⟩ := rfl
    have h₁₀ : (⟨star ((c • M).1 1 0), (c • M).2.2.2.1⟩ : E) =
        star c • ⟨star (M.1 1 0), M.2.2.2.1⟩ :=
      Subtype.ext (star_smul _ _)
    have h₁₁ : (⟨(c • M).1 1 1, (c • M).2.2.2.2⟩ : ℂ ∙ (1 : A)) = c • ⟨M.1 1 1, M.2.2.2.2⟩ := rfl
    rw [h₀₀, h₀₁, h₁₀, h₁₁, map_smul, map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
      star_smul, star_star, SemigroupAction.mul_smul, SemigroupAction.mul_smul, RingHom.id_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

end Submodule

namespace Submodule

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] {E : Submodule ℂ A} [Nontrivial A]

/-- **Paulsen's lemma.** For a complete contraction `φ : E → B`, the map
`!![λ 1, x; y⋆, μ 1] ↦ !![λ 1, φ x; (φ y)⋆, μ 1]` on the Paulsen system is completely positive. A
positive `n × n` matrix over the Paulsen system is, after exchanging the outer and inner indices,
`!![α 1, X; X⋆, β 1]` with positive scalar matrices `α`, `β`; for `ε > 0`, adding `ε • 1` makes them
strictly positive, and positivity becomes `‖α'^{-1/2} X β'^{-1/2}‖ ≤ 1`
(`CStarMatrix.nonneg_star_mul_self_block_iff`), which `φ` preserves since `‖φ‖_cb ≤ 1` and `φ`
commutes with scalar matrices. -/
theorem paulsenMap_nonneg (φ : E →CB B) (hφ : ‖φ‖ ≤ 1) {n : ℕ}
    (X : CStarMatrix (Fin n) (Fin n) E.paulsenSystem) (hX : 0 ≤ X) :
    0 ≤ X.map (paulsenMap φ.toLinearMap) := by
  classical
  have hXA : 0 ≤ X.map Subtype.val := hX
  -- `X` is self-adjoint, so its `(1, 0)` entries are the adjoints of its `(0, 1)` entries
  have hsa : ∀ a b, (X a b).1 1 0 = star ((X b a).1 0 1) := fun a b => by
    have h := congrFun (congrFun (IsSelfAdjoint.of_nonneg hXA).star_eq a) b
    have h' := congrFun (congrFun h 1) 0
    exact h'.symm
  let α : CStarMatrix (Fin n) (Fin n) ℂ :=
    ofMatrix (Matrix.of fun a b => coeffOne (A := A) ⟨(X a b).1 0 0, (X a b).2.1⟩)
  let β : CStarMatrix (Fin n) (Fin n) ℂ :=
    ofMatrix (Matrix.of fun a b => coeffOne (A := A) ⟨(X a b).1 1 1, (X a b).2.2.2.2⟩)
  let xE : CStarMatrix (Fin n) (Fin n) E :=
    ofMatrix (Matrix.of fun a b => ⟨(X a b).1 0 1, (X a b).2.2.1⟩)
  have hT : transposeBlocks (X.map Subtype.val) = ofMatrix !![ofScalar A n α, xE.map Subtype.val;
      star (xE.map Subtype.val), ofScalar A n β] := by
    refine CStarMatrix.ext fun i j => CStarMatrix.ext fun a b => ?_
    fin_cases i <;> fin_cases j
    · change (X a b).1 0 0 = algebraMap ℂ A (α a b)
      rw [Algebra.algebraMap_eq_smul_one]
      exact (coeffOne_smul_one (A := A) ⟨(X a b).1 0 0, (X a b).2.1⟩).symm
    · rfl
    · change (X a b).1 1 0 = star ((X b a).1 0 1)
      exact hsa a b
    · change (X a b).1 1 1 = algebraMap ℂ A (β a b)
      rw [Algebra.algebraMap_eq_smul_one]
      exact (coeffOne_smul_one (A := A) ⟨(X a b).1 1 1, (X a b).2.2.2.2⟩).symm
  have hTφ : transposeBlocks (X.map (paulsenMap φ.toLinearMap)) = ofMatrix !![ofScalar B n α,
      xE.map φ; star (xE.map φ), ofScalar B n β] := by
    refine CStarMatrix.ext fun i j => CStarMatrix.ext fun a b => ?_
    fin_cases i <;> fin_cases j
    · change coeffOne ⟨(X a b).1 0 0, (X a b).2.1⟩ • (1 : B) = algebraMap ℂ B (α a b)
      rw [Algebra.algebraMap_eq_smul_one]
      rfl
    · rfl
    · change star (φ ⟨star ((X a b).1 1 0), (X a b).2.2.2.1⟩) = star (φ (xE b a))
      congr 2
      exact Subtype.ext (by
        change star ((X a b).1 1 0) = (X b a).1 0 1
        rw [hsa, star_star])
    · change coeffOne ⟨(X a b).1 1 1, (X a b).2.2.2.2⟩ • (1 : B) = algebraMap ℂ B (β a b)
      rw [Algebra.algebraMap_eq_smul_one]
      rfl
  -- the diagonal blocks are positive
  have hTn : 0 ≤ transposeBlocks (X.map Subtype.val) := by
    rw [← transposeBlocksStarAlgEquiv_apply]
    exact map_nonneg _ hXA
  have hαβ : 0 ≤ α ∧ 0 ≤ β := by
    rw [hT] at hTn
    have h₀ := diag_nonneg hTn (i := 0)
    have h₁ := diag_nonneg hTn (i := 1)
    rw [← map_zero (ofScalar A n)] at h₀ h₁
    exact ⟨(NonUnitalStarAlgHom.map_le_map_iff _ (ofScalar_injective (C := A) (n := n))).mp h₀,
      (NonUnitalStarAlgHom.map_le_map_iff _ (ofScalar_injective (C := A) (n := n))).mp h₁⟩
  -- the `ε`-step
  have key : ∀ ε : ℝ, 0 < ε →
      0 ≤ transposeBlocks (X.map (paulsenMap φ.toLinearMap)) + (ε : ℂ) • 1 := by
    intro ε hε
    have hα' := isStrictlyPositive_add_smul_one hαβ.1 hε
    have hβ' := isStrictlyPositive_add_smul_one hαβ.2 hε
    -- positivity over `A` gives the norm bound
    have hA : 0 ≤ transposeBlocks (X.map Subtype.val) + (ε : ℂ) • 1 :=
      add_nonneg hTn (smul_nonneg (by exact_mod_cast hε.le) zero_le_one)
    rw [hT, ofScalar_block_add_smul_one, ofScalar_block_nonneg_iff_norm_le_one hα' hβ'] at hA
    set γ := Ring.inverse (CFC.sqrt (α + (ε : ℂ) • 1))
    set δ := Ring.inverse (CFC.sqrt (β + (ε : ℂ) • 1))
    have hE : ‖scalarMul (ofMatrix.symm γ) (ofMatrix.symm δ) xE‖ ≤ 1 := by
      change ‖(scalarMul (ofMatrix.symm γ) (ofMatrix.symm δ) xE).map Subtype.val‖ ≤ 1
      rw [show (scalarMul (ofMatrix.symm γ) (ofMatrix.symm δ) xE).map Subtype.val =
        scalarMul (ofMatrix.symm γ) (ofMatrix.symm δ) (xE.map Subtype.val) from
          scalarMul_map _ _ xE E.subtype, scalarMul_eq_ofScalar_mul_mul]
      exact hA
    have hB : ‖ofScalar B n γ * xE.map φ * ofScalar B n δ‖ ≤ 1 := by
      rw [← scalarMul_eq_ofScalar_mul_mul, show xE.map φ = xE.map φ.toLinearMap from rfl,
        ← scalarMul_map]
      exact (φ.norm_map_cstarMatrix_le _).trans ((mul_le_mul hφ hE (OperatorSpace.norm_nonneg _)
        zero_le_one).trans_eq (one_mul 1))
    rw [hTφ, ofScalar_block_add_smul_one, ofScalar_block_nonneg_iff_norm_le_one hα' hβ']
    exact hB
  rw [← map_le_map_iff (transposeBlocksStarAlgEquiv n 2 B), map_zero,
    transposeBlocksStarAlgEquiv_apply]
  exact CStarAlgebra.nonneg_of_forall_add_smul_one_nonneg key

variable (E) in
/-- The map induced on the Paulsen system by a complete contraction, as a completely positive
map. -/
def paulsenCompletelyPositiveMap (φ : E →CB B) (hφ : ‖φ‖ ≤ 1) :
    E.paulsenSystem →CP' CStarMatrix (Fin 2) (Fin 2) B where
  toLinearMap := paulsenMap φ.toLinearMap
  map_cstarMatrix_nonneg' _ X hX := paulsenMap_nonneg φ hφ X hX

end Submodule
