/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Lp.lpHolder
public import QuantumSystem.Analysis.OperatorSpace.CompletelyPositive
public import QuantumSystem.Analysis.OperatorSystem.Arveson

/-!
# The Choi–Effros theorem

Every operator system `V` (`OperatorSystem`), a matrix-ordered space with an Archimedean matrix order
unit, is a concrete one: there is a unital linear map `j : V → B(H)` into the operators on a Hilbert
space with `0 ≤ X.map j ↔ 0 ≤ X` for every square matrix `X` over `V`
(`OperatorSystem.exists_isCompleteOrderEmbedding`), so that `V` is unitally completely order
isomorphic to an operator subsystem of `B(H)` (`OperatorSystem.exists_linearEquiv_operatorSubsystem`).
Conversely
every operator subsystem of `B(H)` is an operator system (`OperatorSubsystem.instOperatorSystem`).

The map `j` is the direct sum of all unital completely positive maps `φ : V → B(ℂⁿ)`, acting on the
Hilbert sum `⨁ ℂⁿ`; the norms `‖φ v‖` are bounded uniformly in `φ` through the order unit
(`OperatorSystem.norm_apply_le_orderBound`). It is completely positive, and the positivity of
`X.map j` gives that of each `X.map φ`, by restricting the quadratic form to a summand. These maps
detect positivity (`OperatorSystem.nonneg_iff_forall_map_nonneg`). A self-adjoint `k × k` matrix `X`
that is not positive is separated from the positive matrices by a positive functional `F` with
`F 1 = 1` and `F X < 0` (`exists_nonneg_functional_lt_zero_of_not_nonneg`), and `F` gives the
completely positive map `a ↦ ∑ᵢⱼ F(Eᵢⱼ a) |eᵢ⟩⟨eⱼ|` into `B(ℂᵏ)`, whose quadratic form at the
standard basis is `F X` (`OperatorSystem.sum_inner_mapOfFunctional_apply`). Adding `δ τ` to `F`,
with `τ(Y) = F(diag(tr Y))`, makes the value `P` at `1` strictly positive while keeping the value at
`X` negative, and `P^{-1/2} φ P^{-1/2}` is unital. A matrix `X` that is not self-adjoint is reduced
to the self-adjoint `i (X - X⋆)`, which every `φ` with `X.map φ ≥ 0` sends to `0`.

## Main results

* `OperatorSystem.nonneg_iff_forall_map_nonneg` — the unital completely positive maps into `B(ℂᵏ)`
  detect the positivity of `k × k` matrices.
* `OperatorSystem.exists_isCompleteOrderEmbedding` — **the Choi–Effros theorem**.
* `OperatorSystem.exists_linearEquiv_operatorSubsystem` — its form with an operator subsystem of
  `B(H)`.
-/

@[expose] public noncomputable section

open scoped CStarAlgebra InnerProductSpace InnerProduct ComplexOrder ComplexStarModule
open CStarMatrix

/-- The operators on `ℂᵏ`. -/
local notation "B(ℂ^" k ")" => EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)

universe u

namespace OperatorSystem

variable {V : Type u} [AddCommGroup V] [Module ℂ V] [StarAddMonoid V] [StarModule ℂ V]
  [PartialOrder V] [∀ k, PartialOrder (CStarMatrix (Fin k) (Fin k) V)] [One V] [OperatorSystem V]

/-! ### Unital completely positive maps into `B(ℂᵏ)` detect positivity -/

section Separation

variable (V) in
/-- The diagonal matrix `diag(a, …, a)`. -/
private def diagonalₗ (k : ℕ) : V →ₗ[ℂ] CStarMatrix (Fin k) (Fin k) V :=
  (ofMatrixₗ : Matrix (Fin k) (Fin k) V ≃ₗ[ℂ] CStarMatrix (Fin k) (Fin k) V).toLinearMap ∘ₗ
    Matrix.diagonalLinearMap (Fin k) ℂ V ∘ₗ LinearMap.pi fun _ => LinearMap.id

omit [One V] [OperatorSystem V] in
private lemma diagonalₗ_nonneg [MatrixOrdered V] {k : ℕ} {a : V} (ha : 0 ≤ a) : 0 ≤ diagonalₗ V k a := by
  change 0 ≤ ofMatrix (Matrix.diagonal fun _ => a)
  rw [diagonal_eq_sum_scalarConj]
  exact Finset.sum_nonneg fun i _ =>
    MatrixOrdered.scalarConj_nonneg _ (MatrixOrdered.single₁_nonneg_iff'.mpr ha)

variable (V) in
/-- The trace `Y ↦ ∑ᵢ Yᵢᵢ` of matrices over `V`. -/
private def traceₗ (k : ℕ) : CStarMatrix (Fin k) (Fin k) V →ₗ[ℂ] V :=
  Matrix.traceLinearMap (Fin k) ℂ V ∘ₗ
    (ofMatrixₗ : Matrix (Fin k) (Fin k) V ≃ₗ[ℂ] CStarMatrix (Fin k) (Fin k) V).symm.toLinearMap

omit [One V] [OperatorSystem V] in
private lemma traceₗ_nonneg [MatrixOrdered V] {k : ℕ} {Y : CStarMatrix (Fin k) (Fin k) V}
    (hY : 0 ≤ Y) : 0 ≤ traceₗ V k Y := by
  change 0 ≤ ∑ i, Y i i
  refine Finset.sum_nonneg fun i _ => ?_
  have h := MatrixOrdered.sum_smul_nonneg hY fun p => if p = i then (1 : ℂ) else 0
  simpa [apply_ite (star : ℂ → ℂ), ite_mul, ite_smul] using h

/-- A self-adjoint `k × k` matrix `X` over an operator system that is not positive is not positive
under some unital completely positive map `ψ : V → B(ℂᵏ)`: the separating functional of
`exists_nonneg_functional_lt_zero_of_not_nonneg`, perturbed and normalised as in the module
documentation. -/
private lemma exists_completelyPositiveMap_not_nonneg {k : ℕ} {X : CStarMatrix (Fin k) (Fin k) V}
    (hX : IsSelfAdjoint X) (hX0 : ¬0 ≤ X) :
    ∃ ψ : V →CP' B(ℂ^k),
      ψ 1 = 1 ∧ ¬0 ≤ X.map ψ := by
  obtain ⟨F, hF, hF1, hFX⟩ := exists_nonneg_functional_lt_zero_of_not_nonneg
    (E := CStarMatrix (Fin k) (Fin k) V)
    (fun _ hY => MatrixOrdered.isSelfAdjoint_of_cstarMatrix_nonneg hY)
    (fun _ _ hc hY => MatrixOrdered.smul_nonneg_of_nonneg hc hY) (one_nonneg k)
    (fun _ hY => exists_le_smul_one_of_isSelfAdjoint hY)
    (fun _ hY => nonneg_of_forall_add_smul_one_nonneg hY) hX hX0
  let e := EuclideanSpace.basisFun (Fin k) ℂ
  -- the positive functional `τ(Y) = F(diag(tr Y))`, with `τ(Eᵢⱼ 1) = δᵢⱼ`
  let τ := F ∘ₗ diagonalₗ V k ∘ₗ traceₗ V k
  have hτ : ∀ Y, 0 ≤ Y → 0 ≤ τ Y := fun Y hY => hF _ (diagonalₗ_nonneg (traceₗ_nonneg hY))
  have hτ1 : ∀ i j, entryFunctional τ i j 1 = if i = j then 1 else 0 := fun i j => by
    rw [entryFunctional_apply]
    change F (diagonalₗ V k (Matrix.trace (Matrix.single i j (1 : V)))) = _
    split_ifs with h
    · rw [h, Matrix.trace_single_eq_same, show diagonalₗ V k 1 = 1 from rfl, hF1]
    · rw [Matrix.trace_single_eq_of_ne i j (1 : V) h, map_zero, map_zero]
  -- `G = F + δ τ` is still negative at `X` for small `δ > 0`
  set c := (F X).re
  set d := (τ X).re
  have hc : c < 0 := (Complex.lt_def.mp hFX).1
  set δ : ℝ := -c / (2 * (|d| + 1)) with hδ_def
  have hδ : 0 < δ := div_pos (neg_pos.mpr hc) (by positivity)
  have hδd : c + δ * d < 0 := by
    have h₁ : δ * (|d| + 1) = -c / 2 := by
      rw [hδ_def]
      field_simp
    nlinarith [mul_le_mul_of_nonneg_left (le_abs_self d) hδ.le]
  let G := F + (δ : ℂ) • τ
  have hG : ∀ Y, 0 ≤ Y → 0 ≤ G Y := fun Y hY =>
    add_nonneg (hF Y hY) (mul_nonneg (Complex.zero_le_real.mpr hδ.le) (hτ Y hY))
  let φ := completelyPositiveMapOfFunctional G hG fun i => e i
  -- the quadratic form of `X.map φ` at the standard basis is `G X`
  have hφX : ¬0 ≤ X.map φ := fun h => by
    have hβ : (Matrix.of fun q j => ⟪e j, e q⟫_ℂ : Matrix (Fin k) (Fin k) ℂ) = 1 := by
      ext q j
      simp [Matrix.one_apply, orthonormal_iff_ite.mp e.orthonormal, eq_comm]
    have hq := sum_inner_mapOfFunctional_apply G (fun i => e i) X fun i => e i
    rw [hβ, scalarConj, Matrix.conjTranspose_one, scalarMul_one_one] at hq
    have h' := nonneg_iff_sum_inner_apply_nonneg.mp h fun i => e i
    change 0 ≤ ∑ p, ∑ q, ⟪e p, mapOfFunctional G (fun i => e i) (X p q) (e q)⟫_ℂ at h'
    rw [hq] at h'
    have h'' := (Complex.le_def.mp h').1
    change (0 : ℂ).re ≤ (F X + (δ : ℂ) * τ X).re at h''
    rw [Complex.zero_re, Complex.add_re, Complex.re_ofReal_mul] at h''
    linarith
  -- `P = φ 1 = φ_F 1 + δ • 1` is strictly positive
  have hP : φ 1 = mapOfFunctional F (fun i => e i) 1 + (δ : ℂ) • 1 := by
    refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => ?_
    have hG1 : ∀ i j, entryFunctional G i j 1 =
        entryFunctional F i j 1 + (δ : ℂ) * (if i = j then 1 else 0) := fun i j => by
      rw [← hτ1]
      rfl
    change ⟪x, mapOfFunctional G (fun i => e i) 1 y⟫_ℂ = _
    rw [_root_.add_apply, inner_add_right, inner_mapOfFunctional_apply,
      inner_mapOfFunctional_apply, _root_.smul_apply, inner_smul_right, one_apply_eq_self,
      ← e.sum_inner_mul_inner x y]
    simp only [hG1, add_mul, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.mul_sum]
  have hPpos : IsStrictlyPositive (φ 1) := by
    rw [hP]
    refine IsStrictlyPositive.nonneg_add
      (map_nonneg (completelyPositiveMapOfFunctional F hF fun i => e i) zero_le_one') ?_
    rw [show ((δ : ℂ) • 1 : B(ℂ^k)) =
      algebraMap ℝ _ δ by
        rw [Algebra.algebraMap_eq_smul_one]
        exact Complex.coe_smul δ (1 : B(ℂ^k))]
    exact isStrictlyPositive_algebraMap hδ
  -- `ψ = P^{-1/2} φ P^{-1/2}`
  set P := φ 1
  have hrpow : ∀ r : ℝ, (P ^ r)† = P ^ r := fun r => by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact (IsSelfAdjoint.of_nonneg CFC.rpow_nonneg).star_eq
  set T := P ^ (-(1 / 2) : ℝ)
  set S := P ^ (1 / 2 : ℝ)
  have hT : T† = T := hrpow _
  have hS : S† = S := hrpow _
  let ψ := (CompletelyPositiveMapClass'.toCompletelyPositiveMap'
    (ContinuousLinearMap.compressionCP T)).comp φ
  have hψ : ∀ a, ψ a = T * φ a * T := fun a => by
    change T† ∘L φ a ∘L T = _
    rw [hT]
    rfl
  refine ⟨ψ, ?_, fun h => hφX ?_⟩
  · rw [hψ]
    exact CFC.conjugate_rpow_neg_one_half P hPpos
  · have h' := (ContinuousLinearMap.compressionCP S).map_cstarMatrix_nonneg' k _ h
    convert h' using 1
    refine CStarMatrix.ext fun p q => ?_
    change φ (X p q) = S† ∘L ψ (X p q) ∘L S
    rw [hψ, hS]
    change φ (X p q) = S * (T * φ (X p q) * T) * S
    rw [show S * (T * φ (X p q) * T) * S = (S * T) * φ (X p q) * (T * S) by simp only [mul_assoc],
      CFC.rpow_mul_rpow_neg _ hPpos, CFC.rpow_neg_mul_rpow _ hPpos, one_mul, mul_one]

/-- **Unital completely positive maps into `B(ℂᵏ)` detect positivity.** A `k × k` matrix over an
operator system is positive exactly when its images under all unital completely positive maps
`V → B(ℂᵏ)` are. For a self-adjoint matrix that is not positive, such a map is built from a positive
functional separating it from the positive matrices. A matrix `X` that is not self-adjoint is excluded
through the self-adjoint matrix `i (X - X⋆)`, which every such map sends to `0`, since it sends `X` to
a positive, hence self-adjoint, matrix. -/
lemma nonneg_iff_forall_map_nonneg {k : ℕ} {X : CStarMatrix (Fin k) (Fin k) V} :
    0 ≤ X ↔ ∀ φ : V →CP' B(ℂ^k),
      φ 1 = 1 → 0 ≤ X.map φ := by
  refine ⟨fun hX φ _ => φ.map_cstarMatrix_nonneg hX, fun h => ?_⟩
  have hsa : ∀ Y : CStarMatrix (Fin k) (Fin k) V, IsSelfAdjoint Y →
      (∀ φ : V →CP' B(ℂ^k),
        φ 1 = 1 → 0 ≤ Y.map φ) → 0 ≤ Y := fun Y hY hYφ => by
    by_contra hY0
    obtain ⟨φ, hφ1, hφ⟩ := exists_completelyPositiveMap_not_nonneg hY hY0
    exact hφ (hYφ φ hφ1)
  refine hsa X ?_ h
  -- `Z = i (X - X⋆)` is self-adjoint and is sent to `0` by every unital completely positive `φ`
  set Z := Complex.I • (X - star X) with hZ_def
  have hZ : IsSelfAdjoint Z := by
    rw [IsSelfAdjoint, hZ_def, star_smul, star_sub, star_star, Complex.star_def, Complex.conj_I,
      neg_smul, ← smul_neg, neg_sub]
  have hZφ : ∀ φ : V →CP' B(ℂ^k),
      φ 1 = 1 → Z.map φ = 0 := fun φ hφ => by
    have hs := (IsSelfAdjoint.of_nonneg (h φ hφ)).star_eq
    refine CStarMatrix.ext fun p q => ?_
    have hpq : star (φ (X q p)) = φ (X p q) := congrFun (congrFun hs p) q
    change φ (Complex.I • (X p q - star (X q p))) = 0
    rw [map_smul, map_sub, map_star, hpq, sub_self, smul_zero]
  have h₁ := hsa Z hZ fun φ hφ => (hZφ φ hφ).symm ▸ le_rfl
  have h₂ := hsa (-Z) hZ.neg fun φ hφ => by
    refine le_of_eq (CStarMatrix.ext fun p q => ?_)
    change 0 = φ (-(Z p q))
    rw [map_neg, show φ (Z p q) = 0 from congrFun (congrFun (hZφ φ hφ) p) q, neg_zero]
  have hZ0 : Z = 0 := le_antisymm (neg_nonneg.mp h₂) h₁
  exact (sub_eq_zero.mp ((smul_eq_zero.mp hZ0).resolve_left Complex.I_ne_zero)).symm

end Separation

/-! ### The direct sum of the unital completely positive maps into `B(ℂⁿ)` -/

section DirectSum

variable (V) in
/-- The unital completely positive maps `V → B(ℂⁿ)`, for all `n`. -/
private abbrev UCP : Type u :=
  Σ n : ℕ, {φ : V →CP' B(ℂ^n) // φ 1 = 1}

variable (V) in
/-- The Hilbert sum `⨁ ℂⁿ` over the unital completely positive maps `V → B(ℂⁿ)`. -/
private abbrev DirectSumSpace : Type u :=
  ↥(lp (fun i : UCP V => EuclideanSpace ℂ (Fin i.1)) 2)

/-- The unital completely positive maps `V → B(ℂⁿ)` are bounded at `v` uniformly. -/
private lemma norm_apply_le (i : UCP V) (v : V) : ‖i.2.1 v‖ ≤ 3 * orderBound v := by
  have h := norm_apply_le_orderBound i.2.1 v
  rw [i.2.2] at h
  exact h.trans (mul_le_of_le_one_right (mul_nonneg (by norm_num) (orderBound_nonneg v))
    ContinuousLinearMap.norm_id_le)

variable (V) in
/-- The direct sum `v ↦ ⨁ φ(v)` of the unital completely positive maps `φ : V → B(ℂⁿ)`. -/
private def directSumMap : V →ₗ[ℂ] (DirectSumSpace V →L[ℂ] DirectSumSpace V) where
  toFun v := lp.mapCLM 2 (fun i : UCP V => i.2.1 v)
    (mul_nonneg (by norm_num) (orderBound_nonneg v)) fun i => norm_apply_le i v
  map_add' v w := ContinuousLinearMap.ext fun x => lp.ext (funext fun i => by
    simp only [lp.mapCLM_apply_coe, _root_.add_apply, lp.coeFn_add, Pi.add_apply, map_add])
  map_smul' c v := ContinuousLinearMap.ext fun x => lp.ext (funext fun i => by
    simp only [lp.mapCLM_apply_coe, _root_.smul_apply, lp.coeFn_smul, Pi.smul_apply, map_smul,
      RingHom.id_apply])

private lemma directSumMap_apply (v : V) (x : DirectSumSpace V) (i : UCP V) :
    (directSumMap V v x : ∀ i : UCP V, EuclideanSpace ℂ (Fin i.1)) i = i.2.1 v (x i) :=
  rfl

private lemma directSumMap_one : directSumMap V 1 = 1 :=
  ContinuousLinearMap.ext fun x => lp.ext (funext fun i => by
    rw [directSumMap_apply, i.2.2]
    rfl)

/-- The direct sum is completely positive: its quadratic form is the sum over the summands of the
quadratic forms of the `φ`. -/
private lemma map_directSumMap_nonneg {k : ℕ} {X : CStarMatrix (Fin k) (Fin k) V} (hX : 0 ≤ X) :
    0 ≤ X.map (directSumMap V) := by
  rw [nonneg_iff_sum_inner_apply_nonneg]
  intro ξ
  have hterm : ∀ p q, ⟪ξ p, X.map (directSumMap V) p q (ξ q)⟫_ℂ =
      ∑' i : UCP V, ⟪(ξ p : ∀ i : UCP V, EuclideanSpace ℂ (Fin i.1)) i,
        i.2.1 (X p q) ((ξ q : ∀ i : UCP V, EuclideanSpace ℂ (Fin i.1)) i)⟫_ℂ := fun p q => by
    rw [lp.inner_eq_tsum]
    rfl
  have hsum : ∀ p q, Summable fun i : UCP V => ⟪(ξ p : ∀ i : UCP V, EuclideanSpace ℂ (Fin i.1)) i,
      i.2.1 (X p q) ((ξ q : ∀ i : UCP V, EuclideanSpace ℂ (Fin i.1)) i)⟫_ℂ :=
    fun p q => lp.summable_inner (ξ p) (directSumMap V (X p q) (ξ q))
  simp only [hterm]
  rw [Finset.sum_congr rfl fun p _ => (Summable.tsum_finsetSum fun q _ => hsum p q).symm,
    ← Summable.tsum_finsetSum fun p _ => summable_sum fun q _ => hsum p q]
  exact tsum_nonneg fun i => nonneg_iff_sum_inner_apply_nonneg.mp
    (i.2.1.map_cstarMatrix_nonneg hX) _

/-- The positivity of `X.map j` for the direct sum `j` gives that of each `X.map φ`: the quadratic
form of `X.map φ` is that of `X.map j` at vectors in the summand of `φ`. -/
private lemma map_nonneg_of_map_directSumMap_nonneg (i : UCP V) {k : ℕ}
    {X : CStarMatrix (Fin k) (Fin k) V} (h : 0 ≤ X.map (directSumMap V)) : 0 ≤ X.map i.2.1 := by
  classical
  rw [nonneg_iff_sum_inner_apply_nonneg] at h ⊢
  intro η
  refine (h fun p => lp.single 2 i (η p)).trans_eq
    (Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_)
  change ⟪lp.single 2 i (η p), directSumMap V (X p q) (lp.single 2 i (η q))⟫_ℂ =
    ⟪η p, i.2.1 (X p q) (η q)⟫_ℂ
  rw [lp.inner_single_left, directSumMap_apply, lp.single_apply_self]

end DirectSum

variable (V) in
/-- **The Choi–Effros theorem.** Every operator system `V` is a concrete operator system: there are a
Hilbert space `H` and a unital complete order embedding `j : V → B(H)`, a linear map with
`0 ≤ X.map j ↔ 0 ≤ X` for every square matrix `X` over `V`. The map `j` is the direct sum of all unital
completely positive maps `V → B(ℂⁿ)`, which detect positivity
(`OperatorSystem.nonneg_iff_forall_map_nonneg`). -/
theorem exists_isCompleteOrderEmbedding :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (j : V →ₗ[ℂ] (H →L[ℂ] H)), j 1 = 1 ∧ j.IsCompleteOrderEmbedding :=
  ⟨DirectSumSpace V, inferInstance, inferInstance, inferInstance, directSumMap V, directSumMap_one,
    fun _ _ => ⟨fun h => nonneg_iff_forall_map_nonneg.mpr fun φ hφ =>
      map_nonneg_of_map_directSumMap_nonneg ⟨_, φ, hφ⟩ h, map_directSumMap_nonneg⟩⟩

variable (V) in
/-- **The Choi–Effros theorem**, with an operator subsystem: every operator system `V` is unitally
completely order isomorphic to an operator subsystem `S` of `B(H)` for some Hilbert space `H`, by a
linear isomorphism `e : V ≃ S` with `e 1 = 1` and `0 ≤ X.map e ↔ 0 ≤ X` for every square matrix `X`
over `V`; its inverse is then a complete order embedding too
(`LinearMap.IsCompleteOrderEmbedding.symm`). The subsystem is the range
(`CompletelyPositiveMap'.range`) of the map of `OperatorSystem.exists_isCompleteOrderEmbedding`, which
is injective (`LinearMap.IsCompleteOrderEmbedding.injective`) and a complete order embedding onto it
(`LinearMap.IsCompleteOrderEmbedding.rangeRestrict`). -/
theorem exists_linearEquiv_operatorSubsystem :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (S : OperatorSubsystem (H →L[ℂ] H)) (e : V ≃ₗ[ℂ] S),
        e 1 = 1 ∧ (e : V →ₗ[ℂ] S).IsCompleteOrderEmbedding := by
  obtain ⟨H, _, _, _, j, hj1, hj⟩ := exists_isCompleteOrderEmbedding V
  exact ⟨H, inferInstance, inferInstance, inferInstance, hj.toCompletelyPositiveMap'.range hj1,
    LinearEquiv.ofInjective j hj.injective, Subtype.ext hj1, hj.rangeRestrict⟩

end OperatorSystem
