/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.lpSpace
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.RCLike.Extend
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import QuantumSystem.Analysis.CStarAlgebra.GelfandNaimark
public import QuantumSystem.Analysis.OperatorSpace.CompletelyBounded

/-!
# Ruan's theorem

Every operator space `V`, a complex normed space with matrix norms satisfying Ruan's axioms
(`OperatorSpace`), is completely isometric to a space of operators on a Hilbert space
(`OperatorSpace.exists_isCompleteIsometry`).

For `X₀ ∈ M_n(V)`, the Hahn–Banach theorem at level `n` gives a functional `f` on `M_n(V)` with
`‖f X‖ ≤ ‖X‖` and `f X₀ = ‖X₀‖`. Separating the convex cone of the triples
`(a a⋆, b⋆ b, re f(a Y b))`, `‖Y‖ ≤ 1`, from the open cone `(‖A‖ + ‖B‖)/2 < c` gives positive
semidefinite matrices `ρ₁, ρ₂` of trace at most `1` with `re f(a Y b) ≤ (tr(a⋆ ρ₁ a) + tr(b ρ₂ b⋆))/2`
(`OperatorSpace.exists_posSemidef_of_norm_le`); that the triples form a convex cone uses the direct sums
`[a₁ a₂] (Y₁ ⊕ Y₂) [b₁; b₂]`. With `Rᵢ = (ρᵢ + δ)^{-1/2}`, the map `ψ : V → B(ℂⁿ)` with
`⟪u, ψ(v) w⟫ = f(R₁ ū v wᵀ R₂)` is completely contractive and `‖X₀‖ ≤ (1 + n δ) ‖ψₙ(X₀)‖`
(`OperatorSpace.exists_completelyContractive_norm_le`), and a compactness argument removes the factor
`1 + n δ` (`OperatorSpace.exists_completelyContractive_norm_eq`). The direct sum of all complete contractions
`V → B(ℂⁿ)`, into the ℓ∞-product of the `B(ℂⁿ)`, is then a complete isometry, and the Gelfand–Naimark
theorem represents the product on a Hilbert space.

## Main results

* `OperatorSpace.exists_functional_norm_le` — the Hahn–Banach theorem at a matrix level.
* `OperatorSpace.exists_posSemidef_of_norm_le` — the separation by a pair of positive semidefinite
  matrices of trace at most `1`.
* `OperatorSpace.exists_completelyContractive_norm_le` — complete contractions into `B(ℂⁿ)` attain the
  norms of `M_n(V)` up to a factor `1 + n δ`.
* `OperatorSpace.exists_completelyContractive_norm_eq` — the norms of `M_n(V)` are attained by complete
  contractions into `B(ℂⁿ)`.
* `OperatorSpace.exists_isCompleteIsometry` — **Ruan's theorem**.
-/

@[expose] public noncomputable section

open scoped CStarAlgebra ComplexOrder InnerProductSpace MatrixOrder ComplexConjugate Matrix ENNReal
open CStarMatrix

universe u

namespace OperatorSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [∀ k, Norm (CStarMatrix (Fin k) (Fin k) V)] [OperatorSpace V]

/-! ### The Hahn–Banach theorem at a matrix level -/

section HahnBanach

variable (V) in
/-- The matrix space `M_n(V)`, to be given its operator space norm as a normed space. -/
private def MatrixLevel (n : ℕ) : Type _ := CStarMatrix (Fin n) (Fin n) V

private instance (n : ℕ) : AddCommGroup (MatrixLevel V n) :=
  inferInstanceAs (AddCommGroup (CStarMatrix (Fin n) (Fin n) V))

private instance (n : ℕ) : Module ℂ (MatrixLevel V n) :=
  inferInstanceAs (Module ℂ (CStarMatrix (Fin n) (Fin n) V))

private instance (n : ℕ) : Norm (MatrixLevel V n) :=
  inferInstanceAs (Norm (CStarMatrix (Fin n) (Fin n) V))

private lemma matrixLevelCore (n : ℕ) : NormedSpace.Core ℂ (MatrixLevel V n) where
  norm_nonneg X := norm_nonneg (X : CStarMatrix (Fin n) (Fin n) V)
  norm_smul c X := norm_smul c (X : CStarMatrix (Fin n) (Fin n) V)
  norm_triangle X Y := norm_add_le (X : CStarMatrix (Fin n) (Fin n) V) Y
  norm_eq_zero_iff _ := ⟨eq_zero_of_norm_eq_zero, fun h => h ▸ norm_zero⟩

private instance (n : ℕ) : NormedAddCommGroup (MatrixLevel V n) := .ofCore (matrixLevelCore n)

private instance (n : ℕ) : NormedSpace ℂ (MatrixLevel V n) := .ofCore (matrixLevelCore n)

/-- **The Hahn–Banach theorem at a matrix level.** For `X₀ ∈ M_n(V)` there is a functional `f` on
`M_n(V)` with `‖f X‖ ≤ ‖X‖` and `f X₀ = ‖X₀‖`. -/
lemma exists_functional_norm_le {n : ℕ} (X₀ : CStarMatrix (Fin n) (Fin n) V) :
    ∃ f : CStarMatrix (Fin n) (Fin n) V →ₗ[ℂ] ℂ, (∀ X, ‖f X‖ ≤ ‖X‖) ∧ f X₀ = ‖X₀‖ := by
  rcases eq_or_ne ‖X₀‖ 0 with h | h
  · exact ⟨0, fun X => by simpa using norm_nonneg X, by rw [h]; simp⟩
  · let Y₀ : MatrixLevel V n := X₀
    obtain ⟨g, hg, hgX⟩ := exists_dual_vector ℂ Y₀ h
    refine ⟨(g : MatrixLevel V n →ₗ[ℂ] ℂ), fun X => ?_, hgX⟩
    have := g.le_opNorm (show MatrixLevel V n from X)
    rw [hg, one_mul] at this
    exact this

end HahnBanach

/-! ### Direct sums of scalar multiplications -/

section DirectSum

variable {n m₁ m₂ : ℕ}

/-- The block row `[a₁ a₂]` of two `n × mᵢ` matrices, indexing `Fin (m₁ + m₂)` by `finSumFinEquiv`. -/
private abbrev blockRow (a₁ : Matrix (Fin n) (Fin m₁) ℂ) (a₂ : Matrix (Fin n) (Fin m₂) ℂ) :
    Matrix (Fin n) (Fin (m₁ + m₂)) ℂ :=
  (Matrix.fromCols a₁ a₂).reindex (Equiv.refl _) finSumFinEquiv

/-- The block column `[b₁; b₂]` of two `mᵢ × n` matrices, indexing `Fin (m₁ + m₂)` by
`finSumFinEquiv`. -/
private abbrev blockCol (b₁ : Matrix (Fin m₁) (Fin n) ℂ) (b₂ : Matrix (Fin m₂) (Fin n) ℂ) :
    Matrix (Fin (m₁ + m₂)) (Fin n) ℂ :=
  (Matrix.fromRows b₁ b₂).reindex finSumFinEquiv (Equiv.refl _)

private lemma blockRow_mul_conjTranspose (a₁ : Matrix (Fin n) (Fin m₁) ℂ)
    (a₂ : Matrix (Fin n) (Fin m₂) ℂ) :
    blockRow a₁ a₂ * (blockRow a₁ a₂)ᴴ = a₁ * a₁ᴴ + a₂ * a₂ᴴ := by
  ext i j
  simp [Matrix.mul_apply, Fin.sum_univ_add]

private lemma conjTranspose_blockCol_mul (b₁ : Matrix (Fin m₁) (Fin n) ℂ)
    (b₂ : Matrix (Fin m₂) (Fin n) ℂ) :
    (blockCol b₁ b₂)ᴴ * blockCol b₁ b₂ = b₁ᴴ * b₁ + b₂ᴴ * b₂ := by
  ext i j
  simp [Matrix.mul_apply, Fin.sum_univ_add]

omit [NormedAddCommGroup V] [NormedSpace ℂ V] [∀ k, Norm (CStarMatrix (Fin k) (Fin k) V)]
  [OperatorSpace V] in
private lemma scalarMul_blockRow_blockCol [AddCommGroup V] [Module ℂ V]
    (a₁ : Matrix (Fin n) (Fin m₁) ℂ) (a₂ : Matrix (Fin n) (Fin m₂) ℂ)
    (b₁ : Matrix (Fin m₁) (Fin n) ℂ) (b₂ : Matrix (Fin m₂) (Fin n) ℂ)
    (Y₁ : CStarMatrix (Fin m₁) (Fin m₁) V) (Y₂ : CStarMatrix (Fin m₂) (Fin m₂) V) :
    scalarMul (blockRow a₁ a₂) (blockCol b₁ b₂) (directSum Y₁ Y₂) =
      scalarMul a₁ b₁ Y₁ + scalarMul a₂ b₂ Y₂ := by
  ext i j
  simp [scalarMul_apply, Fin.sum_univ_add, directSum, ofMatrix_apply, Finset.sum_add_distrib]

end DirectSum

/-! ### Representing real functionals by Hermitian matrices -/

section Trace

variable {n : ℕ}

/-- A real-linear functional `ℓ` on complex `n × n` matrices agrees on Hermitian matrices with
`A ↦ tr(ρ A)` for a Hermitian `ρ`: the Hermitian part of the matrix of its complex extension. -/
private lemma exists_isHermitian_trace_mul_eq (ℓ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℝ) :
    ∃ ρ : Matrix (Fin n) (Fin n) ℂ, ρ.IsHermitian ∧
      ∀ A : Matrix (Fin n) (Fin n) ℂ, A.IsHermitian → (ρ * A).trace = ℓ A := by
  classical
  let ω : Module.Dual ℂ (Matrix (Fin n) (Fin n) ℂ) := Module.Dual.extendRCLike ℓ
  let ρ₀ : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => ω (Matrix.single j i 1)
  have hω : ∀ A, ω A = (ρ₀ * A).trace := fun A => by
    conv_lhs => rw [Matrix.matrix_eq_sum_single A]
    simp only [map_sum, Matrix.trace, Matrix.diag, Matrix.mul_apply, ρ₀, Matrix.of_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h : Matrix.single j i (A j i) = A j i • Matrix.single j i (1 : ℂ) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [h, map_smul, smul_eq_mul, mul_comm]
  refine ⟨(1 / 2 : ℂ) • (ρ₀ + ρ₀ᴴ), ?_, fun A hA => ?_⟩
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_conjTranspose, add_comm]
    congr 1
    simp
  · have hstar : (ρ₀ᴴ * A).trace = star (ρ₀ * A).trace := by
      rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA.eq, Matrix.trace_mul_comm]
    rw [Matrix.smul_mul, Matrix.trace_smul, Matrix.add_mul, Matrix.trace_add, hstar, ← hω]
    have hre : (ω A).re = ℓ A := by
      have := Module.Dual.re_extendRCLike_apply (𝕜 := ℂ) ℓ A
      rwa [RCLike.re_to_complex] at this
    apply Complex.ext <;> simp [hre]
    ring

/-- `x⋆ ρ x` is the trace of `ρ x x⋆`. -/
private lemma star_dotProduct_mulVec_eq_trace (ρ : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    star x ⬝ᵥ (ρ *ᵥ x) = (ρ * ((Matrix.of fun i (_ : Fin 1) => x i) *
      (Matrix.of fun i (_ : Fin 1) => x i)ᴴ)).trace := by
  simp only [dotProduct, Matrix.mulVec, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_one, Finset.mul_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Trace

/-! ### The separation argument -/

section Separation

variable {n : ℕ}

/-- The ambient real vector space `M_n × M_n × ℝ` of the separation. -/
private abbrev Triple (n : ℕ) := Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × ℝ

variable (f : CStarMatrix (Fin n) (Fin n) V →ₗ[ℂ] ℂ)

/-- The triples `(a a⋆, b⋆ b, re f(a Y b))` with `‖Y‖ ≤ 1`. -/
private def triples : Set (Triple n) :=
  {w | ∃ (m : ℕ) (a : Matrix (Fin n) (Fin m) ℂ) (b : Matrix (Fin m) (Fin n) ℂ)
    (Y : CStarMatrix (Fin m) (Fin m) V), ‖Y‖ ≤ 1 ∧
      w = (a * aᴴ, bᴴ * b, (f (scalarMul a b Y)).re)}

/-- The open cone `(‖A‖ + ‖B‖) / 2 < c`, for the operator norms of `A` and `B`. -/
private def normCone (n : ℕ) : Set (Triple n) :=
  {w | (‖ofMatrix w.1‖ +
    ‖ofMatrix w.2.1‖) / 2 < w.2.2}

omit [OperatorSpace V] in
private lemma smul_mem_triples {c : ℝ} (hc : 0 ≤ c) {w : Triple n} (hw : w ∈ triples f) :
    c • w ∈ triples f := by
  obtain ⟨m, a, b, Y, hY, rfl⟩ := hw
  let s : ℂ := (Real.sqrt c : ℝ)
  have hs : s * s = (c : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc]
  have hss : star s = s := Complex.conj_ofReal _
  refine ⟨m, s • a, s • b, Y, hY, ?_⟩
  simp only [Prod.smul_mk, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hss,
    scalarMul_smul_smul, map_smul, smul_eq_mul, hs, Complex.re_ofReal_mul,
    RCLike.real_smul_eq_coe_smul (K := ℂ) c]
  rfl

private lemma add_mem_triples {w₁ w₂ : Triple n} (h₁ : w₁ ∈ triples f) (h₂ : w₂ ∈ triples f) :
    w₁ + w₂ ∈ triples f := by
  obtain ⟨m₁, a₁, b₁, Y₁, hY₁, rfl⟩ := h₁
  obtain ⟨m₂, a₂, b₂, Y₂, hY₂, rfl⟩ := h₂
  refine ⟨m₁ + m₂, blockRow a₁ a₂, blockCol b₁ b₂, directSum Y₁ Y₂,
    (norm_directSum Y₁ Y₂).trans_le (max_le hY₁ hY₂), ?_⟩
  rw [blockRow_mul_conjTranspose, conjTranspose_blockCol_mul, scalarMul_blockRow_blockCol, map_add,
    Complex.add_re]
  rfl

private lemma zero_mem_triples : (0 : Triple n) ∈ triples f :=
  ⟨0, 0, 0, 0, by rw [norm_zero]; exact zero_le_one, by ext <;> simp⟩

private lemma convex_triples : Convex ℝ (triples f) :=
  convex_iff_forall_pos.mpr fun _ hx _ hy _ _ ha hb _ =>
    add_mem_triples f (smul_mem_triples f ha.le hx) (smul_mem_triples f hb.le hy)

/-- The operator norm of a complex matrix, as a function of the matrix. -/
private lemma continuous_norm_ofMatrix :
    Continuous fun A : Matrix (Fin n) (Fin n) ℂ => ‖ofMatrix A‖ :=
  continuous_norm.comp (ofMatrixL (A := ℂ) (m := Fin n) (n := Fin n)).continuous

private lemma norm_ofMatrix_real_smul (c : ℝ) (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖ofMatrix (c • A)‖ =
      |c| * ‖ofMatrix A‖ := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) c A]
  change ‖(c : ℂ) • (ofMatrix A : CStarMatrix (Fin n) (Fin n) ℂ)‖ = _
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]

private lemma isOpen_normCone : IsOpen (normCone n) :=
  isOpen_lt (((continuous_norm_ofMatrix.comp continuous_fst).add
    (continuous_norm_ofMatrix.comp (continuous_fst.comp continuous_snd))).div_const 2)
    (continuous_snd.comp continuous_snd)

private lemma convex_normCone : Convex ℝ (normCone n) := by
  refine convex_iff_forall_pos.mpr fun x hx y hy a b ha hb hab => ?_
  have h₁ : ∀ A B : Matrix (Fin n) (Fin n) ℂ, ‖ofMatrix (a • A + b • B)‖ ≤
      a * ‖ofMatrix A‖ +
        b * ‖ofMatrix B‖ := fun A B => by
    refine (norm_add_le (ofMatrix (a • A)) (ofMatrix (b • B))).trans_eq ?_
    rw [norm_ofMatrix_real_smul, norm_ofMatrix_real_smul, abs_of_pos ha, abs_of_pos hb]
  change (‖ofMatrix (a • x.1 + b • y.1)‖ +
    ‖ofMatrix (a • x.2.1 + b • y.2.1)‖) / 2 < a * x.2.2 + b * y.2.2
  have hx' : (‖ofMatrix x.1‖ +
      ‖ofMatrix x.2.1‖) / 2 < x.2.2 := hx
  have hy' : (‖ofMatrix y.1‖ +
      ‖ofMatrix y.2.1‖) / 2 < y.2.2 := hy
  nlinarith [h₁ x.1 y.1, h₁ x.2.1 y.2.1]

private lemma disjoint_normCone_triples (hf : ∀ X, ‖f X‖ ≤ ‖X‖) : Disjoint (normCone n) (triples f) := by
  refine Set.disjoint_left.mpr fun w hwN hwD => ?_
  obtain ⟨m, a, b, Y, hY, rfl⟩ := hwD
  change (‖ofMatrix (a * aᴴ)‖ +
    ‖ofMatrix (bᴴ * b)‖) / 2 <
      (f (scalarMul a b Y)).re at hwN
  set α := ‖ofMatrix (a * aᴴ)‖
  set β := ‖ofMatrix (bᴴ * b)‖
  have hsq := norm_scalarMul_sq_le a b Y
  have hY' : ‖Y‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hY
  have hα : 0 ≤ α := norm_nonneg _
  have hβ : 0 ≤ β := norm_nonneg _
  have hre : (f (scalarMul a b Y)).re ≤ ‖scalarMul a b Y‖ :=
    (Complex.re_le_norm _).trans (hf _)
  have h₂ : ‖scalarMul a b Y‖ ^ 2 ≤ ((α + β) / 2) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hY' hα, sq_nonneg (α - β), mul_nonneg hα hβ]
  have h₃ : ‖scalarMul a b Y‖ ≤ (α + β) / 2 :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h₂
  linarith

/-- The identity matrix has operator norm at most `1`. -/
private lemma norm_ofMatrix_one_le : ‖(ofMatrix 1 : CStarMatrix (Fin n) (Fin n) ℂ)‖ ≤ 1 :=
  CStarMatrix.norm_one_le (Fin n) ℂ

/-- The separating functionals: real-linear `ℓ₁, ℓ₂` that are positive on `a a⋆` and `b⋆ b`, at most
`1` at the identity, and satisfy `re f(a Y b) ≤ (ℓ₁(a a⋆) + ℓ₂(b⋆ b)) / 2` for `‖Y‖ ≤ 1`. -/
private lemma exists_functionals_of_norm_le (hf : ∀ X, ‖f X‖ ≤ ‖X‖) :
    ∃ ℓ₁ ℓ₂ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℝ,
      (∀ (m : ℕ) (a : Matrix (Fin n) (Fin m) ℂ), 0 ≤ ℓ₁ (a * aᴴ)) ∧
      (∀ (m : ℕ) (b : Matrix (Fin m) (Fin n) ℂ), 0 ≤ ℓ₂ (bᴴ * b)) ∧ ℓ₁ 1 ≤ 1 ∧ ℓ₂ 1 ≤ 1 ∧
      ∀ (m : ℕ) (a : Matrix (Fin n) (Fin m) ℂ) (b : Matrix (Fin m) (Fin n) ℂ)
        (Y : CStarMatrix (Fin m) (Fin m) V), ‖Y‖ ≤ 1 →
          (f (scalarMul a b Y)).re ≤ (ℓ₁ (a * aᴴ) + ℓ₂ (bᴴ * b)) / 2 := by
  obtain ⟨L, u, hN, hD⟩ := geometric_hahn_banach_open convex_normCone isOpen_normCone
    (convex_triples f) (disjoint_normCone_triples f hf)
  have hu : u ≤ 0 := by simpa using hD 0 (zero_mem_triples f)
  have h001 : (0, 0, 1) ∈ normCone n := by
    change (‖(ofMatrix 0 : CStarMatrix (Fin n) (Fin n) ℂ)‖ +
      ‖(ofMatrix 0 : CStarMatrix (Fin n) (Fin n) ℂ)‖) / 2 < 1
    rw [show (ofMatrix 0 : CStarMatrix (Fin n) (Fin n) ℂ) = 0 from rfl, norm_zero]
    norm_num
  set t := -L (0, 0, 1)
  have ht : 0 < t := by linarith [hN _ h001]
  -- `L` is nonnegative on the cone of triples
  have hDpos : ∀ w ∈ triples f, 0 ≤ L w := fun w hw => by
    by_contra h
    rw [not_le] at h
    have hc : 0 ≤ u / L w + 1 := by
      have : 0 ≤ u / L w := div_nonneg_of_nonpos hu h.le
      linarith
    have := hD _ (smul_mem_triples f hc hw)
    rw [map_smul, smul_eq_mul, add_mul, div_mul_cancel₀ _ h.ne, one_mul] at this
    linarith
  have hsplit : ∀ (A B : Matrix (Fin n) (Fin n) ℂ) (c : ℝ), L (A, B, c) = L (A, 0, 0) + L (0, B, 0) - t * c :=
    fun A B c => by
      have : ((A, B, c) : Triple n) = (A, 0, 0) + (0, B, 0) + c • (0, 0, 1) := by
        ext <;> simp
      rw [this, map_add, map_add, map_smul, smul_eq_mul]
      ring
  -- the bound on the open cone
  have hNle : ∀ A B : Matrix (Fin n) (Fin n) ℂ, L (A, 0, 0) + L (0, B, 0) ≤
      t * ((‖ofMatrix A‖ +
        ‖ofMatrix B‖) / 2) := fun A B => by
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    have hmem : (A, B, (‖ofMatrix A‖ +
        ‖ofMatrix B‖) / 2 + ε / t) ∈ normCone n := by
      change _ < _
      linarith [div_pos hε ht]
    have := hN _ hmem
    rw [hsplit, mul_add, mul_div_cancel₀ _ ht.ne'] at this
    linarith
  let ℓ₁ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℝ := (2 / t) • (L.toLinearMap ∘ₗ LinearMap.inl ℝ _ _)
  let ℓ₂ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℝ :=
    (2 / t) • (L.toLinearMap ∘ₗ LinearMap.inr ℝ _ _ ∘ₗ LinearMap.inl ℝ _ _)
  have hℓ₁ : ∀ A, ℓ₁ A = 2 / t * L (A, 0, 0) := fun A => rfl
  have hℓ₂ : ∀ B, ℓ₂ B = 2 / t * L (0, B, 0) := fun B => rfl
  have h2t : 0 < 2 / t := div_pos two_pos ht
  have hL0 : L ((0 : Matrix (Fin n) (Fin n) ℂ), (0 : Matrix (Fin n) (Fin n) ℂ), (0 : ℝ)) = 0 := map_zero L
  have hn0 : ‖(ofMatrix 0 : CStarMatrix (Fin n) (Fin n) ℂ)‖ = 0 := norm_zero
  refine ⟨ℓ₁, ℓ₂, fun m a => ?_, fun m b => ?_, ?_, ?_, fun m a b Y hY => ?_⟩
  · have h := hDpos _ ⟨m, a, 0, 0, by rw [norm_zero]; exact zero_le_one, rfl⟩
    simp only [Matrix.conjTranspose_zero, Matrix.zero_mul, map_zero, Complex.zero_re] at h
    rw [hℓ₁]
    exact mul_nonneg h2t.le h
  · have h := hDpos _ ⟨m, 0, b, 0, by rw [norm_zero]; exact zero_le_one, rfl⟩
    simp only [Matrix.conjTranspose_zero, Matrix.zero_mul, map_zero, Complex.zero_re] at h
    rw [hℓ₂]
    exact mul_nonneg h2t.le h
  · have h := hNle 1 0
    rw [hL0, add_zero, hn0, add_zero] at h
    rw [hℓ₁]
    calc 2 / t * L (1, 0, 0) ≤ 2 / t * (t * (‖(ofMatrix 1 : CStarMatrix (Fin n) (Fin n) ℂ)‖ / 2)) :=
          mul_le_mul_of_nonneg_left h h2t.le
      _ = ‖(ofMatrix 1 : CStarMatrix (Fin n) (Fin n) ℂ)‖ := by field_simp
      _ ≤ 1 := norm_ofMatrix_one_le
  · have h := hNle 0 1
    rw [hL0, zero_add, hn0, zero_add] at h
    rw [hℓ₂]
    calc 2 / t * L (0, 1, 0) ≤ 2 / t * (t * (‖(ofMatrix 1 : CStarMatrix (Fin n) (Fin n) ℂ)‖ / 2)) :=
          mul_le_mul_of_nonneg_left h h2t.le
      _ = ‖(ofMatrix 1 : CStarMatrix (Fin n) (Fin n) ℂ)‖ := by field_simp
      _ ≤ 1 := norm_ofMatrix_one_le
  · have h := hDpos _ ⟨m, a, b, Y, hY, rfl⟩
    rw [hsplit] at h
    rw [hℓ₁, hℓ₂]
    have : t * (f (scalarMul a b Y)).re ≤ L (a * aᴴ, 0, 0) + L (0, bᴴ * b, 0) := by
      linarith
    rw [show (2 / t * L (a * aᴴ, 0, 0) + 2 / t * L (0, bᴴ * b, 0)) / 2 =
      (L (a * aᴴ, 0, 0) + L (0, bᴴ * b, 0)) / t by field_simp, le_div_iff₀ ht]
    linarith

/-- **Separation by positive semidefinite matrices of trace at most `1`.** For a functional `f` on
`M_n(V)` with `‖f X‖ ≤ ‖X‖`, there are positive semidefinite matrices `ρ₁, ρ₂` of trace at most `1` with
`re f(a Y b) ≤ (tr(a⋆ ρ₁ a) + tr(b ρ₂ b⋆)) / 2` whenever `‖Y‖ ≤ 1`, for all scalar matrices `a`, `b` of
any compatible sizes. Here `0 ≤ ρ` is the Loewner order of `open scoped MatrixOrder`
(`Matrix.nonneg_iff_posSemidef`) and `ρ.trace ≤ 1` the order of `open scoped ComplexOrder`, which for
positive semidefinite `ρ` says `re (tr ρ) ≤ 1`. -/
lemma exists_posSemidef_of_norm_le (hf : ∀ X, ‖f X‖ ≤ ‖X‖) :
    ∃ ρ₁ ρ₂ : Matrix (Fin n) (Fin n) ℂ, 0 ≤ ρ₁ ∧ 0 ≤ ρ₂ ∧ ρ₁.trace ≤ 1 ∧ ρ₂.trace ≤ 1 ∧
      ∀ (m : ℕ) (a : Matrix (Fin n) (Fin m) ℂ) (b : Matrix (Fin m) (Fin n) ℂ)
        (Y : CStarMatrix (Fin m) (Fin m) V), ‖Y‖ ≤ 1 →
          (f (scalarMul a b Y)).re ≤ ((aᴴ * ρ₁ * a).trace.re + (b * ρ₂ * bᴴ).trace.re) / 2 := by
  obtain ⟨ℓ₁, ℓ₂, hℓ₁, hℓ₂, h₁, h₂, h⟩ := exists_functionals_of_norm_le f hf
  obtain ⟨ρ₁, hρ₁, hρ₁ℓ⟩ := exists_isHermitian_trace_mul_eq ℓ₁
  obtain ⟨ρ₂, hρ₂, hρ₂ℓ⟩ := exists_isHermitian_trace_mul_eq ℓ₂
  have hpsd : ∀ {ρ : Matrix (Fin n) (Fin n) ℂ} {ℓ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℝ}, ρ.IsHermitian →
      (∀ A : Matrix (Fin n) (Fin n) ℂ, A.IsHermitian → (ρ * A).trace = ℓ A) →
      (∀ (m : ℕ) (a : Matrix (Fin n) (Fin m) ℂ), 0 ≤ ℓ (a * aᴴ)) → 0 ≤ ρ :=
    fun hρ hρℓ hℓ => (Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hρ fun x => by
      rw [star_dotProduct_mulVec_eq_trace, hρℓ _ (Matrix.isHermitian_mul_conjTranspose_self _)]
      exact Complex.zero_le_real.mpr (hℓ 1 _)).nonneg
  refine ⟨ρ₁, ρ₂, hpsd hρ₁ hρ₁ℓ hℓ₁, hpsd hρ₂ hρ₂ℓ fun m a => by simpa using hℓ₂ m aᴴ, ?_, ?_,
    fun m a b Y hY => ?_⟩
  · rw [← mul_one ρ₁, hρ₁ℓ 1 Matrix.isHermitian_one, ← Complex.ofReal_one]
    exact Complex.real_le_real.mpr h₁
  · rw [← mul_one ρ₂, hρ₂ℓ 1 Matrix.isHermitian_one, ← Complex.ofReal_one]
    exact Complex.real_le_real.mpr h₂
  · have e₁ : (aᴴ * ρ₁ * a).trace = (ρ₁ * (a * aᴴ)).trace := by
      rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
    have e₂ : (b * ρ₂ * bᴴ).trace = (ρ₂ * (bᴴ * b)).trace := by
      rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
    rw [e₁, e₂, hρ₁ℓ _ (Matrix.isHermitian_mul_conjTranspose_self a),
      hρ₂ℓ _ (Matrix.isHermitian_conjTranspose_mul_self b), Complex.ofReal_re, Complex.ofReal_re]
    exact h m a b Y hY

end Separation

/-! ### Complete contractions attaining the norms -/

section Contraction

variable {n : ℕ}

omit [NormedAddCommGroup V] [NormedSpace ℂ V] [∀ k, Norm (CStarMatrix (Fin k) (Fin k) V)]
  [OperatorSpace V] in
/-- `a Y b` is the sum over the entries `Y p q` of the rank-one matrices `(a k p b q l Y p q)ₖₗ`. -/
private lemma scalarMul_eq_sum [AddCommGroup V] [Module ℂ V] {m : ℕ} (a : Matrix (Fin n) (Fin m) ℂ)
    (b : Matrix (Fin m) (Fin n) ℂ) (Y : CStarMatrix (Fin m) (Fin m) V) :
    scalarMul a b Y = ∑ p, ∑ q, ofMatrix (Matrix.of fun k l => (a k p * b q l) • Y p q) := by
  ext k l
  simp [scalarMul_apply, CStarMatrix.sum_apply, ofMatrix_apply]

variable (f : CStarMatrix (Fin n) (Fin n) V →ₗ[ℂ] ℂ) (r₁ r₂ : Matrix (Fin n) (Fin n) ℂ)

/-- The matrix `(f((r₁ₖᵢ r₂ⱼₗ v)ₖₗ))ᵢⱼ` of the operator `ψ(v)`. -/
private def gMatrix : V →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun v := Matrix.of fun i j => f (ofMatrix (Matrix.of fun k l => (r₁ k i * r₂ j l) • v))
  map_add' v w := by
    ext i j
    rw [Matrix.add_apply, Matrix.of_apply, Matrix.of_apply, Matrix.of_apply, ← map_add]
    congr 1
    ext k l
    simp [ofMatrix_apply, smul_add]
  map_smul' c v := by
    ext i j
    rw [Matrix.smul_apply, Matrix.of_apply, Matrix.of_apply, RingHom.id_apply, smul_eq_mul, ← smul_eq_mul,
      ← map_smul]
    congr 1
    ext k l
    simp [ofMatrix_apply, smul_smul, mul_comm c]

/-- The map `ψ : V → B(ℂⁿ)` with `⟪u, ψ(v) w⟫ = f(r₁ ū v wᵀ r₂)`. -/
private def psiMap : V →ₗ[ℂ] (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) where
  toFun v := Matrix.toEuclideanCLM (𝕜 := ℂ) (gMatrix f r₁ r₂ v)
  map_add' v w := by rw [map_add, map_add]
  map_smul' c v := by rw [map_smul, map_smul, RingHom.id_apply]

/-- The `n × m` matrix `(conj ηₚᵢ)ᵢₚ` of a vector of `(ℂⁿ)ᵐ`. -/
private def conjCoords {m : ℕ} (η : PiLp 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n))) :
    Matrix (Fin n) (Fin m) ℂ :=
  Matrix.of fun i p => conj ((η.ofLp p).ofLp i)

/-- The `m × n` matrix `(ξ_qₗ)_qₗ` of a vector of `(ℂⁿ)ᵐ`. -/
private def coords {m : ℕ} (ξ : PiLp 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n))) :
    Matrix (Fin m) (Fin n) ℂ :=
  Matrix.of fun q l => (ξ.ofLp q).ofLp l

omit [∀ k, Norm (CStarMatrix (Fin k) (Fin k) V)] [OperatorSpace V] in
/-- The matrix coefficients of `ψₘ(Y)` are `⟪η, ψₘ(Y) ξ⟫ = f(a Y b)` for `a = r₁ η̄` and `b = ξ r₂`. -/
private lemma inner_toPiLp_map {m : ℕ} (Y : CStarMatrix (Fin m) (Fin m) V)
    (η ξ : PiLp 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n))) :
    ⟪η, toPiLpStarAlgEquiv (Fin m) (EuclideanSpace ℂ (Fin n)) (Y.map (psiMap f r₁ r₂)) ξ⟫_ℂ =
      f (scalarMul (r₁ * conjCoords η) (coords ξ * r₂) Y) := by
  rw [scalarMul_eq_sum, map_sum, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [toPiLpStarAlgEquiv_apply, inner_sum, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hmat : (ofMatrix (Matrix.of fun k l => ((r₁ * conjCoords η) k p * (coords ξ * r₂) q l) • Y p q) :
      CStarMatrix (Fin n) (Fin n) V) = ∑ i, ∑ j, (conj ((η.ofLp p).ofLp i) * (ξ.ofLp q).ofLp j) •
        ofMatrix (Matrix.of fun k l => (r₁ k i * r₂ j l) • Y p q) := by
    ext k l
    simp only [CStarMatrix.sum_apply, ofMatrix_apply, Matrix.of_apply, Matrix.mul_apply, conjCoords, coords,
      CStarMatrix.smul_apply, smul_smul, Finset.sum_mul, Finset.mul_sum, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    congr 1
    ring
  rw [hmat]
  simp only [map_sum, map_smul, smul_eq_mul]
  change ⟪η.ofLp p, Matrix.toEuclideanCLM (𝕜 := ℂ) (gMatrix f r₁ r₂ (Y p q)) (ξ.ofLp q)⟫_ℂ = _
  rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanCLM]
  simp only [dotProduct, Matrix.mulVec, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [gMatrix, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply, Pi.star_apply, Complex.star_def]
  ring


omit [NormedAddCommGroup V] [NormedSpace ℂ V] [∀ k, Norm (CStarMatrix (Fin k) (Fin k) V)]
  [OperatorSpace V] in
/-- `‖η‖² = tr(η̄⋆ η̄)`. -/
private lemma norm_sq_eq_trace_conjCoords {m : ℕ} (η : PiLp 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n))) :
    ‖η‖ ^ 2 = ((conjCoords η)ᴴ * conjCoords η).trace.re := by
  simp only [PiLp.norm_sq_eq_of_L2, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    conjCoords, Matrix.of_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_conj, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

omit [NormedAddCommGroup V] [NormedSpace ℂ V] [∀ k, Norm (CStarMatrix (Fin k) (Fin k) V)]
  [OperatorSpace V] in
/-- `‖ξ‖² = tr(ξ ξ⋆)`. -/
private lemma norm_sq_eq_trace_coords {m : ℕ} (ξ : PiLp 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n))) :
    ‖ξ‖ ^ 2 = (coords ξ * (coords ξ)ᴴ).trace.re := by
  simp only [PiLp.norm_sq_eq_of_L2, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    coords, Matrix.of_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

omit [NormedAddCommGroup V] [NormedSpace ℂ V] [∀ k, Norm (CStarMatrix (Fin k) (Fin k) V)]
  [OperatorSpace V] in
/-- For a positive semidefinite `ρ` and `δ > 0`, a Hermitian square root `s` of `ρ + δ` is invertible,
with `r = s⁻¹`. -/
private lemma exists_sqrt_inv {ρ : Matrix (Fin n) (Fin n) ℂ} (hρ : ρ.PosSemidef) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r s : Matrix (Fin n) (Fin n) ℂ, r * s = 1 ∧ s * r = 1 ∧ s * s = ρ + (δ : ℂ) • 1 ∧
      rᴴ = r ∧ sᴴ = s := by
  have hρ' : 0 ≤ (ofMatrix ρ : CStarMatrix (Fin n) (Fin n) ℂ) := by
    have h := (map_le_map_iff (CStarMatrix.ofMatrixStarAlgEquiv (n := Fin n) (A := ℂ))).mpr
      (Matrix.nonneg_iff_posSemidef.mpr hρ)
    rwa [map_zero] at h
  have hP := isStrictlyPositive_add_smul_one hρ' hδ
  have hu := hP.isUnit_cfcSqrt
  set P := (ofMatrix ρ : CStarMatrix (Fin n) (Fin n) ℂ) + (δ : ℂ) • 1
  exact ⟨ofMatrix.symm (Ring.inverse (CFC.sqrt P)), ofMatrix.symm (CFC.sqrt P),
    congrArg ofMatrix.symm (Ring.inverse_mul_cancel _ hu),
    congrArg ofMatrix.symm (Ring.mul_inverse_cancel _ hu),
    congrArg ofMatrix.symm (CFC.sqrt_mul_sqrt_self P hP.nonneg),
    congrArg ofMatrix.symm (hP.sqrt.ringInverse).isSelfAdjoint.star_eq,
    congrArg ofMatrix.symm (CFC.sqrt_nonneg P).isSelfAdjoint.star_eq⟩

omit [NormedAddCommGroup V] [NormedSpace ℂ V] [∀ k, Norm (CStarMatrix (Fin k) (Fin k) V)]
  [OperatorSpace V] in
/-- `tr((r η̄)⋆ ρ (r η̄)) ≤ ‖η‖²` for `r = (ρ + δ)^{-1/2}`. -/
private lemma trace_conjCoords_le {ρ r s : Matrix (Fin n) (Fin n) ℂ} {δ : ℝ} (hδ : 0 ≤ δ) (hrs : r * s = 1)
    (hsr : s * r = 1) (hss : s * s = ρ + (δ : ℂ) • 1) (hr : rᴴ = r) {m : ℕ}
    (η : PiLp 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n))) :
    ((r * conjCoords η)ᴴ * ρ * (r * conjCoords η)).trace.re ≤ ‖η‖ ^ 2 := by
  set A := r * conjCoords η
  have h₁ : Aᴴ * (s * s) * A = (conjCoords η)ᴴ * conjCoords η := by
    rw [Matrix.conjTranspose_mul, hr]
    calc (conjCoords η)ᴴ * r * (s * s) * (r * conjCoords η)
        = (conjCoords η)ᴴ * (r * s) * (s * r) * conjCoords η := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hrs, hsr, Matrix.mul_one, Matrix.mul_one]
  have h₂ : Aᴴ * ρ * A = Aᴴ * (s * s) * A - (δ : ℂ) • (Aᴴ * A) := by
    rw [hss, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    abel
  have h₃ : 0 ≤ (Aᴴ * A).trace.re :=
    Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self A).trace_nonneg |>.1
  rw [h₂, h₁, Matrix.trace_sub, Matrix.trace_smul, Complex.sub_re, smul_eq_mul, Complex.re_ofReal_mul,
    ← norm_sq_eq_trace_conjCoords]
  nlinarith

omit [NormedAddCommGroup V] [NormedSpace ℂ V] [∀ k, Norm (CStarMatrix (Fin k) (Fin k) V)]
  [OperatorSpace V] in
/-- `tr((ξ r) ρ (ξ r)⋆) ≤ ‖ξ‖²` for `r = (ρ + δ)^{-1/2}`. -/
private lemma trace_coords_le {ρ r s : Matrix (Fin n) (Fin n) ℂ} {δ : ℝ} (hδ : 0 ≤ δ) (hrs : r * s = 1)
    (hsr : s * r = 1) (hss : s * s = ρ + (δ : ℂ) • 1) (hr : rᴴ = r) {m : ℕ}
    (ξ : PiLp 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n))) :
    ((coords ξ * r) * ρ * (coords ξ * r)ᴴ).trace.re ≤ ‖ξ‖ ^ 2 := by
  set B := coords ξ * r
  have h₁ : B * (s * s) * Bᴴ = coords ξ * (coords ξ)ᴴ := by
    rw [Matrix.conjTranspose_mul, hr]
    calc coords ξ * r * (s * s) * (r * (coords ξ)ᴴ)
        = coords ξ * (r * s) * (s * r) * (coords ξ)ᴴ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hrs, hsr, Matrix.mul_one, Matrix.mul_one]
  have h₂ : B * ρ * Bᴴ = B * (s * s) * Bᴴ - (δ : ℂ) • (B * Bᴴ) := by
    rw [hss, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    abel
  have h₃ : 0 ≤ (B * Bᴴ).trace.re :=
    Complex.nonneg_iff.mp (Matrix.posSemidef_self_mul_conjTranspose B).trace_nonneg |>.1
  rw [h₂, h₁, Matrix.trace_sub, Matrix.trace_smul, Complex.sub_re, smul_eq_mul, Complex.re_ofReal_mul,
    ← norm_sq_eq_trace_coords]
  nlinarith

omit [NormedAddCommGroup V] [NormedSpace ℂ V] [∀ k, Norm (CStarMatrix (Fin k) (Fin k) V)]
  [OperatorSpace V] in
/-- The ⋆-isomorphism `M_m(B(H)) ≃ B(Hᵐ)` is isometric. -/
private lemma norm_toPiLpStarAlgEquiv {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {m : ℕ} (Y : CStarMatrix (Fin m) (Fin m) (H →L[ℂ] H)) :
    ‖toPiLpStarAlgEquiv (Fin m) H Y‖ = ‖Y‖ :=
  NonUnitalStarAlgHom.norm_map (toPiLpStarAlgEquiv (Fin m) H)
    (toPiLpStarAlgEquiv (Fin m) H).injective Y

/-- **Complete contractions nearly attaining the norms.** For `X₀ ∈ M_n(V)` and `δ > 0` there is a
complete contraction `ψ : V → B(ℂⁿ)` with `‖X₀‖ ≤ (1 + n δ) ‖ψₙ(X₀)‖`. With the functional `f` and the
matrices `ρᵢ` of `OperatorSpace.exists_posSemidef_of_norm_le`, `ψ` is the map with
`⟪u, ψ(v) w⟫ = f(R₁ ū v wᵀ R₂)` for `Rᵢ = (ρᵢ + δ)^{-1/2}`. -/
lemma exists_completelyContractive_norm_le (X₀ : CStarMatrix (Fin n) (Fin n) V) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ψ : V →CB (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)), ‖ψ‖ ≤ 1 ∧
      ‖X₀‖ ≤ (1 + n * δ) * ‖X₀.map ψ‖ := by
  obtain ⟨f, hf, hfX⟩ := exists_functional_norm_le X₀
  obtain ⟨ρ₁, ρ₂, hρ₁, hρ₂, htr₁, htr₂, hineq⟩ := exists_posSemidef_of_norm_le f hf
  obtain ⟨r₁, s₁, hrs₁, hsr₁, hss₁, hr₁, hs₁⟩ := exists_sqrt_inv (Matrix.nonneg_iff_posSemidef.mp hρ₁) hδ
  obtain ⟨r₂, s₂, hrs₂, hsr₂, hss₂, hr₂, hs₂⟩ := exists_sqrt_inv (Matrix.nonneg_iff_posSemidef.mp hρ₂) hδ
  let ψ₀ := psiMap f r₁ r₂
  have hnorm : ∀ {m : ℕ} (Y : CStarMatrix (Fin m) (Fin m) (EuclideanSpace ℂ (Fin n) →L[ℂ]
      EuclideanSpace ℂ (Fin n))), ‖toPiLpStarAlgEquiv (Fin m) (EuclideanSpace ℂ (Fin n)) Y‖ = ‖Y‖ :=
    fun Y => norm_toPiLpStarAlgEquiv Y
  -- `re ⟪η, ψₘ(Y) ξ⟫ ≤ (‖η‖² + ‖ξ‖²) / 2` for `‖Y‖ ≤ 1`
  have hre : ∀ {m : ℕ} (Y : CStarMatrix (Fin m) (Fin m) V), ‖Y‖ ≤ 1 → ∀ η ξ,
      (⟪η, toPiLpStarAlgEquiv (Fin m) (EuclideanSpace ℂ (Fin n)) (Y.map ψ₀) ξ⟫_ℂ).re ≤
        (‖η‖ ^ 2 + ‖ξ‖ ^ 2) / 2 := fun Y hY η ξ => by
    rw [inner_toPiLp_map]
    refine (hineq _ _ _ Y hY).trans ?_
    have h₁ := trace_conjCoords_le hδ.le hrs₁ hsr₁ hss₁ hr₁ η
    have h₂ := trace_coords_le hδ.le hrs₂ hsr₂ hss₂ hr₂ ξ
    linarith
  -- hence `‖ψₘ(Y)‖ ≤ 1` for `‖Y‖ ≤ 1`
  have hcontr : ∀ {m : ℕ} (Y : CStarMatrix (Fin m) (Fin m) V), ‖Y‖ ≤ 1 → ‖Y.map ψ₀‖ ≤ 1 := fun Y hY => by
    rw [← hnorm]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun ξ => ?_
    set T := toPiLpStarAlgEquiv (Fin _) (EuclideanSpace ℂ (Fin n)) (Y.map ψ₀)
    rcases eq_or_ne ‖T ξ‖ 0 with h0 | h0
    · rw [h0, one_mul]
      exact _root_.norm_nonneg _
    have hξ : ‖ξ‖ ≠ 0 := fun h => h0 (by
      rw [norm_eq_zero.mp h, map_zero, _root_.norm_zero])
    have hTξ := (_root_.norm_nonneg (T ξ)).lt_of_ne' h0
    let c : ℝ := ‖ξ‖ / ‖T ξ‖
    have hη : ‖(c : ℂ) • T ξ‖ = ‖ξ‖ := by
      rw [_root_.norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity), div_mul_cancel₀ _ h0]
    have hinner : (⟪(c : ℂ) • T ξ, T ξ⟫_ℂ).re = ‖ξ‖ * ‖T ξ‖ := by
      rw [inner_smul_left, Complex.conj_ofReal, inner_self_eq_norm_sq_to_K]
      change ((c : ℂ) * ((‖T ξ‖ : ℂ) ^ 2)).re = _
      rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
      change ‖ξ‖ / ‖T ξ‖ * ‖T ξ‖ ^ 2 = ‖ξ‖ * ‖T ξ‖
      field_simp
    have h := hre Y hY ((c : ℂ) • T ξ) ξ
    rw [hinner, hη] at h
    rw [one_mul]
    nlinarith [(_root_.norm_nonneg ξ).lt_of_ne' hξ]
  -- `ψ` is completely contractive
  have hbound : ∀ (k : ℕ) (X : CStarMatrix (Fin k) (Fin k) V), ‖X.map ψ₀‖ ≤ 1 * ‖X‖ := fun k X => by
    rw [one_mul]
    rcases (norm_nonneg X).eq_or_lt with h | h
    · rw [show X.map ψ₀ = 0 by
        rw [eq_zero_of_norm_eq_zero h.symm]
        exact CStarMatrix.ext fun _ _ => map_zero ψ₀, _root_.norm_zero]
      exact norm_nonneg X
    · have hY : ‖((‖X‖⁻¹ : ℝ) : ℂ) • X‖ ≤ 1 := by
        rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity), inv_mul_cancel₀ h.ne']
      have h' := hcontr _ hY
      rw [show (((‖X‖⁻¹ : ℝ) : ℂ) • X).map ψ₀ = ((‖X‖⁻¹ : ℝ) : ℂ) • X.map ψ₀ from
        CStarMatrix.ext fun _ _ => map_smul ψ₀ _ _, _root_.norm_smul, Complex.norm_real,
        Real.norm_of_nonneg (by positivity), inv_mul_le_iff₀ h, mul_one] at h'
      exact h'
  let ψ : V →CB (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) := ⟨ψ₀, ⟨1, hbound⟩⟩
  refine ⟨ψ, CompletelyBoundedMap.norm_le_bound _ zero_le_one hbound, ?_⟩
  -- the lower bound at `X₀`, with `r₁ η̄₀ = 1` and `ξ₀ r₂ = 1`
  let η₀ : PiLp 2 (fun _ : Fin n => EuclideanSpace ℂ (Fin n)) :=
    WithLp.toLp 2 fun p => WithLp.toLp 2 fun i => conj (s₁ i p)
  let ξ₀ : PiLp 2 (fun _ : Fin n => EuclideanSpace ℂ (Fin n)) :=
    WithLp.toLp 2 fun q => WithLp.toLp 2 fun l => s₂ q l
  have hη₀ : conjCoords η₀ = s₁ := by
    ext i p
    simp [conjCoords, η₀]
  have hξ₀ : coords ξ₀ = s₂ := by
    ext q l
    simp [coords, ξ₀]
  set T := toPiLpStarAlgEquiv (Fin n) (EuclideanSpace ℂ (Fin n)) (X₀.map ψ)
  have hX₀ : ⟪η₀, T ξ₀⟫_ℂ = ‖X₀‖ := by
    rw [show T = toPiLpStarAlgEquiv (Fin n) (EuclideanSpace ℂ (Fin n)) (X₀.map ψ₀) from rfl,
      inner_toPiLp_map, hη₀, hξ₀, hrs₁, hsr₂, scalarMul_one_one, hfX]
  have htrace : ∀ {s ρ : Matrix (Fin n) (Fin n) ℂ}, s * s = ρ + (δ : ℂ) • 1 → ρ.trace ≤ 1 →
      (s * s).trace.re ≤ 1 + n * δ := fun {_ ρ} hss htr => by
    have htr : ρ.trace.re ≤ 1 := (Complex.le_def.mp htr).1
    rw [hss, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, Complex.add_re, smul_eq_mul,
      Complex.re_ofReal_mul, Fintype.card_fin, Complex.natCast_re]
    linarith
  have hnη : ‖η₀‖ ^ 2 ≤ 1 + n * δ := by
    rw [norm_sq_eq_trace_conjCoords, hη₀, hs₁]
    exact htrace hss₁ htr₁
  have hnξ : ‖ξ₀‖ ^ 2 ≤ 1 + n * δ := by
    rw [norm_sq_eq_trace_coords, hξ₀, hs₂]
    exact htrace hss₂ htr₂
  have hle : ‖X₀‖ ≤ ‖η₀‖ * (‖T‖ * ‖ξ₀‖) := by
    have h := norm_inner_le_norm (𝕜 := ℂ) η₀ (T ξ₀)
    rw [hX₀, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg X₀)] at h
    exact h.trans (mul_le_mul_of_nonneg_left (T.le_opNorm ξ₀) (_root_.norm_nonneg _))
  rw [← hnorm]
  change ‖X₀‖ ≤ (1 + n * δ) * ‖T‖
  nlinarith [_root_.norm_nonneg η₀, _root_.norm_nonneg ξ₀, _root_.norm_nonneg T, sq_nonneg (‖η₀‖ - ‖ξ₀‖),
    mul_nonneg (_root_.norm_nonneg T) (sq_nonneg (‖η₀‖ - ‖ξ₀‖))]

/-- **Complete contractions attaining the norms.** For `X₀ ∈ M_n(V)` there is a complete contraction
`ψ : V → B(ℂⁿ)` with `‖ψₙ(X₀)‖ = ‖X₀‖`. The complete contractions `V → B(ℂⁿ)` form a compact set for
pointwise convergence, a closed subset of `∏ᵥ {T : ‖T‖ ≤ ‖v‖}`, on which `ψ ↦ ‖ψₙ(X₀)‖` attains its
supremum; by `OperatorSpace.exists_completelyContractive_norm_le` the supremum is `‖X₀‖`. -/
lemma exists_completelyContractive_norm_eq (X₀ : CStarMatrix (Fin n) (Fin n) V) :
    ∃ ψ : V →CB (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)), ‖ψ‖ ≤ 1 ∧
      ‖X₀.map ψ‖ = ‖X₀‖ := by
  let B := EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)
  have : ProperSpace B := FiniteDimensional.proper ℂ B
  -- continuity of `g ↦ X.map g` for the product topology
  have hcont : ∀ {k : ℕ} (X : CStarMatrix (Fin k) (Fin k) V),
      Continuous fun g : V → B => ‖X.map g‖ := fun X =>
    continuous_norm.comp ((ofMatrixL (A := B) (m := Fin _) (n := Fin _)).continuous.comp
      (continuous_pi fun p => continuous_pi fun q => continuous_apply (X p q)))
  -- the complete contractions, as functions
  let C : Set (V → B) := {g | (∀ v w, g (v + w) = g v + g w) ∧ (∀ (c : ℂ) v, g (c • v) = c • g v) ∧
    ∀ (k : ℕ) (X : CStarMatrix (Fin k) (Fin k) V), ‖X.map g‖ ≤ ‖X‖}
  have hC : IsClosed C := by
    simp only [C, Set.ofPred_and, Set.ofPred_forall]
    exact (isClosed_iInter fun v => isClosed_iInter fun w => isClosed_eq (continuous_apply (v + w))
      ((continuous_apply v).add (continuous_apply w))).inter ((isClosed_iInter fun c : ℂ =>
        isClosed_iInter fun v => isClosed_eq (continuous_apply (c • v))
          ((continuous_apply v).const_smul c)).inter
      (isClosed_iInter fun k => isClosed_iInter fun X => isClosed_le (hcont X) continuous_const))
  have hCK : C ⊆ Set.univ.pi fun v => Metric.closedBall (0 : B) ‖v‖ := fun g hg v _ => by
    have h := hg.2.2 1 (single₁ v)
    rw [show (single₁ v).map g = single₁ (g v) from rfl, norm_single₁, norm_single₁] at h
    exact mem_closedBall_zero_iff.mpr h
  have hCc : IsCompact C :=
    (isCompact_univ_pi fun v => isCompact_closedBall _ _).of_isClosed_subset hC hCK
  have h0 : (0 : V → B) ∈ C := ⟨fun _ _ => (add_zero (0 : B)).symm,
    fun c _ => (smul_zero (A := B) c).symm, fun k X => by
    rw [show X.map (0 : V → B) = 0 from rfl, _root_.norm_zero]
    exact norm_nonneg X⟩
  obtain ⟨g, hg, hmax⟩ := hCc.exists_isMaxOn ⟨0, h0⟩ (hcont X₀).continuousOn
  let ψ : V →CB B := ⟨⟨⟨g, hg.1⟩, hg.2.1⟩, ⟨1, fun k X => (hg.2.2 k X).trans_eq (one_mul _).symm⟩⟩
  refine ⟨ψ, CompletelyBoundedMap.norm_le_bound _ zero_le_one fun k X =>
    (hg.2.2 k X).trans_eq (one_mul _).symm, le_antisymm (hg.2.2 n X₀) ?_⟩
  -- `‖X₀‖ ≤ (1 + n δ) ‖ψₙ(X₀)‖` for every `δ > 0`
  set M := ‖X₀.map ψ‖
  have hM : 0 ≤ M := _root_.norm_nonneg _
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hδ : 0 < ε / (n * M + 1) := div_pos hε (by positivity)
  obtain ⟨φ, hφ, hX⟩ := exists_completelyContractive_norm_le X₀ hδ
  have hφC : (φ : V → B) ∈ C := ⟨map_add φ, map_smul φ, fun k X =>
    (φ.norm_map_cstarMatrix_le X).trans (mul_le_of_le_one_left (norm_nonneg X) hφ)⟩
  have hle : ‖X₀.map φ‖ ≤ M := hmax hφC
  calc ‖X₀‖ ≤ (1 + n * (ε / (n * M + 1))) * ‖X₀.map φ‖ := hX
    _ ≤ (1 + n * (ε / (n * M + 1))) * M := by gcongr
    _ = M + ε * (n * M / (n * M + 1)) := by field_simp
    _ ≤ M + ε * 1 := by
        gcongr
        exact (div_le_one (by positivity)).mpr (by linarith)
    _ = M + ε := by rw [mul_one]

end Contraction

/-! ### Ruan's theorem -/

section Ruan

variable (V) in
/-- The complete contractions `V → B(ℂⁿ)`, for all `n`. -/
private abbrev Contraction :=
  Σ n : ℕ, {ψ : V →CB (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) // ‖ψ‖ ≤ 1}

/-- The algebra `B(ℂⁿ)` of the codomain of a complete contraction `V → B(ℂⁿ)`. -/
private def Op (i : Contraction V) : Type :=
  EuclideanSpace ℂ (Fin i.1) →L[ℂ] EuclideanSpace ℂ (Fin i.1)

private instance (i : Contraction V) : CStarAlgebra (Op i) :=
  inferInstanceAs (CStarAlgebra (EuclideanSpace ℂ (Fin i.1) →L[ℂ] EuclideanSpace ℂ (Fin i.1)))

private instance (i : Contraction V) : PartialOrder (Op i) :=
  inferInstanceAs (PartialOrder (EuclideanSpace ℂ (Fin i.1) →L[ℂ] EuclideanSpace ℂ (Fin i.1)))

private instance (i : Contraction V) : StarOrderedRing (Op i) :=
  inferInstanceAs (StarOrderedRing (EuclideanSpace ℂ (Fin i.1) →L[ℂ] EuclideanSpace ℂ (Fin i.1)))

private instance : NonUnitalCStarAlgebra (lp (fun i : Contraction V => Op i) ∞) := inferInstance

private instance : PartialOrder (lp (fun i : Contraction V => Op i) ∞) := CStarAlgebra.spectralOrder _

private instance : StarOrderedRing (lp (fun i : Contraction V => Op i) ∞) :=
  CStarAlgebra.spectralOrderedRing _

private instance (k : ℕ) :
    NonUnitalCStarAlgebra (lp (fun i : Contraction V => CStarMatrix (Fin k) (Fin k) (Op i)) ∞) :=
  inferInstance

variable (V) in
/-- The direct sum `v ↦ (ψ v)_ψ` of all complete contractions `ψ : V → B(ℂⁿ)`, into the ℓ∞-product. -/
private def directSumMap : V →ₗ[ℂ] lp (fun i : Contraction V => Op i) ∞ where
  toFun v := ⟨fun i => show Op i from i.2.1 v, memℓp_infty ⟨‖v‖, by
    rintro _ ⟨i, rfl⟩
    exact (i.2.1.norm_apply_le v).trans (mul_le_of_le_one_left (_root_.norm_nonneg v) i.2.2)⟩⟩
  map_add' v w := lp.ext (funext fun i => map_add i.2.1 v w)
  map_smul' c v := lp.ext (funext fun i => map_smul i.2.1 c v)

/-- The coordinate `x ↦ xᵢ` of the ℓ∞-product, as a ⋆-homomorphism. -/
private def evalHom (i : Contraction V) : lp (fun i : Contraction V => Op i) ∞ →⋆ₙₐ[ℂ] Op i where
  toFun x := x i
  map_smul' c x := by rw [lp.coeFn_smul]; rfl
  map_zero' := by rw [lp.coeFn_zero]; rfl
  map_add' x y := by rw [lp.coeFn_add]; rfl
  map_mul' x y := by rw [lp.infty_coeFn_mul]; rfl
  map_star' x := lp.star_apply x i

/-- The matrix levels of the ℓ∞-product: `X ↦ (X.map evᵢ)ᵢ` into the ℓ∞-product of the matrix
algebras, an injective ⋆-homomorphism. -/
private def matrixProd (k : ℕ) :
    CStarMatrix (Fin k) (Fin k) (lp (fun i : Contraction V => Op i) ∞) →⋆ₙₐ[ℂ]
      lp (fun i : Contraction V => CStarMatrix (Fin k) (Fin k) (Op i)) ∞ where
  toFun X := ⟨fun i => mapₙₐ (evalHom i) X, memℓp_infty ⟨‖X‖, by
    rintro _ ⟨i, rfl⟩
    exact NonUnitalStarAlgHom.norm_apply_le (mapₙₐ (evalHom i)) X⟩⟩
  map_smul' c X := lp.ext (funext fun i => map_smul (mapₙₐ (evalHom i)) c X)
  map_zero' := lp.ext (funext fun i => map_zero (mapₙₐ (evalHom i)))
  map_add' X Y := lp.ext (funext fun i => map_add (mapₙₐ (evalHom i)) X Y)
  map_mul' X Y := by
    refine lp.ext (funext fun i => ?_)
    rw [lp.infty_coeFn_mul]
    exact map_mul (mapₙₐ (evalHom i)) X Y
  map_star' X := by
    refine lp.ext (funext fun i => ?_)
    rw [lp.coeFn_star]
    exact map_star (mapₙₐ (evalHom i)) X

omit [OperatorSpace V] in
private lemma matrixProd_injective (k : ℕ) :
    Function.Injective (matrixProd k : CStarMatrix (Fin k) (Fin k) (lp (fun i : Contraction V => Op i) ∞) → _) := by
  intro X Y h
  refine CStarMatrix.ext fun p q => lp.ext (funext fun i => ?_)
  have := congrFun (congrFun (congrFun (congrArg (⇑) h) i) p) q
  exact this

/-- **The direct sum of the complete contractions is a complete isometry.** Each `ψ` bounds
`‖ψₖ(X)‖ ≤ ‖X‖`, and `OperatorSpace.exists_completelyContractive_norm_eq` attains `‖X‖`. -/
private lemma isCompleteIsometry_directSumMap : IsCompleteIsometry (directSumMap V) := by
  intro k X
  have hmap : ∀ i : Contraction V, mapₙₐ (evalHom i) (X.map (directSumMap V)) = X.map i.2.1 := fun i =>
    rfl
  refine le_antisymm ?_ ?_
  · rw [← NonUnitalStarAlgHom.norm_map (matrixProd k) (matrixProd_injective k)]
    refine lp.norm_le_of_forall_le (norm_nonneg X) fun i => ?_
    change ‖mapₙₐ (evalHom i) (X.map (directSumMap V))‖ ≤ ‖X‖
    rw [hmap]
    exact (i.2.1.norm_map_cstarMatrix_le X).trans (mul_le_of_le_one_left (norm_nonneg X) i.2.2)
  · obtain ⟨ψ, hψ, hX⟩ := exists_completelyContractive_norm_eq X
    rw [← hX, ← hmap ⟨k, ψ, hψ⟩]
    exact NonUnitalStarAlgHom.norm_apply_le _ _

end Ruan

/-- **Ruan's theorem.** Every operator space `V` is completely isometric to a space of operators on a
Hilbert space: there is a linear map `j : V → B(K)` with `‖X.map j‖ = ‖X‖` at every matrix level. The map
is the direct sum of all complete contractions `V → B(ℂⁿ)`, followed by a faithful representation of
their ℓ∞-product (`CStarRep.exists_isometric`). -/
theorem exists_isCompleteIsometry (V : Type u) [NormedAddCommGroup V] [NormedSpace ℂ V]
    [∀ k, Norm (CStarMatrix (Fin k) (Fin k) V)] [OperatorSpace V] :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (_ : CompleteSpace K)
      (j : V →ₗ[ℂ] (K →L[ℂ] K)), IsCompleteIsometry j := by
  obtain ⟨R, -, hinj, -⟩ := CStarRep.exists_isometric (lp (fun i : Contraction V => Op i) ∞)
  let j : V →ₗ[ℂ] (R.H →L[ℂ] R.H) :=
    { toFun := fun v => R.π (directSumMap V v)
      map_add' := fun v w => by rw [map_add, map_add]
      map_smul' := fun c v => by rw [map_smul, map_smul, RingHom.id_apply] }
  refine ⟨R.H, inferInstance, inferInstance, inferInstance, j, fun k X => ?_⟩
  have hπ : Function.Injective (mapₙₐ (n := Fin k) R.π) := fun M N h =>
    CStarMatrix.ext fun p q => hinj (congrFun (congrFun h p) q)
  have := NonUnitalStarAlgHom.norm_map (mapₙₐ (n := Fin k) R.π) hπ (X.map (directSumMap V))
  exact this.trans (isCompleteIsometry_directSumMap k X)

end OperatorSpace
