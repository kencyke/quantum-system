module

public import QuantumSystem.Analysis.CFC.Diagonal
public import QuantumSystem.Analysis.Matrix.PartialTrace
public import QuantumSystem.State

/-!
# Tensor product (Kronecker) of density matrices and bipartite Kronecker calculus

Given density matrices `ρ : DensityMatrix n` and `σ : DensityMatrix m`, we form
their tensor product `ρ ⊗ σ : DensityMatrix (n × m)` whose underlying matrix is
the Kronecker product of the underlying matrices. This is the bipartite product
state (independent-systems product state).

This file is the hub for **Kronecker-product calculus on bipartite matrices**:

* preservation of Hermitian / unitary structure under `⊗ₖ`,
* Kronecker spectral decomposition,
* the **log-tensor identity**
  `matrixLog (A ⊗ₖ B) = matrixLog A ⊗ₖ 1 + 1 ⊗ₖ matrixLog B` for PosDef `A`, `B`,
* the **equivalence-indexed partial trace** `partialTrace`
  (for `e : X ≃ A × B`, retain `A` and sum over `B`),
* and the **Heisenberg duality at product type**
  `Tr(ρ · (X ⊗ 1)) = Tr((partialTrace (Equiv.refl (n × m)) ρ) · X)` together with
  the symmetric `(1 ⊗ Y)` version.

The retained subsystem is determined by the codomain of the chosen equivalence
`e : X ≃ A × B`. For native product types, `partialTrace (Equiv.refl (n × m))`
retains the `n` factor, while `partialTrace (Equiv.prodComm n m)` retains the
`m` factor. LocalNet-facing theorems should instead expose the split subset
`Λ ⊆ Λ_total` (and its complement) explicitly, and use these matrix-level lemmas
only after reindexing by `LocalNet.combineIdx`.

The proof of the log-tensor identity uses the spectral decomposition of `A ⊗ B`
constructed explicitly from spectral decompositions of `A` and `B`, combined
with **spectral invariance** of `matrixFunction` (derived from
`Matrix.matrixFunction_eq_cfc` and `StarAlgHomClass.map_cfc` on the ⋆-algebra
automorphism given by conjugation by a unitary). Working via `matrixFunction`
(spectral, bare `Matrix n n ℂ`) instead of the `CStarMatrix` wrapper avoids the
instance diamond that blocked a previous `cfc`-only approach.

## Main definitions

* `DensityMatrix.kronecker` — tensor product of density matrices.
* `Matrix.partialTrace` — partial trace specified by an explicit bipartite equivalence.

## Main results

* `DensityMatrix.kronecker_toMatrix` — underlying-matrix unfolding.
* `Matrix.IsHermitian.kronecker` — Kronecker of Hermitian matrices is Hermitian.
* `Matrix.kronecker_eq_unitary_conj_diagonal` — Kronecker spectral decomposition.
* `Matrix.matrixLog_kronecker_posDef` — the log-tensor identity.
* `Matrix.partialTrace_apply` — entrywise unfolding of the equivalence-indexed partial trace.
* `Matrix.restrict_eq_partialTrace_combineIdx` /
  `Matrix.restrict_compl_eq_partialTrace_combineIdx` — LocalNet restriction as an
  equivalence-indexed partial trace.
* `Matrix.trace_mul_kronecker_one_right` —
  `Tr(ρ · (X ⊗ 1)) = Tr((partialTrace (Equiv.refl (n × m)) ρ) · X)`.
* `Matrix.trace_mul_kronecker_one_left`  —
  `Tr(ρ · (1 ⊗ Y)) = Tr((partialTrace (Equiv.prodComm n m) ρ) · Y)`.
-/

@[expose] public section

namespace Matrix

open scoped Kronecker MatrixOrder ComplexOrder

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-! ### Kronecker preserves Hermitian / unitary -/

omit [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] in
/-- The Kronecker product of two Hermitian matrices is Hermitian. -/
theorem IsHermitian.kronecker {A : Matrix n n ℂ} {B : Matrix m m ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : (A ⊗ₖ B).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_kronecker, hA.eq, hB.eq]

/-- If `U` and `V` are unitary (i.e. `Uᴴ * U = 1` and `Vᴴ * V = 1`), then so is
`U ⊗ₖ V`. This is the statement used internally; the `unitaryGroup`-membership
version is `Matrix.kronecker_mem_unitary` in Mathlib. -/
private lemma kronecker_conjTranspose_mul_self
    {U : Matrix n n ℂ} {V : Matrix m m ℂ}
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) :
    (U ⊗ₖ V)ᴴ * (U ⊗ₖ V) = 1 := by
  rw [conjTranspose_kronecker, ← mul_kronecker_mul, hU, hV, ← one_kronecker_one]

/-- Dual version: `(U ⊗ V)(U ⊗ V)ᴴ = 1`. -/
private lemma kronecker_mul_conjTranspose_self
    {U : Matrix n n ℂ} {V : Matrix m m ℂ}
    (hU : U * Uᴴ = 1) (hV : V * Vᴴ = 1) :
    (U ⊗ₖ V) * (U ⊗ₖ V)ᴴ = 1 := by
  rw [conjTranspose_kronecker, ← mul_kronecker_mul, hU, hV, ← one_kronecker_one]

/-! ### Kronecker spectral decomposition

Given spectral decompositions `A = U_A * diag λ * U_Aᴴ` and `B = U_B * diag μ * U_Bᴴ`,
the Kronecker product satisfies
  `A ⊗ₖ B = (U_A ⊗ U_B) * diag ((i,j) ↦ λ i * μ j) * (U_A ⊗ U_B)ᴴ`,
exhibiting `U_A ⊗ U_B` as a valid unitary diagonaliser of `A ⊗ B`. -/

/-- **Kronecker spectral decomposition.** If `A = U_A * D_A * U_Aᴴ` and
`B = U_B * D_B * U_Bᴴ` with `D_A = diagonal dA`, `D_B = diagonal dB`, then
`A ⊗ₖ B = (U_A ⊗ U_B) * diagonal (fun (i,j) => dA i * dB j) * (U_A ⊗ U_B)ᴴ`. -/
theorem kronecker_eq_unitary_conj_diagonal
    {U_A : Matrix n n ℂ} {U_B : Matrix m m ℂ}
    {dA : n → ℂ} {dB : m → ℂ}
    {A : Matrix n n ℂ} {B : Matrix m m ℂ}
    (hA : A = U_A * diagonal dA * U_Aᴴ)
    (hB : B = U_B * diagonal dB * U_Bᴴ) :
    A ⊗ₖ B =
      (U_A ⊗ₖ U_B) *
        diagonal (fun ij : n × m => dA ij.1 * dB ij.2) *
        (U_A ⊗ₖ U_B)ᴴ := by
  rw [hA, hB, conjTranspose_kronecker]
  -- Apply mul_kronecker_mul twice (forward) and diagonal_kronecker_diagonal
  rw [mul_kronecker_mul, mul_kronecker_mul, diagonal_kronecker_diagonal]

/-! ### Log-tensor identity -/

section LogTensor

/-- `matrixLog` of a unitary conjugate of a positive real diagonal is the same
unitary conjugation of the diagonal logarithm. Auxiliary for the log-tensor identity. -/
private lemma matrixLog_unitary_conj_diagonal
    {k : Type*} [Fintype k] [DecidableEq k]
    (W : unitary (Matrix k k ℂ)) (d : k → ℝ) (hd : ∀ i, 0 < d i)
    (hM : ((W : Matrix k k ℂ) * diagonal (fun i => ((d i : ℝ) : ℂ)) *
        (W : Matrix k k ℂ)ᴴ).IsHermitian) :
    matrixLog ((W : Matrix k k ℂ) * diagonal (fun i => ((d i : ℝ) : ℂ)) *
        (W : Matrix k k ℂ)ᴴ) hM =
      (W : Matrix k k ℂ) *
        diagonal (fun i => ((Real.log (d i) : ℝ) : ℂ)) * (W : Matrix k k ℂ)ᴴ := by
  unfold matrixLog
  rw [matrixFunction_eq_cfc]
  exact cfc_log_unitary_conj_diagonal W d hd

/-- **Log-tensor identity.** For positive-definite matrices `A` and `B`, the matrix
logarithm of the Kronecker product decomposes as the sum of tensor-embedded logs:
`matrixLog (A ⊗ₖ B) = matrixLog A ⊗ₖ 1 + 1 ⊗ₖ matrixLog B`. -/
theorem matrixLog_kronecker_posDef
    {A : Matrix n n ℂ} (hA : A.PosDef)
    {B : Matrix m m ℂ} (hB : B.PosDef) :
    matrixLog (A ⊗ₖ B) (IsHermitian.kronecker hA.1 hB.1) =
      matrixLog A hA.1 ⊗ₖ (1 : Matrix m m ℂ) +
        (1 : Matrix n n ℂ) ⊗ₖ matrixLog B hB.1 := by
  -- Spectral data
  set U_A := (hA.1.eigenvectorUnitary : Matrix n n ℂ) with hU_A_def
  set U_B := (hB.1.eigenvectorUnitary : Matrix m m ℂ) with hU_B_def
  set dA := hA.1.eigenvalues with hdA_def
  set dB := hB.1.eigenvalues with hdB_def
  -- PosDef → eigenvalues positive
  have hdA_pos : ∀ i, 0 < dA i := fun i => hA.eigenvalues_pos i
  have hdB_pos : ∀ j, 0 < dB j := fun j => hB.eigenvalues_pos j
  -- Unitarity
  have hUA_self : U_Aᴴ * U_A = 1 := by
    have := Unitary.coe_star_mul_self hA.1.eigenvectorUnitary
    simpa [star_eq_conjTranspose, hU_A_def] using this
  have hUA_self' : U_A * U_Aᴴ = 1 := by
    have := Unitary.coe_mul_star_self hA.1.eigenvectorUnitary
    simpa [star_eq_conjTranspose, hU_A_def] using this
  have hUB_self : U_Bᴴ * U_B = 1 := by
    have := Unitary.coe_star_mul_self hB.1.eigenvectorUnitary
    simpa [star_eq_conjTranspose, hU_B_def] using this
  have hUB_self' : U_B * U_Bᴴ = 1 := by
    have := Unitary.coe_mul_star_self hB.1.eigenvectorUnitary
    simpa [star_eq_conjTranspose, hU_B_def] using this
  -- Spectral decompositions
  have hA_decomp : A = U_A * diagonal (fun i => (dA i : ℂ)) * U_Aᴴ := by
    have h := hA.1.spectral_theorem (𝕜 := ℂ)
    rw [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose] at h
    exact h
  have hB_decomp : B = U_B * diagonal (fun j => (dB j : ℂ)) * U_Bᴴ := by
    have h := hB.1.spectral_theorem (𝕜 := ℂ)
    rw [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose] at h
    exact h
  -- Construct Kronecker unitary
  let W : unitary (Matrix (n × m) (n × m) ℂ) :=
    ⟨U_A ⊗ₖ U_B, by
      rw [Unitary.mem_iff, star_eq_conjTranspose]
      exact ⟨kronecker_conjTranspose_mul_self hUA_self hUB_self,
             kronecker_mul_conjTranspose_self hUA_self' hUB_self'⟩⟩
  have hW_val : (W : Matrix (n × m) (n × m) ℂ) = U_A ⊗ₖ U_B := rfl
  -- Kronecker spectral decomposition
  have hAB_decomp : A ⊗ₖ B = (W : Matrix (n × m) (n × m) ℂ) *
      diagonal (fun ij : n × m => (((dA ij.1 * dB ij.2 : ℝ) : ℂ))) *
      (W : Matrix (n × m) (n × m) ℂ)ᴴ := by
    rw [hW_val]
    have h := kronecker_eq_unitary_conj_diagonal hA_decomp hB_decomp
    rw [h]
    congr 1; congr 1
    funext ij; push_cast; ring
  -- Hermitianness of Kronecker
  have hAB_herm : (A ⊗ₖ B).IsHermitian := IsHermitian.kronecker hA.1 hB.1
  -- Positivity of the diagonal product
  have h_dA_dB_pos : ∀ ij : n × m, 0 < (dA ij.1 * dB ij.2 : ℝ) :=
    fun ij => mul_pos (hdA_pos ij.1) (hdB_pos ij.2)
  -- matrixLog of A ⊗ B via aux lemma
  have hAB_herm' : ((W : Matrix (n × m) (n × m) ℂ) *
      diagonal (fun ij : n × m => (((dA ij.1 * dB ij.2 : ℝ) : ℂ))) *
      (W : Matrix (n × m) (n × m) ℂ)ᴴ).IsHermitian := by
    rw [← hAB_decomp]; exact hAB_herm
  have h_matrixLog_AB :
      matrixLog (A ⊗ₖ B) hAB_herm =
        (W : Matrix (n × m) (n × m) ℂ) *
          diagonal (fun ij : n × m => ((Real.log (dA ij.1 * dB ij.2) : ℝ) : ℂ)) *
          (W : Matrix (n × m) (n × m) ℂ)ᴴ := by
    rw [show matrixLog (A ⊗ₖ B) hAB_herm =
        matrixLog ((W : Matrix (n × m) (n × m) ℂ) *
          diagonal (fun ij : n × m => (((dA ij.1 * dB ij.2 : ℝ) : ℂ))) *
          (W : Matrix (n × m) (n × m) ℂ)ᴴ) hAB_herm' from ?_]
    · exact matrixLog_unitary_conj_diagonal W
        (fun ij : n × m => (dA ij.1 * dB ij.2 : ℝ)) h_dA_dB_pos hAB_herm'
    · congr 1
  rw [h_matrixLog_AB]
  -- Split log(dA*dB) = log dA + log dB
  have h_log_split :
      diagonal (fun ij : n × m => ((Real.log (dA ij.1 * dB ij.2) : ℝ) : ℂ)) =
        diagonal (fun ij : n × m => ((Real.log (dA ij.1) : ℝ) : ℂ)) +
          diagonal (fun ij : n × m => ((Real.log (dB ij.2) : ℝ) : ℂ)) := by
    ext ij ij'
    by_cases h : ij = ij'
    · subst h
      simp only [diagonal_apply_eq, Matrix.add_apply, diagonal_apply_eq]
      rw [Real.log_mul (ne_of_gt (hdA_pos ij.1)) (ne_of_gt (hdB_pos ij.2))]
      push_cast; ring
    · simp only [Matrix.add_apply, diagonal_apply_ne _ h, add_zero]
  rw [h_log_split]
  -- Split each diagonal as Kronecker product
  have h_left_as_kronecker :
      diagonal (fun ij : n × m => ((Real.log (dA ij.1) : ℝ) : ℂ)) =
        diagonal (fun i => ((Real.log (dA i) : ℝ) : ℂ)) ⊗ₖ (1 : Matrix m m ℂ) := by
    rw [show (1 : Matrix m m ℂ) = diagonal (fun _ : m => (1 : ℂ)) from (diagonal_one).symm,
        diagonal_kronecker_diagonal]
    congr 1; funext ij; ring
  have h_right_as_kronecker :
      diagonal (fun ij : n × m => ((Real.log (dB ij.2) : ℝ) : ℂ)) =
        (1 : Matrix n n ℂ) ⊗ₖ diagonal (fun j => ((Real.log (dB j) : ℝ) : ℂ)) := by
    rw [show (1 : Matrix n n ℂ) = diagonal (fun _ : n => (1 : ℂ)) from (diagonal_one).symm,
        diagonal_kronecker_diagonal]
    congr 1; funext ij; ring
  rw [h_left_as_kronecker, h_right_as_kronecker]
  -- Distribute the conjugation over the sum
  rw [Matrix.mul_add, Matrix.add_mul, hW_val, conjTranspose_kronecker]
  -- Each term: (X ⊗ Y) * (P ⊗ Q) * (X' ⊗ Y') = (X * P * X') ⊗ (Y * Q * Y')
  -- Using ← mul_kronecker_mul twice per term
  rw [← mul_kronecker_mul, ← mul_kronecker_mul,
      ← mul_kronecker_mul, ← mul_kronecker_mul]
  -- Clean up: U_A * 1 * U_Aᴴ = 1, U_B * 1 * U_Bᴴ = 1
  rw [Matrix.mul_one U_A, hUA_self', Matrix.mul_one U_B, hUB_self']
  -- Now unfold matrixLog of A and B via their spectral decomposition
  rw [matrixLog_spectral_eq hA.1, matrixLog_spectral_eq hB.1]

end LogTensor

/-! ### Equivalence-indexed partial trace

For an explicit bipartite decomposition `e : X ≃ A × B`, `partialTrace e ρ`
retains the `A` factor and sums over the `B` factor. This makes the retained
subsystem part of the type of the decomposition, rather than something inferred
from names such as `A/B` or from left/right position. -/

section PartialTrace

variable {X A B : Type*} [Fintype B]

/-- **Partial trace along an explicit bipartite equivalence.** If `e : X ≃ A × B`, then
`partialTrace e ρ` is the matrix on the retained subsystem `A` obtained by summing out
the `B` factor. -/
noncomputable def partialTrace (e : X ≃ A × B) (ρ : Matrix X X ℂ) : Matrix A A ℂ :=
  Matrix.of fun a a' => ∑ b : B, ρ (e.symm (a, b)) (e.symm (a', b))

@[simp] lemma partialTrace_apply (e : X ≃ A × B) (ρ : Matrix X X ℂ) (a a' : A) :
  partialTrace e ρ a a' = ∑ b : B, ρ (e.symm (a, b)) (e.symm (a', b)) := rfl

end PartialTrace

omit [Fintype n] [DecidableEq n] [DecidableEq m] in
@[simp] lemma partialTrace_refl_apply (ρ : Matrix (n × m) (n × m) ℂ) (a a' : n) :
  partialTrace (A := n) (B := m) (Equiv.refl (n × m)) ρ a a' =
    ∑ b : m, ρ (a, b) (a', b) := rfl

omit [Fintype m] [DecidableEq n] [DecidableEq m] in
@[simp] lemma partialTrace_prodComm_apply (ρ : Matrix (n × m) (n × m) ℂ) (b b' : m) :
  partialTrace (A := m) (B := n) (Equiv.prodComm n m) ρ b b' =
    ∑ a : n, ρ (a, b) (a, b') := rfl

/-! ### LocalNet bridge

These lemmas identify `Matrix.restrict` on a `LocalNet` with the equivalence-indexed
partial trace of the reindexed matrix induced by `LocalNet.combineIdx`. -/

section LocalNetBridge

variable {L : LocalNet}

/-- Combining via `h : Λ ⊆ Λ_total` agrees with combining via the complementary split,
after transporting the remaining factor along `Λ_total \ (Λ_total \ Λ) = Λ`. -/
private lemma combineIdx_swap_apply
    {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    (x : L.regionIdx Λ) (y : L.regionIdx (Λ_total \ Λ)) :
    L.combineIdx h (x, y) =
      L.combineIdx Finset.sdiff_subset
        (y, L.regionIdxCongr (sdiff_sdiff_eq_self h).symm x) := by
  have h_eq : Λ_total \ (Λ_total \ Λ) = Λ := sdiff_sdiff_eq_self h
  funext ⟨s, hs⟩
  by_cases hsΛ : s ∈ Λ
  · have hns_compl : s ∉ Λ_total \ Λ := fun h_in => (Finset.mem_sdiff.mp h_in).2 hsΛ
    have hs_recast : s ∈ Λ_total \ (Λ_total \ Λ) := by
      rw [h_eq]
      exact hsΛ
    rw [LocalNet.combineIdx_apply_mem h _ _ ⟨s, hs⟩ hsΛ,
        LocalNet.combineIdx_apply_not_mem Finset.sdiff_subset _ _ ⟨s, hs⟩ hns_compl,
      LocalNet.regionIdxCongr_apply (L := L) h_eq.symm x hsΛ hs_recast]
  · have hs_compl : s ∈ Λ_total \ Λ := Finset.mem_sdiff.mpr ⟨hs, hsΛ⟩
    rw [LocalNet.combineIdx_apply_not_mem h _ _ ⟨s, hs⟩ hsΛ,
        LocalNet.combineIdx_apply_mem Finset.sdiff_subset _ _ ⟨s, hs⟩ hs_compl]

/-- Restriction to `Λ` equals the partial trace of the reindexed matrix induced by
`combineIdx h`, retaining the `Λ` factor. -/
theorem restrict_eq_partialTrace_combineIdx
    {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    (ρ : L.localAlgebra Λ_total) (x x' : L.regionIdx Λ) :
    Matrix.restrict h ρ x x' =
      Matrix.partialTrace
        (A := L.regionIdx Λ) (B := L.regionIdx (Λ_total \ Λ))
        (Equiv.refl (L.regionIdx Λ × L.regionIdx (Λ_total \ Λ)))
        (ρ.submatrix (L.combineIdx h) (L.combineIdx h)) x x' := by
  rw [Matrix.partialTrace_refl_apply, Matrix.restrict_apply]
  simp [Matrix.submatrix_apply]

/-- Restriction to the complement of `Λ` equals the partial trace of the reindexed matrix
induced by `combineIdx h`, retaining the complementary factor. -/
theorem restrict_compl_eq_partialTrace_combineIdx
    {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    (ρ : L.localAlgebra Λ_total) (y y' : L.regionIdx (Λ_total \ Λ)) :
    Matrix.restrict Finset.sdiff_subset ρ y y' =
      Matrix.partialTrace
        (A := L.regionIdx (Λ_total \ Λ)) (B := L.regionIdx Λ)
        (Equiv.prodComm (L.regionIdx Λ) (L.regionIdx (Λ_total \ Λ)))
        (ρ.submatrix (L.combineIdx h) (L.combineIdx h)) y y' := by
  rw [Matrix.partialTrace_prodComm_apply, Matrix.restrict_apply]
  rw [← (L.regionIdxCongr (sdiff_sdiff_eq_self h).symm).sum_comp
        (fun z => ρ (L.combineIdx Finset.sdiff_subset (y, z))
          (L.combineIdx Finset.sdiff_subset (y', z)))]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.submatrix_apply, combineIdx_swap_apply h x y, combineIdx_swap_apply h x y']

end LocalNetBridge

/-! ### Heisenberg duality at product type

`Tr(ρ · (X ⊗ 1)) = Tr((partialTrace (Equiv.refl (n × m)) ρ) · X)` and the symmetric
`(1 ⊗ Y)` version. -/

omit [DecidableEq n] in
/-- **Right-factor Heisenberg dual**: tracing `ρ` against the embedded observable
`X ⊗ 1` reduces to the trace against the partial trace that retains the first factor. -/
theorem trace_mul_kronecker_one_right
    (ρ : Matrix (n × m) (n × m) ℂ) (X : Matrix n n ℂ) :
  Tr (ρ * (X ⊗ₖ (1 : Matrix m m ℂ))) =
    Tr (partialTrace (A := n) (B := m) (Equiv.refl (n × m)) ρ * X) := by
  classical
  unfold Matrix.trace
  simp_rw [Matrix.diag_apply, Matrix.mul_apply, partialTrace_refl_apply]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type, Matrix.kronecker_apply, Matrix.one_apply]
  -- Goal: ∑ a, ∑ b, ∑ a', ∑ b', ρ (a, b) (a', b') * (X a' a * (if b' = b then 1 else 0))
  --     = ∑ a, ∑ a', (∑ b, ρ (a, b) (a', b)) * X a' a
  have inner : ∀ (a : n) (b : m) (a' : n),
      (∑ b' : m, ρ (a, b) (a', b') * (X a' a * (if b' = b then (1 : ℂ) else 0))) =
      ρ (a, b) (a', b) * X a' a := by
    intro a b a'
    rw [Finset.sum_eq_single b]
    · simp
    · intro b' _ hb'; rw [if_neg hb']; ring
    · simp
  simp_rw [inner]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [Finset.sum_mul]

omit [DecidableEq m] in
/-- **Left-factor Heisenberg dual**: `Tr(ρ · (1 ⊗ Y))` reduces to the trace against the
partial trace that retains the second factor. -/
theorem trace_mul_kronecker_one_left
    (ρ : Matrix (n × m) (n × m) ℂ) (Y : Matrix m m ℂ) :
    Tr (ρ * ((1 : Matrix n n ℂ) ⊗ₖ Y)) =
      Tr (partialTrace (A := m) (B := n) (Equiv.prodComm n m) ρ * Y) := by
  classical
  unfold Matrix.trace
  simp_rw [Matrix.diag_apply, Matrix.mul_apply, partialTrace_prodComm_apply]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type, Matrix.kronecker_apply, Matrix.one_apply]
  -- Goal: ∑ a, ∑ b, ∑ a', ∑ b', ρ (a, b) (a', b') * ((if a' = a then 1 else 0) * Y b' b)
  --     = ∑ b, ∑ b', (∑ a, ρ (a, b) (a, b')) * Y b' b
  have inner : ∀ (a : n) (b : m),
      (∑ a' : n, ∑ b' : m, ρ (a, b) (a', b') * ((if a' = a then (1 : ℂ) else 0) * Y b' b)) =
      ∑ b' : m, ρ (a, b) (a, b') * Y b' b := by
    intro a b
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [Finset.sum_eq_single a]
    · simp
    · intro a' _ ha'; rw [if_neg ha']; ring
    · simp
  simp_rw [inner]
  -- Goal: ∑ a, ∑ b, ∑ b', ρ (a, b) (a, b') * Y b' b
  --     = ∑ b, ∑ b', (∑ a, ρ (a, b) (a, b')) * Y b' b
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [Finset.sum_mul]

/-! ## Paper notation: `tr₁(ρ)` / `tr₂(ρ)`

Subscript convention follows Nielsen–Chuang §2.4: `trᵢ(ρ)` traces *out* factor
`i` and retains the other. For a bipartite density matrix `ρ` on `n × m`:

* `tr₂(ρ) = partialTrace (Equiv.refl (n × m)) ρ` — traces out the second
  factor `m`, retaining `n`.
* `tr₁(ρ) = partialTrace (Equiv.prodComm n m) ρ` — traces out the first
  factor `n`, retaining `m`.

The macros use `Equiv.refl _` / `Equiv.prodComm _ _`; the underscores are
solved from the matrix-typed argument. -/

namespace QuantumInfo

scoped syntax:max "tr₁(" term ")" : term
scoped syntax:max "tr₂(" term ")" : term

scoped macro_rules
  | `(tr₁($ρ)) => `(Matrix.partialTrace (Equiv.prodComm _ _) $ρ)
  | `(tr₂($ρ)) => `(Matrix.partialTrace (Equiv.refl _) $ρ)

end QuantumInfo

end Matrix

/-! ### Tensor product of density matrices -/

namespace DensityMatrix

open scoped Kronecker
open Matrix

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-- **Tensor product (Kronecker) of density matrices.** Represents the
independent-systems product state on the joint system `n × m`. -/
noncomputable def kronecker (ρ : DensityMatrix n) (σ : DensityMatrix m) :
    DensityMatrix (n × m) where
  toMatrix := ρ.toMatrix ⊗ₖ σ.toMatrix
  posSemidef := ρ.posSemidef.kronecker σ.posSemidef
  trace_eq_one := by
    rw [trace_kronecker, ρ.trace_eq_one, σ.trace_eq_one, mul_one]

@[inherit_doc DensityMatrix.kronecker]
scoped[Kronecker] infixl:100 " ⊗ " => DensityMatrix.kronecker

@[simp] lemma kronecker_toMatrix (ρ : DensityMatrix n) (σ : DensityMatrix m) :
    (ρ ⊗ σ).toMatrix = ρ.toMatrix ⊗ₖ σ.toMatrix := rfl

end DensityMatrix
