/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.CFC.Diagonal
public import QuantumSystem.Analysis.Entropy.Umegaki.Basic
public import QuantumSystem.Analysis.Entropy.VonNeumann.Basic
public import QuantumSystem.Analysis.Matrix.DensityMatrix.Kronecker

/-!
# Mutual-information identity

The relative-entropy form of quantum mutual information, with Umegaki's relative entropy
`D(ρ ‖ σ)` (`Matrix.umegakiEntropy`), for a bipartite density matrix on a plain
product index type `n × m`:

  `D(ρ_AB ‖ ρ_A ⊗ ρ_B) = -S(ρ_AB) + S(ρ_A) + S(ρ_B)`.

It is representation-free; the analytic core reused by the direct proof
(`Analysis/Entropy/VonNeumann/StrongSubadditivity.lean`) and, via transport, by the planned
split-net proof (`Analysis/Entropy/VonNeumann/SplitSSA.lean`, not yet formalised — the split
property it rests on is `LocalNet.SplitProperty`).
-/

@[expose] public section

namespace Matrix

open scoped Kronecker MatrixOrder ComplexOrder QuantumInfo

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-! ### Relative-entropy identity -/

/-- **Mutual-information identity**: for a bipartite density matrix `ρ_AB : DensityMatrix (n × m)`
whose canonical partial traces are `ρ_A` and `ρ_B`, the relative entropy w.r.t. the product
`ρ_A ⊗ ρ_B` equals `-S(ρ_AB) + S(ρ_A) + S(ρ_B)`.

No positive-definiteness is assumed: the support inclusion `supp ρ_AB ⊆ supp (ρ_A ⊗ ρ_B)` is
automatic for marginals, and the trace identity holds because `ρ_AB` annihilates every eigenvector
of `ρ_A ⊗ ρ_B` with zero eigenvalue, where the junk value `Real.log 0 = 0` would otherwise break
`log (λᵢ μⱼ) = log λᵢ + log μⱼ`. -/
theorem umegakiEntropy_kronecker_marginals
    (ρ_AB : DensityMatrix (n × m)) (ρ_A : DensityMatrix n) (ρ_B : DensityMatrix m)
    (h_A_partialTrace : tr₂(ρ_AB.toMatrix) = ρ_A.toMatrix)
    (h_B_partialTrace : tr₁(ρ_AB.toMatrix) = ρ_B.toMatrix) :
    D(ρ_AB.toMatrix ∥ (ρ_A ⊗ ρ_B).toMatrix) = -S(ρ_AB) + S(ρ_A) + S(ρ_B) := by
  classical
  -- Spectral data of the factors.
  set U_A : Matrix n n ℂ := (ρ_A.isHermitian.eigenvectorUnitary : Matrix n n ℂ) with hU_A
  set U_B : Matrix m m ℂ := (ρ_B.isHermitian.eigenvectorUnitary : Matrix m m ℂ) with hU_B
  set lam := ρ_A.isHermitian.eigenvalues with hlam
  set mu := ρ_B.isHermitian.eigenvalues with hmu
  have hUA : U_Aᴴ * U_A = 1 := UHU_eq_one _ ρ_A.isHermitian
  have hUA' : U_A * U_Aᴴ = 1 := UUH_eq_one _ ρ_A.isHermitian
  have hUB : U_Bᴴ * U_B = 1 := UHU_eq_one _ ρ_B.isHermitian
  have hUB' : U_B * U_Bᴴ = 1 := UUH_eq_one _ ρ_B.isHermitian
  have hA_spec : ρ_A.toMatrix = U_A * diagonal (fun i => (lam i : ℂ)) * U_Aᴴ :=
    spectral_expand _ ρ_A.isHermitian
  have hB_spec : ρ_B.toMatrix = U_B * diagonal (fun j => (mu j : ℂ)) * U_Bᴴ :=
    spectral_expand _ ρ_B.isHermitian
  have hA_diag : U_Aᴴ * ρ_A.toMatrix * U_A = diagonal (fun i => (lam i : ℂ)) := by
    rw [hA_spec, Matrix.mul_assoc, Matrix.mul_assoc, hUA, Matrix.mul_one, ← Matrix.mul_assoc,
      hUA, Matrix.one_mul]
  have hB_diag : U_Bᴴ * ρ_B.toMatrix * U_B = diagonal (fun j => (mu j : ℂ)) := by
    rw [hB_spec, Matrix.mul_assoc, Matrix.mul_assoc, hUB, Matrix.mul_one, ← Matrix.mul_assoc,
      hUB, Matrix.one_mul]
  -- The Kronecker unitary `W = U_A ⊗ U_B` diagonalises `ρ_A ⊗ ρ_B`.
  let W : unitary (Matrix (n × m) (n × m) ℂ) :=
    ⟨U_A ⊗ₖ U_B, Matrix.kronecker_mem_unitary
      ρ_A.isHermitian.eigenvectorUnitary.property ρ_B.isHermitian.eigenvectorUnitary.property⟩
  have hW : (W : Matrix (n × m) (n × m) ℂ) = U_A ⊗ₖ U_B := rfl
  set d : n × m → ℝ := fun ij => lam ij.1 * mu ij.2 with hd
  have hσ : (ρ_A ⊗ ρ_B).toMatrix =
      (W : Matrix (n × m) (n × m) ℂ) * diagonal (fun ij => ((d ij : ℝ) : ℂ)) *
        (W : Matrix (n × m) (n × m) ℂ)ᴴ := by
    rw [DensityMatrix.kronecker_toMatrix, hW, kronecker_eq_unitary_conj_diagonal hA_spec hB_spec]
    congr 2
    funext ij
    simp only [hd]
    push_cast
    ring
  -- The conjugated state `M = Wᴴ ρ_AB W` and its (real, non-negative) diagonal `r`.
  set M : Matrix (n × m) (n × m) ℂ :=
    (W : Matrix (n × m) (n × m) ℂ)ᴴ * ρ_AB.toMatrix * (W : Matrix (n × m) (n × m) ℂ) with hM
  have hM_psd : M.PosSemidef := ρ_AB.posSemidef.conjTranspose_mul_mul_same _
  set r : n × m → ℝ := fun ij => (M ij ij).re with hr
  have hr_nonneg : ∀ ij, 0 ≤ r ij := fun ij =>
    (Complex.nonneg_iff.mp (hM_psd.diag_nonneg (i := ij))).1
  have hM_diag : ∀ ij, M ij ij = (r ij : ℂ) := by
    intro ij
    apply Complex.ext
    · rfl
    · exact ((Complex.nonneg_iff.mp (hM_psd.diag_nonneg (i := ij))).2).symm.trans
        (Complex.ofReal_im _).symm
  -- Marginal identities: row/column sums of `r` are the eigenvalues of the factors.
  have hsum_j : ∀ i, ∑ j, r (i, j) = lam i := by
    intro i
    have h := sum_diag_conj_kronecker_right ρ_AB.toMatrix U_A hUB' i
    rw [h_A_partialTrace, hA_diag, diagonal_apply_eq] at h
    have h' : (∑ j, r (i, j) : ℂ) = (lam i : ℂ) := by
      rw [← h]
      exact Finset.sum_congr rfl fun j _ => (hM_diag (i, j)).symm
    exact_mod_cast h'
  have hsum_i : ∀ j, ∑ i, r (i, j) = mu j := by
    intro j
    have h := sum_diag_conj_kronecker_left ρ_AB.toMatrix U_B hUA' j
    rw [h_B_partialTrace, hB_diag, diagonal_apply_eq] at h
    have h' : (∑ i, r (i, j) : ℂ) = (mu j : ℂ) := by
      rw [← h]
      exact Finset.sum_congr rfl fun i _ => (hM_diag (i, j)).symm
    exact_mod_cast h'
  -- `r` vanishes wherever the product eigenvalue vanishes.
  have hr_zero : ∀ ij, d ij = 0 → r ij = 0 := by
    rintro ⟨i, j⟩ hij
    rcases mul_eq_zero.mp hij with hi | hj
    · refine le_antisymm ?_ (hr_nonneg _)
      calc r (i, j) ≤ ∑ j', r (i, j') :=
            Finset.single_le_sum (fun j' _ => hr_nonneg (i, j')) (Finset.mem_univ j)
        _ = 0 := by rw [hsum_j, hi]
    · refine le_antisymm ?_ (hr_nonneg _)
      calc r (i, j) ≤ ∑ i', r (i', j) :=
            Finset.single_le_sum (fun i' _ => hr_nonneg (i', j)) (Finset.mem_univ i)
        _ = 0 := by rw [hsum_i, hj]
  -- Support inclusion `supp ρ_AB ⊆ supp (ρ_A ⊗ ρ_B)`.
  have h_supp : suppSubset ρ_AB.toMatrix (ρ_A ⊗ ρ_B).toMatrix := by
    rw [hσ, suppSubset_unitary_conj_diagonal_iff ρ_AB.posSemidef W d]
    intro ij hij
    change M ij ij = 0
    rw [hM_diag, hr_zero ij hij, Complex.ofReal_zero]
  rw [umegakiEntropy_of_suppSubset ρ_AB.posSemidef (ρ_A ⊗ ρ_B).posSemidef h_supp]
  -- The trace against `log (ρ_A ⊗ ρ_B)` splits into the two marginal traces.
  have h_real : ∑ ij : n × m, Real.log (d ij) * r ij =
      ∑ i, lam i * Real.log (lam i) + ∑ j, mu j * Real.log (mu j) := by
    have hsplit : ∀ ij : n × m, Real.log (d ij) * r ij =
        Real.log (lam ij.1) * r ij + Real.log (mu ij.2) * r ij := by
      intro ij
      by_cases h0 : d ij = 0
      · rw [hr_zero ij h0]; ring
      · have h0' : lam ij.1 * mu ij.2 ≠ 0 := h0
        simp only [hd]
        rw [Real.log_mul (left_ne_zero_of_mul h0') (right_ne_zero_of_mul h0')]
        ring
    rw [Finset.sum_congr rfl (fun ij _ => hsplit ij), Finset.sum_add_distrib]
    congr 1
    · rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      change ∑ j, Real.log (lam i) * r (i, j) = lam i * Real.log (lam i)
      rw [← Finset.mul_sum, hsum_j i, mul_comm]
    · rw [Fintype.sum_prod_type_right]
      refine Finset.sum_congr rfl fun j _ => ?_
      change ∑ i, Real.log (mu j) * r (i, j) = mu j * Real.log (mu j)
      rw [← Finset.mul_sum, hsum_i j, mul_comm]
  have h_trace_log_kron :
      (Tr (ρ_AB.toMatrix * cfc Real.log (ρ_A ⊗ ρ_B).toMatrix)).re =
        (Tr (ρ_A.toMatrix * cfc Real.log ρ_A.toMatrix)).re +
        (Tr (ρ_B.toMatrix * cfc Real.log ρ_B.toMatrix)).re := by
    rw [hσ, trace_mul_cfc_unitary_conj_diagonal W Real.log d ρ_AB.toMatrix,
      trace_mul_cfc ρ_A.isHermitian, trace_mul_cfc ρ_B.isHermitian]
    change (∑ ij, ((Real.log (d ij) : ℝ) : ℂ) * M ij ij).re = _
    simp only [hM_diag, ← Complex.ofReal_mul, Complex.re_sum, Complex.ofReal_re]
    exact h_real
  -- Split (log ρ - log(ρ_A⊗ρ_B)) and reduce trace.
  have h_split : Tr (ρ_AB.toMatrix * (cfc Real.log ρ_AB.toMatrix -
        cfc Real.log (ρ_A ⊗ ρ_B).toMatrix)) =
      Tr (ρ_AB.toMatrix * cfc Real.log ρ_AB.toMatrix) -
        Tr (ρ_AB.toMatrix * cfc Real.log (ρ_A ⊗ ρ_B).toMatrix) := by
    rw [Matrix.mul_sub, Matrix.trace_sub]
  -- Translate to the goal in EReal.
  change (↑(Tr (ρ_AB.toMatrix * (cfc Real.log ρ_AB.toMatrix -
        cfc Real.log (ρ_A ⊗ ρ_B).toMatrix))).re : EReal) =
      -S(ρ_AB) + S(ρ_A) + S(ρ_B)
  rw [h_split, Complex.sub_re, h_trace_log_kron]
  set α : ℝ := (Tr (ρ_AB.toMatrix * cfc Real.log ρ_AB.toMatrix)).re with hα
  set β : ℝ := (Tr (ρ_A.toMatrix * cfc Real.log ρ_A.toMatrix)).re with hβ
  set γ : ℝ := (Tr (ρ_B.toMatrix * cfc Real.log ρ_B.toMatrix)).re with hγ
  have hSρ : S(ρ_AB) = -α := rfl
  have hSρ_A : S(ρ_A) = -β := rfl
  have hSρ_B : S(ρ_B) = -γ := rfl
  rw [hSρ, hSρ_A, hSρ_B]
  have h_real' : α - (β + γ) = -(-α) + (-β) + (-γ) := by ring
  exact_mod_cast h_real'

end Matrix
