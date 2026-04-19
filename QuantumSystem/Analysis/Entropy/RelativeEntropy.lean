module

public import QuantumSystem.ForMathlib.Analysis.Calculus.Deriv.Sign
public import QuantumSystem.ForMathlib.InformationTheory.KullbackLeibler.KLFun
public import QuantumSystem.Analysis.Matrix.LiebConcavity
public import QuantumSystem.Analysis.Matrix.Pinching
public import QuantumSystem.Channel

/-!
# Entropy Inequalities for Quantum Channels

This file collects fundamental entropy inequalities for quantum channels.

## Main Results

* `relativeEntropy_channel_le`: Monotonicity of relative entropy — quantum channels do not
  increase relative entropy: S(Φ(ρ) ‖ Φ(σ)) ≤ S(ρ ‖ σ).
* `relativeEntropy_channel_eq_iff_recoverable`: Equality in monotonicity holds when a Petz
  recovery channel exists: if R(Φ(ρ)) = ρ and R(Φ(σ)) = σ, then
  S(Φ(ρ) ‖ Φ(σ)) = S(ρ ‖ σ).
* `relativeEntropy_jointly_convex`: Relative entropy is jointly convex.

## Mathematical Background

### Monotonicity of Relative Entropy
For a quantum channel Φ : Mₙ(ℂ) → Mₘ(ℂ) and positive definite
density matrices ρ, σ:
  S(Φ(ρ) ‖ Φ(σ)) ≤ S(ρ ‖ σ)

**Proof strategy** (Lindblad):
1. Use Stinespring dilation: Φ(ρ) = Tr_E(U(ρ ⊗ |0⟩⟨0|)U†)
2. Relative entropy is additive: S(ρ ⊗ |0⟩⟨0| ‖ σ ⊗ |0⟩⟨0|) = S(ρ ‖ σ)
3. Relative entropy is unitarily invariant
4. Partial trace only decreases relative entropy (strong subadditivity)

### Petz Recovery Map
Equality in monotonicity holds iff there exists a recovery channel R such that
R(Φ(ρ)) = ρ and R(Φ(σ)) = σ. The explicit form is:
  R(·) = σ^(1/2) Φ*(Φ(σ)^(-1/2) · Φ(σ)^(-1/2)) σ^(1/2)
where Φ* is the adjoint of Φ with respect to the Hilbert-Schmidt inner product.

## References

* Lindblad, *Completely positive maps and entropy inequalities*
* Petz, *Monotonicity of quantum relative entropy revisited*
* Ruskai, *Inequalities for quantum entropy: A review with conditions for equality*
-/

@[expose] public section

namespace Matrix

open scoped MatrixOrder ComplexOrder QuantumInfo

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-! ### Relative Entropy -/

/-- Support inclusion: the kernel of σ is contained in the kernel of ρ,
i.e., supp(ρ) ⊆ supp(σ). This is the condition for D(ρ‖σ) to be finite. -/
def suppSubset (ρ σ : Matrix n n ℂ) : Prop :=
  ∀ v : n → ℂ, σ.mulVec v = 0 → ρ.mulVec v = 0

/-- Quantum relative entropy D(ρ‖σ) = Tr (ρ(log ρ - log σ)) (Umegaki 1962).

This is the physically correct definition, following Umegaki (1962):

  D(ρ ‖ σ) = Tr (ρ(log ρ − log σ))   if supp(ρ) ⊆ supp(σ)
             = +∞                       otherwise

- The return type is `EReal` to accommodate the +∞ case.
- The matrix logarithms `log ρ` and `log σ` are computed via the spectral theorem.
  When `σ` has zero eigenvalues, `Real.log 0 = 0` (Mathlib junk value) is used;
  those directions contribute 0 to `Tr (ρ log σ)` because supp(ρ) ⊆ supp(σ).
- When ρ and σ commute (shared eigenbasis), this reduces to Σᵢ λᵢ(log λᵢ - log μᵢ).
-/
noncomputable def relativeEntropy (ρ σ : DensityMatrix n) : EReal :=
  letI := Classical.propDecidable (suppSubset ρ.toMatrix σ.toMatrix)
  if suppSubset ρ.toMatrix σ.toMatrix then
    -- Tr (ρ (log ρ - log σ))
    ↑((Tr (ρ * (log ρ - log σ))).re)
  else ⊤

namespace QuantumInfo
scoped notation "D(" ρ " ∥ " σ ")" => Matrix.relativeEntropy ρ σ
end QuantumInfo

/-! ### Helper Lemmas for Relative Entropy -/

/-- Change-of-basis unitary between eigenvector bases of ρ and σ.
W = Vᴴ * U where V = eigenvectors of σ, U = eigenvectors of ρ. -/
private noncomputable def eigW (ρ σ : DensityMatrix n) : Matrix n n ℂ :=
  (σ.isHermitian.eigenvectorUnitary : Matrix n n ℂ)ᴴ *
  (ρ.isHermitian.eigenvectorUnitary : Matrix n n ℂ)

/-- W * Wᴴ = 1 for the change-of-basis unitary. -/
private lemma eigW_WWH (ρ σ : DensityMatrix n) :
    eigW ρ σ * (eigW ρ σ)ᴴ = 1 := by
  unfold eigW
  set V := (σ.isHermitian.eigenvectorUnitary : Matrix n n ℂ)
  set U := (ρ.isHermitian.eigenvectorUnitary : Matrix n n ℂ)
  rw [conjTranspose_mul, conjTranspose_conjTranspose]
  calc (Vᴴ * U) * (Uᴴ * V)
      = Vᴴ * (U * Uᴴ) * V := by simp only [Matrix.mul_assoc]
    _ = Vᴴ * V := by rw [UUH_eq_one _ ρ.isHermitian, Matrix.mul_one]
    _ = 1 := UHU_eq_one _ σ.isHermitian

/-- Wᴴ * W = 1 for the change-of-basis unitary. -/
private lemma eigW_WHW (ρ σ : DensityMatrix n) :
    (eigW ρ σ)ᴴ * eigW ρ σ = 1 := by
  unfold eigW
  set V := (σ.isHermitian.eigenvectorUnitary : Matrix n n ℂ)
  set U := (ρ.isHermitian.eigenvectorUnitary : Matrix n n ℂ)
  rw [conjTranspose_mul, conjTranspose_conjTranspose]
  calc (Uᴴ * V) * (Vᴴ * U)
      = Uᴴ * (V * Vᴴ) * U := by simp only [Matrix.mul_assoc]
    _ = Uᴴ * U := by rw [UUH_eq_one _ σ.isHermitian, Matrix.mul_one]
    _ = 1 := UHU_eq_one _ ρ.isHermitian

/-- Column sums of |W_{ji}|² equal 1. Follows from W * Wᴴ = 1 (W is unitary). -/
private lemma eigW_unitary_colsum (ρ σ : DensityMatrix n) (i : n) :
    ∑ j : n, Complex.normSq (eigW ρ σ j i) = 1 := by
  have h1 := congr_fun (congr_fun (eigW_WHW ρ σ) i) i
  simp only [mul_apply, conjTranspose_apply, one_apply_eq] at h1
  have h2 : (∑ j : n, (Complex.normSq (eigW ρ σ j i) : ℂ)) = 1 := by
    simp_rw [show ∀ j, (Complex.normSq (eigW ρ σ j i) : ℂ) =
      star (eigW ρ σ j i) * eigW ρ σ j i from fun j => by
        rw [Complex.normSq_eq_conj_mul_self]; simp [RCLike.star_def]]
    exact h1
  exact_mod_cast h2

/-- Row sums of |W_{ji}|² equal 1. Follows from Wᴴ * W = 1 (W is unitary). -/
private lemma eigW_unitary_rowsum (ρ σ : DensityMatrix n) (j : n) :
    ∑ i : n, Complex.normSq (eigW ρ σ j i) = 1 := by
  have h1 := congr_fun (congr_fun (eigW_WWH ρ σ) j) j
  simp only [mul_apply, conjTranspose_apply, one_apply_eq] at h1
  have h2 : (∑ i : n, (Complex.normSq (eigW ρ σ j i) : ℂ)) = 1 := by
    simp_rw [show ∀ i, (Complex.normSq (eigW ρ σ j i) : ℂ) =
      eigW ρ σ j i * star (eigW ρ σ j i) from fun i => by
        rw [Complex.normSq_eq_conj_mul_self]; simp [RCLike.star_def, mul_comm]]
    exact h1
  exact_mod_cast h2

/-- Support subset condition implies: |W_{ji}|² · ev_ρᵢ = 0 when ev_σⱼ = 0.
Here ev_ρᵢ are eigenvalues of ρ, ev_σⱼ are eigenvalues of σ.
Proof: vⱼ = col j of V ∈ ker(σ), suppSubset gives vⱼ ∈ ker(ρ),
injectivity of U gives diag(ev_ρ) · (Uᴴvⱼ) = 0, and (Uᴴvⱼ)ᵢ = conj(Wji). -/
private lemma suppSubset_normSq_ev_zero (ρ σ : DensityMatrix n)
    (h : suppSubset ρ.toMatrix σ.toMatrix) (j : n)
    (hev_σj : σ.isHermitian.eigenvalues j = 0) (i : n) :
    Complex.normSq (eigW ρ σ j i) * ρ.isHermitian.eigenvalues i = 0 := by
  set V := (σ.isHermitian.eigenvectorUnitary : Matrix n n ℂ) with hV_def
  set U := (ρ.isHermitian.eigenvectorUnitary : Matrix n n ℂ) with hU_def
  set W := eigW ρ σ with hW_def
  set ev_ρ := ρ.isHermitian.eigenvalues with hev_ρ_def
  set colV_j : n → ℂ := fun k => V k j with hcolV_def
  -- Column j of V is in ker(σ) since eigenvalue j is 0
  have hσcol : σ.toMatrix.mulVec colV_j = 0 := by
    have h1 := mulVec_eigenvector_col σ.toMatrix σ.isHermitian j
    ext k; rw [congr_fun h1 k, hev_σj, Complex.ofReal_zero, zero_mul, Pi.zero_apply]
  -- By suppSubset, col j of V is also in ker(ρ)
  have hρcol : ρ.toMatrix.mulVec colV_j = 0 := h colV_j hσcol
  -- Compute Uᴴ · colV_j
  set Uh_colV : n → ℂ := Uᴴ.mulVec colV_j with hUh_colV_def
  -- Key: Uh_colV i = star(W j i)
  have hUh_eq_starW : Uh_colV i = star (W j i) := by
    simp only [hUh_colV_def, hW_def, eigW, hcolV_def, mulVec, dotProduct,
      conjTranspose_apply, mul_apply, star_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [star_mul', star_star, mul_comm]
  -- From spectral decomposition ρ = U diag(ev_ρ) Uᴴ, we have:
  -- ρ · colV_j = U · diag(ev_ρ) · (Uᴴ · colV_j)
  have hspec := spectral_expand ρ.toMatrix ρ.isHermitian
  -- Since ρ · colV_j = 0, we have U · diag(ev_ρ) · Uh_colV = 0
  have h_diag_eq : (U * diagonal (fun k => (ev_ρ k : ℂ))).mulVec Uh_colV = 0 := by
    calc (U * diagonal (fun k => (ev_ρ k : ℂ))).mulVec Uh_colV
        = (U * diagonal (fun k => (ev_ρ k : ℂ))).mulVec (Uᴴ.mulVec colV_j) := rfl
      _ = (U * diagonal (fun k => (ev_ρ k : ℂ)) * Uᴴ).mulVec colV_j := by
          rw [Matrix.mulVec_mulVec]
      _ = ρ.toMatrix.mulVec colV_j := by rw [← hspec]
      _ = 0 := hρcol
  -- Extract the i-th component: ev_ρ i * (Uh_colV i) = 0
  have h_ev_Uh_zero : (ev_ρ i : ℂ) * Uh_colV i = 0 := by
    -- From h_diag_eq, we know (U * diag) * Uh_colV = 0
    -- Multiplying by Uᴴ on left: Uᴴ * (U * diag) * Uh_colV = 0
    -- Since Uᴴ * U = 1, this gives diag * Uh_colV = 0
    have h_UhU := UHU_eq_one _ ρ.isHermitian
    have h1 : (diagonal (fun k => (ev_ρ k : ℂ))).mulVec Uh_colV = 0 := by
      have h2 : Uᴴ.mulVec ((U * diagonal (fun k => (ev_ρ k : ℂ))).mulVec Uh_colV) = 0 := by
        rw [h_diag_eq, mulVec_zero]
      simp only [Matrix.mulVec_mulVec] at h2
      have h3 : (Uᴴ * U) * diagonal (fun k => (ev_ρ k : ℂ)) = diagonal (fun k => (ev_ρ k : ℂ)) := by
        rw [h_UhU, Matrix.one_mul]
      rw [← Matrix.mul_assoc] at h2
      rw [h3] at h2
      exact h2
    have h2 := congr_fun h1 i
    simp only [mulVec, dotProduct, diagonal_apply, Pi.zero_apply] at h2
    -- h2 : ∑ x, (if i = x then ev_ρ i else 0) * Uh_colV x = 0
    -- Simplify the sum: only x = i contributes
    have h3 : ∑ x, (if i = x then (ev_ρ i : ℂ) else 0) * Uh_colV x = (ev_ρ i : ℂ) * Uh_colV i := by
      rw [Finset.sum_eq_single i]
      · simp only [ite_true]
      · intro b _ hb
        have hne : i ≠ b := Ne.symm hb
        simp only [hne, ite_false, zero_mul]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    rw [h3] at h2
    exact h2
  -- From ev_ρ i * star(W j i) = 0, derive normSq(W j i) * ev_ρ i = 0
  rw [hUh_eq_starW] at h_ev_Uh_zero
  rcases mul_eq_zero.mp h_ev_Uh_zero with hev_zero | hstar_zero
  · -- Case: ev_ρ i = 0
    simp only [Complex.ofReal_eq_zero] at hev_zero
    simp [hev_zero]
  · -- Case: star(W j i) = 0, hence W j i = 0
    rw [star_eq_zero] at hstar_zero
    simp [hstar_zero]

/-- Trace of ρ log ρ equals the eigenvalue sum ∑ᵢ ev_{ρ,i} log ev_{ρ,i}. -/
private lemma trace_ρlogρ_eq (ρ : DensityMatrix n) :
    (Tr (ρ.toMatrix * log ρ)).re =
    ∑ i, ρ.isHermitian.eigenvalues i * Real.log (ρ.isHermitian.eigenvalues i) := by
  set U := (ρ.isHermitian.eigenvectorUnitary : Matrix n n ℂ)
  set ev_ρ := ρ.isHermitian.eigenvalues
  have hUHU : Uᴴ * U = 1 := UHU_eq_one _ ρ.isHermitian
  -- ρ = U * diag(ev) * Uᴴ
  have hρ_spec := spectral_expand ρ.toMatrix ρ.isHermitian
  -- log(ρ) = U * diag(log ev) * Uᴴ
  have hlogρ_spec : log ρ = U * diagonal (fun i => (Real.log (ev_ρ i) : ℂ)) * Uᴴ := by
    unfold DensityMatrix.log matrixLog matrixFunction
    rfl
  -- ρ * log(ρ) = U * diag(ev) * Uᴴ * U * diag(log ev) * Uᴴ = U * diag(ev * log ev) * Uᴴ
  -- First rewrite log, then ρ
  have h1 : (ρ.toMatrix * log ρ).trace.re =
      (ρ.toMatrix * (U * diagonal (fun i => (Real.log (ev_ρ i) : ℂ)) * Uᴴ)).trace.re := by
    rw [hlogρ_spec]
  rw [h1, hρ_spec]
  have h2 : (U * diagonal (fun i => (ev_ρ i : ℂ)) * Uᴴ *
             (U * diagonal (fun i => (Real.log (ev_ρ i) : ℂ)) * Uᴴ)) =
            U * (diagonal (fun i => (ev_ρ i : ℂ)) *
                 diagonal (fun i => (Real.log (ev_ρ i) : ℂ))) * Uᴴ := calc
    _ = U * diagonal (fun i => (ev_ρ i : ℂ)) *
          (Uᴴ * (U * diagonal (fun i => (Real.log (ev_ρ i) : ℂ)) * Uᴴ)) := by
      simp only [Matrix.mul_assoc]
    _ = U * diagonal (fun i => (ev_ρ i : ℂ)) *
          ((Uᴴ * U) * diagonal (fun i => (Real.log (ev_ρ i) : ℂ)) * Uᴴ) := by
      conv_lhs => rw [← Matrix.mul_assoc Uᴴ (U * _) Uᴴ, ← Matrix.mul_assoc Uᴴ U]
    _ = U * diagonal (fun i => (ev_ρ i : ℂ)) *
          (diagonal (fun i => (Real.log (ev_ρ i) : ℂ)) * Uᴴ) := by
      rw [hUHU, Matrix.one_mul]
    _ = U * (diagonal (fun i => (ev_ρ i : ℂ)) *
             diagonal (fun i => (Real.log (ev_ρ i) : ℂ))) * Uᴴ := by
      simp only [Matrix.mul_assoc]
  rw [h2]
  simp only [Matrix.mul_assoc]
  rw [trace_mul_cycle']
  -- Goal: ((diag_log * Uᴴ) * (U * diag_ev)).trace.re = ...
  -- left associate and expose Uᴴ * U
  conv_lhs => rw [← Matrix.mul_assoc, Matrix.mul_assoc (diagonal _) Uᴴ U]
  rw [hUHU, Matrix.mul_one, diagonal_mul_diagonal, trace_diagonal]
  simp only [← Complex.ofReal_mul]
  rw [Complex.re_sum]
  simp only [Complex.ofReal_re, mul_comm]

/-- Trace of ρ log σ expressed as double sum over eigenvalues via eigW. -/
private lemma trace_ρlogσ_eq (ρ σ : DensityMatrix n) :
    (Tr (ρ.toMatrix * log σ)).re =
    ∑ i, ∑ j, Complex.normSq (eigW ρ σ j i) *
      ρ.isHermitian.eigenvalues i *
      Real.log (σ.isHermitian.eigenvalues j) := by
  set V := (σ.isHermitian.eigenvectorUnitary : Matrix n n ℂ)
  set U := (ρ.isHermitian.eigenvectorUnitary : Matrix n n ℂ)
  set W := eigW ρ σ
  set ev_ρ := ρ.isHermitian.eigenvalues
  set ev_σ := σ.isHermitian.eigenvalues
  have hρ : ρ.toMatrix = U * diagonal (fun i => (ev_ρ i : ℂ)) * Uᴴ := by
    have h := (matrixFunction_id ρ.isHermitian).symm
    unfold matrixFunction at h
    simpa [Function.comp] using h
  have hlogσ : log σ = V * diagonal (fun i => (Real.log (ev_σ i) : ℂ)) * Vᴴ := by
    unfold DensityMatrix.log matrixLog matrixFunction; rfl
  have hUHV : Uᴴ * V = Wᴴ := by
    calc Uᴴ * V = Uᴴ * (Vᴴ)ᴴ := by rw [conjTranspose_conjTranspose]
      _ = (Vᴴ * U)ᴴ := by rw [conjTranspose_mul]
      _ = Wᴴ := rfl
  rw [hρ, hlogσ]
  have hconv : U * diagonal (fun i => (ev_ρ i : ℂ)) * Uᴴ *
        (V * diagonal (fun j => (Real.log (ev_σ j) : ℂ)) * Vᴴ) =
      U * (diagonal (fun i => (ev_ρ i : ℂ)) * Wᴴ *
           diagonal (fun j => (Real.log (ev_σ j) : ℂ))) * Vᴴ := by
    simp only [Matrix.mul_assoc, ← hUHV]
  rw [hconv]
  have hVHU : Vᴴ * U = W := rfl
  -- Apply trace_mul_cycle to bring Vᴴ adjacent to U
  have hstep1 : (U * ((diagonal (fun i => (ev_ρ i : ℂ))) * Wᴴ *
                       (diagonal (fun j => (Real.log (ev_σ j) : ℂ)))) * Vᴴ).trace =
               (Vᴴ * (U * ((diagonal (fun i => (ev_ρ i : ℂ))) * Wᴴ *
                       (diagonal (fun j => (Real.log (ev_σ j) : ℂ)))))).trace := by
    rw [trace_mul_comm]
  rw [hstep1]
  simp only [Matrix.mul_assoc]
  -- Goal: (Vᴴ * (U * (diag_ev * (Wᴴ * diag_log)))).trace.re
  -- Use ← mul_assoc to get (Vᴴ * U) * ...
  conv_lhs => rw [← Matrix.mul_assoc Vᴴ U, hVHU]
  -- Now: (W * (diag_ev * (Wᴴ * diag_log))).trace.re
  rw [← Matrix.mul_assoc W (diagonal _)]
  -- Now: (W * diag_ev * (Wᴴ * diag_log)).trace.re
  -- Use extensionality to compare summands
  simp only [Matrix.trace, Matrix.diag, mul_apply, conjTranspose_apply, diagonal_apply]
  rw [Complex.re_sum]
  -- RHS is ∑ i, ∑ j, ... ; swap to ∑ j, ∑ i, ... to match LHS structure
  conv_rhs => rw [Finset.sum_comm]
  congr 1; ext j
  -- Each summand has nested sums with if-then-else that simplify to single terms
  have h1 : ∀ x, (∑ x_1, W j x_1 * if x_1 = x then ↑(ev_ρ x_1) else 0) = W j x * ↑(ev_ρ x) := by
    intro x
    rw [Finset.sum_eq_single x]
    · simp only [if_true]
    · intro b _ hb
      simp only [if_neg hb, mul_zero]
    · intro h; exact absurd (Finset.mem_univ x) h
  have h2 : ∀ x, (∑ x_1, star (W x_1 x) * if x_1 = j then ↑(Real.log (ev_σ x_1)) else 0) =
      star (W j x) * ↑(Real.log (ev_σ j)) := by
    intro x
    rw [Finset.sum_eq_single j]
    · simp only [if_true]
    · intro b _ hb
      simp only [if_neg hb, mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  simp only [h1, h2]
  rw [Complex.re_sum]
  congr 1; ext x
  -- Goal: (W j x * ↑(ev_ρ x) * (star (W j x) * ↑(Real.log (ev_σ j)))).re =
  --       Complex.normSq (W j x) * ev_ρ x * Real.log (ev_σ j)
  have hstar : star (W j x) * W j x = ↑(Complex.normSq (W j x)) := by
    simp only [RCLike.star_def, Complex.normSq_eq_conj_mul_self]
  have hrearrange : W j x * ↑(ev_ρ x) * (star (W j x) * ↑(Real.log (ev_σ j))) =
      star (W j x) * W j x * ↑(ev_ρ x) * ↑(Real.log (ev_σ j)) := by ring
  rw [hrearrange, hstar]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, mul_assoc]

/-- Quantum relative entropy is non-negative (Klein's inequality).
D(ρ‖σ) ∈ [0, +∞] with D(ρ‖σ) = 0 iff ρ = σ.

**Proof sketch**: When D = ⊤ the bound is trivial. When supp(ρ) ⊆ supp(σ),
apply Klein's operator inequality to f(x) = -log x (operator-convex on (0,∞)). -/
theorem relativeEntropy_nonneg (ρ σ : DensityMatrix n) :
    0 ≤ D(ρ ∥ σ) := by
  unfold relativeEntropy
  split_ifs with h
  · simp only [EReal.coe_nonneg]
    change 0 ≤ (ρ.toMatrix * (log ρ - log σ)).trace.re
    set ev_ρ := ρ.isHermitian.eigenvalues
    set ev_σ := σ.isHermitian.eigenvalues
    set W := eigW ρ σ
    rw [Matrix.mul_sub, trace_sub, Complex.sub_re, trace_ρlogρ_eq ρ, trace_ρlogσ_eq ρ σ]
    rw [show ∑ i, ev_ρ i * Real.log (ev_ρ i) =
            ∑ i, ∑ j, Complex.normSq (W j i) * ev_ρ i * Real.log (ev_ρ i) by
          congr 1; ext i
          rw [← Finset.sum_mul, ← Finset.sum_mul, eigW_unitary_colsum ρ σ, one_mul],
        ← Finset.sum_sub_distrib]
    apply le_trans (b := ∑ i : n, ∑ j : n, Complex.normSq (W j i) * (ev_ρ i - ev_σ j))
    · -- Lower bound: Σᵢⱼ |Wji|² (ev_ρᵢ - ev_σⱼ) = 0 (by unitarity + trace = 1)
      simp only [mul_sub, Finset.sum_sub_distrib]
      rw [show ∑ i : n, ∑ j : n, Complex.normSq (W j i) * ev_ρ i =
              ∑ i : n, ev_ρ i * ∑ j : n, Complex.normSq (W j i) by
            congr 1; ext i; rw [Finset.mul_sum]; congr 1; ext j; ring,
          show ∑ i : n, ∑ j : n, Complex.normSq (W j i) * ev_σ j =
              ∑ j : n, ev_σ j * ∑ i : n, Complex.normSq (W j i) by
            rw [Finset.sum_comm]; congr 1; ext j; rw [Finset.mul_sum]; congr 1; ext i; ring]
      simp_rw [show ∀ i, ∑ j : n, Complex.normSq (W j i) = 1 from eigW_unitary_colsum ρ σ,
               show ∀ j, ∑ i : n, Complex.normSq (W j i) = 1 from eigW_unitary_rowsum ρ σ,
               mul_one,
               show ∑ i, ev_ρ i = 1 from ρ.sum_eigenvalues,
               show ∑ j, ev_σ j = 1 from σ.sum_eigenvalues, sub_self, le_refl]
    · -- Term-by-term: |Wji|²(ev_ρᵢ-ev_σⱼ) ≤ |Wji|²(ev_ρᵢ log ev_ρᵢ - ev_ρᵢ log ev_σⱼ)
      apply Finset.sum_le_sum; intro i _
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_le_sum; intro j _
      -- Normalize goal: eigW ρ σ j i = W j i, eigenvalues = ev_ρ/ev_σ
      change Complex.normSq (W j i) * (ev_ρ i - ev_σ j) ≤
           Complex.normSq (W j i) * ev_ρ i * Real.log (ev_ρ i) -
           Complex.normSq (W j i) * ev_ρ i * Real.log (ev_σ j)
      rw [← mul_sub]
      -- Goal: normSq * (ev_ρ - ev_σ) ≤ normSq * ev_ρ * (log ev_ρ - log ev_σ)
      rw [show Complex.normSq (W j i) * ev_ρ i * (Real.log (ev_ρ i) - Real.log (ev_σ j)) =
              Complex.normSq (W j i) * (ev_ρ i * (Real.log (ev_ρ i) - Real.log (ev_σ j))) by ring]
      -- Check if normSq = 0 first (in which case both sides are 0)
      by_cases hnormSq : Complex.normSq (W j i) = 0
      · simp [hnormSq]
      · apply mul_le_mul_of_nonneg_left _ (Complex.normSq_nonneg _)
        rcases (σ.eigenvalues_nonneg j).lt_or_eq with hevσpos | hevσzero
        · rcases (ρ.eigenvalues_nonneg i).lt_or_eq with hevρpos | hevρzero
          · have := mul_log_div_ge_sub' hevρpos hevσpos
            rw [Real.log_div (ne_of_gt hevρpos) (ne_of_gt hevσpos)] at this; linarith
          · -- ev_ρ i = 0, ev_σ j > 0
            -- Goal: ev_ρ i - ev_σ j ≤ ev_ρ i * (log ev_ρ i - log ev_σ j)
            -- With ev_ρ i = 0: -ev_σ j ≤ 0, which follows from ev_σ j > 0
            have hρeq : ev_ρ i = 0 := hevρzero.symm
            simp only [hρeq, zero_mul, zero_sub]
            linarith
        · -- ev_σ j = 0, but normSq ≠ 0
          -- suppSubset implies normSq * ev_ρ = 0, and since normSq ≠ 0, we get ev_ρ = 0
          have hzero := suppSubset_normSq_ev_zero ρ σ h j hevσzero.symm i
          have hprod : Complex.normSq (W j i) * ev_ρ i = 0 :=
            le_antisymm
              (by nlinarith [Complex.normSq_nonneg (W j i), ρ.eigenvalues_nonneg i,
                  mul_nonneg (Complex.normSq_nonneg (W j i)) (ρ.eigenvalues_nonneg i)])
              (by nlinarith [mul_nonneg (Complex.normSq_nonneg (W j i))
                    (ρ.eigenvalues_nonneg i)])
          have hevρ : ev_ρ i = 0 := by
            rcases (mul_eq_zero.mp hprod) with h | h
            · exact absurd h hnormSq
            · exact h
          -- Goal: 0 - ev_σ j ≤ 0 * (log 0 - log ev_σ j)
          -- With ev_σ j = 0: 0 - 0 ≤ 0 * (...) = 0, so 0 ≤ 0
          have hσeq : ev_σ j = 0 := hevσzero.symm
          simp [hevρ, hσeq]
  · exact le_top

/-- Quantum relative entropy is zero iff ρ = σ (faithfulness / quantum Pinsker).
D(ρ‖σ) = 0 if and only if ρ = σ.

This is a consequence of Klein's inequality plus the strict convexity of x ↦ x log x.
Note: D(ρ‖σ) = ⊤ ≠ 0 when supp(ρ) ⊄ supp(σ). -/
theorem relativeEntropy_eq_zero_iff (ρ σ : DensityMatrix n) :
    D(ρ ∥ σ) = 0 ↔ ρ = σ := by
  constructor
  · -- → direction: D(ρ‖σ) = 0 → ρ = σ
    intro hD
    -- First: D = ⊤ would give ⊤ = 0, contradiction, so we must be in the suppSubset case.
    unfold relativeEntropy at hD
    by_cases h : suppSubset ρ.toMatrix σ.toMatrix
    · simp only [h, ↓reduceIte] at hD
      rw [EReal.coe_eq_zero] at hD
      change (ρ.toMatrix * (log ρ - log σ)).trace.re = 0 at hD
      -- Extract eigenvalue data
      set V := (σ.isHermitian.eigenvectorUnitary : Matrix n n ℂ) with hV_def
      set U := (ρ.isHermitian.eigenvectorUnitary : Matrix n n ℂ) with hU_def
      set W := eigW ρ σ with hW_def
      set ev_ρ := ρ.isHermitian.eigenvalues
      set ev_σ := σ.isHermitian.eigenvalues
      have hVW : V * W = U := by
        simp only [W, eigW]
        rw [← Matrix.mul_assoc, UUH_eq_one _ σ.isHermitian, Matrix.one_mul]
      have hWW : W * Wᴴ = 1 := eigW_WWH ρ σ
      have hVVH : V * Vᴴ = 1 := UUH_eq_one _ σ.isHermitian
      -- D expressed as eigenvalue sum
      have hD_sum : ∑ i : n, ∑ j : n, Complex.normSq (W j i) *
          (ev_ρ i * Real.log (ev_ρ i) - ev_ρ i * Real.log (ev_σ j)) = 0 := by
        rw [Matrix.mul_sub, trace_sub, Complex.sub_re] at hD
        rw [trace_ρlogρ_eq ρ, trace_ρlogσ_eq ρ σ] at hD
        rw [show ∑ i, ev_ρ i * Real.log (ev_ρ i) =
                ∑ i : n, ∑ j : n, Complex.normSq (W j i) * ev_ρ i * Real.log (ev_ρ i) by
              congr 1; ext i
              rw [← Finset.sum_mul, ← Finset.sum_mul, eigW_unitary_colsum ρ σ, one_mul]] at hD
        linarith [show ∑ i : n, ∑ j : n, Complex.normSq (W j i) * ev_ρ i * Real.log (ev_ρ i) -
                      ∑ i : n, ∑ j : n, Complex.normSq (W j i) * ev_ρ i * Real.log (ev_σ j) =
                      ∑ i : n, ∑ j : n, Complex.normSq (W j i) *
                        (ev_ρ i * Real.log (ev_ρ i) - ev_ρ i * Real.log (ev_σ j)) by
                  simp only [← Finset.sum_sub_distrib]; congr 1; ext i; congr 1; ext j; ring]
      -- KL form: D = Σᵢⱼ |Wji|² ev_σⱼ klFun(ev_ρᵢ/ev_σⱼ)
      have hklform : ∑ i : n, ∑ j : n,
          Complex.normSq (W j i) * ev_σ j * InformationTheory.klFun (ev_ρ i / ev_σ j) = 0 := by
        have hD_eq : ∑ i : n, ∑ j : n, Complex.normSq (W j i) *
            (ev_ρ i * Real.log (ev_ρ i) - ev_ρ i * Real.log (ev_σ j)) =
            ∑ i : n, ∑ j : n,
              (Complex.normSq (W j i) * ev_σ j * InformationTheory.klFun (ev_ρ i / ev_σ j) +
               Complex.normSq (W j i) * (ev_ρ i - ev_σ j)) := by
          congr 1; ext i; congr 1; ext j
          unfold InformationTheory.klFun
          rcases (σ.eigenvalues_nonneg j).lt_or_eq with hμpos | hμzero
          · rcases (ρ.eigenvalues_nonneg i).lt_or_eq with hevρpos | hevρzero
            · have hevρne : ev_ρ i ≠ 0 := ne_of_gt hevρpos
              have hevσne : ev_σ j ≠ 0 := ne_of_gt hμpos
              field_simp; rw [Real.log_div hevρne hevσne]; ring
            · have hev_ρ_zero : ev_ρ i = 0 := hevρzero.symm
              simp [hev_ρ_zero, Real.log_zero]
          · have hsupp' := suppSubset_normSq_ev_zero ρ σ h j hμzero.symm i
            rcases mul_eq_zero.mp hsupp' with hw0 | hev0
            · have hW0 : Complex.normSq (W j i) = 0 := hw0
              simp [hW0]
            · have hev0' : ev_ρ i = 0 := by exact_mod_cast hev0
              simp [hev0', Real.log_zero]
        rw [hD_eq] at hD_sum
        simp_rw [Finset.sum_add_distrib] at hD_sum
        have hzero : ∑ i : n, ∑ j : n, Complex.normSq (W j i) * (ev_ρ i - ev_σ j) = 0 := by
          simp only [mul_sub, Finset.sum_sub_distrib]
          rw [show ∑ i : n, ∑ j : n, Complex.normSq (W j i) * ev_ρ i = ∑ i : n, ev_ρ i by
                congr 1; ext i; rw [← Finset.sum_mul, eigW_unitary_colsum ρ σ, one_mul],
              show ∑ i : n, ∑ j : n, Complex.normSq (W j i) * ev_σ j = ∑ j : n, ev_σ j by
                rw [Finset.sum_comm]; congr 1; ext j; rw [← Finset.sum_mul, eigW_unitary_rowsum ρ σ, one_mul]]
          linarith [ρ.sum_eigenvalues, σ.sum_eigenvalues]
        linarith
      -- Each KL term = 0
      have hterms : ∀ (i j : n),
          Complex.normSq (W j i) * ev_σ j * InformationTheory.klFun (ev_ρ i / ev_σ j) = 0 := by
        have hterm_nn : ∀ (i j : n),
            0 ≤ Complex.normSq (W j i) * ev_σ j * InformationTheory.klFun (ev_ρ i / ev_σ j) :=
          fun i j => mul_nonneg (mul_nonneg (Complex.normSq_nonneg _)
            (σ.eigenvalues_nonneg j))
            (InformationTheory.klFun_nonneg (div_nonneg (ρ.eigenvalues_nonneg i)
              (σ.eigenvalues_nonneg j)))
        have hnn_sum : ∀ (i : n), 0 ≤ ∑ j : n,
            Complex.normSq (W j i) * ev_σ j * InformationTheory.klFun (ev_ρ i / ev_σ j) :=
          fun i => Finset.sum_nonneg fun j _ => hterm_nn i j
        intro i j
        have houter := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnn_sum i)).mp
          hklform i (Finset.mem_univ _)
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hterm_nn i j)).mp
          houter j (Finset.mem_univ _)
      -- Derive normSq(Wji) * (ev_ρᵢ - ev_σⱼ) = 0
      have hterm_diff : ∀ (i j : n), Complex.normSq (W j i) * (ev_ρ i - ev_σ j) = 0 := by
        intro i j
        rcases (σ.eigenvalues_nonneg j).lt_or_eq with hμpos | hμzero
        · rcases mul_eq_zero.mp (hterms i j) with h1 | h2
          · rcases mul_eq_zero.mp h1 with h3 | h4
            · rw [h3, zero_mul]
            · exact absurd h4 (ne_of_gt hμpos)
          · have hkl := (InformationTheory.klFun_eq_zero_iff
                (div_nonneg (ρ.eigenvalues_nonneg i) (σ.eigenvalues_nonneg j))).mp h2
            have hev_eq : ev_ρ i = ev_σ j := by
              have := div_eq_one_iff_eq (ne_of_gt hμpos) |>.mp hkl
              exact_mod_cast this
            rw [hev_eq, sub_self, mul_zero]
        · have hev_zero : ev_σ j = 0 := hμzero.symm
          rw [hev_zero, sub_zero]
          exact suppSubset_normSq_ev_zero ρ σ h j hμzero.symm i
      -- Derive W_{ji} * ev_ρᵢ = W_{ji} * ev_σⱼ
      have hstep : ∀ (i j : n), W j i * (ev_ρ i : ℂ) = W j i * (ev_σ j : ℂ) := fun i j => by
        rcases mul_eq_zero.mp (hterm_diff i j) with h1 | h2
        · rw [Complex.normSq_eq_zero] at h1; simp [h1]
        · congr 1; exact_mod_cast sub_eq_zero.mp h2
      -- W * diag(ev_ρ) = diag(ev_σ) * W
      have hcommute : W * diagonal (fun i => (ev_ρ i : ℂ)) = diagonal (fun j => (ev_σ j : ℂ)) * W := by
        ext j i
        simp only [mul_apply, diagonal_apply, ite_mul, zero_mul, mul_ite, mul_zero]
        rw [Finset.sum_ite_eq', Finset.sum_ite_eq]
        simp only [Finset.mem_univ, ite_true]
        calc W j i * (ev_ρ i : ℂ) = W j i * (ev_σ j : ℂ) := hstep i j
          _ = (ev_σ j : ℂ) * W j i := by ring
      -- W * diag(ev_ρ) * W† = diag(ev_σ)
      have hWdiag : W * diagonal (fun i => (ev_ρ i : ℂ)) * Wᴴ = diagonal (fun j => (ev_σ j : ℂ)) := by
        calc W * diagonal (fun i => (ev_ρ i : ℂ)) * Wᴴ
            = diagonal (fun j => (ev_σ j : ℂ)) * W * Wᴴ := by rw [hcommute]
          _ = diagonal (fun j => (ev_σ j : ℂ)) * (W * Wᴴ) := by rw [Matrix.mul_assoc]
          _ = diagonal (fun j => (ev_σ j : ℂ)) := by rw [hWW, Matrix.mul_one]
      -- ρ.toMatrix = U diag(ev_ρ) Uᴴ
      have hρ_spec : ρ.toMatrix = U * diagonal (fun i => (ev_ρ i : ℂ)) * Uᴴ :=
        spectral_expand ρ.toMatrix ρ.isHermitian
      -- σ.toMatrix = V diag(ev_σ) Vᴴ
      have hσ_spec : σ.toMatrix = V * diagonal (fun j => (ev_σ j : ℂ)) * Vᴴ :=
        spectral_expand σ.toMatrix σ.isHermitian
      -- ρ.toMatrix = σ.toMatrix via: U diag(ev_ρ) Uᴴ = VW diag(ev_ρ)Wᴴ Vᴴ = V diag(ev_σ) Vᴴ
      apply DensityMatrix.ext
      rw [hρ_spec, hσ_spec, ← hVW, conjTranspose_mul]
      calc V * W * diagonal (fun i => (ev_ρ i : ℂ)) * (Wᴴ * Vᴴ)
          = V * (W * diagonal (fun i => (ev_ρ i : ℂ)) * Wᴴ) * Vᴴ := by
            simp only [Matrix.mul_assoc]
        _ = V * diagonal (fun j => (ev_σ j : ℂ)) * Vᴴ := by rw [hWdiag]
    · -- h : ¬ suppSubset ρ.toMatrix σ.toMatrix, so relativeEntropy = ⊤ ≠ 0, contradiction
      simp only [h, ↓reduceIte, EReal.top_ne_zero] at hD
  · -- ← direction: ρ = σ → D(ρ‖σ) = 0
    intro h
    subst h
    unfold relativeEntropy
    simp only [show suppSubset ρ.toMatrix ρ.toMatrix from fun _ h => h, ↓reduceIte]
    change (↑(ρ.toMatrix * (log ρ - log ρ)).trace.re : EReal) = 0
    rw [sub_self, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re, EReal.coe_zero]

/-! ### Support Subset Preservation for Channels (needed before monotonicity) -/

omit [DecidableEq n] in
/-- For a positive semidefinite matrix B, if Re[v† B v] = 0 then B v = 0. -/
private lemma mulVec_eq_zero_of_re_inner_zero'
    {B : Matrix n n ℂ} (hB : B.PosSemidef)
    (v : n → ℂ) (hv : (star v ⬝ᵥ B.mulVec v).re = 0) :
    B.mulVec v = 0 := by
  rw [← hB.dotProduct_mulVec_zero_iff]
  apply Complex.ext
  · exact hv
  · exact hB.1.im_star_dotProduct_mulVec_self v

omit [DecidableEq n] [DecidableEq m] in
/-- Support subset is preserved by a single Kraus conjugation K ρ K†. -/
private lemma suppSubset_kraus_single'
    (K : Matrix m n ℂ) {ρ σ : Matrix n n ℂ}
    (hσ : σ.PosSemidef) (h : suppSubset ρ σ) :
    suppSubset (K * ρ * Kᴴ) (K * σ * Kᴴ) := by
  intro v hv
  have hKHv_ker : σ.mulVec (Kᴴ.mulVec v) = 0 := by
    apply mulVec_eq_zero_of_re_inner_zero' hσ
    have h_eq : (star (Kᴴ.mulVec v) ⬝ᵥ σ.mulVec (Kᴴ.mulVec v)).re =
                (star v ⬝ᵥ (K * σ * Kᴴ).mulVec v).re := by
      congr 1
      conv_rhs => rw [show (K * σ * Kᴴ).mulVec v = K.mulVec (σ.mulVec (Kᴴ.mulVec v)) from by
                    simp only [← Matrix.mulVec_mulVec]]
      rw [star_mulVec, Matrix.conjTranspose_conjTranspose, ← dotProduct_mulVec]
    rw [h_eq, hv]; simp
  have hρKHv_zero : ρ.mulVec (Kᴴ.mulVec v) = 0 := h _ hKHv_ker
  simp only [show (K * ρ * Kᴴ).mulVec v = K.mulVec (ρ.mulVec (Kᴴ.mulVec v)) from by
               simp only [← Matrix.mulVec_mulVec], hρKHv_zero, Matrix.mulVec_zero]

omit [DecidableEq n] [DecidableEq m] in
/-- Support subset is preserved under finite sums of Kraus-conjugated pairs. -/
private lemma suppSubset_sum' {r : ℕ} {A B : Fin r → Matrix m m ℂ}
    (hB : ∀ k, (B k).PosSemidef)
    (h : ∀ k, suppSubset (A k) (B k)) :
    suppSubset (∑ k, A k) (∑ k, B k) := by
  intro v hv
  simp only [Matrix.sum_mulVec] at hv ⊢
  have hB_nonneg : ∀ k, 0 ≤ (star v ⬝ᵥ (B k).mulVec v).re :=
    fun k => (hB k).re_dotProduct_nonneg v
  have hsum_zero : ∑ k : Fin r, (star v ⬝ᵥ (B k).mulVec v).re = 0 := by
    have heq : (star v ⬝ᵥ ∑ k : Fin r, (B k).mulVec v).re = 0 := by rw [hv]; simp
    rw [dotProduct_sum] at heq
    simpa [Complex.re_sum] using heq
  have hB_each : ∀ k, (star v ⬝ᵥ (B k).mulVec v).re = 0 := fun k =>
    le_antisymm (by
      calc (star v ⬝ᵥ (B k).mulVec v).re
          ≤ ∑ i : Fin r, (star v ⬝ᵥ (B i).mulVec v).re :=
              Finset.single_le_sum (fun i _ => hB_nonneg i) (Finset.mem_univ k)
        _ = 0 := hsum_zero) (hB_nonneg k)
  have hBv_zero : ∀ k, (B k).mulVec v = 0 := fun k => by
    rw [← (hB k).dotProduct_mulVec_zero_iff]
    apply Complex.ext
    · exact hB_each k
    · exact (hB k).1.im_star_dotProduct_mulVec_self v
  have hAv_zero : ∀ k, (A k).mulVec v = 0 := fun k => h k v (hBv_zero k)
  simp only [hAv_zero, Finset.sum_const_zero]

omit [DecidableEq n] [DecidableEq m] in
/-- Support subset is preserved by quantum channels. -/
private lemma suppSubset_channel'
    (Φ : QuantumChannel n m)
    {ρ σ : Matrix n n ℂ} (hσ : σ.PosSemidef) (h : suppSubset ρ σ) :
    suppSubset (Φ.val ρ) (Φ.val σ) := by
  obtain ⟨r, K, hK⟩ := Φ.property.completelyPositive
  rw [hK, hK]
  exact suppSubset_sum'
    (fun k => hσ.mul_mul_conjTranspose_same (K k))
    (fun k => suppSubset_kraus_single' (K k) hσ h)

/-! ### Monotonicity of Relative Entropy -/

/-! #### Pinching method for the partial trace inequality

The proof of trace_rpow_mul_channel_le uses the pinching method (root-of-unity
unitary averaging). The proof chain is:

1. **Step 1**: F_s(VρV†, VσV†) = F_s(ρ, σ) by `rpow_conj_isometry`
2. **Stage A**: F_s(ω, τ) ≤ F_s(P(ω), P(τ)) by pinching inequality
3. **Stage B**: F_s(P(ω), P(τ)) ≤ F_s(Φρ, Φσ) by super-additivity

where P is the block-diagonal pinching map and ω = VρV†. -/

/-- Tr (ρˢ σ¹⁻ˢ) equals a double sum over eigenvalues via the
change-of-basis unitary W = U_σ† U_ρ:
  Tr (ρˢ σ¹⁻ˢ) = ∑_{i,j} |W_{ji}|² λᵢˢ μⱼ¹⁻ˢ -/
private lemma trace_rpow_mul_double_sum (ρ σ : DensityMatrix n) (s : ℝ) :
    (Tr (ρ ^ s * σ ^ (1 - s))).re =
    ∑ i : n, ∑ j : n,
      Complex.normSq (eigW ρ σ j i) *
      ρ.isHermitian.eigenvalues i ^ s *
      σ.isHermitian.eigenvalues j ^ (1 - s) := by
  change (ρ.toMatrix ^ s * σ.toMatrix ^ (1 - s)).trace.re = _
  set U := (ρ.isHermitian.eigenvectorUnitary : Matrix n n ℂ)
  set V := (σ.isHermitian.eigenvectorUnitary : Matrix n n ℂ)
  set W := eigW ρ σ
  set ev_ρ := ρ.isHermitian.eigenvalues
  set ev_σ := σ.isHermitian.eigenvalues
  have hpsdρ := ρ.posSemidef
  have hpsdσ := σ.posSemidef
  have hρs : ρ.toMatrix ^ s = U * diagonal (fun i => ((ev_ρ i ^ s : ℝ) : ℂ)) * Uᴴ := by
    rw [← matrixFunction_rpow_eq hpsdρ]; unfold matrixFunction; rfl
  have hσs : σ.toMatrix ^ (1 - s) = V * diagonal (fun j => ((ev_σ j ^ (1 - s) : ℝ) : ℂ)) * Vᴴ := by
    rw [← matrixFunction_rpow_eq hpsdσ]; unfold matrixFunction; rfl
  have hVU : Vᴴ * U = W := rfl
  rw [hρs, hσs]
  -- Use cyclic trace property and W = Vᴴ * U to reduce to W D_ρ Wᴴ D_σ
  have hWH : Wᴴ = Uᴴ * V := by rw [← hVU, conjTranspose_mul, conjTranspose_conjTranspose]
  have htrace : (U * diagonal (fun i => ((ev_ρ i ^ s : ℝ) : ℂ)) * Uᴴ *
                 (V * diagonal (fun j => ((ev_σ j ^ (1 - s) : ℝ) : ℂ)) * Vᴴ)).trace =
                (W * diagonal (fun i => ((ev_ρ i ^ s : ℝ) : ℂ)) * Wᴴ *
                 diagonal (fun j => ((ev_σ j ^ (1 - s) : ℝ) : ℂ))).trace := by
    set D1 := diagonal (fun i => ((ev_ρ i ^ s : ℝ) : ℂ))
    set D2 := diagonal (fun j => ((ev_σ j ^ (1 - s) : ℝ) : ℂ))
    -- Cyclic permutation: Tr (U D1 Uᴴ V D2 Vᴴ) = Tr (Vᴴ U D1 Uᴴ V D2)
    rw [show U * D1 * Uᴴ * (V * D2 * Vᴴ) =
        (U * D1 * Uᴴ * V * D2) * Vᴴ from by
      simp [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm]
    rw [show Vᴴ * (U * D1 * Uᴴ * V * D2) = W * D1 * Wᴴ * D2 from by
      rw [show Vᴴ * (U * D1 * Uᴴ * V * D2) = (Vᴴ * U) * D1 * (Uᴴ * V) * D2 from by
        simp [Matrix.mul_assoc]]
      rw [hVU, ← hWH]]
  rw [htrace]
  -- Expand trace elementwise and reduce diagonal selections
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply, diagonal_apply,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Complex.star_def, Complex.normSq_apply, Complex.re_sum, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

omit [DecidableEq n] in
/-- HasDerivAt for the double sum ∑_{i,j} w_{ij} λᵢˢ μⱼ¹⁻ˢ at s=1. -/
private lemma hasDerivAt_double_rpow_sum
    (w : n → n → ℝ)
    (ev1 ev2 : n → ℝ) (hev1 : ∀ i, 0 ≤ ev1 i) (hev2 : ∀ j, 0 ≤ ev2 j)
    (hsupp : ∀ j i, ev2 j = 0 → w i j * ev1 i = 0) :
    HasDerivAt (fun s : ℝ => ∑ i : n, ∑ j : n, w i j * ev1 i ^ s * ev2 j ^ (1 - s))
      (∑ i : n, ∑ j : n, w i j * ev1 i * (Real.log (ev1 i) - Real.log (ev2 j))) 1 := by
  have inner : ∀ i : n, ∀ j : n, HasDerivAt
        (fun s : ℝ => w i j * ev1 i ^ s * ev2 j ^ (1 - s))
        (w i j * ev1 i * (Real.log (ev1 i) - Real.log (ev2 j))) 1 := by
    intro i j
    rcases (hev1 i).lt_or_eq with hev1pos | hev1zero
    · rcases (hev2 j).lt_or_eq with hev2pos | hev2zero
      · have hd1 : HasDerivAt (fun s : ℝ => ev1 i ^ s) (ev1 i * Real.log (ev1 i)) 1 := by
          have := (hasDerivAt_id (𝕜 := ℝ) 1).mul_const (Real.log (ev1 i)) |>.exp
          simp only [id] at this
          have heq : (fun x => Real.exp (x * Real.log (ev1 i))) = (fun x => ev1 i ^ x) := by
            ext x; rw [Real.rpow_def_of_pos hev1pos, mul_comm]
          rw [heq] at this
          convert this using 1
          rw [one_mul, Real.exp_log hev1pos]
        have hd2 : HasDerivAt (fun s : ℝ => ev2 j ^ (1 - s)) (-(Real.log (ev2 j))) 1 := by
          have := ((hasDerivAt_const (𝕜 := ℝ) 1 (Real.log (ev2 j))).sub
              ((hasDerivAt_id (𝕜 := ℝ) 1).mul_const (Real.log (ev2 j)))).exp
          simp only [id, Pi.sub_apply] at this
          have heq : (fun x => Real.exp (Real.log (ev2 j) - x * Real.log (ev2 j))) =
                     (fun x => ev2 j ^ (1 - x)) := by
            ext x; rw [Real.rpow_def_of_pos hev2pos]; ring_nf
          rw [heq] at this
          convert this using 1
          simp only [one_mul, sub_self, Real.exp_zero, zero_sub]
        have h12 := HasDerivAt.mul hd1 hd2
        have h12c := h12.const_mul (w i j)
        simp only [Pi.mul_apply] at h12c
        convert h12c using 1
        · funext s; ring
        · simp only [Real.rpow_one, sub_self, Real.rpow_zero]; ring
      · rcases mul_eq_zero.mp (hsupp j i hev2zero.symm) with hw0 | hev10
        · simp only [hw0, zero_mul]; exact hasDerivAt_const _ _
        · linarith
    · simp only [← hev1zero, mul_zero, zero_mul]
      apply (hasDerivAt_const (𝕜 := ℝ) (1:ℝ) (0:ℝ)).congr_of_eventuallyEq
      apply Filter.eventually_of_mem (Ioi_mem_nhds (show (0:ℝ) < 1 from by norm_num))
      intro s hs
      simp only [Set.mem_Ioi] at hs
      simp only [Real.zero_rpow (ne_of_gt hs), mul_zero, zero_mul]
  have outer : ∀ i : n, HasDerivAt
        (fun s : ℝ => ∑ j : n, w i j * ev1 i ^ s * ev2 j ^ (1 - s))
        (∑ j : n, w i j * ev1 i * (Real.log (ev1 i) - Real.log (ev2 j))) 1 := by
    intro i
    have h := HasDerivAt.sum (u := Finset.univ) (fun j (_ : j ∈ Finset.univ) => inner i j)
    have heq : (∑ j ∈ Finset.univ, fun s : ℝ => w i j * ev1 i ^ s * ev2 j ^ (1 - s)) =
               (fun s : ℝ => ∑ j : n, w i j * ev1 i ^ s * ev2 j ^ (1 - s)) :=
      funext (fun s => Finset.sum_apply _ _ _)
    rwa [heq] at h
  have h_final := HasDerivAt.sum (u := Finset.univ) (fun i (_ : i ∈ Finset.univ) => outer i)
  have heq : (∑ i ∈ Finset.univ, fun s : ℝ => ∑ j : n, w i j * ev1 i ^ s * ev2 j ^ (1 - s)) =
             (fun s : ℝ => ∑ i : n, ∑ j : n, w i j * ev1 i ^ s * ev2 j ^ (1 - s)) :=
    funext (fun s => Finset.sum_apply _ _ _)
  rwa [heq] at h_final

/-- HasDerivAt of Re[Tr (ρˢ σ¹⁻ˢ)] at s=1 equals D(ρ ‖ σ).

When supp(ρ) ⊆ supp(σ):
  (d/ds)|_{s=1} Tr (ρˢ σ¹⁻ˢ) = Tr (ρ(log ρ − log σ)) = D(ρ ‖ σ) -/
private lemma hasDerivAt_trace_rpow_mul (ρ σ : DensityMatrix n) (h : suppSubset ρ.toMatrix σ.toMatrix) :
    HasDerivAt (fun s : ℝ => (Tr (ρ ^ s * σ ^ (1 - s))).re)
      ((Tr (ρ * (log ρ - log σ))).re) 1 := by
  change HasDerivAt (fun s : ℝ => (ρ.toMatrix ^ s * σ.toMatrix ^ (1 - s)).trace.re)
    ((ρ.toMatrix * (log ρ - log σ)).trace.re) 1
  set ev_ρ := ρ.isHermitian.eigenvalues
  set ev_σ := σ.isHermitian.eigenvalues
  set W := eigW ρ σ
  have hconv : (fun s : ℝ => (ρ.toMatrix ^ s * σ.toMatrix ^ (1 - s)).trace.re) = fun s =>
      ∑ i : n, ∑ j : n, Complex.normSq (W j i) * ev_ρ i ^ s * ev_σ j ^ (1 - s) :=
    funext (trace_rpow_mul_double_sum ρ σ)
  rw [hconv]
  have hderiv := hasDerivAt_double_rpow_sum
    (fun i j => Complex.normSq (W j i))
    ev_ρ ev_σ ρ.eigenvalues_nonneg σ.eigenvalues_nonneg
    (fun j i hμ => by
      have := suppSubset_normSq_ev_zero ρ σ h j hμ i
      linarith [mul_nonneg (Complex.normSq_nonneg (W j i)) (ρ.eigenvalues_nonneg i)])
  convert hderiv using 1
  simp only []  -- beta-reduce lambda in hderiv's derivative form
  -- Relate derivative to D(ρ‖σ) = Tr (ρ(log ρ)) - Tr (ρ(log σ))
  rw [Matrix.mul_sub, trace_sub, Complex.sub_re, trace_ρlogρ_eq ρ, trace_ρlogσ_eq ρ σ]
  -- Rewrite Σᵢ evᵢ log evᵢ as Σᵢⱼ |Wji|² evᵢ log evᵢ (using column sum = 1)
  have h1 : ∑ i : n, ev_ρ i * Real.log (ev_ρ i) =
            ∑ i : n, ∑ j : n, Complex.normSq (W j i) * ev_ρ i * Real.log (ev_ρ i) := by
    congr 1; ext i
    rw [← Finset.sum_mul, ← Finset.sum_mul,
        show ∑ j : n, Complex.normSq (W j i) = 1 from eigW_unitary_colsum ρ σ i]
    ring
  rw [h1, ← Finset.sum_sub_distrib]; congr 1; ext i
  rw [← Finset.sum_sub_distrib]; congr 1; ext j; ring

/-! #### Isometry and unitary invariance of F_s -/

/-- Unitary invariance of F_s: Tr ((UAU†)ˢ (UBU†)¹⁻ˢ) = Tr (Aˢ B¹⁻ˢ) for unitary U.

Proof: By `rpow_unitary_conj`, (UAU†)ˢ = U Aˢ U†.
Then trace cyclicity gives Tr (U Aˢ U† U B¹⁻ˢ U†) =
Tr (Aˢ (U†U) B¹⁻ˢ (U†U)) = Tr (Aˢ B¹⁻ˢ). -/
private lemma trace_rpow_mul_unitary_conj_eq
    {α : Type*} [Fintype α] [DecidableEq α]
    (U : Matrix α α ℂ) (hU : U ∈ Matrix.unitaryGroup α ℂ)
    (A B : Matrix α α ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    (Tr ((U * A * Uᴴ) ^ s * (U * B * Uᴴ) ^ (1 - s))).re =
    (Tr (A ^ s * B ^ (1 - s))).re := by
  have h1s_pos : 0 < 1 - s := by linarith
  have hA' : (0 : Matrix α α ℂ) ≤ A := by rw [Matrix.le_iff, sub_zero]; exact hA
  have hB' : (0 : Matrix α α ℂ) ≤ B := by rw [Matrix.le_iff, sub_zero]; exact hB
  have hUA' : (0 : Matrix α α ℂ) ≤ U * A * Uᴴ := by
    rw [Matrix.le_iff, sub_zero]; exact hA.mul_mul_conjTranspose_same U
  have hUB' : (0 : Matrix α α ℂ) ≤ U * B * Uᴴ := by
    rw [Matrix.le_iff, sub_zero]; exact hB.mul_mul_conjTranspose_same U
  rw [rpow_unitary_conj hU hs0.le hA' hUA',
      rpow_unitary_conj hU h1s_pos.le hB' hUB']
  -- Now: Tr (U A^s Uᴴ * U B^{1-s} Uᴴ)
  have hUHU : Uᴴ * U = 1 := by
    rw [← star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hU
  have heq : U * A ^ s * Uᴴ * (U * B ^ (1 - s) * Uᴴ) =
             U * (A ^ s * B ^ (1 - s)) * Uᴴ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U _, hUHU, Matrix.one_mul]
  rw [heq]
  rw [Matrix.trace_mul_comm (U * (A ^ s * B ^ (1 - s))) Uᴴ,
      show Uᴴ * (U * (A ^ s * B ^ (1 - s))) = A ^ s * B ^ (1 - s) by
        rw [← Matrix.mul_assoc, hUHU, Matrix.one_mul]]

/-- Isometry invariance of F_s: F_s(VρV†, VσV†) = F_s(ρ, σ)
when V†V = I.

Proof: By `rpow_conj_isometry`, (VAV†)ˢ = V Aˢ V†.
Then trace cyclicity and V†V = I yield the result. -/
private lemma trace_rpow_mul_isometry_conj_eq
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (V : Matrix β α ℂ) (hV : Vᴴ * V = 1)
    (A B : Matrix α α ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    (Tr ((V * A * Vᴴ) ^ s * (V * B * Vᴴ) ^ (1 - s))).re =
    (Tr (A ^ s * B ^ (1 - s))).re := by
  have h1s_pos : 0 < 1 - s := by linarith
  have hVA_psd := hA.mul_mul_conjTranspose_same V
  have hVB_psd := hB.mul_mul_conjTranspose_same V
  rw [rpow_conj_isometry V hV A hA s hs0,
      rpow_conj_isometry V hV B hB (1 - s) h1s_pos]
  -- Now: Tr (V A^s Vᴴ * V B^{1-s} Vᴴ)
  have heq : V * A ^ s * Vᴴ * (V * B ^ (1 - s) * Vᴴ) =
             V * (A ^ s * B ^ (1 - s)) * Vᴴ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Vᴴ V _, hV, Matrix.one_mul]
  rw [heq]
  rw [Matrix.trace_mul_comm (V * (A ^ s * B ^ (1 - s))) Vᴴ,
      show Vᴴ * (V * (A ^ s * B ^ (1 - s))) = A ^ s * B ^ (1 - s) by
        rw [← Matrix.mul_assoc, hV, Matrix.one_mul]]

/-! #### Block-diagonal decomposition of F_s -/

/-- For `Fin 1 × m`, rpow of a PSD matrix commutes with submatrix extraction at block 0.
Uses `StarAlgHomClass.map_cfc` to show CFC commutes with reindexing. -/
private lemma rpow_submatrix_fin_one
    {A : Matrix (Fin 1 × m) (Fin 1 × m) ℂ} (hA : A.PosSemidef)
    {p : ℝ} (hp : 0 ≤ p) :
    (A ^ p).submatrix (Prod.mk (0 : Fin 1)) (Prod.mk 0) =
    (A.submatrix (Prod.mk 0) (Prod.mk 0)) ^ p := by
  classical
  -- Set up normed algebra and C*-algebra instances
  letI : NormedRing (Matrix (Fin 1 × m) (Fin 1 × m) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin 1 × m) (Fin 1 × m) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : CStarAlgebra (Matrix (Fin 1 × m) (Fin 1 × m) ℂ) := by
    simpa [CStarMatrix] using CStarMatrix.instCStarAlgebra (n := Fin 1 × m) (A := ℂ)
  letI : NormedRing (Matrix m m ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra
  letI : CStarAlgebra (Matrix m m ℂ) := by
    simpa [CStarMatrix] using CStarMatrix.instCStarAlgebra (n := m) (A := ℂ)
  -- Equivalence e : Fin 1 × m ≃ m (canonical)
  let e := Equiv.uniqueProd m (Fin 1)
  -- Construct StarAlgEquiv from reindexAlgEquiv
  let ψ : Matrix (Fin 1 × m) (Fin 1 × m) ℂ ≃⋆ₐ[ℝ] Matrix m m ℂ :=
    StarAlgEquiv.ofAlgEquiv (Matrix.reindexAlgEquiv ℝ ℂ e) (fun M => by
      ext i j
      simp only [star_eq_conjTranspose, Matrix.conjTranspose_apply,
        Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply])
  -- ψ acts as submatrix extraction at block 0
  have hψ_apply : ∀ (M : Matrix (Fin 1 × m) (Fin 1 × m) ℂ),
      ψ M = M.submatrix (Prod.mk (0 : Fin 1)) (Prod.mk 0) := by
    intro M; ext i j
    simp only [ψ, StarAlgEquiv.ofAlgEquiv_apply, Matrix.reindexAlgEquiv_apply,
      Matrix.reindex_apply, Matrix.submatrix_apply, e, Equiv.uniqueProd_symm_apply,
      Fin.default_eq_zero]
  -- Self-adjointness for CFC
  have hA_sa : IsSelfAdjoint A := hA.1.isSelfAdjoint
  have hψA_sa : IsSelfAdjoint (ψ A) := by
    rw [IsSelfAdjoint, ← map_star ψ]; exact congr_arg ψ hA_sa.star_eq
  -- Positivity
  have hA_le : (0 : Matrix (Fin 1 × m) (Fin 1 × m) ℂ) ≤ A := by
    simpa [Matrix.le_iff] using hA
  have hψA_le : 0 ≤ ψ A := by
    rw [hψ_apply]; simpa [Matrix.le_iff] using hA.submatrix (Prod.mk (0 : Fin 1))
  -- Continuity of ψ (finite-dimensional)
  have hψ_cont : Continuous ψ :=
    ψ.toAlgEquiv.toLinearMap.continuous_of_finiteDimensional
  -- Convert LHS rpow to CFC
  rw [CFC.rpow_eq_cfc_real (a := A) (ha := hA_le)]
  -- Rewrite: (cfc f A).sub = ψ (cfc f A)
  conv_lhs => rw [show (cfc (HPow.hPow · p) A).submatrix (Prod.mk (0 : Fin 1)) (Prod.mk 0)
    = ψ (cfc (HPow.hPow · p) A) from (hψ_apply _).symm]
  -- Apply map_cfc: ψ (cfc f A) = cfc f (ψ A)
  rw [StarAlgHomClass.map_cfc (R := ℝ) (S := ℝ) ψ (HPow.hPow · p) A
    ((Real.continuous_rpow_const hp).continuousOn) hψ_cont hA_sa hψA_sa]
  -- Goal: cfc (· ^ p) (ψ A) = (A.sub ...) ^ p
  rw [hψ_apply A]
  -- Goal: cfc (· ^ p) (A.sub) = (A.sub) ^ p
  exact (CFC.rpow_eq_cfc_real (a := A.submatrix (Prod.mk (0 : Fin 1)) (Prod.mk 0))
    (ha := by simpa [Matrix.le_iff] using hA.submatrix (Prod.mk (0 : Fin 1)))).symm

/-- **Pinching inequality for F_s**: For PSD matrices ω, τ on (Fin r × m),
  F_s(ω, τ) ≤ ∑ᵢ F_s(ωᵢᵢ, τᵢᵢ)
where ωᵢᵢ denotes the i-th diagonal block.

Proved via joint concavity of F_s under uniform averaging + unitary invariance + block decomposition. -/
private lemma pinching_inequality_Fs {r : ℕ} [NeZero r]
    (ω τ : Matrix (Fin r × m) (Fin r × m) ℂ) (hω : ω.PosSemidef) (hτ : τ.PosSemidef)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    (Tr (ω ^ s * τ ^ (1 - s))).re ≤
    ∑ k : Fin r, (Tr ((ω.submatrix (Prod.mk k) (Prod.mk k)) ^ s *
                  (τ.submatrix (Prod.mk k) (Prod.mk k)) ^ (1 - s))).re := by
  -- The pinching inequality follows from joint concavity of F_s.
  -- Define P(ω) = (1/r) Σ_k U_k ω U_k† where U_k are the pinching unitaries.
  -- Step 1: P(ω) is block-diagonal with blocks ω_ii
  -- Step 2: F_s(P(ω), P(τ)) ≥ (1/r) Σ_k F_s(U_k ω U_k†, U_k τ U_k†) by joint concavity
  -- Step 3: F_s(U_k ω U_k†, U_k τ U_k†) = F_s(ω, τ) by unitary invariance
  -- Step 4: F_s(P(ω), P(τ)) ≥ F_s(ω, τ)
  -- Step 5: For block-diagonal P(ω), F_s(P(ω), P(τ)) = Σ_i F_s(ω_ii, τ_ii)
  -- Combining: F_s(ω, τ) ≤ Σ_i F_s(ω_ii, τ_ii)
  have h1s_pos : 0 < 1 - s := by linarith
  -- The diagonal blocks are PSD
  have hω_block_psd : ∀ k : Fin r, (ω.submatrix (Prod.mk k) (Prod.mk k)).PosSemidef :=
    fun k => hω.submatrix _
  have hτ_block_psd : ∀ k : Fin r, (τ.submatrix (Prod.mk k) (Prod.mk k)).PosSemidef :=
    fun k => hτ.submatrix _
  -- The trace on (Fin r × m) decomposes as sum over blocks
  -- Tr (A) = Σ_i Σ_a A_{(i,a)(i,a)} = Σ_i Tr_m[A.submatrix (Prod.mk i) (Prod.mk i)]
  have htrace_decomp : ∀ A : Matrix (Fin r × m) (Fin r × m) ℂ,
      A.trace = ∑ i : Fin r, (A.submatrix (Prod.mk i) (Prod.mk i)).trace := by
    intro A
    simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
    rw [← Finset.sum_product']
    rfl
  -- Induction on r, using 2-block fromBlocks decomposition at each step
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    rcases r with _ | _ | r
    · -- r = 0: vacuous
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      have hempty : IsEmpty (Fin 0 × m) := by infer_instance
      rw [Matrix.trace_eq_zero_of_isEmpty, Complex.zero_re]
    · -- r = 1: single block, equality
      rw [Fin.sum_univ_one, htrace_decomp (ω ^ s * τ ^ (1 - s)), Fin.sum_univ_one]
      apply le_of_eq; congr 1; congr 1
      -- submatrix of product = product of submatrices via reindexAlgEquiv
      let e : Fin (0 + 1) × m ≃ m :=
        { toFun := fun p => p.2
          invFun := fun a => (0, a)
          left_inv := fun ⟨i, a⟩ => Prod.ext (Fin.eq_zero i).symm rfl
          right_inv := fun _ => rfl }
      have hsub_eq : ∀ (M : Matrix (Fin (0 + 1) × m) (Fin (0 + 1) × m) ℂ),
          M.submatrix (Prod.mk (0 : Fin (0 + 1))) (Prod.mk 0) =
          Matrix.reindexAlgEquiv ℝ ℂ e M := by
        intro M; ext i j; rfl
      rw [hsub_eq, map_mul, ← hsub_eq, ← hsub_eq]
      -- rpow commutes with submatrix
      congr 1
      · exact rpow_submatrix_fin_one hω (le_of_lt hs0)
      · exact rpow_submatrix_fin_one hτ (le_of_lt h1s_pos)
    · -- r ≥ 2: use 2-block splitting and induction
      haveI : NeZero (r + 2) := ⟨by omega⟩
      -- Lieb concavity with (r+2)-block pinching gives F_s(ω,τ) ≤ F_s(P(ω),P(τ))
      have hr_pos : (0 : ℝ) < r + 2 := by positivity
      have hw_sum : ∑ k : Fin (r + 2), (1 / (r + 2 : ℝ)) = 1 := by
        simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
        rw [show ((r + 2 : ℕ) : ℝ) = (r : ℝ) + 2 from Nat.cast_add r 2]
        field_simp
      have hw_nn : ∀ k : Fin (r + 2), 0 ≤ (1 / (r + 2 : ℝ)) := fun _ => by positivity
      let U := pinchingUnitary (m := m) (r + 2)
      let A := fun k => U k * ω * (U k)ᴴ
      let B := fun k => U k * τ * (U k)ᴴ
      have hA_psd : ∀ k, (A k).PosSemidef := fun k => hω.mul_mul_conjTranspose_same (U k)
      have hB_psd : ∀ k, (B k).PosSemidef := fun k => hτ.mul_mul_conjTranspose_same (U k)
      have hconc := lieb_concavity_weighted A B hA_psd hB_psd
        (fun _ => 1 / (r + 2 : ℝ)) hw_nn hw_sum s hs0.le hs1.le
      have hunitary : ∀ k, ((A k) ^ s * (B k) ^ (1 - s)).trace.re =
          (ω ^ s * τ ^ (1 - s)).trace.re := fun k =>
        trace_rpow_mul_unitary_conj_eq (U k) (pinchingUnitary_isUnitary k) ω τ hω hτ s hs0 hs1
      simp only [hunitary] at hconc
      simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul] at hconc
      rw [show ((r + 2 : ℕ) : ℝ) = (r : ℝ) + 2 from Nat.cast_add r 2, ← mul_assoc] at hconc
      have hmul_cancel : ((r : ℝ) + 2) * (1 / ((r : ℝ) + 2)) = 1 := by field_simp
      rw [hmul_cancel, one_mul] at hconc
      -- Set abbreviations for pinching averages
      set Pω := ∑ k : Fin (r + 2), (1 / (r + 2 : ℝ)) • A k with hPω_def
      set Pτ := ∑ k : Fin (r + 2), (1 / (r + 2 : ℝ)) • B k with hPτ_def
      -- P(ω) is block-diagonal
      have hPω_entry : ∀ i j : Fin (r + 2), ∀ a b : m,
          Pω (i, a) (j, b) = if i = j then ω (i, a) (j, b) else 0 := by
        intro i j a b
        change (∑ k, (1 / (r + 2 : ℝ)) • A k) (i, a) (j, b) = _
        simp_rw [Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul, ← Finset.mul_sum]
        convert pinching_average_eq_blockDiag ω i j a b using 2
        push_cast; ring
      have hPτ_entry : ∀ i j : Fin (r + 2), ∀ a b : m,
          Pτ (i, a) (j, b) = if i = j then τ (i, a) (j, b) else 0 := by
        intro i j a b
        change (∑ k, (1 / (r + 2 : ℝ)) • B k) (i, a) (j, b) = _
        simp_rw [Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul, ← Finset.mul_sum]
        convert pinching_average_eq_blockDiag τ i j a b using 2
        push_cast; ring
      -- Pinching averages are PSD
      have hPω_psd : Pω.PosSemidef := by
        apply posSemidef_sum
        intro k _
        exact (hA_psd k).smul (hw_nn k)
      have hPτ_psd : Pτ.PosSemidef := by
        apply posSemidef_sum
        intro k _
        exact (hB_psd k).smul (hw_nn k)
      -- Restriction to blocks 1..r+1
      let embed : Fin (r + 1) × m → Fin (r + 2) × m := fun ⟨i, a⟩ => (i.succ, a)
      let Qω := Pω.submatrix embed embed
      let Qτ := Pτ.submatrix embed embed
      have hQω_psd : Qω.PosSemidef := hPω_psd.submatrix _
      have hQτ_psd : Qτ.PosSemidef := hPτ_psd.submatrix _
      -- Q blocks match ω blocks
      have hQ_block_ω : ∀ i : Fin (r + 1),
          Qω.submatrix (Prod.mk i) (Prod.mk i) =
          ω.submatrix (Prod.mk (i.succ)) (Prod.mk i.succ) := by
        intro i; ext a b
        change Pω (i.succ, a) (i.succ, b) = ω (i.succ, a) (i.succ, b)
        rw [hPω_entry]; simp
      have hQ_block_τ : ∀ i : Fin (r + 1),
          Qτ.submatrix (Prod.mk i) (Prod.mk i) =
          τ.submatrix (Prod.mk (i.succ)) (Prod.mk i.succ) := by
        intro i; ext a b
        change Pτ (i.succ, a) (i.succ, b) = τ (i.succ, a) (i.succ, b)
        rw [hPτ_entry]; simp
      -- Block 0 matrices
      let ω₀₀ := ω.submatrix (Prod.mk (0 : Fin (r + 2))) (Prod.mk 0)
      let τ₀₀ := τ.submatrix (Prod.mk (0 : Fin (r + 2))) (Prod.mk 0)
      -- Reindex via ψ to show P(ω) = fromBlocks ω₀₀ 0 0 Qω
      classical
      letI : NormedRing (Matrix (Fin (r + 2) × m) (Fin (r + 2) × m) ℂ) :=
        Matrix.linftyOpNormedRing
      letI : NormedAlgebra ℝ (Matrix (Fin (r + 2) × m) (Fin (r + 2) × m) ℂ) :=
        Matrix.linftyOpNormedAlgebra
      letI : CStarAlgebra (Matrix (Fin (r + 2) × m) (Fin (r + 2) × m) ℂ) := by
        simpa [CStarMatrix] using CStarMatrix.instCStarAlgebra (n := Fin (r + 2) × m) (A := ℂ)
      letI : NormedRing (Matrix m m ℂ) := Matrix.linftyOpNormedRing
      letI : NormedAlgebra ℝ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra
      letI : CStarAlgebra (Matrix m m ℂ) := by
        simpa [CStarMatrix] using CStarMatrix.instCStarAlgebra (n := m) (A := ℂ)
      letI : NormedRing (Matrix (Fin (r + 1) × m) (Fin (r + 1) × m) ℂ) :=
        Matrix.linftyOpNormedRing
      letI : NormedAlgebra ℝ (Matrix (Fin (r + 1) × m) (Fin (r + 1) × m) ℂ) :=
        Matrix.linftyOpNormedAlgebra
      letI : CStarAlgebra (Matrix (Fin (r + 1) × m) (Fin (r + 1) × m) ℂ) := by
        simpa [CStarMatrix] using CStarMatrix.instCStarAlgebra (n := Fin (r + 1) × m) (A := ℂ)
      -- Reindex equivalence
      let e := splitFinSuccProdEquiv (r + 1) m
      -- Build star algebra equivalence ψ
      let ψ : Matrix (Fin (r + 2) × m) (Fin (r + 2) × m) ℂ ≃⋆ₐ[ℝ]
          Matrix (m ⊕ (Fin (r + 1) × m)) (m ⊕ (Fin (r + 1) × m)) ℂ :=
        StarAlgEquiv.ofAlgEquiv (Matrix.reindexAlgEquiv ℝ ℂ e) (fun M => by
          ext i j
          simp only [star_eq_conjTranspose, Matrix.conjTranspose_apply,
            Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply])
      -- Key: ψ M = M.submatrix e.symm e.symm
      have hψ_eq : ∀ M : Matrix (Fin (r + 2) × m) (Fin (r + 2) × m) ℂ,
          ψ M = M.submatrix e.symm e.symm := by
        intro M; rfl
      -- e.symm on Sum.inl and Sum.inr
      have he_inl : ∀ a : m, e.symm (Sum.inl a) = (⟨0, by omega⟩, a) := by
        intro a; rfl
      have he_inr : ∀ (i : Fin (r + 1)) (a : m), e.symm (Sum.inr (i, a)) = (i.succ, a) := by
        intro ⟨i, hi⟩ a; rfl
      -- ψ(Pω) = fromBlocks ω₀₀ 0 0 Qω
      have hψPω : ψ Pω = Matrix.fromBlocks ω₀₀ 0 0 Qω := by
        ext (a | ⟨i, a⟩) (b | ⟨j, b⟩)
        · simp only [hψ_eq, Matrix.submatrix_apply, he_inl, Matrix.fromBlocks_apply₁₁]
          exact hPω_entry 0 0 a b |>.trans (if_pos rfl)
        · simp only [hψ_eq, Matrix.submatrix_apply, he_inl, he_inr, Matrix.fromBlocks_apply₁₂]
          exact hPω_entry 0 j.succ a b |>.trans (if_neg (Fin.succ_ne_zero j).symm)
        · simp only [hψ_eq, Matrix.submatrix_apply, he_inl, he_inr, Matrix.fromBlocks_apply₂₁]
          exact hPω_entry i.succ 0 a b |>.trans (if_neg (Fin.succ_ne_zero i))
        · simp only [hψ_eq, Matrix.submatrix_apply, he_inr,
            Matrix.fromBlocks_apply₂₂, Qω, embed]
      have hψPτ : ψ Pτ = Matrix.fromBlocks τ₀₀ 0 0 Qτ := by
        ext (a | ⟨i, a⟩) (b | ⟨j, b⟩)
        · simp only [hψ_eq, Matrix.submatrix_apply, he_inl, Matrix.fromBlocks_apply₁₁]
          exact hPτ_entry 0 0 a b |>.trans (if_pos rfl)
        · simp only [hψ_eq, Matrix.submatrix_apply, he_inl, he_inr, Matrix.fromBlocks_apply₁₂]
          exact hPτ_entry 0 j.succ a b |>.trans (if_neg (Fin.succ_ne_zero j).symm)
        · simp only [hψ_eq, Matrix.submatrix_apply, he_inl, he_inr, Matrix.fromBlocks_apply₂₁]
          exact hPτ_entry i.succ 0 a b |>.trans (if_neg (Fin.succ_ne_zero i))
        · simp only [hψ_eq, Matrix.submatrix_apply, he_inr,
            Matrix.fromBlocks_apply₂₂, Qτ, embed]
      -- ψ preserves trace
      have hψ_trace : ∀ M : Matrix (Fin (r + 2) × m) (Fin (r + 2) × m) ℂ,
          (ψ M).trace = M.trace := by
        intro M
        simp only [hψ_eq, Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
        exact Fintype.sum_equiv e.symm _ _ (fun i => rfl)
      -- ψ preserves rpow (via CFC)
      have hψ_rpow : ∀ (M : Matrix (Fin (r + 2) × m) (Fin (r + 2) × m) ℂ),
          M.PosSemidef → ∀ p : ℝ, 0 < p → ψ (M ^ p) = (ψ M) ^ p := by
        intro M hM p hp
        have hM_sa := hM.1.isSelfAdjoint
        have hM_le : (0 : Matrix _ _ ℂ) ≤ M := by rw [Matrix.le_iff, sub_zero]; exact hM
        have hψM_sa : IsSelfAdjoint (ψ M) := by
          rw [IsSelfAdjoint, ← map_star ψ]; exact congr_arg ψ hM_sa.star_eq
        have hψM_le : (0 : Matrix _ _ ℂ) ≤ ψ M := by
          rw [Matrix.le_iff, sub_zero]
          exact hM.submatrix e.symm
        rw [CFC.rpow_eq_cfc_real (ha := hM_le), CFC.rpow_eq_cfc_real (ha := hψM_le)]
        rw [StarAlgHomClass.map_cfc (R := ℝ) (S := ℝ) ψ _ M
          ((Real.continuous_rpow_const (by linarith)).continuousOn)
          (ψ.toAlgEquiv.toLinearMap.continuous_of_finiteDimensional)
          hM_sa hψM_sa]
      -- Trace splits into block 0 + remaining blocks
      have htrace_split :
          (Pω ^ s * Pτ ^ (1 - s)).trace.re =
          (ω₀₀ ^ s * τ₀₀ ^ (1 - s)).trace.re + (Qω ^ s * Qτ ^ (1 - s)).trace.re := by
        conv_lhs => rw [show (Pω ^ s * Pτ ^ (1 - s)).trace =
          (ψ (Pω ^ s * Pτ ^ (1 - s))).trace from (hψ_trace _).symm]
        rw [map_mul, hψ_rpow Pω hPω_psd s hs0, hψ_rpow Pτ hPτ_psd (1 - s) h1s_pos,
            hψPω, hψPτ]
        rw [fromBlocks_diag_rpow (hω_block_psd 0) hQω_psd (p := s) hs0,
            fromBlocks_diag_rpow (hτ_block_psd 0) hQτ_psd (p := 1 - s) h1s_pos]
        simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
        rw [trace_fromBlocks]
        simp only [Complex.add_re]
        rfl
      -- Apply IH to Q (r+1 blocks)
      haveI : NeZero (r + 1) := ⟨by omega⟩
      have hQ_block_psd_ω : ∀ k : Fin (r + 1),
          (Qω.submatrix (Prod.mk k) (Prod.mk k)).PosSemidef := by
        intro k; rw [hQ_block_ω k]; exact hω_block_psd k.succ
      have hQ_block_psd_τ : ∀ k : Fin (r + 1),
          (Qτ.submatrix (Prod.mk k) (Prod.mk k)).PosSemidef := by
        intro k; rw [hQ_block_τ k]; exact hτ_block_psd k.succ
      have hIH : (Qω ^ s * Qτ ^ (1 - s)).trace.re ≤
          ∑ k : Fin (r + 1), ((Qω.submatrix (Prod.mk k) (Prod.mk k)) ^ s *
            (Qτ.submatrix (Prod.mk k) (Prod.mk k)) ^ (1 - s)).trace.re := by
        exact ih (r + 1) (by omega) Qω Qτ hQω_psd hQτ_psd hQ_block_psd_ω hQ_block_psd_τ
          (fun A' => by simp [Matrix.trace, Matrix.diag, Matrix.submatrix_apply,
            ← Finset.sum_product'])
      calc (ω ^ s * τ ^ (1 - s)).trace.re
          ≤ (Pω ^ s * Pτ ^ (1 - s)).trace.re := hconc
        _ = (ω₀₀ ^ s * τ₀₀ ^ (1 - s)).trace.re +
            (Qω ^ s * Qτ ^ (1 - s)).trace.re := htrace_split
        _ ≤ (ω₀₀ ^ s * τ₀₀ ^ (1 - s)).trace.re +
            ∑ k : Fin (r + 1), ((Qω.submatrix (Prod.mk k) (Prod.mk k)) ^ s *
              (Qτ.submatrix (Prod.mk k) (Prod.mk k)) ^ (1 - s)).trace.re := by
          linarith [hIH]
        _ = ∑ i : Fin (r + 2), ((ω.submatrix (Prod.mk i) (Prod.mk i)) ^ s *
              (τ.submatrix (Prod.mk i) (Prod.mk i)) ^ (1 - s)).trace.re := by
          -- Rewrite as sum over Fin (r+2) = {0} ∪ {1,..,r+1}
          conv_rhs => rw [Fin.sum_univ_succ]
          dsimp only [ω₀₀, τ₀₀]
          simp only [hQ_block_ω, hQ_block_τ]

/-- **Channel inequality for F_s**: Quantum channels increase Tr (ρˢσ¹⁻ˢ).

For a quantum channel Φ and density matrices ρ, σ, for s ∈ (0,1]:
  Tr (ρˢ σ¹⁻ˢ) ≤ Tr ((Φρ)ˢ (Φσ)¹⁻ˢ)

**Proof** (Stinespring + pinching + weighted Lieb concavity):
1. F_s(VρV†, VσV†) = F_s(ρ, σ) by `rpow_conj_isometry`
2. **Stage A**: F_s(ω, τ) ≤ F_s(P(ω), P(τ)) — the pinching inequality,
   proved via root-of-unity unitary averaging + concavity.
3. **Stage B**: F_s(P(ω), P(τ)) ≤ F_s(Φρ, Φσ) — from weighted
   Lieb concavity with w_k = 1/r. -/
private lemma trace_rpow_mul_channel_le
    (Φ : QuantumChannel n m)
    (ρ σ : DensityMatrix n) (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    (Tr (ρ ^ s * σ ^ (1 - s))).re ≤
    (Tr ((Φ.val ↑ρ) ^ s * (Φ.val ↑σ) ^ (1 - s))).re := by
  change (ρ.toMatrix ^ s * σ.toMatrix ^ (1 - s)).trace.re ≤
    ((Φ.val ρ.toMatrix) ^ s * (Φ.val σ.toMatrix) ^ (1 - s)).trace.re
  -- s = 1: both sides equal Tr (ρ) by trace-preservation
  by_cases hs1_eq : s = 1
  · subst hs1_eq
    simp only [sub_self]
    have hρ_psd := ρ.posSemidef
    have hσ_psd := σ.posSemidef
    have hΦρ_psd := (Φ ρ).posSemidef
    have hΦσ_psd := (Φ σ).posSemidef
    rw [CFC.rpow_zero σ.toMatrix (by rw [Matrix.le_iff, sub_zero]; exact hσ_psd),
        CFC.rpow_zero (Φ.val σ.toMatrix) (by rw [Matrix.le_iff, sub_zero]; exact hΦσ_psd),
        CFC.rpow_one ρ.toMatrix (by rw [Matrix.le_iff, sub_zero]; exact hρ_psd),
        CFC.rpow_one (Φ.val ρ.toMatrix) (by rw [Matrix.le_iff, sub_zero]; exact hΦρ_psd),
        Matrix.mul_one, Matrix.mul_one]
    have hTP := Φ.property.tracePreserving ρ.toMatrix
    rw [hTP]
  · -- s < 1: Stinespring isometry + pinching + super-additivity
    have hs1_lt : s < 1 := lt_of_le_of_ne hs1 hs1_eq
    have h1s_pos : 0 < 1 - s := by linarith
    obtain ⟨r, K, hKraus⟩ := Φ.property.completelyPositive
    have hKsum := Φ.kraus_sum_eq_one hKraus
    have hK_ρ_psd : ∀ i, (K i * ρ.toMatrix * (K i)ᴴ).PosSemidef :=
      fun i => ρ.posSemidef.mul_mul_conjTranspose_same (K i)
    have hK_σ_psd : ∀ i, (K i * σ.toMatrix * (K i)ᴴ).PosSemidef :=
      fun i => σ.posSemidef.mul_mul_conjTranspose_same (K i)
    have hΦρ_psd := (Φ ρ).posSemidef
    have hΦσ_psd := (Φ σ).posSemidef
    -- Stage B: super-additivity Σᵢ F_s(KᵢρKᵢ†, KᵢσKᵢ†) ≤ F_s(Φρ, Φσ)
    have hsum_le := lieb_concavity_sum
      (fun i => K i * ρ.toMatrix * (K i)ᴴ)
      (fun i => K i * σ.toMatrix * (K i)ᴴ)
      hK_ρ_psd hK_σ_psd s hs0.le hs1
    have hΦρ_eq : ∑ i : Fin r, K i * ρ.toMatrix * (K i)ᴴ = Φ.val ρ.toMatrix := (hKraus ρ.toMatrix).symm
    have hΦσ_eq : ∑ i : Fin r, K i * σ.toMatrix * (K i)ᴴ = Φ.val σ.toMatrix := (hKraus σ.toMatrix).symm
    rw [hΦρ_eq, hΦσ_eq] at hsum_le
    -- Stage A: pinching inequality F_s(ρ, σ) ≤ Σᵢ F_s(KᵢρKᵢ†, KᵢσKᵢ†)
    rcases r with _ | r
    · -- r = 0: contradicts trace-preservation
      simp only [Finset.univ_eq_empty, Finset.sum_empty] at hKsum
      haveI : Nonempty n := by
        by_contra h
        haveI := not_nonempty_iff.mp h
        have := ρ.trace_eq_one
        rw [Matrix.trace_eq_zero_of_isEmpty] at this
        exact zero_ne_one this
      exfalso
      have h01 := congrFun (congrFun hKsum (Classical.arbitrary n)) (Classical.arbitrary n)
      simp only [Matrix.zero_apply, Matrix.one_apply_eq] at h01
      exact zero_ne_one h01
    · -- r ≥ 1: Stinespring dilation + pinching
      haveI : NeZero (r + 1) := ⟨Nat.succ_ne_zero r⟩
      set V := stinespringIsometry K with hV_def
      have hVV : Vᴴ * V = 1 := stinespringIsometry_conjTranspose_mul hKsum
      set ω := V * ρ.toMatrix * Vᴴ with hω_def
      set τ := V * σ.toMatrix * Vᴴ with hτ_def
      have hω_psd : ω.PosSemidef := ρ.posSemidef.mul_mul_conjTranspose_same V
      have hτ_psd : τ.PosSemidef := σ.posSemidef.mul_mul_conjTranspose_same V
      -- Isometry invariance: F_s(ρ, σ) = F_s(VρV†, VσV†)
      have h_iso := trace_rpow_mul_isometry_conj_eq V hVV ρ.toMatrix σ.toMatrix
        ρ.posSemidef σ.posSemidef s hs0 hs1_lt
      rw [← h_iso]
      -- Chain: F_s(ω, τ) ≤ Σᵢ F_s(KᵢρKᵢ†, KᵢσKᵢ†) ≤ F_s(Φρ, Φσ)
      calc (ω ^ s * τ ^ (1 - s)).trace.re
          ≤ ∑ i : Fin (r + 1), ((K i * ρ.toMatrix * (K i)ᴴ) ^ s *
                                (K i * σ.toMatrix * (K i)ᴴ) ^ (1 - s)).trace.re := by
            -- Diagonal blocks of ω = VρV†
            have hω_block : ∀ i j : Fin (r + 1), ∀ a b : m,
                ω (i, a) (j, b) = (K i * ρ.toMatrix * (K j)ᴴ) a b := by
              intro i j a b
              simp only [hω_def, Matrix.mul_apply, Matrix.conjTranspose_apply]
              simp only [hV_def, stinespringIsometry, Matrix.of_apply]
            have hτ_block : ∀ i j : Fin (r + 1), ∀ a b : m,
                τ (i, a) (j, b) = (K i * σ.toMatrix * (K j)ᴴ) a b := by
              intro i j a b
              simp only [hτ_def, Matrix.mul_apply, Matrix.conjTranspose_apply]
              simp only [hV_def, stinespringIsometry, Matrix.of_apply]
            have hω_diag_block : ∀ i : Fin (r + 1),
                ω.submatrix (Prod.mk i) (Prod.mk i) = K i * ρ.toMatrix * (K i)ᴴ := by
              intro i; ext a b
              simp only [Matrix.submatrix_apply, hω_block i i]
            have hτ_diag_block : ∀ i : Fin (r + 1),
                τ.submatrix (Prod.mk i) (Prod.mk i) = K i * σ.toMatrix * (K i)ᴴ := by
              intro i; ext a b
              simp only [Matrix.submatrix_apply, hτ_block i i]
            -- Pinching inequality: F_s(ω, τ) ≤ Σᵢ F_s(ωᵢᵢ, τᵢᵢ)
            have hpinching := pinching_inequality_Fs ω τ hω_psd hτ_psd s hs0 hs1_lt
            simp_rw [hω_diag_block, hτ_diag_block] at hpinching
            exact hpinching
        _ ≤ ((Φ.val ρ.toMatrix) ^ s * (Φ.val σ.toMatrix) ^ (1 - s)).trace.re := hsum_le

/-- **Monotonicity of Relative Entropy**: Quantum channels do not increase relative entropy.

For a quantum channel Φ and positive definite density matrices ρ, σ:
  S(Φ(ρ) || Φ(σ)) ≤ S(ρ || σ)

**Proof**: Uses derivative argument on g(s) = F_s(Φρ, Φσ) - F_s(ρ, σ) where
F_s(A, B) = Tr (Aˢ B¹⁻ˢ). Since g(s) ≥ 0 on (0,1] and g(1) = 0, we get g'(1) ≤ 0,
which is D(Φρ‖Φσ) ≤ D(ρ‖σ). -/
theorem relativeEntropy_channel_le
    (Φ : QuantumChannel n m)
    (ρ σ : DensityMatrix n) :
    D(Φ ρ ∥ Φ σ) ≤
    D(ρ ∥ σ) := by
  -- Case split: if D(ρ‖σ) = ⊤, trivially true
  by_cases hsupp : suppSubset ρ.toMatrix σ.toMatrix
  · -- Finite case: supp(ρ) ⊆ supp(σ)
    -- suppSubset is preserved by channels
    have hsupp_ch := suppSubset_channel' Φ σ.posSemidef hsupp
    set ρ' : DensityMatrix m := Φ ρ
    set σ' : DensityMatrix m := Φ σ
    -- Both relative entropies are finite
    have hDch : relativeEntropy ρ' σ' =
        ↑(ρ'.toMatrix * (log ρ' - log σ')).trace.re := by
      unfold relativeEntropy
      split_ifs with h
      · rfl
      · exact absurd hsupp_ch h
    have hD : relativeEntropy ρ σ =
        ↑(ρ.toMatrix * (log ρ - log σ)).trace.re := by
      unfold relativeEntropy
      simp only [if_pos hsupp]; rfl
    rw [hDch, hD, EReal.coe_le_coe_iff]
    -- Use derivative argument: define g(s) = F_s(Φρ, Φσ) - F_s(ρ, σ)
    let g : ℝ → ℝ := fun s =>
      (ρ'.toMatrix ^ s * σ'.toMatrix ^ (1 - s)).trace.re -
      (ρ.toMatrix ^ s * σ.toMatrix ^ (1 - s)).trace.re
    -- (a) g(s) ≥ 0 for s ∈ (0,1] by trace_rpow_mul_channel_le
    have g_nonneg : ∀ s ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ g s := by
      intro s hs
      exact sub_nonneg.mpr (trace_rpow_mul_channel_le Φ ρ σ s hs.1 hs.2)
    -- (b) g(1) = 0: at s=1, Tr (ρ¹ σ⁰) = Tr (ρ) = 1 and Tr ((Φρ)¹(Φσ)⁰) = Tr (Φρ) = 1
    have hg_one : g 1 = 0 := by
      simp only [g]
      rw [show (1 : ℝ) - 1 = 0 from by ring]
      rw [CFC.rpow_one _ (by rw [Matrix.le_iff, sub_zero]; exact ρ'.posSemidef),
          CFC.rpow_one _ (by rw [Matrix.le_iff, sub_zero]; exact ρ.posSemidef),
          CFC.rpow_zero _ (by rw [Matrix.le_iff, sub_zero]; exact σ'.posSemidef),
          CFC.rpow_zero _ (by rw [Matrix.le_iff, sub_zero]; exact σ.posSemidef)]
      simp only [Matrix.mul_one]
      rw [ρ'.trace_eq_one, ρ.trace_eq_one]
      simp [Complex.one_re, sub_self]
    -- (c) HasDerivAt of g at s=1
    have hderiv_ch : HasDerivAt (fun s => (ρ'.toMatrix ^ s * σ'.toMatrix ^ (1 - s)).trace.re)
        ((ρ'.toMatrix * (log ρ' - log σ')).trace.re) (1 : ℝ) :=
      hasDerivAt_trace_rpow_mul ρ' σ' hsupp_ch
    have hderiv_orig : HasDerivAt (fun s => (ρ.toMatrix ^ s * σ.toMatrix ^ (1 - s)).trace.re)
        ((ρ.toMatrix * (log ρ - log σ)).trace.re) (1 : ℝ) :=
      hasDerivAt_trace_rpow_mul ρ σ hsupp
    have hderiv_g : HasDerivAt g
        ((ρ'.toMatrix * (log ρ' - log σ')).trace.re -
         (ρ.toMatrix * (log ρ - log σ)).trace.re) (1 : ℝ) :=
      hderiv_ch.sub hderiv_orig
    -- (d) g'(1) ≤ 0 since g has minimum at s=1 from the left
    have hmin : ∀ y ∈ Set.Ioo (1 - (1:ℝ)/2) (1:ℝ), g (1:ℝ) ≤ g y := by
      intro y hy; rw [hg_one]; exact g_nonneg y ⟨by linarith [hy.1], le_of_lt hy.2⟩
    have hderiv_nonpos :
        (ρ'.toMatrix * (log ρ' - log σ')).trace.re -
        (ρ.toMatrix * (log ρ - log σ)).trace.re ≤ 0 :=
      deriv_nonpos_of_forall_lt_min g _ (1:ℝ) (1/2) (by norm_num) hderiv_g hmin
    -- (e) D(Φρ‖Φσ) - D(ρ‖σ) ≤ 0
    linarith
  · -- Infinite case: supp(ρ) ⊄ supp(σ) → D(ρ‖σ) = ⊤
    have hD_top : relativeEntropy ρ σ = ⊤ := by
      simp [relativeEntropy, hsupp]
    rw [hD_top]
    exact le_top

/-! ### Characterization of Equality -/

/-- **Sufficiency of recovery for equality in DPI.**

If a quantum channel R recovers both ρ and σ from Φ, i.e.,
  R(Φ(ρ)) = ρ and R(Φ(σ)) = σ,
then equality holds in the data-processing inequality:
  S(Φ(ρ) ‖ Φ(σ)) = S(ρ ‖ σ).

**Proof.** Applying DPI to Φ gives S(Φ(ρ)‖Φ(σ)) ≤ S(ρ‖σ).
For the reverse, applying DPI to R and using the recovery conditions gives
S(ρ‖σ) = S(R(Φ(ρ))‖R(Φ(σ))) ≤ S(Φ(ρ)‖Φ(σ)).
-/
theorem relativeEntropy_channel_eq_iff_recoverable
    (Φ : QuantumChannel n m)
    (ρ σ : DensityMatrix n)
    (R : QuantumChannel m n) (hRρ : R (Φ ρ) = ρ) (hRσ : R (Φ σ) = σ) :
    D(Φ ρ ∥ Φ σ) =
    D(ρ ∥ σ) := by
  apply le_antisymm
  · -- S(Φ(ρ) || Φ(σ)) ≤ S(ρ || σ) by DPI for Φ
    exact relativeEntropy_channel_le Φ ρ σ
  · -- S(ρ || σ) ≤ S(Φ(ρ) || Φ(σ)) by applying DPI to R and using recovery
    -- DPI for R: S(R(Φρ) || R(Φσ)) ≤ S(Φρ || Φσ)
    have hle := relativeEntropy_channel_le R (Φ ρ) (Φ σ)
    rw [hRρ, hRσ] at hle
    exact hle

/-! ### Joint Convexity of Relative Entropy -/

omit [DecidableEq n] in
/-- For a positive semidefinite matrix B, if Re[v† B v] = 0 then B v = 0. -/
private lemma mulVec_eq_zero_of_re_inner_zero
    {B : Matrix n n ℂ} (hB : B.PosSemidef)
    (v : n → ℂ) (hv : (star v ⬝ᵥ B.mulVec v).re = 0) :
    B.mulVec v = 0 := by
  rw [← hB.dotProduct_mulVec_zero_iff]
  apply Complex.ext
  · exact hv
  · exact hB.1.im_star_dotProduct_mulVec_self v

omit [DecidableEq n] in
/-- The support subset condition is preserved under convex combinations of positive semidefinite pairs.
If supp(Aᵢ) ⊆ supp(Bᵢ) for i=1,2 and p, 1−p ≥ 0, then
supp(p A₁ + (1−p) A₂) ⊆ supp(p B₁ + (1−p) B₂). -/
private lemma suppSubset_mix
    {A₁ A₂ B₁ B₂ : Matrix n n ℂ}
    (hB₁ : B₁.PosSemidef) (hB₂ : B₂.PosSemidef)
    (hsup₁ : suppSubset A₁ B₁) (hsup₂ : suppSubset A₂ B₂)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : 0 ≤ 1 - p) :
    suppSubset (p • A₁ + (1 - p) • A₂) (p • B₁ + (1 - p) • B₂) := by
  intro v hv
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec] at hv
  have h₁ : 0 ≤ (star v ⬝ᵥ B₁.mulVec v).re := hB₁.re_dotProduct_nonneg v
  have h₂ : 0 ≤ (star v ⬝ᵥ B₂.mulVec v).re := hB₂.re_dotProduct_nonneg v
  have hinner_sum : p * (star v ⬝ᵥ B₁.mulVec v).re + (1 - p) * (star v ⬝ᵥ B₂.mulVec v).re = 0 := by
    have h : p * (star v ⬝ᵥ B₁.mulVec v).re + (1 - p) * (star v ⬝ᵥ B₂.mulVec v).re =
             (star v ⬝ᵥ (p • B₁.mulVec v + (1 - p) • B₂.mulVec v)).re := by
      simp [dotProduct_add, dotProduct_smul]
    rw [h, hv]; simp
  have hpB₁ : p * (star v ⬝ᵥ B₁.mulVec v).re = 0 := by
    nlinarith [mul_nonneg hp h₁, mul_nonneg hp1 h₂]
  have h1pB₂ : (1 - p) * (star v ⬝ᵥ B₂.mulVec v).re = 0 := by
    nlinarith [mul_nonneg hp h₁, mul_nonneg hp1 h₂]
  have hpA₁ : p • A₁.mulVec v = 0 := by
    rcases mul_eq_zero.mp hpB₁ with hp0 | h₁0
    · simp [hp0]
    · simp [hsup₁ v (mulVec_eq_zero_of_re_inner_zero hB₁ v h₁0)]
  have h1pA₂ : (1 - p) • A₂.mulVec v = 0 := by
    rcases mul_eq_zero.mp h1pB₂ with hp10 | h₂0
    · simp [hp10]
    · simp [hsup₂ v (mulVec_eq_zero_of_re_inner_zero hB₂ v h₂0)]
  simp [Matrix.add_mulVec, Matrix.smul_mulVec, hpA₁, h1pA₂]

omit [DecidableEq n] [DecidableEq m] in
/-- Support subset is preserved by a single Kraus conjugation K ρ K†.
If supp(ρ) ⊆ supp(σ) then
supp(K ρ K†) ⊆ supp(K σ K†). -/
private lemma suppSubset_kraus_single
    (K : Matrix m n ℂ) {ρ σ : Matrix n n ℂ}
    (hσ : σ.PosSemidef) (h : suppSubset ρ σ) :
    suppSubset (K * ρ * Kᴴ) (K * σ * Kᴴ) := by
  intro v hv
  -- From (K σ Kᴴ) v = 0 and PSD, deduce σ (Kᴴ v) = 0
  have hKHv_ker : σ.mulVec (Kᴴ.mulVec v) = 0 := by
    apply mulVec_eq_zero_of_re_inner_zero hσ
    -- re⟨Kᴴv, σ(Kᴴv)⟩ = re⟨v, (KσKᴴ)v⟩ = 0
    -- Key: ⟨Kᴴv, w⟩ = ⟨v, Kw⟩ (adjoint identity)
    have h_eq : (star (Kᴴ.mulVec v) ⬝ᵥ σ.mulVec (Kᴴ.mulVec v)).re =
                (star v ⬝ᵥ (K * σ * Kᴴ).mulVec v).re := by
      congr 1
      conv_rhs => rw [show (K * σ * Kᴴ).mulVec v = K.mulVec (σ.mulVec (Kᴴ.mulVec v)) from by
                    simp only [← Matrix.mulVec_mulVec]]
      -- star (Kᴴ v) ⬝ᵥ w = star v ⬝ᵥ K w  (adjoint identity)
      rw [star_mulVec, Matrix.conjTranspose_conjTranspose, ← dotProduct_mulVec]
    rw [h_eq, hv]; simp
  -- suppSubset gives ρ (Kᴴ v) = 0
  have hρKHv_zero : ρ.mulVec (Kᴴ.mulVec v) = 0 := h _ hKHv_ker
  -- Therefore (K ρ Kᴴ) v = K (ρ (Kᴴ v)) = 0
  simp only [show (K * ρ * Kᴴ).mulVec v = K.mulVec (ρ.mulVec (Kᴴ.mulVec v)) from by
               simp only [← Matrix.mulVec_mulVec], hρKHv_zero, Matrix.mulVec_zero]

omit [DecidableEq n] [DecidableEq m] in
/-- Support subset is preserved under finite sums of Kraus-conjugated pairs.
If supp(A_k) ⊆ supp(B_k) for all k and each B_k is
positive semidefinite, then supp(∑_k A_k) ⊆ supp(∑_k B_k). -/
private lemma suppSubset_sum {r : ℕ} {A B : Fin r → Matrix m m ℂ}
    (hB : ∀ k, (B k).PosSemidef)
    (h : ∀ k, suppSubset (A k) (B k)) :
    suppSubset (∑ k, A k) (∑ k, B k) := by
  intro v hv
  simp only [Matrix.sum_mulVec] at hv ⊢
  -- Each ⟨v, B_k v⟩.re ≥ 0 (PSD) and their sum = 0
  have hB_nonneg : ∀ k, 0 ≤ (star v ⬝ᵥ (B k).mulVec v).re :=
    fun k => (hB k).re_dotProduct_nonneg v
  have hsum_zero : ∑ k : Fin r, (star v ⬝ᵥ (B k).mulVec v).re = 0 := by
    have heq : (star v ⬝ᵥ ∑ k : Fin r, (B k).mulVec v).re = 0 := by rw [hv]; simp
    rw [dotProduct_sum] at heq
    simpa [Complex.re_sum] using heq
  -- Each term is 0 (nonneg terms sum to 0)
  have hB_each : ∀ k, (star v ⬝ᵥ (B k).mulVec v).re = 0 := fun k =>
    le_antisymm (by
      calc (star v ⬝ᵥ (B k).mulVec v).re
          ≤ ∑ i : Fin r, (star v ⬝ᵥ (B i).mulVec v).re :=
              Finset.single_le_sum (fun i _ => hB_nonneg i) (Finset.mem_univ k)
        _ = 0 := hsum_zero) (hB_nonneg k)
  -- Each (B k) v = 0 via PosSemidef.dotProduct_mulVec_zero_iff
  have hBv_zero : ∀ k, (B k).mulVec v = 0 := fun k => by
    rw [← (hB k).dotProduct_mulVec_zero_iff]
    apply Complex.ext
    · exact hB_each k
    · exact (hB k).1.im_star_dotProduct_mulVec_self v
  -- Each (A k) v = 0
  have hAv_zero : ∀ k, (A k).mulVec v = 0 := fun k => h k v (hBv_zero k)
  simp only [hAv_zero, Finset.sum_const_zero]

omit [DecidableEq n] [DecidableEq m] in
/-- Support subset is preserved by quantum channels.
If supp(ρ) ⊆ supp(σ) then
supp(Φ(ρ)) ⊆ supp(Φ(σ)). -/
private lemma suppSubset_channel
    (Φ : QuantumChannel n m)
    {ρ σ : Matrix n n ℂ} (hσ : σ.PosSemidef) (h : suppSubset ρ σ) :
    suppSubset (Φ.val ρ) (Φ.val σ) := by
  obtain ⟨r, K, hK⟩ := Φ.property.completelyPositive
  rw [hK, hK]
  exact suppSubset_sum
    (fun k => hσ.mul_mul_conjTranspose_same (K k))
    (fun k => suppSubset_kraus_single (K k) hσ h)

/-- Joint concavity of Tr (ρˢ σ¹⁻ˢ) for positive semidefinite matrices.
  p ⋅ Tr (ρ₁ˢ σ₁¹⁻ˢ) + (1−p) ⋅ Tr (ρ₂ˢ σ₂¹⁻ˢ)
  ≤ Tr ((pρ₁ + (1−p)ρ₂)ˢ (pσ₁ + (1−p)σ₂)¹⁻ˢ) -/
private lemma trace_rpow_mul_jointly_concave
    (ρ₁ ρ₂ σ₁ σ₂ : DensityMatrix n) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (s : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    p * (Tr (ρ₁ ^ s * σ₁ ^ (1 - s))).re +
    (1 - p) * (Tr (ρ₂ ^ s * σ₂ ^ (1 - s))).re ≤
    (Tr ((p • ρ₁.toMatrix + (1 - p) • ρ₂.toMatrix) ^ s * (p • σ₁.toMatrix + (1 - p) • σ₂.toMatrix) ^ (1 - s))).re := by
  have hpsd₁ := ρ₁.posSemidef
  have hpsd₂ := ρ₂.posSemidef
  have hpsdσ₁ := σ₁.posSemidef
  have hpsdσ₂ := σ₂.posSemidef
  -- This is lieb_joint_concavity_semidef with K = 1
  have key := lieb_joint_concavity_semidef ρ₁.toMatrix ρ₂.toMatrix σ₁.toMatrix σ₂.toMatrix
    hpsd₁ hpsd₂ hpsdσ₁ hpsdσ₂
    (1 : Matrix n n ℂ) s hs0 hs1 p (1 - p) hp (by linarith) (by ring)
  simp only [liebJointFunction, conjTranspose_one, Matrix.mul_one] at key
  exact key


theorem relativeEntropy_jointly_convex
    (ρ₁ ρ₂ σ₁ σ₂ : DensityMatrix n)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    D(DensityMatrix.mix ρ₁ ρ₂ p hp hp1 ∥ DensityMatrix.mix σ₁ σ₂ p hp hp1) ≤
    p * D(ρ₁ ∥ σ₁) + (1 - p) * D(ρ₂ ∥ σ₂) := by
  set ρ_mix := DensityMatrix.mix ρ₁ ρ₂ p hp hp1
  set σ_mix := DensityMatrix.mix σ₁ σ₂ p hp hp1
  -- Handle boundary cases p = 0 and p = 1
  rcases hp.eq_or_lt' with rfl | hp0
  · -- p = 0: mixture = ρ₂, σ₂; RHS = 0 + D₂ = D₂
    have hρ_eq : ρ_mix = ρ₂ := DensityMatrix.ext (by simp [ρ_mix, DensityMatrix.mix])
    have hσ_eq : σ_mix = σ₂ := DensityMatrix.ext (by simp [σ_mix, DensityMatrix.mix])
    rw [hρ_eq, hσ_eq]; simp [relativeEntropy]
  rcases hp1.lt_or_eq with hp1' | rfl
  · -- 0 < p < 1: handle the three sub-cases
    -- Case split on whether suppSubsets hold
    by_cases h₂ : suppSubset ρ₂.toMatrix σ₂.toMatrix
    · by_cases h₁ : suppSubset ρ₁.toMatrix σ₁.toMatrix
      · -- Both finite: use derivative argument
        -- Step 1: suppSubset for the mixture
        have hsup_mix : suppSubset (p • ρ₁.toMatrix + (1 - p) • ρ₂.toMatrix)
                                   (p • σ₁.toMatrix + (1 - p) • σ₂.toMatrix) :=
          suppSubset_mix σ₁.posSemidef σ₂.posSemidef
                         h₁ h₂ p hp (by linarith)
        -- Step 2: Abbreviate the real-valued relative entropies
        set r₁ := (ρ₁.toMatrix * (log ρ₁ - log σ₁)).trace.re
        set r₂ := (ρ₂.toMatrix * (log ρ₂ - log σ₂)).trace.re
        -- Simplify relativeEntropy using the definitions
        have hD₁_eq : relativeEntropy ρ₁ σ₁ = ↑r₁ := by
          simp only [relativeEntropy, h₁, ↓reduceIte]; rfl
        have hD₂_eq : relativeEntropy ρ₂ σ₂ = ↑r₂ := by
          simp only [relativeEntropy, h₂, ↓reduceIte]; rfl
        have hsup_mix' : suppSubset ρ_mix.toMatrix σ_mix.toMatrix := hsup_mix
        have hD_mix_eq : relativeEntropy ρ_mix σ_mix =
                         ↑(ρ_mix.toMatrix *
                           (log ρ_mix - log σ_mix)).trace.re := by
          simp only [relativeEntropy, hsup_mix', ↓reduceIte]; rfl
        rw [hD_mix_eq, hD₁_eq, hD₂_eq]
        -- Step 3: Convert to real comparison
        rw [show (↑p : EReal) * ↑r₁ + (1 - ↑p) * ↑r₂ = ↑(p * r₁ + (1 - p) * r₂) from by
          push_cast; ring_nf]
        rw [EReal.coe_le_coe_iff]
        -- Step 4: Derivative argument
        -- Define h(s) = Re[Tr (ρ_mix^s σ_mix^{1-s})] - p Re[Tr (ρ₁^s σ₁^{1-s})] - (1-p) Re[Tr (ρ₂^s σ₂^{1-s})]
        let g : ℝ → ℝ := fun s =>
          (ρ_mix.toMatrix ^ s * σ_mix.toMatrix ^ (1 - s)).trace.re -
          (p * (ρ₁.toMatrix ^ s * σ₁.toMatrix ^ (1 - s)).trace.re +
           (1 - p) * (ρ₂.toMatrix ^ s * σ₂.toMatrix ^ (1 - s)).trace.re)
        -- (a) g(s) ≥ 0 for s ∈ (0,1] by joint concavity (Lieb)
        have g_nonneg : ∀ s ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ g s := by
          intro s hs
          simp only [g, ρ_mix, σ_mix, DensityMatrix.mix_toMatrix]
          have h := trace_rpow_mul_jointly_concave ρ₁ ρ₂ σ₁ σ₂ p hp hp1 s (le_of_lt hs.1) hs.2
          change p * (ρ₁.toMatrix ^ s * σ₁.toMatrix ^ (1 - s)).trace.re +
            (1 - p) * (ρ₂.toMatrix ^ s * σ₂.toMatrix ^ (1 - s)).trace.re ≤ _ at h
          linarith
        -- (b) g(1) = 0
        have hg_one : g 1 = 0 := by
          simp only [g]
          rw [show (1 : ℝ) - 1 = 0 from by ring]
          rw [CFC.rpow_one _ (by rw [Matrix.le_iff, sub_zero]; exact ρ_mix.posSemidef),
              CFC.rpow_one _ (by rw [Matrix.le_iff, sub_zero]; exact ρ₁.posSemidef),
              CFC.rpow_one _ (by rw [Matrix.le_iff, sub_zero]; exact ρ₂.posSemidef),
              CFC.rpow_zero _ (by rw [Matrix.le_iff, sub_zero]; exact σ_mix.posSemidef),
              CFC.rpow_zero _ (by rw [Matrix.le_iff, sub_zero]; exact σ₁.posSemidef),
              CFC.rpow_zero _ (by rw [Matrix.le_iff, sub_zero]; exact σ₂.posSemidef)]
          simp only [Matrix.mul_one]
          rw [ρ_mix.trace_eq_one, ρ₁.trace_eq_one, ρ₂.trace_eq_one]
          simp only [Complex.one_re]; linarith
        -- (c) HasDerivAt of g at s=1
        have hderiv_mix : HasDerivAt (fun s : ℝ => (ρ_mix.toMatrix ^ s * σ_mix.toMatrix ^ (1 - s)).trace.re)
            ((ρ_mix.toMatrix * (log ρ_mix - log σ_mix)).trace.re) 1 :=
          hasDerivAt_trace_rpow_mul ρ_mix σ_mix hsup_mix
        have hderiv₁ : HasDerivAt (fun s : ℝ => (ρ₁.toMatrix ^ s * σ₁.toMatrix ^ (1 - s)).trace.re)
            ((ρ₁.toMatrix * (log ρ₁ - log σ₁)).trace.re) 1 :=
          hasDerivAt_trace_rpow_mul ρ₁ σ₁ h₁
        have hderiv₂ : HasDerivAt (fun s : ℝ => (ρ₂.toMatrix ^ s * σ₂.toMatrix ^ (1 - s)).trace.re)
            ((ρ₂.toMatrix * (log ρ₂ - log σ₂)).trace.re) 1 :=
          hasDerivAt_trace_rpow_mul ρ₂ σ₂ h₂
        have hderiv_g : HasDerivAt g
            ((ρ_mix.toMatrix * (log ρ_mix - log σ_mix)).trace.re -
             (p * (ρ₁.toMatrix * (log ρ₁ - log σ₁)).trace.re +
              (1 - p) * (ρ₂.toMatrix * (log ρ₂ - log σ₂)).trace.re)) 1 := by
          exact hderiv_mix.sub (hderiv₁.const_mul p |>.add (hderiv₂.const_mul (1 - p)))
        -- (d) g'(1) ≤ 0 since g has a minimum at s=1 from the left
        have hmin : ∀ y ∈ Set.Ioo (1 - (1:ℝ)/2) 1, g 1 ≤ g y := by
          intro y hy; rw [hg_one]; exact g_nonneg y ⟨by linarith [hy.1], le_of_lt hy.2⟩
        have hderiv_nonpos :
            (ρ_mix.toMatrix * (log ρ_mix - log σ_mix)).trace.re -
            (p * (ρ₁.toMatrix * (log ρ₁ - log σ₁)).trace.re +
             (1 - p) * (ρ₂.toMatrix * (log ρ₂ - log σ₂)).trace.re) ≤ 0 :=
          deriv_nonpos_of_forall_lt_min g _ 1 (1/2) (by norm_num) hderiv_g hmin
        linarith
      · -- D₁ = ⊤: RHS = p * ⊤ + ... = ⊤, LHS ≤ ⊤
        have hD₁ : relativeEntropy ρ₁ σ₁ = ⊤ := by
          simp [relativeEntropy, h₁]
        rw [hD₁, EReal.mul_top_of_pos (by exact_mod_cast hp0),
            EReal.top_add_of_ne_bot (ne_bot_of_gt (lt_of_lt_of_le EReal.bot_lt_zero
              (EReal.mul_nonneg (by norm_cast; linarith) (relativeEntropy_nonneg ρ₂ σ₂))))]
        exact le_top
    · -- D₂ = ⊤: RHS = ... + (1-p) * ⊤ = ⊤
      have hD₂ : relativeEntropy ρ₂ σ₂ = ⊤ := by
        simp [relativeEntropy, h₂]
      rw [hD₂, EReal.mul_top_of_pos (by exact_mod_cast (by linarith : 0 < 1 - p)),
          EReal.add_top_of_ne_bot (ne_bot_of_gt (lt_of_lt_of_le EReal.bot_lt_zero
            (EReal.mul_nonneg (by norm_cast) (relativeEntropy_nonneg ρ₁ σ₁))))]
      exact le_top
  · -- p = 1: mixture = ρ₁, σ₁; RHS = D₁ + 0 = D₁
    have hρ_eq : ρ_mix = ρ₁ := DensityMatrix.ext (by simp [ρ_mix, DensityMatrix.mix])
    have hσ_eq : σ_mix = σ₁ := DensityMatrix.ext (by simp [σ_mix, DensityMatrix.mix])
    rw [hρ_eq, hσ_eq]
    have h1sub1 : (1 : EReal) - 1 = 0 :=
      EReal.sub_self (EReal.coe_ne_top 1) (EReal.coe_ne_bot 1)
    simp only [EReal.coe_one, one_mul, h1sub1, EReal.zero_mul, add_zero]
    exact le_refl _

end Matrix
