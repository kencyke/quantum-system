/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.DensityMatrix.Basic

/-!
# Supports and relative eigenbases of Hermitian matrices

Spectral facts about a pair of Hermitian (or positive semidefinite) matrices `ρ, σ` used to
evaluate Umegaki's relative entropy `Tr ρ (log ρ - log σ)` (`Matrix.umegakiEntropy`, `QuantumSystem.Analysis.Entropy.Umegaki.Basic`).
Nothing here refers to an entropy: the file records the support inclusion `supp ρ ⊆ supp σ` and
the expansion of `Tr ρ log ρ` and `Tr ρ log σ` in the eigenbases of `ρ` and `σ`.

## Main definitions

* `Matrix.suppSubset ρ σ` — support inclusion `supp ρ ⊆ supp σ`, i.e. `ker σ ⊆ ker ρ`.
* `Matrix.eigW hρ hσ` — the change-of-basis unitary `W = Vᴴ U` between the eigenvector bases `U` of
  `ρ` and `V` of `σ`; its entries are the overlaps `W_{ji} = ⟪e_j, f_i⟫` (`Matrix.eigW_apply`).

## Main results

* `Matrix.suppSubset_iff_mul_cfc_eq_zero` — algebraic form of support inclusion, and its
  invariance under `*-`algebra equivalences, `Matrix.suppSubset_map_starAlgEquiv_iff`.
* `Matrix.suppSubset_iff_normSq_eigW_mul_eigenvalues_eq_zero` — support inclusion in the
  eigenbases: `|W_{ji}|² rᵢ = 0` whenever `s_j = 0`.
* `Matrix.re_trace_mul_log_self_eq`, `Matrix.re_trace_mul_log_eq` — the eigenvalue expansions
  `Tr ρ log ρ = Σᵢ rᵢ log rᵢ` and `Tr ρ log σ = Σᵢⱼ |W_{ji}|² rᵢ log s_j`.
-/

@[expose] public section

namespace Matrix

open scoped MatrixOrder ComplexOrder QuantumInfo

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-! ### Support inclusion -/

/-- Support inclusion: the kernel of σ is contained in the kernel of ρ,
i.e., supp(ρ) ⊆ supp(σ). This is the condition for D(ρ‖σ) to be finite. -/
def suppSubset (ρ σ : Matrix n n ℂ) : Prop :=
  ∀ v : n → ℂ, σ.mulVec v = 0 → ρ.mulVec v = 0

omit [DecidableEq n] in
/-- For a positive semidefinite matrix `B`, if `Re[v† B v] = 0` then `B v = 0`. -/
lemma mulVec_eq_zero_of_re_inner_zero
    {B : Matrix n n ℂ} (hB : B.PosSemidef)
    (v : n → ℂ) (hv : (star v ⬝ᵥ B.mulVec v).re = 0) :
    B.mulVec v = 0 := by
  rw [← hB.dotProduct_mulVec_zero_iff]
  apply Complex.ext
  · exact hv
  · exact hB.1.im_star_dotProduct_mulVec_self v

/-- **Algebraic form of support inclusion.** For Hermitian `σ`, `supp ρ ⊆ supp σ` iff `ρ`
annihilates the kernel projection `cfc (fun x => if x = 0 then 1 else 0) σ` of `σ`. No
hypothesis on `ρ` is needed. This is the form that transports along `*`-algebra
equivalences (`suppSubset_map_starAlgEquiv_iff`). -/
theorem suppSubset_iff_mul_cfc_eq_zero {ρ σ : Matrix n n ℂ} (hσ : σ.IsHermitian) :
    suppSubset ρ σ ↔ ρ * cfc (fun x : ℝ => if x = 0 then (1 : ℝ) else 0) σ = 0 := by
  have hfin : (spectrum ℝ σ).Finite := by
    rw [hσ.spectrum_real_eq_range_eigenvalues]; exact Set.finite_range _
  have hsa : IsSelfAdjoint σ := hσ
  set g : ℝ → ℝ := fun x => if x = 0 then 1 else 0 with hg
  -- `σ · P = 0` for the kernel projection `P = cfc g σ`.
  have hσP : σ * cfc g σ = 0 := by
    have h := cfc_mul (fun x : ℝ => x) g σ continuousOn_id (hfin.continuousOn g)
    rw [cfc_id' (R := ℝ) (a := σ) hsa] at h
    rw [← h]
    have : (fun x : ℝ => x * g x) = (0 : ℝ → ℝ) := by
      funext x; simp only [hg, Pi.zero_apply]; split_ifs with h0 <;> simp [h0]
    rw [this, cfc_zero]
  constructor
  · intro h
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec]
    apply h
    rw [Matrix.mulVec_mulVec, hσP, Matrix.zero_mulVec]
  · intro h v hv
    -- `P v = v` for `v ∈ ker σ`, since `1 - P = cfc (x ↦ x⁻¹ · [x ≠ 0]) σ · σ`.
    set h' : ℝ → ℝ := fun x => if x = 0 then 0 else x⁻¹ with hh'
    have hQ : cfc (fun x => h' x * x) σ = cfc h' σ * σ := by
      rw [cfc_mul h' (fun x : ℝ => x) σ (hfin.continuousOn h') continuousOn_id,
        cfc_id' (R := ℝ) (a := σ) hsa]
    have hPQ : cfc g σ + cfc (fun x => h' x * x) σ = 1 := by
      rw [← cfc_add g (fun x => h' x * x) (a := σ) (hfin.continuousOn _) (hfin.continuousOn _)]
      have : (fun x : ℝ => g x + h' x * x) = fun _ => 1 := by
        funext x; simp only [hg, hh']
        split_ifs with h0
        · simp
        · rw [inv_mul_cancel₀ h0]; ring
      rw [this, cfc_const_one ℝ σ]
    have hPv : (cfc g σ).mulVec v = v := by
      have h1 := congr_arg (fun M : Matrix n n ℂ => M.mulVec v) hPQ
      simp only [Matrix.add_mulVec, Matrix.one_mulVec, hQ, ← Matrix.mulVec_mulVec, hv,
        Matrix.mulVec_zero, add_zero] at h1
      exact h1
    rw [← hPv, Matrix.mulVec_mulVec, h, Matrix.zero_mulVec]

/-- **Support inclusion along a unitary diagonalisation.** If `σ = W · diag d · Wᴴ` with
`W` unitary and `ρ` is positive semidefinite, then `supp ρ ⊆ supp σ` iff the conjugated
matrix `Wᴴ ρ W` has vanishing diagonal entry at every index `k` with `d k = 0`. -/
theorem suppSubset_unitary_conj_diagonal_iff {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef)
    (W : unitary (Matrix n n ℂ)) (d : n → ℝ) :
    suppSubset ρ
        ((W : Matrix n n ℂ) * diagonal (fun i => ((d i : ℝ) : ℂ)) * (W : Matrix n n ℂ)ᴴ) ↔
      ∀ k, d k = 0 → ((W : Matrix n n ℂ)ᴴ * ρ * (W : Matrix n n ℂ)) k k = 0 := by
  set Wm : Matrix n n ℂ := (W : Matrix n n ℂ) with hWm
  set D : Matrix n n ℂ := diagonal (fun i => ((d i : ℝ) : ℂ)) with hD
  have hWHW : Wmᴴ * Wm = 1 := by
    have := Unitary.coe_star_mul_self W; simpa [star_eq_conjTranspose, hWm] using this
  have hWWH : Wm * Wmᴴ = 1 := by
    have := Unitary.coe_mul_star_self W; simpa [star_eq_conjTranspose, hWm] using this
  -- `c k` is column `k` of `W`.
  set c : n → n → ℂ := fun k j => Wm j k with hc
  have hρc : ∀ i k, (ρ * Wm) i k = (ρ.mulVec (c k)) i := fun i k => rfl
  have hdiag : ∀ k, (Wmᴴ * ρ * Wm) k k = star (c k) ⬝ᵥ ρ.mulVec (c k) := by
    intro k
    simp only [Matrix.mul_apply, dotProduct, mulVec, conjTranspose_apply, hc, Finset.sum_mul,
      Finset.mul_sum, mul_assoc, Pi.star_apply]
    rw [Finset.sum_comm]
  have hσW : (Wm * D * Wmᴴ) * Wm = Wm * D := by
    rw [Matrix.mul_assoc, hWHW, Matrix.mul_one]
  constructor
  · intro h k hk
    have hσc : (Wm * D * Wmᴴ).mulVec (c k) = 0 := by
      ext i
      change ((Wm * D * Wmᴴ) * Wm) i k = 0
      rw [hσW, hD, mul_diagonal, hk]
      simp
    rw [hdiag, h (c k) hσc, dotProduct_zero]
  · intro h v hv
    set w := Wmᴴ.mulVec v with hw
    have hDw : D.mulVec w = 0 := by
      have h1 : Wmᴴ.mulVec ((Wm * D * Wmᴴ).mulVec v) = 0 := by rw [hv, mulVec_zero]
      rwa [mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hWHW, Matrix.one_mul,
        ← mulVec_mulVec] at h1
    have hdw : ∀ i, d i ≠ 0 → w i = 0 := by
      intro i hi
      have := congr_fun hDw i
      rw [hD, mulVec_diagonal] at this
      simpa [hi] using this
    have hv_eq : v = Wm.mulVec w := by
      rw [hw, mulVec_mulVec, hWWH, one_mulVec]
    rw [hv_eq, mulVec_mulVec]
    ext i
    change ∑ k, (ρ * Wm) i k * w k = 0
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : d k = 0
    · have hρck : ρ.mulVec (c k) = 0 := by
        apply mulVec_eq_zero_of_re_inner_zero hρ
        rw [← hdiag, h k hk, Complex.zero_re]
      rw [hρc, hρck, Pi.zero_apply, zero_mul]
    · rw [hdw k hk, mul_zero]

/-! ### Relative eigenbasis -/

section RelativeEigenbasis

variable {ρ σ : Matrix n n ℂ}

/-- Change-of-basis unitary between eigenvector bases of ρ and σ.
W = Vᴴ * U where V = eigenvectors of σ, U = eigenvectors of ρ. -/
noncomputable def eigW (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) : Matrix n n ℂ :=
  (hσ.eigenvectorUnitary : Matrix n n ℂ)ᴴ *
  (hρ.eigenvectorUnitary : Matrix n n ℂ)

/-- W * Wᴴ = 1 for the change-of-basis unitary. -/
lemma eigW_mul_conjTranspose_eigW (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    eigW hρ hσ * (eigW hρ hσ)ᴴ = 1 := by
  unfold eigW
  set V := (hσ.eigenvectorUnitary : Matrix n n ℂ)
  set U := (hρ.eigenvectorUnitary : Matrix n n ℂ)
  rw [conjTranspose_mul, conjTranspose_conjTranspose]
  calc (Vᴴ * U) * (Uᴴ * V)
      = Vᴴ * (U * Uᴴ) * V := by simp only [Matrix.mul_assoc]
    _ = Vᴴ * V := by rw [UUH_eq_one _ hρ, Matrix.mul_one]
    _ = 1 := UHU_eq_one _ hσ

/-- Wᴴ * W = 1 for the change-of-basis unitary. -/
lemma conjTranspose_eigW_mul_eigW (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    (eigW hρ hσ)ᴴ * eigW hρ hσ = 1 := by
  unfold eigW
  set V := (hσ.eigenvectorUnitary : Matrix n n ℂ)
  set U := (hρ.eigenvectorUnitary : Matrix n n ℂ)
  rw [conjTranspose_mul, conjTranspose_conjTranspose]
  calc (Uᴴ * V) * (Vᴴ * U)
      = Uᴴ * (V * Vᴴ) * U := by simp only [Matrix.mul_assoc]
    _ = Uᴴ * U := by rw [UUH_eq_one _ hσ, Matrix.mul_one]
    _ = 1 := UHU_eq_one _ hρ

/-- Column sums of |W_{ji}|² equal 1. Follows from W * Wᴴ = 1 (W is unitary). -/
lemma sum_normSq_eigW_col (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (i : n) :
    ∑ j : n, Complex.normSq (eigW hρ hσ j i) = 1 := by
  have h1 := congr_fun (congr_fun (conjTranspose_eigW_mul_eigW hρ hσ) i) i
  simp only [mul_apply, conjTranspose_apply, one_apply_eq] at h1
  have h2 : (∑ j : n, (Complex.normSq (eigW hρ hσ j i) : ℂ)) = 1 := by
    simp_rw [show ∀ j, (Complex.normSq (eigW hρ hσ j i) : ℂ) =
      star (eigW hρ hσ j i) * eigW hρ hσ j i from fun j => by
        rw [Complex.normSq_eq_conj_mul_self]; simp [RCLike.star_def]]
    exact h1
  exact_mod_cast h2

/-- Row sums of |W_{ji}|² equal 1. Follows from Wᴴ * W = 1 (W is unitary). -/
lemma sum_normSq_eigW_row (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (j : n) :
    ∑ i : n, Complex.normSq (eigW hρ hσ j i) = 1 := by
  have h1 := congr_fun (congr_fun (eigW_mul_conjTranspose_eigW hρ hσ) j) j
  simp only [mul_apply, conjTranspose_apply, one_apply_eq] at h1
  have h2 : (∑ i : n, (Complex.normSq (eigW hρ hσ j i) : ℂ)) = 1 := by
    simp_rw [show ∀ i, (Complex.normSq (eigW hρ hσ j i) : ℂ) =
      eigW hρ hσ j i * star (eigW hρ hσ j i) from fun i => by
        rw [Complex.normSq_eq_conj_mul_self]; simp [RCLike.star_def, mul_comm]]
    exact h1
  exact_mod_cast h2

/-- Support subset condition implies: |W_{ji}|² · ev_ρᵢ = 0 when ev_σⱼ = 0.
Here ev_ρᵢ are eigenvalues of ρ, ev_σⱼ are eigenvalues of σ.
Proof: vⱼ = col j of V ∈ ker(σ), suppSubset gives vⱼ ∈ ker(ρ),
injectivity of U gives diag(ev_ρ) · (Uᴴvⱼ) = 0, and (Uᴴvⱼ)ᵢ = conj(Wji). -/
lemma normSq_eigW_mul_eigenvalues_eq_zero_of_suppSubset (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (h : suppSubset ρ σ) (j : n)
    (hev_σj : hσ.eigenvalues j = 0) (i : n) :
    Complex.normSq (eigW hρ hσ j i) * hρ.eigenvalues i = 0 := by
  set V := (hσ.eigenvectorUnitary : Matrix n n ℂ) with hV_def
  set U := (hρ.eigenvectorUnitary : Matrix n n ℂ) with hU_def
  set W := eigW hρ hσ with hW_def
  set ev_ρ := hρ.eigenvalues with hev_ρ_def
  set colV_j : n → ℂ := fun k => V k j with hcolV_def
  -- Column j of V is in ker(σ) since eigenvalue j is 0
  have hσcol : σ.mulVec colV_j = 0 := by
    have h1 := mulVec_eigenvector_col σ hσ j
    ext k; rw [congr_fun h1 k, hev_σj, Complex.ofReal_zero, zero_mul, Pi.zero_apply]
  -- By suppSubset, col j of V is also in ker(ρ)
  have hρcol : ρ.mulVec colV_j = 0 := h colV_j hσcol
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
  have hspec := spectral_expand ρ hρ
  -- Since ρ · colV_j = 0, we have U · diag(ev_ρ) · Uh_colV = 0
  have h_diag_eq : (U * diagonal (fun k => (ev_ρ k : ℂ))).mulVec Uh_colV = 0 := by
    calc (U * diagonal (fun k => (ev_ρ k : ℂ))).mulVec Uh_colV
        = (U * diagonal (fun k => (ev_ρ k : ℂ))).mulVec (Uᴴ.mulVec colV_j) := rfl
      _ = (U * diagonal (fun k => (ev_ρ k : ℂ)) * Uᴴ).mulVec colV_j := by
          rw [Matrix.mulVec_mulVec]
      _ = ρ.mulVec colV_j := by rw [← hspec]
      _ = 0 := hρcol
  -- Extract the i-th component: ev_ρ i * (Uh_colV i) = 0
  have h_ev_Uh_zero : (ev_ρ i : ℂ) * Uh_colV i = 0 := by
    -- From h_diag_eq, we know (U * diag) * Uh_colV = 0
    -- Multiplying by Uᴴ on left: Uᴴ * (U * diag) * Uh_colV = 0
    -- Since Uᴴ * U = 1, this gives diag * Uh_colV = 0
    have h_UhU := UHU_eq_one _ hρ
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

/-- The entries of `eigW` are overlaps of eigenvectors: `W_{ji} = ⟪e_j, f_i⟫`, where `e_j` is the
`j`-th eigenvector of `σ` and `f_i` the `i`-th eigenvector of `ρ`. -/
lemma eigW_apply (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (j i : n) :
    eigW hρ hσ j i =
      inner ℂ (hσ.eigenvectorBasis j) (hρ.eigenvectorBasis i) := by
  simp [eigW, Matrix.mul_apply, PiLp.inner_apply, mul_comm]

/-- **Support inclusion in the eigenbases.** `supp ρ ⊆ supp σ` iff `|W_{ji}|² rᵢ = 0` whenever the
eigenvalue `s_j` of `σ` vanishes, `rᵢ` being the eigenvalues of `ρ`. -/
theorem suppSubset_iff_normSq_eigW_mul_eigenvalues_eq_zero (hρ : ρ.PosSemidef) (hσ : σ.IsHermitian) :
    suppSubset ρ σ ↔
      ∀ j, hσ.eigenvalues j = 0 → ∀ i,
        Complex.normSq (eigW hρ.1 hσ j i) * hρ.1.eigenvalues i = 0 := by
  refine ⟨normSq_eigW_mul_eigenvalues_eq_zero_of_suppSubset hρ.1 hσ, fun h => ?_⟩
  set V := hσ.eigenvectorUnitary
  have hW : (V : Matrix n n ℂ)ᴴ * ρ * V =
      eigW hρ.1 hσ * diagonal (fun i => (hρ.1.eigenvalues i : ℂ)) * (eigW hρ.1 hσ)ᴴ := by
    conv_lhs => rw [spectral_expand ρ hρ.1]
    simp only [eigW, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, V]
  have key := (suppSubset_unitary_conj_diagonal_iff hρ V hσ.eigenvalues).mpr
    fun j hj => by
      rw [hW, mul_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      have hji := h j hj i
      rw [mul_diagonal, conjTranspose_apply]
      simp only [RCLike.star_def]
      rw [mul_comm (eigW hρ.1 hσ j i), mul_assoc, Complex.mul_conj, ← Complex.ofReal_mul, mul_comm, hji,
        Complex.ofReal_zero]
  rwa [← spectral_expand σ hσ] at key

/-- Trace of ρ log ρ equals the eigenvalue sum ∑ᵢ ev_{ρ,i} log ev_{ρ,i}. -/
lemma re_trace_mul_log_self_eq (hρ : ρ.IsHermitian) :
    (Tr (ρ * cfc Real.log ρ)).re =
    ∑ i, hρ.eigenvalues i * Real.log (hρ.eigenvalues i) := by
  set U := (hρ.eigenvectorUnitary : Matrix n n ℂ)
  set ev_ρ := hρ.eigenvalues
  have hUHU : Uᴴ * U = 1 := UHU_eq_one _ hρ
  -- ρ = U * diag(ev) * Uᴴ
  have hρ_spec := spectral_expand ρ hρ
  -- log(ρ) = U * diag(log ev) * Uᴴ
  have hlogρ_spec : cfc Real.log ρ = U * diagonal (fun i => (Real.log (ev_ρ i) : ℂ)) * Uᴴ := by
    exact cfc_log_spectral_eq hρ
  -- ρ * log(ρ) = U * diag(ev) * Uᴴ * U * diag(log ev) * Uᴴ = U * diag(ev * log ev) * Uᴴ
  -- First rewrite log, then ρ
  have h1 : (ρ * cfc Real.log ρ).trace.re =
      (ρ * (U * diagonal (fun i => (Real.log (ev_ρ i) : ℂ)) * Uᴴ)).trace.re := by
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
lemma re_trace_mul_log_eq (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    (Tr (ρ * cfc Real.log σ)).re =
    ∑ i, ∑ j, Complex.normSq (eigW hρ hσ j i) *
      hρ.eigenvalues i *
      Real.log (hσ.eigenvalues j) := by
  set V := (hσ.eigenvectorUnitary : Matrix n n ℂ)
  set U := (hρ.eigenvectorUnitary : Matrix n n ℂ)
  set W := eigW hρ hσ
  set ev_ρ := hρ.eigenvalues
  set ev_σ := hσ.eigenvalues
  have hρ : ρ = U * diagonal (fun i => (ev_ρ i : ℂ)) * Uᴴ :=
    spectral_expand ρ hρ
  have hlogσ : cfc Real.log σ = V * diagonal (fun i => (Real.log (ev_σ i) : ℂ)) * Vᴴ := by
    exact cfc_log_spectral_eq hσ
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
    · simp only [ite_true]
    · intro b _ hb
      simp only [ite_eq_right hb, mul_zero]
    · intro h; exact absurd (Finset.mem_univ x) h
  have h2 : ∀ x, (∑ x_1, star (W x_1 x) * if x_1 = j then ↑(Real.log (ev_σ x_1)) else 0) =
      star (W j x) * ↑(Real.log (ev_σ j)) := by
    intro x
    rw [Finset.sum_eq_single j]
    · simp only [ite_true]
    · intro b _ hb
      simp only [ite_eq_right hb, mul_zero]
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

end RelativeEigenbasis

/-! ### Invariance under `*-`algebra equivalences -/

omit [DecidableEq n] [DecidableEq m] in
/-- Support inclusion is invariant under `*-`algebra equivalences of matrix algebras. -/
theorem suppSubset_map_starAlgEquiv_iff {ρ σ : Matrix m m ℂ} (hσ : σ.IsHermitian)
    (φ : Matrix m m ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ) :
    suppSubset (φ ρ) (φ σ) ↔ suppSubset ρ σ := by
  classical
  rw [suppSubset_iff_mul_cfc_eq_zero (hσ.map_starAlgEquiv φ),
    suppSubset_iff_mul_cfc_eq_zero hσ, cfc_map_starAlgEquiv hσ _ φ, ← map_mul,
    map_eq_zero_iff φ φ.injective]

end Matrix
