module

public import QuantumSystem.Analysis.Entropy.SSAProduct
public import QuantumSystem.ForMathlib.LinearAlgebra.Matrix.PosDef

/-!
# Strong subadditivity in the `lean-eval` formulation

This file reproduces the statement of strong subadditivity of the von Neumann entropy as posed in
[`lean-eval`](https://github.com/leanprover/lean-eval) (`LeanEval/Physics/StrongSubadditivity.lean`)
and proves it by reducing to the project's `DensityMatrix.vonNeumannEntropy_SSA`.

The `lean-eval` problem states, for a tripartite **positive semidefinite** matrix `M_ABC`
(deliberately *not* normalised — normalisation is a positive affine transformation on the entropy):

  `entropy M_ABC + entropy M_B ≤ entropy M_AB + entropy M_BC`,

where `entropy M = -Re (Tr (M * cfc Real.log M))` and the marginals are the positional partial
traces `Matrix.traceLeft`/`Matrix.traceRight`.

## Bridge to the project's entropy

The project's `Matrix.vonNeumannEntropy` is defined for a `DensityMatrix` via `DensityMatrix.log`,
i.e. Mathlib's `cfc Real.log`. The lemma
`LeanEval.Physics.entropy_toMatrix_eq_vonNeumannEntropy` records that the two notions of
entropy coincide on a density matrix.
-/

@[expose] public section

open Matrix
open scoped Matrix.QuantumInfo ComplexOrder MatrixOrder

namespace LeanEval

namespace Physics

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Von Neumann entropy of a quantum state (the `lean-eval` definition, via Mathlib's continuous
functional calculus). -/
noncomputable def entropy (M : Matrix n n ℂ) : ℝ :=
  -Complex.re (Matrix.trace (M * cfc Real.log M))

/-- On a density matrix the `lean-eval` `entropy` coincides with the project's
`Matrix.vonNeumannEntropy`. -/
theorem entropy_toMatrix_eq_vonNeumannEntropy (ρ : DensityMatrix n) :
    entropy ρ.toMatrix = S(ρ) := by
  rw [entropy, Matrix.vonNeumannEntropy, DensityMatrix.log]
  rfl

/-- The `lean-eval` `entropy` of a positive semidefinite matrix equals the spectral sum
`∑ᵢ negMulLog λᵢ`, with `Real.negMulLog 0 = 0` accounting for the kernel. Valid for any PSD
matrix (not necessarily normalised). -/
theorem entropy_eq_negMulLog_sum (M : Matrix n n ℂ) (hM : M.PosSemidef) :
    entropy M = ∑ i, Real.negMulLog (hM.1.eigenvalues i) := by
  rw [entropy, trace_mul_cfc hM.1,
    Complex.re_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Complex.ofReal_mul, Complex.ofReal_re, Real.negMulLog]
  ring

/-- The entropy of the zero matrix is `0`. -/
@[simp] theorem entropy_zero : entropy (0 : Matrix n n ℂ) = 0 := by
  rw [entropy]
  simp

/-- A real-valued function is continuous on any finite set (the subspace topology is discrete). -/
private lemma continuousOn_of_finite {s : Set ℝ} (hs : s.Finite) (g : ℝ → ℝ) :
    ContinuousOn g s := by
  rw [continuousOn_iff_continuous_restrict]
  have : Finite s := hs.to_subtype
  exact continuous_of_discreteTopology

/-- The real spectrum of a Hermitian matrix is finite. -/
private lemma spectrum_real_finite {N : Matrix n n ℂ} (hN : N.IsHermitian) :
    (spectrum ℝ N).Finite := by
  rw [hN.spectrum_real_eq_range_eigenvalues]
  exact Set.finite_range _

/-- The real part of the trace of a Hermitian matrix is the sum of its eigenvalues. -/
private lemma trace_re_eq_sum_eigenvalues {N : Matrix n n ℂ} (hN : N.IsHermitian) :
    (N.trace).re = ∑ i, hN.eigenvalues i := by
  have h : N.trace = ∑ i, ((hN.eigenvalues i : ℝ) : ℂ) := by
    have hsa : IsSelfAdjoint N := hN
    conv_lhs => rw [← cfc_id' (R := ℝ) (a := N) hsa]
    rw [trace_cfc hN]
  rw [h, Complex.re_sum]
  simp

/-- **Scale law for the entropy.** For `c > 0` and a positive semidefinite matrix `N`,
`entropy (c • N) = c · entropy N − c · log c · Tr N`. With `c = Tr N` this expresses the
normalisation of an unnormalised state as a positive affine transformation on the entropy. -/
theorem entropy_smul {c : ℝ} (hc : 0 < c) {N : Matrix n n ℂ} (hN : N.PosSemidef) :
    entropy (c • N) = c * entropy N - c * Real.log c * (N.trace).re := by
  have hsa : IsSelfAdjoint N := hN.1
  have hf_cont : ContinuousOn (fun x => c * x) (spectrum ℝ N) :=
    (continuous_const.mul continuous_id).continuousOn
  have hlog_cont : ContinuousOn Real.log ((fun x => c * x) '' spectrum ℝ N) :=
    continuousOn_of_finite ((spectrum_real_finite hN.1).image _) _
  have hgc_cont : ContinuousOn (fun x => Real.log (c * x)) (spectrum ℝ N) :=
    continuousOn_of_finite (spectrum_real_finite hN.1) _
  have hCN : (c • N : Matrix n n ℂ) = cfc (fun x => c * x) N := by
    rw [cfc_const_mul (R := ℝ) c (fun x => x) N, cfc_id' (R := ℝ) (a := N) hsa]
  have hlogCN : cfc Real.log (c • N) = cfc (fun x => Real.log (c * x)) N := by
    conv_lhs => rw [hCN]
    rw [← cfc_comp Real.log (fun x => c * x) N hsa hlog_cont hf_cont]
    rfl
  have hprod : (c • N) * cfc Real.log (c • N) =
      cfc (fun x => (c * x) * Real.log (c * x)) N := by
    rw [hlogCN, hCN, ← cfc_mul (fun x => c * x) (fun x => Real.log (c * x)) N hf_cont hgc_cont]
  rw [entropy, hprod, trace_cfc hN.1,
    Complex.re_sum, entropy_eq_negMulLog_sum N hN,
    trace_re_eq_sum_eigenvalues hN.1, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Complex.ofReal_re]
  rw [Real.negMulLog]
  rcases eq_or_lt_of_le (hN.1.posSemidef_iff_eigenvalues_nonneg.mp hN i) with h0 | hpos
  · rw [← h0]; simp
  · rw [Real.log_mul (ne_of_gt hc) (ne_of_gt hpos)]; ring


/-! ### Reduction to independent universes and to positive semidefinite matrices

The `lean-eval` statement allows the three factors `A`, `B`, `C` to live in independent universes,
and works with an arbitrary positive semidefinite matrix (not necessarily a normalised state).
We reduce it to `strong_subadditivity_density` (same universe, normalised) in two steps:
`ULift`-reindexing into a common universe, then normalisation via the entropy scale law. -/

section Independent

universe uA uB uC

variable {A : Type uA} {B : Type uB} {C : Type uC}
  [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype B] [DecidableEq B] [Nonempty B]
  [Fintype C] [DecidableEq C] [Nonempty C]

/-- **Strong subadditivity of the von Neumann entropy** (the `lean-eval` statement). For any
positive semidefinite `M_ABC` on `A × B × C`,
`S(M_ABC) + S(M_B) ≤ S(M_AB) + S(M_BC)`, where the marginals are obtained by partial traces.
The proof normalises `M_ABC` to a state via the entropy scale law and invokes the
`LocalNet`-free product-form core `DensityMatrix.vonNeumannEntropy_SSA_product`. -/
theorem strong_subadditivity (M_ABC : Matrix (A × B × C) (A × B × C) ℂ) (h : M_ABC.PosSemidef) :
    let M_AB : Matrix (A × B) (A × B) ℂ :=
      Matrix.traceRight (M_ABC.reindex (Equiv.prodAssoc A B C).symm (Equiv.prodAssoc A B C).symm)
    let M_BC : Matrix (B × C) (B × C) ℂ := M_ABC.traceLeft
    let M_B : Matrix B B ℂ := M_BC.traceRight
    entropy M_ABC + entropy M_B ≤ entropy M_AB + entropy M_BC := by
  intro M_AB M_BC M_B
  have htr_nn : (0 : ℂ) ≤ M_ABC.trace := h.trace_nonneg
  have ht_re : (0 : ℝ) ≤ (M_ABC.trace).re := (Complex.nonneg_iff.mp htr_nn).1
  have ht_im : (M_ABC.trace).im = 0 := (Complex.nonneg_iff.mp htr_nn).2.symm
  have htrace_real : M_ABC.trace = (((M_ABC.trace).re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [ht_im]
  rcases eq_or_lt_of_le ht_re with ht0 | ht_pos
  · -- `Tr M_ABC = 0` forces `M_ABC = 0`; all marginals and entropies vanish.
    have hM0 : M_ABC = 0 := by rw [← h.trace_eq_zero_iff, htrace_real, ← ht0]; simp
    simp [M_AB, M_BC, M_B, hM0, Matrix.reindex_apply, entropy_zero]
  · -- Normalise `M_ABC = t • ρ` with `ρ` a state, then apply the density-matrix version.
    set t : ℝ := (M_ABC.trace).re with ht_def
    have htr_smul : Tr ((t⁻¹ : ℝ) • M_ABC) = (t⁻¹ : ℝ) • Tr M_ABC := by
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.smul_apply]
      exact Finset.smul_sum.symm
    have ρtrace : Tr ((t⁻¹ : ℝ) • M_ABC) = 1 := by
      rw [htr_smul, htrace_real, Complex.real_smul, ← Complex.ofReal_mul,
        inv_mul_cancel₀ (ne_of_gt ht_pos), Complex.ofReal_one]
    let ρ : DensityMatrix (A × B × C) :=
      ⟨(t⁻¹ : ℝ) • M_ABC, Matrix.posSemidef_smul_nonneg (inv_nonneg.mpr ht_re) h, ρtrace⟩
    have hMeq : M_ABC = t • ρ.toMatrix := (smul_inv_smul₀ (ne_of_gt ht_pos) M_ABC).symm
    have hρ_tr : (ρ.toMatrix.trace).re = 1 := by rw [ρ.trace_eq_one]; simp
    -- Each marginal of `M_ABC` is `t` times the corresponding marginal of `ρ`.
    have hM_B : M_B = t • Matrix.traceRight (Matrix.traceLeft ρ.toMatrix) := by
      calc
        Matrix.traceRight (Matrix.traceLeft M_ABC)
            = Matrix.traceRight (Matrix.traceLeft (t • ρ.toMatrix)) := by rw [hMeq]
        _ = Matrix.traceRight (t • Matrix.traceLeft ρ.toMatrix) := by
          rw [show Matrix.traceLeft (t • ρ.toMatrix) = t • Matrix.traceLeft ρ.toMatrix from by
            exact Matrix.traceLeft_smul (l := B × C) (n := A) t ρ.toMatrix]
        _ = t • Matrix.traceRight (Matrix.traceLeft ρ.toMatrix) := by
          exact Matrix.traceRight_smul (l := B) (n := C) t (Matrix.traceLeft ρ.toMatrix)
    have hM_BC : M_BC = t • Matrix.traceLeft ρ.toMatrix := by
      calc
        Matrix.traceLeft M_ABC = Matrix.traceLeft (t • ρ.toMatrix) := by rw [hMeq]
        _ = t • Matrix.traceLeft ρ.toMatrix := by
          exact Matrix.traceLeft_smul (l := B × C) (n := A) t ρ.toMatrix
    have hM_AB : M_AB = t • Matrix.traceRight (ρ.toMatrix.reindex (Equiv.prodAssoc A B C).symm
        (Equiv.prodAssoc A B C).symm) := by
      have hrs : (t • ρ.toMatrix).reindex (Equiv.prodAssoc A B C).symm (Equiv.prodAssoc A B C).symm
          = t • ρ.toMatrix.reindex (Equiv.prodAssoc A B C).symm (Equiv.prodAssoc A B C).symm := by
        ext p q; simp [Matrix.reindex_apply, Matrix.submatrix_apply]
      calc
        Matrix.traceRight (M_ABC.reindex (Equiv.prodAssoc A B C).symm (Equiv.prodAssoc A B C).symm)
            = Matrix.traceRight ((t • ρ.toMatrix).reindex (Equiv.prodAssoc A B C).symm
                (Equiv.prodAssoc A B C).symm) := by rw [hMeq]
        _ = Matrix.traceRight (t • ρ.toMatrix.reindex (Equiv.prodAssoc A B C).symm
              (Equiv.prodAssoc A B C).symm) := by rw [hrs]
        _ = t • Matrix.traceRight (ρ.toMatrix.reindex (Equiv.prodAssoc A B C).symm
              (Equiv.prodAssoc A B C).symm) := by
          exact Matrix.traceRight_smul (l := A × B) (n := C) t
            (ρ.toMatrix.reindex (Equiv.prodAssoc A B C).symm (Equiv.prodAssoc A B C).symm)
    -- Positive semidefiniteness and unit trace of the `ρ`-marginals (for the scale law).
    have hρB : (Matrix.traceRight (Matrix.traceLeft ρ.toMatrix)).PosSemidef :=
      Matrix.traceRight_posSemidef (Matrix.traceLeft_posSemidef ρ.posSemidef)
    have hρB_tr : (Matrix.traceRight (Matrix.traceLeft ρ.toMatrix)).trace.re = 1 := by
      rw [Matrix.trace_traceRight, Matrix.trace_traceLeft, ρ.trace_eq_one]; simp
    have hρBC : (Matrix.traceLeft ρ.toMatrix).PosSemidef := Matrix.traceLeft_posSemidef ρ.posSemidef
    have hρBC_tr : (Matrix.traceLeft ρ.toMatrix).trace.re = 1 := by
      rw [Matrix.trace_traceLeft, ρ.trace_eq_one]; simp
    have hρAB : (Matrix.traceRight (ρ.toMatrix.reindex (Equiv.prodAssoc A B C).symm
        (Equiv.prodAssoc A B C).symm)).PosSemidef :=
      Matrix.traceRight_posSemidef ((Matrix.posSemidef_submatrix_equiv _).mpr ρ.posSemidef)
    have hρAB_tr : (Matrix.traceRight (ρ.toMatrix.reindex (Equiv.prodAssoc A B C).symm
        (Equiv.prodAssoc A B C).symm)).trace.re = 1 := by
      rw [Matrix.trace_traceRight, Matrix.trace_reindex_self, ρ.trace_eq_one]; simp
    -- Scale law on each entropy.
    have key_ABC : entropy M_ABC = t * entropy ρ.toMatrix - t * Real.log t := by
      rw [congrArg entropy hMeq, entropy_smul ht_pos ρ.posSemidef, hρ_tr]; ring
    have key_B : entropy M_B
        = t * entropy (Matrix.traceRight (Matrix.traceLeft ρ.toMatrix)) - t * Real.log t := by
      rw [hM_B, entropy_smul ht_pos hρB, hρB_tr]; ring
    have key_BC : entropy M_BC
        = t * entropy (Matrix.traceLeft ρ.toMatrix) - t * Real.log t := by
      rw [hM_BC, entropy_smul ht_pos hρBC, hρBC_tr]; ring
    have key_AB : entropy M_AB
        = t * entropy (Matrix.traceRight (ρ.toMatrix.reindex (Equiv.prodAssoc A B C).symm
            (Equiv.prodAssoc A B C).symm)) - t * Real.log t := by
      rw [hM_AB, entropy_smul ht_pos hρAB, hρAB_tr]; ring
    rw [key_ABC, key_B, key_AB, key_BC]
    -- The density-matrix SSA in `entropy` form, obtained directly from the product-form core.
    have hSSA : entropy ρ.toMatrix + entropy (Matrix.traceRight (Matrix.traceLeft ρ.toMatrix))
        ≤ entropy (Matrix.traceRight (ρ.toMatrix.reindex (Equiv.prodAssoc A B C).symm
            (Equiv.prodAssoc A B C).symm)) + entropy (Matrix.traceLeft ρ.toMatrix) := by
      have e_full : entropy ρ.toMatrix = S(ρ) := entropy_toMatrix_eq_vonNeumannEntropy ρ
      have e_B : entropy (Matrix.traceRight (Matrix.traceLeft ρ.toMatrix))
          = S(ρ.ptLeft.ptRight) := entropy_toMatrix_eq_vonNeumannEntropy ρ.ptLeft.ptRight
      have e_BC : entropy (Matrix.traceLeft ρ.toMatrix) = S(ρ.ptLeft) :=
        entropy_toMatrix_eq_vonNeumannEntropy ρ.ptLeft
      have e_AB : entropy (Matrix.traceRight (ρ.toMatrix.reindex (Equiv.prodAssoc A B C).symm
            (Equiv.prodAssoc A B C).symm)) = S((ρ.mapEquiv (Equiv.prodAssoc A B C)).ptRight) := by
        simp only [Matrix.reindex_apply, Equiv.symm_symm]
        exact entropy_toMatrix_eq_vonNeumannEntropy ((ρ.mapEquiv (Equiv.prodAssoc A B C)).ptRight)
      rw [e_full, e_B, e_AB, e_BC]
      exact DensityMatrix.vonNeumannEntropy_SSA_product ρ _ _ _ rfl rfl rfl
    nlinarith [mul_le_mul_of_nonneg_left hSSA ht_pos.le]

end Independent

end Physics

end LeanEval
