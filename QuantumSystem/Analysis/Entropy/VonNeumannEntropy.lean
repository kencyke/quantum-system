module

public import QuantumSystem.Analysis.Matrix.Order
public import QuantumSystem.ForMathlib.Analysis.Calculus.Deriv.Sign
public import QuantumSystem.ForMathlib.InformationTheory.KullbackLeibler.KLFun
public import QuantumSystem.State

/-!
# Von Neumann Entropy

This file contains definitions and core properties of von Neumann entropy.

## Main Results

* `vonNeumannEntropy_concave`: Von Neumann entropy is concave.
-/

@[expose] public section

namespace Matrix

open scoped MatrixOrder ComplexOrder QuantumInfo

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The entropy function η(x) = -x log x, extended by continuity to η(0) = 0.
This is concave on [0, ∞). -/
noncomputable def entropyFun (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else -x * Real.log x

theorem entropyFun_nonneg {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ entropyFun x := by
  unfold entropyFun
  split_ifs with hle
  · exact le_refl 0
  · push_neg at hle
    have hlog : Real.log x ≤ 0 := Real.log_nonpos hx hx1
    nlinarith [hle, hlog]

/-- Von Neumann entropy of a density matrix: S(ρ) = −Tr (ρ log ρ).
Since ρ log ρ is Hermitian (see `DensityMatrix.mul_log_isHermitian`),
its trace is real, so `.re` is lossless (see `vonNeumannEntropy_ofReal`). -/
noncomputable def vonNeumannEntropy (ρ : DensityMatrix n) : ℝ :=
  -(Tr (ρ * log ρ)).re

namespace QuantumInfo
scoped notation "S(" ρ ")" => Matrix.vonNeumannEntropy ρ
end QuantumInfo

/-- Casting `S(ρ)` back to ℂ recovers −Tr(ρ log ρ) exactly, confirming the trace is real. -/
@[simp]
theorem vonNeumannEntropy_ofReal (ρ : DensityMatrix n) :
    (S(ρ) : ℂ) = -(Tr (ρ * log ρ)) := by
  unfold vonNeumannEntropy
  rw [Complex.ofReal_neg]
  congr 1
  exact ρ.mul_log_isHermitian.trace_ofReal_re

/-- Von Neumann entropy equals the eigenvalue sum S(ρ) = ∑ᵢ (−λᵢ log λᵢ). -/
theorem vonNeumannEntropy_eq_sum (ρ : DensityMatrix n) :
    S(ρ) = ∑ i, entropyFun (ρ.isHermitian.eigenvalues i) := by
  unfold vonNeumannEntropy DensityMatrix.log matrixLog
  change -(Tr (ρ.toMatrix * matrixFunction _ ρ.toMatrix ρ.isHermitian)).re = _
  rw [trace_mul_matrixFunction, Complex.re_sum]
  simp_rw [← Complex.ofReal_mul, Complex.ofReal_re, ← Finset.sum_neg_distrib]
  congr 1
  ext i
  unfold entropyFun
  split_ifs with hle
  · have h0 := le_antisymm hle (ρ.eigenvalues_nonneg i)
    simp [h0]
  · ring

/-- For `x ≥ 0`, `entropyFun x = Real.negMulLog x`. -/
theorem entropyFun_eq_negMulLog_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    entropyFun x = Real.negMulLog x := by
  unfold entropyFun Real.negMulLog
  split_ifs with h
  · have h0 : x = 0 := le_antisymm h hx
    rw [h0]; ring
  · rfl

/-- `vonNeumannEntropy ρ = ∑ᵢ Real.negMulLog (ρ.eigenvalues i)`.

Since `ρ` is PSD, its eigenvalues are non-negative, so `entropyFun = Real.negMulLog`
on the sum range. -/
theorem vonNeumannEntropy_eq_negMulLog_sum (ρ : DensityMatrix n) :
    vonNeumannEntropy ρ = ∑ i, Real.negMulLog (ρ.isHermitian.eigenvalues i) := by
  rw [vonNeumannEntropy_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact entropyFun_eq_negMulLog_of_nonneg (ρ.eigenvalues_nonneg i)

/-- `vonNeumannEntropy` expressed via the spectral matrix function `matrixFunction`
    applied to `Real.negMulLog`. This bridges to Mathlib's continuous functional
    calculus, enabling continuity arguments. -/
theorem vonNeumannEntropy_eq_matrixFunction_re (ρ : DensityMatrix n) :
    vonNeumannEntropy ρ =
      (Tr (matrixFunction (fun x : ℝ => (Real.negMulLog x : ℂ))
        ρ.toMatrix ρ.isHermitian)).re := by
  rw [matrixFunction_trace, vonNeumannEntropy_eq_negMulLog_sum]
  rw [Complex.re_sum]
  simp_rw [Complex.ofReal_re]

/-- Von Neumann entropy is non-negative. -/
theorem vonNeumannEntropy_nonneg (ρ : DensityMatrix n) :
    0 ≤ S(ρ) := by
  rw [vonNeumannEntropy_eq_sum]
  apply Finset.sum_nonneg
  intro i _
  exact entropyFun_nonneg (ρ.eigenvalues_nonneg i) (ρ.eigenvalue_le_one i)

/-- Von Neumann entropy is at most log(dim), achieved for the maximally mixed state.
This follows from Jensen's inequality applied to the concave function -x log x. -/
theorem vonNeumannEntropy_le_log_dim [Nonempty n] (ρ : DensityMatrix n) :
    S(ρ) ≤ Real.log (Fintype.card n) := by
  rw [vonNeumannEntropy_eq_sum]
  have heq : ∀ i, entropyFun (ρ.isHermitian.eigenvalues i) =
      Real.negMulLog (ρ.isHermitian.eigenvalues i) := by
    intro i
    unfold entropyFun Real.negMulLog
    split_ifs with hle
    · have h0 : ρ.isHermitian.eigenvalues i = 0 := le_antisymm hle (ρ.eigenvalues_nonneg i)
      simp [h0]
    · rfl
  simp_rw [heq]
  have hlog_inv : Real.log (1 / Fintype.card n) = -Real.log (Fintype.card n) := by
    rw [one_div, Real.log_inv]
  have hunif_pos : ∀ i : n, 0 < 1 / (Fintype.card n : ℝ) := fun _ => by positivity
  have hunif_sum : ∑ _ : n, 1 / (Fintype.card n : ℝ) = 1 := by
    rw [Finset.sum_const, Finset.card_univ]
    simp
  have hKL : 0 ≤ ∑ i, ρ.isHermitian.eigenvalues i *
      (Real.log (ρ.isHermitian.eigenvalues i) - Real.log (1 / Fintype.card n)) := by
    have hsum_lower : ∑ i, ρ.isHermitian.eigenvalues i *
        (Real.log (ρ.isHermitian.eigenvalues i) - Real.log (1 / Fintype.card n)) ≥
        ∑ i, (ρ.isHermitian.eigenvalues i - 1 / Fintype.card n) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hp : ρ.isHermitian.eigenvalues i = 0
      · simp [hp]
      · have hpi_pos : 0 < ρ.isHermitian.eigenvalues i :=
          lt_of_le_of_ne (ρ.eigenvalues_nonneg i) (ne_comm.mp hp)
        have hmul := mul_log_div_ge_sub' hpi_pos (hunif_pos i)
        rw [Real.log_div (ne_of_gt hpi_pos) (ne_of_gt (hunif_pos i))] at hmul
        linarith
    have hsum_zero : ∑ i, (ρ.isHermitian.eigenvalues i - 1 / Fintype.card n) = 0 := by
      rw [Finset.sum_sub_distrib, ρ.sum_eigenvalues, hunif_sum, sub_self]
    linarith
  simp only [hlog_inv, sub_neg_eq_add] at hKL
  have hexpand : ∑ i, ρ.isHermitian.eigenvalues i *
      (Real.log (ρ.isHermitian.eigenvalues i) + Real.log (Fintype.card n)) =
      ∑ i, ρ.isHermitian.eigenvalues i * Real.log (ρ.isHermitian.eigenvalues i) +
      Real.log (Fintype.card n) := by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ρ.sum_eigenvalues, one_mul]
  rw [hexpand] at hKL
  have hneg : ∑ i, Real.negMulLog (ρ.isHermitian.eigenvalues i) =
      -∑ i, ρ.isHermitian.eigenvalues i * Real.log (ρ.isHermitian.eigenvalues i) := by
    rw [← Finset.sum_neg_distrib]
    congr 1
    ext i
    unfold Real.negMulLog
    ring
  rw [hneg]
  linarith

/-- For PosSemidef ρ: Re(Tr (ρ^s)) = ∑ i, eigenvalue_i ^ s.
This follows from the spectral theorem: ρ^s = U diag(λᵢ^s) U†,
and trace cyclicity Tr (U D U†) = Tr (D) = ∑ Dᵢᵢ. -/
lemma trace_rpow_eq_sum_pow (ρ : Matrix n n ℂ) (hρ : ρ.PosSemidef) (s : ℝ) :
    (Tr (ρ ^ s)).re = ∑ i, hρ.1.eigenvalues i ^ s := by
  rw [← matrixFunction_rpow_eq hρ s, matrixFunction_trace]
  simp [Complex.ofReal_re]

/-- HasDerivAt of eigenvalue rpow sum.
d/ds (∑ i, λᵢ ^ s)|_{s=1} = ∑ i, λᵢ * log(λᵢ).
This follows from HasStrictDerivAt of x^s in s at s=1 for each term. -/
lemma hasDerivAt_sum_rpow {α : Type*} [Fintype α] (evs : α → ℝ) (hev : ∀ i, 0 ≤ evs i) :
    HasDerivAt (fun (s : ℝ) => ∑ i, evs i ^ s) (∑ i, evs i * Real.log (evs i)) 1 := by
  let F : α → ℝ → ℝ := fun i s => evs i ^ s
  have hF : ∀ i ∈ Finset.univ, HasDerivAt (F i) (evs i * Real.log (evs i)) 1 := by
    intro i _
    simp only [F]
    rcases (hev i).lt_or_eq with hpos | hzero
    · have h := HasDerivAt.exp ((hasDerivAt_id (𝕜 := ℝ) 1).mul_const (Real.log (evs i)))
      simp only [id] at h
      convert h using 1
      · ext s
        rw [Real.rpow_def_of_pos hpos, mul_comm (Real.log (evs i))]
      · rw [one_mul, Real.exp_log hpos]
    · rw [← hzero, Real.log_zero, mul_zero]
      exact (hasDerivAt_const (𝕜 := ℝ) 1 0).congr_of_eventuallyEq
        (Filter.Eventually.mono (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
         (fun x hx => by simp [Real.zero_rpow (ne_of_gt hx)]))
  have hsum : HasDerivAt (∑ i : α, F i) (∑ i : α, evs i * Real.log (evs i)) (1 : ℝ) :=
    HasDerivAt.sum (𝕜 := ℝ) (u := Finset.univ) hF
  have heq : (fun s : ℝ => ∑ i : α, evs i ^ s) = ∑ i : α, F i := by
    ext s
    simp [F]
  rw [heq]
  exact hsum

/-- Trace-rpow concavity: for 0 < s ≤ 1 and positive semidefinite A, B,
    p ⋅ Tr (Aˢ) + (1−p) ⋅ Tr (Bˢ) ≤ Tr ((pA + (1−p)B)ˢ).
    This follows from Löwner-order concavity (`rpow_isLownerConcave`) plus the
    trace-monotonicity of the Hermitian order. -/
lemma trace_rpow_concave (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    p * (Tr (A ^ s)).re + (1 - p) * (Tr (B ^ s)).re ≤ (Tr ((p • A + (1 - p) • B) ^ s)).re := by
  have hpsd_mix : (p • A + (1 - p) • B).PosSemidef := (hA.smul hp).add (hB.smul (by linarith))
  have hlowner := rpow_isLownerConcave hs0 hs1 n A B hA hB p hp hp1 hpsd_mix.1
  simp only [] at hlowner
  have hfunc_eq : (fun x : ℝ => ((-x ^ s : ℝ) : ℂ)) = (fun x : ℝ => -(((x ^ s : ℝ) : ℂ))) := by
    ext x
    exact Complex.ofReal_neg _
  rw [hfunc_eq] at hlowner
  rw [matrixFunction_neg hA.1, matrixFunction_neg hB.1, matrixFunction_neg hpsd_mix.1,
      matrixFunction_rpow_eq hA, matrixFunction_rpow_eq hB, matrixFunction_rpow_eq hpsd_mix] at hlowner
  have hlowner' : p • A ^ s + (1 - p) • B ^ s ≤ (p • A + (1 - p) • B) ^ s := by
    have heq : p • -A ^ s + (1 - p) • -B ^ s = -(p • A ^ s + (1 - p) • B ^ s) := by
      simp [smul_neg]
      abel
    rw [heq] at hlowner
    rwa [neg_le_neg_iff] at hlowner
  rw [Matrix.le_iff] at hlowner'
  have htrace := (Complex.nonneg_iff.mp hlowner'.trace_nonneg).1
  rw [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul] at htrace
  simp only [Complex.sub_re, Complex.add_re, Complex.real_smul, Complex.mul_re,
             Complex.ofReal_re, Complex.ofReal_im] at htrace
  linarith

/-- **Von Neumann entropy is concave**.

S(∑ᵢ pᵢ ρᵢ) ≥ ∑ᵢ pᵢ S(ρᵢ)

**Proof**: We use the Löwner-order concavity of A ↦ Aˢ for 0 < s ≤ 1
(from `rpow_isLownerConcave`). Define g(s) := Tr (ρ_mixˢ)
− p Tr (ρ₁ˢ) − (1−p) Tr (ρ₂ˢ).

- **Non-negativity**: For s ∈ (0,1], Löwner concavity gives
  p ρ₁ˢ + (1−p) ρ₂ˢ ≤ ρ_mixˢ in Löwner order,
  so taking traces gives g(s) ≥ 0.
- **Boundary**: g(1) = 0 since all density matrices have trace 1.
- **Derivative sign**: Since g(1) = 0 ≤ g(s) for nearby s < 1, we have g'(1) ≤ 0.
- **Derivative formula**: g'(1) = −S(ρ_mix) + p S(ρ₁) + (1−p) S(ρ₂)
  via (d/ds)|_{s=1} ∑ᵢ λᵢˢ = ∑ᵢ λᵢ log λᵢ = −S(ρ).
- **Conclusion**: g'(1) ≤ 0 gives the desired concavity inequality.
-/
theorem vonNeumannEntropy_concave (ρ₁ ρ₂ : DensityMatrix n) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    S(DensityMatrix.mix ρ₁ ρ₂ p hp hp1) ≥
    p * S(ρ₁) + (1 - p) * S(ρ₂) := by
  set ρ_mix : DensityMatrix n := DensityMatrix.mix ρ₁ ρ₂ p hp hp1
  have hpsd₁ : ρ₁.toMatrix.PosSemidef := ρ₁.posSemidef
  have hpsd₂ : ρ₂.toMatrix.PosSemidef := ρ₂.posSemidef
  have hpsd_mix : ρ_mix.toMatrix.PosSemidef := ρ_mix.posSemidef
  let g : ℝ → ℝ := fun s =>
    (ρ_mix.toMatrix ^ s).trace.re -
    (p * (ρ₁.toMatrix ^ s).trace.re + (1 - p) * (ρ₂.toMatrix ^ s).trace.re)
  have g_nonneg : ∀ s ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ g s := by
    intro s hs
    exact sub_nonneg.mpr (trace_rpow_concave ρ₁.toMatrix ρ₂.toMatrix hpsd₁ hpsd₂ p hp hp1 s hs.1 hs.2)
  have hg_one : g 1 = 0 := by
    simp only [g]
    rw [CFC.rpow_one _ (by simpa [Matrix.le_iff, sub_zero] using hpsd_mix),
      CFC.rpow_one _ (by simpa [Matrix.le_iff, sub_zero] using hpsd₁),
      CFC.rpow_one _ (by simpa [Matrix.le_iff, sub_zero] using hpsd₂)]
    rw [ρ_mix.trace_eq_one, ρ₁.trace_eq_one, ρ₂.trace_eq_one]
    simp [Complex.one_re]
  have hderiv_mix : HasDerivAt (fun (s : ℝ) => (ρ_mix.toMatrix ^ s).trace.re)
      (∑ i, ρ_mix.isHermitian.eigenvalues i * Real.log (ρ_mix.isHermitian.eigenvalues i)) 1 := by
    convert hasDerivAt_sum_rpow hpsd_mix.1.eigenvalues ρ_mix.eigenvalues_nonneg using 1
    funext s
    exact trace_rpow_eq_sum_pow _ hpsd_mix s
  have hderiv₁ : HasDerivAt (fun (s : ℝ) => (ρ₁.toMatrix ^ s).trace.re)
      (∑ i, ρ₁.isHermitian.eigenvalues i * Real.log (ρ₁.isHermitian.eigenvalues i)) 1 := by
    convert hasDerivAt_sum_rpow hpsd₁.1.eigenvalues ρ₁.eigenvalues_nonneg using 1
    funext s
    exact trace_rpow_eq_sum_pow _ hpsd₁ s
  have hderiv₂ : HasDerivAt (fun (s : ℝ) => (ρ₂.toMatrix ^ s).trace.re)
      (∑ i, ρ₂.isHermitian.eigenvalues i * Real.log (ρ₂.isHermitian.eigenvalues i)) 1 := by
    convert hasDerivAt_sum_rpow hpsd₂.1.eigenvalues ρ₂.eigenvalues_nonneg using 1
    funext s
    exact trace_rpow_eq_sum_pow _ hpsd₂ s
  have hderiv_g : HasDerivAt g
      ((∑ i, ρ_mix.isHermitian.eigenvalues i * Real.log (ρ_mix.isHermitian.eigenvalues i)) -
       (p * (∑ i, ρ₁.isHermitian.eigenvalues i * Real.log (ρ₁.isHermitian.eigenvalues i)) +
        (1 - p) * (∑ i, ρ₂.isHermitian.eigenvalues i * Real.log (ρ₂.isHermitian.eigenvalues i)))) 1 := by
    change HasDerivAt (fun s =>
      (ρ_mix.toMatrix ^ s).trace.re -
      (p * (ρ₁.toMatrix ^ s).trace.re + (1 - p) * (ρ₂.toMatrix ^ s).trace.re)) _ _
    exact hderiv_mix.sub (hderiv₁.const_mul p |>.add (hderiv₂.const_mul (1 - p)))
  have hmin : ∀ y ∈ Set.Ioo (1 - (1 : ℝ) / 2) 1, g 1 ≤ g y := fun y hy => by
    rw [hg_one]
    exact g_nonneg y ⟨by linarith [hy.1], le_of_lt hy.2⟩
  have hderiv_g_nonpos :
      (∑ i, ρ_mix.isHermitian.eigenvalues i * Real.log (ρ_mix.isHermitian.eigenvalues i)) -
      (p * (∑ i, ρ₁.isHermitian.eigenvalues i * Real.log (ρ₁.isHermitian.eigenvalues i)) +
       (1 - p) * (∑ i, ρ₂.isHermitian.eigenvalues i * Real.log (ρ₂.isHermitian.eigenvalues i))) ≤ 0 :=
    deriv_nonpos_of_forall_lt_min g _ 1 (1 / 2) (by norm_num) hderiv_g hmin
  have hmix_eq : ∑ i, ρ_mix.isHermitian.eigenvalues i * Real.log (ρ_mix.isHermitian.eigenvalues i) =
      -vonNeumannEntropy ρ_mix := by
    rw [vonNeumannEntropy_eq_sum, ← Finset.sum_neg_distrib]
    congr 1
    ext i
    unfold entropyFun
    split_ifs with h
    · simp [le_antisymm h (ρ_mix.eigenvalues_nonneg i)]
    · push_neg at h
      ring
  have h₁_eq : ∑ i, ρ₁.isHermitian.eigenvalues i * Real.log (ρ₁.isHermitian.eigenvalues i) =
      -vonNeumannEntropy ρ₁ := by
    rw [vonNeumannEntropy_eq_sum, ← Finset.sum_neg_distrib]
    congr 1
    ext i
    unfold entropyFun
    split_ifs with h
    · simp [le_antisymm h (ρ₁.eigenvalues_nonneg i)]
    · push_neg at h
      ring
  have h₂_eq : ∑ i, ρ₂.isHermitian.eigenvalues i * Real.log (ρ₂.isHermitian.eigenvalues i) =
      -vonNeumannEntropy ρ₂ := by
    rw [vonNeumannEntropy_eq_sum, ← Finset.sum_neg_distrib]
    congr 1
    ext i
    unfold entropyFun
    split_ifs with h
    · simp [le_antisymm h (ρ₂.eigenvalues_nonneg i)]
    · push_neg at h
      ring
  rw [hmix_eq, h₁_eq, h₂_eq] at hderiv_g_nonpos
  linarith

/-! ### Isomorphism invariance

For a `*-`algebra equivalence `φ : Matrix m m ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ` that preserves trace,
von Neumann entropy is invariant: `S(ρ.map φ) = S(ρ)`. In quantum-information literature
this is the **unitary invariance of von Neumann entropy** (Nielsen–Chuang Thm 11.1,
Wilde §11.1.3): a special case of Lindblad–Uhlmann monotonicity restricted to invertible
CPTP maps. The reindex specialisation uses `Matrix.reindexStarAlgEquiv e` which preserves
trace automatically (`Matrix.trace_reindexStarAlgEquiv`).

TODO (Mathlib upstream): for matrix algebras over a field,
`Matrix m m R ≃⋆ₐ[R] Matrix n n R` forces `Fintype.card m = Fintype.card n` (Skolem–Noether
/ structure theorem for type `I_n` factors); once formalised, any cardinality hypothesis
in derived statements becomes automatic. -/

section IsomorphismInvariance

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- **Von Neumann entropy is invariant under trace-preserving `*-`algebra equivalence**
(PosDef case). -/
theorem vonNeumannEntropy_map_starAlgEquiv_posDef
    (ρ : DensityMatrix m) (hρ : ρ.toMatrix.PosDef)
    (φ : Matrix m m ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ)
    (hφ : ∀ A, (φ A).trace = A.trace) :
    S(ρ.map φ hφ) = S(ρ) := by
  unfold vonNeumannEntropy
  have h_log_eq : matrixLog (ρ.map φ hφ).toMatrix (ρ.map φ hφ).isHermitian =
      φ (matrixLog ρ.toMatrix ρ.isHermitian) := by
    change matrixLog (φ ρ.toMatrix) _ = _
    exact matrixLog_map_starAlgEquiv hρ φ
  have h_tr : Tr ((ρ.map φ hφ).toMatrix *
        matrixLog (ρ.map φ hφ).toMatrix (ρ.map φ hφ).isHermitian) =
      Tr (ρ.toMatrix * matrixLog ρ.toMatrix ρ.isHermitian) := by
    rw [h_log_eq, DensityMatrix.map_toMatrix, ← map_mul, hφ]
  change -(Tr ((ρ.map φ hφ).toMatrix *
      matrixLog (ρ.map φ hφ).toMatrix (ρ.map φ hφ).isHermitian)).re =
    -(Tr (ρ.toMatrix * matrixLog ρ.toMatrix ρ.isHermitian)).re
  rw [h_tr]

/-- Specialisation of `vonNeumannEntropy_map_starAlgEquiv_posDef` to reindexing. -/
theorem vonNeumannEntropy_mapEquiv_posDef
    (ρ : DensityMatrix m) (hρ : ρ.toMatrix.PosDef) (e : n ≃ m) :
    S(ρ.mapEquiv e) = S(ρ) :=
  vonNeumannEntropy_map_starAlgEquiv_posDef ρ hρ _ _

end IsomorphismInvariance

/-! ### Regularization and entropy

Using the eigenvalue formula and continuity of `Real.negMulLog`, the entropy of a
regularised state `S(ρ_ε) = ∑ᵢ Real.negMulLog ((1-ε) λᵢ + ε/d)` is continuous in `ε`,
which yields `S(ρ_ε) → S(ρ)` as `ε → 0+`. This is the foundation for extending
PosDef-only theorems to PosSemidef. -/

section Regularization

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- **Eigenvalue formula for the entropy of a regularization**:
    `S(regularize ρ ε) = ∑ᵢ Real.negMulLog ((1-ε) λᵢ + ε/d)` where `λᵢ = ρ.eigenvalues i`. -/
theorem vonNeumannEntropy_regularize_eq_negMulLog_sum [Nonempty n]
    (ρ : DensityMatrix n) {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1) :
    vonNeumannEntropy (DensityMatrix.regularize ρ hε hε') =
      ∑ i, Real.negMulLog ((1 - ε) * ρ.isHermitian.eigenvalues i + ε / Fintype.card n) := by
  rw [vonNeumannEntropy_eq_matrixFunction_re]
  rw [matrixFunction_eq_cfc]
  rw [DensityMatrix.regularize_eq_cfc ρ hε hε']
  have hρ_sa : IsSelfAdjoint ρ.toMatrix := ρ.isHermitian
  rw [← cfc_comp (R := ℝ) Real.negMulLog
      (fun x => (1 - ε) * x + ε / Fintype.card n) ρ.toMatrix
      hρ_sa Real.continuous_negMulLog.continuousOn (by fun_prop)]
  rw [show (Real.negMulLog ∘ (fun x : ℝ => (1 - ε) * x + ε / (Fintype.card n : ℝ))) =
      (fun x : ℝ => Real.negMulLog ((1 - ε) * x + ε / (Fintype.card n : ℝ))) from rfl]
  rw [← matrixFunction_eq_cfc ρ.isHermitian
      (fun x : ℝ => Real.negMulLog ((1 - ε) * x + ε / Fintype.card n))]
  rw [matrixFunction_trace, Complex.re_sum]
  simp_rw [Complex.ofReal_re]

/-- The eigenvalue-formula function `ε ↦ ∑ᵢ Real.negMulLog ((1-ε) λᵢ + ε/d)` is
    continuous in `ε ∈ ℝ`. -/
theorem continuous_negMulLog_regularize_sum (ρ : DensityMatrix n) :
    Continuous (fun ε : ℝ =>
      ∑ i, Real.negMulLog ((1 - ε) * ρ.isHermitian.eigenvalues i + ε / Fintype.card n)) := by
  refine continuous_finset_sum _ fun i _ => ?_
  exact Real.continuous_negMulLog.comp
    ((continuous_const.sub continuous_id).mul continuous_const |>.add
      (continuous_id.mul continuous_const))

/-- **Limit of regularization eigenvalue sum at `ε = 0`**:
    `lim_{ε → 0} ∑ᵢ Real.negMulLog ((1-ε) λᵢ + ε/d) = S(ρ)`.

This is the key continuity result. Combined with `vonNeumannEntropy_regularize_eq_negMulLog_sum`,
it gives `lim_{ε → 0+} S(regularize ρ ε) = S(ρ)`, the foundation for extending PosDef-only
theorems to PosSemidef. -/
theorem tendsto_negMulLog_regularize_sum_zero (ρ : DensityMatrix n) :
    Filter.Tendsto
      (fun ε : ℝ =>
        ∑ i, Real.negMulLog ((1 - ε) * ρ.isHermitian.eigenvalues i + ε / Fintype.card n))
      (nhds 0)
      (nhds (vonNeumannEntropy ρ)) := by
  have h_at_zero : (∑ i, Real.negMulLog ((1 - (0 : ℝ)) * ρ.isHermitian.eigenvalues i +
        (0 : ℝ) / Fintype.card n)) = vonNeumannEntropy ρ := by
    rw [vonNeumannEntropy_eq_negMulLog_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring_nf
  rw [← h_at_zero]
  exact (continuous_negMulLog_regularize_sum ρ).tendsto 0

/-- **`vonNeumannEntropy` is invariant under reindex** (PSD case, no PosDef required).

For any density matrix `ρ` and equivalence `e`, the entropy is preserved:
`S(ρ.mapEquiv e) = S(ρ)`. Proven via regularization + limit. -/
theorem vonNeumannEntropy_mapEquiv [Nonempty n] [Nonempty m]
    (ρ : DensityMatrix m) (e : n ≃ m) :
    vonNeumannEntropy (DensityMatrix.mapEquiv ρ e) = vonNeumannEntropy ρ := by
  have h_eq : ∀ ε : ℝ, ∀ (hε_pos : 0 < ε) (hε_le : ε ≤ 1),
      vonNeumannEntropy (DensityMatrix.regularize
          (DensityMatrix.mapEquiv ρ e) hε_pos.le hε_le) =
        vonNeumannEntropy (DensityMatrix.regularize ρ hε_pos.le hε_le) := by
    intro ε hε_pos hε_le
    rw [DensityMatrix.regularize_mapEquiv ρ e hε_pos.le hε_le]
    exact vonNeumannEntropy_mapEquiv_posDef
      (DensityMatrix.regularize ρ hε_pos.le hε_le)
      (DensityMatrix.regularize_posDef ρ hε_pos hε_le) e
  have h_LHS_lim : Filter.Tendsto
      (fun ε : ℝ =>
        ∑ i, Real.negMulLog ((1 - ε) *
            (DensityMatrix.mapEquiv ρ e).isHermitian.eigenvalues i +
          ε / Fintype.card n))
      (nhds 0) (nhds (vonNeumannEntropy (DensityMatrix.mapEquiv ρ e))) :=
    tendsto_negMulLog_regularize_sum_zero (DensityMatrix.mapEquiv ρ e)
  have h_RHS_lim : Filter.Tendsto
      (fun ε : ℝ =>
        ∑ i, Real.negMulLog ((1 - ε) * ρ.isHermitian.eigenvalues i +
          ε / Fintype.card m))
      (nhds 0) (nhds (vonNeumannEntropy ρ)) :=
    tendsto_negMulLog_regularize_sum_zero ρ
  have h_funeq : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (∑ i, Real.negMulLog ((1 - ε) *
          (DensityMatrix.mapEquiv ρ e).isHermitian.eigenvalues i +
          ε / Fintype.card n)) =
      (∑ i, Real.negMulLog ((1 - ε) * ρ.isHermitian.eigenvalues i +
          ε / Fintype.card m)) := by
    intro ε hε_pos hε_le
    rw [← vonNeumannEntropy_regularize_eq_negMulLog_sum
          (DensityMatrix.mapEquiv ρ e) hε_pos.le hε_le,
        ← vonNeumannEntropy_regularize_eq_negMulLog_sum ρ hε_pos.le hε_le]
    exact h_eq ε hε_pos hε_le
  have h_within : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (∑ i, Real.negMulLog ((1 - ε) *
          (DensityMatrix.mapEquiv ρ e).isHermitian.eigenvalues i +
          ε / Fintype.card n)) =
      (∑ i, Real.negMulLog ((1 - ε) * ρ.isHermitian.eigenvalues i +
          ε / Fintype.card m)) := by
    rw [eventually_nhdsWithin_iff]
    have h_le_one : ∀ᶠ ε in nhds (0 : ℝ), ε ≤ 1 :=
      Filter.eventually_of_mem (IsOpen.mem_nhds isOpen_Iio (by norm_num : (0 : ℝ) < 1)) <| by
        intros ε hε
        exact le_of_lt hε
    filter_upwards [h_le_one] with ε hε_le_one hε_pos
    exact h_funeq ε hε_pos hε_le_one
  have hLHS_within := h_LHS_lim.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hRHS_within := h_RHS_lim.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  exact tendsto_nhds_unique (hLHS_within.congr' h_within) hRHS_within

end Regularization

end Matrix
