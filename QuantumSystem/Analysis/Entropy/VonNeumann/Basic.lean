/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.Matrix.Order
public import QuantumSystem.ForMathlib.Analysis.Calculus.Deriv.Sign
public import QuantumSystem.ForMathlib.InformationTheory.KullbackLeibler.KLFun
public import QuantumSystem.Analysis.Matrix.DensityMatrix.Basic

/-!
# Von Neumann Entropy

The **von Neumann entropy** `S(ρ) = -Tr (ρ log ρ)` of a density matrix `ρ`, and its core
properties.

## Conventions

* Logarithms are natural (`Real.log`), so the unit is the nat.
* `log ρ` is the continuous functional calculus `cfc Real.log ρ` (`DensityMatrix.log`). With
  Mathlib's `Real.log 0 = 0`, the kernel of `ρ` contributes `0 · log 0 = 0`, so
  `S(ρ) = -Σᵢ λᵢ log λᵢ` over the eigenvalues `λᵢ` of `ρ`.

## Main definitions

* `Matrix.vonNeumannEntropy ρ` — `S(ρ) = -Re Tr (ρ log ρ) ∈ ℝ`, with notation `S(ρ)` in scope
  `Matrix.QuantumInfo`.

## Main results

* `Matrix.vonNeumannEntropy_eq_negMulLog_sum` — eigenvalue-sum form `S(ρ) = ∑ᵢ negMulLog λᵢ`.
* `Matrix.vonNeumannEntropy_nonneg` — `0 ≤ S(ρ)`.
* `Matrix.vonNeumannEntropy_le_log_dim` — `S(ρ) ≤ log d`, `d = Fintype.card n`;
  `Matrix.vonNeumannEntropy_maximallyMixed` — `S(I / d) = log d`;
  `Matrix.vonNeumannEntropy_eq_log_card_iff` — the maximum is attained only at `I / d`.
* `Matrix.vonNeumannEntropy_concave` — concavity, two-point form;
  `Matrix.vonNeumannEntropy_concave_sum` — the finite form `Σᵢ wᵢ S(ρᵢ) ≤ S(Σᵢ wᵢ ρᵢ)`.
* `Matrix.vonNeumannEntropy_map_starAlgEquiv`, `Matrix.vonNeumannEntropy_mapEquiv` — invariance
  under `⋆`-algebra equivalences and reindexing.
-/

@[expose] public section

namespace Matrix

open scoped MatrixOrder ComplexOrder QuantumInfo

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Von Neumann entropy of a density matrix: S(ρ) = −Tr (ρ log ρ).
Since ρ log ρ is Hermitian (see `DensityMatrix.mul_log_isHermitian`),
its trace is real, so `.re` is lossless (see `vonNeumannEntropy_ofReal`). -/
noncomputable def vonNeumannEntropy (ρ : DensityMatrix n) : ℝ :=
  -(Tr (ρ * log ρ)).re

namespace QuantumInfo
/-- `S(ρ)` is the von Neumann entropy `Matrix.vonNeumannEntropy ρ`. -/
scoped notation "S(" ρ ")" => Matrix.vonNeumannEntropy ρ
end QuantumInfo

/-- Casting `S(ρ)` back to ℂ recovers −Tr(ρ log ρ) exactly, confirming the trace is real. -/
@[simp]
lemma vonNeumannEntropy_ofReal (ρ : DensityMatrix n) :
    (S(ρ) : ℂ) = -(Tr (ρ * log ρ)) := by
  unfold vonNeumannEntropy
  rw [Complex.ofReal_neg]
  congr 1
  exact ρ.mul_log_isHermitian.trace_ofReal_re

/-- `vonNeumannEntropy ρ = ∑ᵢ Real.negMulLog (ρ.eigenvalues i)`, the eigenvalue-sum form
in terms of Mathlib's `Real.negMulLog`. -/
theorem vonNeumannEntropy_eq_negMulLog_sum (ρ : DensityMatrix n) :
    vonNeumannEntropy ρ = ∑ i, Real.negMulLog (ρ.isHermitian.eigenvalues i) := by
  unfold vonNeumannEntropy DensityMatrix.log
  change -(Tr (ρ.toMatrix * cfc Real.log ρ.toMatrix)).re = _
  rw [trace_mul_cfc ρ.isHermitian, Complex.re_sum]
  simp_rw [← Complex.ofReal_mul, Complex.ofReal_re, ← Finset.sum_neg_distrib]
  congr 1
  ext i
  simp only [Real.negMulLog]
  ring

/-- `vonNeumannEntropy` expressed via Mathlib's continuous functional calculus
    `cfc` applied to `Real.negMulLog`, enabling continuity arguments. -/
lemma vonNeumannEntropy_eq_cfc_re (ρ : DensityMatrix n) :
    vonNeumannEntropy ρ =
      (Tr (cfc Real.negMulLog ρ.toMatrix)).re := by
  rw [trace_cfc ρ.isHermitian, vonNeumannEntropy_eq_negMulLog_sum]
  rw [Complex.re_sum]
  simp_rw [Complex.ofReal_re]

/-- Von Neumann entropy is non-negative. -/
theorem vonNeumannEntropy_nonneg (ρ : DensityMatrix n) :
    0 ≤ S(ρ) := by
  rw [vonNeumannEntropy_eq_negMulLog_sum]
  apply Finset.sum_nonneg
  intro i _
  exact Real.negMulLog_nonneg (ρ.eigenvalues_nonneg i) (ρ.eigenvalue_le_one i)

/-- Von Neumann entropy is at most `log d`, `d = Fintype.card n`; the bound is attained exactly at
the maximally mixed state (`vonNeumannEntropy_eq_log_card_iff`). This follows from the Gibbs
inequality `x log (x / y) ≥ x - y` (`mul_log_div_ge_sub'`) against the uniform weights `1 / d`. -/
theorem vonNeumannEntropy_le_log_dim (ρ : DensityMatrix n) :
    S(ρ) ≤ Real.log (Fintype.card n) := by
  have := ρ.nonempty
  rw [vonNeumannEntropy_eq_negMulLog_sum]
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

omit [DecidableEq n] in
/-- The entropy deficit `log d - S(ρ)`, `d = Fintype.card n`, as a sum of `klFun` terms in the
eigenvalues: `log d - S(ρ) = (1 / d) ∑ᵢ klFun (d λᵢ)`. -/
lemma log_card_sub_vonNeumannEntropy [DecidableEq n] (ρ : DensityMatrix n) :
    Real.log (Fintype.card n) - S(ρ) = ∑ i, (Fintype.card n : ℝ)⁻¹ *
      InformationTheory.klFun (Fintype.card n * ρ.isHermitian.eigenvalues i) := by
  have := ρ.nonempty
  have hd : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  rw [vonNeumannEntropy_eq_negMulLog_sum]
  have key : ∀ i, (Fintype.card n : ℝ)⁻¹ *
      InformationTheory.klFun (Fintype.card n * ρ.isHermitian.eigenvalues i) =
      Real.log (Fintype.card n) * ρ.isHermitian.eigenvalues i +
        Real.negMulLog (ρ.isHermitian.eigenvalues i) * (-1) +
        ((Fintype.card n : ℝ)⁻¹ - ρ.isHermitian.eigenvalues i) := by
    intro i
    rcases (ρ.eigenvalues_nonneg i).eq_or_lt with h0 | hpos
    · rw [← h0]; simp [InformationTheory.klFun]
    · rw [InformationTheory.klFun, Real.negMulLog,
        Real.log_mul hd.ne' hpos.ne']
      field_simp
      ring
  simp_rw [key]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ρ.sum_eigenvalues,
    ← Finset.sum_mul, Finset.sum_sub_distrib, ρ.sum_eigenvalues, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hd.ne']
  ring

/-- The **maximally mixed state** `I / d` attains the maximal entropy: `S(I / d) = log d`. -/
theorem vonNeumannEntropy_maximallyMixed [Nonempty n] :
    S(DensityMatrix.maximallyMixed (n := n)) = Real.log (Fintype.card n) := by
  have hd : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hπ : (DensityMatrix.maximallyMixed (n := n)).toMatrix =
      algebraMap ℝ (Matrix n n ℂ) (Fintype.card n : ℝ)⁻¹ := by
    rw [DensityMatrix.maximallyMixed_toMatrix, Algebra.algebraMap_eq_smul_one,
      ← Complex.coe_smul]
    push_cast
    rfl
  unfold vonNeumannEntropy DensityMatrix.log
  change -(Tr (DensityMatrix.maximallyMixed.toMatrix *
    cfc Real.log (DensityMatrix.maximallyMixed (n := n)).toMatrix)).re = _
  rw [hπ, cfc_algebraMap, ← map_mul, Algebra.algebraMap_eq_smul_one, Matrix.trace_smul,
    Matrix.trace_one, Real.log_inv]
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero]
  field_simp

/-- **Uniqueness of the maximum**: `S(ρ) = log d` exactly when `ρ` is the maximally mixed state
`I / d`. -/
theorem vonNeumannEntropy_eq_log_card_iff [Nonempty n] (ρ : DensityMatrix n) :
    S(ρ) = Real.log (Fintype.card n) ↔ ρ = DensityMatrix.maximallyMixed := by
  refine ⟨fun h => ?_, fun h => h ▸ vonNeumannEntropy_maximallyMixed⟩
  have hd : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have h0 := log_card_sub_vonNeumannEntropy ρ
  rw [h, sub_self, eq_comm, Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg
    (inv_nonneg.2 hd.le) (InformationTheory.klFun_nonneg
      (mul_nonneg hd.le (ρ.eigenvalues_nonneg i)))] at h0
  have hev : ∀ i, ρ.isHermitian.eigenvalues i = (Fintype.card n : ℝ)⁻¹ := by
    intro i
    have hi := h0 i (Finset.mem_univ _)
    rw [mul_eq_zero, InformationTheory.klFun_eq_zero_iff
      (mul_nonneg hd.le (ρ.eigenvalues_nonneg i))] at hi
    rcases hi with hi | hi
    · exact absurd hi (inv_ne_zero hd.ne')
    · exact eq_inv_of_mul_eq_one_right hi
  apply DensityMatrix.ext
  rw [spectral_expand _ ρ.isHermitian, DensityMatrix.maximallyMixed_toMatrix]
  simp_rw [hev]
  rw [show (diagonal fun _ : n => (((Fintype.card n : ℝ)⁻¹ : ℝ) : ℂ)) =
      ((Fintype.card n : ℂ)⁻¹) • (1 : Matrix n n ℂ) by
    ext i j; by_cases hij : i = j <;> simp [hij]]
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, UUH_eq_one]

/-- For PosSemidef ρ: Re(Tr (ρ^s)) = ∑ i, eigenvalue_i ^ s.
This follows from the spectral theorem: ρ^s = U diag(λᵢ^s) U†,
and trace cyclicity Tr (U D U†) = Tr (D) = ∑ Dᵢᵢ. -/
lemma re_trace_rpow_eq_sum_rpow (ρ : Matrix n n ℂ) (hρ : ρ.PosSemidef) (s : ℝ) :
    (Tr (ρ ^ s)).re = ∑ i, hρ.1.eigenvalues i ^ s := by
  have h0 : (0 : Matrix n n ℂ) ≤ ρ := by rw [Matrix.le_iff, sub_zero]; exact hρ
  rw [CFC.rpow_eq_cfc_real (a := ρ) (ha := h0), trace_cfc hρ.1]
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
lemma re_trace_rpow_concave (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    p * (Tr (A ^ s)).re + (1 - p) * (Tr (B ^ s)).re ≤ (Tr ((p • A + (1 - p) • B) ^ s)).re := by
  have hpsd_mix : (p • A + (1 - p) • B).PosSemidef :=
    (hA.real_smul hp).add (hB.real_smul (by linarith))
  have hlowner := rpow_isLownerConcave hs0 hs1 n A B hA hB p hp hp1 hpsd_mix.1
  simp only [] at hlowner
  have hA0 : (0 : Matrix n n ℂ) ≤ A := by rw [Matrix.le_iff, sub_zero]; exact hA
  have hB0 : (0 : Matrix n n ℂ) ≤ B := by rw [Matrix.le_iff, sub_zero]; exact hB
  have hM0 : (0 : Matrix n n ℂ) ≤ p • A + (1 - p) • B := by
    rw [Matrix.le_iff, sub_zero]; exact hpsd_mix
  have eA : cfc (fun x : ℝ => -(x ^ s)) A = -(A ^ s) := by
    rw [cfc_neg, ← CFC.rpow_eq_cfc_real (a := A) (ha := hA0)]
  have eB : cfc (fun x : ℝ => -(x ^ s)) B = -(B ^ s) := by
    rw [cfc_neg, ← CFC.rpow_eq_cfc_real (a := B) (ha := hB0)]
  have eM : cfc (fun x : ℝ => -(x ^ s)) (p • A + (1 - p) • B) =
      -((p • A + (1 - p) • B) ^ s) := by
    rw [cfc_neg, ← CFC.rpow_eq_cfc_real (a := p • A + (1 - p) • B) (ha := hM0)]
  rw [eA, eB, eM] at hlowner
  have hlowner' : p • A ^ s + (1 - p) • B ^ s ≤ (p • A + (1 - p) • B) ^ s := by
    have heq : p • -A ^ s + (1 - p) • -B ^ s = -(p • A ^ s + (1 - p) • B ^ s) := by
      have h1 : p • -A ^ s = -(p • A ^ s) := smul_neg p (A ^ s)
      have h2 : (1 - p) • -B ^ s = -((1 - p) • B ^ s) := smul_neg (1 - p) (B ^ s)
      rw [h1, h2, ← neg_add]
    rw [heq] at hlowner
    rwa [neg_le_neg_iff] at hlowner
  rw [Matrix.le_iff] at hlowner'
  have htrace := (Complex.nonneg_iff.mp hlowner'.trace_nonneg).1
  have htr1 : Tr (p • A ^ s) = (p : ℝ) • Tr (A ^ s) := Matrix.trace_smul (p : ℝ) (A ^ s)
  have htr2 : Tr ((1 - p) • B ^ s) = (1 - p : ℝ) • Tr (B ^ s) :=
    Matrix.trace_smul (1 - p : ℝ) (B ^ s)
  rw [Matrix.trace_sub, Matrix.trace_add, htr1, htr2] at htrace
  simp only [Complex.sub_re, Complex.add_re, Complex.real_smul, Complex.mul_re,
             Complex.ofReal_re, Complex.ofReal_im] at htrace
  linarith

/-- **Von Neumann entropy is concave**, two-point form:
`S(p ρ₁ + (1 - p) ρ₂) ≥ p S(ρ₁) + (1 - p) S(ρ₂)` for `0 ≤ p ≤ 1`. The finite form
`S(Σᵢ wᵢ ρᵢ) ≥ Σᵢ wᵢ S(ρᵢ)` is `Matrix.vonNeumannEntropy_concave_sum`.

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
    exact sub_nonneg.mpr (re_trace_rpow_concave ρ₁.toMatrix ρ₂.toMatrix hpsd₁ hpsd₂ p hp hp1 s hs.1 hs.2)
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
    exact re_trace_rpow_eq_sum_rpow _ hpsd_mix s
  have hderiv₁ : HasDerivAt (fun (s : ℝ) => (ρ₁.toMatrix ^ s).trace.re)
      (∑ i, ρ₁.isHermitian.eigenvalues i * Real.log (ρ₁.isHermitian.eigenvalues i)) 1 := by
    convert hasDerivAt_sum_rpow hpsd₁.1.eigenvalues ρ₁.eigenvalues_nonneg using 1
    funext s
    exact re_trace_rpow_eq_sum_rpow _ hpsd₁ s
  have hderiv₂ : HasDerivAt (fun (s : ℝ) => (ρ₂.toMatrix ^ s).trace.re)
      (∑ i, ρ₂.isHermitian.eigenvalues i * Real.log (ρ₂.isHermitian.eigenvalues i)) 1 := by
    convert hasDerivAt_sum_rpow hpsd₂.1.eigenvalues ρ₂.eigenvalues_nonneg using 1
    funext s
    exact re_trace_rpow_eq_sum_rpow _ hpsd₂ s
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
    rw [vonNeumannEntropy_eq_negMulLog_sum, ← Finset.sum_neg_distrib]
    congr 1
    ext i
    simp only [Real.negMulLog]
    ring
  have h₁_eq : ∑ i, ρ₁.isHermitian.eigenvalues i * Real.log (ρ₁.isHermitian.eigenvalues i) =
      -vonNeumannEntropy ρ₁ := by
    rw [vonNeumannEntropy_eq_negMulLog_sum, ← Finset.sum_neg_distrib]
    congr 1
    ext i
    simp only [Real.negMulLog]
    ring
  have h₂_eq : ∑ i, ρ₂.isHermitian.eigenvalues i * Real.log (ρ₂.isHermitian.eigenvalues i) =
      -vonNeumannEntropy ρ₂ := by
    rw [vonNeumannEntropy_eq_negMulLog_sum, ← Finset.sum_neg_distrib]
    congr 1
    ext i
    simp only [Real.negMulLog]
    ring
  rw [hmix_eq, h₁_eq, h₂_eq] at hderiv_g_nonpos
  linarith

/-- The entropy functional `A ↦ -Re Tr (A log A)` is concave on the convex set of density
matrices; this is `Matrix.vonNeumannEntropy_concave` read on the underlying matrices. -/
private lemma concaveOn_vonNeumannEntropy :
    ConcaveOn ℝ {A : Matrix n n ℂ | A.PosSemidef ∧ Tr A = 1}
      (fun A => -(Tr (A * cfc Real.log A)).re) := by
  refine ⟨fun A hA B hB a b ha hb hab => ?_, fun A hA B hB a b ha hb hab => ?_⟩
  all_goals
    obtain rfl : b = 1 - a := by linarith
  · exact ⟨(DensityMatrix.mix ⟨A, hA.1, hA.2⟩ ⟨B, hB.1, hB.2⟩ a ha (by linarith)).posSemidef,
      (DensityMatrix.mix ⟨A, hA.1, hA.2⟩ ⟨B, hB.1, hB.2⟩ a ha (by linarith)).trace_eq_one⟩
  · exact vonNeumannEntropy_concave ⟨A, hA.1, hA.2⟩ ⟨B, hB.1, hB.2⟩ a ha (by linarith)

/-- **Von Neumann entropy is concave**, finite form: for density matrices `ρᵢ` and weights
`wᵢ ≥ 0` with `Σᵢ wᵢ = 1`, the mixture `σ = Σᵢ wᵢ ρᵢ` satisfies `Σᵢ wᵢ S(ρᵢ) ≤ S(σ)`. -/
theorem vonNeumannEntropy_concave_sum {ι : Type*} (s : Finset ι) (ρ : ι → DensityMatrix n)
    (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) (hw1 : ∑ i ∈ s, w i = 1) (σ : DensityMatrix n)
    (hσ : σ.toMatrix = ∑ i ∈ s, w i • (ρ i).toMatrix) :
    ∑ i ∈ s, w i * S(ρ i) ≤ S(σ) := by
  have h := concaveOn_vonNeumannEntropy.le_map_sum hw hw1 (p := fun i => (ρ i).toMatrix)
    (fun i _ => ⟨(ρ i).posSemidef, (ρ i).trace_eq_one⟩)
  change ∑ i ∈ s, w i * S(ρ i) ≤ -(Tr (σ.toMatrix * cfc Real.log σ.toMatrix)).re
  rw [hσ]
  exact h

/-! ### Isomorphism invariance

For a `*-`algebra equivalence `φ : Matrix m m ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ`, von Neumann entropy is
invariant: `S(ρ.map φ) = S(ρ)`. Every such `φ` is conjugation by a unitary (Skolem–Noether), so in
quantum-information terms this is the **unitary invariance of von Neumann entropy**. Such a `φ`
preserves the trace (`Matrix.trace_map`). -/

section IsomorphismInvariance

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- **Von Neumann entropy is invariant under `*-`algebra equivalence**,
for every density matrix (no positive-definiteness required). -/
lemma vonNeumannEntropy_map_starAlgEquiv
    (ρ : DensityMatrix m)
    (φ : Matrix m m ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ) :
    S(ρ.map φ) = S(ρ) := by
  unfold vonNeumannEntropy
  have h_log_eq : cfc Real.log (ρ.map φ).toMatrix =
      φ (cfc Real.log ρ.toMatrix) := by
    change cfc Real.log (φ ρ.toMatrix) = _
    exact cfc_log_map_starAlgEquiv ρ.isHermitian φ
  have h_tr : Tr ((ρ.map φ).toMatrix *
        cfc Real.log (ρ.map φ).toMatrix) =
      Tr (ρ.toMatrix * cfc Real.log ρ.toMatrix) := by
    rw [h_log_eq, DensityMatrix.map_toMatrix, ← map_mul, Matrix.trace_map]
  change -(Tr ((ρ.map φ).toMatrix *
      cfc Real.log (ρ.map φ).toMatrix)).re =
    -(Tr (ρ.toMatrix * cfc Real.log ρ.toMatrix)).re
  rw [h_tr]

/-- **`vonNeumannEntropy` is invariant under reindex**: `S(ρ.mapEquiv e) = S(ρ)` for every
density matrix `ρ` and equivalence `e`. Specialisation of
`vonNeumannEntropy_map_starAlgEquiv` to `Matrix.reindexStarAlgEquiv`. -/
lemma vonNeumannEntropy_mapEquiv (ρ : DensityMatrix m) (e : n ≃ m) :
    S(ρ.mapEquiv e) = S(ρ) :=
  vonNeumannEntropy_map_starAlgEquiv ρ _

end IsomorphismInvariance

end Matrix
