import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Data.Real.StarOrdered

namespace UnitalCStarAlgebra

variable {B : Type*} [CStarAlgebra B]

/-- The norm of a character on a C*-algebra equals 1.
A character φ satisfies φ(1) = 1, which gives ‖φ‖ ≥ 1, and φ(x) ∈ spectrum(x) gives ‖φ‖ ≤ 1. -/
lemma norm_character_eq_one [Nontrivial B]
    (φ : WeakDual.characterSpace ℂ B) : ‖WeakDual.toStrongDual φ.val‖ = 1 := by
  apply le_antisymm
  · -- ‖φ‖ ≤ 1: φ x ∈ spectrum x implies |φ x| ≤ spectralRadius x ≤ ‖x‖
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    have h_mem : φ x ∈ spectrum ℂ x := WeakDual.CharacterSpace.apply_mem_spectrum φ x
    have h_le : (‖φ x‖₊ : ENNReal) ≤ ‖x‖₊ :=
      (le_iSup₂_of_le (φ x) h_mem le_rfl).trans (spectrum.spectralRadius_le_nnnorm x)
    simp only [one_mul]; exact mod_cast h_le
  · -- ‖φ‖ ≥ 1: since φ(1) = 1 and ‖1‖ = 1
    have h_le := (WeakDual.toStrongDual φ.val).le_opNorm 1
    simp only [WeakDual.toStrongDual_apply, norm_one, mul_one] at h_le
    have h_one : (φ : WeakDual ℂ B) 1 = 1 := map_one φ
    rw [h_one, norm_one] at h_le
    exact h_le

lemma norm_sq_add_imaginary_unit_of_selfAdjoint [Nontrivial B] (a : B) (ha : IsSelfAdjoint a) (t : ℝ) :
    ‖a + (Complex.I * t) • (1 : B)‖^2 = ‖a‖^2 + t^2 := by
  set x := a + (Complex.I * t) • (1 : B) with hx_def
  -- Step 1: Compute star x * x = a² + t² • 1
  have hx_star_mul_self : star x * x = a ^ 2 + (t ^ 2 : ℂ) • (1 : B) := by
    simp only [hx_def, star_add, star_smul, star_one, ha.star_eq, star_mul,
               Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
    rw [add_mul, mul_add, mul_add]
    simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, one_mul, mul_one, sq]
    have h_cross : (Complex.I * t) • a + (↑t * -Complex.I) • a = 0 := by
      rw [← add_smul, show Complex.I * t + ↑t * -Complex.I = 0 by ring, zero_smul]
    have h_scalar : (Complex.I * t) • ((↑t * -Complex.I) • (1 : B)) = (t * t : ℂ) • 1 := by
      rw [smul_smul]; congr 1; ring_nf; rw [Complex.I_sq]; ring
    calc a * a + (Complex.I * ↑t) • a + ((↑t * -Complex.I) • a + (Complex.I * ↑t) • (↑t * -Complex.I) • 1)
        = a * a + ((Complex.I * ↑t) • a + (↑t * -Complex.I) • a) + (Complex.I * ↑t) • (↑t * -Complex.I) • 1 := by abel
      _ = a * a + 0 + (t * t : ℂ) • 1 := by rw [h_cross, h_scalar]
      _ = a * a + (t * t : ℂ) • 1 := by rw [add_zero]
  -- Step 2: Apply C*-identity: ‖x‖² = ‖star x * x‖
  have h_norm_sq : ‖x‖ ^ 2 = ‖star x * x‖ := by rw [sq, ← CStarRing.norm_star_mul_self]
  rw [hx_star_mul_self] at h_norm_sq
  -- Step 3: Compute ‖a² + t²•1‖ using spectral radius
  set b := a ^ 2 + (t ^ 2 : ℂ) • (1 : B) with hb_def
  have hb_sa : IsSelfAdjoint b := IsSelfAdjoint.add (IsSelfAdjoint.pow ha 2)
    (IsSelfAdjoint.smul (by rw [isSelfAdjoint_iff, Complex.star_def, Complex.conj_eq_iff_im]; norm_cast)
      (IsSelfAdjoint.one (R := B)))
  have hb_norm : ‖b‖ = (spectralRadius ℂ b).toReal := by
    rw [IsSelfAdjoint.spectralRadius_eq_nnnorm hb_sa]; simp
  -- Spectrum of b via spectral mapping theorem
  set p : Polynomial ℂ := Polynomial.X ^ 2 + Polynomial.C (t ^ 2 : ℂ) with hp_def
  have h_spec : spectrum ℂ b = (fun z => z ^ 2 + (t : ℂ) ^ 2) '' spectrum ℂ a := by
    have hb_poly : b = Polynomial.aeval a p := by
      simp only [hp_def, hb_def, map_add, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]
      rw [Polynomial.aeval_X_pow]
    rw [hb_poly, spectrum.map_polynomial_aeval]; simp [hp_def]
  -- Compute spectral radius
  set ρa := spectralRadius ℂ a with hρa_def
  have hρa_ne_top : ρa ≠ ⊤ := ne_of_lt (lt_of_le_of_lt (spectrum.spectralRadius_le_nnnorm a) ENNReal.coe_lt_top)
  set R := ρa.toReal with hR_def
  have hρa_ofReal : ENNReal.ofReal R = ρa := ENNReal.ofReal_toReal hρa_ne_top
  have hR_nonneg : 0 ≤ R := ENNReal.toReal_nonneg
  -- Helper: for w ∈ spectrum(a), compute ‖w² + t²‖
  have norm_image (w : ℂ) (hw : w ∈ spectrum ℂ a) : ‖w ^ 2 + (t : ℂ) ^ 2‖ = ‖w‖ ^ 2 + t ^ 2 := by
    have hw_real : w = (w.re : ℂ) := ha.mem_spectrum_eq_re hw
    have hw_sq : ‖w‖ ^ 2 = w.re ^ 2 := by
      rw [hw_real, Complex.norm_real, Real.norm_eq_abs, sq_abs, Complex.ofReal_re]
    have h_val : w ^ 2 + (t : ℂ) ^ 2 = (w.re ^ 2 + t ^ 2 : ℝ) := by rw [hw_real]; simp [sq]
    rw [h_val, Complex.norm_of_nonneg (by positivity), hw_sq]
  -- Upper bound: spectralRadius b ≤ R² + t²
  have h_le : spectralRadius ℂ b ≤ ENNReal.ofReal (R ^ 2 + t ^ 2) := by
    refine iSup₂_le fun z hz => ?_
    obtain ⟨w, hw, rfl⟩ : z ∈ (fun w => w ^ 2 + (t : ℂ) ^ 2) '' spectrum ℂ a := by simpa [h_spec] using hz
    have hw_norm_le : ‖w‖ ≤ R := by
      have h1 : (‖w‖₊ : ENNReal) ≤ ρa := le_iSup₂_of_le w hw le_rfl
      have h2 : (‖w‖₊ : ENNReal) ≤ ENNReal.ofReal R := by simpa [hρa_ofReal] using h1
      rw [ENNReal.le_ofReal_iff_toReal_le ENNReal.coe_ne_top hR_nonneg] at h2
      simpa using h2
    have h_sq_le : ‖w‖ ^ 2 ≤ R ^ 2 := sq_le_sq' (by linarith [norm_nonneg w]) hw_norm_le
    calc (‖w ^ 2 + (t : ℂ) ^ 2‖₊ : ENNReal) = ENNReal.ofReal (‖w‖ ^ 2 + t ^ 2) := by
          rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, norm_image w hw]
      _ ≤ ENNReal.ofReal (R ^ 2 + t ^ 2) := ENNReal.ofReal_le_ofReal (add_le_add h_sq_le le_rfl)
  -- Lower bound: R² + t² ≤ spectralRadius b
  have h_ge : ENNReal.ofReal (R ^ 2 + t ^ 2) ≤ spectralRadius ℂ b := by
    obtain ⟨w, hw, hw_eq⟩ := spectrum.exists_nnnorm_eq_spectralRadius (a := a)
    have hw_norm : ‖w‖ = R := by
      have h1 : (‖w‖₊ : ENNReal) = ENNReal.ofReal R := by simpa [hρa_ofReal] using hw_eq
      simpa [ENNReal.toReal_ofReal hR_nonneg] using congrArg ENNReal.toReal h1
    have hz_mem : w ^ 2 + (t : ℂ) ^ 2 ∈ spectrum ℂ b := by simpa [h_spec] using ⟨w, hw, rfl⟩
    calc ENNReal.ofReal (R ^ 2 + t ^ 2) = ENNReal.ofReal (‖w‖ ^ 2 + t ^ 2) := by rw [hw_norm]
      _ = (‖w ^ 2 + (t : ℂ) ^ 2‖₊ : ENNReal) := by rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, norm_image w hw]
      _ ≤ spectralRadius ℂ b := le_iSup₂_of_le _ hz_mem le_rfl
  -- Combine bounds
  have h_rad : spectralRadius ℂ b = ρa ^ 2 + ENNReal.ofReal (t ^ 2) := by
    have h_eq : spectralRadius ℂ b = ENNReal.ofReal (R ^ 2 + t ^ 2) := le_antisymm h_le h_ge
    calc spectralRadius ℂ b = ENNReal.ofReal (R ^ 2 + t ^ 2) := h_eq
      _ = ENNReal.ofReal (R ^ 2) + ENNReal.ofReal (t ^ 2) := ENNReal.ofReal_add (sq_nonneg R) (sq_nonneg t)
      _ = ρa ^ 2 + ENNReal.ofReal (t ^ 2) := by rw [ENNReal.ofReal_pow hR_nonneg, hρa_ofReal]
  -- Final calculation
  rw [h_norm_sq, hb_norm, h_rad, ENNReal.toReal_add (by simp [hρa_ne_top]) (by simp),
      ENNReal.toReal_pow, IsSelfAdjoint.toReal_spectralRadius_complex_eq_norm ha,
      ENNReal.toReal_ofReal (sq_nonneg t)]


end UnitalCStarAlgebra
