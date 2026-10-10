/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Keisuke Suzuki
-/
module

public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Topology.Algebra.Module.TopDualPairing
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Bochner's theorem

A function `φ : G → ℂ` on an additive group is *positive definite* if all the matrices
`(φ (xᵢ - xⱼ))ᵢⱼ` are positive semidefinite. **Bochner's theorem** identifies the continuous
positive definite functions on a finite-dimensional real vector space with the Fourier transforms
of finite measures on its dual: if `L : W →ₗ[ℝ] V →ₗ[ℝ] ℝ` is a continuous perfect pairing of
finite-dimensional real topological vector spaces, a continuous function `φ : V → ℂ` is positive
definite if and only if there is a finite measure `μ` on `W` with
`φ v = ∫ w, exp (i L w v) ∂μ` for all `v`, and this measure is unique. No normalisation is
imposed: the total mass of `μ` is `φ 0`.

## Main definitions

* `IsPositiveDefinite φ`: the function `φ : G → ℂ` is positive definite, i.e. the matrix
  `Matrix.of fun i j ↦ φ (x i - x j)` is `Matrix.PosSemidef` for every `x : Fin n → G`.

## Main statements

* `IsPositiveDefinite.apply_neg`, `IsPositiveDefinite.apply_zero_nonneg`,
  `IsPositiveDefinite.norm_apply_le`: `φ (-x) = conj (φ x)`, `0 ≤ φ 0` and `‖φ x‖ ≤ (φ 0).re`.
* `IsPositiveDefinite.mul`: Schur product theorem for positive definite functions.
* `isPositiveDefinite_integral_cexp`: the Fourier transform of a finite measure is positive
  definite; special cases `isPositiveDefinite_charFun` and `isPositiveDefinite_charFunDual`.
* `MeasureTheory.Measure.ext_of_integral_cexp_eq`: a finite measure on `W` is determined by its
  Fourier transform with respect to a continuous perfect pairing.
* `IsPositiveDefinite.existsUnique_finiteMeasure`, `isPositiveDefinite_iff_exists_finiteMeasure`:
  **Bochner's theorem** for a continuous perfect pairing `L`.
* `IsPositiveDefinite.existsUnique_charFun_eq`, `isPositiveDefinite_iff_exists_charFun_eq`: the
  case `L = innerₗ E` of a finite-dimensional inner product space, stated with `charFun`.
* `IsPositiveDefinite.existsUnique_finiteMeasure_strongDual`,
  `isPositiveDefinite_iff_exists_finiteMeasure_strongDual`: the case of the measure on the dual
  space `StrongDual ℝ V` (`L = topDualPairing ℝ V`), i.e. `φ v = ∫ p, exp (i p v) ∂μ`.
* `LinearMap.exists_euclidean_of_isContPerfPair`: a continuous perfect pairing of
  finite-dimensional real vector spaces is the inner product of a Euclidean space up to continuous
  linear equivalences; `LinearMap.firstCountableTopology_of_isContPerfPair`,
  `LinearMap.measurable_flip_apply_of_isContPerfPair` are consequences used by Fourier transforms
  along `L`.

## Proof outline

The existence part is proved on a finite-dimensional real inner product space `E` and then
transported, once, to a general continuous perfect pairing by continuous linear equivalences with
a Euclidean space.

1. *Fejér's argument.* If `ψ` is continuous, integrable and positive definite, then `0 ≤ ∫ ψ`:
   the averages `vol(B_R)⁻¹ ∫_{B_R} ∫_{B_R} ψ (x - y) dy dx` are nonnegative (they are limits of
   the finite sums in the definition, by approximating the identity with simple functions) and
   converge to `∫ ψ`. Applied to `ψ` times a character this gives `0 ≤ 𝓕 ψ`.
2. Such a `ψ` has an integrable Fourier transform: by Parseval's identity the integrals of `𝓕 ψ`
   against the Gaussians `exp (-t ‖w‖²)` are bounded by `ψ 0`; conclude by Fatou's lemma.
3. By Fourier inversion, `ψ` is then the characteristic function of the image under `w ↦ 2π w` of
   the finite measure with density `𝓕 ψ`.
4. A general continuous positive definite `φ` with `φ 0 = 1` is approximated by the Gaussian
   regularisations `φ x * exp (-t ‖x‖²)`, positive definite by the Schur product theorem since
   Gaussians are characteristic functions of Gaussian measures. Their measures are tight by Lévy's
   continuity theorem (`isTightMeasureSet_of_tendsto_charFun`), so by Prokhorov's theorem a
   subsequence converges weakly, and its limit has characteristic function `φ`. The case of a
   general value `φ 0 ≥ 0` follows by scaling.
5. Uniqueness follows from `MeasureTheory.Measure.ext_of_charFun`.

## References

* S. Bochner, *Monotone Funktionen, Stieltjessche Integrale und harmonische Analyse*,
  Math. Ann. 108 (1933), 378–410.
* W. Rudin, *Fourier Analysis on Groups*, Interscience (1962), Theorem 1.4.3.
* M. R. Douglas, *Bochner's and Minlos' theorems in Lean 4*,
  <https://github.com/mrdouglasny/bochner>.

## TODO

* Bochner's theorem on a locally compact abelian group `G` (Rudin, *Fourier Analysis on Groups*,
  Theorem 1.4.3, the form cited above): a continuous positive definite function on `G` is the
  Fourier transform of a unique finite positive measure on the Pontryagin dual `Ĝ`. Only the case
  of a finite-dimensional real vector space `V`, with dual `Ĝ` realised as `W` through a
  continuous perfect pairing, is proved here; the general case needs Haar measure on `Ĝ` and
  Fourier analysis on LCA groups, which Mathlib does not have yet.

## Implementation notes

Ported from `mrdouglasny/bochner` (Apache-2.0) and modified: positive definiteness is defined
through `Matrix.PosSemidef`; the normalisation `φ 0 = 1` is dropped, so the statements are about
finite measures of total mass `φ 0`; the theorem is stated for a continuous perfect pairing
(`LinearMap.IsContPerfPair`), with the inner product and dual space versions as corollaries; the
hand-made tightness argument is replaced by Mathlib's Lévy continuity theorem; positive
definiteness of Gaussians comes from `ProbabilityTheory.stdGaussian`; the measure of an
integrable positive definite function is built from its own Fourier transform by a `2π` push
forward; the Fejér argument works with an arbitrary finite measure and with `ComplexOrder`, which
also yields that `𝓕 ψ` is real; the proofs were restructured and the auxiliary lemmas renamed and
made private.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology
open scoped ComplexConjugate ComplexOrder FourierTransform RealInnerProductSpace Real

/-! ### Positive definite functions -/

section PositiveDefinite

variable {G H : Type*} [AddGroup G] [AddGroup H] {φ ψ : G → ℂ}

/-- A function `φ : G → ℂ` on an additive group is *positive definite* if for all finitely many
points `x₁, …, xₙ` of `G` the matrix `(φ (xᵢ - xⱼ))ᵢⱼ` is positive semidefinite, i.e. it is
Hermitian and `∑ i, ∑ j, conj (cᵢ) * cⱼ * φ (xᵢ - xⱼ)` is a nonnegative real number for every
`c : Fin n → ℂ` (see `isPositiveDefinite_iff`). -/
def IsPositiveDefinite (φ : G → ℂ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → G), (Matrix.of fun i j ↦ φ (x i - x j)).PosSemidef

namespace IsPositiveDefinite

/-- The kernel matrix `(φ (xᵢ - xⱼ))ᵢⱼ` of a positive definite function on a family of points
indexed by any finite type is positive semidefinite. -/
lemma posSemidef (hφ : IsPositiveDefinite φ) {ι : Type*} [Finite ι] (x : ι → G) :
    (Matrix.of fun i j ↦ φ (x i - x j)).PosSemidef := by
  have := Fintype.ofFinite ι
  rw [← Matrix.posSemidef_submatrix_equiv (Fintype.equivFin ι).symm]
  exact hφ _ (x ∘ (Fintype.equivFin ι).symm)

/-- The quadratic form `∑ i, ∑ j, conj (cᵢ) * cⱼ * φ (xᵢ - xⱼ)` of a positive definite function
is a nonnegative real number. -/
lemma sum_nonneg (hφ : IsPositiveDefinite φ) {ι : Type*} (s : Finset ι) (x : ι → G)
    (c : ι → ℂ) : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, conj (c i) * c j * φ (x i - x j) := by
  have := (hφ.posSemidef fun i : s ↦ x i).dotProduct_mulVec_nonneg fun i ↦ c i
  rw [← Finset.sum_coe_sort s]
  convert this using 1
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.sum_coe_sort s]
  exact Finset.sum_congr rfl fun j _ ↦ by simp only [Complex.star_def]; ring

/-- A positive definite function is Hermitian: `φ (-x) = conj (φ x)`. -/
lemma apply_neg (hφ : IsPositiveDefinite φ) (x : G) : φ (-x) = conj (φ x) := by
  simpa using (congr_fun₂ (hφ 2 ![0, x]).isHermitian 0 1).symm

/-- The value at zero of a positive definite function is a nonnegative real number. -/
lemma apply_zero_nonneg (hφ : IsPositiveDefinite φ) : 0 ≤ φ 0 := by
  simpa using (hφ 1 fun _ ↦ 0).diag_nonneg (i := 0)

/-- The real part of the value at zero of a positive definite function is nonnegative. -/
lemma re_apply_zero_nonneg (hφ : IsPositiveDefinite φ) : 0 ≤ (φ 0).re :=
  (Complex.nonneg_iff.1 hφ.apply_zero_nonneg).1

/-- The value at zero of a positive definite function is real. -/
lemma im_apply_zero (hφ : IsPositiveDefinite φ) : (φ 0).im = 0 :=
  (Complex.nonneg_iff.1 hφ.apply_zero_nonneg).2.symm

/-- The value at zero of a positive definite function is the real number `(φ 0).re`. -/
lemma ofReal_re_apply_zero (hφ : IsPositiveDefinite φ) : ((φ 0).re : ℂ) = φ 0 :=
  Complex.ext (by simp) (by simp [hφ.im_apply_zero])

/-- A positive definite function is bounded by its value at zero. -/
lemma norm_apply_le (hφ : IsPositiveDefinite φ) (x : G) : ‖φ x‖ ≤ (φ 0).re := by
  have h := (hφ 2 ![0, x]).det_nonneg
  simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    sub_self, zero_sub, sub_zero, hφ.apply_neg, conj_mul'] at h
  rw [← hφ.ofReal_re_apply_zero] at h
  have h' : 0 ≤ (φ 0).re * (φ 0).re - ‖φ x‖ ^ 2 := by exact_mod_cast h
  nlinarith [norm_nonneg (φ x), hφ.re_apply_zero_nonneg]

/-- Precomposing a positive definite function with an additive homomorphism gives a positive
definite function. -/
lemma comp_addMonoidHom (hφ : IsPositiveDefinite φ) (f : H →+ G) :
    IsPositiveDefinite (φ ∘ f) := fun n x ↦ by
  simpa [map_sub] using hφ n (f ∘ x)

/-- **Schur product theorem** for positive definite functions: the pointwise product of positive
definite functions is positive definite. -/
lemma mul (hφ : IsPositiveDefinite φ) (hψ : IsPositiveDefinite ψ) :
    IsPositiveDefinite (φ * ψ) := fun n x ↦ by
  convert (hφ n x).hadamard (hψ n x) using 1
  ext i j
  simp

/-- A nonnegative real multiple of a positive definite function is positive definite. -/
lemma smul (hφ : IsPositiveDefinite φ) {c : ℝ} (hc : 0 ≤ c) : IsPositiveDefinite (c • φ) :=
  fun n x ↦ by
  convert (hφ n x).smul hc using 1
  ext i j
  simp

end IsPositiveDefinite

/-- A function is positive definite if and only if it is Hermitian and all its quadratic forms
`∑ i, ∑ j, conj (cᵢ) * cⱼ * φ (xᵢ - xⱼ)` are nonnegative real numbers. -/
lemma isPositiveDefinite_iff : IsPositiveDefinite φ ↔ (∀ x, φ (-x) = conj (φ x)) ∧
    ∀ (n : ℕ) (x : Fin n → G) (c : Fin n → ℂ),
      0 ≤ ∑ i, ∑ j, conj (c i) * c j * φ (x i - x j) := by
  refine ⟨fun hφ ↦ ⟨hφ.apply_neg, fun n x c ↦ hφ.sum_nonneg _ x c⟩, fun ⟨hneg, h⟩ n x ↦ ?_⟩
  refine .of_dotProduct_mulVec_nonneg (Matrix.IsHermitian.ext fun i j ↦ ?_) fun c ↦ ?_
  · simp [← hneg]
  · convert h n x c using 1
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, Matrix.of_apply]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by
      simp only [Complex.star_def]; ring

/-- A real character `x ↦ exp (i f x)` is positive definite. -/
lemma isPositiveDefinite_cexp (f : G →+ ℝ) :
    IsPositiveDefinite fun x ↦ cexp (f x * I) := fun n x ↦ by
  convert Matrix.posSemidef_vecMulVec_self_star fun i ↦ cexp (f (x i) * I) using 1
  ext i j
  rw [Matrix.of_apply, Matrix.vecMulVec_apply, Pi.star_apply, Complex.star_def,
    ← Complex.exp_conj, ← Complex.exp_add]
  simp only [map_sub, ofReal_sub, map_mul, conj_ofReal, conj_I]
  congr 1
  ring

/-- The Fourier transform `x ↦ ∫ a, exp (i f a x) ∂μ` of a finite measure `μ` is positive
definite. -/
lemma isPositiveDefinite_integral_cexp {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (f : α → G →+ ℝ) (hf : ∀ x, AEMeasurable (fun a ↦ f a x) μ) :
    IsPositiveDefinite fun x ↦ ∫ a, cexp (f a x * I) ∂μ := by
  have hint (x : G) : Integrable (fun a ↦ cexp (f a x * I)) μ := by
    refine Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun a ↦ ?_)
    simp [Complex.norm_exp_ofReal_mul_I]
  refine isPositiveDefinite_iff.2 ⟨fun x ↦ ?_, fun n x c ↦ ?_⟩
  · rw [← integral_conj]
    congr 1 with a
    rw [← Complex.exp_conj]
    simp
  · calc (0 : ℂ) ≤ ∫ a, ∑ i, ∑ j, conj (c i) * c j * cexp (f a (x i - x j) * I) ∂μ :=
          integral_nonneg fun a ↦ (isPositiveDefinite_cexp (f a)).sum_nonneg _ x c
      _ = _ := by
          rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
            (hint _).const_mul _]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [integral_finsetSum _ fun j _ ↦ (hint _).const_mul _]
          simp_rw [integral_const_mul]

end PositiveDefinite

/-- The characteristic function of a finite measure on a real inner product space is positive
definite. -/
lemma isPositiveDefinite_charFun {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [OpensMeasurableSpace E] (μ : Measure E) [IsFiniteMeasure μ] :
    IsPositiveDefinite (charFun μ) := by
  convert isPositiveDefinite_integral_cexp μ (fun x ↦ (innerₗ E x).toAddMonoidHom)
    fun t ↦ (continuous_id.inner continuous_const).measurable.aemeasurable using 2 with t
  simp [charFun_apply]

/-- The characteristic function `charFunDual μ` of a finite measure on a normed space is positive
definite. -/
lemma isPositiveDefinite_charFunDual {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [OpensMeasurableSpace E] (μ : Measure E) [IsFiniteMeasure μ] :
    IsPositiveDefinite (charFunDual μ) := by
  convert isPositiveDefinite_integral_cexp μ
    (fun x ↦ AddMonoidHom.mk' (fun L : StrongDual ℝ E ↦ L x) fun _ _ ↦ rfl)
    fun L ↦ L.continuous.measurable.aemeasurable using 2 with L
  simp [charFunDual_apply]

/-! ### Integrable positive definite functions have a nonnegative Fourier transform

We follow the classical Fejér-type argument (Rudin, *Fourier analysis on groups*, 1.4.3): for a
continuous integrable positive definite function `ψ`, the averaged double integrals
`vol(B_R)⁻¹ ∫_{B_R} ∫_{B_R} ψ (x - y) dy dx` are nonnegative (they are limits of the finite sums
in the definition of positive definiteness) and converge to `∫ ψ` as `R → ∞`. Applied to `ψ`
multiplied by a character, this shows that `𝓕 ψ ≥ 0`. -/

open Classical in
/-- The integral of `g ∘ s` for a simple function `s` is a finite sum. -/
private lemma integral_comp_simpleFunc {α β : Type*} [MeasurableSpace α] (s : SimpleFunc α β)
    (g : β → ℂ) (μ : Measure α) [IsFiniteMeasure μ] :
    ∫ x, g (s x) ∂μ = ∑ u ∈ s.range, μ.real (s ⁻¹' {u}) • g u := by
  have hpw (x : α) : g (s x) = ∑ u ∈ s.range, (s ⁻¹' {u}).indicator (fun _ ↦ g u) x := by
    simp only [Set.indicator, Set.mem_preimage, Set.mem_singleton_iff]
    simp_rw [eq_comm (a := s x)]
    rw [Finset.sum_ite_eq' s.range (s x) (fun u ↦ g u)]
    simp
  simp_rw [hpw]
  rw [integral_finsetSum _ fun u _ ↦ (integrable_const _).indicator (s.measurableSet_preimage _)]
  congr 1 with u
  rw [integral_indicator (s.measurableSet_preimage _), setIntegral_const]

section Fejer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ψ : E → ℂ}

/-- For a finite measure `μ`, the double integral `∫∫ ψ (x - y) dμ dμ` of a continuous positive
definite function is nonnegative: approximating the identity by simple functions, it is a limit
of the finite sums in the definition of positive definiteness. -/
private lemma integral_integral_sub_nonneg (hψ : IsPositiveDefinite ψ) (hc : Continuous ψ)
    (μ : Measure E) [IsFiniteMeasure μ] : 0 ≤ ∫ x, ∫ y, ψ (x - y) ∂μ ∂μ := by
  have hid : StronglyMeasurable (id : E → E) := stronglyMeasurable_id
  set s := hid.approx
  have hs (x : E) : Tendsto (fun n ↦ s n x) atTop (𝓝 x) := hid.tendsto_approx x
  have h_inner (x : E) : Tendsto (fun n ↦ ∫ y, ψ (s n x - s n y) ∂μ) atTop
      (𝓝 (∫ y, ψ (x - y) ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun _ ↦ (ψ 0).re)
      (fun n ↦ ((s n).map fun v ↦ ψ (s n x - v)).aestronglyMeasurable) (integrable_const _)
      (fun n ↦ ae_of_all _ fun y ↦ hψ.norm_apply_le _)
      (ae_of_all _ fun y ↦ (hc.tendsto _).comp ((hs x).sub (hs y)))
  have h_outer : Tendsto (fun n ↦ ∫ x, ∫ y, ψ (s n x - s n y) ∂μ ∂μ) atTop
      (𝓝 (∫ x, ∫ y, ψ (x - y) ∂μ ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun _ ↦ (ψ 0).re * μ.real Set.univ)
      (fun n ↦ ((s n).map fun u ↦ ∫ y, ψ (u - s n y) ∂μ).aestronglyMeasurable)
      (integrable_const _)
      (fun n ↦ ae_of_all _ fun x ↦ norm_integral_le_of_norm_le_const
        (ae_of_all _ fun y ↦ hψ.norm_apply_le _))
      (ae_of_all _ h_inner)
  refine ge_of_tendsto' h_outer fun n ↦ ?_
  have h_sum : ∫ x, ∫ y, ψ (s n x - s n y) ∂μ ∂μ = ∑ u ∈ (s n).range, ∑ v ∈ (s n).range,
      conj (μ.real (s n ⁻¹' {u}) : ℂ) * (μ.real (s n ⁻¹' {v}) : ℂ) * ψ (u - v) := by
    have h1 (x : E) : ∫ y, ψ (s n x - s n y) ∂μ =
        ∑ v ∈ (s n).range, μ.real (s n ⁻¹' {v}) • ψ (s n x - v) :=
      integral_comp_simpleFunc (s n) (fun v ↦ ψ (s n x - v)) μ
    simp_rw [h1]
    rw [integral_comp_simpleFunc (s n)
      (fun u ↦ ∑ v ∈ (s n).range, μ.real (s n ⁻¹' {v}) • ψ (u - v)) μ]
    simp_rw [Finset.smul_sum, Complex.real_smul, conj_ofReal, mul_assoc]
  rw [h_sum]
  exact hψ.sum_nonneg _ id _

/-- The proportion `vol (B_R ∩ B_R(v)) / vol B_R` of the ball `B_R = closedBall 0 R` that is
covered by its translate by `v`. -/
private noncomputable def overlapRatio (R : ℝ) (v : E) : ℝ :=
  volume.real (Metric.closedBall (0 : E) R ∩ Metric.closedBall v R) /
    volume.real (Metric.closedBall (0 : E) R)

/-- The overlap ratio is nonnegative. -/
private lemma overlapRatio_nonneg (R : ℝ) (v : E) : 0 ≤ overlapRatio R v := by
  unfold overlapRatio; positivity

/-- The overlap ratio is at most one. -/
private lemma overlapRatio_le_one (R : ℝ) (v : E) : overlapRatio R v ≤ 1 :=
  div_le_one_of_le₀ (measureReal_mono Set.inter_subset_left measure_closedBall_lt_top.ne)
    measureReal_nonneg

/-- The overlap ratio is measurable in the translation vector. -/
private lemma measurable_overlapRatio (R : ℝ) : Measurable (overlapRatio R : E → ℝ) := by
  refine Measurable.div_const ?_ _
  let S := {p : E × E | p.2 ∈ Metric.closedBall (0 : E) R ∧ dist p.2 p.1 ≤ R}
  have hS : MeasurableSet S :=
    .inter (measurableSet_closedBall.preimage measurable_snd)
      (isClosed_le (continuous_snd.dist continuous_fst) continuous_const).measurableSet
  have hfib (v : E) : Prod.mk v ⁻¹' S = Metric.closedBall (0 : E) R ∩ Metric.closedBall v R := by
    ext x
    simp [S, dist_comm x v]
  simp_rw [Measure.real, ← hfib]
  exact (measurable_measure_prodMk_left hS).ennreal_toReal

/-- The overlap ratio tends to one as the radius tends to infinity. -/
private lemma tendsto_overlapRatio (v : E) :
    Tendsto (fun R ↦ overlapRatio R v) atTop (𝓝 1) := by
  set d := Module.finrank ℝ E
  have h_lower : Tendsto (fun R : ℝ ↦ ((R - ‖v‖) / R) ^ d) atTop (𝓝 1) := by
    have h0 : Tendsto (fun R : ℝ ↦ ‖v‖ / R) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    have : Tendsto (fun R : ℝ ↦ 1 - ‖v‖ / R) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub h0
    simpa using (this.congr' (by
      filter_upwards [eventually_gt_atTop 0] with R hR
      field_simp)).pow d
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h_lower tendsto_const_nhds ?_
    (.of_forall fun R ↦ overlapRatio_le_one R v)
  filter_upwards [eventually_gt_atTop ‖v‖] with R hR
  have hR0 : 0 < R := (norm_nonneg v).trans_lt hR
  have hball (r : ℝ) (hr : 0 ≤ r) : volume.real (Metric.closedBall (0 : E) r) =
      r ^ d * volume.real (Metric.ball (0 : E) 1) := by
    rw [Measure.real, Measure.addHaar_closedBall volume _ hr, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), Measure.real]
  have hpos : 0 < volume.real (Metric.ball (0 : E) 1) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  have hsub : Metric.closedBall (0 : E) (R - ‖v‖) ⊆
      Metric.closedBall (0 : E) R ∩ Metric.closedBall v R := by
    intro x hx
    simp only [Metric.mem_closedBall, dist_zero_right] at hx
    refine ⟨by simp only [Metric.mem_closedBall, dist_zero_right]; linarith [norm_nonneg v], ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    linarith [norm_sub_le x v]
  calc ((R - ‖v‖) / R) ^ d
      = volume.real (Metric.closedBall (0 : E) (R - ‖v‖)) /
          volume.real (Metric.closedBall (0 : E) R) := by
        rw [hball _ (sub_nonneg.2 hR.le), hball _ hR0.le, div_pow,
          mul_div_mul_right _ _ hpos.ne']
    _ ≤ overlapRatio R v :=
        div_le_div_of_nonneg_right (measureReal_mono hsub
          ((measure_mono Set.inter_subset_left).trans_lt measure_closedBall_lt_top).ne)
          measureReal_nonneg

/-- **Fejér identity**: the double integral of `ψ (x - y)` over a ball is the integral of `ψ`
against the (unnormalised) overlap function. -/
private lemma setIntegral_setIntegral_sub (hc : Continuous ψ) (R : ℝ) :
    ∫ x in Metric.closedBall (0 : E) R, ∫ y in Metric.closedBall (0 : E) R, ψ (x - y) =
      ∫ v, volume.real (Metric.closedBall (0 : E) R ∩ Metric.closedBall v R) • ψ v := by
  set B := Metric.closedBall (0 : E) R
  set S := {p : E × E | p.1 ∈ B ∧ dist p.1 p.2 ≤ R}
  have hS : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded
      ((Metric.isClosed_closedBall.preimage continuous_fst).inter
        (isClosed_le (continuous_fst.dist continuous_snd) continuous_const)) ?_
    refine (Metric.isBounded_closedBall (x := (0 : E × E)) (r := 2 * |R|)).subset ?_
    rintro ⟨x, v⟩ ⟨hx, hxv⟩
    simp only [B, Metric.mem_closedBall, dist_zero_right] at hx
    simp only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
    have hv : ‖v‖ ≤ ‖x‖ + dist x v := by
      rw [dist_eq_norm']; linarith [norm_le_insert' v x]
    exact max_le (by linarith [le_abs_self R, abs_nonneg R]) (by linarith [le_abs_self R])
  have hint : Integrable (S.indicator (ψ ∘ Prod.snd)) (volume.prod volume) :=
    ((hc.comp continuous_snd).continuousOn.integrableOn_compact hS).integrable_indicator
      hS.isClosed.measurableSet
  have hmem (x v : E) : (x, v) ∈ S ↔ x ∈ B ∩ Metric.closedBall v R := by
    simp [S, B, Metric.mem_closedBall]
  -- substitute `v = x - y` in the inner integral, then swap the integrals
  have h_inner (x : E) : B.indicator (fun x ↦ ∫ y in B, ψ (x - y)) x =
      ∫ v, S.indicator (ψ ∘ Prod.snd) (x, v) := by
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx, ← integral_indicator measurableSet_closedBall,
        ← integral_sub_left_eq_self _ volume x]
      congr 1 with v
      simp only [Set.indicator, hmem, Set.mem_inter_iff, hx, true_and, Function.comp_apply,
        sub_sub_cancel, B, Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_sub_rev x v]
    · simp [hmem, hx]
  rw [← integral_indicator measurableSet_closedBall]
  refine (integral_congr_ae (ae_of_all _ h_inner)).trans ?_
  rw [integral_integral_swap (f := fun x v ↦ S.indicator (ψ ∘ Prod.snd) (x, v)) hint]
  congr 1 with v
  have : (fun x ↦ S.indicator (ψ ∘ Prod.snd) (x, v)) =
      (B ∩ Metric.closedBall v R).indicator fun _ ↦ ψ v := by
    ext x
    by_cases h : x ∈ B ∩ Metric.closedBall v R
    · rw [Set.indicator_of_mem ((hmem x v).2 h), Set.indicator_of_mem h, Function.comp_apply]
    · rw [Set.indicator_of_notMem (mt (hmem x v).1 h), Set.indicator_of_notMem h]
  rw [this, integral_indicator (measurableSet_closedBall.inter measurableSet_closedBall),
    setIntegral_const]

/-- The integral of a continuous integrable positive definite function is nonnegative. -/
private lemma integral_nonneg_of_isPositiveDefinite (hψ : IsPositiveDefinite ψ)
    (hc : Continuous ψ) (hi : Integrable ψ) : 0 ≤ ∫ x, ψ x := by
  have h_tendsto : Tendsto (fun n : ℕ ↦ ∫ v, (overlapRatio (n : ℝ) v : ℂ) * ψ v) atTop
      (𝓝 (∫ v, ψ v)) := by
    have := tendsto_integral_of_dominated_convergence (fun v ↦ ‖ψ v‖)
      (fun n ↦ (continuous_ofReal.measurable.comp
        (measurable_overlapRatio _)).aestronglyMeasurable.mul hc.aestronglyMeasurable) hi.norm
      (fun n ↦ ae_of_all _ fun v ↦ by
        rw [Pi.mul_apply, Function.comp_apply, norm_mul, norm_real,
          Real.norm_of_nonneg (overlapRatio_nonneg _ _)]
        exact mul_le_of_le_one_left (norm_nonneg _) (overlapRatio_le_one _ _))
      (ae_of_all _ fun v ↦ ((continuous_ofReal.tendsto 1).comp
        ((tendsto_overlapRatio v).comp tendsto_natCast_atTop_atTop)).mul_const (ψ v))
    simpa using this
  refine ge_of_tendsto' h_tendsto fun n ↦ ?_
  have : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : E) n)) :=
    isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
  have h_eq : ∫ v, (overlapRatio (n : ℝ) v : ℂ) * ψ v =
      (volume.real (Metric.closedBall (0 : E) n))⁻¹ • ∫ x in Metric.closedBall (0 : E) n,
        ∫ y in Metric.closedBall (0 : E) n, ψ (x - y) := by
    rw [setIntegral_setIntegral_sub hc, ← integral_smul]
    congr 1 with v
    rw [smul_smul, Complex.real_smul, overlapRatio, div_eq_inv_mul]
  rw [h_eq]
  exact smul_nonneg (inv_nonneg.2 measureReal_nonneg) (integral_integral_sub_nonneg hψ hc _)

/-- The Fourier transform of a continuous integrable positive definite function is
nonnegative. -/
private lemma fourier_nonneg (hψ : IsPositiveDefinite ψ) (hc : Continuous ψ) (hi : Integrable ψ)
    (ξ : E) : 0 ≤ 𝓕 ψ ξ := by
  let χ : E →+ ℝ := AddMonoidHom.mk' (fun v ↦ -(2 * π * ⟪v, ξ⟫)) fun v w ↦ by
    rw [inner_add_left]; ring
  have heq : (fun v ↦ 𝐞 (-⟪v, ξ⟫) • ψ v) = ψ * fun v ↦ cexp (χ v * I) := by
    ext v
    simp only [Circle.smul_def, Real.fourierChar_apply, Pi.mul_apply, smul_eq_mul, χ,
      AddMonoidHom.mk'_apply]
    rw [mul_comm]
    congr 2
    push_cast
    ring
  have hi' : Integrable (ψ * fun v ↦ cexp (χ v * I)) :=
    heq ▸ (Real.fourierIntegral_convergent_iff ξ).2 hi
  have hχ : Continuous fun v ↦ (χ v : ℝ) := by
    change Continuous fun v ↦ -(2 * π * ⟪v, ξ⟫)
    fun_prop
  rw [Real.fourier_eq, heq]
  exact integral_nonneg_of_isPositiveDefinite (hψ.mul (isPositiveDefinite_cexp χ))
    (hc.mul (by fun_prop)) hi'

end Fejer

/-! ### Integrability of the Fourier transform and the measure of an integrable function -/

section Integrable

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ψ : E → ℂ}

/-- For a nonnegative complex function, the integral of the norm is the norm of the integral. -/
private lemma integral_norm_eq_norm_integral_of_nonneg {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {h : α → ℂ} (hh : ∀ a, 0 ≤ h a) : ∫ a, ‖h a‖ ∂μ = ‖∫ a, h a ∂μ‖ := by
  have : ∫ a, h a ∂μ = ∫ a, ((‖h a‖ : ℝ) : ℂ) ∂μ :=
    integral_congr_ae (ae_of_all _ fun a ↦ (norm_of_nonneg' (hh a)).symm)
  rw [this, integral_complex_ofReal, norm_real,
    Real.norm_of_nonneg (integral_nonneg fun a ↦ norm_nonneg _)]

/-- Gaussians `x ↦ exp (-t ‖x‖²)`, `t ≥ 0`, are positive definite: they are characteristic
functions of centred Gaussian measures. -/
private lemma isPositiveDefinite_gaussian {t : ℝ} (ht : 0 ≤ t) :
    IsPositiveDefinite fun x : E ↦ cexp (-t * ‖x‖ ^ 2) := by
  convert (isPositiveDefinite_charFun (ProbabilityTheory.stdGaussian E)).comp_addMonoidHom
    (DistribSMul.toAddMonoidHom E √(2 * t)) using 1
  ext x
  have h : ‖√(2 * t) • x‖ ^ 2 = 2 * t * ‖x‖ ^ 2 := by
    rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt (by positivity)]
  have h' : ((‖√(2 * t) • x‖ : ℝ) : ℂ) ^ 2 = 2 * t * ‖x‖ ^ 2 := by exact_mod_cast h
  rw [Function.comp_apply, DistribSMul.toAddMonoidHom_apply,
    ProbabilityTheory.charFun_stdGaussian, h']
  congr 1
  ring

/-- Gaussians are integrable. -/
private lemma integrable_gaussian {t : ℝ} (ht : 0 < t) :
    Integrable fun x : E ↦ cexp (-t * ‖x‖ ^ 2) := by
  simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := E) (b := (t : ℂ))
    (by simpa) 0 0

/-- The Fourier transform of a Gaussian is a Gaussian, hence integrable. -/
private lemma integrable_fourier_gaussian {t : ℝ} (ht : 0 < t) :
    Integrable (𝓕 fun x : E ↦ cexp (-t * ‖x‖ ^ 2)) := by
  have : 𝓕 (fun x : E ↦ cexp (-t * ‖x‖ ^ 2)) = fun w ↦ (π / t : ℂ) ^ (Module.finrank ℝ E / 2 : ℂ) *
      cexp (-((π ^ 2 / t : ℝ) : ℂ) * ‖w‖ ^ 2) := by
    ext w
    rw [fourier_gaussian_innerProductSpace (by simpa)]
    congr 2
    push_cast
    ring
  rw [this]
  exact (integrable_gaussian (by positivity)).const_mul _

/-- The Fourier transform of `x ↦ exp (-t ‖x‖²)` has integral `1`, by Fourier inversion at `0`. -/
private lemma integral_fourier_gaussian {t : ℝ} (ht : 0 < t) :
    ∫ w, 𝓕 (fun x : E ↦ cexp (-t * ‖x‖ ^ 2)) w = 1 := by
  have := (integrable_gaussian ht).fourierInv_fourier_eq (integrable_fourier_gaussian ht)
    (v := (0 : E)) (by fun_prop : Continuous fun x : E ↦ cexp (-t * ‖x‖ ^ 2)).continuousAt
  simpa [Real.fourierInv_eq] using this

/-- The Fourier transform of a continuous integrable positive definite function is integrable:
by Parseval's identity, its integrals against the Gaussians `exp (-t ‖w‖²)` are bounded by `ψ 0`,
and one concludes by Fatou's lemma as `t → 0`. -/
private lemma integrable_fourier (hψ : IsPositiveDefinite ψ) (hc : Continuous ψ)
    (hi : Integrable ψ) : Integrable (𝓕 ψ) := by
  have hF : Continuous (𝓕 ψ) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hi
  set t : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have ht (n : ℕ) : 0 < t n := by positivity
  set g : ℕ → E → ℂ := fun n x ↦ cexp (-t n * ‖x‖ ^ 2)
  have hg_nonneg (n : ℕ) (x : E) : 0 ≤ g n x := by
    have : g n x = ((Real.exp (-t n * ‖x‖ ^ 2) : ℝ) : ℂ) := by
      push_cast [g]
      rfl
    rw [this]
    exact_mod_cast (Real.exp_pos _).le
  have hbound (n : ℕ) : ∫⁻ w, ‖𝓕 ψ w * g n w‖ₑ ≤ ENNReal.ofReal (ψ 0).re := by
    have hint : Integrable fun w ↦ 𝓕 ψ w * g n w :=
      (integrable_gaussian (ht n)).bdd_mul hF.aestronglyMeasurable
        (ae_of_all _ fun w ↦ VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ w)
    rw [← ofReal_integral_norm_eq_lintegral_enorm hint]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [integral_norm_eq_norm_integral_of_nonneg fun w ↦
      mul_nonneg (fourier_nonneg hψ hc hi w) (hg_nonneg n w)]
    have hP : ∫ w, 𝓕 ψ w * g n w = ∫ x, ψ x * 𝓕 (g n) x := by
      have := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ E)
        Real.continuous_fourierChar continuous_inner hi (integrable_gaussian (ht n))
        (μ := volume) (ν := volume)
      simp only [smul_eq_mul, flip_innerₗ] at this
      exact this
    have hFg_nonneg (x : E) : 0 ≤ 𝓕 (g n) x :=
      fourier_nonneg (isPositiveDefinite_gaussian (ht n).le) (by fun_prop)
        (integrable_gaussian (ht n)) x
    rw [hP]
    calc ‖∫ x, ψ x * 𝓕 (g n) x‖
        ≤ ∫ x, ‖ψ x * 𝓕 (g n) x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x, (ψ 0).re * ‖𝓕 (g n) x‖ :=
          integral_mono_of_nonneg (ae_of_all _ fun _ ↦ norm_nonneg _)
            ((integrable_fourier_gaussian (ht n)).norm.const_mul _) (ae_of_all _ fun x ↦ by
              dsimp only
              rw [norm_mul]
              exact mul_le_mul_of_nonneg_right (hψ.norm_apply_le x) (norm_nonneg _))
      _ = (ψ 0).re := by
          rw [integral_const_mul, integral_norm_eq_norm_integral_of_nonneg hFg_nonneg,
            integral_fourier_gaussian (ht n), norm_one, mul_one]
  have h_lim (w : E) : Tendsto (fun n ↦ ‖𝓕 ψ w * g n w‖ₑ) atTop (𝓝 ‖𝓕 ψ w‖ₑ) := by
    have : Tendsto (fun n ↦ g n w) atTop (𝓝 1) := by
      have := (((continuous_ofReal.tendsto 0).comp
        tendsto_one_div_add_atTop_nhds_zero_nat).neg.mul_const ((‖w‖ : ℂ) ^ 2)).cexp
      simpa [g, t] using this
    simpa using (tendsto_const_nhds.mul this).enorm
  refine ⟨hF.aestronglyMeasurable, ?_⟩
  calc ∫⁻ w, ‖𝓕 ψ w‖ₑ
      = ∫⁻ w, liminf (fun n ↦ ‖𝓕 ψ w * g n w‖ₑ) atTop :=
        lintegral_congr fun w ↦ (h_lim w).liminf_eq.symm
    _ ≤ liminf (fun n ↦ ∫⁻ w, ‖𝓕 ψ w * g n w‖ₑ) atTop :=
        lintegral_liminf_le' fun n ↦ (hF.mul (by fun_prop)).aemeasurable.enorm
    _ ≤ ENNReal.ofReal (ψ 0).re := liminf_le_of_frequently_le' (.of_forall hbound)
    _ < ⊤ := ENNReal.ofReal_lt_top

end Integrable

/-! ### Existence of the measure on an inner product space -/

section Existence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {φ : E → ℂ}

/-- A continuous integrable positive definite function is the characteristic function of a finite
measure, namely of the image under `w ↦ 2π w` of the measure with density `𝓕 φ`. -/
private lemma exists_charFun_eq_of_integrable (hφ : IsPositiveDefinite φ) (hc : Continuous φ)
    (hi : Integrable φ) : ∃ μ : Measure E, IsFiniteMeasure μ ∧ charFun μ = φ := by
  have hF : Continuous (𝓕 φ) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hi
  have hFi := integrable_fourier hφ hc hi
  have hF0 := fourier_nonneg hφ hc hi
  have hre (w : E) : (((𝓕 φ w).re : ℝ) : ℂ) = 𝓕 φ w :=
    Complex.ext (by simp) (by simp [(Complex.nonneg_iff.1 (hF0 w)).2])
  set ν := volume.withDensity fun w ↦ ENNReal.ofReal (𝓕 φ w).re
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hFi.re.hasFiniteIntegral
  refine ⟨ν.map ((2 * π) • ·), inferInstance, funext fun ξ ↦ ?_⟩
  rw [charFun_map_smul, charFun_apply, integral_withDensity_eq_integral_toReal_smul
    (f := fun w ↦ ENNReal.ofReal (𝓕 φ w).re) (by fun_prop)
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  conv_rhs => rw [← hc.fourierInv_fourier_eq hi hFi]
  rw [Real.fourierInv_eq]
  congr 1 with w
  rw [ENNReal.toReal_ofReal (Complex.nonneg_iff.1 (hF0 w)).1, Complex.real_smul, hre,
    Circle.smul_def, Real.fourierChar_apply, real_inner_smul_right, smul_eq_mul, mul_comm]

/-- **Bochner's theorem** for a normalised function on a finite-dimensional inner product space:
the Gaussian regularisations `φ x * exp (-t ‖x‖²)` are characteristic functions of probability
measures, which are tight by Lévy's continuity theorem; by Prokhorov's theorem a subsequence
converges weakly, and its limit has characteristic function `φ`. -/
private lemma exists_probabilityMeasure_charFun_eq (hφ : IsPositiveDefinite φ)
    (hc : Continuous φ) (h0 : φ 0 = 1) : ∃ μ : ProbabilityMeasure E, charFun (μ : Measure E) = φ := by
  set t : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have ht (n : ℕ) : 0 < t n := by positivity
  have hμ (n : ℕ) : ∃ μ : ProbabilityMeasure E,
      charFun (μ : Measure E) = fun x ↦ φ x * cexp (-t n * ‖x‖ ^ 2) := by
    obtain ⟨μ, _, hμ⟩ := exists_charFun_eq_of_integrable
      (hφ.mul (isPositiveDefinite_gaussian (ht n).le)) (hc.mul (by fun_prop))
      ((integrable_gaussian (ht n)).bdd_mul hc.aestronglyMeasurable
        (ae_of_all _ hφ.norm_apply_le))
    have : IsProbabilityMeasure μ := by
      have h := congr_fun hμ 0
      rw [charFun_zero] at h
      simp only [Pi.mul_apply, h0, norm_zero] at h
      exact isProbabilityMeasure_iff_real.2 (by exact_mod_cast (by simpa using h))
    exact ⟨⟨μ, this⟩, hμ⟩
  choose μ hμ using hμ
  have h_lim (x : E) : Tendsto (fun n ↦ charFun (μ n : Measure E) x) atTop (𝓝 (φ x)) := by
    simp_rw [hμ]
    have := (((continuous_ofReal.tendsto 0).comp
      tendsto_one_div_add_atTop_nhds_zero_nat).neg.mul_const ((‖x‖ : ℂ) ^ 2)).cexp
    simpa [t] using tendsto_const_nhds.mul this
  have h_tight := isTightMeasureSet_of_tendsto_charFun (μ := fun n ↦ (μ n : Measure E))
    hc.continuousAt h_lim
  obtain ⟨ν, -, f, hf, hν⟩ := (isCompact_closure_of_isTightMeasureSet (S := Set.range μ)
    (by convert h_tight; ext; simp)).tendsto_subseq fun n ↦ subset_closure (Set.mem_range_self n)
  exact ⟨ν, funext fun x ↦ tendsto_nhds_unique
    (ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 hν x) ((h_lim x).comp hf.tendsto_atTop)⟩

/-- **Bochner's theorem**, existence part, on a finite-dimensional inner product space. -/
private lemma exists_charFun_eq (hφ : IsPositiveDefinite φ) (hc : Continuous φ) :
    ∃ μ : Measure E, IsFiniteMeasure μ ∧ charFun μ = φ := by
  rcases hφ.re_apply_zero_nonneg.eq_or_lt with h | h
  · refine ⟨0, inferInstance, funext fun x ↦ ?_⟩
    have := hφ.norm_apply_le x
    rw [← h, norm_le_zero_iff] at this
    rw [charFun_zero_measure, this]
  · obtain ⟨ν, hν⟩ := exists_probabilityMeasure_charFun_eq (hφ.smul (inv_nonneg.2 h.le))
      (hc.const_smul _) (by
        rw [Pi.smul_apply, Complex.real_smul]
        calc (((φ 0).re⁻¹ : ℝ) : ℂ) * φ 0 = (((φ 0).re⁻¹ : ℝ) : ℂ) * ((φ 0).re : ℂ) := by
              rw [hφ.ofReal_re_apply_zero]
          _ = 1 := by rw [← ofReal_mul, inv_mul_cancel₀ h.ne', ofReal_one])
    have : IsFiniteMeasure (ENNReal.ofReal (φ 0).re • (ν : Measure E)) :=
      ⟨by simp⟩
    refine ⟨ENNReal.ofReal (φ 0).re • (ν : Measure E), this, funext fun x ↦ ?_⟩
    rw [charFun_apply, integral_smul_measure, ← charFun_apply, hν, ENNReal.toReal_ofReal h.le,
      Pi.smul_apply, smul_smul, mul_inv_cancel₀ h.ne', one_smul]

end Existence

/-! ### Bochner's theorem for a continuous perfect pairing -/

section Pairing

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup W] [Module ℝ W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  [ContinuousSMul ℝ W] (L : W →ₗ[ℝ] V →ₗ[ℝ] ℝ) [L.IsContPerfPair] {φ : V → ℂ}

/-- Up to continuous linear equivalences, a continuous perfect pairing `L` between
finite-dimensional real vector spaces is the inner product of a Euclidean space. This is the
only place where the pairing form of Bochner's theorem is reduced to the inner product form. -/
lemma LinearMap.exists_euclidean_of_isContPerfPair :
    ∃ (n : ℕ) (e : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (f : W ≃L[ℝ] EuclideanSpace ℝ (Fin n)),
      ∀ w v, L w v = ⟪f w, e v⟫ := by
  have : SeparatingDual ℝ V := ⟨fun v hv ↦ by
    obtain ⟨w, hw⟩ : ∃ w, L w v ≠ 0 := by
      by_contra! h
      exact hv ((LinearMap.IsContPerfPair.bijective_right L).injective
        (a₂ := 0) (by ext w; change L w v = L w 0; simp [h w]))
    exact ⟨⟨L w, L.continuous_of_isContPerfPair⟩, hw⟩⟩
  have : SeparatingDual ℝ W := ⟨fun w hw ↦ by
    obtain ⟨v, hv⟩ : ∃ v, L w v ≠ 0 := by
      by_contra! h
      exact hw ((LinearMap.IsContPerfPair.bijective_left L).injective
        (a₂ := 0) (by ext v; change L w v = L 0 v; simp [h v]))
    exact ⟨⟨L.flip v, L.flip.continuous_of_isContPerfPair⟩, hv⟩⟩
  have : T2Space V := SeparatingDual.t2Space (R := ℝ)
  have : T2Space W := SeparatingDual.t2Space (R := ℝ)
  have : FiniteDimensional ℝ W :=
    (L.toContPerfPair.trans LinearMap.toContinuousLinearMap.symm).symm.finiteDimensional
  set E := EuclideanSpace ℝ (Fin (Module.finrank ℝ V))
  let e : V ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq (by simp [E])
  let f : W ≃L[ℝ] E := (L.toContPerfPair.trans <|
    (e.arrowCongr (.refl ℝ ℝ)).toLinearEquiv.trans (innerₗ E).toContPerfPair.symm)
    |>.toContinuousLinearEquiv
  refine ⟨_, e, f, fun w v ↦ ?_⟩
  have key (g : StrongDual ℝ E) (x : E) : ⟪(innerₗ E).toContPerfPair.symm g, x⟫ = g x := by
    conv_rhs => rw [← (innerₗ E).toContPerfPair.apply_symm_apply g]
    rfl
  simp [f, key]

include L in
/-- The topology of the right factor `V` of a continuous perfect pairing of finite-dimensional real
vector spaces is first countable, as that of a Euclidean space. -/
lemma LinearMap.firstCountableTopology_of_isContPerfPair : FirstCountableTopology V := by
  obtain ⟨n, e, -, -⟩ := L.exists_euclidean_of_isContPerfPair
  exact e.toHomeomorph.isEmbedding.firstCountableTopology

variable [MeasurableSpace W] [BorelSpace W]

omit [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [FiniteDimensional ℝ V] [IsTopologicalAddGroup W]
  [ContinuousSMul ℝ W] in
/-- The pairing `w ↦ L w v` of a continuous perfect pairing is measurable for every `v`; this is
the measurability needed for Fourier transforms `w ↦ exp (i L w v)` of measures on `W`. -/
lemma LinearMap.measurable_flip_apply_of_isContPerfPair (v : V) : Measurable fun w => L w v :=
  (L.flip.continuous_of_isContPerfPair (x := v)).measurable

variable {L} in
/-- **Uniqueness in Bochner's theorem**: a finite measure `μ` on `W` is determined by its Fourier
transform `v ↦ ∫ w, exp (i L w v) ∂μ` with respect to a continuous perfect pairing `L`. -/
lemma MeasureTheory.Measure.ext_of_integral_cexp_eq {μ ν : Measure W} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (h : ∀ v, ∫ w, cexp (L w v * I) ∂μ = ∫ w, cexp (L w v * I) ∂ν) :
    μ = ν := by
  obtain ⟨n, e, f, hL⟩ := L.exists_euclidean_of_isContPerfPair
  let F := f.toHomeomorph.toMeasurableEquiv
  have : μ.map F = ν.map F := by
    refine Measure.ext_of_charFun (funext fun y ↦ ?_)
    rw [charFun_apply, charFun_apply, integral_map_equiv, integral_map_equiv]
    convert h (e.symm y) using 5 <;> simp [F, hL]
  rw [← F.map_symm_map (μ := μ), this, F.map_symm_map]

/-- **Bochner's theorem**, existence part: a continuous positive definite function `φ` on `V` is
the Fourier transform `v ↦ ∫ w, exp (i L w v) ∂μ` of a finite measure `μ` on `W`. -/
lemma IsPositiveDefinite.exists_finiteMeasure (hφ : IsPositiveDefinite φ) (hc : Continuous φ) :
    ∃ μ : FiniteMeasure W, ∀ v, φ v = ∫ w, cexp (L w v * I) ∂μ := by
  obtain ⟨n, e, f, hL⟩ := L.exists_euclidean_of_isContPerfPair
  obtain ⟨μ, _, hμ⟩ := exists_charFun_eq
    (hφ.comp_addMonoidHom e.symm.toLinearEquiv.toAddEquiv.toAddMonoidHom)
    (hc.comp e.symm.continuous)
  let F := f.toHomeomorph.toMeasurableEquiv
  refine ⟨⟨μ.map F.symm, inferInstance⟩, fun v ↦ ?_⟩
  rw [FiniteMeasure.toMeasure_mk, integral_map_equiv]
  have := congr_fun hμ (e v)
  simp only [charFun_apply, Function.comp_apply] at this
  simpa [F, hL] using this.symm

/-- **Bochner's theorem**: a continuous positive definite function `φ` on `V` is the Fourier
transform `v ↦ ∫ w, exp (i L w v) ∂μ` of a unique finite measure `μ` on `W`. -/
theorem IsPositiveDefinite.existsUnique_finiteMeasure (hφ : IsPositiveDefinite φ)
    (hc : Continuous φ) : ∃! μ : FiniteMeasure W, ∀ v, φ v = ∫ w, cexp (L w v * I) ∂μ := by
  obtain ⟨μ, hμ⟩ := hφ.exists_finiteMeasure L hc
  refine ⟨μ, hμ, fun ν hν ↦ FiniteMeasure.toMeasure_injective ?_⟩
  exact Measure.ext_of_integral_cexp_eq (L := L) fun v ↦ by rw [← hν v, ← hμ v]

/-- **Bochner's theorem**: a continuous function `φ` on `V` is positive definite if and only if it
is the Fourier transform `v ↦ ∫ w, exp (i L w v) ∂μ` of a finite measure `μ` on `W`. -/
theorem isPositiveDefinite_iff_exists_finiteMeasure (hc : Continuous φ) :
    IsPositiveDefinite φ ↔ ∃ μ : FiniteMeasure W, ∀ v, φ v = ∫ w, cexp (L w v * I) ∂μ := by
  refine ⟨fun hφ ↦ hφ.exists_finiteMeasure L hc, fun ⟨μ, hμ⟩ ↦ ?_⟩
  convert isPositiveDefinite_integral_cexp (μ : Measure W) (fun w ↦ (L w).toAddMonoidHom)
    fun v ↦ (L.measurable_flip_apply_of_isContPerfPair v).aemeasurable
  exact hμ _

end Pairing

/-! ### Special cases: inner product spaces and the dual space -/

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {φ : E → ℂ}

/-- **Bochner's theorem** on a finite-dimensional real inner product space: a continuous positive
definite function is the characteristic function of a unique finite measure. This is the case
`L = innerₗ E` of `IsPositiveDefinite.existsUnique_finiteMeasure`. -/
lemma IsPositiveDefinite.existsUnique_charFun_eq (hφ : IsPositiveDefinite φ)
    (hc : Continuous φ) : ∃! μ : FiniteMeasure E, charFun (μ : Measure E) = φ := by
  convert hφ.existsUnique_finiteMeasure (innerₗ E) hc using 2
  simp [funext_iff, charFun_apply, eq_comm]

/-- **Bochner's theorem** on a finite-dimensional real inner product space: a continuous function
is positive definite if and only if it is the characteristic function of a finite measure. -/
lemma isPositiveDefinite_iff_exists_charFun_eq (hc : Continuous φ) :
    IsPositiveDefinite φ ↔ ∃ μ : FiniteMeasure E, charFun (μ : Measure E) = φ :=
  ⟨fun hφ ↦ (hφ.existsUnique_charFun_eq hc).exists, fun ⟨_, hμ⟩ ↦ hμ ▸ isPositiveDefinite_charFun _⟩

end InnerProductSpace

section StrongDual

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul ℝ V] [T2Space V] [FiniteDimensional ℝ V] [MeasurableSpace (StrongDual ℝ V)]
  [BorelSpace (StrongDual ℝ V)] {φ : V → ℂ}

/-- **Bochner's theorem** with the measure on the dual space: a continuous positive definite
function `φ` on a finite-dimensional real vector space `V` is of the form
`φ v = ∫ p, exp (i p v) ∂μ` for a unique finite measure `μ` on `StrongDual ℝ V`. -/
theorem IsPositiveDefinite.existsUnique_finiteMeasure_strongDual (hφ : IsPositiveDefinite φ)
    (hc : Continuous φ) :
    ∃! μ : FiniteMeasure (StrongDual ℝ V), ∀ v, φ v = ∫ p : StrongDual ℝ V, cexp (p v * I) ∂μ :=
  hφ.existsUnique_finiteMeasure (topDualPairing ℝ V) hc

/-- **Bochner's theorem** with the measure on the dual space: a continuous function `φ` on a
finite-dimensional real vector space `V` is positive definite if and only if
`φ v = ∫ p, exp (i p v) ∂μ` for a finite measure `μ` on `StrongDual ℝ V`. -/
theorem isPositiveDefinite_iff_exists_finiteMeasure_strongDual (hc : Continuous φ) :
    IsPositiveDefinite φ ↔
      ∃ μ : FiniteMeasure (StrongDual ℝ V), ∀ v, φ v = ∫ p : StrongDual ℝ V, cexp (p v * I) ∂μ :=
  isPositiveDefinite_iff_exists_finiteMeasure (topDualPairing ℝ V) hc

end StrongDual
