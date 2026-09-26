/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Algebra.VonNeumannAlgebra.Diagonal
public import QuantumSystem.Analysis.Entropy.Araki.Basic
public import QuantumSystem.ForMathlib.InformationTheory.KullbackLeibler.Fintype
public import QuantumSystem.ForMathlib.InformationTheory.KullbackLeibler.KLFun

/-!
# Araki's relative entropy on a commutative algebra: Kullback–Leibler

On the diagonal algebra `ℓ^∞(ι)` acting on `ℓ²(ι)` (`VonNeumannAlgebra.diagonalAlgebra`), the vector
`ξ_p = Σᵢ √pᵢ eᵢ` represents the weight `x ↦ Σᵢ pᵢ xᵢᵢ`. For non-negative weights `p, q`, the
relative modular operator `Δ_{ξ_q, ξ_p}` has eigenvalue `qᵢ / pᵢ` on `eᵢ` whenever `pᵢ > 0`, its
spectral measure at `ξ_p` is `Σᵢ pᵢ δ_{qᵢ/pᵢ}`, and Araki's relative entropy is the
**Kullback–Leibler divergence**
`S(ω_{ξ_p} ‖ ω_{ξ_q}) = Σᵢ pᵢ log (pᵢ / qᵢ)` if `supp p ⊆ supp q`, and `+∞` otherwise.

The weights are not normalised, and Araki's convention carries no mass correction: the value is
`Σᵢ pᵢ log (pᵢ / qᵢ)`, not `Σᵢ pᵢ log (pᵢ / qᵢ) + Σᵢ qᵢ - Σᵢ pᵢ`. For weights of equal total mass
it coincides with Mathlib's `InformationTheory.klDiv` of the measures `Σᵢ pᵢ δᵢ` and `Σᵢ qᵢ δᵢ`.

These results pin what the general lemmas of `QuantumSystem.Analysis.Entropy.Araki.Vector`
cannot, namely the argument order and the shape `p log (p / q)` of `VonNeumannAlgebra.arakiVec`
beyond scalars and supports. The first argument is the weight being measured, the second the
reference; for `p = (½, ½)` and `q = (¼, ¾)` the two orders give different values.

## Main results

* `VonNeumannAlgebra.mem_graph_relativeModular_diagonalVec` — `Δ_{ξ_q, ξ_p} eᵢ = (qᵢ / pᵢ) eᵢ`
  for `pᵢ > 0`.
* `VonNeumannAlgebra.spectralMeasure_relativeModular_diagonalVec` — `μ_{ξ_p} = Σᵢ pᵢ δ_{qᵢ/pᵢ}`.
* `VonNeumannAlgebra.arakiVec_diagonalVec`, `VonNeumannAlgebra.arakiEntropy_diagonalVec` —
  `S(ω_{ξ_p} ‖ ω_{ξ_q}) = Σᵢ pᵢ log (pᵢ / qᵢ)` if `supp p ⊆ supp q`, and `+∞` otherwise.
* `VonNeumannAlgebra.arakiEntropy_diagonalVec_eq_klDiv` — for `Σᵢ pᵢ = Σᵢ qᵢ`, the value is
  Mathlib's `klDiv (Σᵢ pᵢ δᵢ) (Σᵢ qᵢ δᵢ)`.
-/

@[expose] public section

open ClosedSubmodule MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace VonNeumannAlgebra lp
open InnerProductSpace (cyclicSubspace)

namespace VonNeumannAlgebra

private lemma ofReal_smul_mem_graph {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {T : E →ₗ.[ℝ] E} {a b : E} (h : (a, b) ∈ T.graph) (r : ℝ) :
    ((r : ℂ) • a, (r : ℂ) • b) ∈ T.graph := by
  have := T.graph.smul_mem r h
  rwa [Prod.smul_mk, ← Complex.coe_smul, ← Complex.coe_smul] at this

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `ξ_r = Σᵢ √rᵢ eᵢ`, the vector representing the diagonal weight `x ↦ Σᵢ rᵢ xᵢᵢ`. -/
noncomputable def diagonalVec (r : ι → ℝ) : ℓ²(ι, ℂ) :=
  ∑ i, ((Real.sqrt (r i) : ℝ) : ℂ) • lp.single 2 i (1 : ℂ)

/-- `Pᵢ ξ_r = √rᵢ eᵢ`. -/
lemma coordProjection_diagonalVec (r : ι → ℝ) (i : ι) :
    coordProjection i (diagonalVec r) = ((Real.sqrt (r i) : ℝ) : ℂ) • lp.single 2 i (1 : ℂ) := by
  simp only [diagonalVec, map_sum, map_smul, coordProjection_apply_single, smul_ite, smul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- If `rᵢ > 0`, the basis vector `eᵢ` lies in the cyclic subspace generated from `ξ_r` by any
von Neumann algebra containing the coordinate projections. -/
lemma single_mem_cyclicSubspace_diagonalVec (N : VonNeumannAlgebra (ℓ²(ι, ℂ)))
    (hN : ∀ i, coordProjection i ∈ N) {r : ι → ℝ} {i : ι} (hr : 0 < r i) :
    lp.single 2 i (1 : ℂ) ∈
      (cyclicSubspace (N : Set (ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ))) (diagonalVec r)).toSubmodule := by
  have h := Submodule.smul_mem _ (((Real.sqrt (r i) : ℝ) : ℂ)⁻¹)
    (InnerProductSpace.apply_mem_cyclicSubspace (diagonalVec r) (hN i))
  rwa [coordProjection_diagonalVec, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast (Real.sqrt_pos.mpr hr).ne'), one_smul] at h

/-- If `rᵢ > 0`, then `s(ξ_r) eᵢ = eᵢ`. -/
lemma supportProj_diagonalVec_single {r : ι → ℝ} {i : ι} (hr : 0 < r i) :
    (diagonalAlgebra ι).supportProj (diagonalVec r) (lp.single 2 i (1 : ℂ)) =
      lp.single 2 i (1 : ℂ) := by
  rw [supportProj, Submodule.starProjection_eq_self_iff]
  exact single_mem_cyclicSubspace_diagonalVec _ coordProjection_mem_commutant hr

/-- If `rᵢ > 0`, then `s′(ξ_r) eᵢ = eᵢ`. -/
lemma supportProj_commutant_diagonalVec_single {r : ι → ℝ} {i : ι} (hr : 0 < r i) :
    (diagonalAlgebra ι)′.supportProj (diagonalVec r) (lp.single 2 i (1 : ℂ)) =
      lp.single 2 i (1 : ℂ) := by
  rw [supportProj_commutant, Submodule.starProjection_eq_self_iff]
  exact single_mem_cyclicSubspace_diagonalVec _ coordProjection_mem hr

variable {p q : ι → ℝ}

/-- If `pᵢ > 0`, the relative Tomita operator of `M` sends `√pᵢ eᵢ` to `√qᵢ eᵢ`. -/
private lemma mem_graph_relativeTomita_diagonalVec {i : ι} (hp : 0 < p i) :
    (((Real.sqrt (p i) : ℝ) : ℂ) • lp.single 2 i (1 : ℂ),
        ((Real.sqrt (q i) : ℝ) : ℂ) • lp.single 2 i (1 : ℂ)) ∈
      ((diagonalAlgebra ι).relativeTomita (diagonalVec q) (diagonalVec p)).graph := by
  have h := apply_mem_graph_relativeTomita (η := diagonalVec q) (ξ := diagonalVec p)
    (coordProjection_mem i)
  rwa [coordProjection_diagonalVec, star_coordProjection, coordProjection_diagonalVec, map_smul,
    supportProj_diagonalVec_single hp] at h

/-- If `pᵢ > 0`, the relative Tomita operator of `M′` sends `√pᵢ eᵢ` to `√qᵢ eᵢ`. -/
private lemma mem_graph_relativeTomita_commutant_diagonalVec {i : ι} (hp : 0 < p i) :
    (((Real.sqrt (p i) : ℝ) : ℂ) • lp.single 2 i (1 : ℂ),
        ((Real.sqrt (q i) : ℝ) : ℂ) • lp.single 2 i (1 : ℂ)) ∈
      ((diagonalAlgebra ι)′.relativeTomita (diagonalVec q) (diagonalVec p)).graph := by
  have h := apply_mem_graph_relativeTomita (M := (diagonalAlgebra ι)′) (η := diagonalVec q)
    (ξ := diagonalVec p) (coordProjection_mem_commutant i)
  rwa [coordProjection_diagonalVec, star_coordProjection, coordProjection_diagonalVec, map_smul,
    supportProj_commutant_diagonalVec_single hp] at h

/-- **The relative modular operator is diagonal**: `Δ_{ξ_q, ξ_p} eᵢ = (qᵢ / pᵢ) eᵢ` whenever
`pᵢ > 0` and `qᵢ ≥ 0`. -/
theorem mem_graph_relativeModular_diagonalVec {i : ι} (hp : 0 < p i) (hq : 0 ≤ q i) :
    (lp.single 2 i (1 : ℂ), ((q i / p i : ℝ) : ℂ) • lp.single 2 i (1 : ℂ)) ∈
      ((diagonalAlgebra ι).relativeModular (diagonalVec q) (diagonalVec p)).graph := by
  have hpi := (Real.sqrt_pos.mpr hp).ne'
  have hpp := Real.mul_self_sqrt hp.le
  have hqq := Real.mul_self_sqrt hq
  rw [mem_graph_relativeModular, LinearPMap.mem_graph_compNat]
  refine ⟨((Real.sqrt (q i) / Real.sqrt (p i) : ℝ) : ℂ) • lp.single 2 i (1 : ℂ), ?_, ?_⟩
  · refine mem_graph_closure_relativeTomita ?_
    have h := ofReal_smul_mem_graph (mem_graph_relativeTomita_diagonalVec (q := q) hp)
      (Real.sqrt (p i))⁻¹
    rwa [smul_smul, smul_smul, ← Complex.ofReal_mul, ← Complex.ofReal_mul, inv_mul_cancel₀ hpi,
      Complex.ofReal_one, one_smul, inv_mul_eq_div] at h
  · rw [LinearPMap.adjoint_closure (dense_domain_relativeTomita _ _ _)]
    refine LinearPMap.le_graph_of_le (relativeTomita_commutant_le_adjoint _ _ _) ?_
    have h := ofReal_smul_mem_graph (mem_graph_relativeTomita_commutant_diagonalVec (q := q) hp)
      (Real.sqrt (q i) / p i)
    have c₁ : Real.sqrt (q i) / p i * Real.sqrt (p i) = Real.sqrt (q i) / Real.sqrt (p i) := by
      rw [div_mul_eq_mul_div, div_eq_div_iff hp.ne' hpi]
      linear_combination Real.sqrt (q i) * hpp
    have c₂ : Real.sqrt (q i) / p i * Real.sqrt (q i) = q i / p i := by
      rw [div_mul_eq_mul_div, div_eq_div_iff hp.ne' hp.ne']
      linear_combination p i * hqq
    rwa [smul_smul, smul_smul, ← Complex.ofReal_mul, ← Complex.ofReal_mul, c₁, c₂] at h

/-- **Spectral measure**: `μ_{ξ_p}` of `Δ_{ξ_q, ξ_p}` is `Σᵢ pᵢ δ_{qᵢ/pᵢ}` for non-negative weights.
(A term with `pᵢ = 0` carries no mass, whatever its junk location `qᵢ / 0 = 0`.) -/
theorem spectralMeasure_relativeModular_diagonalVec (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) :
    (isSelfAdjoint_relativeModular (diagonalAlgebra ι) (diagonalVec q) (diagonalVec p)).spectralMeasure
        (diagonalVec p) =
      ∑ i, (p i).toNNReal • Measure.dirac (q i / p i) := by
  have hnorm : ∀ i, ‖((Real.sqrt (p i) : ℝ) : ℂ) • lp.single (E := fun _ : ι => ℂ) 2 i (1 : ℂ)‖₊ ^ 2 =
      (p i).toNNReal := fun i => by
    ext
    rw [Real.coe_toNNReal _ (hp i), NNReal.coe_pow, coe_nnnorm, norm_smul,
      lp.norm_single_one two_pos, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hp i)]
  simp_rw [← hnorm]
  conv_lhs => rw [diagonalVec]
  refine IsSelfAdjoint.spectralMeasure_sum_of_mem_graph _ Finset.univ
    (x := fun i => ((Real.sqrt (p i) : ℝ) : ℂ) • lp.single 2 i (1 : ℂ))
    (c := fun i => q i / p i) (fun i _ => ?_) (fun i _ j _ hij => ?_)
  · rcases (hp i).eq_or_lt with h0 | hpi
    · simp [← h0]
    have := ((diagonalAlgebra ι).relativeModular (diagonalVec q) (diagonalVec p)).graph.smul_mem
      ((Real.sqrt (p i) : ℝ) : ℂ) (mem_graph_relativeModular_diagonalVec hpi (hq i))
    rwa [Prod.smul_mk, smul_comm] at this
  · simp [lp.inner_single_left, hij]

/-- **Araki = Kullback–Leibler.** On the diagonal algebra, for non-negative weights `p, q`,
`S(ω_{ξ_p} ‖ ω_{ξ_q}) = Σᵢ pᵢ log (pᵢ / qᵢ)` if `supp p ⊆ supp q`, and `+∞` otherwise. This is the
Kullback–Leibler divergence of unnormalised weights in Araki's convention, with no mass correction
`Σᵢ qᵢ - Σᵢ pᵢ`; for equal total masses it is Mathlib's `InformationTheory.klDiv`
(`VonNeumannAlgebra.arakiEntropy_diagonalVec_eq_klDiv`). A term with `pᵢ = 0` contributes `0`. -/
theorem arakiVec_diagonalVec (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    [Decidable (Function.support p ⊆ Function.support q)] :
    (diagonalAlgebra ι).arakiVec (diagonalVec p) (diagonalVec q) =
      if Function.support p ⊆ Function.support q then
        ((∑ i, p i * Real.log (p i / q i) : ℝ) : EReal) else ⊤ := by
  rw [arakiVec, spectralMeasure_relativeModular_diagonalVec hp hq]
  split_ifs with hsupp
  · rw [negLogIntegral_finsetSum_smul_dirac _ _ (fun i _ hc => ?_)]
    · congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Real.coe_toNNReal _ (hp i), ← inv_div, Real.log_inv]
      ring
    · have hpi : 0 < p i := Real.toNNReal_pos.mp (pos_iff_ne_zero.mpr hc)
      exact div_pos ((hq i).lt_of_ne' (hsupp (Function.mem_support.mpr hpi.ne'))) hpi
  · obtain ⟨i, hpi, hqi⟩ := Set.not_subset.mp hsupp
    rw [Function.mem_support] at hpi
    rw [Function.notMem_support] at hqi
    exact negLogIntegral_finsetSum_smul_dirac_eq_top (Finset.mem_univ i)
      (by simpa using (hp i).lt_of_ne' hpi) (by rw [hqi, zero_div])

/-- **Araki = Kullback–Leibler**, for the normal functionals `ω_{ξ_p}` and `ω_{ξ_q}` with
non-negative weights: `Σᵢ pᵢ log (pᵢ / qᵢ)` if `supp p ⊆ supp q`, and `+∞` otherwise. -/
theorem arakiEntropy_diagonalVec (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    [Decidable (Function.support p ⊆ Function.support q)] :
    (diagonalAlgebra ι).arakiEntropy (NormalFunctional.ofVector _ (diagonalVec p))
        (NormalFunctional.ofVector _ (diagonalVec q)) =
      if Function.support p ⊆ Function.support q then
        ((∑ i, p i * Real.log (p i / q i) : ℝ) : EReal) else ⊤ := by
  rw [arakiEntropy_ofVector, arakiVec_diagonalVec hp hq]

omit [DecidableEq ι] in
/-- **Gibbs' inequality** for weights of equal mass: `0 ≤ Σᵢ pᵢ log (pᵢ / qᵢ)` when
`supp p ⊆ supp q` and `Σᵢ pᵢ = Σᵢ qᵢ`. -/
private lemma sum_mul_log_div_nonneg (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hsupp : Function.support p ⊆ Function.support q) (hpq : ∑ i, p i = ∑ i, q i) :
    0 ≤ ∑ i, p i * Real.log (p i / q i) := by
  have h : ∀ i, p i - q i ≤ p i * Real.log (p i / q i) := by
    intro i
    rcases (hp i).eq_or_lt with h0 | hpi
    · rw [← h0]; simpa using hq i
    · exact mul_log_div_ge_sub' hpi
        ((hq i).lt_of_ne' (hsupp (Function.mem_support.mpr hpi.ne')))
  calc (0 : ℝ) = ∑ i, (p i - q i) := by rw [Finset.sum_sub_distrib, hpq, sub_self]
    _ ≤ _ := Finset.sum_le_sum fun i _ => h i

omit [DecidableEq ι] in
/-- The finite measure `Σᵢ rᵢ δᵢ` on `ι` has mass `rᵢ` at `i`. -/
private lemma sum_smul_dirac_singleton [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {r : ι → ℝ} (hr : ∀ i, 0 ≤ r i) (i : ι) :
    (∑ j, ENNReal.ofReal (r j) • Measure.dirac j : Measure ι).real {i} = r i := by
  classical
  rw [measureReal_def, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (measurableSet_singleton i), Set.indicator_apply, Set.mem_singleton_iff,
    Pi.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact ENNReal.toReal_ofReal (hr i)

/-- **Araki = Mathlib's Kullback–Leibler divergence** for weights of equal total mass: with
`μ_r = Σᵢ rᵢ δᵢ`, `S(ω_{ξ_p} ‖ ω_{ξ_q}) = klDiv μ_p μ_q`. -/
theorem arakiEntropy_diagonalVec_eq_klDiv [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) (hpq : ∑ i, p i = ∑ i, q i) :
    (diagonalAlgebra ι).arakiEntropy (NormalFunctional.ofVector _ (diagonalVec p))
        (NormalFunctional.ofVector _ (diagonalVec q)) =
      (InformationTheory.klDiv (∑ i, ENNReal.ofReal (p i) • Measure.dirac i)
        (∑ i, ENNReal.ofReal (q i) • Measure.dirac i) : EReal) := by
  classical
  set μ : Measure ι := ∑ i, ENNReal.ofReal (p i) • Measure.dirac i
  set ν : Measure ι := ∑ i, ENNReal.ofReal (q i) • Measure.dirac i
  have hfin : ∀ r : ι → ℝ, IsFiniteMeasure (∑ i, ENNReal.ofReal (r i) • Measure.dirac i) :=
    fun r => ⟨by simp [Measure.coe_finsetSum, ENNReal.sum_lt_top]⟩
  have := hfin p
  have := hfin q
  have hμ : ∀ i, μ.real {i} = p i := sum_smul_dirac_singleton hp
  have hν : ∀ i, ν.real {i} = q i := sum_smul_dirac_singleton hq
  have hac : μ ≪ ν ↔ Function.support p ⊆ Function.support q := by
    rw [Measure.absolutelyContinuous_iff_singleton]
    refine forall_congr' fun i => ?_
    rw [← measureReal_eq_zero_iff, ← measureReal_eq_zero_iff, hμ, hν]
    exact ⟨fun h hpi => fun hqi => hpi (h hqi), fun h hqi => by_contra fun hpi => h hpi hqi⟩
  have huniv : ∀ (m : Measure ι) [IsFiniteMeasure m], m.real Set.univ = ∑ i, m.real {i} :=
    fun m _ => by rw [sum_measureReal_singleton, Finset.coe_univ]
  rw [arakiEntropy_diagonalVec hp hq, InformationTheory.klDiv_of_fintype, huniv μ, huniv ν]
  simp_rw [hμ, hν]
  by_cases hsupp : Function.support p ⊆ Function.support q
  · rw [ite_eq_left hsupp, ite_eq_left (hac.mpr hsupp), hpq, add_sub_cancel_right,
      EReal.coe_ennreal_ofReal, max_eq_left (sum_mul_log_div_nonneg hp hq hsupp hpq)]
  · rw [ite_eq_right hsupp, ite_eq_right (hac.not.mpr hsupp), EReal.coe_ennreal_top]

end VonNeumannAlgebra
