/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import QuantumSystem.Algebra.VonNeumannAlgebra.Multiplication
public import QuantumSystem.Analysis.Entropy.Araki.Basic
public import QuantumSystem.Analysis.UnboundedOperator.Multiplication

/-!
# Araki's relative entropy on a multiplication algebra: Kullback–Leibler

Let `μ` be a σ-finite measure on `α` and `M` the multiplication algebra on `L²(μ)`
(`VonNeumannAlgebra.multiplicationAlgebra`). Every finite measure `P ≪ μ` defines the normal
functional `ω_P : M_f ↦ ∫ f dP` (`VonNeumannAlgebra.NormalFunctional.ofMeasure`), and every normal
positive functional on `M` is `ω_P` for a unique such `P`
(`VonNeumannAlgebra.existsUnique_eq_ofMeasure`). The functional `ω_P` is the vector functional of
`ξ_P = √(dP/dμ)` (`VonNeumannAlgebra.NormalFunctional.ofMeasure_eq_ofVector`). For finite measures
`P` and `Q`, with densities `p = dP/dμ` and `q = dQ/dμ`, the relative modular operator
`Δ_{ξ_Q, ξ_P}` is the maximal multiplication operator `M_{q/p}`
(`VonNeumannAlgebra.relativeModular_densityVec_eq_mulPMap`); this needs neither σ-finiteness nor
`P ≪ μ`. In that generality `p` is `VonNeumannAlgebra.densityFun P μ = (P.rnDeriv μ).toReal`, the
density of the `μ`-absolutely continuous part of `P`, and `0` when `P` has no Lebesgue
decomposition with respect to `μ` (`MeasureTheory.Measure.rnDeriv`). Here `q / p = 0` on
`{p = 0}` by Lean's convention `q / 0 = 0`, which is the correct value: `Δ` kills the vectors
supported on `{p = 0}`
(`VonNeumannAlgebra.mem_graph_relativeModular_densityVec_zero_of_ae_eq_zero_on_pos`). Hence, for
`P ≪ μ` with a Lebesgue decomposition with respect to `μ`, the spectral measure at `ξ_P` is the
image of `P` under `q / p`, and for σ-finite `μ` Araki's relative entropy is the
**Kullback–Leibler divergence** `S(ω_P ‖ ω_Q) = ∫ log (dP/dQ) dP` if `P ≪ Q`, and `+∞` otherwise,
with the natural logarithm. σ-finiteness of `μ` enters only through the Radon–Nikodym calculus
of the densities (`MeasureTheory.Measure.rnDeriv_mul_rnDeriv`); the multiplication operators and
their spectral measures need no hypothesis on `μ`. The prose writes `S(ψ ‖ φ)`; the
code notation is `S⟦ψ ∥ φ⟧`, with `∥` (U+2225), as in `QuantumSystem.Analysis.Entropy.Araki.Basic`.

This is the divergence *without* the mass correction `Q(α) - P(α)` that Mathlib's
`InformationTheory.klDiv` adds, so `S(ω_P ‖ ω_Q) = klDiv P Q + P(α) - Q(α)` for all finite
`P, Q ≪ μ`, and `S(ω_P ‖ ω_Q) = klDiv P Q` when `ω_P(1) = ω_Q(1)`. The integral is the extended
integral `MeasureTheory.erealIntegral`, which is never `-∞` here
(`MeasureTheory.erealIntegral_llr_ne_bot`). For the density vectors themselves no hypothesis
`Q ≪ μ` is needed: `ξ_Q` represents only the `μ`-absolutely continuous part `Q_ac` of `Q`, but
`P ≪ Q ↔ P ≪ Q_ac` and `dP/dQ = dP/dQ_ac` `P`-almost everywhere, because `P` lives where `μ` does
and the singular part of `Q` does not.

The multiplication by `q / p` is first established on the vectors `u` supported where `p` is
bounded below, `q / p` is bounded and `u` is bounded, which are dense among the vectors supported
on `{p > 0}`: there `u = F ξ_P`, the Tomita operator sends `u` to `F̄ ξ_Q = G ξ_P`, and the Tomita
operator of the commutant sends `G ξ_P` to `Ḡ ξ_Q = (q / p) u`, for bounded `F`, `G`. Vectors
vanishing on `{p > 0}` are orthogonal to `M ξ_P` and killed by `Δ`, and the closedness of `Δ`
extends the relation to every `u` with `(q / p) u ∈ L²`. So `Δ` extends `M_{q/p}`, and a
symmetric extension of the self-adjoint `M_{q/p}` is `M_{q/p}` itself (`IsSelfAdjoint.eq_of_le`).

## Main results

* `VonNeumannAlgebra.relativeModular_densityVec_eq_mulPMap` — `Δ_{ξ_Q, ξ_P} = M_{q/p}`;
  `VonNeumannAlgebra.mem_graph_relativeModular_densityVec_iff` — in graph form,
  `(u, v) ∈ graph Δ ↔ (q / p) u ∈ L² ∧ v = (q / p) u`.
* `VonNeumannAlgebra.measure_pvm_relativeModular_densityVec` — for `P ≪ μ` with a Lebesgue
  decomposition, the spectral measure of `Δ_{ξ_Q, ξ_P}` at `ξ_P` is `(q / p)_* P`.
* `VonNeumannAlgebra.arakiVec_densityVec` — `S(ω_{ξ_P} ‖ ω_{ξ_Q}) = ∫ log (dP/dQ) dP` if `P ≪ Q`,
  and `+∞` otherwise, for finite `P ≪ μ` and `Q`;
  `VonNeumannAlgebra.arakiVec_densityVec_eq_klDiv_add_sub` — the same as
  `klDiv P Q + P(α) - Q(α)`.
* `VonNeumannAlgebra.arakiEntropy_ofMeasure` — `S(ω_P ‖ ω_Q) = ∫ log (dP/dQ) dP` if `P ≪ Q`, and
  `+∞` otherwise, for finite `P, Q ≪ μ`;
  `VonNeumannAlgebra.existsUnique_arakiEntropy_ofMeasure` — the same for every pair of normal
  functionals on the multiplication algebra, with unique representing measures `P, Q`.
* `VonNeumannAlgebra.arakiEntropy_ofMeasure_eq_klDiv_add_sub` — the same as
  `klDiv P Q + P(α) - Q(α)`;
  `VonNeumannAlgebra.arakiEntropy_ofMeasure_eq_klDiv` —
  `S(ω_P ‖ ω_Q) = klDiv P Q` when `ω_P(1) = ω_Q(1)`.
-/

@[expose] public section

open ClosedSubmodule MeasureTheory Linfty Complex Filter
open scoped ENNReal InnerProductSpace VonNeumannAlgebra ComplexConjugate Araki
open InnerProductSpace (cyclicSubspace mem_orthogonal_cyclicSubspace_iff)

namespace VonNeumannAlgebra

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-! ### The relative modular operator as a multiplication operator -/

section Modular

variable (P Q : Measure α) [IsFiniteMeasure P] [IsFiniteMeasure Q]

/-- For `n > 0`, `a ≥ 1/n` and `b ≤ n a` give `a > 0`, `1/√a ≤ √n`, `b / a ≤ n` and
`√(b / a) ≤ √n`. -/
private lemma bounds_of_inv_le_of_le_mul {n : ℝ} (hn : 0 < n) {a b : ℝ} (ha : n⁻¹ ≤ a)
    (hb : b ≤ n * a) :
    0 < a ∧ (Real.sqrt a)⁻¹ ≤ Real.sqrt n ∧ b / a ≤ n ∧ Real.sqrt (b / a) ≤ Real.sqrt n := by
  have ha0 : 0 < a := lt_of_lt_of_le (inv_pos.mpr hn) ha
  have hba : b / a ≤ n := by rw [div_le_iff₀ ha0]; linarith
  refine ⟨ha0, ?_, hba, Real.sqrt_le_sqrt hba⟩
  rw [inv_le_comm₀ (Real.sqrt_pos.mpr ha0) (Real.sqrt_pos.mpr hn), ← Real.sqrt_inv]
  exact Real.sqrt_le_sqrt ha

/-- `√(b / a) √b = b / √a`. -/
private lemma sqrt_div_mul_sqrt {a b : ℝ} (hb : 0 ≤ b) :
    Real.sqrt (b / a) * Real.sqrt b = b / Real.sqrt a := by
  rw [Real.sqrt_div hb, div_mul_eq_mul_div, Real.mul_self_sqrt hb]

/-- `√(b / a) √a = √b`. -/
private lemma sqrt_div_mul_sqrt_self {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    Real.sqrt (b / a) * Real.sqrt a = Real.sqrt b := by
  rw [Real.sqrt_div hb, div_mul_cancel₀ _ (Real.sqrt_pos.mpr ha).ne']

variable {P Q}

/-- **`Δ` multiplies by `q / p` on good vectors**: for `u` bounded by `n` on a measurable set `B`
where `p ≥ 1/n` and `q ≤ n p`, and vanishing off `B`, `Δ_{ξ_Q, ξ_P} u = (q / p) u`. -/
private theorem mem_graph_relativeModular_densityVec_of_bounded {B : Set α} (hB : MeasurableSet B) {n : ℝ}
    (hn : 0 < n) (hBp : ∀ x ∈ B, n⁻¹ ≤ densityFun P μ x)
    (hBq : ∀ x ∈ B, densityFun Q μ x ≤ n * densityFun P μ x) {u : Lp ℂ 2 μ}
    (hub : ∀ x ∈ B, ‖u x‖ ≤ n) (hu0 : ∀ᵐ x ∂μ, x ∉ B → u x = 0) {v : Lp ℂ 2 μ}
    (hv : ⇑v =ᵐ[μ] fun x => ((densityFun Q μ x / densityFun P μ x : ℝ) : ℂ) * u x) :
    (u, v) ∈ (Δ[multiplicationAlgebra μ]⟦densityVec Q μ, densityVec P μ⟧).graph := by
  set p := densityFun P μ
  set q := densityFun Q μ
  have hq0 : ∀ x, 0 ≤ q x := fun x => ENNReal.toReal_nonneg
  have hbd : ∀ x ∈ B, 0 < p x ∧ (Real.sqrt (p x))⁻¹ ≤ Real.sqrt n ∧ q x / p x ≤ n ∧
      Real.sqrt (q x / p x) ≤ Real.sqrt n := fun x hx =>
    bounds_of_inv_le_of_le_mul hn (hBp x hx) (hBq x hx)
  have hsn : 0 ≤ Real.sqrt n := Real.sqrt_nonneg n
  have hum : Measurable (⇑u) := (Lp.stronglyMeasurable u).measurable
  have hpm : Measurable p := measurable_densityFun P μ
  have hqm : Measurable q := measurable_densityFun Q μ
  -- the bounded functions `F = u / √p`, `G = F̄ √(q/p)`, `K = (q/p) u / √p`, supported on `B`
  let fF : α → ℂ := B.indicator fun x => u x / (Real.sqrt (p x) : ℂ)
  let fG : α → ℂ := B.indicator fun x =>
    conj (u x / (Real.sqrt (p x) : ℂ)) * (Real.sqrt (q x / p x) : ℂ)
  let fK : α → ℂ := B.indicator fun x => ((q x / p x : ℝ) : ℂ) * u x / (Real.sqrt (p x) : ℂ)
  have hFb : ∀ x, ‖fF x‖ ≤ n * Real.sqrt n := fun x => by
    simp only [fF]
    by_cases hx : x ∈ B
    · obtain ⟨-, h₁, -, -⟩ := hbd x hx
      rw [Set.indicator_of_mem hx, norm_div, norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
        div_eq_mul_inv]
      exact mul_le_mul (hub x hx) h₁ (inv_nonneg.mpr (Real.sqrt_nonneg _)) hn.le
    · rw [Set.indicator_of_notMem hx, norm_zero]
      positivity
  have hGb : ∀ x, ‖fG x‖ ≤ n * Real.sqrt n * Real.sqrt n := fun x => by
    simp only [fG]
    by_cases hx : x ∈ B
    · obtain ⟨-, h₁, -, h₃⟩ := hbd x hx
      rw [Set.indicator_of_mem hx, norm_mul, RCLike.norm_conj, norm_div, norm_real, norm_real,
        Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg (Real.sqrt_nonneg _),
        div_eq_mul_inv]
      exact mul_le_mul (mul_le_mul (hub x hx) h₁ (inv_nonneg.mpr (Real.sqrt_nonneg _)) hn.le) h₃
        (Real.sqrt_nonneg _) (by positivity)
    · rw [Set.indicator_of_notMem hx, norm_zero]
      positivity
  have hKb : ∀ x, ‖fK x‖ ≤ n * n * Real.sqrt n := fun x => by
    simp only [fK]
    by_cases hx : x ∈ B
    · obtain ⟨hp, h₁, h₂, -⟩ := hbd x hx
      rw [Set.indicator_of_mem hx, norm_div, norm_mul, norm_real, norm_real,
        Real.norm_of_nonneg (div_nonneg (hq0 x) hp.le), Real.norm_of_nonneg (Real.sqrt_nonneg _),
        div_eq_mul_inv]
      exact mul_le_mul (mul_le_mul h₂ (hub x hx) (norm_nonneg _) hn.le) h₁
        (inv_nonneg.mpr (Real.sqrt_nonneg _)) (by positivity)
    · rw [Set.indicator_of_notMem hx, norm_zero]
      positivity
  have hFm : Measurable fF := (hum.div (hpm.sqrt.complex_ofReal)).indicator hB
  have hGm : Measurable fG :=
    ((Complex.continuous_conj.measurable.comp (hum.div hpm.sqrt.complex_ofReal)).mul
      ((hqm.div hpm).sqrt.complex_ofReal)).indicator hB
  have hKm : Measurable fK :=
    (((hqm.div hpm).complex_ofReal.mul hum).div hpm.sqrt.complex_ofReal).indicator hB
  set F : Lp ℂ ∞ μ := boundedLinfty fF hFm _ hFb
  set G : Lp ℂ ∞ μ := boundedLinfty fG hGm _ hGb
  set K : Lp ℂ ∞ μ := boundedLinfty fK hKm _ hKb
  have hF := coeFn_boundedLinfty (μ := μ) fF hFm _ hFb
  have hG := coeFn_boundedLinfty (μ := μ) fG hGm _ hGb
  have hK := coeFn_boundedLinfty (μ := μ) fK hKm _ hKb
  set M := multiplicationAlgebra μ
  set ξ := densityVec P μ
  set η := densityVec Q μ
  have hξ : ⇑ξ =ᵐ[μ] fun x => ((Real.sqrt (p x) : ℝ) : ℂ) := coeFn_densityVec P μ
  have hη : ⇑η =ᵐ[μ] fun x => ((Real.sqrt (q x) : ℝ) : ℂ) := coeFn_densityVec Q μ
  -- the identities between the vectors
  have e₁ : mulL2 F ξ = u := Lp.ext <| by
    filter_upwards [coeFn_mulL2 F ξ, hF, hξ, hu0] with x h₁ h₂ h₃ h₄
    rw [h₁, Pi.mul_apply, h₂, h₃]
    by_cases hx : x ∈ B
    · have hs : ((Real.sqrt (p x) : ℝ) : ℂ) ≠ 0 :=
        ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hbd x hx).1).ne'
      simp only [fF, Set.indicator_of_mem hx]
      field_simp
    · simp only [fF, Set.indicator_of_notMem hx, zero_mul, h₄ hx]
  have e₂ : mulL2 (star F) η = mulL2 G ξ := Lp.ext <| by
    filter_upwards [coeFn_mulL2 (star F) η, Lp.coeFn_star F, hF, hη, coeFn_mulL2 G ξ, hG, hξ]
      with x h₁ h₂ h₃ h₄ h₅ h₆ h₇
    rw [h₁, h₅, Pi.mul_apply, Pi.mul_apply, h₂, Pi.star_apply, h₃, h₄, h₆, h₇]
    by_cases hx : x ∈ B
    · simp only [fF, fG, Set.indicator_of_mem hx, mul_assoc, ← ofReal_mul,
        sqrt_div_mul_sqrt_self (hbd x hx).1 (hq0 x)]
      rfl
    · simp only [fF, fG, Set.indicator_of_notMem hx, star_zero, zero_mul]
  have e₃ : mulL2 (star G) η = mulL2 K ξ := Lp.ext <| by
    filter_upwards [coeFn_mulL2 (star G) η, Lp.coeFn_star G, hG, hη, coeFn_mulL2 K ξ, hK, hξ]
      with x h₁ h₂ h₃ h₄ h₅ h₆ h₇
    rw [h₁, h₅, Pi.mul_apply, Pi.mul_apply, h₂, Pi.star_apply, h₃, h₄, h₆, h₇]
    by_cases hx : x ∈ B
    · have hp := (hbd x hx).1
      have hs : ((Real.sqrt (p x) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hp).ne'
      have hpp : ((p x : ℝ) : ℂ) = ((Real.sqrt (p x) : ℝ) : ℂ) ^ 2 := by
        rw [← ofReal_pow, Real.sq_sqrt hp.le]
      simp only [fG, fK, Set.indicator_of_mem hx, star_mul', RCLike.star_def, conj_ofReal,
        Complex.conj_conj]
      rw [mul_assoc, ← ofReal_mul, sqrt_div_mul_sqrt (hq0 x)]
      push_cast
      rw [hpp]
      field_simp
    · simp only [fG, fK, Set.indicator_of_notMem hx, star_zero, zero_mul]
  have e₄ : mulL2 K ξ = v := Lp.ext <| by
    filter_upwards [coeFn_mulL2 K ξ, hK, hξ, hv, hu0] with x h₁ h₂ h₃ h₄ h₅
    rw [h₁, Pi.mul_apply, h₂, h₃, h₄]
    by_cases hx : x ∈ B
    · have hs : ((Real.sqrt (p x) : ℝ) : ℂ) ≠ 0 :=
        ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hbd x hx).1).ne'
      simp only [fK, Set.indicator_of_mem hx]
      field_simp
    · simp only [fK, Set.indicator_of_notMem hx, zero_mul, h₅ hx, mul_zero]
  -- the Tomita operators
  have hS := apply_mem_graph_relativeTomita (M := M) (η := η) (ξ := ξ)
    (mulL2_mem_multiplicationAlgebra F)
  have hs₁ : M.supportProj ξ (mulL2 (star F) η) = mulL2 (star F) η := by
    rw [supportProj, Submodule.starProjection_eq_self_iff, e₂]
    exact InnerProductSpace.apply_mem_cyclicSubspace ξ (mulL2_mem_commutant_multiplicationAlgebra G)
  rw [← map_star, hs₁, e₁, e₂] at hS
  have hFt := apply_mem_graph_relativeTomita (M := M′) (η := η) (ξ := ξ)
    (mulL2_mem_commutant_multiplicationAlgebra G)
  have hs₂ : M′.supportProj ξ (mulL2 (star G) η) = mulL2 (star G) η := by
    rw [supportProj_commutant, Submodule.starProjection_eq_self_iff, e₃]
    exact InnerProductSpace.apply_mem_cyclicSubspace ξ (mulL2_mem_multiplicationAlgebra K)
  rw [← map_star, hs₂, e₃, e₄] at hFt
  rw [mem_graph_relativeModular, LinearPMap.mem_graph_compNat]
  refine ⟨mulL2 G ξ, mem_graph_closure_relativeTomita hS, ?_⟩
  rw [LinearPMap.adjoint_closure (dense_domain_relativeTomita _ _ _)]
  exact LinearPMap.le_graph_of_le (relativeTomita_commutant_le_adjoint _ _ _) hFt

/-- **`Δ` multiplies by `q / p` on good vectors, a.e. form**: for `u` bounded by `n` almost
everywhere on a measurable set `B` where `p ≥ 1/n` and `q ≤ n p`, and vanishing off `B`,
`Δ_{ξ_Q, ξ_P} u = (q / p) u`. -/
private theorem mem_graph_relativeModular_densityVec_of_bounded_ae {B : Set α} (hB : MeasurableSet B)
    {n : ℝ} (hn : 0 < n) (hBp : ∀ x ∈ B, n⁻¹ ≤ densityFun P μ x)
    (hBq : ∀ x ∈ B, densityFun Q μ x ≤ n * densityFun P μ x) {u : Lp ℂ 2 μ}
    (hub : ∀ᵐ x ∂μ, x ∈ B → ‖u x‖ ≤ n) (hu0 : ∀ᵐ x ∂μ, x ∉ B → u x = 0) {v : Lp ℂ 2 μ}
    (hv : ⇑v =ᵐ[μ] fun x => ((densityFun Q μ x / densityFun P μ x : ℝ) : ℂ) * u x) :
    (u, v) ∈ (Δ[multiplicationAlgebra μ]⟦densityVec Q μ, densityVec P μ⟧).graph := by
  have hum : Measurable (⇑u) := (Lp.stronglyMeasurable u).measurable
  refine mem_graph_relativeModular_densityVec_of_bounded (B := B ∩ {x | ‖u x‖ ≤ n})
    (hB.inter (measurableSet_le hum.norm measurable_const)) hn (fun x hx => hBp x hx.1)
    (fun x hx => hBq x hx.1) (fun x hx => hx.2) ?_ hv
  filter_upwards [hub, hu0] with x h₁ h₂ hx
  by_cases hxB : x ∈ B
  · exact absurd ⟨hxB, h₁ hxB⟩ hx
  · exact h₂ hxB

/-- **`Δ` kills the vectors vanishing where `p > 0`**: such a `u` is orthogonal to `M ξ_P`, so
`S_{ξ_Q, ξ_P} u = 0` and `Δ_{ξ_Q, ξ_P} u = 0`. -/
theorem mem_graph_relativeModular_densityVec_zero_of_ae_eq_zero_on_pos {u : Lp ℂ 2 μ}
    (hu : ∀ᵐ x ∂μ, 0 < densityFun P μ x → u x = 0) :
    (u, 0) ∈ (Δ[multiplicationAlgebra μ]⟦densityVec Q μ, densityVec P μ⟧).graph := by
  set p := densityFun P μ
  have hS : MeasurableSet {x | 0 < p x} := measurableSet_lt measurable_const (measurable_densityFun P μ)
  set E := indicatorConst (μ := μ) hS (1 : ℂ)
  set M := multiplicationAlgebra μ
  set ξ := densityVec P μ
  have hE := coeFn_indicatorConst (μ := μ) hS (1 : ℂ)
  have hξ : ⇑ξ =ᵐ[μ] fun x => ((Real.sqrt (p x) : ℝ) : ℂ) := coeFn_densityVec P μ
  have hEξ : mulL2 E ξ = ξ := Lp.ext <| by
    filter_upwards [coeFn_mulL2 E ξ, hE, hξ] with x h₁ h₂ h₃
    rw [h₁, Pi.mul_apply, h₂, h₃]
    by_cases hx : 0 < p x
    · simp [hx]
    · have hp0 : p x = 0 := le_antisymm (not_lt.mp hx) ENNReal.toReal_nonneg
      simp [hp0]
  have hEu : mulL2 E u = 0 := Lp.ext <| by
    filter_upwards [coeFn_mulL2 E u, hE, hu, Lp.coeFn_zero ℂ 2 μ] with x h₁ h₂ h₃ h₄
    rw [h₁, Pi.mul_apply, h₂, h₄]
    by_cases hx : 0 < p x
    · simp [hx, h₃ hx]
    · simp [hx]
  have hEsa : ContinuousLinearMap.adjoint (mulL2 E) = mulL2 E := by
    rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star]
    congr 1
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_star E, hE] with x h₁ h₂
    rw [h₁, Pi.star_apply, h₂]
    by_cases hx : 0 < p x <;> simp [hx]
  have hζ : u ∈ (cyclicSubspace (M : Set (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)) ξ).toSubmoduleᗮ := by
    rw [mem_orthogonal_cyclicSubspace_iff]
    intro T hT
    have hc := congrArg (fun A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ => A ξ) (commute_mulL2_of_mem hT E)
    simp only [mul_apply_eq_comp, hEξ] at hc
    rw [← hc, ← ContinuousLinearMap.adjoint_inner_right, hEsa, hEu, inner_zero_right]
  have hS' := mk_mem_graph_relativeTomita (M := M) (η := densityVec Q μ) (ξ := ξ) (zero_mem M) hζ
  simp only [zero_apply, zero_add, star_zero, map_zero] at hS'
  rw [mem_graph_relativeModular, LinearPMap.mem_graph_compNat]
  exact ⟨0, mem_graph_closure_relativeTomita hS', Submodule.zero_mem _⟩

/-- **The relative modular operator of a multiplication algebra extends multiplication by
`q / p`**: for finite measures `P, Q` with densities `p, q` with respect to `μ`,
`Δ_{ξ_Q, ξ_P} u = (q / p) u` whenever `u` and `(q / p) u` are in `L²`. On `{p = 0}` the multiplier
is `q / 0 = 0`, matching `mem_graph_relativeModular_densityVec_zero_of_ae_eq_zero_on_pos`. There
are no other vectors in the domain (`mem_graph_relativeModular_densityVec_iff`). -/
theorem mem_graph_relativeModular_densityVec_of_memLp {u : Lp ℂ 2 μ}
    (hu : MemLp (fun x => ((densityFun Q μ x / densityFun P μ x : ℝ) : ℂ) * u x) 2 μ) :
    (u, hu.toLp _) ∈
      (Δ[multiplicationAlgebra μ]⟦densityVec Q μ, densityVec P μ⟧).graph := by
  set p := densityFun P μ
  set q := densityFun Q μ
  set Δ := Δ[multiplicationAlgebra μ]⟦densityVec Q μ, densityVec P μ⟧
  set v := hu.toLp _
  have hv : ⇑v =ᵐ[μ] fun x => ((q x / p x : ℝ) : ℂ) * u x := MemLp.coeFn_toLp _
  have hum : Measurable (⇑u) := (Lp.stronglyMeasurable u).measurable
  have hpm : Measurable p := measurable_densityFun P μ
  have hqm : Measurable q := measurable_densityFun Q μ
  have hp0 : ∀ x, 0 ≤ p x := fun x => ENNReal.toReal_nonneg
  set S : Set α := {x | 0 < p x}
  have hS : MeasurableSet S := measurableSet_lt measurable_const hpm
  -- the truncation sets
  let B : ℕ → Set α := fun n =>
    {x | ((n : ℝ) + 1)⁻¹ ≤ p x ∧ q x ≤ ((n : ℝ) + 1) * p x ∧ ‖u x‖ ≤ (n : ℝ) + 1}
  have hB : ∀ n, MeasurableSet (B n) := fun n =>
    (measurableSet_le measurable_const hpm).inter ((measurableSet_le hqm
      (measurable_const.mul hpm)).inter (measurableSet_le hum.norm measurable_const))
  have hBS : ∀ n, B n ⊆ S := fun n x hx =>
    lt_of_lt_of_le (inv_pos.mpr (by positivity)) hx.1
  have hmono : Monotone B := fun n m hnm x hx => by
    have hnm' : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hnm
    refine ⟨(inv_anti₀ (by positivity) hnm').trans hx.1, hx.2.1.trans ?_, hx.2.2.trans hnm'⟩
    exact mul_le_mul_of_nonneg_right hnm' (hp0 x)
  have hcover : S ⊆ ⋃ n, B n := fun x hx => by
    obtain ⟨n, hn⟩ := exists_nat_ge (max (p x)⁻¹ (max (q x / p x) ‖u x‖))
    refine Set.mem_iUnion.mpr ⟨n, ?_, ?_, ?_⟩
    · rw [inv_le_comm₀ (by positivity) hx]
      linarith [le_max_left (p x)⁻¹ (max (q x / p x) ‖u x‖)]
    · have := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
      rw [div_le_iff₀ hx] at this
      nlinarith [hp0 x]
    · linarith [(le_max_right _ _).trans ((le_max_right _ _).trans hn)]
  -- the truncated relations
  have hgraph : ∀ n, (mulL2 (indicatorConst (hB n) (1 : ℂ)) u,
      mulL2 (indicatorConst (hB n) (1 : ℂ)) v) ∈ Δ.graph := fun n => by
    have hI := coeFn_indicatorConst (μ := μ) (hB n) (1 : ℂ)
    refine mem_graph_relativeModular_densityVec_of_bounded_ae (hB n) (by positivity)
      (fun x hx => hx.1) (fun x hx => hx.2.1) ?_ ?_ ?_
    · filter_upwards [coeFn_mulL2 (indicatorConst (hB n) (1 : ℂ)) u, hI] with x h₁ h₂ hx
      rw [h₁, Pi.mul_apply, h₂, Set.indicator_of_mem hx, one_mul]
      exact hx.2.2
    · filter_upwards [coeFn_mulL2 (indicatorConst (hB n) (1 : ℂ)) u, hI] with x h₁ h₂ hx
      rw [h₁, Pi.mul_apply, h₂, Set.indicator_of_notMem hx, zero_mul]
    · filter_upwards [coeFn_mulL2 (indicatorConst (hB n) (1 : ℂ)) v,
        coeFn_mulL2 (indicatorConst (hB n) (1 : ℂ)) u, hI, hv] with x h₁ h₂ h₃ h₄
      rw [h₁, h₂, Pi.mul_apply, Pi.mul_apply, h₃, h₄]
      ring
  -- passing to the limit
  have hvS : mulL2 (indicatorConst hS (1 : ℂ)) v = v := Lp.ext <| by
    filter_upwards [coeFn_mulL2 (indicatorConst hS (1 : ℂ)) v,
      coeFn_indicatorConst (μ := μ) hS (1 : ℂ), hv] with x h₁ h₂ h₃
    rw [h₁, Pi.mul_apply, h₂, h₃]
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, one_mul]
    · have : p x = 0 := le_antisymm (not_lt.mp hx) (hp0 x)
      rw [Set.indicator_of_notMem hx, zero_mul, this, div_zero, ofReal_zero, zero_mul]
  have hlim : (mulL2 (indicatorConst hS (1 : ℂ)) u, v) ∈ Δ.graph := by
    have hc : IsClosed (Δ.graph : Set (Lp ℂ 2 μ × Lp ℂ 2 μ)) :=
      (isSelfAdjoint_relativeModular _ _ _).isClosed
    have ht := (tendsto_mulL2_indicatorConst u hS hB hmono hBS hcover).prodMk_nhds
      (tendsto_mulL2_indicatorConst v hS hB hmono hBS hcover)
    rw [hvS] at ht
    exact hc.mem_of_tendsto ht (Eventually.of_forall hgraph)
  have hnull : (mulL2 (indicatorConst hS.compl (1 : ℂ)) u, 0) ∈ Δ.graph := by
    refine mem_graph_relativeModular_densityVec_zero_of_ae_eq_zero_on_pos ?_
    filter_upwards [coeFn_mulL2 (indicatorConst hS.compl (1 : ℂ)) u,
      coeFn_indicatorConst (μ := μ) hS.compl (1 : ℂ)] with x h₁ h₂ hx
    rw [h₁, Pi.mul_apply, h₂, Set.indicator_of_notMem (by simpa [S] using hx), zero_mul]
  have hsplit :
      u = mulL2 (indicatorConst hS (1 : ℂ)) u + mulL2 (indicatorConst hS.compl (1 : ℂ)) u :=
    Lp.ext <| by
      filter_upwards [Lp.coeFn_add (mulL2 (indicatorConst hS (1 : ℂ)) u)
          (mulL2 (indicatorConst hS.compl (1 : ℂ)) u), coeFn_mulL2 (indicatorConst hS (1 : ℂ)) u,
        coeFn_mulL2 (indicatorConst hS.compl (1 : ℂ)) u, coeFn_indicatorConst (μ := μ) hS (1 : ℂ),
        coeFn_indicatorConst (μ := μ) hS.compl (1 : ℂ)] with x h₁ h₂ h₃ h₄ h₅
      rw [h₁, Pi.add_apply, h₂, h₃, Pi.mul_apply, Pi.mul_apply, h₄, h₅]
      by_cases hx : x ∈ S <;> simp [hx]
  have := Δ.graph.add_mem hlim hnull
  rwa [Prod.mk_add_mk, add_zero, ← hsplit] at this

/-- **The relative modular operator of a multiplication algebra is multiplication by `q / p`**:
for finite measures `P, Q` with densities `p, q` with respect to `μ`, `Δ_{ξ_Q, ξ_P} = M_{q/p}`, the
maximal multiplication operator by `q / p`, with `q / 0 = 0` on `{p = 0}`. The relative modular
operator is self-adjoint, hence symmetric, and extends `M_{q/p}`
(`mem_graph_relativeModular_densityVec_of_memLp`); as `M_{q/p}` is self-adjoint
(`MeasureTheory.L2.isSelfAdjoint_mulPMap`), the two are equal (`IsSelfAdjoint.eq_of_le`). -/
theorem relativeModular_densityVec_eq_mulPMap :
    Δ[multiplicationAlgebra μ]⟦densityVec Q μ, densityVec P μ⟧ =
      L2.mulPMap fun x => ((densityFun Q μ x / densityFun P μ x : ℝ) : ℂ) :=
  (L2.isSelfAdjoint_mulPMap ((measurable_densityFun Q μ).div (measurable_densityFun P μ))).eq_of_le
    (isSelfAdjoint_relativeModular _ _ _).isFormalAdjoint
    (LinearPMap.le_of_le_graph fun ⟨u, v⟩ huv => by
      obtain ⟨hu, hv⟩ := L2.mem_graph_mulPMap.mp huv
      convert mem_graph_relativeModular_densityVec_of_memLp hu
      exact Lp.ext (hv.trans hu.coeFn_toLp.symm))

/-- The graph of the relative modular operator of a multiplication algebra:
`(u, v) ∈ graph Δ_{ξ_Q, ξ_P} ↔ (q / p) u ∈ L² ∧ v = (q / p) u`, with `q / 0 = 0` on `{p = 0}`. -/
theorem mem_graph_relativeModular_densityVec_iff {u v : Lp ℂ 2 μ} :
    (u, v) ∈ (Δ[multiplicationAlgebra μ]⟦densityVec Q μ, densityVec P μ⟧).graph ↔
      MemLp (fun x => ((densityFun Q μ x / densityFun P μ x : ℝ) : ℂ) * u x) 2 μ ∧
        ⇑v =ᵐ[μ] fun x => ((densityFun Q μ x / densityFun P μ x : ℝ) : ℂ) * u x := by
  rw [relativeModular_densityVec_eq_mulPMap]
  exact L2.mem_graph_mulPMap

/-- **Spectral measure**: for finite measures `P, Q` with `P ≪ μ`, the spectral measure of
`Δ_{ξ_Q, ξ_P}` at `ξ_P` is the image of `P` under `q / p`. This needs only a Lebesgue
decomposition of `P` with respect to `μ` (automatic for σ-finite `μ`), so that `|ξ_P|² μ = P`. -/
theorem measure_pvm_relativeModular_densityVec [P.HaveLebesgueDecomposition μ] (hP : P ≪ μ) :
    μ[multiplicationAlgebra μ]⟦densityVec Q μ, densityVec P μ⟧ =
      P.map fun x => densityFun Q μ x / densityFun P μ x := by
  have hh := (measurable_densityFun Q μ).div (measurable_densityFun P μ)
  unfold relativeModularMeasure
  rw [IsSelfAdjoint.pvm_congr _ (L2.isSelfAdjoint_mulPMap hh)
    relativeModular_densityVec_eq_mulPMap, L2.measure_pvm_mulPMap hh,
    withDensity_enorm_sq_densityVec P hP]
  rfl

/-! ### Araki's relative entropy -/

variable [SigmaFinite μ] in
/-- **Araki's relative entropy of density vectors**: for σ-finite `μ` and finite measures `P ≪ μ`
and `Q`, `S(ω_{ξ_P} ‖ ω_{ξ_Q}) = ∫ log (dP/dQ) dP` if `P ≪ Q`, and `+∞` otherwise, with the
natural logarithm. No hypothesis on `Q` beyond finiteness is needed: `ξ_Q` represents only the
`μ`-absolutely continuous part `Q_ac` of `Q`, but `P ≪ Q ↔ P ≪ Q_ac` and `dP/dQ = dP/dQ_ac`
`P`-almost everywhere, because `P ≪ μ` and the singular part of `Q` lives on a `μ`-null set. The
integral is the extended integral `∫⁻ (llr P Q)⁺ dP - ∫⁻ (llr P Q)⁻ dP`, whose negative part is
finite for finite `Q`, so the value is never `⊥` (`MeasureTheory.erealIntegral_llr_ne_bot`). This
is the Kullback–Leibler divergence without Mathlib's mass correction `Q(α) - P(α)`; see
`VonNeumannAlgebra.arakiVec_densityVec_eq_klDiv_add_sub` for the comparison with
`InformationTheory.klDiv`. -/
theorem arakiVec_densityVec (hP : P ≪ μ) [Decidable (P ≪ Q)] :
    (multiplicationAlgebra μ).arakiVec (densityVec P μ) (densityVec Q μ) =
      if P ≪ Q then erealIntegral P (fun x => (llr P Q x : EReal)) else ⊤ := by
  have hne := arakiVec_ne_bot (multiplicationAlgebra μ) (densityVec P μ) (densityVec Q μ)
  rw [arakiVec, measure_pvm_relativeModular_densityVec hP] at hne ⊢
  set p := densityFun P μ
  set q := densityFun Q μ
  have hpm : Measurable p := measurable_densityFun P μ
  have hqm : Measurable q := measurable_densityFun Q μ
  have hhm : Measurable fun x => q x / p x := hqm.div hpm
  have hq0 : ∀ x, 0 ≤ q x := fun x => ENNReal.toReal_nonneg
  split_ifs with hPQ
  · rw [negLogIntegral, erealIntegral_map (f := fun t : ℝ => -ENNReal.log (ENNReal.ofReal t))
      hhm.aemeasurable (ENNReal.measurable_log.comp ENNReal.measurable_ofReal).neg.aemeasurable]
    refine erealIntegral_congr_ae ?_
    filter_upwards [Measure.rnDeriv_pos hP, hP.ae_le (Measure.rnDeriv_lt_top P μ),
      hP.ae_le (Measure.rnDeriv_lt_top Q μ),
      hP.ae_le (Measure.rnDeriv_mul_rnDeriv (κ := μ) hPQ)] with x hp₁ hp₂ hq₂ hc
    -- `dP/dQ · dQ/dμ = dP/dμ > 0`, so `dQ/dμ > 0` wherever `P` lives
    have hq₁ : 0 < Q.rnDeriv μ x := by
      refine pos_iff_ne_zero.mpr fun h0 => hp₁.ne' ?_
      rw [← hc, Pi.mul_apply, h0, mul_zero]
    have hpx : 0 < p x := ENNReal.toReal_pos hp₁.ne' hp₂.ne
    have hqx : 0 < q x := ENNReal.toReal_pos hq₁.ne' hq₂.ne
    have hcx : P.rnDeriv Q x = P.rnDeriv μ x / Q.rnDeriv μ x :=
      (ENNReal.eq_div_iff hq₁.ne' hq₂.ne).mpr (by rw [mul_comm]; exact hc)
    simp only [Function.comp_apply, llr_def]
    rw [ENNReal.log_ofReal_of_pos (div_pos hqx hpx), hcx, ENNReal.toReal_div, ← inv_div,
      Real.log_inv, EReal.coe_neg, neg_neg]
  · refine negLogIntegral_eq_top_of_measure_Iic_ne_zero ?_ hne
    rw [Measure.map_apply hhm measurableSet_Iic]
    intro hzero
    apply hPQ
    refine Measure.AbsolutelyContinuous.mk fun s hs hQs => ?_
    have hint : ∫⁻ x in s, Q.rnDeriv μ x ∂μ = 0 := by
      rw [← withDensity_apply _ hs]
      exact nonpos_iff_eq_zero.mp
        ((Measure.le_iff'.mp (Measure.withDensity_rnDeriv_le Q μ) s).trans_eq hQs)
    have hae := (ae_restrict_iff' hs).mp
      ((lintegral_eq_zero_iff (Measure.measurable_rnDeriv Q μ)).mp hint)
    have hnull : μ (s ∩ {x | 0 < q x / p x}) = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hae] with x hx hmem
      have hq : q x = 0 := by
        change (Q.rnDeriv μ x).toReal = 0
        rw [hx hmem.1, Pi.zero_apply, ENNReal.toReal_zero]
      have := hmem.2
      rw [Set.mem_ofPred_eq, hq, zero_div] at this
      exact lt_irrefl 0 this
    have hsplit : s ⊆ ((fun x => q x / p x) ⁻¹' Set.Iic 0) ∪ (s ∩ {x | 0 < q x / p x}) :=
      fun x hx => by
        by_cases h : q x / p x ≤ 0
        · exact Or.inl h
        · exact Or.inr ⟨hx, not_le.mp h⟩
    exact measure_mono_null hsplit (measure_union_null hzero (hP hnull))

variable [SigmaFinite μ] in
/-- **Araki = Kullback–Leibler** for density vectors, in terms of Mathlib's
`InformationTheory.klDiv`: for finite measures `P ≪ μ` and `Q`,
`S(ω_{ξ_P} ‖ ω_{ξ_Q}) = klDiv P Q + P(α) - Q(α)`. The term `P(α) - Q(α)` cancels the mass
correction `Q(α) - P(α)` built into `klDiv`, which Araki's relative entropy does not carry. Here
`Q(α)` is the full mass of `Q`, including its `μ`-singular part, which may exceed the mass
`‖ξ_Q‖² = Q_ac(α)` of the functional `ω_{ξ_Q}`. -/
theorem arakiVec_densityVec_eq_klDiv_add_sub (hP : P ≪ μ) :
    (multiplicationAlgebra μ).arakiVec (densityVec P μ) (densityVec Q μ) =
      (InformationTheory.klDiv P Q : EReal) + P.real Set.univ - Q.real Set.univ := by
  classical
  rw [arakiVec_densityVec hP]
  by_cases hPQ : P ≪ Q
  · rw [ite_eq_left hPQ]
    by_cases hint : Integrable (llr P Q) P
    · rw [erealIntegral_coe hint, InformationTheory.klDiv_of_ac_of_integrable hPQ hint,
        EReal.coe_ennreal_ofReal,
        max_eq_left (InformationTheory.integral_llr_add_sub_measure_univ_nonneg hPQ hint),
        ← EReal.coe_add, ← EReal.coe_sub]
      congr 1
      ring
    · rw [InformationTheory.klDiv_of_not_integrable hint, EReal.coe_ennreal_top,
        erealIntegral_llr_eq_top hPQ hint, EReal.top_add_coe, EReal.top_sub_coe]
  · rw [ite_eq_right hPQ, InformationTheory.klDiv_of_not_ac hPQ, EReal.coe_ennreal_top,
      EReal.top_add_coe, EReal.top_sub_coe]

variable [SigmaFinite μ] in
/-- **Araki = Kullback–Leibler** on the multiplication algebra: for finite measures `P, Q ≪ μ`, the
relative entropy of their normal functionals `ω_P : M_f ↦ ∫ f dP` and `ω_Q : M_f ↦ ∫ f dQ` is
`S(ω_P ‖ ω_Q) = ∫ log (dP/dQ) dP` if `P ≪ Q`, and `+∞` otherwise, with the natural logarithm. Every
normal functional is some `ω_P` (`VonNeumannAlgebra.existsUnique_eq_ofMeasure`). This is the
Kullback–Leibler divergence without Mathlib's mass correction `Q(α) - P(α)`; see
`VonNeumannAlgebra.arakiEntropy_ofMeasure_eq_klDiv_add_sub` for the comparison with
`InformationTheory.klDiv`. -/
theorem arakiEntropy_ofMeasure (hP : P ≪ μ) (hQ : Q ≪ μ) [Decidable (P ≪ Q)] :
    S⟦NormalFunctional.ofMeasure P hP ∥ NormalFunctional.ofMeasure Q hQ⟧ =
      if P ≪ Q then erealIntegral P (fun x => (llr P Q x : EReal)) else ⊤ := by
  rw [NormalFunctional.ofMeasure_eq_ofVector, NormalFunctional.ofMeasure_eq_ofVector,
    arakiEntropy_ofVector, arakiVec_densityVec hP]

variable [SigmaFinite μ] in
/-- **Araki = Mathlib's Kullback–Leibler divergence** on the multiplication algebra: for finite
measures `P, Q ≪ μ`, `S(ω_P ‖ ω_Q) = klDiv P Q + P(α) - Q(α)`. The term `P(α) - Q(α)` cancels the
mass correction `Q(α) - P(α)` built into `klDiv`. -/
theorem arakiEntropy_ofMeasure_eq_klDiv_add_sub (hP : P ≪ μ) (hQ : Q ≪ μ) :
    S⟦NormalFunctional.ofMeasure P hP ∥ NormalFunctional.ofMeasure Q hQ⟧ =
      (InformationTheory.klDiv P Q : EReal) + P.real Set.univ - Q.real Set.univ := by
  rw [NormalFunctional.ofMeasure_eq_ofVector, NormalFunctional.ofMeasure_eq_ofVector,
    arakiEntropy_ofVector, arakiVec_densityVec_eq_klDiv_add_sub hP]

variable [SigmaFinite μ] in
/-- **Araki = Kullback–Leibler** for normal functionals of equal mass `ω_P(1) = ω_Q(1)`, i.e.
`P(α) = Q(α)` (`VonNeumannAlgebra.NormalFunctional.ofMeasure_apply_one`):
`S(ω_P ‖ ω_Q) = klDiv P Q`. -/
theorem arakiEntropy_ofMeasure_eq_klDiv (hP : P ≪ μ) (hQ : Q ≪ μ)
    (hmass : (NormalFunctional.ofMeasure P hP).1 1 = (NormalFunctional.ofMeasure Q hQ).1 1) :
    S⟦NormalFunctional.ofMeasure P hP ∥ NormalFunctional.ofMeasure Q hQ⟧ =
      InformationTheory.klDiv P Q := by
  rw [NormalFunctional.ofMeasure_apply_one, NormalFunctional.ofMeasure_apply_one,
    ofReal_inj] at hmass
  rw [arakiEntropy_ofMeasure_eq_klDiv_add_sub hP hQ, hmass]
  exact EReal.add_sub_cancel_right

end Modular

variable [SigmaFinite μ] in
/-- **Araki = Kullback–Leibler for every pair of normal functionals** on the multiplication
algebra: `ψ = ω_P` and `φ = ω_Q` for unique finite measures `P, Q ≪ μ`
(`VonNeumannAlgebra.existsUnique_eq_ofMeasure`), and for these
`S(ψ ‖ φ) = ∫ log (dP/dQ) dP` if `P ≪ Q`, and `+∞` otherwise
(`VonNeumannAlgebra.arakiEntropy_ofMeasure`). -/
theorem existsUnique_arakiEntropy_ofMeasure (ψ φ : (multiplicationAlgebra μ).NormalFunctional) :
    (∃! P : Measure α, ∃ (_ : IsFiniteMeasure P) (hP : P ≪ μ), ψ = NormalFunctional.ofMeasure P hP) ∧
      (∃! Q : Measure α, ∃ (_ : IsFiniteMeasure Q) (hQ : Q ≪ μ),
        φ = NormalFunctional.ofMeasure Q hQ) ∧
      ∀ (P Q : Measure α) [IsFiniteMeasure P] [IsFiniteMeasure Q] (hP : P ≪ μ) (hQ : Q ≪ μ)
        [Decidable (P ≪ Q)], ψ = NormalFunctional.ofMeasure P hP →
          φ = NormalFunctional.ofMeasure Q hQ →
            S⟦ψ ∥ φ⟧ = if P ≪ Q then erealIntegral P (fun x => (llr P Q x : EReal)) else ⊤ := by
  refine ⟨existsUnique_eq_ofMeasure ψ, existsUnique_eq_ofMeasure φ, ?_⟩
  rintro P Q _ _ hP hQ _ rfl rfl
  exact arakiEntropy_ofMeasure hP hQ

end VonNeumannAlgebra
