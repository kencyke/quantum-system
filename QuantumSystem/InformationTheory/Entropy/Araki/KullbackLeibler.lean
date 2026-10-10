/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.ForMathlib.MeasureTheory.Measure.Count
public import QuantumSystem.InformationTheory.Entropy.Araki.Multiplication

/-!
# Araki's relative entropy on a finite diagonal algebra: Kullback–Leibler

On the diagonal algebra `ℓ^∞(ι) = L∞(ι, count)` of a finite type `ι`, acting on
`ℓ²(ι) = L²(ι, count)` (`VonNeumannAlgebra.multiplicationAlgebra`), a finite measure `P = Σᵢ pᵢ δᵢ`
is represented by the vector `ξ_P = Σᵢ √pᵢ eᵢ` (`VonNeumannAlgebra.densityVec`), where
`pᵢ = P {i}` and `eᵢ = 1_{{i}}`. The relative modular operator `Δ_{ξ_Q, ξ_P}` has eigenvalue
`qᵢ / pᵢ` on `eᵢ`, its spectral measure at `ξ_P` is `Σᵢ pᵢ δ_{qᵢ/pᵢ}`, and Araki's relative entropy
is the **Kullback–Leibler divergence**
`S(ω_P ‖ ω_Q) = Σᵢ pᵢ log (pᵢ / qᵢ)` if `P ≪ Q`, and `+∞` otherwise.

The measures are not normalised, and Araki's convention carries no mass correction: the value is
`Σᵢ pᵢ log (pᵢ / qᵢ)`, not `Σᵢ pᵢ log (pᵢ / qᵢ) + Q(ι) - P(ι)`; it is
`InformationTheory.klDivEReal P Q` (`QuantumSystem.InformationTheory.KullbackLeibler.EReal`). For
measures of equal total mass it coincides with Mathlib's `InformationTheory.klDiv P Q`
(`VonNeumannAlgebra.arakiEntropy_ofMeasure_eq_klDiv`).

These results pin what the general lemmas of `QuantumSystem.InformationTheory.Entropy.Araki.VectorFunctional`
cannot, namely the argument order and the shape `p log (p / q)` of `VonNeumannAlgebra.arakiVec`
beyond scalars and supports. The first argument is the measure being measured, the second the
reference; for `P = (½, ½)` and `Q = (¼, ¾)` the two orders give different values.

The results are not computed afresh: they are the case of counting measure on `ι` of
`QuantumSystem.InformationTheory.Entropy.Araki.Multiplication`, which treats the multiplication algebra
`L∞(μ)` of a σ-finite measure `μ`. Every measure is absolutely continuous with respect to counting
measure (`MeasureTheory.Measure.absolutelyContinuous_count`), and the density `dP/d count` is the
mass function `i ↦ P {i}` (`MeasureTheory.Measure.rnDeriv_count`).

## Main results

* `VonNeumannAlgebra.densityFun_count` — `dP/d count (i) = P {i}`.
* `VonNeumannAlgebra.mem_graph_relativeModular_densityVec_single` — `Δ_{ξ_Q, ξ_P} eᵢ = (qᵢ / pᵢ) eᵢ`.
* `VonNeumannAlgebra.measure_pvm_relativeModular_densityVec_fintype` —
  `μ_{ξ_P} = Σᵢ pᵢ δ_{qᵢ/pᵢ}`.
* `VonNeumannAlgebra.arakiVec_densityVec_fintype`, `VonNeumannAlgebra.arakiEntropy_ofMeasure_fintype`
  — `S(ω_P ‖ ω_Q) = Σᵢ pᵢ log (pᵢ / qᵢ)` if `P ≪ Q`, and `+∞` otherwise.
-/

@[expose] public section

open MeasureTheory Linfty
open scoped ENNReal InnerProductSpace VonNeumannAlgebra Araki

namespace VonNeumannAlgebra

variable {ι : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {P Q : Measure ι} [IsFiniteMeasure P] [IsFiniteMeasure Q]

section Finite

variable [Finite ι]

/-- The density of `P` with respect to counting measure is the mass function `i ↦ P {i}`. -/
theorem densityFun_count (P : Measure ι) (i : ι) : densityFun P Measure.count i = P.real {i} := by
  rw [densityFun, measureReal_def, Measure.ae_count_iff.mp (Measure.rnDeriv_count P) i]

/-- **The relative modular operator is diagonal**: `Δ_{ξ_Q, ξ_P} eᵢ = (qᵢ / pᵢ) eᵢ` for
`eᵢ = 1_{{i}}`, `pᵢ = P {i}` and `qᵢ = Q {i}`. When `pᵢ = 0`, the value `qᵢ / 0 = 0` is the genuine
one: `Δ = M_{q/p}` with `q / 0 = 0` (`VonNeumannAlgebra.relativeModular_densityVec_eq_mulPMap`). -/
theorem mem_graph_relativeModular_densityVec_single (i : ι) :
    (indicatorConstLp 2 (measurableSet_singleton i) (measure_ne_top _ _) (1 : ℂ),
      ((Q.real {i} / P.real {i} : ℝ) : ℂ) •
        indicatorConstLp 2 (measurableSet_singleton i) (measure_ne_top _ _) (1 : ℂ)) ∈
      (Δ[multiplicationAlgebra Measure.count]⟦densityVec Q Measure.count,
        densityVec P Measure.count⟧).graph := by
  rw [relativeModular_densityVec_eq_mulPMap]
  refine L2.mem_graph_mulPMap.mpr ⟨MemLp.of_discrete, ?_⟩
  refine Measure.ae_count_iff.mpr fun j => ?_
  simp only [Measure.ae_count_iff.mp (Lp.coeFn_smul _ _) j, Pi.smul_apply,
    Measure.ae_count_iff.mp (indicatorConstLp_coeFn (p := 2) (hs := measurableSet_singleton i)
      (hμs := measure_ne_top _ _) (c := (1 : ℂ))) j, densityFun_count, smul_eq_mul]
  by_cases hji : j = i
  · subst hji
    simp
  · simp [hji]

end Finite

variable [Fintype ι]

/-- **Spectral measure**: `μ_{ξ_P}` of `Δ_{ξ_Q, ξ_P}` is `Σᵢ pᵢ δ_{qᵢ/pᵢ}`. (A term with `pᵢ = 0`
carries no mass, whatever its junk location `qᵢ / 0 = 0`.) This is the image `(q / p)_* P` of
`VonNeumannAlgebra.measure_pvm_relativeModular_densityVec`. -/
theorem measure_pvm_relativeModular_densityVec_fintype :
    μ[multiplicationAlgebra Measure.count]⟦densityVec Q Measure.count,
        densityVec P Measure.count⟧ =
      ∑ i, P {i} • Measure.dirac (Q.real {i} / P.real {i}) := by
  rw [measure_pvm_relativeModular_densityVec (Measure.absolutelyContinuous_count P)]
  simp_rw [densityFun_count]
  set f : ι → ℝ := fun x => Q.real {x} / P.real {x}
  calc Measure.map f P = Measure.mapₗ f (∑ i, P {i} • Measure.dirac i) := by
        rw [Measure.mapₗ_apply_of_measurable Measurable.of_discrete, ← Measure.sum_fintype,
          Measure.sum_smul_dirac]
    _ = ∑ i, P {i} • Measure.dirac (f i) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [LinearMap.map_smul, Measure.mapₗ_apply_of_measurable Measurable.of_discrete,
          Measure.map_dirac' Measurable.of_discrete]

/-- **Araki = Kullback–Leibler.** On the diagonal algebra of a finite type,
`S(ω_{ξ_P} ‖ ω_{ξ_Q}) = Σᵢ pᵢ log (pᵢ / qᵢ)` if `P ≪ Q`, and `+∞` otherwise, with `pᵢ = P {i}` and
`qᵢ = Q {i}`: the Kullback–Leibler divergence `InformationTheory.klDivEReal P Q` of unnormalised
measures in Araki's convention, with no mass correction `Q(ι) - P(ι)`
(`InformationTheory.klDivEReal_of_fintype`); for equal total masses it is Mathlib's
`InformationTheory.klDiv` (`VonNeumannAlgebra.arakiEntropy_ofMeasure_eq_klDiv`). A term with
`pᵢ = 0` contributes `0`. It is `VonNeumannAlgebra.arakiVec_densityVec` for counting measure on
`ι`. -/
theorem arakiVec_densityVec_fintype [Decidable (P ≪ Q)] :
    S[multiplicationAlgebra Measure.count]⟦densityVec P Measure.count ∥
        densityVec Q Measure.count⟧ =
      if P ≪ Q then ((∑ i, P.real {i} * Real.log (P.real {i} / Q.real {i}) : ℝ) : EReal)
      else ⊤ := by
  rw [arakiVec_densityVec (Measure.absolutelyContinuous_count P),
    InformationTheory.klDivEReal_of_fintype]

/-- **Araki = Kullback–Leibler**, for the normal functionals `ω_P` and `ω_Q` of finite measures on
a finite type: `Σᵢ pᵢ log (pᵢ / qᵢ)` if `P ≪ Q`, and `+∞` otherwise. -/
theorem arakiEntropy_ofMeasure_fintype [Decidable (P ≪ Q)] :
    S⟦NormalFunctional.ofMeasure P (Measure.absolutelyContinuous_count P) ∥
        NormalFunctional.ofMeasure Q (Measure.absolutelyContinuous_count Q)⟧ =
      if P ≪ Q then ((∑ i, P.real {i} * Real.log (P.real {i} / Q.real {i}) : ℝ) : EReal)
      else ⊤ := by
  rw [NormalFunctional.ofMeasure_eq_ofVector, NormalFunctional.ofMeasure_eq_ofVector,
    arakiEntropy_ofVector, arakiVec_densityVec_fintype]

end VonNeumannAlgebra
