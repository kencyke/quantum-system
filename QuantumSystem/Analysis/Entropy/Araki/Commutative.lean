/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Algebra.VonNeumannAlgebra.Diagonal
public import QuantumSystem.Analysis.Entropy.Araki.Basic

/-!
# Araki's relative entropy on a commutative algebra: Kullback–Leibler

On the diagonal algebra `ℓ^∞(ι)` acting on `ℓ²(ι)` (`VonNeumannAlgebra.diagonalAlgebra`), the vector
`ξ_p = Σᵢ √pᵢ eᵢ` represents the weight `x ↦ Σᵢ pᵢ xᵢᵢ`. For strictly positive weights `p, q`, the
relative modular operator `Δ_{ξ_q, ξ_p}` is diagonal with eigenvalue `qᵢ / pᵢ` on `eᵢ`, its spectral
measure at `ξ_p` is `Σᵢ pᵢ δ_{qᵢ/pᵢ}`, and Araki's relative entropy is the **Kullback–Leibler
divergence**
`S(ω_{ξ_p} ‖ ω_{ξ_q}) = Σᵢ pᵢ log (pᵢ / qᵢ)`.

This is a witness, not API: it pins what the general lemmas of
`QuantumSystem.Analysis.Entropy.Araki.Vector` cannot, namely the argument order and the shape
`p log (p / q)` of `VonNeumannAlgebra.arakiVec` beyond scalars and supports. The first argument is
the weight being measured, the second the reference; for `p = (½, ½)` and `q = (¼, ¾)` the two
orders give different values.

## Main results

* `VonNeumannAlgebra.mem_graph_relativeModular_diagonalVec` — `Δ_{ξ_q, ξ_p} eᵢ = (qᵢ / pᵢ) eᵢ`.
* `VonNeumannAlgebra.spectralMeasure_relativeModular_diagonalVec` — `μ_{ξ_p} = Σᵢ pᵢ δ_{qᵢ/pᵢ}`.
* `VonNeumannAlgebra.arakiVec_diagonalVec`, `VonNeumannAlgebra.arakiEntropy_diagonalVec` —
  `S(ω_{ξ_p} ‖ ω_{ξ_q}) = Σᵢ pᵢ log (pᵢ / qᵢ)`.
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

/-- For strictly positive weights, every basis vector lies in the cyclic subspace generated from
`ξ_r` by any von Neumann algebra containing the coordinate projections. -/
lemma single_mem_cyclicSubspace_diagonalVec (N : VonNeumannAlgebra (ℓ²(ι, ℂ)))
    (hN : ∀ i, coordProjection i ∈ N) {r : ι → ℝ} (hr : ∀ i, 0 < r i) (i : ι) :
    lp.single 2 i (1 : ℂ) ∈
      (cyclicSubspace (N : Set (ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ))) (diagonalVec r)).toSubmodule := by
  have h := Submodule.smul_mem _ (((Real.sqrt (r i) : ℝ) : ℂ)⁻¹)
    (InnerProductSpace.apply_mem_cyclicSubspace (diagonalVec r) (hN i))
  rwa [coordProjection_diagonalVec, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast (Real.sqrt_pos.mpr (hr i)).ne'), one_smul] at h

/-- For strictly positive weights, `s(ξ_r) = 1` on the basis vectors. -/
lemma supportProj_diagonalVec_single {r : ι → ℝ} (hr : ∀ i, 0 < r i) (i : ι) :
    (diagonalAlgebra ι).supportProj (diagonalVec r) (lp.single 2 i (1 : ℂ)) =
      lp.single 2 i (1 : ℂ) := by
  rw [supportProj, Submodule.starProjection_eq_self_iff]
  exact single_mem_cyclicSubspace_diagonalVec _ coordProjection_mem_commutant hr i

/-- For strictly positive weights, `s′(ξ_r) = 1` on the basis vectors. -/
lemma supportProj_commutant_diagonalVec_single {r : ι → ℝ} (hr : ∀ i, 0 < r i) (i : ι) :
    (diagonalAlgebra ι)′.supportProj (diagonalVec r) (lp.single 2 i (1 : ℂ)) =
      lp.single 2 i (1 : ℂ) := by
  rw [supportProj_commutant, Submodule.starProjection_eq_self_iff]
  exact single_mem_cyclicSubspace_diagonalVec _ coordProjection_mem hr i

variable {p q : ι → ℝ}

/-- The relative Tomita operator of `M` sends `√pᵢ eᵢ` to `√qᵢ eᵢ`. -/
private lemma mem_graph_relativeTomita_diagonalVec (hp : ∀ i, 0 < p i) (i : ι) :
    (((Real.sqrt (p i) : ℝ) : ℂ) • lp.single 2 i (1 : ℂ),
        ((Real.sqrt (q i) : ℝ) : ℂ) • lp.single 2 i (1 : ℂ)) ∈
      ((diagonalAlgebra ι).relativeTomita (diagonalVec q) (diagonalVec p)).graph := by
  have h := apply_mem_graph_relativeTomita (η := diagonalVec q) (ξ := diagonalVec p)
    (coordProjection_mem i)
  rwa [coordProjection_diagonalVec, star_coordProjection, coordProjection_diagonalVec, map_smul,
    supportProj_diagonalVec_single hp] at h

/-- The relative Tomita operator of `M′` sends `√pᵢ eᵢ` to `√qᵢ eᵢ`. -/
private lemma mem_graph_relativeTomita_commutant_diagonalVec (hp : ∀ i, 0 < p i) (i : ι) :
    (((Real.sqrt (p i) : ℝ) : ℂ) • lp.single 2 i (1 : ℂ),
        ((Real.sqrt (q i) : ℝ) : ℂ) • lp.single 2 i (1 : ℂ)) ∈
      ((diagonalAlgebra ι)′.relativeTomita (diagonalVec q) (diagonalVec p)).graph := by
  have h := apply_mem_graph_relativeTomita (M := (diagonalAlgebra ι)′) (η := diagonalVec q)
    (ξ := diagonalVec p) (coordProjection_mem_commutant i)
  rwa [coordProjection_diagonalVec, star_coordProjection, coordProjection_diagonalVec, map_smul,
    supportProj_commutant_diagonalVec_single hp] at h

/-- **The relative modular operator is diagonal**: `Δ_{ξ_q, ξ_p} eᵢ = (qᵢ / pᵢ) eᵢ`. -/
theorem mem_graph_relativeModular_diagonalVec (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) (i : ι) :
    (lp.single 2 i (1 : ℂ), ((q i / p i : ℝ) : ℂ) • lp.single 2 i (1 : ℂ)) ∈
      ((diagonalAlgebra ι).relativeModular (diagonalVec q) (diagonalVec p)).graph := by
  have hpi := (Real.sqrt_pos.mpr (hp i)).ne'
  have hpp := Real.mul_self_sqrt (hp i).le
  have hqq := Real.mul_self_sqrt (hq i).le
  rw [mem_graph_relativeModular, LinearPMap.mem_graph_compNat]
  refine ⟨((Real.sqrt (q i) / Real.sqrt (p i) : ℝ) : ℂ) • lp.single 2 i (1 : ℂ), ?_, ?_⟩
  · refine mem_graph_closure_relativeTomita ?_
    have h := ofReal_smul_mem_graph (mem_graph_relativeTomita_diagonalVec (q := q) hp i)
      (Real.sqrt (p i))⁻¹
    rwa [smul_smul, smul_smul, ← Complex.ofReal_mul, ← Complex.ofReal_mul, inv_mul_cancel₀ hpi,
      Complex.ofReal_one, one_smul, inv_mul_eq_div] at h
  · rw [LinearPMap.adjoint_closure (dense_domain_relativeTomita _ _ _)]
    refine LinearPMap.le_graph_of_le (relativeTomita_commutant_le_adjoint _ _ _) ?_
    have h := ofReal_smul_mem_graph (mem_graph_relativeTomita_commutant_diagonalVec (q := q) hp i)
      (Real.sqrt (q i) / p i)
    have c₁ : Real.sqrt (q i) / p i * Real.sqrt (p i) = Real.sqrt (q i) / Real.sqrt (p i) := by
      rw [div_mul_eq_mul_div, div_eq_div_iff (hp i).ne' hpi]
      linear_combination Real.sqrt (q i) * hpp
    have c₂ : Real.sqrt (q i) / p i * Real.sqrt (q i) = q i / p i := by
      rw [div_mul_eq_mul_div, div_eq_div_iff (hp i).ne' (hp i).ne']
      linear_combination p i * hqq
    rwa [smul_smul, smul_smul, ← Complex.ofReal_mul, ← Complex.ofReal_mul, c₁, c₂] at h

/-- **Spectral measure**: `μ_{ξ_p}` of `Δ_{ξ_q, ξ_p}` is `Σᵢ pᵢ δ_{qᵢ/pᵢ}`. -/
theorem spectralMeasure_relativeModular_diagonalVec (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    (isSelfAdjoint_relativeModular (diagonalAlgebra ι) (diagonalVec q) (diagonalVec p)).spectralMeasure
        (diagonalVec p) =
      ∑ i, (p i).toNNReal • Measure.dirac (q i / p i) := by
  have hnorm : ∀ i, ‖((Real.sqrt (p i) : ℝ) : ℂ) • lp.single (E := fun _ : ι => ℂ) 2 i (1 : ℂ)‖₊ ^ 2 =
      (p i).toNNReal := fun i => by
    ext
    rw [Real.coe_toNNReal _ (hp i).le, NNReal.coe_pow, coe_nnnorm, norm_smul,
      lp.norm_single_one two_pos, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hp i).le]
  simp_rw [← hnorm]
  conv_lhs => rw [diagonalVec]
  refine IsSelfAdjoint.spectralMeasure_sum_of_mem_graph _ Finset.univ
    (x := fun i => ((Real.sqrt (p i) : ℝ) : ℂ) • lp.single 2 i (1 : ℂ))
    (c := fun i => q i / p i) (fun i _ => ?_) (fun i _ j _ hij => ?_)
  · have := ((diagonalAlgebra ι).relativeModular (diagonalVec q) (diagonalVec p)).graph.smul_mem
      ((Real.sqrt (p i) : ℝ) : ℂ) (mem_graph_relativeModular_diagonalVec hp hq i)
    rwa [Prod.smul_mk, smul_comm] at this
  · simp [lp.inner_single_left, hij]

/-- **Araki = Kullback–Leibler.** On the diagonal algebra, for strictly positive weights,
`S(ω_{ξ_p} ‖ ω_{ξ_q}) = Σᵢ pᵢ log (pᵢ / qᵢ)`. -/
theorem arakiVec_diagonalVec (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    (diagonalAlgebra ι).arakiVec (diagonalVec p) (diagonalVec q) =
      ((∑ i, p i * Real.log (p i / q i) : ℝ) : EReal) := by
  rw [arakiVec, spectralMeasure_relativeModular_diagonalVec hp hq,
    negLogIntegral_finsetSum_smul_dirac _ _ (fun i _ _ => div_pos (hq i) (hp i))]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.coe_toNNReal _ (hp i).le, Real.log_div (hq i).ne' (hp i).ne', Real.log_div (hp i).ne' (hq i).ne']
  ring

/-- **Araki = Kullback–Leibler**, for the normal functionals `ω_{ξ_p}` and `ω_{ξ_q}`. -/
theorem arakiEntropy_diagonalVec (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    (diagonalAlgebra ι).arakiEntropy (NormalFunctional.ofVector _ (diagonalVec p))
        (NormalFunctional.ofVector _ (diagonalVec q)) =
      ((∑ i, p i * Real.log (p i / q i) : ℝ) : EReal) := by
  rw [arakiEntropy_ofVector, arakiVec_diagonalVec hp hq]

end VonNeumannAlgebra
