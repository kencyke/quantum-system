/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.InnerProductSpace.Trace
public import QuantumSystem.Analysis.Entropy.Araki.Basic
public import QuantumSystem.Analysis.Entropy.Umegaki.Spectral
public import QuantumSystem.ForMathlib.Analysis.Matrix.Hermitian

/-!
# Araki's relative entropy on a matrix algebra: Umegaki's formula

For positive semidefinite matrices `ρ, σ` on `ℂⁿ` (of any trace), Araki's relative entropy of the
normal functionals `ω_ρ = Tr (ρ ·)` and `ω_σ = Tr (σ ·)` of `B(ℂⁿ)` is given by **Umegaki's formula**
`Tr ρ (log ρ - log σ)`, with the value `+∞` when `supp ρ ⊄ supp σ`. Umegaki's relative entropy
`D(ρ ‖ σ)` is *defined* as `S(ω_ρ ‖ ω_σ)` (`Matrix.umegakiEntropy`,
`QuantumSystem.Analysis.Entropy.Umegaki.Basic`); this file is the computation that makes the
formula a theorem there.

## Setting

`B(ℂⁿ)` acts on `K ⊗̂ ℂⁿ` as `1 ⊗ B(ℂⁿ) = VonNeumannAlgebra.amplify K 𝓑(ℂⁿ)`
(`= HilbertTensor.vnTensorRight`, `VonNeumannAlgebra.amplify_boundedLinearOperators`). For
`K = ℓ²(ℕ)` it is the amplification on which `VonNeumannAlgebra.arakiEntropy` represents normal
functionals, so one computation serves both. For `K = ℂⁿ` the space is the Hilbert–Schmidt space of
`Mₙ` and, for faithful `ρ`, `Ω_ρ` below is cyclic and separating (the standard form); that remark is
not formalised, only the entropy identity on it (`VonNeumannAlgebra.arakiVec_purification_basisFun`).
Given an orthonormal family `g` in `K`, the **purification** `Ω_ρ = Σᵢ √rᵢ gᵢ ⊗ fᵢ`
(`Matrix.PosSemidef.purification`; `fᵢ`, `rᵢ` the eigenvectors and eigenvalues of `ρ`) represents
`ω_ρ`. It depends on the chosen eigenbasis (unlike the canonical `vec(√ρ) = Σᵢ √rᵢ fᵢ ⊗ f̄ᵢ`, which is
not used); the entropy does not (`VonNeumannAlgebra.arakiVec_eq_umegakiEntropy`).

## Computation

With `e_j`, `s_j` the eigendata of `σ`, the relative modular operator is `ρ̃⁻¹ ⊗ σ` on the support,
`ρ̃ = Σᵢ rᵢ |gᵢ⟩⟨gᵢ|` acting on `K`: `Δ_{Ω_σ, Ω_ρ} (gᵢ ⊗ e_j) = (s_j / rᵢ) gᵢ ⊗ e_j` for `rᵢ > 0`. Expanding
`Ω_ρ = Σ_{i,j} √rᵢ ⟪e_j, fᵢ⟫ gᵢ ⊗ e_j` gives the spectral measure
`μ_{Ω_ρ} = Σ_{i,j} rᵢ |W_{ji}|² δ_{s_j / rᵢ}`, with `W_{ji} = ⟪e_j, fᵢ⟫ = Matrix.eigW hρ hσ j i`, and
`∫ -log dμ_{Ω_ρ}` is the eigenvalue expansion of `Tr ρ (log ρ - log σ)`
(`Matrix.re_trace_mul_log_self_eq`, `Matrix.re_trace_mul_log_eq`). An atom at `0` of positive
mass, which makes the integral `+∞`, occurs exactly when `supp ρ ⊄ supp σ`
(`Matrix.suppSubset_iff_normSq_eigW_mul_eigenvalues_eq_zero`).

## Main definitions

* `Matrix.PosSemidef.purification hρ g` — the purification `Σᵢ √rᵢ gᵢ ⊗ fᵢ ∈ K ⊗̂ ℂⁿ`.
* `Matrix.PosSemidef.normalFunctional hρ` — the normal functional `A ↦ Tr (ρ A)` of `B(ℂⁿ)`, a
  normal state when `Tr ρ = 1` (`Matrix.PosSemidef.normalFunctional_apply_one`).

## Main results

* `Matrix.PosSemidef.inner_purification_amplifyRight` — `⟪Ω_ρ, (1 ⊗ A) Ω_ρ⟫ = Tr (ρ A)`.
* `VonNeumannAlgebra.mem_graph_relativeModular_purification` — the eigenvectors of `Δ_{Ω_σ, Ω_ρ}`.
* `VonNeumannAlgebra.spectralMeasure_relativeModular_purification` — the spectral measure.
* `VonNeumannAlgebra.arakiVec_purification` — `S_{1 ⊗ B(ℂⁿ)}(ω_{Ω_ρ} ‖ ω_{Ω_σ})` is
  `Tr ρ (log ρ - log σ)` if `supp ρ ⊆ supp σ`, and `+∞` otherwise.
* `Matrix.PosSemidef.eq_normalFunctional_of_apply` — a normal functional `A ↦ Tr (ρ A)` is `ω_ρ`;
  `Matrix.PosSemidef.normalFunctional_inj` — `ρ ↦ ω_ρ` is injective.
* `VonNeumannAlgebra.arakiEntropy_normalFunctional` — **Umegaki's formula** for `S(ω_ρ ‖ ω_σ)`.

The same identity for any vectors or functionals representing `ρ` and `σ`
(`VonNeumannAlgebra.arakiVec_purification_basisFun`, `VonNeumannAlgebra.arakiVec_eq_umegakiEntropy`,
`VonNeumannAlgebra.arakiEntropy_eq_umegakiEntropy`) is stated with `D(ρ ‖ σ)` in
`QuantumSystem.Analysis.Entropy.Umegaki.Basic`; there `arakiVec_eq_umegakiEntropy` holds for every
multiplicity space `K`, reduced to the present computation by enlarging `K` to `K ⊕ ℂⁿ`.
-/

@[expose] public section

open ClosedSubmodule MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace VonNeumannAlgebra HilbertTensor Matrix.QuantumInfo Araki ComplexOrder
open InnerProductSpace (cyclicSubspace rankOne)
open HilbertTensor (amplifyLeft amplifyRight)

variable {n : Type*} [Fintype n] [DecidableEq n]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

namespace Matrix.PosSemidef

/-- The vector `Σᵢ √rᵢ gᵢ ⊗ fᵢ ∈ K ⊗̂ ℂⁿ` built from a positive semidefinite `ρ` and a family `g` in
`K`, where `fᵢ` is the eigenvector basis of `ρ` and `rᵢ` its eigenvalues. For orthonormal `g` it
is a **purification** of `ρ`: it represents the positive functional `A ↦ Tr (ρ A)` (a state when
`Tr ρ = 1`) of `1 ⊗ B(ℂⁿ)` (`Matrix.PosSemidef.inner_purification_amplifyRight`). -/
noncomputable def purification {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (g : n → K) :
    K ⊗̂ EuclideanSpace ℂ n :=
  ∑ i, ((Real.sqrt (hρ.1.eigenvalues i) : ℝ) : ℂ) • (g i ⊗ₕ hρ.1.eigenvectorBasis i)

variable {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) {g : n → K}

/-- `(1 ⊗ |x⟩⟨fᵢ|) Ω_ρ = √rᵢ gᵢ ⊗ x`. -/
lemma amplifyRight_rankOne_purification (x : EuclideanSpace ℂ n) (i : n) :
    amplifyRight (rankOne ℂ x (hρ.1.eigenvectorBasis i)) (hρ.purification g) =
      ((Real.sqrt (hρ.1.eigenvalues i) : ℝ) : ℂ) • (g i ⊗ₕ x) := by
  have hf := hρ.1.eigenvectorBasis.orthonormal
  simp only [purification, map_sum, map_smul, HilbertTensor.amplifyRight_tmul,
    InnerProductSpace.rankOne_apply]
  rw [Finset.sum_eq_single i (fun k _ hk => by
      rw [hf.2 hk.symm, zero_smul, HilbertTensor.tmul_zero, smul_zero]) (by simp),
    orthonormal_iff_ite.mp hf i i]
  simp

/-- `(|y⟩⟨gᵢ| ⊗ 1) Ω_ρ = √rᵢ y ⊗ fᵢ` for orthonormal `g`. -/
lemma amplifyLeft_rankOne_purification (hg : Orthonormal ℂ g) (y : K) (i : n) :
    amplifyLeft (rankOne ℂ y (g i)) (hρ.purification g) =
      ((Real.sqrt (hρ.1.eigenvalues i) : ℝ) : ℂ) • (y ⊗ₕ hρ.1.eigenvectorBasis i) := by
  simp only [purification, map_sum, map_smul, HilbertTensor.amplifyLeft_tmul,
    InnerProductSpace.rankOne_apply]
  rw [Finset.sum_eq_single i (fun k _ hk => by
      rw [hg.2 hk.symm, zero_smul, HilbertTensor.zero_tmul, smul_zero]) (by simp),
    orthonormal_iff_ite.mp hg i i]
  simp

/-- **The purification represents `ρ`**: `⟪Ω_ρ, (1 ⊗ A) Ω_ρ⟫ = Tr (ρ A)` for orthonormal `g`. -/
theorem inner_purification_amplifyRight (hg : Orthonormal ℂ g) (A : Matrix n n ℂ) :
    ⟪hρ.purification g, amplifyRight (Matrix.toEuclideanCLM (𝕜 := ℂ) A) (hρ.purification g)⟫_ℂ =
      Tr (ρ * A) := by
  rw [hρ.trace_mul_eq_sum_inner]
  simp only [purification, map_sum, map_smul, HilbertTensor.amplifyRight_tmul, sum_inner,
    inner_sum, inner_smul_left, inner_smul_right, HilbertTensor.inner_tmul,
    orthonormal_iff_ite.mp hg, ite_mul, one_mul, zero_mul, Complex.conj_ofReal, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_assoc, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (hρ.eigenvalues_nonneg i)]

end Matrix.PosSemidef

namespace VonNeumannAlgebra

open Matrix.PosSemidef

/-- `B(ℂⁿ)` acting on the second leg of `K ⊗̂ ℂⁿ`, i.e. `1 ⊗ B(ℂⁿ)`. -/
local notation "𝓜" => VonNeumannAlgebra.amplify K 𝓑(EuclideanSpace ℂ n)

variable {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) {g : n → K}

/-- `√r` as a complex number. -/
local notation "√ᶜ" r => ((Real.sqrt r : ℝ) : ℂ)

private lemma sqrt_ne_zero {r : ℝ} (hr : 0 < r) : (√ᶜ r) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hr).ne'

/-- For `rᵢ > 0`, `s(Ω_ρ)` fixes `y ⊗ fᵢ`: it lies in `[𝓜′ Ω_ρ]`. -/
lemma supportProj_purification_tmul (hg : Orthonormal ℂ g) {i : n}
    (hi : 0 < hρ.1.eigenvalues i) (y : K) :
    (𝓜).supportProj (hρ.purification g) (y ⊗ₕ hρ.1.eigenvectorBasis i) =
      y ⊗ₕ hρ.1.eigenvectorBasis i := by
  rw [supportProj, Submodule.starProjection_eq_self_iff]
  have h := Submodule.smul_mem _ (√ᶜ hρ.1.eigenvalues i)⁻¹
    (InnerProductSpace.apply_mem_cyclicSubspace (hρ.purification g)
      (amplifyLeft_mem_commutant_amplify (M := 𝓑(EuclideanSpace ℂ n)) (rankOne ℂ y (g i))))
  rwa [hρ.amplifyLeft_rankOne_purification hg, smul_smul, inv_mul_cancel₀ (sqrt_ne_zero hi),
    one_smul] at h

/-- For `rᵢ > 0`, `s′(Ω_ρ)` fixes `gᵢ ⊗ x`: it lies in `[𝓜 Ω_ρ]`. -/
lemma supportProj_commutant_purification_tmul {i : n} (hi : 0 < hρ.1.eigenvalues i)
    (x : EuclideanSpace ℂ n) :
    (𝓜)′.supportProj (hρ.purification g) (g i ⊗ₕ x) = g i ⊗ₕ x := by
  rw [supportProj_commutant, Submodule.starProjection_eq_self_iff]
  have h := Submodule.smul_mem _ (√ᶜ hρ.1.eigenvalues i)⁻¹
    (InnerProductSpace.apply_mem_cyclicSubspace (hρ.purification g)
      (amplifyRight_mem_amplify (H₁ := K)
        (mem_boundedLinearOperators (rankOne ℂ x (hρ.1.eigenvectorBasis i)))))
  rwa [hρ.amplifyRight_rankOne_purification, smul_smul, inv_mul_cancel₀ (sqrt_ne_zero hi),
    one_smul] at h

variable {hρ hσ}

/-- The relative Tomita operator `S_{Ω_σ, Ω_ρ}` of `1 ⊗ B(ℂⁿ)` sends `√rᵢ gᵢ ⊗ e_j` to
`√s_j g_j ⊗ fᵢ` (`rᵢ > 0`; `e`, `s` the eigendata of `σ`). -/
private lemma mem_graph_relativeTomita_purification (hg : Orthonormal ℂ g) {i : n}
    (hi : 0 < hρ.1.eigenvalues i) (j : n) :
    ((√ᶜ hρ.1.eigenvalues i) • (g i ⊗ₕ hσ.1.eigenvectorBasis j),
        (√ᶜ hσ.1.eigenvalues j) • (g j ⊗ₕ hρ.1.eigenvectorBasis i)) ∈
      ((𝓜).relativeTomita (hσ.purification g) (hρ.purification g)).graph := by
  have h := apply_mem_graph_relativeTomita (η := hσ.purification g) (ξ := hρ.purification g)
    (amplifyRight_mem_amplify (H₁ := K)
      (mem_boundedLinearOperators (rankOne ℂ (hσ.1.eigenvectorBasis j) (hρ.1.eigenvectorBasis i))))
  rwa [hρ.amplifyRight_rankOne_purification, HilbertTensor.amplifyRight_star,
    ContinuousLinearMap.star_eq_adjoint, InnerProductSpace.adjoint_rankOne,
    hσ.amplifyRight_rankOne_purification, map_smul, supportProj_purification_tmul hρ hg hi] at h

/-- The relative Tomita operator `F_{Ω_σ, Ω_ρ}` of the commutant sends `√rᵢ g_j ⊗ fᵢ` to
`√s_j gᵢ ⊗ e_j` (`rᵢ > 0`). -/
private lemma mem_graph_relativeTomita_commutant_purification [CompleteSpace K]
    (hg : Orthonormal ℂ g) {i : n} (hi : 0 < hρ.1.eigenvalues i) (j : n) :
    ((√ᶜ hρ.1.eigenvalues i) • (g j ⊗ₕ hρ.1.eigenvectorBasis i),
        (√ᶜ hσ.1.eigenvalues j) • (g i ⊗ₕ hσ.1.eigenvectorBasis j)) ∈
      ((𝓜)′.relativeTomita (hσ.purification g) (hρ.purification g)).graph := by
  have h := apply_mem_graph_relativeTomita (M := (𝓜)′) (η := hσ.purification g)
    (ξ := hρ.purification g) (amplifyLeft_mem_commutant_amplify (M := 𝓑(EuclideanSpace ℂ n)) (rankOne ℂ (g j) (g i)))
  rwa [hρ.amplifyLeft_rankOne_purification hg, HilbertTensor.amplifyLeft_star,
    ContinuousLinearMap.star_eq_adjoint, InnerProductSpace.adjoint_rankOne,
    hσ.amplifyLeft_rankOne_purification hg, map_smul,
    supportProj_commutant_purification_tmul hρ hi] at h

/-- **The relative modular operator on eigenvectors.** For `rᵢ > 0`,
`Δ_{Ω_σ, Ω_ρ} (gᵢ ⊗ e_j) = (s_j / rᵢ) gᵢ ⊗ e_j`, i.e. `Δ = ρ̃⁻¹ ⊗ σ` on the support, where
`ρ̃ = Σᵢ rᵢ |gᵢ⟩⟨gᵢ|` acts on `K`. -/
theorem mem_graph_relativeModular_purification [CompleteSpace K] (hg : Orthonormal ℂ g) {i : n}
    (hi : 0 < hρ.1.eigenvalues i) (j : n) :
    (g i ⊗ₕ hσ.1.eigenvectorBasis j,
        ((hσ.1.eigenvalues j / hρ.1.eigenvalues i : ℝ) : ℂ) •
          (g i ⊗ₕ hσ.1.eigenvectorBasis j)) ∈
      ((𝓜).relativeModular (hσ.purification g) (hρ.purification g)).graph := by
  set r := hρ.1.eigenvalues i
  set t := hσ.1.eigenvalues j
  have hr := (Real.sqrt_pos.mpr hi).ne'
  have hrr := Real.mul_self_sqrt hi.le
  have htt := Real.mul_self_sqrt (hσ.eigenvalues_nonneg j)
  rw [mem_graph_relativeModular, LinearPMap.mem_graph_compNat]
  refine ⟨((Real.sqrt t / Real.sqrt r : ℝ) : ℂ) • (g j ⊗ₕ hρ.1.eigenvectorBasis i), ?_, ?_⟩
  · refine mem_graph_closure_relativeTomita ?_
    have h := isConjLinear_relativeTomita _ _ _ ((Real.sqrt r)⁻¹ : ℝ) _ _
      (mem_graph_relativeTomita_purification (hρ := hρ) (hσ := hσ) hg hi j)
    rwa [Complex.conj_ofReal, smul_smul, smul_smul, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      inv_mul_cancel₀ hr, Complex.ofReal_one, one_smul, inv_mul_eq_div] at h
  · rw [LinearPMap.adjoint_closure (dense_domain_relativeTomita _ _ _)]
    refine LinearPMap.le_graph_of_le (relativeTomita_commutant_le_adjoint _ _ _) ?_
    have h := isConjLinear_relativeTomita _ _ _ ((Real.sqrt t / r : ℝ) : ℂ) _ _
      (mem_graph_relativeTomita_commutant_purification (hρ := hρ) (hσ := hσ) hg hi j)
    have c₁ : Real.sqrt t / r * Real.sqrt r = Real.sqrt t / Real.sqrt r := by
      rw [div_mul_eq_mul_div, div_eq_div_iff hi.ne' hr]
      linear_combination Real.sqrt t * hrr
    have c₂ : Real.sqrt t / r * Real.sqrt t = t / r := by
      rw [div_mul_eq_mul_div, div_eq_div_iff hi.ne' hi.ne']
      linear_combination r * htt
    rwa [Complex.conj_ofReal, smul_smul, smul_smul, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      c₁, c₂] at h

variable (hρ hσ) in
/-- `Ω_ρ = Σ_{i,j} √rᵢ ⟪e_j, fᵢ⟫ gᵢ ⊗ e_j`: the purification expanded in eigenvectors of
`Δ_{Ω_σ, Ω_ρ}`. -/
lemma purification_eq_sum_eigenvectorBasis :
    hρ.purification g = ∑ p : n × n,
      ((√ᶜ hρ.1.eigenvalues p.1) *
          ⟪hσ.1.eigenvectorBasis p.2, hρ.1.eigenvectorBasis p.1⟫_ℂ) •
        (g p.1 ⊗ₕ hσ.1.eigenvectorBasis p.2) := by
  rw [Fintype.sum_prod_type, purification]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_lhs => rw [← hσ.1.eigenvectorBasis.sum_repr' (hρ.1.eigenvectorBasis i)]
  rw [← HilbertTensor.tmulRightL_apply, map_sum, Finset.smul_sum]
  simp only [map_smul, HilbertTensor.tmulRightL_apply, smul_smul]

variable (hρ hσ) in
/-- **Spectral measure**: `μ_{Ω_ρ}` of `Δ_{Ω_σ, Ω_ρ}` is `Σ_{i,j} rᵢ |⟪e_j, fᵢ⟫|² δ_{s_j / rᵢ}`. -/
theorem spectralMeasure_relativeModular_purification [CompleteSpace K] (hg : Orthonormal ℂ g) :
    (isSelfAdjoint_relativeModular (𝓜) (hσ.purification g) (hρ.purification g)).spectralMeasure
        (hρ.purification g) =
      ∑ p : n × n, (hρ.1.eigenvalues p.1 *
          ‖⟪hσ.1.eigenvectorBasis p.2, hρ.1.eigenvectorBasis p.1⟫_ℂ‖ ^ 2).toNNReal •
        Measure.dirac (hσ.1.eigenvalues p.2 / hρ.1.eigenvalues p.1) := by
  have he := hσ.1.eigenvectorBasis.orthonormal
  have hnorm : ∀ p : n × n, ‖((√ᶜ hρ.1.eigenvalues p.1) *
      ⟪hσ.1.eigenvectorBasis p.2, hρ.1.eigenvectorBasis p.1⟫_ℂ) •
        (g p.1 ⊗ₕ hσ.1.eigenvectorBasis p.2)‖₊ ^ 2 =
      (hρ.1.eigenvalues p.1 *
        ‖⟪hσ.1.eigenvectorBasis p.2, hρ.1.eigenvectorBasis p.1⟫_ℂ‖ ^ 2).toNNReal :=
    fun p => by
      ext
      rw [Real.coe_toNNReal _ (by positivity [hρ.eigenvalues_nonneg p.1]), NNReal.coe_pow,
        coe_nnnorm, norm_smul, HilbertTensor.norm_tmul, hg.1, he.1, mul_one, mul_one, norm_mul,
        Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
        Real.sq_sqrt (hρ.eigenvalues_nonneg p.1)]
  have hsum := purification_eq_sum_eigenvectorBasis (g := g) hρ hσ
  calc _ = (isSelfAdjoint_relativeModular (𝓜) (hσ.purification g) (hρ.purification g)).spectralMeasure
        (∑ p : n × n, ((√ᶜ hρ.1.eigenvalues p.1) *
          ⟪hσ.1.eigenvectorBasis p.2, hρ.1.eigenvectorBasis p.1⟫_ℂ) •
            (g p.1 ⊗ₕ hσ.1.eigenvectorBasis p.2)) := by rw [← hsum]
    _ = _ := by
      simp_rw [← hnorm]
      refine IsSelfAdjoint.spectralMeasure_sum_of_mem_graph _ Finset.univ (fun p _ => ?_)
        (fun p _ q _ hpq => ?_)
      · rcases (hρ.eigenvalues_nonneg p.1).eq_or_lt with h0 | hi
        · simp [← h0]
        · have := ((𝓜).relativeModular (hσ.purification g) (hρ.purification g)).graph.smul_mem
            ((√ᶜ hρ.1.eigenvalues p.1) *
              ⟪hσ.1.eigenvectorBasis p.2, hρ.1.eigenvectorBasis p.1⟫_ℂ)
            (mem_graph_relativeModular_purification hg hi p.2)
          rwa [Prod.smul_mk, smul_comm] at this
      · dsimp only
        rw [inner_smul_left, inner_smul_right, HilbertTensor.inner_tmul]
        rcases eq_or_ne p.1 q.1 with h₁ | h₁
        · rw [he.2 fun h₂ => hpq (Prod.ext h₁ h₂), mul_zero, mul_zero, mul_zero]
        · rw [hg.2 h₁, zero_mul, mul_zero, mul_zero]

variable (hρ hσ) in
/-- **Araki's relative entropy of purifications is given by Umegaki's formula.** For positive
semidefinite matrices `ρ, σ` (of any trace) and their purifications along an orthonormal family
`g` in `K`, `S_{1 ⊗ B(ℂⁿ)}(ω_{Ω_ρ} ‖ ω_{Ω_σ}) = Tr ρ (cfc Real.log ρ - cfc Real.log σ)` if
`supp ρ ⊆ supp σ`, and `+∞` otherwise. -/
theorem arakiVec_purification [CompleteSpace K] (hg : Orthonormal ℂ g)
    [Decidable (Matrix.SuppSubset ρ σ)] :
    (𝓜).arakiVec (hρ.purification g) (hσ.purification g) =
      if Matrix.SuppSubset ρ σ then
        (((Tr (ρ * (cfc Real.log ρ - cfc Real.log σ))).re : ℝ) : EReal)
      else ⊤ := by
  have hW : ∀ i j, ‖⟪hσ.1.eigenvectorBasis j, hρ.1.eigenvectorBasis i⟫_ℂ‖ ^ 2 =
      Complex.normSq (Matrix.eigW hρ.1 hσ.1 j i) := fun i j => by
    rw [Matrix.eigW_apply, Complex.normSq_eq_norm_sq]
  rw [arakiVec, spectralMeasure_relativeModular_purification hρ hσ hg]
  simp_rw [hW]
  by_cases hsupp : Matrix.SuppSubset ρ σ
  · have ht : ∀ i j, hρ.1.eigenvalues i * Complex.normSq (Matrix.eigW hρ.1 hσ.1 j i) ≠ 0 →
        hσ.1.eigenvalues j ≠ 0 := fun i j h ht =>
      h (by
        rw [mul_comm]
        exact Matrix.normSq_eigW_mul_eigenvalues_eq_zero_of_suppSubset hρ.1 hσ.1 hsupp j ht i)
    rw [ite_eq_left hsupp, negLogIntegral_finsetSum_smul_dirac _ _ fun p _ hp => ?_]
    · refine congrArg _ ?_
      rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re,
        Matrix.re_trace_mul_log_self_eq hρ.1, Matrix.re_trace_mul_log_eq hρ.1 hσ.1, Fintype.sum_prod_type]
      have hterm : ∀ i j,
          -(((hρ.1.eigenvalues i * Complex.normSq (Matrix.eigW hρ.1 hσ.1 j i)).toNNReal : ℝ) *
            Real.log (hσ.1.eigenvalues j / hρ.1.eigenvalues i)) =
          Complex.normSq (Matrix.eigW hρ.1 hσ.1 j i) * hρ.1.eigenvalues i *
              Real.log (hρ.1.eigenvalues i) -
            Complex.normSq (Matrix.eigW hρ.1 hσ.1 j i) * hρ.1.eigenvalues i *
              Real.log (hσ.1.eigenvalues j) := fun i j => by
        rw [Real.coe_toNNReal _ (mul_nonneg (hρ.eigenvalues_nonneg i) (Complex.normSq_nonneg _))]
        by_cases h : hρ.1.eigenvalues i * Complex.normSq (Matrix.eigW hρ.1 hσ.1 j i) = 0
        · rw [h, zero_mul, neg_zero, ← mul_sub, mul_comm (Complex.normSq _), h, zero_mul]
        · rw [Real.log_div (ht i j h) (left_ne_zero_of_mul h)]
          ring
      simp_rw [hterm, Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_mul, ← Finset.sum_mul, Matrix.sum_normSq_eigW_col hρ.1 hσ.1, one_mul]
    · have hpos : 0 < hρ.1.eigenvalues p.1 * Complex.normSq (Matrix.eigW hρ.1 hσ.1 p.2 p.1) :=
        Real.toNNReal_pos.mp (pos_iff_ne_zero.mpr hp)
      exact div_pos ((hσ.eigenvalues_nonneg p.2).lt_of_ne' (ht _ _ hpos.ne'))
        ((hρ.eigenvalues_nonneg p.1).lt_of_ne' (left_ne_zero_of_mul hpos.ne'))
  · rw [ite_eq_right hsupp]
    obtain ⟨j, hj, i, hij⟩ : ∃ j, hσ.1.eigenvalues j = 0 ∧
        ∃ i, Complex.normSq (Matrix.eigW hρ.1 hσ.1 j i) * hρ.1.eigenvalues i ≠ 0 := by
      by_contra! h
      exact hsupp ((Matrix.suppSubset_iff_normSq_eigW_mul_eigenvalues_eq_zero hρ hσ.1).mpr h)
    refine negLogIntegral_finsetSum_smul_dirac_eq_top (Finset.mem_univ (i, j)) ?_ (by simp [hj])
    rw [Ne, Real.toNNReal_eq_zero, not_le, mul_comm]
    exact (mul_nonneg (Complex.normSq_nonneg _) (hρ.eigenvalues_nonneg i)).lt_of_ne' hij

end VonNeumannAlgebra

/-! ### Normal states of `B(ℂⁿ)` -/

/-- `δₙ` is the orthonormal family `i ↦ e_{k(i)}` of `ℓ²(ℕ)` indexed by the finite type `n`, where
`k = Fin.val ∘ Fintype.equivFin n : n → ℕ` is injective: the standard basis vectors
`lp.single 2 (k i) 1`. -/
local notation "δₙ" => fun i => lp.single (E := fun _ : ℕ => ℂ) 2 (Fintype.equivFin _ i : ℕ) (1 : ℂ)

omit [DecidableEq n] in
/-- The family `δₙ` is orthonormal in `ℓ²(ℕ)`: it is the standard basis precomposed with the
injection `n ≃ Fin (card n) ↪ ℕ`. -/
private theorem orthonormal_single_equivFin : Orthonormal ℂ (δₙ : n → lp (fun _ : ℕ => ℂ) 2) :=
  lp.orthonormal_single.comp _ (Fin.val_injective.comp (Fintype.equivFin n).injective)

namespace Matrix.PosSemidef

open VonNeumannAlgebra

/-- The **normal functional** `A ↦ Tr (ρ A)` of `B(ℂⁿ)` defined by a positive semidefinite matrix
`ρ`, represented on `ℓ²(ℕ) ⊗̂ ℂⁿ` by a purification. For a density matrix it is the normal state
`ω_ρ`. -/
noncomputable def normalFunctional {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) :
    𝓑(EuclideanSpace ℂ n).NormalFunctional :=
  NormalFunctional.ofAmplifiedVector 𝓑(EuclideanSpace ℂ n) (hρ.purification δₙ)

variable {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef)

/-- `ω_ρ(A) = Tr (ρ A)`. -/
theorem normalFunctional_apply (A : Matrix n n ℂ) :
    hρ.normalFunctional.1 A.toBoundedLinearOperators = Tr (ρ * A) :=
  hρ.inner_purification_amplifyRight orthonormal_single_equivFin A


/-- A normal functional on `B(ℂⁿ)` with `ψ(A) = Tr (ρ A)` for every `A` is `ω_ρ`. -/
theorem eq_normalFunctional_of_apply {ψ : 𝓑(EuclideanSpace ℂ n).NormalFunctional}
    (hψ : ∀ A : Matrix n n ℂ, ψ.1 A.toBoundedLinearOperators = Tr (ρ * A)) :
    ψ = hρ.normalFunctional := by
  refine Subtype.ext (PositiveLinearMap.ext fun x => ?_)
  obtain ⟨A, rfl⟩ := Matrix.toBoundedLinearOperators.surjective x
  exact (hψ A).trans (hρ.normalFunctional_apply A).symm

/-- `ω_ρ(1) = Tr ρ`; for a density matrix, `ω_ρ` is a state. -/
theorem normalFunctional_apply_one : hρ.normalFunctional.1 1 = Tr ρ := by
  have h := hρ.normalFunctional_apply 1
  rwa [map_one, Matrix.mul_one] at h

/-- **Injectivity of `ρ ↦ ω_ρ`**: positive semidefinite matrices with the same normal functional
on `B(ℂⁿ)` are equal. -/
theorem normalFunctional_inj {hσ : σ.PosSemidef} :
    hρ.normalFunctional = hσ.normalFunctional ↔ ρ = σ := by
  refine ⟨fun h => ?_, fun h => by subst h; rfl⟩
  refine (Matrix.ext_iff_trace_mul_right).mpr fun A => ?_
  rw [← hρ.normalFunctional_apply, ← hσ.normalFunctional_apply, h]

end Matrix.PosSemidef

namespace VonNeumannAlgebra

variable {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)

/-- **Araki's relative entropy of the normal functionals `Tr (ρ ·)`, `Tr (σ ·)` of `B(ℂⁿ)` is
given by Umegaki's formula**: `S(ω_ρ ‖ ω_σ) = Tr ρ (log ρ - log σ)` if `supp ρ ⊆ supp σ`, and `+∞`
otherwise. -/
theorem arakiEntropy_normalFunctional [Decidable (Matrix.SuppSubset ρ σ)] :
    S⟦hρ.normalFunctional ∥ hσ.normalFunctional⟧ =
      if Matrix.SuppSubset ρ σ then
        (((Tr (ρ * (cfc Real.log ρ - cfc Real.log σ))).re : ℝ) : EReal)
      else ⊤ :=
  (arakiEntropy_eq_arakiVec (Ξψ := hρ.purification δₙ) (Ξφ := hσ.purification δₙ) (fun _ => rfl)
    (fun _ => rfl)).trans (arakiVec_purification hρ hσ orthonormal_single_equivFin)

end VonNeumannAlgebra
