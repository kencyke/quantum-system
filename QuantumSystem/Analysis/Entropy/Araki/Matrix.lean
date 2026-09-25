/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.Entropy.Araki.Basic
public import QuantumSystem.Analysis.Entropy.RelativeEntropy
public import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Araki's relative entropy on a matrix algebra: Umegaki's relative entropy

For density matrices `ρ, σ` on `ℂⁿ`, Araki's relative entropy of the normal states
`ω_ρ = Tr (ρ ·)` and `ω_σ = Tr (σ ·)` of `B(ℂⁿ)` is **Umegaki's relative entropy**
`D(ρ ‖ σ) = Tr ρ (log ρ - log σ)` (`Matrix.relativeEntropy`), including the value `+∞` when
`supp ρ ⊄ supp σ`.

## Setting

`B(ℂⁿ)` acts on `K ⊗̂ ℂⁿ` as `1 ⊗ B(ℂⁿ) = VonNeumannAlgebra.amplify K 𝓑(ℂⁿ)`
(`= HilbertTensor.vnTensorRight`, `VonNeumannAlgebra.amplify_boundedLinearOperators`). For
`K = ℓ²(ℕ)` it is the amplification on which `VonNeumannAlgebra.arakiEntropy` represents normal
functionals, so one computation serves both. For `K = ℂⁿ` the space is the Hilbert–Schmidt space of
`Mₙ` and, for faithful `ρ`, `Ω_ρ` below is cyclic and separating (the standard form); that remark is
not formalised, only the entropy identity on it (`VonNeumannAlgebra.arakiVec_purification_basisFun`).
Given an orthonormal family `g` in `K`, the **purification** `Ω_ρ = Σᵢ √rᵢ gᵢ ⊗ fᵢ`
(`DensityMatrix.purification`; `fᵢ`, `rᵢ` the eigenvectors and eigenvalues of `ρ`) represents
`ω_ρ`. It depends on the chosen eigenbasis (unlike the canonical `vec(√ρ) = Σᵢ √rᵢ fᵢ ⊗ f̄ᵢ`, which is
not used); the entropy does not (`VonNeumannAlgebra.arakiVec_eq_relativeEntropy`).

## Computation

With `e_j`, `s_j` the eigendata of `σ`, the relative modular operator is `ρ̃⁻¹ ⊗ σ` on the support,
`ρ̃ = Σᵢ rᵢ |gᵢ⟩⟨gᵢ|` acting on `K`: `Δ_{Ω_σ, Ω_ρ} (gᵢ ⊗ e_j) = (s_j / rᵢ) gᵢ ⊗ e_j` for `rᵢ > 0`. Expanding
`Ω_ρ = Σ_{i,j} √rᵢ ⟪e_j, fᵢ⟫ gᵢ ⊗ e_j` gives the spectral measure
`μ_{Ω_ρ} = Σ_{i,j} rᵢ |W_{ji}|² δ_{s_j / rᵢ}`, with `W_{ji} = ⟪e_j, fᵢ⟫ = Matrix.eigW ρ σ j i`, and
`∫ -log dμ_{Ω_ρ}` is the eigenvalue expansion of `Tr ρ (log ρ - log σ)`
(`Matrix.re_trace_mul_log_self_eq`, `Matrix.re_trace_mul_log_eq`). An atom at `0` of positive
mass, which makes the integral `+∞`, occurs exactly when `supp ρ ⊄ supp σ`
(`Matrix.suppSubset_iff_normSq_eigW_mul_eigenvalues_eq_zero`).

## Main definitions

* `DensityMatrix.purification ρ g` — the purification `Σᵢ √rᵢ gᵢ ⊗ fᵢ ∈ K ⊗̂ ℂⁿ`.
* `DensityMatrix.normalState ρ` — the normal state `A ↦ Tr (ρ A)` of `B(ℂⁿ)`.

## Main results

* `DensityMatrix.inner_purification_amplifyRight` — `⟪Ω_ρ, (1 ⊗ A) Ω_ρ⟫ = Tr (ρ A)`.
* `VonNeumannAlgebra.mem_graph_relativeModular_purification` — the eigenvectors of `Δ_{Ω_σ, Ω_ρ}`.
* `VonNeumannAlgebra.spectralMeasure_relativeModular_purification` — the spectral measure.
* `VonNeumannAlgebra.arakiVec_purification`, `VonNeumannAlgebra.arakiVec_purification_basisFun`,
  `VonNeumannAlgebra.arakiVec_eq_relativeEntropy` — `S_{1 ⊗ B(ℂⁿ)}(ω_ξ ‖ ω_η) = D(ρ ‖ σ)` for the
  purifications, on `ℂⁿ ⊗̂ ℂⁿ`, and for any vectors representing `ρ` and `σ` on a `K` that carries
  `n` orthonormal vectors.
* `VonNeumannAlgebra.arakiEntropy_eq_relativeEntropy`, `VonNeumannAlgebra.arakiEntropy_normalState`
  — **Araki = Umegaki**: `S(ω_ρ ‖ ω_σ) = D(ρ ‖ σ)` for normal functionals on `B(ℂⁿ)`.

## Not formalised

`VonNeumannAlgebra.arakiVec_eq_relativeEntropy` assumes `n` orthonormal vectors in `K`, although
representing vectors exist as soon as `dim K ≥ rank ρ, rank σ`. Dropping the assumption needs the
invariance of `arakiVec` under a change of multiplicity space `K ↪ K'`, which is not formalised
(see also `QuantumSystem.Analysis.Entropy.Araki.Basic`).
-/

@[expose] public section

open ClosedSubmodule MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace VonNeumannAlgebra HilbertTensor Matrix.QuantumInfo Araki
open InnerProductSpace (cyclicSubspace rankOne)
open HilbertTensor (amplifyLeft amplifyRight)

variable {n : Type*} [Fintype n] [DecidableEq n]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- An eigenvector of a Hermitian matrix is an eigenvector of the operator it defines on `ℂⁿ`. -/
lemma Matrix.IsHermitian.toEuclideanCLM_eigenvectorBasis {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (i : n) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) A (hA.eigenvectorBasis i) =
      ((hA.eigenvalues i : ℝ) : ℂ) • hA.eigenvectorBasis i := by
  refine PiLp.ext fun k => ?_
  have := congrFun (hA.mulVec_eigenvectorBasis i) k
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)] at this
  exact this

namespace DensityMatrix

/-- A **purification** of `ρ` along a family `g` in `K`: the vector `Σᵢ √rᵢ gᵢ ⊗ fᵢ ∈ K ⊗̂ ℂⁿ`, where
`fᵢ` is the eigenvector basis of `ρ` and `rᵢ` its eigenvalues. For orthonormal `g` it represents
the state `A ↦ Tr (ρ A)` of `1 ⊗ B(ℂⁿ)` (`DensityMatrix.inner_purification_amplifyRight`). -/
noncomputable def purification (ρ : DensityMatrix n) (g : n → K) : K ⊗̂ EuclideanSpace ℂ n :=
  ∑ i, ((Real.sqrt (ρ.isHermitian.eigenvalues i) : ℝ) : ℂ) • (g i ⊗ₕ ρ.isHermitian.eigenvectorBasis i)

variable (ρ : DensityMatrix n) {g : n → K}

/-- `(1 ⊗ |x⟩⟨fᵢ|) Ω_ρ = √rᵢ gᵢ ⊗ x`. -/
lemma amplifyRight_rankOne_purification (x : EuclideanSpace ℂ n) (i : n) :
    amplifyRight (rankOne ℂ x (ρ.isHermitian.eigenvectorBasis i)) (ρ.purification g) =
      ((Real.sqrt (ρ.isHermitian.eigenvalues i) : ℝ) : ℂ) • (g i ⊗ₕ x) := by
  have hf := ρ.isHermitian.eigenvectorBasis.orthonormal
  simp only [purification, map_sum, map_smul, HilbertTensor.amplifyRight_tmul,
    InnerProductSpace.rankOne_apply]
  rw [Finset.sum_eq_single i (fun k _ hk => by
      rw [hf.2 hk.symm, zero_smul, HilbertTensor.tmul_zero, smul_zero]) (by simp),
    orthonormal_iff_ite.mp hf i i]
  simp

/-- `(|y⟩⟨gᵢ| ⊗ 1) Ω_ρ = √rᵢ y ⊗ fᵢ` for orthonormal `g`. -/
lemma amplifyLeft_rankOne_purification (hg : Orthonormal ℂ g) (y : K) (i : n) :
    amplifyLeft (rankOne ℂ y (g i)) (ρ.purification g) =
      ((Real.sqrt (ρ.isHermitian.eigenvalues i) : ℝ) : ℂ) • (y ⊗ₕ ρ.isHermitian.eigenvectorBasis i) := by
  simp only [purification, map_sum, map_smul, HilbertTensor.amplifyLeft_tmul,
    InnerProductSpace.rankOne_apply]
  rw [Finset.sum_eq_single i (fun k _ hk => by
      rw [hg.2 hk.symm, zero_smul, HilbertTensor.zero_tmul, smul_zero]) (by simp),
    orthonormal_iff_ite.mp hg i i]
  simp

/-- `Tr (ρ A) = Σᵢ rᵢ ⟪fᵢ, A fᵢ⟫` in the eigenvector basis of `ρ`. -/
lemma trace_mul_eq_sum_inner (A : Matrix n n ℂ) :
    Tr (ρ.toMatrix * A) = ∑ i, ((ρ.isHermitian.eigenvalues i : ℝ) : ℂ) *
      ⟪ρ.isHermitian.eigenvectorBasis i,
        Matrix.toEuclideanCLM (𝕜 := ℂ) A (ρ.isHermitian.eigenvectorBasis i)⟫_ℂ := by
  have h : Tr (ρ.toMatrix * A) =
      LinearMap.trace ℂ _ (Matrix.toEuclideanLin (ρ.toMatrix * A)) := by
    rw [LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun n ℂ).toBasis,
      Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]
  rw [h, LinearMap.trace_eq_sum_inner _ ρ.isHermitian.eigenvectorBasis]
  refine Finset.sum_congr rfl fun i _ => ?_
  change ⟪_, Matrix.toEuclideanCLM (𝕜 := ℂ) (ρ.toMatrix * A) _⟫_ℂ = _
  rw [map_mul]
  calc _ = ⟪Matrix.toEuclideanCLM (𝕜 := ℂ) ρ.toMatrix (ρ.isHermitian.eigenvectorBasis i),
        Matrix.toEuclideanCLM (𝕜 := ℂ) A (ρ.isHermitian.eigenvectorBasis i)⟫_ℂ :=
        (Matrix.isSymmetric_toEuclideanLin_iff.mpr ρ.isHermitian _ _).symm
    _ = _ := by
      rw [ρ.isHermitian.toEuclideanCLM_eigenvectorBasis, inner_smul_left, Complex.conj_ofReal]

/-- **The purification represents `ρ`**: `⟪Ω_ρ, (1 ⊗ A) Ω_ρ⟫ = Tr (ρ A)` for orthonormal `g`. -/
theorem inner_purification_amplifyRight (hg : Orthonormal ℂ g) (A : Matrix n n ℂ) :
    ⟪ρ.purification g, amplifyRight (Matrix.toEuclideanCLM (𝕜 := ℂ) A) (ρ.purification g)⟫_ℂ =
      Tr (ρ.toMatrix * A) := by
  rw [trace_mul_eq_sum_inner]
  simp only [purification, map_sum, map_smul, HilbertTensor.amplifyRight_tmul, sum_inner,
    inner_sum, inner_smul_left, inner_smul_right, HilbertTensor.inner_tmul,
    orthonormal_iff_ite.mp hg, ite_mul, one_mul, zero_mul, Complex.conj_ofReal, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_assoc, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (ρ.eigenvalues_nonneg i)]

end DensityMatrix

namespace VonNeumannAlgebra

open DensityMatrix

/-- `B(ℂⁿ)` acting on the second leg of `K ⊗̂ ℂⁿ`, i.e. `1 ⊗ B(ℂⁿ)`. -/
local notation "𝓜" => VonNeumannAlgebra.amplify K 𝓑(EuclideanSpace ℂ n)

variable (ρ σ : DensityMatrix n) {g : n → K}

/-- `√r` as a complex number. -/
local notation "√ᶜ" r => ((Real.sqrt r : ℝ) : ℂ)

private lemma sqrt_ne_zero {r : ℝ} (hr : 0 < r) : (√ᶜ r) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hr).ne'

/-- For `rᵢ > 0`, `s(Ω_ρ)` fixes `y ⊗ fᵢ`: it lies in `[𝓜′ Ω_ρ]`. -/
lemma supportProj_purification_tmul (hg : Orthonormal ℂ g) {i : n}
    (hi : 0 < ρ.isHermitian.eigenvalues i) (y : K) :
    (𝓜).supportProj (ρ.purification g) (y ⊗ₕ ρ.isHermitian.eigenvectorBasis i) =
      y ⊗ₕ ρ.isHermitian.eigenvectorBasis i := by
  rw [supportProj, Submodule.starProjection_eq_self_iff]
  have h := Submodule.smul_mem _ (√ᶜ ρ.isHermitian.eigenvalues i)⁻¹
    (InnerProductSpace.apply_mem_cyclicSubspace (ρ.purification g)
      (amplifyLeft_mem_commutant_amplify (M := 𝓑(EuclideanSpace ℂ n)) (rankOne ℂ y (g i))))
  rwa [ρ.amplifyLeft_rankOne_purification hg, smul_smul, inv_mul_cancel₀ (sqrt_ne_zero hi),
    one_smul] at h

/-- For `rᵢ > 0`, `s′(Ω_ρ)` fixes `gᵢ ⊗ x`: it lies in `[𝓜 Ω_ρ]`. -/
lemma supportProj_commutant_purification_tmul {i : n} (hi : 0 < ρ.isHermitian.eigenvalues i)
    (x : EuclideanSpace ℂ n) :
    (𝓜)′.supportProj (ρ.purification g) (g i ⊗ₕ x) = g i ⊗ₕ x := by
  rw [supportProj_commutant, Submodule.starProjection_eq_self_iff]
  have h := Submodule.smul_mem _ (√ᶜ ρ.isHermitian.eigenvalues i)⁻¹
    (InnerProductSpace.apply_mem_cyclicSubspace (ρ.purification g)
      (amplifyRight_mem_amplify (H₁ := K)
        (mem_boundedLinearOperators (rankOne ℂ x (ρ.isHermitian.eigenvectorBasis i)))))
  rwa [ρ.amplifyRight_rankOne_purification, smul_smul, inv_mul_cancel₀ (sqrt_ne_zero hi),
    one_smul] at h

variable {ρ σ}

/-- The relative Tomita operator `S_{Ω_σ, Ω_ρ}` of `1 ⊗ B(ℂⁿ)` sends `√rᵢ gᵢ ⊗ e_j` to
`√s_j g_j ⊗ fᵢ` (`rᵢ > 0`; `e`, `s` the eigendata of `σ`). -/
private lemma mem_graph_relativeTomita_purification (hg : Orthonormal ℂ g) {i : n}
    (hi : 0 < ρ.isHermitian.eigenvalues i) (j : n) :
    ((√ᶜ ρ.isHermitian.eigenvalues i) • (g i ⊗ₕ σ.isHermitian.eigenvectorBasis j),
        (√ᶜ σ.isHermitian.eigenvalues j) • (g j ⊗ₕ ρ.isHermitian.eigenvectorBasis i)) ∈
      ((𝓜).relativeTomita (σ.purification g) (ρ.purification g)).graph := by
  have h := apply_mem_graph_relativeTomita (η := σ.purification g) (ξ := ρ.purification g)
    (amplifyRight_mem_amplify (H₁ := K)
      (mem_boundedLinearOperators (rankOne ℂ (σ.isHermitian.eigenvectorBasis j) (ρ.isHermitian.eigenvectorBasis i))))
  rwa [ρ.amplifyRight_rankOne_purification, HilbertTensor.amplifyRight_star,
    ContinuousLinearMap.star_eq_adjoint, InnerProductSpace.adjoint_rankOne,
    σ.amplifyRight_rankOne_purification, map_smul, supportProj_purification_tmul ρ hg hi] at h

/-- The relative Tomita operator `F_{Ω_σ, Ω_ρ}` of the commutant sends `√rᵢ g_j ⊗ fᵢ` to
`√s_j gᵢ ⊗ e_j` (`rᵢ > 0`). -/
private lemma mem_graph_relativeTomita_commutant_purification [CompleteSpace K]
    (hg : Orthonormal ℂ g) {i : n} (hi : 0 < ρ.isHermitian.eigenvalues i) (j : n) :
    ((√ᶜ ρ.isHermitian.eigenvalues i) • (g j ⊗ₕ ρ.isHermitian.eigenvectorBasis i),
        (√ᶜ σ.isHermitian.eigenvalues j) • (g i ⊗ₕ σ.isHermitian.eigenvectorBasis j)) ∈
      ((𝓜)′.relativeTomita (σ.purification g) (ρ.purification g)).graph := by
  have h := apply_mem_graph_relativeTomita (M := (𝓜)′) (η := σ.purification g)
    (ξ := ρ.purification g) (amplifyLeft_mem_commutant_amplify (M := 𝓑(EuclideanSpace ℂ n)) (rankOne ℂ (g j) (g i)))
  rwa [ρ.amplifyLeft_rankOne_purification hg, HilbertTensor.amplifyLeft_star,
    ContinuousLinearMap.star_eq_adjoint, InnerProductSpace.adjoint_rankOne,
    σ.amplifyLeft_rankOne_purification hg, map_smul,
    supportProj_commutant_purification_tmul ρ hi] at h

/-- **The relative modular operator on eigenvectors.** For `rᵢ > 0`,
`Δ_{Ω_σ, Ω_ρ} (gᵢ ⊗ e_j) = (s_j / rᵢ) gᵢ ⊗ e_j`, i.e. `Δ = ρ̃⁻¹ ⊗ σ` on the support, where
`ρ̃ = Σᵢ rᵢ |gᵢ⟩⟨gᵢ|` acts on `K`. -/
theorem mem_graph_relativeModular_purification [CompleteSpace K] (hg : Orthonormal ℂ g) {i : n}
    (hi : 0 < ρ.isHermitian.eigenvalues i) (j : n) :
    (g i ⊗ₕ σ.isHermitian.eigenvectorBasis j,
        ((σ.isHermitian.eigenvalues j / ρ.isHermitian.eigenvalues i : ℝ) : ℂ) •
          (g i ⊗ₕ σ.isHermitian.eigenvectorBasis j)) ∈
      ((𝓜).relativeModular (σ.purification g) (ρ.purification g)).graph := by
  set r := ρ.isHermitian.eigenvalues i
  set t := σ.isHermitian.eigenvalues j
  have hr := (Real.sqrt_pos.mpr hi).ne'
  have hrr := Real.mul_self_sqrt hi.le
  have htt := Real.mul_self_sqrt (σ.eigenvalues_nonneg j)
  rw [mem_graph_relativeModular, LinearPMap.mem_graph_compNat]
  refine ⟨((Real.sqrt t / Real.sqrt r : ℝ) : ℂ) • (g j ⊗ₕ ρ.isHermitian.eigenvectorBasis i), ?_, ?_⟩
  · refine mem_graph_closure_relativeTomita ?_
    have h := isConjLinear_relativeTomita _ _ _ ((Real.sqrt r)⁻¹ : ℝ) _ _
      (mem_graph_relativeTomita_purification (σ := σ) hg hi j)
    rwa [Complex.conj_ofReal, smul_smul, smul_smul, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      inv_mul_cancel₀ hr, Complex.ofReal_one, one_smul, inv_mul_eq_div] at h
  · rw [LinearPMap.adjoint_closure (dense_domain_relativeTomita _ _ _)]
    refine LinearPMap.le_graph_of_le (relativeTomita_commutant_le_adjoint _ _ _) ?_
    have h := isConjLinear_relativeTomita _ _ _ ((Real.sqrt t / r : ℝ) : ℂ) _ _
      (mem_graph_relativeTomita_commutant_purification (σ := σ) hg hi j)
    have c₁ : Real.sqrt t / r * Real.sqrt r = Real.sqrt t / Real.sqrt r := by
      rw [div_mul_eq_mul_div, div_eq_div_iff hi.ne' hr]
      linear_combination Real.sqrt t * hrr
    have c₂ : Real.sqrt t / r * Real.sqrt t = t / r := by
      rw [div_mul_eq_mul_div, div_eq_div_iff hi.ne' hi.ne']
      linear_combination r * htt
    rwa [Complex.conj_ofReal, smul_smul, smul_smul, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      c₁, c₂] at h

variable (ρ σ) in
/-- `Ω_ρ = Σ_{i,j} √rᵢ ⟪e_j, fᵢ⟫ gᵢ ⊗ e_j`: the purification expanded in eigenvectors of
`Δ_{Ω_σ, Ω_ρ}`. -/
lemma purification_eq_sum_eigenvectorBasis :
    ρ.purification g = ∑ p : n × n,
      ((√ᶜ ρ.isHermitian.eigenvalues p.1) *
          ⟪σ.isHermitian.eigenvectorBasis p.2, ρ.isHermitian.eigenvectorBasis p.1⟫_ℂ) •
        (g p.1 ⊗ₕ σ.isHermitian.eigenvectorBasis p.2) := by
  rw [Fintype.sum_prod_type, purification]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_lhs => rw [← σ.isHermitian.eigenvectorBasis.sum_repr' (ρ.isHermitian.eigenvectorBasis i)]
  rw [← HilbertTensor.tmulRightL_apply, map_sum, Finset.smul_sum]
  simp only [map_smul, HilbertTensor.tmulRightL_apply, smul_smul]

variable (ρ σ) in
/-- **Spectral measure**: `μ_{Ω_ρ}` of `Δ_{Ω_σ, Ω_ρ}` is `Σ_{i,j} rᵢ |⟪e_j, fᵢ⟫|² δ_{s_j / rᵢ}`. -/
theorem spectralMeasure_relativeModular_purification [CompleteSpace K] (hg : Orthonormal ℂ g) :
    (isSelfAdjoint_relativeModular (𝓜) (σ.purification g) (ρ.purification g)).spectralMeasure
        (ρ.purification g) =
      ∑ p : n × n, (ρ.isHermitian.eigenvalues p.1 *
          ‖⟪σ.isHermitian.eigenvectorBasis p.2, ρ.isHermitian.eigenvectorBasis p.1⟫_ℂ‖ ^ 2).toNNReal •
        Measure.dirac (σ.isHermitian.eigenvalues p.2 / ρ.isHermitian.eigenvalues p.1) := by
  have he := σ.isHermitian.eigenvectorBasis.orthonormal
  have hnorm : ∀ p : n × n, ‖((√ᶜ ρ.isHermitian.eigenvalues p.1) *
      ⟪σ.isHermitian.eigenvectorBasis p.2, ρ.isHermitian.eigenvectorBasis p.1⟫_ℂ) •
        (g p.1 ⊗ₕ σ.isHermitian.eigenvectorBasis p.2)‖₊ ^ 2 =
      (ρ.isHermitian.eigenvalues p.1 *
        ‖⟪σ.isHermitian.eigenvectorBasis p.2, ρ.isHermitian.eigenvectorBasis p.1⟫_ℂ‖ ^ 2).toNNReal :=
    fun p => by
      ext
      rw [Real.coe_toNNReal _ (by positivity [ρ.eigenvalues_nonneg p.1]), NNReal.coe_pow,
        coe_nnnorm, norm_smul, HilbertTensor.norm_tmul, hg.1, he.1, mul_one, mul_one, norm_mul,
        Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
        Real.sq_sqrt (ρ.eigenvalues_nonneg p.1)]
  have hsum := purification_eq_sum_eigenvectorBasis (g := g) ρ σ
  calc _ = (isSelfAdjoint_relativeModular (𝓜) (σ.purification g) (ρ.purification g)).spectralMeasure
        (∑ p : n × n, ((√ᶜ ρ.isHermitian.eigenvalues p.1) *
          ⟪σ.isHermitian.eigenvectorBasis p.2, ρ.isHermitian.eigenvectorBasis p.1⟫_ℂ) •
            (g p.1 ⊗ₕ σ.isHermitian.eigenvectorBasis p.2)) := by rw [← hsum]
    _ = _ := by
      simp_rw [← hnorm]
      refine IsSelfAdjoint.spectralMeasure_sum_of_mem_graph _ Finset.univ (fun p _ => ?_)
        (fun p _ q _ hpq => ?_)
      · rcases (ρ.eigenvalues_nonneg p.1).eq_or_lt with h0 | hi
        · simp [← h0]
        · have := ((𝓜).relativeModular (σ.purification g) (ρ.purification g)).graph.smul_mem
            ((√ᶜ ρ.isHermitian.eigenvalues p.1) *
              ⟪σ.isHermitian.eigenvectorBasis p.2, ρ.isHermitian.eigenvectorBasis p.1⟫_ℂ)
            (mem_graph_relativeModular_purification hg hi p.2)
          rwa [Prod.smul_mk, smul_comm] at this
      · dsimp only
        rw [inner_smul_left, inner_smul_right, HilbertTensor.inner_tmul]
        rcases eq_or_ne p.1 q.1 with h₁ | h₁
        · rw [he.2 fun h₂ => hpq (Prod.ext h₁ h₂), mul_zero, mul_zero, mul_zero]
        · rw [hg.2 h₁, zero_mul, mul_zero, mul_zero]

variable (ρ σ) in
/-- **Araki's relative entropy is Umegaki's.** For density matrices `ρ, σ` and their purifications
along an orthonormal family `g` in `K`, `S_{1 ⊗ B(ℂⁿ)}(ω_{Ω_ρ} ‖ ω_{Ω_σ}) = D(ρ ‖ σ)`, including the
value `+∞` when `supp ρ ⊄ supp σ`. -/
theorem arakiVec_purification [CompleteSpace K] (hg : Orthonormal ℂ g) :
    (𝓜).arakiVec (ρ.purification g) (σ.purification g) = D(ρ ∥ σ) := by
  have hW : ∀ i j, ‖⟪σ.isHermitian.eigenvectorBasis j, ρ.isHermitian.eigenvectorBasis i⟫_ℂ‖ ^ 2 =
      Complex.normSq (Matrix.eigW ρ σ j i) := fun i j => by
    rw [Matrix.eigW_apply, Complex.normSq_eq_norm_sq]
  rw [arakiVec, spectralMeasure_relativeModular_purification ρ σ hg, Matrix.relativeEntropy]
  simp_rw [hW]
  by_cases hsupp : Matrix.suppSubset ρ.toMatrix σ.toMatrix
  · have ht : ∀ i j, ρ.isHermitian.eigenvalues i * Complex.normSq (Matrix.eigW ρ σ j i) ≠ 0 →
        σ.isHermitian.eigenvalues j ≠ 0 := fun i j h ht =>
      h (by
        rw [mul_comm]
        exact Matrix.normSq_eigW_mul_eigenvalues_eq_zero_of_suppSubset ρ σ hsupp j ht i)
    rw [ite_eq_left hsupp, negLogIntegral_finsetSum_smul_dirac _ _ fun p _ hp => ?_]
    · refine congrArg _ ?_
      change _ = (ρ.toMatrix * (DensityMatrix.log ρ - DensityMatrix.log σ)).trace.re
      rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re,
        Matrix.re_trace_mul_log_self_eq, Matrix.re_trace_mul_log_eq, Fintype.sum_prod_type]
      have hterm : ∀ i j,
          -(((ρ.isHermitian.eigenvalues i * Complex.normSq (Matrix.eigW ρ σ j i)).toNNReal : ℝ) *
            Real.log (σ.isHermitian.eigenvalues j / ρ.isHermitian.eigenvalues i)) =
          Complex.normSq (Matrix.eigW ρ σ j i) * ρ.isHermitian.eigenvalues i *
              Real.log (ρ.isHermitian.eigenvalues i) -
            Complex.normSq (Matrix.eigW ρ σ j i) * ρ.isHermitian.eigenvalues i *
              Real.log (σ.isHermitian.eigenvalues j) := fun i j => by
        rw [Real.coe_toNNReal _ (mul_nonneg (ρ.eigenvalues_nonneg i) (Complex.normSq_nonneg _))]
        by_cases h : ρ.isHermitian.eigenvalues i * Complex.normSq (Matrix.eigW ρ σ j i) = 0
        · rw [h, zero_mul, neg_zero, ← mul_sub, mul_comm (Complex.normSq _), h, zero_mul]
        · rw [Real.log_div (ht i j h) (left_ne_zero_of_mul h)]
          ring
      simp_rw [hterm, Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_mul, ← Finset.sum_mul, Matrix.sum_normSq_eigW_col, one_mul]
    · have hpos : 0 < ρ.isHermitian.eigenvalues p.1 * Complex.normSq (Matrix.eigW ρ σ p.2 p.1) :=
        Real.toNNReal_pos.mp (pos_iff_ne_zero.mpr hp)
      exact div_pos ((σ.eigenvalues_nonneg p.2).lt_of_ne' (ht _ _ hpos.ne'))
        ((ρ.eigenvalues_nonneg p.1).lt_of_ne' (left_ne_zero_of_mul hpos.ne'))
  · rw [ite_eq_right hsupp]
    obtain ⟨j, hj, i, hij⟩ : ∃ j, σ.isHermitian.eigenvalues j = 0 ∧
        ∃ i, Complex.normSq (Matrix.eigW ρ σ j i) * ρ.isHermitian.eigenvalues i ≠ 0 := by
      by_contra! h
      exact hsupp ((Matrix.suppSubset_iff_normSq_eigW_mul_eigenvalues_eq_zero ρ σ).mpr h)
    refine negLogIntegral_finsetSum_smul_dirac_eq_top (Finset.mem_univ (i, j)) ?_ (by simp [hj])
    rw [Ne, Real.toNNReal_eq_zero, not_le, mul_comm]
    exact (mul_nonneg (Complex.normSq_nonneg _) (ρ.eigenvalues_nonneg i)).lt_of_ne' hij

variable (ρ σ) in
/-- **Araki = Umegaki on `ℂⁿ ⊗̂ ℂⁿ`**, with the purifications along the standard basis. -/
theorem arakiVec_purification_basisFun :
    (VonNeumannAlgebra.amplify (EuclideanSpace ℂ n) 𝓑(EuclideanSpace ℂ n)).arakiVec
        (ρ.purification (EuclideanSpace.basisFun n ℂ)) (σ.purification (EuclideanSpace.basisFun n ℂ)) =
      D(ρ ∥ σ) :=
  arakiVec_purification ρ σ (EuclideanSpace.basisFun n ℂ).orthonormal

variable (ρ σ) in
/-- **Araki = Umegaki, for any representing vectors.** If `ξ, η ∈ K ⊗̂ ℂⁿ` represent `ρ` and `σ` on
`1 ⊗ B(ℂⁿ)` — `⟪ξ, (1 ⊗ A) ξ⟫ = Tr (ρ A)` and likewise for `η` — then
`S_{1 ⊗ B(ℂⁿ)}(ω_ξ ‖ ω_η) = D(ρ ‖ σ)`. The orthonormal family `g` makes `K` large enough to carry
the purifications through which the value is computed; the statement without it (`K` of dimension
only `≥ rank ρ, rank σ`) is not formalised. -/
theorem arakiVec_eq_relativeEntropy [CompleteSpace K] (hg : Orthonormal ℂ g)
    {ξ η : K ⊗̂ EuclideanSpace ℂ n}
    (hξ : ∀ A : Matrix n n ℂ,
      ⟪ξ, amplifyRight (Matrix.toEuclideanCLM (𝕜 := ℂ) A) ξ⟫_ℂ = Tr (ρ.toMatrix * A))
    (hη : ∀ A : Matrix n n ℂ,
      ⟪η, amplifyRight (Matrix.toEuclideanCLM (𝕜 := ℂ) A) η⟫_ℂ = Tr (σ.toMatrix * A)) :
    (𝓜).arakiVec ξ η = D(ρ ∥ σ) := by
  rw [← arakiVec_purification ρ σ hg]
  refine arakiVec_eq_of_inner_eq (fun y hy => inner_apply_eq_of_mem_amplify (fun x _ => ?_) hy)
    (fun y hy => inner_apply_eq_of_mem_amplify (fun x _ => ?_) hy)
  · obtain ⟨A, rfl⟩ : ∃ A, Matrix.toEuclideanCLM (𝕜 := ℂ) A = x :=
      ⟨(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)).symm x, StarAlgEquiv.apply_symm_apply _ _⟩
    rw [ρ.inner_purification_amplifyRight hg, hξ]
  · obtain ⟨A, rfl⟩ : ∃ A, Matrix.toEuclideanCLM (𝕜 := ℂ) A = x :=
      ⟨(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)).symm x, StarAlgEquiv.apply_symm_apply _ _⟩
    rw [σ.inner_purification_amplifyRight hg, hη]

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

namespace DensityMatrix

open VonNeumannAlgebra

/-- The **normal state** `A ↦ Tr (ρ A)` of `B(ℂⁿ)` defined by a density matrix, represented on
`ℓ²(ℕ) ⊗̂ ℂⁿ` by a purification. -/
noncomputable def normalState (ρ : DensityMatrix n) :
    𝓑(EuclideanSpace ℂ n).NormalFunctional :=
  NormalFunctional.ofAmplifiedVector 𝓑(EuclideanSpace ℂ n) (ρ.purification δₙ)

/-- `ω_ρ(A) = Tr (ρ A)`. -/
theorem normalState_apply (ρ : DensityMatrix n) (A : Matrix n n ℂ) :
    ρ.normalState.1 ⟨Matrix.toEuclideanCLM (𝕜 := ℂ) A, mem_boundedLinearOperators _⟩ = Tr (ρ.toMatrix * A) :=
  ρ.inner_purification_amplifyRight orthonormal_single_equivFin A

/-- `ω_ρ` is a state: `ω_ρ(1) = Tr ρ = 1`. -/
theorem normalState_apply_one (ρ : DensityMatrix n) : ρ.normalState.1 1 = 1 := by
  have h := ρ.normalState_apply 1
  rw [map_one, Matrix.mul_one, ρ.trace_eq_one] at h
  exact h

end DensityMatrix

namespace VonNeumannAlgebra

variable (ρ σ : DensityMatrix n)

/-- **Araki's relative entropy of normal states of `B(ℂⁿ)` is Umegaki's.** If the normal functionals
`ψ, φ` on `B(ℂⁿ)` are `A ↦ Tr (ρ A)` and `A ↦ Tr (σ A)`, then `S(ψ ‖ φ) = D(ρ ‖ σ)`. -/
theorem arakiEntropy_eq_relativeEntropy
    {ψ φ : 𝓑(EuclideanSpace ℂ n).NormalFunctional}
    (hψ : ∀ A : Matrix n n ℂ,
      ψ.1 ⟨Matrix.toEuclideanCLM (𝕜 := ℂ) A, mem_boundedLinearOperators _⟩ = Tr (ρ.toMatrix * A))
    (hφ : ∀ A : Matrix n n ℂ,
      φ.1 ⟨Matrix.toEuclideanCLM (𝕜 := ℂ) A, mem_boundedLinearOperators _⟩ = Tr (σ.toMatrix * A)) :
    S⟦ψ ∥ φ⟧ = D(ρ ∥ σ) := by
  refine (arakiEntropy_eq_arakiVec (Ξψ := ρ.purification δₙ) (Ξφ := σ.purification δₙ)
    (fun x => ?_) (fun x => ?_)).trans (arakiVec_purification ρ σ orthonormal_single_equivFin)
  · obtain ⟨A, hA⟩ := Matrix.toEuclideanCLM.surjective (x : EuclideanSpace ℂ n →L[ℂ] _)
    rw [show x = ⟨Matrix.toEuclideanCLM (𝕜 := ℂ) A, mem_boundedLinearOperators _⟩ from Subtype.ext hA.symm, hψ]
    exact ρ.inner_purification_amplifyRight orthonormal_single_equivFin A
  · obtain ⟨A, hA⟩ := Matrix.toEuclideanCLM.surjective (x : EuclideanSpace ℂ n →L[ℂ] _)
    rw [show x = ⟨Matrix.toEuclideanCLM (𝕜 := ℂ) A, mem_boundedLinearOperators _⟩ from Subtype.ext hA.symm, hφ]
    exact σ.inner_purification_amplifyRight orthonormal_single_equivFin A

/-- `S(ω_ρ ‖ ω_σ) = D(ρ ‖ σ)` for the normal states of two density matrices. -/
@[simp]
theorem arakiEntropy_normalState : S⟦ρ.normalState ∥ σ.normalState⟧ = D(ρ ∥ σ) :=
  arakiEntropy_eq_relativeEntropy ρ σ ρ.normalState_apply σ.normalState_apply

end VonNeumannAlgebra
