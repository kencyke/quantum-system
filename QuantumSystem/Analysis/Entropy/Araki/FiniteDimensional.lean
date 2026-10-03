/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.Entropy.Araki.Basic

/-!
# Araki's relative entropy on `B(H)` in finite dimension

Let `H` be a finite-dimensional complex Hilbert space and let `ρ, σ` be positive operators on `H`
with orthonormal eigenbases `b`, `c` and eigenvalues `r`, `s`; finite dimension enters only through
the finite index type `ι` of the bases. Araki's relative entropy of the
normal functionals `A ↦ Σᵢ rᵢ ⟪bᵢ, A bᵢ⟫ = tr(ρ A)` and `A ↦ Σⱼ sⱼ ⟪cⱼ, A cⱼ⟫ = tr(σ A)` of `𝓑(H)`
is the eigenvalue sum `Σᵢⱼ rᵢ |⟪cⱼ, bᵢ⟫|² (log rᵢ - log sⱼ)` when `supp ρ ⊆ supp σ`
(`VonNeumannAlgebra.arakiEntropy_boundedLinearOperators_eq_sum`). This is the computation behind
Umegaki's formula `tr ρ (log ρ - log σ)` for `umegakiEntropy`
(`QuantumSystem.Analysis.Entropy.Umegaki.Basic`); traces, the functional calculus and densities
enter only there. The eigenbases are arbitrary, not Mathlib's chosen
`LinearMap.IsSymmetric.eigenvectorBasis`, and share one index type `ι`.

## Setting

`B(H)` acts on `K ⊗̂ H` as `1 ⊗ B(H) = VonNeumannAlgebra.amplify K 𝓑(H)`. For `K = ℓ²(ℕ)` it is the
amplification on which `VonNeumannAlgebra.arakiEntropy` represents normal functionals. Given an
orthonormal family `g` in `K`, the **purification** `Ω_ρ = Σᵢ √rᵢ gᵢ ⊗ bᵢ`
(`OrthonormalBasis.purification`) represents `A ↦ Σᵢ rᵢ ⟪bᵢ, A bᵢ⟫`
(`OrthonormalBasis.inner_purification_amplifyRight`).

## Computation

The relative modular operator is `ρ̃⁻¹ ⊗ σ` on the support, `ρ̃ = Σᵢ rᵢ |gᵢ⟩⟨gᵢ|` acting on `K`:
`Δ_{Ω_σ, Ω_ρ} (gᵢ ⊗ cⱼ) = (sⱼ / rᵢ) gᵢ ⊗ cⱼ` for `rᵢ > 0`
(`VonNeumannAlgebra.mem_graph_relativeModular_purification`). Expanding
`Ω_ρ = Σᵢⱼ √rᵢ ⟪cⱼ, bᵢ⟫ gᵢ ⊗ cⱼ` gives the spectral measure
`μ_{Ω_ρ} = Σᵢⱼ rᵢ |⟪cⱼ, bᵢ⟫|² δ_{sⱼ / rᵢ}` (`VonNeumannAlgebra.measure_pvm_relativeModular_purification`),
and `∫ -log dμ_{Ω_ρ}` is the eigenvalue sum. When `supp ρ ⊄ supp σ` the entropy is `+∞`; that case
is `VonNeumannAlgebra.arakiEntropy_eq_top_of_apply_star_mul_self` and is not repeated here.

## Main definitions

* `OrthonormalBasis.purification b r g` — the purification `Σᵢ √rᵢ gᵢ ⊗ bᵢ ∈ K ⊗̂ H`.

## Main results

* `OrthonormalBasis.inner_purification_amplifyRight` — `⟪Ω_ρ, (1 ⊗ A) Ω_ρ⟫ = Σᵢ rᵢ ⟪bᵢ, A bᵢ⟫`.
* `VonNeumannAlgebra.mem_graph_relativeModular_purification` — the eigenvectors of `Δ_{Ω_σ, Ω_ρ}`.
* `VonNeumannAlgebra.measure_pvm_relativeModular_purification` — the spectral measure.
* `VonNeumannAlgebra.arakiVec_purification` — `S_{1 ⊗ B(H)}(ω_{Ω_ρ} ‖ ω_{Ω_σ})` is the eigenvalue
  sum when `supp ρ ⊆ supp σ`.
* `VonNeumannAlgebra.arakiEntropy_boundedLinearOperators_eq_sum` — the same for normal functionals
  of `𝓑(H)`.
-/

@[expose] public section

open ClosedSubmodule MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace VonNeumannAlgebra HilbertTensor Araki ComplexOrder
open InnerProductSpace (cyclicSubspace rankOne)
open HilbertTensor (amplifyLeft amplifyRight)

variable {ι : Type*} [Fintype ι]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- `√r` as a complex number. -/
local notation "√ᶜ" r => ((Real.sqrt r : ℝ) : ℂ)

namespace OrthonormalBasis

/-- The vector `Σᵢ √rᵢ gᵢ ⊗ bᵢ ∈ K ⊗̂ H` built from an orthonormal basis `b` of `H`, weights `r` and
a family `g` in `K`. For an orthonormal eigenbasis `b` of a positive operator `ρ` with eigenvalues
`r` and orthonormal `g`, it is a **purification** of `ρ`: it represents the positive functional
`A ↦ Σᵢ rᵢ ⟪bᵢ, A bᵢ⟫ = tr(ρ A)` of `1 ⊗ B(H)`
(`OrthonormalBasis.inner_purification_amplifyRight`). -/
noncomputable def purification (b : OrthonormalBasis ι ℂ H) (r : ι → ℝ) (g : ι → K) : K ⊗̂ H :=
  ∑ i, (√ᶜ r i) • (g i ⊗ₕ b i)

variable (b : OrthonormalBasis ι ℂ H) (r : ι → ℝ) {g : ι → K}

/-- `(1 ⊗ |x⟩⟨bᵢ|) Ω = √rᵢ gᵢ ⊗ x`. -/
lemma amplifyRight_rankOne_purification (x : H) (i : ι) :
    amplifyRight (rankOne ℂ x (b i)) (b.purification r g) = (√ᶜ r i) • (g i ⊗ₕ x) := by
  classical
  have hf := b.orthonormal
  simp only [purification, map_sum, map_smul, HilbertTensor.amplifyRight_tmul,
    InnerProductSpace.rankOne_apply]
  rw [Finset.sum_eq_single i (fun k _ hk => by
      rw [hf.2 hk.symm, zero_smul, HilbertTensor.tmul_zero, smul_zero]) (by simp),
    orthonormal_iff_ite.mp hf i i]
  simp

/-- `(|y⟩⟨gᵢ| ⊗ 1) Ω = √rᵢ y ⊗ bᵢ` for orthonormal `g`. -/
lemma amplifyLeft_rankOne_purification (hg : Orthonormal ℂ g) (y : K) (i : ι) :
    amplifyLeft (rankOne ℂ y (g i)) (b.purification r g) = (√ᶜ r i) • (y ⊗ₕ b i) := by
  classical
  simp only [purification, map_sum, map_smul, HilbertTensor.amplifyLeft_tmul,
    InnerProductSpace.rankOne_apply]
  rw [Finset.sum_eq_single i (fun k _ hk => by
      rw [hg.2 hk.symm, zero_smul, HilbertTensor.zero_tmul, smul_zero]) (by simp),
    orthonormal_iff_ite.mp hg i i]
  simp

/-- **The purification represents the weighted functional**: for nonnegative weights and
orthonormal `g`, `⟪Ω, (1 ⊗ A) Ω⟫ = Σᵢ rᵢ ⟪bᵢ, A bᵢ⟫`. -/
theorem inner_purification_amplifyRight (hr : ∀ i, 0 ≤ r i) (hg : Orthonormal ℂ g)
    (A : H →L[ℂ] H) :
    ⟪b.purification r g, amplifyRight A (b.purification r g)⟫_ℂ =
      ∑ i, (r i : ℂ) * ⟪b i, A (b i)⟫_ℂ := by
  classical
  simp only [purification, map_sum, map_smul, HilbertTensor.amplifyRight_tmul, sum_inner,
    inner_sum, inner_smul_left, inner_smul_right, HilbertTensor.inner_tmul,
    orthonormal_iff_ite.mp hg, ite_mul, one_mul, zero_mul, Complex.conj_ofReal, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_assoc, ← Complex.ofReal_mul, Real.mul_self_sqrt (hr i)]

end OrthonormalBasis

namespace VonNeumannAlgebra

/-- `B(H)` acting on the second leg of `K ⊗̂ H`, i.e. `1 ⊗ B(H)`. -/
local notation "𝓜" => VonNeumannAlgebra.amplify K 𝓑(H)

variable [CompleteSpace H] {b c : OrthonormalBasis ι ℂ H} {r s : ι → ℝ} {g : ι → K}

private lemma sqrt_ne_zero {r : ℝ} (hr : 0 < r) : (√ᶜ r) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hr).ne'

variable (b r) in
/-- For `rᵢ > 0`, `s(Ω)` fixes `y ⊗ bᵢ`: it lies in `[𝓜′ Ω]`. -/
lemma supportProj_purification_tmul (hg : Orthonormal ℂ g) {i : ι} (hi : 0 < r i) (y : K) :
    (𝓜).supportProj (b.purification r g) (y ⊗ₕ b i) = y ⊗ₕ b i := by
  rw [supportProj, Submodule.starProjection_eq_self_iff]
  have h := Submodule.smul_mem _ (√ᶜ r i)⁻¹
    (InnerProductSpace.apply_mem_cyclicSubspace (b.purification r g)
      (amplifyLeft_mem_commutant_amplify (M := 𝓑(H)) (rankOne ℂ y (g i))))
  rwa [b.amplifyLeft_rankOne_purification r hg, smul_smul, inv_mul_cancel₀ (sqrt_ne_zero hi),
    one_smul] at h

variable (b r) in
/-- For `rᵢ > 0`, `s′(Ω)` fixes `gᵢ ⊗ x`: it lies in `[𝓜 Ω]`. -/
lemma supportProj_commutant_purification_tmul {i : ι} (hi : 0 < r i) (x : H) :
    (𝓜)′.supportProj (b.purification r g) (g i ⊗ₕ x) = g i ⊗ₕ x := by
  rw [supportProj_commutant, Submodule.starProjection_eq_self_iff]
  have h := Submodule.smul_mem _ (√ᶜ r i)⁻¹
    (InnerProductSpace.apply_mem_cyclicSubspace (b.purification r g)
      (amplifyRight_mem_amplify (H₁ := K) (mem_boundedLinearOperators (rankOne ℂ x (b i)))))
  rwa [b.amplifyRight_rankOne_purification, smul_smul, inv_mul_cancel₀ (sqrt_ne_zero hi),
    one_smul] at h

/-- The relative Tomita operator `S_{Ω_σ, Ω_ρ}` of `1 ⊗ B(H)` sends `√rᵢ gᵢ ⊗ cⱼ` to `√sⱼ gⱼ ⊗ bᵢ`
(`rᵢ > 0`). -/
private lemma mem_graph_relativeTomita_purification (hg : Orthonormal ℂ g) {i : ι} (hi : 0 < r i)
    (j : ι) :
    ((√ᶜ r i) • (g i ⊗ₕ c j), (√ᶜ s j) • (g j ⊗ₕ b i)) ∈
      ((𝓜).relativeTomita (c.purification s g) (b.purification r g)).graph := by
  have h := apply_mem_graph_relativeTomita (η := c.purification s g) (ξ := b.purification r g)
    (amplifyRight_mem_amplify (H₁ := K) (mem_boundedLinearOperators (rankOne ℂ (c j) (b i))))
  rwa [b.amplifyRight_rankOne_purification, HilbertTensor.amplifyRight_star,
    ContinuousLinearMap.star_eq_adjoint, InnerProductSpace.adjoint_rankOne,
    c.amplifyRight_rankOne_purification, map_smul, supportProj_purification_tmul b r hg hi] at h

/-- The relative Tomita operator `F_{Ω_σ, Ω_ρ}` of the commutant sends `√rᵢ gⱼ ⊗ bᵢ` to
`√sⱼ gᵢ ⊗ cⱼ` (`rᵢ > 0`). -/
private lemma mem_graph_relativeTomita_commutant_purification [CompleteSpace K]
    (hg : Orthonormal ℂ g) {i : ι} (hi : 0 < r i) (j : ι) :
    ((√ᶜ r i) • (g j ⊗ₕ b i), (√ᶜ s j) • (g i ⊗ₕ c j)) ∈
      ((𝓜)′.relativeTomita (c.purification s g) (b.purification r g)).graph := by
  have h := apply_mem_graph_relativeTomita (M := (𝓜)′) (η := c.purification s g)
    (ξ := b.purification r g)
    (amplifyLeft_mem_commutant_amplify (M := 𝓑(H)) (rankOne ℂ (g j) (g i)))
  rwa [b.amplifyLeft_rankOne_purification r hg, HilbertTensor.amplifyLeft_star,
    ContinuousLinearMap.star_eq_adjoint, InnerProductSpace.adjoint_rankOne,
    c.amplifyLeft_rankOne_purification s hg, map_smul,
    supportProj_commutant_purification_tmul b r hi] at h

/-- **The relative modular operator on eigenvectors.** For `rᵢ > 0` and `sⱼ ≥ 0`,
`Δ_{Ω_σ, Ω_ρ} (gᵢ ⊗ cⱼ) = (sⱼ / rᵢ) gᵢ ⊗ cⱼ`, i.e. `Δ = ρ̃⁻¹ ⊗ σ` on the support, where
`ρ̃ = Σᵢ rᵢ |gᵢ⟩⟨gᵢ|` acts on `K`. -/
theorem mem_graph_relativeModular_purification [CompleteSpace K] (hs : ∀ j, 0 ≤ s j)
    (hg : Orthonormal ℂ g) {i : ι} (hi : 0 < r i) (j : ι) :
    (g i ⊗ₕ c j, ((s j / r i : ℝ) : ℂ) • (g i ⊗ₕ c j)) ∈
      ((𝓜).relativeModular (c.purification s g) (b.purification r g)).graph := by
  have hr := (Real.sqrt_pos.mpr hi).ne'
  have hrr := Real.mul_self_sqrt hi.le
  have htt := Real.mul_self_sqrt (hs j)
  rw [mem_graph_relativeModular, LinearPMap.mem_graph_compNat]
  refine ⟨((Real.sqrt (s j) / Real.sqrt (r i) : ℝ) : ℂ) • (g j ⊗ₕ b i), ?_, ?_⟩
  · refine mem_graph_closure_relativeTomita ?_
    have h := isConjLinear_relativeTomita _ _ _ ((Real.sqrt (r i))⁻¹ : ℝ) _ _
      (mem_graph_relativeTomita_purification (b := b) (c := c) (s := s) hg hi j)
    rwa [Complex.conj_ofReal, smul_smul, smul_smul, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      inv_mul_cancel₀ hr, Complex.ofReal_one, one_smul, inv_mul_eq_div] at h
  · rw [LinearPMap.adjoint_closure (dense_domain_relativeTomita _ _ _)]
    refine LinearPMap.le_graph_of_le (relativeTomita_commutant_le_adjoint _ _ _) ?_
    have h := isConjLinear_relativeTomita _ _ _ ((Real.sqrt (s j) / r i : ℝ) : ℂ) _ _
      (mem_graph_relativeTomita_commutant_purification (b := b) (c := c) (s := s) hg hi j)
    have c₁ : Real.sqrt (s j) / r i * Real.sqrt (r i) = Real.sqrt (s j) / Real.sqrt (r i) := by
      rw [div_mul_eq_mul_div, div_eq_div_iff hi.ne' hr]
      linear_combination Real.sqrt (s j) * hrr
    have c₂ : Real.sqrt (s j) / r i * Real.sqrt (s j) = s j / r i := by
      rw [div_mul_eq_mul_div, div_eq_div_iff hi.ne' hi.ne']
      linear_combination r i * htt
    rwa [Complex.conj_ofReal, smul_smul, smul_smul, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      c₁, c₂] at h

omit [CompleteSpace H] in
variable (b c r) in
/-- `Ω_ρ = Σᵢⱼ √rᵢ ⟪cⱼ, bᵢ⟫ gᵢ ⊗ cⱼ`: the purification expanded in eigenvectors of
`Δ_{Ω_σ, Ω_ρ}`. -/
lemma purification_eq_sum :
    b.purification r g =
      ∑ p : ι × ι, ((√ᶜ r p.1) * ⟪c p.2, b p.1⟫_ℂ) • (g p.1 ⊗ₕ c p.2) := by
  rw [Fintype.sum_prod_type, OrthonormalBasis.purification]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_lhs => rw [← c.sum_repr' (b i)]
  rw [← HilbertTensor.tmulRightL_apply, map_sum, Finset.smul_sum]
  simp only [map_smul, HilbertTensor.tmulRightL_apply, smul_smul]

/-- **Spectral measure**: `μ_{Ω_ρ}` of `Δ_{Ω_σ, Ω_ρ}` is `Σᵢⱼ rᵢ |⟪cⱼ, bᵢ⟫|² δ_{sⱼ / rᵢ}`. -/
theorem measure_pvm_relativeModular_purification [CompleteSpace K] (hr : ∀ i, 0 ≤ r i)
    (hs : ∀ j, 0 ≤ s j) (hg : Orthonormal ℂ g) :
    (isSelfAdjoint_relativeModular (𝓜) (c.purification s g) (b.purification r g)).pvm.measure
        (b.purification r g) =
      ∑ p : ι × ι, (r p.1 * ‖⟪c p.2, b p.1⟫_ℂ‖ ^ 2).toNNReal • Measure.dirac (s p.2 / r p.1) := by
  have he := c.orthonormal
  have hnorm : ∀ p : ι × ι, ‖((√ᶜ r p.1) * ⟪c p.2, b p.1⟫_ℂ) • (g p.1 ⊗ₕ c p.2)‖₊ ^ 2 =
      (r p.1 * ‖⟪c p.2, b p.1⟫_ℂ‖ ^ 2).toNNReal := fun p => by
    ext
    rw [Real.coe_toNNReal _ (by positivity [hr p.1]), NNReal.coe_pow, coe_nnnorm, norm_smul,
      HilbertTensor.norm_tmul, hg.1, he.1, mul_one, mul_one, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (hr p.1)]
  have hsum := purification_eq_sum (g := g) b c r
  calc _ = (isSelfAdjoint_relativeModular (𝓜) (c.purification s g) (b.purification r g)).pvm.measure
        (∑ p : ι × ι, ((√ᶜ r p.1) * ⟪c p.2, b p.1⟫_ℂ) • (g p.1 ⊗ₕ c p.2)) := by rw [← hsum]
    _ = _ := by
      simp_rw [← hnorm]
      refine IsSelfAdjoint.measure_pvm_sum_of_mem_graph _ Finset.univ (fun p _ => ?_)
        (fun p _ q _ hpq => ?_)
      · rcases (hr p.1).eq_or_lt with h0 | hi
        · simp [← h0]
        · have := ((𝓜).relativeModular (c.purification s g) (b.purification r g)).graph.smul_mem
            ((√ᶜ r p.1) * ⟪c p.2, b p.1⟫_ℂ)
            (mem_graph_relativeModular_purification (b := b) hs hg hi p.2)
          rwa [Prod.smul_mk, smul_comm] at this
      · dsimp only
        rw [inner_smul_left, inner_smul_right, HilbertTensor.inner_tmul]
        rcases eq_or_ne p.1 q.1 with h₁ | h₁
        · rw [he.2 fun h₂ => hpq (Prod.ext h₁ h₂), mul_zero, mul_zero, mul_zero]
        · rw [hg.2 h₁, zero_mul, mul_zero, mul_zero]

/-- **Araki's relative entropy of purifications is the eigenvalue sum.** For nonnegative weights
with `rᵢ |⟪cⱼ, bᵢ⟫|² = 0` whenever `sⱼ = 0` (the support condition `supp ρ ⊆ supp σ`) and
orthonormal `g`, `S_{1 ⊗ B(H)}(ω_{Ω_ρ} ‖ ω_{Ω_σ}) = Σᵢⱼ rᵢ |⟪cⱼ, bᵢ⟫|² (log rᵢ - log sⱼ)`. -/
theorem arakiVec_purification [CompleteSpace K] (hr : ∀ i, 0 ≤ r i) (hs : ∀ j, 0 ≤ s j)
    (hg : Orthonormal ℂ g) (hsupp : ∀ i j, s j = 0 → r i * ‖⟪c j, b i⟫_ℂ‖ ^ 2 = 0) :
    (𝓜).arakiVec (b.purification r g) (c.purification s g) =
      ((∑ i, ∑ j, r i * ‖⟪c j, b i⟫_ℂ‖ ^ 2 * (Real.log (r i) - Real.log (s j)) : ℝ) : EReal) := by
  rw [arakiVec, measure_pvm_relativeModular_purification hr hs hg]
  have ht : ∀ i j, r i * ‖⟪c j, b i⟫_ℂ‖ ^ 2 ≠ 0 → s j ≠ 0 := fun i j h hj => h (hsupp i j hj)
  rw [negLogIntegral_finsetSum_smul_dirac _ _ fun p _ hp => ?_]
  · refine congrArg _ ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Real.coe_toNNReal _ (by positivity [hr i])]
    by_cases h : r i * ‖⟪c j, b i⟫_ℂ‖ ^ 2 = 0
    · rw [h, zero_mul, zero_mul, neg_zero]
    · rw [Real.log_div (ht i j h) (left_ne_zero_of_mul h)]
      ring
  · have hpos : 0 < r p.1 * ‖⟪c p.2, b p.1⟫_ℂ‖ ^ 2 := Real.toNNReal_pos.mp (pos_iff_ne_zero.mpr hp)
    exact div_pos ((hs p.2).lt_of_ne' (ht _ _ hpos.ne')) ((hr p.1).lt_of_ne'
      (left_ne_zero_of_mul hpos.ne'))

/-- `δ_ι` is the orthonormal family `i ↦ e_{k(i)}` of `ℓ²(ℕ)` indexed by the finite type `ι`, where
`k = Fin.val ∘ Fintype.equivFin ι : ι → ℕ` is injective. -/
local notation "δ_ι" => fun i => lp.single (E := fun _ : ℕ => ℂ) 2 (Fintype.equivFin ι i : ℕ) (1 : ℂ)

/-- The family `δ_ι` is orthonormal in `ℓ²(ℕ)`. -/
private theorem orthonormal_single_equivFin : Orthonormal ℂ (δ_ι : ι → lp (fun _ : ℕ => ℂ) 2) :=
  lp.orthonormal_single.comp _ (Fin.val_injective.comp (Fintype.equivFin ι).injective)

/-- **Araki's relative entropy on `𝓑(H)` is the eigenvalue sum.** If `ψ(A) = Σᵢ rᵢ ⟪bᵢ, A bᵢ⟫` and
`φ(A) = Σⱼ sⱼ ⟪cⱼ, A cⱼ⟫` for orthonormal bases `b, c` and nonnegative weights with
`rᵢ |⟪cⱼ, bᵢ⟫|² = 0` whenever `sⱼ = 0`, then `S(ψ ‖ φ) = Σᵢⱼ rᵢ |⟪cⱼ, bᵢ⟫|² (log rᵢ - log sⱼ)`. -/
theorem arakiEntropy_boundedLinearOperators_eq_sum {ψ φ : 𝓑(H).NormalFunctional}
    (hr : ∀ i, 0 ≤ r i) (hs : ∀ j, 0 ≤ s j)
    (hψ : ∀ x : 𝓑(H), ψ.1 x = ∑ i, (r i : ℂ) * ⟪b i, (x : H →L[ℂ] H) (b i)⟫_ℂ)
    (hφ : ∀ x : 𝓑(H), φ.1 x = ∑ j, (s j : ℂ) * ⟪c j, (x : H →L[ℂ] H) (c j)⟫_ℂ)
    (hsupp : ∀ i j, s j = 0 → r i * ‖⟪c j, b i⟫_ℂ‖ ^ 2 = 0) :
    S⟦ψ ∥ φ⟧ =
      ((∑ i, ∑ j, r i * ‖⟪c j, b i⟫_ℂ‖ ^ 2 * (Real.log (r i) - Real.log (s j)) : ℝ) : EReal) :=
  (arakiEntropy_eq_arakiVec (Ξψ := b.purification r δ_ι) (Ξφ := c.purification s δ_ι)
    (fun x => (b.inner_purification_amplifyRight r hr orthonormal_single_equivFin x).trans
      (hψ x).symm)
    (fun x => (c.inner_purification_amplifyRight s hs orthonormal_single_equivFin x).trans
      (hφ x).symm)).trans (arakiVec_purification hr hs orthonormal_single_equivFin hsupp)

end VonNeumannAlgebra
