/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.Entropy.Araki.Basic
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.SchwarzMap

/-!
# Monotonicity of Araki's relative entropy

The **data-processing inequality** (Uhlmann's monotonicity theorem): for von Neumann algebras
`N ⊆ B(K)`, `M ⊆ B(H)`, a unital normal Schwarz map `α : N → M` and normal positive functionals
`ψ, φ` on `M`,
`S(ψ ∘ α ‖ φ ∘ α) ≤ S(ψ ‖ φ)`
(`VonNeumannAlgebra.arakiEntropy_comp_le`). Unitality `α 1 = 1` cannot be dropped: `½ • id` is a
Schwarz map, and `S(½ψ ‖ ½φ) = ½ S(ψ ‖ φ)` is smaller than `S(ψ ‖ φ)` only when `S(ψ ‖ φ) ≥ 0`.

## Proof (Petz)

Let `ψ ∘ α = ω_ζ`, `φ ∘ α = ω_ζ'` on `N` and `ψ = ω_ξ`, `φ = ω_ξ'` on `M`, and let
`S_N = S_{ζ',ζ}`, `S_M = S_{ξ',ξ}` be the relative Tomita operators, `Δ_N`, `Δ_M` the relative
modular operators. Petz's map `V : y ζ ↦ α(y) ξ` is a contraction with `V† ξ = ζ` by the
Kadison–Schwarz inequality, and `‖S_M V u‖ ≤ ‖S_N u‖`. In the non-faithful case one writes
`y ζ = (y s) ζ` with `s = s(ζ) ∈ N`: then `S_M α(y s) ξ = s(ξ) α(s y⋆) ξ'` and
`‖α(s y⋆) ξ'‖ ≤ ‖s y⋆ ζ'‖ = ‖S_N (y ζ)‖`
(`VonNeumannAlgebra.integral_inv_add_spectralMeasure_relativeModular_le`). The variational formula
for resolvents turns this into `⟪ζ, (t + Δ_N)⁻¹ ζ⟫ ≤ ⟪ξ, (t + Δ_M)⁻¹ ξ⟫` for `t > 0`
(`IsSelfAdjoint.integral_inv_add_spectralMeasure_le_of_forall_mem_graph`), and the representation
`-log λ = ∫_{t > 0} ((t + λ)⁻¹ - (1 + t)⁻¹) dt` integrates it to
`-⟪ζ, log Δ_N ζ⟫ ≤ -⟪ξ, log Δ_M ξ⟫` (`MeasureTheory.negLogIntegral_le_of_integral_inv_add_le`).
Normal functionals reduce to this through the amplification by `ℓ²(ℕ)`, along which `α` lifts to
the Schwarz map `1 ⊗ α` (`VonNeumannAlgebra.amplifySchwarzMap`, built from the `⋆`-isomorphisms
`VonNeumannAlgebra.amplifyEquiv`).

The map `V` is never built as an operator: the comparison of resolvents only needs, for each point
of the graph of `S_B`, a dominating point of the graph of `S_A`.

## Main results

* `VonNeumannAlgebra.norm_schwarzMap_apply_apply_le` — the vector bound `‖α(y) ξ‖ ≤ ‖y ζ‖` when
  `ω_ξ ∘ α = ω_ζ`.
* `VonNeumannAlgebra.integral_inv_add_spectralMeasure_relativeModular_le` — Petz's resolvent
  inequality `⟪ζ, (t + Δ_{ζ',ζ})⁻¹ ζ⟫ ≤ ⟪ξ, (t + Δ_{ξ',ξ})⁻¹ ξ⟫`.
* `VonNeumannAlgebra.arakiVec_le_of_schwarzMap` — the data-processing inequality for vector
  functionals: `S_N(ω_ζ ‖ ω_ζ') ≤ S_M(ω_ξ ‖ ω_ξ')` when `ω_ξ ∘ α = ω_ζ`, `ω_ξ' ∘ α = ω_ζ'`.
* `VonNeumannAlgebra.amplifySchwarzMap` — the Schwarz map `1 ⊗ α` between the amplifications.
* `VonNeumannAlgebra.arakiEntropy_comp_le` — the **data-processing inequality**
  `S(ψ ∘ α ‖ φ ∘ α) ≤ S(ψ ‖ φ)` for unital normal Schwarz maps.

Not formalised: the equality case (sufficiency of `α`, Petz recovery map), which needs the
modular automorphism groups.

## References

* A. Uhlmann, *Relative entropy and the Wigner–Yanase–Dyson–Lieb concavity in an interpolation
  theory*, Comm. Math. Phys. 54 (1977), 21–32.
* D. Petz, *Sufficient subalgebras and the relative entropy of states of a von Neumann algebra*,
  Comm. Math. Phys. 105 (1986), 123–131.
* M. Ohya, D. Petz, *Quantum Entropy and Its Use*, Theorem 5.3.
-/

@[expose] public section

open Complex MeasureTheory
open scoped InnerProductSpace ComplexOrder VonNeumannAlgebra HilbertTensor Araki
open HilbertTensor (amplifyRight)

namespace VonNeumannAlgebra

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}

/-- `⟪ξ, x⋆ x ξ⟫ = ‖x ξ‖²`. -/
private lemma inner_star_mul_self_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (x : E →L[ℂ] E) (ξ : E) :
    ⟪ξ, (star x * x) ξ⟫_ℂ = ((‖x ξ‖ ^ 2 : ℝ) : ℂ) := by
  rw [ContinuousLinearMap.star_eq_adjoint, mul_apply_eq_comp,
    ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast

/-! ### Vector functionals -/

section Vector

variable (α : SchwarzMap N M)

/-- **Contractivity of Petz's map** `y ζ ↦ α(y) ξ`: if `ω_ξ ∘ α = ω_ζ` on `N`, then
`‖α(y) ξ‖ ≤ ‖y ζ‖`, by the Kadison–Schwarz inequality `α(y)⋆ α(y) ≤ α(y⋆ y)`. -/
theorem norm_schwarzMap_apply_apply_le {ζ : K} {ξ : H}
    (hξ : ∀ y : N, ⟪ζ, (y : K →L[ℂ] K) ζ⟫_ℂ = ⟪ξ, (α y : H →L[ℂ] H) ξ⟫_ℂ) (y : N) :
    ‖(α y : H →L[ℂ] H) ξ‖ ≤ ‖(y : K →L[ℂ] K) ζ‖ := by
  have hle := OrderHomClass.mono (M.vectorFunctional ξ) (SchwarzMapClass.le_map_star_mul α y)
  rw [vectorFunctional_apply, vectorFunctional_apply, ← hξ, MulMemClass.coe_mul,
    StarMemClass.coe_star, MulMemClass.coe_mul, StarMemClass.coe_star, inner_star_mul_self_apply,
    inner_star_mul_self_apply, Complex.real_le_real] at hle
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hle

/-- **Petz's resolvent inequality.** Let `α : N → M` be a Schwarz map and `ζ, ζ' ∈ K`,
`ξ, ξ' ∈ H` with `ω_ξ ∘ α = ω_ζ` and `ω_ξ' ∘ α = ω_ζ'` on `N`. Then for `t > 0`,
`⟪ζ, (t + Δ_{ζ',ζ})⁻¹ ζ⟫ ≤ ⟪ξ, (t + Δ_{ξ',ξ})⁻¹ ξ⟫`, in the spectral form
`∫ (t + λ)⁻¹ dμ_ζ ≤ ∫ (t + λ)⁻¹ dμ_ξ`.

The point `(y ζ + z, s(ζ) y⋆ ζ')` of the graph of `S_{ζ',ζ}` (`y ∈ N`, `z ⊥ [N ζ]`) is dominated
by the point `(x ξ, s(ξ) x⋆ ξ')` of the graph of `S_{ξ',ξ}` for `x = α(y s(ζ))`. -/
theorem integral_inv_add_spectralMeasure_relativeModular_le {ζ ζ' : K} {ξ ξ' : H}
    (hξ : ∀ y : N, ⟪ζ, (y : K →L[ℂ] K) ζ⟫_ℂ = ⟪ξ, (α y : H →L[ℂ] H) ξ⟫_ℂ)
    (hξ' : ∀ y : N, ⟪ζ', (y : K →L[ℂ] K) ζ'⟫_ℂ = ⟪ξ', (α y : H →L[ℂ] H) ξ'⟫_ℂ) {t : ℝ}
    (ht : 0 < t) :
    ∫ s, (t + s)⁻¹ ∂(isSelfAdjoint_relativeModular N ζ' ζ).spectralMeasure ζ ≤
      ∫ s, (t + s)⁻¹ ∂(isSelfAdjoint_relativeModular M ξ' ξ).spectralMeasure ξ := by
  refine (isSelfAdjoint_relativeModular M ξ' ξ).integral_inv_add_spectralMeasure_le_of_forall_mem_graph
    (restrictScalars_relativeModular M ξ' ξ) (isSelfAdjoint_relativeModular N ζ' ζ)
    (isClosable_relativeTomita N ζ' ζ) (restrictScalars_relativeModular N ζ' ζ) ξ ζ ?_ ht
  intro w w' hw
  obtain ⟨y, hy, z, hz, h⟩ := mem_graph_relativeTomita.mp hw
  obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp h
  set e := N.supportProj ζ
  have he : e ζ = ζ := N.supportProj_apply_self ζ
  set b : N := ⟨y * e, mul_mem hy (N.supportProj_mem ζ)⟩
  have hb : (b : K →L[ℂ] K) ζ = y ζ := by
    change (y * e) ζ = y ζ
    rw [mul_apply_eq_comp, he]
  have hbs : ((star b : N) : K →L[ℂ] K) ζ' = e (star y ζ') := by
    change star (y * e) ζ' = e (star y ζ')
    rw [star_mul, (N.isStarProjection_supportProj ζ).isSelfAdjoint.star_eq, mul_apply_eq_comp]
  set x : H →L[ℂ] H := (α b : H →L[ℂ] H)
  have hK : y ζ ∈ (InnerProductSpace.cyclicSubspace (N : Set (K →L[ℂ] K)) ζ).toSubmodule :=
    InnerProductSpace.apply_mem_cyclicSubspace ζ hy
  have hK₁ : ζ ∈ (InnerProductSpace.cyclicSubspace (N : Set (K →L[ℂ] K)) ζ).toSubmodule :=
    self_mem_cyclicSubspace N ζ
  refine ⟨x ξ, M.supportProj ξ (star x ξ'),
    mem_graph_closure_relativeTomita (apply_mem_graph_relativeTomita (α b).2), ?_, ?_, ?_⟩
  · -- `‖α(y s) ξ‖ ≤ ‖y s ζ‖ = ‖y ζ‖ ≤ ‖y ζ + z‖`.
    have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) (y ζ) z
      (Submodule.inner_right_of_mem_orthogonal hK hz)
    calc ‖x ξ‖ ≤ ‖(b : K →L[ℂ] K) ζ‖ := norm_schwarzMap_apply_apply_le α hξ b
      _ = ‖y ζ‖ := by rw [hb]
      _ ≤ ‖y ζ + z‖ := by nlinarith [norm_nonneg (y ζ), norm_nonneg (y ζ + z), norm_nonneg z]
  · -- `‖s(ξ) α(y s)⋆ ξ'‖ ≤ ‖α(s y⋆) ξ'‖ ≤ ‖s y⋆ ζ'‖`.
    calc ‖M.supportProj ξ (star x ξ')‖ ≤ ‖star x ξ'‖ := Submodule.norm_starProjection_apply_le _ _
      _ = ‖(α (star b) : H →L[ℂ] H) ξ'‖ := by rw [map_star]; rfl
      _ ≤ ‖((star b : N) : K →L[ℂ] K) ζ'‖ := norm_schwarzMap_apply_apply_le α hξ' (star b)
      _ = ‖e (star y ζ')‖ := by rw [hbs]
  · -- `⟪ζ, y ζ + z⟫ = ⟪ζ, y s ζ⟫ = ⟪ξ, α(y s) ξ⟫`.
    rw [← hξ b, hb, inner_add_right, Submodule.inner_right_of_mem_orthogonal hK₁ hz, add_zero]

/-- **Data-processing inequality for vector functionals.** Let `α : N → M` be a unital Schwarz map
and `ζ, ζ' ∈ K`, `ξ, ξ' ∈ H` with `ω_ξ ∘ α = ω_ζ` and `ω_ξ' ∘ α = ω_ζ'` on `N`. Then
`S_N(ω_ζ ‖ ω_ζ') ≤ S_M(ω_ξ ‖ ω_ξ')`. -/
theorem arakiVec_le_of_schwarzMap (hα : α 1 = 1) {ζ ζ' : K} {ξ ξ' : H}
    (hξ : ∀ y : N, ⟪ζ, (y : K →L[ℂ] K) ζ⟫_ℂ = ⟪ξ, (α y : H →L[ℂ] H) ξ⟫_ℂ)
    (hξ' : ∀ y : N, ⟪ζ', (y : K →L[ℂ] K) ζ'⟫_ℂ = ⟪ξ', (α y : H →L[ℂ] H) ξ'⟫_ℂ) :
    N.arakiVec ζ ζ' ≤ M.arakiVec ξ ξ' := by
  refine negLogIntegral_le_of_integral_inv_add_le (ae_nonneg_spectralMeasure_relativeModular N ζ ζ')
    (le_of_eq ?_) (arakiVec_ne_bot M ξ ξ')
    fun t ht => integral_inv_add_spectralMeasure_relativeModular_le α hξ hξ' ht
  -- Both spectral measures have mass `‖ζ‖² = ω_ζ(1) = ω_ξ(α 1) = ‖ξ‖²`.
  have h1 := hξ 1
  rw [hα, OneMemClass.coe_one, OneMemClass.coe_one, one_apply_eq_self, one_apply_eq_self,
    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h1
  rw [IsSelfAdjoint.spectralMeasure_univ, IsSelfAdjoint.spectralMeasure_univ]
  exact congrArg ENNReal.ofReal (by exact_mod_cast h1.symm)

end Vector

/-! ### Normal functionals -/

section Amplify

variable (H₁ : Type*) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [Nontrivial H₁]

/-- The Schwarz map `1 ⊗ α : amplify H₁ N → amplify H₁ M`, `1 ⊗ y ↦ 1 ⊗ α(y)`, transported along
the `⋆`-isomorphisms `VonNeumannAlgebra.amplifyEquiv`. -/
noncomputable def amplifySchwarzMap (α : SchwarzMap N M) :
    SchwarzMap (N.amplify H₁) (M.amplify H₁) :=
  (SchwarzMapClass.toSchwarzMap (amplifyEquiv H₁ M)).comp
    (α.comp (SchwarzMapClass.toSchwarzMap (amplifyEquiv H₁ N).symm))

variable {H₁}

/-- `(1 ⊗ α)(1 ⊗ y) = 1 ⊗ α(y)`. -/
theorem amplifySchwarzMap_amplifyEquiv (α : SchwarzMap N M) (y : N) :
    amplifySchwarzMap H₁ α (amplifyEquiv H₁ N y) = amplifyEquiv H₁ M (α y) := by
  change amplifyEquiv H₁ M (α ((amplifyEquiv H₁ N).symm (amplifyEquiv H₁ N y))) = _
  rw [StarAlgEquiv.symm_apply_apply]

/-- `1 ⊗ α` is unital when `α` is. -/
theorem amplifySchwarzMap_one {α : SchwarzMap N M} (hα : α 1 = 1) :
    amplifySchwarzMap H₁ α 1 = 1 := by
  rw [← amplifyEquiv_one, amplifySchwarzMap_amplifyEquiv, hα, amplifyEquiv_one]

end Amplify

/-- `ℓ²(ℕ)`, the multiplicity space of the amplification. -/
local notation "ℓ²" => lp (fun _ : ℕ => ℂ) 2

/-- **Data-processing inequality** (Uhlmann; Petz's proof). For a unital normal Schwarz map
`α : N → M` and normal positive functionals `ψ, φ` on `M`, `S(ψ ∘ α ‖ φ ∘ α) ≤ S(ψ ‖ φ)`. -/
theorem arakiEntropy_comp_le (α : SchwarzMap N M) (hα₁ : α 1 = 1) (hα : IsNormalMap α)
    (ψ φ : M.NormalFunctional) :
    S⟦ψ.comp α hα ∥ φ.comp α hα⟧ ≤ S⟦ψ ∥ φ⟧ := by
  have key : ∀ ω : M.NormalFunctional, ∀ y : N.amplify ℓ²,
      ⟪(ω.comp α hα).2.vec, (y : ℓ² ⊗̂ K →L[ℂ] ℓ² ⊗̂ K) (ω.comp α hα).2.vec⟫_ℂ =
        ⟪ω.2.vec, (amplifySchwarzMap ℓ² α y : ℓ² ⊗̂ H →L[ℂ] ℓ² ⊗̂ H) ω.2.vec⟫_ℂ := fun ω y => by
    obtain ⟨y, rfl⟩ : ∃ y', amplifyEquiv ℓ² N y' = y :=
      ⟨(amplifyEquiv ℓ² N).symm y, (amplifyEquiv ℓ² N).apply_symm_apply y⟩
    rw [amplifySchwarzMap_amplifyEquiv, coe_amplifyEquiv_apply, coe_amplifyEquiv_apply,
      (ω.comp α hα).2.inner_vec_amplifyRight, ω.2.inner_vec_amplifyRight,
      NormalFunctional.comp_apply]
  exact arakiVec_le_of_schwarzMap _ (amplifySchwarzMap_one hα₁) (key ψ) (key φ)

end VonNeumannAlgebra
