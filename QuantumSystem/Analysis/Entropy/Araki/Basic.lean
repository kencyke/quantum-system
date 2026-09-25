/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Algebra.VonNeumannAlgebra.Normal
public import QuantumSystem.Algebra.VonNeumannAlgebra.TensorFactor
public import QuantumSystem.Analysis.Entropy.Araki.Vector

/-!
# Araki's relative entropy of normal positive functionals

For normal positive functionals `ψ, φ` on a von Neumann algebra `M ⊆ B(H)`, **Araki's relative
entropy** `S(ψ ‖ φ)` is defined by representing both as vector functionals on the amplification
`M̃ = amplify ℓ²(ℕ) M` on `ℓ²(ℕ) ⊗̂ H`: if `ψ(x) = ⟪Ξ_ψ, (1 ⊗ x) Ξ_ψ⟫` and
`φ(x) = ⟪Ξ_φ, (1 ⊗ x) Ξ_φ⟫`, then `S(ψ ‖ φ) = S_{M̃}(ω_{Ξ_ψ} ‖ ω_{Ξ_φ})`
(`VonNeumannAlgebra.arakiVec`). The value does not depend on the representing vectors
(`VonNeumannAlgebra.arakiEntropy_eq_arakiVec`), and for vector functionals it is the relative
entropy computed on `H` itself (`VonNeumannAlgebra.arakiEntropy_ofVector`).

Normality is σ-weak continuity (`VonNeumannAlgebra.IsNormal`); the representing vectors on the
amplification come from `VonNeumannAlgebra.isNormal_iff_exists`.

## Main definitions

* `VonNeumannAlgebra.arakiEntropy M ψ φ` — `S(ψ ‖ φ) ∈ EReal`, with notation `S⟦ψ ∥ φ⟧` in
  scope `Araki` (the code notation uses `∥`, U+2225, where the prose writes `‖`). The first
  argument is the functional being measured, the second the reference; see the conventions in
  `QuantumSystem.Analysis.Entropy.Araki.Vector`.

## Main results

* `VonNeumannAlgebra.arakiVec_amplify_tmul` — invariance of `arakiVec` under amplification:
  `S_{amplify H₁ M}(ω_{e ⊗ ξ} ‖ ω_{e ⊗ η}) = S_M(ω_ξ ‖ ω_η)` for a unit vector `e`.
* `VonNeumannAlgebra.arakiEntropy_eq_arakiVec` — independence of the representing vectors.
* `VonNeumannAlgebra.arakiEntropy_ofVector` — `S(ω_ξ ‖ ω_η)` agrees with
  `VonNeumannAlgebra.arakiVec M ξ η`.
* `VonNeumannAlgebra.arakiEntropy_ne_bot`, `VonNeumannAlgebra.arakiEntropy_self`.
* `VonNeumannAlgebra.arakiEntropy_eq_top_of_not_supportProj_le` — **support condition**:
  `S(ψ ‖ φ) = +∞` unless `s(ψ) ≤ s(φ)`, for the support projections
  `VonNeumannAlgebra.NormalFunctional.supportProj`; equivalently
  (`VonNeumannAlgebra.arakiEntropy_eq_top_of_apply_star_mul_self`) unless the null ideal of `φ` lies
  in that of `ψ`.
* `VonNeumannAlgebra.arakiEntropy_of_apply_eq_mul_right`,
  `VonNeumannAlgebra.arakiEntropy_of_apply_eq_mul_left` — scaling:
  `S(ψ ‖ c φ) = S(ψ ‖ φ) - ψ(1) log c` for `c > 0` and `S(c ψ ‖ φ) = c (S(ψ ‖ φ) + ψ(1) log c)` for
  `c ≥ 0`.
* `VonNeumannAlgebra.mul_log_le_arakiEntropy` — the **Klein bound**
  `ψ(1) log (ψ(1) / φ(1)) ≤ S(ψ ‖ φ)`; `VonNeumannAlgebra.arakiEntropy_nonneg` —
  `0 ≤ S(ψ ‖ φ)` when `φ(1) ≤ ψ(1)`, e.g. for two states.
* `VonNeumannAlgebra.mul_log_le_arakiEntropy_supportProj` — the **sharp Klein bound** in Araki's
  form `ψ(1) log (ψ(1) / φ(s(ψ))) ≤ S(ψ ‖ φ)`;
  `VonNeumannAlgebra.mul_log_le_arakiEntropy_of_isStarProjection` — the same for every projection
  `p ∈ M` with `p ≥ s(ψ)` (i.e. `ψ(1 - p) = 0`) in place of `s(ψ)`.

The **data-processing inequality** `S(ψ ∘ α ‖ φ ∘ α) ≤ S(ψ ‖ φ)` for unital normal Schwarz maps
is `VonNeumannAlgebra.arakiEntropy_comp_le` (`QuantumSystem.Analysis.Entropy.Araki.Monotonicity`),
and the identification with Umegaki's `Tr ρ (log ρ - log σ)` is
`VonNeumannAlgebra.arakiEntropy_normalState` (`QuantumSystem.Analysis.Entropy.Araki.Matrix`).

Not lifted from the vector case: the finite-dimensional characterisation of `S = +∞`, which would
need a representation of `ψ` by at most `dim H` vectors and a transport between multiplicity
spaces.

## Not formalised

The construction uses only the scalar spectral measures `μ_ξ` of the relative modular operator,
built from its resolvent (`IsSelfAdjoint.spectralMeasure`). The following are not formalised:

* the projection-valued spectral measure and the Borel functional calculus, hence the operators
  `log Δ`, `Δ^{it}` and `Δ^{1/2}` themselves, and `dom Δ^{1/2} = dom S̄`;
* the polar decomposition `S̄ = J Δ^{1/2}` and Tomita–Takesaki theory (`J M J = M′`,
  `Δ^{it} M Δ^{-it} = M`), the modular automorphism group `σ_t`, the KMS condition and Connes'
  cocycle;
* Petz's recovery map and the equality case of the data-processing inequality;
* Kosaki's variational formula, and the joint convexity and lower semicontinuity of `S` that follow
  from it.
-/

@[expose] public section

open scoped InnerProductSpace HilbertTensor
open HilbertTensor (amplifyRight amplifyRightₐ tmulRightL)

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (M : VonNeumannAlgebra H)

/-! ### Invariance under amplification -/

/-- **Invariance under amplification.** For a unit vector `e ∈ H₁`,
`S_{amplify H₁ M}(ω_{e ⊗ ξ} ‖ ω_{e ⊗ η}) = S_M(ω_ξ ‖ ω_η)`. -/
theorem arakiVec_amplify_tmul {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    {e : H₁} (he : ‖e‖ = 1) (ξ η : H) :
    (M.amplify H₁).arakiVec (e ⊗ₕ ξ) (e ⊗ₕ η) = M.arakiVec ξ η := by
  have h₁ : ∀ x : H →L[ℂ] H, amplifyRight x ∘L tmulRightL e = tmulRightL e ∘L x := fun x =>
    ContinuousLinearMap.ext fun u => by simp [HilbertTensor.amplifyRight_tmul]
  have hπ : ∀ S : VonNeumannAlgebra H, ∀ x ∈ S, ∃ y ∈ (S : Set (H →L[ℂ] H)).image amplifyRight,
      y ∘L tmulRightL e = tmulRightL e ∘L x ∧ star y ∘L tmulRightL e = tmulRightL e ∘L star x :=
    fun S x hx => ⟨amplifyRight x, ⟨x, hx, rfl⟩, h₁ x, by rw [HilbertTensor.amplifyRight_star]; exact h₁ _⟩
  refine arakiVec_of_intertwiner M ξ η (V := tmulRightL e)
    (fun x hx => ?_) (fun x hx => ?_) ?_
  · obtain ⟨y, ⟨x', hx', rfl⟩, h⟩ := hπ M x hx
    exact ⟨_, amplifyRight_mem_amplify hx', h⟩
  · obtain ⟨y, ⟨x', hx', rfl⟩, h⟩ := hπ M′ x hx
    exact ⟨_, amplifyRight_mem_commutant_amplify hx', h⟩
  · rw [HilbertTensor.tmulRightL_apply, HilbertTensor.adjoint_tmulRightL_tmul,
      inner_self_eq_norm_sq_to_K, he]
    simp

/-! ### The relative entropy of normal functionals -/

/-- `ℓ²(ℕ)`, the multiplicity space of the amplification. -/
local notation "ℓ²" => lp (fun _ : ℕ => ℂ) 2

/-- **Araki's relative entropy** `S(ψ ‖ φ)` of normal positive functionals on `M`: the relative
entropy of representing vector functionals on the amplification `amplify ℓ²(ℕ) M`. -/
noncomputable def arakiEntropy (ψ φ : M.NormalFunctional) : EReal :=
  (M.amplify ℓ²).arakiVec ψ.2.vec φ.2.vec

/-- `S⟦ψ ∥ φ⟧` is Araki's relative entropy `VonNeumannAlgebra.arakiEntropy M ψ φ`, the algebra `M`
being read off from `ψ : M.NormalFunctional`. -/
scoped[Araki] notation "S⟦" ψ " ∥ " φ "⟧" => VonNeumannAlgebra.arakiEntropy _ ψ φ

variable {M}

/-- **Independence of the representing vectors.** For any `Ξ_ψ, Ξ_φ ∈ ℓ²(ℕ) ⊗̂ H` with
`ψ(x) = ⟪Ξ_ψ, (1 ⊗ x) Ξ_ψ⟫` and `φ(x) = ⟪Ξ_φ, (1 ⊗ x) Ξ_φ⟫`,
`S(ψ ‖ φ) = S_{amplify M}(ω_{Ξ_ψ} ‖ ω_{Ξ_φ})`. -/
theorem arakiEntropy_eq_arakiVec {ψ φ : M.NormalFunctional} {Ξψ Ξφ : ℓ² ⊗̂ H}
    (hψ : ∀ x : M, ⟪Ξψ, amplifyRight (x : H →L[ℂ] H) Ξψ⟫_ℂ = ψ.1 x)
    (hφ : ∀ x : M, ⟪Ξφ, amplifyRight (x : H →L[ℂ] H) Ξφ⟫_ℂ = φ.1 x) :
    M.arakiEntropy ψ φ = (M.amplify ℓ²).arakiVec Ξψ Ξφ := by
  refine arakiVec_eq_of_inner_eq ?_ ?_
  · exact fun y hy => inner_apply_eq_of_mem_amplify (fun x hx =>
      (ψ.2.inner_vec_amplifyRight ⟨x, hx⟩).trans (hψ ⟨x, hx⟩).symm) hy |>.symm
  · exact fun y hy => inner_apply_eq_of_mem_amplify (fun x hx =>
      (φ.2.inner_vec_amplifyRight ⟨x, hx⟩).trans (hφ ⟨x, hx⟩).symm) hy |>.symm

variable (M) in
/-- **Vector functionals.** `S(ω_ξ ‖ ω_η) = arakiVec M ξ η`: the relative entropy of vector
functionals computed through the amplification is the one computed on `H`. -/
theorem arakiEntropy_ofVector (ξ η : H) :
    M.arakiEntropy (NormalFunctional.ofVector M ξ) (NormalFunctional.ofVector M η) =
      M.arakiVec ξ η := by
  rw [arakiEntropy_eq_arakiVec (Ξψ := lp.single (E := fun _ : ℕ => ℂ) 2 0 1 ⊗ₕ ξ)
    (Ξφ := lp.single (E := fun _ : ℕ => ℂ) 2 0 1 ⊗ₕ η)
    (fun x => HilbertTensor.inner_tmul_amplifyRight_tmul (lp.norm_single_one two_pos 0) ξ x)
    (fun x => HilbertTensor.inner_tmul_amplifyRight_tmul (lp.norm_single_one two_pos 0) η x),
    arakiVec_amplify_tmul M (lp.norm_single_one two_pos 0)]

variable (ψ φ : M.NormalFunctional)

/-- `S(ψ ‖ φ) ≠ -∞`. -/
theorem arakiEntropy_ne_bot : M.arakiEntropy ψ φ ≠ ⊥ :=
  arakiVec_ne_bot _ _ _

/-- `S(ψ ‖ ψ) = 0`. -/
@[simp]
theorem arakiEntropy_self : M.arakiEntropy ψ ψ = 0 :=
  arakiVec_self _ _

variable {ψ φ} in
/-- **Support condition.** `S(ψ ‖ φ) = +∞` unless `s(ψ) ≤ s(φ)`. -/
theorem arakiEntropy_eq_top_of_not_supportProj_le (h : ¬ ψ.supportProj ≤ φ.supportProj) :
    M.arakiEntropy ψ φ = ⊤ := by
  refine arakiVec_eq_top_of_not_supportProj_le fun hle => h ?_
  rwa [← NormalFunctional.amplifyRight_supportProj, ← NormalFunctional.amplifyRight_supportProj,
    amplifyRight_le_amplifyRight_iff (NormalFunctional.isStarProjection_supportProj ψ)
      (NormalFunctional.isStarProjection_supportProj φ)] at hle

variable {ψ φ} in
/-- **Support condition**, null-ideal form. If `φ(x⋆x) = 0` but `ψ(x⋆x) ≠ 0` for some `x ∈ M` (the
null ideal of `φ` is not contained in that of `ψ`, i.e. `s(ψ) ≰ s(φ)`), then `S(ψ ‖ φ) = +∞`. -/
theorem arakiEntropy_eq_top_of_apply_star_mul_self (x : M) (hφ : φ.1 (star x * x) = 0)
    (hψ : ψ.1 (star x * x) ≠ 0) : M.arakiEntropy ψ φ = ⊤ := by
  refine arakiEntropy_eq_top_of_not_supportProj_le fun hle => hψ ?_
  rw [NormalFunctional.apply_star_mul_self_eq_zero_iff] at hφ ⊢
  rw [← ((NormalFunctional.isStarProjection_supportProj ψ).le_iff_mul_eq_right
    (NormalFunctional.isStarProjection_supportProj φ)).mp hle, ← mul_assoc, hφ, zero_mul]

/-! ### Scaling -/

/-- `‖Ξ_ψ‖² = ψ(1)` for the representing vector. -/
lemma norm_vec_sq : ‖ψ.2.vec‖ ^ 2 = (ψ.1 1).re :=
  (re_apply_one_eq_norm_sq ψ.2.inner_vec_amplifyRight).symm

variable {ψ φ} in
/-- **Scaling the second functional.** If `φ′ = c φ` with `c > 0`, then
`S(ψ ‖ φ′) = S(ψ ‖ φ) - ψ(1) log c`. -/
theorem arakiEntropy_of_apply_eq_mul_right {φ' : M.NormalFunctional} {c : ℝ} (hc : 0 < c)
    (h : ∀ x, φ'.1 x = c * φ.1 x) :
    M.arakiEntropy ψ φ' = M.arakiEntropy ψ φ - (((ψ.1 1).re * Real.log c : ℝ) : EReal) := by
  rw [arakiEntropy_eq_arakiVec (Ξψ := ψ.2.vec) (Ξφ := (Real.sqrt c : ℂ) • φ.2.vec)
    ψ.2.inner_vec_amplifyRight (fun x => ?_), arakiVec_sqrt_smul_right _ _ hc, norm_vec_sq,
    arakiEntropy]
  rw [map_smul, inner_smul_left, inner_smul_right, φ.2.inner_vec_amplifyRight, h, Complex.conj_ofReal,
    ← mul_assoc, ← Complex.ofReal_mul, Real.mul_self_sqrt hc.le]

variable {ψ φ} in
/-- **Scaling the first functional.** If `ψ′ = c ψ` with `c ≥ 0`, then
`S(ψ′ ‖ φ) = c (S(ψ ‖ φ) + ψ(1) log c)`; at `c = 0` both sides vanish (`log 0 = 0`). -/
theorem arakiEntropy_of_apply_eq_mul_left {ψ' : M.NormalFunctional} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x, ψ'.1 x = c * ψ.1 x) :
    M.arakiEntropy ψ' φ =
      (c : EReal) * (M.arakiEntropy ψ φ + (((ψ.1 1).re * Real.log c : ℝ) : EReal)) := by
  have hsq : ‖(Real.sqrt c : ℂ)‖ ^ 2 = c := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg c), Real.sq_sqrt hc]
  rw [arakiEntropy_eq_arakiVec (Ξψ := (Real.sqrt c : ℂ) • ψ.2.vec) (Ξφ := φ.2.vec)
    (fun x => ?_) φ.2.inner_vec_amplifyRight, arakiVec_smul_left, hsq, norm_vec_sq, arakiEntropy]
  rw [map_smul, inner_smul_left, inner_smul_right, ψ.2.inner_vec_amplifyRight, h, Complex.conj_ofReal,
    ← mul_assoc, ← Complex.ofReal_mul, Real.mul_self_sqrt hc]

/-! ### The Klein bound -/

/-- **Klein bound**: `ψ(1) log (ψ(1) / φ(1)) ≤ S(ψ ‖ φ)`. With Mathlib's conventions the left side
is `0` when `ψ(1) = 0` or `φ(1) = 0`. -/
theorem mul_log_le_arakiEntropy :
    (((ψ.1 1).re * Real.log ((ψ.1 1).re / (φ.1 1).re) : ℝ) : EReal) ≤ M.arakiEntropy ψ φ := by
  have := norm_sq_mul_log_div_norm_sq_le_arakiVec (M.amplify ℓ²) ψ.2.vec φ.2.vec
  rwa [norm_vec_sq, norm_vec_sq] at this

variable {ψ φ} in
/-- **Klein bound** through a projection above the support: for a projection `p ∈ M` with
`ψ(1 - p) = 0` (i.e. `s(ψ) ≤ p`, `NormalFunctional.supportProj_le_iff`),
`ψ(1) log (ψ(1) / φ(p)) ≤ S(ψ ‖ φ)`; the strongest case `p = s(ψ)` is
`mul_log_le_arakiEntropy_supportProj`. With Mathlib's conventions the left side is `0` when `ψ(1) = 0` or `φ(p) = 0`. -/
theorem mul_log_le_arakiEntropy_of_isStarProjection {p : H →L[ℂ] H} (hp : IsStarProjection p)
    (hpM : p ∈ M) (hψp : ψ.1 ⟨1 - p, sub_mem (one_mem M) hpM⟩ = 0) :
    (((ψ.1 1).re * Real.log ((ψ.1 1).re / (φ.1 ⟨p, hpM⟩).re) : ℝ) : EReal) ≤
      M.arakiEntropy ψ φ := by
  set q := amplifyRight (H₁ := ℓ²) p
  have hq : IsStarProjection q := isStarProjection_amplifyRight hp
  have hle : (M.amplify ℓ²).supportProj ψ.2.vec ≤ q := by
    rw [← NormalFunctional.amplifyRight_supportProj,
      amplifyRight_le_amplifyRight_iff (NormalFunctional.isStarProjection_supportProj ψ) hp]
    exact (NormalFunctional.supportProj_le_iff ψ hp hpM).mpr hψp
  have hb : ‖(M.amplify ℓ²).supportProj ψ.2.vec φ.2.vec‖ ^ 2 ≤ (φ.1 ⟨p, hpM⟩).re := by
    have h₁ : (M.amplify ℓ²).supportProj ψ.2.vec = (M.amplify ℓ²).supportProj ψ.2.vec * q :=
      ((IsStarProjection.le_iff_mul_eq_left ((M.amplify ℓ²).isStarProjection_supportProj _)
        hq).mp hle).symm
    have h₂ : ‖(M.amplify ℓ²).supportProj ψ.2.vec φ.2.vec‖ ≤ ‖q φ.2.vec‖ := by
      rw [h₁, mul_apply_eq_comp]
      exact Submodule.norm_starProjection_apply_le _ _
    have hpp : star (⟨p, hpM⟩ : M) * ⟨p, hpM⟩ = ⟨p, hpM⟩ :=
      Subtype.ext (by simp [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq])
    have h₃ := apply_star_mul_self_eq φ.2.inner_vec_amplifyRight ⟨p, hpM⟩
    rw [hpp] at h₃
    rw [h₃, Complex.ofReal_re]
    gcongr
  have := norm_sq_mul_log_le_arakiVec_of_le (M.amplify ℓ²) ψ.2.vec hb
  rwa [norm_vec_sq] at this

/-- **Sharp Klein bound** (Araki): `ψ(1) log (ψ(1) / φ(s(ψ))) ≤ S(ψ ‖ φ)`, for the support
projection `s(ψ)`. With Mathlib's conventions the left side is `0` when `ψ(1) = 0` or
`φ(s(ψ)) = 0`. -/
theorem mul_log_le_arakiEntropy_supportProj :
    (((ψ.1 1).re * Real.log ((ψ.1 1).re /
        (φ.1 ⟨ψ.supportProj, NormalFunctional.supportProj_mem ψ⟩).re) : ℝ) : EReal) ≤
      M.arakiEntropy ψ φ :=
  mul_log_le_arakiEntropy_of_isStarProjection (NormalFunctional.isStarProjection_supportProj ψ)
    (NormalFunctional.supportProj_mem ψ) (NormalFunctional.apply_one_sub_supportProj ψ)

variable {ψ φ} in
/-- **Positivity.** `0 ≤ S(ψ ‖ φ)` when `φ(1) ≤ ψ(1)`; in particular for two states. -/
theorem arakiEntropy_nonneg (h : (φ.1 1).re ≤ (ψ.1 1).re) : 0 ≤ M.arakiEntropy ψ φ := by
  refine arakiVec_nonneg_of_norm_le ?_
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_vec_sq, norm_vec_sq]
  exact h

end VonNeumannAlgebra
