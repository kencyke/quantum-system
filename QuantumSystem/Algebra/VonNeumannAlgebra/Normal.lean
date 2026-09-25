/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.Projection
public import QuantumSystem.Algebra.VonNeumannAlgebra.RadonNikodym
public import QuantumSystem.Algebra.VonNeumannAlgebra.Support
public import QuantumSystem.Algebra.VonNeumannAlgebra.TensorFactor
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.l2Space
public import QuantumSystem.ForMathlib.Analysis.LocallyConvex.SigmaWeakOperatorTopology
public import QuantumSystem.ForMathlib.Analysis.Normed.Lp.lpSpace

/-!
# Normal positive functionals

A positive functional `ω` on a von Neumann algebra `M ⊆ B(H)` is **normal** if it is σ-weakly
continuous (`VonNeumannAlgebra.IsNormal`; Takesaki, *Theory of Operator Algebras I*, §II.2;
Bratteli–Robinson, *Operator Algebras and Quantum Statistical Mechanics 1*, Def. 2.4.1), the
σ-weak topology being that of `H →σw[ℂ] H`
(`QuantumSystem.ForMathlib.Analysis.LocallyConvex.SigmaWeakOperatorTopology`) restricted to `M`.

The representation theorem (Bratteli–Robinson, Thm. 2.4.21): `ω` is normal iff it is a countable
sum of vector functionals, `ω(x) = ∑ₙ ⟪ξₙ, x ξₙ⟫` for a square-summable sequence `(ξₙ)` in `H`
(`VonNeumannAlgebra.isNormal_iff_exists_lp`). Through `lpTensorEquiv : ℓ²(ℕ, H) ≃ ℓ²(ℕ) ⊗̂ H`, a
sequence `(ξₙ)` is a single vector `Ξ = ∑ₙ eₙ ⊗ ξₙ` with `∑ₙ ⟪ξₙ, x ξₙ⟫ = ⟪Ξ, (1 ⊗ x) Ξ⟫`, so normal
functionals are exactly the restrictions to `1 ⊗ M` of vector functionals on `ℓ²(ℕ) ⊗̂ H`
(`VonNeumannAlgebra.isNormal_iff_exists`). The proof: σ-weak continuity gives
`ω(x) = ⟪Ξ₀, (1 ⊗ x) Η₀⟫` (`ContinuousLinearMapSigmaWeak.exists_lp_pair_of_continuous`); positivity
bounds `ω` by the vector functional of the interleaving of `Ξ₀`, `Η₀`; the Radon–Nikodym theorem
(`CStarAlgebra.exists_commute_inner_eq_of_apply_star_mul_self_le`) makes `ω` a vector
functional.

For a normal `ψ`, the **support projection** `s(ψ) ∈ M` is the smallest projection `p ∈ M` with
`ψ(1 - p) = 0` (`VonNeumannAlgebra.NormalFunctional.supportProj_le_iff`). Its null ideal is
`{x ∈ M | ψ(x⋆x) = 0} = {x | x s(ψ) = 0}`
(`VonNeumannAlgebra.NormalFunctional.apply_star_mul_self_eq_zero_iff`). It is built from a
representing vector: if `ψ(x) = ⟪Ξ, (1 ⊗ x) Ξ⟫` on `ℓ²(ℕ) ⊗̂ H`, the vector support `s(Ξ)` in the
amplification `amplify ℓ²(ℕ) M = 1 ⊗ M` is `1 ⊗ s(ψ)`
(`VonNeumannAlgebra.NormalFunctional.amplifyRight_supportProj_eq`), for every such `Ξ`.

## Main definitions

* `VonNeumannAlgebra.sigmaWeak M` — `M` inside `H →σw[ℂ] H`.
* `VonNeumannAlgebra.IsNormal M ω` — `ω` is σ-weakly continuous on `M`.
* `VonNeumannAlgebra.NormalFunctional M` — the normal positive functionals on `M`.
* `VonNeumannAlgebra.IsNormal.vec` — a representing vector in `ℓ²(ℕ) ⊗̂ H`.
* `VonNeumannAlgebra.vectorFunctional M ξ` — the vector functional `ω_ξ = ⟪ξ, (·) ξ⟫` on `M`;
  `VonNeumannAlgebra.NormalFunctional.ofVector M ξ` — the same as a normal functional.
* `VonNeumannAlgebra.amplifiedVectorFunctional M Ξ` — the functional `⟪Ξ, (1 ⊗ ·) Ξ⟫` on `M` for
  `Ξ ∈ H₁ ⊗̂ H`; `VonNeumannAlgebra.NormalFunctional.ofAmplifiedVector M Ξ` — the same as a normal
  functional, for `Ξ ∈ ℓ²(ℕ) ⊗̂ H`.
* `VonNeumannAlgebra.IsNormalMap α` — a map `α : N → M` between von Neumann algebras is σ-weakly
  continuous; `VonNeumannAlgebra.NormalFunctional.comp` — `ω ∘ α` for a normal positive `α`.
* `VonNeumannAlgebra.NormalFunctional.supportProj ψ` — the support projection `s(ψ) ∈ M`.

## Main results

* `HilbertTensor.hasSum_inner_amplifyRight_lpTensorEquiv` —
  `⟪Ξ, (1 ⊗ x) Η⟫ = ∑ₙ ⟪ξₙ, x ηₙ⟫` for `Ξ = lpTensorEquiv ξ`, `Η = lpTensorEquiv η`.
* `VonNeumannAlgebra.isNormal_of_hasSum_inner`, `VonNeumannAlgebra.IsNormal.exists_hasSum_inner` —
  `ω` is normal iff `ω(x) = ∑ₙ ⟪ξₙ, x ηₙ⟫` for square-summable `ξ`, `η`.
* `VonNeumannAlgebra.isNormal_iff_exists` — `ω` is normal iff `ω(x) = ⟪Ξ, (1 ⊗ x) Ξ⟫` for some
  `Ξ ∈ ℓ²(ℕ) ⊗̂ H`; `VonNeumannAlgebra.isNormal_iff_exists_lp` — iff `ω = ∑ₙ ω_{ξₙ}`.
* `VonNeumannAlgebra.isNormal_vectorFunctional` — vector functionals are normal.
* `VonNeumannAlgebra.isNormalMap_id`, `VonNeumannAlgebra.IsNormal.comp`,
  `VonNeumannAlgebra.IsNormalMap.comp` — the identity is normal, and normality is stable
  under composition with normal maps.
* `VonNeumannAlgebra.isNormalMap_of_finiteDimensional` — every linear map between von Neumann
  algebras on finite-dimensional spaces is normal.
* `VonNeumannAlgebra.NormalFunctional.supportProj_mem`,
  `VonNeumannAlgebra.NormalFunctional.isStarProjection_supportProj` — `s(ψ)` is a projection in `M`.
* `VonNeumannAlgebra.NormalFunctional.supportProj_le_iff` — `s(ψ) ≤ p ↔ ψ(1 - p) = 0` for
  projections `p ∈ M`; `VonNeumannAlgebra.NormalFunctional.apply_one_sub_supportProj` —
  `ψ(1 - s(ψ)) = 0`.
* `VonNeumannAlgebra.NormalFunctional.apply_star_mul_self_eq_zero_iff` — `ψ(x⋆x) = 0 ↔ x s(ψ) = 0`.
-/

@[expose] public section

open scoped InnerProductSpace ComplexOrder HilbertTensor
open HilbertTensor (amplifyRight lpTensorEquiv)

namespace HilbertTensor

variable {ι : Type*} [DecidableEq ι] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- For `Ξ = lpTensorEquiv ξ = ∑ᵢ eᵢ ⊗ ξᵢ`, `(1 ⊗ x) Ξ = ∑ᵢ eᵢ ⊗ x ξᵢ`. -/
theorem amplifyRight_lpTensorEquiv (ξ : lp (fun _ : ι => H) 2) (x : H →L[ℂ] H)
    (hx : Memℓp (fun i => x (ξ i)) 2) :
    amplifyRight x (lpTensorEquiv ξ) = lpTensorEquiv ⟨fun i => x (ξ i), hx⟩ := by
  set L := (lpTensorEquiv (ι := ι) (K := H)).toContinuousLinearEquiv.toContinuousLinearMap
  have h₁ := (lp.hasSum_single ENNReal.ofNat_ne_top ξ).mapL ((amplifyRight x).comp L)
  have h₂ := (lp.hasSum_single ENNReal.ofNat_ne_top
    (⟨fun i => x (ξ i), hx⟩ : lp (fun _ : ι => H) 2)).mapL L
  refine h₁.unique (h₂.congr_fun fun i => ?_)
  change amplifyRight x (lpTensorEquiv (lp.single 2 i (ξ i))) =
    lpTensorEquiv (lp.single 2 i (x (ξ i)))
  rw [lpTensorEquiv_single, lpTensorEquiv_single, amplifyRight_tmul]

/-- For `Ξ = lpTensorEquiv ξ` and `Η = lpTensorEquiv η`, `⟪Ξ, (1 ⊗ x) Η⟫ = ∑ᵢ ⟪ξᵢ, x ηᵢ⟫`. -/
theorem hasSum_inner_amplifyRight_lpTensorEquiv (ξ η : lp (fun _ : ι => H) 2) (x : H →L[ℂ] H) :
    HasSum (fun i => ⟪ξ i, x (η i)⟫_ℂ) ⟪lpTensorEquiv ξ, amplifyRight x (lpTensorEquiv η)⟫_ℂ := by
  rw [amplifyRight_lpTensorEquiv η x (lp.memℓp_apply_clm η x), LinearIsometryEquiv.inner_map_map]
  exact lp.hasSum_inner ξ _

omit [DecidableEq ι] in
/-- `⟪Ξ, (1 ⊗ x⋆x) Ξ⟫ = ‖(1 ⊗ x) Ξ‖²`. -/
theorem inner_amplifyRight_star_mul_self {H₁ : Type*} [NormedAddCommGroup H₁]
    [InnerProductSpace ℂ H₁] (Ξ : H₁ ⊗̂ H) (x : H →L[ℂ] H) :
    ⟪Ξ, amplifyRight (star x * x) Ξ⟫_ℂ = ((‖amplifyRight x Ξ‖ ^ 2 : ℝ) : ℂ) := by
  rw [amplifyRight_mul, ← amplifyRight_star, ContinuousLinearMap.star_eq_adjoint,
    mul_apply_eq_comp, ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast

omit [DecidableEq ι] in
/-- `⟪Ξ, (1 ⊗ x⋆x) Η⟫ = ⟪(1 ⊗ x) Ξ, (1 ⊗ x) Η⟫`. -/
theorem inner_amplifyRight_star_mul {H₁ : Type*} [NormedAddCommGroup H₁]
    [InnerProductSpace ℂ H₁] (Ξ Η : H₁ ⊗̂ H) (x : H →L[ℂ] H) :
    ⟪Ξ, amplifyRight (star x * x) Η⟫_ℂ = ⟪amplifyRight x Ξ, amplifyRight x Η⟫_ℂ := by
  rw [amplifyRight_mul, ← amplifyRight_star, ContinuousLinearMap.star_eq_adjoint,
    mul_apply_eq_comp, ContinuousLinearMap.adjoint_inner_right]

omit [DecidableEq ι] [CompleteSpace H] in
/-- `⟪e ⊗ ξ, (1 ⊗ x)(e ⊗ ξ)⟫ = ⟪ξ, x ξ⟫` for a unit vector `e`. -/
theorem inner_tmul_amplifyRight_tmul {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    {e : H₁} (he : ‖e‖ = 1) (ξ : H) (x : H →L[ℂ] H) :
    ⟪e ⊗ₕ ξ, amplifyRight x (e ⊗ₕ ξ)⟫_ℂ = ⟪ξ, x ξ⟫_ℂ := by
  rw [amplifyRight_tmul, inner_tmul, inner_self_eq_norm_sq_to_K, he]
  simp

end HilbertTensor

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

variable (M) in
/-- `M` as a subspace of `B(H)` with the σ-weak operator topology: its subspace topology is the
σ-weak topology of `M`. -/
noncomputable def sigmaWeak : Submodule ℂ (H →σw[ℂ] H) :=
  (Subalgebra.toSubmodule M.toStarSubalgebra.toSubalgebra).comap
    ContinuousLinearMapSigmaWeak.linearEquiv.toLinearMap

/-- Membership in `M.sigmaWeak` is membership of the underlying operator in `M`. -/
@[simp] lemma mem_sigmaWeak_iff {T : H →σw[ℂ] H} : T ∈ M.sigmaWeak ↔ T.toCLM ∈ M := Iff.rfl

variable (M) in
/-- The identification of `M.sigmaWeak` with `M`. -/
def ofSigmaWeak : M.sigmaWeak →ₗ[ℂ] M where
  toFun T := ⟨T.1.toCLM, T.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (M) in
/-- `x ∈ M` as an element of `M.sigmaWeak`. -/
def toSigmaWeak (x : M) : M.sigmaWeak := ⟨ContinuousLinearMapSigmaWeak.ofCLM x, x.2⟩

/-- `ofSigmaWeak` inverts `toSigmaWeak`. -/
@[simp] lemma ofSigmaWeak_toSigmaWeak (x : M) : M.ofSigmaWeak (M.toSigmaWeak x) = x := rfl

variable (M) in
/-- A positive functional `ω` on `M` is **normal** if it is σ-weakly continuous (Takesaki,
*Theory of Operator Algebras I*, §II.2; Bratteli–Robinson, Def. 2.4.1 and Thm. 2.4.21). By
`VonNeumannAlgebra.isNormal_iff_exists_lp` this is equivalent to `ω` being a countable sum of
vector functionals. -/
def IsNormal (ω : M →ₚ[ℂ] ℂ) : Prop :=
  Continuous fun T : M.sigmaWeak => ω (M.ofSigmaWeak T)

variable (M) in
/-- The **normal positive functionals** on `M`. -/
abbrev NormalFunctional := {ω : M →ₚ[ℂ] ℂ // M.IsNormal ω}

/-- `A ↦ ∑ₙ ⟪ξₙ, A ηₙ⟫` is normal. -/
theorem isNormal_of_hasSum_inner {ω : M →ₚ[ℂ] ℂ} (ξ η : lp (fun _ : ℕ => H) 2)
    (h : ∀ x : M, HasSum (fun n => ⟪ξ n, (x : H →L[ℂ] H) (η n)⟫_ℂ) (ω x)) : M.IsNormal ω := by
  have : (fun T : M.sigmaWeak => ω (M.ofSigmaWeak T)) =
      fun T : M.sigmaWeak => ∑' n, ⟪ξ n, (T : H →σw[ℂ] H) (η n)⟫_ℂ :=
    funext fun T => (h (M.ofSigmaWeak T)).tsum_eq.symm
  rw [IsNormal, this]
  exact (ContinuousLinearMapSigmaWeak.continuous_tsum_inner_apply ξ η).comp continuous_subtype_val

/-- A normal functional is `x ↦ ∑ₙ ⟪ξₙ, x ηₙ⟫` for square-summable sequences `ξ`, `η`. -/
theorem IsNormal.exists_hasSum_inner {ω : M →ₚ[ℂ] ℂ} (h : M.IsNormal ω) :
    ∃ ξ η : lp (fun _ : ℕ => H) 2, ∀ x : M,
      HasSum (fun n => ⟪ξ n, (x : H →L[ℂ] H) (η n)⟫_ℂ) (ω x) := by
  obtain ⟨ξ, η, hξη⟩ := ContinuousLinearMapSigmaWeak.exists_lp_pair_of_continuous
    (S := M.sigmaWeak) (φ := ω.toLinearMap ∘ₗ M.ofSigmaWeak) h
  exact ⟨ξ, η, fun x => hξη (M.toSigmaWeak x)⟩

/-- `ℓ²(ℕ)`, the multiplicity space of the amplification. -/
local notation "ℓ²" => lp (fun _ : ℕ => ℂ) 2

/-- **Normal functionals are vector functionals on the amplification.** A normal `ω` is
`x ↦ ⟪Ξ, (1 ⊗ x) Ξ⟫` for some `Ξ ∈ ℓ²(ℕ) ⊗̂ H`: from `ω(x) = ⟪Ξ₀, (1 ⊗ x) Η₀⟫`, positivity gives
`ω ≤ ω_Ζ` for the interleaving `Ζ` of `Ξ₀` and `Η₀`, and the Radon–Nikodym theorem gives
`ω = ω_{R Ζ}` with `R` in the commutant of `1 ⊗ M`. -/
theorem IsNormal.exists_inner_amplifyRight_eq {ω : M →ₚ[ℂ] ℂ} (h : M.IsNormal ω) :
    ∃ Ξ : ℓ² ⊗̂ H, ∀ x : M, ⟪Ξ, amplifyRight (x : H →L[ℂ] H) Ξ⟫_ℂ = ω x := by
  obtain ⟨ξ, η, hξη⟩ := h.exists_hasSum_inner
  set ζ := lp.interleave ξ η
  set ρ : M →⋆ₐ[ℂ] (ℓ² ⊗̂ H →L[ℂ] ℓ² ⊗̂ H) := HilbertTensor.amplifyRightₐ.comp (inclₐ M)
  have hρ : ∀ x : M, ρ x = amplifyRight (x : H →L[ℂ] H) := fun _ => rfl
  have hω : ∀ x : M, ω x = ⟪lpTensorEquiv ξ, amplifyRight (x : H →L[ℂ] H) (lpTensorEquiv η)⟫_ℂ :=
    fun x => (hξη x).unique (HilbertTensor.hasSum_inner_amplifyRight_lpTensorEquiv ξ η x)
  have hζ : ∀ y : H →L[ℂ] H, ⟪lpTensorEquiv ζ, amplifyRight y (lpTensorEquiv ζ)⟫_ℂ =
      ⟪lpTensorEquiv ξ, amplifyRight y (lpTensorEquiv ξ)⟫_ℂ +
        ⟪lpTensorEquiv η, amplifyRight y (lpTensorEquiv η)⟫_ℂ := fun y => by
    refine (HilbertTensor.hasSum_inner_amplifyRight_lpTensorEquiv ζ ζ y).unique ?_
    have hzip := Stream'.zip_interleave (fun u v => ⟪u, y v⟫_ℂ)
      (ξ : ℕ → H) (η : ℕ → H) (ξ : ℕ → H) (η : ℕ → H)
    exact (congrArg (HasSum · _) hzip).mpr
      ((HilbertTensor.hasSum_inner_amplifyRight_lpTensorEquiv ξ ξ y).interleave
        (HilbertTensor.hasSum_inner_amplifyRight_lpTensorEquiv η η y))
  have hdom : ∀ x : M, ‖ω (star x * x)‖ ≤ ‖ρ x (lpTensorEquiv ζ)‖ ^ 2 := fun x => by
    set a := ‖amplifyRight (x : H →L[ℂ] H) (lpTensorEquiv ξ)‖
    set b := ‖amplifyRight (x : H →L[ℂ] H) (lpTensorEquiv η)‖
    have hsq : ‖ρ x (lpTensorEquiv ζ)‖ ^ 2 = a ^ 2 + b ^ 2 := by
      have := hζ (star (x : H →L[ℂ] H) * x)
      rw [HilbertTensor.inner_amplifyRight_star_mul_self,
        HilbertTensor.inner_amplifyRight_star_mul_self,
        HilbertTensor.inner_amplifyRight_star_mul_self, ← Complex.ofReal_add,
        Complex.ofReal_inj] at this
      rw [hρ]
      exact this
    rw [hsq, hω, MulMemClass.coe_mul, StarMemClass.coe_star,
      HilbertTensor.inner_amplifyRight_star_mul]
    have hab := norm_inner_le_norm (𝕜 := ℂ) (amplifyRight (x : H →L[ℂ] H) (lpTensorEquiv ξ))
      (amplifyRight (x : H →L[ℂ] H) (lpTensorEquiv η))
    nlinarith [sq_nonneg (a - b), norm_nonneg (amplifyRight (x : H →L[ℂ] H) (lpTensorEquiv ξ)),
      norm_nonneg (amplifyRight (x : H →L[ℂ] H) (lpTensorEquiv η))]
  obtain ⟨R, -, -, hR⟩ :=
    CStarAlgebra.exists_commute_inner_eq_of_apply_star_mul_self_le (ρ := ρ) (f := ω) hdom
  exact ⟨R (lpTensorEquiv ζ), fun x => (hR x).symm⟩

/-- `ω` is normal iff it is the restriction to `1 ⊗ M` of a vector functional on `ℓ²(ℕ) ⊗̂ H`. -/
theorem isNormal_iff_exists {ω : M →ₚ[ℂ] ℂ} :
    M.IsNormal ω ↔ ∃ Ξ : lp (fun _ : ℕ => ℂ) 2 ⊗̂ H,
      ∀ x : M, ⟪Ξ, amplifyRight (x : H →L[ℂ] H) Ξ⟫_ℂ = ω x := by
  refine ⟨IsNormal.exists_inner_amplifyRight_eq, fun ⟨Ξ, hΞ⟩ => ?_⟩
  refine isNormal_of_hasSum_inner (lpTensorEquiv.symm Ξ) (lpTensorEquiv.symm Ξ) fun x => ?_
  have := HilbertTensor.hasSum_inner_amplifyRight_lpTensorEquiv (lpTensorEquiv.symm Ξ)
    (lpTensorEquiv.symm Ξ) (x : H →L[ℂ] H)
  rwa [LinearIsometryEquiv.apply_symm_apply, hΞ] at this

/-- **Normal functionals are countable sums of vector functionals**: `ω` is normal iff
`ω(x) = ∑ₙ ⟪ξₙ, x ξₙ⟫` for a square-summable sequence `(ξₙ)` in `H`. -/
theorem isNormal_iff_exists_lp {ω : M →ₚ[ℂ] ℂ} :
    M.IsNormal ω ↔ ∃ ξ : lp (fun _ : ℕ => H) 2,
      ∀ x : M, HasSum (fun n => ⟪ξ n, (x : H →L[ℂ] H) (ξ n)⟫_ℂ) (ω x) := by
  refine ⟨fun h => ?_, fun ⟨ξ, hξ⟩ => isNormal_of_hasSum_inner ξ ξ hξ⟩
  obtain ⟨Ξ, hΞ⟩ := isNormal_iff_exists.mp h
  refine ⟨lpTensorEquiv.symm Ξ, fun x => ?_⟩
  have := HilbertTensor.hasSum_inner_amplifyRight_lpTensorEquiv (lpTensorEquiv.symm Ξ)
    (lpTensorEquiv.symm Ξ) (x : H →L[ℂ] H)
  rwa [LinearIsometryEquiv.apply_symm_apply, hΞ] at this

namespace IsNormal

variable {ω : M →ₚ[ℂ] ℂ} (h : M.IsNormal ω)

/-- A **representing vector** `Ξ ∈ ℓ²(ℕ) ⊗̂ H` of a normal functional:
`ω(x) = ⟪Ξ, (1 ⊗ x) Ξ⟫`. -/
noncomputable def vec : lp (fun _ : ℕ => ℂ) 2 ⊗̂ H :=
  (isNormal_iff_exists.mp h).choose

/-- `ω(x) = ⟪Ξ, (1 ⊗ x) Ξ⟫` for the representing vector `Ξ`. -/
theorem inner_vec_amplifyRight (x : M) :
    ⟪h.vec, amplifyRight (x : H →L[ℂ] H) h.vec⟫_ℂ = ω x :=
  (isNormal_iff_exists.mp h).choose_spec x

end IsNormal

/-- `ω(1) = ‖Ξ‖²` for any vector `Ξ` representing `ω`. -/
theorem re_apply_one_eq_norm_sq {ω : M →ₚ[ℂ] ℂ} {Ξ : lp (fun _ : ℕ => ℂ) 2 ⊗̂ H}
    (hΞ : ∀ x : M, ⟪Ξ, amplifyRight (x : H →L[ℂ] H) Ξ⟫_ℂ = ω x) : (ω 1).re = ‖Ξ‖ ^ 2 := by
  rw [← hΞ 1, OneMemClass.coe_one, HilbertTensor.amplifyRight_one,
    one_apply_eq_self, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- `ω(x⋆ x) = ‖(1 ⊗ x) Ξ‖²` for any vector `Ξ` representing `ω`. -/
theorem apply_star_mul_self_eq {ω : M →ₚ[ℂ] ℂ} {Ξ : lp (fun _ : ℕ => ℂ) 2 ⊗̂ H}
    (hΞ : ∀ x : M, ⟪Ξ, amplifyRight (x : H →L[ℂ] H) Ξ⟫_ℂ = ω x) (x : M) :
    ω (star x * x) = ((‖amplifyRight (x : H →L[ℂ] H) Ξ‖ ^ 2 : ℝ) : ℂ) := by
  rw [← hΞ, MulMemClass.coe_mul, StarMemClass.coe_star,
    HilbertTensor.inner_amplifyRight_star_mul_self]

variable (M) in
/-- The **vector functional** `ω_ξ = ⟪ξ, (·) ξ⟫` on `M`. -/
noncomputable def vectorFunctional (ξ : H) : M →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀
    { toFun := fun x => ⟪ξ, (x : H →L[ℂ] H) ξ⟫_ℂ
      map_add' := fun x y => by simp [inner_add_right]
      map_smul' := fun c x => by simp [inner_smul_right] }
    fun x hx => (ContinuousLinearMap.nonneg_iff_isPositive.mp
      (show (0 : H →L[ℂ] H) ≤ x from hx)).inner_nonneg_right ξ

/-- Evaluation of the vector functional: `ω_ξ(x) = ⟪ξ, x ξ⟫`. -/
@[simp]
theorem vectorFunctional_apply (ξ : H) (x : M) :
    M.vectorFunctional ξ x = ⟪ξ, (x : H →L[ℂ] H) ξ⟫_ℂ :=
  rfl

variable (M) in
/-- Vector functionals are normal. -/
theorem isNormal_vectorFunctional (ξ : H) : M.IsNormal (M.vectorFunctional ξ) :=
  isNormal_iff_exists.mpr ⟨lp.single (E := fun _ : ℕ => ℂ) 2 0 (1 : ℂ) ⊗ₕ ξ, fun x => by
    rw [HilbertTensor.inner_tmul_amplifyRight_tmul (lp.norm_single_one two_pos 0),
      vectorFunctional_apply]⟩

variable (M) in
/-- The vector functional `ω_ξ` as a normal functional. -/
noncomputable def NormalFunctional.ofVector (ξ : H) : M.NormalFunctional :=
  ⟨M.vectorFunctional ξ, M.isNormal_vectorFunctional ξ⟩

variable (M) in
/-- The functional `x ↦ ⟪Ξ, (1 ⊗ x) Ξ⟫` on `M` induced by a vector `Ξ ∈ H₁ ⊗̂ H`. -/
noncomputable def amplifiedVectorFunctional {H₁ : Type*} [NormedAddCommGroup H₁]
    [InnerProductSpace ℂ H₁] (Ξ : H₁ ⊗̂ H) : M →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀
    { toFun := fun x => ⟪Ξ, amplifyRight (x : H →L[ℂ] H) Ξ⟫_ℂ
      map_add' := fun x y => by
        simp [HilbertTensor.amplifyRight_add, inner_add_right]
      map_smul' := fun c x => by
        simp [HilbertTensor.amplifyRight_smul, inner_smul_right] }
    fun x hx => by
      obtain ⟨y, hy⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp
        (show (0 : H →L[ℂ] H) ≤ x from hx)
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [hy, HilbertTensor.inner_amplifyRight_star_mul_self]
      exact Complex.zero_le_real.mpr (sq_nonneg _)

/-- Evaluation of the amplified vector functional: `x ↦ ⟪Ξ, (1 ⊗ x) Ξ⟫`. -/
@[simp]
theorem amplifiedVectorFunctional_apply {H₁ : Type*} [NormedAddCommGroup H₁]
    [InnerProductSpace ℂ H₁] (Ξ : H₁ ⊗̂ H) (x : M) :
    M.amplifiedVectorFunctional Ξ x = ⟪Ξ, amplifyRight (x : H →L[ℂ] H) Ξ⟫_ℂ :=
  rfl

variable (M) in
/-- The functional `x ↦ ⟪Ξ, (1 ⊗ x) Ξ⟫` induced by `Ξ ∈ ℓ²(ℕ) ⊗̂ H` as a normal functional; every
normal functional is of this form (`VonNeumannAlgebra.isNormal_iff_exists`). -/
noncomputable def NormalFunctional.ofAmplifiedVector (Ξ : lp (fun _ : ℕ => ℂ) 2 ⊗̂ H) :
    M.NormalFunctional :=
  ⟨M.amplifiedVectorFunctional Ξ, isNormal_iff_exists.mpr ⟨Ξ, fun _ => rfl⟩⟩

section NormalMap

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {N : VonNeumannAlgebra K} {F : Type*}

/-- A map `α : N → M` between von Neumann algebras is **normal** if it is σ-weakly continuous
(Takesaki, *Theory of Operator Algebras I*, §II.2; Ohya–Petz, *Quantum Entropy and Its Use*, §1.C),
the same notion as `VonNeumannAlgebra.IsNormal` for functionals. For positive maps this is
equivalent to preserving suprema of bounded increasing nets; that equivalence is not formalised
here. -/
def IsNormalMap (α : N → M) : Prop :=
  Continuous fun T : N.sigmaWeak => M.toSigmaWeak (α (N.ofSigmaWeak T))

/-- The composite of a normal functional with a normal positive map is normal. -/
theorem IsNormal.comp [FunLike F N M] [LinearMapClass F ℂ N M] [OrderHomClass F N M]
    {ω : M →ₚ[ℂ] ℂ} (hω : M.IsNormal ω) {α : F} (hα : IsNormalMap α) :
    N.IsNormal (ω.comp (PositiveLinearMap.ofClass α)) :=
  Continuous.comp (g := fun T : M.sigmaWeak => ω (M.ofSigmaWeak T)) hω hα

/-- The identity map of a von Neumann algebra is normal. -/
theorem isNormalMap_id : IsNormalMap (id : N → N) :=
  continuous_id

/-- **Linear maps between finite-dimensional von Neumann algebras are normal**: in finite
dimensions the σ-weak topology is the unique Hausdorff vector-space topology, so every linear map is
σ-weakly continuous. -/
theorem isNormalMap_of_finiteDimensional [FiniteDimensional ℂ H] [FiniteDimensional ℂ K]
    [FunLike F N M] [LinearMapClass F ℂ N M] (α : F) : IsNormalMap α := by
  let e : M →ₗ[ℂ] M.sigmaWeak :=
    { toFun := M.toSigmaWeak
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact LinearMap.continuous_of_finiteDimensional
    (e ∘ₗ (LinearMap.ofClass α) ∘ₗ N.ofSigmaWeak)

/-- The composite of two normal maps is normal. -/
theorem IsNormalMap.comp {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L]
    [CompleteSpace L] {P : VonNeumannAlgebra L} {β : M → P} {α : N → M} (hβ : IsNormalMap β)
    (hα : IsNormalMap α) : IsNormalMap (β ∘ α) :=
  Continuous.comp hβ hα

/-- The composite `ω ∘ α` of a normal functional `ω` on `M` with a normal positive map
`α : N → M`, as a normal functional on `N`. -/
noncomputable def NormalFunctional.comp [FunLike F N M] [LinearMapClass F ℂ N M]
    [OrderHomClass F N M] (ω : M.NormalFunctional) (α : F) (hα : IsNormalMap α) :
    N.NormalFunctional :=
  ⟨ω.1.comp (PositiveLinearMap.ofClass α), ω.2.comp hα⟩

/-- `ω.comp α hα` evaluates as `ω ∘ α`. -/
@[simp]
theorem NormalFunctional.comp_apply [FunLike F N M] [LinearMapClass F ℂ N M]
    [OrderHomClass F N M] (ω : M.NormalFunctional) (α : F) (hα : IsNormalMap α) (x : N) :
    (ω.comp α hα).1 x = ω.1 (α x) :=
  rfl

end NormalMap

/-! ### The support projection of a normal functional -/

/-- `1 ⊗ p` is a projection along with `p`. -/
lemma isStarProjection_amplifyRight {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    {p : H →L[ℂ] H} (hp : IsStarProjection p) : IsStarProjection (amplifyRight (H₁ := H₁) p) :=
  ⟨by rw [IsIdempotentElem, ← HilbertTensor.amplifyRight_mul, hp.isIdempotentElem.eq],
    by rw [IsSelfAdjoint, HilbertTensor.amplifyRight_star, hp.isSelfAdjoint.star_eq]⟩

/-- `1 ⊗ (1 - p) = 1 - 1 ⊗ p`. -/
lemma amplifyRight_one_sub {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    (p : H →L[ℂ] H) : amplifyRight (H₁ := H₁) (1 - p) = 1 - amplifyRight p := by
  rw [← HilbertTensor.amplifyRightₐ_apply, map_sub, map_one]
  rfl

/-- For projections, `1 ⊗ e ≤ 1 ⊗ f ↔ e ≤ f`. -/
lemma amplifyRight_le_amplifyRight_iff {e f : H →L[ℂ] H} (he : IsStarProjection e)
    (hf : IsStarProjection f) : amplifyRight (H₁ := ℓ²) e ≤ amplifyRight f ↔ e ≤ f := by
  rw [(isStarProjection_amplifyRight he).le_iff_mul_eq_left (isStarProjection_amplifyRight hf),
    he.le_iff_mul_eq_left hf, ← HilbertTensor.amplifyRight_mul,
    HilbertTensor.amplifyRight_injective.eq_iff]

namespace NormalFunctional

variable (ψ : M.NormalFunctional)

/-- A representing vector's support lies in `1 ⊗ M`. -/
lemma exists_amplifyRight_eq_supportProj :
    ∃ x ∈ M, amplifyRight x = (M.amplify ℓ²).supportProj ψ.2.vec :=
  mem_amplify_iff.mp ((M.amplify ℓ²).supportProj_mem ψ.2.vec)

/-- The **support projection** `s(ψ) ∈ M` of a normal functional: the element of `M` with
`1 ⊗ s(ψ) = s(Ξ_ψ)`, the vector support of a representing vector in `amplify ℓ²(ℕ) M`. -/
noncomputable def supportProj : H →L[ℂ] H :=
  (exists_amplifyRight_eq_supportProj ψ).choose

/-- `s(ψ) ∈ M`. -/
theorem supportProj_mem : supportProj ψ ∈ M :=
  (exists_amplifyRight_eq_supportProj ψ).choose_spec.1

/-- `1 ⊗ s(ψ) = s(Ξ_ψ)` for the chosen representing vector. -/
theorem amplifyRight_supportProj :
    amplifyRight (supportProj ψ) = (M.amplify ℓ²).supportProj ψ.2.vec :=
  (exists_amplifyRight_eq_supportProj ψ).choose_spec.2

/-- **Independence of the representing vector.** `1 ⊗ s(ψ) = s(Ξ)` for *every* `Ξ` with
`ψ(x) = ⟪Ξ, (1 ⊗ x) Ξ⟫`. -/
theorem amplifyRight_supportProj_eq {Ξ : ℓ² ⊗̂ H}
    (hΞ : ∀ x : M, ⟪Ξ, amplifyRight (x : H →L[ℂ] H) Ξ⟫_ℂ = ψ.1 x) :
    amplifyRight (supportProj ψ) = (M.amplify ℓ²).supportProj Ξ := by
  rw [amplifyRight_supportProj]
  refine supportProj_eq_of_inner_eq fun y hy => inner_apply_eq_of_mem_amplify (fun x hx => ?_) hy
  rw [ψ.2.inner_vec_amplifyRight ⟨x, hx⟩, hΞ ⟨x, hx⟩]

/-- `s(ψ)` is a projection. -/
theorem isStarProjection_supportProj : IsStarProjection (supportProj ψ) := by
  have hS := (M.amplify ℓ²).isStarProjection_supportProj ψ.2.vec
  rw [← amplifyRight_supportProj] at hS
  refine ⟨HilbertTensor.amplifyRight_injective (H₁ := ℓ²) ?_,
    HilbertTensor.amplifyRight_injective (H₁ := ℓ²) ?_⟩
  · rw [HilbertTensor.amplifyRight_mul, hS.isIdempotentElem.eq]
  · rw [← HilbertTensor.amplifyRight_star, hS.isSelfAdjoint.star_eq]

/-- **Characterisation of the support.** For a projection `p ∈ M`, `s(ψ) ≤ p ↔ ψ(1 - p) = 0`:
`s(ψ)` is the smallest projection of `M` carrying `ψ`. -/
theorem supportProj_le_iff {p : H →L[ℂ] H} (hp : IsStarProjection p) (hpM : p ∈ M) :
    supportProj ψ ≤ p ↔ ψ.1 ⟨1 - p, sub_mem (one_mem M) hpM⟩ = 0 := by
  rw [← amplifyRight_le_amplifyRight_iff (isStarProjection_supportProj ψ) hp,
    amplifyRight_supportProj, supportProj_le_iff_inner_eq_zero (isStarProjection_amplifyRight hp)
      (amplifyRight_mem_amplify hpM), ← ψ.2.inner_vec_amplifyRight ⟨1 - p, _⟩]
  change _ ↔ ⟪_, amplifyRight (1 - p) _⟫_ℂ = 0
  rw [amplifyRight_one_sub]

/-- `ψ(1 - s(ψ)) = 0`. -/
theorem apply_one_sub_supportProj :
    ψ.1 ⟨1 - supportProj ψ, sub_mem (one_mem M) (supportProj_mem ψ)⟩ = 0 :=
  (supportProj_le_iff ψ (isStarProjection_supportProj ψ) (supportProj_mem ψ)).mp le_rfl

/-- **The null ideal.** `ψ(x⋆x) = 0 ↔ x s(ψ) = 0`. -/
theorem apply_star_mul_self_eq_zero_iff (x : M) :
    ψ.1 (star x * x) = 0 ↔ (x : H →L[ℂ] H) * supportProj ψ = 0 := by
  rw [apply_star_mul_self_eq ψ.2.inner_vec_amplifyRight, Complex.ofReal_eq_zero,
    pow_eq_zero_iff two_ne_zero, norm_eq_zero,
    ← mul_supportProj_eq_zero_iff (amplifyRight_mem_amplify (H₁ := ℓ²) x.2),
    ← amplifyRight_supportProj, ← HilbertTensor.amplifyRight_mul,
    ← HilbertTensor.amplifyRight_zero (H₁ := ℓ²), HilbertTensor.amplifyRight_injective.eq_iff]

end NormalFunctional

end VonNeumannAlgebra
