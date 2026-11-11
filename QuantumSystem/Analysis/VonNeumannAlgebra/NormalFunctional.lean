/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.Projection
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import QuantumSystem.Analysis.CStarAlgebra.Representation.VectorFunctional
public import QuantumSystem.Analysis.VonNeumannAlgebra.RadonNikodym
public import QuantumSystem.Analysis.VonNeumannAlgebra.SupportProjection
public import QuantumSystem.Analysis.VonNeumannAlgebra.TensorFactor
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.l2Space
public import QuantumSystem.ForMathlib.Analysis.LocallyConvex.SigmaWeakOperatorTopology
public import QuantumSystem.ForMathlib.Analysis.Normed.Lp.lpSpace

/-!
# Normal positive functionals

A positive functional `ω` on a von Neumann algebra `M ⊆ B(H)` is **normal** if it is σ-weakly
continuous (`VonNeumannAlgebra.IsNormal`), the σ-weak topology being that of `H →σw[ℂ] H`
(`QuantumSystem.ForMathlib.Analysis.LocallyConvex.SigmaWeakOperatorTopology`) restricted to `M`.

The representation theorem: `ω` is normal iff it is a countable
sum of vector functionals, `ω(x) = ∑ₙ ⟪ξₙ, x ξₙ⟫` for a square-summable sequence `(ξₙ)` in `H`
(`VonNeumannAlgebra.isNormal_iff_exists_hasSum_inner_self`). Through
`lp.completionTensorEquiv : ℓ²(ℕ, H) ≃ Completion (ℓ²(ℕ) ⊗[ℂ] H)`, a sequence `(ξₙ)` is a single
vector `Ξ = ∑ₙ eₙ ⊗ ξₙ` with `∑ₙ ⟪ξₙ, x ξₙ⟫ = ⟪Ξ, (1 ⊗ x) Ξ⟫`, so normal functionals are exactly
the restrictions to `1 ⊗ M` of vector functionals on the completed tensor product
`Completion (ℓ²(ℕ) ⊗[ℂ] H)` (`VonNeumannAlgebra.isNormal_iff_exists_inner_completion_lTensor_eq`).
The proof: σ-weak continuity gives `ω(x) = ⟪Ξ₀, (1 ⊗ x) Η₀⟫`
(`ContinuousLinearMapSigmaWeak.exists_lp_pair_of_continuous`); positivity bounds `ω` by the vector
functional of the interleaving of `Ξ₀`, `Η₀`; the Radon–Nikodym theorem
(`CStarAlgebra.exists_commute_inner_eq_of_apply_star_mul_self_le`) makes `ω` a vector
functional.

For a normal `ψ`, the **support projection** `s(ψ) ∈ M` is the smallest projection `p ∈ M` with
`ψ(1 - p) = 0` (`VonNeumannAlgebra.NormalFunctional.supportProj_le_iff`). Its null ideal is
`{x ∈ M | ψ(x⋆x) = 0} = {x | x s(ψ) = 0}`
(`VonNeumannAlgebra.NormalFunctional.apply_star_mul_self_eq_zero_iff`). It is built from a
representing vector: if `ψ(x) = ⟪Ξ, (1 ⊗ x) Ξ⟫` on `Completion (ℓ²(ℕ) ⊗[ℂ] H)`, the vector support `s(Ξ)` in the
amplification `oneTensor ℓ²(ℕ) M = 1 ⊗ M` is `1 ⊗ s(ψ)`
(`VonNeumannAlgebra.NormalFunctional.completion_lTensor_supportProj_eq`), for every such `Ξ`.

## Main definitions

* `VonNeumannAlgebra.sigmaWeak M` — `M` inside `H →σw[ℂ] H`.
* `VonNeumannAlgebra.IsNormal M ω` — `ω` is σ-weakly continuous on `M`.
* `VonNeumannAlgebra.NormalFunctional M` — the normal positive functionals on `M`.
* `VonNeumannAlgebra.IsNormal.vec` — a representing vector in `Completion (ℓ²(ℕ) ⊗[ℂ] H)`.
* `VonNeumannAlgebra.toCStarRep M` — the defining representation `M ⊆ B(H)` as a `CStarRep`.
* `VonNeumannAlgebra.vectorFunctional M ξ` — the vector functional `ω_ξ = ⟪ξ, (·) ξ⟫` on `M`, the
  vector functional `CStarRep.vectorFunctional` of the defining representation as a positive
  functional; `VonNeumannAlgebra.NormalFunctional.ofVector M ξ` — the same as a normal functional.
* `VonNeumannAlgebra.amplifiedVectorFunctional M Ξ` — the functional `⟪Ξ, (1 ⊗ ·) Ξ⟫` on `M` for
  `Ξ ∈ Completion (H₁ ⊗[ℂ] H)`; `VonNeumannAlgebra.NormalFunctional.ofAmplifiedVector M Ξ` — the
  same as a normal functional, for `Ξ ∈ Completion (ℓ²(ℕ) ⊗[ℂ] H)`.
* `VonNeumannAlgebra.IsNormalMap α` — a map `α : N → M` between von Neumann algebras is σ-weakly
  continuous; `VonNeumannAlgebra.NormalFunctional.comp` — `ω ∘ α` for a normal positive `α`.
* `VonNeumannAlgebra.NormalFunctional.supportProj ψ` — the support projection `s(ψ) ∈ M`.
* `PositiveLinearMap.toNormalFunctional ψ` — a positive functional on `B(H)`, `H`
  finite-dimensional, as a normal functional on `𝓑(H)`.

## Main results

* `lp.hasSum_inner_completion_lTensor_completionTensorEquiv` —
  `⟪Ξ, (1 ⊗ x) Η⟫ = ∑ₙ ⟪ξₙ, x ηₙ⟫` for `Ξ = lp.completionTensorEquiv ξ`,
  `Η = lp.completionTensorEquiv η`.
* `VonNeumannAlgebra.isNormal_of_hasSum_inner`, `VonNeumannAlgebra.IsNormal.exists_hasSum_inner` —
  `ω` is normal iff `ω(x) = ∑ₙ ⟪ξₙ, x ηₙ⟫` for square-summable `ξ`, `η`.
* `VonNeumannAlgebra.isNormal_iff_exists_inner_completion_lTensor_eq` — `ω` is normal iff
  `ω(x) = ⟪Ξ, (1 ⊗ x) Ξ⟫` for some `Ξ ∈ Completion (ℓ²(ℕ) ⊗[ℂ] H)`;
  `VonNeumannAlgebra.isNormal_iff_exists_hasSum_inner_self` — iff `ω = ∑ₙ ω_{ξₙ}`.
* `VonNeumannAlgebra.isNormal_vectorFunctional` — vector functionals are normal.
* `VonNeumannAlgebra.isNormalMap_id`, `VonNeumannAlgebra.IsNormal.comp`,
  `VonNeumannAlgebra.IsNormalMap.comp` — the identity is normal, and normality is stable
  under composition with normal maps.
* `VonNeumannAlgebra.isNormal_of_finiteDimensional`,
  `VonNeumannAlgebra.isNormalMap_of_finiteDimensional` — every positive functional on, and every
  linear map out of, a von Neumann algebra on a finite-dimensional space is normal.
* `VonNeumannAlgebra.NormalFunctional.supportProj_mem`,
  `VonNeumannAlgebra.NormalFunctional.isStarProjection_supportProj` — `s(ψ)` is a projection in `M`.
* `VonNeumannAlgebra.NormalFunctional.supportProj_le_iff` — `s(ψ) ≤ p ↔ ψ(1 - p) = 0` for
  projections `p ∈ M`; `VonNeumannAlgebra.NormalFunctional.apply_one_sub_supportProj` —
  `ψ(1 - s(ψ)) = 0`.
* `VonNeumannAlgebra.NormalFunctional.apply_star_mul_self_eq_zero_iff` — `ψ(x⋆x) = 0 ↔ x s(ψ) = 0`.

## TODO

* Normality of a positive functional, and of a positive map between von Neumann algebras
  (`VonNeumannAlgebra.IsNormalMap`), is also equivalent to preserving the suprema of bounded
  increasing nets of self-adjoint elements. That equivalence is not formalised here.
-/

@[expose] public section

open scoped InnerProductSpace ComplexOrder Amplification lp TensorProduct
open UniformSpace

namespace lp

variable {ι : Type*} [DecidableEq ι] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- For `Ξ = completionTensorEquiv ξ = ∑ᵢ eᵢ ⊗ ξᵢ`, `(1 ⊗ x) Ξ = ∑ᵢ eᵢ ⊗ x ξᵢ`. -/
lemma completion_lTensor_completionTensorEquiv (ξ : ℓ²(ι, H)) (x : H →L[ℂ] H) :
    (𝟙[ℓ²(ι, ℂ)] ⊗ x) (completionTensorEquiv ℂ ξ) =
      completionTensorEquiv ℂ ⟨fun i => x (ξ i), lp.memℓp_apply_clm ξ x⟩ := by
  set L := (completionTensorEquiv ℂ (ι := ι) (K := H)).toContinuousLinearEquiv.toContinuousLinearMap
  have h₁ := (lp.hasSum_single ENNReal.ofNat_ne_top ξ).mapL ((𝟙[ℓ²(ι, ℂ)] ⊗ x).comp L)
  have h₂ := (lp.hasSum_single ENNReal.ofNat_ne_top
    (⟨fun i => x (ξ i), lp.memℓp_apply_clm ξ x⟩ : ℓ²(ι, H))).mapL L
  refine h₁.unique (h₂.congr_fun fun i => ?_)
  change (𝟙[ℓ²(ι, ℂ)] ⊗ x) (completionTensorEquiv ℂ (lp.single 2 i (ξ i))) =
    completionTensorEquiv ℂ (lp.single 2 i (x (ξ i)))
  rw [completionTensorEquiv_single, completionTensorEquiv_single,
    ContinuousLinearMap.completion_apply_coe, ContinuousLinearMap.lTensor_tmul]

/-- For `Ξ = completionTensorEquiv ξ` and `Η = completionTensorEquiv η`,
`⟪Ξ, (1 ⊗ x) Η⟫ = ∑ᵢ ⟪ξᵢ, x ηᵢ⟫`. -/
lemma hasSum_inner_completion_lTensor_completionTensorEquiv (ξ η : ℓ²(ι, H)) (x : H →L[ℂ] H) :
    HasSum (fun i => ⟪ξ i, x (η i)⟫_ℂ)
      ⟪completionTensorEquiv ℂ ξ, (𝟙[ℓ²(ι, ℂ)] ⊗ x) (completionTensorEquiv ℂ η)⟫_ℂ := by
  rw [completion_lTensor_completionTensorEquiv η x, LinearIsometryEquiv.inner_map_map]
  exact lp.hasSum_inner ξ _

end lp

namespace ContinuousLinearMap

variable {H₁ H : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- `⟪Ξ, (1 ⊗ x⋆x) Ξ⟫ = ‖(1 ⊗ x) Ξ‖²`. -/
lemma inner_completion_lTensor_star_mul_self [CompleteSpace H] (Ξ : Completion (H₁ ⊗[ℂ] H))
    (x : H →L[ℂ] H) :
    ⟪Ξ, (𝟙[H₁] ⊗ (star x * x)) Ξ⟫_ℂ = ((‖(𝟙[H₁] ⊗ x) Ξ‖ ^ 2 : ℝ) : ℂ) := by
  rw [lTensor_mul, completion_mul, star_eq_adjoint, ← adjoint_completion_lTensor,
    mul_apply_eq_comp, adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- `⟪Ξ, (1 ⊗ x⋆x) Η⟫ = ⟪(1 ⊗ x) Ξ, (1 ⊗ x) Η⟫`. -/
lemma inner_completion_lTensor_star_mul [CompleteSpace H] (Ξ Η : Completion (H₁ ⊗[ℂ] H))
    (x : H →L[ℂ] H) :
    ⟪Ξ, (𝟙[H₁] ⊗ (star x * x)) Η⟫_ℂ = ⟪(𝟙[H₁] ⊗ x) Ξ, (𝟙[H₁] ⊗ x) Η⟫_ℂ := by
  rw [lTensor_mul, completion_mul, star_eq_adjoint, ← adjoint_completion_lTensor,
    mul_apply_eq_comp, adjoint_inner_right]

/-- `⟪e ⊗ ξ, (1 ⊗ x)(e ⊗ ξ)⟫ = ⟪ξ, x ξ⟫` for a unit vector `e`. -/
lemma inner_coe_tmul_completion_lTensor_coe_tmul {e : H₁} (he : ‖e‖ = 1) (ξ : H) (x : H →L[ℂ] H) :
    ⟪(e ⊗ₜ[ℂ] ξ : Completion (H₁ ⊗[ℂ] H)),
      (𝟙[H₁] ⊗ x) (e ⊗ₜ[ℂ] ξ : Completion (H₁ ⊗[ℂ] H))⟫_ℂ = ⟪ξ, x ξ⟫_ℂ := by
  rw [completion_apply_coe, lTensor_tmul, Completion.inner_coe, TensorProduct.inner_tmul,
    inner_self_eq_norm_sq_to_K, he]
  simp

/-- `1 ⊗ p` is a projection along with `p`. -/
lemma isStarProjection_completion_lTensor [CompleteSpace H] {p : H →L[ℂ] H}
    (hp : IsStarProjection p) : IsStarProjection (𝟙[H₁] ⊗ p) :=
  ⟨by rw [IsIdempotentElem, ← completion_mul, ← lTensor_mul, hp.isIdempotentElem.eq],
    by rw [IsSelfAdjoint, star_eq_adjoint, adjoint_completion_lTensor, ← star_eq_adjoint,
      hp.isSelfAdjoint.star_eq]⟩

/-- `1 ⊗ (1 - p) = 1 - 1 ⊗ p`. -/
lemma completion_lTensor_one_sub [CompleteSpace H] (p : H →L[ℂ] H) :
    𝟙[H₁] ⊗ (1 - p : H →L[ℂ] H) = 1 - 𝟙[H₁] ⊗ p := by
  rw [← lTensorCompletionStarAlgHom_apply, map_sub, map_one]
  rfl

/-- For projections and a nonzero `H₁`, `1 ⊗ e ≤ 1 ⊗ f ↔ e ≤ f`. -/
lemma completion_lTensor_le_completion_lTensor_iff [CompleteSpace H] [Nontrivial H₁]
    {e f : H →L[ℂ] H} (he : IsStarProjection e) (hf : IsStarProjection f) :
    𝟙[H₁] ⊗ e ≤ 𝟙[H₁] ⊗ f ↔ e ≤ f := by
  rw [(isStarProjection_completion_lTensor he).le_iff_mul_eq_left
      (isStarProjection_completion_lTensor hf), he.le_iff_mul_eq_left hf,
    ← completion_mul, ← lTensor_mul]
  exact completion_lTensor_injective.eq_iff

end ContinuousLinearMap

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
/-- A positive functional `ω` on `M` is **normal** if it is σ-weakly continuous. By
`VonNeumannAlgebra.isNormal_iff_exists_hasSum_inner_self` this is equivalent to `ω` being a countable sum of
vector functionals. -/
def IsNormal (ω : M →ₚ[ℂ] ℂ) : Prop :=
  Continuous fun T : M.sigmaWeak => ω (M.ofSigmaWeak T)

variable (M) in
/-- The **normal positive functionals** on `M`. -/
abbrev NormalFunctional := {ω : M →ₚ[ℂ] ℂ // M.IsNormal ω}

/-- `A ↦ ∑ₙ ⟪ξₙ, A ηₙ⟫` is normal. -/
lemma isNormal_of_hasSum_inner {ω : M →ₚ[ℂ] ℂ} (ξ η : ℓ²(ℕ, H))
    (h : ∀ x : M, HasSum (fun n => ⟪ξ n, (x : H →L[ℂ] H) (η n)⟫_ℂ) (ω x)) : M.IsNormal ω := by
  have : (fun T : M.sigmaWeak => ω (M.ofSigmaWeak T)) =
      fun T : M.sigmaWeak => ∑' n, ⟪ξ n, (T : H →σw[ℂ] H) (η n)⟫_ℂ :=
    funext fun T => (h (M.ofSigmaWeak T)).tsum_eq.symm
  rw [IsNormal, this]
  exact (ContinuousLinearMapSigmaWeak.continuous_tsum_inner_apply ξ η).comp continuous_subtype_val

/-- A normal functional is `x ↦ ∑ₙ ⟪ξₙ, x ηₙ⟫` for square-summable sequences `ξ`, `η`. -/
lemma IsNormal.exists_hasSum_inner {ω : M →ₚ[ℂ] ℂ} (h : M.IsNormal ω) :
    ∃ ξ η : ℓ²(ℕ, H), ∀ x : M,
      HasSum (fun n => ⟪ξ n, (x : H →L[ℂ] H) (η n)⟫_ℂ) (ω x) := by
  obtain ⟨ξ, η, hξη⟩ := ContinuousLinearMapSigmaWeak.exists_lp_pair_of_continuous
    (S := M.sigmaWeak) (φ := ω.toLinearMap ∘ₗ M.ofSigmaWeak) h
  exact ⟨ξ, η, fun x => hξη (M.toSigmaWeak x)⟩

/-- **Normal functionals are vector functionals on the amplification.** A normal `ω` is
`x ↦ ⟪Ξ, (1 ⊗ x) Ξ⟫` for some `Ξ ∈ Completion (ℓ²(ℕ) ⊗[ℂ] H)`: from `ω(x) = ⟪Ξ₀, (1 ⊗ x) Η₀⟫`, positivity gives
`ω ≤ ω_Ζ` for the interleaving `Ζ` of `Ξ₀` and `Η₀`, and the Radon–Nikodym theorem gives
`ω = ω_{R Ζ}` with `R` in the commutant of `1 ⊗ M`. -/
theorem IsNormal.exists_inner_completion_lTensor_eq {ω : M →ₚ[ℂ] ℂ} (h : M.IsNormal ω) :
    ∃ Ξ : Completion (ℓ²(ℕ, ℂ) ⊗[ℂ] H), ∀ x : M, ⟪Ξ, (𝟙[ℓ²(ℕ, ℂ)] ⊗ x) Ξ⟫_ℂ = ω x := by
  obtain ⟨ξ, η, hξη⟩ := h.exists_hasSum_inner
  set ζ := lp.interleave ξ η
  set ρ : M →⋆ₐ[ℂ] (Completion (ℓ²(ℕ, ℂ) ⊗[ℂ] H) →L[ℂ] Completion (ℓ²(ℕ, ℂ) ⊗[ℂ] H)) :=
    (𝟙[ℓ²(ℕ, ℂ)] ⊗ₐ).comp M.toStarSubalgebra.subtype
  have hρ : ∀ x : M, ρ x = 𝟙[ℓ²(ℕ, ℂ)] ⊗ x := fun _ => rfl
  have hω : ∀ x : M, ω x = ⟪lp.completionTensorEquiv ℂ ξ, (𝟙[ℓ²(ℕ, ℂ)] ⊗ x) (lp.completionTensorEquiv ℂ η)⟫_ℂ :=
    fun x => (hξη x).unique (lp.hasSum_inner_completion_lTensor_completionTensorEquiv ξ η x)
  have hζ : ∀ y : H →L[ℂ] H, ⟪lp.completionTensorEquiv ℂ ζ, (𝟙[ℓ²(ℕ, ℂ)] ⊗ y) (lp.completionTensorEquiv ℂ ζ)⟫_ℂ =
      ⟪lp.completionTensorEquiv ℂ ξ, (𝟙[ℓ²(ℕ, ℂ)] ⊗ y) (lp.completionTensorEquiv ℂ ξ)⟫_ℂ +
        ⟪lp.completionTensorEquiv ℂ η, (𝟙[ℓ²(ℕ, ℂ)] ⊗ y) (lp.completionTensorEquiv ℂ η)⟫_ℂ := fun y => by
    refine (lp.hasSum_inner_completion_lTensor_completionTensorEquiv ζ ζ y).unique ?_
    have hzip := Stream'.zip_interleave (fun u v => ⟪u, y v⟫_ℂ)
      (ξ : ℕ → H) (η : ℕ → H) (ξ : ℕ → H) (η : ℕ → H)
    exact (congrArg (HasSum · _) hzip).mpr
      ((lp.hasSum_inner_completion_lTensor_completionTensorEquiv ξ ξ y).interleave
        (lp.hasSum_inner_completion_lTensor_completionTensorEquiv η η y))
  have hdom : ∀ x : M, ‖ω (star x * x)‖ ≤ ‖ρ x (lp.completionTensorEquiv ℂ ζ)‖ ^ 2 := fun x => by
    set a := ‖(𝟙[ℓ²(ℕ, ℂ)] ⊗ (x : H →L[ℂ] H)) (lp.completionTensorEquiv ℂ ξ)‖
    set b := ‖(𝟙[ℓ²(ℕ, ℂ)] ⊗ (x : H →L[ℂ] H)) (lp.completionTensorEquiv ℂ η)‖
    have hsq : ‖ρ x (lp.completionTensorEquiv ℂ ζ)‖ ^ 2 = a ^ 2 + b ^ 2 := by
      have := hζ (star (x : H →L[ℂ] H) * x)
      rw [ContinuousLinearMap.inner_completion_lTensor_star_mul_self,
        ContinuousLinearMap.inner_completion_lTensor_star_mul_self,
        ContinuousLinearMap.inner_completion_lTensor_star_mul_self, ← Complex.ofReal_add,
        Complex.ofReal_inj] at this
      rw [hρ]
      exact this
    rw [hsq, hω, MulMemClass.coe_mul, StarMemClass.coe_star,
      ContinuousLinearMap.inner_completion_lTensor_star_mul]
    refine (norm_inner_le_norm _ _).trans ?_
    change a * b ≤ a ^ 2 + b ^ 2
    nlinarith [sq_nonneg (a - b)]
  obtain ⟨R, -, -, hR⟩ :=
    CStarAlgebra.exists_commute_inner_eq_of_apply_star_mul_self_le (ρ := ρ.toNonUnitalStarAlgHom) (f := ω) hdom
  exact ⟨R (lp.completionTensorEquiv ℂ ζ), fun x => (hR x).symm⟩

/-- `ω` is normal iff it is the restriction to `1 ⊗ M` of a vector functional on
`Completion (ℓ²(ℕ) ⊗[ℂ] H)`. -/
lemma isNormal_iff_exists_inner_completion_lTensor_eq {ω : M →ₚ[ℂ] ℂ} :
    M.IsNormal ω ↔ ∃ Ξ : Completion (ℓ²(ℕ, ℂ) ⊗[ℂ] H),
      ∀ x : M, ⟪Ξ, (𝟙[ℓ²(ℕ, ℂ)] ⊗ x) Ξ⟫_ℂ = ω x := by
  refine ⟨IsNormal.exists_inner_completion_lTensor_eq, fun ⟨Ξ, hΞ⟩ => ?_⟩
  refine isNormal_of_hasSum_inner ((lp.completionTensorEquiv ℂ).symm Ξ)
    ((lp.completionTensorEquiv ℂ).symm Ξ) fun x => ?_
  have := lp.hasSum_inner_completion_lTensor_completionTensorEquiv ((lp.completionTensorEquiv ℂ).symm Ξ)
    ((lp.completionTensorEquiv ℂ).symm Ξ) (x : H →L[ℂ] H)
  rwa [LinearIsometryEquiv.apply_symm_apply, hΞ] at this

/-- **Normal functionals are countable sums of vector functionals**: `ω` is normal iff
`ω(x) = ∑ₙ ⟪ξₙ, x ξₙ⟫` for a square-summable sequence `(ξₙ)` in `H`. -/
theorem isNormal_iff_exists_hasSum_inner_self {ω : M →ₚ[ℂ] ℂ} :
    M.IsNormal ω ↔ ∃ ξ : ℓ²(ℕ, H),
      ∀ x : M, HasSum (fun n => ⟪ξ n, (x : H →L[ℂ] H) (ξ n)⟫_ℂ) (ω x) := by
  refine ⟨fun h => ?_, fun ⟨ξ, hξ⟩ => isNormal_of_hasSum_inner ξ ξ hξ⟩
  obtain ⟨Ξ, hΞ⟩ := isNormal_iff_exists_inner_completion_lTensor_eq.mp h
  refine ⟨(lp.completionTensorEquiv ℂ).symm Ξ, fun x => ?_⟩
  have := lp.hasSum_inner_completion_lTensor_completionTensorEquiv ((lp.completionTensorEquiv ℂ).symm Ξ)
    ((lp.completionTensorEquiv ℂ).symm Ξ) (x : H →L[ℂ] H)
  rwa [LinearIsometryEquiv.apply_symm_apply, hΞ] at this

namespace IsNormal

variable {ω : M →ₚ[ℂ] ℂ} (h : M.IsNormal ω)

/-- A **representing vector** `Ξ ∈ Completion (ℓ²(ℕ) ⊗[ℂ] H)` of a normal functional:
`ω(x) = ⟪Ξ, (1 ⊗ x) Ξ⟫`. -/
noncomputable def vec : Completion (ℓ²(ℕ, ℂ) ⊗[ℂ] H) :=
  (isNormal_iff_exists_inner_completion_lTensor_eq.mp h).choose

/-- `ω(x) = ⟪Ξ, (1 ⊗ x) Ξ⟫` for the representing vector `Ξ`. -/
lemma inner_vec_completion_lTensor (x : M) :
    ⟪h.vec, (𝟙[ℓ²(ℕ, ℂ)] ⊗ x) h.vec⟫_ℂ = ω x :=
  (isNormal_iff_exists_inner_completion_lTensor_eq.mp h).choose_spec x

end IsNormal

/-- `ω(1) = ‖Ξ‖²` for any vector `Ξ` representing `ω`. -/
lemma re_apply_one_eq_norm_sq {ω : M →ₚ[ℂ] ℂ} {Ξ : Completion (ℓ²(ℕ, ℂ) ⊗[ℂ] H)}
    (hΞ : ∀ x : M, ⟪Ξ, (𝟙[ℓ²(ℕ, ℂ)] ⊗ x) Ξ⟫_ℂ = ω x) : (ω 1).re = ‖Ξ‖ ^ 2 := by
  rw [← hΞ 1, OneMemClass.coe_one, ContinuousLinearMap.lTensor_one,
    ContinuousLinearMap.completion_one, one_apply_eq_self, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- `ω(x⋆ x) = ‖(1 ⊗ x) Ξ‖²` for any vector `Ξ` representing `ω`. -/
lemma apply_star_mul_self_eq {ω : M →ₚ[ℂ] ℂ} {Ξ : Completion (ℓ²(ℕ, ℂ) ⊗[ℂ] H)}
    (hΞ : ∀ x : M, ⟪Ξ, (𝟙[ℓ²(ℕ, ℂ)] ⊗ x) Ξ⟫_ℂ = ω x) (x : M) :
    ω (star x * x) = ((‖(𝟙[ℓ²(ℕ, ℂ)] ⊗ (x : H →L[ℂ] H)) Ξ‖ ^ 2 : ℝ) : ℂ) := by
  rw [← hΞ, MulMemClass.coe_mul, StarMemClass.coe_star,
    ContinuousLinearMap.inner_completion_lTensor_star_mul_self]

variable (M) in
/-- The **defining representation** of `M` on `H`, the inclusion `M ⊆ B(H)`, as a `CStarRep`. -/
noncomputable def toCStarRep : CStarRep M :=
  ⟨H, M.toStarSubalgebra.subtype.toNonUnitalStarAlgHom⟩

/-- The defining representation acts by inclusion. -/
@[simp]
lemma toCStarRep_π_apply (x : M) (ξ : H) : M.toCStarRep.π x ξ = (x : H →L[ℂ] H) ξ :=
  rfl

variable (M) in
/-- The **vector functional** `ω_ξ = ⟪ξ, (·) ξ⟫` on `M`: the vector functional
`CStarRep.vectorFunctional` of the defining representation `M.toCStarRep`, as a positive
functional. -/
noncomputable def vectorFunctional (ξ : H) : M →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (WeakDual.toStrongDual (M.toCStarRep.vectorFunctional ξ)).toLinearMap
    (M.toCStarRep.vectorFunctional_nonneg ξ)

/-- Evaluation of the vector functional: `ω_ξ(x) = ⟪ξ, x ξ⟫`. -/
@[simp]
lemma vectorFunctional_apply (ξ : H) (x : M) :
    M.vectorFunctional ξ x = ⟪ξ, (x : H →L[ℂ] H) ξ⟫_ℂ :=
  rfl

variable (M) in
/-- Vector functionals are normal. -/
lemma isNormal_vectorFunctional (ξ : H) : M.IsNormal (M.vectorFunctional ξ) :=
  isNormal_iff_exists_inner_completion_lTensor_eq.mpr
    ⟨((lp.single (E := fun _ : ℕ => ℂ) 2 0 (1 : ℂ) ⊗ₜ[ℂ] ξ : ℓ²(ℕ, ℂ) ⊗[ℂ] H) :
      Completion (ℓ²(ℕ, ℂ) ⊗[ℂ] H)), fun x => by
    rw [ContinuousLinearMap.inner_coe_tmul_completion_lTensor_coe_tmul
      (lp.norm_single_one two_pos 0), vectorFunctional_apply]⟩

variable (M) in
/-- The vector functional `ω_ξ` as a normal functional. -/
noncomputable def NormalFunctional.ofVector (ξ : H) : M.NormalFunctional :=
  ⟨M.vectorFunctional ξ, M.isNormal_vectorFunctional ξ⟩

variable (M) in
/-- The functional `x ↦ ⟪Ξ, (1 ⊗ x) Ξ⟫` on `M` induced by a vector `Ξ ∈ Completion (H₁ ⊗[ℂ] H)`. -/
noncomputable def amplifiedVectorFunctional {H₁ : Type*} [NormedAddCommGroup H₁]
    [InnerProductSpace ℂ H₁] (Ξ : Completion (H₁ ⊗[ℂ] H)) : M →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀
    { toFun := fun x => ⟪Ξ, (𝟙[H₁] ⊗ x) Ξ⟫_ℂ
      map_add' := fun x y => by
        simp [ContinuousLinearMap.completion_add, inner_add_right]
      map_smul' := fun c x => by
        simp [ContinuousLinearMap.completion_smul, inner_smul_right] }
    fun x hx => by
      obtain ⟨y, hy⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp
        (show (0 : H →L[ℂ] H) ≤ x from hx)
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [hy, ContinuousLinearMap.inner_completion_lTensor_star_mul_self]
      exact Complex.zero_le_real.mpr (sq_nonneg _)

/-- Evaluation of the amplified vector functional: `x ↦ ⟪Ξ, (1 ⊗ x) Ξ⟫`. -/
@[simp]
lemma amplifiedVectorFunctional_apply {H₁ : Type*} [NormedAddCommGroup H₁]
    [InnerProductSpace ℂ H₁] (Ξ : Completion (H₁ ⊗[ℂ] H)) (x : M) :
    M.amplifiedVectorFunctional Ξ x = ⟪Ξ, (𝟙[H₁] ⊗ x) Ξ⟫_ℂ :=
  rfl

variable (M) in
/-- The functional `x ↦ ⟪Ξ, (1 ⊗ x) Ξ⟫` induced by `Ξ ∈ Completion (ℓ²(ℕ) ⊗[ℂ] H)` as a normal
functional; every normal functional is of this form
(`VonNeumannAlgebra.isNormal_iff_exists_inner_completion_lTensor_eq`). -/
noncomputable def NormalFunctional.ofAmplifiedVector (Ξ : Completion (ℓ²(ℕ, ℂ) ⊗[ℂ] H)) :
    M.NormalFunctional :=
  ⟨M.amplifiedVectorFunctional Ξ,
    isNormal_iff_exists_inner_completion_lTensor_eq.mpr ⟨Ξ, fun _ => rfl⟩⟩

section NormalMap

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {N : VonNeumannAlgebra K} {F : Type*}

/-- A map `α : N → M` between von Neumann algebras is **normal** if it is σ-weakly continuous,
the same notion as `VonNeumannAlgebra.IsNormal` for functionals. -/
def IsNormalMap (α : N → M) : Prop :=
  Continuous fun T : N.sigmaWeak => M.toSigmaWeak (α (N.ofSigmaWeak T))

/-- The composite of a normal functional with a normal positive map is normal. -/
lemma IsNormal.comp [FunLike F N M] [LinearMapClass F ℂ N M] [OrderHomClass F N M]
    {ω : M →ₚ[ℂ] ℂ} (hω : M.IsNormal ω) {α : F} (hα : IsNormalMap α) :
    N.IsNormal (ω.comp (PositiveLinearMap.ofClass α)) :=
  Continuous.comp (g := fun T : M.sigmaWeak => ω (M.ofSigmaWeak T)) hω hα

/-- The identity map of a von Neumann algebra is normal. -/
lemma isNormalMap_id : IsNormalMap (id : N → N) :=
  continuous_id

/-- **Positive functionals on a von Neumann algebra on a finite-dimensional space are normal**: in
finite dimensions the σ-weak topology is the unique Hausdorff vector-space topology, so every linear
functional is σ-weakly continuous. -/
theorem isNormal_of_finiteDimensional [FiniteDimensional ℂ H] (ω : M →ₚ[ℂ] ℂ) : M.IsNormal ω :=
  LinearMap.continuous_of_finiteDimensional (ω.toLinearMap ∘ₗ M.ofSigmaWeak)

/-- **Linear maps out of a finite-dimensional von Neumann algebra are normal**: in finite
dimensions the σ-weak topology is the unique Hausdorff vector-space topology, so every linear map out
of it is σ-weakly continuous, whatever the target. -/
theorem isNormalMap_of_finiteDimensional [FiniteDimensional ℂ K]
    [FunLike F N M] [LinearMapClass F ℂ N M] (α : F) : IsNormalMap α := by
  let e : M →ₗ[ℂ] M.sigmaWeak :=
    { toFun := M.toSigmaWeak
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact LinearMap.continuous_of_finiteDimensional
    (e ∘ₗ (LinearMap.ofClass α) ∘ₗ N.ofSigmaWeak)

/-- The composite of two normal maps is normal. -/
lemma IsNormalMap.comp {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L]
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
lemma NormalFunctional.comp_apply [FunLike F N M] [LinearMapClass F ℂ N M]
    [OrderHomClass F N M] (ω : M.NormalFunctional) (α : F) (hα : IsNormalMap α) (x : N) :
    (ω.comp α hα).1 x = ω.1 (α x) :=
  rfl

end NormalMap

/-! ### The support projection of a normal functional -/

namespace NormalFunctional

variable (ψ : M.NormalFunctional)

/-- A representing vector's support lies in `1 ⊗ M`. -/
lemma exists_completion_lTensor_eq_supportProj :
    ∃ x ∈ M, 𝟙[ℓ²(ℕ, ℂ)] ⊗ x = (𝟙[ℓ²(ℕ, ℂ)] ⊗ M).supportProj ψ.2.vec :=
  mem_oneTensor_iff.mp ((𝟙[ℓ²(ℕ, ℂ)] ⊗ M).supportProj_mem ψ.2.vec)

/-- The **support projection** `s(ψ) ∈ M` of a normal functional: the element of `M` with
`1 ⊗ s(ψ) = s(Ξ_ψ)`, the vector support of a representing vector in `oneTensor ℓ²(ℕ) M`. -/
noncomputable def supportProj : H →L[ℂ] H :=
  (exists_completion_lTensor_eq_supportProj ψ).choose

/-- `s(ψ) ∈ M`. -/
lemma supportProj_mem : supportProj ψ ∈ M :=
  (exists_completion_lTensor_eq_supportProj ψ).choose_spec.1

/-- `1 ⊗ s(ψ) = s(Ξ_ψ)` for the chosen representing vector. -/
lemma completion_lTensor_supportProj :
    𝟙[ℓ²(ℕ, ℂ)] ⊗ (supportProj ψ) = (𝟙[ℓ²(ℕ, ℂ)] ⊗ M).supportProj ψ.2.vec :=
  (exists_completion_lTensor_eq_supportProj ψ).choose_spec.2

/-- **Independence of the representing vector.** `1 ⊗ s(ψ) = s(Ξ)` for *every* `Ξ` with
`ψ(x) = ⟪Ξ, (1 ⊗ x) Ξ⟫`. -/
lemma completion_lTensor_supportProj_eq {Ξ : Completion (ℓ²(ℕ, ℂ) ⊗[ℂ] H)}
    (hΞ : ∀ x : M, ⟪Ξ, (𝟙[ℓ²(ℕ, ℂ)] ⊗ x) Ξ⟫_ℂ = ψ.1 x) :
    𝟙[ℓ²(ℕ, ℂ)] ⊗ (supportProj ψ) = (𝟙[ℓ²(ℕ, ℂ)] ⊗ M).supportProj Ξ := by
  rw [completion_lTensor_supportProj]
  refine supportProj_eq_of_inner_eq fun y hy => inner_apply_eq_of_mem_oneTensor (fun x hx => ?_) hy
  rw [ψ.2.inner_vec_completion_lTensor ⟨x, hx⟩, hΞ ⟨x, hx⟩]

/-- `s(ψ)` is a projection. -/
lemma isStarProjection_supportProj : IsStarProjection (supportProj ψ) := by
  have hS := (𝟙[ℓ²(ℕ, ℂ)] ⊗ M).isStarProjection_supportProj ψ.2.vec
  rw [← completion_lTensor_supportProj] at hS
  refine ⟨ContinuousLinearMap.completion_lTensor_injective (H₁ := ℓ²(ℕ, ℂ)) ?_,
    ContinuousLinearMap.completion_lTensor_injective (H₁ := ℓ²(ℕ, ℂ)) ?_⟩
  · dsimp only
    rw [ContinuousLinearMap.lTensor_mul, ContinuousLinearMap.completion_mul,
      hS.isIdempotentElem.eq]
  · dsimp only
    rw [ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.adjoint_completion_lTensor,
      ← ContinuousLinearMap.star_eq_adjoint, hS.isSelfAdjoint.star_eq]

/-- **Characterisation of the support.** For a projection `p ∈ M`, `s(ψ) ≤ p ↔ ψ(1 - p) = 0`:
`s(ψ)` is the smallest projection of `M` carrying `ψ`. -/
lemma supportProj_le_iff {p : H →L[ℂ] H} (hp : IsStarProjection p) (hpM : p ∈ M) :
    supportProj ψ ≤ p ↔ ψ.1 ⟨1 - p, sub_mem (one_mem M) hpM⟩ = 0 := by
  rw [← ContinuousLinearMap.completion_lTensor_le_completion_lTensor_iff (H₁ := ℓ²(ℕ, ℂ))
      (isStarProjection_supportProj ψ) hp,
    completion_lTensor_supportProj,
    supportProj_le_iff_inner_eq_zero (ContinuousLinearMap.isStarProjection_completion_lTensor hp)
      (completion_lTensor_mem_oneTensor hpM), ← ψ.2.inner_vec_completion_lTensor ⟨1 - p, _⟩]
  change _ ↔ ⟪_, (𝟙[ℓ²(ℕ, ℂ)] ⊗ (1 - p : H →L[ℂ] H)) _⟫_ℂ = 0
  rw [ContinuousLinearMap.completion_lTensor_one_sub]

/-- `ψ(1 - s(ψ)) = 0`. -/
lemma apply_one_sub_supportProj :
    ψ.1 ⟨1 - supportProj ψ, sub_mem (one_mem M) (supportProj_mem ψ)⟩ = 0 :=
  (supportProj_le_iff ψ (isStarProjection_supportProj ψ) (supportProj_mem ψ)).mp le_rfl

/-- **The null ideal.** `ψ(x⋆x) = 0 ↔ x s(ψ) = 0`. -/
lemma apply_star_mul_self_eq_zero_iff (x : M) :
    ψ.1 (star x * x) = 0 ↔ (x : H →L[ℂ] H) * supportProj ψ = 0 := by
  rw [apply_star_mul_self_eq ψ.2.inner_vec_completion_lTensor, Complex.ofReal_eq_zero,
    pow_eq_zero_iff two_ne_zero, norm_eq_zero,
    ← mul_supportProj_eq_zero_iff (completion_lTensor_mem_oneTensor (H₁ := ℓ²(ℕ, ℂ)) x.2),
    ← completion_lTensor_supportProj, ← ContinuousLinearMap.completion_mul,
    ← ContinuousLinearMap.lTensor_mul]
  exact (ContinuousLinearMap.completion_lTensor_injective (H₁ := ℓ²(ℕ, ℂ))).eq_iff' (by simp)

/-- **Support inclusion is null-ideal inclusion.** `s(ψ) ≤ s(φ)` iff `ψ(x⋆x) = 0` whenever
`φ(x⋆x) = 0`. -/
lemma supportProj_le_supportProj_iff (φ : M.NormalFunctional) :
    supportProj ψ ≤ supportProj φ ↔ ∀ x : M, φ.1 (star x * x) = 0 → ψ.1 (star x * x) = 0 := by
  refine ⟨fun hle x hφ => ?_, fun h => ?_⟩
  · rw [apply_star_mul_self_eq_zero_iff] at hφ ⊢
    rw [← ((isStarProjection_supportProj ψ).le_iff_mul_eq_right
      (isStarProjection_supportProj φ)).mp hle, ← mul_assoc, hφ, zero_mul]
  · set e : M := ⟨1 - supportProj φ, sub_mem (one_mem M) (supportProj_mem φ)⟩
    have hee : star e * e = e := by
      apply Subtype.ext
      change star (1 - supportProj φ) * (1 - supportProj φ) = 1 - supportProj φ
      have hp := (isStarProjection_supportProj φ).one_sub
      rw [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]
    have h1 := h e (by rw [hee]; exact apply_one_sub_supportProj φ)
    rw [hee] at h1
    exact (supportProj_le_iff ψ (isStarProjection_supportProj φ) (supportProj_mem φ)).mpr h1

end NormalFunctional

end VonNeumannAlgebra

/-! ### Positive functionals on `B(H)` in finite dimension -/

namespace PositiveLinearMap

open scoped VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

/-- A positive functional `ψ` on `B(H) = H →L[ℂ] H`, for finite-dimensional `H`, as a normal
functional on the von Neumann algebra `𝓑(H)` of all bounded operators: the restriction of `ψ`
along the inclusion `𝓑(H) → B(H)`, normal by `VonNeumannAlgebra.isNormal_of_finiteDimensional`.
This is how Araki's relative entropy `VonNeumannAlgebra.arakiEntropy` applies to functionals on
`B(H)`. -/
noncomputable def toNormalFunctional (ψ : (H →L[ℂ] H) →ₚ[ℂ] ℂ) : 𝓑(H).NormalFunctional :=
  ⟨.mk₀ (ψ.toLinearMap ∘ₗ SMulMemClass.subtype 𝓑(H)) fun _ hx => map_nonneg ψ hx,
    VonNeumannAlgebra.isNormal_of_finiteDimensional _⟩

/-- `ψ.toNormalFunctional` evaluates as `ψ`. -/
@[simp] lemma toNormalFunctional_apply (ψ : (H →L[ℂ] H) →ₚ[ℂ] ℂ) (x : 𝓑(H)) :
    ψ.toNormalFunctional.1 x = ψ x :=
  rfl

/-- `ψ ↦ ψ.toNormalFunctional` is injective. -/
lemma toNormalFunctional_injective :
    Function.Injective (toNormalFunctional (H := H)) := fun ψ φ h => by
  ext A
  simpa using congrArg (fun ω : 𝓑(H).NormalFunctional => ω.1 ⟨A, trivial⟩) h

end PositiveLinearMap
