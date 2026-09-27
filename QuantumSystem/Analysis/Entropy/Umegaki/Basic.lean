/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.KLFun
public import QuantumSystem.Analysis.Entropy.Araki.Matrix
public import QuantumSystem.Analysis.Entropy.Araki.Monotonicity
public import QuantumSystem.Analysis.Matrix.LiebConcavity
public import QuantumSystem.Analysis.Matrix.QuantumChannel.DensityMatrix
public import QuantumSystem.Analysis.Matrix.QuantumChannel.Dual
public import QuantumSystem.ForMathlib.Analysis.Calculus.Deriv.Sign
public import QuantumSystem.ForMathlib.Analysis.Normed.Lp.ProdLp

/-!
# Umegaki's relative entropy

**Umegaki's relative entropy** of positive semidefinite matrices `ρ, σ` on `ℂⁿ` is
`D(ρ ‖ σ) = Tr ρ (log ρ - log σ)` if `supp ρ ⊆ supp σ`, and `+∞` otherwise (Umegaki 1962).
Neither matrix needs trace `1`. It is defined here as the finite-dimensional case of Araki's
relative entropy: `Matrix.umegakiEntropy ρ σ` is `S(ω_ρ ‖ ω_σ)` for the normal functionals
`ω_ρ = Tr (ρ ·)` and `ω_σ = Tr (σ ·)` of `B(ℂⁿ)` (`VonNeumannAlgebra.arakiEntropy`,
`Matrix.PosSemidef.normalFunctional`), and Umegaki's trace formula is the theorem
`Matrix.umegakiEntropy_eq_ite`. If `ρ` or `σ` is not positive semidefinite, `D(ρ ‖ σ)` is the junk
value `0`. Logarithms are natural, so the unit is the nat.

A result about `S(ω_ρ ‖ ω_σ)` is a result about `D(ρ ‖ σ)` by definition. Monotonicity under
channels is Araki's data-processing inequality for the dual channel, a unital normal Schwarz map
(`Matrix.QuantumChannel.dualSchwarzMap`).

## Main definitions

* `Matrix.umegakiEntropy ρ σ` — `D(ρ ‖ σ) ∈ EReal`, with notation `D(ρ ∥ σ)` in scope
  `Matrix.QuantumInfo` (the code notation uses `∥`, U+2225, where the prose writes `‖`).

## Main results

For positive semidefinite `ρ, σ` of any trace (Klein, faithfulness, monotonicity, joint convexity
and reindexing also have density-matrix forms in namespace `DensityMatrix`):

* `Matrix.umegakiEntropy_eq_ite`, `Matrix.umegakiEntropy_of_suppSubset`,
  `Matrix.umegakiEntropy_of_not_suppSubset` — **Umegaki's formula**.
* `VonNeumannAlgebra.arakiVec_eq_umegakiEntropy`, `VonNeumannAlgebra.arakiEntropy_eq_umegakiEntropy`
  — Araki's relative entropy of any vectors (on `K ⊗̂ ℂⁿ`, for every multiplicity space `K`) or
  normal functionals representing `ρ` and `σ` is `D(ρ ‖ σ)`.
* `Matrix.umegakiEntropy_nonneg` — **Klein's inequality** `0 ≤ D(ρ ‖ σ)` when `Tr σ ≤ Tr ρ`.
* `Matrix.umegakiEntropy_eq_zero_iff` — **faithfulness**: `D(ρ ‖ σ) = 0 ↔ ρ = σ` when
  `Tr ρ = Tr σ`.
* `Matrix.umegakiEntropy_channel_le` — **monotonicity** (data-processing inequality):
  `D(Φ(ρ) ‖ Φ(σ)) ≤ D(ρ ‖ σ)` for a quantum channel `Φ`.
* `Matrix.umegakiEntropy_channel_eq_of_recoverable` — equality in monotonicity when a recovery
  channel exists: if `R(Φ(ρ)) = ρ` and `R(Φ(σ)) = σ`, then `D(Φ(ρ) ‖ Φ(σ)) = D(ρ ‖ σ)`.
* `Matrix.umegakiEntropy_map_starAlgEquiv`, `Matrix.umegakiEntropy_reindex` — isometric invariance
  `D(φ(ρ) ‖ φ(σ)) = D(ρ ‖ σ)` under every `⋆`-algebra equivalence, for all matrices.
* `Matrix.umegakiEntropy_ne_bot` — `D(ρ ‖ σ) ≠ -∞`.
* `Matrix.umegakiEntropy_jointly_convex` — joint convexity
  `D(p ρ₁ + (1 - p) ρ₂ ‖ p σ₁ + (1 - p) σ₂) ≤ p D(ρ₁ ‖ σ₁) + (1 - p) D(ρ₂ ‖ σ₂)`.

## Proofs

Monotonicity is `VonNeumannAlgebra.arakiEntropy_comp_le` for the dual channel
`Φ* B = Σᵢ Kᵢᴴ B Kᵢ`, which pulls `ω_ρ` back to `ω_{Φ(ρ)}` (`Matrix.trace_mul_traceDual`).
Joint convexity differentiates `s ↦ Tr ρˢ σ¹⁻ˢ` at `s = 1` and uses Lieb's concavity theorem.
Faithfulness writes `D(ρ ‖ σ)` in the eigenbases of `ρ` and `σ` as a sum of Kullback–Leibler terms.

### Recovery and equality
If a channel R recovers both states, R(Φ(ρ)) = ρ and R(Φ(σ)) = σ, then equality holds in
monotonicity; this direction is `Matrix.umegakiEntropy_channel_eq_of_recoverable`. Petz's theorem
gives the converse — equality forces the existence of such an R, explicitly the Petz map
  R(·) = σ^(1/2) Φ*(Φ(σ)^(-1/2) · Φ(σ)^(-1/2)) σ^(1/2)
with Φ* the trace dual `Matrix.traceDual Φ` — but that converse is **not** formalised here.

## References

* H. Umegaki, *Conditional expectation in an operator algebra IV (entropy and information)*,
  Kodai Math. Sem. Rep. 14 (1962), 59–85.
* H. Araki, *Relative entropy of states of von Neumann algebras*, Publ. RIMS 11 (1976), 809–833.
* A. Uhlmann, *Relative entropy and the Wigner–Yanase–Dyson–Lieb concavity in an interpolation
  theory*, Comm. Math. Phys. 54 (1977), 21–32.
* Lindblad, *Completely positive maps and entropy inequalities*
* Petz, *Monotonicity of quantum relative entropy revisited*
* Ruskai, *Inequalities for quantum entropy: A review with conditions for equality*
-/

@[expose] public section

namespace Matrix

open scoped MatrixOrder ComplexOrder QuantumInfo Araki

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-! ### Definition and Umegaki's formula -/

/-- **Umegaki's relative entropy** `D(ρ ‖ σ)` of positive semidefinite matrices (Umegaki 1962),
defined as Araki's relative entropy `S(ω_ρ ‖ ω_σ)` of the normal functionals `ω_ρ = Tr (ρ ·)` and
`ω_σ = Tr (σ ·)` of `B(ℂⁿ)` (`Matrix.PosSemidef.normalFunctional`). Neither matrix needs trace `1`:
the definition covers density matrices as well as unnormalised references such as the identity in
`D(ρ_AB ‖ 1 ⊗ ρ_B)`. Umegaki's formula — `Tr ρ (log ρ - log σ)` if `supp ρ ⊆ supp σ`, and `+∞`
otherwise — is `Matrix.umegakiEntropy_eq_ite`. Logarithms are natural, so the unit is the nat.

If `ρ` or `σ` is not positive semidefinite the value is the junk value `0`
(`Matrix.umegakiEntropy_of_not_posSemidef`). Theorems about the value of `D(ρ ‖ σ)` assume
positivity; the few that hold for all matrices (`Matrix.umegakiEntropy_ne_bot`,
`Matrix.umegakiEntropy_map_starAlgEquiv`, `Matrix.umegakiEntropy_reindex`) are stated without it. -/
noncomputable def umegakiEntropy (ρ σ : Matrix n n ℂ) : EReal :=
  letI := Classical.propDecidable (ρ.PosSemidef ∧ σ.PosSemidef)
  if h : ρ.PosSemidef ∧ σ.PosSemidef then S⟦h.1.normalFunctional ∥ h.2.normalFunctional⟧ else 0

namespace QuantumInfo
/-- `D(ρ ∥ σ)` is Umegaki's relative entropy `Matrix.umegakiEntropy ρ σ`. -/
scoped notation "D(" ρ " ∥ " σ ")" => Matrix.umegakiEntropy ρ σ
end QuantumInfo

variable {ρ σ : Matrix n n ℂ}

/-- For positive semidefinite `ρ, σ`, `D(ρ ‖ σ)` is Araki's `S(ω_ρ ‖ ω_σ)`. -/
theorem umegakiEntropy_def (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    D(ρ ∥ σ) = S⟦hρ.normalFunctional ∥ hσ.normalFunctional⟧ := by
  rw [umegakiEntropy, dite_eq_left ⟨hρ, hσ⟩]

/-- The junk value: `D(ρ ‖ σ) = 0` unless both `ρ` and `σ` are positive semidefinite. -/
theorem umegakiEntropy_of_not_posSemidef (h : ¬ (ρ.PosSemidef ∧ σ.PosSemidef)) :
    D(ρ ∥ σ) = 0 := by
  rw [umegakiEntropy, dite_eq_right h]

/-- **Umegaki's formula**: `D(ρ ‖ σ) = Tr ρ (log ρ - log σ)` if `supp ρ ⊆ supp σ`, and `+∞`
otherwise. With Mathlib's `Real.log 0 = 0`, `log σ` vanishes on `ker σ`, which `ρ` annihilates in
the first case. -/
theorem umegakiEntropy_eq_ite (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    [Decidable (SuppSubset ρ σ)] :
    D(ρ ∥ σ) =
      if SuppSubset ρ σ then (((Tr (ρ * (cfc Real.log ρ - cfc Real.log σ))).re : ℝ) : EReal)
      else ⊤ := by
  rw [umegakiEntropy_def hρ hσ]
  exact VonNeumannAlgebra.arakiEntropy_normalFunctional hρ hσ

/-- `D(ρ ‖ σ) = Tr ρ (log ρ - log σ)` when `supp ρ ⊆ supp σ`. -/
theorem umegakiEntropy_of_suppSubset (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (h : SuppSubset ρ σ) :
    D(ρ ∥ σ) = (((Tr (ρ * (cfc Real.log ρ - cfc Real.log σ))).re : ℝ) : EReal) := by
  classical
  rw [umegakiEntropy_eq_ite hρ hσ, ite_eq_left h]

/-- `D(ρ ‖ σ) = +∞` when `supp ρ ⊄ supp σ`. -/
theorem umegakiEntropy_of_not_suppSubset (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (h : ¬ SuppSubset ρ σ) : D(ρ ∥ σ) = ⊤ := by
  classical
  rw [umegakiEntropy_eq_ite hρ hσ, ite_eq_right h]

/-- **Finiteness**: `D(ρ ‖ σ) < +∞` exactly when `supp ρ ⊆ supp σ`. -/
theorem umegakiEntropy_ne_top_iff (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    D(ρ ∥ σ) ≠ ⊤ ↔ SuppSubset ρ σ := by
  refine ⟨fun h => by_contra fun hs => h (umegakiEntropy_of_not_suppSubset hρ hσ hs), fun h => ?_⟩
  rw [umegakiEntropy_of_suppSubset hρ hσ h]
  exact EReal.coe_ne_top _

end Matrix

/-! ### Araki's relative entropy of representing vectors and functionals -/

namespace VonNeumannAlgebra

open Matrix.PosSemidef
open scoped InnerProductSpace VonNeumannAlgebra HilbertTensor Matrix.QuantumInfo Araki ComplexOrder
  TensorProduct
open HilbertTensor (amplifyLeft amplifyRight amplifyLeft_adjoint amplifyLeft_comp amplifyLeft_one
  amplifyLeft_comp_amplifyRight)

variable {n : Type*} [Fintype n] [DecidableEq n]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {g : n → K}
  {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)

/-- `B(ℂⁿ)` acting on the second leg of `K ⊗̂ ℂⁿ`, i.e. `1 ⊗ B(ℂⁿ)`. -/
local notation "𝓜" => VonNeumannAlgebra.amplify K 𝓑(EuclideanSpace ℂ n)

/-- **Araki = Umegaki on `ℂⁿ ⊗̂ ℂⁿ`**, with the purifications along the standard basis. -/
theorem arakiVec_purification_basisFun :
    (VonNeumannAlgebra.amplify (EuclideanSpace ℂ n) 𝓑(EuclideanSpace ℂ n)).arakiVec
        (hρ.purification (EuclideanSpace.basisFun n ℂ)) (hσ.purification (EuclideanSpace.basisFun n ℂ)) =
      D(ρ ∥ σ) := by
  classical
  rw [Matrix.umegakiEntropy_eq_ite hρ hσ]
  exact arakiVec_purification hρ hσ (EuclideanSpace.basisFun n ℂ).orthonormal

include hρ hσ in
/-- `arakiVec_eq_umegakiEntropy` when `K` carries `n` orthonormal vectors `g`, so that the
purifications `Ω_ρ, Ω_σ` along `g` live in `K ⊗̂ ℂⁿ` itself. -/
private theorem arakiVec_eq_umegakiEntropy_of_orthonormal [CompleteSpace K] (hg : Orthonormal ℂ g)
    {ξ η : K ⊗̂ EuclideanSpace ℂ n}
    (hξ : ∀ A : Matrix n n ℂ,
      ⟪ξ, amplifyRight (Matrix.toEuclideanCLM (𝕜 := ℂ) A) ξ⟫_ℂ = Tr (ρ * A))
    (hη : ∀ A : Matrix n n ℂ,
      ⟪η, amplifyRight (Matrix.toEuclideanCLM (𝕜 := ℂ) A) η⟫_ℂ = Tr (σ * A)) :
    (𝓜).arakiVec ξ η = D(ρ ∥ σ) := by
  classical
  rw [Matrix.umegakiEntropy_eq_ite hρ hσ, ← arakiVec_purification hρ hσ hg]
  refine arakiVec_eq_of_inner_eq (fun y hy => inner_apply_eq_of_mem_amplify (fun x _ => ?_) hy)
    (fun y hy => inner_apply_eq_of_mem_amplify (fun x _ => ?_) hy)
  · obtain ⟨A, rfl⟩ : ∃ A, Matrix.toEuclideanCLM (𝕜 := ℂ) A = x :=
      ⟨(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)).symm x, StarAlgEquiv.apply_symm_apply _ _⟩
    rw [hρ.inner_purification_amplifyRight hg, hξ]
  · obtain ⟨A, rfl⟩ : ∃ A, Matrix.toEuclideanCLM (𝕜 := ℂ) A = x :=
      ⟨(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)).symm x, StarAlgEquiv.apply_symm_apply _ _⟩
    rw [hσ.inner_purification_amplifyRight hg, hη]

omit [DecidableEq n] in
/-- On `K ⊗̂ ℂⁿ` with `K` trivial or `n` empty, every vector is `0`: the algebraic tensor product is
trivial and dense. -/
private lemma eq_zero_of_subsingleton_tensor [Subsingleton (K ⊗[ℂ] EuclideanSpace ℂ n)]
    (ξ : K ⊗̂ EuclideanSpace ℂ n) : ξ = 0 := by
  refine UniformSpace.Completion.induction_on ξ (isClosed_eq continuous_id continuous_const)
    fun a => ?_
  rw [Subsingleton.elim a 0, UniformSpace.Completion.coe_zero]

include hρ hσ in
/-- **Araki = Umegaki, for any representing vectors.** If `ξ, η ∈ K ⊗̂ ℂⁿ` represent `ρ` and `σ` on
`1 ⊗ B(ℂⁿ)` — `⟪ξ, (1 ⊗ A) ξ⟫ = Tr (ρ A)` and likewise for `η` — then
`S_{1 ⊗ B(ℂⁿ)}(ω_ξ ‖ ω_η) = D(ρ ‖ σ)`, for every multiplicity space `K`.

The value is computed on the enlargement `K' = K ⊕ ℂⁿ`, which carries the purifications along the
standard basis of `ℂⁿ`: the isometry `V = ι ⊗ 1 : K ⊗̂ ℂⁿ → K' ⊗̂ ℂⁿ` induced by `ι : K → K'`
intertwines `1 ⊗ B(ℂⁿ)` and its commutant `B(K) ⊗ 1` with those on `K' ⊗̂ ℂⁿ`, so it preserves the
relative entropy (`VonNeumannAlgebra.arakiVec_of_intertwiner`). -/
theorem arakiVec_eq_umegakiEntropy [CompleteSpace K] {ξ η : K ⊗̂ EuclideanSpace ℂ n}
    (hξ : ∀ A : Matrix n n ℂ,
      ⟪ξ, amplifyRight (Matrix.toEuclideanCLM (𝕜 := ℂ) A) ξ⟫_ℂ = Tr (ρ * A))
    (hη : ∀ A : Matrix n n ℂ,
      ⟪η, amplifyRight (Matrix.toEuclideanCLM (𝕜 := ℂ) A) η⟫_ℂ = Tr (σ * A)) :
    (𝓜).arakiVec ξ η = D(ρ ∥ σ) := by
  classical
  -- Degenerate case: `K ⊗̂ ℂⁿ = 0`, so `ξ = η = 0` and `ρ = σ = 0`.
  by_cases hdeg : Subsingleton K ∨ IsEmpty n
  · have : Subsingleton (K ⊗[ℂ] EuclideanSpace ℂ n) := by
      rcases hdeg with hK | hn
      · infer_instance
      · infer_instance
    have hzero : ∀ (τ : Matrix n n ℂ) (ζ : K ⊗̂ EuclideanSpace ℂ n),
        (∀ A : Matrix n n ℂ,
          ⟪ζ, amplifyRight (Matrix.toEuclideanCLM (𝕜 := ℂ) A) ζ⟫_ℂ = Tr (τ * A)) → τ = 0 :=
      fun τ ζ hζ => Matrix.ext_iff_trace_mul_right.mpr fun A => by
        rw [← hζ A, eq_zero_of_subsingleton_tensor ζ, inner_zero_left, Matrix.zero_mul,
          Matrix.trace_zero]
    obtain rfl := hzero ρ ξ hξ
    obtain rfl := hzero σ η hη
    rw [eq_zero_of_subsingleton_tensor ξ, eq_zero_of_subsingleton_tensor η, arakiVec_self,
      Matrix.umegakiEntropy_of_suppSubset hρ hσ fun _ h => h, Matrix.zero_mul, Matrix.trace_zero,
      Complex.zero_re, EReal.coe_zero]
  -- Main case: enlarge `K` to `K' = K ⊕ ℂⁿ`.
  obtain ⟨hK, hn⟩ : Nontrivial K ∧ Nonempty n := by
    simp only [not_or, not_subsingleton_iff_nontrivial, not_isEmpty_iff] at hdeg
    exact hdeg
  let E := EuclideanSpace ℂ n
  let K' := WithLp 2 (K × E)
  let ι : K →L[ℂ] K' := (WithLp.inlₗᵢ 2 ℂ K E).toContinuousLinearMap
  have hι : ContinuousLinearMap.adjoint ι ∘L ι = 1 := (WithLp.inlₗᵢ 2 ℂ K E).adjoint_comp_self
  let V : K ⊗̂ E →L[ℂ] K' ⊗̂ E := amplifyLeft ι
  have hVV : ContinuousLinearMap.adjoint V ∘L V = 1 := by
    rw [amplifyLeft_adjoint, ← amplifyLeft_comp, hι, amplifyLeft_one]
  have hcomm : ∀ B : E →L[ℂ] E, V ∘L amplifyRight B = amplifyRight B ∘L V := fun B =>
    amplifyLeft_comp_amplifyRight ι B
  -- `V` transports the representing vectors.
  have htransport : ∀ (ζ : K ⊗̂ E) (A : Matrix n n ℂ),
      ⟪V ζ, amplifyRight (Matrix.toEuclideanCLM (𝕜 := ℂ) A) (V ζ)⟫_ℂ =
        ⟪ζ, amplifyRight (Matrix.toEuclideanCLM (𝕜 := ℂ) A) ζ⟫_ℂ := fun ζ A => by
    rw [← ContinuousLinearMap.comp_apply (amplifyRight _) V, ← hcomm,
      ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_inner_left,
      ← ContinuousLinearMap.comp_apply (ContinuousLinearMap.adjoint V) V, hVV,
      one_apply_eq_self]
  -- `V` intertwines `1 ⊗ B(ℂⁿ)` and `B(K) ⊗ 1`.
  have hM : ∀ x ∈ 𝓜, ∃ y ∈ VonNeumannAlgebra.amplify K' 𝓑(E),
      y ∘L V = V ∘L x ∧ star y ∘L V = V ∘L star x := by
    intro x hx
    obtain ⟨B, -, rfl⟩ := (mem_amplify_iff (H₁ := K)).mp hx
    refine ⟨amplifyRight B, amplifyRight_mem_amplify (mem_boundedLinearOperators B),
      (hcomm B).symm, ?_⟩
    rw [HilbertTensor.amplifyRight_star, HilbertTensor.amplifyRight_star]
    exact (hcomm _).symm
  have hM' : ∀ x ∈ (𝓜)′, ∃ y ∈ (VonNeumannAlgebra.amplify K' 𝓑(E))′,
      y ∘L V = V ∘L x ∧ star y ∘L V = V ∘L star x := by
    intro x hx
    rw [amplify_boundedLinearOperators, HilbertTensor.vnTensorRight_commutant] at hx
    obtain ⟨B, rfl⟩ := HilbertTensor.exists_amplifyLeft_of_mem_vnTensorLeft hx
    have key : ∀ C : K →L[ℂ] K,
        amplifyLeft (H₂ := E) (ι ∘L C ∘L ContinuousLinearMap.adjoint ι) ∘L V = V ∘L amplifyLeft C :=
      fun C => by
        rw [← amplifyLeft_comp, ← amplifyLeft_comp, ContinuousLinearMap.comp_assoc,
          ContinuousLinearMap.comp_assoc, hι, ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]
    refine ⟨amplifyLeft (ι ∘L B ∘L ContinuousLinearMap.adjoint ι),
      amplifyLeft_mem_commutant_amplify _, key B, ?_⟩
    rw [HilbertTensor.amplifyLeft_star, HilbertTensor.amplifyLeft_star,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc]
    exact key _
  have hV : ContinuousLinearMap.adjoint V (V ξ) = ξ := by
    rw [← ContinuousLinearMap.comp_apply, hVV, one_apply_eq_self]
  rw [← arakiVec_of_intertwiner (𝓜) ξ η hM hM' hV]
  -- The purifications along the standard basis of `ℂⁿ ⊆ K'`.
  let g' : n → K' := fun i => WithLp.inrₗᵢ 2 ℂ K E (EuclideanSpace.basisFun n ℂ i)
  have hg' : Orthonormal ℂ g' :=
    (EuclideanSpace.basisFun n ℂ).orthonormal.comp_linearIsometry (WithLp.inrₗᵢ 2 ℂ K E)
  exact arakiVec_eq_umegakiEntropy_of_orthonormal hρ hσ hg' (fun A => (htransport ξ A).trans (hξ A))
    (fun A => (htransport η A).trans (hη A))

include hρ hσ in
/-- **Araki = Umegaki, for any representing functionals.** If the normal functionals `ψ, φ` on
`B(ℂⁿ)` are `A ↦ Tr (ρ A)` and `A ↦ Tr (σ A)`, then `S(ψ ‖ φ) = D(ρ ‖ σ)`. -/
theorem arakiEntropy_eq_umegakiEntropy {ψ φ : 𝓑(EuclideanSpace ℂ n).NormalFunctional}
    (hψ : ∀ A : Matrix n n ℂ, ψ.1 A.toBoundedLinearOperators = Tr (ρ * A))
    (hφ : ∀ A : Matrix n n ℂ, φ.1 A.toBoundedLinearOperators = Tr (σ * A)) :
    S⟦ψ ∥ φ⟧ = D(ρ ∥ σ) := by
  rw [hρ.eq_normalFunctional_of_apply hψ, hσ.eq_normalFunctional_of_apply hφ,
    Matrix.umegakiEntropy_def hρ hσ]

end VonNeumannAlgebra

namespace Matrix

open scoped MatrixOrder ComplexOrder QuantumInfo

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-! ### Klein's inequality and faithfulness -/

variable {ρ σ : Matrix n n ℂ}

/-- **Klein's inequality**: `0 ≤ D(ρ ‖ σ)` for positive semidefinite `ρ, σ` with
`Tr σ ≤ Tr ρ`, in particular for two density matrices (`DensityMatrix.umegakiEntropy_nonneg`).
This is Araki's positivity `VonNeumannAlgebra.arakiEntropy_nonneg`. -/
theorem umegakiEntropy_nonneg (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (h : (Tr σ).re ≤ (Tr ρ).re) : 0 ≤ D(ρ ∥ σ) := by
  rw [umegakiEntropy_def hρ hσ]
  exact VonNeumannAlgebra.arakiEntropy_nonneg
    (by rw [hσ.normalFunctional_apply_one, hρ.normalFunctional_apply_one]; exact h)

/-- **Faithfulness**: for positive semidefinite `ρ, σ` of equal trace, `D(ρ ‖ σ) = 0` iff `ρ = σ`.
The trace condition cannot be dropped: for the projection `ρ = diag(1, 0)` and `σ = 1` on `ℂ²`,
`D(ρ ‖ σ) = Tr ρ log ρ - Tr ρ log 1 = 0` although `ρ ≠ σ`.

This is a consequence of Klein's inequality plus the strict convexity of x ↦ x log x.
Note: D(ρ‖σ) = ⊤ ≠ 0 when supp(ρ) ⊄ supp(σ). -/
theorem umegakiEntropy_eq_zero_iff (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (htr : ρ.trace = σ.trace) : D(ρ ∥ σ) = 0 ↔ ρ = σ := by
  have hsum : ∑ i, hρ.1.eigenvalues i = ∑ i, hσ.1.eigenvalues i := by
    have h1 := hρ.1.trace_eq_sum_eigenvalues
    rw [htr, hσ.1.trace_eq_sum_eigenvalues] at h1
    exact_mod_cast h1.symm
  constructor
  · -- → direction: D(ρ‖σ) = 0 → ρ = σ
    intro hD
    -- First: D = ⊤ would give ⊤ = 0, contradiction, so we must be in the SuppSubset case.
    by_cases h : SuppSubset ρ σ
    · rw [umegakiEntropy_of_suppSubset hρ hσ h, EReal.coe_eq_zero] at hD
      change (ρ * (cfc Real.log ρ - cfc Real.log σ)).trace.re = 0 at hD
      -- Extract eigenvalue data
      set V := (hσ.1.eigenvectorUnitary : Matrix n n ℂ) with hV_def
      set U := (hρ.1.eigenvectorUnitary : Matrix n n ℂ) with hU_def
      set W := eigW hρ.1 hσ.1 with hW_def
      set ev_ρ := hρ.1.eigenvalues
      set ev_σ := hσ.1.eigenvalues
      have hVW : V * W = U := by
        simp only [W, eigW]
        rw [← Matrix.mul_assoc, UUH_eq_one _ hσ.1, Matrix.one_mul]
      have hWW : W * Wᴴ = 1 := eigW_mul_conjTranspose_eigW hρ.1 hσ.1
      have hVVH : V * Vᴴ = 1 := UUH_eq_one _ hσ.1
      -- D expressed as eigenvalue sum
      have hD_sum : ∑ i : n, ∑ j : n, Complex.normSq (W j i) *
          (ev_ρ i * Real.log (ev_ρ i) - ev_ρ i * Real.log (ev_σ j)) = 0 := by
        rw [Matrix.mul_sub, trace_sub, Complex.sub_re] at hD
        rw [re_trace_mul_log_self_eq hρ.1, re_trace_mul_log_eq hρ.1 hσ.1] at hD
        rw [show ∑ i, ev_ρ i * Real.log (ev_ρ i) =
                ∑ i : n, ∑ j : n, Complex.normSq (W j i) * ev_ρ i * Real.log (ev_ρ i) by
              congr 1; ext i
              rw [← Finset.sum_mul, ← Finset.sum_mul, sum_normSq_eigW_col hρ.1 hσ.1, one_mul]] at hD
        linarith [show ∑ i : n, ∑ j : n, Complex.normSq (W j i) * ev_ρ i * Real.log (ev_ρ i) -
                      ∑ i : n, ∑ j : n, Complex.normSq (W j i) * ev_ρ i * Real.log (ev_σ j) =
                      ∑ i : n, ∑ j : n, Complex.normSq (W j i) *
                        (ev_ρ i * Real.log (ev_ρ i) - ev_ρ i * Real.log (ev_σ j)) by
                  simp only [← Finset.sum_sub_distrib]; congr 1; ext i; congr 1; ext j; ring]
      -- KL form: D = Σᵢⱼ |Wji|² ev_σⱼ klFun(ev_ρᵢ/ev_σⱼ)
      have hklform : ∑ i : n, ∑ j : n,
          Complex.normSq (W j i) * ev_σ j * InformationTheory.klFun (ev_ρ i / ev_σ j) = 0 := by
        have hD_eq : ∑ i : n, ∑ j : n, Complex.normSq (W j i) *
            (ev_ρ i * Real.log (ev_ρ i) - ev_ρ i * Real.log (ev_σ j)) =
            ∑ i : n, ∑ j : n,
              (Complex.normSq (W j i) * ev_σ j * InformationTheory.klFun (ev_ρ i / ev_σ j) +
               Complex.normSq (W j i) * (ev_ρ i - ev_σ j)) := by
          congr 1; ext i; congr 1; ext j
          unfold InformationTheory.klFun
          rcases (hσ.eigenvalues_nonneg j).lt_or_eq with hμpos | hμzero
          · rcases (hρ.eigenvalues_nonneg i).lt_or_eq with hevρpos | hevρzero
            · have hevρne : ev_ρ i ≠ 0 := ne_of_gt hevρpos
              have hevσne : ev_σ j ≠ 0 := ne_of_gt hμpos
              field_simp; rw [Real.log_div hevρne hevσne]; ring
            · have hev_ρ_zero : ev_ρ i = 0 := hevρzero.symm
              simp [hev_ρ_zero, Real.log_zero]
          · have hsupp' := normSq_eigW_mul_eigenvalues_eq_zero_of_suppSubset hρ.1 hσ.1 h j hμzero.symm i
            rcases mul_eq_zero.mp hsupp' with hw0 | hev0
            · have hW0 : Complex.normSq (W j i) = 0 := hw0
              simp [hW0]
            · have hev0' : ev_ρ i = 0 := by exact_mod_cast hev0
              simp [hev0', Real.log_zero]
        rw [hD_eq] at hD_sum
        simp_rw [Finset.sum_add_distrib] at hD_sum
        have hzero : ∑ i : n, ∑ j : n, Complex.normSq (W j i) * (ev_ρ i - ev_σ j) = 0 := by
          simp only [mul_sub, Finset.sum_sub_distrib]
          rw [show ∑ i : n, ∑ j : n, Complex.normSq (W j i) * ev_ρ i = ∑ i : n, ev_ρ i by
                congr 1; ext i; rw [← Finset.sum_mul, sum_normSq_eigW_col hρ.1 hσ.1, one_mul],
              show ∑ i : n, ∑ j : n, Complex.normSq (W j i) * ev_σ j = ∑ j : n, ev_σ j by
                rw [Finset.sum_comm]; congr 1; ext j; rw [← Finset.sum_mul, sum_normSq_eigW_row hρ.1 hσ.1, one_mul]]
          linarith [hsum]
        linarith
      -- Each KL term = 0
      have hterms : ∀ (i j : n),
          Complex.normSq (W j i) * ev_σ j * InformationTheory.klFun (ev_ρ i / ev_σ j) = 0 := by
        have hterm_nn : ∀ (i j : n),
            0 ≤ Complex.normSq (W j i) * ev_σ j * InformationTheory.klFun (ev_ρ i / ev_σ j) :=
          fun i j => mul_nonneg (mul_nonneg (Complex.normSq_nonneg _)
            (hσ.eigenvalues_nonneg j))
            (InformationTheory.klFun_nonneg (div_nonneg (hρ.eigenvalues_nonneg i)
              (hσ.eigenvalues_nonneg j)))
        have hnn_sum : ∀ (i : n), 0 ≤ ∑ j : n,
            Complex.normSq (W j i) * ev_σ j * InformationTheory.klFun (ev_ρ i / ev_σ j) :=
          fun i => Finset.sum_nonneg fun j _ => hterm_nn i j
        intro i j
        have houter := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnn_sum i)).mp
          hklform i (Finset.mem_univ _)
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hterm_nn i j)).mp
          houter j (Finset.mem_univ _)
      -- Derive normSq(Wji) * (ev_ρᵢ - ev_σⱼ) = 0
      have hterm_diff : ∀ (i j : n), Complex.normSq (W j i) * (ev_ρ i - ev_σ j) = 0 := by
        intro i j
        rcases (hσ.eigenvalues_nonneg j).lt_or_eq with hμpos | hμzero
        · rcases mul_eq_zero.mp (hterms i j) with h1 | h2
          · rcases mul_eq_zero.mp h1 with h3 | h4
            · rw [h3, zero_mul]
            · exact absurd h4 (ne_of_gt hμpos)
          · have hkl := (InformationTheory.klFun_eq_zero_iff
                (div_nonneg (hρ.eigenvalues_nonneg i) (hσ.eigenvalues_nonneg j))).mp h2
            have hev_eq : ev_ρ i = ev_σ j := by
              have := div_eq_one_iff_eq (ne_of_gt hμpos) |>.mp hkl
              exact_mod_cast this
            rw [hev_eq, sub_self, mul_zero]
        · have hev_zero : ev_σ j = 0 := hμzero.symm
          rw [hev_zero, sub_zero]
          exact normSq_eigW_mul_eigenvalues_eq_zero_of_suppSubset hρ.1 hσ.1 h j hμzero.symm i
      -- Derive W_{ji} * ev_ρᵢ = W_{ji} * ev_σⱼ
      have hstep : ∀ (i j : n), W j i * (ev_ρ i : ℂ) = W j i * (ev_σ j : ℂ) := fun i j => by
        rcases mul_eq_zero.mp (hterm_diff i j) with h1 | h2
        · rw [Complex.normSq_eq_zero] at h1; simp [h1]
        · congr 1; exact_mod_cast sub_eq_zero.mp h2
      -- W * diag(ev_ρ) = diag(ev_σ) * W
      have hcommute : W * diagonal (fun i => (ev_ρ i : ℂ)) = diagonal (fun j => (ev_σ j : ℂ)) * W := by
        ext j i
        simp only [mul_apply, diagonal_apply, ite_mul, zero_mul, mul_ite, mul_zero]
        rw [Finset.sum_ite_eq', Finset.sum_ite_eq]
        simp only [Finset.mem_univ, ite_true]
        calc W j i * (ev_ρ i : ℂ) = W j i * (ev_σ j : ℂ) := hstep i j
          _ = (ev_σ j : ℂ) * W j i := by ring
      -- W * diag(ev_ρ) * W† = diag(ev_σ)
      have hWdiag : W * diagonal (fun i => (ev_ρ i : ℂ)) * Wᴴ = diagonal (fun j => (ev_σ j : ℂ)) := by
        calc W * diagonal (fun i => (ev_ρ i : ℂ)) * Wᴴ
            = diagonal (fun j => (ev_σ j : ℂ)) * W * Wᴴ := by rw [hcommute]
          _ = diagonal (fun j => (ev_σ j : ℂ)) * (W * Wᴴ) := by rw [Matrix.mul_assoc]
          _ = diagonal (fun j => (ev_σ j : ℂ)) := by rw [hWW, Matrix.mul_one]
      -- ρ = U diag(ev_ρ) Uᴴ
      have hρ_spec : ρ = U * diagonal (fun i => (ev_ρ i : ℂ)) * Uᴴ :=
        spectral_expand ρ hρ.1
      -- σ = V diag(ev_σ) Vᴴ
      have hσ_spec : σ = V * diagonal (fun j => (ev_σ j : ℂ)) * Vᴴ :=
        spectral_expand σ hσ.1
      -- ρ = σ via: U diag(ev_ρ) Uᴴ = VW diag(ev_ρ)Wᴴ Vᴴ = V diag(ev_σ) Vᴴ
      rw [hρ_spec, hσ_spec, ← hVW, conjTranspose_mul]
      calc V * W * diagonal (fun i => (ev_ρ i : ℂ)) * (Wᴴ * Vᴴ)
          = V * (W * diagonal (fun i => (ev_ρ i : ℂ)) * Wᴴ) * Vᴴ := by
            simp only [Matrix.mul_assoc]
        _ = V * diagonal (fun j => (ev_σ j : ℂ)) * Vᴴ := by rw [hWdiag]
    · -- h : ¬ SuppSubset ρ σ, so D(ρ‖σ) = ⊤ ≠ 0, contradiction
      rw [umegakiEntropy_of_not_suppSubset hρ hσ h] at hD
      exact absurd hD EReal.top_ne_zero
  · -- ← direction: ρ = σ → D(ρ‖σ) = 0
    intro h
    subst h
    rw [umegakiEntropy_of_suppSubset hρ hρ fun _ h => h]
    rw [sub_self, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re, EReal.coe_zero]

end Matrix

namespace DensityMatrix

open Matrix
open scoped Matrix.QuantumInfo

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Klein's inequality** for density matrices: `0 ≤ D(ρ ‖ σ)`. -/
theorem umegakiEntropy_nonneg (ρ σ : DensityMatrix n) : 0 ≤ D(ρ.toMatrix ∥ σ.toMatrix) :=
  Matrix.umegakiEntropy_nonneg ρ.posSemidef σ.posSemidef (by rw [ρ.trace_eq_one, σ.trace_eq_one])

/-- **Faithfulness** for density matrices: `D(ρ ‖ σ) = 0 ↔ ρ = σ`. -/
theorem umegakiEntropy_eq_zero_iff (ρ σ : DensityMatrix n) :
    D(ρ.toMatrix ∥ σ.toMatrix) = 0 ↔ ρ = σ := by
  rw [Matrix.umegakiEntropy_eq_zero_iff ρ.posSemidef σ.posSemidef
    (by rw [ρ.trace_eq_one, σ.trace_eq_one])]
  exact ⟨DensityMatrix.ext, fun h => h ▸ rfl⟩

end DensityMatrix

namespace Matrix

open scoped MatrixOrder ComplexOrder QuantumInfo

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-! ### The derivative of `Tr ρˢ σ¹⁻ˢ` at `s = 1`

For positive semidefinite `ρ, σ` with `supp ρ ⊆ supp σ`, `s ↦ Tr ρˢ σ¹⁻ˢ` has derivative
`Tr ρ (log ρ - log σ)` at `s = 1` (`hasDerivAt_trace_rpow_mul`). Joint convexity of `D` follows
from this and Lieb's concavity theorem for `Tr ρˢ σ¹⁻ˢ`. -/

/-- Tr (ρˢ σ¹⁻ˢ) equals a double sum over eigenvalues via the
change-of-basis unitary W = U_σ† U_ρ:
  Tr (ρˢ σ¹⁻ˢ) = ∑_{i,j} |W_{ji}|² λᵢˢ μⱼ¹⁻ˢ -/
private lemma trace_rpow_mul_double_sum {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef)
    (hσ : σ.PosSemidef) (s : ℝ) :
    (Tr (ρ ^ s * σ ^ (1 - s))).re =
    ∑ i : n, ∑ j : n,
      Complex.normSq (eigW hρ.1 hσ.1 j i) *
      hρ.1.eigenvalues i ^ s *
      hσ.1.eigenvalues j ^ (1 - s) := by
  set U := (hρ.1.eigenvectorUnitary : Matrix n n ℂ)
  set V := (hσ.1.eigenvectorUnitary : Matrix n n ℂ)
  set W := eigW hρ.1 hσ.1
  set ev_ρ := hρ.1.eigenvalues
  set ev_σ := hσ.1.eigenvalues
  have hpsdρ := hρ
  have hpsdσ := hσ
  have hρs : ρ ^ s = U * diagonal (fun i => ((ev_ρ i ^ s : ℝ) : ℂ)) * Uᴴ := by
    rw [CFC.rpow_eq_cfc_real (a := ρ) (ha := by rw [Matrix.le_iff, sub_zero]; exact hpsdρ),
      cfc_spectral_eq hρ.1 (fun x => x ^ s)]
  have hσs : σ ^ (1 - s) = V * diagonal (fun j => ((ev_σ j ^ (1 - s) : ℝ) : ℂ)) * Vᴴ := by
    rw [CFC.rpow_eq_cfc_real (a := σ) (ha := by rw [Matrix.le_iff, sub_zero]; exact hpsdσ),
      cfc_spectral_eq hσ.1 (fun x => x ^ (1 - s))]
  have hVU : Vᴴ * U = W := rfl
  rw [hρs, hσs]
  -- Use cyclic trace property and W = Vᴴ * U to reduce to W D_ρ Wᴴ D_σ
  have hWH : Wᴴ = Uᴴ * V := by rw [← hVU, conjTranspose_mul, conjTranspose_conjTranspose]
  have htrace : (U * diagonal (fun i => ((ev_ρ i ^ s : ℝ) : ℂ)) * Uᴴ *
                 (V * diagonal (fun j => ((ev_σ j ^ (1 - s) : ℝ) : ℂ)) * Vᴴ)).trace =
                (W * diagonal (fun i => ((ev_ρ i ^ s : ℝ) : ℂ)) * Wᴴ *
                 diagonal (fun j => ((ev_σ j ^ (1 - s) : ℝ) : ℂ))).trace := by
    set D1 := diagonal (fun i => ((ev_ρ i ^ s : ℝ) : ℂ))
    set D2 := diagonal (fun j => ((ev_σ j ^ (1 - s) : ℝ) : ℂ))
    -- Cyclic permutation: Tr (U D1 Uᴴ V D2 Vᴴ) = Tr (Vᴴ U D1 Uᴴ V D2)
    rw [show U * D1 * Uᴴ * (V * D2 * Vᴴ) =
        (U * D1 * Uᴴ * V * D2) * Vᴴ from by
      simp [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm]
    rw [show Vᴴ * (U * D1 * Uᴴ * V * D2) = W * D1 * Wᴴ * D2 from by
      rw [show Vᴴ * (U * D1 * Uᴴ * V * D2) = (Vᴴ * U) * D1 * (Uᴴ * V) * D2 from by
        simp [Matrix.mul_assoc]]
      rw [hVU, ← hWH]]
  rw [htrace]
  -- Expand trace elementwise and reduce diagonal selections
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply, diagonal_apply,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Complex.star_def, Complex.normSq_apply, Complex.re_sum, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

omit [DecidableEq n] in
/-- HasDerivAt for the double sum ∑_{i,j} w_{ij} λᵢˢ μⱼ¹⁻ˢ at s=1. -/
private lemma hasDerivAt_double_rpow_sum
    (w : n → n → ℝ)
    (ev1 ev2 : n → ℝ) (hev1 : ∀ i, 0 ≤ ev1 i) (hev2 : ∀ j, 0 ≤ ev2 j)
    (hsupp : ∀ j i, ev2 j = 0 → w i j * ev1 i = 0) :
    HasDerivAt (fun s : ℝ => ∑ i : n, ∑ j : n, w i j * ev1 i ^ s * ev2 j ^ (1 - s))
      (∑ i : n, ∑ j : n, w i j * ev1 i * (Real.log (ev1 i) - Real.log (ev2 j))) 1 := by
  have inner : ∀ i : n, ∀ j : n, HasDerivAt
        (fun s : ℝ => w i j * ev1 i ^ s * ev2 j ^ (1 - s))
        (w i j * ev1 i * (Real.log (ev1 i) - Real.log (ev2 j))) 1 := by
    intro i j
    rcases (hev1 i).lt_or_eq with hev1pos | hev1zero
    · rcases (hev2 j).lt_or_eq with hev2pos | hev2zero
      · have hd1 : HasDerivAt (fun s : ℝ => ev1 i ^ s) (ev1 i * Real.log (ev1 i)) 1 := by
          have := (hasDerivAt_id (𝕜 := ℝ) 1).mul_const (Real.log (ev1 i)) |>.exp
          simp only [id] at this
          have heq : (fun x => Real.exp (x * Real.log (ev1 i))) = (fun x => ev1 i ^ x) := by
            ext x; rw [Real.rpow_def_of_pos hev1pos, mul_comm]
          rw [heq] at this
          convert this using 1
          rw [one_mul, Real.exp_log hev1pos]
        have hd2 : HasDerivAt (fun s : ℝ => ev2 j ^ (1 - s)) (-(Real.log (ev2 j))) 1 := by
          have := ((hasDerivAt_const (𝕜 := ℝ) 1 (Real.log (ev2 j))).sub
              ((hasDerivAt_id (𝕜 := ℝ) 1).mul_const (Real.log (ev2 j)))).exp
          simp only [id, Pi.sub_apply] at this
          have heq : (fun x => Real.exp (Real.log (ev2 j) - x * Real.log (ev2 j))) =
                     (fun x => ev2 j ^ (1 - x)) := by
            ext x; rw [Real.rpow_def_of_pos hev2pos]; ring_nf
          rw [heq] at this
          convert this using 1
          simp only [one_mul, sub_self, Real.exp_zero, zero_sub]
        have h12 := HasDerivAt.mul hd1 hd2
        have h12c := h12.const_mul (w i j)
        simp only [Pi.mul_apply] at h12c
        convert h12c using 1
        · funext s; ring
        · simp only [Real.rpow_one, sub_self, Real.rpow_zero]; ring
      · rcases mul_eq_zero.mp (hsupp j i hev2zero.symm) with hw0 | hev10
        · simp only [hw0, zero_mul]; exact hasDerivAt_const _ _
        · linarith
    · simp only [← hev1zero, mul_zero, zero_mul]
      apply (hasDerivAt_const (𝕜 := ℝ) (1:ℝ) (0:ℝ)).congr_of_eventuallyEq
      apply Filter.eventually_of_mem (Ioi_mem_nhds (show (0:ℝ) < 1 from by norm_num))
      intro s hs
      simp only [Set.mem_Ioi] at hs
      simp only [Real.zero_rpow (ne_of_gt hs), mul_zero, zero_mul]
  have outer : ∀ i : n, HasDerivAt
        (fun s : ℝ => ∑ j : n, w i j * ev1 i ^ s * ev2 j ^ (1 - s))
        (∑ j : n, w i j * ev1 i * (Real.log (ev1 i) - Real.log (ev2 j))) 1 := by
    intro i
    have h := HasDerivAt.sum (u := Finset.univ) (fun j (_ : j ∈ Finset.univ) => inner i j)
    have heq : (∑ j ∈ Finset.univ, fun s : ℝ => w i j * ev1 i ^ s * ev2 j ^ (1 - s)) =
               (fun s : ℝ => ∑ j : n, w i j * ev1 i ^ s * ev2 j ^ (1 - s)) :=
      funext (fun s => Finset.sum_apply _ _ _)
    rwa [heq] at h
  have h_final := HasDerivAt.sum (u := Finset.univ) (fun i (_ : i ∈ Finset.univ) => outer i)
  have heq : (∑ i ∈ Finset.univ, fun s : ℝ => ∑ j : n, w i j * ev1 i ^ s * ev2 j ^ (1 - s)) =
             (fun s : ℝ => ∑ i : n, ∑ j : n, w i j * ev1 i ^ s * ev2 j ^ (1 - s)) :=
    funext (fun s => Finset.sum_apply _ _ _)
  rwa [heq] at h_final

/-- HasDerivAt of Re[Tr (ρˢ σ¹⁻ˢ)] at s=1 equals D(ρ ‖ σ).

When supp(ρ) ⊆ supp(σ):
  (d/ds)|_{s=1} Tr (ρˢ σ¹⁻ˢ) = Tr (ρ(log ρ − log σ)) = D(ρ ‖ σ) -/
private lemma hasDerivAt_trace_rpow_mul {ρ σ : Matrix n n ℂ} (hρ : ρ.PosSemidef)
    (hσ : σ.PosSemidef) (h : SuppSubset ρ σ) :
    HasDerivAt (fun s : ℝ => (Tr (ρ ^ s * σ ^ (1 - s))).re)
      ((Tr (ρ * (cfc Real.log ρ - cfc Real.log σ))).re) 1 := by
  set ev_ρ := hρ.1.eigenvalues
  set ev_σ := hσ.1.eigenvalues
  set W := eigW hρ.1 hσ.1
  have hconv : (fun s : ℝ => (ρ ^ s * σ ^ (1 - s)).trace.re) = fun s =>
      ∑ i : n, ∑ j : n, Complex.normSq (W j i) * ev_ρ i ^ s * ev_σ j ^ (1 - s) :=
    funext (trace_rpow_mul_double_sum hρ hσ)
  rw [hconv]
  have hderiv := hasDerivAt_double_rpow_sum
    (fun i j => Complex.normSq (W j i))
    ev_ρ ev_σ hρ.eigenvalues_nonneg hσ.eigenvalues_nonneg
    (fun j i hμ => by
      have := normSq_eigW_mul_eigenvalues_eq_zero_of_suppSubset hρ.1 hσ.1 h j hμ i
      linarith [mul_nonneg (Complex.normSq_nonneg (W j i)) (hρ.eigenvalues_nonneg i)])
  convert hderiv using 1
  -- Relate derivative to D(ρ‖σ) = Tr (ρ(log ρ)) - Tr (ρ(log σ))
  rw [Matrix.mul_sub, trace_sub, Complex.sub_re, re_trace_mul_log_self_eq hρ.1, re_trace_mul_log_eq hρ.1 hσ.1]
  -- Rewrite Σᵢ evᵢ log evᵢ as Σᵢⱼ |Wji|² evᵢ log evᵢ (using column sum = 1)
  have h1 : ∑ i : n, ev_ρ i * Real.log (ev_ρ i) =
            ∑ i : n, ∑ j : n, Complex.normSq (W j i) * ev_ρ i * Real.log (ev_ρ i) := by
    congr 1; ext i
    rw [← Finset.sum_mul, ← Finset.sum_mul,
        show ∑ j : n, Complex.normSq (W j i) = 1 from sum_normSq_eigW_col hρ.1 hσ.1 i]
    ring
  rw [h1, ← Finset.sum_sub_distrib]; congr 1; ext i
  rw [← Finset.sum_sub_distrib]; congr 1; ext j; ring

/-! ### Monotonicity -/

/-- **Monotonicity of Umegaki's relative entropy** (data-processing inequality, Lindblad–Uhlmann):
for a quantum channel `Φ` and positive semidefinite `ρ, σ`, `D(Φ(ρ) ‖ Φ(σ)) ≤ D(ρ ‖ σ)`.

This is Uhlmann's monotonicity theorem for Araki's relative entropy
(`VonNeumannAlgebra.arakiEntropy_comp_le`) applied to the dual channel `Φ*`, a unital normal
Schwarz map (`Matrix.QuantumChannel.dualSchwarzMap`) that pulls `ω_ρ` back to `ω_{Φ(ρ)}`:
`Tr (ρ Φ*(B)) = Tr (Φ(ρ) B)` (`Matrix.trace_mul_traceDual`). -/
theorem umegakiEntropy_channel_le (Φ : QuantumChannel n m) {ρ σ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) : D(Φ.val ρ ∥ Φ.val σ) ≤ D(ρ ∥ σ) := by
  have hα := QuantumChannel.isNormalMap_dualSchwarzMap Φ
  have key : ∀ {τ : Matrix n n ℂ} (hτ : τ.PosSemidef),
      (Φ.2.completelyPositive.posSemidef_map hτ).normalFunctional =
        hτ.normalFunctional.comp (QuantumChannel.dualSchwarzMap Φ) hα := fun {τ} hτ =>
    ((Φ.2.completelyPositive.posSemidef_map hτ).eq_normalFunctional_of_apply fun B => by
      rw [VonNeumannAlgebra.NormalFunctional.comp_apply, QuantumChannel.dualSchwarzMap_apply,
        hτ.normalFunctional_apply, trace_mul_traceDual]).symm
  rw [umegakiEntropy_def (Φ.2.completelyPositive.posSemidef_map hρ)
      (Φ.2.completelyPositive.posSemidef_map hσ), umegakiEntropy_def hρ hσ, key hρ, key hσ]
  exact VonNeumannAlgebra.arakiEntropy_comp_le _ (QuantumChannel.dualSchwarzMap_one Φ) hα _ _

/-! ### Equality under recoverable channels -/

/-- **Sufficiency of recovery for equality in DPI.**

If a quantum channel R recovers both ρ and σ from Φ, i.e.,
  R(Φ(ρ)) = ρ and R(Φ(σ)) = σ,
then equality holds in the data-processing inequality:
  D(Φ(ρ) ‖ Φ(σ)) = D(ρ ‖ σ).

**Proof.** Applying DPI to Φ gives D(Φ(ρ)‖Φ(σ)) ≤ D(ρ‖σ).
For the reverse, applying DPI to R and using the recovery conditions gives
D(ρ‖σ) = D(R(Φ(ρ))‖R(Φ(σ))) ≤ D(Φ(ρ)‖Φ(σ)).
-/
theorem umegakiEntropy_channel_eq_of_recoverable (Φ : QuantumChannel n m) {ρ σ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (R : QuantumChannel m n)
    (hRρ : R.val (Φ.val ρ) = ρ) (hRσ : R.val (Φ.val σ) = σ) :
    D(Φ.val ρ ∥ Φ.val σ) = D(ρ ∥ σ) := by
  refine le_antisymm (umegakiEntropy_channel_le Φ hρ hσ) ?_
  have hle := umegakiEntropy_channel_le R (Φ.2.completelyPositive.posSemidef_map hρ)
    (Φ.2.completelyPositive.posSemidef_map hσ)
  rwa [hRρ, hRσ] at hle

/-! ### Joint Convexity of Relative Entropy -/

omit [DecidableEq n] in
/-- The support subset condition is preserved under convex combinations of positive semidefinite pairs.
If supp(Aᵢ) ⊆ supp(Bᵢ) for i=1,2 and p, 1−p ≥ 0, then
supp(p A₁ + (1−p) A₂) ⊆ supp(p B₁ + (1−p) B₂). -/
private lemma suppSubset_mix
    {A₁ A₂ B₁ B₂ : Matrix n n ℂ}
    (hB₁ : B₁.PosSemidef) (hB₂ : B₂.PosSemidef)
    (hsup₁ : SuppSubset A₁ B₁) (hsup₂ : SuppSubset A₂ B₂)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : 0 ≤ 1 - p) :
    SuppSubset (p • A₁ + (1 - p) • A₂) (p • B₁ + (1 - p) • B₂) := by
  intro v hv
  rw [Matrix.add_mulVec, show (p • B₁) *ᵥ v = p • B₁ *ᵥ v from Matrix.smul_mulVec _ _ _,
      show ((1 - p) • B₂) *ᵥ v = (1 - p) • B₂ *ᵥ v from Matrix.smul_mulVec _ _ _] at hv
  have h₁ : 0 ≤ (star v ⬝ᵥ B₁.mulVec v).re := hB₁.re_dotProduct_nonneg v
  have h₂ : 0 ≤ (star v ⬝ᵥ B₂.mulVec v).re := hB₂.re_dotProduct_nonneg v
  have hinner_sum : p * (star v ⬝ᵥ B₁.mulVec v).re + (1 - p) * (star v ⬝ᵥ B₂.mulVec v).re = 0 := by
    have hsmul₁ : star v ⬝ᵥ p • B₁.mulVec v = p • (star v ⬝ᵥ B₁.mulVec v) :=
      dotProduct_smul p (star v) (B₁.mulVec v)
    have hsmul₂ : star v ⬝ᵥ (1 - p) • B₂.mulVec v = (1 - p) • (star v ⬝ᵥ B₂.mulVec v) :=
      dotProduct_smul (1 - p) (star v) (B₂.mulVec v)
    have h : p * (star v ⬝ᵥ B₁.mulVec v).re + (1 - p) * (star v ⬝ᵥ B₂.mulVec v).re =
             (star v ⬝ᵥ (p • B₁.mulVec v + (1 - p) • B₂.mulVec v)).re := by
      rw [dotProduct_add, hsmul₁, hsmul₂]
      simp [Complex.real_smul, Complex.add_re, Complex.mul_re]
    rw [h, hv]; simp
  have hpB₁ : p * (star v ⬝ᵥ B₁.mulVec v).re = 0 := by
    nlinarith [mul_nonneg hp h₁, mul_nonneg hp1 h₂]
  have h1pB₂ : (1 - p) * (star v ⬝ᵥ B₂.mulVec v).re = 0 := by
    nlinarith [mul_nonneg hp h₁, mul_nonneg hp1 h₂]
  have hpA₁ : p • A₁.mulVec v = 0 := by
    rcases mul_eq_zero.mp hpB₁ with hp0 | h₁0
    · subst hp0; exact zero_smul ℝ _
    · rw [hsup₁ v (mulVec_eq_zero_of_re_inner_zero hB₁ v h₁0)]; exact smul_zero _
  have h1pA₂ : (1 - p) • A₂.mulVec v = 0 := by
    rcases mul_eq_zero.mp h1pB₂ with hp10 | h₂0
    · rw [hp10]; exact zero_smul ℝ _
    · rw [hsup₂ v (mulVec_eq_zero_of_re_inner_zero hB₂ v h₂0)]; exact smul_zero _
  rw [Matrix.add_mulVec, show (p • A₁) *ᵥ v = p • A₁ *ᵥ v from Matrix.smul_mulVec _ _ _,
      show ((1 - p) • A₂) *ᵥ v = (1 - p) • A₂ *ᵥ v from Matrix.smul_mulVec _ _ _,
      hpA₁, h1pA₂, add_zero]

/-- Joint concavity of Tr (ρˢ σ¹⁻ˢ) for positive semidefinite matrices.
  p ⋅ Tr (ρ₁ˢ σ₁¹⁻ˢ) + (1−p) ⋅ Tr (ρ₂ˢ σ₂¹⁻ˢ)
  ≤ Tr ((pρ₁ + (1−p)ρ₂)ˢ (pσ₁ + (1−p)σ₂)¹⁻ˢ) -/
private lemma trace_rpow_mul_jointly_concave {ρ₁ ρ₂ σ₁ σ₂ : Matrix n n ℂ}
    (hρ₁ : ρ₁.PosSemidef) (hρ₂ : ρ₂.PosSemidef) (hσ₁ : σ₁.PosSemidef) (hσ₂ : σ₂.PosSemidef)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    p * (Tr (ρ₁ ^ s * σ₁ ^ (1 - s))).re +
    (1 - p) * (Tr (ρ₂ ^ s * σ₂ ^ (1 - s))).re ≤
    (Tr ((p • ρ₁ + (1 - p) • ρ₂) ^ s * (p • σ₁ + (1 - p) • σ₂) ^ (1 - s))).re := by
  -- This is lieb_joint_concavity_general with K = 1 and exponents (s, 1 - s)
  have key := lieb_joint_concavity_general ρ₁ ρ₂ hρ₁ hρ₂ σ₁ σ₂ hσ₁ hσ₂
    (1 : Matrix n n ℂ) s (1 - s) hs0 (by linarith) (by linarith)
    p (1 - p) hp (by linarith) (by ring)
  simp only [conjTranspose_one, Matrix.mul_one] at key
  exact key

omit [Fintype n] [DecidableEq n] in
/-- A convex combination of positive semidefinite matrices is positive semidefinite. -/
private lemma posSemidef_mix {A₁ A₂ : Matrix n n ℂ} (h₁ : A₁.PosSemidef) (h₂ : A₂.PosSemidef)
    {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) : (p • A₁ + (1 - p) • A₂).PosSemidef := by
  have e : ∀ (c : ℝ) (A : Matrix n n ℂ), c • A = (c : ℂ) • A := fun c A => by
    ext i j; simp [Matrix.smul_apply, Complex.real_smul]
  rw [e, e]
  exact (h₁.smul (by exact_mod_cast hp)).add (h₂.smul (by exact_mod_cast sub_nonneg.mpr hp1))

/-- `D(ρ ‖ σ) ≠ -∞`, for all matrices. -/
theorem umegakiEntropy_ne_bot (ρ σ : Matrix n n ℂ) : D(ρ ∥ σ) ≠ ⊥ := by
  by_cases h : ρ.PosSemidef ∧ σ.PosSemidef
  · rw [umegakiEntropy_def h.1 h.2]
    exact VonNeumannAlgebra.arakiEntropy_ne_bot _ _
  · rw [umegakiEntropy_of_not_posSemidef h]
    exact EReal.zero_ne_bot

/-- `c · x ≠ -∞` for a finite `c > 0` and `x ≠ -∞`. -/
private lemma mul_ne_bot_of_pos {c x : EReal} (hc : 0 < c) (hct : c ≠ ⊤) (hx : x ≠ ⊥) :
    c * x ≠ ⊥ := by
  lift c to ℝ using ⟨hct, ne_bot_of_gt hc⟩
  induction x using EReal.rec with
  | bot => exact absurd rfl hx
  | coe x => exact_mod_cast EReal.coe_ne_bot (c * x)
  | top => rw [EReal.mul_top_of_pos hc]; exact top_ne_bot

/-- **Joint convexity**: for positive semidefinite `ρ₁, ρ₂, σ₁, σ₂` (of any trace) and
`0 ≤ p ≤ 1`, `D(p ρ₁ + (1 - p) ρ₂ ‖ p σ₁ + (1 - p) σ₂) ≤ p D(ρ₁ ‖ σ₁) + (1 - p) D(ρ₂ ‖ σ₂)`. -/
theorem umegakiEntropy_jointly_convex {ρ₁ ρ₂ σ₁ σ₂ : Matrix n n ℂ}
    (hρ₁ : ρ₁.PosSemidef) (hρ₂ : ρ₂.PosSemidef) (hσ₁ : σ₁.PosSemidef) (hσ₂ : σ₂.PosSemidef)
    {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    D(p • ρ₁ + (1 - p) • ρ₂ ∥ p • σ₁ + (1 - p) • σ₂) ≤
      p * D(ρ₁ ∥ σ₁) + (1 - p) * D(ρ₂ ∥ σ₂) := by
  -- Boundary cases `p = 0` and `p = 1`
  rcases hp.eq_or_lt' with rfl | hp0
  · simp
  rcases hp1.lt_or_eq with hp1' | rfl
  swap
  · have h1sub1 : (1 : EReal) - 1 = 0 :=
      EReal.sub_self (EReal.coe_ne_top 1) (EReal.coe_ne_bot 1)
    simp [h1sub1]
  have hq : 0 < 1 - p := by linarith
  have hq' : (0 : EReal) < 1 - p := by
    rw [show (1 : EReal) - p = ((1 - p : ℝ) : EReal) by norm_cast]; exact_mod_cast hq
  have hqt : (1 : EReal) - p ≠ ⊤ := by
    rw [show (1 : EReal) - p = ((1 - p : ℝ) : EReal) by norm_cast]; exact EReal.coe_ne_top _
  have hρmix := posSemidef_mix hρ₁ hρ₂ hp hp1
  have hσmix := posSemidef_mix hσ₁ hσ₂ hp hp1
  by_cases h₂ : SuppSubset ρ₂ σ₂
  swap
  · -- `D₂ = ⊤`: the right side is `⊤`
    rw [umegakiEntropy_of_not_suppSubset hρ₂ hσ₂ h₂, EReal.mul_top_of_pos hq',
      EReal.add_top_of_ne_bot (mul_ne_bot_of_pos (by exact_mod_cast hp0) (EReal.coe_ne_top p)
        (umegakiEntropy_ne_bot ρ₁ σ₁))]
    exact le_top
  by_cases h₁ : SuppSubset ρ₁ σ₁
  swap
  · -- `D₁ = ⊤`: the right side is `⊤`
    rw [umegakiEntropy_of_not_suppSubset hρ₁ hσ₁ h₁, EReal.mul_top_of_pos (by exact_mod_cast hp0),
      EReal.top_add_of_ne_bot (mul_ne_bot_of_pos hq' hqt (umegakiEntropy_ne_bot ρ₂ σ₂))]
    exact le_top
  -- Both finite: derivative argument
  have hsup_mix : SuppSubset (p • ρ₁ + (1 - p) • ρ₂) (p • σ₁ + (1 - p) • σ₂) :=
    suppSubset_mix hσ₁ hσ₂ h₁ h₂ p hp hq.le
  set ρm := p • ρ₁ + (1 - p) • ρ₂ with hρm
  set σm := p • σ₁ + (1 - p) • σ₂ with hσm
  set r₁ := (ρ₁ * (cfc Real.log ρ₁ - cfc Real.log σ₁)).trace.re
  set r₂ := (ρ₂ * (cfc Real.log ρ₂ - cfc Real.log σ₂)).trace.re
  rw [umegakiEntropy_of_suppSubset hρmix hσmix hsup_mix, umegakiEntropy_of_suppSubset hρ₁ hσ₁ h₁,
    umegakiEntropy_of_suppSubset hρ₂ hσ₂ h₂]
  rw [show (↑p : EReal) * ↑r₁ + (1 - ↑p) * ↑r₂ = ↑(p * r₁ + (1 - p) * r₂) from by
    push_cast; ring_nf, EReal.coe_le_coe_iff]
  -- `g(s) = Tr ρmˢ σm¹⁻ˢ - (p Tr ρ₁ˢ σ₁¹⁻ˢ + (1 - p) Tr ρ₂ˢ σ₂¹⁻ˢ)`
  let g : ℝ → ℝ := fun s =>
    (ρm ^ s * σm ^ (1 - s)).trace.re -
    (p * (ρ₁ ^ s * σ₁ ^ (1 - s)).trace.re + (1 - p) * (ρ₂ ^ s * σ₂ ^ (1 - s)).trace.re)
  -- (a) `g ≥ 0` on `(0, 1]` by Lieb's joint concavity
  have g_nonneg : ∀ s ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ g s := fun s hs => by
    have h := trace_rpow_mul_jointly_concave hρ₁ hρ₂ hσ₁ hσ₂ p hp hp1 s hs.1.le hs.2
    simp only [g]
    linarith
  -- (b) `g 1 = 0`, by linearity of the trace
  have hg_one : g 1 = 0 := by
    simp only [g]
    rw [show (1 : ℝ) - 1 = 0 from by ring,
      CFC.rpow_one _ (by rw [Matrix.le_iff, sub_zero]; exact hρmix),
      CFC.rpow_one _ (by rw [Matrix.le_iff, sub_zero]; exact hρ₁),
      CFC.rpow_one _ (by rw [Matrix.le_iff, sub_zero]; exact hρ₂),
      CFC.rpow_zero _ (by rw [Matrix.le_iff, sub_zero]; exact hσmix),
      CFC.rpow_zero _ (by rw [Matrix.le_iff, sub_zero]; exact hσ₁),
      CFC.rpow_zero _ (by rw [Matrix.le_iff, sub_zero]; exact hσ₂)]
    simp only [Matrix.mul_one, hρm, Matrix.trace_add, Matrix.trace_smul, Complex.add_re,
      Complex.real_smul, Complex.re_ofReal_mul]
    ring
  -- (c) the derivative of `g` at `1`
  have hderiv_g : HasDerivAt g
      ((ρm * (cfc Real.log ρm - cfc Real.log σm)).trace.re - (p * r₁ + (1 - p) * r₂)) 1 :=
    (hasDerivAt_trace_rpow_mul hρmix hσmix hsup_mix).sub
      ((hasDerivAt_trace_rpow_mul hρ₁ hσ₁ h₁).const_mul p |>.add
        ((hasDerivAt_trace_rpow_mul hρ₂ hσ₂ h₂).const_mul (1 - p)))
  -- (d) `g` has a minimum at `1` from the left, so `g'(1) ≤ 0`
  have hmin : ∀ y ∈ Set.Ioo (1 - (1:ℝ)/2) 1, g 1 ≤ g y := by
    intro y hy; rw [hg_one]; exact g_nonneg y ⟨by linarith [hy.1], le_of_lt hy.2⟩
  have := deriv_nonpos_of_forall_lt_min g _ 1 (1/2) (by norm_num) hderiv_g hmin
  linarith

/-! ### Isomorphism invariance

For a `*-`algebra equivalence `φ : Matrix m m ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ`, Umegaki's relative entropy
is invariant: `D(φ ρ ‖ φ σ) = D(ρ ‖ σ)`. In quantum information literature this is the
**isometric invariance of relative entropy**, a special case of Lindblad–Uhlmann monotonicity
restricted to invertible CPTP maps. No trace hypothesis is needed: every algebra equivalence
between full matrix algebras preserves the trace (`Matrix.trace_map`). -/

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- **Umegaki's relative entropy is invariant under `*-`algebra equivalences**, for all matrices
`ρ, σ` (the `⊤` case and the junk value included). -/
lemma umegakiEntropy_map_starAlgEquiv (ρ σ : Matrix m m ℂ)
    (φ : Matrix m m ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ) :
    D(φ ρ ∥ φ σ) = D(ρ ∥ σ) := by
  have hpsd : ∀ {A : Matrix m m ℂ}, (φ A).PosSemidef ↔ A.PosSemidef := fun {A} =>
    ⟨fun h => by simpa using h.map_starAlgEquiv φ.symm, fun h => h.map_starAlgEquiv φ⟩
  by_cases hρσ : ρ.PosSemidef ∧ σ.PosSemidef
  · obtain ⟨hρ, hσ⟩ := hρσ
    have h_supp_iff : SuppSubset (φ ρ) (φ σ) ↔ SuppSubset ρ σ :=
      suppSubset_map_starAlgEquiv_iff hσ.1 φ
    by_cases h : SuppSubset ρ σ
    · rw [umegakiEntropy_of_suppSubset (hpsd.mpr hρ) (hpsd.mpr hσ) (h_supp_iff.mpr h),
        umegakiEntropy_of_suppSubset hρ hσ h, cfc_log_map_starAlgEquiv hρ.1 φ,
        cfc_log_map_starAlgEquiv hσ.1 φ, ← map_sub, ← map_mul, Matrix.trace_map]
    · rw [umegakiEntropy_of_not_suppSubset (hpsd.mpr hρ) (hpsd.mpr hσ) (h_supp_iff.not.mpr h),
        umegakiEntropy_of_not_suppSubset hρ hσ h]
  · rw [umegakiEntropy_of_not_posSemidef hρσ,
      umegakiEntropy_of_not_posSemidef (by rwa [hpsd, hpsd])]

/-- Specialisation of `umegakiEntropy_map_starAlgEquiv` to reindexing, for all matrices. -/
lemma umegakiEntropy_reindex (e : m ≃ n) (ρ σ : Matrix m m ℂ) :
    D(reindex e e ρ ∥ reindex e e σ) = D(ρ ∥ σ) :=
  umegakiEntropy_map_starAlgEquiv ρ σ (Matrix.reindexStarAlgEquiv (R := ℂ) e)

end Matrix

namespace DensityMatrix

open Matrix
open scoped Matrix.QuantumInfo

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-- **Monotonicity** for density matrices: `D(Φ(ρ) ‖ Φ(σ)) ≤ D(ρ ‖ σ)`. -/
theorem umegakiEntropy_channel_le (Φ : QuantumChannel n m) (ρ σ : DensityMatrix n) :
    D((Φ ρ).toMatrix ∥ (Φ σ).toMatrix) ≤ D(ρ.toMatrix ∥ σ.toMatrix) :=
  Matrix.umegakiEntropy_channel_le Φ ρ.posSemidef σ.posSemidef

/-- **Joint convexity** for density matrices. -/
theorem umegakiEntropy_jointly_convex (ρ₁ ρ₂ σ₁ σ₂ : DensityMatrix n) (p : ℝ) (hp : 0 ≤ p)
    (hp1 : p ≤ 1) :
    D((mix ρ₁ ρ₂ p hp hp1).toMatrix ∥ (mix σ₁ σ₂ p hp hp1).toMatrix) ≤
      p * D(ρ₁.toMatrix ∥ σ₁.toMatrix) + (1 - p) * D(ρ₂.toMatrix ∥ σ₂.toMatrix) :=
  Matrix.umegakiEntropy_jointly_convex ρ₁.posSemidef ρ₂.posSemidef σ₁.posSemidef σ₂.posSemidef hp hp1

/-- `umegakiEntropy_reindex` for density matrices. -/
lemma umegakiEntropy_mapEquiv (ρ σ : DensityMatrix m) (e : n ≃ m) :
    D((ρ.mapEquiv e).toMatrix ∥ (σ.mapEquiv e).toMatrix) = D(ρ.toMatrix ∥ σ.toMatrix) :=
  Matrix.umegakiEntropy_reindex e.symm ρ.toMatrix σ.toMatrix

end DensityMatrix
