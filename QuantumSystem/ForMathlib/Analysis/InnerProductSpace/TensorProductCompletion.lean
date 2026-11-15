/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Topology.Algebra.LinearMapCompletion

import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# Operators on the completed tensor product of Hilbert spaces

For inner product spaces `H₁` and `H₂` over `𝕜 = ℝ` or `ℂ`, Mathlib equips the algebraic tensor
product `H₁ ⊗[𝕜] H₂` with an inner product (`TensorProduct.instInnerProductSpace`), with
`⟪a ⊗ₜ b, c ⊗ₜ d⟫ = ⟪a, c⟫ * ⟪b, d⟫`, but leaves it incomplete. Its completion
`UniformSpace.Completion (H₁ ⊗[𝕜] H₂)` is again an inner product space
(`UniformSpace.Completion.innerProductSpace`) and is complete, hence a Hilbert space: the Hilbert
space tensor product. This file states its operator theory with Mathlib's objects only.

A bounded operator `A : H₁ → H₃` acts on the algebraic tensor product as Mathlib's
`ContinuousLinearMap.rTensor`, `x ⊗ y ↦ A x ⊗ y`, bounded by `ContinuousLinearMap.norm_rTensor_le`,
and on the completion as its extension `ContinuousLinearMap.completion`: the **amplification**
`A ⊗ 𝟙 = (A.rTensor H₂).completion`. Symmetrically `𝟙 ⊗ B = (B.lTensor H₁).completion`.

The normed and inner product structures of `Completion (H₁ ⊗[ℂ] H₂)` get shortcut instances, without
which `NormedStarGroup` and `ContinuousStar` on its operators are not found (see the section *The
completed tensor product as a Hilbert space*).

## Main definitions

* `LinearIsometryEquiv.completion` — the completion of a semilinear isometric equivalence, the
  equivalence form of Mathlib's `LinearIsometry.completion`.
* `ContinuousLinearMap.rTensorCompletionStarAlgHom`, `ContinuousLinearMap.lTensorCompletionStarAlgHom`
  — the amplifications of operators on a Hilbert space, as unital `⋆`-algebra homomorphisms into
  the operators on the completed tensor product.
* `NonUnitalStarAlgHom.mapLCompletion π ρ` — the tensor product of two `⋆`-homomorphisms
  `π : A → B(H₁)`, `ρ : B → B(H₂)`, a `⋆`-homomorphism `A ⊗[𝕜] B → B(Completion (H₁ ⊗[𝕜] H₂))`;
  `TensorProduct.mapLCompletionStarAlgHom 𝕜 H₁ H₂` — the product map
  `B(H₁) ⊗ B(H₂) → B(Completion (H₁ ⊗[𝕜] H₂))`, its value at the identity homomorphisms.
* `TensorProduct.sumTmulL e` — for a finite family `e` of `H₂`, the operator
  `(ξᵢ)ᵢ ↦ ∑ᵢ ξᵢ ⊗ eᵢ` from the Hilbert sum of copies of `H₁` to `H₁ ⊗[𝕜] H₂`.
* `lp.completionTensorEquiv` — `ℓ²(ι, K) ≃ₗᵢ Completion (ℓ²(ι) ⊗[𝕜] K)`.

## Main results

* `UniformSpace.Completion.toComplL_surjective`, `FiniteDimensional.completion` — a
  finite-dimensional seminormed space surjects onto its completion, which is therefore
  finite-dimensional.
* `ContinuousLinearMap.completion_comp`, `completion_add`, `completion_smul`, … — the completion of
  continuous linear maps is functorial and linear.
* `ContinuousLinearMap.completion_eq_adjoint_completion` — the completion of a formal adjoint is the adjoint of
  the completion.
* `ContinuousLinearMap.adjoint_completion_rTensor`, `adjoint_completion_lTensor` — the adjoint of an
  amplification is the amplification of the adjoint.
* `ContinuousLinearMap.conjStarAlgEquiv_completion_commIsometry_lTensor` — swapping the factors
  turns `𝟙 ⊗ B` into `B ⊗ 𝟙`.
* `ContinuousLinearMap.norm_completion` — completion preserves the operator norm.
* `TensorProduct.norm_mapL`, `ContinuousLinearMap.norm_completion_mapL` — the operator tensor
  product has the cross norm `‖A ⊗ B‖ = ‖A‖ * ‖B‖`, on the algebraic and on the completed tensor
  product.
* `ContinuousLinearMap.adjoint_completion_mapL` — `(A ⊗ B)† = A† ⊗ B†` on the completed tensor
  product; `ContinuousLinearMap.conjStarAlgEquiv_completion_commIsometry_mapL` — swapping the
  factors turns `A ⊗ B` into `B ⊗ A`.
* `ContinuousLinearMap.eq_sum_rankOne_tensor_slice` — along an orthonormal basis `b` of a
  finite-dimensional `H₁`, an operator on `Completion (H₁ ⊗[𝕜] H₂)` is the matrix
  `∑ᵢⱼ |bᵢ⟩⟨bⱼ| ⊗ Tᵢⱼ` of operators on `H₂`; hence
  `TensorProduct.mapLCompletionStarAlgHom_surjective_of_finiteDimensional_left` and
  `TensorProduct.mapLCompletionStarAlgHom_surjective_of_finiteDimensional_right` — the product map
  `B(H₁) ⊗[𝕜] B(H₂) → B(Completion (H₁ ⊗[𝕜] H₂))` is surjective when `H₁` or `H₂` is
  finite-dimensional.
* `TensorProduct.norm_sumTmulL_apply` — for an orthonormal family `e`, `sumTmulL e` is isometric.
* `ContinuousLinearMap.opNorm_le_of_forall_inner_sumTmulL` — an operator on the completed tensor
  product is bounded by `C` as soon as its compressions to the ranges of the `sumTmulL e`, `e` a
  finite orthonormal family, are.

## Notation

| Symbol | Expansion | How to activate |
|---|---|---|
| `A ⊗ 𝟙[H₂]` | `(A.rTensor H₂).completion` | `open scoped Amplification` |
| `A ⊗ B` | `(TensorProduct.mapL A B).completion` | `open scoped Amplification` |
| `𝟙[H₁] ⊗ B` | `(B.lTensor H₁).completion` | `open scoped Amplification` |
| `⊗ₐ 𝟙[H₂]` | `ContinuousLinearMap.rTensorCompletionStarAlgHom H₂` | `open scoped Amplification` |
| `𝟙[H₁] ⊗ₐ` | `ContinuousLinearMap.lTensorCompletionStarAlgHom H₁` | `open scoped Amplification` |

The token `⊗` is also Mathlib's notation for the tensor product of modules (scope `TensorProduct`);
the two are told apart by the types of their arguments.
-/

@[expose] public section

open scoped TensorProduct InnerProduct InnerProductSpace

open UniformSpace

/-! ### Notation for operators on the completed tensor product

The three notations are declared with `notation3`, whose delaborator matches the term itself: the
unexpander of an ordinary `notation` matches the printed syntax, in which `ContinuousLinearMap.rTensor`
and `TensorProduct.mapL` are shortened inside their namespaces, and does not fire there. -/

/-- `A ⊗ 𝟙[H₂]` is the amplification `(A.rTensor H₂).completion` of `A : H₁ →L[𝕜] H₃`, the
operator `Completion (H₁ ⊗[𝕜] H₂) →L[𝕜] Completion (H₃ ⊗[𝕜] H₂)`. -/
scoped[Amplification] notation3:100 A:101 " ⊗ " "𝟙[" H₂ "]" =>
  ContinuousLinearMap.completion (ContinuousLinearMap.rTensor H₂ A)

/-- `𝟙[H₁] ⊗ B` is the amplification `(B.lTensor H₁).completion` of `B : H₂ →L[𝕜] H₄`, the
operator `Completion (H₁ ⊗[𝕜] H₂) →L[𝕜] Completion (H₁ ⊗[𝕜] H₄)`. -/
scoped[Amplification] notation3:100 "𝟙[" H₁ "]" " ⊗ " B:101 =>
  ContinuousLinearMap.completion (ContinuousLinearMap.lTensor H₁ B)

/-- `A ⊗ B` is the operator tensor product `(TensorProduct.mapL A B).completion` of `A : H₁ →L[𝕜] H₃`
and `B : H₂ →L[𝕜] H₄` on the completed tensor product, the operator
`Completion (H₁ ⊗[𝕜] H₂) →L[𝕜] Completion (H₃ ⊗[𝕜] H₄)`. -/
scoped[Amplification] notation3:100 A:101 " ⊗ " B:101 =>
  ContinuousLinearMap.completion (TensorProduct.mapL A B)

open scoped Amplification

/-! ### The completed tensor product as a Hilbert space

The normed structures of `Completion (H₁ ⊗[ℂ] H₂)` are found by instance search, but through a
nested search for those of `H₁ ⊗[ℂ] H₂`. When the outer search is itself started inside a
unification (as for `NormedStarGroup` or `ContinuousStar` on the operators of the completed tensor
product, which `CStarRing.to_normedStarGroup` reaches through their ring structure), the nested
search exceeds the default `maxSynthPendingDepth = 1` and the instance is not found. The shortcut
instances below state the two structures for the type as it is elaborated; their values are
Mathlib's instances. They are stated over `ℂ`: with the scalar field a variable they are not found
in that situation either. They cover factors that are variables or projections of a structure;
when a factor is a concrete space (`ℂ`, `EuclideanSpace ℂ ι`, `ℓ²(ι, ℂ)`) the instances of
that factor need a further nested search, and `NormedStarGroup` is still not found.

TODO: remove these once the instances of `H₁ ⊗[𝕜] H₂` need no nested search upstream. -/

namespace UniformSpace.Completion

variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]

/-- Shortcut instance for the completed tensor product; see the section doc. -/
noncomputable instance instNormedAddCommGroupTensorProduct :
    NormedAddCommGroup (Completion (H₁ ⊗[ℂ] H₂)) :=
  inferInstance

/-- Shortcut instance for the completed tensor product; see the section doc. -/
noncomputable instance instInnerProductSpaceTensorProduct :
    InnerProductSpace ℂ (Completion (H₁ ⊗[ℂ] H₂)) :=
  inferInstance

end UniformSpace.Completion

/-! ### Completion of a linear isometric equivalence and of a finite-dimensional space -/

section Completion

namespace LinearIsometryEquiv

variable {R R₂ : Type*} [Semiring R] [Semiring R₂] {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R}
  [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {E F : Type*}
  [NormedAddCommGroup E] [Module R E] [UniformContinuousConstSMul R E]
  [NormedAddCommGroup F] [Module R₂ F] [UniformContinuousConstSMul R₂ F]

/-- The completion of a semilinear isometric equivalence `f : E ≃ₛₗᵢ[σ₁₂] F`, a semilinear isometric
equivalence `Completion E ≃ₛₗᵢ[σ₁₂] Completion F`: Mathlib's `LinearIsometry.completion` of `f`, with
that of `f.symm` as its inverse. -/
noncomputable def completion (f : E ≃ₛₗᵢ[σ₁₂] F) : Completion E ≃ₛₗᵢ[σ₁₂] Completion F where
  __ := f.toLinearIsometry.completion.toLinearMap
  invFun := f.symm.toLinearIsometry.completion
  left_inv x := by
    induction x using Completion.induction_on with
    | hp => exact isClosed_eq (f.symm.toLinearIsometry.completion.continuous.comp
        f.toLinearIsometry.completion.continuous) continuous_id
    | ih a => simp [LinearIsometry.completion_apply_coe]
  right_inv x := by
    induction x using Completion.induction_on with
    | hp => exact isClosed_eq (f.toLinearIsometry.completion.continuous.comp
        f.symm.toLinearIsometry.completion.continuous) continuous_id
    | ih a => simp [LinearIsometry.completion_apply_coe]
  norm_map' := f.toLinearIsometry.completion.norm_map

/-- The completion `f.completion` agrees with `f` on the image of `E → Completion E`. -/
@[simp] lemma completion_apply_coe (f : E ≃ₛₗᵢ[σ₁₂] F) (a : E) :
    f.completion (a : Completion E) = (f a : Completion F) :=
  f.toLinearIsometry.completion_apply_coe a

/-- The inverse of `f.completion` is the completion of `f.symm`. -/
@[simp] lemma completion_symm (f : E ≃ₛₗᵢ[σ₁₂] F) : f.completion.symm = f.symm.completion := rfl

end LinearIsometryEquiv

/-- The coercion `E → Completion E` of a finite-dimensional seminormed space (over a complete
field) is surjective: its image is a finite-dimensional, hence closed, subspace, and it is dense. -/
lemma UniformSpace.Completion.toComplL_surjective {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] :
    Function.Surjective (Completion.toComplL : E →L[𝕜] Completion E) := by
  set f : E →L[𝕜] Completion E := Completion.toComplL with hf
  have hdense : DenseRange f := by
    simpa [hf, Completion.coe_toComplL] using Completion.denseRange_coe (α := E)
  have hclosed : IsClosed (Set.range f) := by
    have h := (LinearMap.range (f : E →ₗ[𝕜] Completion E)).closed_of_finiteDimensional
    rwa [LinearMap.coe_range] at h
  have hu : Set.range f = Set.univ := by rw [← hclosed.closure_eq, hdense.closure_eq]
  exact Set.range_eq_univ.mp hu

/-- The completion of a finite-dimensional seminormed space (over a complete field) is
finite-dimensional, since `toComplL : E → Completion E` is surjective. -/
instance FiniteDimensional.completion {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] :
    FiniteDimensional 𝕜 (Completion E) :=
  Module.Finite.of_surjective (Completion.toComplL : E →L[𝕜] Completion E).toLinearMap
    Completion.toComplL_surjective

end Completion

/-! ### The completion of continuous linear maps is functorial and linear -/

namespace ContinuousLinearMap

section Functorial

variable {R S T : Type*} [Semiring R] [Semiring S] [Semiring T]
  {σ : R →+* S} {τ : S →+* T} {ρ : R →+* T} [RingHomCompTriple σ τ ρ] {E F G : Type*}
  [UniformSpace E] [AddCommGroup E] [IsUniformAddGroup E] [Module R E] [UniformContinuousConstSMul R E]
  [UniformSpace F] [AddCommGroup F] [IsUniformAddGroup F] [Module S F] [UniformContinuousConstSMul S F]
  [UniformSpace G] [AddCommGroup G] [IsUniformAddGroup G] [Module T G] [UniformContinuousConstSMul T G]

/-- The completion of the identity of `E` is the identity of `Completion E`. -/
@[simp] lemma completion_id : (ContinuousLinearMap.id R E).completion = .id R (Completion E) := by
  ext x
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (ContinuousLinearMap.continuous _) continuous_id
  | ih a => simp

/-- The completion of the unit operator `1` on `E` is the unit operator on `Completion E`. -/
@[simp] lemma completion_one : (1 : E →L[R] E).completion = 1 :=
  completion_id

/-- Completion commutes with composition: `(g ∘SL f).completion = g.completion ∘SL f.completion`. -/
lemma completion_comp (g : F →SL[τ] G) (f : E →SL[σ] F) :
    (g ∘SL f).completion = g.completion ∘SL f.completion := by
  ext x
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
  | ih a => simp

/-- Completion of operators on `E` is multiplicative: `(f * g).completion = f.completion * g.completion`. -/
lemma completion_mul (f g : E →L[R] E) : (f * g).completion = f.completion * g.completion :=
  completion_comp f g

/-- The completion of the zero map is the zero map. -/
@[simp] lemma completion_zero : (0 : E →SL[σ] F).completion = 0 := by
  ext x
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (ContinuousLinearMap.continuous _) continuous_const
  | ih a => simp

/-- Completion is additive: `(f + g).completion = f.completion + g.completion`. -/
lemma completion_add (f g : E →SL[σ] F) : (f + g).completion = f.completion + g.completion := by
  ext x
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
  | ih a => rw [completion_apply_coe, add_apply, add_apply, completion_apply_coe,
      completion_apply_coe, Completion.coe_add]

end Functorial

section Smul

variable {R : Type*} [CommSemiring R] {E F : Type*}
  [UniformSpace E] [AddCommGroup E] [IsUniformAddGroup E] [Module R E] [UniformContinuousConstSMul R E]
  [UniformSpace F] [AddCommGroup F] [IsUniformAddGroup F] [Module R F] [UniformContinuousConstSMul R F]

/-- Completion commutes with scalar multiplication: `(c • f).completion = c • f.completion`. -/
lemma completion_smul (c : R) (f : E →L[R] F) : (c • f).completion = c • f.completion := by
  ext x
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
  | ih a => rw [completion_apply_coe, smul_apply, smul_apply, completion_apply_coe,
      Completion.coe_smul]

end Smul

section Adjoint

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- **The completion of a formal adjoint is the adjoint of the completion.** If `g` is adjoint to
`f` on the (possibly incomplete) inner product spaces, `⟪g x, y⟫ = ⟪x, f y⟫`, then
`g.completion = f.completion†`. -/
lemma completion_eq_adjoint_completion {f : E →L[𝕜] F} {g : F →L[𝕜] E}
    (h : ∀ x y, ⟪g x, y⟫_𝕜 = ⟪x, f y⟫_𝕜) : g.completion = f.completion† := by
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro u v
  induction u, v using Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih a b => rw [completion_apply_coe, completion_apply_coe, Completion.inner_coe,
      Completion.inner_coe, h]

end Adjoint

section Norm

variable {𝕜 𝕜₂ E F : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  {σ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜₂ F]

/-- Completion preserves the operator norm: `‖f.completion‖ = ‖f‖`. -/
@[simp] lemma norm_completion (f : E →SL[σ] F) : ‖f.completion‖ = ‖f‖ := by
  refine le_antisymm (opNorm_le_bound _ (norm_nonneg f) fun x => ?_)
    (opNorm_le_bound _ (norm_nonneg _) fun a => ?_)
  · induction x using Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih a =>
      rw [completion_apply_coe, Completion.norm_coe, Completion.norm_coe]
      exact f.le_opNorm a
  · rw [← Completion.norm_coe (f a), ← completion_apply_coe, ← Completion.norm_coe a]
    exact f.completion.le_opNorm _

end Norm

/-! ### Amplifications on the completed tensor product -/

variable {𝕜 : Type*} [RCLike 𝕜] {H₁ H₂ H₃ H₄ : Type*}
  [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
  [NormedAddCommGroup H₃] [InnerProductSpace 𝕜 H₃]
  [NormedAddCommGroup H₄] [InnerProductSpace 𝕜 H₄]

/-- On pure tensors the formal adjoint of `A.rTensor H₂` is `A†.rTensor H₂`. -/
private lemma inner_adjoint_rTensor [CompleteSpace H₁] [CompleteSpace H₃] (A : H₁ →L[𝕜] H₃)
    (a : H₃ ⊗[𝕜] H₂) (b : H₁ ⊗[𝕜] H₂) :
    ⟪(A†).rTensor H₂ a, b⟫_𝕜 = ⟪a, A.rTensor H₂ b⟫_𝕜 := by
  induction a using TensorProduct.inductionOn with
  | tmul x y =>
    induction b using TensorProduct.inductionOn with
    | tmul x' y' => simp [TensorProduct.inner_tmul, adjoint_inner_left]
    | add p q hp hq => simp only [inner_add_right, map_add, hp, hq]
  | add p q hp hq => simp only [inner_add_left, map_add, hp, hq]

/-- On pure tensors the formal adjoint of `B.lTensor H₁` is `B†.lTensor H₁`. -/
private lemma inner_adjoint_lTensor [CompleteSpace H₂] [CompleteSpace H₄] (B : H₂ →L[𝕜] H₄)
    (a : H₁ ⊗[𝕜] H₄) (b : H₁ ⊗[𝕜] H₂) :
    ⟪(B†).lTensor H₁ a, b⟫_𝕜 = ⟪a, B.lTensor H₁ b⟫_𝕜 := by
  induction a using TensorProduct.inductionOn with
  | tmul x y =>
    induction b using TensorProduct.inductionOn with
    | tmul x' y' => simp [TensorProduct.inner_tmul, adjoint_inner_left]
    | add p q hp hq => simp only [inner_add_right, map_add, hp, hq]
  | add p q hp hq => simp only [inner_add_left, map_add, hp, hq]

/-- The adjoint of the amplification `A ⊗ 𝟙` is `A† ⊗ 𝟙`. -/
lemma adjoint_completion_rTensor [CompleteSpace H₁] [CompleteSpace H₃] (A : H₁ →L[𝕜] H₃) :
    (A ⊗ 𝟙[H₂])† = (A†) ⊗ 𝟙[H₂] :=
  (completion_eq_adjoint_completion (inner_adjoint_rTensor A)).symm

/-- The adjoint of the amplification `𝟙 ⊗ B` is `𝟙 ⊗ B†`. -/
lemma adjoint_completion_lTensor [CompleteSpace H₂] [CompleteSpace H₄] (B : H₂ →L[𝕜] H₄) :
    (𝟙[H₁] ⊗ B)† = 𝟙[H₁] ⊗ (B†) :=
  (completion_eq_adjoint_completion (inner_adjoint_lTensor B)).symm

variable (H₂) in
/-- The **amplification** `A ↦ A ⊗ 𝟙` of the operators on a Hilbert space `H₁`, as a unital
`⋆`-algebra homomorphism into the operators on `Completion (H₁ ⊗[𝕜] H₂)`. -/
noncomputable def rTensorCompletionStarAlgHom [CompleteSpace H₁] :
    (H₁ →L[𝕜] H₁) →⋆ₐ[𝕜] (Completion (H₁ ⊗[𝕜] H₂) →L[𝕜] Completion (H₁ ⊗[𝕜] H₂)) where
  toFun A := (A.rTensor H₂).completion
  map_one' := by simp
  map_mul' A B := by rw [rTensor_mul, completion_mul]
  map_zero' := by simp
  map_add' A B := by rw [rTensor_add, completion_add]
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one, rTensor_smul, completion_smul, rTensor_one,
      completion_one]
  map_star' A := by
    simp only [star_eq_adjoint, adjoint_completion_rTensor]

/-- `rTensorCompletionStarAlgHom H₂` sends `A` to the completion of `A.rTensor H₂`, the operator `A ⊗ 𝟙`. -/
@[simp] lemma rTensorCompletionStarAlgHom_apply [CompleteSpace H₁] (A : H₁ →L[𝕜] H₁) :
    rTensorCompletionStarAlgHom H₂ A = (A.rTensor H₂).completion := rfl

variable (H₁) in
/-- The **amplification** `B ↦ 𝟙 ⊗ B` of the operators on a Hilbert space `H₂`, as a unital
`⋆`-algebra homomorphism into the operators on `Completion (H₁ ⊗[𝕜] H₂)`. -/
noncomputable def lTensorCompletionStarAlgHom [CompleteSpace H₂] :
    (H₂ →L[𝕜] H₂) →⋆ₐ[𝕜] (Completion (H₁ ⊗[𝕜] H₂) →L[𝕜] Completion (H₁ ⊗[𝕜] H₂)) where
  toFun B := (B.lTensor H₁).completion
  map_one' := by simp
  map_mul' A B := by rw [lTensor_mul, completion_mul]
  map_zero' := by simp
  map_add' A B := by rw [lTensor_add, completion_add]
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one, lTensor_smul, completion_smul, lTensor_one,
      completion_one]
  map_star' B := by
    simp only [star_eq_adjoint, adjoint_completion_lTensor]

/-- `lTensorCompletionStarAlgHom H₁` sends `B` to the completion of `B.lTensor H₁`, the operator `𝟙 ⊗ B`. -/
@[simp] lemma lTensorCompletionStarAlgHom_apply [CompleteSpace H₂] (B : H₂ →L[𝕜] H₂) :
    lTensorCompletionStarAlgHom H₁ B = (B.lTensor H₁).completion := rfl

/-- Swapping the factors turns the amplification `𝟙 ⊗ B` on `Completion (H₁ ⊗[𝕜] H₂)` into
the amplification `B ⊗ 𝟙` on `Completion (H₂ ⊗[𝕜] H₁)`. -/
lemma conjStarAlgEquiv_completion_commIsometry_lTensor (B : H₂ →L[𝕜] H₂) :
    (TensorProduct.commIsometry 𝕜 H₁ H₂).completion.conjStarAlgEquiv (𝟙[H₁] ⊗ B) = B ⊗ 𝟙[H₁] := by
  ext w
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  induction w using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih a =>
    rw [LinearIsometryEquiv.completion_symm, LinearIsometryEquiv.completion_apply_coe,
      completion_apply_coe, LinearIsometryEquiv.completion_apply_coe, completion_apply_coe]
    congr 1
    induction a using TensorProduct.inductionOn with
    | tmul y x => simp
    | add p q hp hq => simp only [map_add, hp, hq]

/-! ### The operator tensor product on the completed tensor product

The tensor product `A ⊗ B` of operators `A : H₁ → H₃` and `B : H₂ → H₄` is Mathlib's
`TensorProduct.mapL A B` on the algebraic tensor product and its completion
`(TensorProduct.mapL A B).completion` on the Hilbert space tensor product; it is the composite
`(A ⊗ 𝟙)(𝟙 ⊗ B)` of the two amplifications. -/

/-- `A ⊗ B = (A ⊗ 𝟙)(𝟙 ⊗ B)` on the completed tensor product. -/
lemma completion_mapL (A : H₁ →L[𝕜] H₃) (B : H₂ →L[𝕜] H₄) :
    A ⊗ B = (A ⊗ 𝟙[H₄]) ∘L (𝟙[H₁] ⊗ B) :=
  completion_comp _ _

/-- The adjoint of `A ⊗ B` on the completed tensor product is `A† ⊗ B†`. -/
lemma adjoint_completion_mapL [CompleteSpace H₁] [CompleteSpace H₂] [CompleteSpace H₃]
    [CompleteSpace H₄] (A : H₁ →L[𝕜] H₃) (B : H₂ →L[𝕜] H₄) :
    (A ⊗ B)† = A† ⊗ B† := by
  rw [completion_mapL, adjoint_comp, adjoint_completion_rTensor, adjoint_completion_lTensor,
    ← completion_comp, lTensor_comp_rTensor]

open scoped ComplexOrder in
/-- **The tensor product of positive operators on Hilbert spaces is positive** on the Hilbert space
tensor product: with `A = a⋆ a` and `B = b⋆ b`, `A ⊗ B = (a ⊗ b)⋆ (a ⊗ b)`. The spaces are complex:
Mathlib makes the operators a star-ordered ring, in which every positive element is some `a⋆ a`,
only over `ℂ`, through their C⋆-algebra structure. -/
theorem completion_mapL_nonneg {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [CompleteSpace H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    {A : H₁ →L[ℂ] H₁} {B : H₂ →L[ℂ] H₂} (hA : 0 ≤ A) (hB : 0 ≤ B) : 0 ≤ A ⊗ B := by
  obtain ⟨a, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA
  obtain ⟨b, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB
  rw [TensorProduct.mapL_mul, completion_mul, star_eq_adjoint, star_eq_adjoint,
    ← adjoint_completion_mapL, ← star_eq_adjoint]
  exact star_mul_self_nonneg _

end ContinuousLinearMap

namespace TensorProduct

variable {𝕜 : Type*} [RCLike 𝕜] {H₁ H₂ H₃ H₄ : Type*}
  [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
  [NormedAddCommGroup H₃] [InnerProductSpace 𝕜 H₃]
  [NormedAddCommGroup H₄] [InnerProductSpace 𝕜 H₄]

open ContinuousLinearMap in
/-- The operator tensor product has the cross norm `‖A ⊗ B‖ = ‖A‖ * ‖B‖`, already on the algebraic
tensor product. -/
@[simp] lemma norm_mapL (A : H₁ →L[𝕜] H₃) (B : H₂ →L[𝕜] H₄) :
    ‖TensorProduct.mapL A B‖ = ‖A‖ * ‖B‖ := by
  refine le_antisymm (TensorProduct.norm_mapL_le A B) ?_
  have key (x : H₁) (y : H₂) : ‖A x‖ * ‖B y‖ ≤ ‖TensorProduct.mapL A B‖ * (‖x‖ * ‖y‖) := by
    have h := (TensorProduct.mapL A B).le_opNorm (x ⊗ₜ[𝕜] y)
    rwa [TensorProduct.mapL_tmul, TensorProduct.norm_tmul, TensorProduct.norm_tmul] at h
  have hA (x : H₁) : ‖A x‖ * ‖B‖ ≤ ‖TensorProduct.mapL A B‖ * ‖x‖ := by
    have h : ‖(‖A x‖ : 𝕜) • B‖ ≤ ‖TensorProduct.mapL A B‖ * ‖x‖ :=
      opNorm_le_bound _ (by positivity) fun y => by
        rw [smul_apply, norm_smul, RCLike.norm_ofReal, abs_norm, mul_assoc]
        exact key x y
    rwa [norm_smul, RCLike.norm_ofReal, abs_norm] at h
  have h : ‖(‖B‖ : 𝕜) • A‖ ≤ ‖TensorProduct.mapL A B‖ :=
    opNorm_le_bound _ (norm_nonneg _) fun x => by
      rw [smul_apply, norm_smul, RCLike.norm_ofReal, abs_norm, mul_comm]
      exact hA x
  rwa [norm_smul, RCLike.norm_ofReal, abs_norm, mul_comm] at h

end TensorProduct

namespace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜] {H₁ H₂ H₃ H₄ : Type*}
  [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
  [NormedAddCommGroup H₃] [InnerProductSpace 𝕜 H₃]
  [NormedAddCommGroup H₄] [InnerProductSpace 𝕜 H₄]

/-- The operator tensor product has the cross norm `‖A ⊗ B‖ = ‖A‖ * ‖B‖` on the completed tensor
product. -/
lemma norm_completion_mapL (A : H₁ →L[𝕜] H₃) (B : H₂ →L[𝕜] H₄) : ‖A ⊗ B‖ = ‖A‖ * ‖B‖ := by
  rw [norm_completion, TensorProduct.norm_mapL]

/-- Swapping the factors turns `A ⊗ B` on `Completion (H₁ ⊗[𝕜] H₂)` into `B ⊗ A` on
`Completion (H₂ ⊗[𝕜] H₁)`. -/
lemma conjStarAlgEquiv_completion_commIsometry_mapL (A : H₁ →L[𝕜] H₁) (B : H₂ →L[𝕜] H₂) :
    (TensorProduct.commIsometry 𝕜 H₁ H₂).completion.conjStarAlgEquiv (A ⊗ B) = B ⊗ A := by
  ext w
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  induction w using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih a =>
    rw [LinearIsometryEquiv.completion_symm, LinearIsometryEquiv.completion_apply_coe,
      completion_apply_coe, LinearIsometryEquiv.completion_apply_coe, completion_apply_coe]
    congr 1
    induction a using TensorProduct.inductionOn with
    | tmul y x => simp
    | add p q hp hq => simp only [map_add, hp, hq]

end ContinuousLinearMap

/-- `⊗ₐ 𝟙[H₂]` is the amplification `A ↦ A ⊗ 𝟙[H₂]` as a `⋆`-algebra homomorphism. -/
scoped[Amplification] notation "⊗ₐ " "𝟙[" H₂ "]" => ContinuousLinearMap.rTensorCompletionStarAlgHom H₂

/-- `𝟙[H₁] ⊗ₐ` is the amplification `B ↦ 𝟙[H₁] ⊗ B` as a `⋆`-algebra homomorphism. -/
scoped[Amplification] notation "𝟙[" H₁ "]" " ⊗ₐ" => ContinuousLinearMap.lTensorCompletionStarAlgHom H₁

/-! ### The tensor product of two `⋆`-homomorphisms into operator algebras

For `⋆`-homomorphisms `π : A → B(H₁)` and `ρ : B → B(H₂)` of `⋆`-algebras, the operators
`π(a) ⊗ ρ(b)` on the completed tensor product define a `⋆`-homomorphism of the algebraic tensor
product `A ⊗[𝕜] B`. For `π` and `ρ` the identity it is the product map
`B(H₁) ⊗ B(H₂) → B(Completion (H₁ ⊗[𝕜] H₂))`. -/

namespace NonUnitalStarAlgHom

variable {𝕜 : Type*} [RCLike 𝕜] {A B H₁ H₂ : Type*}
  [NonUnitalRing A] [StarRing A] [Module 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
  [StarModule 𝕜 A]
  [NonUnitalRing B] [StarRing B] [Module 𝕜 B] [IsScalarTower 𝕜 B B] [SMulCommClass 𝕜 B B]
  [StarModule 𝕜 B]
  [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]

open TensorProduct in
/-- The **tensor product of two `⋆`-homomorphisms into operator algebras** `π : A → B(H₁)` and
`ρ : B → B(H₂)`, on the algebraic tensor product: the `⋆`-homomorphism of `A ⊗[𝕜] B` into the
operators on the Hilbert space tensor product `Completion (H₁ ⊗[𝕜] H₂)` that sends `a ⊗ b` to
`π(a) ⊗ ρ(b)`. -/
noncomputable def mapLCompletion (π : A →⋆ₙₐ[𝕜] (H₁ →L[𝕜] H₁)) (ρ : B →⋆ₙₐ[𝕜] (H₂ →L[𝕜] H₂)) :
    A ⊗[𝕜] B →⋆ₙₐ[𝕜] (Completion (H₁ ⊗[𝕜] H₂) →L[𝕜] Completion (H₁ ⊗[𝕜] H₂)) where
  toFun := TensorProduct.lift <| LinearMap.mk₂ 𝕜 (fun a b => (mapL (π a) (ρ b)).completion)
    (fun a a' b => by rw [map_add, mapL_add_left, ContinuousLinearMap.completion_add])
    (fun c a b => by rw [map_smul, mapL_smul_left, ContinuousLinearMap.completion_smul])
    (fun a b b' => by rw [map_add, mapL_add_right, ContinuousLinearMap.completion_add])
    (fun c a b => by rw [map_smul, mapL_smul_right, ContinuousLinearMap.completion_smul])
  map_smul' c x := map_smul _ c x
  map_zero' := map_zero _
  map_add' := map_add _
  map_mul' x y := by
    induction x using TensorProduct.inductionOn with
    | tmul a b =>
      induction y using TensorProduct.inductionOn with
      | tmul a' b' =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, lift.tmul, LinearMap.mk₂_apply,
          map_mul, mapL_mul, ContinuousLinearMap.completion_mul]
      | add p q hp hq => rw [mul_add, map_add, hp, hq, map_add, mul_add]
    | add p q hp hq => rw [add_mul, map_add, hp, hq, map_add, add_mul]
  map_star' x := by
    induction x using TensorProduct.inductionOn with
    | tmul a b =>
      simp only [star_tmul, lift.tmul, LinearMap.mk₂_apply, map_star,
        ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_completion_mapL]
    | add p q hp hq => rw [star_add, map_add, hp, hq, map_add, ← star_add]

/-- `mapLCompletion π ρ` sends the pure tensor `a ⊗ b` to the operator `π(a) ⊗ ρ(b)`. -/
@[simp] lemma mapLCompletion_tmul (π : A →⋆ₙₐ[𝕜] (H₁ →L[𝕜] H₁)) (ρ : B →⋆ₙₐ[𝕜] (H₂ →L[𝕜] H₂))
    (a : A) (b : B) :
    mapLCompletion π ρ (a ⊗ₜ[𝕜] b) = π a ⊗ ρ b := rfl

/-- The tensor product of two `⋆`-homomorphisms is natural in the algebras: if `π = π' ∘ f` and
`ρ = ρ' ∘ g` for linear maps `f : A → A'` and `g : B → B'`, then `π ⊗ ρ = (π' ⊗ ρ') ∘ (f ⊗ g)`. -/
lemma mapLCompletion_eq_mapLCompletion_map {A' B' : Type*}
    [NonUnitalRing A'] [StarRing A'] [Module 𝕜 A'] [IsScalarTower 𝕜 A' A'] [SMulCommClass 𝕜 A' A']
    [StarModule 𝕜 A']
    [NonUnitalRing B'] [StarRing B'] [Module 𝕜 B'] [IsScalarTower 𝕜 B' B'] [SMulCommClass 𝕜 B' B']
    [StarModule 𝕜 B']
    {π : A →⋆ₙₐ[𝕜] (H₁ →L[𝕜] H₁)} {ρ : B →⋆ₙₐ[𝕜] (H₂ →L[𝕜] H₂)}
    {π' : A' →⋆ₙₐ[𝕜] (H₁ →L[𝕜] H₁)} {ρ' : B' →⋆ₙₐ[𝕜] (H₂ →L[𝕜] H₂)} {f : A →ₗ[𝕜] A'}
    {g : B →ₗ[𝕜] B'} (hπ : ∀ a, π a = π' (f a)) (hρ : ∀ b, ρ b = ρ' (g b)) (x : A ⊗[𝕜] B) :
    mapLCompletion π ρ x = mapLCompletion π' ρ' (TensorProduct.map f g x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => rw [mapLCompletion_tmul, TensorProduct.map_tmul, mapLCompletion_tmul, hπ, hρ]
  | add p q hp hq => rw [map_add, hp, hq, map_add, map_add]

end NonUnitalStarAlgHom

namespace TensorProduct

variable {𝕜 : Type*} [RCLike 𝕜] {H₁ H₂ : Type*}
  [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]

variable (𝕜 H₁ H₂) in
/-- The **product map** `B(H₁) ⊗ B(H₂) → B(Completion (H₁ ⊗[𝕜] H₂))`, `f ⊗ g ↦ f ⊗ g`, of the
algebraic tensor product of the operator algebras into the operators on the Hilbert space tensor
product, as a unital `⋆`-algebra homomorphism: the tensor product
`NonUnitalStarAlgHom.mapLCompletion` of the two identity homomorphisms. -/
noncomputable def mapLCompletionStarAlgHom :
    (H₁ →L[𝕜] H₁) ⊗[𝕜] (H₂ →L[𝕜] H₂) →⋆ₐ[𝕜]
      (Completion (H₁ ⊗[𝕜] H₂) →L[𝕜] Completion (H₁ ⊗[𝕜] H₂)) :=
  have hone : NonUnitalStarAlgHom.mapLCompletion (NonUnitalStarAlgHom.id 𝕜 (H₁ →L[𝕜] H₁))
      (NonUnitalStarAlgHom.id 𝕜 (H₂ →L[𝕜] H₂)) 1 = 1 := by
    rw [Algebra.TensorProduct.one_def, NonUnitalStarAlgHom.mapLCompletion_tmul]
    simp only [NonUnitalStarAlgHom.coe_id, id_eq, ContinuousLinearMap.one_def, mapL_id_id,
      ContinuousLinearMap.completion_id]
  { NonUnitalStarAlgHom.mapLCompletion (NonUnitalStarAlgHom.id 𝕜 (H₁ →L[𝕜] H₁))
      (NonUnitalStarAlgHom.id 𝕜 (H₂ →L[𝕜] H₂)) with
    map_one' := hone
    commutes' := fun r => by
      simp only [Algebra.algebraMap_eq_smul_one]
      exact (map_smul _ r 1).trans (congrArg (r • ·) hone) }

/-- The product map sends `f ⊗ g` to the operator tensor product on the completed tensor
product. -/
@[simp] lemma mapLCompletionStarAlgHom_tmul (f : H₁ →L[𝕜] H₁) (g : H₂ →L[𝕜] H₂) :
    mapLCompletionStarAlgHom 𝕜 H₁ H₂ (f ⊗ₜ[𝕜] g) = f ⊗ g := rfl

end TensorProduct

/-! ### Slices along a vector of the first factor

For `e : H₁`, the inclusion `ι_e : y ↦ e ⊗ y` of `H₂` into `Completion (H₁ ⊗[𝕜] H₂)` has the
`e`-slice `g ⊗ z ↦ ⟪e, g⟫ • z` as adjoint. Along an orthonormal basis of a finite-dimensional `H₁`
the slices decompose an operator on the completed tensor product into a matrix of operators on
`H₂`, so that the product map `B(H₁) ⊗[𝕜] B(H₂) → B(Completion (H₁ ⊗[𝕜] H₂))` is surjective when a
factor is finite-dimensional. -/

namespace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜] {H₁ H₂ : Type*}
  [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]

/-- `ι[e]` is the inclusion `ι_e : H₂ → Completion (H₁ ⊗[𝕜] H₂)`, `y ↦ e ⊗ y`. -/
local notation "ι[" e "]" => Completion.toComplL ∘L TensorProduct.mkL 𝕜 H₁ H₂ e

/-- The adjoint of the inclusion `ι_e : y ↦ e ⊗ y` acts on pure tensors as the `e`-slice
`g ⊗ z ↦ ⟪e, g⟫ • z`. -/
lemma adjoint_toComplL_comp_mkL_apply_coe_tmul (e g : H₁) (z : H₂) :
    (ι[e]†) (g ⊗ₜ[𝕜] z : Completion (H₁ ⊗[𝕜] H₂)) = ⟪e, g⟫_𝕜 • z := by
  refine ext_inner_right 𝕜 fun y => ?_
  rw [adjoint_inner_left, comp_apply, Completion.coe_toComplL, TensorProduct.mkL_apply_apply,
    Completion.inner_coe, TensorProduct.inner_tmul, inner_smul_left, inner_conj_symm]

/-- The amplification of a rank-one operator `|f⟩⟨e|` factors through the `e`-slice and the
inclusion `ι_f`: `(|f⟩⟨e|) ⊗ 𝟙 = ι_f ∘ ι_e†`. This is the algebraic heart of the slice
argument. -/
lemma completion_rTensor_rankOne (e f : H₁) :
    (InnerProductSpace.rankOne 𝕜 f e) ⊗ 𝟙[H₂]
      = ι[f] ∘L ι[e]† := by
  ext w
  induction w using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih a =>
    induction a using TensorProduct.inductionOn with
    | tmul g z =>
      rw [completion_apply_coe, comp_apply, adjoint_toComplL_comp_mkL_apply_coe_tmul, comp_apply,
        Completion.coe_toComplL, TensorProduct.mkL_apply_apply, rTensor_tmul,
        InnerProductSpace.rankOne_apply, TensorProduct.smul_tmul]
    | add p q hp hq => rw [Completion.coe_add, map_add, map_add, hp, hq]

/-- The `e`-slice `ι_e†` intertwines the amplification `𝟙 ⊗ S` with `S`:
`ι_e† ∘ (𝟙 ⊗ S) = S ∘ ι_e†`. -/
lemma adjoint_toComplL_comp_mkL_comp_completion_lTensor (e : H₁) (S : H₂ →L[𝕜] H₂) :
    ι[e]† ∘L (𝟙[H₁] ⊗ S) = S ∘L ι[e]† := by
  ext w
  induction w using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih a =>
    induction a using TensorProduct.inductionOn with
    | tmul g z =>
      rw [comp_apply, completion_apply_coe, lTensor_tmul, adjoint_toComplL_comp_mkL_apply_coe_tmul,
        comp_apply, adjoint_toComplL_comp_mkL_apply_coe_tmul, map_smul]
    | add p q hp hq => rw [Completion.coe_add, map_add, map_add, hp, hq]

/-- **An operator on `Completion (H₁ ⊗[𝕜] H₂)` is a matrix of operators on `H₂`** along an
orthonormal basis `b` of a finite-dimensional `H₁`: `T = ∑ᵢⱼ |bᵢ⟩⟨bⱼ| ⊗ Tᵢⱼ` with
`Tᵢⱼ = ι_{bᵢ}† ∘ T ∘ ι_{bⱼ}`. -/
lemma eq_sum_rankOne_tensor_slice {κ : Type*} [Fintype κ]
    (b : OrthonormalBasis κ 𝕜 H₁)
    (T : Completion (H₁ ⊗[𝕜] H₂) →L[𝕜] Completion (H₁ ⊗[𝕜] H₂)) :
    T = ∑ i, ∑ j, InnerProductSpace.rankOne 𝕜 (b i) (b j) ⊗ (ι[b i]† ∘L T ∘L ι[b j]) := by
  have : FiniteDimensional 𝕜 H₁ := Module.Basis.finiteDimensional_of_finite b.toBasis
  have : CompleteSpace H₁ := FiniteDimensional.complete 𝕜 H₁
  have hterm (i j : κ) : InnerProductSpace.rankOne 𝕜 (b i) (b j) ⊗ (ι[b i]† ∘L T ∘L ι[b j]) =
      (InnerProductSpace.rankOne 𝕜 (b i) (b i) ⊗ 𝟙[H₂]) ∘L T ∘L
        (InnerProductSpace.rankOne 𝕜 (b j) (b j) ⊗ 𝟙[H₂]) := by
    rw [completion_mapL, completion_rTensor_rankOne, completion_rTensor_rankOne,
      completion_rTensor_rankOne, comp_assoc, adjoint_toComplL_comp_mkL_comp_completion_lTensor]
    simp only [comp_assoc]
  have hone : ∑ i, InnerProductSpace.rankOne 𝕜 (b i) (b i) ⊗ 𝟙[H₂] = 1 := by
    simp_rw [← rTensorCompletionStarAlgHom_apply]
    rw [← map_sum, b.sum_rankOne_eq_id, ← one_def, map_one]
  calc T = (∑ i, InnerProductSpace.rankOne 𝕜 (b i) (b i) ⊗ 𝟙[H₂]) ∘L T ∘L
        (∑ j, InnerProductSpace.rankOne 𝕜 (b j) (b j) ⊗ 𝟙[H₂]) := by
        rw [hone, one_def, id_comp, comp_id]
    _ = ∑ i, ∑ j, InnerProductSpace.rankOne 𝕜 (b i) (b j) ⊗ (ι[b i]† ∘L T ∘L ι[b j]) := by
        rw [finsetSum_comp]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [comp_finsetSum, comp_finsetSum]
        exact Finset.sum_congr rfl fun j _ => (hterm i j).symm

/-- Swapping the factors carries the product map of `H₁`, `H₂` onto that of `H₂`, `H₁`. -/
lemma conjStarAlgEquiv_completion_commIsometry_mapLCompletionStarAlgHom [CompleteSpace H₁]
    (x : (H₁ →L[𝕜] H₁) ⊗[𝕜] (H₂ →L[𝕜] H₂)) :
    (TensorProduct.commIsometry 𝕜 H₁ H₂).completion.conjStarAlgEquiv
        (TensorProduct.mapLCompletionStarAlgHom 𝕜 H₁ H₂ x) =
      TensorProduct.mapLCompletionStarAlgHom 𝕜 H₂ H₁ (TensorProduct.comm 𝕜 _ _ x) := by
  ext w
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  induction x using TensorProduct.inductionOn with
  | tmul f g =>
    rw [← LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
      TensorProduct.mapLCompletionStarAlgHom_tmul, conjStarAlgEquiv_completion_commIsometry_mapL,
      TensorProduct.comm_tmul, TensorProduct.mapLCompletionStarAlgHom_tmul]
  | add p q hp hq => simp only [map_add, add_apply, hp, hq]

end ContinuousLinearMap

namespace TensorProduct

variable {𝕜 : Type*} [RCLike 𝕜] {H₁ H₂ : Type*}
  [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]

/-- **The product map `B(H₁) ⊗[𝕜] B(H₂) → B(Completion (H₁ ⊗[𝕜] H₂))` is surjective when `H₁` is
finite-dimensional**: an operator on the Hilbert space tensor product is a matrix of operators on
`H₂` (`ContinuousLinearMap.eq_sum_rankOne_tensor_slice`). -/
theorem mapLCompletionStarAlgHom_surjective_of_finiteDimensional_left [FiniteDimensional 𝕜 H₁] :
    Function.Surjective (mapLCompletionStarAlgHom 𝕜 H₁ H₂) := fun T => by
  let b := stdOrthonormalBasis 𝕜 H₁
  refine ⟨∑ i, ∑ j, InnerProductSpace.rankOne 𝕜 (b i) (b j) ⊗ₜ[𝕜]
    ((Completion.toComplL ∘L TensorProduct.mkL 𝕜 H₁ H₂ (b i))† ∘L T ∘L
      (Completion.toComplL ∘L TensorProduct.mkL 𝕜 H₁ H₂ (b j))), ?_⟩
  simp_rw [map_sum, mapLCompletionStarAlgHom_tmul]
  exact (ContinuousLinearMap.eq_sum_rankOne_tensor_slice b T).symm

/-- **The product map `B(H₁) ⊗[𝕜] B(H₂) → B(Completion (H₁ ⊗[𝕜] H₂))` is surjective when `H₂` is
finite-dimensional.** -/
theorem mapLCompletionStarAlgHom_surjective_of_finiteDimensional_right [FiniteDimensional 𝕜 H₂] :
    Function.Surjective (mapLCompletionStarAlgHom 𝕜 H₁ H₂) := fun T => by
  obtain ⟨y, hy⟩ := mapLCompletionStarAlgHom_surjective_of_finiteDimensional_left (H₁ := H₂)
    (H₂ := H₁) ((TensorProduct.commIsometry 𝕜 H₁ H₂).completion.conjStarAlgEquiv T)
  refine ⟨(TensorProduct.comm 𝕜 (H₁ →L[𝕜] H₁) (H₂ →L[𝕜] H₂)).symm y, ?_⟩
  refine EquivLike.injective (TensorProduct.commIsometry 𝕜 H₁ H₂).completion.conjStarAlgEquiv ?_
  rw [ContinuousLinearMap.conjStarAlgEquiv_completion_commIsometry_mapLCompletionStarAlgHom,
    LinearEquiv.apply_symm_apply, hy]

end TensorProduct

/-! ### Compression to finitely many vectors of the second factor

A finite family `e : ι → H₂` gives the operator `(ξᵢ)ᵢ ↦ ∑ᵢ ξᵢ ⊗ eᵢ` from the Hilbert sum
`PiLp 2 (fun _ : ι => H₁)` to `H₁ ⊗[𝕜] H₂`, isometric when `e` is orthonormal. Any two vectors of the
algebraic tensor product lie in the range of one such isometry, so an operator on the completed
tensor product is bounded by `C` as soon as all its compressions to these ranges are. -/

namespace TensorProduct

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜] {H₁ H₂ : Type*}
  [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
  {ι : Type*} [Fintype ι]

/-- The operator `(ξᵢ)ᵢ ↦ ∑ᵢ ξᵢ ⊗ eᵢ` from the Hilbert sum of `ι` copies of `H₁` to the tensor
product `H₁ ⊗[𝕜] H₂`, for a finite family `e : ι → H₂`. -/
noncomputable def sumTmulL (e : ι → H₂) : PiLp 2 (fun _ : ι => H₁) →L[𝕜] H₁ ⊗[𝕜] H₂ :=
  ∑ i, (mkL 𝕜 H₁ H₂).flip (e i) ∘L PiLp.proj 2 (fun _ : ι => H₁) i

/-- `sumTmulL e` sends `(ξᵢ)ᵢ` to `∑ᵢ ξᵢ ⊗ eᵢ`. -/
lemma sumTmulL_apply (e : ι → H₂) (ξ : PiLp 2 (fun _ : ι => H₁)) :
    sumTmulL e ξ = ∑ i, ξ i ⊗ₜ[𝕜] e i := by
  simp [sumTmulL]

/-- For an orthonormal family `e`, the operator `sumTmulL e` preserves inner products. -/
lemma inner_sumTmulL_sumTmulL {e : ι → H₂} (he : Orthonormal 𝕜 e)
    (ξ ξ' : PiLp 2 (fun _ : ι => H₁)) :
    ⟪(sumTmulL e ξ : H₁ ⊗[𝕜] H₂), sumTmulL e ξ'⟫_𝕜 = ⟪ξ, ξ'⟫_𝕜 := by
  classical
  simp_rw [sumTmulL_apply, sum_inner, inner_sum, inner_tmul, orthonormal_iff_ite.1 he, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, PiLp.inner_apply]

/-- For an orthonormal family `e`, the operator `sumTmulL e` is isometric. -/
lemma norm_sumTmulL_apply {e : ι → H₂} (he : Orthonormal 𝕜 e) (ξ : PiLp 2 (fun _ : ι => H₁)) :
    ‖(sumTmulL e ξ : H₁ ⊗[𝕜] H₂)‖ = ‖ξ‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← inner_self_eq_norm_sq (𝕜 := 𝕜),
    ← inner_self_eq_norm_sq (𝕜 := 𝕜), inner_sumTmulL_sumTmulL he]

/-- The matrix of `A ⊗ B` between the ranges of `sumTmulL e`: its `(i, j)` block is
`⟪eᵢ, B eⱼ⟫ • A`. -/
lemma inner_sumTmulL_mapL (e : ι → H₂) (A : H₁ →L[𝕜] H₁) (B : H₂ →L[𝕜] H₂)
    (ξ ξ' : PiLp 2 (fun _ : ι => H₁)) :
    ⟪(sumTmulL e ξ : H₁ ⊗[𝕜] H₂), mapL A B (sumTmulL e ξ')⟫_𝕜 =
      ∑ i, ∑ j, ⟪ξ i, A (ξ' j)⟫_𝕜 * ⟪e i, B (e j)⟫_𝕜 := by
  simp_rw [sumTmulL_apply, map_sum, mapL_tmul, sum_inner, inner_sum, inner_tmul]

/-- Any two vectors of the tensor product lie in the range of `sumTmulL e` for one finite
orthonormal family `e`. -/
lemma exists_sumTmulL_eq (p q : H₁ ⊗[𝕜] H₂) :
    ∃ (n : ℕ) (e : Fin n → H₂), Orthonormal 𝕜 e ∧ ∃ ξ ξ' : PiLp 2 (fun _ : Fin n => H₁),
      sumTmulL e ξ = p ∧ sumTmulL e ξ' = q := by
  obtain ⟨N, hN, hsub⟩ :=
    exists_finite_submodule_right_of_setFinite ({p, q} : Set (H₁ ⊗[𝕜] H₂)) (Set.toFinite _)
  obtain ⟨p', rfl⟩ := hsub (Set.mem_insert _ _)
  obtain ⟨q', rfl⟩ := hsub (Set.mem_insert_of_mem _ rfl)
  let b := stdOrthonormalBasis 𝕜 N
  have key (r : H₁ ⊗[𝕜] N) : ∃ ξ : PiLp 2 (fun _ : Fin (Module.finrank 𝕜 N) => H₁),
      sumTmulL (fun i => (b i : H₂)) ξ = N.subtype.lTensor H₁ r := by
    obtain ⟨c, rfl⟩ := eq_repr_basis_right b.toBasis r
    refine ⟨WithLp.toLp 2 c, ?_⟩
    rw [sumTmulL_apply, Finsupp.sum_fintype _ _ (by simp), map_sum]
    simp
  obtain ⟨ξ, hξ⟩ := key p'
  obtain ⟨ξ', hξ'⟩ := key q'
  exact ⟨_, fun i => (b i : H₂), b.orthonormal.comp_linearIsometry N.subtypeₗᵢ, ξ, ξ', hξ, hξ'⟩

end TensorProduct

namespace ContinuousLinearMap

open TensorProduct

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜] {H₁ H₂ : Type*}
  [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]

/-- An operator `T` on the completed tensor product has norm at most `C ≥ 0` as soon as its
compressions to the ranges of the isometries `TensorProduct.sumTmulL e`, for the finite orthonormal
families `e` of the second factor, do: `‖⟪V ξ, T (V ξ')⟫‖ ≤ C * ‖ξ‖ * ‖ξ'‖` for `V = sumTmulL e`. -/
lemma opNorm_le_of_forall_inner_sumTmulL
    (T : Completion (H₁ ⊗[𝕜] H₂) →L[𝕜] Completion (H₁ ⊗[𝕜] H₂)) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ (n : ℕ) (e : Fin n → H₂), Orthonormal 𝕜 e → ∀ ξ ξ' : PiLp 2 (fun _ : Fin n => H₁),
      ‖⟪((sumTmulL e ξ : H₁ ⊗[𝕜] H₂) : Completion (H₁ ⊗[𝕜] H₂)),
        T (sumTmulL e ξ' : H₁ ⊗[𝕜] H₂)⟫_𝕜‖ ≤ C * ‖ξ‖ * ‖ξ'‖) : ‖T‖ ≤ C := by
  have hinner (u v : Completion (H₁ ⊗[𝕜] H₂)) : ‖⟪u, T v⟫_𝕜‖ ≤ C * ‖u‖ * ‖v‖ := by
    induction u, v using Completion.induction_on₂ with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih p q =>
      obtain ⟨n, e, he, ξ, ξ', rfl, rfl⟩ := exists_sumTmulL_eq p q
      rw [Completion.norm_coe, Completion.norm_coe, norm_sumTmulL_apply he, norm_sumTmulL_apply he]
      exact h n e he ξ ξ'
  refine T.opNorm_le_bound hC fun v => ?_
  by_cases hTv : T v = 0
  · rw [hTv, norm_zero]
    positivity
  have hv := hinner (T v) v
  rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm, sq,
    mul_right_comm C] at hv
  exact le_of_mul_le_mul_right hv (norm_pos_iff.2 hTv)

end ContinuousLinearMap

/-! ### `Completion (ℓ²(ι) ⊗[𝕜] K) ≃ ℓ²(ι, K)`

The completed tensor product of `ℓ²(ι) = lp (fun _ : ι => 𝕜) 2` with a Hilbert space `K` is the
`ℓ²` sum of `ι`-many copies of `K`: the inclusions `k ↦ δᵢ ⊗ k` form an orthogonal family whose
total span is dense, a Hilbert sum (`IsHilbertSum`). -/

namespace lp

open scoped ENNReal lp

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [DecidableEq ι] {K : Type*} [NormedAddCommGroup K]
  [InnerProductSpace 𝕜 K]

/-- The isometric inclusion `K → Completion (ℓ²(ι) ⊗[𝕜] K)`, `k ↦ δᵢ ⊗ k`, where
`δᵢ = lp.single 2 i 1`. -/
noncomputable def tmulSingleₗᵢ (i : ι) :
    K →ₗᵢ[𝕜] Completion (ℓ²(ι, 𝕜) ⊗[𝕜] K) where
  toFun k := ((lp.single 2 i (1 : 𝕜) ⊗ₜ[𝕜] k : ℓ²(ι, 𝕜) ⊗[𝕜] K) : Completion (ℓ²(ι, 𝕜) ⊗[𝕜] K))
  map_add' k k' := by rw [TensorProduct.tmul_add, Completion.coe_add]
  map_smul' c k := by rw [RingHom.id_apply, TensorProduct.tmul_smul, Completion.coe_smul]
  norm_map' k := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Completion.norm_coe, TensorProduct.norm_tmul]
    rw [lp.norm_single (p := 2) (by norm_num), norm_one, one_mul]

/-- `tmulSingleₗᵢ i` sends `k` to the pure tensor `δᵢ ⊗ k`, where `δᵢ = lp.single 2 i 1`. -/
@[simp] lemma tmulSingleₗᵢ_apply (i : ι) (k : K) :
    tmulSingleₗᵢ i k =
      ((lp.single 2 i (1 : 𝕜) ⊗ₜ[𝕜] k : ℓ²(ι, 𝕜) ⊗[𝕜] K) : Completion (ℓ²(ι, 𝕜) ⊗[𝕜] K)) := rfl

/-- Distinct standard basis vectors of `ℓ²(ι)` are orthogonal, so the inclusions `tmulSingleₗᵢ`
form an orthogonal family. -/
lemma orthogonalFamily_tmulSingleₗᵢ :
    OrthogonalFamily 𝕜 (fun _ : ι => K) (fun i => tmulSingleₗᵢ (K := K) i) := by
  intro i j hij k k'
  have hδ : ⟪(lp.single 2 i (1 : 𝕜) : ℓ²(ι, 𝕜)), lp.single 2 j (1 : 𝕜)⟫_𝕜 = 0 := by
    rw [lp.inner_single_left, lp.coeFn_single, Pi.single_eq_of_ne hij, inner_zero_right]
  rw [tmulSingleₗᵢ_apply, tmulSingleₗᵢ_apply, Completion.inner_coe, TensorProduct.inner_tmul, hδ,
    zero_mul]

/-- The orthogonal family `tmulSingleₗᵢ` has dense total span: a pure tensor `a ⊗ k` is the sum of
the series `∑ᵢ (a i) • (δᵢ ⊗ k)`. -/
lemma isHilbertSum_tmulSingleₗᵢ [CompleteSpace K] :
    IsHilbertSum 𝕜 (fun _ : ι => K) (fun i => tmulSingleₗᵢ (K := K) i) := by
  have : ∀ _ : ι, CompleteSpace K := fun _ => inferInstance
  refine IsHilbertSum.mk orthogonalFamily_tmulSingleₗᵢ ?_
  set M : Submodule 𝕜 (Completion (ℓ²(ι, 𝕜) ⊗[𝕜] K)) :=
    ⨆ i, LinearMap.range (tmulSingleₗᵢ (K := K) i).toLinearMap with hM
  have key : ∀ z : ℓ²(ι, 𝕜) ⊗[𝕜] K, (z : Completion (ℓ²(ι, 𝕜) ⊗[𝕜] K)) ∈ M.topologicalClosure := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add p q hp hq =>
        rw [Completion.coe_add]
        exact (M.topologicalClosure).add_mem hp hq
    | tmul a k =>
        let ι₁ : ℓ²(ι, 𝕜) →L[𝕜] Completion (ℓ²(ι, 𝕜) ⊗[𝕜] K) :=
          Completion.toComplL ∘L (TensorProduct.mkL 𝕜 _ K).flip k
        have hsum : HasSum (fun i => ι₁ (lp.single 2 i (a i))) (ι₁ a) :=
          (lp.hasSum_single (E := fun _ : ι => 𝕜) (p := 2) (by norm_num) a).mapL ι₁
        have hmem : ∀ i, ι₁ (lp.single 2 i (a i)) ∈ M := by
          intro i
          have heq : ι₁ (lp.single 2 i (a i)) = (a i) • tmulSingleₗᵢ (K := K) i k := by
            rw [show (lp.single 2 i (a i) : ℓ²(ι, 𝕜)) = (a i) • lp.single 2 i (1 : 𝕜) by
                rw [← lp.single_smul, smul_eq_mul, mul_one], map_smul]
            rfl
          rw [heq]
          exact Submodule.smul_mem _ _
            (Submodule.mem_iSup_of_mem i (LinearMap.mem_range_self _ k))
        have hcl : ι₁ a ∈ closure (M : Set (Completion (ℓ²(ι, 𝕜) ⊗[𝕜] K))) :=
          mem_closure_of_tendsto hsum
            (Filter.Eventually.of_forall fun s =>
              SetLike.mem_coe.mpr (Submodule.sum_mem _ fun i _ => hmem i))
        rwa [← Submodule.topologicalClosure_coe, SetLike.mem_coe] at hcl
  have hsub : Set.range ((↑) : (ℓ²(ι, 𝕜) ⊗[𝕜] K) →
      Completion (ℓ²(ι, 𝕜) ⊗[𝕜] K)) ⊆
      (M.topologicalClosure : Set _) := by
    rintro _ ⟨z, rfl⟩
    exact key z
  rw [top_le_iff]
  apply SetLike.coe_injective
  rw [Submodule.top_coe]
  apply Set.eq_univ_of_univ_subset
  rw [← Completion.denseRange_coe.closure_range]
  exact closure_minimal hsub M.isClosed_topologicalClosure

variable (𝕜) in
/-- The `ℓ²` sum of `ι`-many copies of a Hilbert space `K` is isometrically the completed tensor
product `Completion (ℓ²(ι) ⊗[𝕜] K)`; the single `lp.single 2 i k` corresponds to the pure tensor
`δᵢ ⊗ k` (`completionTensorEquiv_single`). -/
noncomputable def completionTensorEquiv [CompleteSpace K] :
    ℓ²(ι, K) ≃ₗᵢ[𝕜] Completion (ℓ²(ι, 𝕜) ⊗[𝕜] K) :=
  isHilbertSum_tmulSingleₗᵢ.linearIsometryEquiv.symm

/-- `completionTensorEquiv` sends the single `lp.single 2 i k` to the pure tensor `δᵢ ⊗ k`. -/
@[simp] lemma completionTensorEquiv_single [CompleteSpace K] (i : ι) (k : K) :
    completionTensorEquiv 𝕜 (lp.single 2 i k) =
      ((lp.single 2 i (1 : 𝕜) ⊗ₜ[𝕜] k : ℓ²(ι, 𝕜) ⊗[𝕜] K) : Completion (ℓ²(ι, 𝕜) ⊗[𝕜] K)) := by
  rw [completionTensorEquiv,
    IsHilbertSum.linearIsometryEquiv_symm_apply_single isHilbertSum_tmulSingleₗᵢ,
    tmulSingleₗᵢ_apply]

end lp
