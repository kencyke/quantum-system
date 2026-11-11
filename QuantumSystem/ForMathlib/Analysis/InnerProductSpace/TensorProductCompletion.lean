/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Topology.Algebra.LinearMapCompletion

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

## Main definitions

* `LinearIsometryEquiv.completion` — the completion of a semilinear isometric equivalence, the
  equivalence form of Mathlib's `LinearIsometry.completion`.
* `ContinuousLinearMap.rTensorCompletionStarAlgHom`, `ContinuousLinearMap.lTensorCompletionStarAlgHom`
  — the amplifications of operators on a Hilbert space, as unital `⋆`-algebra homomorphisms into
  the operators on the completed tensor product.
* `lp.completionTensorEquiv` — `ℓ²(ι, K) ≃ₗᵢ Completion (ℓ²(ι) ⊗[𝕜] K)`.

## Main results

* `UniformSpace.Completion.surjective_toComplL`, `FiniteDimensional.completion` — a
  finite-dimensional seminormed space surjects onto its completion, which is therefore
  finite-dimensional.
* `ContinuousLinearMap.completion_comp`, `completion_add`, `completion_smul`, … — the completion of
  continuous linear maps is functorial and linear.
* `ContinuousLinearMap.completion_eq_adjoint` — the completion of a formal adjoint is the adjoint of
  the completion.
* `ContinuousLinearMap.adjoint_completion_rTensor`, `adjoint_completion_lTensor` — the adjoint of an
  amplification is the amplification of the adjoint.
* `ContinuousLinearMap.conjStarAlgEquiv_completion_commIsometry_lTensor` — swapping the factors
  turns `𝟙 ⊗ B` into `B ⊗ 𝟙`.

## Notation

| Symbol | Expansion | How to activate |
|---|---|---|
| `A ⊗ 𝟙[H₂]` | `(A.rTensor H₂).completion` | `open scoped Amplification` |
| `𝟙[H₁] ⊗ B` | `(B.lTensor H₁).completion` | `open scoped Amplification` |
| `⊗ₐ 𝟙[H₂]` | `ContinuousLinearMap.rTensorCompletionStarAlgHom H₂` | `open scoped Amplification` |
| `𝟙[H₁] ⊗ₐ` | `ContinuousLinearMap.lTensorCompletionStarAlgHom H₁` | `open scoped Amplification` |
-/

@[expose] public section

open scoped TensorProduct InnerProduct

open UniformSpace

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
@[simp] lemma completion_coe (f : E ≃ₛₗᵢ[σ₁₂] F) (a : E) :
    f.completion (a : Completion E) = (f a : Completion F) :=
  f.toLinearIsometry.completion_apply_coe a

/-- The inverse of `f.completion` is the completion of `f.symm`. -/
@[simp] lemma completion_symm (f : E ≃ₛₗᵢ[σ₁₂] F) : f.completion.symm = f.symm.completion := rfl

end LinearIsometryEquiv

/-- The coercion `E → Completion E` of a finite-dimensional seminormed space (over a complete
field) is surjective: its image is a finite-dimensional, hence closed, subspace, and it is dense. -/
lemma UniformSpace.Completion.surjective_toComplL {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
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
    Completion.surjective_toComplL

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
lemma completion_eq_adjoint {f : E →L[𝕜] F} {g : F →L[𝕜] E}
    (h : ∀ x y, inner 𝕜 (g x) y = inner 𝕜 x (f y)) : g.completion = f.completion† := by
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro u v
  induction u, v using Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih a b => rw [completion_apply_coe, completion_apply_coe, Completion.inner_coe,
      Completion.inner_coe, h]

end Adjoint

/-! ### Amplifications on the completed tensor product -/

variable {𝕜 : Type*} [RCLike 𝕜] {H₁ H₂ H₃ H₄ : Type*}
  [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
  [NormedAddCommGroup H₃] [InnerProductSpace 𝕜 H₃]
  [NormedAddCommGroup H₄] [InnerProductSpace 𝕜 H₄]

/-- On pure tensors the formal adjoint of `A.rTensor H₂` is `A†.rTensor H₂`. -/
private lemma inner_adjoint_rTensor [CompleteSpace H₁] [CompleteSpace H₃] (A : H₁ →L[𝕜] H₃)
    (a : H₃ ⊗[𝕜] H₂) (b : H₁ ⊗[𝕜] H₂) :
    inner 𝕜 ((A†).rTensor H₂ a) b = inner 𝕜 a (A.rTensor H₂ b) := by
  induction a using TensorProduct.inductionOn with
  | tmul x y =>
    induction b using TensorProduct.inductionOn with
    | tmul x' y' => simp [TensorProduct.inner_tmul, adjoint_inner_left]
    | add p q hp hq => simp only [inner_add_right, map_add, hp, hq]
  | add p q hp hq => simp only [inner_add_left, map_add, hp, hq]

/-- On pure tensors the formal adjoint of `B.lTensor H₁` is `B†.lTensor H₁`. -/
private lemma inner_adjoint_lTensor [CompleteSpace H₂] [CompleteSpace H₄] (B : H₂ →L[𝕜] H₄)
    (a : H₁ ⊗[𝕜] H₄) (b : H₁ ⊗[𝕜] H₂) :
    inner 𝕜 ((B†).lTensor H₁ a) b = inner 𝕜 a (B.lTensor H₁ b) := by
  induction a using TensorProduct.inductionOn with
  | tmul x y =>
    induction b using TensorProduct.inductionOn with
    | tmul x' y' => simp [TensorProduct.inner_tmul, adjoint_inner_left]
    | add p q hp hq => simp only [inner_add_right, map_add, hp, hq]
  | add p q hp hq => simp only [inner_add_left, map_add, hp, hq]

/-- The adjoint of the amplification `A ⊗ 𝟙` is `A† ⊗ 𝟙`. -/
lemma adjoint_completion_rTensor [CompleteSpace H₁] [CompleteSpace H₃] (A : H₁ →L[𝕜] H₃) :
    ((A.rTensor H₂).completion)† = ((A†).rTensor H₂).completion :=
  (completion_eq_adjoint (inner_adjoint_rTensor A)).symm

/-- The adjoint of the amplification `𝟙 ⊗ B` is `𝟙 ⊗ B†`. -/
lemma adjoint_completion_lTensor [CompleteSpace H₂] [CompleteSpace H₄] (B : H₂ →L[𝕜] H₄) :
    ((B.lTensor H₁).completion)† = ((B†).lTensor H₁).completion :=
  (completion_eq_adjoint (inner_adjoint_lTensor B)).symm

variable (H₂) in
/-- The **left amplification** `A ↦ A ⊗ 𝟙` of the operators on a Hilbert space `H₁`, as a unital
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
/-- The **right amplification** `B ↦ 𝟙 ⊗ B` of the operators on a Hilbert space `H₂`, as a unital
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

/-- Swapping the factors turns the right amplification `𝟙 ⊗ B` on `Completion (H₁ ⊗[𝕜] H₂)` into
the left amplification `B ⊗ 𝟙` on `Completion (H₂ ⊗[𝕜] H₁)`. -/
lemma conjStarAlgEquiv_completion_commIsometry_lTensor (B : H₂ →L[𝕜] H₂) :
    (TensorProduct.commIsometry 𝕜 H₁ H₂).completion.conjStarAlgEquiv (B.lTensor H₁).completion =
      (B.rTensor H₁).completion := by
  ext w
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  induction w using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih a =>
    rw [LinearIsometryEquiv.completion_symm, LinearIsometryEquiv.completion_coe,
      completion_apply_coe, LinearIsometryEquiv.completion_coe, completion_apply_coe]
    congr 1
    induction a using TensorProduct.inductionOn with
    | tmul y x => simp
    | add p q hp hq => simp only [map_add, hp, hq]

end ContinuousLinearMap

/-- `A ⊗ 𝟙[H₂]` is the amplification `(A.rTensor H₂).completion` of `A : H₁ →L[𝕜] H₃`, the
operator `Completion (H₁ ⊗[𝕜] H₂) →L[𝕜] Completion (H₃ ⊗[𝕜] H₂)`. -/
scoped[Amplification] notation:100 A:101 " ⊗ " "𝟙[" H₂ "]" =>
  ContinuousLinearMap.completion (ContinuousLinearMap.rTensor H₂ A)

/-- `𝟙[H₁] ⊗ B` is the amplification `(B.lTensor H₁).completion` of `B : H₂ →L[𝕜] H₄`, the
operator `Completion (H₁ ⊗[𝕜] H₂) →L[𝕜] Completion (H₁ ⊗[𝕜] H₄)`. -/
scoped[Amplification] notation:100 "𝟙[" H₁ "]" " ⊗ " B:101 =>
  ContinuousLinearMap.completion (ContinuousLinearMap.lTensor H₁ B)

/-- `⊗ₐ 𝟙[H₂]` is the left amplification `A ↦ A ⊗ 𝟙[H₂]` as a `⋆`-algebra homomorphism. -/
scoped[Amplification] notation "⊗ₐ " "𝟙[" H₂ "]" => ContinuousLinearMap.rTensorCompletionStarAlgHom H₂

/-- `𝟙[H₁] ⊗ₐ` is the right amplification `B ↦ 𝟙[H₁] ⊗ B` as a `⋆`-algebra homomorphism. -/
scoped[Amplification] notation "𝟙[" H₁ "]" " ⊗ₐ" => ContinuousLinearMap.lTensorCompletionStarAlgHom H₁

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
  have hδ : inner 𝕜 (lp.single 2 i (1 : 𝕜) : ℓ²(ι, 𝕜)) (lp.single 2 j (1 : 𝕜)) = 0 := by
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
