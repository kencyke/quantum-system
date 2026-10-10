/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The Hilbert–Schmidt inner product on operators between finite-dimensional spaces

For finite-dimensional complex inner product spaces `H` and `K`, the operators `H →L[ℂ] K` form
an inner product space under the **Hilbert–Schmidt inner product** `⟪X, Y⟫ = tr(X† Y)`. Its norm
is the Hilbert–Schmidt (Frobenius) norm, not the operator norm carried by `H →L[ℂ] K`, so the
inner product space is the type synonym `HilbertSchmidt H K`. In finite dimension every operator
is Hilbert–Schmidt; the instances need `FiniteDimensional ℂ H` and `FiniteDimensional ℂ K`.

Operators act on `HilbertSchmidt H K` by multiplication: `B : K →L[ℂ] K` on the left,
`X ↦ B X`, and `A : H →L[ℂ] H` on the right, `X ↦ X A`. Left multiplication is a unital
`⋆`-homomorphism `HilbertSchmidt.leftMul`, right multiplication a unital `⋆`-anti-homomorphism,
written as the `⋆`-homomorphism `HilbertSchmidt.rightMul` into the opposite algebra. The two
commute (`HilbertSchmidt.commute_leftMul_rightMul`).

## Main definitions

* `HilbertSchmidt H K`: the type copy of `H →L[ℂ] K` with the Hilbert–Schmidt inner product.
* `HilbertSchmidt.ofCLM`: the linear equivalence `(H →L[ℂ] K) ≃ₗ[ℂ] HilbertSchmidt H K`.
* `HilbertSchmidt.leftMul`, `HilbertSchmidt.rightMul`: the left and right multiplication
  representations, with the scoped notations `𝐋[H] B` and `𝐑[K] A` for the operators `X ↦ B X`
  and `X ↦ X A` (Effros's `L_B` and `R_A`).

## Main results

* `HilbertSchmidt.inner_ofCLM_ofCLM`: `⟪X, Y⟫ = tr(X† Y)`;
  `HilbertSchmidt.inner_ofCLM_ofCLM_eq_sum`: `⟪X, Y⟫ = ∑ᵢ ⟪X bᵢ, Y bᵢ⟫` for an orthonormal basis
  `b` of `H`.

## TODO

* Generalise to infinite-dimensional `H` and `K`, where the Hilbert–Schmidt operators form a proper
  subspace of `H →L[ℂ] K`, and to `RCLike 𝕜`.
* Turn the type synonym into a one-field structure, as Mathlib's `WithLp`, to rule out defeq abuse.

## Notation

`𝐋[H] B` is `HilbertSchmidt.leftMul H B` and `𝐑[K] A` is
`MulOpposite.unop (HilbertSchmidt.rightMul K A)`; activate them with `open scoped HilbertSchmidt`.
-/

@[expose] public section

noncomputable section

open ContinuousLinearMap
open scoped InnerProductSpace ComplexConjugate

variable (H K : Type*)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The operators `H →L[ℂ] K`, as a type synonym to carry the Hilbert–Schmidt inner product
`⟪X, Y⟫ = tr(X† Y)` instead of the operator norm. The inner product space structure is defined for
finite-dimensional `H` and `K`, where every operator is Hilbert–Schmidt. -/
def HilbertSchmidt := H →L[ℂ] K

namespace HilbertSchmidt

instance : AddCommGroup (HilbertSchmidt H K) := inferInstanceAs (AddCommGroup (H →L[ℂ] K))

instance : Module ℂ (HilbertSchmidt H K) := inferInstanceAs (Module ℂ (H →L[ℂ] K))

/-- The identification of the operators `H →L[ℂ] K` with the Hilbert–Schmidt space. -/
def ofCLM : (H →L[ℂ] K) ≃ₗ[ℂ] HilbertSchmidt H K := LinearEquiv.refl ℂ (H →L[ℂ] K)

variable {H K}

@[simp]
lemma ofCLM_symm_ofCLM (X : H →L[ℂ] K) : (ofCLM H K).symm (ofCLM H K X) = X := rfl

@[simp]
lemma ofCLM_ofCLM_symm (X : HilbertSchmidt H K) : ofCLM H K ((ofCLM H K).symm X) = X := rfl

/-- Induction principle: every element of the Hilbert–Schmidt space is `ofCLM X` for an operator
`X`. -/
@[elab_as_elim]
lemma ofCLM_induction {P : HilbertSchmidt H K → Prop} (h : ∀ X, P (ofCLM H K X))
    (Y : HilbertSchmidt H K) : P Y :=
  h ((ofCLM H K).symm Y)

variable [FiniteDimensional ℂ H] [FiniteDimensional ℂ K]

instance : FiniteDimensional ℂ (HilbertSchmidt H K) :=
  inferInstanceAs (FiniteDimensional ℂ (H →L[ℂ] K))

/-- `tr(X† Y) = ∑ᵢ ⟪X bᵢ, Y bᵢ⟫` for an orthonormal basis `b` of `H`. -/
lemma _root_.ContinuousLinearMap.trace_adjoint_comp_eq_sum {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ H) (X Y : H →L[ℂ] K) :
    LinearMap.trace ℂ H (adjoint X ∘L Y) = ∑ i, ⟪X (b i), Y (b i)⟫_ℂ := by
  rw [LinearMap.trace_eq_sum_inner _ b]
  simp [adjoint_inner_right]

private lemma re_trace_adjoint_comp_self_eq_sum (X : H →L[ℂ] K) :
    RCLike.re (LinearMap.trace ℂ H (adjoint X ∘L X)) =
      ∑ i, ‖X (stdOrthonormalBasis ℂ H i)‖ ^ 2 := by
  rw [ContinuousLinearMap.trace_adjoint_comp_eq_sum (stdOrthonormalBasis ℂ H), map_sum]
  simp only [inner_self_eq_norm_sq]

/-- The Hilbert–Schmidt inner product `⟪X, Y⟫ = tr(X† Y)`. -/
instance instCore : InnerProductSpace.Core ℂ (HilbertSchmidt H K) where
  inner X Y := LinearMap.trace ℂ H (adjoint ((ofCLM H K).symm X) ∘L (ofCLM H K).symm Y)
  conj_inner_symm X Y := by
    rw [ContinuousLinearMap.trace_adjoint_comp_eq_sum (stdOrthonormalBasis ℂ H),
      ContinuousLinearMap.trace_adjoint_comp_eq_sum (stdOrthonormalBasis ℂ H), map_sum]
    simp only [inner_conj_symm]
  re_inner_nonneg X := by
    rw [re_trace_adjoint_comp_self_eq_sum]
    positivity
  add_left X Y Z := by
    rw [ContinuousLinearMap.trace_adjoint_comp_eq_sum (stdOrthonormalBasis ℂ H),
      ContinuousLinearMap.trace_adjoint_comp_eq_sum (stdOrthonormalBasis ℂ H),
      ContinuousLinearMap.trace_adjoint_comp_eq_sum (stdOrthonormalBasis ℂ H),
      ← Finset.sum_add_distrib]
    simp only [map_add, add_apply, inner_add_left]
  smul_left X Y r := by
    rw [ContinuousLinearMap.trace_adjoint_comp_eq_sum (stdOrthonormalBasis ℂ H),
      ContinuousLinearMap.trace_adjoint_comp_eq_sum (stdOrthonormalBasis ℂ H), Finset.mul_sum]
    simp only [map_smul, smul_apply, inner_smul_left]
  definite X h := by
    have h' := congrArg RCLike.re h
    rw [re_trace_adjoint_comp_self_eq_sum, map_zero,
      Finset.sum_eq_zero_iff_of_nonneg fun _ _ => by positivity] at h'
    refine (ofCLM H K).symm.injective ?_
    rw [map_zero]
    exact ContinuousLinearMap.coe_injective <| (stdOrthonormalBasis ℂ H).toBasis.ext fun i => by
      simpa using h' i (Finset.mem_univ i)

instance : NormedAddCommGroup (HilbertSchmidt H K) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

instance : InnerProductSpace ℂ (HilbertSchmidt H K) := InnerProductSpace.ofCore _

instance : CompleteSpace (HilbertSchmidt H K) := FiniteDimensional.complete ℂ _

/-- The Hilbert–Schmidt inner product: `⟪X, Y⟫ = tr(X† Y)`. -/
lemma inner_ofCLM_ofCLM (X Y : H →L[ℂ] K) :
    ⟪ofCLM H K X, ofCLM H K Y⟫_ℂ = LinearMap.trace ℂ H (adjoint X ∘L Y) :=
  rfl

/-- The Hilbert–Schmidt inner product in an orthonormal basis `b` of `H`:
`⟪X, Y⟫ = ∑ᵢ ⟪X bᵢ, Y bᵢ⟫`. -/
lemma inner_ofCLM_ofCLM_eq_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ H)
    (X Y : H →L[ℂ] K) :
    ⟪ofCLM H K X, ofCLM H K Y⟫_ℂ = ∑ i, ⟪X (b i), Y (b i)⟫_ℂ :=
  ContinuousLinearMap.trace_adjoint_comp_eq_sum b X Y

/-! ### Left and right multiplication -/

/-- Composition `X ↦ B X ∘ A` on the Hilbert–Schmidt space, as a linear map. -/
def sandwichₗ (B : K →L[ℂ] K) (A : H →L[ℂ] H) :
    HilbertSchmidt H K →ₗ[ℂ] HilbertSchmidt H K where
  toFun X := ofCLM H K (B ∘L (ofCLM H K).symm X ∘L A)
  map_add' X Y := by simp [comp_add, add_comp]
  map_smul' c X := by simp [smul_comp]

/-- Composition `X ↦ B X ∘ A` on the Hilbert–Schmidt space, as a bounded operator. -/
def sandwich (B : K →L[ℂ] K) (A : H →L[ℂ] H) :
    HilbertSchmidt H K →L[ℂ] HilbertSchmidt H K :=
  LinearMap.toContinuousLinearMap (sandwichₗ B A)

/-- `sandwich B A` acts as `X ↦ B X A`. -/
@[simp]
lemma sandwich_ofCLM (B : K →L[ℂ] K) (A : H →L[ℂ] H) (X : H →L[ℂ] K) :
    sandwich B A (ofCLM H K X) = ofCLM H K (B ∘L X ∘L A) :=
  rfl

/-- `sandwich 1 1` is the identity. -/
lemma sandwich_one_one : sandwich (1 : K →L[ℂ] K) (1 : H →L[ℂ] H) = 1 := by
  ext X : 1
  induction X using ofCLM_induction
  rfl

/-- The Hilbert–Schmidt adjoint of `X ↦ B X A` is `X ↦ B† X A†`, by cyclicity of the trace. -/
lemma adjoint_sandwich (B : K →L[ℂ] K) (A : H →L[ℂ] H) :
    adjoint (sandwich B A) = sandwich (adjoint B) (adjoint A) := by
  symm
  rw [eq_adjoint_iff]
  intro X Y
  induction X using ofCLM_induction with | h X => ?_
  induction Y using ofCLM_induction with | h Y => ?_
  rw [sandwich_ofCLM, sandwich_ofCLM, inner_ofCLM_ofCLM, inner_ofCLM_ofCLM]
  have key (M N : H →L[ℂ] H) :
      LinearMap.trace ℂ H (M ∘L N) = LinearMap.trace ℂ H (N ∘L M) := by
    -- `ContinuousLinearMap.trace_comp_comm'` is in `ForMathlib/.../TraceDual.lean`, which a
    -- `ForMathlib` file cannot import
    rw [toLinearMap_comp, LinearMap.trace_comp_comm', ← toLinearMap_comp]
  simp only [adjoint_comp, adjoint_adjoint, comp_assoc]
  rw [key]
  simp only [comp_assoc]

variable (H) in
/-- Left multiplication `X ↦ B X` on the Hilbert–Schmidt space, as a unital `⋆`-homomorphism. -/
def leftMul : (K →L[ℂ] K) →⋆ₐ[ℂ] (HilbertSchmidt H K →L[ℂ] HilbertSchmidt H K) where
  toFun B := sandwich B 1
  map_one' := sandwich_one_one
  map_mul' B₁ B₂ := by
    ext X : 1
    induction X using ofCLM_induction
    rfl
  map_zero' := by
    ext X : 1
    induction X using ofCLM_induction
    simp
  map_add' B₁ B₂ := by
    ext X : 1
    induction X using ofCLM_induction
    simp only [sandwich_ofCLM, add_apply, add_comp, map_add]
  commutes' c := by
    ext X : 1
    induction X using ofCLM_induction
    rfl
  map_star' B := by
    simp only [star_eq_adjoint, adjoint_sandwich, adjoint_one]

variable (K) in
/-- Right multiplication `X ↦ X A` on the Hilbert–Schmidt space, a unital `⋆`-anti-homomorphism,
as a `⋆`-homomorphism into the opposite algebra. -/
def rightMul :
    (H →L[ℂ] H) →⋆ₐ[ℂ] (HilbertSchmidt H K →L[ℂ] HilbertSchmidt H K)ᵐᵒᵖ where
  toFun A := MulOpposite.op (sandwich 1 A)
  map_one' := by rw [sandwich_one_one, MulOpposite.op_one]
  map_mul' A₁ A₂ := by
    rw [← MulOpposite.op_mul, MulOpposite.op_inj]
    ext X : 1
    induction X using ofCLM_induction
    rfl
  map_zero' := by
    rw [MulOpposite.op_eq_zero_iff]
    ext X : 1
    induction X using ofCLM_induction
    simp
  map_add' A₁ A₂ := by
    rw [← MulOpposite.op_add, MulOpposite.op_inj]
    ext X : 1
    induction X using ofCLM_induction
    simp only [sandwich_ofCLM, add_apply, comp_add, map_add]
  commutes' c := by
    rw [MulOpposite.algebraMap_apply, MulOpposite.op_inj]
    ext X : 1
    induction X using ofCLM_induction
    rw [sandwich_ofCLM, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    simp only [comp_smul, map_smul, smul_apply]
    rfl
  map_star' A := by
    rw [← MulOpposite.op_star, MulOpposite.op_inj, star_eq_adjoint, star_eq_adjoint,
      adjoint_sandwich, adjoint_one]

@[simp]
lemma leftMul_ofCLM (B : K →L[ℂ] K) (X : H →L[ℂ] K) :
    leftMul H B (ofCLM H K X) = ofCLM H K (B ∘L X) :=
  rfl

@[simp]
lemma unop_rightMul_ofCLM (A : H →L[ℂ] H) (X : H →L[ℂ] K) :
    MulOpposite.unop (rightMul K A) (ofCLM H K X) = ofCLM H K (X ∘L A) :=
  rfl

@[inherit_doc] scoped notation "𝐋[" H "]" => HilbertSchmidt.leftMul H

/-- `𝐑[K] A` is right multiplication `X ↦ X A` by `A : H →L[ℂ] H` as an operator on
`HilbertSchmidt H K`. -/
scoped notation "𝐑[" K "] " A:max => MulOpposite.unop (HilbertSchmidt.rightMul K A)

/-- Left and right multiplication commute. -/
lemma commute_leftMul_rightMul (B : K →L[ℂ] K) (A : H →L[ℂ] H) :
    Commute (leftMul H B) (MulOpposite.unop (rightMul K A)) := by
  ext X : 1
  induction X using ofCLM_induction
  rfl

end HilbertSchmidt

end
