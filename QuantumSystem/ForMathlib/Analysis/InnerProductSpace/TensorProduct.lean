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
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# Tensor products of inner product spaces and their completion

## The algebraic tensor product

Supplements to Mathlib's `Mathlib/Analysis/InnerProductSpace/TensorProduct.lean` for bounded
operators on the inner product space `E ⊗[𝕜] G`: the amplification `A ↦ A ⊗ 1` as a
⋆-homomorphism, tensor products of rank-one operators, and the adjoints of the insertions
`y ↦ x ⊗ y` and `x ↦ x ⊗ y`.

The operator tensor product `A ⊗ B` of `A : E →L[𝕜] F` and `B : G →L[𝕜] H` is Mathlib's
`TensorProduct.mapL A B`, and the amplification `A ⊗ 1` is `A.rTensor G`.

The statements that involve an adjoint on `E ⊗[𝕜] G` assume that algebraic tensor product complete,
as Mathlib's `TensorProduct.adjoint_mapL` does; the positivity of `A ⊗ B` needs no completeness. It is complete when one
factor is finite-dimensional and the other complete
(`TensorProduct.completeSpace_of_finiteDimensional_left`,
`TensorProduct.completeSpace_of_finiteDimensional_right`); for Hilbert spaces in general the
statements are those on the completion `UniformSpace.Completion (E ⊗[𝕜] G)`.

Nested tensor products `E ⊗ (F ⊗ G)` and `(E ⊗ F) ⊗ G` get shortcut instances for their normed
structures, without which the C⋆-algebra and Loewner order of their operators are not found
(see the section *Nested tensor products*).

## The completed tensor product

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

## The algebraic tensor product as its own completion

When `E ⊗[𝕜] G` is complete — when one factor is finite-dimensional and the other complete — the
embedding into its completion is an isometric equivalence
(`UniformSpace.Completion.linearIsometryEquivOfComplete`), and the completion of an operator is its
conjugate by it (`ContinuousLinearMap.completion_eq_conj`). The operators on the completed tensor
product are then those on the algebraic one: the amplifications and the product map on the
completion are the conjugates of those on `E ⊗[𝕜] G`
(`ContinuousLinearMap.rTensorCompletionStarAlgHom_eq_conj`,
`ContinuousLinearMap.lTensorCompletionStarAlgHom_eq_conj`,
`TensorProduct.mapLCompletionStarAlgHom_eq_conj`). The statements on `E ⊗[𝕜] G` are in this sense
the finite-dimensional case of those on the completion.

## Main definitions

* `ContinuousLinearMap.rTensorStarAlgHom 𝕜 E G` — the amplification `A ↦ A ⊗ 1 = A.rTensor G` as a
  unital ⋆-homomorphism `B(E) →⋆ₐ B(E ⊗ G)`; `ContinuousLinearMap.lTensorStarAlgHom 𝕜 E G` — the
  amplification `A ↦ 1 ⊗ A = A.lTensor G`, `B(E) →⋆ₐ B(G ⊗ E)`.
* `TensorProduct.mapLEquiv 𝕜 E F G H` — for finite-dimensional `E` and `G`, the linear
  equivalence `(E →L F) ⊗ (G →L H) ≃ (E ⊗ G →L F ⊗ H)`, `f ⊗ g ↦ mapL f g`; so linear maps out
  of `E ⊗ G →L F ⊗ H` are determined on the `mapL f g` (`TensorProduct.ext_mapL`).
* `TensorProduct.mapLStarAlgHom 𝕜 E G` — for a complete algebraic tensor product `E ⊗[𝕜] G`, the
  product map `B(E) ⊗ B(G) →⋆ₐ B(E ⊗ G)`, `f ⊗ g ↦ mapL f g`, a unital ⋆-homomorphism.
* `TensorProduct.mapLStarAlgEquiv 𝕜 E G` — for finite-dimensional `E` and `G`, the product map as a
  `⋆`-algebra equivalence `B(E) ⊗ B(G) ≃⋆ₐ B(E ⊗ G)`: it is `TensorProduct.mapLEquiv`.

* `LinearIsometryEquiv.completion` — the completion of a semilinear isometric equivalence, the
  equivalence form of Mathlib's `LinearIsometry.completion`.
* `LinearIsometry.completionEquivOfDenseRange f hf` — for a linear isometry `f : E → F` with dense
  range, the isometric equivalence `Completion E ≃ₗᵢ Completion F` extending it.
* `TensorProduct.completionLeftEquiv 𝕜 E F`, `TensorProduct.completionRightEquiv 𝕜 E F` —
  `Completion (E ⊗ F) ≃ₗᵢ Completion (Completion E ⊗ F)` and
  `Completion (E ⊗ F) ≃ₗᵢ Completion (E ⊗ Completion F)`, the identity on `E ⊗ F`.
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
* `UniformSpace.Completion.linearIsometryEquivOfComplete` — for a complete space `E`, the embedding
  `E ≃ₗᵢ Completion E`.

## Main statements

* `TensorProduct.mapL_rankOne_rankOne` — `|x⟩⟨y| ⊗ |z⟩⟨w| = |x ⊗ z⟩⟨y ⊗ w|`.
* `TensorProduct.adjoint_mkL_apply_tmul` — the adjoint of the insertion `y ↦ x ⊗ y` is the
  partial inner product `x' ⊗ y' ↦ ⟪x, x'⟫ • y'`.
* `TensorProduct.adjoint_flip_mkL_apply_tmul` — the adjoint of the insertion `x ↦ x ⊗ y` is the
  partial inner product `x' ⊗ y' ↦ ⟪y, y'⟫ • x'`.
* `TensorProduct.mapL_rankOne_left` — `|x⟩⟨y| ⊗ B = ιₓ B ι_y†` for the insertions `ιₓ : z ↦ x ⊗ z`.
* `TensorProduct.lTensor_comp_mkL` — `(1 ⊗ A) ιₓ = ιₓ A`.
* `TensorProduct.rTensor_rankOne_eq_sum`, `TensorProduct.lTensor_rankOne_eq_sum` —
  `|x⟩⟨y| ⊗ 1 = Σⱼ |x ⊗ bⱼ⟩⟨y ⊗ bⱼ|` and its mirror image.
* `TensorProduct.trace_mapL` — `tr(A ⊗ B) = tr A · tr B`.
* `TensorProduct.mapL_nonneg`, `ContinuousLinearMap.completion_mapL_nonneg` — the tensor product of
  positive operators is positive, on the algebraic and on the completed tensor product, over `ℝ` or
  `ℂ`; `ContinuousLinearMap.IsPositive.completion` — the completion of a positive operator is
  positive.
* `TensorProduct.adjoint_mkL_comp_mkL`, `TensorProduct.sum_mkL_comp_adjoint_mkL` — `ιₓ† ι_y = ⟪x, y⟫`,
  and `Σᵢ ι_{bᵢ} ι_{bᵢ}† = 1` along an orthonormal basis `b`.
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
* `LinearIsometryEquiv.opNorm_eq_of_intertwine` — operators intertwined by an isometric
  equivalence have the same norm.
* `TensorProduct.denseRange_mapIsometry_toComplₗᵢ_id`,
  `TensorProduct.denseRange_mapIsometry_id_toComplₗᵢ` — `E ⊗ F` is dense in `Completion E ⊗ F` and
  in `E ⊗ Completion F`.
* `TensorProduct.completionLeftEquiv_mapL`, `TensorProduct.completionRightEquiv_mapL` — these
  identifications intertwine `S ⊗ T` with `S.completion ⊗ T` and with `S ⊗ T.completion`.
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
* `ContinuousLinearMap.completion_eq_conj` — on a complete space, the completion of an operator is
  its conjugate by `UniformSpace.Completion.linearIsometryEquivOfComplete`.
* `ContinuousLinearMap.rTensorCompletionStarAlgHom_eq_conj`,
  `ContinuousLinearMap.lTensorCompletionStarAlgHom_eq_conj`,
  `TensorProduct.mapLCompletionStarAlgHom_eq_conj` — for a complete algebraic tensor product, the
  amplifications and the product map on the completion are those on `E ⊗[𝕜] G`.

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

The notations always denote operators on the completed tensor product. In the prose and docstrings
on the algebraic tensor product, `A ⊗ B`, `A ⊗ 1` and `1 ⊗ B` abbreviate `TensorProduct.mapL A B`,
`A.rTensor G` and `B.lTensor E`, which have no notation.
-/

@[expose] public section

/-! ## Operators on the algebraic tensor product -/

section Algebraic


open scoped TensorProduct InnerProductSpace InnerProduct

variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-! ### Nested tensor products

The type `E ⊗[𝕜] (F ⊗[𝕜] G)` carries, for its inner factor `F ⊗ G`, the algebraic instances
`TensorProduct.addCommMonoid` and `TensorProduct.instModule`, whereas Mathlib's
`TensorProduct.instNormedAddCommGroup` and `TensorProduct.instInnerProductSpace` state their
conclusion with the factor's additive and module structure projected from its normed structure.
Unifying the two triggers a nested instance search for `NormedAddCommGroup (F ⊗ G)`. When the
outer search was itself started inside a unification (as for `ContinuousSMul`, the Loewner order or
`CStarAlgebra` on `E ⊗ (F ⊗ G) →L E ⊗ (F ⊗ G)`), this nested search runs at depth 2 and exceeds
the default `maxSynthPendingDepth = 1`, so these instances are not found. The shortcut instances
below state the normed structures with the nested type as it is elaborated, so that no nested
search is needed; their values are Mathlib's instances. They make the C⋆-algebra structure and the
order of `(E ⊗ F) ⊗ G →L[ℂ] (E ⊗ F) ⊗ G` available anywhere.

`set_option maxSynthPendingDepth 2 in` is the other workaround. The shortcuts do not cover
composites of generic constructions at nested types, which still time out at depth `1`.

TODO: fix the instance statements upstream so that nested tensor products of inner product spaces
need no shortcut, and remove these. Only one level of nesting (three factors) is covered. -/

namespace TensorProduct

/-- Shortcut instance for the right-nested tensor product `E ⊗ (F ⊗ G)`; see the section doc. -/
noncomputable instance instNormedAddCommGroupTensorRight :
    NormedAddCommGroup (E ⊗[𝕜] (F ⊗[𝕜] G)) :=
  TensorProduct.instNormedAddCommGroup

/-- Shortcut instance for the right-nested tensor product `E ⊗ (F ⊗ G)`; see the section doc. -/
noncomputable instance instInnerProductSpaceTensorRight :
    InnerProductSpace 𝕜 (E ⊗[𝕜] (F ⊗[𝕜] G)) :=
  TensorProduct.instInnerProductSpace

/-- Shortcut instance for the left-nested tensor product `(E ⊗ F) ⊗ G`; see the section doc. -/
noncomputable instance instNormedAddCommGroupTensorLeft :
    NormedAddCommGroup ((E ⊗[𝕜] F) ⊗[𝕜] G) :=
  TensorProduct.instNormedAddCommGroup

/-- Shortcut instance for the left-nested tensor product `(E ⊗ F) ⊗ G`; see the section doc. -/
noncomputable instance instInnerProductSpaceTensorLeft :
    InnerProductSpace 𝕜 ((E ⊗[𝕜] F) ⊗[𝕜] G) :=
  TensorProduct.instInnerProductSpace

end TensorProduct

/-! ### Finite sums of pure tensors along a family of the second factor -/

namespace TensorProduct

variable {ι : Type*} [Fintype ι]

/-- The operator `(ξᵢ)ᵢ ↦ ∑ᵢ ξᵢ ⊗ eᵢ` from the Hilbert sum of `ι` copies of `E` to the tensor
product `E ⊗[𝕜] F`, for a finite family `e : ι → F`. -/
noncomputable def sumTmulL (e : ι → F) : PiLp 2 (fun _ : ι => E) →L[𝕜] E ⊗[𝕜] F :=
  ∑ i, (mkL 𝕜 E F).flip (e i) ∘L PiLp.proj 2 (fun _ : ι => E) i

/-- `sumTmulL e` sends `(ξᵢ)ᵢ` to `∑ᵢ ξᵢ ⊗ eᵢ`. -/
lemma sumTmulL_apply (e : ι → F) (ξ : PiLp 2 (fun _ : ι => E)) :
    sumTmulL e ξ = ∑ i, ξ i ⊗ₜ[𝕜] e i := by
  simp [sumTmulL]

/-- For an orthonormal family `e`, the operator `sumTmulL e` preserves inner products. -/
lemma inner_sumTmulL_sumTmulL {e : ι → F} (he : Orthonormal 𝕜 e)
    (ξ ξ' : PiLp 2 (fun _ : ι => E)) :
    ⟪(sumTmulL e ξ : E ⊗[𝕜] F), sumTmulL e ξ'⟫_𝕜 = ⟪ξ, ξ'⟫_𝕜 := by
  classical
  simp_rw [sumTmulL_apply, sum_inner, inner_sum, inner_tmul, orthonormal_iff_ite.1 he, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, PiLp.inner_apply]

/-- For an orthonormal family `e`, the operator `sumTmulL e` is isometric. -/
lemma norm_sumTmulL_apply {e : ι → F} (he : Orthonormal 𝕜 e) (ξ : PiLp 2 (fun _ : ι => E)) :
    ‖(sumTmulL e ξ : E ⊗[𝕜] F)‖ = ‖ξ‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← inner_self_eq_norm_sq (𝕜 := 𝕜),
    ← inner_self_eq_norm_sq (𝕜 := 𝕜), inner_sumTmulL_sumTmulL he]

/-- The matrix of `A ⊗ B` between the ranges of `sumTmulL e`: its `(i, j)` block is
`⟪eᵢ, B eⱼ⟫ • A`. -/
lemma inner_sumTmulL_mapL (e : ι → F) (A : E →L[𝕜] E) (B : F →L[𝕜] F)
    (ξ ξ' : PiLp 2 (fun _ : ι => E)) :
    ⟪(sumTmulL e ξ : E ⊗[𝕜] F), mapL A B (sumTmulL e ξ')⟫_𝕜 =
      ∑ i, ∑ j, ⟪ξ i, A (ξ' j)⟫_𝕜 * ⟪e i, B (e j)⟫_𝕜 := by
  simp_rw [sumTmulL_apply, map_sum, mapL_tmul, sum_inner, inner_sum, inner_tmul]

/-- Any two vectors of the tensor product lie in the range of `sumTmulL e` for one finite
orthonormal family `e`. -/
lemma exists_sumTmulL_eq (p q : E ⊗[𝕜] F) :
    ∃ (n : ℕ) (e : Fin n → F), Orthonormal 𝕜 e ∧ ∃ ξ ξ' : PiLp 2 (fun _ : Fin n => E),
      sumTmulL e ξ = p ∧ sumTmulL e ξ' = q := by
  obtain ⟨N, hN, hsub⟩ :=
    exists_finite_submodule_right_of_setFinite ({p, q} : Set (E ⊗[𝕜] F)) (Set.toFinite _)
  obtain ⟨p', rfl⟩ := hsub (Set.mem_insert _ _)
  obtain ⟨q', rfl⟩ := hsub (Set.mem_insert_of_mem _ rfl)
  let b := stdOrthonormalBasis 𝕜 N
  have key (r : E ⊗[𝕜] N) : ∃ ξ : PiLp 2 (fun _ : Fin (Module.finrank 𝕜 N) => E),
      sumTmulL (fun i => (b i : F)) ξ = N.subtype.lTensor E r := by
    obtain ⟨c, rfl⟩ := eq_repr_basis_right b.toBasis r
    refine ⟨WithLp.toLp 2 c, ?_⟩
    rw [sumTmulL_apply, Finsupp.sum_fintype _ _ (by simp), map_sum]
    simp
  obtain ⟨ξ, hξ⟩ := key p'
  obtain ⟨ξ', hξ'⟩ := key q'
  exact ⟨_, fun i => (b i : F), b.orthonormal.comp_linearIsometry N.subtypeₗᵢ, ξ, ξ', hξ, hξ'⟩

/-- A vector of the tensor product lies in the range of `sumTmulL e` for a finite family `e` on
which a given positive operator `B` of the second factor is diagonal with nonnegative entries: an
orthonormal basis of eigenvectors of the compression of `B` to a finite-dimensional subspace. -/
lemma exists_sumTmulL_eq_of_isPositive {B : F →L[𝕜] F} (hB : B.IsPositive) (p : E ⊗[𝕜] F) :
    ∃ (n : ℕ) (e : Fin n → F) (c : Fin n → ℝ), (∀ i, 0 ≤ c i) ∧
      (∀ i j, ⟪e i, B (e j)⟫_𝕜 = if i = j then (c i : 𝕜) else 0) ∧
      ∃ ξ : PiLp 2 (fun _ : Fin n => E), sumTmulL e ξ = p := by
  obtain ⟨N, hN, hsub⟩ :=
    exists_finite_submodule_right_of_setFinite ({p} : Set (E ⊗[𝕜] F)) (Set.finite_singleton _)
  obtain ⟨p', rfl⟩ := hsub (Set.mem_singleton _)
  let T : N →ₗ[𝕜] N := N.orthogonalProjectionOnto.toLinearMap ∘ₗ B.toLinearMap ∘ₗ N.subtype
  have hinner (x y : N) : ⟪x, T y⟫_𝕜 = ⟪(x : F), B y⟫_𝕜 :=
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left x (B y)
  have hT : T.IsPositive := by
    refine ⟨fun x y => ?_, fun x => ?_⟩
    · rw [hinner, ← inner_conj_symm, hinner, inner_conj_symm]
      exact hB.isSymmetric x y
    · rw [← inner_conj_symm, RCLike.conj_re, hinner]
      exact hB.re_inner_nonneg_right x
  let b := hT.isSymmetric.eigenvectorBasis rfl
  refine ⟨_, fun i => (b i : F), hT.isSymmetric.eigenvalues rfl, hT.nonneg_eigenvalues rfl,
    fun i j => ?_, ?_⟩
  · rw [← hinner, hT.isSymmetric.apply_eigenvectorBasis, inner_smul_right,
      orthonormal_iff_ite.1 b.orthonormal]
    split_ifs with h
    · rw [h, mul_one]
    · rw [mul_zero]
  · obtain ⟨c, rfl⟩ := eq_repr_basis_right b.toBasis p'
    refine ⟨WithLp.toLp 2 c, ?_⟩
    rw [sumTmulL_apply, Finsupp.sum_fintype _ _ (by simp), map_sum]
    simp

end TensorProduct

/-! ### Completeness with a finite-dimensional factor

The algebraic tensor product of a complete inner product space and a finite-dimensional one is
complete, the isometries `TensorProduct.sumTmulL` along an orthonormal basis being onto. -/

namespace TensorProduct

/-- `E ⊗[𝕜] F` is complete when `E` is complete and `F` is finite-dimensional: along an
orthonormal basis `b` of `F`, `sumTmulL b` is an isometry of the Hilbert sum of copies of `E` onto
`E ⊗ F`. -/
instance completeSpace_of_finiteDimensional_right [CompleteSpace E] [FiniteDimensional 𝕜 F] :
    CompleteSpace (E ⊗[𝕜] F) := by
  classical
  let b := stdOrthonormalBasis 𝕜 F
  have hsurj : Function.Surjective (sumTmulL (𝕜 := 𝕜) (E := E) fun i => b i) := fun z => by
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      refine ⟨WithLp.toLp 2 fun i => b.repr y i • x, ?_⟩
      rw [sumTmulL_apply]
      calc ∑ i, (b.repr y i • x) ⊗ₜ[𝕜] b i = ∑ i, x ⊗ₜ[𝕜] (b.repr y i • b i) :=
            Finset.sum_congr rfl fun i _ => by rw [TensorProduct.smul_tmul]
        _ = x ⊗ₜ[𝕜] ∑ i, b.repr y i • b i := (TensorProduct.tmul_sum _ _ _).symm
        _ = x ⊗ₜ[𝕜] y := by rw [b.sum_repr]
    | add p q hp hq =>
      obtain ⟨x, rfl⟩ := hp
      obtain ⟨y, rfl⟩ := hq
      exact ⟨x + y, map_add _ x y⟩
  exact ((LinearIsometryEquiv.ofSurjective ⟨(sumTmulL (𝕜 := 𝕜) (E := E) fun i => b i).toLinearMap,
    norm_sumTmulL_apply b.orthonormal⟩ hsurj).symm.toIsometryEquiv).completeSpace

/-- `E ⊗[𝕜] F` is complete when `E` is finite-dimensional and `F` is complete. -/
instance completeSpace_of_finiteDimensional_left [FiniteDimensional 𝕜 E] [CompleteSpace F] :
    CompleteSpace (E ⊗[𝕜] F) :=
  ((TensorProduct.commIsometry 𝕜 E F).toIsometryEquiv).completeSpace

end TensorProduct

namespace ContinuousLinearMap

variable (𝕜 E G) in
/-- The **amplification** `A ↦ A ⊗ 1 = A.rTensor G` as a unital ⋆-homomorphism
`B(E) →⋆ₐ B(E ⊗ G)`, for `E ⊗[𝕜] G` complete. It is the identity representation of `B(E)` with
multiplicity `G`. -/
noncomputable def rTensorStarAlgHom [CompleteSpace E] [CompleteSpace G]
    [CompleteSpace (E ⊗[𝕜] G)] : (E →L[𝕜] E) →⋆ₐ[𝕜] (E ⊗[𝕜] G →L[𝕜] E ⊗[𝕜] G) where
  toFun A := A.rTensor G
  map_one' := rTensor_one G
  map_mul' A B := rTensor_mul G A B
  map_zero' := rTensor_zero G
  map_add' A B := rTensor_add G A B
  commutes' r := by simp [Algebra.algebraMap_eq_smul_one]
  map_star' A := by simp [star_eq_adjoint]

/-- The amplification sends `A` to `A ⊗ 1 = A.rTensor G`. -/
@[simp] lemma rTensorStarAlgHom_apply [CompleteSpace E] [CompleteSpace G]
    [CompleteSpace (E ⊗[𝕜] G)] (A : E →L[𝕜] E) : rTensorStarAlgHom 𝕜 E G A = A.rTensor G :=
  rfl

variable (𝕜 E G) in
/-- The **amplification** `A ↦ 1 ⊗ A = A.lTensor G` as a unital ⋆-homomorphism
`B(E) →⋆ₐ B(G ⊗ E)`, for `G ⊗[𝕜] E` complete, with the multiplicity space on the left. -/
noncomputable def lTensorStarAlgHom [CompleteSpace E] [CompleteSpace G]
    [CompleteSpace (G ⊗[𝕜] E)] : (E →L[𝕜] E) →⋆ₐ[𝕜] (G ⊗[𝕜] E →L[𝕜] G ⊗[𝕜] E) where
  toFun A := A.lTensor G
  map_one' := lTensor_one G
  map_mul' A B := lTensor_mul G A B
  map_zero' := lTensor_zero G
  map_add' A B := lTensor_add G A B
  commutes' r := by simp [Algebra.algebraMap_eq_smul_one]
  map_star' A := by simp [star_eq_adjoint]

/-- The amplification sends `A` to `1 ⊗ A = A.lTensor G`. -/
@[simp] lemma lTensorStarAlgHom_apply [CompleteSpace E] [CompleteSpace G]
    [CompleteSpace (G ⊗[𝕜] E)] (A : E →L[𝕜] E) : lTensorStarAlgHom 𝕜 E G A = A.lTensor G :=
  rfl

end ContinuousLinearMap

namespace TensorProduct

open InnerProductSpace

/-- The tensor product of rank-one operators is rank-one: `|x⟩⟨y| ⊗ |z⟩⟨w| = |x ⊗ z⟩⟨y ⊗ w|`. -/
lemma mapL_rankOne_rankOne (x : E) (y : F) (z : G) (w : H) :
    mapL (rankOne 𝕜 x y) (rankOne 𝕜 z w) = rankOne 𝕜 (x ⊗ₜ[𝕜] z) (y ⊗ₜ[𝕜] w) := by
  refine ContinuousLinearMap.coe_inj.mp <| ext' fun u v => ?_
  simp [TensorProduct.smul_tmul', smul_smul, mul_comm]

/-- The adjoint of the insertion `mkL 𝕜 E F x : y ↦ x ⊗ y` is the partial inner product
`x' ⊗ y' ↦ ⟪x, x'⟫ • y'`. -/
lemma adjoint_mkL_apply_tmul [CompleteSpace F] [CompleteSpace (E ⊗[𝕜] F)] (x x' : E) (y : F) :
    ((mkL 𝕜 E F x)†) (x' ⊗ₜ y) = ⟪x, x'⟫_𝕜 • y :=
  ext_inner_left 𝕜 fun w => by
    rw [ContinuousLinearMap.adjoint_inner_right, mkL_apply_apply, inner_tmul, inner_smul_right]

/-- The adjoint of the insertion `(mkL 𝕜 E F).flip y : x ↦ x ⊗ y` is the partial inner product
`x' ⊗ y' ↦ ⟪y, y'⟫ • x'`. -/
lemma adjoint_flip_mkL_apply_tmul [CompleteSpace E] [CompleteSpace (E ⊗[𝕜] F)] (y y' : F)
    (x : E) : (((mkL 𝕜 E F).flip y)†) (x ⊗ₜ y') = ⟪y, y'⟫_𝕜 • x :=
  ext_inner_left 𝕜 fun w => by
    rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.flip_apply, mkL_apply_apply,
      inner_tmul, inner_smul_right, mul_comm]

variable (𝕜 E F G H) in
/-- For finite-dimensional `E` and `G`, operators on `E ⊗ G` are tensors of operators: the linear
equivalence `(E →L F) ⊗ (G →L H) ≃ (E ⊗ G →L F ⊗ H)`, `f ⊗ g ↦ mapL f g`
(`TensorProduct.mapLEquiv_tmul`), the continuous form of Mathlib's `homTensorHomEquiv`. -/
noncomputable def mapLEquiv [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 G] :
    (E →L[𝕜] F) ⊗[𝕜] (G →L[𝕜] H) ≃ₗ[𝕜] (E ⊗[𝕜] G →L[𝕜] F ⊗[𝕜] H) :=
  (TensorProduct.congr LinearMap.toContinuousLinearMap.symm
    LinearMap.toContinuousLinearMap.symm).trans
      ((homTensorHomEquiv 𝕜 E G F H).trans LinearMap.toContinuousLinearMap)

/-- `mapLEquiv` sends `f ⊗ g` to the operator tensor product `mapL f g`. -/
@[simp] lemma mapLEquiv_tmul [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 G] (f : E →L[𝕜] F)
    (g : G →L[𝕜] H) : mapLEquiv 𝕜 E F G H (f ⊗ₜ g) = mapL f g := by
  refine ContinuousLinearMap.coe_inj.mp <| ext' fun x y => ?_
  simp [mapLEquiv]

/-- Two linear maps out of `E ⊗ G →L F ⊗ H` agree if they agree on the operator tensors
`mapL f g`, which span it (`TensorProduct.mapLEquiv`). -/
lemma ext_mapL [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 G] {M : Type*} [AddCommGroup M]
    [Module 𝕜 M] {u v : (E ⊗[𝕜] G →L[𝕜] F ⊗[𝕜] H) →ₗ[𝕜] M}
    (h : ∀ (f : E →L[𝕜] F) (g : G →L[𝕜] H), u (mapL f g) = v (mapL f g)) : u = v := by
  refine LinearMap.ext fun X => ?_
  obtain ⟨z, rfl⟩ := (mapLEquiv 𝕜 E F G H).surjective X
  induction z using TensorProduct.inductionOn with
  | tmul f g => rw [mapLEquiv_tmul, h]
  | add z z' hz hz' => rw [map_add, map_add, map_add, hz, hz']

variable (𝕜 E G) in
/-- The **product map** `B(E) ⊗ B(G) → B(E ⊗ G)`, `f ⊗ g ↦ mapL f g`, of the algebraic tensor
product of the operator algebras into the operators on a complete algebraic tensor product
`E ⊗[𝕜] G`, as a unital `⋆`-algebra homomorphism. -/
noncomputable def mapLStarAlgHom [CompleteSpace E] [CompleteSpace G] [CompleteSpace (E ⊗[𝕜] G)] :
    (E →L[𝕜] E) ⊗[𝕜] (G →L[𝕜] G) →⋆ₐ[𝕜] (E ⊗[𝕜] G →L[𝕜] E ⊗[𝕜] G) where
  toFun := TensorProduct.lift <| LinearMap.mk₂ 𝕜 (fun f g => mapL f g)
    (fun f f' g => by rw [mapL_add_left]) (fun c f g => by rw [mapL_smul_left])
    (fun f g g' => by rw [mapL_add_right]) (fun c f g => by rw [mapL_smul_right])
  map_one' := by
    rw [Algebra.TensorProduct.one_def, lift.tmul, LinearMap.mk₂_apply]
    simp only [ContinuousLinearMap.one_def, mapL_id_id]
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' r := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one, lift.tmul,
      LinearMap.mk₂_apply, mapL_smul_left, Algebra.algebraMap_eq_smul_one]
    simp only [ContinuousLinearMap.one_def, mapL_id_id]
  map_mul' x y := by
    induction x using TensorProduct.inductionOn with
    | tmul f g =>
      induction y using TensorProduct.inductionOn with
      | tmul f' g' =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, lift.tmul, LinearMap.mk₂_apply, mapL_mul]
      | add p q hp hq => rw [mul_add, map_add, hp, hq, map_add, mul_add]
    | add p q hp hq => rw [add_mul, map_add, hp, hq, map_add, add_mul]
  map_star' x := by
    induction x using TensorProduct.inductionOn with
    | tmul f g =>
      simp only [star_tmul, lift.tmul, LinearMap.mk₂_apply, ContinuousLinearMap.star_eq_adjoint,
        adjoint_mapL]
    | add p q hp hq => rw [star_add, map_add, hp, hq, map_add, ← star_add]

/-- The product map sends `f ⊗ g` to the operator tensor product `mapL f g`. -/
@[simp] lemma mapLStarAlgHom_tmul [CompleteSpace E] [CompleteSpace G] [CompleteSpace (E ⊗[𝕜] G)]
    (f : E →L[𝕜] E) (g : G →L[𝕜] G) : mapLStarAlgHom 𝕜 E G (f ⊗ₜ g) = mapL f g :=
  rfl

/-- For finite-dimensional factors the product map is the linear equivalence
`TensorProduct.mapLEquiv`. -/
lemma mapLStarAlgHom_eq_mapLEquiv [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 G]
    [CompleteSpace E] [CompleteSpace G] (x : (E →L[𝕜] E) ⊗[𝕜] (G →L[𝕜] G)) :
    mapLStarAlgHom 𝕜 E G x = mapLEquiv 𝕜 E E G G x := by
  induction x using TensorProduct.inductionOn with
  | tmul f g => rw [mapLStarAlgHom_tmul, mapLEquiv_tmul]
  | add p q hp hq => rw [map_add, map_add, hp, hq]

variable (𝕜 E G) in
/-- For finite-dimensional `E` and `G`, the product map `TensorProduct.mapLStarAlgHom` of
`B(E) ⊗ B(G)` into `B(E ⊗ G)`, `f ⊗ g ↦ mapL f g`, is a `⋆`-algebra equivalence: it is the linear
equivalence `TensorProduct.mapLEquiv`. -/
noncomputable def mapLStarAlgEquiv [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 G]
    [CompleteSpace E] [CompleteSpace G] :
    (E →L[𝕜] E) ⊗[𝕜] (G →L[𝕜] G) ≃⋆ₐ[𝕜] (E ⊗[𝕜] G →L[𝕜] E ⊗[𝕜] G) :=
  StarAlgEquiv.ofBijective (mapLStarAlgHom 𝕜 E G) <| by
    rw [funext mapLStarAlgHom_eq_mapLEquiv]
    exact (mapLEquiv 𝕜 E E G G).bijective

/-- `mapLStarAlgEquiv` is the product map `mapLStarAlgHom`. -/
lemma mapLStarAlgEquiv_apply [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 G]
    [CompleteSpace E] [CompleteSpace G] (x : (E →L[𝕜] E) ⊗[𝕜] (G →L[𝕜] G)) :
    mapLStarAlgEquiv 𝕜 E G x = mapLStarAlgHom 𝕜 E G x :=
  rfl

/-- `mapLStarAlgEquiv` sends `f ⊗ g` to the operator tensor product `mapL f g`. -/
@[simp] lemma mapLStarAlgEquiv_tmul [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 G]
    [CompleteSpace E] [CompleteSpace G] (f : E →L[𝕜] E) (g : G →L[𝕜] G) :
    mapLStarAlgEquiv 𝕜 E G (f ⊗ₜ g) = mapL f g :=
  rfl

/-- The tensor product of a rank-one operator with an operator `B` factors through the insertions
`ιₓ = mkL 𝕜 E H x : z ↦ x ⊗ z`: `|x⟩⟨y| ⊗ B = ιₓ B ι_y†`. -/
lemma mapL_rankOne_left [CompleteSpace G] [CompleteSpace (F ⊗[𝕜] G)] (x : E) (y : F)
    (B : G →L[𝕜] H) :
    mapL (rankOne 𝕜 x y) B = mkL 𝕜 E H x ∘L B ∘L (mkL 𝕜 F G y)† := by
  refine ContinuousLinearMap.coe_inj.mp <| ext' fun u v => ?_
  simp [adjoint_mkL_apply_tmul, smul_tmul]

/-- The insertion `ιₓ : z ↦ x ⊗ z` intertwines `A` with `1 ⊗ A`: `(1 ⊗ A) ιₓ = ιₓ A`. -/
lemma lTensor_comp_mkL (x : E) (A : G →L[𝕜] H) :
    A.lTensor E ∘L mkL 𝕜 E G x = mkL 𝕜 E H x ∘L A := by
  ext z
  simp

/-- The insertions are orthogonal: `ιₓ† ι_y = ⟪x, y⟫ • 1`. -/
lemma adjoint_mkL_comp_mkL [CompleteSpace F] [CompleteSpace (E ⊗[𝕜] F)] (x y : E) :
    (mkL 𝕜 E F x)† ∘L mkL 𝕜 E F y = ⟪x, y⟫_𝕜 • (1 : F →L[𝕜] F) := by
  ext v
  simp [adjoint_mkL_apply_tmul]

/-- **Resolution of the identity** on `E ⊗ F` along an orthonormal basis `b` of `E`:
`Σᵢ ι_{bᵢ} ι_{bᵢ}† = 1`, that is, `z = Σᵢ bᵢ ⊗ ι_{bᵢ}† z`. -/
lemma sum_mkL_comp_adjoint_mkL [CompleteSpace F] [CompleteSpace (E ⊗[𝕜] F)] {ι : Type*}
    [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) :
    ∑ i, mkL 𝕜 E F (b i) ∘L (mkL 𝕜 E F (b i))† = 1 := by
  refine ContinuousLinearMap.coe_inj.mp <| ext' fun u v => ?_
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.toLinearMap_sum,
    LinearMap.coe_sum, Finset.sum_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    adjoint_mkL_apply_tmul, mkL_apply_apply, one_apply_eq_self]
  simp_rw [← smul_tmul, ← sum_tmul, b.sum_repr']

/-- `|x⟩⟨y| ⊗ 1 = Σⱼ |x ⊗ bⱼ⟩⟨y ⊗ bⱼ|` along an orthonormal basis `b` of the second factor. -/
lemma rTensor_rankOne_eq_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι 𝕜 G) (x y : E) :
    (rankOne 𝕜 x y).rTensor G = ∑ j, rankOne 𝕜 (x ⊗ₜ[𝕜] b j) (y ⊗ₜ[𝕜] b j) := by
  refine ContinuousLinearMap.coe_inj.mp <| ext' fun u v => ?_
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.rTensor_tmul, rankOne_apply,
    ContinuousLinearMap.toLinearMap_sum, LinearMap.coe_sum, Finset.sum_apply, inner_tmul]
  conv_lhs => rw [← b.sum_repr' v, tmul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [tmul_smul, ← smul_tmul', smul_smul]
  rw [mul_comm]

/-- `1 ⊗ |x⟩⟨y| = Σᵢ |bᵢ ⊗ x⟩⟨bᵢ ⊗ y|` along an orthonormal basis `b` of the first factor. -/
lemma lTensor_rankOne_eq_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) (x y : G) :
    (rankOne 𝕜 x y).lTensor E = ∑ i, rankOne 𝕜 (b i ⊗ₜ[𝕜] x) (b i ⊗ₜ[𝕜] y) := by
  refine ContinuousLinearMap.coe_inj.mp <| ext' fun u v => ?_
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.lTensor_tmul, rankOne_apply,
    ContinuousLinearMap.toLinearMap_sum, LinearMap.coe_sum, Finset.sum_apply, inner_tmul]
  conv_lhs => rw [← b.sum_repr' u, sum_tmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [tmul_smul, ← smul_tmul', smul_smul]
  rw [mul_comm]

/-- The trace is multiplicative on operator tensor products: `tr(A ⊗ B) = tr A · tr B`
(`LinearMap.trace_tensorProduct'`). -/
lemma trace_mapL [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 G] (A : E →L[𝕜] E)
    (B : G →L[𝕜] G) :
    LinearMap.trace 𝕜 (E ⊗[𝕜] G) (mapL A B) = LinearMap.trace 𝕜 E A * LinearMap.trace 𝕜 G B := by
  rw [toLinearMap_mapL, LinearMap.trace_tensorProduct']

/-- The tensor product of symmetric operators is symmetric. -/
lemma isSymmetric_mapL {A : E →L[𝕜] E} {B : G →L[𝕜] G} (hA : (A : E →ₗ[𝕜] E).IsSymmetric)
    (hB : (B : G →ₗ[𝕜] G).IsSymmetric) : (mapL A B : E ⊗[𝕜] G →ₗ[𝕜] E ⊗[𝕜] G).IsSymmetric := by
  intro z w
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    induction w using TensorProduct.inductionOn with
    | tmul x' y' =>
      have h₁ : ⟪A x, x'⟫_𝕜 = ⟪x, A x'⟫_𝕜 := hA x x'
      have h₂ : ⟪B y, y'⟫_𝕜 = ⟪y, B y'⟫_𝕜 := hB y y'
      simp only [ContinuousLinearMap.coe_coe, mapL_tmul, inner_tmul, h₁, h₂]
    | add w w' hw hw' => simp only [map_add, inner_add_right, hw, hw']
  | add z z' hz hz' => simp only [map_add, inner_add_left, hz, hz']

/-- **The tensor product of positive operators is positive**, on the algebraic tensor product of
inner product spaces over `ℝ` or `ℂ`, complete or not: a vector is `∑ᵢ ξᵢ ⊗ eᵢ` for a finite family
`e` on which `B` is diagonal with entries `cᵢ ≥ 0`
(`TensorProduct.exists_sumTmulL_eq_of_isPositive`), and then
`⟪z, (A ⊗ B) z⟫ = ∑ᵢ cᵢ ⟪ξᵢ, A ξᵢ⟫`. -/
theorem mapL_nonneg {A : E →L[𝕜] E} {B : G →L[𝕜] G} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ mapL A B := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive] at hA hB ⊢
  have hsymm := isSymmetric_mapL hA.isSymmetric hB.isSymmetric
  refine ⟨hsymm, fun z => ?_⟩
  obtain ⟨n, e, c, hc, he, ξ, rfl⟩ := exists_sumTmulL_eq_of_isPositive hB z
  have hz : ⟪mapL A B (sumTmulL e ξ), (sumTmulL e ξ : E ⊗[𝕜] G)⟫_𝕜 =
      ∑ i, ⟪ξ i, A (ξ i)⟫_𝕜 * (c i : 𝕜) := by
    rw [← ContinuousLinearMap.coe_coe, hsymm, ContinuousLinearMap.coe_coe, inner_sumTmulL_mapL]
    simp only [he, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, hz, map_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [RCLike.re_mul_ofReal]
  exact mul_nonneg (hA.re_inner_nonneg_right (ξ i)) (hc i)

end TensorProduct

end Algebraic

/-! ## Operators on the completed tensor product -/

section Completed


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

namespace LinearIsometryEquiv

variable {𝕜 V W : Type*} [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [SeminormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- Operators intertwined by a linear isometric equivalence, `U ∘ X = Z ∘ U`, have the same
norm. -/
lemma opNorm_eq_of_intertwine (U : V ≃ₗᵢ[𝕜] W) {X : V →L[𝕜] V} {Z : W →L[𝕜] W}
    (h : ∀ v, U (X v) = Z (U v)) : ‖X‖ = ‖Z‖ := by
  refine le_antisymm (X.opNorm_le_bound (norm_nonneg Z) fun v => ?_)
    (Z.opNorm_le_bound (norm_nonneg X) fun w => ?_)
  · rw [← U.norm_map, h, ← U.norm_map v]
    exact Z.le_opNorm _
  · obtain ⟨v, rfl⟩ := U.surjective w
    rw [← h, U.norm_map, U.norm_map]
    exact X.le_opNorm v

end LinearIsometryEquiv

namespace LinearIsometry

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The completion of a linear isometry with dense range is onto: its range is complete, hence
closed, and dense. -/
lemma completion_surjective_of_denseRange {f : E →ₗᵢ[𝕜] F} (hf : DenseRange f) :
    Function.Surjective f.completion := by
  have hcl : IsClosed (Set.range f.completion) :=
    f.completion.isometry.isUniformInducing.isComplete_range.isClosed
  have hd : Dense (Set.range f.completion) :=
    (Completion.denseRange_coe.comp hf (Completion.continuous_coe F)).mono (by
      rintro _ ⟨x, rfl⟩
      exact ⟨x, f.completion_apply_coe x⟩)
  exact Set.range_eq_univ.1 (hcl.closure_eq.symm.trans hd.closure_eq)

/-- The completion of a linear isometry with dense range, a linear isometric equivalence
`Completion E ≃ₗᵢ[𝕜] Completion F`. -/
noncomputable def completionEquivOfDenseRange (f : E →ₗᵢ[𝕜] F) (hf : DenseRange f) :
    Completion E ≃ₗᵢ[𝕜] Completion F :=
  LinearIsometryEquiv.ofSurjective f.completion (completion_surjective_of_denseRange hf)

/-- `f.completionEquivOfDenseRange hf` extends `f`. -/
@[simp] lemma completionEquivOfDenseRange_coe (f : E →ₗᵢ[𝕜] F) (hf : DenseRange f) (x : E) :
    f.completionEquivOfDenseRange hf (x : Completion E) = (f x : Completion F) :=
  f.completion_apply_coe x

end LinearIsometry

namespace TensorProduct

open scoped TensorProduct

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- `E ⊗[𝕜] F` is dense in `Completion E ⊗[𝕜] F`. -/
lemma denseRange_mapIsometry_toComplₗᵢ_id :
    DenseRange (mapIsometry (Completion.toComplₗᵢ : E →ₗᵢ[𝕜] Completion E)
      (LinearIsometry.id : F →ₗᵢ[𝕜] F)) := by
  set R := LinearMap.range (mapIsometry (Completion.toComplₗᵢ : E →ₗᵢ[𝕜] Completion E)
    (LinearIsometry.id : F →ₗᵢ[𝕜] F)).toLinearMap
  set S := R.topologicalClosure
  have hS (z : Completion E ⊗[𝕜] F) : z ∈ S := by
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      refine Completion.induction_on x
        (R.isClosed_topologicalClosure.preimage ((mkL 𝕜 (Completion E) F).flip y).continuous)
        fun e => ?_
      exact R.le_topologicalClosure ⟨e ⊗ₜ y, by simp [Completion.coe_toComplₗᵢ]⟩
    | add z z' hz hz' => exact S.add_mem hz hz'
  intro z
  have h := hS z
  rwa [← SetLike.mem_coe, Submodule.topologicalClosure_coe, LinearMap.coe_range] at h

/-- `E ⊗[𝕜] F` is dense in `E ⊗[𝕜] Completion F`. -/
lemma denseRange_mapIsometry_id_toComplₗᵢ :
    DenseRange (mapIsometry (LinearIsometry.id : E →ₗᵢ[𝕜] E)
      (Completion.toComplₗᵢ : F →ₗᵢ[𝕜] Completion F)) := by
  set R := LinearMap.range (mapIsometry (LinearIsometry.id : E →ₗᵢ[𝕜] E)
    (Completion.toComplₗᵢ : F →ₗᵢ[𝕜] Completion F)).toLinearMap
  set S := R.topologicalClosure
  have hS (z : E ⊗[𝕜] Completion F) : z ∈ S := by
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      refine Completion.induction_on y
        (R.isClosed_topologicalClosure.preimage (mkL 𝕜 E (Completion F) x).continuous)
        fun e => ?_
      exact R.le_topologicalClosure ⟨x ⊗ₜ e, by simp [Completion.coe_toComplₗᵢ]⟩
    | add z z' hz hz' => exact S.add_mem hz hz'
  intro z
  have h := hS z
  rwa [← SetLike.mem_coe, Submodule.topologicalClosure_coe, LinearMap.coe_range] at h

variable (𝕜 E F) in
/-- The Hilbert space tensor product of `Completion E` and `F` is that of `E` and `F`:
`Completion (E ⊗ F) ≃ₗᵢ Completion (Completion E ⊗ F)`, the identity on `E ⊗ F`. -/
noncomputable def completionLeftEquiv :
    Completion (E ⊗[𝕜] F) ≃ₗᵢ[𝕜] Completion (Completion E ⊗[𝕜] F) :=
  (mapIsometry (Completion.toComplₗᵢ : E →ₗᵢ[𝕜] Completion E)
    (LinearIsometry.id : F →ₗᵢ[𝕜] F)).completionEquivOfDenseRange
    denseRange_mapIsometry_toComplₗᵢ_id

/-- `TensorProduct.completionLeftEquiv 𝕜 E F` sends `x ⊗ y` to `x ⊗ y`. -/
@[simp] lemma completionLeftEquiv_coe_tmul (x : E) (y : F) :
    completionLeftEquiv 𝕜 E F (↑(x ⊗ₜ[𝕜] y) : Completion (E ⊗[𝕜] F)) =
      (↑((x : Completion E) ⊗ₜ[𝕜] y) : Completion (Completion E ⊗[𝕜] F)) := by
  simp [completionLeftEquiv, Completion.coe_toComplₗᵢ]

variable (𝕜 E F) in
/-- The Hilbert space tensor product of `E` and `Completion F` is that of `E` and `F`:
`Completion (E ⊗ F) ≃ₗᵢ Completion (E ⊗ Completion F)`, the identity on `E ⊗ F`. -/
noncomputable def completionRightEquiv :
    Completion (E ⊗[𝕜] F) ≃ₗᵢ[𝕜] Completion (E ⊗[𝕜] Completion F) :=
  (mapIsometry (LinearIsometry.id : E →ₗᵢ[𝕜] E)
    (Completion.toComplₗᵢ : F →ₗᵢ[𝕜] Completion F)).completionEquivOfDenseRange
    denseRange_mapIsometry_id_toComplₗᵢ

/-- `TensorProduct.completionRightEquiv 𝕜 E F` sends `x ⊗ y` to `x ⊗ y`. -/
@[simp] lemma completionRightEquiv_coe_tmul (x : E) (y : F) :
    completionRightEquiv 𝕜 E F (↑(x ⊗ₜ[𝕜] y) : Completion (E ⊗[𝕜] F)) =
      (↑(x ⊗ₜ[𝕜] (y : Completion F)) : Completion (E ⊗[𝕜] Completion F)) := by
  simp [completionRightEquiv, Completion.coe_toComplₗᵢ]

/-- `TensorProduct.completionLeftEquiv 𝕜 E F` intertwines the operator `S ⊗ T` with
`S.completion ⊗ T`. -/
lemma completionLeftEquiv_mapL (S : E →L[𝕜] E) (T : F →L[𝕜] F) (v : Completion (E ⊗[𝕜] F)) :
    completionLeftEquiv 𝕜 E F ((mapL S T).completion v) =
      (mapL S.completion T).completion (completionLeftEquiv 𝕜 E F v) := by
  induction v using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih q =>
    rw [ContinuousLinearMap.completion_apply_coe]
    induction q using TensorProduct.inductionOn with
    | tmul x y => simp [ContinuousLinearMap.completion_apply_coe]
    | add p q hp hq => simp only [map_add, Completion.coe_add, hp, hq]

/-- `TensorProduct.completionRightEquiv 𝕜 E F` intertwines the operator `S ⊗ T` with
`S ⊗ T.completion`. -/
lemma completionRightEquiv_mapL (S : E →L[𝕜] E) (T : F →L[𝕜] F) (v : Completion (E ⊗[𝕜] F)) :
    completionRightEquiv 𝕜 E F ((mapL S T).completion v) =
      (mapL S T.completion).completion (completionRightEquiv 𝕜 E F v) := by
  induction v using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih q =>
    rw [ContinuousLinearMap.completion_apply_coe]
    induction q using TensorProduct.inductionOn with
    | tmul x y => simp [ContinuousLinearMap.completion_apply_coe]
    | add p q hp hq => simp only [map_add, Completion.coe_add, hp, hq]

end TensorProduct

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

variable (R E F) in
/-- The completion `f ↦ f.completion` of continuous linear maps, as a linear map. -/
noncomputable def completionₗ : (E →L[R] F) →ₗ[R] (Completion E →L[R] Completion F) where
  toFun := ContinuousLinearMap.completion
  map_add' := completion_add
  map_smul' := completion_smul

/-- `completionₗ R E F f = f.completion`. -/
@[simp] lemma completionₗ_apply (f : E →L[R] F) : completionₗ R E F f = f.completion := rfl

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

/-- **The completion of a positive operator is positive**: symmetry and the positivity of
`re ⟪T x, x⟫` pass to the completion by density. -/
theorem IsPositive.completion {T : E →L[𝕜] E} (hT : T.IsPositive) : T.completion.IsPositive := by
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · induction x, y using Completion.induction_on₂ with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih a b =>
      simp only [coe_coe, completion_apply_coe, Completion.inner_coe]
      exact hT.isSymmetric a b
  · induction x using Completion.induction_on with
    | hp =>
      simp only [reApplyInnerSelf_apply]
      exact isClosed_le continuous_const (by fun_prop)
    | ih a =>
      rw [reApplyInnerSelf_apply, completion_apply_coe, Completion.inner_coe]
      exact hT.re_inner_nonneg_left a

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
lemma completion_mapL_eq_comp (A : H₁ →L[𝕜] H₃) (B : H₂ →L[𝕜] H₄) :
    A ⊗ B = (A ⊗ 𝟙[H₄]) ∘L (𝟙[H₁] ⊗ B) :=
  completion_comp _ _

/-- The adjoint of `A ⊗ B` on the completed tensor product is `A† ⊗ B†`. -/
lemma adjoint_completion_mapL [CompleteSpace H₁] [CompleteSpace H₂] [CompleteSpace H₃]
    [CompleteSpace H₄] (A : H₁ →L[𝕜] H₃) (B : H₂ →L[𝕜] H₄) :
    (A ⊗ B)† = A† ⊗ B† := by
  rw [completion_mapL_eq_comp, adjoint_comp, adjoint_completion_rTensor, adjoint_completion_lTensor,
    ← completion_comp, lTensor_comp_rTensor]

/-- **The tensor product of positive operators is positive** on the Hilbert space tensor product,
the completion of the algebraic tensor product, over `ℝ` or `ℂ`: the completion of a positive
operator is positive (`ContinuousLinearMap.IsPositive.completion`). -/
theorem completion_mapL_nonneg {A : H₁ →L[𝕜] H₁} {B : H₂ →L[𝕜] H₂} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ A ⊗ B :=
  nonneg_iff_isPositive.2 (nonneg_iff_isPositive.1 (TensorProduct.mapL_nonneg hA hB)).completion

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
    rw [completion_mapL_eq_comp, completion_rTensor_rankOne, completion_rTensor_rankOne,
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

/-! ### `ℓ²(ι, K) ≃ Completion (ℓ²(ι) ⊗[𝕜] K)`

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

end Completed

/-! ## The algebraic tensor product as its own completion -/

section OwnCompletion

open scoped TensorProduct
open UniformSpace

namespace UniformSpace.Completion

variable {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

variable (𝕜 E) in
/-- For a complete normed space `E`, the embedding into its completion is an isometric
equivalence: its range is complete, hence closed, and it is dense. -/
noncomputable def linearIsometryEquivOfComplete : E ≃ₗᵢ[𝕜] Completion E :=
  LinearIsometryEquiv.ofSurjective (toComplₗᵢ (𝕜 := 𝕜) (E := E)) fun y => by
    have hcl : IsClosed (Set.range ((↑) : E → Completion E)) :=
      coe_isometry.isClosedEmbedding.isClosed_range
    exact Set.eq_univ_iff_forall.mp (hcl.closure_eq ▸ denseRange_coe.closure_range) y

/-- `UniformSpace.Completion.linearIsometryEquivOfComplete 𝕜 E` is the embedding into the
completion. -/
@[simp] lemma linearIsometryEquivOfComplete_apply (x : E) :
    linearIsometryEquivOfComplete 𝕜 E x = (x : Completion E) :=
  rfl

end UniformSpace.Completion

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- **On a complete space, the completion of an operator is its conjugate by the embedding into the
completion**, `UniformSpace.Completion.linearIsometryEquivOfComplete`. -/
lemma completion_eq_conj (T : E →L[𝕜] E) :
    T.completion = (Completion.linearIsometryEquivOfComplete 𝕜 E).conjStarAlgEquiv T := by
  refine ContinuousLinearMap.ext fun y => Completion.induction_on y
    (isClosed_eq (by fun_prop) (by fun_prop)) fun x => ?_
  rw [completion_apply_coe, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  exact congrArg _ (congrArg T
    ((Completion.linearIsometryEquivOfComplete 𝕜 E).symm_apply_apply x).symm)

variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]

/-- **For a complete algebraic tensor product, the amplification `A ↦ A ⊗ 𝟙` on the completion is
the amplification `A ↦ A.rTensor H₂` on `H₁ ⊗[𝕜] H₂`**, read through the embedding into the
completion. -/
lemma rTensorCompletionStarAlgHom_eq_conj [CompleteSpace (H₁ ⊗[𝕜] H₂)] (A : H₁ →L[𝕜] H₁) :
    rTensorCompletionStarAlgHom H₂ A =
      (Completion.linearIsometryEquivOfComplete 𝕜 (H₁ ⊗[𝕜] H₂)).conjStarAlgEquiv
        (rTensorStarAlgHom 𝕜 H₁ H₂ A) :=
  completion_eq_conj _

/-- **For a complete algebraic tensor product, the amplification `B ↦ 𝟙 ⊗ B` on the completion is
the amplification `B ↦ B.lTensor H₁` on `H₁ ⊗[𝕜] H₂`**, read through the embedding into the
completion. -/
lemma lTensorCompletionStarAlgHom_eq_conj [CompleteSpace (H₁ ⊗[𝕜] H₂)] (B : H₂ →L[𝕜] H₂) :
    lTensorCompletionStarAlgHom H₁ B =
      (Completion.linearIsometryEquivOfComplete 𝕜 (H₁ ⊗[𝕜] H₂)).conjStarAlgEquiv
        (lTensorStarAlgHom 𝕜 H₂ H₁ B) :=
  completion_eq_conj _

end ContinuousLinearMap

namespace TensorProduct

variable {𝕜 H₁ H₂ : Type*} [RCLike 𝕜] [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₁] [CompleteSpace H₂]

/-- **For a complete algebraic tensor product, the product map
`B(H₁) ⊗ B(H₂) → B(Completion (H₁ ⊗ H₂))` is the product map `B(H₁) ⊗ B(H₂) → B(H₁ ⊗ H₂)`**,
`TensorProduct.mapLStarAlgHom`, read through the embedding into the completion. For
finite-dimensional factors it is the `⋆`-algebra equivalence `TensorProduct.mapLStarAlgEquiv`. -/
lemma mapLCompletionStarAlgHom_eq_conj [CompleteSpace (H₁ ⊗[𝕜] H₂)]
    (x : (H₁ →L[𝕜] H₁) ⊗[𝕜] (H₂ →L[𝕜] H₂)) :
    mapLCompletionStarAlgHom 𝕜 H₁ H₂ x =
      (Completion.linearIsometryEquivOfComplete 𝕜 (H₁ ⊗[𝕜] H₂)).conjStarAlgEquiv
        (mapLStarAlgHom 𝕜 H₁ H₂ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul f g =>
    rw [mapLCompletionStarAlgHom_tmul, mapLStarAlgHom_tmul]
    exact ContinuousLinearMap.completion_eq_conj _
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

end TensorProduct

end OwnCompletion
