/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Unital ⋆-representations of `B(H)`

Let `H` be a finite-dimensional complex Hilbert space and `π : B(H) →⋆ₐ B(L)` a unital
⋆-representation of `B(H) = H →L[ℂ] H` on a Hilbert space `L`, not necessarily finite-dimensional.
Then `π` is a multiple of the identity representation. For a unit vector `ξ₀ ∈ H`, the
**multiplicity space** is the range `range π(|ξ₀⟩⟨ξ₀|) ⊆ L` (`StarAlgHom.multiplicitySpace`).
For every Hilbert space `E` identified with it by an isometry `ι : E → L` onto it, the map
`U : H ⊗ E → L`, `η ⊗ e ↦ π(|η⟩⟨ξ₀|) ι e`, is a unitary (`StarAlgHom.multiplicityEquiv`) with
`π(A) U = U (A ⊗ 1)` (`StarAlgHom.apply_multiplicityEquiv`).

The proof uses only rank-one operators. `U` preserves inner products since
`π(|η⟩⟨ξ₀|)† π(|η'⟩⟨ξ₀|) = ⟪η, η'⟫ π(|ξ₀⟩⟨ξ₀|)` and `π(|ξ₀⟩⟨ξ₀|)` is the identity on its range; it
is onto since `x = π(1) x = Σᵢ π(|bᵢ⟩⟨ξ₀|) π(|ξ₀⟩⟨bᵢ|) x` for an orthonormal basis `b` of `H`, with
`π(|ξ₀⟩⟨bᵢ|) x` in the range of `π(|ξ₀⟩⟨ξ₀|)`; and `π(A) π(|η⟩⟨ξ₀|) = π(|A η⟩⟨ξ₀|)`.

## Main definitions

* `StarAlgHom.multiplicitySpace π ξ₀` — the range of `π(|ξ₀⟩⟨ξ₀|)`.
* `StarAlgHom.multiplicityEquiv hξ₀ ι hι` — the unitary `H ⊗ E ≃ L`,
  `η ⊗ e ↦ π(|η⟩⟨ξ₀|) ι e`.

## Main statements

* `StarAlgHom.multiplicityEquiv_tmul` — `U (η ⊗ e) = π(|η⟩⟨ξ₀|) ι e`.
* `StarAlgHom.apply_multiplicityEquiv` — `π(A) (U z) = U ((A ⊗ 1) z)`: `π` is unitarily equivalent
  to the ampliation `A ↦ A ⊗ 1` on `H ⊗ E`.

## Implementation notes

The multiplicity space enters through an abstract Hilbert space `E` and an isometry `ι : E → L`
onto `range π(|ξ₀⟩⟨ξ₀|)`, rather than as the subspace itself: a tensor factor that is a
`Submodule` carries two instance paths to its additive structure, one through `Submodule` and one
through its normed structure, so that the inner product space lemmas of `H ⊗ E` do not apply to it
by rewriting. The subspace itself is the case `ι = Submodule.subtypeₗᵢ`, and a finite-dimensional
multiplicity space may be taken to be `EuclideanSpace ℂ (Fin d)`.
-/

@[expose] public section

open scoped TensorProduct InnerProductSpace InnerProduct
open InnerProductSpace TensorProduct

namespace StarAlgHom

variable {H L E : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  (π : (H →L[ℂ] H) →⋆ₐ[ℂ] (L →L[ℂ] L))

/-- The **multiplicity space** of a ⋆-representation `π` of `B(H)` at `ξ₀ ∈ H`: the range of
`π(|ξ₀⟩⟨ξ₀|)`. For a unit vector `ξ₀` and unital `π`, `L ≅ H ⊗ E` for any Hilbert space `E`
isometric to it (`StarAlgHom.multiplicityEquiv`). -/
noncomputable def multiplicitySpace (ξ₀ : H) : Submodule ℂ L :=
  LinearMap.range (π (rankOne ℂ ξ₀ ξ₀) : L →ₗ[ℂ] L)

variable {π}

/-- For a unit vector `ξ₀`, `π(|ξ₀⟩⟨ξ₀|)` is the identity on the multiplicity space. -/
lemma apply_rankOne_self_of_mem_multiplicitySpace {ξ₀ : H} (hξ₀ : ‖ξ₀‖ = 1) {e : L}
    (he : e ∈ multiplicitySpace π ξ₀) : π (rankOne ℂ ξ₀ ξ₀) e = e := by
  obtain ⟨x, rfl⟩ := he
  change (π (rankOne ℂ ξ₀ ξ₀) * π (rankOne ℂ ξ₀ ξ₀)) x = π (rankOne ℂ ξ₀ ξ₀) x
  rw [← map_mul, (isIdempotentElem_rankOne_self hξ₀).eq]

/-- `π(|η⟩⟨ξ₀|)† π(|η'⟩⟨ξ₀|) = ⟪η, η'⟫ π(|ξ₀⟩⟨ξ₀|)`. -/
lemma adjoint_apply_rankOne_comp_apply_rankOne (ξ₀ η η' : H) :
    (π (rankOne ℂ η ξ₀))† ∘L π (rankOne ℂ η' ξ₀) =
      ⟪η, η'⟫_ℂ • π (rankOne ℂ ξ₀ ξ₀) := by
  rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, ContinuousLinearMap.star_eq_adjoint,
    adjoint_rankOne, ← ContinuousLinearMap.mul_def, ← map_mul, ContinuousLinearMap.mul_def,
    rankOne_comp_rankOne, map_smul]

/-- `π(|η⟩⟨ξ₀|) π(|ξ₀⟩⟨ζ|) = π(|η⟩⟨ζ|)` for a unit vector `ξ₀`. -/
lemma apply_rankOne_comp_apply_rankOne {ξ₀ : H} (hξ₀ : ‖ξ₀‖ = 1) (η ζ : H) :
    π (rankOne ℂ η ξ₀) ∘L π (rankOne ℂ ξ₀ ζ) = π (rankOne ℂ η ζ) := by
  rw [← ContinuousLinearMap.mul_def, ← map_mul, ContinuousLinearMap.mul_def, rankOne_comp_rankOne,
    inner_self_eq_norm_sq_to_K, hξ₀]
  simp

/-- The bilinear map `(η, e) ↦ π(|η⟩⟨ξ₀|) ι e` underlying `StarAlgHom.multiplicityEquiv`. -/
noncomputable def multiplicityBilin (ξ₀ : H) (ι : E →ₗᵢ[ℂ] L) : H →ₗ[ℂ] E →ₗ[ℂ] L :=
  LinearMap.mk₂ ℂ (fun η e => π (rankOne ℂ η ξ₀) (ι e))
    (fun η η' e => by simp [map_add])
    (fun c η e => by simp [map_smul])
    (fun η e e' => by simp)
    (fun c η e => by simp)

variable {ξ₀ : H} (hξ₀ : ‖ξ₀‖ = 1) (ι : E →ₗᵢ[ℂ] L)
  (hι : LinearMap.range ι.toLinearMap = multiplicitySpace π ξ₀)
include hξ₀ hι

/-- The map `η ⊗ e ↦ π(|η⟩⟨ξ₀|) ι e` preserves inner products: on pure tensors
`⟪π(|η⟩⟨ξ₀|) ι e, π(|η'⟩⟨ξ₀|) ι e'⟫ = ⟪η, η'⟫ ⟪ι e, π(|ξ₀⟩⟨ξ₀|) ι e'⟫ = ⟪η, η'⟫ ⟪e, e'⟫`. -/
lemma inner_lift_multiplicityBilin (z w : H ⊗[ℂ] E) :
    ⟪TensorProduct.lift (multiplicityBilin (π := π) ξ₀ ι) z,
      TensorProduct.lift (multiplicityBilin (π := π) ξ₀ ι) w⟫_ℂ = ⟪z, w⟫_ℂ := by
  have key (η η' : H) (e e' : E) :
      ⟪π (rankOne ℂ η ξ₀) (ι e), π (rankOne ℂ η' ξ₀) (ι e')⟫_ℂ = ⟪η, η'⟫_ℂ * ⟪e, e'⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.comp_apply,
      adjoint_apply_rankOne_comp_apply_rankOne, smul_apply, inner_smul_right,
      apply_rankOne_self_of_mem_multiplicitySpace hξ₀ (hι ▸ LinearMap.mem_range_self _ e'),
      LinearIsometry.inner_map_map]
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => rw [map_add, inner_add_left, inner_add_left, hz, hz']
  | tmul η e =>
    induction w using TensorProduct.inductionOn with
    | add w w' hw hw' => rw [map_add, inner_add_right, inner_add_right, hw, hw']
    | tmul η' e' =>
      simp only [lift.tmul, multiplicityBilin, LinearMap.mk₂_apply, inner_tmul]
      rw [key]

/-- The map `η ⊗ e ↦ π(|η⟩⟨ξ₀|) ι e` is onto for unital `π`: `x = π(1) x = Σᵢ π(|bᵢ⟩⟨bᵢ|) x`
is the image of `Σᵢ bᵢ ⊗ eᵢ` for an orthonormal basis `b` of `H`, where `ι eᵢ = π(|ξ₀⟩⟨bᵢ|) x`,
which lies in the multiplicity space since `π(|ξ₀⟩⟨bᵢ|) = π(|ξ₀⟩⟨ξ₀|) π(|ξ₀⟩⟨bᵢ|)`. -/
lemma surjective_lift_multiplicityBilin :
    Function.Surjective (TensorProduct.lift (multiplicityBilin (π := π) ξ₀ ι)) := by
  intro x
  let b := stdOrthonormalBasis ℂ H
  have hmem (i : Fin (Module.finrank ℂ H)) :
      π (rankOne ℂ ξ₀ (b i)) x ∈ LinearMap.range ι.toLinearMap :=
    hι ▸ ⟨π (rankOne ℂ ξ₀ (b i)) x, by
      rw [ContinuousLinearMap.coe_coe, ← ContinuousLinearMap.comp_apply,
        apply_rankOne_comp_apply_rankOne hξ₀]⟩
  choose e he using hmem
  refine ⟨∑ i, b i ⊗ₜ e i, ?_⟩
  simp only [map_sum, lift.tmul, multiplicityBilin, LinearMap.mk₂_apply]
  simp only [LinearIsometry.coe_toLinearMap] at he
  simp_rw [he, ← ContinuousLinearMap.comp_apply, apply_rankOne_comp_apply_rankOne hξ₀,
    ← sum_apply, ← map_sum, b.sum_rankOne_eq_id, ← ContinuousLinearMap.one_def, map_one,
    one_apply_eq_self]

/-- The map `η ⊗ e ↦ π(|η⟩⟨ξ₀|) ι e` preserves norms
(`StarAlgHom.inner_lift_multiplicityBilin`). -/
lemma norm_lift_multiplicityBilin (z : H ⊗[ℂ] E) :
    ‖TensorProduct.lift (multiplicityBilin (π := π) ξ₀ ι) z‖ = ‖z‖ := by
  rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ,
    inner_lift_multiplicityBilin hξ₀ ι hι]

/-- A unital ⋆-representation of `B(H)` on `L` is a multiple of the identity representation: the
**unitary** `U : H ⊗ E ≃ L`, `η ⊗ e ↦ π(|η⟩⟨ξ₀|) ι e`, for a unit vector `ξ₀ ∈ H` and an isometry
`ι` of a Hilbert space `E` onto the multiplicity space `range π(|ξ₀⟩⟨ξ₀|)`. It preserves inner
products (`StarAlgHom.inner_lift_multiplicityBilin`) and is onto
(`StarAlgHom.surjective_lift_multiplicityBilin`). -/
noncomputable def multiplicityEquiv : H ⊗[ℂ] E ≃ₗᵢ[ℂ] L where
  toLinearEquiv := LinearEquiv.ofBijective (TensorProduct.lift (multiplicityBilin (π := π) ξ₀ ι))
    ⟨LinearMap.ker_eq_bot.1 <| LinearMap.ker_eq_bot'.2 fun z hz => norm_eq_zero.1 <| by
      rw [← norm_lift_multiplicityBilin hξ₀ ι hι, hz, norm_zero],
      surjective_lift_multiplicityBilin hξ₀ ι hι⟩
  norm_map' := norm_lift_multiplicityBilin hξ₀ ι hι

/-- The unitary of the multiplicity decomposition sends `η ⊗ e` to `π(|η⟩⟨ξ₀|) ι e`. -/
@[simp] lemma multiplicityEquiv_tmul (η : H) (e : E) :
    multiplicityEquiv hξ₀ ι hι (η ⊗ₜ e) = π (rankOne ℂ η ξ₀) (ι e) := by
  simp [multiplicityEquiv, multiplicityBilin]

/-- **Multiplicity decomposition** of a unital ⋆-representation of `B(H)`: `π(A) U = U (A ⊗ 1)`,
so `π` is unitarily equivalent to the ampliation `A ↦ A ⊗ 1` on `H ⊗ E`. On `η ⊗ e`,
`π(A) π(|η⟩⟨ξ₀|) = π(|A η⟩⟨ξ₀|)`. -/
theorem apply_multiplicityEquiv (A : H →L[ℂ] H) (z : H ⊗[ℂ] E) :
    π A (multiplicityEquiv hξ₀ ι hι z) = multiplicityEquiv hξ₀ ι hι (A.rTensor E z) := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | tmul η e =>
    rw [multiplicityEquiv_tmul, ContinuousLinearMap.rTensor_tmul, multiplicityEquiv_tmul,
      ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, ← map_mul,
      ContinuousLinearMap.mul_def, comp_rankOne]

end StarAlgHom
