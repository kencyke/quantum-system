/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.CStarAlgebra.TensorProduct.Minimal

/-!
# The bound on slice maps for the minimal norm

For a bounded functional `φ` on a C⋆-algebra `A`, the slice map `φ ⊗ id : A ⊗[ℂ] B → B`,
`a ⊗ b ↦ φ(a) b`, written `TensorProduct.lid ℂ B ∘ φ.rTensor B`, is bounded by `‖φ‖` for the norm
of the minimal tensor product `A ⊗ₘᵢₙ B`. The functional is arbitrary: no positivity is assumed.

With `A` and `B` represented faithfully by `π` on `H` and `ρ` on `K`, and `c = (φ ⊗ id)(z)`, the
matrix coefficient `⟪η, ρ(c) η'⟫` is `φ(a)` for the slice `a = (id ⊗ ⟪η, ρ(·) η'⟫)(z)` of `z` along
`B`, and the matrix coefficients of `π(a)` are those of `(π ⊗ ρ)(z)` at pure tensors:
`⟪ξ, π(a) ξ'⟫ = ⟪ξ ⊗ η, (π ⊗ ρ)(z) (ξ' ⊗ η')⟫`. Hence `‖a‖ ≤ ‖(π ⊗ ρ)(z)‖ ‖η‖ ‖η'‖` and
`|⟪η, ρ(c) η'⟫| ≤ ‖φ‖ ‖(π ⊗ ρ)(z)‖ ‖η‖ ‖η'‖`.

## Main results

* `MinTensorProduct.norm_lid_rTensor_le` — `‖(φ ⊗ id)(z)‖ ≤ ‖φ‖ ‖z‖`, `z` normed in `A ⊗ₘᵢₙ B`.
-/

@[expose] public section

open scoped TensorProduct InnerProductSpace MinTensorProduct

open UniformSpace

universe u v

variable {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

namespace CStarRep

/-- Slicing along `A` by `φ` and then applying `ω` is slicing along `B` by `ω` and then applying
`φ`. -/
private lemma apply_lid_rTensor_eq_apply_rid_lTensor (φ : A →ₗ[ℂ] ℂ) (ω : B →ₗ[ℂ] ℂ)
    (z : A ⊗[ℂ] B) :
    ω (TensorProduct.lid ℂ B (φ.rTensor B z)) = φ (TensorProduct.rid ℂ A (ω.lTensor A z)) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, LinearMap.lTensor_tmul,
      TensorProduct.rid_tmul, map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_comm]
  | add p q hp hq => simp only [map_add, hp, hq]

/-- For a faithful `π` and a bounded functional `φ` on `A`, the image under `ρ` of the slice
`(φ ⊗ id)(z)` is bounded by `‖φ‖ ‖(π ⊗ ρ)(z)‖`. -/
private lemma norm_π_lid_rTensor_le {R : CStarRep A} (hR : Function.Injective R.π)
    (S : CStarRep B) (φ : StrongDual ℂ A) (z : A ⊗[ℂ] B) :
    ‖S.π (TensorProduct.lid ℂ B ((φ : A →ₗ[ℂ] ℂ).rTensor B z))‖ ≤
      ‖φ‖ * ‖R.spatial S z‖ := by
  refine ContinuousLinearMap.opNorm_le_of_re_inner_le (by positivity) fun η' η hη' hη => ?_
  rw [← inner_re_symm, ← matrixCoeff_apply]
  change RCLike.re ((S.matrixCoeff η η' : B →ₗ[ℂ] ℂ) _) ≤ _
  rw [apply_lid_rTensor_eq_apply_rid_lTensor]
  refine (RCLike.re_le_norm _).trans ((φ.le_opNorm _).trans ?_)
  have h := norm_rid_lTensor_matrixCoeff_le hR S η η' z
  rw [hη, hη', mul_one, mul_one] at h
  exact mul_le_mul_of_nonneg_left h (norm_nonneg φ)

end CStarRep

namespace MinTensorProduct

/-- **A slice by a bounded functional is bounded by the minimal norm**: for a bounded functional
`φ` on `A`, the slice `a ⊗ b ↦ φ(a) b` of `A ⊗[ℂ] B` has `‖(φ ⊗ id)(z)‖ ≤ ‖φ‖ ‖z‖`, `z` normed in
`A ⊗ₘᵢₙ B`. -/
theorem norm_lid_rTensor_le (φ : StrongDual ℂ A) (z : A ⊗[ℂ] B) :
    ‖TensorProduct.lid ℂ B ((φ : A →ₗ[ℂ] ℂ).rTensor B z)‖ ≤
      ‖φ‖ * ‖of A B z‖ := by
  rw [← NonUnitalStarAlgHom.norm_map _ (CStarRep.gelfandNaimark_injective B), norm_of]
  exact CStarRep.norm_π_lid_rTensor_le (CStarRep.gelfandNaimark_injective A) _ φ z

end MinTensorProduct
