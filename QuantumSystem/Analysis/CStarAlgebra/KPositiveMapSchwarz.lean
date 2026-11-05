/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.KPositiveMap
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.SchwarzMap

import QuantumSystem.Analysis.CStarAlgebra.ChoiEffros

/-!
# `2`-positive maps as Schwarz maps

By the Kadison–Schwarz inequality (`KPositiveMapClass.le_smul_map_star_mul_of_norm_le`),
a `2`-positive contraction `φ` (`‖φ x‖ ≤ ‖x‖`) between possibly non-unital C⋆-algebras is a
Schwarz map. Between unital C⋆-algebras the condition reads `φ 1 ≤ 1`: the normalised
Kadison–Schwarz inequality `KPositiveMapClass.le_map_star_mul` holds under it directly. This file
packages both as Schwarz maps. Through the rigidity of Schwarz maps
(`SchwarzMapClass.starAlgEquivOfInverse`), a `2`-positive contraction with a `2`-positive
contractive inverse is then a ⋆-isomorphism (`KPositiveMapClass.starAlgEquivOfInverseOfNormLe`),
and so, between unital C⋆-algebras, is a unital `2`-positive map with a `2`-positive inverse, in
particular a unital complete order isomorphism (`KPositiveMapClass.starAlgEquivOfInverse`). An
injective `2`-positive map which reverses products, between possibly non-unital C⋆-algebras, has
a commutative domain (`KPositiveMapClass.mul_comm_of_injective_of_map_mul_swap`), with no
normalisation assumed: such a map is a ⋆-anti-homomorphism, hence a contraction
(`StarHomClass.norm_apply_le_of_map_mul_swap`). So a ⋆-anti-automorphism of a noncommutative
C⋆-algebra is not `2`-positive. The file lives outside `ForMathlib/` because
it needs both `KPositiveMap.lean` and `SchwarzMap.lean`, and a `ForMathlib` file imports Mathlib
only.

## Main definitions

* `KPositiveMapClass.toSchwarzMapOfNormLe` — a `2`-positive contraction between possibly
  non-unital C⋆-algebras as a Schwarz map.
* `KPositiveMapClass.toSchwarzMap` — a `2`-positive map with `φ 1 ≤ 1` between unital C⋆-algebras
  as a Schwarz map.
* `KPositiveMapClass.starAlgEquivOfInverseOfNormLe` — a `2`-positive contraction with a
  `2`-positive contractive inverse, between possibly non-unital C⋆-algebras, as a ⋆-isomorphism.
* `KPositiveMapClass.starAlgEquivOfInverse` — a unital `2`-positive map with a `2`-positive
  inverse, in particular a unital complete order isomorphism, as a ⋆-isomorphism.
-/

@[expose] public section

namespace KPositiveMapClass

section NonUnital

variable {F A₁ A₂ : Type*} [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂] [PartialOrder A₁]
  [PartialOrder A₂] [StarOrderedRing A₁] [StarOrderedRing A₂] [FunLike F A₁ A₂]
  [LinearMapClass F ℂ A₁ A₂] [KPositiveMapClass F 2 A₁ A₂]

/-- A `2`-positive contraction (`‖φ x‖ ≤ ‖x‖`) between possibly non-unital C⋆-algebras as a
Schwarz map: `φ(a)⋆ φ(a) ≤ φ(a⋆ a)` is the Kadison–Schwarz inequality
`KPositiveMapClass.le_smul_map_star_mul_of_norm_le` with constant `1`. -/
noncomputable def toSchwarzMapOfNormLe (φ : F) (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖) : SchwarzMap A₁ A₂ where
  toLinearMap := (φ : A₁ →ₗ[ℂ] A₂)
  le_map_star_mul' a := by
    simpa using le_smul_map_star_mul_of_norm_le φ (C := 1) (by simpa using hφ) a

/-- `toSchwarzMapOfNormLe φ hφ` evaluates as `φ`. -/
@[simp] lemma toSchwarzMapOfNormLe_apply (φ : F) (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖) (a : A₁) :
    toSchwarzMapOfNormLe φ hφ a = φ a := rfl

/-- An injective `2`-positive map `φ` between possibly non-unital C⋆-algebras which reverses
products, `φ(a b) = φ(b) φ(a)`, has a commutative domain. No normalisation is needed: being
positive, `φ` preserves the involution, so it is a contraction
(`StarHomClass.norm_apply_le_of_map_mul_swap`), hence a Schwarz map
(`KPositiveMapClass.toSchwarzMapOfNormLe`), and
`SchwarzMapClass.mul_comm_of_injective_of_map_mul_swap` applies. Equivalently, a
⋆-anti-automorphism of a noncommutative C⋆-algebra is not `2`-positive. -/
lemma mul_comm_of_injective_of_map_mul_swap (φ : F) (hinj : Function.Injective φ)
    (hφ' : ∀ a b, φ (a * b) = φ b * φ a) (a b : A₁) : a * b = b * a :=
  SchwarzMapClass.mul_comm_of_injective_of_map_mul_swap
    (toSchwarzMapOfNormLe φ (StarHomClass.norm_apply_le_of_map_mul_swap φ hφ')) hinj hφ' a b

variable {G : Type*} [FunLike G A₂ A₁] [KPositiveMapClass G 2 A₂ A₁]

/-- **Rigidity.** A `2`-positive contraction `φ` between possibly non-unital C⋆-algebras with a
`2`-positive contractive inverse `ψ` is a ⋆-isomorphism. The inverse `ψ` is linear as the inverse
of `φ`, so both maps are Schwarz maps (`KPositiveMapClass.toSchwarzMapOfNormLe`), and `φ` is
multiplicative by `SchwarzMapClass.map_mul_of_inverse`. On a nonzero C⋆-algebra neither bound can
be dropped, as the mutually inverse completely positive maps `2⁻¹ • id` and `2 • id` show. Here
`h₁` and `h₂` say `ψ ∘ φ = id` and `φ ∘ ψ = id`. -/
@[simps apply symm_apply]
noncomputable def starAlgEquivOfInverseOfNormLe (φ : F) (ψ : G) (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖)
    (hψ : ∀ x, ‖ψ x‖ ≤ ‖x‖) (h₁ : Function.LeftInverse ψ φ) (h₂ : Function.RightInverse ψ φ) :
    A₁ ≃⋆ₐ[ℂ] A₂ where
  toFun := φ
  invFun := ψ
  left_inv := h₁
  right_inv := h₂
  map_mul' := SchwarzMapClass.map_mul_of_inverse (toSchwarzMapOfNormLe φ hφ)
    (toSchwarzMapOfNormLe (⟨(⟨(φ : A₁ →ₗ[ℂ] A₂), ψ, h₁, h₂⟩ : A₁ ≃ₗ[ℂ] A₂).symm.toLinearMap,
      map_cstarMatrix_nonneg' ψ⟩ : KPositiveMap 2 A₂ A₁) hψ) h₁ h₂
  map_add' := map_add φ
  map_star' := map_star φ
  map_smul' := map_smul φ

end NonUnital

section Unital

variable {F A₁ A₂ : Type*} [CStarAlgebra A₁] [CStarAlgebra A₂] [PartialOrder A₁] [PartialOrder A₂]
  [StarOrderedRing A₁] [StarOrderedRing A₂] [FunLike F A₁ A₂] [LinearMapClass F ℂ A₁ A₂]
  [KPositiveMapClass F 2 A₁ A₂]

/-- A `2`-positive map with `φ 1 ≤ 1` between unital C⋆-algebras as a Schwarz map:
`φ(a)⋆ φ(a) ≤ φ(a⋆ a)` is the normalised Kadison–Schwarz inequality
`KPositiveMapClass.le_map_star_mul`. -/
noncomputable def toSchwarzMap (φ : F) (hφ : φ 1 ≤ 1) : SchwarzMap A₁ A₂ where
  toLinearMap := (φ : A₁ →ₗ[ℂ] A₂)
  le_map_star_mul' := le_map_star_mul φ hφ

/-- `toSchwarzMap φ hφ` evaluates as `φ`. -/
@[simp] lemma toSchwarzMap_apply (φ : F) (hφ : φ 1 ≤ 1) (a : A₁) :
    toSchwarzMap φ hφ a = φ a := rfl

/-- `toSchwarzMap φ hφ` is idempotent when `φ` is, so that `ChoiEffros (toSchwarzMap φ hφ)` is a
C⋆-algebra. -/
instance {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {F : Type*}
    [FunLike F A A] [LinearMapClass F ℂ A A] [KPositiveMapClass F 2 A A] (φ : F) (hφ : φ 1 ≤ 1)
    [h : Fact (IsIdempotentElem (φ : A →ₗ[ℂ] A))] :
    Fact (IsIdempotentElem (toSchwarzMap φ hφ : A →ₗ[ℂ] A)) :=
  ⟨h.out⟩

noncomputable example {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {F : Type*}
    [FunLike F A A] [LinearMapClass F ℂ A A] [KPositiveMapClass F 2 A A] (φ : F) (hφ : φ 1 ≤ 1)
    [Fact (IsIdempotentElem (φ : A →ₗ[ℂ] A))] : CStarAlgebra (ChoiEffros (toSchwarzMap φ hφ)) :=
  inferInstance

variable {G : Type*} [FunLike G A₂ A₁] [KPositiveMapClass G 2 A₂ A₁]

/-- **Unital complete order isomorphisms are ⋆-isomorphisms.** A unital `2`-positive map `φ`
between unital C⋆-algebras with a `2`-positive inverse `ψ` is a ⋆-isomorphism; in particular so
is a unital completely positive map with a completely positive inverse
(`LinearMap.IsCompleteOrderEmbedding.starAlgEquiv`). The inverse `ψ` is linear as the inverse of
`φ` and unital as `ψ 1 = ψ (φ 1) = 1`, so both maps are Schwarz maps by the normalised
Kadison–Schwarz inequality, hence contractions (`SchwarzMapClass.norm_apply_le`), and
`KPositiveMapClass.starAlgEquivOfInverseOfNormLe` applies. Here `h₁` and `h₂` say `ψ ∘ φ = id` and
`φ ∘ ψ = id`. For `φ` a ⋆-algebra homomorphism, whose `LinearMapClass` instance Mathlib does not
register globally, supply it with `letI := AlgHomClass.linearMapClass`. -/
@[simps! apply symm_apply]
noncomputable def starAlgEquivOfInverse (φ : F) (ψ : G) (hφ : φ 1 = 1)
    (h₁ : Function.LeftInverse ψ φ) (h₂ : Function.RightInverse ψ φ) : A₁ ≃⋆ₐ[ℂ] A₂ :=
  starAlgEquivOfInverseOfNormLe φ ψ (SchwarzMapClass.norm_apply_le (toSchwarzMap φ hφ.le))
    (SchwarzMapClass.norm_apply_le
      (⟨(⟨(φ : A₁ →ₗ[ℂ] A₂), ψ, h₁, h₂⟩ : A₁ ≃ₗ[ℂ] A₂).symm.toLinearMap,
        le_map_star_mul ψ (by rw [← hφ, h₁ 1])⟩ : SchwarzMap A₂ A₁)) h₁ h₂

end Unital

end KPositiveMapClass
