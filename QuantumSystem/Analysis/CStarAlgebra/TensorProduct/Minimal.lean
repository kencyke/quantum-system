/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import QuantumSystem.Analysis.CStarAlgebra.GelfandNaimark
public import QuantumSystem.Analysis.CStarAlgebra.TensorProduct.Spatial
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.ClosureRange
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.TensorProduct

import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.Quotient

/-!
# The minimal tensor product of C⋆-algebras

The minimal tensor product `A ⊗ₘᵢₙ B` of two C⋆-algebras is the completion of the algebraic tensor
product `A ⊗[ℂ] B` in the spatial norm `x ↦ ‖(π ⊗ ρ)(x)‖` of a pair of faithful representations `π`
of `A` and `ρ` of `B` (`CStarRep.spatial`). It is defined here as the norm closure of
`(π ⊗ ρ)(A ⊗[ℂ] B)` for `π = CStarRep.gelfandNaimark A` and `ρ = CStarRep.gelfandNaimark B`, a
C⋆-subalgebra of the operators on the tensor product of their Hilbert spaces: the closure of the
range `NonUnitalStarAlgHom.closureRange` of the `⋆`-homomorphism `π ⊗ ρ`. The choice does not
matter: the norm of `A ⊗ₘᵢₙ B` on `A ⊗[ℂ] B` is `‖(π ⊗ ρ)(x)‖` for every pair of faithful
representations (`MinTensorProduct.norm_of_eq_norm_spatial`). No norm is put on `A ⊗[ℂ] B` itself.

The algebras are not assumed unital: `A ⊗ₘᵢₙ B` is a `NonUnitalCStarAlgebra`, and a `CStarAlgebra`
when `A` and `B` are unital, with the same underlying non-unital structure. Its order is the
spectral order.

## Main definitions

* `MinTensorProduct A B`, written `A ⊗ₘᵢₙ B` — the minimal tensor product.
* `MinTensorProduct.of A B` — the `⋆`-homomorphism `A ⊗[ℂ] B →⋆ₙₐ[ℂ] A ⊗ₘᵢₙ B`.
* `MinTensorProduct.subtype A B` — the inclusion of `A ⊗ₘᵢₙ B` in the operators on the Hilbert space
  tensor product on which it is defined.
* `MinTensorProduct.inl A B`, `MinTensorProduct.inr A B` — the inclusions `a ↦ a ⊗ 1`, for unital
  `B`, and `b ↦ 1 ⊗ b`, for unital `A`.
* `CStarRep.tensorProduct R S` — the tensor product of two representations, as a representation of
  `A ⊗ₘᵢₙ B` on the Hilbert space tensor product: the extension of `CStarRep.spatial R S`.
* `MinTensorProduct.map φ ψ` — the tensor product `A₁ ⊗ₘᵢₙ B₁ →⋆ₙₐ[ℂ] A₂ ⊗ₘᵢₙ B₂` of two
  `⋆`-homomorphisms.
* `MinTensorProduct.equivClosureRange hR hS` — for faithful representations `π` and `ρ`, the
  `⋆`-isomorphism of `A ⊗ₘᵢₙ B` onto the norm closure of `(π ⊗ ρ)(A ⊗[ℂ] B)`.
* `MinTensorProduct.ofEquiv h` — when `MinTensorProduct.of` is surjective, the `⋆`-isomorphism
  `A ⊗[ℂ] B ≃⋆ₐ[ℂ] A ⊗ₘᵢₙ B`.
* `MinTensorProduct.continuousLinearMapEquivClosureRange H K` — for Hilbert spaces `H` and `K`,
  the `⋆`-isomorphism of `B(H) ⊗ₘᵢₙ B(K)` onto the norm closure of `B(H) ⊗[ℂ] B(K)` in
  `B(Completion (H ⊗[ℂ] K))`.
* `MinTensorProduct.continuousLinearMapCompletionEquiv h` — when the product map
  `B(H) ⊗[ℂ] B(K) → B(Completion (H ⊗[ℂ] K))` is surjective, as it is when `H` or `K` is
  finite-dimensional, `B(H) ⊗ₘᵢₙ B(K) ≃⋆ₐ[ℂ] B(Completion (H ⊗[ℂ] K))`.
* `MinTensorProduct.continuousLinearMapEquivOfSurjective h` — when moreover `H ⊗[ℂ] K` is
  complete, `B(H) ⊗ₘᵢₙ B(K) ≃⋆ₐ[ℂ] B(H ⊗[ℂ] K)`, the operators on the algebraic tensor product; it
  corresponds to `MinTensorProduct.continuousLinearMapCompletionEquiv h` under
  `H ⊗[ℂ] K → Completion (H ⊗[ℂ] K)`
  (`MinTensorProduct.completion_continuousLinearMapEquivOfSurjective`).
* `MinTensorProduct.continuousLinearMapEquiv H K` — its case of a finite-dimensional `H`, the form
  the finite-dimensional files use.

## Main results

* `MinTensorProduct.of_injective`, `MinTensorProduct.denseRange_of` — the algebraic tensor product
  embeds into `A ⊗ₘᵢₙ B` as a dense `⋆`-subalgebra.
* `MinTensorProduct.norm_of_tmul` — the cross norm `‖a ⊗ b‖ = ‖a‖ * ‖b‖`.
* `MinTensorProduct.ext_of_tmul` — a continuous additive map on `A ⊗ₘᵢₙ B` is determined by its
  values on the pure tensors.
* `MinTensorProduct.norm_of_eq_norm_spatial` — the norm is computed in any pair of faithful
  representations; `MinTensorProduct.norm_spatial_le_norm_of` — it dominates the tensor product of
  any two representations.
* `CStarRep.norm_tensorProduct_π_of_injective` — the tensor product of two faithful representations is an
  isometric representation of `A ⊗ₘᵢₙ B`.
* `MinTensorProduct.norm_map_of_injective` — the tensor product of two injective
  `⋆`-homomorphisms is isometric: the minimal tensor product of C⋆-subalgebras is a C⋆-subalgebra.
* `MinTensorProduct.norm_of_eq_norm_mapLCompletionStarAlgHom` — for Hilbert spaces `H` and `K`,
  the norm of `B(H) ⊗ₘᵢₙ B(K)` on `B(H) ⊗[ℂ] B(K)` is the operator norm on `Completion (H ⊗[ℂ] K)`.
* `MinTensorProduct.of_surjective_of_finiteDimensional_left`,
  `MinTensorProduct.of_surjective_of_finiteDimensional_right` — when `A` or `B` is
  finite-dimensional, the algebraic tensor product is all of `A ⊗ₘᵢₙ B`.

## Notation

Activated by `open scoped MinTensorProduct`:

* `A ⊗ₘᵢₙ B` — `MinTensorProduct A B`.
* `π₀[A, B]` — `CStarRep.spatial (CStarRep.gelfandNaimark A) (CStarRep.gelfandNaimark B)`, the
  `⋆`-homomorphism of `A ⊗[ℂ] B` whose norm closed range is `A ⊗ₘᵢₙ B`.

## Related files

* `QuantumSystem/Analysis/CStarAlgebra/TensorProduct/CompletelyPositiveMap.lean` — the tensor
  product `φ ⊗ ψ : A₁ ⊗ₘᵢₙ B₁ → A₂ ⊗ₘᵢₙ B₂` of completely positive maps.
* `QuantumSystem/Analysis/CStarAlgebra/TensorProduct/CStarNorm.lean` — the norm of `A ⊗ₘᵢₙ B` is the
  least C⋆-norm on `A ⊗[ℂ] B`.
* `QuantumSystem/Analysis/CStarAlgebra/TensorProduct/Nuclear.lean` — nuclear C⋆-algebras.
-/

@[expose] public section

open scoped TensorProduct InnerProduct Amplification

open UniformSpace

universe u v w₁ w₂

variable {A : Type u} {B : Type v}

/-- `π₀[A, B]` is the tensor product of the representations `CStarRep.gelfandNaimark A` and
`CStarRep.gelfandNaimark B`, the `⋆`-homomorphism of `A ⊗[ℂ] B` that defines `A ⊗ₘᵢₙ B`. -/
scoped[MinTensorProduct] notation "π₀[" A ", " B "]" =>
  CStarRep.spatial (CStarRep.gelfandNaimark A) (CStarRep.gelfandNaimark B)

open scoped MinTensorProduct

section Defs

variable (A B) [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- The **minimal tensor product** `A ⊗ₘᵢₙ B` of two C⋆-algebras: the norm closure of the image of
the algebraic tensor product `A ⊗[ℂ] B` under the tensor product of the faithful representations
`CStarRep.gelfandNaimark A` and `CStarRep.gelfandNaimark B`. -/
def MinTensorProduct : Type (max u v) :=
  π₀[A, B].closureRange

@[inherit_doc] scoped[MinTensorProduct] notation:99 A:101 " ⊗ₘᵢₙ " B:101 => MinTensorProduct A B

end Defs

namespace MinTensorProduct

section NonUnital

variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- The minimal tensor product is a C⋆-algebra, as a norm closed `⋆`-subalgebra of the operators on
a Hilbert space. -/
noncomputable instance instNonUnitalCStarAlgebra : NonUnitalCStarAlgebra (A ⊗ₘᵢₙ B) :=
  inferInstanceAs (NonUnitalCStarAlgebra π₀[A, B].closureRange)

/-- The order of the minimal tensor product is its spectral order, the only order making it a
star-ordered ring. -/
noncomputable instance instPartialOrder : PartialOrder (A ⊗ₘᵢₙ B) :=
  CStarAlgebra.spectralOrder (A ⊗ₘᵢₙ B)

/-- The minimal tensor product is a star-ordered ring for its spectral order. -/
instance instStarOrderedRing : StarOrderedRing (A ⊗ₘᵢₙ B) :=
  CStarAlgebra.spectralOrderedRing (A ⊗ₘᵢₙ B)

variable (A B) in
/-- The canonical `⋆`-homomorphism of the algebraic tensor product `A ⊗[ℂ] B` into the minimal
tensor product `A ⊗ₘᵢₙ B`. It is injective (`MinTensorProduct.of_injective`) with dense range
(`MinTensorProduct.denseRange_of`). -/
noncomputable def of : A ⊗[ℂ] B →⋆ₙₐ[ℂ] A ⊗ₘᵢₙ B :=
  π₀[A, B].closureRangeRestrict

/-- The norm of `A ⊗ₘᵢₙ B` on the algebraic tensor product is the norm of the tensor product of the
representations `CStarRep.gelfandNaimark A` and `CStarRep.gelfandNaimark B`. For the same statement
with any pair of faithful representations, see `MinTensorProduct.norm_of_eq_norm_spatial`. -/
lemma norm_of (x : A ⊗[ℂ] B) : ‖of A B x‖ = ‖π₀[A, B] x‖ := rfl

/-- The algebraic tensor product embeds into the minimal tensor product: `MinTensorProduct.of` is
injective. -/
lemma of_injective : Function.Injective (of A B) :=
  NonUnitalStarAlgHom.closureRangeRestrict_injective
    (CStarRep.spatial_injective (CStarRep.gelfandNaimark_injective A)
      (CStarRep.gelfandNaimark_injective B))

/-- The algebraic tensor product is dense in the minimal tensor product. -/
lemma denseRange_of : DenseRange (of A B) :=
  NonUnitalStarAlgHom.denseRange_closureRangeRestrict _

/-- A continuous additive map on the minimal tensor product is determined by its values on the
pure tensors, the algebraic tensor product being dense. -/
lemma ext_of_tmul {F E : Type*} [FunLike F (A ⊗ₘᵢₙ B) E] [Add E] [TopologicalSpace E]
    [T2Space E] [AddHomClass F (A ⊗ₘᵢₙ B) E] {ψ₁ ψ₂ : F} (h₁ : Continuous ψ₁)
    (h₂ : Continuous ψ₂)
    (h : ∀ (a : A) (b : B), ψ₁ (of A B (a ⊗ₜ[ℂ] b)) = ψ₂ (of A B (a ⊗ₜ[ℂ] b))) : ψ₁ = ψ₂ := by
  refine DFunLike.ext _ _ fun T => ?_
  have hof (x : A ⊗[ℂ] B) : ψ₁ (of A B x) = ψ₂ (of A B x) := by
    induction x using TensorProduct.inductionOn with
    | tmul a b => exact h a b
    | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  exact congrFun (denseRange_of.equalizer h₁ h₂ (funext hof)) T

/-- **The norm of the minimal tensor product is computed in any pair of faithful
representations**: for faithful representations `π` of `A` and `ρ` of `B`, the norm of `x` in
`A ⊗ₘᵢₙ B` is the operator norm of `(π ⊗ ρ)(x)`. -/
theorem norm_of_eq_norm_spatial {R : CStarRep A} {S : CStarRep B}
    (hR : Function.Injective R.π) (hS : Function.Injective S.π) (x : A ⊗[ℂ] B) :
    ‖of A B x‖ = ‖R.spatial S x‖ :=
  CStarRep.norm_spatial_eq_of_injective (CStarRep.gelfandNaimark_injective A)
    (CStarRep.gelfandNaimark_injective B) hR hS x

/-- The norm of the minimal tensor product dominates the tensor product of any two
representations: `‖(π ⊗ ρ)(x)‖ ≤ ‖x‖` in `A ⊗ₘᵢₙ B`. -/
lemma norm_spatial_le_norm_of (R : CStarRep A) (S : CStarRep B) (x : A ⊗[ℂ] B) :
    ‖R.spatial S x‖ ≤ ‖of A B x‖ :=
  CStarRep.norm_spatial_le_of_injective (CStarRep.gelfandNaimark_injective A)
    (CStarRep.gelfandNaimark_injective B) R S x

variable (A B) in
/-- The inclusion of the minimal tensor product `A ⊗ₘᵢₙ B` in the operators on the tensor product of
the Hilbert spaces of `CStarRep.gelfandNaimark A` and `CStarRep.gelfandNaimark B`, of which it is a
C⋆-subalgebra by definition. -/
noncomputable def subtype : A ⊗ₘᵢₙ B →⋆ₙₐ[ℂ]
    (Completion ((CStarRep.gelfandNaimark A).H ⊗[ℂ] (CStarRep.gelfandNaimark B).H) →L[ℂ]
      Completion ((CStarRep.gelfandNaimark A).H ⊗[ℂ] (CStarRep.gelfandNaimark B).H)) :=
  NonUnitalStarSubalgebraClass.subtype π₀[A, B].closureRange

/-- The inclusion of `A ⊗ₘᵢₙ B` in the operators is injective. -/
lemma subtype_injective : Function.Injective (subtype A B) :=
  Subtype.val_injective

/-- On the algebraic tensor product, the inclusion of `A ⊗ₘᵢₙ B` in the operators is the tensor
product of the representations `CStarRep.gelfandNaimark A` and `CStarRep.gelfandNaimark B`. -/
@[simp] lemma subtype_of (x : A ⊗[ℂ] B) : subtype A B (of A B x) = π₀[A, B] x := rfl

/-- The norm of the minimal tensor product is a cross norm: `‖a ⊗ b‖ = ‖a‖ * ‖b‖`. -/
lemma norm_of_tmul (a : A) (b : B) : ‖of A B (a ⊗ₜ[ℂ] b)‖ = ‖a‖ * ‖b‖ := by
  rw [norm_of, CStarRep.norm_spatial_tmul,
    NonUnitalStarAlgHom.norm_map _ (CStarRep.gelfandNaimark_injective A),
    NonUnitalStarAlgHom.norm_map _ (CStarRep.gelfandNaimark_injective B)]

end NonUnital

end MinTensorProduct

/-! ### The tensor product of two representations on the minimal tensor product -/

namespace CStarRep

open scoped MinTensorProduct

variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- The **tensor product of two representations** `π` of `A` and `ρ` of `B`, as a representation
of the minimal tensor product `A ⊗ₘᵢₙ B` on the Hilbert space tensor product: the extension of
`π ⊗ ρ` (`CStarRep.spatial`) from the algebraic tensor product, which is contractive for the norm
of `A ⊗ₘᵢₙ B` (`MinTensorProduct.norm_spatial_le_norm_of`). -/
noncomputable abbrev tensorProduct (R : CStarRep.{u, w₁} A) (S : CStarRep.{v, w₂} B) :
    CStarRep.{max u v, max w₁ w₂} (A ⊗ₘᵢₙ B) where
  H := Completion (R.H ⊗[ℂ] S.H)
  π := (NonUnitalStarSubalgebraClass.subtype (R.spatial S).closureRange).comp
    (NonUnitalStarAlgHom.closureRangeMap (φ := π₀[A, B]) (ψ := R.spatial S)
      (MinTensorProduct.norm_spatial_le_norm_of R S))

/-- On the algebraic tensor product, the tensor product of two representations is `π ⊗ ρ`. -/
@[simp] lemma tensorProduct_π_of (R : CStarRep A) (S : CStarRep B)
    (x : A ⊗[ℂ] B) : (R.tensorProduct S).π (MinTensorProduct.of A B x) = R.spatial S x :=
  congrArg Subtype.val (NonUnitalStarAlgHom.closureRangeMap_closureRangeRestrict (φ := π₀[A, B])
    (ψ := R.spatial S) (MinTensorProduct.norm_spatial_le_norm_of R S) x)

/-- The tensor product of two cyclic vectors is cyclic for the tensor product of the
representations: if the orbits of `ξ` under `π(A)` and of `η` under `ρ(B)` are dense, so is the orbit
of `ξ ⊗ η` under `(π ⊗ ρ)(A ⊗ₘᵢₙ B)`. -/
lemma denseRange_orbit_tensorProduct (R : CStarRep A) (S : CStarRep B) {ξ : R.H}
    {η : S.H} (hξ : DenseRange (R.orbit ξ)) (hη : DenseRange (S.orbit η)) :
    DenseRange ((R.tensorProduct S).orbit (↑(ξ ⊗ₜ[ℂ] η) : Completion (R.H ⊗[ℂ] S.H))) :=
  (denseRange_spatial_apply_tmul R S hξ hη).mono <| by
    rintro _ ⟨y, rfl⟩
    exact ⟨MinTensorProduct.of A B y, congrArg
      (fun T : Completion (R.H ⊗[ℂ] S.H) →L[ℂ] Completion (R.H ⊗[ℂ] S.H) => T ↑(ξ ⊗ₜ[ℂ] η))
      (tensorProduct_π_of R S y)⟩

/-- The tensor product of two faithful representations is an isometric representation of the
minimal tensor product: `‖(π ⊗ ρ)(T)‖ = ‖T‖`. -/
lemma norm_tensorProduct_π_of_injective {R : CStarRep A} {S : CStarRep B}
    (hR : Function.Injective R.π) (hS : Function.Injective S.π) (T : A ⊗ₘᵢₙ B) :
    ‖(R.tensorProduct S).π T‖ = ‖T‖ := by
  have hcont : Continuous (R.tensorProduct S).π :=
    AddMonoidHomClass.continuous_of_bound (R.tensorProduct S).π 1 fun T => by
      rw [one_mul]
      exact NonUnitalStarAlgHom.norm_apply_le (R.tensorProduct S).π T
  have h := MinTensorProduct.denseRange_of.equalizer hcont.norm
    continuous_norm (funext fun x => by
      rw [Function.comp_apply, Function.comp_apply, tensorProduct_π_of]
      exact (MinTensorProduct.norm_of_eq_norm_spatial hR hS x).symm)
  exact congrFun h T

/-- The tensor product of two faithful representations is a faithful representation of the minimal
tensor product. -/
lemma tensorProduct_π_injective {R : CStarRep A} {S : CStarRep B}
    (hR : Function.Injective R.π) (hS : Function.Injective S.π) :
    Function.Injective (R.tensorProduct S).π :=
  (injective_iff_map_eq_zero _).2 fun T hT =>
    norm_eq_zero.1 (by rw [← norm_tensorProduct_π_of_injective hR hS, hT, norm_zero])

/-- The range of the tensor product of two representations is the norm closure of
`(π ⊗ ρ)(A ⊗[ℂ] B)`: it lies in the closure, contains `(π ⊗ ρ)(A ⊗[ℂ] B)`, and is closed, as the
range of a `⋆`-homomorphism of C⋆-algebras. The representations need not be faithful. -/
lemma range_tensorProduct_π (R : CStarRep A) (S : CStarRep B) :
    Set.range (R.tensorProduct S).π = closure (Set.range (R.spatial S)) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    exact (NonUnitalStarAlgHom.closureRangeMap (φ := π₀[A, B]) (ψ := R.spatial S)
      (MinTensorProduct.norm_spatial_le_norm_of R S) x).2
  · have hcl : IsClosed (Set.range (R.tensorProduct S).π) :=
      NonUnitalStarAlgHom.isClosed_range (R.tensorProduct S).π
    refine closure_minimal ?_ hcl
    rintro _ ⟨x, rfl⟩
    exact ⟨MinTensorProduct.of A B x, tensorProduct_π_of R S x⟩

end CStarRep

namespace MinTensorProduct

section NonUnital

variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- **For faithful representations `π` of `A` and `ρ` of `B`, the minimal tensor product is
`⋆`-isomorphic to the norm closure of `(π ⊗ ρ)(A ⊗[ℂ] B)`**, by the isomorphism that is `π ⊗ ρ` on
the algebraic tensor product. -/
noncomputable def equivClosureRange {R : CStarRep.{u, w₁} A} {S : CStarRep.{v, w₂} B}
    (hR : Function.Injective R.π) (hS : Function.Injective S.π) :
    A ⊗ₘᵢₙ B ≃⋆ₐ[ℂ] (R.spatial S).closureRange :=
  NonUnitalStarAlgHom.closureRangeEquiv (φ := π₀[A, B]) (ψ := R.spatial S)
    fun x => norm_of_eq_norm_spatial hR hS x

/-- `MinTensorProduct.equivClosureRange` is `π ⊗ ρ` on the algebraic tensor product. -/
@[simp] lemma equivClosureRange_of {R : CStarRep.{u, w₁} A} {S : CStarRep.{v, w₂} B}
    (hR : Function.Injective R.π) (hS : Function.Injective S.π) (x : A ⊗[ℂ] B) :
    equivClosureRange hR hS (of A B x) = (R.spatial S).closureRangeRestrict x :=
  NonUnitalStarAlgHom.closureRangeEquiv_closureRangeRestrict _ x

/-- `MinTensorProduct.equivClosureRange` is the tensor product `CStarRep.tensorProduct` of the two
representations, with values in the closure of the range. -/
lemma coe_equivClosureRange {R : CStarRep.{u, w₁} A} {S : CStarRep.{v, w₂} B}
    (hR : Function.Injective R.π) (hS : Function.Injective S.π) (T : A ⊗ₘᵢₙ B) :
    (equivClosureRange hR hS T : Completion (R.H ⊗[ℂ] S.H) →L[ℂ] Completion (R.H ⊗[ℂ] S.H)) =
      (R.tensorProduct S).π T := rfl

end NonUnital

section Inclusions

section Left

variable [NonUnitalCStarAlgebra A] [CStarAlgebra B]

variable (A B) in
/-- The inclusion `a ↦ a ⊗ 1` of a C⋆-algebra `A` into `A ⊗ₘᵢₙ B`, for unital `B`: a
`⋆`-homomorphism, unital when `A` is unital too (`MinTensorProduct.inl_one`). -/
noncomputable def inl : A →⋆ₙₐ[ℂ] A ⊗ₘᵢₙ B where
  toFun a := of A B (a ⊗ₜ[ℂ] 1)
  map_smul' c a := by
    rw [MonoidHom.id_apply, ← TensorProduct.smul_tmul', map_smul]
  map_zero' := by rw [TensorProduct.zero_tmul, map_zero]
  map_add' a a' := by rw [TensorProduct.add_tmul, map_add]
  map_mul' a a' := by
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  map_star' a := by rw [← map_star, TensorProduct.star_tmul, star_one]

/-- `MinTensorProduct.inl A B a` is `a ⊗ 1`. -/
@[simp] lemma inl_apply (a : A) : inl A B a = of A B (a ⊗ₜ[ℂ] 1) := rfl

end Left

section Right

variable [CStarAlgebra A] [NonUnitalCStarAlgebra B]

variable (A B) in
/-- The inclusion `b ↦ 1 ⊗ b` of a C⋆-algebra `B` into `A ⊗ₘᵢₙ B`, for unital `A`: a
`⋆`-homomorphism, unital when `B` is unital too (`MinTensorProduct.inr_one`). -/
noncomputable def inr : B →⋆ₙₐ[ℂ] A ⊗ₘᵢₙ B where
  toFun b := of A B (1 ⊗ₜ[ℂ] b)
  map_smul' c b := by
    rw [MonoidHom.id_apply, TensorProduct.tmul_smul, map_smul]
  map_zero' := by rw [TensorProduct.tmul_zero, map_zero]
  map_add' b b' := by rw [TensorProduct.tmul_add, map_add]
  map_mul' b b' := by
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  map_star' b := by rw [← map_star, TensorProduct.star_tmul, star_one]

/-- `MinTensorProduct.inr A B b` is `1 ⊗ b`. -/
@[simp] lemma inr_apply (b : B) : inr A B b = of A B (1 ⊗ₜ[ℂ] b) := rfl

end Right

end Inclusions

section Unital

variable [CStarAlgebra A] [CStarAlgebra B]

/-- For unital `A` and `B`, the identity operator is `(π ⊗ ρ)(1 ⊗ 1)` for the unital
representations `CStarRep.gelfandNaimark A` and `CStarRep.gelfandNaimark B`, so it lies in the
closure of the image of the algebraic tensor product. -/
lemma one_mem_closureRange_spatial : (1 : Completion ((CStarRep.gelfandNaimark A).H ⊗[ℂ]
    (CStarRep.gelfandNaimark B).H) →L[ℂ] Completion ((CStarRep.gelfandNaimark A).H ⊗[ℂ]
    (CStarRep.gelfandNaimark B).H)) ∈ π₀[A, B].closureRange :=
  NonUnitalStarSubalgebra.le_topologicalClosure _ ⟨1 ⊗ₜ[ℂ] 1,
    CStarRep.spatial_one_tmul_one _ _ (CStarRep.gelfandNaimark_π_one A)
      (CStarRep.gelfandNaimark_π_one B)⟩

/-- The minimal tensor product of unital C⋆-algebras is a unital C⋆-algebra, with unit the identity
operator. Its non-unital structure is `MinTensorProduct.instNonUnitalCStarAlgebra`, by
definition. -/
noncomputable instance instCStarAlgebra : CStarAlgebra (A ⊗ₘᵢₙ B) :=
  letI nu : NonUnitalCStarAlgebra (A ⊗ₘᵢₙ B) := instNonUnitalCStarAlgebra
  letI ring : NormedRing (A ⊗ₘᵢₙ B) :=
    { nu.toNonUnitalNormedRing with
      one := ⟨1, one_mem_closureRange_spatial⟩
      one_mul := fun _ => Subtype.ext (one_mul _)
      mul_one := fun _ => Subtype.ext (mul_one _) }
  letI alg : NormedAlgebra ℂ (A ⊗ₘᵢₙ B) :=
    { Algebra.ofModule (fun c T T' => smul_mul_assoc c T T')
        (fun c T T' => mul_smul_comm c T T') with
      norm_smul_le := norm_smul_le }
  { ring, alg, nu with }

/-- For unital `A` and `B`, `MinTensorProduct.of` is unital. -/
@[simp] lemma of_one : of A B 1 = 1 :=
  Subtype.ext <| by
    change π₀[A, B] 1 = 1
    rw [Algebra.TensorProduct.one_def]
    exact CStarRep.spatial_one_tmul_one _ _ (CStarRep.gelfandNaimark_π_one A)
      (CStarRep.gelfandNaimark_π_one B)

/-- For unital `A` and `B`, `MinTensorProduct.inl` is unital: `1 ⊗ 1 = 1`. -/
lemma inl_one : inl A B 1 = 1 := by rw [inl_apply, ← Algebra.TensorProduct.one_def, of_one]

/-- For unital `A` and `B`, `MinTensorProduct.inr` is unital: `1 ⊗ 1 = 1`. -/
lemma inr_one : inr A B 1 = 1 := by rw [inr_apply, ← Algebra.TensorProduct.one_def, of_one]

end Unital

/-! ### The tensor product of two `⋆`-homomorphisms

For `⋆`-homomorphisms `φ : A₁ → A₂` and `ψ : B₁ → B₂`, the composites of `φ` and `ψ` with the
representations defining `A₂ ⊗ₘᵢₙ B₂` are representations of `A₁` and `B₁`, and their tensor product
is `(φ ⊗ ψ)` followed by the embedding of `A₂ ⊗[ℂ] B₂`; the norm of `A₁ ⊗ₘᵢₙ B₁` dominates it. -/

section Map

variable {A₁ B₁ A₂ B₂ A₃ B₃ : Type*} [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra B₁]
  [NonUnitalCStarAlgebra A₂] [NonUnitalCStarAlgebra B₂] [NonUnitalCStarAlgebra A₃]
  [NonUnitalCStarAlgebra B₃]

/-- The tensor product of the pullbacks along `φ` and `ψ` of the representations defining
`A₂ ⊗ₘᵢₙ B₂` is `φ ⊗ ψ` followed by their tensor product. -/
lemma spatial_comp_gelfandNaimark (φ : A₁ →⋆ₙₐ[ℂ] A₂) (ψ : B₁ →⋆ₙₐ[ℂ] B₂) (x : A₁ ⊗[ℂ] B₁) :
    CStarRep.spatial ((CStarRep.gelfandNaimark A₂).comp φ) ((CStarRep.gelfandNaimark B₂).comp ψ) x =
      π₀[A₂, B₂] (TensorProduct.map (φ : A₁ →ₗ[ℂ] A₂) (ψ : B₁ →ₗ[ℂ] B₂) x) :=
  NonUnitalStarAlgHom.mapLCompletion_eq_mapLCompletion_map (fun _ => rfl) (fun _ => rfl) x

/-- The closure of the image of `A₁ ⊗[ℂ] B₁` under `π₀[A₂, B₂] ∘ (φ ⊗ ψ)` lies in `A₂ ⊗ₘᵢₙ B₂`. -/
lemma closureRange_spatial_comp_gelfandNaimark_le (φ : A₁ →⋆ₙₐ[ℂ] A₂) (ψ : B₁ →⋆ₙₐ[ℂ] B₂) :
    (CStarRep.spatial ((CStarRep.gelfandNaimark A₂).comp φ) ((CStarRep.gelfandNaimark B₂).comp ψ)).closureRange ≤
      π₀[A₂, B₂].closureRange :=
  NonUnitalStarSubalgebra.topologicalClosure_mono <| by
    rintro _ ⟨x, rfl⟩
    exact ⟨_, (spatial_comp_gelfandNaimark φ ψ x).symm⟩

/-- The **tensor product of two `⋆`-homomorphisms** `φ : A₁ → A₂` and `ψ : B₁ → B₂`, as a
`⋆`-homomorphism `A₁ ⊗ₘᵢₙ B₁ → A₂ ⊗ₘᵢₙ B₂` of the minimal tensor products: the extension of
`a ⊗ b ↦ φ(a) ⊗ ψ(b)` (`MinTensorProduct.map_of_tmul`). It is isometric when `φ` and `ψ` are
injective (`MinTensorProduct.norm_map_of_injective`). -/
noncomputable def map (φ : A₁ →⋆ₙₐ[ℂ] A₂) (ψ : B₁ →⋆ₙₐ[ℂ] B₂) :
    A₁ ⊗ₘᵢₙ B₁ →⋆ₙₐ[ℂ] A₂ ⊗ₘᵢₙ B₂ :=
  ((NonUnitalStarSubalgebra.inclusion (closureRange_spatial_comp_gelfandNaimark_le φ ψ)).comp
    (NonUnitalStarAlgHom.closureRangeMap (φ := π₀[A₁, B₁])
      (norm_spatial_le_norm_of ((CStarRep.gelfandNaimark A₂).comp φ)
        ((CStarRep.gelfandNaimark B₂).comp ψ))) :
    π₀[A₁, B₁].closureRange →⋆ₙₐ[ℂ] π₀[A₂, B₂].closureRange)

/-- On the algebraic tensor product, `MinTensorProduct.map φ ψ` is the algebraic tensor product
`φ ⊗ ψ` of the linear maps. -/
lemma map_of (φ : A₁ →⋆ₙₐ[ℂ] A₂) (ψ : B₁ →⋆ₙₐ[ℂ] B₂) (x : A₁ ⊗[ℂ] B₁) :
    map φ ψ (of A₁ B₁ x) =
      of A₂ B₂ (TensorProduct.map (φ : A₁ →ₗ[ℂ] A₂) (ψ : B₁ →ₗ[ℂ] B₂) x) :=
  Subtype.ext <| (congrArg Subtype.val (NonUnitalStarAlgHom.closureRangeMap_closureRangeRestrict
    (φ := π₀[A₁, B₁]) (norm_spatial_le_norm_of ((CStarRep.gelfandNaimark A₂).comp φ)
      ((CStarRep.gelfandNaimark B₂).comp ψ)) x)).trans
      (spatial_comp_gelfandNaimark φ ψ x)

/-- `MinTensorProduct.map φ ψ` sends `a ⊗ b` to `φ(a) ⊗ ψ(b)`. -/
@[simp] lemma map_of_tmul (φ : A₁ →⋆ₙₐ[ℂ] A₂) (ψ : B₁ →⋆ₙₐ[ℂ] B₂) (a : A₁) (b : B₁) :
    map φ ψ (of A₁ B₁ (a ⊗ₜ[ℂ] b)) = of A₂ B₂ (φ a ⊗ₜ[ℂ] ψ b) :=
  map_of φ ψ (a ⊗ₜ[ℂ] b)

/-- The tensor product of two `⋆`-homomorphisms is continuous. -/
lemma continuous_map (φ : A₁ →⋆ₙₐ[ℂ] A₂) (ψ : B₁ →⋆ₙₐ[ℂ] B₂) : Continuous (map φ ψ) :=
  AddMonoidHomClass.continuous_of_bound (map φ ψ) 1 fun T => by
    rw [one_mul]
    exact NonUnitalStarAlgHom.norm_apply_le (map φ ψ) T

/-- The tensor product of the identity homomorphisms is the identity. -/
@[simp] lemma map_id : map (NonUnitalStarAlgHom.id ℂ A₁) (NonUnitalStarAlgHom.id ℂ B₁) =
    NonUnitalStarAlgHom.id ℂ (A₁ ⊗ₘᵢₙ B₁) :=
  ext_of_tmul (continuous_map _ _) continuous_id fun a b => by
    rw [map_of_tmul]
    rfl

/-- The tensor product of `⋆`-homomorphisms is compatible with composition:
`(φ' ∘ φ) ⊗ (ψ' ∘ ψ) = (φ' ⊗ ψ') ∘ (φ ⊗ ψ)`. -/
lemma map_comp (φ' : A₂ →⋆ₙₐ[ℂ] A₃) (ψ' : B₂ →⋆ₙₐ[ℂ] B₃) (φ : A₁ →⋆ₙₐ[ℂ] A₂)
    (ψ : B₁ →⋆ₙₐ[ℂ] B₂) : map (φ'.comp φ) (ψ'.comp ψ) = (map φ' ψ').comp (map φ ψ) :=
  ext_of_tmul (continuous_map _ _) ((continuous_map φ' ψ').comp (continuous_map φ ψ)) fun a b => by
    simp only [NonUnitalStarAlgHom.comp_apply, map_of_tmul]

/-- **The minimal tensor product of two injective `⋆`-homomorphisms is isometric**: for
C⋆-subalgebras `A₁ ⊆ A₂` and `B₁ ⊆ B₂`, the minimal tensor product `A₁ ⊗ₘᵢₙ B₁` is a C⋆-subalgebra of
`A₂ ⊗ₘᵢₙ B₂`. -/
theorem norm_map_of_injective {φ : A₁ →⋆ₙₐ[ℂ] A₂} {ψ : B₁ →⋆ₙₐ[ℂ] B₂}
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ) (T : A₁ ⊗ₘᵢₙ B₁) :
    ‖map φ ψ T‖ = ‖T‖ := by
  have h := denseRange_of.equalizer (continuous_map φ ψ).norm continuous_norm (funext fun x => by
    rw [Function.comp_apply, Function.comp_apply, map_of, norm_of, ← spatial_comp_gelfandNaimark]
    exact (norm_of_eq_norm_spatial
      (CStarRep.comp_π_injective (CStarRep.gelfandNaimark_injective A₂) hφ)
      (CStarRep.comp_π_injective (CStarRep.gelfandNaimark_injective B₂) hψ) x).symm)
  exact congrFun h T

/-- The minimal tensor product of two injective `⋆`-homomorphisms is injective. -/
lemma map_injective {φ : A₁ →⋆ₙₐ[ℂ] A₂} {ψ : B₁ →⋆ₙₐ[ℂ] B₂} (hφ : Function.Injective φ)
    (hψ : Function.Injective ψ) : Function.Injective (map φ ψ) :=
  (injective_iff_map_eq_zero _).2 fun T hT =>
    norm_eq_zero.1 (by rw [← norm_map_of_injective hφ hψ, hT, norm_zero])

end Map

/-! ### A finite-dimensional factor -/

section FiniteDimensional

variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- **When `A` is finite-dimensional, the algebraic tensor product is all of the minimal tensor
product**, whatever the C⋆-algebra `B`: its image is closed
(`CStarRep.isClosed_range_spatial_of_finiteDimensional_left`) and dense. -/
theorem of_surjective_of_finiteDimensional_left [FiniteDimensional ℂ A] :
    Function.Surjective (of A B) :=
  NonUnitalStarAlgHom.closureRangeRestrict_surjective_of_isClosed
    (CStarRep.isClosed_range_spatial_of_finiteDimensional_left _ _)

/-- **When `B` is finite-dimensional, the algebraic tensor product is all of the minimal tensor
product**, whatever the C⋆-algebra `A`: its image is closed
(`CStarRep.isClosed_range_spatial_of_finiteDimensional_right`) and dense. -/
theorem of_surjective_of_finiteDimensional_right [FiniteDimensional ℂ B] :
    Function.Surjective (of A B) :=
  NonUnitalStarAlgHom.closureRangeRestrict_surjective_of_isClosed
    (CStarRep.isClosed_range_spatial_of_finiteDimensional_right _ _)

/-- When `MinTensorProduct.of` is surjective, as it is when `A` or `B` is finite-dimensional
(`MinTensorProduct.of_surjective_of_finiteDimensional_left`,
`MinTensorProduct.of_surjective_of_finiteDimensional_right`), the algebraic tensor product
`A ⊗[ℂ] B` is `⋆`-isomorphic to the minimal tensor product `A ⊗ₘᵢₙ B` by it. -/
noncomputable def ofEquiv (h : Function.Surjective (of A B)) : A ⊗[ℂ] B ≃⋆ₐ[ℂ] A ⊗ₘᵢₙ B :=
  StarAlgEquiv.ofBijective (of A B) ⟨of_injective, h⟩

/-- `MinTensorProduct.ofEquiv` is `MinTensorProduct.of`. -/
@[simp] lemma ofEquiv_apply (h : Function.Surjective (of A B)) (x : A ⊗[ℂ] B) :
    ofEquiv h x = of A B x := rfl

end FiniteDimensional

/-! ### Operator algebras -/

section ContinuousLinearMap

variable (H K : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

section Complete

variable [CompleteSpace H] [CompleteSpace K]

/-- `idRep[H]` is the identity representation of `B(H)` on `H`. -/
local notation "idRep[" H "]" =>
  CStarRep.mk (A := H →L[ℂ] H) H (NonUnitalStarAlgHom.id ℂ (H →L[ℂ] H))

variable {H K} in
/-- For Hilbert spaces `H` and `K`, the norm of `B(H) ⊗ₘᵢₙ B(K)` on the algebraic tensor product is
the operator norm on the Hilbert space tensor product `Completion (H ⊗[ℂ] K)`, through the product
map `TensorProduct.mapLCompletionStarAlgHom`. -/
lemma norm_of_eq_norm_mapLCompletionStarAlgHom (x : (H →L[ℂ] H) ⊗[ℂ] (K →L[ℂ] K)) :
    ‖of (H →L[ℂ] H) (K →L[ℂ] K) x‖ = ‖TensorProduct.mapLCompletionStarAlgHom ℂ H K x‖ :=
  norm_of_eq_norm_spatial (R := idRep[H]) (S := idRep[K]) Function.injective_id
    Function.injective_id x

/-- **For Hilbert spaces `H` and `K`, the minimal tensor product `B(H) ⊗ₘᵢₙ B(K)` is the norm closure
of `B(H) ⊗[ℂ] B(K)` in `B(Completion (H ⊗[ℂ] K))`**: it is `⋆`-isomorphic to the closure of the
range of the product map `TensorProduct.mapLCompletionStarAlgHom`, by the isomorphism that is the
product map on the algebraic tensor product. -/
noncomputable def continuousLinearMapEquivClosureRange :
    (H →L[ℂ] H) ⊗ₘᵢₙ (K →L[ℂ] K) ≃⋆ₐ[ℂ]
      (TensorProduct.mapLCompletionStarAlgHom ℂ H K).toNonUnitalStarAlgHom.closureRange :=
  equivClosureRange (R := idRep[H]) (S := idRep[K]) Function.injective_id Function.injective_id

variable {H K} in
/-- `MinTensorProduct.continuousLinearMapEquivClosureRange` is the product map on the algebraic
tensor product. -/
@[simp] lemma coe_continuousLinearMapEquivClosureRange_of (x : (H →L[ℂ] H) ⊗[ℂ] (K →L[ℂ] K)) :
    (continuousLinearMapEquivClosureRange H K (of _ _ x) :
      Completion (H ⊗[ℂ] K) →L[ℂ] Completion (H ⊗[ℂ] K)) =
        TensorProduct.mapLCompletionStarAlgHom ℂ H K x :=
  congrArg Subtype.val (equivClosureRange_of (R := idRep[H]) (S := idRep[K])
    Function.injective_id Function.injective_id x)

variable {H K} in
/-- `MinTensorProduct.continuousLinearMapEquivClosureRange` sends `f ⊗ g` to the operator `f ⊗ g`
on the Hilbert space tensor product. -/
lemma coe_continuousLinearMapEquivClosureRange_of_tmul (f : H →L[ℂ] H) (g : K →L[ℂ] K) :
    (continuousLinearMapEquivClosureRange H K (of _ _ (f ⊗ₜ[ℂ] g)) :
      Completion (H ⊗[ℂ] K) →L[ℂ] Completion (H ⊗[ℂ] K)) = f ⊗ g :=
  coe_continuousLinearMapEquivClosureRange_of (f ⊗ₜ[ℂ] g)

variable {H K} in
/-- When the product map `B(H) ⊗[ℂ] B(K) → B(Completion (H ⊗[ℂ] K))` is surjective, as it is when
`H` or `K` is finite-dimensional
(`TensorProduct.mapLCompletionStarAlgHom_surjective_of_finiteDimensional_left`,
`TensorProduct.mapLCompletionStarAlgHom_surjective_of_finiteDimensional_right`), the minimal
tensor product of the operator algebras is the operator algebra of the Hilbert space tensor
product: `B(H) ⊗ₘᵢₙ B(K) ≃ B(Completion (H ⊗[ℂ] K))`, the tensor `f ⊗ g` corresponding to the
operator `f ⊗ g`. -/
noncomputable def continuousLinearMapCompletionEquiv
    (h : Function.Surjective (TensorProduct.mapLCompletionStarAlgHom ℂ H K)) :
    (H →L[ℂ] H) ⊗ₘᵢₙ (K →L[ℂ] K) ≃⋆ₐ[ℂ]
      (Completion (H ⊗[ℂ] K) →L[ℂ] Completion (H ⊗[ℂ] K)) :=
  StarAlgEquiv.ofBijective (idRep[H].tensorProduct idRep[K]).π
    ⟨CStarRep.tensorProduct_π_injective Function.injective_id Function.injective_id, fun T => by
      obtain ⟨x, rfl⟩ := h T
      exact ⟨of _ _ x, CStarRep.tensorProduct_π_of _ _ x⟩⟩

variable {H K} in
/-- `MinTensorProduct.continuousLinearMapCompletionEquiv` is the product map on the algebraic
tensor product. -/
@[simp] lemma continuousLinearMapCompletionEquiv_of
    (h : Function.Surjective (TensorProduct.mapLCompletionStarAlgHom ℂ H K))
    (x : (H →L[ℂ] H) ⊗[ℂ] (K →L[ℂ] K)) :
    continuousLinearMapCompletionEquiv h (of _ _ x) =
      TensorProduct.mapLCompletionStarAlgHom ℂ H K x :=
  CStarRep.tensorProduct_π_of _ _ x

variable {H K} in
/-- `MinTensorProduct.continuousLinearMapCompletionEquiv` sends `f ⊗ g` to the operator `f ⊗ g` on
the Hilbert space tensor product. -/
lemma continuousLinearMapCompletionEquiv_of_tmul
    (h : Function.Surjective (TensorProduct.mapLCompletionStarAlgHom ℂ H K)) (f : H →L[ℂ] H)
    (g : K →L[ℂ] K) :
    continuousLinearMapCompletionEquiv h (of _ _ (f ⊗ₜ[ℂ] g)) = f ⊗ g :=
  continuousLinearMapCompletionEquiv_of h (f ⊗ₜ[ℂ] g)

end Complete

section CompleteTensorProduct

variable [CompleteSpace H] [CompleteSpace K] [CompleteSpace (H ⊗[ℂ] K)]

variable {H K} in
/-- When the product map `B(H) ⊗[ℂ] B(K) → B(Completion (H ⊗[ℂ] K))` is surjective and the algebraic
tensor product `H ⊗[ℂ] K` is complete, as both are when `H` or `K` is finite-dimensional
(`TensorProduct.completeSpace_of_finiteDimensional_left`,
`TensorProduct.completeSpace_of_finiteDimensional_right`), the minimal tensor product of the
operator algebras is the operator algebra of `H ⊗[ℂ] K`: `B(H) ⊗ₘᵢₙ B(K) ≃ B(H ⊗[ℂ] K)`, the tensor
`f ⊗ g` corresponding to the operator `TensorProduct.mapL f g`. It is
`MinTensorProduct.continuousLinearMapCompletionEquiv h` read on `H ⊗[ℂ] K`, which is its own
completion. -/
noncomputable def continuousLinearMapEquivOfSurjective
    (h : Function.Surjective (TensorProduct.mapLCompletionStarAlgHom ℂ H K)) :
    (H →L[ℂ] H) ⊗ₘᵢₙ (K →L[ℂ] K) ≃⋆ₐ[ℂ] (H ⊗[ℂ] K →L[ℂ] H ⊗[ℂ] K) :=
  (continuousLinearMapCompletionEquiv h).trans
    (Completion.linearIsometryEquivOfComplete ℂ (H ⊗[ℂ] K)).symm.conjStarAlgEquiv

variable {H K}

/-- `MinTensorProduct.continuousLinearMapEquivOfSurjective h` sends `f ⊗ g` to the operator tensor
product `TensorProduct.mapL f g`. -/
@[simp] lemma continuousLinearMapEquivOfSurjective_of_tmul
    (h : Function.Surjective (TensorProduct.mapLCompletionStarAlgHom ℂ H K)) (f : H →L[ℂ] H)
    (g : K →L[ℂ] K) :
    continuousLinearMapEquivOfSurjective h (of _ _ (f ⊗ₜ[ℂ] g)) = TensorProduct.mapL f g := by
  ext x
  rw [continuousLinearMapEquivOfSurjective, StarAlgEquiv.trans_apply,
    continuousLinearMapCompletionEquiv_of_tmul, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_symm]
  exact (congrArg _ (ContinuousLinearMap.completion_apply_coe _ x)).trans
    (LinearIsometryEquiv.symm_apply_apply _ _)

/-- **The two descriptions of `B(H) ⊗ₘᵢₙ B(K)` agree**: the extension to `Completion (H ⊗[ℂ] K)` of
the operator `MinTensorProduct.continuousLinearMapEquivOfSurjective h T` on `H ⊗[ℂ] K` is
`MinTensorProduct.continuousLinearMapCompletionEquiv h T`. -/
lemma completion_continuousLinearMapEquivOfSurjective
    (h : Function.Surjective (TensorProduct.mapLCompletionStarAlgHom ℂ H K))
    (T : (H →L[ℂ] H) ⊗ₘᵢₙ (K →L[ℂ] K)) :
    (continuousLinearMapEquivOfSurjective h T).completion =
      continuousLinearMapCompletionEquiv h T := by
  refine ContinuousLinearMap.ext fun y => Completion.induction_on y
    (isClosed_eq (by fun_prop) (by fun_prop)) fun x => ?_
  rw [ContinuousLinearMap.completion_apply_coe, continuousLinearMapEquivOfSurjective,
    StarAlgEquiv.trans_apply, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_symm]
  exact LinearIsometryEquiv.apply_symm_apply (Completion.linearIsometryEquivOfComplete ℂ (H ⊗[ℂ] K)) _

end CompleteTensorProduct

variable [FiniteDimensional ℂ H] [CompleteSpace K]

/-- For a finite-dimensional Hilbert space `H` and a Hilbert space `K`, the minimal tensor product of
the operator algebras is the operator algebra of the algebraic tensor product `H ⊗[ℂ] K`, which is
complete: `B(H) ⊗ₘᵢₙ B(K) ≃ B(H ⊗[ℂ] K)`, the tensor `f ⊗ g` corresponding to the operator
`TensorProduct.mapL f g`. It is `MinTensorProduct.continuousLinearMapEquivOfSurjective` for the
surjectivity `TensorProduct.mapLCompletionStarAlgHom_surjective_of_finiteDimensional_left`; for a
finite-dimensional `K` instead, use it with
`TensorProduct.mapLCompletionStarAlgHom_surjective_of_finiteDimensional_right`. -/
noncomputable def continuousLinearMapEquiv :
    (H →L[ℂ] H) ⊗ₘᵢₙ (K →L[ℂ] K) ≃⋆ₐ[ℂ] (H ⊗[ℂ] K →L[ℂ] H ⊗[ℂ] K) :=
  continuousLinearMapEquivOfSurjective
    TensorProduct.mapLCompletionStarAlgHom_surjective_of_finiteDimensional_left

variable {H K}

/-- `MinTensorProduct.continuousLinearMapEquiv` sends `f ⊗ g` to the operator tensor product
`TensorProduct.mapL f g`. -/
@[simp] lemma continuousLinearMapEquiv_of_tmul (f : H →L[ℂ] H) (g : K →L[ℂ] K) :
    continuousLinearMapEquiv H K (of _ _ (f ⊗ₜ[ℂ] g)) = TensorProduct.mapL f g :=
  continuousLinearMapEquivOfSurjective_of_tmul _ f g

/-- **For a finite-dimensional `H`, the two descriptions of `B(H) ⊗ₘᵢₙ B(K)` agree**: the extension
to `Completion (H ⊗[ℂ] K)` of the operator `MinTensorProduct.continuousLinearMapEquiv H K T` on
`H ⊗[ℂ] K` is `MinTensorProduct.continuousLinearMapCompletionEquiv h T`, for the surjectivity `h`
of the product map when `H` is finite-dimensional. -/
lemma completion_continuousLinearMapEquiv (T : (H →L[ℂ] H) ⊗ₘᵢₙ (K →L[ℂ] K)) :
    (continuousLinearMapEquiv H K T).completion = continuousLinearMapCompletionEquiv
      TensorProduct.mapLCompletionStarAlgHom_surjective_of_finiteDimensional_left T :=
  completion_continuousLinearMapEquivOfSurjective _ T

end ContinuousLinearMap

end MinTensorProduct
