/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import QuantumSystem.Analysis.CStarAlgebra.CStarSeminorm
public import QuantumSystem.Analysis.CStarAlgebra.TensorProduct.Nuclear
public import QuantumSystem.ForMathlib.Algebra.Star.TensorProductMap
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.Completion
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.Shrink

import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.Quotient

/-!
# The maximal tensor product of C⋆-algebras

The maximal tensor product `A ⊗ₘₐₓ B` of two C⋆-algebras is the completion of the algebraic tensor
product `A ⊗[ℂ] B` for the greatest C⋆-norm on it: the supremum of the C⋆-seminorms on `A ⊗[ℂ] B`
(`CStarSeminorm`), each of which satisfies `p (a ⊗ b) ≤ ‖a‖ * ‖b‖` (`CStarSeminorm.apply_tmul_le`),
so that the supremum is finite and is the greatest C⋆-seminorm (`CStarSeminorm.greatest`,
`MaxTensorProduct.maxNorm`). Every `⋆`-homomorphism `Φ` of `A ⊗[ℂ] B` into a C⋆-algebra gives
such a seminorm `x ↦ ‖Φ x‖` (`CStarSeminorm.ofStarAlgHom`), so `Φ` extends to
`A ⊗ₘₐₓ B` (`MaxTensorProduct.lift`), whatever the universe of its target: the seminorms are functions
on `A ⊗[ℂ] B`, and `A ⊗ₘₐₓ B` lies in the universe of `A ⊗[ℂ] B`. The supremum is a norm, being at
least the norm of the minimal tensor product.

The algebras are not assumed unital: `A ⊗ₘₐₓ B` is a `NonUnitalCStarAlgebra`.

## Main definitions

* `MaxTensorProduct.maxNorm A B` — the maximal norm, a `CStarSeminorm (A ⊗[ℂ] B)`.
* `MaxTensorProduct A B`, written `A ⊗ₘₐₓ B` — the maximal tensor product.
* `MaxTensorProduct.of A B` — the `⋆`-homomorphism `A ⊗[ℂ] B →⋆ₙₐ[ℂ] A ⊗ₘₐₓ B`.
* `MaxTensorProduct.lift Φ` — the extension of a `⋆`-homomorphism `Φ : A ⊗[ℂ] B → C`.
* `MaxTensorProduct.toMin A B` — the `⋆`-homomorphism onto the minimal tensor product.
* `MaxTensorProduct.map φ ψ` — the tensor product of two `⋆`-homomorphisms.
* `MaxTensorProduct.comm A B` — `A ⊗ₘₐₓ B ≃⋆ₐ[ℂ] B ⊗ₘₐₓ A`.

## Main results

* `CStarSeminorm.apply_tmul_le` — a C⋆-seminorm on `A ⊗[ℂ] B` is bounded by the cross norm on pure
  tensors.
* `MaxTensorProduct.norm_apply_le_norm_of` — `‖Φ x‖ ≤ ‖x‖` in `A ⊗ₘₐₓ B` for every `⋆`-homomorphism
  `Φ` of `A ⊗[ℂ] B` into a C⋆-algebra.
* `MaxTensorProduct.of_injective`, `MaxTensorProduct.denseRange_of`.
* `MaxTensorProduct.norm_of_tmul` — the cross norm `‖a ⊗ b‖ = ‖a‖ * ‖b‖`.
* `MaxTensorProduct.lift_of`, `MaxTensorProduct.lift_unique`.
* `MaxTensorProduct.toMin_surjective`.
* `CStarAlgebra.IsNuclear.iff_norm_of_le` — `A` is nuclear exactly when the maximal and the minimal
  norms agree on `A ⊗[ℂ] B` for every `B`; `CStarAlgebra.IsNuclear.iff_toMin_injective`.
* `CStarAlgebra.IsNuclear.lift_universes` — nuclearity does not depend on the universes of the test
  algebras and of the targets.

## Notation

Activated by `open scoped MaxTensorProduct`: `A ⊗ₘₐₓ B` — `MaxTensorProduct A B`.
-/

@[expose] public section

open scoped TensorProduct MinTensorProduct CStarAlgebra

open UniformSpace

universe u v w

/-! ### C⋆-seminorms on the algebraic tensor product -/

namespace CStarSeminorm

variable {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  (p : CStarSeminorm (A ⊗[ℂ] B))

/-- **A C⋆-seminorm on `A ⊗[ℂ] B` is bounded by the cross norm**: `p (a ⊗ b) ≤ ‖a‖ ‖b‖`, as the
seminorm of a `⋆`-homomorphism into a C⋆-algebra (`CStarSeminorm.norm_toCompletion`,
`NonUnitalStarAlgHom.norm_apply_tmul_le`). -/
theorem apply_tmul_le (a : A) (b : B) : p (a ⊗ₜ[ℂ] b) ≤ ‖a‖ * ‖b‖ := by
  rw [← p.norm_toCompletion]
  exact NonUnitalStarAlgHom.norm_apply_tmul_le p.toCompletion a b

/-- A C⋆-seminorm is bounded by the projective bound `∑ ‖aᵢ‖ ‖bᵢ‖` of any expression
`x = ∑ aᵢ ⊗ bᵢ`. -/
lemma apply_sum_tmul_le (S : Finset (A × B)) : p (∑ i ∈ S, i.1 ⊗ₜ[ℂ] i.2) ≤ ∑ i ∈ S, ‖i.1‖ * ‖i.2‖ :=
  (p.apply_sum_le S _).trans (Finset.sum_le_sum fun i _ => p.apply_tmul_le i.1 i.2)

end CStarSeminorm

namespace MaxTensorProduct

variable {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-! ### The maximal norm -/

/-- The values of the C⋆-seminorms at `x` are bounded: by `∑ ‖aᵢ‖ ‖bᵢ‖` for `x = ∑ aᵢ ⊗ bᵢ`. -/
lemma bddAbove_range (x : A ⊗[ℂ] B) :
    BddAbove (Set.range fun p : CStarSeminorm (A ⊗[ℂ] B) => p x) := by
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset x
  exact ⟨_, by rintro _ ⟨p, rfl⟩; exact p.apply_sum_tmul_le S⟩

variable (A B) in
/-- The **maximal norm** on `A ⊗[ℂ] B`: the supremum of the C⋆-seminorms, the greatest
C⋆-seminorm. -/
noncomputable def maxNorm : CStarSeminorm (A ⊗[ℂ] B) :=
  CStarSeminorm.greatest bddAbove_range

/-- Every C⋆-seminorm is at most the maximal norm. -/
lemma le_maxNorm (p : CStarSeminorm (A ⊗[ℂ] B)) (x : A ⊗[ℂ] B) : p x ≤ maxNorm A B x :=
  CStarSeminorm.le_greatest bddAbove_range p x

/-- The maximal norm is the least bound of the C⋆-seminorms. -/
lemma maxNorm_le {x : A ⊗[ℂ] B} {c : ℝ} (h : ∀ p : CStarSeminorm (A ⊗[ℂ] B), p x ≤ c) :
    maxNorm A B x ≤ c :=
  CStarSeminorm.greatest_le bddAbove_range h

/-- A `⋆`-homomorphism `Φ` of `A ⊗[ℂ] B` into a C⋆-algebra, in any universe, is contractive for the
maximal norm: `‖Φ x‖ ≤ maxNorm A B x`, as `x ↦ ‖Φ x‖` is a C⋆-seminorm
(`CStarSeminorm.ofStarAlgHom`). -/
lemma norm_apply_le_maxNorm {C : Type*} [NonUnitalCStarAlgebra C] (Φ : A ⊗[ℂ] B →⋆ₙₐ[ℂ] C)
    (x : A ⊗[ℂ] B) : ‖Φ x‖ ≤ maxNorm A B x :=
  le_maxNorm (CStarSeminorm.ofStarAlgHom Φ) x

/-- The maximal norm dominates the minimal one. -/
lemma norm_minOf_le_maxNorm (x : A ⊗[ℂ] B) : ‖MinTensorProduct.of A B x‖ ≤ maxNorm A B x :=
  norm_apply_le_maxNorm (MinTensorProduct.of A B) x

/-- The maximal norm is a norm: it dominates the minimal norm, which is one. -/
lemma eq_zero_of_maxNorm_eq_zero {x : A ⊗[ℂ] B} (h : maxNorm A B x = 0) : x = 0 := by
  have h0 : ‖MinTensorProduct.of A B x‖ = 0 :=
    le_antisymm (h ▸ norm_minOf_le_maxNorm x) (norm_nonneg _)
  exact MinTensorProduct.of_injective (by rw [norm_eq_zero.1 h0, map_zero])

end MaxTensorProduct

section Defs

variable (A : Type u) (B : Type v) [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- The **maximal tensor product** `A ⊗ₘₐₓ B` of two C⋆-algebras: the completion of the algebraic
tensor product for the maximal norm, the greatest C⋆-norm on it. -/
abbrev MaxTensorProduct : Type (max u v) :=
  Completion (MaxTensorProduct.maxNorm A B).Carrier

@[inherit_doc] scoped[MaxTensorProduct] notation:99 A:101 " ⊗ₘₐₓ " B:101 => MaxTensorProduct A B

end Defs

open scoped MaxTensorProduct

namespace MaxTensorProduct

variable {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- The maximal tensor product is a C⋆-algebra, as the completion of a C⋆-normed algebra. Recorded
as a shortcut instance. -/
noncomputable instance instNonUnitalCStarAlgebra : NonUnitalCStarAlgebra (A ⊗ₘₐₓ B) :=
  inferInstance

variable (A B) in
/-- The canonical `⋆`-homomorphism of the algebraic tensor product into the maximal tensor
product. -/
noncomputable def of : A ⊗[ℂ] B →⋆ₙₐ[ℂ] A ⊗ₘₐₓ B :=
  (maxNorm A B).toCompletion

/-- The norm of `A ⊗ₘₐₓ B` on the algebraic tensor product is the maximal norm. -/
lemma norm_of (x : A ⊗[ℂ] B) : ‖of A B x‖ = maxNorm A B x :=
  (maxNorm A B).norm_toCompletion x

/-- **A `⋆`-homomorphism of `A ⊗[ℂ] B` into a C⋆-algebra is contractive for the norm of
`A ⊗ₘₐₓ B`**: `‖Φ x‖ ≤ ‖x‖` in `A ⊗ₘₐₓ B` for every `⋆`-homomorphism `Φ` of `A ⊗[ℂ] B` into a
C⋆-algebra, in any universe. -/
theorem norm_apply_le_norm_of {C : Type*} [NonUnitalCStarAlgebra C] (Φ : A ⊗[ℂ] B →⋆ₙₐ[ℂ] C)
    (x : A ⊗[ℂ] B) : ‖Φ x‖ ≤ ‖of A B x‖ := by
  rw [norm_of]
  exact norm_apply_le_maxNorm Φ x

/-- The norm of the maximal tensor product dominates that of the minimal one. -/
lemma norm_minOf_le_norm_of (x : A ⊗[ℂ] B) : ‖MinTensorProduct.of A B x‖ ≤ ‖of A B x‖ :=
  norm_apply_le_norm_of (MinTensorProduct.of A B) x

/-- The algebraic tensor product embeds into the maximal tensor product. -/
lemma of_injective : Function.Injective (of A B) :=
  (injective_iff_map_eq_zero _).2 fun x hx =>
    eq_zero_of_maxNorm_eq_zero (by rw [← norm_of, hx, norm_zero])

/-- The algebraic tensor product is dense in the maximal tensor product. -/
lemma denseRange_of : DenseRange (of A B) :=
  (maxNorm A B).denseRange_toCompletion

/-- The norm of the maximal tensor product is a cross norm: `‖a ⊗ b‖ = ‖a‖ * ‖b‖`. -/
lemma norm_of_tmul (a : A) (b : B) : ‖of A B (a ⊗ₜ[ℂ] b)‖ = ‖a‖ * ‖b‖ := by
  refine le_antisymm ?_ ((MinTensorProduct.norm_of_tmul a b).symm.le.trans
    (norm_minOf_le_norm_of _))
  rw [norm_of]
  exact maxNorm_le fun p => p.apply_tmul_le a b

/-! ### The universal property -/

section Lift

variable {C : Type*} [NonUnitalCStarAlgebra C]

/-- **The universal property of the maximal tensor product**: a `⋆`-homomorphism `Φ` of `A ⊗[ℂ] B`
into a C⋆-algebra extends to `A ⊗ₘₐₓ B`, by continuity, `Φ` being contractive for the maximal
norm. -/
noncomputable def lift (Φ : A ⊗[ℂ] B →⋆ₙₐ[ℂ] C) : A ⊗ₘₐₓ B →⋆ₙₐ[ℂ] C :=
  (maxNorm A B).lift Φ (norm_apply_le_maxNorm Φ)

/-- `MaxTensorProduct.lift Φ` extends `Φ`. -/
@[simp] lemma lift_of (Φ : A ⊗[ℂ] B →⋆ₙₐ[ℂ] C) (x : A ⊗[ℂ] B) : lift Φ (of A B x) = Φ x :=
  (maxNorm A B).lift_toCompletion Φ (norm_apply_le_maxNorm Φ) x

/-- Two `⋆`-homomorphisms out of `A ⊗ₘₐₓ B` that agree on the algebraic tensor product agree. -/
lemma nonUnitalStarAlgHom_ext {ψ₁ ψ₂ : A ⊗ₘₐₓ B →⋆ₙₐ[ℂ] C} (h : ∀ x, ψ₁ (of A B x) = ψ₂ (of A B x)) :
    ψ₁ = ψ₂ :=
  (maxNorm A B).nonUnitalStarAlgHom_ext h

/-- `MaxTensorProduct.lift Φ` is the only extension of `Φ`. -/
lemma lift_unique (Φ : A ⊗[ℂ] B →⋆ₙₐ[ℂ] C) {ψ : A ⊗ₘₐₓ B →⋆ₙₐ[ℂ] C}
    (h : ∀ x, ψ (of A B x) = Φ x) : ψ = lift Φ :=
  (maxNorm A B).lift_unique Φ (norm_apply_le_maxNorm Φ) h

end Lift

/-! ### The map onto the minimal tensor product -/

variable (A B) in
/-- The canonical `⋆`-homomorphism of the maximal tensor product onto the minimal one, the identity
on the algebraic tensor product. -/
noncomputable def toMin : A ⊗ₘₐₓ B →⋆ₙₐ[ℂ] A ⊗ₘᵢₙ B :=
  lift (MinTensorProduct.of A B)

/-- `MaxTensorProduct.toMin A B` is the identity on the algebraic tensor product. -/
@[simp] lemma toMin_of (x : A ⊗[ℂ] B) : toMin A B (of A B x) = MinTensorProduct.of A B x :=
  lift_of _ x

/-- The canonical map onto the minimal tensor product is onto: its range is closed, as that of a
`⋆`-homomorphism of C⋆-algebras, and contains the dense algebraic tensor product. -/
theorem toMin_surjective : Function.Surjective (toMin A B) := by
  have hcl : IsClosed (Set.range (toMin A B)) :=
    NonUnitalStarAlgHom.isClosed_range (toMin A B)
  have hd : Dense (Set.range (toMin A B)) :=
    MinTensorProduct.denseRange_of.mono (by rintro _ ⟨x, rfl⟩; exact ⟨of A B x, toMin_of x⟩)
  exact Set.range_eq_univ.1 (hcl.closure_eq.symm.trans hd.closure_eq)

/-! ### Functoriality -/

section Map

variable {A₂ B₂ : Type*} [NonUnitalCStarAlgebra A₂] [NonUnitalCStarAlgebra B₂]

/-- The tensor product `φ ⊗ ψ : A ⊗ₘₐₓ B → A₂ ⊗ₘₐₓ B₂` of two `⋆`-homomorphisms. -/
noncomputable def map (φ : A →⋆ₙₐ[ℂ] A₂) (ψ : B →⋆ₙₐ[ℂ] B₂) : A ⊗ₘₐₓ B →⋆ₙₐ[ℂ] A₂ ⊗ₘₐₓ B₂ :=
  lift ((of A₂ B₂).comp (NonUnitalStarAlgebra.TensorProduct.map φ ψ))

/-- `MaxTensorProduct.map φ ψ` is `TensorProduct.map φ ψ` on the algebraic tensor product. -/
@[simp] lemma map_of (φ : A →⋆ₙₐ[ℂ] A₂) (ψ : B →⋆ₙₐ[ℂ] B₂) (x : A ⊗[ℂ] B) :
    map φ ψ (of A B x) = of A₂ B₂ (TensorProduct.map (φ : A →ₗ[ℂ] A₂) (ψ : B →ₗ[ℂ] B₂) x) :=
  lift_of _ x

end Map

/-! ### Commutativity -/

/-- The maximal norm is symmetric: the norm of `x` in `A ⊗ₘₐₓ B` is that of the flipped tensor
`a ⊗ b ↦ b ⊗ a` in `B ⊗ₘₐₓ A`. -/
lemma norm_of_comm (x : A ⊗[ℂ] B) :
    ‖of A B x‖ = ‖of B A (TensorProduct.comm ℂ A B x)‖ := by
  have h₁ : ‖of B A (TensorProduct.comm ℂ A B x)‖ ≤ ‖of A B x‖ := norm_apply_le_norm_of
    ((of B A).comp (NonUnitalStarAlgebra.TensorProduct.comm (R := ℂ) (A₁ := A)
      (B₁ := B)).toNonUnitalStarAlgHom) x
  have h₂ : ‖of A B (TensorProduct.comm ℂ B A (TensorProduct.comm ℂ A B x))‖ ≤
      ‖of B A (TensorProduct.comm ℂ A B x)‖ := norm_apply_le_norm_of
    ((of A B).comp (NonUnitalStarAlgebra.TensorProduct.comm (R := ℂ) (A₁ := B)
      (B₁ := A)).toNonUnitalStarAlgHom) (TensorProduct.comm ℂ A B x)
  rw [TensorProduct.comm_comm] at h₂
  exact le_antisymm h₂ h₁

variable (A B) in
/-- **The commutativity of the maximal tensor product**: `A ⊗ₘₐₓ B ≃⋆ₐ[ℂ] B ⊗ₘₐₓ A`, by the
isomorphism that is `a ⊗ b ↦ b ⊗ a` on the algebraic tensor product
(`MaxTensorProduct.comm_of`). -/
noncomputable def comm : A ⊗ₘₐₓ B ≃⋆ₐ[ℂ] B ⊗ₘₐₓ A := by
  refine NonUnitalStarAlgHom.equivOfDenseRange (φ := of A B)
    (ψ := (of B A).comp NonUnitalStarAlgebra.TensorProduct.comm.toNonUnitalStarAlgHom)
    denseRange_of ?_ norm_of_comm
  have h := (denseRange_of (A := B) (B := A))
  unfold DenseRange at h ⊢
  rwa [← (TensorProduct.comm ℂ A B).surjective.range_comp] at h

/-- `MaxTensorProduct.comm A B` is `a ⊗ b ↦ b ⊗ a` on the algebraic tensor product. -/
lemma comm_of (x : A ⊗[ℂ] B) : comm A B (of A B x) = of B A (TensorProduct.comm ℂ A B x) :=
  NonUnitalStarAlgHom.equivOfDenseRange_apply _ _ _ x

/-- `MaxTensorProduct.comm A B` sends `a ⊗ b` to `b ⊗ a`. -/
@[simp] lemma comm_of_tmul (a : A) (b : B) :
    comm A B (of A B (a ⊗ₜ[ℂ] b)) = of B A (b ⊗ₜ[ℂ] a) :=
  comm_of (a ⊗ₜ[ℂ] b)

end MaxTensorProduct

/-! ### Nuclearity through the maximal tensor product -/

namespace CStarAlgebra.IsNuclear

variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- If the maximal and the minimal norms agree on `A ⊗[ℂ] B` for every `B`, then `A` is nuclear,
for every universe of the targets of the `⋆`-homomorphisms. -/
lemma of_norm_of_le
    (h : ∀ (B : Type v) [NonUnitalCStarAlgebra B] (x : A ⊗[ℂ] B),
      ‖MaxTensorProduct.of A B x‖ ≤ ‖MinTensorProduct.of A B x‖) : IsNuclear.{v, w} A :=
  ⟨fun B _ _ _ Φ x => (MaxTensorProduct.norm_apply_le_norm_of Φ x).trans (h B x)⟩

/-- **A C⋆-algebra is nuclear exactly when the maximal and the minimal norms agree** on its
algebraic tensor product with every C⋆-algebra. -/
theorem iff_norm_of_le :
    IsNuclear.{v, max u v} A ↔ ∀ (B : Type v) [NonUnitalCStarAlgebra B] (x : A ⊗[ℂ] B),
      ‖MaxTensorProduct.of A B x‖ ≤ ‖MinTensorProduct.of A B x‖ :=
  ⟨fun h B _ x => h.norm_apply_le_norm_of B _ (MaxTensorProduct.of A B) x, of_norm_of_le⟩

/-- Nuclearity for targets in the universe `max u v` of `A ⊗ₘₐₓ B` gives nuclearity for targets in
every universe. -/
private lemma lift_target_universe [IsNuclear.{v, max u v} A] : IsNuclear.{v, w} A :=
  of_norm_of_le (iff_norm_of_le.1 inferInstance)

/-- **Nuclearity does not depend on the universes**: nuclearity for test algebras in one universe
`v` and targets in `max u v` gives it for test algebras and targets in every universe. The
elements `bᵢ` of a tensor `∑ aᵢ ⊗ bᵢ` of `A ⊗[ℂ] B` lie in a closed `⋆`-subalgebra `B₀` of `B` that
is small in `Type` (`NonUnitalStarSubalgebra.exists_subset_isClosed_small`), and `B₀` has a copy in
`Type v` (`Shrink.starAlgEquiv`). The tensor comes from the algebraic tensor product of `A` with
that copy, on which the minimal norm is that of `A ⊗ₘᵢₙ B`
(`MinTensorProduct.norm_map_of_injective`). -/
theorem lift_universes.{v'} [IsNuclear.{v, max u v} A] : IsNuclear.{v', w} A := by
  have : IsNuclear.{v, w} A := lift_target_universe
  refine ⟨fun B _ C _ Φ x => ?_⟩
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset x
  have : Finite (Prod.snd '' (S : Set (A × B))) := (S.finite_toSet.image _).to_subtype
  have : Small.{0} (Prod.snd '' (S : Set (A × B))) := Countable.toSmall _
  obtain ⟨B₀, hS, hcl, hsmall⟩ :=
    NonUnitalStarSubalgebra.exists_subset_isClosed_small.{0} ℂ (Prod.snd '' (S : Set (A × B)))
  have : IsClosed (B₀ : Set B) := hcl
  have : Small.{v} B₀ := @small_lift _ hsmall
  let e := Shrink.starAlgEquiv.{v} ℂ B₀
  let ι : Shrink.{v} B₀ →⋆ₙₐ[ℂ] B :=
    (NonUnitalStarSubalgebraClass.subtype B₀).comp e.toNonUnitalStarAlgHom
  have hι : Function.Injective ι := Subtype.val_injective.comp (EquivLike.injective e)
  have hx : ∑ i ∈ S, i.1 ⊗ₜ[ℂ] i.2 ∈ LinearMap.range (TensorProduct.map
      (NonUnitalStarAlgHom.id ℂ A : A →ₗ[ℂ] A) (ι : Shrink.{v} B₀ →ₗ[ℂ] B)) :=
    Submodule.sum_mem _ fun i hi => ⟨i.1 ⊗ₜ[ℂ] e.symm ⟨i.2, hS ⟨i, hi, rfl⟩⟩, by simp [ι]⟩
  obtain ⟨x', hx'⟩ := hx
  calc ‖Φ (∑ i ∈ S, i.1 ⊗ₜ[ℂ] i.2)‖ = ‖(Φ.comp (NonUnitalStarAlgebra.TensorProduct.map
        (NonUnitalStarAlgHom.id ℂ A) ι)) x'‖ := by
        rw [NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgebra.TensorProduct.map_apply, hx']
    _ ≤ ‖MinTensorProduct.of A (Shrink.{v} B₀) x'‖ := norm_apply_le_norm_of _ C _ x'
    _ = ‖MinTensorProduct.of A B (∑ i ∈ S, i.1 ⊗ₜ[ℂ] i.2)‖ := by
        rw [← hx', ← MinTensorProduct.map_of,
          MinTensorProduct.norm_map_of_injective Function.injective_id hι]

/-- **A C⋆-algebra is nuclear exactly when the canonical map from the maximal onto the minimal
tensor product is injective**, hence a `⋆`-isomorphism, for every C⋆-algebra `B`. -/
theorem iff_toMin_injective :
    IsNuclear.{v, max u v} A ↔
      ∀ (B : Type v) [NonUnitalCStarAlgebra B], Function.Injective (MaxTensorProduct.toMin A B) := by
  rw [iff_norm_of_le]
  refine ⟨fun h B _ => ?_, fun h B _ x => ?_⟩
  · have hiso : ∀ T : A ⊗ₘₐₓ B, ‖MaxTensorProduct.toMin A B T‖ = ‖T‖ := fun T =>
      congrFun (MaxTensorProduct.denseRange_of.equalizer
        (map_continuous _).norm continuous_norm (funext fun x => by
          simp only [Function.comp_apply, MaxTensorProduct.toMin_of]
          exact le_antisymm (MaxTensorProduct.norm_minOf_le_norm_of x) (h B x))) T
    refine (injective_iff_map_eq_zero _).2 fun T hT => norm_eq_zero.1 ?_
    rw [← hiso, hT, norm_zero]
  · rw [← MaxTensorProduct.toMin_of, NonUnitalStarAlgHom.norm_map _ (h B)]

variable (A) in
/-- For a nuclear `A`, **the maximal and the minimal tensor products coincide**: the canonical map
`A ⊗ₘₐₓ B → A ⊗ₘᵢₙ B` is a `⋆`-isomorphism. -/
noncomputable def toMinEquiv [IsNuclear.{v, max u v} A] (B : Type v) [NonUnitalCStarAlgebra B] :
    A ⊗ₘₐₓ B ≃⋆ₐ[ℂ] A ⊗ₘᵢₙ B :=
  StarAlgEquiv.ofBijective (MaxTensorProduct.toMin A B)
    ⟨iff_toMin_injective.1 inferInstance B, MaxTensorProduct.toMin_surjective⟩

/-- `CStarAlgebra.IsNuclear.toMinEquiv A B` is the identity on the algebraic tensor product. -/
@[simp] lemma toMinEquiv_of [IsNuclear.{v, max u v} A] {B : Type v} [NonUnitalCStarAlgebra B]
    (x : A ⊗[ℂ] B) : toMinEquiv A B (MaxTensorProduct.of A B x) = MinTensorProduct.of A B x :=
  MaxTensorProduct.toMin_of x

end CStarAlgebra.IsNuclear
