/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import QuantumSystem.Analysis.CStarAlgebra.TensorProduct.Maximal.Associativity
public import QuantumSystem.Analysis.CStarAlgebra.TensorProduct.Minimal.Associativity
public import QuantumSystem.Analysis.CStarAlgebra.TensorProduct.PiMinimal

/-!
# Nuclearity of the minimal tensor product

The minimal tensor product of two nuclear C⋆-algebras is nuclear
(`CStarAlgebra.IsNuclear.minTensorProduct`). For a C⋆-algebra `C` and `t` in the triple algebraic
tensor product, the maximal norm of `t` in `(A ⊗ₘᵢₙ B) ⊗ₘₐₓ C` is bounded by its norm in
`A ⊗ₘₐₓ (B ⊗ₘₐₓ C)` (`MaxTensorProduct.norm_apply_le_norm_of_assoc`), which is bounded by its norm in
`A ⊗ₘᵢₙ (B ⊗ₘᵢₙ C)` as `A` and `B` are nuclear, and that is its norm in `(A ⊗ₘᵢₙ B) ⊗ₘᵢₙ C`
(`MinTensorProduct.norm_of_assoc`). The triple algebraic tensor product being dense in
`(A ⊗ₘᵢₙ B) ⊗ₘₐₓ C`, the canonical map onto `(A ⊗ₘᵢₙ B) ⊗ₘᵢₙ C` is isometric.

## Main results

* `CStarAlgebra.IsNuclear.minTensorProduct` — `A ⊗ₘᵢₙ B` is nuclear when `A` and `B` are.
* `CStarAlgebra.IsNuclear.piMinTensorProduct` — the minimal tensor product of finitely many nuclear
  C⋆-algebras is nuclear.
-/

@[expose] public section

open scoped TensorProduct MinTensorProduct MaxTensorProduct PiMinTensorProduct CStarAlgebra

universe u v w w'

namespace CStarAlgebra.IsNuclear

variable {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- On the triple algebraic tensor product, the maximal norm of `(A ⊗ₘᵢₙ B) ⊗ₘₐₓ C` is bounded by
the minimal norm of `(A ⊗ₘᵢₙ B) ⊗ₘᵢₙ C`. -/
private lemma norm_maxOf_le_norm_minOf {C : Type w} [NonUnitalCStarAlgebra C]
    [IsNuclear.{max v w, max u v w} A] [IsNuclear.{w, max v w} B] (t : (A ⊗[ℂ] B) ⊗[ℂ] C) :
    ‖MaxTensorProduct.of (A ⊗ₘᵢₙ B) C
        (TensorProduct.map (MinTensorProduct.of A B : A ⊗[ℂ] B →ₗ[ℂ] A ⊗ₘᵢₙ B) LinearMap.id t)‖ ≤
      ‖MinTensorProduct.of (A ⊗ₘᵢₙ B) C
        (TensorProduct.map (MinTensorProduct.of A B : A ⊗[ℂ] B →ₗ[ℂ] A ⊗ₘᵢₙ B) LinearMap.id t)‖ := by
  let Ψ : (A ⊗ₘₐₓ B) ⊗[ℂ] C →⋆ₙₐ[ℂ] (A ⊗ₘᵢₙ B) ⊗ₘₐₓ C :=
    (MaxTensorProduct.of (A ⊗ₘᵢₙ B) C).comp
      (NonUnitalStarAlgebra.TensorProduct.map (MaxTensorProduct.toMin A B) (NonUnitalStarAlgHom.id ℂ C))
  let Φ : A ⊗[ℂ] (B ⊗ₘₐₓ C) →⋆ₙₐ[ℂ] A ⊗ₘᵢₙ (B ⊗ₘᵢₙ C) :=
    (MinTensorProduct.of A (B ⊗ₘᵢₙ C)).comp
      (NonUnitalStarAlgebra.TensorProduct.map (NonUnitalStarAlgHom.id ℂ A) (MaxTensorProduct.toMin B C))
  have hΦ : Function.Injective Φ :=
    MinTensorProduct.of_injective.comp (Module.Flat.lTensor_preserves_injective_linearMap
      (M := A) (MaxTensorProduct.toMin B C : B ⊗ₘₐₓ C →ₗ[ℂ] B ⊗ₘᵢₙ C)
      (iff_toMin_injective.1 inferInstance C))
  have hΨ : Ψ (TensorProduct.map (MaxTensorProduct.of A B : A ⊗[ℂ] B →ₗ[ℂ] A ⊗ₘₐₓ B) LinearMap.id t) =
      MaxTensorProduct.of (A ⊗ₘᵢₙ B) C
        (TensorProduct.map (MinTensorProduct.of A B : A ⊗[ℂ] B →ₗ[ℂ] A ⊗ₘᵢₙ B) LinearMap.id t) := by
    have e : (MaxTensorProduct.toMin A B : A ⊗ₘₐₓ B →ₗ[ℂ] A ⊗ₘᵢₙ B) ∘ₗ
        (MaxTensorProduct.of A B : A ⊗[ℂ] B →ₗ[ℂ] A ⊗ₘₐₓ B) = MinTensorProduct.of A B :=
      LinearMap.ext MaxTensorProduct.toMin_of
    simp only [Ψ, NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgebra.TensorProduct.map_apply]
    rw [TensorProduct.map_map, e]
    rfl
  have hΦ' : Φ (TensorProduct.map LinearMap.id (MaxTensorProduct.of B C : B ⊗[ℂ] C →ₗ[ℂ] B ⊗ₘₐₓ C)
      (TensorProduct.assoc ℂ A B C t)) =
      MinTensorProduct.of A (B ⊗ₘᵢₙ C) (TensorProduct.map LinearMap.id
        (MinTensorProduct.of B C : B ⊗[ℂ] C →ₗ[ℂ] B ⊗ₘᵢₙ C) (TensorProduct.assoc ℂ A B C t)) := by
    have e : (MaxTensorProduct.toMin B C : B ⊗ₘₐₓ C →ₗ[ℂ] B ⊗ₘᵢₙ C) ∘ₗ
        (MaxTensorProduct.of B C : B ⊗[ℂ] C →ₗ[ℂ] B ⊗ₘₐₓ C) = MinTensorProduct.of B C :=
      LinearMap.ext MaxTensorProduct.toMin_of
    simp only [Φ, NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgebra.TensorProduct.map_apply]
    rw [TensorProduct.map_map, e]
    rfl
  rw [← hΨ, MinTensorProduct.norm_of_assoc, ← hΦ']
  refine (MaxTensorProduct.norm_apply_le_norm_of_assoc Ψ t).trans ?_
  exact (norm_apply_le_norm_of (A := A) (B ⊗ₘₐₓ C) _ (MaxTensorProduct.of A (B ⊗ₘₐₓ C)) _).trans
    (MinTensorProduct.norm_of_le_norm_apply hΦ _)

/-- **The minimal tensor product of two nuclear C⋆-algebras is nuclear.** The proof applies the
nuclearity of `A` to `B ⊗ₘₐₓ C`, whose universe it reaches by `CStarAlgebra.IsNuclear.lift_universes`. -/
instance minTensorProduct [IsNuclear.{w, max u w} A] [IsNuclear.{w, max v w} B] :
    IsNuclear.{w, w'} (A ⊗ₘᵢₙ B) := by
  have : IsNuclear.{max v w, max u v w} A := lift_universes
  refine of_norm_of_le fun C _ x => ?_
  rw [← MaxTensorProduct.toMin_of]
  suffices h : ∀ y : (A ⊗ₘᵢₙ B) ⊗ₘₐₓ C, ‖y‖ ≤ ‖MaxTensorProduct.toMin (A ⊗ₘᵢₙ B) C y‖ from h _
  have hd : DenseRange fun t : (A ⊗[ℂ] B) ⊗[ℂ] C => MaxTensorProduct.of (A ⊗ₘᵢₙ B) C
      (TensorProduct.map (MinTensorProduct.of A B : A ⊗[ℂ] B →ₗ[ℂ] A ⊗ₘᵢₙ B) LinearMap.id t) :=
    NonUnitalStarAlgHom.denseRange_comp_map _ MaxTensorProduct.denseRange_of
      MinTensorProduct.denseRange_of denseRange_id
  intro y
  refine hd.induction_on y
    (isClosed_le continuous_norm (map_continuous _).norm) fun t => ?_
  rw [MaxTensorProduct.toMin_of]
  exact norm_maxOf_le_norm_minOf t

/-- **The minimal tensor product of finitely many nuclear C⋆-algebras is nuclear**, by induction on
the number of factors: splitting off one index, `⨂ₘᵢₙ i, A i` is the minimal tensor product
of two minimal tensor products of fewer factors (`PiMinTensorProduct.splitEquiv`), and over a single
index it is that factor (`PiMinTensorProduct.subsingletonEquiv`). -/
instance piMinTensorProduct.{uι, uA} {ι : Type uι} [Fintype ι] {A : ι → Type uA}
    [∀ i, NonUnitalCStarAlgebra (A i)] [∀ i, IsNuclear.{w, max uA w} (A i)] :
    IsNuclear.{w, w'} (⨂ₘᵢₙ i, A i) := by
  have (i : ι) : IsNuclear.{max uι uA w, max uι uA w} (A i) := lift_universes
  suffices h : ∀ (κ : Type uι) [Fintype κ] (A : κ → Type uA) [∀ i, NonUnitalCStarAlgebra (A i)]
      [∀ i, IsNuclear.{max uι uA w, max uι uA w} (A i)],
      IsNuclear.{max uι uA w, max uι uA w} (⨂ₘᵢₙ i, A i) by
    have := h ι A
    exact lift_universes
  intro κ _
  refine Fintype.induction_subsingleton_or_nontrivial (P := fun κ _ => ∀ (A : κ → Type uA)
    [∀ i, NonUnitalCStarAlgebra (A i)] [∀ i, IsNuclear.{max uι uA w, max uι uA w} (A i)],
      IsNuclear.{max uι uA w, max uι uA w} (⨂ₘᵢₙ i, A i)) κ ?_ ?_
  · intro κ _ _ A _ _
    rcases isEmpty_or_nonempty κ with hκ | hκ
    · have : ∀ i, FiniteDimensional ℂ (A i) := fun i => isEmptyElim i
      infer_instance
    · obtain ⟨i₀⟩ := hκ
      exact of_starAlgEquiv (PiMinTensorProduct.subsingletonEquiv A i₀).symm
  · intro κ _ _ ih A _ _
    classical
    obtain ⟨i₀⟩ : Nonempty κ := inferInstance
    obtain ⟨j, hj⟩ := exists_ne i₀
    have := @ih {i // i = i₀} (Subtype.fintype _)
      (by convert Fintype.card_subtype_lt (p := fun i => i = i₀) hj) (fun i => A i)
    have := @ih {i // ¬i = i₀} (Subtype.fintype _)
      (Fintype.card_subtype_lt (p := fun i => ¬i = i₀) (x := i₀) (not_not.2 rfl)) (fun i => A i)
    exact of_starAlgEquiv (PiMinTensorProduct.splitEquiv A fun i => i = i₀).symm

end CStarAlgebra.IsNuclear
