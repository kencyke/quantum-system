/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.OperatorSystem.Arveson
public import QuantumSystem.Analysis.OperatorSystem.ChoiEffros

/-!
# Injective operator systems

A complex vector space `W` with matrix orders, such as an operator system, is **injective**
(`OperatorSystem.Injective`) if completely positive maps into it extend along unital complete order
embeddings of operator systems: for every unital complete order embedding `j : V → V'` and every
completely positive `φ : V → W` there is a completely positive `ψ : V' → W` with `ψ ∘ j = φ`. The
definition tests `V` and `V'` in the universe of `W`; for an operator system `W` the extension then
exists for `V` and `V'` in any universes (`OperatorSystem.Injective.exists_extension`): embedded in
some `B(H)` by the Choi–Effros theorem, `W` is a retract of `B(H)`, and `B(H)` extends in all
universes by Arveson's extension theorem. So `B(H)` is injective
(`OperatorSystem.injective_continuousLinearMap`), and a retract of an injective operator system, a
space `R` with completely positive maps `i : R → W` and `ρ : W → R` such that `ρ ∘ i = id`, is
injective (`OperatorSystem.Injective.of_retract`): extend into `W` and project back.

A unital complete order embedding `κ : V → I` of an operator system into an injective operator system
is an **injective envelope** of `V` (`OperatorSystem.IsInjectiveEnvelope`) when it is rigid: the only
completely positive map `γ : I → I` with `γ ∘ κ = κ` is the identity. Two injective envelopes of `V`
are completely order isomorphic over `V` (`OperatorSystem.IsInjectiveEnvelope.exists_linearEquiv`):
each extends the other's embedding, and the two extensions compose to completely positive maps fixing
`V`, which are identities by rigidity.

## Main definitions

* `OperatorSystem.Injective W` — injectivity of a space `W` with matrix orders.
* `OperatorSystem.IsInjectiveEnvelope κ` — `κ : V → I` is an injective envelope of the operator
  system `V`.

## Main results

* `OperatorSystem.Injective.exists_extension` — an injective operator system extends completely
  positive maps from operator systems in any universes.
* `OperatorSystem.injective_continuousLinearMap` — `B(H)` is injective.
* `OperatorSystem.Injective.of_retract` — a retract of an injective operator system is injective.
* `OperatorSystem.IsInjectiveEnvelope.exists_linearEquiv` — injective envelopes are unique up to
  complete order isomorphism.
-/

@[expose] public section

open scoped CStarAlgebra

universe u

namespace OperatorSystem

/-- A complex vector space `W` with matrix orders, such as an operator system, is **injective** if
completely positive maps into it extend along unital complete order embeddings: for every unital
complete order embedding `j : V → V'` between operator systems and every completely positive
`φ : V → W`, there is a completely positive `ψ : V' → W` with `ψ ∘ j = φ`. The operator systems `V`
and `V'` range over the universe of `W`; for an operator system `W` this gives the extension for `V`
and `V'` in any universes (`OperatorSystem.Injective.exists_extension`). -/
def Injective (W : Type u) [AddCommGroup W] [Module ℂ W]
    [∀ k, PartialOrder (CStarMatrix (Fin k) (Fin k) W)] : Prop :=
  ∀ (V V' : Type u) [AddCommGroup V] [Module ℂ V] [StarAddMonoid V] [StarModule ℂ V] [PartialOrder V]
    [∀ k, PartialOrder (CStarMatrix (Fin k) (Fin k) V)] [One V] [OperatorSystem V] [AddCommGroup V']
    [Module ℂ V'] [StarAddMonoid V'] [StarModule ℂ V'] [PartialOrder V']
    [∀ k, PartialOrder (CStarMatrix (Fin k) (Fin k) V')] [One V'] [OperatorSystem V']
    (j : V →ₗ[ℂ] V') (hj : j.IsCompleteOrderEmbedding), j 1 = 1 →
      ∀ φ : V →CP' W, ∃ ψ : V' →CP' W, ψ.comp hj.toCompletelyPositiveMap' = φ

/-- **`B(H)` is injective**, by Arveson's extension theorem
(`LinearMap.IsCompleteOrderEmbedding.exists_extension_completelyPositiveMap`), which extends
completely positive maps into `B(H)` from operator systems in any universes. -/
lemma injective_continuousLinearMap (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : Injective (H →L[ℂ] H) := by
  intro V V' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j hj hj1 φ
  exact hj.exists_extension_completelyPositiveMap hj1 φ

variable {W : Type*} [AddCommGroup W] [Module ℂ W] [StarAddMonoid W] [StarModule ℂ W] [PartialOrder W]
  [∀ k, PartialOrder (CStarMatrix (Fin k) (Fin k) W)] [One W] [OperatorSystem W]

/-- **An injective operator system extends completely positive maps from operator systems in any
universes.** By the Choi–Effros theorem (`OperatorSystem.isCompleteOrderEmbedding_directSumMap`)
`W` embeds into `B(H)` by `ι`, with `H` in the universe of `W`, and the identity of `W` extends
along `ι` to a completely positive `ρ : B(H) → W`. Arveson's extension theorem extends `ι ∘ φ` to
`ψ' : V' → B(H)`, and `ρ ∘ ψ'` extends `φ`. -/
theorem Injective.exists_extension (hW : Injective W) {V V' : Type*} [AddCommGroup V] [Module ℂ V]
    [StarAddMonoid V] [StarModule ℂ V] [PartialOrder V] [∀ k, PartialOrder (CStarMatrix (Fin k) (Fin k) V)]
    [One V] [OperatorSystem V] [AddCommGroup V'] [Module ℂ V'] [StarAddMonoid V'] [StarModule ℂ V']
    [PartialOrder V'] [∀ k, PartialOrder (CStarMatrix (Fin k) (Fin k) V')] [One V'] [OperatorSystem V']
    {j : V →ₗ[ℂ] V'} (hj : j.IsCompleteOrderEmbedding) (hj1 : j 1 = 1) (φ : V →CP' W) :
    ∃ ψ : V' →CP' W, ψ.comp hj.toCompletelyPositiveMap' = φ := by
  have hι := isCompleteOrderEmbedding_directSumMap W
  obtain ⟨ρ, hρ⟩ := hW W (DirectSumSpace W →L[ℂ] DirectSumSpace W) (directSumMap W) hι
    (directSumMap_one W) (CompletelyPositiveMap'.id W)
  obtain ⟨ψ', hψ'⟩ := hj.exists_extension_completelyPositiveMap hj1 (hι.toCompletelyPositiveMap'.comp φ)
  refine ⟨ρ.comp ψ', CompletelyPositiveMap'.ext fun v => ?_⟩
  change ρ (ψ' (j v)) = φ v
  rw [show ψ' (j v) = directSumMap W (φ v) from DFunLike.congr_fun hψ' v]
  exact DFunLike.congr_fun hρ (φ v)

/-- **A retract of an injective operator system is injective.** If completely positive maps
`i : R → W` and `ρ : W → R` satisfy `ρ ∘ i = id` and `W` is injective, then so is `R`: a completely
positive `φ : V → R` extends, as the map `i ∘ φ` into `W`, to `ψ : V' → W`
(`OperatorSystem.Injective.exists_extension`), and `ρ ∘ ψ` extends `φ`. -/
lemma Injective.of_retract (hW : Injective W) {R : Type*} [AddCommGroup R] [Module ℂ R]
    [∀ k, PartialOrder (CStarMatrix (Fin k) (Fin k) R)] (i : R →CP' W) (ρ : W →CP' R)
    (h : ∀ r, ρ (i r) = r) : Injective R := by
  intro V V' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j hj hj1 φ
  obtain ⟨ψ, hψ⟩ := hW.exists_extension hj hj1 (i.comp φ)
  refine ⟨ρ.comp ψ, CompletelyPositiveMap'.ext fun v => ?_⟩
  change ρ (ψ (j v)) = φ v
  rw [show ψ (j v) = i (φ v) from DFunLike.congr_fun hψ v, h]

/-- A unital complete order embedding `κ : V → I` of an operator system `V` into an operator system
`I` is an **injective envelope** of `V` when `I` is injective and `κ` is rigid: the only completely
positive map `γ : I → I` with `γ ∘ κ = κ` is the identity. -/
structure IsInjectiveEnvelope {V : Type*} [AddCommGroup V] [Module ℂ V] [StarAddMonoid V]
    [StarModule ℂ V] [PartialOrder V] [∀ k, PartialOrder (CStarMatrix (Fin k) (Fin k) V)] [One V]
    [OperatorSystem V] {I : Type*} [AddCommGroup I] [Module ℂ I] [StarAddMonoid I] [StarModule ℂ I]
    [PartialOrder I] [∀ k, PartialOrder (CStarMatrix (Fin k) (Fin k) I)] [One I] [OperatorSystem I]
    (κ : V →ₗ[ℂ] I) : Prop where
  /-- The embedding is unital. -/
  map_one : κ 1 = 1
  /-- The embedding is a complete order embedding. -/
  isCompleteOrderEmbedding : κ.IsCompleteOrderEmbedding
  /-- The extension is injective. -/
  injective : Injective I
  /-- The extension is rigid: a completely positive map of `I` into itself fixing `κ(V)` is the
  identity. -/
  rigid : ∀ γ : I →CP' I, (∀ v, γ (κ v) = κ v) → γ = CompletelyPositiveMap'.id I

/-- **Uniqueness of the injective envelope.** Two injective envelopes `κ₁ : V → I₁` and
`κ₂ : V → I₂` of `V` are completely order isomorphic over `V`. By injectivity
(`OperatorSystem.Injective.exists_extension`), `κ₂` extends along `κ₁` to `α : I₁ → I₂` and `κ₁`
along `κ₂` to `β : I₂ → I₁`; then `β ∘ α` and `α ∘ β` fix `V`, so they are identities by
rigidity. -/
theorem IsInjectiveEnvelope.exists_linearEquiv {V : Type*} [AddCommGroup V] [Module ℂ V]
    [StarAddMonoid V] [StarModule ℂ V] [PartialOrder V] [∀ k, PartialOrder (CStarMatrix (Fin k) (Fin k) V)]
    [One V] [OperatorSystem V] {I₁ : Type*} [AddCommGroup I₁] [Module ℂ I₁] [StarAddMonoid I₁]
    [StarModule ℂ I₁] [PartialOrder I₁] [∀ k, PartialOrder (CStarMatrix (Fin k) (Fin k) I₁)] [One I₁]
    [OperatorSystem I₁] {I₂ : Type*} [AddCommGroup I₂] [Module ℂ I₂] [StarAddMonoid I₂]
    [StarModule ℂ I₂] [PartialOrder I₂] [∀ k, PartialOrder (CStarMatrix (Fin k) (Fin k) I₂)] [One I₂]
    [OperatorSystem I₂] {κ₁ : V →ₗ[ℂ] I₁} {κ₂ : V →ₗ[ℂ] I₂} (h₁ : IsInjectiveEnvelope κ₁)
    (h₂ : IsInjectiveEnvelope κ₂) :
    ∃ e : I₁ ≃ₗ[ℂ] I₂, (e : I₁ →ₗ[ℂ] I₂).IsCompleteOrderEmbedding ∧ ∀ v, e (κ₁ v) = κ₂ v := by
  obtain ⟨hκ₁1, hκ₁, hI₁, hr₁⟩ := h₁
  obtain ⟨hκ₂1, hκ₂, hI₂, hr₂⟩ := h₂
  obtain ⟨α, hα⟩ := hI₂.exists_extension hκ₁ hκ₁1 hκ₂.toCompletelyPositiveMap'
  obtain ⟨β, hβ⟩ := hI₁.exists_extension hκ₂ hκ₂1 hκ₁.toCompletelyPositiveMap'
  have hαv (v : V) : α (κ₁ v) = κ₂ v := DFunLike.congr_fun hα v
  have hβv (v : V) : β (κ₂ v) = κ₁ v := DFunLike.congr_fun hβ v
  have hβα : β.comp α = CompletelyPositiveMap'.id I₁ := hr₁ _ fun v => by
    change β (α (κ₁ v)) = κ₁ v
    rw [hαv, hβv]
  have hαβ : α.comp β = CompletelyPositiveMap'.id I₂ := hr₂ _ fun v => by
    change α (β (κ₂ v)) = κ₂ v
    rw [hβv, hαv]
  let e : I₁ ≃ₗ[ℂ] I₂ :=
    { α.toLinearMap with
      invFun := β
      left_inv := fun x => DFunLike.congr_fun hβα x
      right_inv := fun x => DFunLike.congr_fun hαβ x }
  refine ⟨e, fun k X => ⟨fun hX => ?_, α.map_cstarMatrix_nonneg⟩, hαv⟩
  have h := β.map_cstarMatrix_nonneg hX
  convert h using 1
  exact (CStarMatrix.ext fun i j => DFunLike.congr_fun hβα (X i j)).symm

end OperatorSystem
