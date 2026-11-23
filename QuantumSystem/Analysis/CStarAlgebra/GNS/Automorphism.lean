/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
public import QuantumSystem.Analysis.CStarAlgebra.GNS.Representation

/-!
# Invariant involutions in GNS representations

A ⋆-automorphism `θ` of `A` that preserves a positive functional `f`, `f ∘ θ = f`, is implemented
in every GNS triplet `(π, H, ξ)` of `f` by a unitary fixing `ξ`: precomposing `π` with `θ` gives a
second GNS triplet `(π ∘ θ, H, ξ)` of `f`, and the unitary equivalence of the two
(`GNS.Representation.unique_up_to_unitary_equivalence`) sends `π a ξ` to `π (θ a) ξ`. When `θ` is
an involution, so is the unitary, which is then selfadjoint: a grading of `H` implementing `θ`,
`π (θ a) = Γ π a Γ`.

## Main definitions and results

* `GNS.Representation.compStarAlgEquiv T θ hf` — the GNS triplet `(π ∘ θ, H, ξ)`.
* **`GNS.Representation.exists_implementing`** — an `f`-preserving involutive ⋆-automorphism is
  implemented by a selfadjoint unitary `Γ` with `Γ (π a ξ) = π (θ a) ξ`.
* `GNS.Representation.implementing` — that unitary; it is `1` when `θ` is the identity
  (`GNS.Representation.implementing_eq_one`).
-/

@[expose] public section

open scoped ComplexOrder

namespace GNS.Representation

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {f : A →ₚ[ℂ] ℂ}

/-- The GNS triplet `(π ∘ θ, H, ξ)` of `f` for a ⋆-automorphism `θ` preserving `f`: its orbit is that
of `T`, since `θ` is surjective. -/
noncomputable def compStarAlgEquiv (T : Representation f) (θ : A ≃⋆ₐ[ℂ] A)
    (hf : ∀ a, f (θ a) = f a) : Representation f where
  toCStarRep := { T.toCStarRep with π := T.π.comp θ.toNonUnitalStarAlgHom }
  ξ := T.ξ
  cyclic := by
    have hr : Set.range ((T.π.comp θ.toNonUnitalStarAlgHom : A →⋆ₙₐ[ℂ] (T.H →L[ℂ] T.H)) :
        A → T.H →L[ℂ] T.H) = Set.range (T.π : A → T.H →L[ℂ] T.H) :=
      θ.toEquiv.surjective.range_comp _
    exact hr ▸ T.cyclic
  gns_condition a := by
    rw [← hf]
    exact T.gns_condition (θ a)

/-- Two operators that agree on the orbit of the cyclic vector are equal. -/
lemma eq_of_apply_orbit (T : Representation f) {U V : T.H →L[ℂ] T.H}
    (h : ∀ a, U (T.π a T.ξ) = V (T.π a T.ξ)) : U = V :=
  DFunLike.coe_injective <| Continuous.ext_on T.denseRange_orbit (map_continuous _)
    (map_continuous _) (by rintro _ ⟨a, rfl⟩; exact h a)

/-- **An invariant involution is implemented by a grading of the GNS space**: if `θ` is an
involutive ⋆-automorphism with `f ∘ θ = f`, a selfadjoint unitary `Γ` sends `π a ξ` to `π (θ a) ξ`
and implements `θ`, `π (θ a) = Γ π a Γ`. -/
theorem exists_implementing (T : Representation f) (θ : A ≃⋆ₐ[ℂ] A)
    (hθθ : ∀ a, θ (θ a) = a) (hf : ∀ a, f (θ a) = f a) :
    ∃ Γ : T.H →L[ℂ] T.H, IsSelfAdjoint Γ ∧ Γ * Γ = 1 ∧
      (∀ a, Γ (T.π a T.ξ) = T.π (θ a) T.ξ) ∧ ∀ a, T.π (θ a) = Γ * T.π a * Γ := by
  obtain ⟨U⟩ := unique_up_to_unitary_equivalence (T.compStarAlgEquiv θ hf) T
  let V : T.H ≃ₗᵢ[ℂ] T.H := U.toLinearIsometryEquiv
  let Γ : T.H →L[ℂ] T.H := (V : T.H →L[ℂ] T.H)
  have hint : ∀ a, Γ * T.π (θ a) = T.π a * Γ := fun a => U.intertwines a
  have hξ : Γ T.ξ = T.ξ := U.map_cyclic_vector
  have horb : ∀ a, Γ (T.π a T.ξ) = T.π (θ a) T.ξ := fun a => by
    have := congrArg (fun F : T.H →L[ℂ] T.H => F T.ξ) (hint (θ a))
    simp only [hθθ] at this
    change Γ (T.π a T.ξ) = T.π (θ a) (Γ T.ξ) at this
    rwa [hξ] at this
  have hΓΓ : Γ * Γ = 1 := T.eq_of_apply_orbit fun a => by
    change Γ (Γ _) = _
    rw [horb, horb, hθθ]
    rfl
  have hU : Γ ∈ unitary (T.H →L[ℂ] T.H) := by
    change (V : T.H →L[ℂ] T.H) ∈ unitary (T.H →L[ℂ] T.H)
    rw [← Unitary.coe_symm_linearIsometryEquiv_apply]
    exact (Unitary.linearIsometryEquiv.symm V).2
  have hsa : star Γ = Γ :=
    calc star Γ = star Γ * (Γ * Γ) := by rw [hΓΓ, mul_one]
      _ = Γ := by rw [← mul_assoc, Unitary.star_mul_self_of_mem hU, one_mul]
  refine ⟨Γ, hsa, hΓΓ, horb, fun a => ?_⟩
  calc T.π (θ a) = Γ * Γ * T.π (θ a) := by rw [hΓΓ, one_mul]
    _ = Γ * T.π a * Γ := by rw [mul_assoc Γ Γ, hint, mul_assoc]

/-- The selfadjoint unitary implementing an `f`-preserving involutive ⋆-automorphism `θ` in the GNS
triplet `T` (`exists_implementing`). -/
noncomputable def implementing (T : Representation f) (θ : A ≃⋆ₐ[ℂ] A)
    (hθθ : ∀ a, θ (θ a) = a) (hf : ∀ a, f (θ a) = f a) : T.H →L[ℂ] T.H :=
  (T.exists_implementing θ hθθ hf).choose

variable (T : Representation f) (θ : A ≃⋆ₐ[ℂ] A) (hθθ : ∀ a, θ (θ a) = a)
  (hf : ∀ a, f (θ a) = f a)

/-- The implementing unitary is selfadjoint. -/
lemma isSelfAdjoint_implementing : IsSelfAdjoint (T.implementing θ hθθ hf) :=
  (T.exists_implementing θ hθθ hf).choose_spec.1

/-- The implementing unitary is an involution. -/
lemma implementing_mul_implementing :
    T.implementing θ hθθ hf * T.implementing θ hθθ hf = 1 :=
  (T.exists_implementing θ hθθ hf).choose_spec.2.1

/-- The implementing unitary sends `π a ξ` to `π (θ a) ξ`. -/
lemma implementing_apply_orbit (a : A) :
    T.implementing θ hθθ hf (T.π a T.ξ) = T.π (θ a) T.ξ :=
  (T.exists_implementing θ hθθ hf).choose_spec.2.2.1 a

/-- The implementing unitary implements `θ`: `π (θ a) = Γ π a Γ`. -/
lemma π_apply_eq_implementing_mul (a : A) :
    T.π (θ a) = T.implementing θ hθθ hf * T.π a * T.implementing θ hθθ hf :=
  (T.exists_implementing θ hθθ hf).choose_spec.2.2.2 a

/-- The identity is implemented by `1`. -/
lemma implementing_eq_one (hθ : ∀ a, θ a = a) : T.implementing θ hθθ hf = 1 :=
  T.eq_of_apply_orbit fun a => by rw [implementing_apply_orbit, hθ]; rfl

end GNS.Representation
