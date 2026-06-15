module

public import QuantumSystem.Algebra.Sector.Category.Tannaka.STCStar

/-!
# Commutative monoid objects and their global sections — S11 (R7-B6)

Müger, *Abstract Duality Theory for Symmetric Tensor ∗-Categories*, §1.5 and §2.4:
the Doplicher–Roberts/Deligne reconstruction is organised around **commutative
monoid objects** `(Q, m, η)` in the symmetric tensor category, their **modules**,
and the algebra of **global sections** `Γ_Q = Hom(𝟙, Q)`.  The absorbing monoid `B`
with `Γ_B = ℂ` (Müger Thm 2.40) is the device producing the fiber functor.

This file fixes the **minimal interface** for that layer (the higher structure —
the absorbing monoid, its filtered colimit in `Ind C`, and `Γ_B = ℂ` — is the
deferred Phase-3 epic S20–S22, so the API here is kept deliberately small, in the
same anti-speculative spirit as `HasIndCompletion`):

* `CommMonoidObject C` — a commutative monoid object `(X, μ, η)`;
* `ModuleObject Q` — a left module over a monoid object;
* `Gamma Q = 𝟙 ⟶ Q.X` — the **global sections**, a `ℂ`-module with the convolution
  product `f ⋆ g = (λ_𝟙)⁻¹ ≫ (f ⊗ g) ≫ μ` and unit `η` (the carrier of the
  commutative algebra `Γ_Q`).

This is **S11** of the Tannaka roadmap (`implementation-notes.md` §4).
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-! ### Commutative monoid objects -/

/-- A **commutative monoid object** `(X, μ, η)` in a braided monoidal category (Müger
§1.5): an object `X` with a multiplication `μ : X ⊗ X ⟶ X` and unit `η : 𝟙 ⟶ X`
satisfying associativity, the unit laws and commutativity (with respect to the
braiding).  The field forms follow Mathlib's `Mon_` convention. -/
structure CommMonoidObject (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [BraidedCategory C] where
  /-- The underlying object. -/
  X : C
  /-- The multiplication `μ : X ⊗ X ⟶ X`. -/
  mul : X ⊗ X ⟶ X
  /-- The unit `η : 𝟙 ⟶ X`. -/
  one : 𝟙_ C ⟶ X
  /-- Left unit law: `(η ▷ X) ≫ μ = (λ_ X).hom`. -/
  one_mul : (one ▷ X) ≫ mul = (λ_ X).hom
  /-- Right unit law: `(X ◁ η) ≫ μ = (ρ_ X).hom`. -/
  mul_one : (X ◁ one) ≫ mul = (ρ_ X).hom
  /-- Associativity: `(μ ▷ X) ≫ μ = (α_ X X X).hom ≫ (X ◁ μ) ≫ μ`. -/
  mul_assoc : (mul ▷ X) ≫ mul = (α_ X X X).hom ≫ (X ◁ mul) ≫ mul
  /-- Commutativity: `(β_ X X).hom ≫ μ = μ`. -/
  mul_comm : (β_ X X).hom ≫ mul = mul

/-- A **left module** over a monoid object `Q` (Müger §1.5): an object `M` with an
action `act : Q.X ⊗ M ⟶ M` compatible with the unit and multiplication of `Q`. -/
structure ModuleObject [BraidedCategory C] (Q : CommMonoidObject C) where
  /-- The underlying object of the module. -/
  M : C
  /-- The action `Q.X ⊗ M ⟶ M`. -/
  act : Q.X ⊗ M ⟶ M
  /-- The unit acts as the identity: `(η ▷ M) ≫ act = (λ_ M).hom`. -/
  one_act : (Q.one ▷ M) ≫ act = (λ_ M).hom
  /-- The action is associative with the multiplication:
  `(μ ▷ M) ≫ act = (α_ Q.X Q.X M).hom ≫ (Q.X ◁ act) ≫ act`. -/
  mul_act : (Q.mul ▷ M) ≫ act = (α_ Q.X Q.X M).hom ≫ (Q.X ◁ act) ≫ act

/-! ### Global sections `Γ_Q = Hom(𝟙, Q)` -/

section Gamma

variable [BraidedCategory C]

/-- The **global sections** `Γ_Q = Hom(𝟙, Q.X)` of a monoid object (Müger §2.4): a
`ℂ`-module (inherited from the hom-space) carrying the convolution algebra of `Q`.
The absorbing monoid's `Γ_B = ℂ` (Müger Thm 2.40) lives here. -/
abbrev Gamma (Q : CommMonoidObject C) : Type v := 𝟙_ C ⟶ Q.X

/-- The **convolution product** on `Γ_Q`: `f ⋆ g = (λ_𝟙)⁻¹ ≫ (f ⊗ g) ≫ μ`. -/
noncomputable def Gamma.mul {Q : CommMonoidObject C} (f g : Gamma Q) : Gamma Q :=
  (λ_ (𝟙_ C)).inv ≫ (f ⊗ₘ g) ≫ Q.mul

/-- The **unit** of `Γ_Q` is the monoid unit `η`. -/
def Gamma.one {Q : CommMonoidObject C} : Gamma Q := Q.one

@[simp] lemma Gamma.mul_def {Q : CommMonoidObject C} (f g : Gamma Q) :
    Gamma.mul f g = (λ_ (𝟙_ C)).inv ≫ (f ⊗ₘ g) ≫ Q.mul := rfl

@[simp] lemma Gamma.one_def {Q : CommMonoidObject C} :
    (Gamma.one : Gamma Q) = Q.one := rfl

end Gamma

end CategoryTheory
