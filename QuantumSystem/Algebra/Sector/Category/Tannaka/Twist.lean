module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import QuantumSystem.Algebra.Sector.Category.Dagger

/-!
# The twist of an object — R7-B2

For an object `X` with a left dual in a braided dagger monoidal category, the
**twist** (Müger, *Abstract Duality Theory for Symmetric Tensor ∗-Categories*,
Definition 1.43) is

```
Θ(X) = (r* ⊗ id_X) ∘ (id_{ᘁX} ⊗ c_{X,X}) ∘ (r ⊗ id_X) : X ⟶ X,
```

where `r = η_{ᘁX, X} : 𝟙 ⟶ ᘁX ⊗ X` is the coevaluation of the left dual and
`r* = r†` its dagger.  In a symmetric tensor ∗-category it satisfies `Θ(X)² = 𝟙`
and is a monoidal natural transformation (Müger Lemma 1.44(v)); for irreducible `X`
it is `±1`, recording whether `X` is bosonic or fermionic — the parity used in the
super/bosonization step (R7-H).

This file fixes the **definition** (Müger Def 1.43).  The properties (`Θ² = 𝟙`,
naturality, monoidality — Lemma 1.44) are the substantive content deferred to the
rest of R7-B; they require a *standard* solution and the dagger–rigid compatibility.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    [DaggerMonoidalCategory C]

/-- The **twist** `Θ(X)` of an object with a left dual (Müger Definition 1.43):
`Θ(X) = (r* ⊗ id) ∘ (id ⊗ c_{X,X}) ∘ (r ⊗ id)` with `r = η_{ᘁX, X}` the left-dual
coevaluation and `r*` its dagger.  Associators are inserted by `⊗≫`. -/
noncomputable def categoricalTwist (X : C) [HasLeftDual X] : X ⟶ X :=
  (λ_ X).inv ≫ (η_ (ᘁX) X ▷ X) ⊗≫ ((ᘁX) ◁ (β_ X X).hom) ⊗≫
    (DaggerCategory.dagger (η_ (ᘁX) X) ▷ X) ≫ (λ_ X).hom

/-- A braided dagger rigid category is **even** (Müger §1.4) when every object has
trivial twist, `Θ(X) = 𝟙`.  Even symmetric tensor ∗-categories reconstruct compact
*groups* (Müger Theorem 2.12, R7-G); the general (super)group case reduces to the
even one by bosonization — twisting the symmetry by `Θ` (R7-H, Theorem 2.18). -/
def IsEven [LeftRigidCategory C] : Prop :=
  ∀ X : C, categoricalTwist X = 𝟙 X

/-- The **twist of the unit object is trivial** (Müger Lemma 1.44, the normalisation
`Θ(𝟙_C) = 𝟙`): for the canonical self-duality of `𝟙_C` (`exactPairingUnit`,
`η_ 𝟙 𝟙 = (ρ_𝟙)⁻¹`) the coevaluation and its dagger are the right-unitor and its inverse
(`rightUnitor_unitary`), the braiding `β_{𝟙,𝟙}` collapses to the identity, and the
associators of `⊗≫` cancel, so the whole composite reduces to `(ρ_𝟙)⁻¹ ≫ (ρ_𝟙) = 𝟙`.

This is the twist analogue of `categoricalDim_unit` (Müger §1.4): the substantive twist
properties (`Θ² = 𝟙`, naturality, monoidality — Lemma 1.44(v)) still require a standard
solution (roadmap S7) and are deferred, but the unit normalisation needed for the `IsEven`
bookkeeping is available now.  The dagger comes from `DaggerMonoidalCategory`, so the
unitor-unitarity of the dagger (`rightUnitor_unitary`) applies to the very dagger appearing
in `categoricalTwist` — there is a single dagger instance, with no diamond. -/
@[simp] lemma categoricalTwist_unit :
    categoricalTwist (𝟙_ C) = 𝟙 (𝟙_ C) := by
  have hη : η_ (ᘁ(𝟙_ C)) (𝟙_ C) = (ρ_ (𝟙_ C)).inv := rfl
  have hd : ((ρ_ (𝟙_ C)).inv : 𝟙_ C ⟶ _)† = (ρ_ (𝟙_ C)).hom := by
    rw [← DaggerMonoidalCategory.rightUnitor_unitary (𝟙_ C), DaggerCategory.dagger_dagger]
  rw [categoricalTwist]
  simp only [hη, monoidalComp, MonoidalCategory.unitors_equal,
    MonoidalCategory.unitors_inv_equal, hd]
  simp

end CategoryTheory
