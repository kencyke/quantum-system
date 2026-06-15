module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Dagger categories and dagger monoidal categories

Mathlib's `CategoryTheory` library has no notion of a dagger (`†`) category, so
we introduce a minimal bespoke layer here:

* `CategoryTheory.DaggerCategory` — an involutive, identity-on-objects,
  contravariant assignment `f ↦ f†` on morphisms;
* `CategoryTheory.Unitary` — the predicate `f ≫ f† = 𝟙 ∧ f† ≫ f = 𝟙`;
* `CategoryTheory.DaggerMonoidalCategory` — a monoidal category whose dagger is
  monoidal (`(f ⊗ₘ g)† = f† ⊗ₘ g†`) and whose coherence isomorphisms are
  unitary.

These are the categorical (non-analytic) ingredients of a `†`-tensor category;
the C\*-analytic enrichment (normed hom-spaces, C\*-identity, positivity) is
added on top in `CStarTensorCategory.lean`.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory

universe v u

/-- A **dagger category**: an involutive, identity-on-objects, contravariant
operation `f ↦ f†` on morphisms. -/
class DaggerCategory (C : Type u) [Category.{v} C] where
  /-- The dagger (adjoint) of a morphism. -/
  dagger : {X Y : C} → (X ⟶ Y) → (Y ⟶ X)
  /-- The dagger fixes identities. -/
  dagger_id : ∀ X : C, dagger (𝟙 X) = 𝟙 X
  /-- The dagger is contravariant. -/
  dagger_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
    dagger (f ≫ g) = dagger g ≫ dagger f
  /-- The dagger is involutive. -/
  dagger_dagger : ∀ {X Y : C} (f : X ⟶ Y), dagger (dagger f) = f

/-- Postfix notation `f†` for the dagger of a morphism. -/
scoped postfix:max "†" => DaggerCategory.dagger

attribute [simp] DaggerCategory.dagger_id DaggerCategory.dagger_dagger

/-- A morphism is **unitary** when it is invertible with inverse its dagger. -/
def Unitary {C : Type u} [Category.{v} C] [DaggerCategory C] {X Y : C}
    (f : X ⟶ Y) : Prop :=
  f ≫ f† = 𝟙 X ∧ f† ≫ f = 𝟙 Y

/-- The identity morphism is unitary. -/
lemma Unitary.id {C : Type u} [Category.{v} C] [DaggerCategory C] (X : C) :
    Unitary (𝟙 X) := by
  refine ⟨?_, ?_⟩ <;> simp

/-- Unitaries are closed under composition: `f ≫ g` is unitary whenever `f` and `g`
are. -/
lemma Unitary.comp {C : Type u} [Category.{v} C] [DaggerCategory C] {X Y Z : C}
    {f : X ⟶ Y} {g : Y ⟶ Z} (hf : Unitary f) (hg : Unitary g) : Unitary (f ≫ g) := by
  refine ⟨?_, ?_⟩
  · have h : (f ≫ g) ≫ (f ≫ g)† = f ≫ (g ≫ g†) ≫ f† := by
      rw [DaggerCategory.dagger_comp]; simp only [Category.assoc]
    rw [h, hg.1, Category.id_comp, hf.1]
  · have h : (f ≫ g)† ≫ (f ≫ g) = g† ≫ (f† ≫ f) ≫ g := by
      rw [DaggerCategory.dagger_comp]; simp only [Category.assoc]
    rw [h, hf.2, Category.id_comp, hg.2]

/-- The dagger of a unitary is unitary. -/
lemma Unitary.dagger {C : Type u} [Category.{v} C] [DaggerCategory C] {X Y : C}
    {f : X ⟶ Y} (hf : Unitary f) : Unitary f† := by
  refine ⟨?_, ?_⟩
  · rw [DaggerCategory.dagger_dagger]; exact hf.2
  · rw [DaggerCategory.dagger_dagger]; exact hf.1

/-- A unitary morphism is an **isomorphism**, with inverse its dagger. -/
lemma Unitary.isIso {C : Type u} [Category.{v} C] [DaggerCategory C] {X Y : C}
    {f : X ⟶ Y} (hf : Unitary f) : IsIso f :=
  ⟨⟨f†, hf.1, hf.2⟩⟩

/-- A morphism `p : X ⟶ X` is **positive** in the C\*-categorical sense (Müger,
*Abstract Duality Theory for Symmetric Tensor ∗-Categories*, Definition 1.28): it
factors as `f ≫ f†` for some `f : X ⟶ Y`.  This is the abstract, hom-type-level
counterpart of `Positivity.comp_dagger_nonneg` (`0 ≤ (f ≫ f†).t`) for the concrete
sector category; over a `CStarCategory` the two coincide once `End X` is realised as
a C\*-algebra. -/
def IsPositiveEndo {C : Type u} [Category.{v} C] [DaggerCategory C] {X : C}
    (p : X ⟶ X) : Prop :=
  ∃ (Y : C) (f : X ⟶ Y), p = f ≫ f†

/-- A positive endomorphism is **self-adjoint**: `(f ≫ f†)† = f ≫ f†` by
contravariance of the dagger (Müger Def 1.28). -/
lemma IsPositiveEndo.isSelfAdjoint {C : Type u} [Category.{v} C] [DaggerCategory C]
    {X : C} {p : X ⟶ X} (hp : IsPositiveEndo p) : p† = p := by
  obtain ⟨Y, f, rfl⟩ := hp
  simp only [DaggerCategory.dagger_comp, DaggerCategory.dagger_dagger]

/-- The identity is positive (it factors as `𝟙 = 𝟙 ≫ 𝟙†`). -/
lemma IsPositiveEndo.id {C : Type u} [Category.{v} C] [DaggerCategory C] (X : C) :
    IsPositiveEndo (𝟙 X) :=
  ⟨X, 𝟙 X, by simp⟩

/-- Positivity is preserved under **compression** by an arbitrary morphism: if `p` is
positive then so is `f ≫ p ≫ f†` (the C\*-categorical analogue of `f* a f ≥ 0` for
`a ≥ 0`).  This is what makes the dimension of a subobject positive (R7-B). -/
lemma IsPositiveEndo.conj {C : Type u} [Category.{v} C] [DaggerCategory C] {X Y : C}
    {p : X ⟶ X} (hp : IsPositiveEndo p) (f : Y ⟶ X) :
    IsPositiveEndo (f ≫ p ≫ f†) := by
  obtain ⟨Z, g, rfl⟩ := hp
  exact ⟨Z, f ≫ g, by rw [DaggerCategory.dagger_comp]; simp only [Category.assoc]⟩

/-- A **projection** (a self-adjoint idempotent, `p ≫ p = p` and `p† = p`) is positive:
`p = p ≫ p†`.  This links the subobject/projection theory (R3, R9) to positivity. -/
lemma IsPositiveEndo.of_projection {C : Type u} [Category.{v} C] [DaggerCategory C] {X : C}
    {p : X ⟶ X} (hidem : p ≫ p = p) (hsa : p† = p) : IsPositiveEndo p :=
  ⟨X, p, by rw [hsa, hidem]⟩

/-- `f ≫ f†` is positive (the defining form of positivity). -/
lemma IsPositiveEndo.comp_dagger {C : Type u} [Category.{v} C] [DaggerCategory C] {X Y : C}
    (f : X ⟶ Y) : IsPositiveEndo (f ≫ f†) :=
  ⟨Y, f, rfl⟩

/-- `f† ≫ f` is positive (the other canonical form, via `f = (f†)†`). -/
lemma IsPositiveEndo.dagger_comp {C : Type u} [Category.{v} C] [DaggerCategory C] {X Y : C}
    (f : X ⟶ Y) : IsPositiveEndo (f† ≫ f) :=
  ⟨X, f†, by rw [DaggerCategory.dagger_dagger]⟩

/-- The dagger transfers to any full subcategory: morphisms are the ambient
ones (wrapped by `InducedCategory`), so the dagger acts on the underlying
morphism. -/
instance fullSubcategoryDagger {C : Type u} [Category.{v} C] [DaggerCategory C]
    (P : ObjectProperty C) : DaggerCategory P.FullSubcategory where
  dagger f := { hom := f.hom† }
  dagger_id X := by ext; exact DaggerCategory.dagger_id X.obj
  dagger_comp f g := by ext; exact DaggerCategory.dagger_comp f.hom g.hom
  dagger_dagger f := by ext; exact DaggerCategory.dagger_dagger f.hom

/-- A **dagger monoidal category**: a monoidal category whose dagger is a
monoidal involution and whose coherence isomorphisms are unitary. -/
class DaggerMonoidalCategory (C : Type u) [Category.{v} C] [MonoidalCategory C]
    extends DaggerCategory C where
  /-- The dagger is monoidal. -/
  dagger_tensorHom : ∀ {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂),
    (f ⊗ₘ g)† = f† ⊗ₘ g†
  /-- The associator is unitary. -/
  associator_unitary : ∀ X Y Z : C, ((α_ X Y Z).hom)† = (α_ X Y Z).inv
  /-- The left unitor is unitary. -/
  leftUnitor_unitary : ∀ X : C, ((λ_ X).hom)† = (λ_ X).inv
  /-- The right unitor is unitary. -/
  rightUnitor_unitary : ∀ X : C, ((ρ_ X).hom)† = (ρ_ X).inv

attribute [simp] DaggerMonoidalCategory.dagger_tensorHom
  DaggerMonoidalCategory.associator_unitary
  DaggerMonoidalCategory.leftUnitor_unitary
  DaggerMonoidalCategory.rightUnitor_unitary

end CategoryTheory
