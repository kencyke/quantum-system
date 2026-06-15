module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import QuantumSystem.Algebra.Sector.Category.CStarTensorCategory

/-!
# The endomorphism category `End(A)` of a C\*-algebra

For a (unital) C\*-algebra `A`, the **category of `*`-endomorphisms** has:

* objects: unital `*`-endomorphisms `A →⋆ₐ[ℂ] A` (wrapped in `StarEndoCat A`);
* morphisms `ρ ⟶ σ`: **intertwiners**, elements `t : A` with
  `t * ρ a = σ a * t` for all `a`;
* composition: multiplication in `A`;
* tensor product: composition of endomorphisms `ρ ⊗ σ := ρ ∘ σ`.

Because `StarAlgHom.comp` is definitionally associative and unital (its
underlying function is ordinary function composition, and the bundled proof
fields are proof-irrelevant), `End(A)` is a **strict** monoidal category: the
associator and unitors are `Iso.refl`.  The dagger `t ↦ star t` makes it a
`DaggerMonoidalCategory`.

This is the abstract "monoidal category constructed from a C\*-algebra"; taking
`A` to be the quasi-local algebra of a local net realises the sector category
(`Sector/Net/`).
-/

@[expose] public section

namespace CategoryTheory

universe u

/-- Objects of `End(A)`: unital `*`-endomorphisms of `A`. -/
structure StarEndoCat (A : Type u) [CStarAlgebra A] where
  /-- The underlying unital `*`-endomorphism. -/
  endo : A →⋆ₐ[ℂ] A

namespace StarEndo

variable {A : Type u} [CStarAlgebra A]

/-- A morphism `ρ ⟶ σ` in `End(A)`: an intertwiner `t` with
`t * ρ a = σ a * t`. -/
structure Intertwiner (ρ σ : StarEndoCat A) where
  /-- The underlying algebra element. -/
  t : A
  /-- The intertwining relation. -/
  intertwines : ∀ a : A, t * ρ.endo a = σ.endo a * t

attribute [ext] Intertwiner

/-- The identity intertwiner. -/
def homId (ρ : StarEndoCat A) : Intertwiner ρ ρ where
  t := 1
  intertwines a := by rw [one_mul, mul_one]

/-- Composition of intertwiners (multiplication in `A`, in diagrammatic order). -/
def homComp {ρ σ τ : StarEndoCat A} (f : Intertwiner ρ σ) (g : Intertwiner σ τ) :
    Intertwiner ρ τ where
  t := g.t * f.t
  intertwines a := by
    rw [mul_assoc, f.intertwines a, ← mul_assoc, g.intertwines a, mul_assoc]

@[simp] lemma homId_t (ρ : StarEndoCat A) : (homId ρ).t = 1 := rfl

@[simp] lemma homComp_t {ρ σ τ : StarEndoCat A} (f : Intertwiner ρ σ)
    (g : Intertwiner σ τ) : (homComp f g).t = g.t * f.t := rfl

instance : Category (StarEndoCat A) where
  Hom ρ σ := Intertwiner ρ σ
  id ρ := homId ρ
  comp f g := homComp f g
  id_comp f := Intertwiner.ext (mul_one f.t)
  comp_id f := Intertwiner.ext (one_mul f.t)
  assoc f g h := Intertwiner.ext (mul_assoc h.t g.t f.t).symm

@[simp] lemma id_t (ρ : StarEndoCat A) : (𝟙 ρ : ρ ⟶ ρ).t = 1 := rfl

@[simp] lemma comp_t {ρ σ τ : StarEndoCat A} (f : ρ ⟶ σ) (g : σ ⟶ τ) :
    (f ≫ g).t = g.t * f.t := rfl

/-! ### Strict monoidal structure: tensor = composition of endomorphisms -/

open MonoidalCategory

/-- Tensor product of objects: composition of endomorphisms. -/
def tensorObj (ρ σ : StarEndoCat A) : StarEndoCat A := ⟨ρ.endo.comp σ.endo⟩

@[simp] lemma tensorObj_endo_apply (ρ σ : StarEndoCat A) (a : A) :
    (tensorObj ρ σ).endo a = ρ.endo (σ.endo a) := rfl

/-- Left whiskering: `X ◁ f` acts as `X(f.t)`. -/
def whiskerLeftHom (X : StarEndoCat A) {Y₁ Y₂ : StarEndoCat A} (f : Y₁ ⟶ Y₂) :
    tensorObj X Y₁ ⟶ tensorObj X Y₂ where
  t := X.endo f.t
  intertwines a := by
    change X.endo f.t * X.endo (Y₁.endo a) = X.endo (Y₂.endo a) * X.endo f.t
    rw [← map_mul, ← map_mul, f.intertwines a]

/-- Right whiskering: `f ▷ Y` acts as `f.t`. -/
def whiskerRightHom {X₁ X₂ : StarEndoCat A} (f : X₁ ⟶ X₂) (Y : StarEndoCat A) :
    tensorObj X₁ Y ⟶ tensorObj X₂ Y where
  t := f.t
  intertwines a := f.intertwines (Y.endo a)

@[simp] lemma whiskerLeftHom_t (X : StarEndoCat A) {Y₁ Y₂ : StarEndoCat A}
    (f : Y₁ ⟶ Y₂) : (whiskerLeftHom X f).t = X.endo f.t := rfl

@[simp] lemma whiskerRightHom_t {X₁ X₂ : StarEndoCat A} (f : X₁ ⟶ X₂)
    (Y : StarEndoCat A) : (whiskerRightHom f Y).t = f.t := rfl

instance : MonoidalCategoryStruct (StarEndoCat A) where
  tensorObj := tensorObj
  whiskerLeft X _ _ f := whiskerLeftHom X f
  whiskerRight f Y := whiskerRightHom f Y
  tensorUnit := ⟨StarAlgHom.id ℂ A⟩
  associator _ _ _ := Iso.refl _
  leftUnitor _ := Iso.refl _
  rightUnitor _ := Iso.refl _

@[simp] lemma monoidalTensorObj_endo_apply (ρ σ : StarEndoCat A) (a : A) :
    (ρ ⊗ σ).endo a = ρ.endo (σ.endo a) := rfl

@[simp] lemma whiskerLeft_t (X : StarEndoCat A) {Y₁ Y₂ : StarEndoCat A}
    (f : Y₁ ⟶ Y₂) : (X ◁ f).t = X.endo f.t := rfl

@[simp] lemma whiskerRight_t {X₁ X₂ : StarEndoCat A} (f : X₁ ⟶ X₂)
    (Y : StarEndoCat A) : (f ▷ Y).t = f.t := rfl

@[simp] lemma tensorUnit_endo :
    (𝟙_ (StarEndoCat A)).endo = StarAlgHom.id ℂ A := rfl

@[simp] lemma tensorHom_t {ρ ρ' σ σ' : StarEndoCat A} (f : ρ ⟶ ρ') (g : σ ⟶ σ') :
    (f ⊗ₘ g).t = ρ'.endo g.t * f.t := by
  change ((f ▷ σ) ≫ (ρ' ◁ g)).t = _
  simp

@[simp] lemma associator_hom_t (X Y Z : StarEndoCat A) :
    (α_ X Y Z).hom.t = 1 := rfl

@[simp] lemma leftUnitor_hom_t (X : StarEndoCat A) : (λ_ X).hom.t = 1 := rfl

@[simp] lemma rightUnitor_hom_t (X : StarEndoCat A) : (ρ_ X).hom.t = 1 := rfl

instance : MonoidalCategory (StarEndoCat A) where
  id_tensorHom_id _ _ := by apply Intertwiner.ext; simp
  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ := by
    apply Intertwiner.ext
    simp only [comp_t, tensorHom_t, map_mul, mul_assoc]
    rw [← mul_assoc g₁.t, g₁.intertwines f₂.t, mul_assoc]
  whiskerLeft_id _ _ := by apply Intertwiner.ext; simp
  id_whiskerRight _ _ := by apply Intertwiner.ext; simp
  associator_naturality _ _ _ := by apply Intertwiner.ext; simp [mul_assoc]
  leftUnitor_naturality _ := by apply Intertwiner.ext; simp
  rightUnitor_naturality _ := by apply Intertwiner.ext; simp
  pentagon _ _ _ _ := by apply Intertwiner.ext; simp
  triangle _ _ := by apply Intertwiner.ext; simp

/-! ### Dagger structure: the involution `t ↦ star t` -/

/-- The dagger of an intertwiner `t : ρ ⟶ σ` is `star t : σ ⟶ ρ`. -/
def homDagger {ρ σ : StarEndoCat A} (f : ρ ⟶ σ) : σ ⟶ ρ where
  t := star f.t
  intertwines a := by
    have h := congrArg star (f.intertwines (star a))
    simp only [star_mul, map_star, star_star] at h
    exact h.symm

@[simp] lemma homDagger_t {ρ σ : StarEndoCat A} (f : ρ ⟶ σ) :
    (homDagger f).t = star f.t := rfl

lemma homDagger_id (ρ : StarEndoCat A) : homDagger (𝟙 ρ) = 𝟙 ρ := by
  apply Intertwiner.ext; simp

lemma homDagger_comp {ρ σ τ : StarEndoCat A} (f : ρ ⟶ σ) (g : σ ⟶ τ) :
    homDagger (f ≫ g) = homDagger g ≫ homDagger f := by
  apply Intertwiner.ext; simp [star_mul]

lemma homDagger_homDagger {ρ σ : StarEndoCat A} (f : ρ ⟶ σ) :
    homDagger (homDagger f) = f := by
  apply Intertwiner.ext; simp

instance : DaggerCategory (StarEndoCat A) where
  dagger f := homDagger f
  dagger_id := homDagger_id
  dagger_comp := homDagger_comp
  dagger_dagger := homDagger_homDagger

@[simp] lemma dagger_t {ρ σ : StarEndoCat A} (f : ρ ⟶ σ) :
    (DaggerCategory.dagger f).t = star f.t := rfl

@[simp] lemma associator_inv_t (X Y Z : StarEndoCat A) :
    (α_ X Y Z).inv.t = 1 := rfl

@[simp] lemma leftUnitor_inv_t (X : StarEndoCat A) : (λ_ X).inv.t = 1 := rfl

@[simp] lemma rightUnitor_inv_t (X : StarEndoCat A) : (ρ_ X).inv.t = 1 := rfl

instance : DaggerMonoidalCategory (StarEndoCat A) where
  dagger_tensorHom f g := by
    apply Intertwiner.ext
    simp only [dagger_t, tensorHom_t, star_mul]
    rw [← map_star]
    exact (homDagger f).intertwines (star g.t)
  associator_unitary _ _ _ := by apply Intertwiner.ext; simp
  leftUnitor_unitary _ := by apply Intertwiner.ext; simp
  rightUnitor_unitary _ := by apply Intertwiner.ext; simp

end StarEndo

end CategoryTheory
