module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.LinearAlgebra.Quotient.Basic
public import QuantumSystem.Algebra.Sector.Category.Dagger
public import QuantumSystem.Algebra.Sector.Category.Tannaka.FiberFunctor

/-!
# The algebra of a pair of fiber functors — R7-E3

For fiber functors `E₁, E₂ : C ⥤ V` (Müger, *Abstract Duality Theory for Symmetric
Tensor ∗-Categories*, §2.3), the **pre-algebra**

```
A₀(E₁, E₂) = ⨁_{X ∈ C} Hom_V(E₂ X, E₁ X)
```

carries (after quotienting by the *naturality ideal* and, in the ∗-preserving case,
completing to a C\*-algebra) the structure whose **character space** is the
reconstructed group `G_E` (concrete Tannaka, Müger Theorem 2.6).  Its continuous dual
is `Nat(E₁, E₂)`; multiplicative characters correspond to monoidal natural
transformations, ∗-characters to unitary ones (Prop 2.27/2.28).

This file begins the construction (R7-E3) with the **underlying `ℂ`-module**
`A₀(E₁, E₂)`, a direct sum of the hom-spaces of the target category indexed by the
objects of `C`.  The injection of a single homogeneous component `[X, s]`, the product
(a convolution using the monoidal structure of `V`), the naturality ideal, the quotient
`A(E₁, E₂)`, the ∗-structure and the C\*-completion are built on top of this in
subsequent stages.

Mathlib does not provide this Tannaka–Krein–Müger algebra; it is built here from the
`DirectSum` API and the monoidal/linear structure already available on fiber functors.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory DirectSum Limits

-- A single canonical classical `DecidableEq` on every type, used for the `DirectSum`
-- injections indexed by the (arbitrary) object type of `C`.  Being one shared instance,
-- it lets the `DirectSum` computation lemmas (`toModule_lof`) match the injections
-- definitionally; it adds no axioms beyond Lean's core `Classical.choice`.
attribute [local instance] Classical.propDecidable

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear ℂ C]
    [MonoidalCategory C] [SymmetricCategory C]
    {V : Type u₂} [Category.{v₂} V] [Preadditive V] [Linear ℂ V]
    [MonoidalCategory V] [SymmetricCategory V]

/-- A `ℂ`-linear dagger category whose dagger is **conjugate-linear** on each hom-space:
`(f + g)† = f† + g†` and `(c • f)† = (star c) • f†`.  `DaggerCategory` alone fixes only the
multiplicative/involutive structure; this mixin records compatibility with the additive and
`ℂ`-linear structure, as holds in every C\*-category.  It is what makes the component-wise
dagger a well-defined conjugate-linear involution on the fiber-functor algebra. -/
class DaggerLinear (W : Type u₂) [Category.{v₂} W] [Preadditive W] [Linear ℂ W]
    [DaggerCategory W] : Prop where
  /-- The dagger is additive. -/
  dagger_add : ∀ {X Y : W} (f g : X ⟶ Y),
    DaggerCategory.dagger (f + g) = DaggerCategory.dagger f + DaggerCategory.dagger g
  /-- The dagger is conjugate-`ℂ`-linear. -/
  dagger_smul : ∀ {X Y : W} (c : ℂ) (f : X ⟶ Y),
    DaggerCategory.dagger (c • f) = star c • DaggerCategory.dagger f

/-- The **pre-algebra of a pair of fiber functors** (Müger §2.3, R7-E3):
`A₀(E₁, E₂) = ⨁_{X} Hom_V(E₂ X, E₁ X)`, the direct sum over all objects `X` of `C` of
the hom-spaces `E₂ X ⟶ E₁ X` in the target.  This is the underlying `ℂ`-module of the
fiber-functor algebra whose character space reconstructs the group. -/
def FiberFunctor.preAlgebra (E₁ E₂ : FiberFunctor C V) : Type (max u₁ v₂) :=
  ⨁ X : C, (E₂.functor.obj X ⟶ E₁.functor.obj X)

namespace FiberFunctor.preAlgebra

variable {E₁ E₂ : FiberFunctor C V}

noncomputable instance : AddCommGroup (E₁.preAlgebra E₂) :=
  inferInstanceAs (AddCommGroup (⨁ X : C, (E₂.functor.obj X ⟶ E₁.functor.obj X)))

noncomputable instance : Module ℂ (E₁.preAlgebra E₂) :=
  inferInstanceAs (Module ℂ (⨁ X : C, (E₂.functor.obj X ⟶ E₁.functor.obj X)))

/-- The `ℂ`-linear **injection of the homogeneous component** of degree `X`,
`s ↦ [X, s]` (Müger §2.3). -/
noncomputable def mkₗ (X : C) :
    (E₂.functor.obj X ⟶ E₁.functor.obj X) →ₗ[ℂ] E₁.preAlgebra E₂ :=
  DirectSum.lof ℂ C (fun X : C => E₂.functor.obj X ⟶ E₁.functor.obj X) X

/-- The **homogeneous element** `[X, s] ∈ A₀(E₁, E₂)` (Müger §2.3): the morphism
`s : E₂ X ⟶ E₁ X` placed in degree `X`. -/
noncomputable def mk (X : C) (s : E₂.functor.obj X ⟶ E₁.functor.obj X) :
    E₁.preAlgebra E₂ :=
  mkₗ X s

@[simp] lemma mk_zero (X : C) : (mk X 0 : E₁.preAlgebra E₂) = 0 := (mkₗ X).map_zero

lemma mk_add (X : C) (s t : E₂.functor.obj X ⟶ E₁.functor.obj X) :
    (mk X (s + t) : E₁.preAlgebra E₂) = mk X s + mk X t := (mkₗ X).map_add s t

lemma mk_smul (c : ℂ) (X : C) (s : E₂.functor.obj X ⟶ E₁.functor.obj X) :
    (mk X (c • s) : E₁.preAlgebra E₂) = c • mk X s := (mkₗ X).map_smul c s

end FiberFunctor.preAlgebra

/-- The homogeneous **convolution product** underlying the algebra structure on
`A(E) = A(E, E)` (Müger Proposition 2.21): for endomorphisms `s : E X ⟶ E X` and
`t : E Y ⟶ E Y`, transport `s ⊗ t` through the strong-monoidal comparison
`E(X ⊗ Y) ≅ E X ⊗ E Y`, i.e. `δ ≫ (s ⊗ t) ≫ μ : E(X ⊗ Y) ⟶ E(X ⊗ Y)`. -/
noncomputable def FiberFunctor.homMul (E : FiberFunctor C V) {X Y : C}
    (s : E.functor.obj X ⟶ E.functor.obj X) (t : E.functor.obj Y ⟶ E.functor.obj Y) :
    E.functor.obj (X ⊗ Y) ⟶ E.functor.obj (X ⊗ Y) :=
  Functor.OplaxMonoidal.δ E.functor X Y ≫ (s ⊗ₘ t) ≫ Functor.LaxMonoidal.μ E.functor X Y

/-- **Left naturality of the convolution product** (the coherence underlying the
descent of `mul` to the coend): for `f : X ⟶ Y`, `g : E Y ⟶ E X`, `u : E Z ⟶ E Z`,
`homMul (E f ≫ g) u = E(f ⊗ 𝟙) ≫ (δ ≫ (g ⊗ u) ≫ μ)`.  Proved from the interchange law
and the oplax-monoidal naturality `δ_natural`. -/
lemma FiberFunctor.homMul_map_comp_left (E : FiberFunctor C V) {X Y Z : C} (f : X ⟶ Y)
    (g : E.functor.obj Y ⟶ E.functor.obj X) (u : E.functor.obj Z ⟶ E.functor.obj Z) :
    E.homMul (E.functor.map f ≫ g) u
      = E.functor.map (f ⊗ₘ 𝟙 Z) ≫ Functor.OplaxMonoidal.δ E.functor Y Z
        ≫ (g ⊗ₘ u) ≫ Functor.LaxMonoidal.μ E.functor X Z := by
  have hδ := Functor.OplaxMonoidal.δ_natural E.functor f (𝟙 Z)
  rw [E.functor.map_id] at hδ
  have hi : (E.functor.map f ≫ g) ⊗ₘ u
      = (E.functor.map f ⊗ₘ 𝟙 (E.functor.obj Z)) ≫ (g ⊗ₘ u) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]
  rw [homMul, hi]
  simp only [Category.assoc]
  rw [reassoc_of% hδ]

/-- **Right naturality of the convolution product** (the dual coherence): for
`f : X ⟶ Y`, `g : E Y ⟶ E X`, `u : E Z ⟶ E Z`,
`homMul (g ≫ E f) u = (δ ≫ (g ⊗ u) ≫ μ) ≫ E(f ⊗ 𝟙)`.  Proved from the interchange law
and the lax-monoidal naturality `μ_natural`. -/
lemma FiberFunctor.homMul_comp_map_left (E : FiberFunctor C V) {X Y Z : C} (f : X ⟶ Y)
    (g : E.functor.obj Y ⟶ E.functor.obj X) (u : E.functor.obj Z ⟶ E.functor.obj Z) :
    E.homMul (g ≫ E.functor.map f) u
      = (Functor.OplaxMonoidal.δ E.functor Y Z ≫ (g ⊗ₘ u)
          ≫ Functor.LaxMonoidal.μ E.functor X Z) ≫ E.functor.map (f ⊗ₘ 𝟙 Z) := by
  have hμ := Functor.LaxMonoidal.μ_natural E.functor f (𝟙 Z)
  rw [E.functor.map_id] at hμ
  have hi : (g ≫ E.functor.map f) ⊗ₘ u
      = (g ⊗ₘ u) ≫ (E.functor.map f ⊗ₘ 𝟙 (E.functor.obj Z)) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]
  rw [homMul, hi]
  simp only [Category.assoc]
  rw [hμ]

/-- Right-factor analogue of `homMul_map_comp_left`: for `f : Z ⟶ W`,
`homMul s (E f ≫ g) = E(𝟙 ⊗ f) ≫ (δ ≫ (s ⊗ g) ≫ μ)`. -/
lemma FiberFunctor.homMul_map_comp_right (E : FiberFunctor C V) {X Z W : C} (f : Z ⟶ W)
    (s : E.functor.obj X ⟶ E.functor.obj X) (g : E.functor.obj W ⟶ E.functor.obj Z) :
    E.homMul s (E.functor.map f ≫ g)
      = E.functor.map (𝟙 X ⊗ₘ f) ≫ Functor.OplaxMonoidal.δ E.functor X W
        ≫ (s ⊗ₘ g) ≫ Functor.LaxMonoidal.μ E.functor X Z := by
  have hδ := Functor.OplaxMonoidal.δ_natural E.functor (𝟙 X) f
  rw [E.functor.map_id] at hδ
  have hi : s ⊗ₘ (E.functor.map f ≫ g)
      = (𝟙 (E.functor.obj X) ⊗ₘ E.functor.map f) ≫ (s ⊗ₘ g) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]
  rw [homMul, hi]
  simp only [Category.assoc]
  rw [reassoc_of% hδ]

/-- Right-factor analogue of `homMul_comp_map_left`: for `f : Z ⟶ W`,
`homMul s (g ≫ E f) = (δ ≫ (s ⊗ g) ≫ μ) ≫ E(𝟙 ⊗ f)`. -/
lemma FiberFunctor.homMul_comp_map_right (E : FiberFunctor C V) {X Z W : C} (f : Z ⟶ W)
    (s : E.functor.obj X ⟶ E.functor.obj X) (g : E.functor.obj W ⟶ E.functor.obj Z) :
    E.homMul s (g ≫ E.functor.map f)
      = (Functor.OplaxMonoidal.δ E.functor X W ≫ (s ⊗ₘ g)
          ≫ Functor.LaxMonoidal.μ E.functor X Z) ≫ E.functor.map (𝟙 X ⊗ₘ f) := by
  have hμ := Functor.LaxMonoidal.μ_natural E.functor (𝟙 X) f
  rw [E.functor.map_id] at hμ
  have hi : s ⊗ₘ (g ≫ E.functor.map f)
      = (s ⊗ₘ g) ≫ (𝟙 (E.functor.obj X) ⊗ₘ E.functor.map f) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]
  rw [homMul, hi]
  simp only [Category.assoc]
  rw [hμ]

/-- **Associativity of the convolution product, up to the associator** (Müger
Proposition 2.21): conjugating `homMul (homMul s t) u` by `E(α)` yields
`homMul s (homMul t u)`, i.e.
`homMul (homMul s t) u ≫ E(α) = E(α) ≫ homMul s (homMul t u)`.  This is the coherence
that descends to the associativity of the coend product on `A(E)`.  Both sides reduce,
via the strong-monoidal associator coherence `Functor.Monoidal.map_associator`, the
`μ`/`δ` inverse relations, the interchange law, and the associator naturality in `V`,
to a common normal form. -/
lemma FiberFunctor.homMul_map_associator (E : FiberFunctor C V) {X Y Z : C}
    (s : E.functor.obj X ⟶ E.functor.obj X) (t : E.functor.obj Y ⟶ E.functor.obj Y)
    (u : E.functor.obj Z ⟶ E.functor.obj Z) :
    E.homMul (E.homMul s t) u ≫ E.functor.map (α_ X Y Z).hom
      = E.functor.map (α_ X Y Z).hom ≫ E.homMul s (E.homMul t u) := by
  have hL : (Functor.OplaxMonoidal.δ E.functor X Y ≫ (s ⊗ₘ t)
        ≫ Functor.LaxMonoidal.μ E.functor X Y ⊗ₘ u)
        ≫ Functor.OplaxMonoidal.δ E.functor X Y ▷ E.functor.obj Z
      = Functor.OplaxMonoidal.δ E.functor X Y ▷ E.functor.obj Z ≫ ((s ⊗ₘ t) ⊗ₘ u) := by
    simp only [← MonoidalCategory.tensorHom_id, MonoidalCategory.tensorHom_comp_tensorHom,
      Category.assoc, Functor.Monoidal.μ_δ, Category.comp_id, Category.id_comp]
  have hR : (s ⊗ₘ (t ⊗ₘ u)) ≫ E.functor.obj X ◁ Functor.LaxMonoidal.μ E.functor Y Z
      = E.functor.obj X ◁ Functor.LaxMonoidal.μ E.functor Y Z
        ≫ (s ⊗ₘ Functor.OplaxMonoidal.δ E.functor Y Z ≫ (t ⊗ₘ u)
            ≫ Functor.LaxMonoidal.μ E.functor Y Z) := by
    simp only [← MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom,
      Functor.Monoidal.μ_δ_assoc, Category.comp_id, Category.id_comp]
  simp only [homMul, Category.assoc, Functor.Monoidal.map_associator,
    Functor.Monoidal.μ_δ_assoc]
  rw [reassoc_of% hL, reassoc_of% MonoidalCategory.associator_naturality, reassoc_of% hR]

/-- **Left unit coherence of the convolution product** (Müger §2.3): convolution by the
identity on `E(𝟙_C)` is the left-unitor conjugate of `s`, i.e.
`homMul (𝟙 (E 𝟙_C)) s ≫ E(λ) = E(λ) ≫ s`.  This descends to the left unit law of the coend
product.  Both sides reduce, via `Functor.Monoidal.map_leftUnitor`, the `μ`/`δ` relations,
the whisker exchange, and the left-unitor naturality, to `δ ≫ (η ▷ E X) ≫ λ ≫ s`. -/
lemma FiberFunctor.homMul_id_comp_map_leftUnitor (E : FiberFunctor C V) {X : C}
    (s : E.functor.obj X ⟶ E.functor.obj X) :
    E.homMul (𝟙 (E.functor.obj (𝟙_ C))) s ≫ E.functor.map (λ_ X).hom
      = E.functor.map (λ_ X).hom ≫ s := by
  simp only [homMul, Category.assoc, Functor.Monoidal.map_leftUnitor,
    Functor.Monoidal.μ_δ_assoc, MonoidalCategory.id_tensorHom]
  rw [reassoc_of% MonoidalCategory.whisker_exchange, MonoidalCategory.leftUnitor_naturality]

/-- **Right unit coherence of the convolution product** (Müger §2.3): convolution by the
identity on `E(𝟙_C)` on the right is the right-unitor conjugate of `s`, i.e.
`homMul s (𝟙 (E 𝟙_C)) ≫ E(ρ) = E(ρ) ≫ s`.  This descends to the right unit law of the coend
product.  Both sides reduce, via `Functor.Monoidal.map_rightUnitor`, the `μ`/`δ` relations,
the whisker exchange, and the right-unitor naturality, to `δ ≫ (E X ◁ η) ≫ ρ ≫ s`. -/
lemma FiberFunctor.homMul_comp_id_map_rightUnitor (E : FiberFunctor C V) {X : C}
    (s : E.functor.obj X ⟶ E.functor.obj X) :
    E.homMul s (𝟙 (E.functor.obj (𝟙_ C))) ≫ E.functor.map (ρ_ X).hom
      = E.functor.map (ρ_ X).hom ≫ s := by
  simp only [homMul, Category.assoc, Functor.Monoidal.map_rightUnitor,
    Functor.Monoidal.μ_δ_assoc, MonoidalCategory.tensorHom_id]
  rw [← reassoc_of% MonoidalCategory.whisker_exchange, MonoidalCategory.rightUnitor_naturality]

/-- **Commutativity coherence of the convolution product** (Müger §2.3, using that `C` and
`V` are symmetric and `E` is braided): conjugating `homMul s t` by `E(β_{X,Y})` swaps the
factors, `homMul s t ≫ E(β) = E(β) ≫ homMul t s`.  This descends to the commutativity of the
coend product on `A(E)`.  Proved from the lax-braided coherence `Functor.LaxBraided.braided`,
its `δ`-form, and the braiding naturality in `V`. -/
lemma FiberFunctor.homMul_comp_map_braiding (E : FiberFunctor C V) {X Y : C}
    (s : E.functor.obj X ⟶ E.functor.obj X) (t : E.functor.obj Y ⟶ E.functor.obj Y) :
    E.homMul s t ≫ E.functor.map (β_ X Y).hom
      = E.functor.map (β_ X Y).hom ≫ E.homMul t s := by
  have hμ := Functor.LaxBraided.braided (F := E.functor) X Y
  have hδ : Functor.OplaxMonoidal.δ E.functor X Y
        ≫ (β_ (E.functor.obj X) (E.functor.obj Y)).hom
      = E.functor.map (β_ X Y).hom ≫ Functor.OplaxMonoidal.δ E.functor Y X := by
    rw [← Functor.Monoidal.δ_μ_assoc E.functor X Y
        (E.functor.map (β_ X Y).hom ≫ Functor.OplaxMonoidal.δ E.functor Y X),
      reassoc_of% hμ, Functor.Monoidal.μ_δ, Category.comp_id]
  simp only [homMul, Category.assoc]
  rw [hμ, reassoc_of% BraidedCategory.braiding_naturality, reassoc_of% hδ]

/-- A fiber functor is **∗-monoidal** (Müger Definition 2.1) when its oplax tensorator is the
dagger of its lax tensorator, `δ_{X,Y} = μ_{X,Y}†` — i.e. the strong-monoidal comparison
`μ` is *unitary*.  This holds for the ∗-preserving symmetric fiber functors into Hilbert
spaces used in the concrete C\*-Tannaka theorem; it is the property making the ∗-structure
on `A(E)` multiplicative. -/
def FiberFunctor.IsStarMonoidal [DaggerMonoidalCategory V] (E : FiberFunctor C V) : Prop :=
  ∀ X Y : C, Functor.OplaxMonoidal.δ E.functor X Y
    = DaggerCategory.dagger (Functor.LaxMonoidal.μ E.functor X Y)

/-- **The convolution product is a ∗-homomorphism** (Müger §2.3): for a ∗-monoidal fiber
functor the dagger of `homMul s t` is `homMul s† t†`.  Proved from the contravariance of the
dagger, its monoidality `(s ⊗ t)† = s† ⊗ t†`, and the unitarity of the tensorator `δ = μ†`.
This descends to the multiplicativity of the ∗-involution on the coend algebra `A(E)`. -/
lemma FiberFunctor.homMul_dagger [DaggerMonoidalCategory V] {E : FiberFunctor C V}
    (hE : E.IsStarMonoidal) {X Y : C}
    (s : E.functor.obj X ⟶ E.functor.obj X) (t : E.functor.obj Y ⟶ E.functor.obj Y) :
    DaggerCategory.dagger (E.homMul s t)
      = E.homMul (DaggerCategory.dagger s) (DaggerCategory.dagger t) := by
  rw [homMul, homMul, DaggerCategory.dagger_comp, DaggerCategory.dagger_comp,
    DaggerMonoidalCategory.dagger_tensorHom, hE X Y, DaggerCategory.dagger_dagger, ← hE X Y,
    Category.assoc]

/-- A fiber functor is a **∗-functor** (Müger Definition 2.1) when it is both ∗-monoidal (its
tensorator `μ` is unitary, `IsStarMonoidal`) and ∗-preserving (`IsStarPreserving`).  Bundled
as a `Prop`-valued mixin so that the full ∗-algebra structure on the coend `A(E)` is available
as typeclass instances.  This is the input to the concrete C\*-Tannaka theorem (R7-E). -/
class FiberFunctor.IsStar [DaggerCategory C] [DaggerMonoidalCategory V] [DaggerLinear V]
    (E : FiberFunctor C V) : Prop where
  /-- The tensorator is unitary. -/
  isStarMonoidal : E.IsStarMonoidal
  /-- The functor commutes with the dagger. -/
  isStarPreserving : E.IsStarPreserving

namespace FiberFunctor

-- The bilinearity of `homMul` requires the target `V` to be monoidal-(pre)additive (for
-- additivity) and monoidal-`ℂ`-linear (for `ℂ`-linearity) of whiskering.  Fiber-functor
-- targets (`Vect_ℂ`, `Hilb`) are such; this is the standing assumption for the algebra.
variable [MonoidalPreadditive V] {E : FiberFunctor C V} {X Y : C}

@[simp] lemma homMul_zero_left (t : E.functor.obj Y ⟶ E.functor.obj Y) :
    E.homMul (0 : E.functor.obj X ⟶ E.functor.obj X) t = 0 := by
  simp [homMul, MonoidalCategory.tensorHom_def]

@[simp] lemma homMul_zero_right (s : E.functor.obj X ⟶ E.functor.obj X) :
    E.homMul s (0 : E.functor.obj Y ⟶ E.functor.obj Y) = 0 := by
  simp [homMul, MonoidalCategory.tensorHom_def]

lemma homMul_add_left (s s' : E.functor.obj X ⟶ E.functor.obj X)
    (t : E.functor.obj Y ⟶ E.functor.obj Y) :
    E.homMul (s + s') t = E.homMul s t + E.homMul s' t := by
  simp [homMul, MonoidalCategory.tensorHom_def]

lemma homMul_add_right (s : E.functor.obj X ⟶ E.functor.obj X)
    (t t' : E.functor.obj Y ⟶ E.functor.obj Y) :
    E.homMul s (t + t') = E.homMul s t + E.homMul s t' := by
  simp [homMul, MonoidalCategory.tensorHom_def]

variable [MonoidalLinear ℂ V]

lemma homMul_smul_left (c : ℂ) (s : E.functor.obj X ⟶ E.functor.obj X)
    (t : E.functor.obj Y ⟶ E.functor.obj Y) :
    E.homMul (c • s) t = c • E.homMul s t := by
  simp [homMul, MonoidalCategory.tensorHom_def]

lemma homMul_smul_right (c : ℂ) (s : E.functor.obj X ⟶ E.functor.obj X)
    (t : E.functor.obj Y ⟶ E.functor.obj Y) :
    E.homMul s (c • t) = c • E.homMul s t := by
  simp [homMul, MonoidalCategory.tensorHom_def]

/-- The convolution product `homMul` packaged as a **`ℂ`-bilinear map**
`Hom(E X, E X) →ₗ Hom(E Y, E Y) →ₗ Hom(E(X ⊗ Y), E(X ⊗ Y))`.  This is the ingredient
extended (via `DirectSum.toModule`) to the algebra multiplication on `A(E)`. -/
noncomputable def homMulₗ (E : FiberFunctor C V) (X Y : C) :
    (E.functor.obj X ⟶ E.functor.obj X) →ₗ[ℂ]
      (E.functor.obj Y ⟶ E.functor.obj Y) →ₗ[ℂ]
        (E.functor.obj (X ⊗ Y) ⟶ E.functor.obj (X ⊗ Y)) :=
  LinearMap.mk₂ ℂ E.homMul
    E.homMul_add_left E.homMul_smul_left E.homMul_add_right E.homMul_smul_right

@[simp] lemma homMulₗ_apply (E : FiberFunctor C V) (X Y : C)
    (s : E.functor.obj X ⟶ E.functor.obj X) (t : E.functor.obj Y ⟶ E.functor.obj Y) :
    E.homMulₗ X Y s t = E.homMul s t := rfl

/-- Left multiplication by the homogeneous element `[X, s]` as a `ℂ`-linear endomorphism
of `A₀(E)`: the linear extension of `[Y, t] ↦ [X ⊗ Y, homMul s t]` (one currying of the
algebra product, Müger Prop 2.21). -/
noncomputable def mulSecond (E : FiberFunctor C V) (X : C)
    (s : E.functor.obj X ⟶ E.functor.obj X) : E.preAlgebra E →ₗ[ℂ] E.preAlgebra E :=
  DirectSum.toModule ℂ C (E.preAlgebra E)
    (fun Y => (preAlgebra.mkₗ (X ⊗ Y)).comp (E.homMulₗ X Y s))

@[simp] lemma mulSecond_mk (E : FiberFunctor C V) (X Y : C)
    (s : E.functor.obj X ⟶ E.functor.obj X) (t : E.functor.obj Y ⟶ E.functor.obj Y) :
    E.mulSecond X s (preAlgebra.mk Y t) = preAlgebra.mk (X ⊗ Y) (E.homMul s t) := by
  change DirectSum.toModule ℂ C (E.preAlgebra E)
      (fun Z => (preAlgebra.mkₗ (X ⊗ Z)).comp (E.homMulₗ X Z s))
      (DirectSum.lof ℂ C (fun Z => E.functor.obj Z ⟶ E.functor.obj Z) Y t)
    = preAlgebra.mk (X ⊗ Y) (E.homMul s t)
  rw [DirectSum.toModule_lof]
  rfl

/-- `mulSecond X` is additive in the homogeneous element `s` (checked on generators). -/
lemma mulSecond_add_left (E : FiberFunctor C V) (X : C)
    (s s' : E.functor.obj X ⟶ E.functor.obj X) :
    E.mulSecond X (s + s') = E.mulSecond X s + E.mulSecond X s' := by
  refine DirectSum.linearMap_ext ℂ fun Y => LinearMap.ext fun t => ?_
  change E.mulSecond X (s + s') (preAlgebra.mk Y t)
    = (E.mulSecond X s + E.mulSecond X s') (preAlgebra.mk Y t)
  rw [LinearMap.add_apply, mulSecond_mk, mulSecond_mk, mulSecond_mk,
    homMul_add_left, preAlgebra.mk_add]

/-- `mulSecond X` is `ℂ`-homogeneous in `s` (checked on generators). -/
lemma mulSecond_smul_left (E : FiberFunctor C V) (X : C) (c : ℂ)
    (s : E.functor.obj X ⟶ E.functor.obj X) :
    E.mulSecond X (c • s) = c • E.mulSecond X s := by
  refine DirectSum.linearMap_ext ℂ fun Y => LinearMap.ext fun t => ?_
  change E.mulSecond X (c • s) (preAlgebra.mk Y t)
    = (c • E.mulSecond X s) (preAlgebra.mk Y t)
  rw [LinearMap.smul_apply, mulSecond_mk, mulSecond_mk, homMul_smul_left,
    preAlgebra.mk_smul]

/-- Left multiplication packaged linearly in the homogeneous element:
`Hom(E X, E X) →ₗ End_ℂ(A₀(E))`. -/
noncomputable def mulFirst (E : FiberFunctor C V) (X : C) :
    (E.functor.obj X ⟶ E.functor.obj X) →ₗ[ℂ]
      (E.preAlgebra E →ₗ[ℂ] E.preAlgebra E) where
  toFun := E.mulSecond X
  map_add' := E.mulSecond_add_left X
  map_smul' := E.mulSecond_smul_left X

/-- The **multiplication** of the fiber-functor algebra `A₀(E)` (Müger Prop 2.21), as a
`ℂ`-bilinear map: the linear extension of `homMul` in both homogeneous degrees,
`[X, s] · [Y, t] = [X ⊗ Y, homMul s t]`. -/
noncomputable def mul (E : FiberFunctor C V) :
    E.preAlgebra E →ₗ[ℂ] E.preAlgebra E →ₗ[ℂ] E.preAlgebra E :=
  DirectSum.toModule ℂ C (E.preAlgebra E →ₗ[ℂ] E.preAlgebra E) E.mulFirst

/-- The product of two homogeneous elements (Müger Prop 2.21):
`[X, s] · [Y, t] = [X ⊗ Y, homMul s t]`. -/
@[simp] lemma mul_mk_mk (E : FiberFunctor C V) (X Y : C)
    (s : E.functor.obj X ⟶ E.functor.obj X) (t : E.functor.obj Y ⟶ E.functor.obj Y) :
    E.mul (preAlgebra.mk X s) (preAlgebra.mk Y t)
      = preAlgebra.mk (X ⊗ Y) (E.homMul s t) := by
  have h : E.mul (preAlgebra.mk X s) = E.mulSecond X s := by
    change DirectSum.toModule ℂ C (E.preAlgebra E →ₗ[ℂ] E.preAlgebra E) E.mulFirst
        (DirectSum.lof ℂ C (fun Z => E.functor.obj Z ⟶ E.functor.obj Z) X s)
      = E.mulSecond X s
    rw [DirectSum.toModule_lof]
    rfl
  rw [h, mulSecond_mk]

/-- The (pre-)**unit** of the algebra `A₀(E)` (Müger §2.3): the identity endomorphism
placed in degree `𝟙_C`, `[𝟙_C, id_{E 𝟙_C}]`.  It descends to the multiplicative unit of
the coend `A(E)` (the unit law holds modulo the unitor naturality). -/
noncomputable def one (E : FiberFunctor C V) : E.preAlgebra E :=
  preAlgebra.mk (𝟙_ C) (𝟙 (E.functor.obj (𝟙_ C)))

end FiberFunctor

namespace FiberFunctor.preAlgebra

variable {E₁ E₂ : FiberFunctor C V}

/-- The **naturality submodule** of `A₀(E₁, E₂)` (Müger §2.3): the relations turning the
direct sum into the coend `∫^X Hom(E₂ X, E₁ X)`.  For `f : X ⟶ Y` and `g : E₂ Y ⟶ E₁ X`,
the homogeneous elements `[X, E₂ f ≫ g]` and `[Y, g ≫ E₁ f]` are identified (dinaturality). -/
noncomputable def naturalityRel (E₁ E₂ : FiberFunctor C V) :
    Submodule ℂ (E₁.preAlgebra E₂) :=
  Submodule.span ℂ
    { x | ∃ (X Y : C) (f : X ⟶ Y) (g : E₂.functor.obj Y ⟶ E₁.functor.obj X),
        x = mk X (E₂.functor.map f ≫ g) - mk Y (g ≫ E₁.functor.map f) }

/-- The **algebra of natural transformations** `A(E₁, E₂)` (Müger §2.3): the coend
`∫^X Hom(E₂ X, E₁ X)`, i.e. `A₀(E₁, E₂)` modulo the naturality submodule.  Its continuous
dual is `Nat(E₁, E₂)`; for `E₁ = E₂` it is the (associative, commutative in the symmetric
case) algebra whose character space reconstructs the group. -/
def algebra (E₁ E₂ : FiberFunctor C V) : Type _ :=
  E₁.preAlgebra E₂ ⧸ naturalityRel E₁ E₂

noncomputable instance : AddCommGroup (algebra E₁ E₂) :=
  inferInstanceAs (AddCommGroup (_ ⧸ naturalityRel E₁ E₂))

noncomputable instance : Module ℂ (algebra E₁ E₂) :=
  inferInstanceAs (Module ℂ (_ ⧸ naturalityRel E₁ E₂))

/-- The quotient map `A₀(E₁, E₂) → A(E₁, E₂)` onto the coend. -/
noncomputable def toAlgebra (E₁ E₂ : FiberFunctor C V) :
    E₁.preAlgebra E₂ →ₗ[ℂ] algebra E₁ E₂ :=
  (naturalityRel E₁ E₂).mkQ

/-- **Left ideal compatibility (on generators)**: multiplying a naturality generator
`[X, E f ≫ g] - [Y, g ≫ E f]` on the right by `[Z, u]` stays in the naturality submodule.
This is the key step (via the left coherence lemmas `homMul_{map_comp,comp_map}_left`) for
descending the product to the coend `A(E)`. -/
lemma mul_naturality_left [MonoidalPreadditive V] [MonoidalLinear ℂ V]
    (E : FiberFunctor C V) {X Y : C} (f : X ⟶ Y)
    (g : E.functor.obj Y ⟶ E.functor.obj X) (Z : C)
    (u : E.functor.obj Z ⟶ E.functor.obj Z) :
    E.mul (mk X (E.functor.map f ≫ g)) (mk Z u)
      - E.mul (mk Y (g ≫ E.functor.map f)) (mk Z u) ∈ naturalityRel E E := by
  rw [E.mul_mk_mk, E.mul_mk_mk, E.homMul_map_comp_left, E.homMul_comp_map_left]
  exact Submodule.subset_span
    ⟨X ⊗ Z, Y ⊗ Z, f ⊗ₘ 𝟙 Z,
      Functor.OplaxMonoidal.δ E.functor Y Z ≫ (g ⊗ₘ u)
        ≫ Functor.LaxMonoidal.μ E.functor X Z, rfl⟩

/-- **Right ideal compatibility (on generators)**: multiplying `[X, s]` on the left by a
naturality generator `[Z, E f ≫ g] - [W, g ≫ E f]` stays in the naturality submodule
(via the right coherence lemmas `homMul_{map_comp,comp_map}_right`). -/
lemma mul_naturality_right [MonoidalPreadditive V] [MonoidalLinear ℂ V]
    (E : FiberFunctor C V) (X : C) (s : E.functor.obj X ⟶ E.functor.obj X)
    {Z W : C} (f : Z ⟶ W) (g : E.functor.obj W ⟶ E.functor.obj Z) :
    E.mul (mk X s) (mk Z (E.functor.map f ≫ g))
      - E.mul (mk X s) (mk W (g ≫ E.functor.map f)) ∈ naturalityRel E E := by
  rw [E.mul_mk_mk, E.mul_mk_mk, E.homMul_map_comp_right, E.homMul_comp_map_right]
  exact Submodule.subset_span
    ⟨X ⊗ Z, X ⊗ W, 𝟙 X ⊗ₘ f,
      Functor.OplaxMonoidal.δ E.functor X W ≫ (s ⊗ₘ g)
        ≫ Functor.LaxMonoidal.μ E.functor X Z, rfl⟩

/-- Right ideal compatibility for an **arbitrary** left factor `a` (extending
`mul_naturality_right` from homogeneous generators via `DirectSum.linearMap_ext`). -/
lemma mul_naturality_right' [MonoidalPreadditive V] [MonoidalLinear ℂ V]
    (E : FiberFunctor C V) (a : E.preAlgebra E) {Z W : C} (f : Z ⟶ W)
    (g : E.functor.obj W ⟶ E.functor.obj Z) :
    E.mul a (mk Z (E.functor.map f ≫ g) - mk W (g ≫ E.functor.map f)) ∈ naturalityRel E E := by
  have h0 : (toAlgebra E E).comp
      ((E.mul).flip (mk Z (E.functor.map f ≫ g) - mk W (g ≫ E.functor.map f))) = 0 := by
    refine DirectSum.linearMap_ext ℂ fun X => LinearMap.ext fun s => ?_
    change toAlgebra E E
      (E.mul (mk X s) (mk Z (E.functor.map f ≫ g) - mk W (g ≫ E.functor.map f))) = 0
    rw [map_sub]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (mul_naturality_right E X s f g)
  have hk := LinearMap.congr_fun h0 a
  rw [LinearMap.comp_apply, LinearMap.flip_apply] at hk
  exact (Submodule.Quotient.mk_eq_zero _).mp hk

/-- Left ideal compatibility for an **arbitrary** right factor `b` (extending
`mul_naturality_left` from homogeneous generators via `DirectSum.linearMap_ext`). -/
lemma mul_naturality_left' [MonoidalPreadditive V] [MonoidalLinear ℂ V]
    (E : FiberFunctor C V) {X Y : C} (f : X ⟶ Y)
    (g : E.functor.obj Y ⟶ E.functor.obj X) (b : E.preAlgebra E) :
    E.mul (mk X (E.functor.map f ≫ g) - mk Y (g ≫ E.functor.map f)) b ∈ naturalityRel E E := by
  have h0 : (toAlgebra E E).comp
      (E.mul (mk X (E.functor.map f ≫ g) - mk Y (g ≫ E.functor.map f))) = 0 := by
    refine DirectSum.linearMap_ext ℂ fun Z => LinearMap.ext fun u => ?_
    change toAlgebra E E
      (E.mul (mk X (E.functor.map f ≫ g) - mk Y (g ≫ E.functor.map f)) (mk Z u)) = 0
    rw [map_sub, LinearMap.sub_apply]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (mul_naturality_left E f g Z u)
  have hk := LinearMap.congr_fun h0 b
  rw [LinearMap.comp_apply] at hk
  exact (Submodule.Quotient.mk_eq_zero _).mp hk

/-- **Associativity on generators, modulo naturality** (the descent of the convolution
associativity `homMul_map_associator` to the coend): the associator difference
`[(X⊗Y)⊗Z, homMul (homMul s t) u] - [X⊗(Y⊗Z), homMul s (homMul t u)]` lies in the
naturality submodule, witnessed by `f = α_{X,Y,Z}` and `g = E(α⁻¹) ≫ homMul (homMul s t) u`. -/
lemma mul_assoc_naturality [MonoidalPreadditive V] [MonoidalLinear ℂ V]
    (E : FiberFunctor C V) {X Y Z : C} (s : E.functor.obj X ⟶ E.functor.obj X)
    (t : E.functor.obj Y ⟶ E.functor.obj Y) (u : E.functor.obj Z ⟶ E.functor.obj Z) :
    E.mul (E.mul (mk X s) (mk Y t)) (mk Z u)
      - E.mul (mk X s) (E.mul (mk Y t) (mk Z u)) ∈ naturalityRel E E := by
  rw [E.mul_mk_mk, E.mul_mk_mk, E.mul_mk_mk, E.mul_mk_mk]
  have hg1 : E.functor.map (α_ X Y Z).hom
        ≫ (E.functor.map (α_ X Y Z).inv ≫ E.homMul (E.homMul s t) u)
      = E.homMul (E.homMul s t) u := by
    rw [← Category.assoc, ← E.functor.map_comp, Iso.hom_inv_id, E.functor.map_id, Category.id_comp]
  have hg2 : (E.functor.map (α_ X Y Z).inv ≫ E.homMul (E.homMul s t) u)
        ≫ E.functor.map (α_ X Y Z).hom
      = E.homMul s (E.homMul t u) := by
    rw [Category.assoc, E.homMul_map_associator, ← Category.assoc, ← E.functor.map_comp,
      Iso.inv_hom_id, E.functor.map_id, Category.id_comp]
  refine Submodule.subset_span ⟨(X ⊗ Y) ⊗ Z, X ⊗ (Y ⊗ Z), (α_ X Y Z).hom,
    E.functor.map (α_ X Y Z).inv ≫ E.homMul (E.homMul s t) u, ?_⟩
  rw [hg1, hg2]

/-- **Left unit on generators, modulo naturality**: `[𝟙_C, id] · [X, s] - [X, s]` lies in the
naturality submodule, witnessed by `f = λ_X` and `g = s ≫ E(λ⁻¹)` (descent of
`homMul_id_comp_map_leftUnitor`). -/
lemma one_mul_naturality [MonoidalPreadditive V] [MonoidalLinear ℂ V]
    (E : FiberFunctor C V) {X : C} (s : E.functor.obj X ⟶ E.functor.obj X) :
    E.mul E.one (mk X s) - mk X s ∈ naturalityRel E E := by
  change E.mul (mk (𝟙_ C) (𝟙 (E.functor.obj (𝟙_ C)))) (mk X s) - mk X s ∈ naturalityRel E E
  rw [E.mul_mk_mk]
  have hg1 : E.functor.map (λ_ X).hom ≫ s ≫ E.functor.map (λ_ X).inv
      = E.homMul (𝟙 (E.functor.obj (𝟙_ C))) s := by
    rw [← Category.assoc, ← E.homMul_id_comp_map_leftUnitor s, Category.assoc,
      ← E.functor.map_comp, Iso.hom_inv_id, E.functor.map_id, Category.comp_id]
  have hg2 : (s ≫ E.functor.map (λ_ X).inv) ≫ E.functor.map (λ_ X).hom = s := by
    rw [Category.assoc, ← E.functor.map_comp, Iso.inv_hom_id, E.functor.map_id, Category.comp_id]
  refine Submodule.subset_span
    ⟨𝟙_ C ⊗ X, X, (λ_ X).hom, s ≫ E.functor.map (λ_ X).inv, ?_⟩
  rw [hg1, hg2]

/-- **Right unit on generators, modulo naturality**: `[X, s] · [𝟙_C, id] - [X, s]` lies in the
naturality submodule, witnessed by `f = ρ_X` and `g = s ≫ E(ρ⁻¹)` (descent of
`homMul_comp_id_map_rightUnitor`). -/
lemma mul_one_naturality [MonoidalPreadditive V] [MonoidalLinear ℂ V]
    (E : FiberFunctor C V) {X : C} (s : E.functor.obj X ⟶ E.functor.obj X) :
    E.mul (mk X s) E.one - mk X s ∈ naturalityRel E E := by
  change E.mul (mk X s) (mk (𝟙_ C) (𝟙 (E.functor.obj (𝟙_ C)))) - mk X s ∈ naturalityRel E E
  rw [E.mul_mk_mk]
  have hg1 : E.functor.map (ρ_ X).hom ≫ s ≫ E.functor.map (ρ_ X).inv
      = E.homMul s (𝟙 (E.functor.obj (𝟙_ C))) := by
    rw [← Category.assoc, ← E.homMul_comp_id_map_rightUnitor s, Category.assoc,
      ← E.functor.map_comp, Iso.hom_inv_id, E.functor.map_id, Category.comp_id]
  have hg2 : (s ≫ E.functor.map (ρ_ X).inv) ≫ E.functor.map (ρ_ X).hom = s := by
    rw [Category.assoc, ← E.functor.map_comp, Iso.inv_hom_id, E.functor.map_id, Category.comp_id]
  refine Submodule.subset_span
    ⟨X ⊗ 𝟙_ C, X, (ρ_ X).hom, s ≫ E.functor.map (ρ_ X).inv, ?_⟩
  rw [hg1, hg2]

/-- **Commutativity on generators, modulo naturality** (the descent of the braiding coherence
`homMul_comp_map_braiding`): `[X, s] · [Y, t] - [Y, t] · [X, s]` lies in the naturality
submodule, witnessed by `f = β_{X,Y}` and `g = E(β⁻¹) ≫ homMul s t`. -/
lemma mul_comm_naturality [MonoidalPreadditive V] [MonoidalLinear ℂ V]
    (E : FiberFunctor C V) {X Y : C} (s : E.functor.obj X ⟶ E.functor.obj X)
    (t : E.functor.obj Y ⟶ E.functor.obj Y) :
    E.mul (mk X s) (mk Y t) - E.mul (mk Y t) (mk X s) ∈ naturalityRel E E := by
  rw [E.mul_mk_mk, E.mul_mk_mk]
  have hg1 : E.functor.map (β_ X Y).hom ≫ (E.functor.map (β_ X Y).inv ≫ E.homMul s t)
      = E.homMul s t := by
    rw [← Category.assoc, ← E.functor.map_comp, Iso.hom_inv_id, E.functor.map_id, Category.id_comp]
  have hg2 : (E.functor.map (β_ X Y).inv ≫ E.homMul s t) ≫ E.functor.map (β_ X Y).hom
      = E.homMul t s := by
    rw [Category.assoc, E.homMul_comp_map_braiding, ← Category.assoc, ← E.functor.map_comp,
      Iso.inv_hom_id, E.functor.map_id, Category.id_comp]
  refine Submodule.subset_span ⟨X ⊗ Y, Y ⊗ X, (β_ X Y).hom,
    E.functor.map (β_ X Y).inv ≫ E.homMul s t, ?_⟩
  rw [hg1, hg2]

/-- **Associativity of the descended product on the coend** at the level of `preAlgebra`:
`[(a · b) · c] = [a · (b · c)]` in `A(E)`.  Reduces all three arguments to homogeneous
generators by trilinearity (three nested `DirectSum.linearMap_ext`), landing on the
generator identity `mul_assoc_naturality`. -/
lemma toAlgebra_mul_assoc [MonoidalPreadditive V] [MonoidalLinear ℂ V]
    (E : FiberFunctor C V) (a b c : E.preAlgebra E) :
    toAlgebra E E (E.mul (E.mul a b) c) = toAlgebra E E (E.mul a (E.mul b c)) := by
  suffices Hc : ∀ a b : E.preAlgebra E,
      (toAlgebra E E).comp (E.mul (E.mul a b))
        = (toAlgebra E E).comp ((E.mul a).comp (E.mul b)) by
    have h := LinearMap.congr_fun (Hc a b) c
    simpa only [LinearMap.comp_apply] using h
  clear a b c
  intro a b
  refine DirectSum.linearMap_ext ℂ fun Z => LinearMap.ext fun u => ?_
  suffices Hb : ∀ a : E.preAlgebra E,
      (toAlgebra E E).comp ((E.mul.flip (mk Z u)).comp (E.mul a))
        = (toAlgebra E E).comp ((E.mul a).comp (E.mul.flip (mk Z u))) by
    have h := LinearMap.congr_fun (Hb a) b
    simpa only [LinearMap.comp_apply, LinearMap.flip_apply] using h
  clear a b
  intro a
  refine DirectSum.linearMap_ext ℂ fun Y => LinearMap.ext fun t => ?_
  suffices Ha :
      (toAlgebra E E).comp ((E.mul.flip (mk Z u)).comp (E.mul.flip (mk Y t)))
        = (toAlgebra E E).comp (E.mul.flip (E.mul (mk Y t) (mk Z u))) by
    have h := LinearMap.congr_fun Ha a
    simpa only [LinearMap.comp_apply, LinearMap.flip_apply] using h
  clear a
  refine DirectSum.linearMap_ext ℂ fun X => LinearMap.ext fun s => ?_
  change toAlgebra E E (E.mul (E.mul (mk X s) (mk Y t)) (mk Z u))
      = toAlgebra E E (E.mul (mk X s) (E.mul (mk Y t) (mk Z u)))
  rw [← sub_eq_zero, ← map_sub]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (mul_assoc_naturality E s t u)

/-- **Left unit law on the coend** at the level of `preAlgebra`: `[1 · a] = [a]` in `A(E)`.
Reduces `a` to homogeneous generators by linearity, landing on `one_mul_naturality`. -/
lemma toAlgebra_one_mul [MonoidalPreadditive V] [MonoidalLinear ℂ V]
    (E : FiberFunctor C V) (a : E.preAlgebra E) :
    toAlgebra E E (E.mul E.one a) = toAlgebra E E a := by
  have h0 : (toAlgebra E E).comp (E.mul E.one) = toAlgebra E E := by
    refine DirectSum.linearMap_ext ℂ fun X => LinearMap.ext fun s => ?_
    change toAlgebra E E (E.mul E.one (mk X s)) = toAlgebra E E (mk X s)
    rw [← sub_eq_zero, ← map_sub]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (one_mul_naturality E s)
  exact LinearMap.congr_fun h0 a

/-- **Right unit law on the coend** at the level of `preAlgebra`: `[a · 1] = [a]` in `A(E)`.
Reduces `a` to homogeneous generators by linearity, landing on `mul_one_naturality`. -/
lemma toAlgebra_mul_one [MonoidalPreadditive V] [MonoidalLinear ℂ V]
    (E : FiberFunctor C V) (a : E.preAlgebra E) :
    toAlgebra E E (E.mul a E.one) = toAlgebra E E a := by
  have h0 : (toAlgebra E E).comp (E.mul.flip E.one) = toAlgebra E E := by
    refine DirectSum.linearMap_ext ℂ fun X => LinearMap.ext fun s => ?_
    change toAlgebra E E (E.mul (mk X s) E.one) = toAlgebra E E (mk X s)
    rw [← sub_eq_zero, ← map_sub]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (mul_one_naturality E s)
  exact LinearMap.congr_fun h0 a

/-- **Commutativity of the coend product** at the level of `preAlgebra`: `[a · b] = [b · a]`
in `A(E)`.  Reduces both arguments to homogeneous generators by bilinearity (two nested
`DirectSum.linearMap_ext`), landing on `mul_comm_naturality`. -/
lemma toAlgebra_mul_comm [MonoidalPreadditive V] [MonoidalLinear ℂ V]
    (E : FiberFunctor C V) (a b : E.preAlgebra E) :
    toAlgebra E E (E.mul a b) = toAlgebra E E (E.mul b a) := by
  suffices Ha : ∀ b : E.preAlgebra E,
      (toAlgebra E E).comp (E.mul.flip b) = (toAlgebra E E).comp (E.mul b) by
    have h := LinearMap.congr_fun (Ha b) a
    simpa only [LinearMap.comp_apply, LinearMap.flip_apply] using h
  clear a b
  intro b
  refine DirectSum.linearMap_ext ℂ fun X => LinearMap.ext fun s => ?_
  suffices Hb : (toAlgebra E E).comp (E.mul (mk X s))
      = (toAlgebra E E).comp (E.mul.flip (mk X s)) by
    have h := LinearMap.congr_fun Hb b
    simpa only [LinearMap.comp_apply, LinearMap.flip_apply] using h
  clear b
  refine DirectSum.linearMap_ext ℂ fun Y => LinearMap.ext fun t => ?_
  change toAlgebra E E (E.mul (mk X s) (mk Y t)) = toAlgebra E E (E.mul (mk Y t) (mk X s))
  rw [← sub_eq_zero, ← map_sub]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (mul_comm_naturality E s t)

/-- `mul a` maps the naturality submodule into itself (for the descent of the product to
the coend, second argument), i.e. `N ≤ comap (mul a) N`. -/
lemma naturalityRel_le_comap_mul [MonoidalPreadditive V] [MonoidalLinear ℂ V]
    (E : FiberFunctor C V) (a : E.preAlgebra E) :
    naturalityRel E E ≤ Submodule.comap (E.mul a) (naturalityRel E E) :=
  Submodule.span_le.mpr <| by rintro _ ⟨Z, W, f, g, rfl⟩; exact mul_naturality_right' E a f g

/-- The bilinear map `A₀(E) →ₗ A₀(E) →ₗ A(E)`, `(a, b) ↦ [a · b]` into the coend, obtained
by postcomposing `mul` with the quotient map.  (First step toward the coend product;
expressed as a composition of linear maps to avoid manual bundling.) -/
noncomputable def mulHomQ [MonoidalPreadditive V] [MonoidalLinear ℂ V] (E : FiberFunctor C V) :
    E.preAlgebra E →ₗ[ℂ] E.preAlgebra E →ₗ[ℂ] algebra E E :=
  (LinearMap.llcomp ℂ (E.preAlgebra E) (E.preAlgebra E) (algebra E E) (toAlgebra E E)).comp E.mul

@[simp] lemma mulHomQ_apply [MonoidalPreadditive V] [MonoidalLinear ℂ V] (E : FiberFunctor C V)
    (a b : E.preAlgebra E) : mulHomQ E a b = toAlgebra E E (E.mul a b) := rfl

/-- The naturality submodule is in the kernel of `(mulHomQ E).flip` (right ideal
compatibility), allowing the first factor of `mulHomQ` to descend to the coend. -/
lemma naturalityRel_le_ker_mulHomQ_flip [MonoidalPreadditive V] [MonoidalLinear ℂ V]
    (E : FiberFunctor C V) : naturalityRel E E ≤ LinearMap.ker (mulHomQ E).flip := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨Z, W, f, g, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker]
  refine LinearMap.ext fun a => ?_
  rw [LinearMap.flip_apply, mulHomQ_apply, LinearMap.zero_apply]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (mul_naturality_right' E a f g)

/-- `mulHomQ` with its first factor descended to the coend: `A(E) →ₗ (A₀(E) →ₗ A(E))`,
`(ā, b) ↦ [a · b]`. -/
noncomputable def mulHomQ2 [MonoidalPreadditive V] [MonoidalLinear ℂ V] (E : FiberFunctor C V) :
    algebra E E →ₗ[ℂ] E.preAlgebra E →ₗ[ℂ] algebra E E :=
  (naturalityRel E E).liftQ (mulHomQ E).flip (naturalityRel_le_ker_mulHomQ_flip E)

/-- The naturality submodule is in the kernel of `(mulHomQ2 E).flip` (left ideal
compatibility), allowing the second factor to descend to the coend. -/
lemma naturalityRel_le_ker_mulHomQ2_flip [MonoidalPreadditive V] [MonoidalLinear ℂ V]
    (E : FiberFunctor C V) : naturalityRel E E ≤ LinearMap.ker (mulHomQ2 E).flip := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨X, Y, f, g, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker]
  refine LinearMap.ext fun b => ?_
  obtain ⟨b, rfl⟩ := (naturalityRel E E).mkQ_surjective b
  simp only [LinearMap.flip_apply, LinearMap.zero_apply, mulHomQ2]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (mul_naturality_left' E f g b)

/-- The **multiplication on the coend** `A(E)` (Müger §2.3): the descent of `mul` through
the naturality submodule in both factors.  `A(E) = ∫^X End(E X)` is thereby a (non-unital,
to be shown associative) `ℂ`-algebra. -/
noncomputable def mulQ [MonoidalPreadditive V] [MonoidalLinear ℂ V] (E : FiberFunctor C V) :
    algebra E E →ₗ[ℂ] algebra E E →ₗ[ℂ] algebra E E :=
  (naturalityRel E E).liftQ (mulHomQ2 E).flip (naturalityRel_le_ker_mulHomQ2_flip E)

/-- The defining property of the coend product: `[a] · [b] = [a · b]` (Müger §2.3). -/
@[simp] lemma mulQ_toAlgebra [MonoidalPreadditive V] [MonoidalLinear ℂ V]
    (E : FiberFunctor C V) (a b : E.preAlgebra E) :
    mulQ E (toAlgebra E E a) (toAlgebra E E b) = toAlgebra E E (E.mul a b) := rfl

/-- **Associativity of the coend product** `A(E)` (Müger §2.3): `(A · B) · C = A · (B · C)`.
Obtained from the `preAlgebra`-level associativity `toAlgebra_mul_assoc` after writing each
argument as a class via surjectivity of the quotient map. -/
lemma mulQ_assoc [MonoidalPreadditive V] [MonoidalLinear ℂ V] (E : FiberFunctor C V)
    (A B D : algebra E E) : mulQ E (mulQ E A B) D = mulQ E A (mulQ E B D) := by
  obtain ⟨a, rfl⟩ := (naturalityRel E E).mkQ_surjective A
  obtain ⟨b, rfl⟩ := (naturalityRel E E).mkQ_surjective B
  obtain ⟨d, rfl⟩ := (naturalityRel E E).mkQ_surjective D
  change toAlgebra E E (E.mul (E.mul a b) d) = toAlgebra E E (E.mul a (E.mul b d))
  exact toAlgebra_mul_assoc E a b d

/-- The **unit element** of the coend algebra `A(E)`: the class `[𝟙_C, id_{E 𝟙}]` of the
pre-unit `one` (Müger §2.3). -/
noncomputable def oneQ (E : FiberFunctor C V) : algebra E E :=
  toAlgebra E E E.one

@[simp] lemma oneQ_def (E : FiberFunctor C V) : oneQ E = toAlgebra E E E.one := rfl

/-- **Left unit law of the coend product** `A(E)`: `oneQ · A = A`.  Descent of
`toAlgebra_one_mul` through the surjective quotient map. -/
lemma mulQ_oneQ_mul [MonoidalPreadditive V] [MonoidalLinear ℂ V] (E : FiberFunctor C V)
    (A : algebra E E) : mulQ E (oneQ E) A = A := by
  obtain ⟨a, rfl⟩ := (naturalityRel E E).mkQ_surjective A
  change mulQ E (toAlgebra E E E.one) (toAlgebra E E a) = toAlgebra E E a
  rw [mulQ_toAlgebra]
  exact toAlgebra_one_mul E a

/-- **Right unit law of the coend product** `A(E)`: `A · oneQ = A`.  Descent of
`toAlgebra_mul_one` through the surjective quotient map. -/
lemma mulQ_mul_oneQ [MonoidalPreadditive V] [MonoidalLinear ℂ V] (E : FiberFunctor C V)
    (A : algebra E E) : mulQ E A (oneQ E) = A := by
  obtain ⟨a, rfl⟩ := (naturalityRel E E).mkQ_surjective A
  change mulQ E (toAlgebra E E a) (toAlgebra E E E.one) = toAlgebra E E a
  rw [mulQ_toAlgebra]
  exact toAlgebra_mul_one E a

/-- **Commutativity of the coend product** `A(E)`: `A · B = B · A`.  Descent of
`toAlgebra_mul_comm` through the surjective quotient map.  This is the key consequence of `C`
being **symmetric** (Müger §2.3): the natural-transformation algebra is commutative, which is
what allows its spectrum to be a group via Gelfand duality. -/
lemma mulQ_comm [MonoidalPreadditive V] [MonoidalLinear ℂ V] (E : FiberFunctor C V)
    (A B : algebra E E) : mulQ E A B = mulQ E B A := by
  obtain ⟨a, rfl⟩ := (naturalityRel E E).mkQ_surjective A
  obtain ⟨b, rfl⟩ := (naturalityRel E E).mkQ_surjective B
  change toAlgebra E E (E.mul a b) = toAlgebra E E (E.mul b a)
  exact toAlgebra_mul_comm E a b

/-- The natural-transformation coend `A(E)` is a **commutative unital ring** under `mulQ` with
unit `oneQ` (Müger §2.3): distributivity is the bilinearity of `mulQ`, associativity is
`mulQ_assoc` (descent of `homMul_map_associator`), the unit laws are `mulQ_oneQ_mul`/
`mulQ_mul_oneQ`, and commutativity is `mulQ_comm` (descent of the braiding coherence, using
that `C` is symmetric).  `A(E) = ∫^X End(E X)` is thereby a commutative unital `ℂ`-algebra —
the algebra whose characters reconstruct the group in the concrete Tannaka theorem. -/
noncomputable instance [MonoidalPreadditive V] [MonoidalLinear ℂ V] (E : FiberFunctor C V) :
    CommRing (algebra E E) :=
  { (inferInstance : AddCommGroup (algebra E E)) with
    mul := fun x y => mulQ E x y
    one := oneQ E
    left_distrib := fun a b c => (mulQ E a).map_add b c
    right_distrib := fun a b c => by
      change mulQ E (a + b) c = mulQ E a c + mulQ E b c
      rw [map_add]; rfl
    zero_mul := fun a => by change mulQ E 0 a = 0; rw [map_zero]; rfl
    mul_zero := fun a => (mulQ E a).map_zero
    mul_assoc := mulQ_assoc E
    one_mul := mulQ_oneQ_mul E
    mul_one := mulQ_mul_oneQ E
    mul_comm := mulQ_comm E }

/-- The coend `A(E)` is a **`ℂ`-algebra** (Müger §2.3): the scalar action commutes with the
ring product because `mulQ` is `ℂ`-bilinear.  This is the unital associative `ℂ`-algebra
`A(E) = ∫^X End(E X)` whose spectrum reconstructs the group in the concrete Tannaka theorem. -/
noncomputable instance [MonoidalPreadditive V] [MonoidalLinear ℂ V] (E : FiberFunctor C V) :
    Algebra ℂ (algebra E E) :=
  Algebra.ofModule
    (fun r x y => by
      change mulQ E (r • x) y = r • mulQ E x y
      rw [map_smul, LinearMap.smul_apply])
    (fun r x y => by
      change mulQ E x (r • y) = r • mulQ E x y
      rw [map_smul])

/-- The **component-wise dagger** as an additive map on the pre-algebra `A₀(E)`:
`[X, s] ↦ [X, s†]` (Müger §2.3).  Additivity is `DaggerLinear.dagger_add`; this is the
underlying involution of the ∗-structure on the fiber-functor algebra. -/
noncomputable def starHom [DaggerCategory V] [DaggerLinear V] (E : FiberFunctor C V) :
    E.preAlgebra E →+ E.preAlgebra E :=
  DirectSum.toAddMonoid fun X =>
    AddMonoidHom.mk' (fun s => mk X (DaggerCategory.dagger s)) fun s t => by
      simp only [DaggerLinear.dagger_add, mk_add]

@[simp] lemma starHom_mk [DaggerCategory V] [DaggerLinear V] (E : FiberFunctor C V) (X : C)
    (s : E.functor.obj X ⟶ E.functor.obj X) :
    starHom E (mk X s) = mk X (DaggerCategory.dagger s) := by
  unfold starHom
  change DirectSum.toAddMonoid _
      (DirectSum.of (fun X => E.functor.obj X ⟶ E.functor.obj X) X s)
    = mk X (DaggerCategory.dagger s)
  rw [DirectSum.toAddMonoid_of]
  rfl

/-- The component-wise dagger is **involutive** on `A₀(E)`: `[X, s†]† = [X, s]`. -/
lemma starHom_starHom [DaggerCategory V] [DaggerLinear V] (E : FiberFunctor C V)
    (a : E.preAlgebra E) : starHom E (starHom E a) = a := by
  suffices h : (starHom E).comp (starHom E) = AddMonoidHom.id (E.preAlgebra E) from
    DFunLike.congr_fun h a
  refine DirectSum.addHom_ext fun X s => ?_
  change starHom E (starHom E (mk X s)) = mk X s
  rw [starHom_mk, starHom_mk, DaggerCategory.dagger_dagger]

/-- The component-wise dagger is **conjugate-`ℂ`-linear** on `A₀(E)`:
`(c • a)† = (star c) • a†`. -/
lemma starHom_smul [DaggerCategory V] [DaggerLinear V] (E : FiberFunctor C V) (c : ℂ)
    (a : E.preAlgebra E) : starHom E (c • a) = star c • starHom E a := by
  suffices h : (starHom E).comp (DistribSMul.toAddMonoidHom (E.preAlgebra E) c)
      = (DistribSMul.toAddMonoidHom (E.preAlgebra E) (star c)).comp (starHom E) from
    DFunLike.congr_fun h a
  refine DirectSum.addHom_ext fun X s => ?_
  change starHom E (c • mk X s) = star c • starHom E (mk X s)
  rw [← mk_smul, starHom_mk, DaggerLinear.dagger_smul, mk_smul, starHom_mk]

/-- **The component-wise dagger preserves the naturality ideal on generators** (Müger §2.3):
applying `starHom` to a naturality generator for `(f, g)` yields the negation of the generator
for `(f†, g†)`, using that `E` is ∗-preserving (`E(f)† = E(f†)`). -/
lemma starHom_mem_naturalityRel_gen [DaggerCategory C] [DaggerCategory V] [DaggerLinear V]
    (E : FiberFunctor C V) (hE' : E.IsStarPreserving) {X Y : C} (f : X ⟶ Y)
    (g : E.functor.obj Y ⟶ E.functor.obj X) :
    starHom E (mk X (E.functor.map f ≫ g) - mk Y (g ≫ E.functor.map f)) ∈ naturalityRel E E := by
  rw [map_sub, starHom_mk, starHom_mk, DaggerCategory.dagger_comp, DaggerCategory.dagger_comp,
    ← hE' f, ← neg_sub]
  exact neg_mem (Submodule.subset_span
    ⟨Y, X, DaggerCategory.dagger f, DaggerCategory.dagger g, rfl⟩)

/-- **The component-wise dagger preserves the naturality ideal** `N ≤ starHom⁻¹ N` (Müger §2.3):
since `starHom` is additive and conjugate-linear and maps generators into `N`, it maps the
whole submodule into itself.  This is what lets the ∗-involution descend to the coend. -/
lemma starHom_mem_naturalityRel [DaggerCategory C] [DaggerCategory V] [DaggerLinear V]
    (E : FiberFunctor C V) (hE' : E.IsStarPreserving) {x : E.preAlgebra E}
    (hx : x ∈ naturalityRel E E) :
    starHom E x ∈ naturalityRel E E := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro y ⟨X, Y, f, g, rfl⟩
    exact starHom_mem_naturalityRel_gen E hE' f g
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [map_add]; exact Submodule.add_mem _ ha hb
  · intro c a _ ha; rw [starHom_smul]; exact Submodule.smul_mem _ _ ha

/-- The component-wise dagger as a `starRingEnd ℂ`-**semilinear** (conjugate-linear) map on
`A₀(E)`, bundling `starHom` with its conjugate-linearity `starHom_smul`. -/
noncomputable def starHomₛₗ [DaggerCategory V] [DaggerLinear V] (E : FiberFunctor C V) :
    E.preAlgebra E →ₛₗ[starRingEnd ℂ] E.preAlgebra E where
  toFun := starHom E
  map_add' := (starHom E).map_add
  map_smul' c a := by rw [starHom_smul, starRingEnd_apply]

/-- The **∗-involution on the coend algebra** `A(E)` (Müger §2.3): the descent of the
component-wise dagger through the naturality ideal (well-defined by `starHom_mem_naturalityRel`,
using that `E` is ∗-preserving).  It is `starRingEnd ℂ`-semilinear (conjugate-linear). -/
noncomputable def starQ [DaggerCategory C] [DaggerCategory V] [DaggerLinear V]
    (E : FiberFunctor C V) (hE' : E.IsStarPreserving) :
    algebra E E →ₛₗ[starRingEnd ℂ] algebra E E :=
  Submodule.mapQ (naturalityRel E E) (naturalityRel E E) (starHomₛₗ E)
    fun _ hx => Submodule.mem_comap.mpr (starHom_mem_naturalityRel E hE' hx)

@[simp] lemma starQ_toAlgebra [DaggerCategory C] [DaggerCategory V] [DaggerLinear V]
    (E : FiberFunctor C V) (hE' : E.IsStarPreserving) (a : E.preAlgebra E) :
    starQ E hE' (toAlgebra E E a) = toAlgebra E E (starHom E a) := rfl

/-- The ∗-involution on `A(E)` is **involutive**: `(A⋆)⋆ = A`. -/
lemma starQ_starQ [DaggerCategory C] [DaggerCategory V] [DaggerLinear V]
    (E : FiberFunctor C V) (hE' : E.IsStarPreserving) (A : algebra E E) :
    starQ E hE' (starQ E hE' A) = A := by
  obtain ⟨a, rfl⟩ := (naturalityRel E E).mkQ_surjective A
  rw [show (naturalityRel E E).mkQ a = toAlgebra E E a from rfl, starQ_toAlgebra,
    starQ_toAlgebra, starHom_starHom]

/-- **Multiplicativity of the ∗-involution at the `preAlgebra` level** (Müger §2.3):
`[(a · b)⋆] = [b⋆ · a⋆]` in `A(E)`.  Reduces both factors to homogeneous generators by
bi-additivity (two nested `DirectSum.addHom_ext`; `starHom` is conjugate-linear, hence only
additive), where the generator case is the convolution ∗-homomorphism `homMul_dagger`
combined with the commutativity `toAlgebra_mul_comm`. -/
lemma toAlgebra_starHom_mul [MonoidalPreadditive V] [MonoidalLinear ℂ V] [DaggerMonoidalCategory V]
    [DaggerLinear V] (E : FiberFunctor C V) (hE : E.IsStarMonoidal) (a b : E.preAlgebra E) :
    toAlgebra E E (starHom E (E.mul a b))
      = toAlgebra E E (E.mul (starHom E b) (starHom E a)) := by
  suffices Ha : ∀ b : E.preAlgebra E,
      ((toAlgebra E E).toAddMonoidHom.comp (starHom E)).comp (E.mul.flip b).toAddMonoidHom
        = (toAlgebra E E).toAddMonoidHom.comp
          ((E.mul (starHom E b)).toAddMonoidHom.comp (starHom E)) by
    exact DFunLike.congr_fun (Ha b) a
  clear a b
  intro b
  refine DirectSum.addHom_ext fun X s => ?_
  suffices Hb : ((toAlgebra E E).toAddMonoidHom.comp (starHom E)).comp
        (E.mul (mk X s)).toAddMonoidHom
      = (toAlgebra E E).toAddMonoidHom.comp
        ((E.mul.flip (starHom E (mk X s))).toAddMonoidHom.comp (starHom E)) by
    exact DFunLike.congr_fun Hb b
  clear b
  refine DirectSum.addHom_ext fun Y t => ?_
  change toAlgebra E E (starHom E (E.mul (mk X s) (mk Y t)))
      = toAlgebra E E (E.mul (starHom E (mk Y t)) (starHom E (mk X s)))
  rw [mul_mk_mk, starHom_mk, homMul_dagger hE, starHom_mk, starHom_mk, mul_mk_mk, ← mul_mk_mk,
    ← mul_mk_mk]
  exact toAlgebra_mul_comm E (mk X (DaggerCategory.dagger s)) (mk Y (DaggerCategory.dagger t))

/-- **The ∗-involution is multiplicative (anti-homomorphism)** on the coend algebra `A(E)`
(Müger §2.3): `(A · B)⋆ = B⋆ · A⋆`.  Descent of `toAlgebra_starHom_mul` through the surjective
quotient map. -/
lemma starQ_mulQ [MonoidalPreadditive V] [MonoidalLinear ℂ V] [DaggerCategory C]
    [DaggerMonoidalCategory V] [DaggerLinear V] (E : FiberFunctor C V) (hE : E.IsStarMonoidal)
    (hE' : E.IsStarPreserving) (A B : algebra E E) :
    starQ E hE' (mulQ E A B) = mulQ E (starQ E hE' B) (starQ E hE' A) := by
  obtain ⟨a, rfl⟩ := (naturalityRel E E).mkQ_surjective A
  obtain ⟨b, rfl⟩ := (naturalityRel E E).mkQ_surjective B
  change starQ E hE' (mulQ E (toAlgebra E E a) (toAlgebra E E b))
      = mulQ E (starQ E hE' (toAlgebra E E b)) (starQ E hE' (toAlgebra E E a))
  rw [mulQ_toAlgebra, starQ_toAlgebra, starQ_toAlgebra, starQ_toAlgebra, mulQ_toAlgebra]
  exact toAlgebra_starHom_mul E hE a b

/-- The coend algebra `A(E)` is a **`∗`-ring** (Müger §2.3) for a ∗-preserving ∗-monoidal
fiber functor: the conjugate-linear involution `starQ` is additive and an anti-multiplicative
involution.  This is provided as a `def` parametrised by the ∗-hypotheses `hE`/`hE'` (rather
than a global instance, since those are properties of `E`, not typeclasses). -/
@[reducible] noncomputable def starRing [MonoidalPreadditive V] [MonoidalLinear ℂ V]
    [DaggerCategory C] [DaggerMonoidalCategory V] [DaggerLinear V] (E : FiberFunctor C V)
    (hE : E.IsStarMonoidal)
    (hE' : E.IsStarPreserving) : StarRing (algebra E E) where
  star A := starQ E hE' A
  star_involutive := starQ_starQ E hE'
  star_mul := starQ_mulQ E hE hE'
  star_add := (starQ E hE').map_add

/-- **The ∗-involution is conjugate-`ℂ`-linear** on `A(E)` (the `StarModule ℂ` law,
Müger §2.3): `(c • A)⋆ = (star c) • A⋆`.  This is `starQ`'s `starRingEnd ℂ`-semilinearity. -/
@[simp] lemma starQ_smul [DaggerCategory C] [DaggerCategory V] [DaggerLinear V]
    (E : FiberFunctor C V) (hE' : E.IsStarPreserving) (c : ℂ) (A : algebra E E) :
    starQ E hE' (c • A) = star c • starQ E hE' A := by
  rw [map_smulₛₗ, starRingEnd_apply]

/-- **The ∗-involution fixes the unit** `oneQ⋆ = oneQ` (`star_one`), since `𝟙† = 𝟙`. -/
@[simp] lemma starQ_oneQ [DaggerCategory C] [DaggerCategory V] [DaggerLinear V]
    (E : FiberFunctor C V) (hE' : E.IsStarPreserving) : starQ E hE' (oneQ E) = oneQ E := by
  rw [oneQ_def, starQ_toAlgebra]
  congr 1
  change starHom E (mk (𝟙_ C) (𝟙 (E.functor.obj (𝟙_ C))))
    = mk (𝟙_ C) (𝟙 (E.functor.obj (𝟙_ C)))
  rw [starHom_mk, DaggerCategory.dagger_id]

/-- The coend algebra `A(E)` of a **∗-functor** (`E.IsStar`) is a `∗`-ring (Müger §2.3),
available as a global instance: the conjugate-linear involution `starQ` is an additive,
anti-multiplicative involution. -/
noncomputable instance instStarRing [MonoidalPreadditive V] [MonoidalLinear ℂ V]
    [DaggerCategory C] [DaggerMonoidalCategory V] [DaggerLinear V] (E : FiberFunctor C V)
    [hE : E.IsStar] : StarRing (algebra E E) :=
  starRing E hE.isStarMonoidal hE.isStarPreserving

/-- The ∗-involution on `A(E)` is conjugate-`ℂ`-linear, so `A(E)` is a `StarModule ℂ`.
Together with the `Algebra ℂ`, `CommRing` and `StarRing` instances this makes `A(E)` a
commutative star `ℂ`-algebra — the algebra of the concrete C\*-Tannaka theorem. -/
instance instStarModule [MonoidalPreadditive V] [MonoidalLinear ℂ V] [DaggerCategory C]
    [DaggerMonoidalCategory V] [DaggerLinear V] (E : FiberFunctor C V) [hE : E.IsStar] :
    StarModule ℂ (algebra E E) where
  star_smul c a := starQ_smul E hE.isStarPreserving c a

/-! ### Generator API for the coend algebra

Concrete handles on the ring/`∗` operations of `A(E)` in terms of the homogeneous generators
`[X, s] = toAlgebra (mk X s)`, used throughout the downstream C\*-completion and character
theory (Müger Prop 2.22–2.28). -/

/-- **Dinaturality of the coend** (the defining relation of `A(E) = ∫^X End(E X)`): for
`f : X ⟶ Y` and `g : E Y ⟶ E X`, the classes `[X, E f ≫ g]` and `[Y, g ≫ E f]` coincide in
`A(E)`.  This is exactly the quotient by the naturality ideal, lifted to `toAlgebra`. -/
lemma toAlgebra_mk_naturality (E : FiberFunctor C V) {X Y : C} (f : X ⟶ Y)
    (g : E.functor.obj Y ⟶ E.functor.obj X) :
    toAlgebra E E (mk X (E.functor.map f ≫ g))
      = toAlgebra E E (mk Y (g ≫ E.functor.map f)) := by
  rw [← sub_eq_zero, ← map_sub]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨X, Y, f, g, rfl⟩)

/-- **Dinaturality of the off-diagonal coend** `A(E₁, E₂) = ∫^X Hom(E₂ X, E₁ X)` (Müger §2.3):
for `f : X ⟶ Y` and `g : E₂ Y ⟶ E₁ X`, the classes `[X, E₂ f ≫ g]` and `[Y, g ≫ E₁ f]`
coincide.  This is the defining relation of the bimodule `A(E₁, E₂)` underlying the
reconstruction functor `C → Rep(G_E)`; the self case `E₁ = E₂` is `toAlgebra_mk_naturality`. -/
lemma toAlgebra_mk_naturality' (E₁ E₂ : FiberFunctor C V) {X Y : C} (f : X ⟶ Y)
    (g : E₂.functor.obj Y ⟶ E₁.functor.obj X) :
    toAlgebra E₁ E₂ (mk X (E₂.functor.map f ≫ g))
      = toAlgebra E₁ E₂ (mk Y (g ≫ E₁.functor.map f)) := by
  rw [← sub_eq_zero, ← map_sub]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨X, Y, f, g, rfl⟩)

/-- **Pushing a generator into a biproduct corner** (Müger Prop 2.22): via dinaturality along
the inclusion `X → X ⊞ Y`, the class `[X, s]` equals `[X ⊞ Y, fst ≫ s ≫ inl]`. -/
lemma toAlgebra_mk_biprod_left [HasBinaryBiproducts C] (E : FiberFunctor C V) {X : C} (Y : C)
    (s : E.functor.obj X ⟶ E.functor.obj X) :
    toAlgebra E E (mk X s)
      = toAlgebra E E (mk (X ⊞ Y)
          (E.functor.map biprod.fst ≫ s ≫ E.functor.map biprod.inl)) := by
  have h := toAlgebra_mk_naturality E (biprod.inl : X ⟶ X ⊞ Y) (E.functor.map biprod.fst ≫ s)
  rw [← Category.assoc, ← E.functor.map_comp, biprod.inl_fst, E.functor.map_id, Category.id_comp,
    Category.assoc] at h
  exact h

/-- Right-corner analogue of `toAlgebra_mk_biprod_left`. -/
lemma toAlgebra_mk_biprod_right [HasBinaryBiproducts C] (E : FiberFunctor C V) (X : C) {Y : C}
    (t : E.functor.obj Y ⟶ E.functor.obj Y) :
    toAlgebra E E (mk Y t)
      = toAlgebra E E (mk (X ⊞ Y)
          (E.functor.map biprod.snd ≫ t ≫ E.functor.map biprod.inr)) := by
  have h := toAlgebra_mk_naturality E (biprod.inr : Y ⟶ X ⊞ Y) (E.functor.map biprod.snd ≫ t)
  rw [← Category.assoc, ← E.functor.map_comp, biprod.inr_snd, E.functor.map_id, Category.id_comp,
    Category.assoc] at h
  exact h

/-- **A sum of two generators is a single generator** (Müger Prop 2.22): the block-diagonal
endomorphism on `E(X ⊞ Y)` represents `[X, s] + [Y, t]`.  Iterating, every element of `A(E)`
is a single class `[Z, r]` — the fact underlying the C\*-norm and completion (Prop 2.22–24). -/
lemma toAlgebra_mk_add_biprod [HasBinaryBiproducts C] (E : FiberFunctor C V) {X Y : C}
    (s : E.functor.obj X ⟶ E.functor.obj X) (t : E.functor.obj Y ⟶ E.functor.obj Y) :
    toAlgebra E E (mk X s) + toAlgebra E E (mk Y t)
      = toAlgebra E E (mk (X ⊞ Y)
          (E.functor.map biprod.fst ≫ s ≫ E.functor.map biprod.inl
            + E.functor.map biprod.snd ≫ t ≫ E.functor.map biprod.inr)) := by
  rw [toAlgebra_mk_biprod_left E Y s, toAlgebra_mk_biprod_right E X t, ← map_add, ← mk_add]

/-- **Every element of `A(E)` is a single generator** (Müger Proposition 2.22): for any
`A : A(E)` there are an object `Z` and an endomorphism `r : E Z ⟶ E Z` with `A = [Z, r]`.
Proved by surjectivity of the quotient map and induction over the direct sum, merging the
finitely many homogeneous components into one via the biproduct (`toAlgebra_mk_add_biprod`).
This is the structural fact that lets the C\*-norm be defined componentwise. -/
lemma exists_toAlgebra_mk [HasBinaryBiproducts C] (E : FiberFunctor C V) (A : algebra E E) :
    ∃ (Z : C) (r : E.functor.obj Z ⟶ E.functor.obj Z), A = toAlgebra E E (mk Z r) := by
  obtain ⟨a, rfl⟩ := (naturalityRel E E).mkQ_surjective A
  change ∃ Z r, toAlgebra E E a = toAlgebra E E (mk Z r)
  induction a using DirectSum.induction_on with
  | zero =>
      refine ⟨𝟙_ C, 0, ?_⟩
      change toAlgebra E E (0 : E.preAlgebra E) = toAlgebra E E (mk (𝟙_ C) 0)
      rw [mk_zero]
  | of X s => exact ⟨X, s, rfl⟩
  | add a b ha hb =>
      obtain ⟨Z₁, r₁, h₁⟩ := ha
      obtain ⟨Z₂, r₂, h₂⟩ := hb
      refine ⟨Z₁ ⊞ Z₂,
        E.functor.map biprod.fst ≫ r₁ ≫ E.functor.map biprod.inl
          + E.functor.map biprod.snd ≫ r₂ ≫ E.functor.map biprod.inr, ?_⟩
      have key : toAlgebra E E (a + b)
          = toAlgebra E E (mk Z₁ r₁) + toAlgebra E E (mk Z₂ r₂) := by
        rw [← h₁, ← h₂]; exact (toAlgebra E E).map_add a b
      rw [key, toAlgebra_mk_add_biprod]

/-- Off-diagonal analogue of `toAlgebra_mk_biprod_left` for the bimodule `A(E₁, E₂)`. -/
lemma toAlgebra_mk_biprod_left' [HasBinaryBiproducts C] (E₁ E₂ : FiberFunctor C V) {X : C} (Y : C)
    (s : E₂.functor.obj X ⟶ E₁.functor.obj X) :
    toAlgebra E₁ E₂ (mk X s)
      = toAlgebra E₁ E₂ (mk (X ⊞ Y)
          (E₂.functor.map biprod.fst ≫ s ≫ E₁.functor.map biprod.inl)) := by
  have h := toAlgebra_mk_naturality' E₁ E₂ (biprod.inl : X ⟶ X ⊞ Y)
    (E₂.functor.map biprod.fst ≫ s)
  rw [← Category.assoc, ← E₂.functor.map_comp, biprod.inl_fst, E₂.functor.map_id,
    Category.id_comp, Category.assoc] at h
  exact h

/-- Off-diagonal analogue of `toAlgebra_mk_biprod_right` for the bimodule `A(E₁, E₂)`. -/
lemma toAlgebra_mk_biprod_right' [HasBinaryBiproducts C] (E₁ E₂ : FiberFunctor C V) (X : C) {Y : C}
    (t : E₂.functor.obj Y ⟶ E₁.functor.obj Y) :
    toAlgebra E₁ E₂ (mk Y t)
      = toAlgebra E₁ E₂ (mk (X ⊞ Y)
          (E₂.functor.map biprod.snd ≫ t ≫ E₁.functor.map biprod.inr)) := by
  have h := toAlgebra_mk_naturality' E₁ E₂ (biprod.inr : Y ⟶ X ⊞ Y)
    (E₂.functor.map biprod.snd ≫ t)
  rw [← Category.assoc, ← E₂.functor.map_comp, biprod.inr_snd, E₂.functor.map_id,
    Category.id_comp, Category.assoc] at h
  exact h

/-- **A sum of two generators of `A(E₁, E₂)` is a single generator** (Müger Prop 2.22 for the
bimodule): the block-diagonal morphism on `E₂(X ⊞ Y) ⟶ E₁(X ⊞ Y)` represents `[X,s] + [Y,t]`. -/
lemma toAlgebra_mk_add_biprod' [HasBinaryBiproducts C] (E₁ E₂ : FiberFunctor C V) {X Y : C}
    (s : E₂.functor.obj X ⟶ E₁.functor.obj X) (t : E₂.functor.obj Y ⟶ E₁.functor.obj Y) :
    toAlgebra E₁ E₂ (mk X s) + toAlgebra E₁ E₂ (mk Y t)
      = toAlgebra E₁ E₂ (mk (X ⊞ Y)
          (E₂.functor.map biprod.fst ≫ s ≫ E₁.functor.map biprod.inl
            + E₂.functor.map biprod.snd ≫ t ≫ E₁.functor.map biprod.inr)) := by
  rw [toAlgebra_mk_biprod_left' E₁ E₂ Y s, toAlgebra_mk_biprod_right' E₁ E₂ X t, ← map_add,
    ← mk_add]

/-- **Every element of the bimodule `A(E₁, E₂)` is a single generator** (Müger Prop 2.22):
generalises `exists_toAlgebra_mk` from the algebra `A(E)` to the hom-space `A(E₁, E₂)`. -/
lemma exists_toAlgebra_mk' [HasBinaryBiproducts C] (E₁ E₂ : FiberFunctor C V)
    (A : algebra E₁ E₂) :
    ∃ (Z : C) (r : E₂.functor.obj Z ⟶ E₁.functor.obj Z), A = toAlgebra E₁ E₂ (mk Z r) := by
  obtain ⟨a, rfl⟩ := (naturalityRel E₁ E₂).mkQ_surjective A
  change ∃ Z r, toAlgebra E₁ E₂ a = toAlgebra E₁ E₂ (mk Z r)
  induction a using DirectSum.induction_on with
  | zero =>
      refine ⟨𝟙_ C, 0, ?_⟩
      change toAlgebra E₁ E₂ (0 : E₁.preAlgebra E₂) = toAlgebra E₁ E₂ (mk (𝟙_ C) 0)
      rw [mk_zero]
  | of X s => exact ⟨X, s, rfl⟩
  | add a b ha hb =>
      obtain ⟨Z₁, r₁, h₁⟩ := ha
      obtain ⟨Z₂, r₂, h₂⟩ := hb
      refine ⟨Z₁ ⊞ Z₂,
        E₂.functor.map biprod.fst ≫ r₁ ≫ E₁.functor.map biprod.inl
          + E₂.functor.map biprod.snd ≫ r₂ ≫ E₁.functor.map biprod.inr, ?_⟩
      have key : toAlgebra E₁ E₂ (a + b)
          = toAlgebra E₁ E₂ (mk Z₁ r₁) + toAlgebra E₁ E₂ (mk Z₂ r₂) := by
        rw [← h₁, ← h₂]; exact (toAlgebra E₁ E₂).map_add a b
      rw [key, toAlgebra_mk_add_biprod']

/-- **Scalar action on generators**: `c • [X, s] = [X, c • s]`. -/
@[simp] lemma toAlgebra_mk_smul (E : FiberFunctor C V) {X : C} (c : ℂ)
    (s : E.functor.obj X ⟶ E.functor.obj X) :
    toAlgebra E E (mk X (c • s)) = c • toAlgebra E E (mk X s) := by
  rw [mk_smul]; exact map_smul (toAlgebra E E) c (mk X s)

/-- **Additivity on generators (same degree)**: `[X, s + t] = [X, s] + [X, t]`. -/
@[simp] lemma toAlgebra_mk_add (E : FiberFunctor C V) {X : C}
    (s t : E.functor.obj X ⟶ E.functor.obj X) :
    toAlgebra E E (mk X (s + t)) = toAlgebra E E (mk X s) + toAlgebra E E (mk X t) := by
  rw [mk_add]; exact map_add (toAlgebra E E) (mk X s) (mk X t)

/-- The pre-unit class is the ring unit of `A(E)`: `[𝟙_C, id] = 1`. -/
@[simp] lemma oneQ_eq_one [MonoidalPreadditive V] [MonoidalLinear ℂ V] (E : FiberFunctor C V) :
    oneQ E = (1 : algebra E E) := rfl

/-- The structure map of the `ℂ`-algebra `A(E)` is scalar multiplication of the unit:
`algebraMap ℂ A(E) c = c • [𝟙_C, id]`. -/
lemma algebraMap_eq [MonoidalPreadditive V] [MonoidalLinear ℂ V] (E : FiberFunctor C V) (c : ℂ) :
    algebraMap ℂ (algebra E E) c = c • oneQ E := by
  rw [Algebra.algebraMap_eq_smul_one, oneQ_eq_one]

/-- The scalar `c` of `A(E)` is the class of the scaled unit endomorphism in degree `𝟙_C`:
`[𝟙_C, c • id] = algebraMap ℂ A(E) c`.  In particular the generators in degree `𝟙_C` are
exactly the scalars (when `End_V(E 𝟙) ≅ ℂ`). -/
lemma toAlgebra_mk_unit_smul [MonoidalPreadditive V] [MonoidalLinear ℂ V] (E : FiberFunctor C V)
    (c : ℂ) :
    toAlgebra E E (mk (𝟙_ C) (c • 𝟙 (E.functor.obj (𝟙_ C)))) = algebraMap ℂ (algebra E E) c := by
  rw [toAlgebra_mk_smul]
  exact (algebraMap_eq E c).symm

/-- **The ring product on generators** (Müger Prop 2.21): `[X, s] · [Y, t] = [X ⊗ Y, s ⊗ t]`
(the convolution `homMul`), via the descent `mulQ_toAlgebra`. -/
@[simp] lemma toAlgebra_mk_mul [MonoidalPreadditive V] [MonoidalLinear ℂ V] (E : FiberFunctor C V)
    {X Y : C} (s : E.functor.obj X ⟶ E.functor.obj X) (t : E.functor.obj Y ⟶ E.functor.obj Y) :
    toAlgebra E E (mk X s) * toAlgebra E E (mk Y t)
      = toAlgebra E E (mk (X ⊗ Y) (E.homMul s t)) := by
  change mulQ E (toAlgebra E E (mk X s)) (toAlgebra E E (mk Y t)) = _
  rw [mulQ_toAlgebra, mul_mk_mk]

/-- **The ∗-involution on generators** (Müger §2.3): `[X, s]⋆ = [X, s†]`. -/
@[simp] lemma star_toAlgebra_mk [MonoidalPreadditive V] [MonoidalLinear ℂ V] [DaggerCategory C]
    [DaggerMonoidalCategory V] [DaggerLinear V] (E : FiberFunctor C V) [hE : E.IsStar] {X : C}
    (s : E.functor.obj X ⟶ E.functor.obj X) :
    star (toAlgebra E E (mk X s)) = toAlgebra E E (mk X (DaggerCategory.dagger s)) := by
  change starQ E hE.isStarPreserving (toAlgebra E E (mk X s)) = _
  rw [starQ_toAlgebra, starHom_mk]

/-- **The ∗-involution in terms of the component-wise dagger** on any element of `A(E)`:
`(toAlgebra a)⋆ = toAlgebra (starHom a)`.  Generalises `star_toAlgebra_mk` from generators to
arbitrary `a : A₀(E)`; the building block for computing `⋆` after `exists_toAlgebra_mk`. -/
@[simp] lemma star_toAlgebra [MonoidalPreadditive V] [MonoidalLinear ℂ V] [DaggerCategory C]
    [DaggerMonoidalCategory V] [DaggerLinear V] (E : FiberFunctor C V) [hE : E.IsStar]
    (a : E.preAlgebra E) :
    star (toAlgebra E E a) = toAlgebra E E (starHom E a) :=
  starQ_toAlgebra E hE.isStarPreserving a

/-- A generator with self-adjoint endomorphism is **self-adjoint** in `A(E)`:
`s† = s ⟹ [X, s]⋆ = [X, s]`. -/
lemma star_toAlgebra_mk_self [MonoidalPreadditive V] [MonoidalLinear ℂ V] [DaggerCategory C]
    [DaggerMonoidalCategory V] [DaggerLinear V] (E : FiberFunctor C V) [E.IsStar] {X : C}
    {s : E.functor.obj X ⟶ E.functor.obj X} (hs : DaggerCategory.dagger s = s) :
    star (toAlgebra E E (mk X s)) = toAlgebra E E (mk X s) := by
  rw [star_toAlgebra_mk, hs]

/-- **Self-adjoint elements have self-adjoint single representatives** (Müger Prop 2.23, the
form used for the C\*-norm and positivity): a self-adjoint `a : A(E)` (`a⋆ = a`) equals a single
class `[Z, r]` with `r† = r`.  Take any representative `[Z, r₀]` (`exists_toAlgebra_mk`) and
replace `r₀` by its *real part* `(r₀ + r₀†)/2`; self-adjointness of `a` makes the class
unchanged. -/
lemma exists_toAlgebra_mk_isSelfAdjoint [HasBinaryBiproducts C] [DaggerCategory C]
    [DaggerMonoidalCategory V] [DaggerLinear V] [MonoidalPreadditive V] [MonoidalLinear ℂ V]
    (E : FiberFunctor C V) [E.IsStar] {a : algebra E E} (ha : star a = a) :
    ∃ (Z : C) (r : E.functor.obj Z ⟶ E.functor.obj Z),
      DaggerCategory.dagger r = r ∧ a = toAlgebra E E (mk Z r) := by
  obtain ⟨Z, r, rfl⟩ := exists_toAlgebra_mk E a
  rw [star_toAlgebra_mk] at ha
  refine ⟨Z, (2⁻¹ : ℂ) • (r + DaggerCategory.dagger r), ?_, ?_⟩
  · rw [DaggerLinear.dagger_smul, DaggerLinear.dagger_add, DaggerCategory.dagger_dagger,
      add_comm (DaggerCategory.dagger r) r, show star (2⁻¹ : ℂ) = 2⁻¹ by simp]
  · rw [toAlgebra_mk_smul, toAlgebra_mk_add, ha, ← two_smul ℂ, smul_smul]
    norm_num

end FiberFunctor.preAlgebra

end CategoryTheory
