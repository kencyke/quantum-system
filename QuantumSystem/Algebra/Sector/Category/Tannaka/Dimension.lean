module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Monoidal.Linear

/-!
# Categorical dimension — R7-B1

For an object `X` with a right dual in a braided monoidal category, the
**categorical (quantum) dimension** (Müger, *Abstract Duality Theory for Symmetric
Tensor ∗-Categories*, Definition 1.41) is the right trace of the identity,

```
dim X = η ≫ β ≫ ε : 𝟙 ⟶ 𝟙,
```

where `η : 𝟙 ⟶ X ⊗ ᘁX` is the coevaluation, `β : X ⊗ ᘁX ≅ ᘁX ⊗ X` the braiding,
and `ε : ᘁX ⊗ X ⟶ 𝟙` the evaluation.  In a symmetric tensor ∗-category with
`End 𝟙 = ℂ` this is a complex number, and Müger shows it is additive
(`dim (X ⊕ Y) = dim X + dim Y`), multiplicative (`dim (X ⊗ Y) = dim X · dim Y`),
and satisfies `dim X = dim X̄ ≥ 1` (Lemma 1.42).

This file fixes the **definition** (Müger Def 1.41); the numerical properties
(positivity, additivity, multiplicativity, integrality — Lemma 1.42, 2.45–2.53)
are the substantive content deferred to the rest of **R7-B**.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- The **categorical (quantum) dimension** of an object `X` with a right dual
(Müger Definition 1.41): `dim X = η ≫ β ≫ ε : 𝟙 ⟶ 𝟙`, the right trace of the
identity, where `η`/`ε` are the coevaluation/evaluation of the exact pairing
`X ⊣ ᘁX` and `β` is the braiding. -/
noncomputable def categoricalDim (X : C) [HasRightDual X] : 𝟙_ C ⟶ 𝟙_ C :=
  η_ X (Xᘁ) ≫ (β_ X (Xᘁ)).hom ≫ ε_ X (Xᘁ)

/-- The **dimension of the unit object is one** (Müger Lemma 1.42): `dim 𝟙_C = 𝟙_{𝟙_C}`.
For the unit's self-pairing the coevaluation/evaluation are `(ρ_ 𝟙).inv`/`(ρ_ 𝟙).hom`, so the
right trace of the identity collapses to `(ρ_ 𝟙).inv ≫ (β_ 𝟙 𝟙).hom ≫ (ρ_ 𝟙).hom = 𝟙`. -/
@[simp] lemma categoricalDim_unit : categoricalDim (𝟙_ C) = 𝟙 (𝟙_ C) := by
  have h : categoricalDim (𝟙_ C)
      = (ρ_ (𝟙_ C)).inv ≫ (β_ (𝟙_ C) (𝟙_ C)).hom ≫ (ρ_ (𝟙_ C)).hom := rfl
  rw [h]
  simp [MonoidalCategory.unitors_inv_equal]

/-- The **categorical dimension is independent of the chosen right dual** (Müger §1.4):
two `HasRightDual` instances for the same object give the same dimension.  The two right
duals are related by the right adjoint mate of the identity; braiding naturality plus the
coevaluation/evaluation–mate compatibilities (`coevaluation_comp_rightAdjointMate`,
`rightAdjointMate_comp_evaluation`) carry one right trace to the other.  This is what lets
`STCStar.dim (𝟙_C)` (which uses the rigid-category dual) be computed via `categoricalDim_unit`
(which uses the canonical self-dual `hasRightDualUnit`). -/
lemma categoricalDim_eq_of_hasRightDual {X : C} (d₁ d₂ : HasRightDual X) :
    @categoricalDim C _ _ _ X d₁ = @categoricalDim C _ _ _ X d₂ := by
  have T1 := @coevaluation_comp_rightAdjointMate C _ _ X X d₁ d₂ (𝟙 X)
  have T2 := @rightAdjointMate_comp_evaluation C _ _ X X d₁ d₂ (𝟙 X)
  simp only [MonoidalCategory.id_whiskerRight, MonoidalCategory.whiskerLeft_id,
    Category.comp_id, Category.id_comp] at T1 T2
  simp only [categoricalDim]
  rw [← T1, ← T2]
  simp only [Category.assoc]
  rw [BraidedCategory.braiding_naturality_right_assoc]

/-- The **right (categorical) trace** of an endomorphism `f : X ⟶ X` (Müger §1.4):
`tr(f) = η ≫ (f ▷ Xᘁ) ≫ β ≫ ε : 𝟙 ⟶ 𝟙`.  In a symmetric tensor ∗-category with `End 𝟙 = ℂ`
this is the categorical trace whose pairing with `A(E)` underlies the characters ↔ natural
transformations correspondence (Müger Prop 2.27); the categorical dimension is the trace of
the identity (`categoricalTrace_id`). -/
noncomputable def categoricalTrace {X : C} [HasRightDual X] (f : X ⟶ X) : 𝟙_ C ⟶ 𝟙_ C :=
  η_ X (Xᘁ) ≫ (f ▷ Xᘁ) ≫ (β_ X (Xᘁ)).hom ≫ ε_ X (Xᘁ)

/-- The categorical **dimension is the trace of the identity** (Müger Definition 1.41):
`tr(𝟙_X) = dim X`. -/
@[simp] lemma categoricalTrace_id (X : C) [HasRightDual X] :
    categoricalTrace (𝟙 X) = categoricalDim X := by
  rw [categoricalTrace, categoricalDim, MonoidalCategory.id_whiskerRight, Category.id_comp]

/-- The categorical trace is **additive** in its argument (Müger §1.4): `tr(f + g) = tr f + tr g`.
Additivity of the right whiskering and bilinearity of composition. -/
lemma categoricalTrace_add [Preadditive C] [MonoidalPreadditive C] {X : C} [HasRightDual X]
    (f g : X ⟶ X) :
    categoricalTrace (f + g) = categoricalTrace f + categoricalTrace g := by
  simp only [categoricalTrace, MonoidalPreadditive.add_whiskerRight, Preadditive.add_comp,
    Preadditive.comp_add]

/-- The categorical trace is **`R`-linear** in its argument (Müger §1.4):
`tr(c • f) = c • tr f`.  `R`-linearity of the right whiskering and of composition. -/
lemma categoricalTrace_smul {R : Type*} [Semiring R] [Preadditive C] [Linear R C]
    [MonoidalPreadditive C] [MonoidalLinear R C] {X : C} [HasRightDual X] (c : R) (f : X ⟶ X) :
    categoricalTrace (c • f) = c • categoricalTrace f := by
  simp only [categoricalTrace, MonoidalLinear.smul_whiskerRight, Linear.smul_comp,
    Linear.comp_smul]

/-- The categorical trace bundled as an **`R`-linear functional** `End X →ₗ[R] End 𝟙`
(Müger §1.4).  The continuous dual of `A(E)` is built from such trace functionals; pairing a
natural transformation with `[X, s]` uses `tr(s ≫ η_X)` (Müger Prop 2.27). -/
noncomputable def categoricalTraceₗ {R : Type*} [Semiring R] [Preadditive C] [Linear R C]
    [MonoidalPreadditive C] [MonoidalLinear R C] (X : C) [HasRightDual X] :
    (X ⟶ X) →ₗ[R] (𝟙_ C ⟶ 𝟙_ C) where
  toFun := categoricalTrace
  map_add' := categoricalTrace_add
  map_smul' c f := categoricalTrace_smul c f

@[simp] lemma categoricalTraceₗ_apply {R : Type*} [Semiring R] [Preadditive C] [Linear R C]
    [MonoidalPreadditive C] [MonoidalLinear R C] (X : C) [HasRightDual X] (f : X ⟶ X) :
    categoricalTraceₗ (R := R) X f = categoricalTrace f := rfl

/-- The trace of a **scalar multiple of the identity** is that scalar times the dimension
(Müger §1.4): `tr(c • 𝟙_X) = c • dim X`.  Together with `End 𝟙 = ℂ` this expresses the trace
of scalars on `X`. -/
@[simp] lemma categoricalTrace_smul_id {R : Type*} [Semiring R] [Preadditive C] [Linear R C]
    [MonoidalPreadditive C] [MonoidalLinear R C] (X : C) [HasRightDual X] (c : R) :
    categoricalTrace (c • 𝟙 X) = c • categoricalDim X := by
  rw [categoricalTrace_smul, categoricalTrace_id]

/-- The trace of the identity on the **unit object** is `𝟙` (Müger §1.4, the normalisation
`dim 𝟙 = 1`): `tr(𝟙_{𝟙_C}) = 𝟙`.  Combines `categoricalTrace_id` with `categoricalDim_unit`. -/
@[simp] lemma categoricalTrace_id_unit : categoricalTrace (𝟙 (𝟙_ C)) = 𝟙 (𝟙_ C) := by
  rw [categoricalTrace_id, categoricalDim_unit]

/-- Paper notation `d(X)` for the categorical (quantum) dimension, as written by Müger
(`references/mueger-tannaka-duality/`, INDEX "Key concepts" and Definition 1.41:
`d(X) = R†∘R ∈ End 1 = ℂ`).  Open `scoped CategoryTheory.SectorDim` to use. -/
scoped[CategoryTheory.SectorDim] notation "d(" X ")" => CategoryTheory.categoricalDim X

/-- Paper notation `tr(f)` for the right categorical trace of an endomorphism, as written by
Müger (`references/mueger-tannaka-duality/`, §1.4).  Lower-case `tr` avoids the global `Tr`
prefix already bound to `Matrix.trace`.  Open `scoped CategoryTheory.SectorDim` to use. -/
scoped[CategoryTheory.SectorDim] notation "tr(" f ")" => CategoryTheory.categoricalTrace f

end CategoryTheory

section PaperNotation
open CategoryTheory
open scoped CategoryTheory.SectorDim
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
variable (X : C) [HasRightDual X] (f : X ⟶ X)

-- The paper notations elaborate to the underlying definitions.  (Pretty-print round-trip
-- `d(X)` / `tr(f)` is verified during development; the project's `linter.hashCommand` forbids
-- committing `#check` / `#guard_msgs`, so we pin the elaboration with `example`s instead.)
example : (d(X)) = categoricalDim X := rfl
example : (tr(f)) = categoricalTrace f := rfl
end PaperNotation
