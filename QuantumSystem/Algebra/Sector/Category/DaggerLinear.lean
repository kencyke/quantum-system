module

public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.Data.Complex.Basic
public import QuantumSystem.Algebra.Sector.Category.Dagger

/-!
# Conjugate-linearity of the dagger

`DaggerCategory` (`Dagger.lean`) fixes only the multiplicative/involutive structure
of the adjoint `f ↦ f†`.  In a `ℂ`-linear category the dagger is moreover
**conjugate-linear** on each hom-space — additive and conjugate-homogeneous — as
holds in every C\*-category (Müger, *Abstract Duality Theory for Symmetric Tensor
∗-Categories*, §1.4).  This mixin records that compatibility.

It is factored into its own small module so that both the C\*-side (the C\*-algebra
structure on `End X`, `EndCStarAlgebra.lean`) and the fiber-functor side (the
∗-structure on the reconstruction algebra, `FiberAlgebra.lean`) can depend on it
without pulling in each other's heavier infrastructure.
-/

@[expose] public section

namespace CategoryTheory

universe v u

/-- A `ℂ`-linear dagger category whose dagger is **conjugate-linear** on each hom-space:
`(f + g)† = f† + g†` and `(c • f)† = (star c) • f†`.  `DaggerCategory` alone fixes only the
multiplicative/involutive structure; this mixin records compatibility with the additive and
`ℂ`-linear structure, as holds in every C\*-category.  It is what makes the component-wise
dagger a well-defined conjugate-linear involution (e.g. on the fiber-functor algebra, and the
star-ring structure on each `End X`). -/
class DaggerLinear (W : Type u) [Category.{v} W] [Preadditive W] [Linear ℂ W]
    [DaggerCategory W] : Prop where
  /-- The dagger is additive. -/
  dagger_add : ∀ {X Y : W} (f g : X ⟶ Y),
    DaggerCategory.dagger (f + g) = DaggerCategory.dagger f + DaggerCategory.dagger g
  /-- The dagger is conjugate-`ℂ`-linear. -/
  dagger_smul : ∀ {X Y : W} (c : ℂ) (f : X ⟶ Y),
    DaggerCategory.dagger (c • f) = star c • DaggerCategory.dagger f

section
variable {W : Type u} [Category.{v} W] [Preadditive W] [Linear ℂ W] [DaggerCategory W]
    [DaggerLinear W]

/-- The dagger sends the zero morphism to the zero morphism. -/
@[simp] lemma DaggerLinear.dagger_zero {X Y : W} :
    DaggerCategory.dagger (0 : X ⟶ Y) = 0 := by
  simpa using DaggerLinear.dagger_smul (0 : ℂ) (0 : X ⟶ Y)

/-- The dagger commutes with negation. -/
lemma DaggerLinear.dagger_neg {X Y : W} (f : X ⟶ Y) :
    DaggerCategory.dagger (-f) = -DaggerCategory.dagger f := by
  have h := DaggerLinear.dagger_add f (-f)
  rw [add_neg_cancel, DaggerLinear.dagger_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- The dagger is subtractive, `(f - g)† = f† - g†`. -/
lemma DaggerLinear.dagger_sub {X Y : W} (f g : X ⟶ Y) :
    DaggerCategory.dagger (f - g) = DaggerCategory.dagger f - DaggerCategory.dagger g := by
  rw [sub_eq_add_neg, DaggerLinear.dagger_add, DaggerLinear.dagger_neg, ← sub_eq_add_neg]

end

end CategoryTheory
