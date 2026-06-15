module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import QuantumSystem.Algebra.Sector.Category.Dagger

/-!
# The target: rigid symmetric (C\*-)tensor categories

The DHR/Doplicher–Roberts theory says that, in a high-dimensional local net,
the superselection sectors form a **rigid symmetric C\*-tensor category**.  This
file bundles the *categorical* core of that target on top of Mathlib's monoidal
hierarchy together with the bespoke dagger layer (`Dagger.lean`):

* `CategoryTheory.RigidSymmetricDaggerCategory` — a category that is
  simultaneously `SymmetricCategory`, `RigidCategory` and
  `DaggerMonoidalCategory`, with the symmetry required to be unitary.

## On the C\*-analytic enrichment

A genuine *C\*-tensor category* additionally requires each hom-space to be a
complex Banach space with the C\*-identity `‖f† ≫ f‖ = ‖f‖²` and positivity of
`f† ≫ f`.  Mathlib does not have normed/Banach-*enriched* categories, so this
analytic enrichment is **not** captured by the class below; it is supplied
concretely where the category is realised inside a C\*-algebra (the hom-spaces
of `End(A)` are closed subspaces of `A`, see `Endomorphism.lean`).  The class
here is the categorical skeleton; "C\*" lives in the realisation, not the
abstract class.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory

universe v u

/-- The categorical core of a **rigid symmetric dagger tensor category**:
symmetric + rigid + dagger-monoidal, with unitary symmetry.  This is the
abstract target into which a high-dimensional DHR sector category lands; the
C\*-analytic enrichment is supplied at the point of realisation. -/
class RigidSymmetricDaggerCategory (C : Type u) [Category.{v} C]
    [MonoidalCategory C] extends
    SymmetricCategory C, RigidCategory C, DaggerMonoidalCategory C where
  /-- The symmetry braiding is unitary with respect to the dagger. -/
  symmetry_unitary : ∀ X Y : C, Unitary (β_ X Y).hom

/-- The dagger-monoidal structure transfers to a full monoidal subcategory: its
tensor, associator and unitors are the ambient ones (via `homMk`/`isoMk`), so the
dagger compatibilities reduce by `ext` to the ambient ones. -/
instance fullSubcategoryDaggerMonoidal {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [DaggerMonoidalCategory C] (P : ObjectProperty C) [P.IsMonoidal] :
    DaggerMonoidalCategory P.FullSubcategory where
  dagger_tensorHom f g := by
    ext; exact DaggerMonoidalCategory.dagger_tensorHom f.hom g.hom
  associator_unitary X Y Z := by
    ext; exact DaggerMonoidalCategory.associator_unitary X.obj Y.obj Z.obj
  leftUnitor_unitary X := by
    ext; exact DaggerMonoidalCategory.leftUnitor_unitary X.obj
  rightUnitor_unitary X := by
    ext; exact DaggerMonoidalCategory.rightUnitor_unitary X.obj

/-- **Assembly of the DHR target on a full subcategory.**  If `C` is symmetric and
dagger-monoidal with unitary symmetry, and `P` is a monoidal object property whose
full subcategory is rigid (every object having a dual within `P` — the input the
existence of conjugates provides), then `P.FullSubcategory` is a
`RigidSymmetricDaggerCategory`.  The symmetric and dagger-monoidal structures
transfer from `C` along the full embedding (`fullSymmetricSubcategory` and
`fullSubcategoryDaggerMonoidal`), the rigid structure is the supplied hypothesis,
and the symmetry stays unitary because the braiding of the full subcategory has the
ambient braiding as underlying morphism.

This is the categorical core of the Doplicher–Roberts target assembly (Müger §1.4):
once conjugates of the (symmetric, transportable) DHR sectors are known to exist —
making the conjugate-closed full subcategory rigid — this turns that subcategory
into the abstract target class. -/
@[reducible] noncomputable def fullSubcategoryRigidSymmetricDagger {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [SymmetricCategory C] [DaggerMonoidalCategory C]
    (P : ObjectProperty C) [P.IsMonoidal] [RigidCategory P.FullSubcategory]
    (hsymU : ∀ X Y : C, Unitary (β_ X Y).hom) :
    RigidSymmetricDaggerCategory P.FullSubcategory where
  symmetry_unitary X Y := by
    obtain ⟨h1, h2⟩ := hsymU X.obj Y.obj
    refine ⟨?_, ?_⟩
    · apply ObjectProperty.hom_ext
      change (β_ X.obj Y.obj).hom ≫ ((β_ X.obj Y.obj).hom)† = 𝟙 (X.obj ⊗ Y.obj)
      exact h1
    · apply ObjectProperty.hom_ext
      change ((β_ X.obj Y.obj).hom)† ≫ (β_ X.obj Y.obj).hom = 𝟙 (Y.obj ⊗ X.obj)
      exact h2

end CategoryTheory
