module

public import QuantumSystem.Algebra.Sector.Category.CStarTensorCategory
public import QuantumSystem.Algebra.Sector.Category.CStarLinearCategory
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Abstract symmetric tensor ∗-categories (STC∗) — R7-A

This file defines the abstract target hypothesis of the Doplicher–Roberts
reconstruction (Müger, *Abstract Duality Theory for Symmetric Tensor
∗-Categories*, Theorem 2.18): a **symmetric tensor ∗-category** `STCStar`.

Following Müger Definitions 1.33 (`TC∗`) and 1.46 (C\*-tensor category), an
`STCStar` is an abstract category that is simultaneously:

* `ℂ`-linear (`Preadditive` + `Linear ℂ`) with a C\*-enrichment (`CStarCategory`:
  Banach hom-spaces with the C\*-identity `‖f† ≫ f‖ = ‖f‖²`);
* symmetric, rigid and dagger-monoidal with unitary symmetry
  (`RigidSymmetricDaggerCategory`);
* closed under binary direct sums (`HasBinaryBiproducts`) and subobjects
  (`IsIdempotentComplete`, i.e. every projector splits);
* with **irreducible unit** `End 𝟙 = ℂ · id` (Müger Definition 1.32).

The reconstruction theorem (R7-D/E/F) is to be stated for an abstract `[STCStar C]`;
the DHR sector category (`dhrRigidSymmetricDagger`) is then *one instance*, exactly
as Mathlib's finite Tannaka duality is stated for the abstract `FDRep k G`.

This is **R7-A** of the staged plan in `implementation-notes.md` (§4 R7): the
abstract class on which the standard-solution / dimension / twist / commutative
algebra layer (R7-B) and the fiber-functor reconstruction (R7-C–F) are built. No
specialisation to a concrete realisation, even/finite case, or hypothesised fiber
functor is taken (AGENTS "Abstraction first").
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory Limits

universe v u

/-- A **symmetric tensor ∗-category** (Müger Def 1.33 + 1.46): an abstract
`ℂ`-linear dagger C\*-tensor category that is symmetric and rigid (with unitary
symmetry), closed under binary direct sums and subobjects, and whose monoidal unit
is irreducible (`End 𝟙 = ℂ`).  This is the abstract hypothesis of the
Doplicher–Roberts reconstruction (Müger Theorem 2.18).

The C\*-analytic enrichment is supplied through `[CStarLinearCategory C]`
(R7-0a, `CStarLinearCategory.lean`): the hom-space norm is carried as data and the
`NormedAddCommGroup`/`NormedSpace`/`CStarCategory` instances are *derived* on top of
the categorical `Preadditive`/`Linear ℂ` structure, so the categorical and analytic
scalar actions coincide definitionally.  This is what makes scalar uniqueness
(`CStarCategory.smul_id_inj`, fed by `CStarLinearCategory.norm_unit_id_ne_zero`)
usable on the scalars produced by `irreducible_unit`. -/
class STCStar (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    [RigidSymmetricDaggerCategory C] [CStarLinearCategory C]
    [∀ X Y : C, CompleteSpace (X ⟶ Y)]
    [HasBinaryBiproducts C] [IsIdempotentComplete C] : Prop where
  /-- The monoidal unit is **irreducible**: every endomorphism of `𝟙` is a scalar
  multiple of the identity, i.e. `End 𝟙 = ℂ · id` (Müger Definition 1.32). -/
  irreducible_unit : ∀ f : 𝟙_ C ⟶ 𝟙_ C, ∃ c : ℂ, f = c • 𝟙 (𝟙_ C)

end CategoryTheory
