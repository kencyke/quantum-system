module

public import QuantumSystem.Algebra.Sector.Category.CStarCategory

/-!
# C\*-linear categories — R7-0a (interface stabilisation)

This file introduces the abstract analytic interface on which the
Doplicher–Roberts / Tannaka reconstruction is built, resolving the
`Module ℂ (X ⟶ Y)` *instance diamond* that otherwise blocks scalar uniqueness
in a symmetric tensor ∗-category (`implementation-notes.md` §4 R7, barrier 1).

A `CStarCategory` (`CStarCategory.lean`) takes the Banach structure on each
hom-space as **independent** prerequisite instances `[∀ X Y, NormedAddCommGroup
(X ⟶ Y)]`, `[∀ X Y, NormedSpace ℂ (X ⟶ Y)]`.  Together with the categorical
`Preadditive`/`Linear ℂ` structure this produces *two* a priori unrelated
`AddCommGroup (X ⟶ Y)` instances (`Preadditive.homGroup` versus
`NormedAddCommGroup.toAddCommGroup`) and hence two `Module ℂ (X ⟶ Y)` instances.
The categorical `c • f` (from `Linear ℂ C`) and the analytic `c • f` (from
`NormedSpace ℂ (X ⟶ Y)`) then fail to be definitionally equal, so the C\*-norm
lemma `CStarCategory.smul_id_inj` cannot be used on the scalar multiples produced
by `irreducible_unit`, blocking `dim 𝟙 = 1` and the linearity of the categorical
trace/dimension.

The fix here is the only diamond-free design: a `CStarLinearCategory` **carries a
norm function** `homNorm` and the C\*-axioms, and *derives* the
`NormedAddCommGroup`/`NormedSpace`/`CStarCategory` instances **on top of the
existing** `Preadditive.homGroup` and `Linear.homModule`, via `NormedSpace.Core`
(which reuses the supplied `AddCommGroup`, `Module` and `Norm`).  Consequently the
derived `NormedSpace`'s scalar action *is* `Linear ℂ C`'s — by construction, no
diamond.  The class also records `unit_id_norm_ne_zero`, the analytic input that
upgrades `End 𝟙 = ℂ` to a genuine scalar isomorphism (Müger §1.5).
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory

universe v u

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [Preadditive C] [Linear ℂ C]
    [DaggerCategory C]

/-- A **C\*-linear category** (Müger §1.4, *Additive, ℂ-linear and ∗-categories*):
a `ℂ`-linear dagger category equipped with a hom-space norm `homNorm` making each
hom-space a complex Banach space with the C\*-identity, *and compatible with the
existing `Preadditive`/`Linear ℂ` structure by construction*.

Unlike `CStarCategory`, the norm is **carried as data** (`homNorm`) rather than
assumed through independent `NormedAddCommGroup`/`NormedSpace` instances; the latter
are then *derived* on top of `Preadditive.homGroup`/`Linear.homModule`
(`instNormedAddCommGroup`/`instNormedSpace`), so the categorical and analytic scalar
actions coincide definitionally.  This is the R7-0a interface that unblocks scalar
uniqueness (`smul_id_inj`), `dim 𝟙 = 1` and trace/dimension linearity. -/
class CStarLinearCategory : Type (max u v) where
  /-- The norm on each hom-space. -/
  homNorm : {X Y : C} → (X ⟶ Y) → ℝ
  /-- The norm is non-negative. -/
  norm_nonneg : ∀ {X Y : C} (f : X ⟶ Y), 0 ≤ homNorm f
  /-- The norm is `ℂ`-homogeneous for the `Linear ℂ C` scalar action. -/
  norm_smul : ∀ {X Y : C} (c : ℂ) (f : X ⟶ Y), homNorm (c • f) = ‖c‖ * homNorm f
  /-- The triangle inequality. -/
  norm_triangle : ∀ {X Y : C} (f g : X ⟶ Y), homNorm (f + g) ≤ homNorm f + homNorm g
  /-- The norm is definite: it vanishes only on the zero morphism. -/
  norm_eq_zero_iff : ∀ {X Y : C} (f : X ⟶ Y), homNorm f = 0 ↔ f = 0
  /-- The **C\*-identity** `‖f ≫ f†‖ = ‖f‖²`. -/
  norm_comp_dagger : ∀ {X Y : C} (f : X ⟶ Y), homNorm (f ≫ f†) = homNorm f ^ 2
  /-- The identity of the monoidal unit has **nonzero norm** (the unit is a nonzero
  object).  This is the analytic input that turns `End 𝟙 = ℂ` into a scalar
  isomorphism: scalar uniqueness `c • 𝟙 = c' • 𝟙 → c = c'` (Müger §1.5). -/
  unit_id_norm_ne_zero : homNorm (𝟙 (𝟙_ C)) ≠ 0

namespace CStarLinearCategory

variable {C} [CStarLinearCategory C]

/-- The hom-space norm of a `CStarLinearCategory`, as a `Norm` instance.  The derived
`NormedAddCommGroup`/`NormedSpace` reuse this norm, so `‖f‖ = homNorm f` definitionally. -/
instance (priority := 100) instNorm (X Y : C) : Norm (X ⟶ Y) where
  norm := homNorm

@[simp] lemma norm_eq_homNorm {X Y : C} (f : X ⟶ Y) : ‖f‖ = homNorm f := rfl

/-- The `NormedSpace.Core` bundling the four hom-space norm axioms.  It is stated on
the existing `Preadditive.homGroup`/`Linear.homModule`, so producing the
`NormedAddCommGroup`/`NormedSpace` from it cannot introduce a new additive or module
structure. -/
def normedSpaceCore (X Y : C) : NormedSpace.Core ℂ (X ⟶ Y) where
  norm_nonneg := CStarLinearCategory.norm_nonneg
  norm_smul := CStarLinearCategory.norm_smul
  norm_triangle := CStarLinearCategory.norm_triangle
  norm_eq_zero_iff := CStarLinearCategory.norm_eq_zero_iff

/-- The derived `NormedAddCommGroup (X ⟶ Y)`, built from the norm `homNorm` **on top of
the `Preadditive` additive structure** (`NormedAddCommGroup.ofCore` reuses the supplied
`AddCommGroup`).  Hence its `AddCommGroup` is `Preadditive.homGroup` — no diamond. -/
noncomputable instance (priority := 100) instNormedAddCommGroup (X Y : C) :
    NormedAddCommGroup (X ⟶ Y) :=
  NormedAddCommGroup.ofCore (normedSpaceCore X Y)

/-- The derived `NormedSpace ℂ (X ⟶ Y)`, built **directly on the `Linear ℂ C` module
structure**: its `toModule` field is `Linear.homModule` by construction, so the
categorical and analytic scalar action `c • f` are *syntactically* the same instance.
This is what kills the `Module ℂ (X ⟶ Y)` diamond — `CStarCategory.smul_id_inj` then
applies verbatim to the scalars produced by `irreducible_unit`. -/
noncomputable instance (priority := 100) instNormedSpace (X Y : C) :
    NormedSpace ℂ (X ⟶ Y) where
  norm_smul_le c f := le_of_eq (CStarLinearCategory.norm_smul c f)

/-- A `CStarLinearCategory` whose hom-spaces are complete is a `CStarCategory`: the
derived Banach structure satisfies the C\*-identity by the carried `norm_comp_dagger`. -/
instance (priority := 100) instCStarCategory [∀ X Y : C, CompleteSpace (X ⟶ Y)] :
    CStarCategory C where
  norm_comp_dagger f := CStarLinearCategory.norm_comp_dagger f

/-- The identity of the monoidal unit has nonzero norm, phrased with the categorical
norm `‖·‖`.  This is the hypothesis feeding `CStarCategory.smul_id_inj` to obtain
scalar uniqueness against `𝟙 (𝟙_ C)`. -/
lemma norm_unit_id_ne_zero : ‖𝟙 (𝟙_ C)‖ ≠ 0 :=
  CStarLinearCategory.unit_id_norm_ne_zero

end CStarLinearCategory

end CategoryTheory
