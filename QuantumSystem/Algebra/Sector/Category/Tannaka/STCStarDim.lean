module

public import QuantumSystem.Algebra.Sector.Category.Tannaka.STCStar
public import QuantumSystem.Algebra.Sector.Category.Tannaka.Dimension

/-!
# The scalar dimension of an STC∗ object — R7-B1 (scalar)

In a symmetric tensor ∗-category with irreducible unit (`STCStar`, `End 𝟙 = ℂ`),
the categorical dimension `categoricalDim X : 𝟙 ⟶ 𝟙` (`Tannaka/Dimension.lean`,
Müger Definition 1.41) is a scalar multiple of the identity.  This file extracts
that scalar `dim X ∈ ℂ` and records the defining relation
`categoricalDim X = dim X • 𝟙`.

The numerical *properties* of `dim` (positivity, `dim X ≥ 1`, additivity,
multiplicativity, integrality — Müger Lemma 1.42, 2.45–2.53) remain the substantive
content of the rest of R7-B.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory Limits

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C] [Linear ℂ C]
    [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    [RigidSymmetricDaggerCategory C] [CStarLinearCategory C]
    [∀ X Y : C, CompleteSpace (X ⟶ Y)]
    [HasBinaryBiproducts C] [IsIdempotentComplete C] [STCStar C]

open Classical in
/-- The **scalar dimension** `dim X ∈ ℂ` of an object of an STC∗ (Müger Definition
1.41): since `End 𝟙 = ℂ` (`STCStar.irreducible_unit`), the categorical dimension
`categoricalDim X` is a scalar multiple of `𝟙`; `STCStar.dim X` is that scalar. -/
noncomputable def STCStar.dim (X : C) : ℂ :=
  (STCStar.irreducible_unit (categoricalDim X)).choose

open Classical in
/-- The defining relation of the scalar dimension: `categoricalDim X = (dim X) • 𝟙`. -/
lemma STCStar.categoricalDim_eq_dim_smul (X : C) :
    categoricalDim X = STCStar.dim X • 𝟙 (𝟙_ C) :=
  (STCStar.irreducible_unit (categoricalDim X)).choose_spec

open Classical in
/-- The **scalar trace** `tr f ∈ ℂ` of an endomorphism in an STC∗ (Müger §1.4): since
`End 𝟙 = ℂ` (`STCStar.irreducible_unit`), the categorical trace `categoricalTrace f` is a
scalar multiple of `𝟙`; `STCStar.trace f` is that scalar.  The pairing of natural
transformations with `A(E)` is built from these scalar traces (Müger Prop 2.27). -/
noncomputable def STCStar.trace {X : C} (f : X ⟶ X) : ℂ :=
  (STCStar.irreducible_unit (categoricalTrace f)).choose

open Classical in
/-- The defining relation of the scalar trace: `categoricalTrace f = (trace f) • 𝟙`. -/
lemma STCStar.categoricalTrace_eq_trace_smul {X : C} (f : X ⟶ X) :
    categoricalTrace f = STCStar.trace f • 𝟙 (𝟙_ C) :=
  (STCStar.irreducible_unit (categoricalTrace f)).choose_spec

/-- The scalar **trace of the identity is the scalar dimension** (Müger Definition 1.41):
`trace (𝟙_X) = dim X`.  Both are the scalar of the same morphism `categoricalDim X`. -/
@[simp] lemma STCStar.trace_id (X : C) : STCStar.trace (𝟙 X) = STCStar.dim X := by
  simp only [STCStar.trace, STCStar.dim, categoricalTrace_id]

/-- **Value determination of the scalar trace** (Müger §1.5): the scalar `trace f` is
the *unique* `c` with `categoricalTrace f = c • 𝟙`.  This is the well-definedness that
`End 𝟙 = ℂ` plus the nonzero unit identity (`CStarLinearCategory.unit_id_norm_ne_zero`)
provide: scalar uniqueness (`CStarCategory.smul_id_inj`) pins the value. -/
lemma STCStar.trace_eq_of {X : C} {f : X ⟶ X} {c : ℂ}
    (h : categoricalTrace f = c • 𝟙 (𝟙_ C)) : STCStar.trace f = c := by
  have h1 : c • 𝟙 (𝟙_ C) = STCStar.trace f • 𝟙 (𝟙_ C) :=
    h.symm.trans (STCStar.categoricalTrace_eq_trace_smul f)
  exact (CStarCategory.smul_id_inj (C := C) (CStarLinearCategory.norm_unit_id_ne_zero (C := C))
    h1).symm

/-- **Value determination of the scalar dimension** (Müger Definition 1.41 + §1.5):
`dim X` is the unique `c` with `categoricalDim X = c • 𝟙`. -/
lemma STCStar.dim_eq_of {X : C} {c : ℂ} (h : categoricalDim X = c • 𝟙 (𝟙_ C)) :
    STCStar.dim X = c := by
  have h1 : c • 𝟙 (𝟙_ C) = STCStar.dim X • 𝟙 (𝟙_ C) :=
    h.symm.trans (STCStar.categoricalDim_eq_dim_smul X)
  exact (CStarCategory.smul_id_inj (C := C) (CStarLinearCategory.norm_unit_id_ne_zero (C := C))
    h1).symm

/-- The scalar trace is **additive** (Müger §1.4): `trace (f + g) = trace f + trace g`,
from additivity of the categorical trace and value determination. -/
lemma STCStar.trace_add {X : C} (f g : X ⟶ X) :
    STCStar.trace (f + g) = STCStar.trace f + STCStar.trace g := by
  apply STCStar.trace_eq_of
  rw [categoricalTrace_add, STCStar.categoricalTrace_eq_trace_smul f,
    STCStar.categoricalTrace_eq_trace_smul g, add_smul]

/-- The scalar trace is **`ℂ`-homogeneous** (Müger §1.4): `trace (c • f) = c · trace f`,
from `ℂ`-linearity of the categorical trace and value determination. -/
lemma STCStar.trace_smul {X : C} (c : ℂ) (f : X ⟶ X) :
    STCStar.trace (c • f) = c * STCStar.trace f := by
  apply STCStar.trace_eq_of
  rw [categoricalTrace_smul, STCStar.categoricalTrace_eq_trace_smul f, smul_smul]

/-- The scalar **trace of `c • 𝟙_X` is `c · dim X`** (Müger §1.4): combine
`trace_smul` with `trace_id`. -/
@[simp] lemma STCStar.trace_smul_id (c : ℂ) (X : C) :
    STCStar.trace (c • 𝟙 X) = c * STCStar.dim X := by
  rw [STCStar.trace_smul, STCStar.trace_id]

/-- The scalar trace bundled as a **`ℂ`-linear functional** `End X →ₗ[ℂ] ℂ` (Müger §1.4).
The continuous dual of the fiber algebra `A(E)` is built from such trace functionals;
pairing a natural transformation with `[X, s]` uses `trace (s ≫ η_X)` (Müger Prop 2.27). -/
noncomputable def STCStar.traceₗ (X : C) : (X ⟶ X) →ₗ[ℂ] ℂ where
  toFun := STCStar.trace
  map_add' := STCStar.trace_add
  map_smul' c f := STCStar.trace_smul c f

@[simp] lemma STCStar.traceₗ_apply {X : C} (f : X ⟶ X) :
    STCStar.traceₗ X f = STCStar.trace f := rfl

/-- The **scalar dimension of the unit object is one** (Müger Lemma 1.42): `dim 𝟙_C = 1`.
`STCStar.dim (𝟙_C)` extracts the scalar of `categoricalDim (𝟙_C)`, which uses the
rigid-category dual; by `categoricalDim_eq_of_hasRightDual` this equals the dimension
computed with the canonical self-dual, which is `𝟙` (`categoricalDim_unit`).  Value
determination (`dim_eq_of`) then pins the scalar to `1`. -/
@[simp] lemma STCStar.dim_unit : STCStar.dim (𝟙_ C) = 1 := by
  apply STCStar.dim_eq_of
  rw [one_smul, categoricalDim_eq_of_hasRightDual _ CategoryTheory.hasRightDualUnit,
    categoricalDim_unit]

/-- The scalar **trace of the identity on the unit is one** (Müger §1.4, normalisation
`dim 𝟙 = 1`): `trace (𝟙_{𝟙_C}) = 1`. -/
@[simp] lemma STCStar.trace_id_unit : STCStar.trace (𝟙 (𝟙_ C)) = 1 := by
  rw [STCStar.trace_id, STCStar.dim_unit]

end CategoryTheory
