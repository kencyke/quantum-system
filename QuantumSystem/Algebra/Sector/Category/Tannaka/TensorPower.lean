module

public import QuantumSystem.Algebra.Sector.Category.Tannaka.STCStar
public import QuantumSystem.Algebra.Sector.Category.Tannaka.FiberAlgebra

/-!
# Tensor powers and (anti)symmetrizers — S9 (R7-B4)

Müger, *Abstract Duality Theory for Symmetric Tensor ∗-Categories*, §1.7: the
tensor powers `X⊗ⁿ` of an object carry an action of the symmetric group `Sₙ`
through the symmetry (braiding), and the (anti)symmetrizing idempotents
`S_n = (1/n!) ∑_σ π(σ)`, `A_n = (1/n!) ∑_σ sgn(σ) π(σ)` are the projections whose
splittings (in an idempotent-complete category) give the symmetric/antisymmetric
powers — the determinant and the conjugate of Doplicher–Roberts.

This file fixes:

* the **tensor power** `tensorPow X n = X⊗ⁿ` (`tensorPow_zero`/`tensorPow_succ`);
* the **degree-2 (anti)symmetrizers** `symmetrizer X = ½(𝟙 + c)`,
  `antisymmetrizer X = ½(𝟙 - c)` for the self-braiding `c = β_{X,X}`, proved to be
  orthogonal **projections** summing to `𝟙` (`symmetrizer_idem`, `antisymmetrizer_idem`,
  `symmetrizer_dagger`, `antisymmetrizer_dagger`, `symmetrizer_add_antisymmetrizer`).

These rest only on the symmetry relation `c ≫ c = 𝟙` and the unitarity of the
symmetry (`c† = c`), so they are proved in full.  The action of `Sₙ` for general
`n` (whose well-definedness is the coherence of the symmetric braiding) and the
higher (anti)symmetrizers are the deferred combinatorial content of §1.7.  This is
**S9** of the Tannaka roadmap (`implementation-notes.md` §4).
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory Limits

universe v u

/-! ### Tensor powers -/

section TensorPow

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The **`n`-th tensor power** `X⊗ⁿ` of an object (Müger §1.7), defined recursively
with `X⊗⁰ = 𝟙` and `X⊗ⁿ⁺¹ = X ⊗ X⊗ⁿ`. -/
def tensorPow (X : C) : ℕ → C
  | 0 => 𝟙_ C
  | (n + 1) => X ⊗ tensorPow X n

@[simp] lemma tensorPow_zero (X : C) : tensorPow X 0 = 𝟙_ C := rfl

@[simp] lemma tensorPow_succ (X : C) (n : ℕ) : tensorPow X (n + 1) = X ⊗ tensorPow X n := rfl

end TensorPow

/-! ### Conjugate-linearity of the dagger on differences -/

section DaggerSub

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [DaggerCategory C]
    [DaggerLinear C]

/-- The conjugate-linear dagger is **subtractive**: `(f - g)† = f† - g†` (derived from
`DaggerLinear.dagger_add` and `dagger_smul` via `-g = (-1) • g`). -/
lemma DaggerLinear.dagger_sub {X Y : C} (f g : X ⟶ Y) :
    (f - g)† = f† - g† := by
  have hneg : (-g)† = -(g†) := by
    rw [show (-g : X ⟶ Y) = (-1 : ℂ) • g from by rw [neg_smul, one_smul],
      DaggerLinear.dagger_smul, star_neg, star_one, neg_smul, one_smul]
  rw [sub_eq_add_neg, DaggerLinear.dagger_add, hneg, ← sub_eq_add_neg]

end DaggerSub

/-! ### The self-braiding of an object -/

section Symmetrizer

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [RigidSymmetricDaggerCategory C]

variable (X : C)

/-- The **self-braiding** `c = β_{X,X} : X ⊗ X ⟶ X ⊗ X` is an **involution**:
`c ≫ c = 𝟙` (the symmetry relation `β_{X,Y} ≫ β_{Y,X} = 𝟙` at `Y = X`). -/
@[simp] lemma braiding_self_comp : (β_ X X).hom ≫ (β_ X X).hom = 𝟙 (X ⊗ X) :=
  SymmetricCategory.symmetry X X

/-- The self-braiding is **self-adjoint**, `c† = c`: it is unitary (`symmetry_unitary`,
`c ≫ c† = 𝟙`) and an involution (`braiding_self_comp`, `c ≫ c = 𝟙`), so its dagger and
its inverse both equal `c`. -/
lemma braiding_self_dagger : ((β_ X X).hom)† = (β_ X X).hom := by
  have hsq : (β_ X X).hom ≫ (β_ X X).hom = 𝟙 (X ⊗ X) := braiding_self_comp X
  have huni : (β_ X X).hom ≫ ((β_ X X).hom)† = 𝟙 (X ⊗ X) :=
    (RigidSymmetricDaggerCategory.symmetry_unitary X X).1
  calc ((β_ X X).hom)† = 𝟙 (X ⊗ X) ≫ ((β_ X X).hom)† := (Category.id_comp _).symm
    _ = ((β_ X X).hom ≫ (β_ X X).hom) ≫ ((β_ X X).hom)† := by rw [hsq]
    _ = (β_ X X).hom ≫ ((β_ X X).hom ≫ ((β_ X X).hom)†) := by rw [Category.assoc]
    _ = (β_ X X).hom ≫ 𝟙 (X ⊗ X) := by rw [huni]
    _ = (β_ X X).hom := Category.comp_id _

end Symmetrizer

/-! ### The degree-2 (anti)symmetrizers -/

section Symmetrizer2

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C] [Linear ℂ C]
    [RigidSymmetricDaggerCategory C]

variable (X : C)

/-- The **symmetrizer** `S₂ = ½(𝟙 + c)` for the self-braiding `c = β_{X,X}` (Müger §1.7):
the projection onto the symmetric part of `X ⊗ X`. -/
noncomputable def symmetrizer : X ⊗ X ⟶ X ⊗ X := (2⁻¹ : ℂ) • (𝟙 (X ⊗ X) + (β_ X X).hom)

/-- The **antisymmetrizer** `A₂ = ½(𝟙 - c)` for the self-braiding `c = β_{X,X}` (Müger §1.7):
the projection onto the antisymmetric part of `X ⊗ X`, whose splitting carries the
conjugate in the Doplicher–Roberts construction (cf. `reflectionProjection`). -/
noncomputable def antisymmetrizer : X ⊗ X ⟶ X ⊗ X := (2⁻¹ : ℂ) • (𝟙 (X ⊗ X) - (β_ X X).hom)

/-- The symmetrizer is **idempotent**: `S₂ ≫ S₂ = S₂`, using `c ≫ c = 𝟙`. -/
lemma symmetrizer_idem : symmetrizer X ≫ symmetrizer X = symmetrizer X := by
  rw [symmetrizer, Linear.smul_comp, Linear.comp_smul]
  simp only [Preadditive.add_comp, Preadditive.comp_add, Category.id_comp, Category.comp_id,
    braiding_self_comp]
  module

/-- The antisymmetrizer is **idempotent**: `A₂ ≫ A₂ = A₂`, using `c ≫ c = 𝟙`. -/
lemma antisymmetrizer_idem : antisymmetrizer X ≫ antisymmetrizer X = antisymmetrizer X := by
  rw [antisymmetrizer, Linear.smul_comp, Linear.comp_smul]
  simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp, Category.comp_id,
    braiding_self_comp]
  module

/-- The symmetrizer is **self-adjoint**, `S₂† = S₂`: the dagger is conjugate-linear
(`DaggerLinear`), `𝟙† = 𝟙`, `c† = c` (`braiding_self_dagger`), and `½` is real. -/
lemma symmetrizer_dagger [DaggerLinear C] : (symmetrizer X)† = symmetrizer X := by
  rw [symmetrizer, DaggerLinear.dagger_smul, DaggerLinear.dagger_add,
    DaggerCategory.dagger_id, braiding_self_dagger,
    show star (2⁻¹ : ℂ) = 2⁻¹ from by norm_num]

/-- The antisymmetrizer is **self-adjoint**, `A₂† = A₂`. -/
lemma antisymmetrizer_dagger [DaggerLinear C] : (antisymmetrizer X)† = antisymmetrizer X := by
  rw [antisymmetrizer, DaggerLinear.dagger_smul, DaggerLinear.dagger_sub,
    DaggerCategory.dagger_id, braiding_self_dagger,
    show star (2⁻¹ : ℂ) = 2⁻¹ from by norm_num]

/-- The symmetrizer is a **positive** endomorphism (a self-adjoint idempotent). -/
lemma symmetrizer_isPositive [DaggerLinear C] : IsPositiveEndo (symmetrizer X) :=
  IsPositiveEndo.of_projection (symmetrizer_idem X) (symmetrizer_dagger X)

/-- The antisymmetrizer is a **positive** endomorphism (a self-adjoint idempotent). -/
lemma antisymmetrizer_isPositive [DaggerLinear C] : IsPositiveEndo (antisymmetrizer X) :=
  IsPositiveEndo.of_projection (antisymmetrizer_idem X) (antisymmetrizer_dagger X)

/-- The (anti)symmetrizers give an **orthogonal decomposition of the identity**:
`S₂ + A₂ = 𝟙` (so `X ⊗ X` splits as symmetric ⊕ antisymmetric parts). -/
lemma symmetrizer_add_antisymmetrizer : symmetrizer X + antisymmetrizer X = 𝟙 (X ⊗ X) := by
  rw [symmetrizer, antisymmetrizer]
  module

/-- The (anti)symmetrizers are **orthogonal**: `S₂ ≫ A₂ = 0`, using `c ≫ c = 𝟙`. -/
lemma symmetrizer_comp_antisymmetrizer : symmetrizer X ≫ antisymmetrizer X = 0 := by
  rw [symmetrizer, antisymmetrizer, Linear.smul_comp, Linear.comp_smul]
  simp only [Preadditive.add_comp, Preadditive.comp_sub, Category.id_comp, Category.comp_id,
    braiding_self_comp]
  module

end Symmetrizer2

end CategoryTheory
