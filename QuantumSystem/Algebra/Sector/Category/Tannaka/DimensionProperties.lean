module

public import QuantumSystem.Algebra.Sector.Category.Tannaka.STCStarDim
public import QuantumSystem.Algebra.Sector.Category.Tannaka.StandardSolution
public import QuantumSystem.Algebra.Sector.Category.Tannaka.FiberAlgebra

/-!
# Dimension properties — S8 (Müger Lemma 1.42)

Müger, *Abstract Duality Theory for Symmetric Tensor ∗-Categories*, Lemma 1.42:
in a symmetric tensor ∗-category with conjugates, the scalar dimension is a
**non-negative real**, satisfies `d(X) = d(X̄) ≥ 1` for every nonzero object, and is
**additive** over direct sums and **multiplicative** over tensor products.

This file proves the parts that follow directly from a standard solution and the
C\*-linear enrichment:

* the dimension of a standard solution is a **scalar** `scalarDim ∈ ℂ` (via `End 𝟙 = ℂ`);
* it is **real** (`scalarDim_isReal`), because `d(X) = r ≫ r†` is self-adjoint and the
  dagger is conjugate-linear (`DaggerLinear`);
* the two dimensions of a standard solution **agree**, `d(X) = d̄(X)`
  (`scalarDim_eq_scalarDim'`), the scalar form of `StandardSolution.dim_eq_dim'`.

The remaining numerical content of Lemma 1.42 — additivity over biproducts,
multiplicativity over `⊗`, and the lower bound `d(X) ≥ 1` — requires comparing the
standard solutions of *different* objects (their direct-sum/tensor gluing and the
spherical inequality), which is the deferred content of Müger §1.4–1.7.  It is
recorded as the hypothesis interface `HasStandardDimension`, in the same style as the
other deferred statements of this development.  This is **S8** of the Tannaka roadmap
(`implementation-notes.md` §4); the determinant/integrality of S10 consumes it.
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

/-! ### The scalar dimension of a standard solution -/

open Classical in
/-- The **scalar dimension** of a standard solution (Müger Definition 1.41): since
`d(X) = r ≫ r† ∈ End 𝟙 = ℂ` (`STCStar.irreducible_unit`), it is a scalar multiple of
`𝟙`; `scalarDim` is that scalar. -/
noncomputable def StandardSolution.scalarDim {X : C} (s : StandardSolution X) : ℂ :=
  (STCStar.irreducible_unit s.dim).choose

open Classical in
/-- The conjugate scalar dimension `d̄(X)` of a standard solution. -/
noncomputable def StandardSolution.scalarDim' {X : C} (s : StandardSolution X) : ℂ :=
  (STCStar.irreducible_unit s.dim').choose

open Classical in
/-- The defining relation `d(X) = scalarDim • 𝟙`. -/
lemma StandardSolution.dim_eq_scalarDim_smul {X : C} (s : StandardSolution X) :
    s.dim = s.scalarDim • 𝟙 (𝟙_ C) :=
  (STCStar.irreducible_unit s.dim).choose_spec

open Classical in
/-- The defining relation `d̄(X) = scalarDim' • 𝟙`. -/
lemma StandardSolution.dim'_eq_scalarDim'_smul {X : C} (s : StandardSolution X) :
    s.dim' = s.scalarDim' • 𝟙 (𝟙_ C) :=
  (STCStar.irreducible_unit s.dim').choose_spec

/-- **Value determination** of the scalar dimension: `scalarDim` is the unique `c` with
`d(X) = c • 𝟙` (scalar uniqueness via `CStarLinearCategory.norm_unit_id_ne_zero`). -/
lemma StandardSolution.scalarDim_eq_of {X : C} (s : StandardSolution X) {c : ℂ}
    (h : s.dim = c • 𝟙 (𝟙_ C)) : s.scalarDim = c := by
  have h1 : c • 𝟙 (𝟙_ C) = s.scalarDim • 𝟙 (𝟙_ C) :=
    h.symm.trans s.dim_eq_scalarDim_smul
  exact (CStarCategory.smul_id_inj (CStarLinearCategory.norm_unit_id_ne_zero (C := C)) h1).symm

/-- The two scalar dimensions of a standard solution **agree**, `d(X) = d̄(X)` (Müger
Lemma 1.42), the scalar form of `StandardSolution.dim_eq_dim'`. -/
lemma StandardSolution.scalarDim_eq_scalarDim' {X : C} (s : StandardSolution X) :
    s.scalarDim = s.scalarDim' := by
  apply s.scalarDim_eq_of
  rw [s.dim_eq_dim', s.dim'_eq_scalarDim'_smul]

/-- The scalar dimension is **real** (Müger Lemma 1.42): `d(X) = r ≫ r†` is self-adjoint
(`StandardSolution.dim_dagger`), and the dagger is conjugate-linear (`DaggerLinear`), so
`star (scalarDim) • 𝟙 = scalarDim • 𝟙`, whence `star (scalarDim) = scalarDim`. -/
lemma StandardSolution.scalarDim_isReal [DaggerLinear C] {X : C} (s : StandardSolution X) :
    star s.scalarDim = s.scalarDim := by
  have h1 : (s.dim)† = s.dim := s.dim_dagger
  rw [s.dim_eq_scalarDim_smul, DaggerLinear.dagger_smul, DaggerCategory.dagger_id] at h1
  exact CStarCategory.smul_id_inj (CStarLinearCategory.norm_unit_id_ne_zero (C := C)) h1

/-! ### The numerical content of Lemma 1.42 -/

/-- The **standard-dimension properties** of Müger Lemma 1.42, as a hypothesis interface:
the scalar dimension `STCStar.dim` is real, bounded below by `1` on nonzero objects, and a
semiring homomorphism (additive over biproducts, multiplicative over `⊗`).  These follow
from comparing standard solutions of different objects (their direct-sum/tensor gluing and
the spherical inequality), the deferred constructive content of Müger §1.4–1.7; they are
carried as a class here (as with `IsSemisimple`/`HasStandardSolutions`).  The
determinant/integrality of S10 is stated relative to `[HasStandardDimension C]`. -/
class HasStandardDimension (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    [RigidSymmetricDaggerCategory C] [CStarLinearCategory C]
    [∀ X Y : C, CompleteSpace (X ⟶ Y)] [HasBinaryBiproducts C] [IsIdempotentComplete C]
    [STCStar C] : Prop where
  /-- The scalar dimension is real (`im = 0`). -/
  dim_im : ∀ X : C, (STCStar.dim X).im = 0
  /-- Every nonzero object has dimension `≥ 1` (the spherical lower bound). -/
  one_le_dim_re : ∀ X : C, ‖𝟙 X‖ ≠ 0 → 1 ≤ (STCStar.dim X).re
  /-- The dimension is **additive** over binary direct sums. -/
  dim_biprod : ∀ X Y : C, STCStar.dim (X ⊞ Y) = STCStar.dim X + STCStar.dim Y
  /-- The dimension is **multiplicative** over tensor products. -/
  dim_tensor : ∀ X Y : C, STCStar.dim (X ⊗ Y) = STCStar.dim X * STCStar.dim Y

/-- Under `HasStandardDimension`, the dimension of a nonzero object is a real `≥ 1`
(combining `dim_im` and `one_le_dim_re`): `STCStar.dim X = (STCStar.dim X).re` with
`(STCStar.dim X).re ≥ 1`. -/
lemma STCStar.dim_eq_re [HasStandardDimension C] (X : C) :
    STCStar.dim X = (STCStar.dim X).re := by
  apply Complex.ext <;> simp [HasStandardDimension.dim_im X]

end CategoryTheory
