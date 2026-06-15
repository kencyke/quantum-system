module

public import QuantumSystem.Algebra.Sector.Category.Tannaka.Semisimple
public import QuantumSystem.Algebra.Sector.Category.Tannaka.StandardSolution

/-!
# Existence of standard solutions — S7 (Müger Lemma 1.37)

Müger, *Abstract Duality Theory for Symmetric Tensor ∗-Categories*, Lemma 1.37:
in a semisimple tensor ∗-category every object admits a **standard solution** of
the conjugate equations (`StandardSolution`, Müger Definition 1.36).  The proof
glues two ingredients:

* **base case** — for a *simple* object a conjugate solution is standard as soon as
  its two dimensions agree (`r ≫ r† = r̄ ≫ r̄†`), because the standardness condition
  `r ≫ (X̄ ◁ s) ≫ r† = r̄ ≫ (s ▷ X̄) ≫ r̄†` need only be checked on `End X = ℂ · 𝟙`
  (every `s` is a scalar), where it collapses to that single equation;
* **gluing** — standard solutions are closed under the orthogonal direct sums of a
  semisimple decomposition (`SimpleDecomposition`).

The base-case reduction (`standard_of_simple`) is proved here in full; it is the
genuinely C\*-categorical content of the base case (simplicity + `ℂ`-linearity of
whiskering).  The existence statement of Lemma 1.37 itself — which additionally
requires the direct-sum gluing over a semisimple decomposition — is carried as the
hypothesis class `HasStandardSolutions`, in the same style as the other deferred
existence statements of this development (`IsSemisimple`, `HasCStarCompletion`).
This is **S7** of the Tannaka roadmap (`implementation-notes.md` §4); the dimension
additivity/multiplicativity (S8) is stated relative to `[HasStandardSolutions C]`.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory

universe v u

/-! ### The base case of Lemma 1.37 -/

section BaseCase

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C] [Linear ℂ C]
    [MonoidalPreadditive C] [MonoidalLinear ℂ C] [DaggerCategory C]

/-- **The base case of Lemma 1.37**: for a *simple* object `X`, a conjugate solution
`(r, r̄)` is standard as soon as its two dimensions agree.  The standardness condition
`r ≫ (X̄ ◁ s) ≫ r† = r̄ ≫ (s ▷ X̄) ≫ r̄†` is `ℂ`-linear in `s`, and on a simple object
every `s ∈ End X` is a scalar multiple of `𝟙 X`, so the condition for all `s` follows
from the single equation `r ≫ r† = r̄ ≫ r̄†` (the `s = 𝟙 X` instance). -/
lemma standard_of_simple {X conj : C} (hX : IsSimpleObject X)
    (r : 𝟙_ C ⟶ conj ⊗ X) (rbar : 𝟙_ C ⟶ X ⊗ conj)
    (hdim : r ≫ r† = rbar ≫ rbar†) (s : X ⟶ X) :
    r ≫ (conj ◁ s) ≫ r† = rbar ≫ (s ▷ conj) ≫ rbar† := by
  obtain ⟨c, rfl⟩ := hX s
  simp only [MonoidalLinear.whiskerLeft_smul, MonoidalLinear.smul_whiskerRight,
    MonoidalCategory.whiskerLeft_id, MonoidalCategory.id_whiskerRight,
    Linear.smul_comp, Linear.comp_smul, Category.id_comp]
  rw [hdim]

end BaseCase

/-! ### The existence statement -/

/-- The category **has standard solutions** (Müger Lemma 1.37): every object admits a
standard solution of the conjugate equations.  In a semisimple C\*-tensor category
this follows from the base case `standard_of_simple` glued over a semisimple
decomposition (`SimpleDecomposition`); the gluing over the orthogonal direct sums is
the deferred constructive content, so the existence is carried as a hypothesis class
here (as with `IsSemisimple`).  The dimension theory of S8 consumes
`[HasStandardSolutions C]`. -/
class HasStandardSolutions (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [DaggerCategory C] : Prop where
  /-- Every object admits a standard solution. -/
  nonempty_standardSolution : ∀ X : C, Nonempty (StandardSolution X)

/-- A chosen standard solution of an object. -/
noncomputable def standardSolution {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [DaggerCategory C] [HasStandardSolutions C] (X : C) : StandardSolution X :=
  (HasStandardSolutions.nonempty_standardSolution X).some

end CategoryTheory
