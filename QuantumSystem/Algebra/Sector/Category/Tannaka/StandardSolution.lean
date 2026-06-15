module

public import Mathlib.CategoryTheory.Monoidal.Category
public import QuantumSystem.Algebra.Sector.Category.Dagger

/-!
# Standard solutions of the conjugate equations — R7-B (standard solution)

In a tensor ∗-category, a **conjugate** of an object `X` (Müger, *Abstract Duality
Theory for Symmetric Tensor ∗-Categories*, Definition 1.31) is an object `X̄` with
morphisms `r : 𝟙 ⟶ X̄ ⊗ X`, `r̄ : 𝟙 ⟶ X ⊗ X̄` satisfying the conjugate (zig-zag)
equations

```
(r̄* ⊗ id_X) ∘ (id_X ⊗ r) = id_X,    (r* ⊗ id_X̄) ∘ (id_X̄ ⊗ r̄) = id_X̄.
```

The solution is **standard** (Müger Definition 1.36) when, for every `s ∈ End X`,

```
r* ∘ (id_X̄ ⊗ s) ∘ r = r̄* ∘ (s ⊗ id_X̄) ∘ r̄.
```

Standard solutions are the data underlying the trace, dimension and twist (Müger
Proposition 1.40, Definitions 1.41/1.43) used throughout the Tannaka reconstruction.
Their *existence* for every object (Müger Lemma 1.37, via semisimplicity) is the
substantive content deferred to the rest of R7-B; this file fixes the **structure**.

This is **R7-B** (the standard-solution carrier) of the staged plan in
`implementation-notes.md` (§4 R7).
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [DaggerCategory C]

/-- A **standard solution of the conjugate equations** for `X` (Müger Definitions
1.31 + 1.36): a conjugate object `conj` (`X̄`) with coevaluation-type morphisms
`r : 𝟙 ⟶ conj ⊗ X`, `rbar : 𝟙 ⟶ X ⊗ conj` satisfying the two conjugate (zig-zag)
equations and the standardness condition.  `r*`/`rbar*` denote the daggers. -/
structure StandardSolution (X : C) where
  /-- The conjugate object `X̄`. -/
  conj : C
  /-- The solution `r : 𝟙 ⟶ X̄ ⊗ X`. -/
  r : 𝟙_ C ⟶ conj ⊗ X
  /-- The solution `r̄ : 𝟙 ⟶ X ⊗ X̄`. -/
  rbar : 𝟙_ C ⟶ X ⊗ conj
  /-- First conjugate equation `(r̄* ⊗ id_X) ∘ (id_X ⊗ r) = id_X`. -/
  conj_eq₁ : (ρ_ X).inv ≫ (X ◁ r) ≫ (α_ X conj X).inv ≫
    (DaggerCategory.dagger rbar ▷ X) ≫ (λ_ X).hom = 𝟙 X
  /-- Second conjugate equation `(r* ⊗ id_X̄) ∘ (id_X̄ ⊗ r̄) = id_X̄`. -/
  conj_eq₂ : (ρ_ conj).inv ≫ (conj ◁ rbar) ≫ (α_ conj X conj).inv ≫
    (DaggerCategory.dagger r ▷ conj) ≫ (λ_ conj).hom = 𝟙 conj
  /-- Standardness (Müger Definition 1.36): `r* ∘ (id_X̄ ⊗ s) ∘ r = r̄* ∘ (s ⊗ id_X̄) ∘ r̄`
  for every `s ∈ End X`. -/
  standard : ∀ s : X ⟶ X,
    r ≫ (conj ◁ s) ≫ DaggerCategory.dagger r = rbar ≫ (s ▷ conj) ≫ DaggerCategory.dagger rbar

namespace StandardSolution

variable {X : C}

/-- The **dimension** of a standard solution (Müger Definition 1.41): `d(X) = r* ∘ r`,
an endomorphism of the unit (a non-negative real once `End 𝟙 = ℂ` and positivity are
available — Lemma 1.42, deferred). -/
noncomputable def dim (s : StandardSolution X) : 𝟙_ C ⟶ 𝟙_ C :=
  s.r ≫ DaggerCategory.dagger s.r

/-- The **conjugate dimension** of a standard solution, `d̄(X) = r̄* ∘ r̄`. -/
noncomputable def dim' (s : StandardSolution X) : 𝟙_ C ⟶ 𝟙_ C :=
  s.rbar ≫ DaggerCategory.dagger s.rbar

/-- For a **standard** solution the two dimensions agree, `d(X) = d̄(X)` (part of
Müger Lemma 1.42): apply the standardness condition to `s = id_X`, where the
whiskered identities collapse. -/
lemma dim_eq_dim' (s : StandardSolution X) : s.dim = s.dim' := by
  have h := s.standard (𝟙 X)
  simpa only [dim, dim', MonoidalCategory.whiskerLeft_id, MonoidalCategory.id_whiskerRight,
    Category.id_comp] using h

/-- The dimension `d(X) = r* ∘ r` is **self-adjoint** (a step toward its positivity,
Müger Lemma 1.42): the dagger of `r ≫ r*` is itself, by contravariance of `†`. -/
lemma dim_dagger (s : StandardSolution X) : DaggerCategory.dagger s.dim = s.dim := by
  simp only [dim, DaggerCategory.dagger_comp, DaggerCategory.dagger_dagger]

/-- The conjugate dimension `d̄(X) = r̄* ∘ r̄` is likewise **self-adjoint**; together
with `dim_eq_dim'` this gives the self-adjointness of the common dimension. -/
lemma dim'_dagger (s : StandardSolution X) : DaggerCategory.dagger s.dim' = s.dim' := by
  simp only [dim', DaggerCategory.dagger_comp, DaggerCategory.dagger_dagger]

/-- The dimension `d(X) = r* ∘ r = r ≫ r†` is a **positive** element of `End 𝟙`
(Müger Lemma 1.42, positivity half): it factors through `r : 𝟙 ⟶ X̄ ⊗ X`.  Together
with `End 𝟙 = ℂ` (`STCStar.irreducible_unit`) and C\*-positivity this is what makes
`d(X)` a non-negative real `0 ≤ d(X)`. -/
lemma dim_isPositive (s : StandardSolution X) : IsPositiveEndo s.dim :=
  ⟨s.conj ⊗ X, s.r, rfl⟩

/-- The conjugate dimension `d̄(X) = r̄ ≫ r̄†` is likewise a **positive** element of
`End 𝟙`, factoring through `r̄ : 𝟙 ⟶ X ⊗ X̄`. -/
lemma dim'_isPositive (s : StandardSolution X) : IsPositiveEndo s.dim' :=
  ⟨X ⊗ s.conj, s.rbar, rfl⟩

end StandardSolution

end CategoryTheory
