module

public import Mathlib.Algebra.Order.Star.Basic
public import QuantumSystem.Algebra.Sector.Category.CStarCategory
public import QuantumSystem.Algebra.Sector.Category.Conjugate
public import QuantumSystem.Algebra.Sector.Category.Subobject

/-!
# Positivity of `f† ≫ f` in `End(A)`

This file supplies the remaining C\*-analytic fact of Müger, *Abstract Duality
Theory for Symmetric Tensor ∗-Categories*, §1.4 (Additive, ℂ-linear and
\*-categories): in a C\*-category every morphism `f` has

```
f ≫ f† ≥ 0      (equivalently  f† ≫ f ≥ 0),
```

i.e. `f ≫ f†` is a **positive element** of the endomorphism algebra `End`.

For `End(A)` (`Sector/Category/Endomorphism.lean`) the hom-space `ρ ⟶ σ` is a
subspace of the C\*-algebra `A`, composition with the dagger is `star f.t * f.t`,
and positivity is exactly the C\*-algebra fact `0 ≤ star a * a`
(`star_mul_self_nonneg`).  As elsewhere in Mathlib, the C\*-order on `A` is not a
global instance (to avoid order diamonds); it is taken here as the canonical
spectral order via the hypotheses `[PartialOrder A] [StarOrderedRing A]`
(supplied for any concrete C\*-algebra by `CStarAlgebra.spectralOrderedRing`).

This completes the C\*-analytic enrichment begun in `CStarCategory.lean`
(`norm_comp_dagger`), which is deliberately kept order-free so that its many
downstream importers need not carry the order instances.
-/

@[expose] public section

namespace CategoryTheory

namespace StarEndo

universe u

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {ρ σ : StarEndoCat A}

/-- **Positivity of `f ≫ f†`** (Müger §1.4).  The underlying element
`(f ≫ f†).t = star f.t * f.t` is a positive element of the C\*-algebra `A`. -/
lemma comp_dagger_nonneg (f : ρ ⟶ σ) : 0 ≤ (f ≫ f†).t := by
  rw [comp_t, dagger_t]
  exact star_mul_self_nonneg f.t

/-- **Positivity of `f† ≫ f`**.  The underlying element `(f† ≫ f).t = f.t * star f.t`
is a positive element of the C\*-algebra `A`. -/
lemma dagger_comp_nonneg (f : ρ ⟶ σ) : 0 ≤ (f† ≫ f).t := by
  rw [comp_t, dagger_t]
  exact mul_star_self_nonneg f.t

/-- A **positive endomorphism** in the categorical sense (`IsPositiveEndo p`, i.e.
`p = f ≫ f†` for some `f`) has a positive underlying C\*-algebra element, `0 ≤ p.t`.
This is the bridge from the abstract categorical positivity predicate (Müger Def 1.28)
to the spectral C\*-order on `A`; applied to `Conjugate.dim` it yields the
non-negativity of the categorical dimension (R7-B). -/
lemma _root_.CategoryTheory.IsPositiveEndo.t_nonneg {ρ : StarEndoCat A} {p : ρ ⟶ ρ}
    (hp : IsPositiveEndo p) : 0 ≤ p.t := by
  obtain ⟨σ, f, rfl⟩ := hp
  exact comp_dagger_nonneg f

/-- The (left) **dimension** of a conjugate is a non-negative element of the C\*-algebra,
`0 ≤ d(X).t` (Müger §1.4, R7-B "dim non-negativity"): the categorical dimension
`d(X) = R ≫ R†` is positive (`Conjugate.dim_isPositive`), hence C\*-nonnegative via
`IsPositiveEndo.t_nonneg`. -/
lemma Conjugate.dim_t_nonneg {X : StarEndoCat A} (c : Conjugate X) : 0 ≤ c.dim.t :=
  c.dim_isPositive.t_nonneg

/-- The right **dimension** of a conjugate is likewise non-negative, `0 ≤ d̄(X).t`. -/
lemma Conjugate.dim'_t_nonneg {X : StarEndoCat A} (c : Conjugate X) : 0 ≤ c.dim'.t :=
  c.dim'_isPositive.t_nonneg

/-- The antisymmetric **reflection projection** `½(𝟙 - s)` of a self-adjoint involution
`s` is a non-negative element of the C\*-algebra, `0 ≤ (reflectionProjection s).t`: it is
a projection (`reflectionProjection_isPositive`), hence C\*-nonnegative via
`IsPositiveEndo.t_nonneg`.  This connects the antisymmetric subobject (R3) to the
C\*-order (R7-B). -/
lemma reflectionProjection_t_nonneg {X : StarEndoCat A} {s : X ⟶ X} (hsa : s† = s)
    (hinv : s ≫ s = 𝟙 X) : 0 ≤ (reflectionProjection s).t :=
  (reflectionProjection_isPositive hsa hinv).t_nonneg

end StarEndo

end CategoryTheory
