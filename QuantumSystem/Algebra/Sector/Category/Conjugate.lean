module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import QuantumSystem.Algebra.Sector.Category.Endomorphism

/-!
# Conjugates and rigidity for `End(A)`

In Müger, *Abstract Duality Theory for Symmetric Tensor ∗-Categories*, §1.4, an
object `X` of a tensor ∗-category has a **conjugate** `X̄` if there are morphisms

```
R  : 𝟙 ⟶ X̄ ⊗ X,      R̄ : 𝟙 ⟶ X ⊗ X̄
```

satisfying the **conjugate equations** (zig-zag / snake identities)

```
(R̄† ⊗ 1_X) ∘ (1_X ⊗ R) = 1_X,    (R† ⊗ 1_X̄) ∘ (1_X̄ ⊗ R̄) = 1_X̄.
```

In the strict monoidal category `StarEndoCat A` (associators and unitors are
`Iso.refl`, with underlying element `1`) the conjugate equations reduce to two
algebra identities on the underlying elements `R.t`, `R̄.t ∈ A`:

```
star R.t * X̄.endo R̄.t = 1,        X.endo (star R.t) * R̄.t = 1.
```

This is exactly the data of a Mathlib `ExactPairing X X̄` (coevaluation `R̄`,
evaluation `R†`), so a conjugate makes `X` have a right dual `X̄` (and `X̄` a left
dual `X`).  Assembling these over a full subcategory of conjugable objects gives
the `RigidCategory` structure (next step).
-/

@[expose] public section

namespace CategoryTheory

namespace StarEndo

open MonoidalCategory

universe u

variable {A : Type u} [CStarAlgebra A]

/-- A **conjugate** of `X` in `End(A)` (Müger §1.4): an object `bar` with
solutions `R : 𝟙 ⟶ bar ⊗ X`, `Rbar : 𝟙 ⟶ X ⊗ bar` of the conjugate equations,
stated in their strict-monoidal element form. -/
structure Conjugate (X : StarEndoCat A) where
  /-- The conjugate object `X̄`. -/
  bar : StarEndoCat A
  /-- The coevaluation-type solution `R : 𝟙 ⟶ X̄ ⊗ X`. -/
  R : 𝟙_ (StarEndoCat A) ⟶ bar ⊗ X
  /-- The coevaluation-type solution `R̄ : 𝟙 ⟶ X ⊗ X̄`. -/
  Rbar : 𝟙_ (StarEndoCat A) ⟶ X ⊗ bar
  /-- First conjugate equation: the `R̄`-snake (`ExactPairing X X̄`). -/
  eq1 : star R.t * bar.endo Rbar.t = 1
  /-- Second conjugate equation: the `R̄`-snake (`ExactPairing X X̄`). -/
  eq2 : X.endo (star R.t) * Rbar.t = 1
  /-- Third conjugate equation: the `R`-snake (`ExactPairing X̄ X`). -/
  eq3 : star Rbar.t * X.endo R.t = 1
  /-- Fourth conjugate equation: the `R`-snake (`ExactPairing X̄ X`). -/
  eq4 : bar.endo (star Rbar.t) * R.t = 1

variable {X : StarEndoCat A}

/-- A conjugate of `X` realises a Mathlib `ExactPairing X X̄`: the coevaluation is
`R̄`, the evaluation is `R†`, and the two triangle identities are the conjugate
equations (the strict associators/unitors contribute trivial factors). -/
@[reducible] noncomputable def Conjugate.exactPairing (c : Conjugate X) : ExactPairing X c.bar where
  coevaluation' := c.Rbar
  evaluation' := c.R†
  coevaluation_evaluation' := by
    apply Intertwiner.ext
    simp only [comp_t, whiskerLeft_t, whiskerRight_t, associator_inv_t, dagger_t,
      leftUnitor_inv_t, rightUnitor_hom_t, mul_one]
    exact c.eq1
  evaluation_coevaluation' := by
    apply Intertwiner.ext
    simp only [comp_t, whiskerLeft_t, whiskerRight_t, associator_hom_t, dagger_t,
      leftUnitor_hom_t, rightUnitor_inv_t, mul_one]
    exact c.eq2

/-- A conjugate makes `X` have a right dual `X̄`. -/
@[reducible] noncomputable def Conjugate.hasRightDual (c : Conjugate X) : HasRightDual X where
  rightDual := c.bar
  exact := c.exactPairing

/-- A conjugate makes `X̄` have a left dual `X`. -/
@[reducible] noncomputable def Conjugate.hasLeftDual (c : Conjugate X) : HasLeftDual c.bar where
  leftDual := X
  exact := c.exactPairing

/-- The *second* exact pairing of a conjugate, `ExactPairing X̄ X` (coevaluation
`R`, evaluation `R̄†`); its triangle identities are the `R`-snake equations
`eq3`, `eq4`.  This is the two-sidedness of the conjugate. -/
@[reducible] noncomputable def Conjugate.exactPairing' (c : Conjugate X) :
    ExactPairing c.bar X where
  coevaluation' := c.R
  evaluation' := c.Rbar†
  coevaluation_evaluation' := by
    apply Intertwiner.ext
    simp only [comp_t, whiskerLeft_t, whiskerRight_t, associator_inv_t, dagger_t,
      leftUnitor_inv_t, rightUnitor_hom_t, mul_one]
    exact c.eq3
  evaluation_coevaluation' := by
    apply Intertwiner.ext
    simp only [comp_t, whiskerLeft_t, whiskerRight_t, associator_hom_t, dagger_t,
      leftUnitor_hom_t, rightUnitor_inv_t, mul_one]
    exact c.eq4

/-- A conjugate makes `X` have a **left** dual `X̄` (via the second exact pairing),
so together with `Conjugate.hasRightDual`, `X` has a two-sided dual. -/
@[reducible] noncomputable def Conjugate.hasLeftDual_self (c : Conjugate X) : HasLeftDual X where
  leftDual := c.bar
  exact := c.exactPairing'

/-- A conjugate makes `X̄` have a **right** dual `X` (via the second exact pairing). -/
@[reducible] noncomputable def Conjugate.hasRightDual_bar (c : Conjugate X) :
    HasRightDual c.bar where
  rightDual := X
  exact := c.exactPairing'

/-- **Conjugation is symmetric.**  If `X̄` is a conjugate of `X` then `X` is a
conjugate of `X̄` (swap `R` and `R̄`); the four snake equations permute among
themselves.  Hence the class of objects with conjugates is closed under taking
conjugates — the closure needed for the rigid full subcategory. -/
def Conjugate.swap (c : Conjugate X) : Conjugate c.bar where
  bar := X
  R := c.Rbar
  Rbar := c.R
  eq1 := c.eq3
  eq2 := c.eq4
  eq3 := c.eq1
  eq4 := c.eq2

/-- The **(left) dimension** of a conjugate, `d(X) = R† ∘ R : 𝟙 ⟶ 𝟙`, a positive
endomorphism of the unit (Müger §1.4).  Its underlying element is
`R⋆ · R ∈ End 𝟙 = ℂ` (well-defined for standard solutions). -/
noncomputable def Conjugate.dim (c : Conjugate X) :
    𝟙_ (StarEndoCat A) ⟶ 𝟙_ (StarEndoCat A) :=
  c.R ≫ c.R†

@[simp] lemma Conjugate.dim_t (c : Conjugate X) : c.dim.t = star c.R.t * c.R.t := by
  simp only [Conjugate.dim, comp_t, dagger_t]

/-- The **right dimension** of a conjugate, `d̄(X) = R̄† ∘ R̄ : 𝟙 ⟶ 𝟙`. -/
noncomputable def Conjugate.dim' (c : Conjugate X) :
    𝟙_ (StarEndoCat A) ⟶ 𝟙_ (StarEndoCat A) :=
  c.Rbar ≫ c.Rbar†

@[simp] lemma Conjugate.dim'_t (c : Conjugate X) : c.dim'.t = star c.Rbar.t * c.Rbar.t := by
  simp only [Conjugate.dim', comp_t, dagger_t]

/-- The (left) dimension of a conjugate is a **positive** endomorphism of the unit:
`d(X) = R ≫ R†` factors as `f ≫ f†`.  This is the concrete (DHR-category) counterpart
of `StandardSolution.dim_isPositive` (R7-B). -/
lemma Conjugate.dim_isPositive (c : Conjugate X) : IsPositiveEndo c.dim :=
  ⟨c.bar ⊗ X, c.R, rfl⟩

/-- The right dimension of a conjugate is likewise a **positive** endomorphism,
`d̄(X) = R̄ ≫ R̄†`. -/
lemma Conjugate.dim'_isPositive (c : Conjugate X) : IsPositiveEndo c.dim' :=
  ⟨X ⊗ c.bar, c.Rbar, rfl⟩

/-- The dimension of a conjugate is **self-adjoint** (being positive). -/
lemma Conjugate.dim_dagger (c : Conjugate X) : c.dim† = c.dim :=
  c.dim_isPositive.isSelfAdjoint

/-- The right dimension of a conjugate is **self-adjoint** (being positive). -/
lemma Conjugate.dim'_dagger (c : Conjugate X) : c.dim'† = c.dim' :=
  c.dim'_isPositive.isSelfAdjoint

/-- The underlying element `d(X).t ∈ A` is **self-adjoint** (`IsSelfAdjoint`), bridging
the categorical `dim_dagger` to the C\*-algebra predicate and enabling spectral
arguments on the dimension. -/
lemma Conjugate.dim_t_isSelfAdjoint (c : Conjugate X) : IsSelfAdjoint c.dim.t := by
  change star c.dim.t = c.dim.t
  rw [← dagger_t, c.dim_dagger]

/-- The element `d̄(X).t ∈ A` is likewise self-adjoint. -/
lemma Conjugate.dim'_t_isSelfAdjoint (c : Conjugate X) : IsSelfAdjoint c.dim'.t := by
  change star c.dim'.t = c.dim'.t
  rw [← dagger_t, c.dim'_dagger]

/-- The (left) dimension **vanishes iff the coevaluation does**: `d(X).t = 0 ↔ R.t = 0`,
by the C\*-faithfulness of `a ↦ star a * a`.  In particular a conjugate with nonzero
coevaluation has strictly positive dimension. -/
lemma Conjugate.dim_t_eq_zero_iff (c : Conjugate X) : c.dim.t = 0 ↔ c.R.t = 0 := by
  rw [Conjugate.dim_t]
  exact CStarRing.star_mul_self_eq_zero_iff c.R.t

/-- The right dimension vanishes iff `R̄` does: `d̄(X).t = 0 ↔ R̄.t = 0`. -/
lemma Conjugate.dim'_t_eq_zero_iff (c : Conjugate X) : c.dim'.t = 0 ↔ c.Rbar.t = 0 := by
  rw [Conjugate.dim'_t]
  exact CStarRing.star_mul_self_eq_zero_iff c.Rbar.t

/-- Under conjugation symmetry the two dimensions **swap**: `d(X̄) = d̄(X)`, since
`Conjugate.swap` exchanges `R` and `R̄` (Müger §1.4, `d = d̄` for standard solutions). -/
@[simp] lemma Conjugate.swap_dim_t (c : Conjugate X) : c.swap.dim.t = c.dim'.t := rfl

/-- Dually, `d̄(X̄) = d(X)`. -/
@[simp] lemma Conjugate.swap_dim'_t (c : Conjugate X) : c.swap.dim'.t = c.dim.t := rfl

/-! ### Intertwining relations of the conjugate solutions

`R : 𝟙 ⟶ X̄ ⊗ X` being an intertwiner says `R.t · a = X̄.endo (X.endo a) · R.t`;
together with its starred form these are the algebraic content used to prove the
conjugate-of-a-tensor equations. -/

/-- `R`-intertwining: `X̄.endo (X.endo a) · R.t = R.t · a`. -/
lemma Conjugate.R_intertwine (c : Conjugate X) (a : A) :
    c.bar.endo (X.endo a) * c.R.t = c.R.t * a := by
  have h := c.R.intertwines a
  simpa using h.symm

/-- Starred `R`-intertwining: `R⋆ · X̄.endo (X.endo b) = b · R⋆`. -/
lemma Conjugate.R_intertwine_star (c : Conjugate X) (b : A) :
    star c.R.t * c.bar.endo (X.endo b) = b * star c.R.t := by
  have h := congrArg star (c.R_intertwine (star b))
  simp only [star_mul, ← map_star, star_star] at h
  exact h

/-- `R̄`-intertwining: `X.endo (X̄.endo a) · R̄.t = R̄.t · a`. -/
lemma Conjugate.Rbar_intertwine (c : Conjugate X) (a : A) :
    X.endo (c.bar.endo a) * c.Rbar.t = c.Rbar.t * a := by
  have h := c.Rbar.intertwines a
  simpa using h.symm

/-- Starred `R̄`-intertwining: `R̄⋆ · X.endo (X̄.endo b) = b · R̄⋆`. -/
lemma Conjugate.Rbar_intertwine_star (c : Conjugate X) (b : A) :
    star c.Rbar.t * X.endo (c.bar.endo b) = b * star c.Rbar.t := by
  have h := congrArg star (c.Rbar_intertwine (star b))
  simp only [star_mul, ← map_star, star_star] at h
  exact h

/-- The **monoidal unit is self-conjugate**: `R = R̄ = (λ_ 𝟙).inv` solve the
conjugate equations trivially (the unit endomorphism is the identity). -/
def Conjugate.unit : Conjugate (𝟙_ (StarEndoCat A)) where
  bar := 𝟙_ (StarEndoCat A)
  R := (λ_ (𝟙_ (StarEndoCat A))).inv
  Rbar := (λ_ (𝟙_ (StarEndoCat A))).inv
  eq1 := by simp [leftUnitor_inv_t]
  eq2 := by simp [leftUnitor_inv_t]
  eq3 := by simp [leftUnitor_inv_t]
  eq4 := by simp [leftUnitor_inv_t]

/-- The **dimension of the monoidal unit is `1`** (Müger §1.4): `d(𝟙).t = 1`, since the
self-conjugate solution `R = (λ_ 𝟙).inv` has underlying element `1`. -/
@[simp] lemma Conjugate.unit_dim_t :
    (Conjugate.unit : Conjugate (𝟙_ (StarEndoCat A))).dim.t = 1 := by
  simp [Conjugate.dim_t, Conjugate.unit, leftUnitor_inv_t]

/-- The right dimension of the monoidal unit is also `1`, `d̄(𝟙).t = 1`. -/
@[simp] lemma Conjugate.unit_dim'_t :
    (Conjugate.unit : Conjugate (𝟙_ (StarEndoCat A))).dim'.t = 1 := by
  simp [Conjugate.dim'_t, Conjugate.unit, leftUnitor_inv_t]

/-- At the morphism level the **dimension of the unit is the identity**, `d(𝟙) = 𝟙`
(so the categorical dimension of the unit object is `1`, Müger §1.4). -/
@[simp] lemma Conjugate.unit_dim :
    (Conjugate.unit : Conjugate (𝟙_ (StarEndoCat A))).dim = 𝟙 (𝟙_ (StarEndoCat A)) := by
  apply Intertwiner.ext
  rw [unit_dim_t, id_t]

/-! ### Conjugate of a tensor product

The conjugate of `ρ ⊗ σ` is `σ̄ ⊗ ρ̄`, with coevaluations built by inserting one
conjugate's solution inside the other's. -/

variable {ρ σ : StarEndoCat A}

/-- Coevaluation for the conjugate of a tensor, `R_{ρσ} = (σ̄ ◁ (R_ρ ▷ σ)) ∘ R_σ`. -/
noncomputable def Conjugate.tensorR (cρ : Conjugate ρ) (cσ : Conjugate σ) :
    𝟙_ (StarEndoCat A) ⟶ (cσ.bar ⊗ cρ.bar) ⊗ (ρ ⊗ σ) :=
  cσ.R ≫ (cσ.bar ◁ (cρ.R ▷ σ))

@[simp] lemma Conjugate.tensorR_t (cρ : Conjugate ρ) (cσ : Conjugate σ) :
    (cρ.tensorR cσ).t = cσ.bar.endo cρ.R.t * cσ.R.t := by
  simp only [Conjugate.tensorR, comp_t, whiskerLeft_t, whiskerRight_t]

/-- Coevaluation `R̄_{ρσ} = (ρ ◁ (R̄_σ ▷ ρ̄)) ∘ R̄_ρ`. -/
noncomputable def Conjugate.tensorRbar (cρ : Conjugate ρ) (cσ : Conjugate σ) :
    𝟙_ (StarEndoCat A) ⟶ (ρ ⊗ σ) ⊗ (cσ.bar ⊗ cρ.bar) :=
  cρ.Rbar ≫ (ρ ◁ (cσ.Rbar ▷ cρ.bar))

@[simp] lemma Conjugate.tensorRbar_t (cρ : Conjugate ρ) (cσ : Conjugate σ) :
    (cρ.tensorRbar cσ).t = ρ.endo cσ.Rbar.t * cρ.Rbar.t := by
  simp only [Conjugate.tensorRbar, comp_t, whiskerLeft_t, whiskerRight_t]

lemma Conjugate.tensorEq1 (cρ : Conjugate ρ) (cσ : Conjugate σ) :
    star (cρ.tensorR cσ).t * (cσ.bar ⊗ cρ.bar).endo (cρ.tensorRbar cσ).t = 1 := by
  rw [tensorR_t, tensorRbar_t, monoidalTensorObj_endo_apply, star_mul, ← map_star cσ.bar.endo,
    mul_assoc, ← map_mul cσ.bar.endo, map_mul cρ.bar.endo, ← mul_assoc, cρ.R_intertwine_star,
    mul_assoc, cρ.eq1, mul_one, cσ.eq1]

lemma Conjugate.tensorEq2 (cρ : Conjugate ρ) (cσ : Conjugate σ) :
    (ρ ⊗ σ).endo (star (cρ.tensorR cσ).t) * (cρ.tensorRbar cσ).t = 1 := by
  rw [tensorR_t, tensorRbar_t, monoidalTensorObj_endo_apply, star_mul, ← map_star cσ.bar.endo,
    map_mul σ.endo, map_mul ρ.endo, mul_assoc,
    ← mul_assoc (ρ.endo (σ.endo (cσ.bar.endo (star cρ.R.t)))), ← map_mul ρ.endo,
    cσ.Rbar_intertwine, ← mul_assoc, ← map_mul ρ.endo, ← mul_assoc, cσ.eq2, one_mul, cρ.eq2]

lemma Conjugate.tensorEq3 (cρ : Conjugate ρ) (cσ : Conjugate σ) :
    star (cρ.tensorRbar cσ).t * (ρ ⊗ σ).endo (cρ.tensorR cσ).t = 1 := by
  rw [tensorRbar_t, tensorR_t, monoidalTensorObj_endo_apply, star_mul, ← map_star ρ.endo,
    map_mul σ.endo, map_mul ρ.endo, mul_assoc, ← mul_assoc (ρ.endo (star cσ.Rbar.t)),
    ← map_mul ρ.endo, cσ.Rbar_intertwine_star, ← map_mul ρ.endo, mul_assoc, cσ.eq3, mul_one,
    cρ.eq3]

lemma Conjugate.tensorEq4 (cρ : Conjugate ρ) (cσ : Conjugate σ) :
    (cσ.bar ⊗ cρ.bar).endo (star (cρ.tensorRbar cσ).t) * (cρ.tensorR cσ).t = 1 := by
  rw [tensorRbar_t, tensorR_t, monoidalTensorObj_endo_apply, star_mul, ← map_star ρ.endo,
    map_mul cρ.bar.endo, map_mul cσ.bar.endo, mul_assoc,
    ← mul_assoc (cσ.bar.endo (cρ.bar.endo (ρ.endo (star cσ.Rbar.t)))), ← map_mul cσ.bar.endo,
    cρ.R_intertwine, ← mul_assoc, ← map_mul cσ.bar.endo, ← mul_assoc, cρ.eq4, one_mul, cσ.eq4]

/-- **The conjugate of a tensor product.**  If `ρ̄` conjugates `ρ` and `σ̄`
conjugates `σ`, then `σ̄ ⊗ ρ̄` conjugates `ρ ⊗ σ` (Müger §1.4).  This makes the
class of objects with conjugates closed under tensor. -/
noncomputable def Conjugate.tensor (cρ : Conjugate ρ) (cσ : Conjugate σ) :
    Conjugate (ρ ⊗ σ) where
  bar := cσ.bar ⊗ cρ.bar
  R := cρ.tensorR cσ
  Rbar := cρ.tensorRbar cσ
  eq1 := cρ.tensorEq1 cσ
  eq2 := cρ.tensorEq2 cσ
  eq3 := cρ.tensorEq3 cσ
  eq4 := cρ.tensorEq4 cσ

end StarEndo

end CategoryTheory
