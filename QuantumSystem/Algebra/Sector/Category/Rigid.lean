module

public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import QuantumSystem.Algebra.Sector.Category.Conjugate

/-!
# The rigid full subcategory of objects with conjugates

An object of `StarEndoCat A` lies in the **rigid** part when it admits a
conjugate (a two-sided dual, `Conjugate`).  By `Conjugate.swap` this class is
closed under conjugation, and by `Conjugate.unit` it contains the monoidal unit;
closure under tensor (`Conjugate.tensor`) is the remaining ingredient that makes
it an `ObjectProperty.IsMonoidal`, whence the full subcategory inherits a
monoidal structure and — every object having a two-sided dual
(`Conjugate.hasRightDual` / `hasLeftDual_self`) — a `RigidCategory` structure.

This file records the object property and the unit closure; the tensor closure
and the `RigidCategory` instance are built on top.
-/

@[expose] public section

namespace CategoryTheory

namespace StarEndo

open MonoidalCategory

variable {A : Type*} [CStarAlgebra A]

/-- The object property of having a conjugate (a two-sided dual). -/
def HasConjugate : ObjectProperty (StarEndoCat A) := fun ρ => Nonempty (Conjugate ρ)

/-- The monoidal unit has a conjugate (itself), so the rigid class contains the
unit. -/
instance : (HasConjugate (A := A)).ContainsUnit where
  prop_unit := ⟨Conjugate.unit⟩

/-- The conjugate of an object in the rigid class is again in the rigid class
(`Conjugate.swap`). -/
lemma HasConjugate.bar_mem {ρ : StarEndoCat A} (c : Conjugate ρ) :
    HasConjugate (A := A) c.bar := ⟨c.swap⟩

/-- The rigid class is closed under tensor (`Conjugate.tensor`). -/
instance : (HasConjugate (A := A)).TensorLE (HasConjugate (A := A)) (HasConjugate (A := A)) where
  prop_tensor ρ σ h₁ h₂ := by
    obtain ⟨cρ⟩ := h₁
    obtain ⟨cσ⟩ := h₂
    exact ⟨cρ.tensor cσ⟩

/-- Hence `HasConjugate` is a monoidal object property: it contains the unit and
is closed under tensor. -/
instance : (HasConjugate (A := A)).IsMonoidal where

/-- The **rigid sector category**: the full monoidal subcategory of objects that
admit a conjugate (a two-sided dual).  It inherits the strict monoidal and
dagger-monoidal structure from `StarEndoCat A`. -/
noncomputable abbrev rigidCat : Type _ := (HasConjugate (A := A)).FullSubcategory

noncomputable example : MonoidalCategory (rigidCat (A := A)) := inferInstance

open Classical in
/-- Every object of the rigid sector category has a right dual: its conjugate. -/
noncomputable instance rigidCat_hasRightDual (X : rigidCat (A := A)) : HasRightDual X where
  rightDual := ⟨X.property.some.bar, ⟨X.property.some.swap⟩⟩
  exact :=
    { coevaluation' := ObjectProperty.homMk X.property.some.Rbar
      evaluation' := ObjectProperty.homMk X.property.some.R†
      coevaluation_evaluation' := by ext; exact X.property.some.exactPairing.coevaluation_evaluation'
      evaluation_coevaluation' := by ext; exact X.property.some.exactPairing.evaluation_coevaluation' }

open Classical in
/-- Every object of the rigid sector category has a left dual: its conjugate
(via the second exact pairing). -/
noncomputable instance rigidCat_hasLeftDual (X : rigidCat (A := A)) : HasLeftDual X where
  leftDual := ⟨X.property.some.bar, ⟨X.property.some.swap⟩⟩
  exact :=
    { coevaluation' := ObjectProperty.homMk X.property.some.R
      evaluation' := ObjectProperty.homMk X.property.some.Rbar†
      coevaluation_evaluation' := by
        ext; exact X.property.some.exactPairing'.coevaluation_evaluation'
      evaluation_coevaluation' := by
        ext; exact X.property.some.exactPairing'.evaluation_coevaluation' }

/-- `rigidCat` is right rigid: every object has a right dual. -/
noncomputable instance : RightRigidCategory (rigidCat (A := A)) where
  rightDual X := rigidCat_hasRightDual X

/-- `rigidCat` is left rigid: every object has a left dual. -/
noncomputable instance : LeftRigidCategory (rigidCat (A := A)) where
  leftDual X := rigidCat_hasLeftDual X

/-- **The rigid sector category is rigid.**  Every object (a localized
endomorphism with a conjugate) has a two-sided dual, assembled from the
`ExactPairing`s of its conjugate.  This is the categorical content of
Doplicher–Roberts / Müger §1.4: a tensor `∗`-category with conjugates is rigid. -/
noncomputable instance : RigidCategory (rigidCat (A := A)) where

/-- `rigidCat` is simultaneously a strict **rigid** and **dagger-monoidal**
category — the rigid + dagger-monoidal part of the DHR target
`RigidSymmetricDaggerCategory` (only the *symmetric* braiding, an extra
geometric/statistics input, is still missing). -/
noncomputable example : DaggerMonoidalCategory (rigidCat (A := A)) := inferInstance

noncomputable example : RigidCategory (rigidCat (A := A)) := inferInstance

/-! ### The endomorphisms of the monoidal unit

`End 𝟙` is the centre of `A`: the intertwining relation for the unit says an
endomorphism of `𝟙` commutes with every element of `A`.  It is therefore `ℂ`
exactly when `A` has trivial centre (is a *factor*) — the `End 𝟙 = ℂ` hypothesis
of the Doplicher–Roberts reconstruction (Müger Theorem 2.18), supplied as a model
input alongside Haag duality. -/

/-- An endomorphism of the monoidal unit is a **central** element of `A`. -/
lemma endUnit_t_mem_center (t : 𝟙_ (StarEndoCat A) ⟶ 𝟙_ (StarEndoCat A)) :
    t.t ∈ Subalgebra.center ℂ A := by
  rw [Subalgebra.mem_center_iff]
  intro a
  have h := t.intertwines a
  simpa using h.symm

/-- Conversely, a **central** element of `A` underlies an endomorphism of the
monoidal unit.  With `endUnit_t_mem_center` this identifies `End 𝟙` with the centre
of `A`; it collapses to `ℂ` exactly when `A` is a factor. -/
def endUnitOfCentral (c : A) (hc : c ∈ Subalgebra.center ℂ A) :
    𝟙_ (StarEndoCat A) ⟶ 𝟙_ (StarEndoCat A) where
  t := c
  intertwines a := by
    rw [Subalgebra.mem_center_iff] at hc
    change c * a = a * c
    exact (hc a).symm

@[simp] lemma endUnitOfCentral_t (c : A) (hc : c ∈ Subalgebra.center ℂ A) :
    (endUnitOfCentral c hc).t = c := rfl

/-- The dimension of a conjugate lies in the **centre** of `A` (`End 𝟙 = Z(A)`, via
`endUnit_t_mem_center`).  Together with `Conjugate.dim_t_nonneg` this exhibits `d(X)`
as a non-negative central element — a non-negative real scalar when `A` is a factor
(`Z(A) = ℂ`), which is the form of the categorical dimension used in R7-B. -/
lemma Conjugate.dim_t_mem_center {X : StarEndoCat A} (c : Conjugate X) :
    c.dim.t ∈ Subalgebra.center ℂ A :=
  endUnit_t_mem_center c.dim

/-- The right dimension of a conjugate likewise lies in the centre of `A`. -/
lemma Conjugate.dim'_t_mem_center {X : StarEndoCat A} (c : Conjugate X) :
    c.dim'.t ∈ Subalgebra.center ℂ A :=
  endUnit_t_mem_center c.dim'

end StarEndo

end CategoryTheory
