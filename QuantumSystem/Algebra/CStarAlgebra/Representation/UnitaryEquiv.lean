module

public import QuantumSystem.Algebra.CStarAlgebra.Representation
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Unitary equivalence of `CStarRep`s

Two non-unital `*`-representations `R₁ R₂ : CStarRep A` are *unitarily
equivalent* if there exists a unitary `U : R₁.H ≃ₗᵢ[ℂ] R₂.H` intertwining
the two representations:

```
U ∘L R₁.π a = R₂.π a ∘L U   for every  a : A
```

A unitary between complex Hilbert spaces is exactly a linear isometric
equivalence, so the unitary is carried as Mathlib's `R₁.H ≃ₗᵢ[ℂ] R₂.H`; its
adjoint is its inverse (`LinearIsometryEquiv.adjoint_eq_symm`).

This is the standard notion used in sector theory: representations in
the same unitary-equivalence class are physically indistinguishable.
Compared with `GNS.Representation.UnitaryEquiv` (which additionally
requires the unitary to identify the GNS cyclic vectors of two triplets
for the *same* state `ω`), this notion drops the cyclic-vector
compatibility and applies to two general representations of possibly
unrelated origin.

## Main definitions

* `CStarRep.UnitaryEquiv R₁ R₂` — a unitary `R₁.H ≃ₗᵢ[ℂ] R₂.H` together
  with the intertwining property.
* `CStarRep.UnitaryEquiv.refl` / `.symm` / `.trans` — equivalence
  closure.
* `CStarRep.unitarySetoid` — the corresponding `Setoid` on `CStarRep A`,
  whose underlying relation is `Nonempty ∘ UnitaryEquiv`.
-/

@[expose] public section

namespace CStarRep

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- A unitary equivalence between two `CStarRep`s of the same C\*-algebra
`A`: a unitary `U : R₁.H ≃ₗᵢ[ℂ] R₂.H` between the underlying Hilbert spaces
that intertwines the two `*`-representations, `U ∘L R₁.π a = R₂.π a ∘L U`. -/
structure UnitaryEquiv (R₁ R₂ : CStarRep A) extends R₁.H ≃ₗᵢ[ℂ] R₂.H where
  /-- The intertwining property `U ∘L R₁.π a = R₂.π a ∘L U`. -/
  intertwines :
    ∀ a : A,
      (toLinearIsometryEquiv : R₁.H →L[ℂ] R₂.H) ∘L R₁.π a =
        R₂.π a ∘L (toLinearIsometryEquiv : R₁.H →L[ℂ] R₂.H)

namespace UnitaryEquiv

variable {R₁ R₂ R₃ : CStarRep A}

/-- The intertwining property, pointwise: `U (π₁ a x) = π₂ a (U x)`. -/
lemma intertwines_apply (U : UnitaryEquiv R₁ R₂) (a : A) (x : R₁.H) :
    U.toLinearIsometryEquiv (R₁.π a x) = R₂.π a (U.toLinearIsometryEquiv x) := by
  simpa using DFunLike.congr_fun (U.intertwines a) x

/-- Identity unitary equivalence. -/
noncomputable def refl (R : CStarRep A) : UnitaryEquiv R R where
  toLinearIsometryEquiv := LinearIsometryEquiv.refl ℂ R.H
  intertwines a := by ext x; simp

/-- Inverse of a unitary equivalence: the inverse unitary `U.symm` (which is the adjoint
`U†`) intertwines in the other direction. -/
noncomputable def symm (U : UnitaryEquiv R₁ R₂) : UnitaryEquiv R₂ R₁ where
  toLinearIsometryEquiv := U.toLinearIsometryEquiv.symm
  intertwines a := by
    ext y
    apply U.toLinearIsometryEquiv.injective
    simp [U.intertwines_apply]

/-- Composition of unitary equivalences. -/
noncomputable def trans (U : UnitaryEquiv R₁ R₂) (V : UnitaryEquiv R₂ R₃) :
    UnitaryEquiv R₁ R₃ where
  toLinearIsometryEquiv := U.toLinearIsometryEquiv.trans V.toLinearIsometryEquiv
  intertwines a := by ext x; simp [U.intertwines_apply, V.intertwines_apply]

@[simp] lemma refl_toLinearIsometryEquiv (R : CStarRep A) :
    (refl R).toLinearIsometryEquiv = LinearIsometryEquiv.refl ℂ R.H := rfl

@[simp] lemma symm_toLinearIsometryEquiv (U : UnitaryEquiv R₁ R₂) :
    U.symm.toLinearIsometryEquiv = U.toLinearIsometryEquiv.symm := rfl

@[simp] lemma trans_toLinearIsometryEquiv (U : UnitaryEquiv R₁ R₂) (V : UnitaryEquiv R₂ R₃) :
    (U.trans V).toLinearIsometryEquiv = U.toLinearIsometryEquiv.trans V.toLinearIsometryEquiv :=
  rfl

end UnitaryEquiv

/-- The relation "there exists a unitary equivalence between `R₁` and `R₂`". -/
def unitarilyEquivalent (R₁ R₂ : CStarRep A) : Prop :=
  Nonempty (UnitaryEquiv R₁ R₂)

lemma unitarilyEquivalent.refl (R : CStarRep A) : unitarilyEquivalent R R :=
  ⟨UnitaryEquiv.refl R⟩

lemma unitarilyEquivalent.symm {R₁ R₂ : CStarRep A}
    (h : unitarilyEquivalent R₁ R₂) : unitarilyEquivalent R₂ R₁ :=
  h.elim fun U => ⟨U.symm⟩

lemma unitarilyEquivalent.trans {R₁ R₂ R₃ : CStarRep A}
    (h₁ : unitarilyEquivalent R₁ R₂) (h₂ : unitarilyEquivalent R₂ R₃) :
    unitarilyEquivalent R₁ R₃ :=
  h₁.elim fun U => h₂.elim fun V => ⟨U.trans V⟩

/-- The `Setoid` of `CStarRep`s up to unitary equivalence. -/
def unitarySetoid : Setoid (CStarRep A) where
  r := unitarilyEquivalent
  iseqv :=
    { refl := unitarilyEquivalent.refl
      symm := unitarilyEquivalent.symm
      trans := unitarilyEquivalent.trans }

end CStarRep
