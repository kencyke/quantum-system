module

public import QuantumSystem.Algebra.CStarAlgebra.Representation.UnitaryEquiv
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.AdjointNotation

/-!
# Intertwiners between `CStarRep`s

A *morphism* `T : CStarRep.Hom R₁ R₂` in the representation category of a
non-unital C\*-algebra `A` is a bounded linear map
`T : R₁.H →L[ℂ] R₂.H` that intertwines the two `*`-representations:

```
T ∘L R₁.π a = R₂.π a ∘L T   for every  a : A.
```

This is the standard notion of intertwiner used throughout sector
theory: subrepresentations, irreducibility, direct sums, Schur's lemma
and ultimately fusion of DHR sectors are all phrased in this language.
Unitary equivalence (`CStarAlgebra/Representation/UnitaryEquiv.lean`) is the subgroupoid of
isomorphisms in this category.

## Main definitions

* `CStarRep.Hom R₁ R₂` — bundled intertwiner.
* `CStarRep.Hom.id` — identity intertwiner.
* `CStarRep.Hom.comp` — composition of intertwiners.
* `CStarRep.UnitaryEquiv.toHom` — forget a unitary equivalence to an
  intertwiner.
-/

@[expose] public section

open scoped Adjoint

namespace CStarRep

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- A morphism between two `CStarRep`s of the same C\*-algebra: a
bounded linear map intertwining the two `*`-representations. -/
structure Hom (R₁ R₂ : CStarRep A) where
  /-- The underlying bounded linear map. -/
  toContinuousLinearMap : R₁.H →L[ℂ] R₂.H
  /-- The intertwining property. -/
  intertwines :
    ∀ a : A,
      toContinuousLinearMap ∘L R₁.π a = R₂.π a ∘L toContinuousLinearMap

namespace Hom

variable {R₁ R₂ R₃ : CStarRep A}

/-- Two intertwiners are equal when their underlying continuous linear
maps agree. -/
@[ext] lemma ext {T S : Hom R₁ R₂}
    (h : T.toContinuousLinearMap = S.toContinuousLinearMap) : T = S := by
  cases T; cases S; congr

/-- The identity intertwiner. -/
noncomputable def id (R : CStarRep A) : Hom R R where
  toContinuousLinearMap := ContinuousLinearMap.id ℂ R.H
  intertwines a := by ext x; simp

/-- Composition of intertwiners. -/
noncomputable def comp (S : Hom R₂ R₃) (T : Hom R₁ R₂) : Hom R₁ R₃ where
  toContinuousLinearMap :=
    S.toContinuousLinearMap ∘L T.toContinuousLinearMap
  intertwines a := by
    -- `S ∘L T ∘L π₁ a = S ∘L (π₂ a ∘L T) = (S ∘L π₂ a) ∘L T = (π₃ a ∘L S) ∘L T`.
    ext x
    have hT := congrArg (fun (f : R₁.H →L[ℂ] R₂.H) => f x) (T.intertwines a)
    have hS := congrArg (fun (f : R₂.H →L[ℂ] R₃.H) => f (T.toContinuousLinearMap x))
      (S.intertwines a)
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply] at hT hS ⊢
    rw [← hT] at hS
    exact hS

@[simp] lemma id_toContinuousLinearMap (R : CStarRep A) :
    (Hom.id R).toContinuousLinearMap = ContinuousLinearMap.id ℂ R.H := rfl

@[simp] lemma comp_toContinuousLinearMap (S : Hom R₂ R₃) (T : Hom R₁ R₂) :
    (S.comp T).toContinuousLinearMap =
      S.toContinuousLinearMap ∘L T.toContinuousLinearMap := rfl

@[simp] lemma id_comp (T : Hom R₁ R₂) : (Hom.id R₂).comp T = T := by
  ext; simp

@[simp] lemma comp_id (T : Hom R₁ R₂) : T.comp (Hom.id R₁) = T := by
  ext; simp

lemma comp_assoc {R₄ : CStarRep A}
    (U : Hom R₃ R₄) (S : Hom R₂ R₃) (T : Hom R₁ R₂) :
    (U.comp S).comp T = U.comp (S.comp T) := by
  ext; simp [ContinuousLinearMap.comp_assoc]

end Hom

namespace UnitaryEquiv

variable {R₁ R₂ : CStarRep A}

/-- A unitary equivalence is in particular an intertwiner. -/
noncomputable def toHom (U : UnitaryEquiv R₁ R₂) : Hom R₁ R₂ where
  toContinuousLinearMap := U.unitary_map.toContinuousLinearMap
  intertwines := U.intertwines

@[simp] lemma toHom_toContinuousLinearMap (U : UnitaryEquiv R₁ R₂) :
    U.toHom.toContinuousLinearMap = U.unitary_map.toContinuousLinearMap := rfl

@[simp] lemma symm_toHom (U : UnitaryEquiv R₁ R₂) :
    U.symm.toHom.toContinuousLinearMap =
      U.unitary_map.toContinuousLinearMap† := rfl

@[simp] lemma refl_toHom (R : CStarRep A) :
    (UnitaryEquiv.refl R).toHom = Hom.id R := by
  ext; rfl

end UnitaryEquiv

end CStarRep
