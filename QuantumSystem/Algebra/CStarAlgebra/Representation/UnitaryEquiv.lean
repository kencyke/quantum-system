module

public import QuantumSystem.Algebra.CStarAlgebra.Representation

/-!
# Unitary equivalence of `CStarRep`s

Two non-unital `*`-representations `R₁ R₂ : CStarRep A` are *unitarily
equivalent* if there exists a unitary map `U : R₁.H → R₂.H` intertwining
the two representations:

```
U ∘L R₁.π a = R₂.π a ∘L U   for every  a : A
```

This is the standard notion used in sector theory: representations in
the same unitary-equivalence class are physically indistinguishable.
Compared with `GNS.Representation.UnitaryEquiv` (which additionally
requires the unitary to identify the GNS cyclic vectors of two triplets
for the *same* state `ω`), this notion drops the cyclic-vector
compatibility and applies to two general representations of possibly
unrelated origin.

## Main definitions

* `CStarRep.UnitaryEquiv R₁ R₂` — the data of a unitary intertwiner.
* `CStarRep.UnitaryEquiv.refl` / `.symm` / `.trans` — equivalence
  closure.
* `CStarRep.unitarySetoid` — the corresponding `Setoid` on `CStarRep A`,
  whose underlying relation is `Nonempty ∘ UnitaryEquiv`.
-/

@[expose] public section

namespace CStarRep

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- A unitary equivalence between two `CStarRep`s of the same C\*-algebra
`A`: a unitary map between the underlying Hilbert spaces that intertwines
the two `*`-representations. -/
structure UnitaryEquiv (R₁ R₂ : CStarRep A) where
  /-- The underlying unitary between the Hilbert spaces. -/
  unitary_map : UnitaryMap R₁.H R₂.H
  /-- The intertwining property. -/
  intertwines :
    ∀ a : A,
      unitary_map.toContinuousLinearMap ∘L R₁.π a =
        R₂.π a ∘L unitary_map.toContinuousLinearMap

namespace UnitaryEquiv

/-- Identity unitary equivalence. -/
noncomputable def refl (R : CStarRep A) : UnitaryEquiv R R where
  unitary_map :=
    { toContinuousLinearMap := ContinuousLinearMap.id ℂ R.H
      adjoint_comp := by
        rw [ContinuousLinearMap.adjoint_id]
        ext x; simp
      comp_adjoint := by
        rw [ContinuousLinearMap.adjoint_id]
        ext x; simp }
  intertwines a := by ext x; simp

/-- Inverse of a unitary equivalence: take the adjoint of the unitary map. -/
noncomputable def symm {R₁ R₂ : CStarRep A} (U : UnitaryEquiv R₁ R₂) :
    UnitaryEquiv R₂ R₁ where
  unitary_map :=
    { toContinuousLinearMap := U.unitary_map.toContinuousLinearMap.adjoint
      adjoint_comp := by
        rw [ContinuousLinearMap.adjoint_adjoint]
        exact U.unitary_map.comp_adjoint
      comp_adjoint := by
        rw [ContinuousLinearMap.adjoint_adjoint]
        exact U.unitary_map.adjoint_comp }
  intertwines a := by
    -- From `U ∘L π₁ a = π₂ a ∘L U`, taking adjoints both sides yields
    -- `(π₁ a)† ∘L U† = U† ∘L (π₂ a)†`; rewriting (πᵢ a)† = πᵢ (star a)
    -- gives `π₁ (star a) ∘L U† = U† ∘L π₂ (star a)`. Substituting
    -- `a ↦ star a` (and using `star (star a) = a`) yields the goal.
    have h := U.intertwines (star a)
    have h' :
        (U.unitary_map.toContinuousLinearMap ∘L R₁.π (star a)).adjoint =
          (R₂.π (star a) ∘L U.unitary_map.toContinuousLinearMap).adjoint := by
      rw [h]
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp] at h'
    -- Now `(π₁ (star a))† ∘L U†.adjoint.adjoint = U†.adjoint.adjoint ∘L (π₂ (star a))†`.
    -- But the LHS is `(π₁ (star a))† ∘L U†` after no rewriting since adjoint sits in
    -- the outer position. The relevant simp lemma: `(π a)† = π (star a)`.
    have hπ₁ : (R₁.π (star a)).adjoint = R₁.π a := by
      have := (R₁.π).map_star' (star a)
      rw [ContinuousLinearMap.star_eq_adjoint, star_star] at this
      exact this.symm
    have hπ₂ : (R₂.π (star a)).adjoint = R₂.π a := by
      have := (R₂.π).map_star' (star a)
      rw [ContinuousLinearMap.star_eq_adjoint, star_star] at this
      exact this.symm
    -- After rewriting:
    rw [hπ₁, hπ₂] at h'
    exact h'.symm

/-- Composition of unitary equivalences. -/
noncomputable def trans {R₁ R₂ R₃ : CStarRep A}
    (U : UnitaryEquiv R₁ R₂) (V : UnitaryEquiv R₂ R₃) :
    UnitaryEquiv R₁ R₃ where
  unitary_map :=
    { toContinuousLinearMap :=
        V.unitary_map.toContinuousLinearMap ∘L U.unitary_map.toContinuousLinearMap
      adjoint_comp := by
        ext x
        -- ((VU)† ∘L (VU)) x = U†(V†(V(Ux))) = U†(Ux) = x
        simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.coe_comp',
          Function.comp_apply, ContinuousLinearMap.one_apply]
        have hV :
            V.unitary_map.toContinuousLinearMap.adjoint
              (V.unitary_map.toContinuousLinearMap (U.unitary_map.toContinuousLinearMap x)) =
              U.unitary_map.toContinuousLinearMap x := by
          have := congrArg
            (fun (f : R₂.H →L[ℂ] R₂.H) => f (U.unitary_map.toContinuousLinearMap x))
            V.unitary_map.adjoint_comp
          simpa using this
        rw [hV]
        have hU :
            U.unitary_map.toContinuousLinearMap.adjoint
              (U.unitary_map.toContinuousLinearMap x) = x := by
          have := congrArg
            (fun (f : R₁.H →L[ℂ] R₁.H) => f x) U.unitary_map.adjoint_comp
          simpa using this
        exact hU
      comp_adjoint := by
        ext y
        simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.coe_comp',
          Function.comp_apply, ContinuousLinearMap.one_apply]
        have hU :
            U.unitary_map.toContinuousLinearMap
              (U.unitary_map.toContinuousLinearMap.adjoint
                (V.unitary_map.toContinuousLinearMap.adjoint y)) =
              V.unitary_map.toContinuousLinearMap.adjoint y := by
          have := congrArg
            (fun (f : R₂.H →L[ℂ] R₂.H) => f (V.unitary_map.toContinuousLinearMap.adjoint y))
            U.unitary_map.comp_adjoint
          simpa using this
        rw [hU]
        have hV :
            V.unitary_map.toContinuousLinearMap
              (V.unitary_map.toContinuousLinearMap.adjoint y) = y := by
          have := congrArg
            (fun (f : R₃.H →L[ℂ] R₃.H) => f y) V.unitary_map.comp_adjoint
          simpa using this
        exact hV }
  intertwines a := by
    -- (VU) ∘L π₁ a = V ∘L (U ∘L π₁ a) = V ∘L (π₂ a ∘L U) = (V ∘L π₂ a) ∘L U
    --             = (π₃ a ∘L V) ∘L U = π₃ a ∘L (V ∘L U)
    ext x
    have hU := congrArg (fun (f : R₁.H →L[ℂ] R₂.H) => f x) (U.intertwines a)
    have hV := congrArg (fun (f : R₂.H →L[ℂ] R₃.H) => f (U.unitary_map.toContinuousLinearMap x))
      (V.intertwines a)
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply] at hU hV ⊢
    rw [← hU] at hV
    exact hV

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
