module

public import QuantumSystem.Algebra.CStarAlgebra.Representation.UnitaryEquiv

/-!
# Conjugation of a `CStarRep` by a unitary

Given a representation `R : CStarRep A` and a unitary
`U : UnitaryMap R.H K` between Hilbert spaces, the **conjugated
representation** is the `CStarRep A` on `K` whose action sends
`a : A` to the bounded operator

```
U ∘L R.π a ∘L U⋆ : K →L[ℂ] K.
```

The unitary `U` itself intertwines `R` with `R.conjBy U`, so the two
representations are canonically unitarily equivalent.

This is the operator-algebraic building block of the DHR structure
theorem: given a DHR-intertwined `R` with witness unitary
`U : R.H → globalHilbert L Ω`, the conjugated representation
`R.conjBy U` lives on the same Hilbert space as the vacuum
representation, and the intertwining condition forces it to agree
with the vacuum action on operators localised outside the
DHR-localisation region.

## Main definitions

* `CStarRep.conjBy R U` — the conjugated representation.
* `CStarRep.conjByUnitaryEquiv R U` — the canonical unitary
  equivalence `R ≃ R.conjBy U`.

## Main results

* `CStarRep.conjBy_π_apply` — `(R.conjBy U).π a = U R.π a U⋆`.
* `CStarRep.conjBy_π_eq_of_intertwined` — if the intertwining identity
  `U ∘L R.π a = T ∘L U` holds at a particular operator `T`, then
  `(R.conjBy U).π a = T`.  This is the bridge to the DHR structure
  theorem: the conjugated DHR representation acts as the vacuum
  representation on operators localised outside the DHR region.

## References

* Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §3.2.
* Bratteli, Robinson, *Operator Algebras and Quantum Statistical
  Mechanics II*, §5.3.
-/

@[expose] public section

namespace CStarRep

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- The **conjugated representation** of `R : CStarRep A` by a unitary
`U : UnitaryMap R.H K`: the carrier is `K` and the action is
`a ↦ U ∘L R.π a ∘L U⋆`.

Internally the underlying non-unital star-algebra homomorphism is the
composition of `R.π` with the conjugation-by-`U` star-algebra
equivalence `(R.H →L[ℂ] R.H) ≃⋆ₐ[ℂ] (K →L[ℂ] K)` provided by
`LinearIsometryEquiv.conjStarAlgEquiv`. -/
noncomputable def conjBy (R : CStarRep A) {K : Type*} [ComplexHilbertSpace K]
    (U : UnitaryMap R.H K) : CStarRep A where
  H := K
  π :=
    (((U.toLinearIsometryEquiv.conjStarAlgEquiv :
        (R.H →L[ℂ] R.H) →⋆ₙₐ[ℂ] (K →L[ℂ] K))).comp R.π)

@[simp] lemma conjBy_H (R : CStarRep A) {K : Type*} [ComplexHilbertSpace K]
    (U : UnitaryMap R.H K) : (R.conjBy U).H = K := rfl

/-- The action of the conjugated representation: `(R.conjBy U).π a` is
the operator `U ∘L R.π a ∘L U⋆` on `K`. -/
@[simp] lemma conjBy_π_apply (R : CStarRep A) {K : Type*}
    [ComplexHilbertSpace K] (U : UnitaryMap R.H K) (a : A) :
    (R.conjBy U).π a =
      U.toContinuousLinearMap ∘L R.π a ∘L U.toContinuousLinearMap.adjoint := by
  -- `conjStarAlgEquiv` is defined so that `e.conjStarAlgEquiv x = e ∘L x ∘L e.symm`
  -- and `UnitaryMap.toLinearIsometryEquiv` is built with `toFun = U.toCLM` and
  -- `invFun = U.toCLM.adjoint`, so both sides reduce to the same CLM.
  apply ContinuousLinearMap.ext
  intro y
  rfl

/-- The **canonical unitary equivalence** `R ≃ R.conjBy U`: the
intertwining unitary is `U` itself, and the intertwining identity is
`U ∘L R.π a = (U R.π a U⋆) ∘L U`, which follows from `U⋆ U = id`. -/
noncomputable def conjByUnitaryEquiv (R : CStarRep A) {K : Type*}
    [ComplexHilbertSpace K] (U : UnitaryMap R.H K) :
    CStarRep.UnitaryEquiv R (R.conjBy U) where
  unitary_map := U
  intertwines a := by
    -- LHS: `U ∘L R.π a`.
    -- RHS: `(R.conjBy U).π a ∘L U = U ∘L R.π a ∘L U⋆ ∘L U = U ∘L R.π a`
    -- using `U⋆ U = id` from `U.adjoint_comp`.
    rw [conjBy_π_apply]
    apply ContinuousLinearMap.ext
    intro x
    have h : U.toContinuousLinearMap.adjoint
        (U.toContinuousLinearMap x) = x := by
      have := congrArg
        (fun (f : R.H →L[ℂ] R.H) => f x) U.adjoint_comp
      simpa using this
    -- Goal: `U (R.π a x) = U (R.π a (U⋆ (U x)))`.  Unfold nested
    -- `.comp` applications and then rewrite with `h`.
    change U.toContinuousLinearMap ((R.π a) x) =
      U.toContinuousLinearMap ((R.π a) (U.toContinuousLinearMap.adjoint
        (U.toContinuousLinearMap x)))
    rw [h]

/-- **Intertwining-from-the-left transports to operator equality** for
the conjugated representation.

If a unitary `U : UnitaryMap R.H K` satisfies `U ∘L R.π a = T ∘L U`
for some `T : K →L[ℂ] K` at a particular `a : A`, then the conjugated
action `(R.conjBy U).π a` equals `T`.

This is the bridge to the DHR structure theorem: when `U` is the
witness of a DHR intertwining condition and `T = incl a` is the action
of a reference inclusion (for instance the vacuum representation
`Subtype.val`), the conjugated representation agrees with that
inclusion on every operator where the intertwining condition holds —
i.e. on operators localised outside the DHR region. -/
lemma conjBy_π_eq_of_intertwined {R : CStarRep A}
    {K : Type*} [ComplexHilbertSpace K]
    (U : UnitaryMap R.H K)
    {a : A} {T : K →L[ℂ] K}
    (hUa : U.toContinuousLinearMap ∘L R.π a = T ∘L U.toContinuousLinearMap) :
    (R.conjBy U).π a = T := by
  -- From `U ∘L R.π a = T ∘L U`, post-compose with `U⋆`:
  -- `U ∘L R.π a ∘L U⋆ = T ∘L U ∘L U⋆ = T` using `U U⋆ = id`.
  rw [conjBy_π_apply]
  apply ContinuousLinearMap.ext
  intro y
  -- Apply `hUa` at the point `U⋆ y`.
  have hy := congrArg
    (fun (f : R.H →L[ℂ] K) => f (U.toContinuousLinearMap.adjoint y)) hUa
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply] at hy ⊢
  rw [hy]
  -- Remaining: `T (U (U⋆ y)) = T y`.
  have hUU : U.toContinuousLinearMap
      (U.toContinuousLinearMap.adjoint y) = y := by
    have := congrArg
      (fun (f : K →L[ℂ] K) => f y) U.comp_adjoint
    simpa using this
  rw [hUU]

end CStarRep
