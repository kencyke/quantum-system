/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Algebra.CStarAlgebra.Representation.UnitaryEquiv

/-!
# Conjugation of a `CStarRep` by a unitary

Given a representation `R : CStarRep A` and a unitary
`U : R.H ≃ₗᵢ[ℂ] K` between Hilbert spaces, the **conjugated
representation** is the `CStarRep A` on `K` whose action sends
`a : A` to the bounded operator

```
U ∘L R.π a ∘L U.symm : K →L[ℂ] K,
```

i.e. `U π(a) U†`, since the adjoint of a unitary is its inverse
(`LinearIsometryEquiv.adjoint_eq_symm`).

The unitary `U` itself intertwines `R` with `R.conjBy U`, so the two
representations are canonically unitarily equivalent.

This is the operator-algebraic building block of the DHR selection
criterion (`LocalNet.SatisfiesDHR`, in `Algebra/LocalNet/Superselection.lean`):
given a representation `R` of the quasi-local algebra with a DHR
intertwiner `U : R.H ≃ₗᵢ[ℂ] H₀` for a region `O`
(`LocalNet.IsDHRIntertwiner`), the conjugated representation
`R.conjBy U` lives on the Hilbert space `H₀` of the vacuum
representation `π₀`, and the intertwining condition forces it to agree
with `π₀` on the observables localised outside `O`
(`LocalNet.conjBy_π_ιLocalCStar_eq_of_isDHRIntertwiner`, from
`CStarRep.conjBy_π_eq_of_intertwined`).

## Main definitions

* `CStarRep.conjBy R U` — the conjugated representation.
* `CStarRep.conjByUnitaryEquiv R U` — the canonical unitary
  equivalence `R ≃ R.conjBy U`.

## Main results

* `CStarRep.conjBy_π_apply` — `(R.conjBy U).π a = U ∘L R.π a ∘L U.symm`.
* `CStarRep.conjBy_π_eq_of_intertwined` — if the intertwining identity
  `U ∘L R.π a = T ∘L U` holds at a particular operator `T`, then
  `(R.conjBy U).π a = T`.  This is the bridge to the DHR selection
  criterion: the conjugated representation acts as the vacuum
  representation on the observables localised outside the region
  (`LocalNet.conjBy_π_ιLocalCStar_eq_of_isDHRIntertwiner`).

## References

* Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §3.2.
* Bratteli, Robinson, *Operator Algebras and Quantum Statistical
  Mechanics II*, §5.3.
-/

@[expose] public section

namespace CStarRep

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- The **conjugated representation** of `R : CStarRep A` by a unitary
`U : R.H ≃ₗᵢ[ℂ] K`: the carrier is `K` and the action is
`a ↦ U ∘L R.π a ∘L U.symm`.

Internally the underlying non-unital star-algebra homomorphism is the
composition of `R.π` with the conjugation-by-`U` star-algebra
equivalence `(R.H →L[ℂ] R.H) ≃⋆ₐ[ℂ] (K →L[ℂ] K)` provided by
`LinearIsometryEquiv.conjStarAlgEquiv`. -/
noncomputable def conjBy (R : CStarRep A) {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (U : R.H ≃ₗᵢ[ℂ] K) : CStarRep A where
  H := K
  π := U.conjStarAlgEquiv.toStarAlgHom.toNonUnitalStarAlgHom.comp R.π

/-- The carrier of the conjugated representation `R.conjBy U` is the target `K` of `U`. -/
@[simp] lemma conjBy_H (R : CStarRep A) {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (U : R.H ≃ₗᵢ[ℂ] K) : (R.conjBy U).H = K := rfl

/-- The action of the conjugated representation: `(R.conjBy U).π a` is
the operator `U ∘L R.π a ∘L U.symm` on `K`. -/
lemma conjBy_π_apply (R : CStarRep A) {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (U : R.H ≃ₗᵢ[ℂ] K) (a : A) :
    (R.conjBy U).π a = (U : R.H →L[ℂ] K) ∘L R.π a ∘L (U.symm : K →L[ℂ] R.H) := rfl

/-- The action of the conjugated representation on a vector: `(R.conjBy U).π a y = U (π a (U⁻¹ y))`. -/
@[simp] lemma conjBy_π_apply_apply (R : CStarRep A) {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (U : R.H ≃ₗᵢ[ℂ] K) (a : A) (y : K) :
    (R.conjBy U).π a y = U (R.π a (U.symm y)) := rfl

/-- The **canonical unitary equivalence** `R ≃ R.conjBy U`: the
intertwining unitary is `U` itself, and the intertwining identity is
`U ∘L R.π a = (U ∘L R.π a ∘L U.symm) ∘L U`. -/
noncomputable def conjByUnitaryEquiv (R : CStarRep A) {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (U : R.H ≃ₗᵢ[ℂ] K) :
    CStarRep.UnitaryEquiv R (R.conjBy U) where
  toLinearIsometryEquiv := U
  intertwines a := by
    ext x
    change U (R.π a x) = U (R.π a (U.symm (U x)))
    rw [U.symm_apply_apply]

/-- **Intertwining-from-the-left transports to operator equality** for
the conjugated representation.

If a unitary `U : R.H ≃ₗᵢ[ℂ] K` satisfies `U ∘L R.π a = T ∘L U`
for some `T : K →L[ℂ] K` at a particular `a : A`, then the conjugated
action `(R.conjBy U).π a` equals `T`.

This is the bridge to the DHR selection criterion: when `U` is a DHR
intertwiner for a region `O` (`LocalNet.IsDHRIntertwiner`) and
`T = π₀ a` the vacuum action, the conjugated representation agrees with
the vacuum representation on every observable `a` localised outside `O`
(`LocalNet.conjBy_π_ιLocalCStar_eq_of_isDHRIntertwiner`). -/
lemma conjBy_π_eq_of_intertwined {R : CStarRep A}
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (U : R.H ≃ₗᵢ[ℂ] K)
    {a : A} {T : K →L[ℂ] K}
    (hUa : (U : R.H →L[ℂ] K) ∘L R.π a = T ∘L (U : R.H →L[ℂ] K)) :
    (R.conjBy U).π a = T := by
  refine ContinuousLinearMap.ext fun y : K => ?_
  change U (R.π a (U.symm y)) = T y
  simpa using DFunLike.congr_fun hUa (U.symm y)

end CStarRep
