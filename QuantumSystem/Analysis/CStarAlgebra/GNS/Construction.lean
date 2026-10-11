/-
Copyright (c) 2025 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.CStarAlgebra.GNS.Representation
public import QuantumSystem.Analysis.CStarAlgebra.State.Faithful

/-!
# The GNS construction for a positive functional and a state

For a positive linear functional `f` on a (possibly non-unital) C\*-algebra `A`, the
Gelfand–Naimark–Segal construction produces the canonical GNS triplet
`GNS.Representation.canonical f`, from Mathlib's objects:

* the GNS Hilbert space `PositiveLinearMap.GNS`, the completion of `A` for the semi-inner product
  `⟪a, b⟫ = f (a* b)`;
* the GNS representation `PositiveLinearMap.gnsNonUnitalStarAlgHom`, induced by left
  multiplication;
* the cyclic vector `PositiveLinearMap.gnsVector`, characterised by `⟪ξ_f, [a]⟫ = f a`, of norm
  `√‖f‖ₒₚ`.

The canonical map `a ↦ [a]` is `PositiveLinearMap.gnsMk`.  For a state `ω` the triplet is written
`GNS[ω]` (`open scoped GNS`), with components `GNS[ω].H`, `GNS[ω].π a` and `GNS[ω].ξ`.  Facts
that hold for every GNS triplet of a state — `ξ` is a unit vector, a multiplicative state acts by
scalars, faithfulness is injectivity of the orbit map — are stated for a general triplet in
`QuantumSystem.Analysis.CStarAlgebra.GNS.Representation` and apply to `GNS[ω]` directly.

## Main definitions

* `GNS.Representation.canonical` — the GNS triplet of a positive functional, with the scoped
  notation `GNS[ω]` for a state `ω`.

## Main results

* `GNS.Representation.canonical_π_apply_ξ` — `π_f a ξ_f = [a]`.
* `GNS.Representation.canonical_ξ_eq_gnsMk_one` — on a unital algebra, `ξ_f = [1]`.
* `State.isFaithful_iff_injective_gnsMk` — `ω` is faithful iff `a ↦ [a]` is injective.
* `State.normalize_apply_eq_inner` — for a nonzero positive functional `f`, the state
  `‖f‖ₒₚ⁻¹ f` is the vector state of the unit cyclic vector `normalize ξ_f`.

## References

* Bratteli, Robinson, *Operator Algebras and Quantum Statistical Mechanics I*, Theorem 2.3.16.
* Murphy, *C\*-algebras and Operator Theory*, §5.1.
-/

@[expose] public section

open scoped InnerProductSpace ComplexOrder

/-! ### The canonical GNS triplet of a positive functional -/

namespace GNS.Representation

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (f : A →ₚ[ℂ] ℂ)

/-- The canonical GNS triplet `(f.GNS, π_f, ξ_f)` produced by the GNS construction: Mathlib's
`PositiveLinearMap.GNS` and `PositiveLinearMap.gnsNonUnitalStarAlgHom`, with the cyclic vector
`PositiveLinearMap.gnsVector`.  For a state `ω` it is written `GNS[ω]`.

A plain `def` rather than an `abbrev`, so that it is elaborated once over a generic `A`. Unfolded
at a concrete algebra such as the quasi-local algebra of a net (a uniform-space completion),
the instance search for the GNS space's normed structure times out. -/
noncomputable def canonical : Representation f where
  toCStarRep := ⟨f.GNS, f.gnsNonUnitalStarAlgHom⟩
  ξ := f.gnsVector
  cyclic := (CStarRep.isCyclicVector_iff_denseRange_orbit ⟨f.GNS, f.gnsNonUnitalStarAlgHom⟩ _).mpr
    f.denseRange_gnsNonUnitalStarAlgHom_apply_gnsVector
  gns_condition := f.apply_eq_inner_gnsNonUnitalStarAlgHom_gnsVector

/-- The Hilbert space of the canonical triplet is Mathlib's `PositiveLinearMap.GNS`. -/
lemma canonical_H : (canonical f).H = f.GNS := rfl

/-- The representation of the canonical triplet is `PositiveLinearMap.gnsNonUnitalStarAlgHom`. -/
lemma canonical_π : (canonical f).π = f.gnsNonUnitalStarAlgHom := rfl

/-- The cyclic vector of the canonical triplet is `PositiveLinearMap.gnsVector`. -/
lemma canonical_ξ : (canonical f).ξ = f.gnsVector := rfl

/-- The fundamental identity `π_f a ξ_f = [a]`. -/
lemma canonical_π_apply_ξ (a : A) : (canonical f).π a (canonical f).ξ = f.gnsMk a :=
  f.gnsNonUnitalStarAlgHom_apply_gnsVector a

end NonUnital

/-- On a unital algebra the cyclic vector of the canonical triplet is the class of the unit:
`ξ_f = [1]`. -/
lemma canonical_ξ_eq_gnsMk_one {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (f : A →ₚ[ℂ] ℂ) : (canonical f).ξ = f.gnsMk 1 :=
  f.gnsVector_eq_gnsMk_one

end GNS.Representation

/-- `GNS[ω]` is the canonical GNS triplet of the state `ω`, with components `GNS[ω].H`,
`GNS[ω].π a` and `GNS[ω].ξ`.

The notation is displayed only where the namespace `PositiveLinearMap` is not opened: under
`open PositiveLinearMap` the argument is printed as `ofClass ω`, which the unexpander does not
match.  Use `open scoped PositiveLinearMap` for its notations instead. -/
scoped[GNS] notation:max "GNS[" ω "]" => GNS.Representation.canonical (PositiveLinearMap.ofClass ω)

namespace State

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (ω : State A)

/-! ### Faithful states -/

/-- A state is faithful iff the canonical map `a ↦ [a]` into `GNS[ω].H` is injective. -/
lemma isFaithful_iff_injective_gnsMk :
    ω.IsFaithful ↔ Function.Injective (PositiveLinearMap.ofClass ω).gnsMk := by
  rw [injective_iff_map_eq_zero]
  simp only [PositiveLinearMap.gnsMk_eq_zero_iff]
  rfl

end State

/-! ### The normalised cyclic vector of a positive functional

The Mathlib TODO asks for a unit cyclic vector `ζ` of the GNS representation of a positive
functional `f` such that `a ↦ ⟪ζ, π_f a ζ⟫` is a state.  For `f ≠ 0`, `ζ_f = normalize ξ_f` does
this, and the state it realises is `State.normalize f`. -/

namespace State

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The vector state of `ζ_f = normalize ξ_f` is the normalised state `‖f‖ₒₚ⁻¹ f`. -/
lemma normalize_apply_eq_inner (f : A →ₚ[ℂ] ℂ) (hf : f ≠ 0) (a : A) :
    normalize f hf a = ⟪NormedSpace.normalize f.gnsVector,
      f.gnsNonUnitalStarAlgHom a (NormedSpace.normalize f.gnsVector)⟫_ℂ := by
  rw [normalize_apply, PositiveLinearMap.inner_gnsNonUnitalStarAlgHom_normalize_gnsVector]

end State
