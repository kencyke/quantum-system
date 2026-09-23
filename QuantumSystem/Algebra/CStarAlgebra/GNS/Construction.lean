/-
Copyright (c) 2025 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.HilbertSpace
public import QuantumSystem.Algebra.CStarAlgebra.Representation
public import QuantumSystem.Algebra.CStarAlgebra.State.Faithful

/-!
# The GNS construction for a state

For a state `ω` on a (possibly non-unital) C\*-algebra `A`, the Gelfand–Naimark–Segal
construction produces the *GNS triplet* `(𝓗[ω], π[ω], ξ[ω])`:

* `𝓗[ω]` — the GNS Hilbert space, the completion of `A` for the semi-inner product
  `⟪a, b⟫ = ω (a* b)`;
* `π[ω] : A →⋆ₙₐ[ℂ] 𝓑(𝓗[ω])` — the GNS representation, induced by left multiplication;
* `ξ[ω] : 𝓗[ω]` — the cyclic unit vector, characterised by `⟪ξ[ω], [a]⟫ = ω a`.

All three are the GNS construction of a general positive linear functional, applied to the
functional `ω.toPositiveLinearMap` underlying the state: the space and the representation are
Mathlib's `PositiveLinearMap.GNS` and `PositiveLinearMap.gnsNonUnitalStarAlgHom`, and the cyclic
vector is `PositiveLinearMap.gnsVector`, whose norm is `√‖f‖ₒₚ` for a general positive functional
`f`.  The only input specific to states is `‖ω‖ = 1`, which makes `ξ[ω]` a unit vector.  The
canonical map `a ↦ [a]` is `ω.toPositiveLinearMap.gnsMk`.

## Main definitions

* `State.gnsSpace`, `State.gnsRep`, `State.gnsVector` — the GNS triplet, with the scoped
  notations `𝓗[ω]`, `π[ω]`, `ξ[ω]` (activate with `open scoped GNS`).
* `State.gnsCStarRep` — the pair `(𝓗[ω], π[ω])` bundled as a `CStarRep`, so that the orbit map
  `a ↦ π[ω] a ξ[ω]` is `CStarRep.orbit`.

## Main results

* `State.gnsRep_apply_gnsVector` — `π[ω] a ξ[ω] = [a]`.
* `State.gnsVector_cyclic`, `State.norm_gnsVector`, `State.gns_condition` — `ξ[ω]` is a cyclic
  unit vector realising `ω a = ⟪ξ[ω], π[ω] a ξ[ω]⟫`.
* `State.isFaithful_iff_separating` — `ω` is faithful iff `a ↦ π[ω] a ξ[ω]` is injective.
* `State.normalize_apply_eq_inner` — for a nonzero positive functional `f`, the state
  `‖f‖ₒₚ⁻¹ f` is the vector state of the unit cyclic vector `normalize ξ_f`.
* `State.gnsRep_one`, `State.gnsVector_eq_gnsMk_one` — on a unital algebra, `π[ω] 1 = 1` and
  `ξ[ω] = [1]`.

## References

* Bratteli, Robinson, *Operator Algebras and Quantum Statistical Mechanics I*, Theorem 2.3.16.
* Murphy, *C\*-algebras and Operator Theory*, §5.1.
-/

@[expose] public section

open scoped InnerProductSpace ComplexOrder ComplexHilbertSpace
open PositiveLinearMap

namespace State

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (ω : State A)

/-! ### The GNS triplet -/

/-- The GNS Hilbert space `𝓗[ω]` of a state: Mathlib's `PositiveLinearMap.GNS`, the completion
of `A` for the semi-inner product `⟪a, b⟫ = ω (a* b)`. -/
abbrev gnsSpace : Type _ := ω.toPositiveLinearMap.GNS

/-- Notation `𝓗[ω]` for the GNS Hilbert space `State.gnsSpace ω`. -/
scoped[GNS] notation:max "𝓗[" ω "]" => State.gnsSpace ω

open scoped GNS

noncomputable instance : ComplexHilbertSpace 𝓗[ω] where
  toNormedAddCommGroup := inferInstance
  toInnerProductSpace := inferInstance
  toCompleteSpace := inferInstance

/-- The GNS representation `π[ω] : A →⋆ₙₐ[ℂ] 𝓑(𝓗[ω])`, induced by left multiplication:
Mathlib's `PositiveLinearMap.gnsNonUnitalStarAlgHom`. -/
noncomputable abbrev gnsRep : A →⋆ₙₐ[ℂ] 𝓑(𝓗[ω]) := ω.toPositiveLinearMap.gnsNonUnitalStarAlgHom

/-- Notation `π[ω]` for the GNS representation `State.gnsRep ω`. -/
scoped[GNS] notation:max "π[" ω "]" => State.gnsRep ω

/-- The cyclic vector `ξ[ω] ∈ 𝓗[ω]`: `PositiveLinearMap.gnsVector`, the Riesz representative of
the functional `[a] ↦ ω a`. -/
noncomputable abbrev gnsVector : 𝓗[ω] := ω.toPositiveLinearMap.gnsVector

/-- Notation `ξ[ω]` for the cyclic vector `State.gnsVector ω`. -/
scoped[GNS] notation:max "ξ[" ω "]" => State.gnsVector ω

/-- The GNS representation `(𝓗[ω], π[ω])` bundled as a `CStarRep`. -/
noncomputable abbrev gnsCStarRep : CStarRep A := ⟨𝓗[ω], π[ω]⟩

/-- The GNS representation is contractive: `‖π[ω] a‖ ≤ ‖a‖`. -/
lemma norm_gnsRep_le (a : A) : ‖π[ω] a‖ ≤ ‖a‖ :=
  NonUnitalStarAlgHom.norm_apply_le _ a

/-- The fundamental identity `π[ω] a ξ[ω] = [a]`. -/
lemma gnsRep_apply_gnsVector (a : A) : π[ω] a ξ[ω] = ω.toPositiveLinearMap.gnsMk a :=
  ω.toPositiveLinearMap.gnsNonUnitalStarAlgHom_apply_gnsVector a

/-- Cyclicity of `ξ[ω]`: the orbit `{π[ω] a ξ[ω] | a : A}` is dense in `𝓗[ω]`. -/
lemma gnsVector_cyclic : DenseRange (ω.gnsCStarRep.orbit ξ[ω]) :=
  ω.toPositiveLinearMap.denseRange_gnsNonUnitalStarAlgHom_apply_gnsVector

/-- The GNS identity `ω a = ⟪ξ[ω], π[ω] a ξ[ω]⟫`. -/
lemma gns_condition (a : A) : ω a = ⟪ξ[ω], π[ω] a ξ[ω]⟫_ℂ :=
  ω.toPositiveLinearMap.apply_eq_inner_gnsNonUnitalStarAlgHom_gnsVector a

/-- Normalisation of the cyclic vector: `‖ξ[ω]‖ = 1`, since `‖ξ[ω]‖ = √‖ω‖ₒₚ` and
`‖ω‖ₒₚ = 1`. -/
lemma norm_gnsVector : ‖ξ[ω]‖ = 1 := by
  rw [gnsVector, PositiveLinearMap.norm_gnsVector, ← Real.sqrt_one]
  congr 1
  exact ω.norm_ofClass

lemma gnsVector_ne_zero : ξ[ω] ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_gnsVector]
  exact one_ne_zero

/-! ### Faithful states -/

/-- A state is faithful iff the canonical map `a ↦ [a]` into `𝓗[ω]` is injective. -/
theorem isFaithful_iff_injective_gnsMk :
    ω.IsFaithful ↔ Function.Injective ω.toPositiveLinearMap.gnsMk := by
  rw [injective_iff_map_eq_zero]
  simp only [gnsMk_eq_zero_iff]
  rfl

/-- A state is faithful iff the cyclic vector separates the algebra, i.e. the orbit map
`a ↦ π[ω] a ξ[ω]` is injective. -/
theorem isFaithful_iff_separating :
    ω.IsFaithful ↔ Function.Injective (ω.gnsCStarRep.orbit ξ[ω]) := by
  rw [ω.isFaithful_iff_injective_gnsMk]
  exact Iff.of_eq (congrArg Function.Injective (funext (gnsRep_apply_gnsVector ω)).symm)

/-- The GNS representation of a faithful state is injective. -/
lemma IsFaithful.injective_gnsRep (hω : ω.IsFaithful) : Function.Injective π[ω] :=
  fun _ _ hab => ω.isFaithful_iff_separating.mp hω (congrArg (· ξ[ω]) hab)

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
  rw [normalize_apply, inner_gnsNonUnitalStarAlgHom_normalize_gnsVector]

end State

/-! ### Unital algebras -/

namespace State

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (ω : State A)

open scoped GNS

/-- On a unital algebra the GNS representation of a state is unital: `π[ω] 1 = 1`. -/
lemma gnsRep_one : π[ω] 1 = 1 :=
  ω.toPositiveLinearMap.gnsNonUnitalStarAlgHom_one

/-- On a unital algebra the cyclic vector is the class of the unit: `ξ[ω] = [1]`. -/
lemma gnsVector_eq_gnsMk_one : ξ[ω] = ω.toPositiveLinearMap.gnsMk 1 :=
  ω.toPositiveLinearMap.gnsVector_eq_gnsMk_one

end State
