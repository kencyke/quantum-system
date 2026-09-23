module

public import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Analysis.Normed.Module.Completion
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.AdjointNotation
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.HilbertSpace
public import QuantumSystem.Algebra.CStarAlgebra.State.Faithful

/-!
# The GNS construction for a state

For a state `ω` on a (possibly non-unital) C\*-algebra `A`, the Gelfand–Naimark–Segal
construction produces the *GNS triplet* `(𝓗[ω], π[ω], ξ[ω])`:

* `𝓗[ω]` — the GNS Hilbert space, the completion of `A` for the semi-inner product
  `⟪a, b⟫ = ω (a* b)`;
* `π[ω] : A →⋆ₙₐ[ℂ] 𝓑(𝓗[ω])` — the GNS representation, induced by left multiplication;
* `ξ[ω] : 𝓗[ω]` — the cyclic unit vector, characterised by `⟪ξ[ω], [a]⟫ = ω a`.

The Hilbert space and the representation are exactly Mathlib's `PositiveLinearMap.GNS` and
`PositiveLinearMap.gnsNonUnitalStarAlgHom`, applied to the positive linear functional
`ω.toPositiveLinearMap` underlying the state; this file only names them for a state and adds the
cyclic vector, which Mathlib does not construct.  The vector `ξ[ω]` is obtained through the Riesz
representation of the bounded functional `[a] ↦ ω a` on `𝓗[ω]`; that this functional is bounded
is the inequality `|ω a|² ≤ ω (a* a)` (`State.norm_apply_sq_le`).

## Main definitions

* `State.gnsSpace`, `State.gnsRep`, `State.gnsVector` — the GNS triplet, with the scoped
  notations `𝓗[ω]`, `π[ω]`, `ξ[ω]` (activate with `open scoped GNS`).
* `State.gnsMk` — the canonical linear map `A →ₗ[ℂ] 𝓗[ω]`, `a ↦ [a]`.

## Main results

* `State.gnsRep_apply_gnsVector` — `π[ω] a ξ[ω] = [a]`.
* `State.gnsVector_cyclic`, `State.norm_gnsVector`, `State.gns_condition` — `ξ[ω]` is a cyclic
  unit vector realising `ω a = ⟪ξ[ω], π[ω] a ξ[ω]⟫`.
* `State.isFaithful_iff_separating` — `ω` is faithful iff `a ↦ π[ω] a ξ[ω]` is injective.

## References

* Bratteli, Robinson, *Operator Algebras and Quantum Statistical Mechanics I*, Theorem 2.3.16.
* Murphy, *C\*-algebras and Operator Theory*, §5.1.
-/

@[expose] public section

open scoped InnerProductSpace ComplexOrder ComplexHilbertSpace Adjoint
open UniformSpace Completion Filter Topology PositiveLinearMap

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
noncomputable def gnsRep : A →⋆ₙₐ[ℂ] 𝓑(𝓗[ω]) := ω.toPositiveLinearMap.gnsNonUnitalStarAlgHom

/-- Notation `π[ω]` for the GNS representation `State.gnsRep ω`. -/
scoped[GNS] notation:max "π[" ω "]" => State.gnsRep ω

/-- The canonical map `A →ₗ[ℂ] 𝓗[ω]`, `a ↦ [a]`, sending an element of the algebra to its class
in the GNS Hilbert space. -/
noncomputable def gnsMk : A →ₗ[ℂ] 𝓗[ω] :=
  (toComplₗᵢ : ω.toPositiveLinearMap.PreGNS →ₗᵢ[ℂ] 𝓗[ω]).toLinearMap ∘ₗ
    ω.toPositiveLinearMap.toPreGNS.toLinearMap

lemma gnsMk_apply (a : A) : ω.gnsMk a = (ω.toPositiveLinearMap.toPreGNS a : 𝓗[ω]) := rfl

lemma gnsMk_ofPreGNS (x : ω.toPositiveLinearMap.PreGNS) :
    ω.gnsMk (ω.toPositiveLinearMap.ofPreGNS x) = (x : 𝓗[ω]) := rfl

/-- The classes `[a]` are dense in `𝓗[ω]`. -/
lemma denseRange_gnsMk : DenseRange ω.gnsMk :=
  denseRange_coe.comp ω.toPositiveLinearMap.toPreGNS.surjective.denseRange (continuous_coe _)

/-- `⟪[a], [b]⟫ = ω (a* b)`. -/
lemma inner_gnsMk (a b : A) : ⟪ω.gnsMk a, ω.gnsMk b⟫_ℂ = ω (star a * b) := by
  rw [gnsMk_apply, gnsMk_apply, inner_coe, preGNS_inner_def]
  simp

/-- `‖[a]‖² = Re ω (a* a)`. -/
lemma norm_gnsMk_sq (a : A) : ‖ω.gnsMk a‖ ^ 2 = (ω (star a * a)).re := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_gnsMk]
  rfl

/-- `‖[a]‖ ≤ ‖a‖`. -/
lemma norm_gnsMk_le (a : A) : ‖ω.gnsMk a‖ ≤ ‖a‖ := by
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero, norm_gnsMk_sq]
  calc (ω (star a * a)).re
      ≤ ‖ω (star a * a)‖ := Complex.re_le_norm _
    _ ≤ ‖star a * a‖ := ω.norm_apply_le _
    _ ≤ ‖a‖ ^ 2 := by simpa [sq, norm_star] using norm_mul_le (star a) a

/-- `π[ω] a [b] = [a b]`. -/
@[simp] lemma gnsRep_apply_gnsMk (a b : A) : π[ω] a (ω.gnsMk b) = ω.gnsMk (a * b) := by
  simp [gnsRep, gnsMk_apply]

/-- `π[ω] (a*) = (π[ω] a)†`. -/
lemma gnsRep_star (a : A) : (π[ω] a)† = π[ω] (star a) := by
  rw [map_star, ContinuousLinearMap.star_eq_adjoint]

/-- The GNS representation is contractive: `‖π[ω] a‖ ≤ ‖a‖`. -/
lemma norm_gnsRep_le (a : A) : ‖π[ω] a‖ ≤ ‖a‖ :=
  NonUnitalStarAlgHom.norm_apply_le _ a

/-! ### The cyclic vector -/

/-- The bounded functional `[a] ↦ ω a` on the pre-Hilbert space of the GNS construction; its
operator norm is at most `1`. -/
noncomputable def gnsFunctional₀ : ω.toPositiveLinearMap.PreGNS →L[ℂ] ℂ :=
  (ω.toLinearMap ∘ₗ ω.toPositiveLinearMap.ofPreGNS.toLinearMap).mkContinuous 1 fun x => by
    have hx : ‖x‖ ^ 2 =
        (ω (star (ω.toPositiveLinearMap.ofPreGNS x) * ω.toPositiveLinearMap.ofPreGNS x)).re := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), preGNS_inner_def]
      rfl
    rw [one_mul, ← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero, hx]
    exact ω.norm_apply_sq_le _

lemma gnsFunctional₀_apply (x : ω.toPositiveLinearMap.PreGNS) :
    ω.gnsFunctional₀ x = ω (ω.toPositiveLinearMap.ofPreGNS x) := rfl

/-- The bounded functional `𝓗[ω] →L[ℂ] ℂ` extending `[a] ↦ ω a` by continuity. -/
noncomputable def gnsFunctional : 𝓗[ω] →L[ℂ] ℂ :=
  ω.gnsFunctional₀.extend (toComplL : ω.toPositiveLinearMap.PreGNS →L[ℂ] 𝓗[ω])

lemma gnsFunctional_coe (x : ω.toPositiveLinearMap.PreGNS) :
    ω.gnsFunctional x = ω (ω.toPositiveLinearMap.ofPreGNS x) :=
  ContinuousLinearMap.extend_eq _ denseRange_coe (isUniformInducing_coe _) x

@[simp] lemma gnsFunctional_gnsMk (a : A) : ω.gnsFunctional (ω.gnsMk a) = ω a :=
  ω.gnsFunctional_coe _

/-- The GNS functional has operator norm `1`. -/
lemma norm_gnsFunctional : ‖ω.gnsFunctional‖ = 1 := by
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_) ?_
  · induction x using Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih x =>
      rw [gnsFunctional_coe, one_mul, norm_coe]
      simpa [gnsFunctional₀_apply] using ω.gnsFunctional₀.le_of_opNorm_le
        (LinearMap.mkContinuous_norm_le _ zero_le_one _) x
  · rw [← ω.norm_toContinuousLinearMap]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg ω.gnsFunctional) fun a => ?_
    calc ‖ω.toContinuousLinearMap a‖
        = ‖ω.gnsFunctional (ω.gnsMk a)‖ := by simp
      _ ≤ ‖ω.gnsFunctional‖ * ‖ω.gnsMk a‖ := ω.gnsFunctional.le_opNorm _
      _ ≤ ‖ω.gnsFunctional‖ * ‖a‖ := by gcongr; exact ω.norm_gnsMk_le a

/-- The cyclic vector `ξ[ω] ∈ 𝓗[ω]`: the Riesz representative of the functional `[a] ↦ ω a`. -/
noncomputable def gnsVector : 𝓗[ω] := (InnerProductSpace.toDual ℂ 𝓗[ω]).symm ω.gnsFunctional

/-- Notation `ξ[ω]` for the cyclic vector `State.gnsVector ω`. -/
scoped[GNS] notation:max "ξ[" ω "]" => State.gnsVector ω

/-- Riesz identification: `⟪ξ[ω], x⟫` is the GNS functional. -/
lemma inner_gnsVector (x : 𝓗[ω]) : ⟪ξ[ω], x⟫_ℂ = ω.gnsFunctional x :=
  InnerProductSpace.toDual_symm_apply

/-- `⟪ξ[ω], [a]⟫ = ω a`. -/
@[simp] lemma inner_gnsVector_gnsMk (a : A) : ⟪ξ[ω], ω.gnsMk a⟫_ℂ = ω a := by
  rw [inner_gnsVector, gnsFunctional_gnsMk]

/-- The fundamental identity `π[ω] a ξ[ω] = [a]`. -/
@[simp] lemma gnsRep_apply_gnsVector (a : A) : π[ω] a ξ[ω] = ω.gnsMk a := by
  refine ext_inner_right ℂ fun x => ?_
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x =>
    rw [← gnsMk_ofPreGNS, ← ContinuousLinearMap.adjoint_inner_right, gnsRep_star,
      gnsRep_apply_gnsMk, inner_gnsVector_gnsMk, inner_gnsMk]

/-- Cyclicity of `ξ[ω]`: the span of `{π[ω] a ξ[ω] | a : A}` is dense in `𝓗[ω]`. -/
lemma gnsVector_cyclic : Dense (↑(Submodule.span ℂ {π[ω] a ξ[ω] | a : A}) : Set 𝓗[ω]) :=
  ω.denseRange_gnsMk.mono <| Set.range_subset_iff.mpr fun a =>
    Submodule.subset_span ⟨a, ω.gnsRep_apply_gnsVector a⟩

/-- The GNS identity `ω a = ⟪ξ[ω], π[ω] a ξ[ω]⟫`. -/
lemma gns_condition (a : A) : ω a = ⟪ξ[ω], π[ω] a ξ[ω]⟫_ℂ := by simp

/-- Normalisation of the cyclic vector: `‖ξ[ω]‖ = 1`. -/
lemma norm_gnsVector : ‖ξ[ω]‖ = 1 := by
  rw [gnsVector, LinearIsometryEquiv.norm_map, norm_gnsFunctional]

lemma gnsVector_ne_zero : ξ[ω] ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_gnsVector]
  exact one_ne_zero

/-! ### Faithful states -/

/-- `[a] = 0` in `𝓗[ω]` iff `ω (a* a) = 0`. -/
lemma gnsMk_eq_zero_iff (a : A) : ω.gnsMk a = 0 ↔ ω (star a * a) = 0 := by
  rw [← norm_eq_zero, ← pow_eq_zero_iff two_ne_zero, norm_gnsMk_sq, ← Complex.ofReal_eq_zero,
    ω.ofReal_re_apply_star_mul_self]

/-- A state is faithful iff the canonical map `a ↦ [a]` into `𝓗[ω]` is injective. -/
theorem isFaithful_iff_injective_gnsMk : ω.IsFaithful ↔ Function.Injective ω.gnsMk := by
  rw [injective_iff_map_eq_zero]
  simp only [gnsMk_eq_zero_iff]
  rfl

/-- A state is faithful iff the cyclic vector separates the algebra, i.e. `a ↦ π[ω] a ξ[ω]` is
injective. -/
theorem isFaithful_iff_separating :
    ω.IsFaithful ↔ Function.Injective fun a : A => π[ω] a ξ[ω] := by
  simp only [gnsRep_apply_gnsVector]
  exact ω.isFaithful_iff_injective_gnsMk

/-- The GNS representation of a faithful state is injective. -/
lemma IsFaithful.injective_gnsRep (hω : ω.IsFaithful) : Function.Injective π[ω] :=
  fun a b hab => ω.isFaithful_iff_separating.mp hω (by simp only [hab])

end State
