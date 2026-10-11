/-
Copyright (c) 2025 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM

/-!
# Strong operator topology: closedness of commutants and strong sums

This file shows that commutants (`Set.centralizer`) and double commutants are closed in the
strong operator topology (SOT), and characterises strong sums of operators pointwise.

The strong operator topology on `B(H) = H →L[ℂ] H` is the topology of pointwise convergence
in the norm topology: a net `T_α → T` in SOT iff `∀ x, T_α x → T x` in norm. Mathlib already
provides this topology as `PointwiseConvergenceCLM` (notation `H →Lₚₜ[ℂ] H`), a type copy of
`H →L[ℂ] H` carrying the topology of uniform convergence on finite sets. Operators are carried
into it by Mathlib's continuous linear map `ContinuousLinearMap.toPointwiseConvergenceCLM`
(abbreviated `ContinuousLinearMap.toSOT` and written `↑ₚₜ`), and back by the inverse of the linear
equivalence `ContinuousLinearMap.toUniformConvergenceCLM`; this file uses that type copy and these
identifications rather than introducing another one.

## Main definitions

* `Set.toSOT`: view a subset of operators inside the SOT type-copy, as its preimage under the
  inverse of `ContinuousLinearMap.toUniformConvergenceCLM`. Every result about SOT-closedness is
  stated in this preimage form.
* `IsSOTClosed`: a predicate for subsets closed in the SOT.
* `ContinuousLinearMap.toSOT`: Mathlib's embedding `ContinuousLinearMap.toPointwiseConvergenceCLM`
  into the SOT type copy, with its arguments implicit, written `↑ₚₜ`.

## Main results

* `isSOTClosed_centralizer`: the commutant of any set is SOT-closed.
* `isSOTClosed_centralizer_centralizer`: double commutants are SOT-closed.
* `PointwiseConvergenceCLM.hasSum_iff_forall_hasSum`: a series of operators converges in the
  topology of pointwise convergence iff it converges at every vector;
  `PointwiseConvergenceCLM.hasSum_toSOT_iff` — the same for operators carried over by
  `ContinuousLinearMap.toSOT`. This is how a strong sum `∑ᵢ Tᵢ = T` is stated, as
  `HasSum (fun i => ↑ₚₜ (T i)) (↑ₚₜ T)` in `H →Lₚₜ[ℂ] H`, and evaluated at vectors.

Left and right multiplication by a fixed operator are SOT-continuous; they are Mathlib's
`PointwiseConvergenceCLM.postcomp` and `PointwiseConvergenceCLM.precomp`, which are already
bundled as continuous linear maps, so this file uses them directly.

## Notation

| Symbol | Expansion | How to activate |
|---|---|---|
| `↑ₚₜ T` | `ContinuousLinearMap.toSOT T` | `open scoped StrongOperatorTopology` |

`↑ₚₜ` is the embedding itself, so it is applied like a function: `↑ₚₜ T`, `↑ₚₜ (T i)`.

The comparison with the weak operator topology — SOT is finer than WOT, so every WOT-closed set
is SOT-closed (`continuous_sotToWOT`, `isSOTClosed_of_isWOTClosed`) — lives in
`QuantumSystem.Analysis.VonNeumannAlgebra.DoubleCommutant.SOTClosedSubalgebra`, the first file that may import
both type copies: this file, like every `ForMathlib` file, imports Mathlib only.
-/

@[expose] public section

namespace PointwiseConvergenceCLM

variable {ι 𝕜₁ 𝕜₂ E F : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂}
  [AddCommGroup E] [TopologicalSpace E] [Module 𝕜₁ E]
  [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F] [Module 𝕜₂ F]

/-- In the topology of pointwise convergence, `∑ᵢ fᵢ = a` iff `∑ᵢ fᵢ x = a x` for every `x`. -/
lemma hasSum_iff_forall_hasSum {f : ι → E →SLₚₜ[σ] F} {a : E →SLₚₜ[σ] F} :
    HasSum f a ↔ ∀ x, HasSum (fun i => f i x) (a x) := by
  simp only [HasSum, tendsto_iff_forall_tendsto, sum_apply]

variable [ContinuousSMul 𝕜₁ E] [ContinuousConstSMul 𝕜₂ F]

/-- The embedding `E →SL[σ] F → E →SLₚₜ[σ] F` of continuous linear maps into the type copy carrying
the topology of pointwise convergence (for `E = F = H` a Hilbert space, the strong operator
topology): Mathlib's `ContinuousLinearMap.toPointwiseConvergenceCLM`, with its scalar field, ring
homomorphism and spaces implicit. It is a reducible abbreviation, so every Mathlib lemma about
`ContinuousLinearMap.toPointwiseConvergenceCLM` applies to it; it exists so that the notation
`↑ₚₜ` (`open scoped StrongOperatorTopology`) is displayed in goals. -/
abbrev _root_.ContinuousLinearMap.toSOT : (E →SL[σ] F) →L[𝕜₂] E →SLₚₜ[σ] F :=
  ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜₂ σ E F

/-- `↑ₚₜ T` is the continuous linear map `T`, viewed in the type copy `E →SLₚₜ[σ] F` carrying the
topology of pointwise convergence (`ContinuousLinearMap.toSOT`). -/
scoped[StrongOperatorTopology] notation:max "↑ₚₜ" => ContinuousLinearMap.toSOT

open scoped StrongOperatorTopology

/-- A family of continuous linear maps, viewed in the topology of pointwise convergence through
`ContinuousLinearMap.toSOT`, sums to `a` iff `∑ᵢ fᵢ x = a x` for every `x`. -/
lemma hasSum_toSOT_iff {f : ι → E →SL[σ] F} {a : E →SL[σ] F} :
    HasSum (fun i => ↑ₚₜ (f i)) (↑ₚₜ a) ↔ ∀ x, HasSum (fun i => f i x) (a x) :=
  hasSum_iff_forall_hasSum

end PointwiseConvergenceCLM

namespace StrongOperatorTopology

open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

local notation "B" => (H →L[ℂ] H)
local notation "BSOT" => (H →Lₚₜ[ℂ] H)

open ContinuousLinearMap (toUniformConvergenceCLM)

/-- View a subset of operators inside the SOT type-copy, as its preimage under the inverse of
`ContinuousLinearMap.toUniformConvergenceCLM`. -/
def Set.toSOT (S : Set B) : Set BSOT :=
  (toUniformConvergenceCLM _ _ _).symm ⁻¹' S

/-- `T` lies in the SOT copy of `S` exactly when its underlying operator lies in `S`. -/
lemma Set.mem_toSOT_iff {S : Set B} {T : BSOT} :
    T ∈ Set.toSOT (H := H) S ↔ (toUniformConvergenceCLM _ _ _).symm T ∈ S :=
  Iff.rfl

/-- A subset of `B(H)` is SOT-closed if its copy `Set.toSOT S` in the SOT type-copy is closed. -/
def IsSOTClosed (S : Set B) : Prop :=
  IsClosed (Set.toSOT (H := H) S)

/-- The commutant `Set.centralizer S` is SOT-closed. -/
lemma isSOTClosed_centralizer (S : Set B) : IsSOTClosed (H := H) (Set.centralizer S) := by
  -- Express the commutant as an intersection of commuting constraints, each closed because
  -- left and right multiplication are SOT-continuous.
  have key : Set.toSOT (H := H) (Set.centralizer S) =
      ⋂ a ∈ S, {T : BSOT | PointwiseConvergenceCLM.postcomp H a T
        = PointwiseConvergenceCLM.precomp H a T} := by
    ext T
    simp only [Set.mem_toSOT_iff, Set.mem_centralizer_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · intro hT a ha
      ext x
      exact congrArg (fun R => R x) (hT a ha)
    · intro hT a ha
      ext x
      exact congrArg (fun R => R x) (hT a ha)
  rw [IsSOTClosed, key]
  exact isClosed_biInter fun a _ =>
    isClosed_eq (PointwiseConvergenceCLM.postcomp H a).continuous
      (PointwiseConvergenceCLM.precomp H a).continuous

/-- Any double commutant is SOT-closed. -/
lemma isSOTClosed_centralizer_centralizer (S : Set B) :
    IsSOTClosed (H := H) (Set.centralizer (Set.centralizer S)) :=
  isSOTClosed_centralizer (H := H) (S := Set.centralizer S)

end StrongOperatorTopology
