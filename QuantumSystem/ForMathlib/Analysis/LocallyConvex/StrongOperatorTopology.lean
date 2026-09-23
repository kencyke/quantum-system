module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM

@[expose] public section

/-!
# Strong operator topology closedness of commutants

This file shows that commutants (`Set.centralizer`) and double commutants are closed in the
strong operator topology (SOT).

The strong operator topology on `B(H) = H →L[ℂ] H` is the topology of pointwise convergence
in the norm topology: a net `T_α → T` in SOT iff `∀ x, T_α x → T x` in norm. Mathlib already
provides this topology as `PointwiseConvergenceCLM` (notation `H →SLₚₜ[RingHom.id ℂ] H`), a type
copy of `H →L[ℂ] H` carrying the topology of uniform convergence on finite sets; this file uses
that type copy rather than introducing another one.

## Main definitions

* `toSOTEquiv`: the linear equivalence from `B(H)` to the SOT type-copy.
* `Set.toSOT`: view a subset of operators inside the SOT type-copy.
* `IsSOTClosed`: a predicate for subsets closed in the SOT.

## Main results

* `Set.toSOT_eq_image`: `Set.toSOT` is the image of the subset under `toSOTEquiv`.
* `isSOTClosed_centralizer`: the commutant of any set is SOT-closed.
* `isSOTClosed_centralizer_centralizer`: double commutants are SOT-closed.

Left and right multiplication by a fixed operator are SOT-continuous; they are Mathlib's
`PointwiseConvergenceCLM.postcomp` and `PointwiseConvergenceCLM.precomp`, which are already
bundled as continuous linear maps, so this file uses them directly.

The comparison with the weak operator topology — SOT is finer than WOT, so every WOT-closed set
is SOT-closed (`continuous_sotToWOT`, `isSOTClosed_of_isWOTClosed`) — lives in
`QuantumSystem.Algebra.Star.DoubleCommutant.SOTClosedSubAlgebra`, the first file that may import
both type copies: this file, like every `ForMathlib` file, imports Mathlib only.
-/

namespace StrongOperatorTopology

open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

local notation "B" => (H →L[ℂ] H)
local notation "BSOT" => (H →SLₚₜ[RingHom.id ℂ] H)

/-- The linear equivalence from `B(H)` to the SOT type-copy. It is the identity on the underlying
operators; only the topology differs. -/
noncomputable def toSOTEquiv : B ≃ₗ[ℂ] BSOT := LinearEquiv.refl ℂ (H →L[ℂ] H)

@[simp] lemma toSOTEquiv_apply (T : B) (x : H) : (toSOTEquiv (H := H) T) x = T x := rfl

@[simp] lemma toSOTEquiv_symm_apply (T : BSOT) (x : H) :
    ((toSOTEquiv (H := H)).symm T) x = T x := rfl

/-- View a subset of operators inside the SOT type-copy. -/
def Set.toSOT (S : Set B) : Set BSOT :=
  {T | (toSOTEquiv (H := H)).symm T ∈ S}

lemma Set.mem_toSOT_iff {S : Set B} {T : BSOT} :
    T ∈ Set.toSOT (H := H) S ↔ (toSOTEquiv (H := H)).symm T ∈ S :=
  Iff.rfl

/-- `Set.toSOT` is the image of the subset under `toSOTEquiv`. -/
lemma Set.toSOT_eq_image (S : Set B) :
    Set.toSOT (H := H) S = (toSOTEquiv (H := H)) '' S := by
  ext T
  constructor
  · intro h
    exact ⟨_, h, (toSOTEquiv (H := H)).apply_symm_apply T⟩
  · rintro ⟨x, hx, rfl⟩
    simpa [Set.mem_toSOT_iff] using hx

/-- A subset of `B(H)` is SOT-closed if its image in the SOT type-copy is closed. -/
def IsSOTClosed (S : Set B) : Prop :=
  IsClosed (Set.toSOT (H := H) S)

/-- SOT-closedness stated as closedness of the image, the form in which the strong operator
topology is usually phrased. -/
lemma isSOTClosed_iff_isClosed_image (S : Set B) :
    IsSOTClosed (H := H) S ↔
      IsClosed (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H '' S) := by
  rw [IsSOTClosed, Set.toSOT_eq_image]
  rfl

/-- The commutant `Set.centralizer S` is SOT-closed. -/
lemma isSOTClosed_centralizer (S : Set B) : IsSOTClosed (H := H) (Set.centralizer S) := by
  -- Express the commutant as an intersection of commuting constraints, each closed because
  -- left and right multiplication are SOT-continuous.
  have key : Set.toSOT (H := H) (Set.centralizer S) =
      ⋂ a ∈ S, {T : BSOT | PointwiseConvergenceCLM.postcomp H a T
        = PointwiseConvergenceCLM.precomp H a T} := by
    ext T
    simp only [Set.mem_toSOT_iff, Set.mem_centralizer_iff, Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro hT a ha
      ext x
      simpa [ContinuousLinearMap.mul_apply] using congrArg (fun R => R x) (hT a ha)
    · intro hT a ha
      ext x
      simpa [ContinuousLinearMap.mul_apply] using congrArg (fun R => R x) (hT a ha)
  rw [IsSOTClosed, key]
  exact isClosed_biInter fun a _ =>
    isClosed_eq (PointwiseConvergenceCLM.postcomp H a).continuous
      (PointwiseConvergenceCLM.precomp H a).continuous

/-- Any double commutant is SOT-closed. -/
theorem isSOTClosed_centralizer_centralizer (S : Set B) :
    IsSOTClosed (H := H) (Set.centralizer (Set.centralizer S)) :=
  isSOTClosed_centralizer (H := H) (S := Set.centralizer S)

end StrongOperatorTopology
