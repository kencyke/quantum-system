module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.WeakOperatorTopology

@[expose] public section

/-!
# Strong operator topology closedness of commutants

This file provides SOT-continuity of left/right multiplication by a fixed bounded operator,
consequently showing that commutants (`Set.centralizer`) and double commutants are SOT-closed.

The strong operator topology (SOT) on `B(H) = H →L[ℂ] H` is the topology of pointwise convergence
in the norm topology: a net `T_α → T` in SOT iff `∀ x, T_α x → T x` in norm.

## Main definitions

* `ContinuousLinearMapSOT`: type copy of `H →L[ℂ] H` equipped with the SOT.
* `ContinuousLinearMapSOT.inducingFn`: the inducing function for SOT (evaluation at all points).
* `leftMulSOT`, `rightMulSOT`: left/right multiplication on the SOT type-copy.
* `IsSOTClosed`: a predicate for subsets closed in the SOT.
* `Set.toSOT`: view a subset of operators inside the SOT type-copy.

## Main results

* `continuous_leftMulSOT`, `continuous_rightMulSOT`: multiplication by a fixed operator is
  SOT-continuous.
* `isSOTClosed_centralizer`: the commutant of any set is SOT-closed.
* `isSOTClosed_centralizer_centralizer`: double commutants are SOT-closed.

## Comparison with WOT

SOT is finer than WOT: SOT convergence implies WOT convergence. This file does not develop the
SOT→WOT comparison map; it is imported/used elsewhere when relating SOT-closedness to
WOT-closedness for *-subalgebras.
-/

namespace StrongOperatorTopology

open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

local notation "B" => (H →L[ℂ] H)

/-- Type copy of `H →L[ℂ] H` equipped with the strong operator topology (pointwise norm convergence). -/
@[ext]
structure ContinuousLinearMapSOT (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The underlying continuous linear map. -/
  toCLM : H →L[ℂ] H

local notation "BSOT" => ContinuousLinearMapSOT H

namespace ContinuousLinearMapSOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Coercion from `BSOT` back to `B`. -/
instance : Coe (ContinuousLinearMapSOT H) (H →L[ℂ] H) := ⟨toCLM⟩

/-- Coercion from `BSOT` to a function `H → H`. -/
instance : CoeFun (ContinuousLinearMapSOT H) (fun _ => H → H) := ⟨fun T x => T.toCLM x⟩

/-- Addition on `BSOT`. -/
instance : Add (ContinuousLinearMapSOT H) := ⟨fun T S => ⟨T.toCLM + S.toCLM⟩⟩

/-- Scalar multiplication on `BSOT`. -/
instance : SMul ℂ (ContinuousLinearMapSOT H) := ⟨fun c T => ⟨c • T.toCLM⟩⟩

/-- Zero element on `BSOT`. -/
instance : Zero (ContinuousLinearMapSOT H) := ⟨⟨0⟩⟩

@[simp] lemma add_toCLM (T S : ContinuousLinearMapSOT H) : (T + S).toCLM = T.toCLM + S.toCLM := rfl
@[simp] lemma smul_toCLM (c : ℂ) (T : ContinuousLinearMapSOT H) : (c • T).toCLM = c • T.toCLM := rfl
@[simp] lemma zero_toCLM : (0 : ContinuousLinearMapSOT H).toCLM = 0 := rfl
@[simp] lemma mk_toCLM (T : H →L[ℂ] H) : (ContinuousLinearMapSOT.mk T).toCLM = T := rfl

/-- The inducing function for SOT: evaluation at all points. -/
def inducingFn : ContinuousLinearMapSOT H → (H → H) := fun T x => T x

/-- The SOT on `BSOT` is the initial topology induced by pointwise evaluation. -/
instance : TopologicalSpace (ContinuousLinearMapSOT H) :=
  TopologicalSpace.induced inducingFn Pi.topologicalSpace

/-- The SOT is induced by `inducingFn`. -/
lemma isInducing_inducingFn :
    Topology.IsInducing (inducingFn (H := H)) :=
  ⟨rfl⟩

/-- `inducingFn` is injective. -/
lemma inducingFn_injective : Function.Injective (inducingFn (H := H)) := by
  intro T S h
  ext x
  exact congrFun h x

/-- The SOT on `B(H)` is T2 (Hausdorff) since it embeds into a product of T2 spaces. -/
instance : T2Space (ContinuousLinearMapSOT H) := by
  have hemb : Topology.IsEmbedding (inducingFn (H := H)) :=
    ⟨isInducing_inducingFn (H := H), inducingFn_injective (H := H)⟩
  exact hemb.t2Space

/-- Evaluation at a point `x` is SOT-continuous. -/
lemma continuous_eval (x : H) : Continuous (fun T : ContinuousLinearMapSOT H => T x) := by
  have : (fun T : ContinuousLinearMapSOT H => T x) = (fun f : H → H => f x) ∘ inducingFn := rfl
  rw [this]
  exact (continuous_apply x).comp (isInducing_inducingFn (H := H)).continuous

/-- Characterization of SOT-continuity: a map is SOT-continuous iff all pointwise evaluations are. -/
lemma continuous_of_forall_eval_continuous {g : ContinuousLinearMapSOT H → ContinuousLinearMapSOT H}
    (h : ∀ x : H, Continuous (fun T => g T x)) : Continuous g := by
  rw [continuous_induced_rng]
  exact continuous_pi h

end ContinuousLinearMapSOT

open ContinuousLinearMapSOT in
/-- A subset of `B(H)` is SOT-closed if its image in `BSOT` is closed. -/
def IsSOTClosed (S : Set B) : Prop :=
  IsClosed {T : BSOT | T.toCLM ∈ S}

/-- View a subset of operators inside the SOT type-copy. -/
def Set.toSOT (S : Set B) : Set BSOT :=
  {T | T.toCLM ∈ S}

lemma Set.mem_toSOT_iff {S : Set B} {T : BSOT} :
    T ∈ Set.toSOT (H := H) S ↔ T.toCLM ∈ S := Iff.rfl

/-- Left multiplication on `BSOT`. -/
def leftMulSOT (a : B) : BSOT → BSOT :=
  fun T => ⟨a * T.toCLM⟩

/-- Right multiplication on `BSOT`. -/
def rightMulSOT (a : B) : BSOT → BSOT :=
  fun T => ⟨T.toCLM * a⟩

@[simp] lemma leftMulSOT_apply (a : B) (T : BSOT) (x : H) :
    (leftMulSOT (H := H) a T) x = a (T x) := by
  simp [leftMulSOT, ContinuousLinearMap.mul_apply]

@[simp] lemma rightMulSOT_apply (a : B) (T : BSOT) (x : H) :
    (rightMulSOT (H := H) a T) x = T (a x) := by
  simp [rightMulSOT, ContinuousLinearMap.mul_apply]

/-- Left multiplication by a fixed operator is SOT-continuous. -/
lemma continuous_leftMulSOT (a : B) : Continuous (leftMulSOT (H := H) a) := by
  refine ContinuousLinearMapSOT.continuous_of_forall_eval_continuous (H := H) ?_
  intro x
  have : (fun T : BSOT => (leftMulSOT (H := H) a T) x) = (fun y => a y) ∘ (fun T => T x) := by
    ext T
    simp
  rw [this]
  exact a.continuous.comp (ContinuousLinearMapSOT.continuous_eval (H := H) x)

/-- Right multiplication by a fixed operator is SOT-continuous. -/
lemma continuous_rightMulSOT (a : B) : Continuous (rightMulSOT (H := H) a) := by
  refine ContinuousLinearMapSOT.continuous_of_forall_eval_continuous (H := H) ?_
  intro x
  have : (fun T : BSOT => (rightMulSOT (H := H) a T) x) = (fun T => T (a x)) := by
    ext T
    simp
  rw [this]
  exact ContinuousLinearMapSOT.continuous_eval (H := H) (a x)

/-- The set of operators (in BSOT) commuting with a fixed operator `a` is closed. -/
lemma isClosed_commutesWithSOT (a : B) :
    IsClosed {T : BSOT | leftMulSOT (H := H) a T = rightMulSOT (H := H) a T} :=
  isClosed_eq (continuous_leftMulSOT (H := H) a) (continuous_rightMulSOT (H := H) a)


/-- The commutant `Set.centralizer S` is SOT-closed. -/
lemma isSOTClosed_centralizer (S : Set B) : IsSOTClosed (H := H) (Set.centralizer S) := by
  unfold IsSOTClosed
  -- Rewrite the SOT-image of the centralizer as an intersection.
  have : {T : BSOT | T.toCLM ∈ Set.centralizer S} =
      ⋂ a : B, ⋂ _ : a ∈ S, {T : BSOT | leftMulSOT (H := H) a T = rightMulSOT (H := H) a T} := by
    ext T
    constructor
    · intro hT
      refine Set.mem_iInter.2 ?_
      intro a
      refine Set.mem_iInter.2 ?_
      intro ha
      have hcomm : a * T.toCLM = T.toCLM * a := Set.mem_centralizer_iff.mp hT a ha
      simp only [Set.mem_setOf_eq, leftMulSOT, rightMulSOT]
      ext x
      simp [ContinuousLinearMap.mul_apply, hcomm]
    · intro hT
      refine Set.mem_centralizer_iff.mpr ?_
      intro a ha
      have h := Set.mem_iInter.1 (Set.mem_iInter.1 hT a) ha
      simp only [Set.mem_setOf_eq, leftMulSOT, rightMulSOT] at h
      have := congrArg ContinuousLinearMapSOT.toCLM h
      simpa using this
  rw [this]
  refine isClosed_iInter ?_
  intro a
  refine isClosed_iInter ?_
  intro _
  exact isClosed_commutesWithSOT (H := H) a

/-- Any double commutant is SOT-closed. -/
theorem isSOTClosed_centralizer_centralizer (S : Set B) :
    IsSOTClosed (H := H) (Set.centralizer (Set.centralizer S)) :=
  isSOTClosed_centralizer (H := H) (S := Set.centralizer S)

end StrongOperatorTopology
