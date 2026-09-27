/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.MeasureTheory.Measure.Complex
public import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM

/-!
# Projection-valued measures

A **projection-valued measure** (a *resolution of the identity*, Rudin, *Functional Analysis*,
Definition 12.17) on a measurable space `X` with values in the bounded operators on a complex
Hilbert space `H` is a countably additive map `E` from the measurable sets of `X` to the orthogonal
projections on `H` with `E X = 1`. No regularity is imposed, as befits a general σ-algebra.

Countable additivity is taken in the strong operator topology: `E` is a Mathlib
`VectorMeasure X (H →Lₚₜ[ℂ] H)`, valued in the type copy of `H →L[ℂ] H` carrying the topology of
pointwise convergence. It cannot be taken in the norm topology, in which a projection-valued
measure is not countably additive in general (the projections onto the coordinate axes of `ℓ²` do
not sum in norm). Rudin requires weak countable additivity instead; for projection-valued maps the
two are equivalent, since finitely additive projection-valued maps take orthogonal values on
disjoint sets. The values are read back in `H →L[ℂ] H` through Mathlib's
`ContinuousLinearMap.toUniformConvergenceCLM`, the identity map between the two copies; the
coercion `E s : H →L[ℂ] H` does this. As for every vector measure, `E s = 0` when `s` is not
measurable.

Rudin's axiom `E (s ∩ t) = E s E t` is not a field: it follows from finite additivity, because
projections `P`, `Q` with `P + Q` a projection are orthogonal
(`MeasureTheory.ProjectionValuedMeasure.apply_inter`).

The complex measures follow Mathlib's convention for inner products, conjugate-linear in the first
argument: `E.complexMeasure x y s = ⟪x, E s y⟫`, which is Rudin's `E_{y,x}(s) = (E(s) y, x)`.

## Main definitions

* `MeasureTheory.ProjectionValuedMeasure X H` — projection-valued measures on `X` acting on `H`.
* `MeasureTheory.ProjectionValuedMeasure.ofHasSum` — a projection-valued measure from a map to
  `H →L[ℂ] H` that is countably additive at every vector.
* `MeasureTheory.ProjectionValuedMeasure.dirac a` — the projection-valued measure concentrated at
  `a`, `s ↦ 1` if `a ∈ s` and `0` otherwise.
* `MeasureTheory.ProjectionValuedMeasure.measure E x` — the finite measure `s ↦ ‖E s x‖²`, i.e.
  `⟪x, E(·) x⟫`.
* `MeasureTheory.ProjectionValuedMeasure.complexMeasure E x y` — the complex measure
  `s ↦ ⟪x, E s y⟫`.
* `MeasureTheory.ProjectionValuedMeasure.map E f hf` — the image of `E` under a measurable map `f`,
  with `(E.map f) s = E (f ⁻¹' s)` for measurable `s`.

## Main results

* `MeasureTheory.ProjectionValuedMeasure.apply_union`, `apply_univ`, `apply_empty` — finite
  additivity and normalisation.
* `MeasureTheory.ProjectionValuedMeasure.mul_eq_zero_of_disjoint`,
  `MeasureTheory.ProjectionValuedMeasure.apply_inter` — the projections of disjoint sets are
  orthogonal, and `E (s ∩ t) = E s E t`.
* `MeasureTheory.ProjectionValuedMeasure.hasSum_apply` — strong countable additivity,
  `E (⋃ sᵢ) x = Σ E sᵢ x` for pairwise disjoint measurable `sᵢ`.
* `MeasureTheory.ProjectionValuedMeasure.commute`, `mono` — the projections commute and increase
  with the set.
* `MeasureTheory.ProjectionValuedMeasure.measure_apply`, `measure_univ` — `E.measure x s =
  ‖E s x‖²`, of total mass `‖x‖²`; `measure_smul` — `E.measure (a • x) = |a|² E.measure x`;
  `measure_apply_eq_restrict` — `E.measure (E s x)` is `E.measure x` restricted to `s`;
  `measure_add_apply_of_disjoint` — orthogonal splitting over disjoint sets.
* `MeasureTheory.ProjectionValuedMeasure.re_complexMeasure_self`, `im_complexMeasure_self` — on the
  diagonal, `E.complexMeasure x x` is the diagonal measure `E.measure x`.
* `MeasureTheory.ProjectionValuedMeasure.apply_eq_zero_iff` — `E s = 0` iff every diagonal measure
  vanishes on `s`.
* `MeasureTheory.ProjectionValuedMeasure.ext_of_measure` — a projection-valued measure is determined
  by its diagonal measures `E.measure x`.
-/

@[expose] public section

open Set Filter Function Topology ContinuousLinearMap
open scoped ENNReal InnerProductSpace

section StarProjection

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- For an orthogonal projection `P`, `⟪x, P x⟫ = ‖P x‖²`. -/
lemma IsStarProjection.inner_apply_self {P : H →L[ℂ] H} (hP : IsStarProjection P) (x : H) :
    ⟪x, P x⟫_ℂ = (‖P x‖ ^ 2 : ℝ) := by
  have hx : P (P x) = P x := by
    rw [← mul_apply_eq_comp, hP.isIdempotentElem.eq]
  calc ⟪x, P x⟫_ℂ = ⟪x, P (P x)⟫_ℂ := by rw [hx]
    _ = ⟪P x, P x⟫_ℂ := by
      rw [← adjoint_inner_left, ← star_eq_adjoint, hP.isSelfAdjoint.star_eq]
    _ = (‖P x‖ ^ 2 : ℝ) := by
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast

end StarProjection

namespace MeasureTheory

variable (X H : Type*) [MeasurableSpace X] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A **projection-valued measure** on `X` acting on `H`: a vector measure `E`, countably additive
in the strong operator topology, whose values `E s` are orthogonal projections, with `E X = 1`. -/
structure ProjectionValuedMeasure extends VectorMeasure X (H →Lₚₜ[ℂ] H) where
  /-- Every value is an orthogonal projection. -/
  isStarProjection' (s : Set X) :
    IsStarProjection ((toUniformConvergenceCLM (RingHom.id ℂ) H {T : Set H | Finite T}).symm
      (measureOf' s))
  /-- The whole space has the identity as projection. -/
  univ' : (toUniformConvergenceCLM (RingHom.id ℂ) H {T : Set H | Finite T}).symm (measureOf' univ) = 1

namespace ProjectionValuedMeasure

variable {X H}

/-- A projection-valued measure is read as a map from sets to operators on `H`. -/
noncomputable instance instFunLike : FunLike (ProjectionValuedMeasure X H) (Set X) (H →L[ℂ] H) where
  coe E s := (toUniformConvergenceCLM (RingHom.id ℂ) H {T : Set H | Finite T}).symm (E.measureOf' s)
  coe_injective E F h := by
    rcases E with ⟨⟨fE, _, _, _⟩, _, _⟩
    rcases F with ⟨⟨fF, _, _, _⟩, _, _⟩
    obtain rfl : fE = fF := funext fun s =>
      (toUniformConvergenceCLM (RingHom.id ℂ) H {T : Set H | Finite T}).symm.injective
        (congrFun h s)
    rfl

variable (E : ProjectionValuedMeasure X H) {s t : Set X}

/-- The value `E s`, read back in `H →L[ℂ] H` from the strong-operator-topology copy. -/
lemma coe_def (s : Set X) :
    E s = (toUniformConvergenceCLM (RingHom.id ℂ) H {T : Set H | Finite T}).symm
      (E.toVectorMeasure s) := rfl

/-- The underlying vector measure acts on vectors as `E s` does. -/
@[simp]
lemma toVectorMeasure_apply (s : Set X) (x : H) : E.toVectorMeasure s x = E s x := rfl

/-- Every value of a projection-valued measure is an orthogonal projection. -/
lemma isStarProjection (s : Set X) : IsStarProjection (E s) := E.isStarProjection' s

/-- The empty set has the zero projection. -/
@[simp]
lemma apply_empty : E ∅ = 0 := by
  rw [coe_def, E.toVectorMeasure.empty, map_zero]

/-- A non-measurable set has the zero projection. -/
lemma apply_of_not_measurableSet (hs : ¬MeasurableSet s) : E s = 0 := by
  rw [coe_def, E.toVectorMeasure.not_measurable hs, map_zero]

/-- The whole space has the identity as projection. -/
@[simp]
lemma apply_univ : E univ = 1 := E.univ'

/-- **Finite additivity**: `E (s ∪ t) = E s + E t` for disjoint measurable `s` and `t`. -/
lemma apply_union (hst : Disjoint s t) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    E (s ∪ t) = E s + E t := by
  rw [coe_def, E.toVectorMeasure.of_union hst hs ht, map_add]
  rfl

/-- **Strong countable additivity**: for pairwise disjoint measurable `sᵢ`,
`E (⋃ sᵢ) x = Σ E sᵢ x`. -/
lemma hasSum_apply {ι : Type*} [Countable ι] {f : ι → Set X} (hf : ∀ i, MeasurableSet (f i))
    (hd : Pairwise (Disjoint on f)) (x : H) : HasSum (fun i => E (f i) x) (E (⋃ i, f i) x) :=
  (E.toVectorMeasure.hasSum_of_disjoint_iUnion hf hd).mapL
    (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) H x)

/-- The projections of disjoint sets are orthogonal: `E s + E t = E (s ∪ t)` is a projection, and
projections with a projection as sum anticommute, hence have zero product. -/
lemma mul_eq_zero_of_disjoint (hst : Disjoint s t) : E s * E t = 0 := by
  by_cases hs : MeasurableSet s
  · by_cases ht : MeasurableSet t
    · let : Module ℚ (H →L[ℂ] H) := Module.compHom _ (algebraMap ℚ ℂ)
      have : IsAddTorsionFree (H →L[ℂ] H) := IsAddTorsionFree.of_module_rat _
      have h := (E.isStarProjection (s ∪ t)).isIdempotentElem
      rw [E.apply_union hst hs ht] at h
      have hs' := (E.isStarProjection s).isIdempotentElem
      exact hs'.mul_eq_zero_of_anticommute
        ((hs'.add_iff (E.isStarProjection t).isIdempotentElem).mp h)
    · rw [E.apply_of_not_measurableSet ht, mul_zero]
  · rw [E.apply_of_not_measurableSet hs, zero_mul]

/-- **Multiplicativity**: `E (s ∩ t) = E s E t` for measurable `s` and `t`. Writing
`E s = E (s \ t) + E (s ∩ t)` and `E t = E (t \ s) + E (s ∩ t)`, every cross term vanishes by
orthogonality. -/
lemma apply_inter (hs : MeasurableSet s) (ht : MeasurableSet t) : E (s ∩ t) = E s * E t := by
  have h₁ : E s = E (s \ t) + E (s ∩ t) := by
    rw [← E.apply_union disjoint_sdiff_inter (hs.diff ht) (hs.inter ht), sdiff_union_inter]
  have h₂ : E t = E (t \ s) + E (s ∩ t) := by
    rw [inter_comm, ← E.apply_union disjoint_sdiff_inter (ht.diff hs) (ht.inter hs),
      sdiff_union_inter]
  have hc : Disjoint (s ∩ t) (t \ s) := (disjoint_sdiff_inter (s := t) (t := s)).symm.mono_left
    (inter_comm s t).le
  rw [h₁, h₂, add_mul, mul_add, mul_add, E.mul_eq_zero_of_disjoint disjoint_sdiff_sdiff,
    E.mul_eq_zero_of_disjoint disjoint_sdiff_inter, E.mul_eq_zero_of_disjoint hc,
    (E.isStarProjection _).isIdempotentElem.eq, zero_add, zero_add, zero_add]

/-- The projections of a projection-valued measure commute. -/
lemma commute (s t : Set X) : Commute (E s) (E t) := by
  by_cases hs : MeasurableSet s
  · by_cases ht : MeasurableSet t
    · rw [Commute, SemiconjBy, ← E.apply_inter hs ht, ← E.apply_inter ht hs, inter_comm]
    · rw [E.apply_of_not_measurableSet ht]
      exact Commute.zero_right _
  · rw [E.apply_of_not_measurableSet hs]
    exact Commute.zero_left _

/-- A projection-valued measure is monotone. -/
lemma mono (ht : MeasurableSet t) (hst : s ⊆ t) : E s ≤ E t := by
  by_cases hs : MeasurableSet s
  · exact IsStarProjection.le_of_mul_eq_left (E.isStarProjection s) (E.isStarProjection t) (by
      rw [← E.apply_inter hs ht, inter_eq_left.mpr hst])
  · rw [E.apply_of_not_measurableSet hs]
    exact (E.isStarProjection t).nonneg

/-- For the projection `E s`, `⟪x, E s x⟫ = ‖E s x‖²`. -/
lemma inner_apply_self (s : Set X) (x : H) : ⟪x, E s x⟫_ℂ = (‖E s x‖ ^ 2 : ℝ) :=
  (E.isStarProjection s).inner_apply_self x

/-- A projection has norm at most one on each vector: `‖E s x‖ ≤ ‖x‖`. -/
lemma norm_apply_le (s : Set X) (x : H) : ‖E s x‖ ≤ ‖x‖ :=
  (le_opNorm _ _).trans (mul_le_of_le_one_left (norm_nonneg _) ((E.isStarProjection s).norm_le))

/-- Each `E s` is self-adjoint: `⟪E s x, y⟫ = ⟪x, E s y⟫`. -/
lemma inner_apply_left (s : Set X) (x y : H) : ⟪E s x, y⟫_ℂ = ⟪x, E s y⟫_ℂ := by
  rw [← ContinuousLinearMap.adjoint_inner_left, ((E.isStarProjection s).isSelfAdjoint).adjoint_eq]

/-! ### Construction from pointwise countable additivity -/

/-- Build a projection-valued measure from a map `P : Set X → H →L[ℂ] H` whose values are
orthogonal projections, with `P s = 0` off the measurable sets, `P X = 1`, and
`P (⋃ sᵢ) x = Σ P sᵢ x` for every `x` and pairwise disjoint measurable `sᵢ`: countable additivity
in the strong operator topology is countable additivity at every vector. (`P ∅ = 0` follows, from
the constant sequence `∅`.) -/
noncomputable def ofHasSum (P : Set X → H →L[ℂ] H)
    (not_measurable : ∀ s, ¬MeasurableSet s → P s = 0)
    (hasSum : ∀ f : ℕ → Set X, (∀ i, MeasurableSet (f i)) → Pairwise (Disjoint on f) →
      ∀ x, HasSum (fun i => P (f i) x) (P (⋃ i, f i) x))
    (isStarProjection : ∀ s, IsStarProjection (P s)) (univ : P univ = 1) :
    ProjectionValuedMeasure X H where
  measureOf' s := toUniformConvergenceCLM (RingHom.id ℂ) H {T : Set H | Finite T} (P s)
  empty' := by
    have h₀ : P ∅ = 0 := by
      ext x
      have h := hasSum (fun _ => ∅) (fun _ => MeasurableSet.empty) (fun _ _ _ => disjoint_bot_left) x
      rw [iUnion_const] at h
      exact (summable_const_iff _).mp h.summable
    rw [h₀, map_zero]
  not_measurable' s hs := by rw [not_measurable s hs, map_zero]
  m_iUnion' f hf hd := by
    rw [HasSum, PointwiseConvergenceCLM.tendsto_iff_forall_tendsto]
    intro x
    have h := hasSum f hf hd x
    rw [HasSum] at h
    convert h using 2 with t
    · exact map_sum (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) H x) _ t
    · exact toUniformConvergenceCLM_apply
  isStarProjection' s := isStarProjection s
  univ' := univ

/-- The projection-valued measure `ofHasSum P …` has the values of `P`. -/
@[simp]
lemma ofHasSum_apply (P : Set X → H →L[ℂ] H) (not_measurable hasSum isStarProjection univ)
    (s : Set X) : ofHasSum P not_measurable hasSum isStarProjection univ s = P s := rfl

/-! ### Scalar measures -/

/-- Countable additivity of `s ↦ ‖E s x‖²`. -/
private lemma hasSum_norm_sq {f : ℕ → Set X} (hf : ∀ i, MeasurableSet (f i))
    (hd : Pairwise (Disjoint on f)) (x : H) :
    HasSum (fun i => ‖E (f i) x‖ ^ 2) (‖E (⋃ i, f i) x‖ ^ 2) := by
  have h := (E.hasSum_apply hf hd x).mapL (innerSL ℂ x)
  simp only [innerSL_apply_apply, inner_apply_self] at h
  exact Complex.hasSum_ofReal.mp h

/-- The measure `s ↦ ‖E s x‖² = ⟪x, E s x⟫` of a projection-valued measure at `x`. -/
noncomputable def measure (x : H) : Measure X :=
  Measure.ofMeasurable (fun s _ => ‖E s x‖ₑ ^ 2) (by simp) fun f hf hd => by
    have h := E.hasSum_norm_sq hf hd x
    simp only [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [← h.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) h.summable]

variable {E} in
/-- The diagonal measure of a measurable set is `E.measure x s = ‖E s x‖²`. -/
lemma measure_apply (x : H) (hs : MeasurableSet s) : E.measure x s = ‖E s x‖ₑ ^ 2 :=
  Measure.ofMeasurable_apply s hs

/-- The diagonal measure `E.measure x` has total mass `‖x‖²`. -/
@[simp]
lemma measure_univ (x : H) : E.measure x univ = ‖x‖ₑ ^ 2 := by
  rw [measure_apply x MeasurableSet.univ, apply_univ, one_apply_eq_self]

/-- **Scaling.** `E.measure (a • x) = |a|² E.measure x`. -/
lemma measure_smul (a : ℂ) (x : H) : E.measure (a • x) = (‖a‖₊ ^ 2) • E.measure x := by
  ext s hs
  rw [Measure.smul_apply, measure_apply _ hs, measure_apply _ hs, map_smul, enorm_smul, mul_pow,
    ENNReal.smul_def, smul_eq_mul, enorm_eq_nnnorm, ENNReal.coe_pow]

variable {E} in
/-- **Restriction**: the diagonal measure at `E s x` is that at `x` restricted to `s`. -/
lemma measure_apply_eq_restrict (hs : MeasurableSet s) (x : H) :
    E.measure (E s x) = (E.measure x).restrict s := by
  ext t ht
  rw [Measure.restrict_apply ht, measure_apply _ ht, measure_apply _ (ht.inter hs),
    E.apply_inter ht hs, mul_apply_eq_comp]

variable {E} in
/-- **Orthogonal splitting**: for disjoint measurable `s` and `t`,
`E.measure (E s x + E t y) = E.measure (E s x) + E.measure (E t y)`. -/
lemma measure_add_apply_of_disjoint (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : Disjoint s t) (x y : H) :
    E.measure (E s x + E t y) = E.measure (E s x) + E.measure (E t y) := by
  ext u hu
  rw [Measure.add_apply, measure_apply _ hu, measure_apply _ hu, measure_apply _ hu, map_add]
  have h0 : ⟪E u (E s x), E u (E t y)⟫_ℂ = 0 := by
    rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, ← E.apply_inter hu hs, ← E.apply_inter hu ht,
      inner_apply_left, ← mul_apply_eq_comp,
      E.mul_eq_zero_of_disjoint (hst.mono Set.inter_subset_right Set.inter_subset_right),
      zero_apply, inner_zero_right]
  have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h0
  simp only [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [sq, sq, sq, this, ENNReal.ofReal_add (by positivity) (by positivity)]

/-- The diagonal measures of a projection-valued measure are finite. -/
instance (x : H) : IsFiniteMeasure (E.measure x) :=
  ⟨by rw [measure_univ]; exact ENNReal.pow_lt_top enorm_lt_top⟩

variable {E} in
/-- The diagonal measure of a measurable set is `‖E s x‖²`, as a real number. -/
lemma measureReal_apply (x : H) (hs : MeasurableSet s) : (E.measure x).real s = ‖E s x‖ ^ 2 := by
  rw [measureReal_def, measure_apply x hs, ← ofReal_norm,
    ← ENNReal.ofReal_pow (norm_nonneg _), ENNReal.toReal_ofReal (by positivity)]

/-- The diagonal measure `E.measure x` has total mass `‖x‖²`, as a real number. -/
@[simp]
lemma measureReal_univ (x : H) : (E.measure x).real univ = ‖x‖ ^ 2 := by
  rw [measureReal_apply x MeasurableSet.univ, apply_univ, one_apply_eq_self]

/-- A projection of a measurable set vanishes iff all the diagonal measures vanish on the set. -/
lemma apply_eq_zero_iff (hs : MeasurableSet s) : E s = 0 ↔ ∀ x, E.measure x s = 0 := by
  constructor
  · intro h x
    simp [measure_apply x hs, h]
  · intro h
    ext x
    simpa [measure_apply x hs] using h x

/-- The complex measure `s ↦ ⟪x, E s y⟫` of a projection-valued measure, conjugate-linear in `x`
(Rudin's `E_{y,x}`). -/
noncomputable def complexMeasure (x y : H) : ComplexMeasure X :=
  E.toVectorMeasure.mapRange
    ((innerSL ℂ x).comp
      (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) H y)).toLinearMap.toAddMonoidHom
    (ContinuousLinearMap.continuous _)

/-- The complex measure `E.complexMeasure x y` takes the value `⟪x, E s y⟫` on `s`. -/
lemma complexMeasure_apply (x y : H) (s : Set X) : E.complexMeasure x y s = ⟪x, E s y⟫_ℂ := rfl

/-- On a measurable set, the diagonal complex measure takes the value of the diagonal measure:
`⟪x, E s x⟫ = ‖E s x‖²`. -/
lemma complexMeasure_self_apply (x : H) (hs : MeasurableSet s) :
    E.complexMeasure x x s = ((E.measure x).real s : ℂ) := by
  rw [complexMeasure_apply, inner_apply_self, measureReal_apply x hs]

/-- On the diagonal, the real part of `E.complexMeasure x x` is the diagonal measure
`E.measure x`. -/
lemma re_complexMeasure_self (x : H) :
    (E.complexMeasure x x).re = (E.measure x).toSignedMeasure := by
  ext s hs
  have h : (E.complexMeasure x x).re s = (E.complexMeasure x x s).re := by
    simp [ComplexMeasure.re, VectorMeasure.mapRangeL, VectorMeasure.mapRange_apply]
  rw [h, E.complexMeasure_self_apply x hs, Complex.ofReal_re,
    Measure.toSignedMeasure_apply_measurable hs]

/-- On the diagonal, the imaginary part of `E.complexMeasure x x` vanishes. -/
lemma im_complexMeasure_self (x : H) : (E.complexMeasure x x).im = 0 := by
  ext s hs
  have h : (E.complexMeasure x x).im s = (E.complexMeasure x x s).im := by
    simp [ComplexMeasure.im, VectorMeasure.mapRangeL, VectorMeasure.mapRange_apply]
  rw [h, E.complexMeasure_self_apply x hs, Complex.ofReal_im, zero_apply]

/-- `‖E s x‖² = re ⟪x, E s x⟫`. -/
lemma norm_sq_eq_re_inner_apply_self (s : Set X) (x : H) : ‖E s x‖ ^ 2 = (⟪x, E s x⟫_ℂ).re := by
  rw [inner_apply_self, Complex.ofReal_re]

/-- Each `E s` is self-adjoint: `⟪y, E s x⟫ = conj ⟪x, E s y⟫`. -/
lemma inner_apply_swap (s : Set X) (x y : H) : ⟪y, E s x⟫_ℂ = starRingEnd ℂ ⟪x, E s y⟫_ℂ := by
  rw [← inner_apply_left, inner_conj_symm]

/-- **Polarization**, real part: `re ⟪x, E s y⟫ = ¼ (‖E s (x + y)‖² - ‖E s (x - y)‖²)`, so the real
part of `E.complexMeasure x y` is `¼ (E.measure (x + y) - E.measure (x - y))`. -/
lemma re_complexMeasure (x y : H) :
    (E.complexMeasure x y).re = (4⁻¹ : ℝ) • ((E.measure (x + y)).toSignedMeasure -
      (E.measure (x - y)).toSignedMeasure) := by
  ext s hs
  have h : (E.complexMeasure x y).re s = (E.complexMeasure x y s).re := by
    simp [ComplexMeasure.re, VectorMeasure.mapRangeL, VectorMeasure.mapRange_apply]
  rw [h, complexMeasure_apply, _root_.smul_apply, _root_.sub_apply,
    Measure.toSignedMeasure_apply_measurable hs, Measure.toSignedMeasure_apply_measurable hs,
    measureReal_apply _ hs, measureReal_apply _ hs, smul_eq_mul, norm_sq_eq_re_inner_apply_self,
    norm_sq_eq_re_inner_apply_self]
  simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    E.inner_apply_swap s x y, Complex.add_re, Complex.sub_re, Complex.conj_re]
  ring

/-- **Polarization**, imaginary part:
`im ⟪x, E s y⟫ = ¼ (‖E s (x - i y)‖² - ‖E s (x + i y)‖²)`, so the imaginary part of
`E.complexMeasure x y` is `¼ (E.measure (x - i y) - E.measure (x + i y))`. -/
lemma im_complexMeasure (x y : H) :
    (E.complexMeasure x y).im = (4⁻¹ : ℝ) • ((E.measure (x - Complex.I • y)).toSignedMeasure -
      (E.measure (x + Complex.I • y)).toSignedMeasure) := by
  ext s hs
  have h : (E.complexMeasure x y).im s = (E.complexMeasure x y s).im := by
    simp [ComplexMeasure.im, VectorMeasure.mapRangeL, VectorMeasure.mapRange_apply]
  rw [h, complexMeasure_apply, _root_.smul_apply, _root_.sub_apply,
    Measure.toSignedMeasure_apply_measurable hs, Measure.toSignedMeasure_apply_measurable hs,
    measureReal_apply _ hs, measureReal_apply _ hs, smul_eq_mul, norm_sq_eq_re_inner_apply_self,
    norm_sq_eq_re_inner_apply_self]
  simp only [map_add, map_sub, map_smul, inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right, inner_smul_left, inner_smul_right, E.inner_apply_swap s x y, Complex.add_re,
    Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.add_im, Complex.sub_im, Complex.conj_re,
    Complex.conj_im, Complex.I_re, Complex.I_im]
  ring

/-- **Restriction**: `E.complexMeasure x (E t y)` is the restriction of `E.complexMeasure x y` to
a measurable `t`, since `E s (E t y) = E (s ∩ t) y`. -/
lemma complexMeasure_apply_right (x y : H) (ht : MeasurableSet t) :
    E.complexMeasure x (E t y) = (E.complexMeasure x y).restrict t := by
  ext s hs
  rw [complexMeasure_apply, VectorMeasure.restrict_apply _ ht hs, complexMeasure_apply,
    ← mul_apply_eq_comp, ← E.apply_inter hs ht]

/-- The sharp bound `‖E.complexMeasure x y s‖ ≤ ‖x‖ ‖y‖`, since `E s` is a projection. -/
lemma norm_complexMeasure_apply_le (x y : H) (s : Set X) :
    ‖E.complexMeasure x y s‖ ≤ ‖x‖ * ‖y‖ := by
  rw [complexMeasure_apply]
  exact (norm_inner_le_norm _ _).trans (by gcongr; exact E.norm_apply_le s y)

/-! ### Uniqueness -/

/-- Two projection-valued measures agreeing on measurable sets are equal. -/
@[ext]
lemma ext {F : ProjectionValuedMeasure X H} (h : ∀ s, MeasurableSet s → E s = F s) : E = F := by
  refine DFunLike.coe_injective (funext fun s => ?_)
  by_cases hs : MeasurableSet s
  · exact h s hs
  · rw [E.apply_of_not_measurableSet hs, F.apply_of_not_measurableSet hs]

/-- A projection-valued measure is determined by its diagonal measures `E.measure x`. -/
lemma ext_of_measure {F : ProjectionValuedMeasure X H} (h : ∀ x, E.measure x = F.measure x) :
    E = F := by
  refine E.ext fun s hs => ?_
  have hx : ∀ x, ⟪E s x, x⟫_ℂ = ⟪F s x, x⟫_ℂ := fun x => by
    have hm := congrArg (fun μ => μ.real s) (h x)
    simp only [measureReal_apply x hs] at hm
    rw [← inner_conj_symm, inner_apply_self, ← inner_conj_symm, inner_apply_self, hm]
  have := (ext_inner_map (E s : H →ₗ[ℂ] H) (F s)).mp hx
  exact ContinuousLinearMap.coe_injective this

/-! ### Dirac projection-valued measures -/

section Dirac

variable (H)

open scoped Classical in
/-- The **Dirac** projection-valued measure at `a`: `s ↦ 1` if `s` is measurable and contains `a`,
and `0` otherwise. -/
noncomputable def dirac (a : X) : ProjectionValuedMeasure X H :=
  ofHasSum (fun s => if MeasurableSet s ∧ a ∈ s then 1 else 0)
    (fun s hs => ite_eq_right fun h => absurd h.1 hs)
    (fun f hf hd x => by
      by_cases ha : ∃ i, a ∈ f i
      · obtain ⟨i, hi⟩ := ha
        have hj : ∀ j, (if MeasurableSet (f j) ∧ a ∈ f j then (1 : H →L[ℂ] H) else 0) x =
            if j = i then x else 0 := fun j => by
          by_cases hji : j = i
          · subst hji
            simp [hf j, hi]
          · have : a ∉ f j := fun h => Set.disjoint_left.mp (hd hji) h hi
            simp [hji, this]
        simp only [hj, MeasurableSet.iUnion hf, mem_iUnion, true_and]
        rw [ite_eq_left ⟨i, hi⟩, one_apply_eq_self]
        exact hasSum_ite_eq i x
      · simp only [not_exists] at ha
        simp only [ha, and_false, ite_false, zero_apply, mem_iUnion, exists_false]
        exact hasSum_zero)
    (fun s => by
      split_ifs
      · exact .one _
      · exact .zero _)
    (by simp)

variable {H}

/-- The Dirac projection-valued measure at `a` is `1` on the measurable sets containing `a` and
`0` on the others. -/
lemma dirac_apply (a : X) (hs : MeasurableSet s) : dirac H a s = s.indicator 1 a := by
  classical
  rw [dirac, ofHasSum_apply]
  by_cases ha : a ∈ s <;> simp [hs, ha]

/-- The diagonal measures of the Dirac projection-valued measure are `‖x‖² δ_a`. -/
lemma measure_dirac (a : X) (x : H) : (dirac H a).measure x = ‖x‖ₑ ^ 2 • Measure.dirac a := by
  ext s hs
  rw [measure_apply x hs, dirac_apply a hs, Measure.smul_apply, Measure.dirac_apply' a hs,
    smul_eq_mul]
  by_cases ha : a ∈ s <;> simp [ha]

end Dirac

/-! ### Image under a measurable map -/

variable {Y : Type*} [MeasurableSpace Y] {f : X → Y}

open scoped Classical in
/-- The image `s ↦ E (f ⁻¹' s)` of a projection-valued measure under a measurable map. -/
noncomputable def map (f : X → Y) (hf : Measurable f) : ProjectionValuedMeasure Y H :=
  ofHasSum (fun s => if MeasurableSet s then E (f ⁻¹' s) else 0)
    (fun s hs => ite_eq_right hs)
    (fun g hg hd x => by
      simp only [ite_eq_left (MeasurableSet.iUnion hg), ite_eq_left (hg _), preimage_iUnion]
      exact E.hasSum_apply (fun i => hf (hg i)) (fun i j hij => (hd hij).preimage f) x)
    (fun s => by
      split_ifs
      · exact E.isStarProjection _
      · exact .zero _)
    (by rw [ite_eq_left MeasurableSet.univ, preimage_univ, apply_univ])

/-- The image of `E` under `f` takes the value `E (f ⁻¹' s)` on a measurable `s`. -/
lemma map_apply (hf : Measurable f) {s : Set Y} (hs : MeasurableSet s) :
    E.map f hf s = E (f ⁻¹' s) := by
  rw [map, ofHasSum_apply, ite_eq_left hs]

/-- The diagonal measures of the image of `E` are the images of those of `E`. -/
lemma measure_map (hf : Measurable f) (x : H) : (E.map f hf).measure x = (E.measure x).map f := by
  ext s hs
  rw [measure_apply x hs, Measure.map_apply hf hs, measure_apply x (hf hs), map_apply _ hf hs]

/-- The complex measures of the image of `E` are the images of those of `E`. -/
lemma complexMeasure_map (hf : Measurable f) (x y : H) :
    (E.map f hf).complexMeasure x y = (E.complexMeasure x y).map f := by
  ext s hs
  rw [complexMeasure_apply, VectorMeasure.map_apply _ hf hs, complexMeasure_apply,
    map_apply _ hf hs]

end ProjectionValuedMeasure

end MeasureTheory
