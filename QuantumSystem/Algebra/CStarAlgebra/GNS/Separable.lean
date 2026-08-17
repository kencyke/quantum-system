module

public import Mathlib.Analysis.CStarAlgebra.Hom
public import QuantumSystem.Algebra.CStarAlgebra.GNS.PureState
public import QuantumSystem.Algebra.CStarAlgebra.Representation.DirectSum
public import QuantumSystem.ForMathlib.Analysis.Normed.Lp.Separable

/-!
# A countable norming family of pure states, for a separable C\*-algebra

The Gelfand-Naimark representation built in `CStarAlgebra/GNS/DirectSum.lean` is indexed by
the *whole* pure state space, so its Hilbert space is typically nonseparable even when `A`
is separable. This file builds the countable replacement.

The idea is to index not by states but by a dense sequence of the algebra: for each nonzero
member `aₙ` of a countable dense sequence, pick a pure state that **norms** `aₙ`
(`IsPureState.exists_norm_sq_of_ne_zero`), and take the ℓ²-direct sum of the corresponding
GNS representations. Norming — rather than merely detecting — is what makes a countable
family enough: for `a ≠ 0` and `aₙ` within `‖a‖ / 2` of `a`, the `n`-th representation
cannot annihilate `a`, because it does not shrink `aₙ`.

## Main results

* `GNS.Representation.norm_sq_apply_cyclic` — `‖T.π x T.ξ‖ ^ 2 = (ω (star x * x)).re` for any
  GNS triplet. This is what turns a norming *state* into a non-vanishing *operator*.
* `GNS.Representation.separableSpace_H` — the Hilbert space of a GNS triplet over a
  separable algebra is separable.
* `GNS.normingFamily` — the countable family of GNS representations described above, and
  `GNS.normingFamily_separatesPoints`, `GNS.separableSpace_normingFamily_directSumHilbert`.

The theorem these serve is `CStarRep.exists_isometric_separable`, in
`CStarAlgebra/GelfandNaimark.lean`.
-/

@[expose] public section

open TopologicalSpace

open scoped InnerProductSpace Adjoint ComplexHilbertSpace

universe u

namespace GNS

variable {A : Type u} [NonUnitalCStarAlgebra A]

namespace Representation

/-- For a GNS triplet, the squared length of the orbit vector `T.π x T.ξ` is the value of
the state at `star x * x`.

This is the bridge between a *norming state* and a *non-vanishing operator*: a state whose
value at `star x * x` is `‖x‖ ^ 2` yields a representation with `‖T.π x T.ξ‖ = ‖x‖`. -/
lemma norm_sq_apply_cyclic {ω : State ℂ A} (T : Representation ω) (x : A) :
    ‖T.π x T.ξ‖ ^ 2 = (ω (star x * x)).re := by
  have hstar : T.π (star x) = (T.π x)† := by
    rw [map_star, ContinuousLinearMap.star_eq_adjoint]
  have hval : T.π (star x * x) T.ξ = (T.π x)† (T.π x T.ξ) := by
    rw [map_mul, hstar]
    rfl
  rw [T.gns_condition (star x * x), hval, ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

/-- A norming state gives an orbit vector of full length: if `ω (star x * x) = ‖x‖ ^ 2`
then `‖T.π x T.ξ‖ = ‖x‖`. -/
lemma norm_apply_cyclic_of_norming {ω : State ℂ A} (T : Representation ω) {x : A}
    (hx : ω (star x * x) = ((‖x‖ ^ 2 : ℝ) : ℂ)) :
    ‖T.π x T.ξ‖ = ‖x‖ := by
  have h := T.norm_sq_apply_cyclic x
  rw [hx] at h
  have h' : ‖T.π x T.ξ‖ ^ 2 = ‖x‖ ^ 2 := by rw [h, Complex.ofReal_re]
  nlinarith [norm_nonneg (T.π x T.ξ), norm_nonneg x, h']

/-- The orbit map `a ↦ T.π a T.ξ` is `1`-Lipschitz.

It is the composition of the contraction `a ↦ T.π a` with evaluation at a unit vector. -/
lemma lipschitzWith_apply_cyclic {ω : State ℂ A} (T : Representation ω) :
    LipschitzWith 1 (fun a : A => T.π a T.ξ) := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  have hsub : T.π a T.ξ - T.π b T.ξ = T.π (a - b) T.ξ := by
    rw [map_sub]
    rfl
  have hbound : dist (T.π a T.ξ) (T.π b T.ξ) ≤ ‖a - b‖ := by
    calc dist (T.π a T.ξ) (T.π b T.ξ) = ‖T.π (a - b) T.ξ‖ := by rw [dist_eq_norm, hsub]
      _ ≤ ‖T.π (a - b)‖ * ‖T.ξ‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖a - b‖ * 1 := by
          gcongr
          · exact NonUnitalStarAlgHom.norm_apply_le _ _
          · exact le_of_eq T.unit_norm
      _ = ‖a - b‖ := mul_one _
  simpa [dist_eq_norm] using hbound

/-- The Hilbert space of a GNS triplet over a **separable** C\*-algebra is separable.

The orbit of the cyclic vector is a continuous image of `A`, hence separable; its span is
separable, and the span is dense by cyclicity. -/
theorem separableSpace_H [SeparableSpace A] {ω : State ℂ A} (T : Representation ω) :
    SeparableSpace T.H := by
  have hrange : IsSeparable (Set.range fun a : A => T.π a T.ξ) :=
    isSeparable_range T.lipschitzWith_apply_cyclic.continuous
  have hspan : IsSeparable
      ((Submodule.span ℂ {x | ∃ a : A, T.π a T.ξ = x} : Submodule ℂ T.H) : Set T.H) :=
    hrange.span
  rw [← isSeparable_univ_iff, ← T.cyclic.closure_eq]
  exact hspan.closure

end Representation

section Norming

variable (A) in
/-- The index type of the norming family: the positions of the **nonzero** members of a
fixed dense sequence of `A`.

Dropping the zero members is what lets every index carry a pure state; the discarded
positions carry no information, since `0` is annihilated by every representation. When
`A = 0` the index type is empty, which is the correct answer there. -/
noncomputable def NormingIndex [SeparableSpace A] : Type := {n : ℕ // denseSeq A n ≠ 0}

instance [SeparableSpace A] : Countable (NormingIndex A) :=
  inferInstanceAs (Countable {n : ℕ // denseSeq A n ≠ 0})

/-- The element of the dense sequence sitting at a norming index. -/
noncomputable def NormingIndex.elem [SeparableSpace A] (i : NormingIndex A) : A :=
  denseSeq A i.1

lemma NormingIndex.elem_ne_zero [SeparableSpace A] (i : NormingIndex A) : i.elem ≠ 0 := i.2

/-- A pure state norming the element at a norming index. -/
noncomputable def normingState [SeparableSpace A] (i : NormingIndex A) : PureState A :=
  ⟨(IsPureState.exists_norm_sq_of_ne_zero i.elem i.elem_ne_zero).choose,
    (IsPureState.exists_norm_sq_of_ne_zero i.elem i.elem_ne_zero).choose_spec.1⟩

lemma normingState_spec [SeparableSpace A] (i : NormingIndex A) :
    (normingState i : State ℂ A) (star i.elem * i.elem) = ((‖i.elem‖ ^ 2 : ℝ) : ℂ) :=
  (IsPureState.exists_norm_sq_of_ne_zero i.elem i.elem_ne_zero).choose_spec.2

variable (A) in
/-- The **countable norming family**: one GNS representation for each nonzero member of a
dense sequence of `A`, at a pure state norming that member. -/
noncomputable def normingFamily [SeparableSpace A] : SectorFamily.{u, u, 0} A where
  Index := NormingIndex A
  rep i := (PureState.gnsRepresentation (normingState i)).toCStarRep

/-- Each summand of the norming family is separable. -/
instance [SeparableSpace A] (i : NormingIndex A) :
    SeparableSpace ((normingFamily A).rep i).H :=
  Representation.separableSpace_H _

/-- The direct-sum Hilbert space of the norming family is separable: it is an ℓ²-sum of
countably many separable spaces. -/
instance separableSpace_normingFamily_directSumHilbert [SeparableSpace A] :
    SeparableSpace (normingFamily A).directSumHilbert :=
  inferInstanceAs (SeparableSpace (lp (fun i : NormingIndex A =>
    ((normingFamily A).rep i).H) 2))

variable (A) in
/-- **The norming family separates points.**

If every member annihilates `a ≠ 0`, take `aₙ` from the dense sequence within `‖a‖ / 2` of
`a`. Then `aₙ ≠ 0`, so it carries an index `i`, and its norming state gives
`‖π_i(aₙ) ξ_i‖ = ‖aₙ‖`. But `π_i(a) = 0` forces
`‖aₙ‖ = ‖π_i(aₙ - a) ξ_i‖ ≤ ‖aₙ - a‖ < ‖a‖ / 2`, contradicting `‖aₙ‖ > ‖a‖ / 2`. -/
theorem normingFamily_separatesPoints [SeparableSpace A] :
    (normingFamily A).SeparatesPoints := by
  intro a ha
  by_contra hne
  have hapos : (0 : ℝ) < ‖a‖ := norm_pos_iff.mpr hne
  -- A member of the dense sequence within `‖a‖ / 2` of `a`.
  obtain ⟨n, hn⟩ := (denseRange_denseSeq A).exists_dist_lt a (by positivity : (0:ℝ) < ‖a‖ / 2)
  have hdist : ‖denseSeq A n - a‖ < ‖a‖ / 2 := by
    rw [dist_eq_norm] at hn
    rwa [norm_sub_rev] at hn
  have hb_lower : ‖a‖ / 2 < ‖denseSeq A n‖ := by
    have := norm_sub_norm_le a (denseSeq A n)
    rw [← norm_neg (a - denseSeq A n), neg_sub] at this
    linarith
  have hb_ne : denseSeq A n ≠ 0 := by
    intro h
    rw [h, norm_zero] at hb_lower
    linarith
  set i : NormingIndex A := ⟨n, hb_ne⟩ with hi
  have helem : i.elem = denseSeq A n := rfl
  set T := PureState.gnsRepresentation (normingState i) with hT
  -- The representation at `i` norms `i.elem`.
  have hnorm : ‖T.π i.elem T.ξ‖ = ‖i.elem‖ :=
    T.norm_apply_cyclic_of_norming (normingState_spec i)
  -- but it kills `a`, so it can only see the difference.
  have hzero : T.π a = 0 := ha i
  have hsplit : T.π i.elem T.ξ = T.π (i.elem - a) T.ξ := by
    rw [map_sub]
    simp [hzero]
  have hle : ‖T.π i.elem T.ξ‖ ≤ ‖i.elem - a‖ := by
    rw [hsplit]
    calc ‖T.π (i.elem - a) T.ξ‖ ≤ ‖T.π (i.elem - a)‖ * ‖T.ξ‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖i.elem - a‖ * 1 := by
          gcongr
          · exact NonUnitalStarAlgHom.norm_apply_le _ _
          · exact le_of_eq T.unit_norm
      _ = ‖i.elem - a‖ := mul_one _
  rw [hnorm, helem] at hle
  linarith

variable (A) in
/-- The ℓ²-direct sum of the norming family, bundled as a `CStarRep`.

This is the separable counterpart of `GNS.DirectSum.rep`: same construction, but indexed by
a dense sequence of the algebra instead of by the whole pure state space. -/
noncomputable def normingRep [SeparableSpace A] : CStarRep.{u, u} A where
  H := (normingFamily A).directSumHilbert
  π := (normingFamily A).directSumRep

@[simp]
lemma normingRep_π [SeparableSpace A] :
    (normingRep A).π = (normingFamily A).directSumRep := rfl

instance [SeparableSpace A] : SeparableSpace (normingRep A).H :=
  separableSpace_normingFamily_directSumHilbert

variable (A) in
/-- The norming representation is faithful. -/
theorem normingRep_injective [SeparableSpace A] :
    Function.Injective (normingRep A).π :=
  (normingFamily A).directSumRep_injective_of (normingFamily_separatesPoints A)

variable (A) in
/-- The norming representation is isometric, by faithfulness. -/
theorem normingRep_isometry [SeparableSpace A] : Isometry (normingRep A).π :=
  AddMonoidHomClass.isometry_of_norm _ fun a =>
    NonUnitalStarAlgHom.norm_map _ (normingRep_injective A) a

variable (A) in
/-- The image of the norming representation is norm closed, so it is a C\*-subalgebra of
the bounded operators on a separable Hilbert space. -/
theorem normingRep_isClosed_range [SeparableSpace A] :
    IsClosed (NonUnitalStarAlgHom.range (normingRep A).π : Set 𝓑((normingRep A).H)) := by
  rw [NonUnitalStarAlgHom.coe_range]
  exact (normingRep_isometry A).isClosedEmbedding.isClosed_range

end Norming

end GNS
