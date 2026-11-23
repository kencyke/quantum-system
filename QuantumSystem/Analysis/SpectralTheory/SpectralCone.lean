/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.Convex.Cone.Dual
public import QuantumSystem.Analysis.SpectralTheory.Stone

/-!
# The spectral cone of a unitary representation

Let `U` be a strongly continuous unitary representation of a finite-dimensional real vector space
`V`. For `a : V`, the one-parameter group `s ↦ U (s • a)` has a self-adjoint generator `P_a` by
Stone's theorem (`UnitaryAddRepresentation.selfAdjointGeneratorAlong`), `U (s • a) = e^{isP_a}`;
`i P_a` is the derived representation `∂U(a)`. In quantum field theory, with `U` the translations,
`P_a` is the component of the energy-momentum operator along `a` (in units with ℏ = 1). The
**spectral cone** of `U` (`UnitaryAddRepresentation.spectralCone`) is the set of directions `a` with
`P_a ≥ 0`. It is a
closed convex cone (`ProperCone`); Neeb and Ólafsson call it the *positive cone*
`C_U = {a | -i ∂U(a) ≥ 0}` of `U`.

Through the SNAG theorem, `U v = ∫ exp (i L(p, v)) dE_U(p)` for a continuous perfect pairing
`L : W × V → ℝ`, the generator is `P_a = ∫ L(p, a) dE_U(p)`
(`UnitaryAddRepresentation.selfAdjointGeneratorAlong_eq_integralPMap`), with projection-valued
measure the image of `E_U` under `p ↦ L(p, a)`
(`UnitaryAddRepresentation.pvm_selfAdjointGeneratorAlong`). Hence `a` is in the spectral cone
iff `E_U {p | L(p, a) < 0} = 0` (`UnitaryAddRepresentation.mem_spectralCone_iff`), and a set
`C ⊆ V` lies in the spectral cone iff `E_U` vanishes off the dual cone
`C* = {p | ∀ a ∈ C, 0 ≤ L(p, a)}` (`UnitaryAddRepresentation.subset_spectralCone_iff`). The
latter is the **spectrum condition** of quantum field theory in the form `E_U((C*)ᶜ) = 0` ("the
joint spectrum of the translations lies in the dual cone"), which therefore says exactly that `C`
is contained in the spectral cone. For the dual pairing `L = topDualPairing ℝ V` the dual cone is
`{p ∈ StrongDual ℝ V | ∀ a ∈ C, 0 ≤ p a}`.

## Main definitions

* `UnitaryAddRepresentation.selfAdjointGeneratorAlong U a` — the self-adjoint generator `P_a` of
  `s ↦ U (s • a)`, `i P_a y = d/ds U(s • a) y |_{s = 0}`.
* `UnitaryAddRepresentation.spectralCone U` — the closed convex cone of the directions `a`
  with `P_a ≥ 0`.

## Main results

* `UnitaryAddRepresentation.isSelfAdjoint_selfAdjointGeneratorAlong`,
  `UnitaryAddRepresentation.unitaryGroup_selfAdjointGeneratorAlong` — `P_a` is self-adjoint
  and `U (s • a) = e^{isP_a}`.
* `UnitaryAddRepresentation.selfAdjointGeneratorAlong_eq_integralPMap`,
  `UnitaryAddRepresentation.pvm_selfAdjointGeneratorAlong` — `P_a = ∫ L(p, a) dE_U(p)`, with
  projection-valued measure the image of `E_U` under `p ↦ L(p, a)`.
* `UnitaryAddRepresentation.mem_spectralCone_iff_isPositive`,
  `UnitaryAddRepresentation.mem_spectralCone_iff` — `a` is in the spectral cone iff `P_a ≥ 0`,
  iff `E_U {p | L(p, a) < 0} = 0`.
* `UnitaryAddRepresentation.subset_spectralCone_iff` — **spectrum condition**: `C` lies in the
  spectral cone iff `E_U` vanishes off the dual cone of `C`.
* `UnitaryAddRepresentation.one_mem_spectralCone_iff` — for `V = ℝ`, `1` is in the spectral
  cone iff the self-adjoint generator of `U` is positive.

## TODO

* The positive cone `C_U = {x ∈ 𝔤 | -i ∂U(x) ≥ 0}` of a unitary representation of a Lie group
  `G` (Neeb–Ólafsson), a closed convex `Ad(G)`-invariant cone in the Lie algebra. Only the vector
  groups `V` are treated here, where the SNAG theorem describes `C_U` through the joint spectrum;
  for a general `G` convexity needs the derived representation on the space of smooth vectors.
* `[T2Space V]` is used only to reach the dual pairing `topDualPairing ℝ V` in the construction;
  a strongly continuous `U` factors through the Hausdorff quotient of `V`, so the assumption could
  be removed.
* Holomorphy in the tube `V + i C`: the spectrum condition `E_U((C*)ᶜ) = 0` holds iff
  `v ↦ U v` extends to a bounded family on `V + i C`, holomorphic on `V + i C°` and strongly
  continuous up to the boundary, `U (v + i w) = ∫ exp (i L(p, v)) exp (-L(p, w)) dE_U(p)`.
  This needs holomorphy in several complex variables;
  only the one-variable case along a direction `a` of the spectral cone, `w ↦ e^{iwP_a}` on the
  upper half-plane (`ProjectionValuedMeasure.diffContOnCl_integralApply_cexp_of_nonneg`), is
  formalised.

## References

* H.-J. Borchers, *On the use of modular groups in quantum field theory*,
  Ann. Inst. H. Poincaré Phys. Théor. 63 (1995), 331–382, §2
* R. F. Streater, A. S. Wightman, *PCT, Spin and Statistics, and All That*, Benjamin (1964)
* K.-H. Neeb, G. Ólafsson, *Nets of standard subspaces on Lie groups*, Adv. Math. 384 (2021)
  (the positive cone `C_U` of a unitary representation)
-/

@[expose] public section

open Set Filter Topology MeasureTheory

/-! ### Self-adjoint generators along directions -/

namespace UnitaryAddRepresentation

variable {V H F : Type*} [AddCommGroup V] [Module ℝ V] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

section Algebraic

variable [FunLike F V (UnitarySOT ℂ H)] [AddCharClass F V (UnitarySOT ℂ H)]

/-- The **self-adjoint generator along `a`** of a unitary representation `U` of `V`: the
self-adjoint generator `P_a` of the one-parameter group `s ↦ U (s • a)`,
`i P_a y = d/ds U(s • a) y |_{s = 0}`; `i P_a` is the derived representation `∂U(a)`. It is defined
for every additive character `U` of `V` into the unitary group, on which no continuity is
imposed. For a strongly continuous `U` it is self-adjoint with `U (s • a) = e^{isP_a}`
(`UnitaryAddRepresentation.unitaryGroup_selfAdjointGeneratorAlong`), and
`P_a = ∫ L(p, a) dE_U(p)`
(`UnitaryAddRepresentation.selfAdjointGeneratorAlong_eq_integralPMap`). -/
noncomputable def selfAdjointGeneratorAlong (U : F) (a : V) : H →ₗ.[ℂ] H :=
  selfAdjointGenerator ((U : AddChar V (UnitarySOT ℂ H)).compAddMonoidHom
    (LinearMap.toSpanSingleton ℝ V a).toAddMonoidHom)

end Algebraic

/-- For a one-parameter group, the self-adjoint generator along `1` is the self-adjoint
generator. -/
@[simp]
lemma selfAdjointGeneratorAlong_one [FunLike F ℝ (UnitarySOT ℂ H)]
    [AddCharClass F ℝ (UnitarySOT ℂ H)] (U : F) :
    selfAdjointGeneratorAlong U 1 = selfAdjointGenerator U := by
  refine LinearPMap.eq_of_eq_graph (Submodule.ext fun ⟨y, z⟩ => ?_)
  rw [selfAdjointGeneratorAlong, mem_graph_selfAdjointGenerator_iff,
    mem_graph_selfAdjointGenerator_iff]
  simp

variable [TopologicalSpace V] [ContinuousSMul ℝ V]

/-- For a strongly continuous `U`, the self-adjoint generator along `a` is the self-adjoint
generator of the strongly continuous one-parameter group `s ↦ U (s • a)`. -/
lemma selfAdjointGeneratorAlong_eq (U : UnitaryAddRepresentation V H) (a : V) :
    selfAdjointGeneratorAlong U a = selfAdjointGenerator
      (U.compContinuousAddMonoidHom (ContinuousLinearMap.toSpanSingleton ℝ a : ℝ →ₜ+ V)) :=
  rfl

end UnitaryAddRepresentation

namespace UnitaryAddRepresentation

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup W] [Module ℝ W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  [ContinuousSMul ℝ W] [MeasurableSpace W] [BorelSpace W] (L : W →ₗ[ℝ] V →ₗ[ℝ] ℝ)
  [L.IsContPerfPair] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] (U : UnitaryAddRepresentation V H)

omit [IsTopologicalAddGroup V] [FiniteDimensional ℝ V] in
/-- The one-parameter group `s ↦ U (s • a)`. -/
private noncomputable abbrev alongLine (a : V) : UnitaryAddRepresentation ℝ H :=
  U.compContinuousAddMonoidHom (ContinuousLinearMap.toSpanSingleton ℝ a : ℝ →ₜ+ V)

/-- The projection-valued measure of the one-parameter group `s ↦ U (s • a)` is the image of
`E_U` under `p ↦ L(p, a)`. -/
private lemma pvm_compContinuousAddMonoidHom_toSpanSingleton (a : V) :
    (U.alongLine a).pvm (LinearMap.mul ℝ ℝ) =
      (U.pvm L).map (fun w => L w a) (L.measurable_flip_apply_of_isContPerfPair a) :=
  U.pvm_compContinuousAddMonoidHom (ContinuousLinearMap.toSpanSingleton ℝ a)
    ⟨L.flip a, L.flip.continuous_of_isContPerfPair⟩ fun w s => by simp [mul_comm]

omit [IsTopologicalAddGroup V] [FiniteDimensional ℝ V] in
/-- The self-adjoint generator along `a` of a strongly continuous representation is
self-adjoint. -/
lemma isSelfAdjoint_selfAdjointGeneratorAlong (a : V) :
    IsSelfAdjoint (selfAdjointGeneratorAlong U a) :=
  (U.alongLine a).isSelfAdjoint_selfAdjointGenerator

omit [IsTopologicalAddGroup V] [FiniteDimensional ℝ V] in
/-- `U (s • a) = e^{isP_a}` for the self-adjoint generator `P_a` along `a`. -/
lemma unitaryGroup_selfAdjointGeneratorAlong (a : V) (s : ℝ) :
    (U.isSelfAdjoint_selfAdjointGeneratorAlong a).unitaryGroup s = U (s • a) := by
  exact congrArg (· s) (U.alongLine a).unitaryGroup_selfAdjointGenerator

/-- The projection-valued measure of the self-adjoint generator `P_a` along `a` is the image of
`E_U` under `p ↦ L(p, a)`. -/
lemma pvm_selfAdjointGeneratorAlong (a : V) :
    (U.isSelfAdjoint_selfAdjointGeneratorAlong a).pvm =
      (U.pvm L).map (fun w => L w a) (L.measurable_flip_apply_of_isContPerfPair a) :=
  ((U.alongLine a).pvm_selfAdjointGenerator).trans (U.pvm_compContinuousAddMonoidHom_toSpanSingleton L a)

/-- The self-adjoint generator along `a` is `P_a = ∫ L(p, a) dE_U(p)`. -/
lemma selfAdjointGeneratorAlong_eq_integralPMap (a : V) :
    selfAdjointGeneratorAlong U a = (U.pvm L).integralPMap fun w => (L w a : ℂ) := by
  rw [selfAdjointGeneratorAlong_eq, (U.alongLine a).selfAdjointGenerator_eq_integralPMap,
    U.pvm_compContinuousAddMonoidHom_toSpanSingleton L a,
    ProjectionValuedMeasure.integralPMap_map _ _ Complex.measurable_ofReal]
  rfl

/-- `P_a ≥ 0` iff `E_U {p | L(p, a) < 0} = 0`. -/
private lemma isPositive_selfAdjointGeneratorAlong_iff (a : V) :
    (selfAdjointGeneratorAlong U a).IsPositive ↔ U.pvm L {w | L w a < 0} = 0 := by
  rw [(U.isSelfAdjoint_selfAdjointGeneratorAlong a).isPositive_iff_pvm_Iio_eq_zero,
    U.pvm_selfAdjointGeneratorAlong L a, ProjectionValuedMeasure.map_apply _ _ measurableSet_Iio]
  rfl

/-! ### Null half-spaces -/

omit [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [FiniteDimensional ℝ V]
  [IsTopologicalAddGroup W] [ContinuousSMul ℝ W] in
private lemma measurableSet_neg (a : V) : MeasurableSet {w | L w a < 0} :=
  measurableSet_lt (L.measurable_flip_apply_of_isContPerfPair a) measurable_const

private lemma pvm_neg_zero : U.pvm L {w | L w 0 < 0} = 0 := by
  simp

private lemma pvm_neg_add {a b : V} (ha : U.pvm L {w | L w a < 0} = 0)
    (hb : U.pvm L {w | L w b < 0} = 0) : U.pvm L {w | L w (a + b) < 0} = 0 := by
  have h := (U.pvm L).apply_biUnion_null (T := {a, b}) (toFinite _).countable
    (measurableSet_neg L) (by simp [ha, hb])
  refine (U.pvm L).apply_mono_null (.biUnion (toFinite _).countable fun _ _ =>
    measurableSet_neg L _) (fun w hw => ?_) h
  simp only [mem_insert_iff, mem_singleton_iff, iUnion_iUnion_eq_or_left, iUnion_iUnion_eq_left,
    mem_union, mem_ofPred_eq]
  by_contra! hc
  simp only [mem_ofPred_eq, map_add] at hw
  linarith [hc.1, hc.2]

private lemma pvm_neg_smul {a : V} (ha : U.pvm L {w | L w a < 0} = 0) {c : ℝ} (hc : 0 ≤ c) :
    U.pvm L {w | L w (c • a) < 0} = 0 :=
  (U.pvm L).apply_mono_null (measurableSet_neg L a)
    (fun w hw => by
      simp only [mem_ofPred_eq, map_smul, smul_eq_mul] at hw ⊢
      by_contra! h
      linarith [mul_nonneg hc h]) ha

/-- The directions `a` with `E_U {p | L(p, a) < 0} = 0` form a closed set: if `aₙ → a`, then
`{L(·, a) < 0} ⊆ ⋃ₙ {L(·, aₙ) < 0}`. -/
private lemma isClosed_setOf_pvm_neg : IsClosed {a : V | U.pvm L {w | L w a < 0} = 0} := by
  have := L.firstCountableTopology_of_isContPerfPair
  refine isClosed_of_closure_subset fun a ha => ?_
  obtain ⟨b, hb, hba⟩ := mem_closure_iff_seq_limit.mp ha
  have h := (U.pvm L).apply_biUnion_null (T := univ) countable_univ
    (fun n => measurableSet_neg L (b n)) fun n _ => hb n
  refine (U.pvm L).apply_mono_null (.biUnion countable_univ fun n _ => measurableSet_neg L (b n))
    (fun w hw => ?_) h
  have hw' := (((L.continuous_of_isContPerfPair (x := w)).tendsto a).comp hba).eventually_mem
    (Iio_mem_nhds hw)
  obtain ⟨n, hn⟩ := hw'.exists
  exact mem_biUnion (mem_univ n) hn

end UnitaryAddRepresentation

/-! ### The spectral cone -/

namespace UnitaryAddRepresentation

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [FiniteDimensional ℝ V] [T2Space V]
  [AddCommGroup W] [Module ℝ W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  [ContinuousSMul ℝ W] [MeasurableSpace W] [BorelSpace W] (L : W →ₗ[ℝ] V →ₗ[ℝ] ℝ)
  [L.IsContPerfPair] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] (U : UnitaryAddRepresentation V H)

/-- The **spectral cone** of a strongly continuous unitary representation `U` of `V`: the closed
convex cone of the directions `a` for which the one-parameter group `s ↦ U (s • a)` has a
positive self-adjoint generator, `U (s • a) = e^{isP_a}` with `P_a ≥ 0`
(`UnitaryAddRepresentation.selfAdjointGeneratorAlong`). Its convexity and closedness come from the
description `E_U {p | p(a) < 0} = 0` through the SNAG theorem
(`UnitaryAddRepresentation.mem_spectralCone_iff`). -/
noncomputable def spectralCone : ProperCone ℝ V :=
  letI : MeasurableSpace (StrongDual ℝ V) := borel _
  haveI : BorelSpace (StrongDual ℝ V) := ⟨rfl⟩
  { carrier := {a | (selfAdjointGeneratorAlong U a).IsPositive}
    zero_mem' := by
      exact (isPositive_selfAdjointGeneratorAlong_iff (topDualPairing ℝ V) U 0).mpr
        (pvm_neg_zero (topDualPairing ℝ V) U)
    add_mem' := fun {a b} ha hb => by
      exact (isPositive_selfAdjointGeneratorAlong_iff (topDualPairing ℝ V) U (a + b)).mpr
        (pvm_neg_add (topDualPairing ℝ V) U
          ((isPositive_selfAdjointGeneratorAlong_iff _ U a).mp ha)
          ((isPositive_selfAdjointGeneratorAlong_iff _ U b).mp hb))
    smul_mem' := fun c a ha => by
      exact (isPositive_selfAdjointGeneratorAlong_iff (topDualPairing ℝ V) U _).mpr
        (pvm_neg_smul (topDualPairing ℝ V) U
          ((isPositive_selfAdjointGeneratorAlong_iff _ U a).mp ha) c.2)
    isClosed' := by
      convert isClosed_setOf_pvm_neg (topDualPairing ℝ V) U using 1
      ext a
      exact isPositive_selfAdjointGeneratorAlong_iff (topDualPairing ℝ V) U a }

/-- `a` is in the spectral cone iff the one-parameter group `s ↦ U (s • a)` has a positive
self-adjoint generator. -/
lemma mem_spectralCone_iff_isPositive {a : V} :
    a ∈ U.spectralCone ↔ (selfAdjointGeneratorAlong U a).IsPositive :=
  Iff.rfl

/-- `a` is in the spectral cone iff `E_U {p | L(p, a) < 0} = 0`. -/
lemma mem_spectralCone_iff {a : V} : a ∈ U.spectralCone ↔ U.pvm L {w | L w a < 0} = 0 :=
  isPositive_selfAdjointGeneratorAlong_iff L U a

/-- **Spectrum condition**: a set `C ⊆ V` lies in the spectral cone iff the projection-valued
measure `E_U` vanishes off the dual cone `C* = {p | ∀ a ∈ C, 0 ≤ L(p, a)}`. For `⇒`, the
complement of `C*` is the union of the open half-spaces `{L(·, a) < 0}`, `a ∈ C`, and countably
many of them suffice since `W` is second countable. -/
theorem subset_spectralCone_iff (C : Set V) :
    C ⊆ U.spectralCone ↔ U.pvm L (ProperCone.dual L.flip C : Set W)ᶜ = 0 := by
  have hdual : MeasurableSet (ProperCone.dual L.flip C : Set W)ᶜ :=
    (ProperCone.isClosed _).measurableSet.compl
  refine ⟨fun h => ?_, fun h a ha => (U.mem_spectralCone_iff L).mpr <|
    (U.pvm L).apply_mono_null hdual (fun w hw hw' => not_le.mpr hw (hw' ha)) h⟩
  obtain ⟨n, -, f, -⟩ := L.exists_euclidean_of_isContPerfPair
  have : SecondCountableTopology W := f.toHomeomorph.secondCountableTopology
  obtain ⟨T, hT, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable (fun a : C => {w | L w a < 0})
    fun a => isOpen_lt (L.flip.continuous_of_isContPerfPair (x := a)) continuous_const
  have hc : (ProperCone.dual L.flip C : Set W)ᶜ = ⋃ a ∈ T, {w | L w a < 0} := by
    rw [hTU]
    ext w
    simp [ProperCone.mem_dual]
  rw [hc]
  exact (U.pvm L).apply_biUnion_null hT (fun a => measurableSet_neg L a) fun a _ =>
    (U.mem_spectralCone_iff L).mp (h a.2)

end UnitaryAddRepresentation

namespace UnitaryAddRepresentation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : UnitaryAddRepresentation ℝ H)

/-- For a one-parameter group, `1` is in the spectral cone iff the self-adjoint generator is
positive. -/
lemma one_mem_spectralCone_iff : (1 : ℝ) ∈ U.spectralCone ↔ (selfAdjointGenerator U).IsPositive := by
  rw [mem_spectralCone_iff_isPositive, selfAdjointGeneratorAlong_one]

end UnitaryAddRepresentation
