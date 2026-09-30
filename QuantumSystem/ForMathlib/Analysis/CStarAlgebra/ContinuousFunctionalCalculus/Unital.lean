/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
public import Mathlib.Topology.ContinuousMap.ContinuousSqrt

/-!
# Self-adjoint elements with spectrum in a set

For a set `s ⊆ ℝ`, the self-adjoint elements of an algebra with a real continuous functional
calculus whose spectrum lies in `s` form the natural domain of operator-monotone and
operator-convex functions on `s`. This file identifies the two most common instances with the
order-theoretic sets and shows that the domain is convex when `s` is an interval.

## Main results

* `setOf_isSelfAdjoint_spectrum_subset_Ici`: for `s = [0, ∞)` the domain is `Set.Ici 0`.
* `setOf_isSelfAdjoint_spectrum_subset_Ioi`: for `s = (0, ∞)` the domain is the set of strictly
  positive elements.
* `Set.OrdConnected.convex_setOf_isSelfAdjoint_spectrum_subset`: for an order-connected `s` the
  domain is convex. The spectra are compact, so they sit in an interval `[lo, hi] ⊆ s`, and
  `lo ≤ a, b ≤ hi` passes to convex combinations.
-/

@[expose] public section

open Set

variable {A : Type*} [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [TopologicalSpace A]
  [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [NonnegSpectrumClass ℝ A]

/-- The self-adjoint elements with spectrum in `[0, ∞)` are the nonnegative elements. -/
theorem setOf_isSelfAdjoint_spectrum_subset_Ici :
    {a : A | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ Ici 0} = Ici 0 := by
  ext a
  refine ⟨fun ⟨ha, h⟩ => (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) a ha).2
      fun x hx => h hx,
    fun h => ⟨IsSelfAdjoint.of_nonneg h, fun x hx =>
      (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) a (IsSelfAdjoint.of_nonneg h)).1 h x hx⟩⟩

/-- The self-adjoint elements with spectrum in `(0, ∞)` are the strictly positive elements. -/
theorem setOf_isSelfAdjoint_spectrum_subset_Ioi :
    {a : A | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ Ioi 0} = {a | IsStrictlyPositive a} := by
  ext a
  refine ⟨fun ⟨ha, h⟩ => (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos (R := ℝ) a ha).2
      fun x hx => h hx,
    fun h => ⟨h.isSelfAdjoint, fun x hx =>
      (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos (R := ℝ) a h.isSelfAdjoint).1 h x hx⟩⟩

/-- For an order-connected `s ⊆ ℝ`, the self-adjoint elements with spectrum in `s` form a convex
set. -/
theorem Set.OrdConnected.convex_setOf_isSelfAdjoint_spectrum_subset [StarModule ℝ A]
    {s : Set ℝ} (hs : s.OrdConnected) :
    Convex ℝ {a : A | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ s} := by
  rintro a ⟨ha, has⟩ b ⟨hb, hbs⟩ t u ht hu htu
  have hc : IsSelfAdjoint (t • a + u • b) :=
    ((IsSelfAdjoint.all t).smul ha).add ((IsSelfAdjoint.all u).smul hb)
  refine ⟨hc, ?_⟩
  rcases subsingleton_or_nontrivial A with _ | _
  · simp [spectrum.of_subsingleton]
  have hK (c : A) := ContinuousFunctionalCalculus.isCompact_spectrum (R := ℝ) c
  obtain ⟨la, hla⟩ := (hK a).exists_isLeast (ContinuousFunctionalCalculus.spectrum_nonempty a ha)
  obtain ⟨ua, hua⟩ := (hK a).exists_isGreatest (ContinuousFunctionalCalculus.spectrum_nonempty a ha)
  obtain ⟨lb, hlb⟩ := (hK b).exists_isLeast (ContinuousFunctionalCalculus.spectrum_nonempty b hb)
  obtain ⟨ub, hub⟩ := (hK b).exists_isGreatest (ContinuousFunctionalCalculus.spectrum_nonempty b hb)
  have hlo_a : algebraMap ℝ A (min la lb) ≤ a :=
    (algebraMap_le_iff_le_spectrum ha).2 fun x hx => (min_le_left _ _).trans (hla.2 hx)
  have hlo_b : algebraMap ℝ A (min la lb) ≤ b :=
    (algebraMap_le_iff_le_spectrum hb).2 fun x hx => (min_le_right _ _).trans (hlb.2 hx)
  have hhi_a : a ≤ algebraMap ℝ A (max ua ub) :=
    (le_algebraMap_iff_spectrum_le ha).2 fun x hx => (hua.2 hx).trans (le_max_left _ _)
  have hhi_b : b ≤ algebraMap ℝ A (max ua ub) :=
    (le_algebraMap_iff_spectrum_le hb).2 fun x hx => (hub.2 hx).trans (le_max_right _ _)
  have hsplit (r : ℝ) : algebraMap ℝ A r = t • algebraMap ℝ A r + u • algebraMap ℝ A r := by
    rw [← add_smul, htu, one_smul]
  have hlo : algebraMap ℝ A (min la lb) ≤ t • a + u • b := by
    rw [hsplit]
    exact add_le_add (smul_le_smul_of_nonneg_left hlo_a ht) (smul_le_smul_of_nonneg_left hlo_b hu)
  have hhi : t • a + u • b ≤ algebraMap ℝ A (max ua ub) := by
    rw [hsplit (max ua ub)]
    exact add_le_add (smul_le_smul_of_nonneg_left hhi_a ht) (smul_le_smul_of_nonneg_left hhi_b hu)
  have hIcc : Icc (min la lb) (max ua ub) ⊆ s := by
    refine hs.out ?_ ?_
    · rcases min_choice la lb with h | h <;> rw [h]
      exacts [has hla.1, hbs hlb.1]
    · rcases max_choice ua ub with h | h <;> rw [h]
      exacts [has hua.1, hbs hub.1]
  intro x hx
  exact hIcc ⟨(algebraMap_le_iff_le_spectrum hc).1 hlo x hx,
    (le_algebraMap_iff_spectrum_le hc).1 hhi x hx⟩
