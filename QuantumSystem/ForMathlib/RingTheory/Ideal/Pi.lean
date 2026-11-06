/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.SimpleRing.Congr

/-!
# Two-sided ideals of a finite product of simple rings

An ideal of a finite product of rings is the product of its images under the projections
(`Ideal.piOrderIso`). When the factors are simple, each image of a two-sided ideal is `⊥` or `⊤`,
so a two-sided ideal is the set of elements vanishing outside a set of indices.

## Main results

* `Ideal.eq_pi_map_evalRingHom`: an ideal of a finite product is the product of its projections.
* **`Ideal.IsTwoSided.exists_set_forall_mem_iff`**: a two-sided ideal of a finite product of
  simple rings is the set of elements vanishing outside a set of indices.
-/

@[expose] public section

namespace Ideal

variable {ι : Type*} {R : ι → Type*}

/-- An ideal of a finite product is the product of its images under the projections. -/
lemma eq_pi_map_evalRingHom [Finite ι] [∀ i, Semiring (R i)] (I : Ideal (Π i, R i)) :
    I = Ideal.pi fun i ↦ I.map (Pi.evalRingHom R i) :=
  (Ideal.piOrderIso.symm_apply_apply I).symm

variable [∀ i, Ring (R i)] [∀ i, IsSimpleRing (R i)] (I : Ideal (Π i, R i)) [I.IsTwoSided]

/-- The image of a two-sided ideal under the projection onto a simple factor is `⊥` or `⊤`. -/
private lemma IsTwoSided.map_evalRingHom_eq_bot_or_eq_top (i : ι) :
    I.map (Pi.evalRingHom R i) = ⊥ ∨ I.map (Pi.evalRingHom R i) = ⊤ :=
  (isSimpleRing_iff_isTwoSided_imp.mp inferInstance).2 _ inferInstance

/-- A two-sided ideal of a finite product of simple rings is the set of elements vanishing
outside a set of indices. -/
theorem IsTwoSided.exists_set_forall_mem_iff [Finite ι] :
    ∃ S : Set ι, ∀ x, x ∈ I ↔ ∀ i ∉ S, x i = 0 := by
  refine ⟨{i | I.map (Pi.evalRingHom R i) = ⊤}, fun x ↦ ?_⟩
  conv_lhs => rw [I.eq_pi_map_evalRingHom, Ideal.mem_pi]
  refine ⟨fun h i hi ↦ ?_, fun h i ↦ ?_⟩
  · rcases IsTwoSided.map_evalRingHom_eq_bot_or_eq_top I i with h' | h'
    · simpa [h'] using h i
    · exact absurd h' hi
  · rcases IsTwoSided.map_evalRingHom_eq_bot_or_eq_top I i with h' | h'
    · rw [h', Ideal.mem_bot]
      exact h i (by rw [Set.mem_ofPred_eq, h']; exact bot_ne_top)
    · rw [h']; trivial

end Ideal
