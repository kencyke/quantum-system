/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.EReal.Operations

/-!
# Finite sums in `EReal`

The coercion `ℝ → EReal` commutes with finite sums (`EReal.coe_finsetSum`), and a finite sum of
extended reals none of which is `⊥` is `⊤` as soon as one term is `⊤` (`EReal.finsetSum_eq_top`).

## TODO

Newer Mathlib provides `EReal.coe_finsetSum` itself. When the Mathlib pin is bumped, delete the
copy here (and this file, if Mathlib also covers the other two lemmas).
-/

@[expose] public section

namespace EReal

variable {ι : Type*}

/-- The coercion `ℝ → EReal` commutes with finite sums. -/
@[simp, norm_cast]
lemma coe_finsetSum (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, (f i : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, coe_add, ih]

/-- A finite sum of extended reals none of which is `⊥` is not `⊥`. -/
lemma finsetSum_ne_bot {s : Finset ι} {f : ι → EReal} (h : ∀ i ∈ s, f i ≠ ⊥) :
    ∑ i ∈ s, f i ≠ ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact add_ne_bot_iff.mpr ⟨h i (Finset.mem_insert_self i s),
      ih fun j hj => h j (Finset.mem_insert_of_mem hj)⟩

/-- A finite sum of extended reals none of which is `⊥` is `⊤` as soon as one term is `⊤`. -/
lemma finsetSum_eq_top {s : Finset ι} {f : ι → EReal} (hbot : ∀ i ∈ s, f i ≠ ⊥) {i : ι}
    (hi : i ∈ s) (htop : f i = ⊤) : ∑ j ∈ s, f j = ⊤ := by
  classical
  rw [← Finset.add_sum_erase s f hi, htop]
  exact top_add_of_ne_bot (finsetSum_ne_bot fun j hj => hbot j (Finset.mem_of_mem_erase hj))

end EReal
