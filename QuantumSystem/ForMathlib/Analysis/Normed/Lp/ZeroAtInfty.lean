/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# The c₀-direct sum of a family of normed spaces

For a family `E : ι → Type*` of normed spaces over `𝕜`, the elements `f` of `ℓ^∞(E)` with
`‖f i‖ → 0` along the cofinite filter form a closed subspace `lp.zeroAtInfty 𝕜 E`, the c₀-direct
sum of the family. It is the closure of the finitely supported elements, the algebraic direct sum.
For a family of normed rings it absorbs multiplication on both sides.

## Main definitions

* `lp.zeroAtInfty 𝕜 E`: the c₀-direct sum, as a subspace of `ℓ^∞(E)`.

## Main results

* `lp.isClosed_zeroAtInfty`: the c₀-direct sum is closed.
* **`lp.closure_setOf_finite_support`**: the c₀-direct sum is the closure of the finitely
  supported elements.
* `lp.zeroAtInfty.mul_mem_left`, `lp.zeroAtInfty.mul_mem_right`: the c₀-direct sum of normed
  rings is a two-sided ideal of `ℓ^∞`.
-/

@[expose] public section

open Filter Topology Metric
open scoped ENNReal

namespace lp

section Module

variable (𝕜 : Type*) {ι : Type*} (E : ι → Type*) [NormedField 𝕜] [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace 𝕜 (E i)]

/-- The c₀-direct sum of a family of normed spaces: the elements `f` of `ℓ^∞(E)` with `‖f i‖ → 0`
along the cofinite filter. -/
noncomputable def zeroAtInfty : Submodule 𝕜 (lp E ∞) where
  carrier := {f | Tendsto (fun i ↦ ‖f i‖) cofinite (𝓝 0)}
  zero_mem' := by simpa using tendsto_const_nhds
  add_mem' {f g} hf hg := by
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun i ↦ ?_) (by simpa using hf.add hg)
    rw [coeFn_add, Pi.add_apply]
    exact norm_add_le _ _
  smul_mem' c f hf := by
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun i ↦ ?_) (by simpa using hf.const_mul ‖c‖)
    rw [coeFn_smul, Pi.smul_apply]
    exact (norm_smul c (f i)).le

variable {𝕜 E}

/-- Membership in the c₀-direct sum: `‖f i‖ → 0` along the cofinite filter. -/
lemma mem_zeroAtInfty {f : lp E ∞} :
    f ∈ zeroAtInfty 𝕜 E ↔ Tendsto (fun i ↦ ‖f i‖) cofinite (𝓝 0) :=
  Iff.rfl

/-- The c₀-direct sum is closed in `ℓ^∞(E)`. -/
instance isClosed_zeroAtInfty : IsClosed (zeroAtInfty 𝕜 E : Set (lp E ∞)) := by
  refine isClosed_of_closure_subset fun f hf ↦ ?_
  rw [SetLike.mem_coe, mem_zeroAtInfty]
  refine tendsto_order.2 ⟨fun a ha ↦ .of_forall fun i ↦ ha.trans_le (norm_nonneg _), fun ε hε ↦ ?_⟩
  obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.1 hf (ε / 2) (half_pos hε)
  filter_upwards [(mem_zeroAtInfty.1 hg).eventually (gt_mem_nhds (half_pos hε))] with i hi
  have hfgi : ‖f i - g i‖ ≤ ‖f - g‖ := by
    rw [← Pi.sub_apply, ← coeFn_sub]
    exact norm_apply_le_norm ENNReal.top_ne_zero _ i
  rw [dist_eq_norm] at hfg
  linarith [norm_sub_norm_le (f i) (g i)]

/-- An element supported at one index lies in the c₀-direct sum. -/
lemma single_mem_zeroAtInfty [DecidableEq ι] (i : ι) (a : E i) :
    lp.single ∞ i a ∈ zeroAtInfty 𝕜 E :=
  mem_zeroAtInfty.2 <| tendsto_nhds_of_eventually_eq <|
    (eventually_cofinite_ne i).mono fun j hj ↦ by simp [hj]

/-- The c₀-direct sum is the closure of the finitely supported elements of `ℓ^∞(E)`. -/
theorem closure_setOf_finite_support :
    closure {f : lp E ∞ | {i | f i ≠ 0}.Finite} = zeroAtInfty 𝕜 E := by
  refine subset_antisymm (closure_minimal (fun f hf ↦ ?_) isClosed_zeroAtInfty) fun f hf ↦ ?_
  · exact mem_zeroAtInfty.2 <| tendsto_nhds_of_eventually_eq <|
      hf.eventually_cofinite_notMem.mono fun i hi ↦ by simpa using hi
  · classical
    refine Metric.mem_closure_iff.2 fun ε hε ↦ ?_
    set s := {i | ¬‖f i‖ < ε / 2}
    have hs : s.Finite :=
      eventually_cofinite.1 <| (mem_zeroAtInfty.1 hf).eventually (gt_mem_nhds (half_pos hε))
    have hg : Memℓp (fun i ↦ if i ∈ s then f i else 0) ∞ := by
      refine memℓp_infty ⟨‖f‖, ?_⟩
      rintro _ ⟨i, rfl⟩
      dsimp only
      split_ifs
      · exact norm_apply_le_norm ENNReal.top_ne_zero f i
      · simp
    refine ⟨⟨_, hg⟩, hs.subset fun i hi ↦ ?_, ?_⟩
    · by_contra h
      exact hi (ite_eq_right_iff.2 fun h' ↦ absurd h' h)
    · rw [dist_eq_norm]
      refine (norm_le_of_forall_le (half_pos hε).le fun i ↦ ?_).trans_lt (half_lt_self hε)
      rw [coeFn_sub, Pi.sub_apply]
      change ‖f i - if i ∈ s then f i else 0‖ ≤ ε / 2
      split_ifs with h
      · simpa using (half_pos hε).le
      · simpa using (show ‖f i‖ < ε / 2 by simpa [s] using h).le

end Module

section Ring

variable {𝕜 ι : Type*} {B : ι → Type*} [NormedField 𝕜] [∀ i, NonUnitalNormedRing (B i)]
  [∀ i, NormedSpace 𝕜 (B i)]

/-- The c₀-direct sum of normed rings absorbs multiplication on the left. -/
lemma zeroAtInfty.mul_mem_left (f : lp B ∞) {g : lp B ∞} (hg : g ∈ zeroAtInfty 𝕜 B) :
    f * g ∈ zeroAtInfty 𝕜 B := by
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun i ↦ ?_) (by simpa using hg.const_mul ‖f‖)
  rw [infty_coeFn_mul, Pi.mul_apply]
  exact (norm_mul_le _ _).trans <| by
    gcongr
    exact norm_apply_le_norm ENNReal.top_ne_zero f i

/-- The c₀-direct sum of normed rings absorbs multiplication on the right. -/
lemma zeroAtInfty.mul_mem_right (g : lp B ∞) {f : lp B ∞} (hf : f ∈ zeroAtInfty 𝕜 B) :
    f * g ∈ zeroAtInfty 𝕜 B := by
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun i ↦ ?_) (by simpa using hf.mul_const ‖g‖)
  rw [infty_coeFn_mul, Pi.mul_apply]
  exact (norm_mul_le _ _).trans <| by
    gcongr
    exact norm_apply_le_norm ENNReal.top_ne_zero g i

end Ring

end lp
