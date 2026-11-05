/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.StarSubalgebra

/-!
# The range of a ⋆-homomorphism between C⋆-algebras is closed

Every value `π a` of a unital ⋆-homomorphism `π : A → B` between C⋆-algebras has a preimage of the
same norm (`StarAlgHom.exists_apply_eq_norm_le`): with `r = ‖π a‖` and `g(t) = r / √(max t r²)`,
the element `b = a g(a⋆ a)` satisfies `b⋆ b = h(a⋆ a)` with `h(t) = t g(t)² = min t r²`, so
`‖b‖ ≤ r`, and `π b = π a · g(π(a)⋆ π(a)) = π a`, as `g = 1` on `[0, r²]`, which contains the spectrum
of `π(a)⋆ π(a)`. A point `y` of the closure of the range is then a limit `yₙ → y` of values with
`‖yₙ₊₁ - yₙ‖ ≤ 2 · 2⁻ⁿ`; the lifts of the differences form a summable series, whose sum is sent to
`y`. So the range is closed (`StarAlgHom.isClosed_range`).

Continuous ⋆-homomorphisms out of a topological ⋆-algebra agree when they agree on a set that
generates it as a closed ⋆-subalgebra (`StarAlgHom.ext_of_topologicalClosure_adjoin_eq_top`), the
topological form of `StarAlgHom.ext_of_adjoin_eq_top`.

## Main results

* `StarAlgHom.exists_apply_eq_norm_le` — values of `π` have preimages of the same norm.
* **`StarAlgHom.isClosed_range`** — the range of `π` is closed.
* `StarAlgHom.ext_of_topologicalClosure_adjoin_eq_top` — ⋆-homomorphisms agreeing on a topological
  generating set agree.
-/

@[expose] public section

open scoped CStarAlgebra
open Filter Topology

namespace StarAlgHom

/-- Continuous ⋆-homomorphisms `f, g : A → B` agree when they agree on a set `s` whose generated
closed ⋆-subalgebra is `A`: their equalizer is a closed ⋆-subalgebra containing `s`. -/
lemma ext_of_topologicalClosure_adjoin_eq_top {R A B : Type*} [CommSemiring R] [StarRing R]
    [TopologicalSpace A] [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]
    [IsSemitopologicalSemiring A] [ContinuousStar A] [TopologicalSpace B] [Semiring B] [Algebra R B]
    [StarRing B] [T2Space B] {s : Set A} (h : (StarAlgebra.adjoin R s).topologicalClosure = ⊤)
    {f g : A →⋆ₐ[R] B} (hf : Continuous f) (hg : Continuous g) (hs : s.EqOn f g) : f = g := by
  have hcl := StarSubalgebra.topologicalClosure_minimal (adjoin_le_equalizer f g hs) (isClosed_eq hf hg)
  rw [h] at hcl
  exact StarAlgHom.ext fun x => hcl trivial

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

/-- **Lifts of the same norm.** Every value `π a` of a unital ⋆-homomorphism between C⋆-algebras is
`π b` for some `b` with `‖b‖ ≤ ‖π a‖`. With `r = ‖π a‖` and `g(t) = r / √(max t r²)`, take
`b = a g(a⋆ a)`: then `b⋆ b = h(a⋆ a)` with `h(t) = t g(t)² = min t r²`, so `‖b‖² ≤ r²`, and
`π b = π a · g(π(a)⋆ π(a)) = π a`, as `g = 1` on `[0, r²]`, which contains the spectrum of
`π(a)⋆ π(a)`. -/
lemma exists_apply_eq_norm_le (π : A →⋆ₐ[ℂ] B) (a : A) : ∃ b, π b = π a ∧ ‖b‖ ≤ ‖π a‖ := by
  let := CStarAlgebra.spectralOrder A
  have := CStarAlgebra.spectralOrderedRing A
  rcases eq_or_lt_of_le (norm_nonneg (π a)) with hr0 | hr0
  · exact ⟨0, by rw [map_zero, norm_eq_zero.mp hr0.symm], by rw [norm_zero]; exact norm_nonneg _⟩
  have : Nontrivial B := ⟨⟨π a, 0, norm_pos_iff.mp hr0⟩⟩
  let g : ℝ → ℝ := fun t => ‖π a‖ / Real.sqrt (max t (‖π a‖ ^ 2))
  have hpos : ∀ t, 0 < Real.sqrt (max t (‖π a‖ ^ 2)) := fun t =>
    Real.sqrt_pos.mpr ((pow_pos hr0 2).trans_le (le_max_right _ _))
  have hg : Continuous g :=
    continuous_const.div (Real.continuous_sqrt.comp (continuous_id.max continuous_const))
      fun t => (hpos t).ne'
  have hg1 : ∀ t, t ≤ ‖π a‖ ^ 2 → g t = 1 := fun t ht => by
    simp only [g, max_eq_right ht, Real.sqrt_sq (norm_nonneg _), div_self hr0.ne']
  have hg0 : ∀ t, 0 ≤ g t := fun t => div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  have hxsa : IsSelfAdjoint (star a * a) := IsSelfAdjoint.star_mul_self a
  refine ⟨a * cfc g (star a * a), ?_, ?_⟩
  · rw [map_mul, StarAlgHom.map_cfc π g (star a * a) hg.continuousOn (map_continuous π) hxsa
      (hxsa.map π)]
    have : cfc g (π (star a * a)) = 1 := by
      refine (cfc_congr fun t ht => ?_).trans (cfc_one (R := ℝ) (ha := hxsa.map π))
      have h := spectrum.norm_le_norm_of_mem ht
      rw [map_mul, map_star, CStarRing.norm_star_mul_self, ← sq, Real.norm_eq_abs] at h
      exact hg1 t ((le_abs_self t).trans h)
    rw [this, mul_one]
  · have hb : star (a * cfc g (star a * a)) * (a * cfc g (star a * a)) =
        cfc g (star a * a) * cfc (fun t : ℝ => t) (star a * a) * cfc g (star a * a) := by
      rw [star_mul, (cfc_predicate g (star a * a)).star_eq, cfc_id' ℝ (star a * a) hxsa]
      noncomm_ring
    have h2 : ‖a * cfc g (star a * a)‖ * ‖a * cfc g (star a * a)‖ ≤ ‖π a‖ * ‖π a‖ := by
      rw [← CStarRing.norm_star_mul_self, hb, ← cfc_mul g (fun t : ℝ => t) (star a * a)
        hg.continuousOn continuous_id.continuousOn, ← cfc_mul (fun t => g t * t) g (star a * a)
        (hg.mul continuous_id).continuousOn hg.continuousOn, ← sq]
      refine norm_cfc_le (by positivity) fun t ht => ?_
      have ht0 : 0 ≤ t := spectrum_nonneg_of_nonneg (star_mul_self_nonneg a) ht
      change ‖g t * t * g t‖ ≤ ‖π a‖ ^ 2
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (hg0 t) ht0) (hg0 t))]
      rcases le_or_gt t (‖π a‖ ^ 2) with h | h
      · rw [hg1 t h, one_mul, mul_one]
        exact h
      · have hgt : g t = ‖π a‖ / Real.sqrt t := by simp only [g, max_eq_left h.le]
        have htne : t ≠ 0 := ((sq_nonneg _).trans_lt h).ne'
        rw [hgt, div_mul_eq_mul_div, div_mul_div_comm, Real.mul_self_sqrt ht0, mul_right_comm,
          mul_div_assoc, div_self htne, mul_one, sq]
    exact (mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _)).mpr h2

/-- **The range of a unital ⋆-homomorphism between C⋆-algebras is closed.** For `y` in the closure,
choose values `yₙ` with `‖y - yₙ‖ ≤ 2⁻ⁿ` and lift the differences `yₙ₊₁ - yₙ` with the same norm
(`StarAlgHom.exists_apply_eq_norm_le`); the lifts are summable, and their sum, plus a lift of
`y₀`, is sent to `y`. -/
theorem isClosed_range (π : A →⋆ₐ[ℂ] B) : IsClosed (Set.range π) := by
  refine isClosed_of_closure_subset fun y hy => ?_
  have hy' : ∀ n : ℕ, ∃ a : A, ‖y - π a‖ ≤ (1 / 2 : ℝ) ^ n := fun n => by
    obtain ⟨_, ⟨a, rfl⟩, h⟩ := Metric.mem_closure_iff.mp hy _ (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n)
    exact ⟨a, by rw [← dist_eq_norm]; exact h.le⟩
  choose a ha using hy'
  have hd : ∀ n, ∃ b : A, π b = π (a (n + 1) - a n) ∧ ‖b‖ ≤ 2 * (1 / 2 : ℝ) ^ n := fun n => by
    obtain ⟨b, hb, hnb⟩ := exists_apply_eq_norm_le π (a (n + 1) - a n)
    refine ⟨b, hb, hnb.trans ?_⟩
    rw [map_sub, show π (a (n + 1)) - π (a n) = (y - π (a n)) - (y - π (a (n + 1))) by abel]
    refine (norm_sub_le _ _).trans ?_
    have := ha (n + 1)
    have hp : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
    rw [pow_succ] at this
    linarith [ha n]
  choose b hb hnb using hd
  have hsum : Summable b :=
    Summable.of_norm_bounded ((summable_geometric_two).mul_left 2) hnb
  refine ⟨a 0 + ∑' n, b n, ?_⟩
  have hπ : HasSum (fun n => π (b n)) (π (∑' n, b n)) := hsum.hasSum.map π (map_continuous π)
  have hlim : Tendsto (fun n => π (a n)) atTop (𝓝 y) := by
    refine tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero (g := fun n => (1 / 2 : ℝ) ^ n)
      (fun _ => norm_nonneg _) (fun n => by rw [norm_sub_rev]; exact ha n) ?_)
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hpartial : ∀ n, ∑ k ∈ Finset.range n, π (b k) = π (a n) - π (a 0) := fun n => by
    simp only [hb, map_sub]
    exact Finset.sum_range_sub (fun k => π (a k)) n
  have h := hπ.tendsto_sum_nat
  simp only [hpartial] at h
  rw [map_add, tendsto_nhds_unique h (hlim.sub_const _), add_sub_cancel]

end StarAlgHom
