/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.PartitionOfUnity

/-!
# Uniform approximation along a partition of unity

On a compact space `X`, finitely many continuous functions `g k : X → E` into a normed space are
uniformly approximated, within any `ε > 0`, by the combinations `∑ j, φ j y • g k (x j)` of
finitely many nonnegative continuous functions `φ j` with `∑ j, φ j ≤ 1` and points `x j`. The
`φ j` are a partition of unity subordinate to a cover by sets on which every `g k` varies by less
than `ε`. It is taken on the image of `y ↦ (g k y)_k`, a compact pseudometric space, and pulled
back to `X`, so that `X` need not be Hausdorff. When every `g k` vanishes at a point `x₀`, the
`φ j` can be taken to vanish at `x₀`: the open set on which every `g k` is smaller than `ε` covers
`x₀` and contributes nothing.

## Main results

* `ContinuousMap.exists_approx_partitionOfUnity` — the approximation, with every `φ j` vanishing at a
  common zero of the `g k`.
* `ContinuousMap.exists_approx_partitionOfUnity_sum_eq_one` — the approximation without a common
  zero, with `∑ j, φ j = 1`.
-/

@[expose] public section

open Set

namespace ContinuousMap

variable {X E K : Type*} [TopologicalSpace X] [CompactSpace X]
  [SeminormedAddCommGroup E] [NormedSpace ℝ E] [Finite K]

/-- **Uniform approximation along a partition of unity.** On a compact space, finitely many
continuous functions `g k` vanishing at `x₀` are approximated within `ε` by
`∑ j, φ j y • g k (x j)`, for nonnegative continuous functions `φ j` with `∑ j, φ j ≤ 1` that vanish
at `x₀`. No separation axiom is needed: the partition of unity is taken on the image of
`y ↦ (g k y)_k`, a compact pseudometric space, and pulled back. -/
theorem exists_approx_partitionOfUnity (g : K → C(X, E)) (x₀ : X) (hg : ∀ k, g k x₀ = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (φ : Fin n → C(X, ℝ)) (x : Fin n → X), (∀ j y, 0 ≤ φ j y) ∧
      (∀ y, ∑ j, φ j y ≤ 1) ∧ (∀ j, φ j x₀ = 0) ∧
      ∀ k y, ‖g k y - ∑ j, φ j y • g k (x j)‖ ≤ ε := by
  classical
  have := Fintype.ofFinite K
  -- all the `g k` at once, and the compact pseudometric space of their values
  let G : X → K → E := fun y k => g k y
  have hG : Continuous G := continuous_pi fun k => (g k).continuous
  let Y := Set.range G
  have : CompactSpace Y := isCompact_iff_compactSpace.1 (isCompact_range hG)
  let GY : C(X, Y) := ⟨fun y => ⟨G y, y, rfl⟩, hG.subtype_mk _⟩
  -- the point attached to an index of the cover
  let pt : Option X → X := fun i => i.elim x₀ id
  let V : Option X → Set (K → E) := fun i => i.elim {v | ∀ k, ‖v k‖ < ε}
    fun x => {v | ∀ k, ‖v k - g k x‖ < ε} ∩ {v | ∃ k, ε / 2 < ‖v k‖}
  have hVo (i : Option X) : IsOpen (V i) := by
    cases i with
    | none =>
      simp only [V, Option.elim_none, ofPred_forall]
      exact isOpen_iInter_of_finite fun k => isOpen_lt (by fun_prop) continuous_const
    | some x =>
      simp only [V, Option.elim_some, ofPred_forall, ofPred_exists]
      exact (isOpen_iInter_of_finite fun k => isOpen_lt (by fun_prop) continuous_const).inter
        (isOpen_iUnion fun k => isOpen_lt continuous_const (by fun_prop))
  have hpt (i : Option X) (y : X) (hy : G y ∈ V i) (k : K) : ‖g k y - g k (pt i)‖ < ε := by
    cases i with
    | none => simpa [V, G, pt, hg] using hy k
    | some x => exact hy.1 k
  have hcov (y : X) : ∃ i, G y ∈ V i := by
    by_cases h : ∀ k, ‖g k y‖ < ε
    · exact ⟨none, h⟩
    · push Not at h
      obtain ⟨k, hk⟩ := h
      exact ⟨some y, fun k' => by simpa [G] using hε, k, by linarith⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun i => G ⁻¹' V i)
    (fun i => (hVo i).preimage hG) fun y _ => mem_iUnion.2 (hcov y)
  obtain ⟨ψ', hψ'⟩ := PartitionOfUnity.exists_isSubordinate (X := Y) isClosed_univ
    (fun i : t => Subtype.val ⁻¹' V i) (fun i => (hVo i).preimage continuous_subtype_val)
    fun z _ => by
      obtain ⟨_, y, rfl⟩ := z
      obtain ⟨i, hi, hy⟩ := mem_iUnion₂.1 (ht (mem_univ y))
      exact mem_iUnion.2 ⟨⟨i, hi⟩, hy⟩
  -- the partition of unity pulled back to `X`
  let ψ : t → C(X, ℝ) := fun i => (ψ' i).comp GY
  have hψ0 (i : t) (y : X) : 0 ≤ ψ i y := ψ'.nonneg i (GY y)
  have hsum (y : X) : ∑ i : t, ψ i y = 1 := by
    rw [← finsum_eq_sum_of_fintype]
    exact ψ'.sum_eq_one (mem_univ (GY y))
  have hψV (i : t) (y : X) (h : ψ i y ≠ 0) : G y ∈ V i :=
    hψ' i (subset_tsupport _ (Function.mem_support.2 h))
  -- each index contributes within `ε` of `g k y`
  have hterm (i : t) (y : X) (k : K) :
      ψ i y * ‖g k y - g k (pt i)‖ ≤ ψ i y * ε := by
    by_cases h : ψ i y = 0
    · rw [h, zero_mul, zero_mul]
    · exact mul_le_mul_of_nonneg_left (hpt i y (hψV i y h) k).le (hψ0 i y)
  let e := (Fintype.equivFin t).symm
  refine ⟨Fintype.card t, fun j => if (e j : Option X) = none then 0 else ψ (e j),
    fun j => pt (e j), fun j y => ?_, fun y => ?_, fun j => ?_, fun k y => ?_⟩
  · dsimp only
    split_ifs
    · exact le_rfl
    · exact hψ0 _ y
  · calc ∑ j, (if (e j : Option X) = none then 0 else ψ (e j)) y ≤ ∑ j, ψ (e j) y :=
          Finset.sum_le_sum fun j _ => by
            split_ifs
            · exact hψ0 _ y
            · exact le_rfl
      _ = 1 := by rw [e.sum_comp fun i => ψ i y, hsum]
  · dsimp only
    split_ifs with h
    · rfl
    · by_contra hx
      have hx' : G x₀ ∈ V (e j : Option X) := hψV (e j) x₀ hx
      cases hi : (e j : Option X) with
      | none => exact h hi
      | some x =>
        rw [hi] at hx'
        obtain ⟨k, hk⟩ := hx'.2
        simp only [G, hg k, norm_zero] at hk
        linarith
  · -- the terms of the zero index vanish, since `g k x₀ = 0`
    have hcoef (j : Fin (Fintype.card t)) :
        (if (e j : Option X) = none then 0 else ψ (e j)) y • g k (pt (e j)) =
          ψ (e j) y • g k (pt (e j)) := by
      split_ifs with h
      · rw [h]
        simp [pt, hg]
      · rfl
    simp only [hcoef]
    rw [e.sum_comp fun i => ψ i y • g k (pt i)]
    have hy : g k y = ∑ i : t, ψ i y • g k y := by rw [← Finset.sum_smul, hsum, one_smul]
    calc ‖g k y - ∑ i : t, ψ i y • g k (pt i)‖ = ‖∑ i : t, ψ i y • (g k y - g k (pt i))‖ := by
          rw [hy, ← Finset.sum_sub_distrib]
          simp only [smul_sub]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← hy]
      _ ≤ ∑ i : t, ψ i y * ‖g k y - g k (pt i)‖ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          rw [norm_smul, Real.norm_of_nonneg (hψ0 i y)]
      _ ≤ ∑ i : t, ψ i y * ε := Finset.sum_le_sum fun i _ => hterm i y k
      _ = ε := by rw [← Finset.sum_mul, hsum, one_mul]

/-- **Uniform approximation along a partition of unity, without a common zero.** On a compact space,
finitely many continuous functions `g k` are approximated within `ε` by `∑ j, φ j y • g k (x j)`,
for nonnegative continuous functions `φ j` with `∑ j, φ j = 1`: the functions `g k - g k x₀` vanish
at `x₀`, and `1 - ∑ j, φ j` at the point `x₀` completes their approximation to a partition of
unity. -/
theorem exists_approx_partitionOfUnity_sum_eq_one (g : K → C(X, E)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (φ : Fin n → C(X, ℝ)) (x : Fin n → X), (∀ j y, 0 ≤ φ j y) ∧
      (∀ y, ∑ j, φ j y = 1) ∧ ∀ k y, ‖g k y - ∑ j, φ j y • g k (x j)‖ ≤ ε := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · exact ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun y => hX.elim y, fun _ y => hX.elim y⟩
  obtain ⟨n, φ, x, hφ0, hφ1, -, happ⟩ := exists_approx_partitionOfUnity
    (fun k => g k - ContinuousMap.const X (g k x₀)) x₀ (fun k => by simp) hε
  refine ⟨n + 1, Fin.cons (1 - ∑ j, φ j) φ, Fin.cons x₀ x, fun j y => ?_, fun y => ?_,
    fun k y => ?_⟩
  · cases j using Fin.cases with
    | zero => simpa using hφ1 y
    | succ j => simpa using hφ0 j y
  · simp [Fin.sum_univ_succ]
  · have h := happ k y
    simp only [ContinuousMap.sub_apply, ContinuousMap.const_apply, smul_sub,
      Finset.sum_sub_distrib, ← Finset.sum_smul] at h
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, ContinuousMap.sub_apply, ContinuousMap.one_apply,
      ContinuousMap.coe_sum, Finset.sum_apply, sub_smul, one_smul]
    rwa [show g k y - (g k x₀ - (∑ j, φ j y) • g k x₀ + ∑ j, φ j y • g k (x j)) =
      g k y - g k x₀ - (∑ j, φ j y • g k (x j) - (∑ j, φ j y) • g k x₀) by abel]

end ContinuousMap
