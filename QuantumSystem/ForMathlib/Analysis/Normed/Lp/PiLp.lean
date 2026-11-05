/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Coordinate inclusions into `PiLp`

## Main definitions

* `LinearIsometry.piLpSingle p 𝕜 β i` — `PiLp.single p i` as a linear isometry
  `β i →ₗᵢ[𝕜] PiLp p β`, the `PiLp` version of `LinearIsometry.single`.

## Main results

* `PiLp.inner_single_left`, `PiLp.inner_single_right` — the inner product with `PiLp.single 2 i a`
  is the inner product with the `i`-th coordinate.
-/

@[expose] public section

open scoped ENNReal InnerProductSpace

variable (p : ℝ≥0∞) [Fact (1 ≤ p)] (𝕜 : Type*) {ι : Type*} [Fintype ι] [DecidableEq ι]
  (β : ι → Type*)

/-- The inclusion `a ↦ PiLp.single p i a` of the `i`-th coordinate as a linear isometry. -/
protected noncomputable def LinearIsometry.piLpSingle [Semiring 𝕜] [∀ i, SeminormedAddCommGroup (β i)]
    [∀ i, Module 𝕜 (β i)] (i : ι) : β i →ₗᵢ[𝕜] PiLp p β where
  toLinearMap := (WithLp.linearEquiv p 𝕜 (∀ j, β j)).symm.toLinearMap ∘ₗ LinearMap.single 𝕜 β i
  norm_map' := PiLp.norm_single p β i

variable {p 𝕜 β}

/-- `LinearIsometry.piLpSingle p 𝕜 β i` is `PiLp.single p i`. -/
@[simp]
lemma LinearIsometry.piLpSingle_apply [Semiring 𝕜] [∀ i, SeminormedAddCommGroup (β i)]
    [∀ i, Module 𝕜 (β i)] (i : ι) (a : β i) :
    LinearIsometry.piLpSingle p 𝕜 β i a = PiLp.single p i a :=
  rfl

variable [RCLike 𝕜] [∀ i, NormedAddCommGroup (β i)] [∀ i, InnerProductSpace 𝕜 (β i)]

/-- The inner product with `PiLp.single 2 i a` on the left is that of `a` with the `i`-th
coordinate. -/
theorem PiLp.inner_single_left (i : ι) (a : β i) (v : PiLp 2 β) :
    ⟪PiLp.single 2 i a, v⟫_𝕜 = ⟪a, v i⟫_𝕜 := by
  rw [PiLp.inner_apply, Finset.sum_eq_single i (fun j _ hj => by
    rw [PiLp.single_eq_of_ne 2 hj, inner_zero_left]) (fun h => absurd (Finset.mem_univ i) h),
    PiLp.single_eq_same 2]

/-- The inner product with `PiLp.single 2 i a` on the right is that of the `i`-th coordinate
with `a`. -/
theorem PiLp.inner_single_right (i : ι) (a : β i) (v : PiLp 2 β) :
    ⟪v, PiLp.single 2 i a⟫_𝕜 = ⟪v i, a⟫_𝕜 := by
  rw [← inner_conj_symm, PiLp.inner_single_left, inner_conj_symm]
