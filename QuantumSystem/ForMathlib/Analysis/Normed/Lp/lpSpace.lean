/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# Congruence of `ℓ²` sums and unit basis vectors of `ℓ^p`

## Main definitions

* `lpCongr e` — a family of linear isometric equivalences `G i ≃ₗᵢ G' i` induces
  `lp G 2 ≃ₗᵢ lp G' 2`, componentwise.

## Main results

* `memℓp_congr_linearIsometryEquiv` — componentwise isometries preserve `Memℓp · 2`.
* `lp.norm_single_one` — the standard basis vector `lp.single p i 1` is a unit vector.
-/

@[expose] public section

open scoped ENNReal

section LpCongr

variable {α : Type*} {𝕜 : Type*} [RCLike 𝕜] {G G' : α → Type*}
  [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace 𝕜 (G i)]
  [∀ i, NormedAddCommGroup (G' i)] [∀ i, NormedSpace 𝕜 (G' i)]

/-- A family of isometries preserves `Memℓp`: norms are pointwise unchanged. -/
lemma memℓp_congr_linearIsometryEquiv (e : ∀ i, G i ≃ₗᵢ[𝕜] G' i) {f : ∀ i, G i}
    (hf : Memℓp f 2) : Memℓp (fun i => e i (f i)) 2 := by
  apply Memℓp.of_norm
  have hnorm : (fun i => ‖e i (f i)‖) = fun i => ‖f i‖ := funext fun i => (e i).norm_map (f i)
  rw [hnorm]
  exact hf.norm

/-- A family of linear isometric equivalences `G i ≃ₗᵢ G' i` induces a linear isometric
equivalence between the `ℓ²` sums `lp G 2 ≃ₗᵢ lp G' 2`, applied componentwise. -/
noncomputable def lpCongr (e : ∀ i, G i ≃ₗᵢ[𝕜] G' i) : lp G 2 ≃ₗᵢ[𝕜] lp G' 2 where
  toFun f := ⟨fun i => e i (f i), memℓp_congr_linearIsometryEquiv e (lp.memℓp f)⟩
  invFun g := ⟨fun i => (e i).symm (g i), memℓp_congr_linearIsometryEquiv (fun i => (e i).symm)
    (lp.memℓp g)⟩
  left_inv f := by
    refine Subtype.ext (funext fun i => ?_)
    change (e i).symm (e i (f i)) = f i
    rw [LinearIsometryEquiv.symm_apply_apply]
  right_inv g := by
    refine Subtype.ext (funext fun i => ?_)
    change e i ((e i).symm (g i)) = g i
    rw [LinearIsometryEquiv.apply_symm_apply]
  map_add' x y := by
    refine Subtype.ext (funext fun i => ?_)
    change e i ((x + y) i) = e i (x i) + e i (y i)
    rw [lp.coeFn_add, Pi.add_apply, map_add]
  map_smul' c f := by
    refine Subtype.ext (funext fun i => ?_)
    change e i ((c • f) i) = c • e i (f i)
    rw [lp.coeFn_smul, Pi.smul_apply, map_smul]
  norm_map' f := by
    have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
    rw [lp.norm_eq_tsum_rpow hp, lp.norm_eq_tsum_rpow hp]
    congr 1
    refine tsum_congr fun i => ?_
    congr 1
    exact (e i).norm_map (f i)

end LpCongr

section Single

variable {ι : Type*} {𝕜 : Type*} [NormedRing 𝕜] [NormOneClass 𝕜] [DecidableEq ι] {p : ℝ≥0∞}

/-- The standard basis vector `lp.single p i 1` is a unit vector. -/
lemma lp.norm_single_one (hp : 0 < p) (i : ι) :
    ‖lp.single (E := fun _ : ι => 𝕜) p i (1 : 𝕜)‖ = 1 := by
  rw [lp.norm_single hp, norm_one]

end Single
