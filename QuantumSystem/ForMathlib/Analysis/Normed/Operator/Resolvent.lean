/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# Resolvents of unbounded operators

For a partially defined operator `T` on a normed space, `z` lies in the *resolvent set* if
`z - T : dom T → E` is a bijection with bounded inverse, the *resolvent* `(z - T)⁻¹ : E →L[𝕜] E`.
The sign convention `(z - T)⁻¹` is Mathlib's (`resolvent a r = (r - a)⁻¹`), and outside the
resolvent set the resolvent is the junk value `0`, as Mathlib's is. Having a nonempty resolvent
set forces `T` to be closed (`LinearPMap.isClosed_of_mem_resolventSet`).

## Main definitions

* `LinearPMap.resolventSet T` — the `z` for which `z - T` has a bounded two-sided inverse.
* `LinearPMap.resolvent T z` — that inverse, and `0` outside the resolvent set.

## Main results

* `LinearPMap.resolvent_apply_of_mem_graph` — `(z - T)⁻¹ u = (z - c)⁻¹ u` for an eigenvector
  `T u = c u`.
* `LinearPMap.range_resolvent` — the range of the resolvent is `dom T`; the resolvent is injective
  (`LinearPMap.resolvent_injective`).
* `LinearPMap.norm_resolvent_le` — `‖(z - T)⁻¹‖ ≤ c⁻¹` when `c ‖u‖ ≤ ‖(z - T) u‖` on `dom T`.
* `LinearPMap.resolvent_sub_resolvent` — the resolvent identity
  `(z - T)⁻¹ - (w - T)⁻¹ = (w - z) (w - T)⁻¹ (z - T)⁻¹`; resolvents commute
  (`LinearPMap.commute_resolvent`).
* `LinearPMap.notMem_spectrum_resolvent` — for `z, w` in the resolvent set, `(w - z)⁻¹` is not in
  the spectrum of `(w - T)⁻¹`; equivalently `1 - (w - z) ζ ≠ 0` on that spectrum
  (`LinearPMap.one_sub_mul_ne_zero_of_mem_spectrum`).
* `LinearPMap.isClosed_of_mem_resolventSet` — an operator with nonempty resolvent set is closed.
* `LinearPMap.comp_resolvent_eq_resolvent_comp` — a bounded `V` mapping the graph of `T` into the
  graph of `S` intertwines their resolvents: `V (z - T)⁻¹ = (z - S)⁻¹ V`.
-/

@[expose] public section

namespace LinearPMap

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The **resolvent set** of a partially defined operator `T`: the scalars `z` for which
`z - T : dom T → E` has a bounded two-sided inverse `R`, i.e. `R x ∈ dom T` with
`(z - T) (R x) = x` for all `x`, and `R ((z - T) u) = u` for all `u ∈ dom T`. -/
def resolventSet (T : E →ₗ.[𝕜] E) : Set 𝕜 :=
  {z | ∃ R : E →L[𝕜] E, (∀ x, (R x, z • R x - x) ∈ T.graph) ∧
    ∀ u v, (u, v) ∈ T.graph → R (z • u - v) = u}

open scoped Classical in
/-- The **resolvent** `(z - T)⁻¹` of a partially defined operator, as a bounded operator; it is
`0` when `z` is not in the resolvent set. -/
noncomputable def resolvent (T : E →ₗ.[𝕜] E) (z : 𝕜) : E →L[𝕜] E :=
  if h : z ∈ T.resolventSet then h.choose else 0

variable {T : E →ₗ.[𝕜] E} {z w : 𝕜}

/-- The resolvent maps into the domain, and `(z - T) ((z - T)⁻¹ x) = x`, in graph form. -/
lemma resolvent_mem_graph (hz : z ∈ T.resolventSet) (x : E) :
    (T.resolvent z x, z • T.resolvent z x - x) ∈ T.graph := by
  simp only [resolvent, hz, ↓reduceDIte]
  exact hz.choose_spec.1 x

/-- `(z - T)⁻¹ ((z - T) u) = u` for `u ∈ dom T`, in graph form. -/
lemma resolvent_sub_apply (hz : z ∈ T.resolventSet) {u v : E} (huv : (u, v) ∈ T.graph) :
    T.resolvent z (z • u - v) = u := by
  simp only [resolvent, hz, ↓reduceDIte]
  exact hz.choose_spec.2 u v huv

/-- Outside the resolvent set the resolvent is `0`. -/
lemma resolvent_of_notMem (hz : z ∉ T.resolventSet) : T.resolvent z = 0 := by
  simp only [resolvent, hz, ↓reduceDIte]

/-- The resolvent maps into the domain. -/
lemma resolvent_apply_mem_domain (hz : z ∈ T.resolventSet) (x : E) :
    T.resolvent z x ∈ T.domain :=
  mem_domain_of_mem_graph (resolvent_mem_graph hz x)

/-- On an eigenvector `T u = c u`, the resolvent acts as `(z - T)⁻¹ u = (z - c)⁻¹ u`. -/
lemma resolvent_apply_of_mem_graph (hz : z ∈ T.resolventSet) {u : E} {c : 𝕜}
    (hu : (u, c • u) ∈ T.graph) : T.resolvent z u = (z - c)⁻¹ • u := by
  have h := resolvent_sub_apply hz hu
  rw [← sub_smul, ContinuousLinearMap.map_smul] at h
  rcases eq_or_ne (z - c) 0 with hzc | hzc
  · rw [← h, hzc, zero_smul, smul_zero, ContinuousLinearMap.map_zero]
  calc T.resolvent z u = (z - c)⁻¹ • ((z - c) • T.resolvent z u) := by
        rw [smul_smul, inv_mul_cancel₀ hzc, one_smul]
    _ = (z - c)⁻¹ • u := by rw [h]

/-- The resolvent is the unique bounded two-sided inverse of `z - T`. -/
lemma resolvent_eq_of {R : E →L[𝕜] E} (h₁ : ∀ x, (R x, z • R x - x) ∈ T.graph)
    (h₂ : ∀ u v, (u, v) ∈ T.graph → R (z • u - v) = u) : T.resolvent z = R := by
  have hz : z ∈ T.resolventSet := ⟨R, h₁, h₂⟩
  ext x
  simpa using resolvent_sub_apply hz (h₁ x)

/-- The range of the resolvent is the domain of `T`. -/
lemma range_resolvent (hz : z ∈ T.resolventSet) :
    LinearMap.range (T.resolvent z : E →ₗ[𝕜] E) = T.domain := by
  refine le_antisymm ?_ fun u hu => ⟨z • u - T ⟨u, hu⟩, resolvent_sub_apply hz (T.mem_graph ⟨u, hu⟩)⟩
  rintro _ ⟨x, rfl⟩
  exact resolvent_apply_mem_domain hz x

/-- The resolvent at a point of the resolvent set is injective. -/
lemma resolvent_injective (hz : z ∈ T.resolventSet) : Function.Injective (T.resolvent z) := by
  intro x y hxy
  have hx := resolvent_mem_graph hz x
  have hy := resolvent_mem_graph hz y
  have := T.graph.sub_mem hx hy
  simp only [Prod.mk_sub_mk, hxy, sub_self, sub_sub_sub_cancel_left] at this
  exact (sub_eq_zero.mp (T.graph_fst_eq_zero_snd this rfl)).symm

/-- If `c ‖u‖ ≤ ‖(z - T) u‖` on `dom T`, then `‖(z - T)⁻¹‖ ≤ c⁻¹`. -/
lemma norm_resolvent_le {c : ℝ} (hc : 0 < c)
    (hbdd : ∀ u v, (u, v) ∈ T.graph → c * ‖u‖ ≤ ‖z • u - v‖) : ‖T.resolvent z‖ ≤ c⁻¹ := by
  by_cases hz : z ∈ T.resolventSet
  swap
  · rw [resolvent_of_notMem hz, norm_zero]
    exact inv_nonneg.mpr hc.le
  refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hc.le) fun x => ?_
  rw [inv_mul_eq_div, le_div_iff₀' hc]
  simpa using hbdd _ _ (resolvent_mem_graph hz x)

/-- **Resolvent identity**: `(z - T)⁻¹ - (w - T)⁻¹ = (w - z) (w - T)⁻¹ (z - T)⁻¹`. -/
theorem resolvent_sub_resolvent (hz : z ∈ T.resolventSet) (hw : w ∈ T.resolventSet) :
    T.resolvent z - T.resolvent w = (w - z) • (T.resolvent w * T.resolvent z) := by
  ext x
  have h := resolvent_sub_apply hw (resolvent_mem_graph hz x)
  rw [show w • T.resolvent z x - (z • T.resolvent z x - x) =
      (w - z) • T.resolvent z x + x by module] at h
  simp only [ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul] at h
  simp only [_root_.sub_apply, _root_.smul_apply, mul_apply_eq_comp]
  exact (eq_sub_of_add_eq h).symm

/-- Resolvents commute. -/
theorem commute_resolvent (T : E →ₗ.[𝕜] E) (z w : 𝕜) : Commute (T.resolvent z) (T.resolvent w) := by
  by_cases hz : z ∈ T.resolventSet
  swap
  · rw [resolvent_of_notMem hz]
    exact Commute.zero_left _
  by_cases hw : w ∈ T.resolventSet
  swap
  · rw [resolvent_of_notMem hw]
    exact Commute.zero_right _
  rcases eq_or_ne z w with rfl | hzw
  · exact Commute.refl _
  have h₁ := resolvent_sub_resolvent hz hw
  have h₂ := resolvent_sub_resolvent hw hz
  rw [← neg_sub (T.resolvent z), h₁, show z - w = -(w - z) by abel, neg_smul, neg_inj] at h₂
  exact (smul_right_injective _ (sub_ne_zero.mpr hzw.symm) h₂).symm

/-- If `z` and `w` both lie in the resolvent set, `z ≠ w`, then `(w - z)⁻¹` is not in the spectrum
of the resolvent at `w`: `(w - z)⁻¹ - (w - T)⁻¹` is invertible, with inverse
`(w - z) (1 + (w - z) (z - T)⁻¹)`. -/
theorem notMem_spectrum_resolvent (hw : w ∈ T.resolventSet) (hz : z ∈ T.resolventSet)
    (hne : z ≠ w) : (w - z)⁻¹ ∉ spectrum 𝕜 (T.resolvent w) := by
  have hc : w - z ≠ 0 := sub_ne_zero.mpr hne.symm
  have hid := resolvent_sub_resolvent hz hw
  have hcomm := (T.commute_resolvent z w).eq
  have hx : ∀ x, T.resolvent z x - T.resolvent w x = (w - z) • T.resolvent w (T.resolvent z x) :=
    fun x => congrArg (fun L : E →L[𝕜] E => L x) hid
  have hx' : ∀ x, T.resolvent z (T.resolvent w x) = T.resolvent w (T.resolvent z x) :=
    fun x => congrArg (fun L : E →L[𝕜] E => L x) hcomm
  have hrw : (w - z)⁻¹ • (1 : E →L[𝕜] E) - T.resolvent w =
      (w - z)⁻¹ • (1 - (w - z) • T.resolvent w) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [spectrum.notMem_iff, Algebra.algebraMap_eq_smul_one, hrw]
  refine ⟨⟨_, (w - z) • (1 + (w - z) • T.resolvent z), ?_, ?_⟩, rfl⟩
  · rw [smul_mul_smul, inv_mul_cancel₀ hc, one_smul]
    ext x
    simp only [mul_apply_eq_comp, _root_.sub_apply,
      _root_.add_apply, _root_.smul_apply, one_apply_eq_self, ContinuousLinearMap.map_add,
      ContinuousLinearMap.map_smul]
    linear_combination (norm := module) (w - z) • hx x
  · rw [smul_mul_smul, mul_inv_cancel₀ hc, one_smul]
    ext x
    simp only [mul_apply_eq_comp, _root_.sub_apply,
      _root_.add_apply, _root_.smul_apply, one_apply_eq_self, ContinuousLinearMap.map_sub,
      ContinuousLinearMap.map_smul]
    linear_combination (norm := module) (w - z) • hx x - (w - z) ^ 2 • hx' x

/-- For `z, w` in the resolvent set, `1 - (w - z) ζ ≠ 0` for every `ζ` in the spectrum of
`(w - T)⁻¹`: the function `ζ ↦ ζ / (1 - (w - z) ζ)`, which sends `(w - T)⁻¹` to `(z - T)⁻¹`, has
no pole on that spectrum. -/
theorem one_sub_mul_ne_zero_of_mem_spectrum (hw : w ∈ T.resolventSet) (hz : z ∈ T.resolventSet)
    {ζ : 𝕜} (hζ : ζ ∈ spectrum 𝕜 (T.resolvent w)) : 1 - (w - z) * ζ ≠ 0 := by
  intro h
  have hc : w - z ≠ 0 := by
    rintro hc
    rw [hc, zero_mul, sub_zero] at h
    exact one_ne_zero h
  have hzw : z ≠ w := fun h => hc (by rw [h, sub_self])
  exact notMem_spectrum_resolvent hw hz hzw (eq_inv_of_mul_eq_one_right (sub_eq_zero.mp h).symm ▸ hζ)

/-- A partially defined operator with nonempty resolvent set is closed: its graph is the range
of `x ↦ ((z - T)⁻¹ x, z (z - T)⁻¹ x - x)`, which has the continuous left inverse
`(a, b) ↦ z a - b`. -/
theorem isClosed_of_mem_resolventSet (hz : z ∈ T.resolventSet) : T.IsClosed := by
  let φ : E → E × E := fun x => (T.resolvent z x, z • T.resolvent z x - x)
  let ψ : E × E → E := fun p => z • p.1 - p.2
  have hgraph : (T.graph : Set (E × E)) = {p | φ (ψ p) = p} := by
    ext ⟨u, v⟩
    simp only [SetLike.mem_coe, Set.mem_ofPred_eq, φ, ψ]
    constructor
    · intro h
      rw [resolvent_sub_apply hz h, sub_sub_cancel]
    · intro h
      rw [← h]
      exact resolvent_mem_graph hz _
  rw [IsClosed, hgraph]
  exact isClosed_eq (by fun_prop) continuous_id

section Intertwine

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {S : F →ₗ.[𝕜] F} {V : E →L[𝕜] F}

/-- A bounded operator `V` mapping the graph of `T` into the graph of `S` (so `V (dom T) ⊆ dom S`
and `S V = V T` on `dom T`) intertwines the resolvents: `V (z - T)⁻¹ = (z - S)⁻¹ V` for `z` in
both resolvent sets. -/
theorem comp_resolvent_eq_resolvent_comp (hzT : z ∈ T.resolventSet) (hzS : z ∈ S.resolventSet)
    (hV : ∀ u v, (u, v) ∈ T.graph → (V u, V v) ∈ S.graph) :
    V ∘L T.resolvent z = S.resolvent z ∘L V := by
  ext x
  have h := resolvent_sub_apply hzS (hV _ _ (resolvent_mem_graph hzT x))
  rw [show V (z • T.resolvent z x - x) = z • V (T.resolvent z x) - V x by
    rw [ContinuousLinearMap.map_sub, ContinuousLinearMap.map_smul], sub_sub_cancel] at h
  exact h.symm

end Intertwine

end LinearPMap
