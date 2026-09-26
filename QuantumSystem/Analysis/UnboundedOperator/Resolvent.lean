/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.LinearPMap.Positive
public import QuantumSystem.ForMathlib.Analysis.Normed.Operator.Banach
public import QuantumSystem.ForMathlib.Analysis.Normed.Operator.Resolvent
public import QuantumSystem.ForMathlib.LinearAlgebra.LinearPMap

/-!
# Resolvents of unbounded operators on Hilbert spaces

Membership criteria for the resolvent set (`LinearPMap.resolventSet`, defined for normed spaces in
`QuantumSystem.ForMathlib.Analysis.Normed.Operator.Resolvent`) of operators on a Hilbert space,
and the adjoint of a resolvent.

## Main results

* `LinearPMap.mem_resolventSet_of_bounded_below` — a closed, densely defined `T` with
  `c ‖u‖ ≤ ‖(z - T) u‖` (`c > 0`) and `ker (z̄ - T†) = 0` has `z` in its resolvent set.
* `IsSelfAdjoint.mem_resolventSet` — for self-adjoint `A`, every `z` with `im z ≠ 0` lies in the
  resolvent set, and `‖(z - A)⁻¹‖ ≤ |im z|⁻¹` (`IsSelfAdjoint.norm_resolvent_le`).
* `LinearPMap.IsPositive.mem_resolventSet` — for positive self-adjoint `A`, every `z` with
  `re z < 0` lies in the resolvent set, and `‖(z - A)⁻¹‖ ≤ (-re z)⁻¹`
  (`LinearPMap.IsPositive.norm_resolvent_le`).
* `LinearPMap.adjoint_resolvent`, `LinearPMap.conj_mem_resolventSet_adjoint` — for densely defined
  `T` and `z` in its resolvent set, `z̄` lies
  in the resolvent set of `T†` and `((z - T)⁻¹)† = (z̄ - T†)⁻¹`; `IsSelfAdjoint.adjoint_resolvent`
  is the self-adjoint case.
* `LinearPMap.resolvent_smul` — `(z - c T)⁻¹ = c⁻¹ (c⁻¹ z - T)⁻¹`.
* `IsSelfAdjoint.im_sub_inv_eq_zero_of_mem_spectrum` — the spectrum of `(w - A)⁻¹` lies in
  `{0} ∪ {(w - λ)⁻¹ | λ ∈ ℝ}` for self-adjoint `A`.
-/

@[expose] public section

open RCLike
open scoped ComplexConjugate LinearPMap

namespace LinearPMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

variable {T : E →ₗ.[𝕜] E} {z w : 𝕜}

/-- For a symmetric operator, `|im z| ‖u‖ ≤ ‖(z - T) u‖`. -/
lemma IsFormalAdjoint.abs_im_mul_norm_le (hT : T.IsFormalAdjoint T) {u v : E}
    (huv : (u, v) ∈ T.graph) (z : 𝕜) : |im z| * ‖u‖ ≤ ‖z • u - v‖ := by
  obtain ⟨p, rfl, rfl⟩ := (mem_graph_iff T).mp huv
  have him : im ⟪(p : E), z • (p : E) - T p⟫ = im z * ‖(p : E)‖ ^ 2 := by
    rw [inner_sub_right, inner_smul_right, _root_.map_sub, hT.inner_map_self_im_eq_zero p, sub_zero,
      inner_self_eq_norm_sq_to_K, mul_im, ← ofReal_pow, ofReal_im, ofReal_re, mul_zero, zero_add]
  have h : ‖(p : E)‖ * (|im z| * ‖(p : E)‖) ≤ ‖(p : E)‖ * ‖z • (p : E) - T p‖ := by
    calc ‖(p : E)‖ * (|im z| * ‖(p : E)‖) = |im ⟪(p : E), z • (p : E) - T p⟫| := by
          rw [him, abs_mul, abs_of_nonneg (sq_nonneg ‖(p : E)‖)]
          ring
      _ ≤ ‖⟪(p : E), z • (p : E) - T p⟫‖ := abs_im_le_norm _
      _ ≤ ‖(p : E)‖ * ‖z • (p : E) - T p‖ := norm_inner_le_norm _ _
  rcases (norm_nonneg (p : E)).eq_or_lt with h0 | h0
  · rw [← h0, mul_zero]
    exact norm_nonneg _
  · exact le_of_mul_le_mul_left h h0

/-- For a positive operator, `-re z ‖u‖ ≤ ‖(z - T) u‖`. -/
lemma IsPositive.neg_re_mul_norm_le (hT : T.IsPositive) {u v : E} (huv : (u, v) ∈ T.graph)
    (z : 𝕜) : -re z * ‖u‖ ≤ ‖z • u - v‖ := by
  obtain ⟨p, rfl, rfl⟩ := (mem_graph_iff T).mp huv
  have hre : re ⟪(p : E), z • (p : E) - T p⟫ ≤ re z * ‖(p : E)‖ ^ 2 := by
    rw [inner_sub_right, inner_smul_right, _root_.map_sub, inner_self_eq_norm_sq_to_K, mul_re,
      ← ofReal_pow, ofReal_im, ofReal_re, mul_zero, sub_zero]
    linarith [hT.re_inner_nonneg_right p]
  have h : ‖(p : E)‖ * (-re z * ‖(p : E)‖) ≤ ‖(p : E)‖ * ‖z • (p : E) - T p‖ := by
    calc ‖(p : E)‖ * (-re z * ‖(p : E)‖) = -(re z * ‖(p : E)‖ ^ 2) := by ring
      _ ≤ -re ⟪(p : E), z • (p : E) - T p⟫ := neg_le_neg hre
      _ ≤ ‖⟪(p : E), z • (p : E) - T p⟫‖ := by
          rw [← norm_neg, ← _root_.map_neg]
          exact re_le_norm _
      _ ≤ ‖(p : E)‖ * ‖z • (p : E) - T p‖ := norm_inner_le_norm _ _
  rcases (norm_nonneg (p : E)).eq_or_lt with h0 | h0
  · rw [← h0, mul_zero]
    exact norm_nonneg _
  · exact le_of_mul_le_mul_left h h0

/-- Resolvents of a scalar multiple: `(z - c T)⁻¹ = c⁻¹ (c⁻¹ z - T)⁻¹` for `c ≠ 0`, when `c⁻¹ z` lies
in the resolvent set of `T`. -/
theorem resolvent_smul {c : 𝕜} (hc : c ≠ 0) (hz : c⁻¹ * z ∈ T.resolventSet) :
    (c • T).resolvent z = c⁻¹ • T.resolvent (c⁻¹ * z) := by
  set R := T.resolvent (c⁻¹ * z)
  refine resolvent_eq_of (fun x => ?_) (fun u v huv => ?_)
  · rw [mem_graph_smul]
    refine ⟨c⁻¹ • ((c⁻¹ * z) • R x - x), ?_, ?_⟩
    · simpa only [Prod.smul_mk, _root_.smul_apply] using
        T.graph.smul_mem c⁻¹ (resolvent_mem_graph hz x)
    · simp only [_root_.smul_apply, smul_smul, mul_inv_cancel₀ hc, one_smul, smul_sub]
      rw [mul_inv_cancel_left₀ hc, mul_comm z]
  · obtain ⟨v₀, huv₀, rfl⟩ := (mem_graph_smul c).mp huv
    have h := resolvent_sub_apply hz huv₀
    rw [_root_.smul_apply, show z • u - c • v₀ = c • ((c⁻¹ * z) • u - v₀) by
      rw [smul_sub, smul_smul, mul_inv_cancel_left₀ hc], ContinuousLinearMap.map_smul, h,
      inv_smul_smul₀ hc]

section Complete

variable [CompleteSpace E]

/-- A closed, densely defined operator `T` with `c ‖u‖ ≤ ‖(z - T) u‖` on `dom T` (`c > 0`) and
`ker (z̄ - T†) = 0` has `z` in its resolvent set: `z - T` is injective with closed range, and the
orthogonal complement of the range is `ker (z̄ - T†)`. -/
theorem mem_resolventSet_of_bounded_below (hT : T.IsClosed) (hTd : Dense (T.domain : Set E))
    {c : ℝ} (hc : 0 < c) (hbdd : ∀ u v, (u, v) ∈ T.graph → c * ‖u‖ ≤ ‖z • u - v‖)
    (hker : ∀ w, (w, conj z • w) ∈ T†.graph → w = 0) : z ∈ T.resolventSet := by
  let L : E →ₗ.[𝕜] E := ((z • ContinuousLinearMap.id 𝕜 E : E →L[𝕜] E) : E →ₗ[𝕜] E) +ᵥ (-T)
  have hLapp : ∀ x : L.domain, L x = z • (x : E) - T x := fun x => by
    simp only [L, vadd_apply, neg_apply, ContinuousLinearMap.coe_coe, sub_eq_add_neg]
    rfl
  have hL : ∀ x y, (x, y) ∈ L.graph ↔ (x, z • x - y) ∈ T.graph := fun x y => by
    simp only [mem_graph_iff]
    refine ⟨fun ⟨p, hp, hpy⟩ => ⟨p, hp, ?_⟩, fun ⟨p, hp, hpy⟩ => ⟨p, hp, ?_⟩⟩
    · rw [← hpy, hLapp, hp]
      abel
    · rw [hLapp, hpy, ← hp]
      abel
  have hLc : L.IsClosed := hT.neg.vadd _
  have hLb : ∀ x y, (x, y) ∈ L.graph → c * ‖x‖ ≤ ‖y‖ := fun x y hxy => by
    simpa using hbdd _ _ ((hL x y).mp hxy)
  have hLd : Dense (LinearMap.range L.toFun : Set E) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
      Submodule.eq_bot_iff]
    intro w hw
    have hw' : ∀ u : T.domain, ⟪conj z • w, (u : E)⟫ = ⟪w, T u⟫ := fun u => by
      have h := (Submodule.mem_orthogonal _ _).mp hw (L u) ⟨u, rfl⟩
      rw [hLapp, inner_sub_left, inner_smul_left, sub_eq_zero] at h
      rw [inner_smul_left, conj_conj, ← inner_conj_symm w (T u), ← h, map_mul, conj_conj,
        inner_conj_symm]
    have hwd : w ∈ T†.domain := mem_adjoint_domain_of_exists w ⟨_, hw'⟩
    exact hker w ((mem_graph_iff _).mpr ⟨⟨w, hwd⟩, rfl, adjoint_apply_eq hTd ⟨w, hwd⟩ hw'⟩)
  obtain ⟨R, hR₁, hR₂⟩ := hLc.exists_inverse hc hLb hLd
  refine ⟨R, fun x => (hL _ _).mp (hR₁ x), fun u v huv => hR₂ _ _ ((hL _ _).mpr ?_)⟩
  rwa [sub_sub_cancel]

/-- For a self-adjoint operator, every `z` with `im z ≠ 0` lies in the resolvent set. -/
theorem _root_.IsSelfAdjoint.mem_resolventSet {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A) {z : 𝕜}
    (hz : im z ≠ 0) : z ∈ A.resolventSet := by
  refine mem_resolventSet_of_bounded_below hA.isClosed hA.dense_domain (abs_pos.mpr hz)
    (fun u v h => hA.isFormalAdjoint.abs_im_mul_norm_le h z) fun w hw => ?_
  rw [isSelfAdjoint_def.mp hA] at hw
  have := hA.isFormalAdjoint.abs_im_mul_norm_le hw (conj z)
  rw [sub_self, norm_zero, conj_im, abs_neg] at this
  exact norm_eq_zero.mp (le_antisymm ((mul_nonpos_iff_pos_imp_nonpos.mp this).1 (abs_pos.mpr hz))
    (norm_nonneg _))

/-- For a positive self-adjoint operator, every `z` with `re z < 0` lies in the resolvent set. -/
theorem IsPositive.mem_resolventSet {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A) (hpos : A.IsPositive)
    {z : 𝕜} (hz : re z < 0) : z ∈ A.resolventSet := by
  refine mem_resolventSet_of_bounded_below hA.isClosed hA.dense_domain (neg_pos.mpr hz)
    (fun u v h => hpos.neg_re_mul_norm_le h z) fun w hw => ?_
  rw [isSelfAdjoint_def.mp hA] at hw
  have := hpos.neg_re_mul_norm_le hw (conj z)
  rw [sub_self, norm_zero, conj_re] at this
  exact norm_eq_zero.mp (le_antisymm ((mul_nonpos_iff_pos_imp_nonpos.mp this).1 (neg_pos.mpr hz))
    (norm_nonneg _))

/-- For a densely defined `T`, the adjoint of `(z - T)⁻¹` is a bounded two-sided inverse of
`z̄ - T†`. -/
private lemma adjoint_resolvent_isInverse (hTd : Dense (T.domain : Set E))
    (hz : z ∈ T.resolventSet) :
    (∀ x, (ContinuousLinearMap.adjoint (T.resolvent z) x,
      conj z • ContinuousLinearMap.adjoint (T.resolvent z) x - x) ∈ T†.graph) ∧
    ∀ u v, (u, v) ∈ T†.graph →
      ContinuousLinearMap.adjoint (T.resolvent z) (conj z • u - v) = u := by
  have hRb : ∀ a b, (a, b) ∈ T.graph → T.resolvent z b = z • T.resolvent z a - a := fun a b hab => by
    have := resolvent_sub_apply hz hab
    rw [ContinuousLinearMap.map_sub, ContinuousLinearMap.map_smul] at this
    linear_combination (norm := module) -this
  refine ⟨fun x => ?_, fun u v huv => ?_⟩
  · rw [adjoint_graph_eq_graph_adjoint hTd, Submodule.mem_adjoint_iff]
    intro a b hab
    simp only [ContinuousLinearMap.adjoint_inner_right, hRb a b hab, inner_sub_left,
      inner_smul_left, inner_sub_right, inner_smul_right]
    ring
  · refine ext_inner_right 𝕜 fun y => ?_
    obtain ⟨q, rfl, rfl⟩ := (mem_graph_iff T†).mp huv
    obtain ⟨p, hp, hpv⟩ := (mem_graph_iff T).mp (resolvent_mem_graph hz y)
    have hadj := adjoint_isFormalAdjoint hTd q p
    rw [hp, hpv] at hadj
    rw [ContinuousLinearMap.adjoint_inner_left, inner_sub_left, inner_smul_left, conj_conj, hadj,
      inner_sub_right, inner_smul_right]
    ring

/-- For a densely defined operator `T` and `z` in its resolvent set, `z̄` lies in the resolvent
set of `T†`. -/
theorem conj_mem_resolventSet_adjoint (hTd : Dense (T.domain : Set E))
    (hz : z ∈ T.resolventSet) : conj z ∈ T†.resolventSet :=
  ⟨_, adjoint_resolvent_isInverse hTd hz⟩

/-- For a densely defined operator `T` and `z` in its resolvent set, the adjoint of the resolvent
of `T` at `z` is the resolvent of `T†` at `z̄`: `((z - T)⁻¹)† = (z̄ - T†)⁻¹`. -/
theorem adjoint_resolvent (hTd : Dense (T.domain : Set E)) (hz : z ∈ T.resolventSet) :
    ContinuousLinearMap.adjoint (T.resolvent z) = T†.resolvent (conj z) :=
  (resolvent_eq_of (adjoint_resolvent_isInverse hTd hz).1
    (adjoint_resolvent_isInverse hTd hz).2).symm

/-- For a self-adjoint operator, `z̄` lies in the resolvent set whenever `z` does. -/
theorem _root_.IsSelfAdjoint.conj_mem_resolventSet {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    {z : 𝕜} (hz : z ∈ A.resolventSet) : conj z ∈ A.resolventSet := by
  simpa only [isSelfAdjoint_def.mp hA] using conj_mem_resolventSet_adjoint hA.dense_domain hz

/-- For a self-adjoint operator, the adjoint of the resolvent at `z` is the resolvent at `z̄`:
`((z - A)⁻¹)† = (z̄ - A)⁻¹`. -/
theorem _root_.IsSelfAdjoint.adjoint_resolvent {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A) {z : 𝕜}
    (hz : z ∈ A.resolventSet) :
    ContinuousLinearMap.adjoint (A.resolvent z) = A.resolvent (conj z) := by
  simpa only [isSelfAdjoint_def.mp hA] using LinearPMap.adjoint_resolvent hA.dense_domain hz

/-- For a self-adjoint operator and `im z ≠ 0`, `‖(z - A)⁻¹‖ ≤ |im z|⁻¹`. -/
theorem _root_.IsSelfAdjoint.norm_resolvent_le {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A) {z : 𝕜}
    (hz : im z ≠ 0) : ‖A.resolvent z‖ ≤ |im z|⁻¹ :=
  LinearPMap.norm_resolvent_le (abs_pos.mpr hz) fun _ _ h =>
    hA.isFormalAdjoint.abs_im_mul_norm_le h z

omit [CompleteSpace E] in
/-- For a positive operator and `re z < 0`, `‖(z - A)⁻¹‖ ≤ (-re z)⁻¹`. -/
theorem IsPositive.norm_resolvent_le {A : E →ₗ.[𝕜] E} (hpos : A.IsPositive) {z : 𝕜}
    (hz : re z < 0) : ‖A.resolvent z‖ ≤ (-re z)⁻¹ :=
  LinearPMap.norm_resolvent_le (neg_pos.mpr hz) fun _ _ h => hpos.neg_re_mul_norm_le h z

/-- For a self-adjoint operator, every nonzero point `ζ` of the spectrum of the resolvent at `w`
has `w - ζ⁻¹` real: the spectrum of `(w - A)⁻¹` lies in `{0} ∪ {(w - λ)⁻¹ | λ ∈ ℝ}`. -/
theorem _root_.IsSelfAdjoint.im_sub_inv_eq_zero_of_mem_spectrum {A : E →ₗ.[𝕜] E}
    (hA : IsSelfAdjoint A) (hw : w ∈ A.resolventSet) {ζ : 𝕜}
    (hζ : ζ ∈ spectrum 𝕜 (A.resolvent w)) (hζ0 : ζ ≠ 0) : im (w - ζ⁻¹) = 0 := by
  by_contra h
  have hne : w - ζ⁻¹ ≠ w := by simpa using hζ0
  have := notMem_spectrum_resolvent hw (hA.mem_resolventSet h) hne
  rw [sub_sub_cancel, inv_inv] at this
  exact this hζ

end Complete

end LinearPMap
