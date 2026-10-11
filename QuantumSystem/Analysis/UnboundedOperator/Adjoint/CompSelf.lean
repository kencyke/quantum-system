/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.UnboundedOperator.Adjoint.Semilinear
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.LinearPMap.Closure
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.LinearPMap.Positive
public import QuantumSystem.ForMathlib.Topology.Algebra.Module.LinearPMap.Semilinear
public import QuantumSystem.ForMathlib.Topology.Algebra.Module.LinearPMap

/-!
# Von Neumann's theorem on `T†T`

For a closed, densely defined operator `T : E → F` between Hilbert spaces, the operator `T†T`
(composed on its natural domain) is positive and self-adjoint, `1 + T†T` maps its domain onto
`E`, and its domain is a core for `T`.

The self-adjointness comes from a general criterion: a symmetric operator `A` for which `z + A` and
`z̄ + A` are surjective for some scalar `z` is self-adjoint; here `z` is real.

The theorem extends to a closed, densely defined `σ`-semilinear `T : E →ₛₗ.[σ] F` between complex
Hilbert spaces (`σ` the identity or the conjugation): with the semilinear adjoint
`T.adjointₛₗ : F →ₛₗ.[σ] E`, the composite `T†T` is a complex-linear positive self-adjoint operator.
For the Tomita operator `S` of a standard subspace it is the modular operator `Δ = S†S`.

## Main results

* `LinearPMap.IsFormalAdjoint.isSelfAdjoint_of_surjective_conj` — a symmetric `A` with `z + A` and
  `z̄ + A` surjective is self-adjoint; `LinearPMap.IsFormalAdjoint.isSelfAdjoint_of_surjective` is
  the case of real `z`.
* `LinearPMap.surjective_id_vadd_adjoint_compNat_self` — `1 + T†T` is surjective.
* `LinearPMap.isPositive_adjoint_compNat_self` — `T†T` is positive, with
  `⟪T†T x, x⟫ = ⟪T x, T x⟫` (`LinearPMap.inner_adjoint_compNat_self`).
* `LinearPMap.isSelfAdjoint_adjoint_compNat_self` — **von Neumann's theorem**: `T†T` is
  self-adjoint.
* `LinearPMap.hasCore_adjoint_compNat_self` — the domain of `T†T` is a core for `T`.
* `LinearPMap.ker_adjoint_compNat_self` — `ker (T†T) = ker T`.
* `LinearPMap.adjoint_compNat_self_eq_smul_of_inner` — `T†T` depends only on the form of `T`:
  `dom T₁ = dom T₂` and `⟪T₂ ·, T₂ ·⟫ = r ⟪T₁ ·, T₁ ·⟫` give `T₂†T₂ = r T₁†T₁`;
  `LinearPMap.adjoint_compNat_self_eq_smul` is the case of a correspondence `B T₁ ⊆ T₂`,
  `C T₂ ⊆ T₁` with `B = r C†`.
* `LinearPMap.isSelfAdjoint_adjointₛₗ_compNat_self` — **von Neumann's theorem for semilinear
  operators**: `T†T` is self-adjoint for a closed, densely defined `σ`-semilinear `T`.
* `LinearPMap.isPositive_adjointₛₗ_compNat_self`, `LinearPMap.ker_adjointₛₗ_compNat_self`,
  `LinearPMap.mem_closure_graphₛₗ_adjointₛₗ_compNat_self` — `T†T` is positive with
  `re ⟪T†T x, x⟫ = ‖T x‖²`, `ker (T†T) = ker T`, and the domain of `T†T` is a core for `T`.
* `LinearPMap.adjointₛₗ_compNat_self_eq_smul_of_inner`, `LinearPMap.adjointₛₗ_compNat_self_eq_smul`
  — the semilinear versions of the form comparison.

## Implementation notes

The semilinear von Neumann theorem is reduced to the complex-linear one through the realification
`LinearPMap.restrictScalars ℝ`, which turns the semilinear adjoint into the adjoint for the real
inner product `re ⟪·, ·⟫` (`LinearPMap.restrictScalars_adjointₛₗ`). The realification is only a
proof device; every statement is about the semilinear operator itself.

## References

* [J. Weidmann, *Linear Operators in Hilbert Spaces*][weidmann_linear]
-/

@[expose] public section

open RCLike
open scoped ComplexConjugate LinearPMap InnerProductSpace

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

namespace LinearPMap

/-- **Self-adjointness criterion.** A symmetric operator `A` on a Hilbert space such that `z + A`
and `z̄ + A` both map `dom A` onto the whole space for some scalar `z` is self-adjoint. (Its domain
is then automatically dense.) The usual choice is `z = i`: `A` is self-adjoint when `A ± i` are
surjective. -/
lemma IsFormalAdjoint.isSelfAdjoint_of_surjective_conj [CompleteSpace E] {A : E →ₗ.[𝕜] E}
    (hA : A.IsFormalAdjoint A) (z : 𝕜)
    (hz : Function.Surjective ((z • LinearMap.id : E →ₗ[𝕜] E) +ᵥ A))
    (hz' : Function.Surjective ((conj z • LinearMap.id : E →ₗ[𝕜] E) +ᵥ A)) : IsSelfAdjoint A := by
  -- the inner-product argument below runs on graph points `(u, A u)`
  have hsurj := surjective_vadd_iff.mp hz
  have hsurj' := surjective_vadd_iff.mp hz'
  simp only [LinearMap.smul_apply, LinearMap.id_apply] at hsurj hsurj'
  have hd : Dense (A.domain : Set E) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
      Submodule.eq_bot_iff]
    intro h hh
    obtain ⟨u, v, huv, rfl⟩ := hsurj h
    have hu : ∀ x, ⟪x, u⟫_𝕜 = 0 := fun x => by
      obtain ⟨a, b, hab, rfl⟩ := hsurj' x
      have h₁ := (Submodule.mem_orthogonal _ _).mp hh a (mem_domain_of_mem_graph hab)
      rw [inner_add_right, inner_smul_right, ← hA.inner_eq_of_mem_graph hab huv] at h₁
      rw [inner_add_left, inner_smul_left, conj_conj, h₁]
    have hu0 : u = 0 := inner_self_eq_zero.mp (hu u)
    subst hu0
    rw [A.graph_fst_eq_zero_snd huv rfl, smul_zero, add_zero]
  rw [isSelfAdjoint_def]
  refine eq_of_eq_graph ?_
  rw [adjoint_graph_eq_graph_adjoint hd]
  refine (le_antisymm (fun p huv => ?_) fun p hyw => ?_).symm
  · obtain ⟨u, v⟩ := p
    rw [Submodule.mem_adjoint_iff]
    intro a b hab
    rw [hA.inner_eq_of_mem_graph hab huv, sub_self]
  · obtain ⟨y, w⟩ := p
    rw [Submodule.mem_adjoint_iff] at hyw
    obtain ⟨u, v, huv, he⟩ := hsurj (z • y + w)
    have hperp : ∀ a b, (a, b) ∈ A.graph → ⟪conj z • a + b, y - u⟫_𝕜 = 0 := fun a b hab => by
      have h₁ := hyw a b hab
      dsimp only at h₁
      have h₂ := hA.inner_eq_of_mem_graph hab huv
      have h₃ : ⟪a, z • u + v⟫_𝕜 = ⟪a, z • y + w⟫_𝕜 := by rw [he]
      simp only [inner_add_right, inner_smul_right] at h₃
      simp only [inner_add_left, inner_sub_right, inner_smul_left, conj_conj]
      linear_combination h₁ - h₂ - h₃
    have hyu : y = u := by
      obtain ⟨a, b, hab, hab'⟩ := hsurj' (y - u)
      have := hperp a b hab
      rw [hab', inner_self_eq_zero, sub_eq_zero] at this
      exact this
    subst hyu
    obtain rfl : v = w := add_left_cancel he
    exact huv

/-- **Self-adjointness criterion.** A symmetric operator `A` on a Hilbert space such that `c + A`
maps `dom A` onto the whole space for some real `c` is self-adjoint. (Its domain is then
automatically dense.) -/
lemma IsFormalAdjoint.isSelfAdjoint_of_surjective [CompleteSpace E] {A : E →ₗ.[𝕜] E}
    (hA : A.IsFormalAdjoint A) (c : ℝ)
    (hc : Function.Surjective (((c : 𝕜) • LinearMap.id : E →ₗ[𝕜] E) +ᵥ A)) :
    IsSelfAdjoint A :=
  hA.isSelfAdjoint_of_surjective_conj c hc (by rwa [conj_ofReal])

variable [CompleteSpace E] [CompleteSpace F] {T : E →ₗ.[𝕜] F}

omit [CompleteSpace F] in
/-- The defining relation of the adjoint in graph form: for `(x, y)` in the graph of `T` and
`(y', z')` in the graph of `T†`, `⟪z', x⟫ = ⟪y', y⟫`. -/
lemma inner_eq_of_mem_graph_adjoint (hTd : Dense (T.domain : Set E)) {x : E} {y y' : F} {z' : E}
    (h : (x, y) ∈ T.graph) (h' : (y', z') ∈ T†.graph) : ⟪z', x⟫_𝕜 = ⟪y', y⟫_𝕜 := by
  obtain ⟨p, rfl, rfl⟩ := (mem_graph_iff T).mp h
  obtain ⟨q, rfl, rfl⟩ := (mem_graph_iff T†).mp h'
  exact adjoint_isFormalAdjoint hTd q p

omit [CompleteSpace F] in
/-- `⟪T†T x, x⟫ = ⟪T x, T x⟫` for `x` in the domain of `T†T`. -/
lemma inner_adjoint_compNat_self (hTd : Dense (T.domain : Set E)) (x : (T†.compNat T).domain) :
    ⟪T†.compNat T x, (x : E)⟫_𝕜 =
      ⟪T ⟨x, compNat_domain_le x.2⟩, T ⟨x, compNat_domain_le x.2⟩⟫_𝕜 := by
  rw [compNat_apply]
  exact inner_eq_of_mem_graph_adjoint hTd (T.mem_graph ⟨x, compNat_domain_le x.2⟩)
    (T†.mem_graph ⟨_, compNat_apply_mem x⟩)

omit [CompleteSpace F] in
/-- `re ⟪T†T x, x⟫ = ‖T x‖²` for `x` in the domain of `T†T`. -/
lemma re_inner_adjoint_compNat_self (hTd : Dense (T.domain : Set E))
    (x : (T†.compNat T).domain) :
    re ⟪T†.compNat T x, (x : E)⟫_𝕜 = ‖T ⟨x, compNat_domain_le x.2⟩‖ ^ 2 := by
  rw [inner_adjoint_compNat_self hTd, inner_self_eq_norm_sq]

omit [CompleteSpace F] in
/-- **`ker (T†T) = ker T`**, since `‖T x‖² = ⟪T†T x, x⟫`. -/
lemma ker_adjoint_compNat_self (hTd : Dense (T.domain : Set E)) : (T†.compNat T).ker = T.ker := by
  ext x
  -- `T†T x = 0` forces `‖T x‖² = ⟪T†T x, x⟫ = 0`, a computation at the single vector `x`
  rw [← mem_graph_zero_iff_mem_ker, ← mem_graph_zero_iff_mem_ker, mem_graph_compNat]
  refine ⟨fun ⟨y, hxy, hy⟩ => ?_, fun h => ⟨0, h, (T†).graph.zero_mem⟩⟩
  have := inner_eq_of_mem_graph_adjoint hTd hxy hy
  rw [inner_zero_left, eq_comm, inner_self_eq_zero] at this
  rwa [this] at hxy

omit [CompleteSpace F] in
/-- **`T†T` depends only on the form of `T`.** If densely defined `T₁, T₂` have the same domain and
`⟪T₂ v, T₂ u⟫ = r ⟪T₁ v, T₁ u⟫` for a real `r ≠ 0` (on graph points), then `T₂†T₂ = r T₁†T₁`. -/
lemma adjoint_compNat_self_eq_smul_of_inner {T₁ T₂ : E →ₗ.[𝕜] F}
    (hT₁ : Dense (T₁.domain : Set E)) (hT₂ : Dense (T₂.domain : Set E)) {r : ℝ} (hr : r ≠ 0)
    (hdom : T₁.domain = T₂.domain)
    (hinner : ∀ u y₁ y₂ v z₁ z₂, (u, y₁) ∈ T₁.graph → (u, y₂) ∈ T₂.graph → (v, z₁) ∈ T₁.graph →
      (v, z₂) ∈ T₂.graph → ⟪z₂, y₂⟫_𝕜 = (r : 𝕜) * ⟪z₁, y₁⟫_𝕜) :
    T₂†.compNat T₂ = (r : 𝕜) • T₁†.compNat T₁ := by
  have hr' : (r : 𝕜) ≠ 0 := ofReal_ne_zero.mpr hr
  -- the adjoints are characterised by inner products with graph points
  replace hdom : ∀ u, (∃ y, (u, y) ∈ T₁.graph) ↔ ∃ y, (u, y) ∈ T₂.graph := fun u => by
    simp only [← mem_domain_iff, hdom]
  refine eq_of_eq_graph (Submodule.ext fun ⟨u, w⟩ => ?_)
  rw [mem_graph_smul]
  simp_rw [mem_graph_compNat, mem_graph_adjoint_iff hT₁, mem_graph_adjoint_iff hT₂]
  constructor
  · rintro ⟨y₂, hy₂, h⟩
    obtain ⟨y₁, hy₁⟩ := (hdom u).mpr ⟨y₂, hy₂⟩
    refine ⟨(r : 𝕜)⁻¹ • w, ⟨y₁, hy₁, fun v z₁ hz₁ => ?_⟩, by rw [smul_inv_smul₀ hr']⟩
    obtain ⟨z₂, hz₂⟩ := (hdom v).mp ⟨z₁, hz₁⟩
    rw [inner_smul_right, ← h _ _ hz₂, hinner u y₁ y₂ v z₁ z₂ hy₁ hy₂ hz₁ hz₂,
      inv_mul_cancel_left₀ hr']
  · rintro ⟨z, ⟨y₁, hy₁, h⟩, rfl⟩
    obtain ⟨y₂, hy₂⟩ := (hdom u).mp ⟨y₁, hy₁⟩
    refine ⟨y₂, hy₂, fun v z₂ hz₂ => ?_⟩
    obtain ⟨z₁, hz₁⟩ := (hdom v).mpr ⟨z₂, hz₂⟩
    rw [hinner u y₁ y₂ v z₁ z₂ hy₁ hy₂ hz₁ hz₂, h _ _ hz₁, inner_smul_right]

omit [CompleteSpace F] in
/-- **`T†T` under a correspondence.** Let `T₁, T₂` be densely defined, with bounded `B, C` such that
`B T₁ ⊆ T₂`, `C T₂ ⊆ T₁` and `⟪y', B y⟫ = r ⟪C y', y⟫` for a real `r ≠ 0`. Then `T₂†T₂ = r T₁†T₁`
(`LinearPMap.adjoint_compNat_self_eq_smul_of_inner`). -/
lemma adjoint_compNat_self_eq_smul {T₁ T₂ : E →ₗ.[𝕜] F} (hT₁ : Dense (T₁.domain : Set E))
    (hT₂ : Dense (T₂.domain : Set E)) {B C : F →L[𝕜] F} {r : ℝ} (hr : r ≠ 0)
    (hB : (B : F →ₗ[𝕜] F).compPMap T₁ ≤ T₂) (hC : (C : F →ₗ[𝕜] F).compPMap T₂ ≤ T₁)
    (hBC : ∀ y y', ⟪y', B y⟫_𝕜 = (r : 𝕜) * ⟪C y', y⟫_𝕜) :
    T₂†.compNat T₂ = (r : 𝕜) • T₁†.compNat T₁ := by
  refine adjoint_compNat_self_eq_smul_of_inner hT₁ hT₂ hr (le_antisymm hB.1 hC.1)
    fun u y₁ y₂ v z₁ z₂ hy₁ hy₂ hz₁ hz₂ => ?_
  -- the inner products are evaluated at graph points
  replace hB := compPMap_le_iff.mp hB
  replace hC := compPMap_le_iff.mp hC
  -- The graphs are graphs of functions: `y₂ = B y₁` and `z₁ = C z₂`.
  have e₁ : y₂ = B y₁ := (sub_eq_zero.mp (T₂.graph_fst_eq_zero_snd
    (T₂.graph.sub_mem hy₂ (hB hy₁)) (sub_self u)))
  have e₂ : z₁ = C z₂ := (sub_eq_zero.mp (T₁.graph_fst_eq_zero_snd
    (T₁.graph.sub_mem hz₁ (hC hz₂)) (sub_self v)))
  rw [e₁, e₂, hBC]

omit [CompleteSpace F] in
/-- `T†T` is symmetric. -/
lemma isFormalAdjoint_adjoint_compNat_self (hTd : Dense (T.domain : Set E)) :
    (T†.compNat T).IsFormalAdjoint (T†.compNat T) := fun x y => by
  have h₁ := inner_eq_of_mem_graph_adjoint hTd (T.mem_graph ⟨y, compNat_domain_le y.2⟩)
    (T†.mem_graph ⟨_, compNat_apply_mem x⟩)
  have h₂ := inner_eq_of_mem_graph_adjoint hTd (T.mem_graph ⟨x, compNat_domain_le x.2⟩)
    (T†.mem_graph ⟨_, compNat_apply_mem y⟩)
  rw [compNat_apply, compNat_apply]
  calc _ = _ := h₁
    _ = conj _ := (inner_conj_symm _ _).symm
    _ = conj _ := congrArg conj h₂.symm
    _ = _ := inner_conj_symm _ _

omit [CompleteSpace F] in
/-- `T†T` is positive. -/
lemma isPositive_adjoint_compNat_self (hTd : Dense (T.domain : Set E)) :
    (T†.compNat T).IsPositive :=
  ⟨isFormalAdjoint_adjoint_compNat_self hTd, fun x => by
    rw [re_inner_adjoint_compNat_self hTd]
    exact sq_nonneg _⟩

/-- **Von Neumann.** For a closed, densely defined `T`, the operator `1 + T†T` maps its domain
onto `E`, in graph form: every `h` is `x + z` for `(x, z)` in the graph of `T†T`. -/
private lemma exists_mem_graph_adjoint_compNat_self (hT : T.IsClosed)
    (hTd : Dense (T.domain : Set E)) (h : E) :
    ∃ x z, (x, z) ∈ (T†.compNat T).graph ∧ x + z = h := by
  let G : Submodule 𝕜 (WithLp 2 (E × F)) := T.graph.comap (WithLp.linearEquiv 2 𝕜 (E × F)).toLinearMap
  have hG : _root_.IsClosed (G : Set (WithLp 2 (E × F))) :=
    hT.preimage (WithLp.prod_continuous_ofLp 2 E F)
  have : CompleteSpace G := hG.completeSpace_coe
  obtain ⟨p, hp, q, hq, hpq⟩ := G.exists_add_mem_mem_orthogonal (WithLp.toLp 2 (h, 0))
  have hpq' := congrArg WithLp.ofLp hpq
  simp only [WithLp.ofLp_add, Prod.ext_iff, Prod.fst_add, Prod.snd_add] at hpq'
  have hq' : ∀ a b, (a, b) ∈ T.graph →
      ⟪a, (WithLp.ofLp q).1⟫_𝕜 + ⟪b, (WithLp.ofLp q).2⟫_𝕜 = 0 := fun a b hab => by
    have := (Submodule.mem_orthogonal _ _).mp hq (WithLp.toLp 2 (a, b)) hab
    rwa [WithLp.prod_inner_apply, WithLp.ofLp_toLp] at this
  have hba : ((WithLp.ofLp q).2, -(WithLp.ofLp q).1) ∈ T†.graph := by
    rw [adjoint_graph_eq_graph_adjoint hTd, Submodule.mem_adjoint_iff]
    intro a b hab
    rw [inner_neg_right, sub_neg_eq_add, add_comm]
    exact hq' a b hab
  have hya : ((WithLp.ofLp p).2, (WithLp.ofLp q).1) ∈ T†.graph := by
    have := T†.graph.neg_mem hba
    rwa [Prod.neg_mk, neg_neg, ← eq_neg_of_add_eq_zero_left hpq'.2.symm] at this
  exact ⟨_, _, mem_graph_compNat.mpr ⟨_, hp, hya⟩, hpq'.1.symm⟩

/-- **Von Neumann.** For a closed, densely defined `T`, the operator `1 + T†T` maps its domain
onto `E`. -/
lemma surjective_id_vadd_adjoint_compNat_self (hT : T.IsClosed)
    (hTd : Dense (T.domain : Set E)) : Function.Surjective ((LinearMap.id : E →ₗ[𝕜] E) +ᵥ T†.compNat T) :=
  fun h => by
    obtain ⟨x, z, hxz, rfl⟩ := exists_mem_graph_adjoint_compNat_self hT hTd h
    obtain ⟨p, rfl, rfl⟩ := (mem_graph_iff _).mp hxz
    exact ⟨p, vadd_apply (LinearMap.id : E →ₗ[𝕜] E) (T†.compNat T) p⟩

/-- For a closed, densely defined `T`, the domain of `T†T` is dense. -/
lemma dense_adjoint_compNat_self_domain (hT : T.IsClosed) (hTd : Dense (T.domain : Set E)) :
    Dense ((T†.compNat T).domain : Set E) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro h hh
  obtain ⟨x, z, hxz, rfl⟩ := exists_mem_graph_adjoint_compNat_self hT hTd h
  obtain ⟨p, rfl, rfl⟩ := (mem_graph_iff _).mp hxz
  have hre := congrArg re ((Submodule.mem_orthogonal _ _).mp hh p p.2)
  rw [inner_add_right, _root_.map_add, inner_self_eq_norm_sq, ← inner_conj_symm, conj_re,
    re_inner_adjoint_compNat_self hTd, _root_.map_zero] at hre
  have hp : (p : E) = 0 := norm_eq_zero.mp (by
    nlinarith [sq_nonneg ‖(p : E)‖, sq_nonneg ‖T ⟨p, compNat_domain_le p.2⟩‖, norm_nonneg (p : E)])
  rw [(T†.compNat T).graph_fst_eq_zero_snd hxz hp, hp, add_zero]

/-- **Von Neumann's theorem.** For a closed, densely defined operator `T` between Hilbert spaces,
`T†T` is self-adjoint. -/
theorem isSelfAdjoint_adjoint_compNat_self (hT : T.IsClosed) (hTd : Dense (T.domain : Set E)) :
    IsSelfAdjoint (T†.compNat T) :=
  (isFormalAdjoint_adjoint_compNat_self hTd).isSelfAdjoint_of_surjective 1 (by
    rw [ofReal_one, one_smul]
    exact surjective_id_vadd_adjoint_compNat_self hT hTd)

/-- For a closed, densely defined `T`, the domain of `T†T` is a core for `T`. -/
lemma hasCore_adjoint_compNat_self (hT : T.IsClosed) (hTd : Dense (T.domain : Set E)) :
    T.HasCore (T†.compNat T).domain := by
  refine ⟨compNat_domain_le, ?_⟩
  set D := (T†.compNat T).domain
  have hKc : (T.domRestrict D).IsClosable := hT.isClosable.leIsClosable domRestrict_le
  refine eq_of_eq_graph ?_
  rw [← hKc.graph_closure_eq_closure_graph]
  refine le_antisymm
    (Submodule.topologicalClosure_minimal _ (le_graph_of_le domRestrict_le) hT) fun p hp => ?_
  let e := (WithLp.linearEquiv 2 𝕜 (E × F)).toLinearMap
  let G : Submodule 𝕜 (WithLp 2 (E × F)) := T.graph.comap e
  let K : Submodule 𝕜 (WithLp 2 (E × F)) := (T.domRestrict D).graph.comap e
  have hG : _root_.IsClosed (G : Set (WithLp 2 (E × F))) :=
    hT.preimage (WithLp.prod_continuous_ofLp 2 E F)
  have : CompleteSpace G := hG.completeSpace_coe
  have hKG : K ≤ G := Submodule.comap_mono (le_graph_of_le domRestrict_le)
  -- The only vector of `G` orthogonal to `K` is `0`.
  have hGK : ∀ r ∈ G, r ∈ Kᗮ → r = 0 := fun r hrG hrK => by
    have hrG' : ((WithLp.ofLp r).1, (WithLp.ofLp r).2) ∈ T.graph := hrG
    have hu : ∀ x w, (x, w) ∈ (T†.compNat T).graph → ⟪x + w, (WithLp.ofLp r).1⟫_𝕜 = 0 :=
      fun x w hxw => by
        obtain ⟨y, hxy, hyw⟩ := mem_graph_compNat.mp hxw
        have h₁ := (Submodule.mem_orthogonal' _ _).mp hrK (WithLp.toLp 2 (x, y))
          (mem_graph_domRestrict.mpr ⟨mem_domain_of_mem_graph hxw, hxy⟩)
        simp only [WithLp.prod_inner_apply] at h₁
        rw [inner_add_left, inner_eq_of_mem_graph_adjoint hTd hrG' hyw, ← inner_conj_symm x,
          ← inner_conj_symm y, ← _root_.map_add, h₁, _root_.map_zero]
    obtain ⟨x, w, hxw, he⟩ := exists_mem_graph_adjoint_compNat_self hT hTd (WithLp.ofLp r).1
    have h0 : (WithLp.ofLp r).1 = 0 := by
      have := hu x w hxw
      rwa [he, inner_self_eq_zero] at this
    have h1 : (WithLp.ofLp r).2 = 0 := T.graph_fst_eq_zero_snd hrG h0
    exact (WithLp.ofLp_injective 2).eq_iff.mp (Prod.ext h0 h1)
  have key : WithLp.toLp 2 p ∈ Kᗮᗮ := by
    rw [Submodule.mem_orthogonal]
    intro q hq
    obtain ⟨q₁, hq₁, q₂, hq₂, rfl⟩ := G.exists_add_mem_mem_orthogonal q
    have hq₁K : q₁ ∈ Kᗮ := by
      have := Kᗮ.sub_mem hq (Submodule.orthogonal_le hKG hq₂)
      rwa [add_sub_cancel_right] at this
    rw [hGK q₁ hq₁ hq₁K, zero_add]
    exact Submodule.inner_left_of_mem_orthogonal hp hq₂
  rw [Submodule.orthogonal_orthogonal_eq_closure] at key
  exact map_mem_closure (WithLp.prod_continuous_ofLp 2 E F) key fun q hq => hq

end LinearPMap

/-! ### Von Neumann's theorem for semilinear operators -/

namespace LinearPMap

open ClosedSubmodule

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] {σ : ℂ →+* ℂ} [RingHomInvPair σ σ]
  [RingHomIsometric σ] {T : E →ₛₗ.[σ] F}

/-- A complex operator whose underlying real-linear operator is self-adjoint for the real inner
products `re ⟪·, ·⟫` is self-adjoint. -/
private lemma isSelfAdjoint_of_restrictScalars {A : E →ₗ.[ℂ] E}
    (hA : IsSelfAdjoint (A.restrictScalars ℝ fun _ => rfl)) : IsSelfAdjoint A := by
  have hd : Dense (A.domain : Set E) := hA.dense_domain
  rw [isSelfAdjoint_def] at hA ⊢
  refine restrictScalars_injective (R₀ := ℝ) (hσ := fun _ => rfl) ?_
  rw [← adjointₛₗ_eq_adjoint, restrictScalars_adjointₛₗ hd]
  exact hA

/-- `⟪T†T x, y⟫ = σ ⟪T x, T y⟫` for `x` in the domain of `T†T` and `y` in that of `T`. -/
lemma inner_adjointₛₗ_compNat_self (hTd : Dense (T.domain : Set E))
    (x : (T.adjointₛₗ.compNat T).domain) (y : T.domain) :
    ⟪T.adjointₛₗ.compNat T x, (y : E)⟫_ℂ = σ ⟪T ⟨x, compNat_domain_le x.2⟩, T y⟫_ℂ := by
  rw [compNat_apply]
  exact inner_adjointₛₗ_apply hTd ⟨_, compNat_apply_mem x⟩ y

/-- `re ⟪T†T x, x⟫ = ‖T x‖²` for `x` in the domain of `T†T`. -/
lemma re_inner_adjointₛₗ_compNat_self (hTd : Dense (T.domain : Set E))
    (x : (T.adjointₛₗ.compNat T).domain) :
    (⟪T.adjointₛₗ.compNat T x, (x : E)⟫_ℂ).re = ‖T ⟨x, compNat_domain_le x.2⟩‖ ^ 2 := by
  have h : ∀ v : F, ⟪v, v⟫_ℂ = ((‖v‖ ^ 2 : ℝ) : ℂ) := fun v => by
    simp [inner_self_eq_norm_sq_to_K]
  rw [inner_adjointₛₗ_compNat_self hTd x ⟨x, compNat_domain_le x.2⟩, h,
    RingHom.apply_ofReal_of_isometric σ, Complex.ofReal_re]

/-- `T†T` is positive, for a densely defined `σ`-semilinear `T`. -/
lemma isPositive_adjointₛₗ_compNat_self (hTd : Dense (T.domain : Set E)) :
    (T.adjointₛₗ.compNat T).IsPositive := by
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · rw [inner_adjointₛₗ_compNat_self hTd x ⟨y, compNat_domain_le y.2⟩, ← inner_conj_symm (x : E),
      inner_adjointₛₗ_compNat_self hTd y ⟨x, compNat_domain_le x.2⟩,
      ← RingHom.apply_conj_of_isometric σ, inner_conj_symm]
  · rw [RCLike.re_to_complex, re_inner_adjointₛₗ_compNat_self hTd]
    positivity

/-- **`ker (T†T) = ker T`**, since `‖T x‖² = ⟪T†T x, x⟫`. -/
lemma ker_adjointₛₗ_compNat_self (hTd : Dense (T.domain : Set E)) :
    (T.adjointₛₗ.compNat T).ker = T.ker := by
  ext x
  rw [← mem_graphₛₗ_zero_iff_mem_ker, ← mem_graphₛₗ_zero_iff_mem_ker, mem_graphₛₗ_compNat]
  refine ⟨fun ⟨y, hxy, hy⟩ => ?_, fun h => ⟨0, h, T.adjointₛₗ.graphₛₗ.zero_mem⟩⟩
  have h := inner_eq_of_mem_graphₛₗ_adjointₛₗ hTd hxy hy
  rw [inner_zero_left, eq_comm, map_eq_zero, inner_self_eq_zero] at h
  rwa [h] at hxy

/-- **`T†T` depends only on the form of `T`.** If densely defined `σ`-semilinear `T₁, T₂` have the
same domain and `⟪T₂ v, T₂ u⟫ = r ⟪T₁ v, T₁ u⟫` for a real `r ≠ 0` (on graph points), then
`T₂†T₂ = r T₁†T₁`. -/
lemma adjointₛₗ_compNat_self_eq_smul_of_inner {T₁ T₂ : E →ₛₗ.[σ] F}
    (hT₁ : Dense (T₁.domain : Set E)) (hT₂ : Dense (T₂.domain : Set E)) {r : ℝ} (hr : r ≠ 0)
    (hdom : T₁.domain = T₂.domain)
    (hinner : ∀ u y₁ y₂ v z₁ z₂, (u, y₁) ∈ T₁.graphₛₗ → (u, y₂) ∈ T₂.graphₛₗ →
      (v, z₁) ∈ T₁.graphₛₗ → (v, z₂) ∈ T₂.graphₛₗ → ⟪z₂, y₂⟫_ℂ = (r : ℂ) * ⟪z₁, y₁⟫_ℂ) :
    T₂.adjointₛₗ.compNat T₂ = (r : ℂ) • T₁.adjointₛₗ.compNat T₁ := by
  have hr' : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr
  -- the adjoints are characterised by inner products with graph points
  replace hdom : ∀ u, (∃ y, (u, y) ∈ T₁.graphₛₗ) ↔ ∃ y, (u, y) ∈ T₂.graphₛₗ := fun u => by
    simp only [← mem_domain_iff_exists_mem_graphₛₗ, hdom]
  have key : ∀ u y₁ y₂ v z₁ z₂, (u, y₁) ∈ T₁.graphₛₗ → (u, y₂) ∈ T₂.graphₛₗ →
      (v, z₁) ∈ T₁.graphₛₗ → (v, z₂) ∈ T₂.graphₛₗ →
      σ ⟪y₂, z₂⟫_ℂ = (r : ℂ) * σ ⟪y₁, z₁⟫_ℂ := fun u y₁ y₂ v z₁ z₂ hy₁ hy₂ hz₁ hz₂ => by
    rw [← inner_conj_symm y₂ z₂, hinner u y₁ y₂ v z₁ z₂ hy₁ hy₂ hz₁ hz₂, map_mul, Complex.conj_ofReal,
      inner_conj_symm, map_mul, RingHom.apply_ofReal_of_isometric σ]
  refine eq_of_eq_graphₛₗ (AddSubgroup.ext fun ⟨u, w⟩ => ?_)
  rw [mem_graphₛₗ_smul]
  simp_rw [mem_graphₛₗ_compNat, mem_graphₛₗ_adjointₛₗ_iff hT₁, mem_graphₛₗ_adjointₛₗ_iff hT₂]
  constructor
  · rintro ⟨y₂, hy₂, h⟩
    obtain ⟨y₁, hy₁⟩ := (hdom u).mpr ⟨y₂, hy₂⟩
    refine ⟨(r : ℂ)⁻¹ • w, ⟨y₁, hy₁, fun v z₁ hz₁ => ?_⟩, by rw [smul_inv_smul₀ hr']⟩
    obtain ⟨z₂, hz₂⟩ := (hdom v).mp ⟨z₁, hz₁⟩
    rw [inner_smul_left, ← Complex.ofReal_inv, Complex.conj_ofReal, h _ _ hz₂,
      key u y₁ y₂ v z₁ z₂ hy₁ hy₂ hz₁ hz₂, Complex.ofReal_inv, inv_mul_cancel_left₀ hr']
  · rintro ⟨z, ⟨y₁, hy₁, h⟩, rfl⟩
    obtain ⟨y₂, hy₂⟩ := (hdom u).mp ⟨y₁, hy₁⟩
    refine ⟨y₂, hy₂, fun v z₂ hz₂ => ?_⟩
    obtain ⟨z₁, hz₁⟩ := (hdom v).mpr ⟨z₂, hz₂⟩
    rw [key u y₁ y₂ v z₁ z₂ hy₁ hy₂ hz₁ hz₂, ← h _ _ hz₁, inner_smul_left, Complex.conj_ofReal]

/-- **`T†T` under a correspondence.** Let `T₁, T₂` be densely defined and `σ`-semilinear, with
bounded complex-linear `B, C` such that `B T₁ ⊆ T₂`, `C T₂ ⊆ T₁` and `⟪y', B y⟫ = r ⟪C y', y⟫` for a
real `r ≠ 0`. Then `T₂†T₂ = r T₁†T₁` (`LinearPMap.adjointₛₗ_compNat_self_eq_smul_of_inner`). -/
lemma adjointₛₗ_compNat_self_eq_smul {T₁ T₂ : E →ₛₗ.[σ] F} (hT₁ : Dense (T₁.domain : Set E))
    (hT₂ : Dense (T₂.domain : Set E)) {B C : F →L[ℂ] F} {r : ℝ} (hr : r ≠ 0)
    (hB : (B : F →ₗ[ℂ] F).compPMap T₁ ≤ T₂) (hC : (C : F →ₗ[ℂ] F).compPMap T₂ ≤ T₁)
    (hBC : ∀ y y', ⟪y', B y⟫_ℂ = (r : ℂ) * ⟪C y', y⟫_ℂ) :
    T₂.adjointₛₗ.compNat T₂ = (r : ℂ) • T₁.adjointₛₗ.compNat T₁ := by
  refine adjointₛₗ_compNat_self_eq_smul_of_inner hT₁ hT₂ hr (le_antisymm hB.1 hC.1)
    fun u y₁ y₂ v z₁ z₂ hy₁ hy₂ hz₁ hz₂ => ?_
  -- the inner products are evaluated at graph points
  replace hB := compPMap_le_iffₛₗ.mp hB
  replace hC := compPMap_le_iffₛₗ.mp hC
  -- The graphs are graphs of functions: `y₂ = B y₁` and `z₁ = C z₂`.
  have e₁ : y₂ = B y₁ := mem_graphₛₗ_snd_inj hy₂ (hB hy₁)
  have e₂ : z₁ = C z₂ := mem_graphₛₗ_snd_inj hz₁ (hC hz₂)
  rw [e₁, e₂, hBC]

variable [CompleteSpace F]

/-- **Von Neumann's theorem for semilinear operators.** For a closed, densely defined
`σ`-semilinear `T` between complex Hilbert spaces, `σ` the identity or the conjugation, the
complex-linear operator `T†T` is self-adjoint. For the Tomita operator `S` of a standard subspace
it is the modular operator `Δ = S†S`. -/
theorem isSelfAdjoint_adjointₛₗ_compNat_self (hT : T.IsClosedₛₗ) (hTd : Dense (T.domain : Set E)) :
    IsSelfAdjoint (T.adjointₛₗ.compNat T) := by
  have hσ := RingHom.apply_real_smul_one_of_isometric σ
  refine isSelfAdjoint_of_restrictScalars ?_
  rw [restrictScalars_compNat (hτ := hσ) (hσ := hσ), restrictScalars_adjointₛₗ hTd]
  exact isSelfAdjoint_adjoint_compNat_self (isClosed_restrictScalars_iff.mpr hT) hTd

/-- For a closed, densely defined `σ`-semilinear `T`, the domain of `T†T` is a core for `T`: every
point of the graph of `T` is a limit of points of the graph over the domain of `T†T`. -/
lemma mem_closure_graphₛₗ_adjointₛₗ_compNat_self (hT : T.IsClosedₛₗ)
    (hTd : Dense (T.domain : Set E)) {p : E × F} (hp : p ∈ T.graphₛₗ) :
    p ∈ _root_.closure
      {q : E × F | q.1 ∈ (T.adjointₛₗ.compNat T).domain ∧ q ∈ T.graphₛₗ} := by
  have hσ := RingHom.apply_real_smul_one_of_isometric σ
  set Tr := T.restrictScalars ℝ hσ
  have hTr : Tr.IsClosed := isClosed_restrictScalars_iff.mpr hT
  have hcore := hasCore_adjoint_compNat_self hTr hTd
  have hKc : (Tr.domRestrict (Tr†.compNat Tr).domain).IsClosable :=
    hTr.isClosable.leIsClosable domRestrict_le
  have hp' : p ∈ (Tr.domRestrict (Tr†.compNat Tr).domain).graph.topologicalClosure := by
    rw [hKc.graph_closure_eq_closure_graph, hcore.closure_eq]
    exact mem_graph_restrictScalars.mpr hp
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hp'
  refine closure_mono (fun q hq => ?_) hp'
  obtain ⟨q₁, q₂⟩ := q
  obtain ⟨hq₁, hq⟩ := mem_graph_domRestrict.mp hq
  refine ⟨?_, mem_graph_restrictScalars.mp hq⟩
  rw [← restrictScalars_adjointₛₗ hTd, ← restrictScalars_compNat (hρ := fun _ => rfl)] at hq₁
  exact hq₁

end LinearPMap
