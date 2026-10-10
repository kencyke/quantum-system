/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.InnerProductSpace.StandardSubspace
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.LinearPMap.Closure
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.Semilinear
public import QuantumSystem.ForMathlib.LinearAlgebra.LinearPMap

/-!
# Adjoints of semilinear unbounded operators

For a densely defined `σ`-semilinear operator `T : E → F` between complex Hilbert spaces, `σ` the
identity or the complex conjugation, the adjoint `T†` (`LinearPMap.adjointₛₗ`) is the
`σ`-semilinear operator with `⟪T† y, x⟫ = σ ⟪y, T x⟫`. This file develops its graph theory: the
graph of `T†` is the twisted orthogonal complement of the graph of `T`, `T†` is closed, the
closure has the same adjoint, `T` is closable iff `T†` is densely defined, and `T†† = T̄`. For
`σ = id` these are the corresponding statements for Mathlib's `LinearPMap.adjoint`
(`LinearPMap.adjointₛₗ_eq_adjoint`); for the conjugation they are the theory of conjugate-linear
operators such as Tomita operators.

## Main results

* `LinearPMap.real_smul_mem_graphₛₗ` — the graph of `T` is a real subspace.
* `LinearPMap.mem_graphₛₗ_adjointₛₗ_iff`, `LinearPMap.inner_eq_of_mem_graphₛₗ_adjointₛₗ` — the graph
  of `T†`: `(y, w) ∈ graph T†` iff `⟪w, x⟫ = σ ⟪y, v⟫` for all `(x, v) ∈ graph T`;
  `LinearPMap.mem_graphₛₗ_adjointₛₗ_iff_re` — the real parts of these relations suffice.
* `LinearPMap.isClosedₛₗ_adjointₛₗ` — `T†` is closed.
* `LinearPMap.adjointₛₗ_anti` — `S ⊆ T` implies `T† ⊆ S†`.
* `LinearPMap.adjointₛₗ_closureₛₗ` — `T̄† = T†`.
* `LinearPMap.isClosableₛₗ_iff_dense_adjointₛₗ_domain` — `T` is closable iff `T†` is densely
  defined.
* `LinearPMap.adjointₛₗ_adjointₛₗ`, `LinearPMap.IsClosedₛₗ.adjointₛₗ_adjointₛₗ` — `T†† = T̄`.
* `LinearPMap.adjointₛₗ_compPMap` — `(B T)† = T† B†` for a bounded semilinear `B`, with the bounded
  adjoint `B† = B.adjointₛₗ` (`ContinuousLinearMap.adjointₛₗ`).
* `LinearPMap.compPMap_adjoint_le_adjointₛₗ_compNat_toPMap` — `B† S† ⊆ (S B)†` for a bounded
  complex-linear `B`.
* `LinearPMap.restrictScalars_adjointₛₗ` — realification commutes with taking adjoints.

## Implementation notes

The closability criterion and the double adjoint are transferred from the real-linear case: a
complex Hilbert space is a real Hilbert space for the inner product `re ⟪x, y⟫`, Mathlib's scoped
instance `ClosedSubmodule.instInnerProductSpaceReal`, and the underlying real-linear operator
`T.restrictScalars ℝ` of `T` has the same graph, with real adjoint the underlying real-linear
operator of `T†` (`LinearPMap.restrictScalars_adjointₛₗ`). This realification is a proof device
only; every statement is about the semilinear operators themselves.
-/

@[expose] public section

open Complex ClosedSubmodule
open scoped ComplexConjugate LinearPMap InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

namespace LinearPMap

variable {σ : ℂ →+* ℂ} [RingHomInvPair σ σ] [RingHomIsometric σ] {T : E →ₛₗ.[σ] F}

omit [RingHomInvPair σ σ] in
/-- The graph of a `σ`-semilinear operator between complex spaces, `σ` the identity or the
conjugation, is a real subspace: `(x, y) ∈ graph T` implies `(r x, r y) ∈ graph T` for real `r`. -/
lemma real_smul_mem_graphₛₗ (r : ℝ) {x : E} {y : F} (h : (x, y) ∈ T.graphₛₗ) :
    (r • x, r • y) ∈ T.graphₛₗ := by
  have h' := smul_mem_graphₛₗ (r : ℂ) h
  rwa [RingHom.apply_ofReal_of_isometric, Complex.coe_smul, Complex.coe_smul] at h'

/-! ### The graph of the adjoint -/

section Graph

variable [CompleteSpace E]

/-- **The graph of the adjoint**: `(y, w)` lies in the graph of `T†` iff `⟪w, x⟫ = σ ⟪y, v⟫` for
every `(x, v)` in the graph of `T`. -/
lemma mem_graphₛₗ_adjointₛₗ_iff (hT : Dense (T.domain : Set E)) {y : F} {w : E} :
    (y, w) ∈ T.adjointₛₗ.graphₛₗ ↔ ∀ x v, (x, v) ∈ T.graphₛₗ → ⟪w, x⟫_ℂ = σ ⟪y, v⟫_ℂ := by
  constructor
  · rintro ⟨y', rfl, rfl⟩ _ _ ⟨x', rfl, rfl⟩
    exact inner_adjointₛₗ_apply hT y' x'
  · intro h
    have hy : y ∈ T.adjointₛₗ.domain :=
      mem_adjointₛₗ_domain_of_exists y ⟨w, fun x => h x _ (T.mem_graphₛₗ x)⟩
    exact ⟨⟨y, hy⟩, rfl, adjointₛₗ_apply_eq hT ⟨y, hy⟩ fun x => h x _ (T.mem_graphₛₗ x)⟩

/-- The defining relation of the adjoint in graph form: for `(x, v)` in the graph of `T` and
`(y, w)` in the graph of `T†`, `⟪w, x⟫ = σ ⟪y, v⟫`. -/
lemma inner_eq_of_mem_graphₛₗ_adjointₛₗ (hT : Dense (T.domain : Set E)) {x : E} {v : F} {y : F}
    {w : E} (h : (x, v) ∈ T.graphₛₗ) (h' : (y, w) ∈ T.adjointₛₗ.graphₛₗ) :
    ⟪w, x⟫_ℂ = σ ⟪y, v⟫_ℂ :=
  (mem_graphₛₗ_adjointₛₗ_iff hT).mp h' x v h

/-- **The real form of the adjoint relation**: for a densely defined `σ`-semilinear `T`, `(y, w)`
lies in the graph of `T†` as soon as `re ⟪w, x⟫ = re ⟪y, v⟫` for all `(x, v)` in the graph of `T`;
the imaginary parts follow from the points `(i x, σ(i) v)`. -/
lemma mem_graphₛₗ_adjointₛₗ_iff_re (hT : Dense (T.domain : Set E)) {y : F} {w : E} :
    (y, w) ∈ T.adjointₛₗ.graphₛₗ ↔
      ∀ x v, (x, v) ∈ T.graphₛₗ → (⟪w, x⟫_ℂ).re = (⟪y, v⟫_ℂ).re := by
  rw [mem_graphₛₗ_adjointₛₗ_iff hT]
  constructor
  · intro h x v hxv
    rw [h x v hxv]
    rcases RingHom.eq_id_or_conj_of_isometric σ with rfl | rfl
    · rfl
    · exact conj_re _
  · intro h x v hxv
    have h₁ := h x v hxv
    have h₂ := h _ _ (smul_mem_graphₛₗ I hxv)
    rw [inner_smul_right, inner_smul_right] at h₂
    rcases RingHom.eq_id_or_conj_of_isometric σ with rfl | rfl
    · simp only [RingHom.id_apply, mul_re, I_re, I_im, zero_mul, one_mul, zero_sub,
        neg_inj] at h₂ ⊢
      exact Complex.ext h₁ h₂
    · simp only [conj_I, neg_mul, neg_re, mul_re, I_re, I_im, zero_mul, one_mul, zero_sub,
        neg_neg] at h₂
      refine Complex.ext (by rw [conj_re]; exact h₁) ?_
      rw [conj_im]
      linarith

/-- The adjoint of a densely defined operator is closed. -/
lemma isClosedₛₗ_adjointₛₗ (hT : Dense (T.domain : Set E)) : T.adjointₛₗ.IsClosedₛₗ := by
  have h : (T.adjointₛₗ.graphₛₗ : Set (F × E)) =
      ⋂ p ∈ T.graphₛₗ, {q : F × E | ⟪q.2, p.1⟫_ℂ = σ ⟪q.1, p.2⟫_ℂ} := by
    ext ⟨y, w⟩
    simp only [SetLike.mem_coe, mem_graphₛₗ_adjointₛₗ_iff hT, Set.mem_iInter, Set.mem_ofPred_eq,
      Prod.forall]
  have hσ : Continuous σ :=
    (AddMonoidHomClass.isometry_of_norm σ fun _ => RingHomIsometric.norm_map).continuous
  rw [IsClosedₛₗ, h]
  exact isClosed_biInter fun p _ => isClosed_eq (by fun_prop) (hσ.comp (by fun_prop))

/-- **The adjoint reverses inclusions**: `S ⊆ T` implies `T† ⊆ S†`, for densely defined `S`. -/
lemma adjointₛₗ_anti {S : E →ₛₗ.[σ] F} (hS : Dense (S.domain : Set E)) (h : S ≤ T) :
    T.adjointₛₗ ≤ S.adjointₛₗ :=
  le_of_le_graphₛₗ fun ⟨_, _⟩ hyw => (mem_graphₛₗ_adjointₛₗ_iff hS).mpr fun x v hv =>
    (mem_graphₛₗ_adjointₛₗ_iff (hS.mono h.1)).mp hyw x v (le_graphₛₗ_of_le h hv)

/-- A densely defined operator and its closure have the same adjoint. (If `T` is not closable,
`T̄ = T` by convention and the statement is trivial.) -/
lemma adjointₛₗ_closureₛₗ (hT : Dense (T.domain : Set E)) : T.closureₛₗ.adjointₛₗ = T.adjointₛₗ := by
  by_cases hc : T.IsClosableₛₗ
  · refine le_antisymm (adjointₛₗ_anti hT (le_closureₛₗ T)) (le_of_le_graphₛₗ fun ⟨y, w⟩ hyw => ?_)
    rw [mem_graphₛₗ_adjointₛₗ_iff (dense_domain_closureₛₗ hT)]
    intro x v hxv
    rw [← SetLike.mem_coe, hc.coe_graphₛₗ_closureₛₗ] at hxv
    have hσ : Continuous σ :=
      (AddMonoidHomClass.isometry_of_norm σ fun _ => RingHomIsometric.norm_map).continuous
    have hcl : _root_.IsClosed {p : E × F | ⟪w, p.1⟫_ℂ = σ ⟪y, p.2⟫_ℂ} :=
      isClosed_eq (by fun_prop) (hσ.comp (by fun_prop))
    exact closure_minimal (fun p hp => (mem_graphₛₗ_adjointₛₗ_iff hT).mp hyw p.1 p.2 hp) hcl hxv
  · rw [closureₛₗ_def' hc]

end Graph

/-! ### Composites with bounded operators -/

section Compositions

variable [CompleteSpace E] {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [CompleteSpace F] {τ ρ : ℂ →+* ℂ} [RingHomInvPair τ τ] [RingHomIsometric τ] [RingHomInvPair ρ ρ]
  [RingHomIsometric ρ] [RingHomCompTriple σ τ ρ] [RingHomCompTriple τ σ ρ]

/-- **Adjoint of a composite with a bounded left factor.** For a bounded semilinear `B` and a
densely defined `T`, `(B T)† = T† B†`, the right-hand side on its natural domain
`{y | B† y ∈ dom T†}`. -/
lemma adjointₛₗ_compPMap (hT : Dense (T.domain : Set E)) (B : F →SL[τ] G) :
    ((B : F →ₛₗ[τ] G).compPMap (ρ := ρ) T).adjointₛₗ =
      T.adjointₛₗ.compNat (ρ := ρ) ((B.adjointₛₗ : G →ₛₗ[τ] F).toPMap ⊤) := by
  refine eq_of_eq_graphₛₗ (AddSubgroup.ext fun ⟨y, w⟩ => ?_)
  rw [mem_graphₛₗ_adjointₛₗ_iff (T := (B : F →ₛₗ[τ] G).compPMap (ρ := ρ) T) hT,
    mem_graphₛₗ_compNat_toPMap, mem_graphₛₗ_adjointₛₗ_iff hT]
  simp only [ContinuousLinearMap.coe_coe]
  constructor
  · intro h x u hxu
    rw [ContinuousLinearMap.adjointₛₗ_inner_left, RingHomCompTriple.comp_apply]
    exact h x (B u) (mem_graphₛₗ_compPMap.mpr ⟨u, hxu, rfl⟩)
  · intro h x v hxv
    obtain ⟨u, hxu, rfl⟩ := mem_graphₛₗ_compPMap.mp hxv
    rw [h x u hxu, ContinuousLinearMap.adjointₛₗ_inner_left, RingHomCompTriple.comp_apply]
    rfl

end Compositions

section LinearCompositions

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace E]
  [CompleteSpace G]

/-- **Adjoint of a composite with a bounded complex-linear right factor, general inclusion**:
`B† S† ⊆ (S B)†` for a densely defined `S` and a bounded complex-linear `B` with `S B` densely
defined. -/
lemma compPMap_adjoint_le_adjointₛₗ_compNat_toPMap {S : G →ₛₗ.[σ] F}
    (hS : Dense (S.domain : Set G)) (B : E →L[ℂ] G)
    (hSB : Dense ((S.compNat ((B : E →ₗ[ℂ] G).toPMap ⊤)).domain : Set E)) :
    ((ContinuousLinearMap.adjoint B : G →L[ℂ] E) : G →ₗ[ℂ] E).compPMap S.adjointₛₗ ≤
      (S.compNat ((B : E →ₗ[ℂ] G).toPMap ⊤)).adjointₛₗ :=
  IsFormalAdjointₛₗ.le_adjointₛₗ hSB fun x y => by
    rw [compNat_apply, LinearMap.compPMap_apply, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.adjoint_inner_right]
    exact (adjointₛₗ_isFormalAdjointₛₗ hS).symm _ ⟨y, y.2⟩

end LinearCompositions

/-! ### Realification -/

section Realification

/-- The adjoint of the underlying real-linear operator, for the real inner products `re ⟪·, ·⟫`, is
the underlying real-linear operator of the adjoint. -/
lemma restrictScalars_adjointₛₗ [CompleteSpace E] (hT : Dense (T.domain : Set E))
    {hσ : ∀ r : ℝ, σ (r • 1) = r • 1} :
    T.adjointₛₗ.restrictScalars ℝ hσ = (T.restrictScalars ℝ hσ)† := by
  refine eq_of_eq_graph (Submodule.ext fun ⟨y, w⟩ => ?_)
  rw [mem_graph_restrictScalars, adjoint_graph_eq_graph_adjoint (T := T.restrictScalars ℝ hσ) hT,
    Submodule.mem_adjoint_iff, mem_graphₛₗ_adjointₛₗ_iff_re hT]
  simp only [mem_graph_restrictScalars, sub_eq_zero, inner_real_eq_re_inner]
  refine forall₂_congr fun a b => imp_congr_right fun _ => ?_
  rw [← inner_conj_symm w a, ← inner_conj_symm y b, conj_re, conj_re, eq_comm]

variable [CompleteSpace E] [CompleteSpace F]

/-- **Closability criterion**: a densely defined operator is closable iff its adjoint is densely
defined. -/
theorem isClosableₛₗ_iff_dense_adjointₛₗ_domain (hT : Dense (T.domain : Set E)) :
    T.IsClosableₛₗ ↔ Dense (T.adjointₛₗ.domain : Set F) := by
  have hσ := RingHom.apply_real_smul_one_of_isometric σ
  rw [← isClosable_restrictScalars_iff (R₀ := ℝ) (hσ := hσ),
    isClosable_iff_dense_adjoint_domain (T := T.restrictScalars ℝ hσ) hT,
    ← restrictScalars_adjointₛₗ hT]
  rfl

/-- **Double adjoint.** For a densely defined closable operator `T`, `T†† = T̄`. -/
theorem adjointₛₗ_adjointₛₗ (hT : Dense (T.domain : Set E)) (hc : T.IsClosableₛₗ) :
    T.adjointₛₗ.adjointₛₗ = T.closureₛₗ := by
  have hσ := RingHom.apply_real_smul_one_of_isometric σ
  have hd : Dense (T.adjointₛₗ.domain : Set F) := (isClosableₛₗ_iff_dense_adjointₛₗ_domain hT).mp hc
  refine restrictScalars_injective (R₀ := ℝ) (hσ := hσ) ?_
  rw [restrictScalars_adjointₛₗ hd, restrictScalars_adjointₛₗ hT, ← closure_restrictScalars,
    adjoint_adjoint (T := T.restrictScalars ℝ hσ) hT (isClosable_restrictScalars_iff.mpr hc)]

/-- A densely defined closed operator is its own double adjoint. -/
lemma IsClosedₛₗ.adjointₛₗ_adjointₛₗ (hT : Dense (T.domain : Set E)) (hTc : T.IsClosedₛₗ) :
    T.adjointₛₗ.adjointₛₗ = T := by
  rw [LinearPMap.adjointₛₗ_adjointₛₗ hT hTc.isClosableₛₗ, hTc.closureₛₗ_eq]

end Realification

end LinearPMap
