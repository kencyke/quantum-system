/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.LinearAlgebra.LinearPMap
public import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# Natural-domain composition and restriction of scalars for partially defined linear maps

Mathlib's `LinearPMap.comp g f H` composes two partially defined linear maps only under the
hypothesis `H` that `f` maps its whole domain into the domain of `g`. The composition used for
unbounded operators (`T†T`, `S T` with `S` bounded, …) is instead the one on the *natural domain*
`{x ∈ dom f | f x ∈ dom g}`, which needs no hypothesis. This file provides it, together with
restriction of scalars, which Mathlib provides for linear maps but not for `LinearPMap`.

## Main definitions

* `LinearPMap.compNat g f` — the composition `g ∘ f` on `{x ∈ dom f | f x ∈ dom g}`.

## Main results

* `LinearPMap.mem_compNat_domain` / `LinearPMap.compNat_apply` — the domain and the values.
* `LinearPMap.compNat_eq_comp` / `LinearPMap.toPMap_compNat` — `compNat` agrees with Mathlib's
  `LinearPMap.comp` when the latter is defined, and with `LinearMap.compPMap` when `g` is
  everywhere defined.
* `LinearPMap.mem_graph_compNat` — the graph of `g ∘ f` is the relational composite of the graphs.
* `LinearPMap.compNat_assoc`, `LinearPMap.compPMap_compNat`, `LinearPMap.compNat_mono` —
  associativity and monotonicity.
* `LinearPMap.mem_graph_domRestrict` — the graph of a restriction.
* `LinearPMap.mem_graph_compPMap`, `LinearPMap.mem_graph_compNat_toPMap`,
  `LinearPMap.mem_graph_smul` — the graphs of `g ∘ f` with `g` or `f` everywhere defined, and of
  `a • f`.
* `LinearPMap.restrictScalars` — an `S`-linear partially defined map as an `R`-linear one, with the
  same graph (`LinearPMap.graph_restrictScalars`); restriction of scalars is injective
  (`LinearPMap.restrictScalars_injective`).
* `LinearPMap.isClosed_restrictScalars_iff`, `LinearPMap.isClosable_restrictScalars_iff`,
  `LinearPMap.closure_restrictScalars`, `LinearPMap.topologicalClosure_graph_restrictScalars` —
  restricting scalars does not change the graph as a set, so closedness, closability and the
  closure are unaffected.
* `LinearPMap.IsSemilinear σ T` — for a ring homomorphism `σ : S₁ →+* S₂`, the graph of an
  `R`-linear `T` is invariant under `(x, y) ↦ (c • x, σ c • y)`; for real-linear operators between
  complex spaces, `σ = RingHom.id ℂ` gives the complex-linear and `σ = starRingEnd ℂ` the
  conjugate-linear ones. `LinearPMap.IsSemilinear.compNat` and `LinearPMap.IsSemilinear.closure`:
  semilinearity passes to composites (for the composite ring homomorphism) and to the closure.
* `LinearPMap.IsSemilinear.toLinearPMap` — an `R`-linear operator that is `RingHom.id S`-semilinear,
  regarded as an `S`-linear operator with the same graph; `LinearPMap.isSemilinear_restrictScalars`,
  `LinearPMap.toLinearPMap_restrictScalars`, `LinearPMap.IsSemilinear.restrictScalars_toLinearPMap`
  and `LinearPMap.IsSemilinear.coe_domain_toLinearPMap` say that it is inverse to
  `restrictScalars R`.
-/

@[expose] public section

namespace LinearPMap

section Semilinear

variable {R S T : Type*} [Ring R] [Ring S] [Ring T] {σ : R →+* S} {τ : S →+* T} {ρ : R →+* T}
  [RingHomCompTriple σ τ ρ]
  {E F G : Type*} [AddCommGroup E] [Module R E] [AddCommGroup F] [Module S F]
  [AddCommGroup G] [Module T G]

/-- The natural domain `{x ∈ dom f | f x ∈ dom g}` of the composition `g ∘ f`.

This is an auxiliary definition; the preferred spelling is `(g.compNat f).domain`, see
`LinearPMap.mem_compNat_domain`. -/
def compNatDomain (g : F →ₛₗ.[τ] G) (f : E →ₛₗ.[σ] F) : Submodule R E :=
  (g.domain.comap f.toFun).map f.domain.subtype

/-- The natural domain of `g ∘ f` is contained in the domain of `f`. -/
lemma compNatDomain_le (g : F →ₛₗ.[τ] G) (f : E →ₛₗ.[σ] F) : g.compNatDomain f ≤ f.domain := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

/-- The composition `g ∘ f` of two partially defined linear maps on the natural domain
`{x ∈ dom f | f x ∈ dom g}`. Unlike `LinearPMap.comp`, no hypothesis on the range of `f` is
needed. -/
def compNat (g : F →ₛₗ.[τ] G) (f : E →ₛₗ.[σ] F) : E →ₛₗ.[ρ] G :=
  g.comp (f.domRestrict (g.compNatDomain f)) fun x => by
    obtain ⟨y, hy, hyx⟩ := x.2.1
    rw [domRestrict_apply (hyx.symm : (x : E) = y)]
    exact hy

variable {g : F →ₛₗ.[τ] G} {f : E →ₛₗ.[σ] F}

/-- The domain of `g ∘ f` is the natural domain `{x ∈ dom f | f x ∈ dom g}`. -/
lemma compNat_domain : (g.compNat (ρ := ρ) f).domain = g.compNatDomain f :=
  inf_eq_left.mpr (compNatDomain_le g f)

/-- Membership in the domain of `g ∘ f`: `x ∈ dom f` and `f x ∈ dom g`. -/
lemma mem_compNat_domain {x : E} :
    x ∈ (g.compNat (ρ := ρ) f).domain ↔ ∃ hx : x ∈ f.domain, f ⟨x, hx⟩ ∈ g.domain := by
  refine ⟨fun h => ⟨h.2, ?_⟩, fun ⟨hx, h⟩ => ⟨⟨⟨x, hx⟩, h, rfl⟩, hx⟩⟩
  obtain ⟨y, hy, hyx⟩ := h.1
  obtain rfl : y = ⟨x, h.2⟩ := Subtype.ext hyx
  exact hy

/-- The domain of `g ∘ f` is contained in the domain of `f`. -/
lemma compNat_domain_le : (g.compNat (ρ := ρ) f).domain ≤ f.domain := fun _ h => h.2

/-- For `x` in the domain of `g ∘ f`, the value `f x` lies in the domain of `g`. -/
lemma compNat_apply_mem (x : (g.compNat (ρ := ρ) f).domain) :
    f ⟨x, compNat_domain_le x.2⟩ ∈ g.domain :=
  (mem_compNat_domain.mp x.2).2

/-- The value of `g ∘ f` is `g (f x)`. -/
lemma compNat_apply (x : (g.compNat (ρ := ρ) f).domain) :
    g.compNat f x = g ⟨f ⟨x, compNat_domain_le x.2⟩, compNat_apply_mem x⟩ :=
  rfl

/-- When `f` maps its domain into the domain of `g`, `compNat` is Mathlib's `LinearPMap.comp`. -/
lemma compNat_eq_comp (H : ∀ x : f.domain, f x ∈ g.domain) :
    g.compNat (ρ := ρ) f = g.comp f H :=
  LinearPMap.ext (Submodule.ext fun x => mem_compNat_domain.trans
    ⟨fun ⟨hx, _⟩ => hx, fun hx => ⟨hx, H ⟨x, hx⟩⟩⟩) fun _ _ _ => rfl

/-- Composing on the left with an everywhere-defined map is Mathlib's `LinearMap.compPMap`. -/
@[simp]
lemma toPMap_compNat (g : F →ₛₗ[τ] G) (f : E →ₛₗ.[σ] F) :
    (g.toPMap ⊤).compNat (ρ := ρ) f = g.compPMap f := by
  rw [compNat_eq_comp fun _ => Submodule.mem_top]
  rfl

/-- Composing on the right with an everywhere-defined map `f`: the domain is `f⁻¹(dom g)`. -/
lemma mem_compNat_toPMap_domain {g : F →ₛₗ.[τ] G} {f : E →ₛₗ[σ] F} {x : E} :
    x ∈ (g.compNat (ρ := ρ) (f.toPMap ⊤)).domain ↔ f x ∈ g.domain := by
  simp [mem_compNat_domain]

/-- Composing on the right with an everywhere-defined map `f`, evaluated at `x : E`. -/
lemma compNat_toPMap_apply {g : F →ₛₗ.[τ] G} {f : E →ₛₗ[σ] F} {x : E}
    (hx : x ∈ (g.compNat (ρ := ρ) (f.toPMap ⊤)).domain) :
    g.compNat (f.toPMap ⊤) ⟨x, hx⟩ = g ⟨f x, mem_compNat_toPMap_domain.mp hx⟩ :=
  rfl

end Semilinear

section Linear

variable {R E F G K : Type*} [Ring R] [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
  [AddCommGroup G] [Module R G] [AddCommGroup K] [Module R K]

/-- The graph of `g ∘ f` is the relational composite of the graphs of `f` and `g`. -/
lemma mem_graph_compNat {g : F →ₗ.[R] G} {f : E →ₗ.[R] F} {x : E} {z : G} :
    (x, z) ∈ (g.compNat f).graph ↔ ∃ y, (x, y) ∈ f.graph ∧ (y, z) ∈ g.graph := by
  simp only [mem_graph_iff, Subtype.exists, exists_and_left, exists_eq_left]
  constructor
  · rintro ⟨hx, rfl⟩
    exact ⟨_, ⟨compNat_domain_le hx, rfl⟩, compNat_apply_mem ⟨x, hx⟩, rfl⟩
  · rintro ⟨_, ⟨hx, rfl⟩, hy, rfl⟩
    exact ⟨mem_compNat_domain.mpr ⟨hx, hy⟩, rfl⟩

/-- The graph of the restriction of `f` to `S` is the part of the graph of `f` over `S`. -/
lemma mem_graph_domRestrict {f : E →ₗ.[R] F} {S : Submodule R E} {x : E} {y : F} :
    (x, y) ∈ (f.domRestrict S).graph ↔ x ∈ S ∧ (x, y) ∈ f.graph := by
  simp only [mem_graph_iff, Subtype.exists, exists_and_left, exists_eq_left, domRestrict_domain,
    Submodule.mem_inf]
  constructor
  · rintro ⟨⟨hS, hf⟩, rfl⟩
    exact ⟨hS, hf, (domRestrict_apply rfl).symm⟩
  · rintro ⟨hS, hf, rfl⟩
    exact ⟨⟨hS, hf⟩, domRestrict_apply rfl⟩

/-- Composition on the natural domain is associative. -/
lemma compNat_assoc (h : G →ₗ.[R] K) (g : F →ₗ.[R] G) (f : E →ₗ.[R] F) :
    (h.compNat g).compNat f = h.compNat (g.compNat f) := by
  refine eq_of_eq_graph (Submodule.ext fun ⟨x, w⟩ => ?_)
  simp only [mem_graph_compNat]
  exact ⟨fun ⟨y, hxy, z, hyz, hzw⟩ => ⟨z, ⟨y, hxy, hyz⟩, hzw⟩,
    fun ⟨z, ⟨y, hxy, hyz⟩, hzw⟩ => ⟨y, hxy, z, hyz, hzw⟩⟩

/-- Associativity of `compNat` with an everywhere-defined left factor. -/
lemma compPMap_compNat (h : G →ₗ[R] K) (g : F →ₗ.[R] G) (f : E →ₗ.[R] F) :
    (h.compPMap g).compNat f = h.compPMap (g.compNat f) := by
  rw [← toPMap_compNat, ← toPMap_compNat, compNat_assoc]

/-- Composition on the natural domain is monotone in both factors. -/
lemma compNat_mono {g g' : F →ₗ.[R] G} {f f' : E →ₗ.[R] F} (hg : g ≤ g') (hf : f ≤ f') :
    g.compNat f ≤ g'.compNat f' := by
  refine le_of_le_graph fun ⟨x, z⟩ hxz => ?_
  obtain ⟨y, hxy, hyz⟩ := mem_graph_compNat.mp hxz
  exact mem_graph_compNat.mpr ⟨y, le_graph_of_le hf hxy, le_graph_of_le hg hyz⟩

/-- The graph of `g ∘ f` for an everywhere-defined `g`: `(x, z)` lies in it iff `z = g y` for
`(x, y)` in the graph of `f`. -/
lemma mem_graph_compPMap {g : F →ₗ[R] G} {f : E →ₗ.[R] F} {x : E} {z : G} :
    (x, z) ∈ (g.compPMap f).graph ↔ ∃ y, (x, y) ∈ f.graph ∧ g y = z := by
  simp only [mem_graph_iff]
  exact ⟨fun ⟨p, hp, hpz⟩ => ⟨f p, ⟨p, hp, rfl⟩, hpz⟩, fun ⟨_, ⟨p, hp, rfl⟩, hpz⟩ => ⟨p, hp, hpz⟩⟩

/-- The graph of `g ∘ f` for an everywhere-defined `f`: `(x, z)` lies in it iff `(f x, z)` lies in
the graph of `g`. -/
lemma mem_graph_compNat_toPMap {g : F →ₗ.[R] G} {f : E →ₗ[R] F} {x : E} {z : G} :
    (x, z) ∈ (g.compNat (f.toPMap ⊤)).graph ↔ (f x, z) ∈ g.graph := by
  rw [mem_graph_compNat]
  refine ⟨fun ⟨y, hxy, hyz⟩ => ?_, fun h => ⟨f x, ?_, h⟩⟩
  · obtain ⟨p, hp, rfl⟩ := (mem_graph_iff _).mp hxy
    change (p : E) = x at hp
    subst hp
    exact hyz
  · exact (mem_graph_iff _).mpr ⟨⟨x, Submodule.mem_top⟩, rfl, rfl⟩

/-- The graph of `a • f`: `(x, z)` lies in it iff `z = a • y` for `(x, y)` in the graph of `f`. -/
lemma mem_graph_smul {M : Type*} [Monoid M] [DistribMulAction M F] [SMulCommClass R M F] (a : M)
    {f : E →ₗ.[R] F} {x : E} {z : F} :
    (x, z) ∈ (a • f).graph ↔ ∃ y, (x, y) ∈ f.graph ∧ a • y = z := by
  simp only [mem_graph_iff]
  exact ⟨fun ⟨p, hp, hpz⟩ => ⟨f p, ⟨p, hp, rfl⟩, hpz⟩, fun ⟨_, ⟨p, hp, rfl⟩, hpz⟩ => ⟨p, hp, hpz⟩⟩

/-- Injectivity in graph form: `f.ker = ⊥` iff `(x, 0) ∈ graph f` forces `x = 0`. -/
lemma ker_eq_bot_iff_mem_graph {f : E →ₗ.[R] F} : f.ker = ⊥ ↔ ∀ x, (x, 0) ∈ f.graph → x = 0 := by
  rw [ker_eq_bot']
  constructor
  · intro h x hx
    obtain ⟨y, rfl, hy⟩ := (mem_graph_iff f).mp hx
    exact congrArg Subtype.val (h y hy)
  · intro h y hy
    exact Subtype.ext (h y ((mem_graph_iff f).mpr ⟨y, rfl, hy⟩))

/-- The graph of the inverse of an injective partial linear map is its flipped graph. -/
lemma mem_graph_inverse_iff {f : E →ₗ.[R] F} (hf : f.ker = ⊥) {x : E} {y : F} :
    (y, x) ∈ f.inverse.graph ↔ (x, y) ∈ f.graph := by
  rw [inverse_graph hf, Submodule.map_equiv_eq_comap_symm]
  rfl

end Linear

section RestrictScalars

variable (R : Type*) {S E F : Type*} [Ring R] [Ring S] [SMul R S]
  [AddCommGroup E] [Module R E] [Module S E] [IsScalarTower R S E]
  [AddCommGroup F] [Module R F] [Module S F] [IsScalarTower R S F]

/-- An `S`-linear partially defined map, regarded as an `R`-linear one for `R` acting on `S`.
Domain and values are unchanged. -/
def restrictScalars (T : E →ₗ.[S] F) : E →ₗ.[R] F where
  domain := T.domain.restrictScalars R
  toFun :=
    { toFun := fun x => T ⟨x, x.2⟩
      map_add' := fun x y => T.map_add ⟨x, x.2⟩ ⟨y, y.2⟩
      map_smul' := fun c x => LinearMap.map_smul_of_tower T.toFun c ⟨x, x.2⟩ }

variable {R} {T : E →ₗ.[S] F}

/-- The domain of `T.restrictScalars R` is the domain of `T`. -/
@[simp]
lemma restrictScalars_domain : (T.restrictScalars R).domain = T.domain.restrictScalars R := rfl

/-- `T.restrictScalars R` takes the same values as `T`. -/
lemma restrictScalars_apply (x : (T.restrictScalars R).domain) :
    T.restrictScalars R x = T ⟨x, x.2⟩ :=
  rfl

/-- The graph of `T.restrictScalars R` is the graph of `T`. -/
@[simp]
lemma mem_graph_restrictScalars {p : E × F} : p ∈ (T.restrictScalars R).graph ↔ p ∈ T.graph := by
  simp only [mem_graph_iff, restrictScalars_domain, Subtype.exists, Submodule.restrictScalars_mem]
  rfl

/-- The graph of `T.restrictScalars R` is the graph of `T`, as an `R`-submodule. -/
lemma graph_restrictScalars : (T.restrictScalars R).graph = T.graph.restrictScalars R :=
  Submodule.ext fun _ => mem_graph_restrictScalars

/-- Restriction of scalars is injective on partially defined maps. -/
lemma restrictScalars_injective :
    Function.Injective (restrictScalars R : (E →ₗ.[S] F) → E →ₗ.[R] F) := fun T T' h =>
  eq_of_eq_graph (Submodule.ext fun p => by
    rw [← mem_graph_restrictScalars (R := R), h, mem_graph_restrictScalars])

end RestrictScalars

section Topology

variable {R S E F : Type*} [CommRing R] [CommRing S] [SMul R S]
  [AddCommGroup E] [Module R E] [Module S E] [IsScalarTower R S E]
  [AddCommGroup F] [Module R F] [Module S F] [IsScalarTower R S F]
  [TopologicalSpace E] [TopologicalSpace F] {T : E →ₗ.[S] F}

/-- `T.restrictScalars R` is closed iff `T` is. -/
@[simp]
lemma isClosed_restrictScalars_iff : (T.restrictScalars R).IsClosed ↔ T.IsClosed := by
  rw [IsClosed, IsClosed, graph_restrictScalars, Submodule.coe_restrictScalars]

variable [ContinuousAdd E] [ContinuousAdd F]
  [TopologicalSpace R] [ContinuousSMul R E] [ContinuousSMul R F]
  [TopologicalSpace S] [ContinuousSMul S E] [ContinuousSMul S F]

/-- The closure of the graph commutes with restriction of scalars. -/
lemma topologicalClosure_graph_restrictScalars :
    (T.restrictScalars R).graph.topologicalClosure =
      T.graph.topologicalClosure.restrictScalars R := by
  refine SetLike.coe_injective ?_
  rw [Submodule.topologicalClosure_coe, Submodule.coe_restrictScalars,
    Submodule.topologicalClosure_coe, graph_restrictScalars, Submodule.coe_restrictScalars]

/-- `T.restrictScalars R` is closable iff `T` is. -/
@[simp]
lemma isClosable_restrictScalars_iff : (T.restrictScalars R).IsClosable ↔ T.IsClosable := by
  refine ⟨fun ⟨T', hT'⟩ => ?_, fun ⟨T', hT'⟩ => ⟨T'.restrictScalars R, ?_⟩⟩
  · refine ⟨T.graph.topologicalClosure.toLinearPMap, (Submodule.toLinearPMap_graph_eq _ ?_).symm⟩
    intro x hx hx0
    have : x ∈ T'.graph := by
      rw [← hT', topologicalClosure_graph_restrictScalars]
      exact hx
    exact T'.graph_fst_eq_zero_snd this hx0
  · rw [topologicalClosure_graph_restrictScalars, hT', graph_restrictScalars]

/-- The closure commutes with restriction of scalars. -/
lemma closure_restrictScalars : (T.restrictScalars R).closure = T.closure.restrictScalars R := by
  by_cases hT : T.IsClosable
  · refine eq_of_eq_graph ?_
    rw [← (isClosable_restrictScalars_iff.mpr hT).graph_closure_eq_closure_graph,
      topologicalClosure_graph_restrictScalars, hT.graph_closure_eq_closure_graph,
      graph_restrictScalars]
  · rw [closure_def' hT, closure_def' (mt isClosable_restrictScalars_iff.mp hT)]

end Topology

/-! ### Semilinear operators -/

section Semilinear

variable {R S₁ S₂ S₃ E F G : Type*} [Ring R] [Semiring S₁] [Semiring S₂] [Semiring S₃]
  [AddCommGroup E] [Module R E] [SMul S₁ E] [AddCommGroup F] [Module R F] [SMul S₂ F]
  [AddCommGroup G] [Module R G] [SMul S₃ G]

/-- An `R`-linear partially defined operator `T : E → F` is **`σ`-semilinear**, for a ring
homomorphism `σ : S₁ →+* S₂` between rings acting on `E` and `F`, if its graph is invariant under
`(x, y) ↦ (c • x, σ c • y)` for every `c : S₁`: `c • x ∈ dom T` and `T (c • x) = σ c • T x`.
For a real-linear operator between complex spaces, `σ = RingHom.id ℂ` gives the complex-linear
operators and `σ = starRingEnd ℂ` the conjugate-linear ones. -/
def IsSemilinear (σ : S₁ →+* S₂) (T : E →ₗ.[R] F) : Prop :=
  ∀ (c : S₁) (x : E) (y : F), (x, y) ∈ T.graph → (c • x, σ c • y) ∈ T.graph

/-- A composite of semilinear operators is semilinear for the composite ring homomorphism; for
instance, a composite of two conjugate-linear operators is complex-linear. -/
lemma IsSemilinear.compNat {σ₁₂ : S₁ →+* S₂} {σ₂₃ : S₂ →+* S₃} {σ₁₃ : S₁ →+* S₃}
    [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] {T : E →ₗ.[R] F} {S : F →ₗ.[R] G}
    (hS : IsSemilinear σ₂₃ S) (hT : IsSemilinear σ₁₂ T) : IsSemilinear σ₁₃ (S.compNat T) :=
  fun c x z h => by
    obtain ⟨y, hxy, hyz⟩ := mem_graph_compNat.mp h
    have := hS (σ₁₂ c) _ _ hyz
    rw [RingHomCompTriple.comp_apply] at this
    exact mem_graph_compNat.mpr ⟨_, hT c x y hxy, this⟩

end Semilinear

section SemilinearClosure

variable {R S₁ S₂ E F : Type*} [CommRing R] [Semiring S₁] [Semiring S₂]
  [AddCommGroup E] [Module R E] [SMul S₁ E] [AddCommGroup F] [Module R F] [SMul S₂ F]
  [TopologicalSpace E] [TopologicalSpace F] [ContinuousAdd E] [ContinuousAdd F]
  [TopologicalSpace R] [ContinuousSMul R E] [ContinuousSMul R F]
  [ContinuousConstSMul S₁ E] [ContinuousConstSMul S₂ F]

/-- The closure of a semilinear operator is semilinear. -/
lemma IsSemilinear.closure {σ : S₁ →+* S₂} {T : E →ₗ.[R] F} (hT : IsSemilinear σ T) :
    IsSemilinear σ T.closure := by
  by_cases hc : T.IsClosable
  · intro c x y h
    rw [← hc.graph_closure_eq_closure_graph] at h ⊢
    exact map_mem_closure (f := fun p : E × F => (c • p.1, σ c • p.2)) (by fun_prop) h
      fun p hp => hT c p.1 p.2 hp
  · rwa [closure_def' hc]

end SemilinearClosure

section ToLinearPMap

variable {R S E F : Type*} [Ring R] [Ring S] [AddCommGroup E] [Module R E] [Module S E]
  [AddCommGroup F] [Module R F] [Module S F] {T : E →ₗ.[R] F}

/-- An `S`-linear `R`-linear operator, regarded as an `S`-linear operator with the same graph. -/
noncomputable def IsSemilinear.toLinearPMap (hT : IsSemilinear (RingHom.id S) T) : E →ₗ.[S] F :=
  Submodule.toLinearPMap
    { carrier := T.graph
      add_mem' := T.graph.add_mem
      zero_mem' := T.graph.zero_mem
      smul_mem' := fun c p hp => hT c p.1 p.2 hp }

/-- The graph of `hT.toLinearPMap` is the graph of `T`. -/
@[simp]
lemma IsSemilinear.mem_graph_toLinearPMap (hT : IsSemilinear (RingHom.id S) T) {p : E × F} :
    p ∈ hT.toLinearPMap.graph ↔ p ∈ T.graph := by
  rw [IsSemilinear.toLinearPMap, Submodule.toLinearPMap_graph_eq]
  · rfl
  · exact fun x hx hx0 => T.graph_fst_eq_zero_snd hx hx0

variable [SMul R S] [IsScalarTower R S E] [IsScalarTower R S F]

/-- An `S`-linear operator, regarded as an `R`-linear one, is `S`-linear. -/
lemma isSemilinear_restrictScalars (T : E →ₗ.[S] F) :
    IsSemilinear (RingHom.id S) (T.restrictScalars R) := fun c x y h => by
  rw [mem_graph_restrictScalars] at h ⊢
  exact T.graph.smul_mem c h

/-- Regarding `hT.toLinearPMap` as an `R`-linear operator recovers `T`. -/
@[simp]
lemma IsSemilinear.restrictScalars_toLinearPMap (hT : IsSemilinear (RingHom.id S) T) :
    hT.toLinearPMap.restrictScalars R = T :=
  eq_of_eq_graph (Submodule.ext fun _ => mem_graph_restrictScalars.trans hT.mem_graph_toLinearPMap)

/-- `toLinearPMap` inverts restriction of scalars: an `S`-linear operator regarded as an `R`-linear
one and back is itself. -/
@[simp]
lemma toLinearPMap_restrictScalars (T : E →ₗ.[S] F) :
    (isSemilinear_restrictScalars (R := R) T).toLinearPMap = T :=
  restrictScalars_injective (R := R) (IsSemilinear.restrictScalars_toLinearPMap _)

/-- The domain of `hT.toLinearPMap` is the domain of `T`. -/
lemma IsSemilinear.coe_domain_toLinearPMap (hT : IsSemilinear (RingHom.id S) T) :
    (hT.toLinearPMap.domain : Set E) = T.domain := by
  conv_rhs => rw [← hT.restrictScalars_toLinearPMap]
  rfl

end ToLinearPMap

end LinearPMap
