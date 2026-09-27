/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.LinearAlgebra.LinearPMap

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

end LinearPMap
