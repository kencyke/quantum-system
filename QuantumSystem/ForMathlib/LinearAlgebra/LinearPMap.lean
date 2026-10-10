/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.LinearAlgebra.LinearPMap
public import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# Graphs, natural-domain composition and closures of semilinear partially defined maps

Mathlib's partially defined maps `E →ₛₗ.[σ] F` are semilinear, but their graph, closedness,
closability and closure (`LinearPMap.graph`, `LinearPMap.IsClosed`, `LinearPMap.IsClosable`,
`LinearPMap.closure`) are only defined for linear maps `E →ₗ.[R] F`: the graph of a linear map is a
submodule of `E × F`, whereas that of a `σ`-semilinear map is invariant under
`(x, y) ↦ (c • x, σ c • y)` only. This file develops them for semilinear maps, with the graph an
additive subgroup of `E × F`; a conjugate-linear unbounded operator between complex spaces, such as
a Tomita operator, is an `E →ₛₗ.[starRingEnd ℂ] F`.

Mathlib's `LinearPMap.comp g f H` composes two partially defined maps only under the hypothesis
`H` that `f` maps its whole domain into the domain of `g`. The composition used for unbounded
operators (`T†T`, `S T` with `S` bounded, …) is instead the one on the *natural domain*
`{x ∈ dom f | f x ∈ dom g}`, which needs no hypothesis. This file provides it, for semilinear maps:
the composite of two conjugate-linear maps is linear (`RingHomCompTriple`).

## Main definitions

* `LinearPMap.graphₛₗ f` — the graph of a semilinear partially defined map, an additive subgroup.
* `LinearPMap.ofGraphₛₗ g` — the semilinear partially defined map with a given graph `g`.
* `LinearPMap.compNat g f` — the composition `g ∘ f` on `{x ∈ dom f | f x ∈ dom g}`.
* `LinearPMap.restrictScalars R₀ hσ T` — a `σ`-semilinear map as an `R₀`-linear one, for scalars
  `R₀` fixed by `σ`; for instance a conjugate-linear map between complex spaces as a real-linear
  one.
* `LinearPMap.IsClosedₛₗ`, `LinearPMap.IsClosableₛₗ`, `LinearPMap.closureₛₗ` — closedness,
  closability and the closure of a semilinear partially defined map.

## Main results

* `LinearPMap.mem_graphₛₗ_iff`, `LinearPMap.eq_of_eq_graphₛₗ`, `LinearPMap.le_iff_mem_graphₛₗ`,
  `LinearPMap.smul_mem_graphₛₗ` — the graph determines the map and its order, and is
  `σ`-invariant.
* `LinearPMap.mem_compNat_domain` / `LinearPMap.compNat_apply` — the domain and the values of
  `g ∘ f`.
* `LinearPMap.compNat_eq_comp` / `LinearPMap.toPMap_compNat` — `compNat` agrees with Mathlib's
  `LinearPMap.comp` when the latter is defined, and with `LinearMap.compPMap` when `g` is
  everywhere defined.
* `LinearPMap.mem_graphₛₗ_compNat`, `LinearPMap.mem_graphₛₗ_compPMap`,
  `LinearPMap.mem_graphₛₗ_compNat_toPMap`, `LinearPMap.mem_graphₛₗ_domRestrict`,
  `LinearPMap.mem_graphₛₗ_smul` — the graphs of composites, restrictions and multiples, and their
  linear forms `LinearPMap.mem_graph_compNat`, ….
* `LinearPMap.compNat_assoc`, `LinearPMap.compPMap_compNat`, `LinearPMap.compPMap_comp`,
  `LinearPMap.compNat_toPMap_comp`, `LinearPMap.toPMap_comp`, `LinearPMap.id_compPMap`,
  `LinearPMap.compNat_toPMap_id`, `LinearPMap.compNat_mono`, `LinearPMap.compPMap_mono` —
  associativity, units and monotonicity.
* `LinearPMap.compNat_self_eq_id_iff`, `LinearPMap.compNat_toPMap_eq_compPMap_iff`,
  `LinearPMap.compPMap_le_compNat_toPMap_iffₛₗ`, `LinearPMap.compPMap_le_iffₛₗ` — `S S = 1` on
  `dom S`, `B V = V A` for a semilinear equivalence `V`, `g T ⊆ S f` and `g A ⊆ T` in terms of
  graph points, for the arguments that are genuinely pointwise (closures, limits, single vectors).
* `LinearPMap.mem_graph_restrictScalars`, `LinearPMap.restrictScalars_injective`,
  `LinearPMap.restrictScalars_le_iff`, `LinearPMap.restrictScalars_compNat`, … — restricting scalars
  keeps the graph, and commutes with composition and kernels.
* `LinearPMap.IsClosableₛₗ.coe_graphₛₗ_closureₛₗ`, `LinearPMap.isClosableₛₗ_iff`,
  `LinearPMap.IsClosableₛₗ.isClosedₛₗ_closureₛₗ`, `LinearPMap.IsClosedₛₗ.closureₛₗ_eq` — the graph
  of the closure is the closure of the graph, and the closure is closed.
* `LinearPMap.IsClosableₛₗ.leIsClosableₛₗ`, `LinearPMap.IsClosableₛₗ.closureₛₗ_mono`,
  `LinearPMap.isClosableₛₗ_iff_exists_closed_extension` — closability passes to restrictions and
  means having a closed extension.
* `LinearPMap.compPMap_closureₛₗ_le`, `LinearPMap.IsClosedₛₗ.compNat_toPMap`,
  `LinearPMap.isClosedₛₗ_toPMap`, `LinearPMap.closureₛₗ_compNat_toPMap_le`,
  `LinearPMap.compPMap_closureₛₗ_le_closureₛₗ_compNat_toPMap` — for continuous everywhere defined
  `B` and `C`: `B T̄ ⊆ (B T)‾`, `T B` is closed for closed `T`, `B` itself is closed,
  `(T B)‾ ⊆ T̄ B`, and `B T ⊆ S C` passes to the closures.
* `LinearPMap.isClosed_restrictScalars_iff`, `LinearPMap.isClosable_restrictScalars_iff`,
  `LinearPMap.closure_restrictScalars` — closedness, closability and the closure commute with
  restriction of scalars.

## Implementation notes

The graph, closedness, closability and closure of a semilinear map carry the subscript `ₛₗ`
because Mathlib's names are taken by the linear notions. This is a gap in Mathlib, whose graph
API is only for `E →ₗ.[R] F`; for a linear map the semilinear notions are Mathlib's, by
`LinearPMap.mem_graphₛₗ_iff_mem_graph`, `LinearPMap.isClosedₛₗ_iff_isClosed`,
`LinearPMap.closureₛₗ_eq_closure` and `LinearPMap.ofGraphₛₗ_eq_toLinearPMap`. Linear operators
keep Mathlib's notions throughout the project.

`LinearPMap.restrictScalars` is a proof device: it transfers results that Mathlib proves for linear
maps (for instance over `ℝ`) to semilinear maps, whose statements are made with the `ₛₗ` notions.

## TODO

Upstream the semilinear graph, closure and natural-domain composition to Mathlib, generalising
`LinearPMap.graph`, `LinearPMap.IsClosed`, `LinearPMap.IsClosable` and `LinearPMap.closure` to
`E →ₛₗ.[σ] F`, so that the subscripted notions and the compatibility lemmas disappear.
-/

@[expose] public section

namespace LinearPMap

/-! ### Composition on the natural domain -/

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

/-- The composition `g ∘ f` of two partially defined semilinear maps on the natural domain
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

/-! ### The graph of a semilinear partially defined map -/

section Graph

variable {R S : Type*} [Ring R] [Ring S] {σ : R →+* S}
  {E F : Type*} [AddCommGroup E] [Module R E] [AddCommGroup F] [Module S F]

/-- The **graph** `{(x, f x) | x ∈ dom f}` of a semilinear partially defined map, an additive
subgroup of `E × F`, invariant under `(x, y) ↦ (c • x, σ c • y)` (`LinearPMap.smul_mem_graphₛₗ`).
For a linear map it is Mathlib's `LinearPMap.graph` (`LinearPMap.mem_graphₛₗ_iff_mem_graph`). -/
def graphₛₗ (f : E →ₛₗ.[σ] F) : AddSubgroup (E × F) where
  carrier := {p | ∃ y : f.domain, (y : E) = p.1 ∧ f y = p.2}
  add_mem' := by
    rintro ⟨_, _⟩ ⟨_, _⟩ ⟨y, rfl, rfl⟩ ⟨z, rfl, rfl⟩
    exact ⟨y + z, rfl, f.map_add y z⟩
  zero_mem' := ⟨0, rfl, f.map_zero⟩
  neg_mem' := by
    rintro ⟨_, _⟩ ⟨y, rfl, rfl⟩
    exact ⟨-y, rfl, f.map_neg y⟩

variable {f g : E →ₛₗ.[σ] F}

/-- Membership in the graph: `p = (y, f y)` for some `y ∈ dom f`. -/
@[simp]
lemma mem_graphₛₗ_iff {p : E × F} : p ∈ f.graphₛₗ ↔ ∃ y : f.domain, (y : E) = p.1 ∧ f y = p.2 :=
  Iff.rfl

/-- The point `(x, f x)` lies in the graph of `f`. -/
lemma mem_graphₛₗ (f : E →ₛₗ.[σ] F) (x : f.domain) : ((x : E), f x) ∈ f.graphₛₗ :=
  ⟨x, rfl, rfl⟩

/-- A point of the graph lies over the domain. -/
lemma mem_domain_of_mem_graphₛₗ {x : E} {y : F} (h : (x, y) ∈ f.graphₛₗ) : x ∈ f.domain := by
  obtain ⟨z, rfl, -⟩ := h
  exact z.2

/-- The domain is the projection of the graph. -/
lemma mem_domain_iff_exists_mem_graphₛₗ {x : E} : x ∈ f.domain ↔ ∃ y, (x, y) ∈ f.graphₛₗ :=
  ⟨fun hx => ⟨_, f.mem_graphₛₗ (⟨x, hx⟩ : f.domain)⟩, fun ⟨_, h⟩ => mem_domain_of_mem_graphₛₗ h⟩

/-- `y = f x` iff `(x, y)` lies in the graph of `f`. -/
lemma eq_apply_iff_mem_graphₛₗ {x : E} (hx : x ∈ f.domain) {y : F} :
    y = f ⟨x, hx⟩ ↔ (x, y) ∈ f.graphₛₗ := by
  constructor
  · rintro rfl
    exact f.mem_graphₛₗ ⟨x, hx⟩
  · rintro ⟨z, hz, rfl⟩
    obtain rfl : z = ⟨x, hx⟩ := Subtype.ext hz
    rfl

/-- The graph is the graph of a function. -/
lemma mem_graphₛₗ_snd_inj {x : E} {y y' : F} (h : (x, y) ∈ f.graphₛₗ) (h' : (x, y') ∈ f.graphₛₗ) :
    y = y' := by
  have hx := mem_domain_of_mem_graphₛₗ h
  rw [← eq_apply_iff_mem_graphₛₗ hx] at h h'
  rw [h, h']

/-- The property `f 0 = 0` in terms of the graph. -/
lemma graphₛₗ_fst_eq_zero_snd {x : E} {y : F} (h : (x, y) ∈ f.graphₛₗ) (hx : x = 0) : y = 0 := by
  subst hx
  exact mem_graphₛₗ_snd_inj h f.graphₛₗ.zero_mem

/-- The graph of a `σ`-semilinear map is invariant under `(x, y) ↦ (c • x, σ c • y)`. -/
lemma smul_mem_graphₛₗ (c : R) {x : E} {y : F} (h : (x, y) ∈ f.graphₛₗ) :
    (c • x, σ c • y) ∈ f.graphₛₗ := by
  obtain ⟨z, rfl, rfl⟩ := h
  exact ⟨c • z, rfl, f.map_smulₛₗ c z⟩

/-- An extension has a larger graph. -/
lemma le_graphₛₗ_of_le (h : f ≤ g) : f.graphₛₗ ≤ g.graphₛₗ := by
  rintro ⟨_, _⟩ ⟨z, rfl, rfl⟩
  exact ⟨⟨z, h.1 z.2⟩, rfl, (h.2 rfl).symm⟩

/-- A larger graph is the graph of an extension. -/
lemma le_of_le_graphₛₗ (h : f.graphₛₗ ≤ g.graphₛₗ) : f ≤ g :=
  ⟨fun x hx => mem_domain_of_mem_graphₛₗ (h (f.mem_graphₛₗ ⟨x, hx⟩)), fun x y hxy =>
    (eq_apply_iff_mem_graphₛₗ y.2).mpr (by rw [← hxy]; exact h (f.mem_graphₛₗ x))⟩

/-- Inclusion of graphs is the extension order. -/
lemma le_graphₛₗ_iff : f.graphₛₗ ≤ g.graphₛₗ ↔ f ≤ g :=
  ⟨le_of_le_graphₛₗ, le_graphₛₗ_of_le⟩

/-- **Inclusion of operators, pointwise**: `f ≤ g` iff every point of the graph of `f` lies in the
graph of `g`, i.e. `x ∈ dom f` forces `x ∈ dom g` and `g x = f x`. -/
lemma le_iff_mem_graphₛₗ :
    f ≤ g ↔ ∀ ⦃x : E⦄ ⦃y : F⦄, (x, y) ∈ f.graphₛₗ → (x, y) ∈ g.graphₛₗ :=
  le_graphₛₗ_iff.symm.trans ⟨fun h _ _ hxy => h hxy, fun h ⟨_, _⟩ hxy => h hxy⟩

/-- A semilinear partially defined map is determined by its graph. -/
lemma eq_of_eq_graphₛₗ (h : f.graphₛₗ = g.graphₛₗ) : f = g :=
  le_antisymm (le_of_le_graphₛₗ h.le) (le_of_le_graphₛₗ h.ge)

/-- The kernel in graph form: `x ∈ ker f` iff `(x, 0)` lies in the graph of `f`. -/
lemma mem_graphₛₗ_zero_iff_mem_ker {x : E} : (x, 0) ∈ f.graphₛₗ ↔ x ∈ f.ker := by
  rw [mem_graphₛₗ_iff, mem_ker_iff]
  exact ⟨fun ⟨y, hy, h⟩ => ⟨y, hy.symm, h⟩, fun ⟨y, hy, h⟩ => ⟨y, hy.symm, h⟩⟩

/-- Injectivity in graph form: `f.ker = ⊥` iff `(x, 0) ∈ graph f` forces `x = 0`. -/
lemma ker_eq_bot_iff_mem_graphₛₗ : f.ker = ⊥ ↔ ∀ x, (x, 0) ∈ f.graphₛₗ → x = 0 := by
  rw [ker_eq_bot']
  constructor
  · rintro h x ⟨y, rfl, hy⟩
    exact congrArg Subtype.val (h y hy)
  · intro h y hy
    exact Subtype.ext (h y ⟨y, rfl, hy⟩)

/-- The range in graph form. -/
lemma mem_range_iff_mem_graphₛₗ {y : F} : y ∈ Set.range f ↔ ∃ x, (x, y) ∈ f.graphₛₗ :=
  ⟨fun ⟨x, hx⟩ => ⟨x, x, rfl, hx⟩, fun ⟨_, x, _, hx⟩ => ⟨x, hx⟩⟩

/-- Extending a partially defined map by zero does not change it on its domain. -/
lemma mem_graphₛₗ_extend {v : E} (hv : v ∈ f.domain) :
    (v, Function.extend Subtype.val f 0 v) ∈ f.graphₛₗ := by
  have h := Subtype.val_injective.extend_apply f 0 ⟨v, hv⟩
  rw [h]
  exact f.mem_graphₛₗ ⟨v, hv⟩

/-! #### The map with a given graph -/

section OfGraph

/-- The projection `{x | ∃ y, (x, y) ∈ g}` of a `σ`-invariant additive subgroup `g ⊆ E × F`, a
submodule. This is an auxiliary definition; the preferred spelling is
`(LinearPMap.ofGraphₛₗ g hsmul hg).domain`. -/
def graphDomainₛₗ (g : AddSubgroup (E × F))
    (hsmul : ∀ (c : R) ⦃x : E⦄ ⦃y : F⦄, (x, y) ∈ g → (c • x, σ c • y) ∈ g) : Submodule R E where
  carrier := {x | ∃ y, (x, y) ∈ g}
  add_mem' := fun ⟨y, hy⟩ ⟨y', hy'⟩ => ⟨y + y', g.add_mem hy hy'⟩
  zero_mem' := ⟨0, g.zero_mem⟩
  smul_mem' c _ := fun ⟨y, hy⟩ => ⟨σ c • y, hsmul c hy⟩

/-- The **semilinear partially defined map with graph `g`**, for an additive subgroup `g ⊆ E × F`
invariant under `(x, y) ↦ (c • x, σ c • y)` that is the graph of a function (`(0, y) ∈ g` forces
`y = 0`); its graph is `g` (`LinearPMap.graphₛₗ_ofGraphₛₗ`). -/
noncomputable def ofGraphₛₗ (g : AddSubgroup (E × F))
    (hsmul : ∀ (c : R) ⦃x : E⦄ ⦃y : F⦄, (x, y) ∈ g → (c • x, σ c • y) ∈ g)
    (hg : ∀ ⦃y : F⦄, ((0 : E), y) ∈ g → y = 0) : E →ₛₗ.[σ] F where
  domain := graphDomainₛₗ g hsmul
  toFun :=
    { toFun := fun x => (x.2 : ∃ y, ((x : E), y) ∈ g).choose
      map_add' := fun x y => sub_eq_zero.mp (hg (by
        simpa using g.sub_mem (x + y).2.choose_spec (g.add_mem x.2.choose_spec y.2.choose_spec)))
      map_smul' := fun c x => sub_eq_zero.mp (hg (by
        simpa using g.sub_mem (c • x).2.choose_spec (hsmul c x.2.choose_spec))) }

/-- The graph of `LinearPMap.ofGraphₛₗ g` is `g`. -/
@[simp]
lemma graphₛₗ_ofGraphₛₗ (g : AddSubgroup (E × F))
    (hsmul : ∀ (c : R) ⦃x : E⦄ ⦃y : F⦄, (x, y) ∈ g → (c • x, σ c • y) ∈ g)
    (hg : ∀ ⦃y : F⦄, ((0 : E), y) ∈ g → y = 0) : (ofGraphₛₗ g hsmul hg).graphₛₗ = g := by
  ext ⟨x, y⟩
  constructor
  · rintro ⟨z, rfl, rfl⟩
    exact (z.2 : ∃ y, ((z : E), y) ∈ g).choose_spec
  · intro h
    refine ⟨⟨x, y, h⟩, rfl, sub_eq_zero.mp (hg ?_)⟩
    have h' := g.sub_mem (⟨y, h⟩ : ∃ y, (x, y) ∈ g).choose_spec h
    rw [Prod.mk_sub_mk, sub_self] at h'
    exact h'

end OfGraph

end Graph

section LinearGraph

variable {R : Type*} [Ring R] {E F : Type*} [AddCommGroup E] [Module R E] [AddCommGroup F]
  [Module R F]

/-- For a linear map, the graph `LinearPMap.graphₛₗ` is Mathlib's `LinearPMap.graph`. -/
@[simp]
lemma mem_graphₛₗ_iff_mem_graph {f : E →ₗ.[R] F} {p : E × F} : p ∈ f.graphₛₗ ↔ p ∈ f.graph :=
  (mem_graph_iff f).symm

/-- The graph `LinearPMap.graphₛₗ` of a linear map is Mathlib's graph, as a set. -/
private lemma coe_graphₛₗ (f : E →ₗ.[R] F) : (f.graphₛₗ : Set (E × F)) = f.graph :=
  Set.ext fun _ => mem_graphₛₗ_iff_mem_graph

/-- For a graph-like submodule `g`, `LinearPMap.ofGraphₛₗ` is Mathlib's `Submodule.toLinearPMap`. -/
lemma ofGraphₛₗ_eq_toLinearPMap (g : Submodule R (E × F))
    (hsmul : ∀ (c : R) ⦃x : E⦄ ⦃y : F⦄, (x, y) ∈ g → (c • x, RingHom.id R c • y) ∈ g)
    (hg : ∀ ⦃y : F⦄, ((0 : E), y) ∈ g → y = 0) :
    ofGraphₛₗ g.toAddSubgroup hsmul hg = g.toLinearPMap :=
  eq_of_eq_graphₛₗ (AddSubgroup.ext fun p => by
    rw [graphₛₗ_ofGraphₛₗ, mem_graphₛₗ_iff_mem_graph,
      Submodule.toLinearPMap_graph_eq g fun x hx hx0 => hg (by rwa [← hx0]), Submodule.mem_toAddSubgroup])

end LinearGraph

/-! ### Composites and their graphs -/

section CompGraph

variable {R₁ R₂ R₃ R₄ : Type*} [Ring R₁] [Ring R₂] [Ring R₃] [Ring R₄]
  {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃} {σ₃₄ : R₃ →+* R₄} {σ₂₄ : R₂ →+* R₄}
  {σ₁₄ : R₁ →+* R₄} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
  {E F G K : Type*} [AddCommGroup E] [Module R₁ E] [AddCommGroup F] [Module R₂ F]
  [AddCommGroup G] [Module R₃ G] [AddCommGroup K] [Module R₄ K]

/-- The graph of `g ∘ f` is the relational composite of the graphs of `f` and `g`. -/
lemma mem_graphₛₗ_compNat {g : F →ₛₗ.[σ₂₃] G} {f : E →ₛₗ.[σ₁₂] F} {x : E} {z : G} :
    (x, z) ∈ (g.compNat (ρ := σ₁₃) f).graphₛₗ ↔ ∃ y, (x, y) ∈ f.graphₛₗ ∧ (y, z) ∈ g.graphₛₗ := by
  simp only [mem_graphₛₗ_iff, Subtype.exists, exists_and_left, exists_eq_left]
  constructor
  · rintro ⟨hx, rfl⟩
    exact ⟨_, ⟨compNat_domain_le hx, rfl⟩, compNat_apply_mem ⟨x, hx⟩, rfl⟩
  · rintro ⟨_, ⟨hx, rfl⟩, hy, rfl⟩
    exact ⟨mem_compNat_domain.mpr ⟨hx, hy⟩, rfl⟩

/-- The graph of the restriction of `f` to `S` is the part of the graph of `f` over `S`. -/
lemma mem_graphₛₗ_domRestrict {f : E →ₛₗ.[σ₁₂] F} {S : Submodule R₁ E} {x : E} {y : F} :
    (x, y) ∈ (f.domRestrict S).graphₛₗ ↔ x ∈ S ∧ (x, y) ∈ f.graphₛₗ := by
  simp only [mem_graphₛₗ_iff, Subtype.exists, exists_and_left, exists_eq_left, domRestrict_domain,
    Submodule.mem_inf]
  constructor
  · rintro ⟨⟨hS, hf⟩, rfl⟩
    exact ⟨hS, hf, (domRestrict_apply rfl).symm⟩
  · rintro ⟨hS, hf, rfl⟩
    exact ⟨⟨hS, hf⟩, domRestrict_apply rfl⟩

/-- The graph of `g ∘ f` for an everywhere-defined `g`: `(x, z)` lies in it iff `z = g y` for
`(x, y)` in the graph of `f`. -/
lemma mem_graphₛₗ_compPMap {g : F →ₛₗ[σ₂₃] G} {f : E →ₛₗ.[σ₁₂] F} {x : E} {z : G} :
    (x, z) ∈ (g.compPMap (ρ := σ₁₃) f).graphₛₗ ↔ ∃ y, (x, y) ∈ f.graphₛₗ ∧ g y = z := by
  simp only [mem_graphₛₗ_iff]
  exact ⟨fun ⟨p, hp, hpz⟩ => ⟨f p, ⟨p, hp, rfl⟩, hpz⟩, fun ⟨_, ⟨p, hp, rfl⟩, hpz⟩ => ⟨p, hp, hpz⟩⟩

/-- The graph of `g ∘ f` for an everywhere-defined `f`: `(x, z)` lies in it iff `(f x, z)` lies in
the graph of `g`. -/
lemma mem_graphₛₗ_compNat_toPMap {g : F →ₛₗ.[σ₂₃] G} {f : E →ₛₗ[σ₁₂] F} {x : E} {z : G} :
    (x, z) ∈ (g.compNat (ρ := σ₁₃) (f.toPMap ⊤)).graphₛₗ ↔ (f x, z) ∈ g.graphₛₗ := by
  rw [mem_graphₛₗ_compNat]
  refine ⟨fun ⟨y, hxy, hyz⟩ => ?_, fun h => ⟨f x, ⟨⟨x, Submodule.mem_top⟩, rfl, rfl⟩, h⟩⟩
  obtain ⟨p, hp, rfl⟩ := hxy
  change (p : E) = x at hp
  subst hp
  exact hyz

/-- The graph of `a • f`: `(x, z)` lies in it iff `z = a • y` for `(x, y)` in the graph of `f`. -/
lemma mem_graphₛₗ_smul {M : Type*} [Monoid M] [DistribMulAction M F] [SMulCommClass R₂ M F]
    (a : M) {f : E →ₛₗ.[σ₁₂] F} {x : E} {z : F} :
    (x, z) ∈ (a • f).graphₛₗ ↔ ∃ y, (x, y) ∈ f.graphₛₗ ∧ a • y = z := by
  simp only [mem_graphₛₗ_iff]
  exact ⟨fun ⟨p, hp, hpz⟩ => ⟨f p, ⟨p, hp, rfl⟩, hpz⟩, fun ⟨_, ⟨p, hp, rfl⟩, hpz⟩ => ⟨p, hp, hpz⟩⟩

/-- Surjectivity of `g + f` in graph form: every `h` is `g u + v` for some `(u, v)` in the graph of
`f`. -/
lemma surjective_vadd_iffₛₗ {f : E →ₛₗ.[σ₁₂] F} {g : E →ₛₗ[σ₁₂] F} :
    Function.Surjective (g +ᵥ f) ↔ ∀ h, ∃ u v, (u, v) ∈ f.graphₛₗ ∧ g u + v = h := by
  refine forall_congr' fun h => ⟨fun ⟨x, hx⟩ => ⟨x, f ⟨x, x.2⟩, f.mem_graphₛₗ ⟨x, x.2⟩, ?_⟩,
    fun ⟨u, v, huv, he⟩ => ?_⟩
  · rw [← hx, vadd_apply]
    rfl
  · obtain ⟨p, rfl, rfl⟩ := huv
    exact ⟨p, by rw [vadd_apply]; exact he⟩

/-- Composition on the natural domain is associative. -/
lemma compNat_assoc [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄] [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄]
    [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄] (h : G →ₛₗ.[σ₃₄] K) (g : F →ₛₗ.[σ₂₃] G)
    (f : E →ₛₗ.[σ₁₂] F) :
    (h.compNat (ρ := σ₂₄) g).compNat (ρ := σ₁₄) f =
      h.compNat (ρ := σ₁₄) (g.compNat (ρ := σ₁₃) f) := by
  refine eq_of_eq_graphₛₗ (AddSubgroup.ext fun ⟨x, w⟩ => ?_)
  simp only [mem_graphₛₗ_compNat]
  exact ⟨fun ⟨y, hxy, z, hyz, hzw⟩ => ⟨z, ⟨y, hxy, hyz⟩, hzw⟩,
    fun ⟨z, ⟨y, hxy, hyz⟩, hzw⟩ => ⟨y, hxy, z, hyz, hzw⟩⟩

/-- Associativity of `compNat` with an everywhere-defined left factor. -/
lemma compPMap_compNat [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄] [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄]
    [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄] (h : G →ₛₗ[σ₃₄] K) (g : F →ₛₗ.[σ₂₃] G)
    (f : E →ₛₗ.[σ₁₂] F) :
    (h.compPMap (ρ := σ₂₄) g).compNat (ρ := σ₁₄) f =
      h.compPMap (ρ := σ₁₄) (g.compNat (ρ := σ₁₃) f) := by
  rw [← toPMap_compNat, ← toPMap_compNat, compNat_assoc]

/-- Composition on the natural domain is monotone in both factors. -/
lemma compNat_mono {g g' : F →ₛₗ.[σ₂₃] G} {f f' : E →ₛₗ.[σ₁₂] F} (hg : g ≤ g') (hf : f ≤ f') :
    g.compNat (ρ := σ₁₃) f ≤ g'.compNat f' := by
  refine le_of_le_graphₛₗ fun ⟨x, z⟩ hxz => ?_
  obtain ⟨y, hxy, hyz⟩ := mem_graphₛₗ_compNat.mp hxz
  exact mem_graphₛₗ_compNat.mpr ⟨y, le_graphₛₗ_of_le hf hxy, le_graphₛₗ_of_le hg hyz⟩

/-- Composition with an everywhere-defined left factor is monotone. -/
lemma compPMap_mono (g : F →ₛₗ[σ₂₃] G) {f f' : E →ₛₗ.[σ₁₂] F} (hf : f ≤ f') :
    g.compPMap (ρ := σ₁₃) f ≤ g.compPMap f' := by
  rw [← toPMap_compNat, ← toPMap_compNat]
  exact compNat_mono le_rfl hf

/-- An everywhere-defined composite, as a partially defined map, is the composite of the factors. -/
lemma toPMap_comp (g : F →ₛₗ[σ₂₃] G) (f : E →ₛₗ[σ₁₂] F) :
    (g.comp f).toPMap ⊤ = (g.toPMap ⊤).compNat (ρ := σ₁₃) (f.toPMap ⊤) := by
  rw [toPMap_compNat]
  rfl

/-- Composition with everywhere-defined left factors is associative. -/
lemma compPMap_comp [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄] [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄]
    [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄] (h : G →ₛₗ[σ₃₄] K) (g : F →ₛₗ[σ₂₃] G) (f : E →ₛₗ.[σ₁₂] F) :
    (h.comp (σ₁₃ := σ₂₄) g).compPMap (ρ := σ₁₄) f =
      h.compPMap (ρ := σ₁₄) (g.compPMap (ρ := σ₁₃) f) :=
  ext rfl fun _ _ _ => rfl

/-- Composition with everywhere-defined right factors is associative. -/
lemma compNat_toPMap_comp [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄] [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄]
    [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄] (h : G →ₛₗ.[σ₃₄] K) (g : F →ₛₗ[σ₂₃] G)
    (f : E →ₛₗ[σ₁₂] F) :
    h.compNat (ρ := σ₁₄) ((g.comp (σ₁₃ := σ₁₃) f).toPMap ⊤) =
      (h.compNat (ρ := σ₂₄) (g.toPMap ⊤)).compNat (ρ := σ₁₄) (f.toPMap ⊤) := by
  rw [toPMap_comp, compNat_assoc]

/-- The identity is a left unit for composition. -/
@[simp]
lemma id_compPMap (f : E →ₛₗ.[σ₁₂] F) : LinearMap.id.compPMap f = f :=
  ext rfl fun _ _ _ => rfl

/-- The identity is a right unit for composition. -/
@[simp]
lemma compNat_toPMap_id (f : E →ₛₗ.[σ₁₂] F) : f.compNat (LinearMap.id.toPMap ⊤) = f :=
  eq_of_eq_graphₛₗ (AddSubgroup.ext fun ⟨_, _⟩ => mem_graphₛₗ_compNat_toPMap)

/-- **Intertwining, pointwise**: `g T ⊆ S f` iff every point `(u, v)` of the graph of `T` is mapped
to the point `(f u, g v)` of the graph of `S`. -/
lemma compPMap_le_compNat_toPMap_iffₛₗ [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄]
    [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄] {T : E →ₛₗ.[σ₁₂] F} {S : G →ₛₗ.[σ₃₄] K}
    {f : E →ₛₗ[σ₁₃] G} {g : F →ₛₗ[σ₂₄] K} :
    g.compPMap (ρ := σ₁₄) T ≤ S.compNat (ρ := σ₁₄) (f.toPMap ⊤) ↔
      ∀ ⦃u v⦄, (u, v) ∈ T.graphₛₗ → (f u, g v) ∈ S.graphₛₗ := by
  rw [le_iff_mem_graphₛₗ]
  constructor
  · intro h u v hv
    exact mem_graphₛₗ_compNat_toPMap.mp (h (mem_graphₛₗ_compPMap.mpr ⟨v, hv, rfl⟩))
  · intro h u z hz
    obtain ⟨v, hv, rfl⟩ := mem_graphₛₗ_compPMap.mp hz
    exact mem_graphₛₗ_compNat_toPMap.mpr (h hv)

/-- **Extension by a composite, pointwise**: `g A ⊆ T` iff `(x, g u)` lies in the graph of `T` for
every point `(x, u)` of the graph of `A`. -/
lemma compPMap_le_iffₛₗ {A : E →ₛₗ.[σ₁₂] F} {T : E →ₛₗ.[σ₁₃] G} {g : F →ₛₗ[σ₂₃] G} :
    g.compPMap A ≤ T ↔ ∀ ⦃x u⦄, (x, u) ∈ A.graphₛₗ → (x, g u) ∈ T.graphₛₗ := by
  rw [le_iff_mem_graphₛₗ]
  constructor
  · intro h x u hu
    exact h (mem_graphₛₗ_compPMap.mpr ⟨u, hu, rfl⟩)
  · intro h x z hz
    obtain ⟨u, hu, rfl⟩ := mem_graphₛₗ_compPMap.mp hz
    exact h hu

end CompGraph

/-- **Involutions, pointwise**: `S S = 1` on `dom S` iff the graph of `S` is symmetric, i.e.
`S x = v` implies `S v = x`. Here `S` is `σ`-semilinear with `σ ∘ σ = id`, for instance
conjugate-linear. -/
lemma compNat_self_eq_id_iff {R E : Type*} [Ring R] [AddCommGroup E] [Module R E] {σ : R →+* R}
    [RingHomCompTriple σ σ (RingHom.id R)] {S : E →ₛₗ.[σ] E} :
    S.compNat S = LinearMap.id.toPMap S.domain ↔
      ∀ ⦃x v⦄, (x, v) ∈ S.graphₛₗ → (v, x) ∈ S.graphₛₗ := by
  constructor
  · intro h x v hxv
    obtain ⟨p, rfl, rfl⟩ := hxv
    have hp : (p : E) ∈ (S.compNat S).domain := by rw [h]; exact p.2
    have hval : S.compNat S ⟨p, hp⟩ = p := h.le.2 (x := ⟨p, hp⟩) (y := ⟨p, p.2⟩) rfl
    rw [compNat_apply] at hval
    exact ⟨⟨S ⟨p, compNat_domain_le hp⟩, compNat_apply_mem (g := S) (f := S) ⟨(p : E), hp⟩⟩, rfl,
      hval⟩
  · intro h
    refine ext (Submodule.ext fun x => ?_) fun x hx _ => ?_
    · rw [mem_compNat_domain]
      exact ⟨fun ⟨hx, _⟩ => hx,
        fun hx => ⟨hx, mem_domain_of_mem_graphₛₗ (h (S.mem_graphₛₗ ⟨x, hx⟩))⟩⟩
    · rw [compNat_apply]
      exact ((eq_apply_iff_mem_graphₛₗ _).mpr (h (S.mem_graphₛₗ _))).symm

/-! ### Linear maps -/

section Linear

variable {R E F G K : Type*} [Ring R] [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
  [AddCommGroup G] [Module R G] [AddCommGroup K] [Module R K]

/-- The graph of `g ∘ f` is the relational composite of the graphs of `f` and `g`. -/
lemma mem_graph_compNat {g : F →ₗ.[R] G} {f : E →ₗ.[R] F} {x : E} {z : G} :
    (x, z) ∈ (g.compNat f).graph ↔ ∃ y, (x, y) ∈ f.graph ∧ (y, z) ∈ g.graph := by
  simp only [← mem_graphₛₗ_iff_mem_graph, mem_graphₛₗ_compNat]

/-- The graph of the restriction of `f` to `S` is the part of the graph of `f` over `S`. -/
lemma mem_graph_domRestrict {f : E →ₗ.[R] F} {S : Submodule R E} {x : E} {y : F} :
    (x, y) ∈ (f.domRestrict S).graph ↔ x ∈ S ∧ (x, y) ∈ f.graph := by
  simp only [← mem_graphₛₗ_iff_mem_graph, mem_graphₛₗ_domRestrict]

/-- **Inclusion of operators, pointwise**: `f ≤ g` iff every point of the graph of `f` lies in the
graph of `g`, i.e. `x ∈ dom f` forces `x ∈ dom g` and `g x = f x`. -/
lemma le_iff_mem_graph {f g : E →ₗ.[R] F} :
    f ≤ g ↔ ∀ ⦃x : E⦄ ⦃y : F⦄, (x, y) ∈ f.graph → (x, y) ∈ g.graph := by
  simp only [← mem_graphₛₗ_iff_mem_graph, le_iff_mem_graphₛₗ]

/-- The graph of `g ∘ f` for an everywhere-defined `g`: `(x, z)` lies in it iff `z = g y` for
`(x, y)` in the graph of `f`. -/
lemma mem_graph_compPMap {g : F →ₗ[R] G} {f : E →ₗ.[R] F} {x : E} {z : G} :
    (x, z) ∈ (g.compPMap f).graph ↔ ∃ y, (x, y) ∈ f.graph ∧ g y = z := by
  simp only [← mem_graphₛₗ_iff_mem_graph, mem_graphₛₗ_compPMap]

/-- The graph of `g ∘ f` for an everywhere-defined `f`: `(x, z)` lies in it iff `(f x, z)` lies in
the graph of `g`. -/
lemma mem_graph_compNat_toPMap {g : F →ₗ.[R] G} {f : E →ₗ[R] F} {x : E} {z : G} :
    (x, z) ∈ (g.compNat (f.toPMap ⊤)).graph ↔ (f x, z) ∈ g.graph := by
  simp only [← mem_graphₛₗ_iff_mem_graph, mem_graphₛₗ_compNat_toPMap]

/-- **Intertwining, pointwise**: `g T ⊆ S f` iff every point `(u, v)` of the graph of `T` is mapped
to the point `(f u, g v)` of the graph of `S`. -/
lemma compPMap_le_compNat_toPMap_iff {T : E →ₗ.[R] F} {S : G →ₗ.[R] K} {f : E →ₗ[R] G}
    {g : F →ₗ[R] K} :
    g.compPMap T ≤ S.compNat (f.toPMap ⊤) ↔ ∀ ⦃u v⦄, (u, v) ∈ T.graph → (f u, g v) ∈ S.graph := by
  simp only [← mem_graphₛₗ_iff_mem_graph, compPMap_le_compNat_toPMap_iffₛₗ]

/-- **Extension by a composite, pointwise**: `g A ⊆ T` iff `(x, g u)` lies in the graph of `T` for
every point `(x, u)` of the graph of `A`. -/
lemma compPMap_le_iff {A : E →ₗ.[R] F} {T : E →ₗ.[R] G} {g : F →ₗ[R] G} :
    g.compPMap A ≤ T ↔ ∀ ⦃x u⦄, (x, u) ∈ A.graph → (x, g u) ∈ T.graph := by
  simp only [← mem_graphₛₗ_iff_mem_graph, compPMap_le_iffₛₗ]

/-- The graph of `a • f`: `(x, z)` lies in it iff `z = a • y` for `(x, y)` in the graph of `f`. -/
lemma mem_graph_smul {M : Type*} [Monoid M] [DistribMulAction M F] [SMulCommClass R M F] (a : M)
    {f : E →ₗ.[R] F} {x : E} {z : F} :
    (x, z) ∈ (a • f).graph ↔ ∃ y, (x, y) ∈ f.graph ∧ a • y = z := by
  simp only [← mem_graphₛₗ_iff_mem_graph, mem_graphₛₗ_smul]

/-- The kernel in graph form: `x ∈ ker f` iff `(x, 0)` lies in the graph of `f`. -/
lemma mem_graph_zero_iff_mem_ker {f : E →ₗ.[R] F} {x : E} : (x, 0) ∈ f.graph ↔ x ∈ f.ker := by
  rw [← mem_graphₛₗ_iff_mem_graph, mem_graphₛₗ_zero_iff_mem_ker]

/-- Surjectivity of `g + f` in graph form: every `h` is `g u + v` for some `(u, v)` in the graph of
`f`. -/
lemma surjective_vadd_iff {f : E →ₗ.[R] F} {g : E →ₗ[R] F} :
    Function.Surjective (g +ᵥ f) ↔ ∀ h, ∃ u v, (u, v) ∈ f.graph ∧ g u + v = h := by
  simp only [← mem_graphₛₗ_iff_mem_graph, surjective_vadd_iffₛₗ]

/-- Injectivity in graph form: `f.ker = ⊥` iff `(x, 0) ∈ graph f` forces `x = 0`. -/
lemma ker_eq_bot_iff_mem_graph {f : E →ₗ.[R] F} : f.ker = ⊥ ↔ ∀ x, (x, 0) ∈ f.graph → x = 0 := by
  simp only [← mem_graphₛₗ_iff_mem_graph, ker_eq_bot_iff_mem_graphₛₗ]

/-- The graph of the inverse of an injective partial linear map is its flipped graph. -/
lemma mem_graph_inverse_iff {f : E →ₗ.[R] F} (hf : f.ker = ⊥) {x : E} {y : F} :
    (y, x) ∈ f.inverse.graph ↔ (x, y) ∈ f.graph := by
  rw [inverse_graph hf, Submodule.map_equiv_eq_comap_symm]
  rfl

section SemilinearEquiv

variable {S E K : Type*} [Ring S] [AddCommGroup E] [Module S E] [AddCommGroup K] [Module S K]
  {σ σ' : S →+* S} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]

/-- **Conjugation by a semilinear equivalence, pointwise**: `B V = V A` iff `V × V` maps the graph
of `A` onto the graph of `B`. -/
lemma compNat_toPMap_eq_compPMap_iff {A : E →ₗ.[S] E} {B : K →ₗ.[S] K} (V : E ≃ₛₗ[σ] K) :
    B.compNat ((V : E →ₛₗ[σ] K).toPMap ⊤) = (V : E →ₛₗ[σ] K).compPMap A ↔
      ∀ u v, (u, v) ∈ A.graph ↔ (V u, V v) ∈ B.graph := by
  constructor
  · intro h u v
    constructor
    · intro huv
      obtain ⟨p, rfl, rfl⟩ := (mem_graph_iff A).mp huv
      have hp : (p : E) ∈ (B.compNat ((V : E →ₛₗ[σ] K).toPMap ⊤)).domain := h.ge.1 p.2
      have hval := h.ge.2 (x := ⟨p, p.2⟩) (y := ⟨p, hp⟩) rfl
      rw [compNat_toPMap_apply] at hval
      exact (mem_graph_iff B).mpr ⟨⟨_, mem_compNat_toPMap_domain.mp hp⟩, rfl, hval.symm⟩
    · intro huv
      have hu : u ∈ (B.compNat ((V : E →ₛₗ[σ] K).toPMap ⊤)).domain :=
        mem_compNat_toPMap_domain.mpr (mem_domain_of_mem_graph huv)
      have hval := h.le.2 (x := ⟨u, hu⟩) (y := ⟨u, h.le.1 hu⟩) rfl
      rw [compNat_toPMap_apply] at hval
      have hBu : B ⟨V u, mem_domain_of_mem_graph huv⟩ = V v := ((image_iff _).mpr huv).symm
      have hV : V (A ⟨u, h.le.1 hu⟩) = V v := by
        rw [← hBu]
        exact hval.symm
      exact (image_iff (h.le.1 hu)).mp (V.injective hV).symm
  · intro h
    have hdom : ∀ u, u ∈ (B.compNat ((V : E →ₛₗ[σ] K).toPMap ⊤)).domain ↔ u ∈ A.domain := fun u => by
      rw [mem_compNat_toPMap_domain, mem_domain_iff, mem_domain_iff]
      exact ⟨fun ⟨y, hy⟩ => ⟨V.symm y, (h _ _).mpr (by rwa [V.apply_symm_apply])⟩,
        fun ⟨y, hy⟩ => ⟨V y, (h _ _).mp hy⟩⟩
    refine ext (Submodule.ext hdom) fun x hx hx' => ?_
    rw [compNat_toPMap_apply]
    exact ((image_iff _).mpr ((h _ _).mp (A.mem_graph ⟨x, hx'⟩))).symm

end SemilinearEquiv

end Linear

/-! ### Closed and closable semilinear maps -/

section Topology

variable {R S : Type*} [Ring R] [Ring S] {σ : R →+* S}
  {E F : Type*} [AddCommGroup E] [Module R E] [AddCommGroup F] [Module S F]
  [TopologicalSpace E] [TopologicalSpace F]

/-- A semilinear partially defined map is **closed** if its graph is closed. For a linear map
this is Mathlib's `LinearPMap.IsClosed` (`LinearPMap.isClosedₛₗ_iff_isClosed`). -/
def IsClosedₛₗ (f : E →ₛₗ.[σ] F) : Prop :=
  _root_.IsClosed (f.graphₛₗ : Set (E × F))

/-- A semilinear partially defined map is **closable** if the closure of its graph is the graph of
a semilinear partially defined map, the closure `LinearPMap.closureₛₗ`. -/
def IsClosableₛₗ (f : E →ₛₗ.[σ] F) : Prop :=
  ∃ f' : E →ₛₗ.[σ] F, _root_.closure (f.graphₛₗ : Set (E × F)) = f'.graphₛₗ

open scoped Classical in
/-- The **closure** of a semilinear partially defined map: for a closable `f`, the map whose graph
is the closure of the graph of `f` (`LinearPMap.IsClosableₛₗ.coe_graphₛₗ_closureₛₗ`), and `f`
itself otherwise. For a linear map it is Mathlib's `LinearPMap.closure`
(`LinearPMap.closureₛₗ_eq_closure`). -/
noncomputable def closureₛₗ (f : E →ₛₗ.[σ] F) : E →ₛₗ.[σ] F :=
  if hf : f.IsClosableₛₗ then hf.choose else f

variable {f g : E →ₛₗ.[σ] F}

/-- The closure of a closable map is the chosen map with the closed graph. -/
lemma closureₛₗ_def (hf : f.IsClosableₛₗ) : f.closureₛₗ = hf.choose := by
  simp [closureₛₗ, hf]

/-- The closure of a non-closable map is the map itself. -/
lemma closureₛₗ_def' (hf : ¬f.IsClosableₛₗ) : f.closureₛₗ = f := by
  simp [closureₛₗ, hf]

/-- The graph of the closure is the closure of the graph. -/
lemma IsClosableₛₗ.coe_graphₛₗ_closureₛₗ (hf : f.IsClosableₛₗ) :
    (f.closureₛₗ.graphₛₗ : Set (E × F)) = _root_.closure (f.graphₛₗ : Set (E × F)) := by
  rw [closureₛₗ_def hf]
  exact hf.choose_spec.symm

/-- A closed map is closable. -/
lemma IsClosedₛₗ.isClosableₛₗ (hf : f.IsClosedₛₗ) : f.IsClosableₛₗ :=
  ⟨f, hf.closure_eq⟩

/-- A map is contained in its closure. -/
lemma le_closureₛₗ (f : E →ₛₗ.[σ] F) : f ≤ f.closureₛₗ := by
  by_cases hf : f.IsClosableₛₗ
  · refine le_of_le_graphₛₗ fun p hp => ?_
    rw [← SetLike.mem_coe, hf.coe_graphₛₗ_closureₛₗ]
    exact subset_closure hp
  · rw [closureₛₗ_def' hf]

/-- The closure of a closable map is closed. -/
lemma IsClosableₛₗ.isClosedₛₗ_closureₛₗ (hf : f.IsClosableₛₗ) : f.closureₛₗ.IsClosedₛₗ := by
  rw [IsClosedₛₗ, hf.coe_graphₛₗ_closureₛₗ]
  exact isClosed_closure

/-- A closed map is its own closure. -/
lemma IsClosedₛₗ.closureₛₗ_eq (hf : f.IsClosedₛₗ) : f.closureₛₗ = f :=
  eq_of_eq_graphₛₗ (SetLike.coe_injective (by
    rw [hf.isClosableₛₗ.coe_graphₛₗ_closureₛₗ]
    exact _root_.IsClosed.closure_eq hf))

/-- The closure of a densely defined map is densely defined. -/
lemma dense_domain_closureₛₗ (hf : Dense (f.domain : Set E)) :
    Dense (f.closureₛₗ.domain : Set E) :=
  hf.mono (le_closureₛₗ f).1

/-- A continuous map carrying the graph of `T₁` into the graph of a closable `T₂` carries the graph
of the closure `T̄₁` into that of `T̄₂`. -/
lemma mem_graphₛₗ_closureₛₗ_of_mapsTo {R' S' : Type*} [Ring R'] [Ring S'] {σ' : R' →+* S'}
    {E' F' : Type*} [AddCommGroup E'] [Module R' E'] [AddCommGroup F'] [Module S' F']
    [TopologicalSpace E'] [TopologicalSpace F'] {T₂ : E' →ₛₗ.[σ'] F'} (h₂ : T₂.IsClosableₛₗ)
    {φ : E × F → E' × F'} (hφ : Continuous φ) (h : ∀ p ∈ f.graphₛₗ, φ p ∈ T₂.graphₛₗ)
    {p : E × F} (hp : p ∈ f.closureₛₗ.graphₛₗ) : φ p ∈ T₂.closureₛₗ.graphₛₗ := by
  rw [← SetLike.mem_coe, h₂.coe_graphₛₗ_closureₛₗ]
  by_cases h₁ : f.IsClosableₛₗ
  · rw [← SetLike.mem_coe, h₁.coe_graphₛₗ_closureₛₗ] at hp
    exact map_mem_closure hφ hp h
  · rw [closureₛₗ_def' h₁] at hp
    exact subset_closure (h p hp)

variable [IsTopologicalAddGroup E] [IsTopologicalAddGroup F] [ContinuousConstSMul R E]
  [ContinuousConstSMul S F]

/-- **Closability criterion**: `f` is closable iff the closure of its graph is the graph of a
function, i.e. contains no point `(0, y)` with `y ≠ 0`. -/
lemma isClosableₛₗ_iff :
    f.IsClosableₛₗ ↔ ∀ ⦃y : F⦄, ((0 : E), y) ∈ _root_.closure (f.graphₛₗ : Set (E × F)) → y = 0 := by
  constructor
  · rintro ⟨f', hf'⟩ y hy
    rw [hf'] at hy
    exact graphₛₗ_fst_eq_zero_snd hy rfl
  · intro h
    refine ⟨ofGraphₛₗ f.graphₛₗ.topologicalClosure (fun c x y hxy => ?_) (fun y hy => h ?_), ?_⟩
    · rw [← SetLike.mem_coe, AddSubgroup.topologicalClosure_coe] at hxy ⊢
      exact map_mem_closure (f := fun p : E × F => (c • p.1, σ c • p.2)) (by fun_prop) hxy
        fun p hp => smul_mem_graphₛₗ c hp
    · rwa [← SetLike.mem_coe, AddSubgroup.topologicalClosure_coe] at hy
    · rw [graphₛₗ_ofGraphₛₗ, AddSubgroup.topologicalClosure_coe]

/-- A restriction of a closable map is closable. -/
lemma IsClosableₛₗ.leIsClosableₛₗ (hf : f.IsClosableₛₗ) (hgf : g ≤ f) : g.IsClosableₛₗ :=
  isClosableₛₗ_iff.mpr fun _ hy => isClosableₛₗ_iff.mp hf
    (closure_mono (SetLike.coe_subset_coe.mpr (le_graphₛₗ_of_le hgf)) hy)

/-- The closure is monotone. -/
lemma IsClosableₛₗ.closureₛₗ_mono (hg : g.IsClosableₛₗ) (h : f ≤ g) :
    f.closureₛₗ ≤ g.closureₛₗ := by
  refine le_of_le_graphₛₗ fun p hp => ?_
  rw [← SetLike.mem_coe, (hg.leIsClosableₛₗ h).coe_graphₛₗ_closureₛₗ] at hp
  rw [← SetLike.mem_coe, hg.coe_graphₛₗ_closureₛₗ]
  exact closure_mono (SetLike.coe_subset_coe.mpr (le_graphₛₗ_of_le h)) hp

/-- A map is closable iff it has a closed extension. -/
lemma isClosableₛₗ_iff_exists_closed_extension :
    f.IsClosableₛₗ ↔ ∃ g : E →ₛₗ.[σ] F, g.IsClosedₛₗ ∧ f ≤ g :=
  ⟨fun hf => ⟨f.closureₛₗ, hf.isClosedₛₗ_closureₛₗ, le_closureₛₗ f⟩,
    fun ⟨_, hg, hfg⟩ => hg.isClosableₛₗ.leIsClosableₛₗ hfg⟩

end Topology

/-! ### Closures of composites with bounded maps -/

section TopologyComp

variable {R₁ R₂ R₃ R₄ : Type*} [Ring R₁] [Ring R₂] [Ring R₃] [Ring R₄]
  {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃} {σ₁₄ : R₁ →+* R₄} {σ₄₃ : R₄ →+* R₃}
  [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
  {E F G E' : Type*} [AddCommGroup E] [Module R₁ E] [TopologicalSpace E]
  [AddCommGroup F] [Module R₂ F] [TopologicalSpace F] [AddCommGroup G] [Module R₃ G]
  [TopologicalSpace G] [AddCommGroup E'] [Module R₄ E'] [TopologicalSpace E']

/-- **`B T̄ ⊆ closure (B T)`** for a bounded `B` with `B T` closable. -/
lemma compPMap_closureₛₗ_le {T : E →ₛₗ.[σ₁₂] F} (hT : T.IsClosableₛₗ) (B : F →SL[σ₂₃] G)
    (hBT : ((B : F →ₛₗ[σ₂₃] G).compPMap (ρ := σ₁₃) T).IsClosableₛₗ) :
    (B : F →ₛₗ[σ₂₃] G).compPMap (ρ := σ₁₃) T.closureₛₗ ≤
      ((B : F →ₛₗ[σ₂₃] G).compPMap (ρ := σ₁₃) T).closureₛₗ := by
  -- the closure of a graph is a limit argument
  refine le_of_le_graphₛₗ fun ⟨x, z⟩ hz => ?_
  obtain ⟨y, hy, rfl⟩ := mem_graphₛₗ_compPMap.mp hz
  rw [← SetLike.mem_coe, hT.coe_graphₛₗ_closureₛₗ] at hy
  rw [← SetLike.mem_coe, hBT.coe_graphₛₗ_closureₛₗ]
  exact map_mem_closure (f := fun p : E × F => (p.1, B p.2)) (by fun_prop) hy
    fun p hp => mem_graphₛₗ_compPMap.mpr ⟨p.2, hp, rfl⟩

/-- A closed operator composed with a bounded right factor is closed. -/
lemma IsClosedₛₗ.compNat_toPMap {T : F →ₛₗ.[σ₂₃] G} (hT : T.IsClosedₛₗ) (B : E →SL[σ₁₂] F) :
    (T.compNat (ρ := σ₁₃) ((B : E →ₛₗ[σ₁₂] F).toPMap ⊤)).IsClosedₛₗ := by
  -- the graph is the preimage of the graph of `T` under `(x, z) ↦ (B x, z)`
  have h : ((T.compNat (ρ := σ₁₃) ((B : E →ₛₗ[σ₁₂] F).toPMap ⊤)).graphₛₗ : Set (E × G)) =
      (fun p : E × G => (B p.1, p.2)) ⁻¹' T.graphₛₗ :=
    Set.ext fun ⟨_, _⟩ => mem_graphₛₗ_compNat_toPMap
  rw [IsClosedₛₗ, h]
  exact hT.preimage (by fun_prop)

/-- A continuous everywhere-defined map is closed: its graph is `{(x, B x)}`. -/
lemma isClosedₛₗ_toPMap [T2Space F] (B : E →SL[σ₁₂] F) :
    ((B : E →ₛₗ[σ₁₂] F).toPMap ⊤).IsClosedₛₗ := by
  have h : (((B : E →ₛₗ[σ₁₂] F).toPMap ⊤).graphₛₗ : Set (E × F)) = {p | B p.1 = p.2} :=
    Set.ext fun p => by simp [mem_graphₛₗ_iff]
  rw [IsClosedₛₗ, h]
  exact isClosed_eq (by fun_prop) continuous_snd

variable [IsTopologicalAddGroup E] [IsTopologicalAddGroup G] [ContinuousConstSMul R₁ E]
  [ContinuousConstSMul R₃ G]

/-- **`closure (T B) ⊆ T̄ B`** for a closable `T` and a bounded `B`. -/
lemma closureₛₗ_compNat_toPMap_le {T : F →ₛₗ.[σ₂₃] G} (hT : T.IsClosableₛₗ) (B : E →SL[σ₁₂] F) :
    (T.compNat (ρ := σ₁₃) ((B : E →ₛₗ[σ₁₂] F).toPMap ⊤)).closureₛₗ ≤
      T.closureₛₗ.compNat (ρ := σ₁₃) ((B : E →ₛₗ[σ₁₂] F).toPMap ⊤) := by
  have hc := hT.isClosedₛₗ_closureₛₗ.compNat_toPMap (σ₁₃ := σ₁₃) B
  have h := hc.isClosableₛₗ.closureₛₗ_mono (compNat_mono (le_closureₛₗ T) le_rfl)
  rwa [hc.closureₛₗ_eq] at h

variable [RingHomCompTriple σ₁₄ σ₄₃ σ₁₃]

/-- **Intertwining passes to closures**: if `B T ⊆ S C` for closable `T`, `S` and bounded `B`, `C`,
then `B T̄ ⊆ S̄ C`, since `B T̄ ⊆ closure (B T) ⊆ closure (S̄ C) = S̄ C`. -/
lemma compPMap_closureₛₗ_le_closureₛₗ_compNat_toPMap {T : E →ₛₗ.[σ₁₂] F}
    {S : E' →ₛₗ.[σ₄₃] G} (hT : T.IsClosableₛₗ) (hS : S.IsClosableₛₗ) (B : F →SL[σ₂₃] G)
    (C : E →SL[σ₁₄] E')
    (h : (B : F →ₛₗ[σ₂₃] G).compPMap (ρ := σ₁₃) T ≤
      S.compNat (ρ := σ₁₃) ((C : E →ₛₗ[σ₁₄] E').toPMap ⊤)) :
    (B : F →ₛₗ[σ₂₃] G).compPMap (ρ := σ₁₃) T.closureₛₗ ≤
      S.closureₛₗ.compNat (ρ := σ₁₃) ((C : E →ₛₗ[σ₁₄] E').toPMap ⊤) := by
  have hc := hS.isClosedₛₗ_closureₛₗ.compNat_toPMap (σ₁₃ := σ₁₃) C
  have h' := h.trans (compNat_mono (le_closureₛₗ S) le_rfl)
  calc (B : F →ₛₗ[σ₂₃] G).compPMap (ρ := σ₁₃) T.closureₛₗ
      ≤ ((B : F →ₛₗ[σ₂₃] G).compPMap (ρ := σ₁₃) T).closureₛₗ :=
        compPMap_closureₛₗ_le hT B (hc.isClosableₛₗ.leIsClosableₛₗ h')
    _ ≤ (S.closureₛₗ.compNat (ρ := σ₁₃) ((C : E →ₛₗ[σ₁₄] E').toPMap ⊤)).closureₛₗ :=
        hc.isClosableₛₗ.closureₛₗ_mono h'
    _ = _ := hc.closureₛₗ_eq

end TopologyComp

section LinearTopology

variable {R E F : Type*} [CommRing R] [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
  [TopologicalSpace E] [TopologicalSpace F]

/-- For a linear map, `LinearPMap.IsClosedₛₗ` is Mathlib's `LinearPMap.IsClosed`. -/
lemma isClosedₛₗ_iff_isClosed {f : E →ₗ.[R] F} : f.IsClosedₛₗ ↔ f.IsClosed := by
  rw [IsClosedₛₗ, LinearPMap.IsClosed, coe_graphₛₗ]

variable [ContinuousAdd E] [ContinuousAdd F] [TopologicalSpace R] [ContinuousSMul R E]
  [ContinuousSMul R F]

/-- For a linear map, `LinearPMap.closureₛₗ` is Mathlib's `LinearPMap.closure`. -/
lemma closureₛₗ_eq_closure (f : E →ₗ.[R] F) : f.closureₛₗ = f.closure := by
  have hiff : f.IsClosableₛₗ ↔ f.IsClosable := exists_congr fun f' => by
    rw [coe_graphₛₗ, coe_graphₛₗ, ← Submodule.topologicalClosure_coe, SetLike.coe_set_eq]
  by_cases hf : f.IsClosable
  · refine eq_of_eq_graphₛₗ (SetLike.coe_injective ?_)
    rw [(hiff.mpr hf).coe_graphₛₗ_closureₛₗ, coe_graphₛₗ, coe_graphₛₗ,
      ← hf.graph_closure_eq_closure_graph, Submodule.topologicalClosure_coe]
  · rw [closureₛₗ_def' (mt hiff.mp hf), closure_def' hf]

end LinearTopology

/-! ### Restriction of scalars -/

section RestrictScalars

variable (R₀ : Type*) {R S E F : Type*} [Ring R₀] [Ring R] [Ring S] {σ : R →+* S}
  [SMul R₀ R] [SMul R₀ S]
  [AddCommGroup E] [Module R E] [Module R₀ E] [IsScalarTower R₀ R E]
  [AddCommGroup F] [Module S F] [Module R₀ F] [IsScalarTower R₀ S F]

/-- A `σ`-semilinear partially defined map, regarded as an `R₀`-linear one for scalars `R₀` fixed
by `σ` (`σ (r • 1) = r • 1`), with the same domain, values and graph
(`LinearPMap.mem_graph_restrictScalars`). For a complex-linear or conjugate-linear map between
complex spaces and `R₀ = ℝ` it is the underlying real-linear map. -/
def restrictScalars (hσ : ∀ r : R₀, σ (r • 1) = r • 1) (T : E →ₛₗ.[σ] F) : E →ₗ.[R₀] F where
  domain := T.domain.restrictScalars R₀
  toFun :=
    { toFun := fun x => T ⟨x, x.2⟩
      map_add' := fun x y => T.map_add ⟨x, x.2⟩ ⟨y, y.2⟩
      map_smul' := fun c x => by
        change T ⟨c • (x : E), _⟩ = c • T ⟨x, x.2⟩
        have h : (⟨c • (x : E), (T.domain.restrictScalars R₀).smul_mem c x.2⟩ : T.domain) =
            (c • (1 : R)) • (⟨x, x.2⟩ : T.domain) := Subtype.ext (smul_one_smul R c (x : E)).symm
        rw [h, T.map_smulₛₗ, hσ, smul_one_smul] }

variable {R₀} {hσ : ∀ r : R₀, σ (r • 1) = r • 1} {T : E →ₛₗ.[σ] F}

/-- The domain of `T.restrictScalars R₀ hσ` is the domain of `T`. -/
@[simp]
lemma restrictScalars_domain : (T.restrictScalars R₀ hσ).domain = T.domain.restrictScalars R₀ :=
  rfl

/-- `T.restrictScalars R₀ hσ` takes the same values as `T`. -/
lemma restrictScalars_apply (x : (T.restrictScalars R₀ hσ).domain) :
    T.restrictScalars R₀ hσ x = T ⟨x, x.2⟩ :=
  rfl

/-- The graph of `T.restrictScalars R₀ hσ` is the graph of `T`. -/
@[simp]
lemma mem_graph_restrictScalars {p : E × F} :
    p ∈ (T.restrictScalars R₀ hσ).graph ↔ p ∈ T.graphₛₗ := by
  rw [mem_graph_iff, mem_graphₛₗ_iff]
  exact ⟨fun ⟨y, h₁, h₂⟩ => ⟨⟨y, y.2⟩, h₁, h₂⟩, fun ⟨y, h₁, h₂⟩ => ⟨⟨y, y.2⟩, h₁, h₂⟩⟩

/-- Restriction of scalars preserves and reflects inclusions. -/
@[simp]
lemma restrictScalars_le_iff {T' : E →ₛₗ.[σ] F} :
    T.restrictScalars R₀ hσ ≤ T'.restrictScalars R₀ hσ ↔ T ≤ T' := by
  rw [le_iff_mem_graph, le_iff_mem_graphₛₗ]
  simp only [mem_graph_restrictScalars]

/-- Restriction of scalars commutes with taking kernels. -/
lemma restrictScalars_ker : (T.restrictScalars R₀ hσ).ker = T.ker.restrictScalars R₀ := by
  ext x
  simp only [mem_ker_iff, Submodule.restrictScalars_mem, restrictScalars_domain, Subtype.exists]
  rfl

/-- Restriction of scalars is injective on partially defined maps. -/
lemma restrictScalars_injective :
    Function.Injective (restrictScalars R₀ hσ : (E →ₛₗ.[σ] F) → E →ₗ.[R₀] F) := fun T T' h =>
  eq_of_eq_graphₛₗ (AddSubgroup.ext fun p => by
    rw [← mem_graph_restrictScalars (R₀ := R₀) (hσ := hσ), h, mem_graph_restrictScalars])

section Comp

variable {U : Type*} [Ring U] {τ : S →+* U} {ρ : R →+* U} [RingHomCompTriple σ τ ρ] [SMul R₀ U]
  {G : Type*} [AddCommGroup G] [Module U G] [Module R₀ G] [IsScalarTower R₀ U G]
  {hτ : ∀ r : R₀, τ (r • 1) = r • 1} {hρ : ∀ r : R₀, ρ (r • 1) = r • 1}

/-- Restriction of scalars commutes with composition on the natural domain. -/
lemma restrictScalars_compNat (g : F →ₛₗ.[τ] G) (f : E →ₛₗ.[σ] F) :
    (g.compNat (ρ := ρ) f).restrictScalars R₀ hρ =
      (g.restrictScalars R₀ hτ).compNat (f.restrictScalars R₀ hσ) :=
  eq_of_eq_graph (Submodule.ext fun ⟨_, _⟩ => by
    simp only [mem_graph_restrictScalars, mem_graph_compNat, mem_graphₛₗ_compNat])

end Comp

end RestrictScalars

section RestrictScalarsTopology

variable {R₀ R S E F : Type*} [CommRing R₀] [Ring R] [Ring S] {σ : R →+* S}
  [SMul R₀ R] [SMul R₀ S]
  [AddCommGroup E] [Module R E] [Module R₀ E] [IsScalarTower R₀ R E]
  [AddCommGroup F] [Module S F] [Module R₀ F] [IsScalarTower R₀ S F]
  {hσ : ∀ r : R₀, σ (r • 1) = r • 1} {T : E →ₛₗ.[σ] F}

/-- The graph of `T.restrictScalars R₀ hσ` is the graph of `T`, as a set. -/
lemma coe_graph_restrictScalars :
    ((T.restrictScalars R₀ hσ).graph : Set (E × F)) = T.graphₛₗ :=
  Set.ext fun _ => mem_graph_restrictScalars

variable [TopologicalSpace E] [TopologicalSpace F]

/-- `T.restrictScalars R₀ hσ` is closed iff `T` is. -/
@[simp]
lemma isClosed_restrictScalars_iff : (T.restrictScalars R₀ hσ).IsClosed ↔ T.IsClosedₛₗ := by
  rw [LinearPMap.IsClosed, IsClosedₛₗ, coe_graph_restrictScalars]

variable [IsTopologicalAddGroup E] [IsTopologicalAddGroup F] [ContinuousConstSMul R E]
  [ContinuousConstSMul S F] [TopologicalSpace R₀] [ContinuousSMul R₀ E] [ContinuousSMul R₀ F]

omit [ContinuousConstSMul R E] [ContinuousConstSMul S F] in
/-- The closure of the graph of `T.restrictScalars R₀ hσ` is that of `T`. -/
lemma coe_topologicalClosure_graph_restrictScalars :
    ((T.restrictScalars R₀ hσ).graph.topologicalClosure : Set (E × F)) =
      _root_.closure (T.graphₛₗ : Set (E × F)) := by
  rw [Submodule.topologicalClosure_coe, coe_graph_restrictScalars]

/-- `T.restrictScalars R₀ hσ` is closable iff `T` is. -/
@[simp]
lemma isClosable_restrictScalars_iff : (T.restrictScalars R₀ hσ).IsClosable ↔ T.IsClosableₛₗ := by
  constructor
  · rintro ⟨T', hT'⟩
    refine isClosableₛₗ_iff.mpr fun y hy => T'.graph_fst_eq_zero_snd ?_ rfl
    rw [← SetLike.mem_coe, ← hT', coe_topologicalClosure_graph_restrictScalars]
    exact hy
  · intro hT
    refine ⟨T.closureₛₗ.restrictScalars R₀ hσ, SetLike.coe_injective ?_⟩
    rw [coe_topologicalClosure_graph_restrictScalars, coe_graph_restrictScalars,
      hT.coe_graphₛₗ_closureₛₗ]

/-- The closure commutes with restriction of scalars. -/
lemma closure_restrictScalars :
    (T.restrictScalars R₀ hσ).closure = T.closureₛₗ.restrictScalars R₀ hσ := by
  by_cases hT : T.IsClosableₛₗ
  · refine eq_of_eq_graph (SetLike.coe_injective ?_)
    rw [← (isClosable_restrictScalars_iff.mpr hT).graph_closure_eq_closure_graph,
      coe_topologicalClosure_graph_restrictScalars, coe_graph_restrictScalars,
      hT.coe_graphₛₗ_closureₛₗ]
  · rw [closure_def' (mt isClosable_restrictScalars_iff.mp hT), closureₛₗ_def' hT]

end RestrictScalarsTopology

end LinearPMap
