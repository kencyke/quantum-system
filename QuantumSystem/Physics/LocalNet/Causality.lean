/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Data.Fintype.EquivFin
public import QuantumSystem.Physics.LocalNet.Orthogonality

/-!
# Causal index sets

An ordered set `K` of regions with a causal orthogonality relation
(`QuantumSystem.Physics.LocalNet.Orthogonality`) is a **causal index set** when every region admits
a causally disjoint one: the existence of causal complements, the literature's third axiom on the
index set. It is the mixin `CausalIndexSet`, kept separate from `CausalOrthogonality` because not
every index family of the corpus satisfies it.

On a directed causal index set every region has a partner for the derived relation `⊥̂`
(`CausalIndexSet.exists_orthogonalHat`), so the locality of a net binds at every region.

**Lattice regions.** The finite regions `Finset α` of a lattice and the possibly infinite ones
`Set α` form causal index sets through the empty region; the nonempty finite ones do when `α` is
infinite.
-/

@[expose] public section

open scoped CausalOrthogonality

/-- A **causal index set** in the full sense of Guido–Longo–Roberts–Verch §3.1: on top of the
    symmetry and heredity carried by `CausalOrthogonality`, the third condition of the
    axiomatization — the **existence of causal complements**, every region admitting a causally
    disjoint one. An ordered `K` with `[CausalOrthogonality K]` and this mixin is exactly the
    causal index set of Guido–Longo–Roberts–Verch, arXiv math-ph/9906019, §3.1.

    Carried as a mixin rather than folded into `CausalOrthogonality`, because unlike symmetry and
    heredity this condition is a property of the index set rather than of the relation, and the
    corpus's index families do not all satisfy it (see the docstring of `CausalOrthogonality`).
    It is genuinely model-dependent input: what this development draws from it is
    `CausalIndexSet.exists_orthogonalHat` — on a directed index set the locality axiom of a
    net bites at every region — while the duality theory it really feeds (the dual net, and
    the DHR analysis built on the selection criterion `CStarNet.SatisfiesDHR`, which itself needs
    no causal complements) is not formalized here; the literature's causal index set is not
    expressible without it. -/
class CausalIndexSet (K : Type*) [Preorder K] [CausalOrthogonality K] : Prop where
  /-- Every region admits a causally disjoint region — axiom c) of the
      Guido–Longo–Roberts–Verch axiomatization. -/
  exists_orthogonal : ∀ O₁ : K, ∃ O₂, O₁ ⟂ O₂

/-- **On a directed causal index set every region has a `⊥̂`-orthogonal partner**: directedness
    upgrades the causal complement supplied by `exists_orthogonal` to the derived relation `⊥̂`
    (`CausalOrthogonality.orthogonalHat_iff`), which is the relation the locality axiom of a
    net actually constrains. So the locality axiom is nowhere vacuous on such an index set:
    `GradedLocalNet.exists_locality_of_orthogonalHat` applies at every region. -/
lemma CausalIndexSet.exists_orthogonalHat {K : Type*} [Preorder K] [CausalOrthogonality K]
    [IsDirectedOrder K] [CausalIndexSet K] (O : K) :
    ∃ O', CausalOrthogonality.OrthogonalHat O O' :=
  let ⟨O', h⟩ := CausalIndexSet.exists_orthogonal O
  ⟨O', CausalOrthogonality.orthogonalHat_iff.2 h⟩

/-! ### Lattice regions -/

/-- The lattice regions form a causal index set in the full sense: the **empty region** is
    disjoint from every region, so causal complements exist for free. This is how the literature's
    lattice index set secures the condition — through `∅ ∈ 𝒦` rather than through a membership
    clause — at the price of `⟂` being reflexive at `∅`. -/
instance {α : Type*} : CausalIndexSet (Finset α) :=
  ⟨fun Λ => ⟨∅, Finset.disjoint_empty_right Λ⟩⟩

/-- The nonempty finite regions of an infinite lattice form a causal index set: a nonempty finite
    region `s` is disjoint from `{p}` for a site `p ∉ s`. Unlike on `Finset α`, the causal complement
    is not supplied by an empty region. -/
instance {α : Type*} [Infinite α] : CausalIndexSet {s : Finset α // s.Nonempty} :=
  ⟨fun s =>
    let ⟨p, hp⟩ := Infinite.exists_notMem_finset (s : Finset α)
    ⟨⟨{p}, Finset.singleton_nonempty p⟩, Finset.disjoint_singleton_right.2 hp⟩⟩

/-- The infinite lattice regions form a causal index set in the full sense, through the empty
    region, exactly as the finite ones do. -/
instance {α : Type*} : CausalIndexSet (Set α) :=
  ⟨fun S => ⟨∅, disjoint_bot_right (a := S)⟩⟩
