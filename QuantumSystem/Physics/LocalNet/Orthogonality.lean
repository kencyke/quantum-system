/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Data.Finset.Disjoint
public import Mathlib.Order.Directed

/-!
# Causal orthogonality of regions

The regions of a net form an ordered set `K` (in the literature, the open bounded regions of
spacetime ordered by inclusion) with a **causal orthogonality relation** `O₁ ⟂ O₂`
(`CausalOrthogonality`, abstracting spacelike separation), symmetric and hereditary under shrinking
regions. This file is about that relation alone: the existence of causal complements, the
literature's third axiom on the index set, is `CausalIndexSet` in
`QuantumSystem.Physics.LocalNet.Causality`, and locality — what the relation demands of a net — is
in `QuantumSystem.Physics.LocalNet.Locality`.

The order is carried as a `Preorder` throughout, not a `PartialOrder`: the literature's index sets
are ordered by inclusion and so are partial orders, but antisymmetry is used nowhere in this
development, so demanding it would restrict the interface without buying anything.

**Directedness.** Nothing here assumes the index set directed — the intervals of the circle, its
open, connected, nonempty and non-dense subsets, are not: two intervals covering the circle have no
interval above both. Without directedness, two causally orthogonal regions
need not have a common upper bound; the derived relation `⊥̂` (`CausalOrthogonality.OrthogonalHat`)
adds that demand. It collapses onto `⟂` whenever `K` is directed
(`CausalOrthogonality.orthogonalHat_iff`), and directedness of `K` is equivalent to the collapse for
*every* `CausalOrthogonality K` (`CausalOrthogonality.isDirectedOrder_iff_forall_orthogonalHat_iff`).
What this means for the locality of a net is in `QuantumSystem.Physics.LocalNet.Locality`.

**Lattice regions.** The finite regions `Finset α` of a lattice, the nonempty ones and the possibly
infinite ones `Set α` carry causal orthogonality `Disjoint`.

## Notation

`O₁ ⟂ O₂` is `CausalOrthogonality.Orthogonal O₁ O₂`, causal orthogonality of regions; activate it
with `open scoped CausalOrthogonality`.

`𝔄(O)` in the prose is documentation shorthand for the local C⋆-algebra `N.algebra O`; the
convention is stated in full in `QuantumSystem.Physics.LocalNet.Isotony`.
-/

@[expose] public section

/-! ### The relation `⟂` -/

/-- A **causal orthogonality relation** on an index set of regions: `O₁ ⟂ O₂` abstracts causal
    (spacelike) disjointness of regions, the relation under which the Haag–Kastler locality axiom
    applies. It is symmetric and hereditary under shrinking regions.

    The literature's axiomatization (Guido–Longo–Roberts–Verch, arXiv math-ph/9906019, §3.1)
    asks for three conditions: symmetry, heredity,
    and the existence of causal complements (`∀ O₁, ∃ O₂, O₁ ⟂ O₂`). This class carries the first
    two, which are properties of the relation itself; the third is a property of the *index set*
    and is carried separately, as the mixin `CausalIndexSet`
    (`QuantumSystem.Physics.LocalNet.Causality`). Splitting it off keeps this
    class available where the third condition is absent or in doubt: the corpus secures it in
    three different ways — through a membership condition (Guido–Longo–Roberts–Verch's regular
    diamonds demand a non-void causal complement to *be* a region), by admitting the empty region
    (lattice regions, where `∅` is disjoint from everything), or not at all.

    What the third condition buys — on a *directed* index set, through heredity — is that causal
    orthogonality refines the *other* derived relation of Guido–Longo–Roberts–Verch (`⊥̃`, a common
    orthogonal partner rather than a common upper bound), and through it the duality theory of the
    dual net and the DHR selection criterion; without directedness it has no order-theoretic
    consequence at all, since adjoining a bottom element related to everything satisfies all three
    conditions on any poset. None of that is used here.

    The relation is *not* required to be irreflexive: `O ⟂ O` legitimately holds for degenerate
    regions (e.g. the empty lattice region) and forces `𝔄(O)` to be commutative. For Minkowski
    double cones one instantiates `⟂` with spacelike separation — note this is *not* set
    disjointness (disjoint timelike-separated regions are not causally orthogonal), which is why
    the relation is carried as data rather than derived from the order. -/
class CausalOrthogonality (K : Type*) [Preorder K] where
  /-- The causal orthogonality relation `O₁ ⟂ O₂` on regions. -/
  Orthogonal : K → K → Prop
  /-- Causal orthogonality is symmetric. -/
  orthogonal_symm : ∀ ⦃O₁ O₂ : K⦄, Orthogonal O₁ O₂ → Orthogonal O₂ O₁
  /-- Causal orthogonality is hereditary under shrinking the left region. -/
  orthogonal_mono_left : ∀ ⦃O₀ O₁ O₂ : K⦄, O₀ ≤ O₁ → Orthogonal O₁ O₂ → Orthogonal O₀ O₂

namespace CausalOrthogonality

/-- `O₁ ⟂ O₂` : the regions `O₁` and `O₂` are causally orthogonal (spacelike separated).

    The token `⟂` is also used globally by Mathlib for `Submodule.IsOrtho` at precedence 50;
    this scoped notation is declared at the same precedence so that the two coexist by
    type-directed disambiguation. -/
scoped infixl:50 " ⟂ " => CausalOrthogonality.Orthogonal

variable {K : Type*} [Preorder K] [CausalOrthogonality K]

/-- Causal orthogonality is symmetric (dot-notation form). -/
lemma Orthogonal.symm {O₁ O₂ : K} (h : O₁ ⟂ O₂) : O₂ ⟂ O₁ :=
  orthogonal_symm h

/-- Causal orthogonality is hereditary under shrinking the left region. -/
lemma Orthogonal.mono_left {O₀ O₁ O₂ : K} (h₀ : O₀ ≤ O₁) (h : O₁ ⟂ O₂) : O₀ ⟂ O₂ :=
  orthogonal_mono_left h₀ h

/-- Causal orthogonality is hereditary under shrinking the right region. -/
lemma Orthogonal.mono_right {O₁ O₂ O₃ : K} (h₀ : O₃ ≤ O₂) (h : O₁ ⟂ O₂) : O₁ ⟂ O₃ :=
  (h.symm.mono_left h₀).symm

/-- Causal orthogonality is hereditary under shrinking both regions. -/
lemma Orthogonal.mono {O₁' O₁ O₂' O₂ : K} (h₁ : O₁' ≤ O₁) (h₂ : O₂' ≤ O₂)
    (h : O₁ ⟂ O₂) : O₁' ⟂ O₂' :=
  (h.mono_left h₁).mono_right h₂

/-! ### The derived relation `⊥̂`

Guido–Longo–Roberts–Verch derive from `⟂` a relation written `⊥̂`, obtained by supplementing
`O₁ ⟂ O₂` with the demand that `O₁` and `O₂` have a **common upper bound** in the index set. It is
purely order- and `⟂`-theoretic — no topology, no closures — so it is available over
`CausalOrthogonality` exactly as that class stands. On a directed index set it collapses back onto
`⟂` (`orthogonalHat_iff`); off one it *can* be strictly weaker, though whether it is depends on the
relation — the collapse characterises directedness only after quantifying over all causal
orthogonality relations on the index set (`isDirectedOrder_iff_forall_orthogonalHat_iff`). The whole
`⟂` / `⊥̂` distinction is the price of dropping directedness.

It is carried here because it, and not `⟂`, is what the locality of a net
(`QuantumSystem.Physics.LocalNet.Locality`) actually constrains: see
`CStarNet.Grading.IsGradedLocal.exists_commute_of_orthogonalHat` and, for a local net,
`GradedLocalNet.locality` and `GradedLocalNet.exists_locality_of_orthogonalHat`.

No notation is introduced for it: the literature's `⊥̂` needs a combining accent, and the relation
appears rarely enough that the spelled-out name reads better than a near-collision with `⟂`.
-/

/-- The **derived orthogonality relation `⊥̂`** of Guido–Longo–Roberts–Verch: `O₁` and `O₂` are
    causally orthogonal *and* admit a common upper bound in the index set.

    This is the relation on which the locality axiom of a net bites, since commutation of
    `𝔄(O₁)` with `𝔄(O₂)` can only be *stated* inside an algebra containing both. On a directed
    index set it is `⟂` itself (`orthogonalHat_iff`). -/
def OrthogonalHat (O₁ O₂ : K) : Prop :=
  O₁ ⟂ O₂ ∧ ∃ O₃, O₁ ≤ O₃ ∧ O₂ ≤ O₃

/-- The derived relation refines causal orthogonality. -/
lemma OrthogonalHat.orthogonal {O₁ O₂ : K} (h : OrthogonalHat O₁ O₂) : O₁ ⟂ O₂ :=
  h.1

/-- A common upper bound of a pair related by the derived relation. -/
lemma OrthogonalHat.exists_upperBound {O₁ O₂ : K} (h : OrthogonalHat O₁ O₂) :
    ∃ O₃, O₁ ≤ O₃ ∧ O₂ ≤ O₃ :=
  h.2

/-- The derived relation is symmetric. Symmetry of `⟂` is what is used on the first component;
    a common upper bound is symmetric on the nose. -/
lemma OrthogonalHat.symm {O₁ O₂ : K} (h : OrthogonalHat O₁ O₂) : OrthogonalHat O₂ O₁ :=
  ⟨h.1.symm, h.2.imp fun _ hO => ⟨hO.2, hO.1⟩⟩

/-- The derived relation is hereditary under shrinking the left region: heredity of `⟂` handles
    the first component and transitivity of `≤` the upper bound. -/
lemma OrthogonalHat.mono_left {O₀ O₁ O₂ : K} (h₀ : O₀ ≤ O₁) (h : OrthogonalHat O₁ O₂) :
    OrthogonalHat O₀ O₂ :=
  ⟨h.1.mono_left h₀, h.2.imp fun _ hO => ⟨h₀.trans hO.1, hO.2⟩⟩

/-- The derived relation is hereditary under shrinking the right region. -/
lemma OrthogonalHat.mono_right {O₁ O₂ O₃ : K} (h₀ : O₃ ≤ O₂) (h : OrthogonalHat O₁ O₂) :
    OrthogonalHat O₁ O₃ :=
  (h.symm.mono_left h₀).symm

/-- The derived relation is hereditary under shrinking both regions. -/
lemma OrthogonalHat.mono {O₁' O₁ O₂' O₂ : K} (h₁ : O₁' ≤ O₁) (h₂ : O₂' ≤ O₂)
    (h : OrthogonalHat O₁ O₂) : OrthogonalHat O₁' O₂' :=
  (h.mono_left h₁).mono_right h₂

/-- **Passing to the derived relation is idempotent**: supplementing `⊥̂` with the demand for a
    common upper bound asks for nothing new, since `⊥̂` already carries one. No axiom of
    `CausalOrthogonality` is used. -/
lemma orthogonalHat_and_exists_upperBound_iff {O₁ O₂ : K} :
    (OrthogonalHat O₁ O₂ ∧ ∃ O₃, O₁ ≤ O₃ ∧ O₂ ≤ O₃) ↔ OrthogonalHat O₁ O₂ :=
  ⟨And.left, fun h => ⟨h, h.2⟩⟩

/-- **On a directed index set the derived relation is causal orthogonality itself.** Directedness
    supplies the common upper bound, and no axiom of `CausalOrthogonality` is needed.

    Only this implication holds for a *fixed* orthogonality relation: off a directed index set the
    two need not differ, since an empty `⟂` collapses onto `⊥̂` on any preorder. The sharp converse
    quantifies over the relation (`isDirectedOrder_iff_forall_orthogonalHat_iff`). Where they do
    differ it is `⊥̂` that the locality axiom of a net constrains: on the two-element
    antichain `{O₁, O₂}` with `O₁ ⟂ O₂` there is no common upper bound at all, so `⊥̂` is empty
    there while `⟂` is not. -/
lemma orthogonalHat_iff [IsDirectedOrder K] {O₁ O₂ : K} :
    OrthogonalHat O₁ O₂ ↔ O₁ ⟂ O₂ :=
  ⟨OrthogonalHat.orthogonal, fun h => ⟨h, directed_of (· ≤ ·) O₁ O₂⟩⟩

/-- **Directedness is exactly the coincidence of `⊥̂` with `⟂`, quantified over the relation.**
    For one fixed `CausalOrthogonality K` the coincidence is strictly weaker than directedness —
    the empty relation collapses on every preorder. The forward direction is `orthogonalHat_iff`, and the
    converse tests directedness against the *total* relation, in which every pair is causally
    orthogonal and `⊥̂` therefore records nothing but the existence of a common upper bound. -/
lemma isDirectedOrder_iff_forall_orthogonalHat_iff (K : Type*) [Preorder K] :
    IsDirectedOrder K ↔
      ∀ [CausalOrthogonality K] (O₁ O₂ : K), OrthogonalHat O₁ O₂ ↔ O₁ ⟂ O₂ := by
  constructor
  · intro _ _ _ _
    exact orthogonalHat_iff
  · intro h
    refine ⟨fun O₁ O₂ => ?_⟩
    let : CausalOrthogonality K :=
      { Orthogonal := fun _ _ => True
        orthogonal_symm := fun _ _ _ => trivial
        orthogonal_mono_left := fun _ _ _ _ _ => trivial }
    exact ((h O₁ O₂).2 trivial).2

end CausalOrthogonality

/-! ### Lattice regions -/

/-- On the finite regions of a lattice of sites, causal orthogonality is plain set disjointness:
    a lattice net is kinematical (equal-time), so "spacelike separated" degenerates to "disjoint in
    space" (Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §3.4). -/
instance {α : Type*} : CausalOrthogonality (Finset α) where
  Orthogonal := Disjoint
  orthogonal_symm _ _ h := h.symm
  orthogonal_mono_left _ _ _ h₀ h := h.mono_left h₀

/-- On the **nonempty** finite regions of a lattice, causal orthogonality is again disjointness of
    the underlying sets, as on `Finset α`. -/
instance {α : Type*} : CausalOrthogonality {s : Finset α // s.Nonempty} where
  Orthogonal s t := Disjoint (s : Finset α) t
  orthogonal_symm _ _ h := h.symm
  orthogonal_mono_left _ _ _ h₀ h := h.mono_left h₀

namespace CausalOrthogonality

/-- No nonempty finite region is causally orthogonal to itself. -/
lemma not_orthogonal_self_nonemptyFinset {α : Type*} (s : {s : Finset α // s.Nonempty}) :
    ¬ s ⟂ s :=
  fun h => s.2.ne_empty (disjoint_self.1 h)

end CausalOrthogonality

/-- On the possibly **infinite** regions of a lattice of sites — half-chains, cones, complements
    of finite regions — causal orthogonality is again set disjointness. These are the regions the
    lattice split property is about; a net over finite regions reaches them through
    `VonNeumannNet.extend` (`QuantumSystem.Physics.LocalNet.InfiniteRegion`). -/
instance {α : Type*} : CausalOrthogonality (Set α) where
  Orthogonal := Disjoint
  orthogonal_symm _ _ h := h.symm
  orthogonal_mono_left _ _ _ h₀ h := h.mono_left h₀
