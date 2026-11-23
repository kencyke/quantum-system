/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Physics.LocalNet.Grading
public import QuantumSystem.Physics.LocalNet.Orthogonality

/-!
# Locality of a net

**Locality** (microcausality, Einstein causality) is what a causal orthogonality relation `⟂` on
the regions (`QuantumSystem.Physics.LocalNet.Orthogonality`) demands of a net of C⋆-algebras: the
algebras of causally orthogonal regions commute. It is stated here in its graded form, for a net
with a grading (`QuantumSystem.Physics.LocalNet.Grading`): `CStarNet.Grading.IsGradedLocal` asks
that, for causally orthogonal regions, even elements commute with everything and odd elements
anticommute. This is the locality of a system with fermions, where the fermionic operators of
different regions anticommute. Locality proper is the case of the trivial grading, where every
element is even and graded locality is commutation (`CStarNet.Grading.isGradedLocal_trivial_iff`).

**What locality means without directedness.** Nothing here assumes the index set directed, so a
non-directed `K` — the proper intervals of the circle, wedges — carries a graded-local net perfectly
well. Locality, however, is weaker there than its name suggests: commutation of `𝔄(O₁)` with
`𝔄(O₂)` has to be stated inside an algebra containing both, so it binds a common upper bound of the
two regions and therefore constrains only the pairs related by `⊥̂`
(`CausalOrthogonality.OrthogonalHat`), which is `⟂` on a directed index set. The dichotomy is
spelled out at `CStarNet.Grading.IsGradedLocal.exists_commute_of_orthogonalHat` and
`CStarNet.Grading.IsGradedLocal.exists_commute_of_orthogonal`, and the regions carrying the
interesting statements are precisely the ones it bites on: a region and its causal complement
typically have no common upper bound in the index set — on the circle their union misses only two
points and so is neither connected nor non-dense, hence not a region. A net over such an index set
needing graded locality for `⟂` itself must be taken as a net of von Neumann algebras with a grading
(`VonNeumannNet.Grading.IsGradedLocal`, in `QuantumSystem.Physics.LocalNet.VonNeumannNet`), where
the ambient `𝓑(H)` removes the obstruction.

## Main definitions and results

* `CStarNet.Grading.IsGradedLocal Γ` — graded locality of the net with the grading `Γ`.
* `CStarNet.Grading.isGradedLocal_trivial_iff` — for the trivial grading, graded locality is
  commutation.
* `CStarNet.Grading.isGradedLocal_iff_sup` — over a join-semilattice of regions, graded locality
  inside the joins is graded locality.
* `CStarNet.Grading.isGradedLocal_iff_orthogonalHat` — graded locality constrains exactly the
  pairs of regions related by `⊥̂`; `CStarNet.Grading.IsGradedLocal.exists_commute_of_orthogonalHat`,
  `CStarNet.Grading.IsGradedLocal.exists_commute_of_orthogonal` — the directedness dichotomy.
-/

@[expose] public section

open scoped CausalOrthogonality

namespace CStarNet.Grading

section Preorder

variable {K : Type*} [Preorder K] [CausalOrthogonality K] {N : CStarNet K}

/-- **Graded locality** of a net with a grading, over a causal index set: for causally orthogonal
    regions, an even element commutes with every element of the other region (`locality_even`) and
    two odd elements anticommute (`locality_odd`), inside any common larger region.

    The common region `O` is bound *before* the orthogonality hypothesis, and that is not an
    accident of phrasing: `Commute x y` for `x : 𝔄(O₁)` and `y : 𝔄(O₂)` is not even typeable
    without an algebra containing both, and over a non-directed index set there need be no such
    region — nor any quasi-local algebra to fall back on. So the pairs these statements constrain
    are exactly those causally orthogonal pairs that admit a common upper bound, which is the
    derived relation `CausalOrthogonality.OrthogonalHat` (`⊥̂`) rather than `⟂` itself. The two
    coincide on directed index sets (`CausalOrthogonality.orthogonalHat_iff`) — and, once the
    orthogonality relation is quantified over, only there
    (`CausalOrthogonality.isDirectedOrder_iff_forall_orthogonalHat_iff`). -/
structure IsGradedLocal (Γ : N.Grading) : Prop where
  /-- **Graded locality**, even elements: an even element localised in a region commutes with
      every element localised in a causally orthogonal region, inside any common larger region. -/
  locality_even : ∀ {O₁ O₂ O : K} (h₁ : O₁ ≤ O) (h₂ : O₂ ≤ O), O₁ ⟂ O₂ →
      ∀ (x : N.algebra O₁) (y : N.algebra O₂), Γ.parity O₁ x = x →
        Commute (N.incl h₁ x) (N.incl h₂ y)
  /-- **Graded locality**, odd elements: odd elements localised in causally orthogonal regions
      anticommute inside any common larger region. -/
  locality_odd : ∀ {O₁ O₂ O : K} (h₁ : O₁ ≤ O) (h₂ : O₂ ≤ O), O₁ ⟂ O₂ →
      ∀ (x : N.algebra O₁) (y : N.algebra O₂), Γ.parity O₁ x = -x → Γ.parity O₂ y = -y →
        N.incl h₁ x * N.incl h₂ y = -(N.incl h₂ y * N.incl h₁ x)

/-- **For the trivial grading, graded locality is commutation**: every element is even, so the
    algebras of causally orthogonal regions commute inside any common larger region, and no element
    other than `0` is odd. -/
theorem isGradedLocal_trivial_iff :
    (Grading.trivial N).IsGradedLocal ↔
      ∀ ⦃O₁ O₂ O : K⦄ (h₁ : O₁ ≤ O) (h₂ : O₂ ≤ O), O₁ ⟂ O₂ →
        ∀ (x : N.algebra O₁) (y : N.algebra O₂), Commute (N.incl h₁ x) (N.incl h₂ y) := by
  refine ⟨fun h _ _ _ h₁ h₂ hd x y => h.locality_even h₁ h₂ hd x y rfl, fun h => ⟨?_, ?_⟩⟩
  · intro _ _ _ h₁ h₂ hd x y _
    exact h h₁ h₂ hd x y
  · intro _ _ _ h₁ h₂ hd x y hx _
    rw [trivial_parity_apply] at hx
    have h2 : (2 : ℂ) • x = 0 := by
      rw [two_smul]
      exact eq_neg_iff_add_eq_zero.mp hx
    have hx0 : x = 0 := (smul_eq_zero.mp h2).resolve_left two_ne_zero
    simp [hx0]

/-! ### What locality constrains

Graded locality quantifies over a common upper bound of the two regions, so the pairs it constrains
are exactly those related by the derived relation `⊥̂` of `CausalOrthogonality.OrthogonalHat`. The
first theorem below says exactly this; the two after it are the directedness dichotomy:
`⊥̂`-related pairs always get commutation somewhere, and on a directed index set that is every
causally orthogonal pair. They are stated for even elements; for a local net, whose elements are
all even, they are `GradedLocalNet.exists_locality_of_orthogonalHat` and
`GradedLocalNet.exists_locality_of_orthogonal`.
-/

/-- **Graded locality is graded locality for the derived relation `⊥̂`**: it says that the pairs of
    regions related by `⊥̂` graded-commute inside every common upper bound, and nothing about a
    causally orthogonal pair with no common upper bound. -/
theorem isGradedLocal_iff_orthogonalHat {Γ : N.Grading} :
    Γ.IsGradedLocal ↔
      (∀ ⦃O₁ O₂ : K⦄, CausalOrthogonality.OrthogonalHat O₁ O₂ →
        ∀ ⦃O : K⦄ (h₁ : O₁ ≤ O) (h₂ : O₂ ≤ O) (x : N.algebra O₁) (y : N.algebra O₂),
          Γ.parity O₁ x = x → Commute (N.incl h₁ x) (N.incl h₂ y)) ∧
      (∀ ⦃O₁ O₂ : K⦄, CausalOrthogonality.OrthogonalHat O₁ O₂ →
        ∀ ⦃O : K⦄ (h₁ : O₁ ≤ O) (h₂ : O₂ ≤ O) (x : N.algebra O₁) (y : N.algebra O₂),
          Γ.parity O₁ x = -x → Γ.parity O₂ y = -y →
            N.incl h₁ x * N.incl h₂ y = -(N.incl h₂ y * N.incl h₁ x)) :=
  ⟨fun h => ⟨fun _ _ hd _ h₁ h₂ => h.locality_even h₁ h₂ hd.orthogonal,
      fun _ _ hd _ h₁ h₂ => h.locality_odd h₁ h₂ hd.orthogonal⟩,
    fun h => ⟨fun h₁ h₂ hd => h.1 ⟨hd, _, h₁, h₂⟩ h₁ h₂,
      fun h₁ h₂ hd => h.2 ⟨hd, _, h₁, h₂⟩ h₁ h₂⟩⟩

/-- The even elements of a region commute with a causally orthogonal region inside a common upper
    bound, when there is one. For a causally orthogonal pair with *no* common upper bound graded
    locality says nothing (`isGradedLocal_iff_orthogonalHat`), and cannot, since the commutation
    has nowhere to be stated. -/
theorem IsGradedLocal.exists_commute_of_orthogonalHat {Γ : N.Grading} (hΓ : Γ.IsGradedLocal)
    {O₁ O₂ : K} (h : CausalOrthogonality.OrthogonalHat O₁ O₂) :
    ∃ (O : K) (h₁ : O₁ ≤ O) (h₂ : O₂ ≤ O),
      ∀ (x : N.algebra O₁) (y : N.algebra O₂), Γ.parity O₁ x = x →
        Commute (N.incl h₁ x) (N.incl h₂ y) :=
  let ⟨O, h₁, h₂⟩ := h.exists_upperBound
  ⟨O, h₁, h₂, hΓ.locality_even h₁ h₂ h.orthogonal⟩

/-- **On a directed index set locality is locality for `⟂` itself**: directedness supplies the
    common upper bound, so the even elements of a region commute with every causally orthogonal
    region inside some region. -/
theorem IsGradedLocal.exists_commute_of_orthogonal [IsDirectedOrder K] {Γ : N.Grading}
    (hΓ : Γ.IsGradedLocal) {O₁ O₂ : K} (h : O₁ ⟂ O₂) :
    ∃ (O : K) (h₁ : O₁ ≤ O) (h₂ : O₂ ≤ O),
      ∀ (x : N.algebra O₁) (y : N.algebra O₂), Γ.parity O₁ x = x →
        Commute (N.incl h₁ x) (N.incl h₂ y) :=
  hΓ.exists_commute_of_orthogonalHat (CausalOrthogonality.orthogonalHat_iff.2 h)

end Preorder

section SemilatticeSup

variable {K : Type*} [SemilatticeSup K] [CausalOrthogonality K] {N : CStarNet K}

/-- Over a join-semilattice of regions, **graded locality inside the canonical join region
    `O₁ ⊔ O₂` is graded locality**: a relation there pushes forward along
    `incl : 𝔄(O₁ ⊔ O₂) →⋆ₐ[ℂ] 𝔄(O)` to any common superregion `O`. For lattice nets
    (`K = Finset sites`) the join is the union of regions. -/
theorem isGradedLocal_iff_sup {Γ : N.Grading} :
    Γ.IsGradedLocal ↔
      (∀ ⦃O₁ O₂ : K⦄, O₁ ⟂ O₂ → ∀ (x : N.algebra O₁) (y : N.algebra O₂), Γ.parity O₁ x = x →
        Commute (N.incl le_sup_left x) (N.incl le_sup_right y)) ∧
      (∀ ⦃O₁ O₂ : K⦄, O₁ ⟂ O₂ → ∀ (x : N.algebra O₁) (y : N.algebra O₂),
        Γ.parity O₁ x = -x → Γ.parity O₂ y = -y →
          N.incl le_sup_left x * N.incl le_sup_right y =
            -(N.incl le_sup_right y * N.incl le_sup_left x)) := by
  refine ⟨fun h => ⟨fun _ _ hd => h.locality_even _ _ hd, fun _ _ hd => h.locality_odd _ _ hd⟩,
    fun h => ⟨fun h₁ h₂ hd x y hx => ?_, fun h₁ h₂ hd x y hx hy => ?_⟩⟩
  · have h' := (h.1 hd x y hx).map (N.incl (sup_le h₁ h₂))
    rwa [N.incl_trans, N.incl_trans] at h'
  · have h' := congrArg (N.incl (sup_le h₁ h₂)) (h.2 hd x y hx hy)
    rwa [map_mul, map_neg, map_mul, N.incl_trans, N.incl_trans] at h'

/-- For the trivial grading over a join-semilattice of regions, **commutation inside the canonical
    join region `O₁ ⊔ O₂` is locality** (`isGradedLocal_iff_sup` for the trivial grading). -/
theorem isGradedLocal_trivial_of_sup
    (h : ∀ ⦃O₁ O₂ : K⦄, O₁ ⟂ O₂ → ∀ (x : N.algebra O₁) (y : N.algebra O₂),
      Commute (N.incl le_sup_left x) (N.incl le_sup_right y)) :
    (Grading.trivial N).IsGradedLocal :=
  isGradedLocal_trivial_iff.mpr fun _ _ _ h₁ h₂ hd x y => by
    have h' := (h hd x y).map (N.incl (sup_le h₁ h₂))
    rwa [N.incl_trans, N.incl_trans] at h'

end SemilatticeSup

end CStarNet.Grading
