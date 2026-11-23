/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Physics.LocalNet.Locality
public import QuantumSystem.Physics.LocalNet.QuasiLocalAlgebra

/-!
# Graded-local nets and local nets of C⋆-algebras

The net of the Haag–Kastler form, over a causal index set `K`, is assembled here from its
properties, each stated in its own file:

* **isotony** — a net of C⋆-algebras `CStarNet`, the local algebras with their functorial
  embeddings (`QuantumSystem.Physics.LocalNet.Isotony`);
* a **grading** — a parity automorphism of every local algebra, `CStarNet.Grading`
  (`QuantumSystem.Physics.LocalNet.Grading`);
* **locality** — graded locality `CStarNet.Grading.IsGradedLocal` for the causal orthogonality
  relation `⟂` of the index set (`QuantumSystem.Physics.LocalNet.Locality`,
  `QuantumSystem.Physics.LocalNet.Orthogonality`).

A **graded-local net** `GradedLocalNet` is a net with a grading that is graded-local: for causally
orthogonal regions, even elements commute with everything and odd elements anticommute. This is the
net of a system with fermions. A **local net** is a graded-local net whose parity is trivial
(`GradedLocalNet.IsTriviallyGraded`); its locality is commutation (`GradedLocalNet.locality`), and
`GradedLocalNet.ofLocality` builds one from a net and the commutation. Lattice (quantum spin system)
nets are the instance `K = Finset sites` with `⟂ = Disjoint`.

There is one structure, the graded one: a local net is not a second structure but the property
`IsTriviallyGraded` of this one. What uses only the isotony embeddings — faithfulness (`CStarNet.Faithful`),
the quasi-local algebra (`QuantumSystem.Physics.LocalNet.QuasiLocalAlgebra`) — is stated for
`CStarNet` and applies through `GradedLocalNet.toCStarNet`. The symmetries of a graded-local net are
its automorphisms (`QuantumSystem.Physics.LocalNet.Automorphism.Basic`), and its subnets — the fixed
points of an internal symmetry and the even (Bose) subnet — are in
`QuantumSystem.Physics.LocalNet.Subnet`.

Over a directed index set, graded locality passes to the quasi-local algebra: even local observables
of causally orthogonal regions commute with everything
(`GradedLocalNet.ιLocalCStar_commute_of_orthogonal_of_even`), odd ones anticommute
(`GradedLocalNet.ιLocalCStar_mul_eq_neg_of_orthogonal_of_odd`); for a local net this is commutation
(`GradedLocalNet.ιLocalCStar_commute_of_orthogonal`).

## Main definitions

* `GradedLocalNet K` — a graded-local net over the causal index set `K`.
* `GradedLocalNet.IsTriviallyGraded N` — the net `N` is local: its parity is trivial.
* `GradedLocalNet.ofLocality N h`, `GradedLocalNet.ofLocalitySup N h` — the local net of a net of
  C⋆-algebras whose algebras of causally orthogonal regions commute.

## Notation

`𝔄(O)` in the prose is documentation shorthand for the local C⋆-algebra `N.algebra O`; the
convention — and why it is not a Lean notation — is stated in full in
`QuantumSystem.Physics.LocalNet.Isotony`.

`𝔄_loc` is shorthand for the algebra of local observables `N.localObservables` and `𝔄` for the
quasi-local C⋆-algebra `N.quasiLocalCStarAlgebra`.
-/

@[expose] public section

open scoped CausalOrthogonality

/-- A **graded-local net of C⋆-algebras** over a causal index set `K`: a net of C⋆-algebras
    (`CStarNet`: the assignment `O ↦ 𝔄(O)` with functorial isotony embeddings `incl`), with a
    grading (`CStarNet.Grading`: a **parity** automorphism of every local algebra, involutive and
    natural for the isotony embeddings) that is graded-local (`CStarNet.Grading.IsGradedLocal`):
    for causally orthogonal regions, an even element commutes with every element of the other
    region (`locality_even`) and two odd elements anticommute (`locality_odd`).

    This is the locality of a system with fermions: the odd (fermionic) elements of causally
    orthogonal regions anticommute rather than commute. A local net is the case of the trivial
    parity (`GradedLocalNet.IsTriviallyGraded`), where graded locality is commutation; the even parts form a
    local net (`GradedLocalNet.even`).

    The local case is the Haag–Kastler net structure over an abstract index set, *without* the
    injectivity requirement on the isotony embeddings, which is the class `CStarNet.Faithful`. The
    locality fields bind the common region `O` before the orthogonality hypothesis, so they constrain the
    causally orthogonal pairs with a common upper bound (`CausalOrthogonality.OrthogonalHat`). -/
structure GradedLocalNet (K : Type*) [Preorder K] [CausalOrthogonality K]
    extends CStarNet K, CStarNet.Grading toCStarNet, CStarNet.Grading.IsGradedLocal toGrading

namespace GradedLocalNet

section Local

variable {K : Type*} [Preorder K] [CausalOrthogonality K]

/-! ### Local nets -/

/-- A graded-local net is **local** when its parity is trivial: every element is even, and graded
    locality is commutation (`GradedLocalNet.locality`). Over a directed index set, a local net
    together with `CStarNet.Faithful` is the literature's net of C⋆-algebras.

    This is a property of the grading, and stronger than the commutation it implies: where `⟂`
    relates no two regions, every grading is graded-local and the commutation holds for want of
    pairs, whatever the parity. -/
class IsTriviallyGraded (N : GradedLocalNet K) : Prop where
  /-- The parity of a local net is trivial: every element is even. -/
  parity_apply : ∀ {O : K} (x : N.algebra O), N.parity O x = x

variable (N : GradedLocalNet K) [N.IsTriviallyGraded]

/-- The parity of a local net fixes every element. -/
lemma parity_apply {O : K} (x : N.algebra O) : N.parity O x = x :=
  IsTriviallyGraded.parity_apply x

/-- **Locality** (microcausality, Einstein causality) of a local net: observables localised in
    causally orthogonal regions commute inside any common larger region.

    The pairs this statement constrains are the causally orthogonal pairs that admit a common upper
    bound — the derived relation `CausalOrthogonality.OrthogonalHat` (`⊥̂`) rather than `⟂` itself
    (see `CStarNet.Grading.IsGradedLocal`). The two coincide on directed index sets
    (`GradedLocalNet.exists_locality_of_orthogonal`). A net over a genuinely non-directed index set that
    needs locality for `⟂` itself must be taken as a net of von Neumann algebras
    (`QuantumSystem.Physics.LocalNet.VonNeumannNet`), whose ambient `𝓑(H)` states locality
    (`VonNeumannNet.IsLocal`) and graded locality (`VonNeumannNet.Grading.IsGradedLocal`) with no
    upper bound. -/
lemma locality {O₁ O₂ O : K} (h₁ : O₁ ≤ O) (h₂ : O₂ ≤ O) (hd : O₁ ⟂ O₂)
    (x : N.algebra O₁) (y : N.algebra O₂) : Commute (N.incl h₁ x) (N.incl h₂ y) :=
  N.locality_even h₁ h₂ hd x y (N.parity_apply x)

/-- **Every map commutes with the parity of a local net**, the parity being trivial: in particular
the parity condition `β_parity` of an automorphism (`GradedLocalNet.Automorphism`) holds for any `β`. -/
lemma map_parity {O O' : K} (f : N.algebra O → N.algebra O') (x : N.algebra O) :
    f (N.parity O x) = N.parity O' (f x) := by
  rw [N.parity_apply, N.parity_apply]

/-- **Locality is locality for the derived relation `⊥̂`**: a causally orthogonal pair admitting a
    common upper bound commutes inside one. These are the only pairs `GradedLocalNet.locality`
    constrains (`CStarNet.Grading.isGradedLocal_iff_orthogonalHat`): for a causally orthogonal
    pair with *no* common upper bound it says nothing, and cannot, since the commutation has
    nowhere to be stated. -/
lemma exists_locality_of_orthogonalHat {O₁ O₂ : K}
    (h : CausalOrthogonality.OrthogonalHat O₁ O₂) :
    ∃ (O : K) (h₁ : O₁ ≤ O) (h₂ : O₂ ≤ O),
      ∀ (x : N.algebra O₁) (y : N.algebra O₂), Commute (N.incl h₁ x) (N.incl h₂ y) :=
  let ⟨O, h₁, h₂, hc⟩ := N.toIsGradedLocal.exists_commute_of_orthogonalHat h
  ⟨O, h₁, h₂, fun x y => hc x y (N.parity_apply x)⟩

/-- **On a directed index set locality is locality for `⟂` itself**: directedness supplies the
    common upper bound, so every causally orthogonal pair commutes inside some region. On such an
    index set the quasi-local algebra provides the ambient algebra in which the commutation is
    stated for all pairs at once (`GradedLocalNet.ιLocal_commute_of_orthogonal`). -/
lemma exists_locality_of_orthogonal [IsDirectedOrder K] {O₁ O₂ : K} (h : O₁ ⟂ O₂) :
    ∃ (O : K) (h₁ : O₁ ≤ O) (h₂ : O₂ ≤ O),
      ∀ (x : N.algebra O₁) (y : N.algebra O₂), Commute (N.incl h₁ x) (N.incl h₂ y) :=
  N.exists_locality_of_orthogonalHat (CausalOrthogonality.orthogonalHat_iff.2 h)

/-- **The local net of a net of C⋆-algebras whose algebras of causally orthogonal regions commute**
    inside any common larger region. The parity is the identity, every element is even, and graded
    locality is the given commutation (`CStarNet.Grading.isGradedLocal_trivial_iff`). -/
def ofLocality (N : CStarNet K)
    (locality : ∀ ⦃O₁ O₂ O : K⦄ (h₁ : O₁ ≤ O) (h₂ : O₂ ≤ O), O₁ ⟂ O₂ →
      ∀ (x : N.algebra O₁) (y : N.algebra O₂), Commute (N.incl h₁ x) (N.incl h₂ y)) :
    GradedLocalNet K where
  toCStarNet := N
  toGrading := CStarNet.Grading.trivial N
  toIsGradedLocal := CStarNet.Grading.isGradedLocal_trivial_iff.mpr locality

/-- The net built from commutation is local. -/
instance instIsTriviallyGradedOfLocality (N : CStarNet K)
    (locality : ∀ ⦃O₁ O₂ O : K⦄ (h₁ : O₁ ≤ O) (h₂ : O₂ ≤ O), O₁ ⟂ O₂ →
      ∀ (x : N.algebra O₁) (y : N.algebra O₂), Commute (N.incl h₁ x) (N.incl h₂ y)) :
    (ofLocality N locality).IsTriviallyGraded where
  parity_apply _ := rfl

end Local

section SemilatticeSup

variable {K : Type*} [SemilatticeSup K] [CausalOrthogonality K]

/-- **The local net of a net of C⋆-algebras over a join-semilattice of regions**, taking locality
    only inside the canonical join region `O₁ ⊔ O₂`: commutation there is equivalent to the general
    locality (`CStarNet.Grading.isGradedLocal_iff_sup`). For lattice nets
    (`K = Finset sites`) the join is the union of regions. -/
def ofLocalitySup (N : CStarNet K)
    (locality_sup : ∀ ⦃O₁ O₂ : K⦄, O₁ ⟂ O₂ → ∀ (x : N.algebra O₁) (y : N.algebra O₂),
      Commute (N.incl le_sup_left x) (N.incl le_sup_right y)) :
    GradedLocalNet K where
  toCStarNet := N
  toGrading := CStarNet.Grading.trivial N
  toIsGradedLocal := CStarNet.Grading.isGradedLocal_trivial_of_sup locality_sup

/-- The net built from commutation inside the joins is local. -/
instance instIsTriviallyGradedOfLocalitySup (N : CStarNet K)
    (locality_sup : ∀ ⦃O₁ O₂ : K⦄, O₁ ⟂ O₂ → ∀ (x : N.algebra O₁) (y : N.algebra O₂),
      Commute (N.incl le_sup_left x) (N.incl le_sup_right y)) :
    (ofLocalitySup N locality_sup).IsTriviallyGraded where
  parity_apply _ := rfl

end SemilatticeSup

/-! ### Locality in the quasi-local algebra

Over a directed index set every pair of regions has a common upper bound, so graded locality holds
for all causally orthogonal pairs at once inside the algebra of local observables and the
quasi-local C⋆-algebra.
-/

section QuasiLocal

variable {K : Type*} [Preorder K] [CausalOrthogonality K] [IsDirectedOrder K] [Nonempty K]
variable (N : GradedLocalNet K)

/-- **Graded locality in the algebra of local observables**, even elements: an even observable
    localised in a region commutes inside `𝔄_loc` with every observable localised in a causally
    orthogonal region. -/
lemma ιLocal_commute_of_orthogonal_of_even {O₁ O₂ : K} (hd : O₁ ⟂ O₂)
    (X : N.algebra O₁) (Y : N.algebra O₂) (hX : N.parity O₁ X = X) :
    Commute (N.ιLocal O₁ X) (N.ιLocal O₂ Y) := by
  obtain ⟨O, h₁, h₂⟩ := directed_of (· ≤ ·) O₁ O₂
  rw [← N.ιLocal_incl h₁ X, ← N.ιLocal_incl h₂ Y]
  exact (N.locality_even h₁ h₂ hd X Y hX).map (N.ιLocal O)

/-- **Graded locality in the algebra of local observables**, odd elements: odd observables
    localised in causally orthogonal regions anticommute inside `𝔄_loc`. -/
lemma ιLocal_mul_eq_neg_of_orthogonal_of_odd {O₁ O₂ : K} (hd : O₁ ⟂ O₂)
    (X : N.algebra O₁) (Y : N.algebra O₂) (hX : N.parity O₁ X = -X) (hY : N.parity O₂ Y = -Y) :
    N.ιLocal O₁ X * N.ιLocal O₂ Y = -(N.ιLocal O₂ Y * N.ιLocal O₁ X) := by
  obtain ⟨O, h₁, h₂⟩ := directed_of (· ≤ ·) O₁ O₂
  rw [← N.ιLocal_incl h₁ X, ← N.ιLocal_incl h₂ Y, ← map_mul, ← map_mul, ← map_neg,
    N.locality_odd h₁ h₂ hd X Y hX hY]

/-- **Locality in the algebra of local observables**: observables localised in causally orthogonal
    regions commute inside `𝔄_loc`: graded locality for the trivial parity of a local net. -/
lemma ιLocal_commute_of_orthogonal [N.IsTriviallyGraded] {O₁ O₂ : K} (hd : O₁ ⟂ O₂)
    (X : N.algebra O₁) (Y : N.algebra O₂) :
    Commute (N.ιLocal O₁ X) (N.ιLocal O₂ Y) :=
  N.ιLocal_commute_of_orthogonal_of_even hd X Y (N.parity_apply X)

variable [N.Faithful]

/-- **Graded locality in the quasi-local C⋆-algebra**, even elements: an even observable
    localised in a region commutes inside `𝔄` with every observable localised in a causally
    orthogonal region. -/
lemma ιLocalCStar_commute_of_orthogonal_of_even {O₁ O₂ : K} (hd : O₁ ⟂ O₂)
    (X : N.algebra O₁) (Y : N.algebra O₂) (hX : N.parity O₁ X = X) :
    Commute (N.ιLocalCStar O₁ X) (N.ιLocalCStar O₂ Y) :=
  (N.ιLocal_commute_of_orthogonal_of_even hd X Y hX).map UniformSpace.Completion.coeRingHom

/-- **Graded locality in the quasi-local C⋆-algebra**, odd elements: odd observables localised in
    causally orthogonal regions anticommute inside `𝔄`. -/
lemma ιLocalCStar_mul_eq_neg_of_orthogonal_of_odd {O₁ O₂ : K} (hd : O₁ ⟂ O₂)
    (X : N.algebra O₁) (Y : N.algebra O₂) (hX : N.parity O₁ X = -X) (hY : N.parity O₂ Y = -Y) :
    N.ιLocalCStar O₁ X * N.ιLocalCStar O₂ Y = -(N.ιLocalCStar O₂ Y * N.ιLocalCStar O₁ X) := by
  have h := congrArg (UniformSpace.Completion.coeRingHom (α := N.localObservables))
    (N.ιLocal_mul_eq_neg_of_orthogonal_of_odd hd X Y hX hY)
  rw [map_mul, map_neg, map_mul] at h
  exact h

/-- **Locality in the quasi-local C⋆-algebra**: observables localised in causally orthogonal
    regions commute inside `𝔄`: graded locality for the trivial parity of a local net. -/
lemma ιLocalCStar_commute_of_orthogonal [N.IsTriviallyGraded] {O₁ O₂ : K} (hd : O₁ ⟂ O₂)
    (X : N.algebra O₁) (Y : N.algebra O₂) :
    Commute (N.ιLocalCStar O₁ X) (N.ιLocalCStar O₂ Y) :=
  N.ιLocalCStar_commute_of_orthogonal_of_even hd X Y (N.parity_apply X)

end QuasiLocal

end GradedLocalNet
