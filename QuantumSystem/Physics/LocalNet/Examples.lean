/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.ForMathlib.Algebra.Order.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Complex.Circle
public import QuantumSystem.Analysis.CStarAlgebra.DynamicalSystem
public import QuantumSystem.Physics.LocalNet.DHRCriterion
public import QuantumSystem.Physics.LocalNet.Graded
public import QuantumSystem.Physics.LocalNet.HalfChainSplit
public import QuantumSystem.Physics.LocalNet.Nuclear
public import QuantumSystem.Physics.LocalNet.TensorNet

/-!
# Witnesses for the local-net interfaces

Every class and structure the local-net development introduces is inhabited here, by explicit
construction. Without such witnesses the theorems of `QuantumSystem.Physics.LocalNet.Basic`,
`QuantumSystem.Physics.LocalNet.QuasiLocalAlgebra` and
`QuantumSystem.Physics.LocalNet.SplitProperty` would be unfalsifiable: nobody could apply them, and
no construction could contradict them. In particular the split property is a `Prop`-valued
hypothesis which the development proves for no net in general (it fails for `diagonalNet` below), so
a model with it must be exhibited before the hypothesis can be believed consistent.

The witnesses are deliberately the smallest ones that are not degenerate in the way that matters.

* **A separating proper containment.** `ProperContainment.integerChain` is the 1-neighbourhood
  thickening on the integer chain, `Λ₁ ⋐ Λ₂` iff `nbhd Λ₁ ⊊ Λ₂`. What makes it *separating* is that
  `nbhd` enlarges in both directions, so `Λ₂` contains both neighbours of every site of `Λ₁`
  (`ProperContainment.add_mem_of_properlyContained`), the collar `Λ₂ \ nbhd Λ₁` touches `Λ₁` from
  neither side (`ProperContainment.add_notMem_collar`), and *touching* pairs are excluded
  (`ProperContainment.not_properlyContained_touching`). Mere enlargement would not do this — see
  the docstring of `ProperContainment.ofThicken`, and `ProperContainment.ofLT` for the degenerate
  model the class axioms admit. `ProperContainment.properlyContained_singleton` exhibits an actual pair, so
  `⋐` is not empty and the split property below is not vacuously true.
* **A separating proper containment on infinite regions.** `ProperContainment.halfChain` is the
  metric model `ProperContainment.ofCThickening ℤ 1` on `Set ℤ`. It relates the gapped half-chain
  pair `(-∞, 0] ⋐ (-∞, 2]` (`ProperContainment.Iic_properlyContained_Iic_two`) and rejects the
  touching pair `(-∞, 0] ⋐ (-∞, 1]` (`ProperContainment.not_Iic_properlyContained_Iic_one`).
* **A faithful local net.** `LocalNet.Examples.constNet A` assigns a commutative C⋆-algebra `A` to
  every region of the integer chain, with identity isotony embeddings, built through the
  join-semilattice smart constructor `LocalNet.mk'`; its `Faithful` instance is immediate.
  `LocalNet.Examples.trivialNet` is the case `A = ℂ`, and its quasi-local C⋆-algebra
  is nuclear (`LocalNet.Examples.isNuclear_quasiLocalCStarAlgebra_trivialNet`).
* **A continuous symmetry that is not discrete.** A C⋆-dynamical system `ψ` on `A` acts on the
  quasi-local C⋆-algebra of `constNet A` as a C⋆-dynamical system
  (`LocalNet.Examples.constNetDynamicalSystem`), so the continuity hypothesis of
  `GradedLocalNet.Covariance.quasiLocalCStarDynamicalSystem` is satisfied beyond discrete groups:
  `LocalNet.Examples.circleRotation` is the action of the rotations of the circle on the constant
  net at `C(Circle, ℂ)`, and it is not trivial (`LocalNet.Examples.circleRotation_neg_one_ne`).
  The constant net has identity embeddings; on a net whose embeddings are not identities,
  `LocalNet.Examples.spinChainPhaseRotation` is the circle acting on the spin chain on `ℤ` (the
  tensor product net `LocalNet.tensorNet ℤ M₂(ℂ)`) by the phase rotation `x ↦ diag(1, z) x diag(1, z)⋆`
  of every spin (`LocalNet.onSiteDynamicalSystem`), and it reverses the spin `σ_x` at a site
  (`LocalNet.Examples.spinChainPhaseRotation_neg_one_pauliXAtZero`), so it is not trivial
  (`LocalNet.Examples.spinChainPhaseRotation_neg_one_ne`). These covariances do not move the regions;
  `LocalNet.Examples.shiftCovariance` does.
* **A graded-local net that is not local.** `LocalNet.Examples.pauliMajoranaNet` is the net of two
  Majorana modes `σ_x`, `σ_y` in `M₂(ℂ)` with the parity `a ↦ σ_z a σ_z`
  (`LocalNet.Examples.majoranaNet`, a net of subalgebras): its two modes are odd and do not commute
  (`LocalNet.Examples.not_commute_pauliMajoranaNet`), so the graded locality of `GradedLocalNet` is
  inhabited beyond commutation and the net is not local (`LocalNet.Examples.not_locality_pauliMajoranaNet`).
  Its regions are directed and the net is faithful, so it has a quasi-local algebra, where the
  graded API of `QuantumSystem.Physics.LocalNet.QuasiLocalAlgebra` and
  `QuantumSystem.Physics.LocalNet.Graded` is not vacuous: the two modes anticommute
  (`LocalNet.Examples.ιLocalCStar_pauliMajoranaLeft_mul_pauliMajoranaRight`) without commuting
  (`LocalNet.Examples.not_commute_ιLocalCStar_pauliMajorana`), the quasi-local parity moves `σ_x`
  (`LocalNet.Examples.quasiLocalParity_ιLocalCStar_pauliMajoranaLeft_ne`), and the even part of the
  quasi-local algebra contains `σ_z` but not `σ_x`
  (`LocalNet.Examples.ιLocalCStar_pauliMajoranaZ_mem_quasiLocalEvenPart`,
  `LocalNet.Examples.ιLocalCStar_pauliMajoranaLeft_notMem_quasiLocalEvenPart`).
* **A net of von Neumann algebras with the split property.**
  `LocalNet.Examples.scalarNet` is the constant net at `𝓑(ℂ)`, and
  `LocalNet.Examples.scalarNet_splitProperty` proves `VonNeumannNet.SplitProperty` for it. Locality
  holds because bounded operators on `ℂ` commute.
* **The split property at the representation level, in two representations.**
  `LocalNet.Examples.trivialNet_splitProperty` proves `LocalNet.SplitProperty` for `trivialNet` in
  the *zero* representation on `ℂ`, and `LocalNet.Examples.unitalRep_splitProperty` in the *unital*
  representation `LocalNet.Examples.unitalRep`, which sends `1` to `1`
  (`LocalNet.Examples.unitalRep_π_one`). The second is there because the first alone would leave
  the representation-level interface inhabited only by a degenerate `π`.
* **A refuter.** `LocalNet.Examples.diagonalNet` is the constant net at the diagonal algebra
  `ℂ ⊕ ℂ = L∞(Fin 2, count)` on `L²(Fin 2, count)`, and
  `LocalNet.Examples.not_splitProperty_diagonalNet` proves it does
  *not* have `VonNeumannNet.SplitProperty` under the integer-chain `⋐`. It rests on
  `VonNeumannAlgebra.not_isSplitInclusion_multiplicationAlgebra_count`, which refutes a single inclusion; the
  net-level refuter is what keeps the property itself from being a theorem about all nets.
  `LocalNet.Examples.not_splitProperty_diagonalNet_extend` does the same on infinite regions, for
  the extension `diagonalNet.extend`, and `LocalNet.Examples.scalarNet_extend_splitProperty` is
  the one-dimensional positive witness there.
* **The gap-free half-chain pair.** `LocalNet.Examples.not_isSplitPair_diagonalNet_extend`
  refutes `VonNeumannNet.IsSplitPair` at `(-∞, 0]`, `[1, ∞)` for the diagonal net, and
  `LocalNet.Examples.scalarNet_extend_isSplitPair` inhabits it. At the state level,
  `LocalNet.Examples.evalState_hasHalfChainSplit` inhabits `LocalNet.HasHalfChainSplit` with the
  evaluation state of the trivial net, a multiplicative state whose GNS algebras are scalar, for
  every order on the quasi-local algebra compatible with its star structure; at the canonical
  spectral order it holds outright (`LocalNet.Examples.evalState_hasHalfChainSplit_spectralOrder`).
* **Localisation in the regions of the net.** `LocalizationRegions.ofOrthogonal` needs a causal
  index set with no self-orthogonal region, which the lattice index set `Finset α` is not (its
  empty region is orthogonal to everything). `LocalNet.Examples.nonemptyFinsetOrthogonality` puts
  disjointness on the *nonempty* finite sets of sites of an infinite `α`; it is a causal index set
  (`LocalNet.Examples.nonemptyFinset_causalIndexSet`) with no self-orthogonal region
  (`LocalNet.Examples.not_orthogonal_self_nonemptyFinset`), so
  `LocalNet.Examples.nonemptyFinsetLocalizationRegions` applies `ofOrthogonal` to it.

What is deliberately *not* built here is a spin-system net with genuine tensor-product local
algebras — the physically interesting lattice model the module docs of
`QuantumSystem.Physics.LocalNet.Basic` and `QuantumSystem.Physics.LocalNet.Covariance` describe.
That is a construction in its own right, not a witness; these witnesses establish consistency and
applicability of the interfaces, nothing more.

**The residual degeneracy, stated so it is not mistaken for evidence.** Every Hilbert space
appearing below is `ℂ`, and on `ℂ` the split property is *automatic*: the only von Neumann algebra
there is `𝓑(ℂ)` (`VonNeumannAlgebra.eq_boundedLinearOperators_complex`), so every net of von
Neumann algebras on `ℂ` splits (`VonNeumannNet.splitProperty_of_complex`), and both
representation-level witnesses below are instances of that one theorem. So the degeneracy is
`dim H = 1` — *not* the zero representation, which is why exchanging it for a unital one changes
nothing mathematically. A reflexive proper containment is rejected precisely because it would
force every local algebra to be type I. These witnesses show the interfaces are inhabited and applicable;
they are **not** evidence about nets whose local algebras are type III₁, and no argument should
treat them as such. The degeneracy is also forced rather than chosen at the C⋆ level: over
`Finset ℤ` with `⟂ = Disjoint`, any two disjoint regions lie under their union, so locality makes
every *constant* net commutative — a noncommutative witness needs the tensor-product net descoped
above.

**Finite versus infinite regions.** Even a genuine spin net would make the split property on
`Finset ℤ` say nothing: every finite-region algebra is then a finite-dimensional factor, and every
inclusion between such factors splits. The property has content only on infinite regions, which
`QuantumSystem.Physics.LocalNet.InfiniteRegion` makes expressible and the `halfChain` witnesses
above inhabit. A non-trivial positive model on infinite regions still needs the spin net descoped
above.
-/

@[expose] public section

open scoped CausalOrthogonality ProperContainment VonNeumannAlgebra

namespace ProperContainment

/-! ### A separating proper containment on the integer chain -/

/-- The **1-neighbourhood** of a finite set of integer sites: the region together with its two
    neighbouring layers. This is the thickening operator of a nearest-neighbour spin chain. -/
def nbhd (Λ : Finset ℤ) : Finset ℤ := Λ ∪ Λ.image (· - 1) ∪ Λ.image (· + 1)

/-- A region is contained in its 1-neighbourhood. -/
lemma subset_nbhd (Λ : Finset ℤ) : Λ ⊆ nbhd Λ :=
  fun _ hx => Finset.mem_union_left _ (Finset.mem_union_left _ hx)

/-- The 1-neighbourhood is monotone. -/
lemma monotone_nbhd : Monotone nbhd := fun _ _ h =>
  Finset.union_subset_union (Finset.union_subset_union h (Finset.image_subset_image h))
    (Finset.image_subset_image h)

/-- **The 1-neighbourhood absorbs both neighbours of every site of the region.** This — and not
    mere enlargement `subset_nbhd` — is what makes the induced proper containment
    *separating*: the collar `Λ₂ \ nbhd Λ₁` avoids `nbhd Λ₁`, hence contains no site adjacent to
    `Λ₁` on either side. A one-sided thickening satisfies the hypotheses of `ofThicken` just as
    well and does not have this property. -/
lemma add_mem_nbhd_of_mem {Λ : Finset ℤ} {x : ℤ} (hx : x ∈ Λ) (d : ℤ) (hd : d = 1 ∨ d = -1) :
    x + d ∈ nbhd Λ := by
  rcases hd with rfl | rfl
  · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨x, hx, rfl⟩)
  · exact Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image.2 ⟨x, hx, by omega⟩))

/-- **Proper containment on the integer chain**: `Λ₁ ⋐ Λ₂` iff the 1-neighbourhood of `Λ₁` is a
    strict subset of `Λ₂`. The buffer layer `nbhd Λ₁ \ Λ₁` separates `Λ₁` from the collar on both
    sides (`add_mem_of_properlyContained`, `add_notMem_collar`), so touching pairs — which the
    literature excludes, since local algebras of touching regions are not statistically
    independent — do not satisfy this relation (`not_properlyContained_touching`).

    Deliberately a `def` rather than a global `instance`: this file is re-exported by the aggregate
    root, so a global instance would silently resolve every downstream `⋐` on `Finset ℤ` to the
    nearest-neighbour relation of this one witness. It is activated by `attribute [local instance]`
    where this file needs it; a model that wants it elsewhere says so, either the same way or by
    rebuilding it from the public `nbhd`, `subset_nbhd` and `monotone_nbhd`. -/
@[reducible] noncomputable def integerChain : ProperContainment (Finset ℤ) :=
  ProperContainment.ofThicken (fun _ _ h => h) nbhd subset_nbhd monotone_nbhd

attribute [local instance] integerChain

/-- **`⋐` is inhabited on the integer chain**: the single site `{0}`, whose 1-neighbourhood is
    `{-1, 0, 1}`, is properly contained in `{-2, -1, 0, 1, 2}`. Recorded so that the split property
    over this index set is not vacuously true. -/
lemma properlyContained_singleton : ({0} : Finset ℤ) ⋐ ({-2, -1, 0, 1, 2} : Finset ℤ) := by
  change nbhd {0} ⊂ ({-2, -1, 0, 1, 2} : Finset ℤ)
  decide

/-- **A properly containing region contains both neighbours of every inner site.** Under
    `Λ₁ ⋐ Λ₂` the whole 1-neighbourhood `nbhd Λ₁` lies in `Λ₂`, so `Λ₂` surrounds `Λ₁` with a buffer
    layer on both sides. This is the sense in which the integer-chain `⋐` is *separating*. -/
lemma add_mem_of_properlyContained {Λ₁ Λ₂ : Finset ℤ} (h : Λ₁ ⋐ Λ₂) {x : ℤ} (hx : x ∈ Λ₁)
    (d : ℤ) (hd : d = 1 ∨ d = -1) : x + d ∈ Λ₂ :=
  (show nbhd Λ₁ ⊂ Λ₂ from h).subset (add_mem_nbhd_of_mem hx d hd)

/-- **The collar touches the inner region from neither side**: no site of `Λ₂ \ nbhd Λ₁` is a
    neighbour of a site of `Λ₁`. -/
lemma add_notMem_collar {Λ₁ Λ₂ : Finset ℤ} {x : ℤ} (hx : x ∈ Λ₁) (d : ℤ) (hd : d = 1 ∨ d = -1) :
    x + d ∉ Λ₂ \ nbhd Λ₁ :=
  fun hmem => (Finset.mem_sdiff.1 hmem).2 (add_mem_nbhd_of_mem hx d hd)

/-- **Touching pairs are not properly contained on the integer chain**: `{0} ⋐ {0, 1}` fails,
    because `{0, 1}` does not contain the neighbour `-1` of `0`. Under the degenerate model
    `ProperContainment.ofLT` the same pair *is* properly contained. -/
lemma not_properlyContained_touching : ¬ (({0} : Finset ℤ) ⋐ ({0, 1} : Finset ℤ)) := fun h => by
  have := add_mem_of_properlyContained h (Finset.mem_singleton_self 0) (-1) (Or.inr rfl)
  simp at this

/-! ### A separating proper containment on infinite regions of the integer chain -/

/-- **The closed 1-thickening of the left half-chain `(-∞, 0]` is `(-∞, 1]`.** -/
lemma cthickening_one_Iic : Metric.cthickening 1 (Set.Iic (0 : ℤ)) = Set.Iic 1 := by
  refine subset_antisymm (fun x hx => ?_) fun x hx => ?_
  · obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 <|
      Metric.cthickening_subset_iUnion_closedBall_of_lt (Set.Iic (0 : ℤ))
        (δ := 1) (δ' := 3 / 2) (by norm_num) (by norm_num) hx
    rw [Metric.mem_closedBall, Int.dist_eq] at hxy
    refine Set.mem_Iic.2 (not_lt.1 fun hlt => ?_)
    have h2 : (2 : ℤ) ≤ |x - y| := by rw [abs_of_nonneg (by grind)]; grind
    have : (2 : ℝ) ≤ ((|x - y| : ℤ) : ℝ) := by exact_mod_cast h2
    push_cast at this
    linarith
  · rcases le_or_gt x 0 with h | h
    · exact Metric.self_subset_cthickening _ h
    · obtain rfl : x = 1 := le_antisymm hx h
      exact Metric.mem_cthickening_of_dist_le 1 0 1 _ (Set.mem_Iic.2 le_rfl)
        (by simp)

/-- **Proper containment on infinite regions of the integer chain**: the metric model
    `ofCThickening ℤ 1`, whose buffer is the same nearest-neighbour layer as `integerChain`'s.
    A `def` activated locally, for the same reason as `integerChain`. -/
@[reducible] noncomputable def halfChain : ProperContainment (Set ℤ) :=
  ofCThickening ℤ ⟨1, one_pos⟩

attribute [local instance] halfChain

/-- **`⋐` relates a genuine pair of infinite regions**: under the metric proper containment
    `halfChain = ofCThickening ℤ 1`, the left half-chain `(-∞, 0]` is properly contained in `(-∞, 2]`, whose
    extra layer `{1}` is the buffer and `{2}` the collar. This is the gapped half-chain pair. -/
lemma Iic_properlyContained_Iic_two : Set.Iic (0 : ℤ) ⋐ Set.Iic 2 := by
  change Metric.cthickening 1 (Set.Iic (0 : ℤ)) < Set.Iic 2
  rw [cthickening_one_Iic]
  exact Set.Iic_ssubset_Iic.2 (by norm_num)

/-- **Touching half-chains are not properly contained**: `(-∞, 0] ⋐ (-∞, 1]` fails, because the
    1-thickening of `(-∞, 0]` already fills `(-∞, 1]`. -/
lemma not_Iic_properlyContained_Iic_one : ¬ Set.Iic (0 : ℤ) ⋐ Set.Iic 1 := by
  change ¬ Metric.cthickening 1 (Set.Iic (0 : ℤ)) < Set.Iic 1
  rw [cthickening_one_Iic]
  exact lt_irrefl _

end ProperContainment

namespace LocalNet.Examples

attribute [local instance] ProperContainment.integerChain ProperContainment.halfChain

/-! ### A faithful local net -/

/-- The **constant local net** at a commutative C⋆-algebra `A` over the integer chain: every region
    carries `A`, and every isotony embedding is the identity. Locality holds because `A` is
    commutative, and is supplied only for the join region `Λ₁ ∪ Λ₂` — the smart constructor
    `LocalNet.mk'` pushes it forward to every common superregion. -/
noncomputable def constNet (A : Type*) [CommCStarAlgebra A] : LocalNet (Finset ℤ) :=
  LocalNet.mk' (fun _ : Finset ℤ => A) (fun _ => StarAlgHom.id ℂ A) (fun _ => rfl)
    (fun _ _ _ => rfl) (fun _ x y => mul_comm x y)

/-- A constant net is faithful: its isotony embeddings are identities. -/
instance (A : Type*) [CommCStarAlgebra A] : (constNet A).Faithful where
  incl_injective _ := fun _ _ h => h

/-- The **trivial local net** over the integer chain: the constant net at `ℂ`. -/
noncomputable def trivialNet : LocalNet (Finset ℤ) :=
  constNet ℂ

/-- The trivial net is faithful: its isotony embeddings are identities. -/
instance : trivialNet.Faithful :=
  inferInstanceAs (constNet ℂ).Faithful

/-- The quasi-local C⋆-algebra of the trivial net is nuclear, its local algebras `ℂ` being so. -/
theorem isNuclear_quasiLocalCStarAlgebra_trivialNet.{v, w} :
    CStarAlgebra.IsNuclear.{v, w} trivialNet.quasiLocalCStarAlgebra :=
  haveI : ∀ O, CStarAlgebra.IsNuclear.{v, w} (trivialNet.algebra O) := fun _ =>
    inferInstanceAs (CStarAlgebra.IsNuclear.{v, w} ℂ)
  trivialNet.isNuclear_quasiLocalCStarAlgebra

/-! ### A covariance moving the regions -/

/-- **The unit translation of the integer chain**, as a covariance of the trivial net: the site
    permutation `x ↦ x + 1` induces the region automorphism `Λ ↦ Λ + 1`, and every local algebra
    being `ℂ` the covariance `*`-isomorphisms are identities.

    This is the witness that makes the covariance API testable. `GradedLocalNet.Covariance.id` inhabits
    the structure, but at the identity region map every naturality square of `Covariance` closes by
    `rfl` and `Covariance.sitePerm`, `Covariance.exists_sitePerm` and
    `Covariance.exists_eq_ofSitePerm` all speak about the trivial permutation. Here the region map
    genuinely moves (`σ_shiftCovariance`), so those statements have content. -/
noncomputable def shiftCovariance : trivialNet.Covariance :=
  GradedLocalNet.Covariance.ofSitePerm' trivialNet (Equiv.addRight (1 : ℤ))
    (fun _ => StarAlgEquiv.refl ℂ _) (fun _ _ => rfl)

/-- **The unit translation moves regions**: it carries the site `0` to the site `1`. So
    `shiftCovariance` is not the identity covariance, and the site permutation recovered from it by
    `GradedLocalNet.Covariance.exists_sitePerm` is not the identity permutation. -/
@[simp] lemma σ_shiftCovariance : shiftCovariance.σ ({0} : Finset ℤ) = {1} := rfl

/-! ### A continuous symmetry that is not discrete -/

section ConstNet

variable {A : Type*} [CommCStarAlgebra A]

/-- A ⋆-automorphism `e` of `A` as a covariance of the constant net at `A`: the regions are not
    moved, and `e` acts on every local algebra. -/
noncomputable def constCovariance (e : A ≃⋆ₐ[ℂ] A) : (constNet A).Covariance :=
  GradedLocalNet.Covariance.mk' (constNet A) (OrderIso.refl _) (fun _ _ => Iff.rfl) (fun _ => e)
    fun _ _ => rfl

variable (A) in
/-- The ⋆-automorphisms of `A` act on the constant net at `A` by covariances. -/
noncomputable def constCovarianceHom : (A ≃⋆ₐ[ℂ] A) →* (constNet A).Covariance where
  toFun := constCovariance
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The action of the ⋆-automorphisms of `A` on the quasi-local C⋆-algebra of the constant net is
    continuous from the point-norm topology of `A`: on a local observable it is `e ↦ ι_O (e x)`
    (`GradedLocalNet.Covariance.continuous_quasiLocalCStarCovarianceHom_comp_iff`). -/
theorem continuous_quasiLocalCStarCovarianceHom_constCovariance :
    Continuous fun e : A ≃⋆ₐ[ℂ] A =>
      GradedLocalNet.Covariance.quasiLocalCStarCovarianceHom (constCovariance e) :=
  GradedLocalNet.Covariance.continuous_quasiLocalCStarCovarianceHom_comp_iff.mpr fun O x =>
    ((constNet A).isometry_ιLocalCStar O).continuous.comp (continuous_eval_const x)

variable {G : Type*} [Monoid G] [TopologicalSpace G]

/-- **A C⋆-dynamical system on a commutative C⋆-algebra `A` is a continuous symmetry of the constant
    net at `A`**: `G` acts on the quasi-local C⋆-algebra as a C⋆-dynamical system
    (`GradedLocalNet.Covariance.quasiLocalCStarDynamicalSystem`), whatever the topology of `G`. This is
    the witness that the continuity hypothesis of `quasiLocalCStarDynamicalSystem` is satisfied by
    groups that are not discrete, such as the rotations of the circle (`circleRotation`). -/
noncomputable def constNetDynamicalSystem (ψ : G →ₜ* (A ≃⋆ₐ[ℂ] A)) :
    G →ₜ* ((constNet A).quasiLocalCStarAlgebra ≃⋆ₐ[ℂ] (constNet A).quasiLocalCStarAlgebra) :=
  GradedLocalNet.Covariance.quasiLocalCStarDynamicalSystem ((constCovarianceHom A).comp ψ.toMonoidHom)
    (continuous_quasiLocalCStarCovarianceHom_constCovariance.comp ψ.continuous)

/-- On a local observable the dynamical system of the constant net acts by `ψ`. -/
@[simp] lemma constNetDynamicalSystem_ιLocalCStar (ψ : G →ₜ* (A ≃⋆ₐ[ℂ] A)) (g : G) (O : Finset ℤ)
    (x : A) :
    constNetDynamicalSystem ψ g ((constNet A).ιLocalCStar O x) =
      (constNet A).ιLocalCStar O (ψ g x) :=
  GradedLocalNet.Covariance.quasiLocalCStarCovarianceEquiv_ιLocalCStar (constCovariance (ψ g)) O x

end ConstNet

/-- **The rotations of the circle**, acting on the constant net at `C(Circle, ℂ)`: a C⋆-dynamical
    system on its quasi-local C⋆-algebra whose group, the circle, is not discrete. -/
noncomputable def circleRotation :
    Circle →ₜ* ((constNet C(Circle, ℂ)).quasiLocalCStarAlgebra ≃⋆ₐ[ℂ]
      (constNet C(Circle, ℂ)).quasiLocalCStarAlgebra) :=
  constNetDynamicalSystem (ContinuousMap.smulStarAlgAut Circle Circle)

/-- **The rotations act non-trivially**: the rotation by `-1` moves the local observable `z ↦ z`,
    the inclusion of the circle in `ℂ`. So `circleRotation` is not the trivial action. -/
theorem circleRotation_neg_one_ne (O : Finset ℤ) :
    circleRotation (-1) ((constNet C(Circle, ℂ)).ιLocalCStar O ⟨(↑), continuous_subtype_val⟩) ≠
      (constNet C(Circle, ℂ)).ιLocalCStar O ⟨(↑), continuous_subtype_val⟩ := fun h => by
  rw [circleRotation, constNetDynamicalSystem_ιLocalCStar] at h
  have h1 : ContinuousMap.smulStarAlgAut Circle Circle (-1) ⟨(↑), continuous_subtype_val⟩ =
      (⟨(↑), continuous_subtype_val⟩ : C(Circle, ℂ)) :=
    (constNet C(Circle, ℂ)).ιLocalCStar_injective O h
  have h2 : (((-1 : Circle)⁻¹ * 1 : Circle) : ℂ) = ((1 : Circle) : ℂ) := DFunLike.congr_fun h1 1
  norm_num [Circle.coe_neg, Circle.coe_inv] at h2

/-! ### A net of von Neumann algebras with the split property -/

/-- The **constant net at `𝓑(ℂ)`** over the integer chain. Isotony is trivial, and locality holds
    because bounded operators on `ℂ` commute (`VonNeumannAlgebra.mul_comm_complex`), so every
    algebra of the net lies in the commutant of every other. -/
noncomputable def scalarNet : VonNeumannNet (Finset ℤ) ℂ where
  algebra _ := 𝓑(ℂ)
  algebra_mono _ _ _ := le_rfl
  algebra_le_commutant_of_orthogonal _ _ _ := by
    intro x _
    rw [VonNeumannAlgebra.mem_commutant_iff]
    exact fun y _ => VonNeumannAlgebra.mul_comm_complex y x

/-- **The constant net has the split property.** Together with
    `ProperContainment.properlyContained_singleton` this is a non-vacuous model of
    `VonNeumannNet.SplitProperty`. It is an instance of `VonNeumannNet.splitProperty_of_complex`,
    which is also the reason it is no evidence about anything but inhabitation: on `ℂ` every net
    splits. -/
theorem scalarNet_splitProperty : scalarNet.SplitProperty :=
  VonNeumannNet.splitProperty_of_complex scalarNet

/-! ### A net of von Neumann algebras without the split property -/

/-- The **constant net at the diagonal algebra** `ℂ ⊕ ℂ = L∞(Fin 2, count)` on `L²(Fin 2, count)`
    over the integer chain. Isotony is trivial, and locality holds because the diagonal algebra
    is its own commutant (`VonNeumannAlgebra.commutant_multiplicationAlgebra`). -/
noncomputable def diagonalNet :
    VonNeumannNet (Finset ℤ) (MeasureTheory.Lp ℂ 2 (MeasureTheory.Measure.count : MeasureTheory.Measure (Fin 2))) where
  algebra _ := VonNeumannAlgebra.multiplicationAlgebra MeasureTheory.Measure.count
  algebra_mono _ _ _ := le_rfl
  algebra_le_commutant_of_orthogonal _ _ _ := VonNeumannAlgebra.commutant_multiplicationAlgebra.ge

/-- **The split property is not automatic: the diagonal net does not have it.** The genuine pair
    `ProperContainment.properlyContained_singleton` would make the identity inclusion of the
    diagonal algebra split, which `VonNeumannAlgebra.not_isSplitInclusion_multiplicationAlgebra_count`
    refutes. This is the net-level refuter that keeps `VonNeumannNet.SplitProperty`
    distinguishable from a theorem about all nets over this index set. -/
theorem not_splitProperty_diagonalNet : ¬ diagonalNet.SplitProperty := fun hs =>
  VonNeumannAlgebra.not_isSplitInclusion_multiplicationAlgebra_count
    (hs ProperContainment.properlyContained_singleton)

/-! ### The split property on infinite regions -/

/-- **Every extended algebra of the diagonal net is the diagonal algebra**: it contains the algebra
    of the empty finite region and is generated by copies of the diagonal algebra. -/
lemma diagonalNet_extend_algebra (S : Set ℤ) :
    diagonalNet.extend.algebra S =
      VonNeumannAlgebra.multiplicationAlgebra (MeasureTheory.Measure.count : MeasureTheory.Measure (Fin 2)) :=
  le_antisymm
    (VonNeumannAlgebra.generated_le fun x hx => by
      obtain ⟨Λ, -, hx⟩ := VonNeumannNet.mem_finiteLocalOperators.1 hx
      exact hx)
    (diagonalNet.algebra_le_extend_algebra (Λ := ∅) (by simp))

/-- **The infinite-region split property is not automatic either**: the extension of the diagonal
    net to infinite regions of the integer chain fails it under `ProperContainment.halfChain`, at
    the gapped half-chain pair `(-∞, 0] ⋐ (-∞, 2]`, since every extended algebra is the diagonal
    algebra (`diagonalNet_extend_algebra`). -/
theorem not_splitProperty_diagonalNet_extend : ¬ diagonalNet.extend.SplitProperty := fun hs => by
  have h := hs ProperContainment.Iic_properlyContained_Iic_two
  rw [diagonalNet_extend_algebra, diagonalNet_extend_algebra] at h
  exact VonNeumannAlgebra.not_isSplitInclusion_multiplicationAlgebra_count h

/-- **The gap-free half-chain pair does not split for the diagonal net**: `(-∞, 0]` and `[1, ∞)` do
    not form a split pair of `diagonalNet.extend`. The diagonal algebra is its own commutant
    (`VonNeumannAlgebra.commutant_multiplicationAlgebra`), so a split pair would make its identity
    inclusion split. This keeps `VonNeumannNet.IsSplitPair` at this pair from being automatic. -/
lemma not_isSplitPair_diagonalNet_extend :
    ¬ diagonalNet.extend.IsSplitPair (Set.Iic 0) (Set.Ici 1) := fun h => by
  rw [VonNeumannNet.IsSplitPair, diagonalNet_extend_algebra, diagonalNet_extend_algebra,
    VonNeumannAlgebra.commutant_multiplicationAlgebra] at h
  exact VonNeumannAlgebra.not_isSplitInclusion_multiplicationAlgebra_count h

/-- **The extended constant net at `𝓑(ℂ)` has the infinite-region split property.** Evidence of
    inhabitation only: it is an instance of `VonNeumannNet.splitProperty_of_complex`, and on `ℂ`
    every net splits. A non-trivial positive model needs a spin net, which is not built here. -/
lemma scalarNet_extend_splitProperty : scalarNet.extend.SplitProperty :=
  VonNeumannNet.splitProperty_of_complex _

/-- **Every pair of regions splits for the extended constant net at `𝓑(ℂ)`**, in particular
    the gap-free half-chain pair. Evidence of inhabitation only: on `ℂ` every von Neumann
    algebra, commutants included, is `𝓑(ℂ)`. -/
lemma scalarNet_extend_isSplitPair (S₁ S₂ : Set ℤ) : scalarNet.extend.IsSplitPair S₁ S₂ := by
  rw [VonNeumannNet.IsSplitPair,
    VonNeumannAlgebra.eq_boundedLinearOperators_complex (scalarNet.extend.algebra S₁),
    VonNeumannAlgebra.eq_boundedLinearOperators_complex (scalarNet.extend.algebra S₂)′]
  exact (VonNeumannAlgebra.isTypeIFactor_boundedLinearOperators (H := ℂ)).isSplitInclusion_self

/-! ### The split property at the representation level

Two representations of `trivialNet.quasiLocalCStarAlgebra` on `ℂ`, both exhibiting
`LocalNet.SplitProperty`: the zero one, and — so that the interface is not inhabited by a
degenerate `π` alone — a unital one.
-/

/-- The zero `*`-representation of the quasi-local C⋆-algebra of the trivial net on `ℂ`. The
    representation is degenerate as a `*`-map — it sends `1` to `0` — but that is *not* what makes
    the split property hold below: `𝓡(O)` contains `1` regardless, since a von Neumann algebra is
    unital, and on `ℂ` it is forced to be `𝓑(ℂ)` for every representation whatsoever
    (`VonNeumannNet.splitProperty_of_complex`). The unital representation `unitalRep` below is the
    same witness with the degeneracy of `π` removed. -/
noncomputable def zeroHom : trivialNet.quasiLocalCStarAlgebra →⋆ₙₐ[ℂ] (ℂ →L[ℂ] ℂ) where
  toFun _ := 0
  map_smul' _ _ := by simp
  map_zero' := rfl
  map_add' _ _ := by simp
  map_mul' _ _ := (zero_mul (0 : ℂ →L[ℂ] ℂ)).symm
  map_star' _ := (star_zero (ℂ →L[ℂ] ℂ)).symm

/-- The zero representation of the trivial net's quasi-local C⋆-algebra, on `ℂ`. -/
noncomputable def zeroRep : CStarRep trivialNet.quasiLocalCStarAlgebra where
  H := ℂ
  π := zeroHom

/-- **The trivial net has the split property in the zero representation.** Its local von Neumann
    algebras act on `ℂ`, where the only von Neumann algebra is `𝓑(ℂ)`, a type I factor. This
    inhabits `LocalNet.SplitProperty` itself, not merely the `VonNeumannNet` form. -/
lemma trivialNet_splitProperty : trivialNet.SplitProperty zeroRep :=
  VonNeumannNet.splitProperty_of_complex (trivialNet.vonNeumannNet zeroRep)

/-! #### A unital representation

The isotony embeddings of `trivialNet` are all the identity of `ℂ`, so its algebra of local
observables collapses onto `ℂ` and its quasi-local C⋆-algebra onto the completion of `ℂ`. Reading
off that scalar and letting it multiply gives a representation on `ℂ` that carries `1` to `1`.
-/

/-- **Evaluation of a local observable of the trivial net.** Every local algebra is `ℂ` and every
    connecting map the identity, so the inductive limit maps onto `ℂ` by reading off the
    component. -/
noncomputable def evalLocal : trivialNet.localObservables →+* ℂ :=
  NormedDirectLimit.liftRingHom (fun _ => RingHom.id ℂ) (fun _ _ _ _ => rfl)

/-- Evaluation reads off the component of a local observable. -/
@[simp] lemma evalLocal_mk (O : Finset ℤ) (x : ℂ) :
    evalLocal (NormedDirectLimit.mk O x : trivialNet.localObservables) = x := rfl

/-- Evaluation preserves the involution: the involution of the limit acts componentwise, and on
    `ℂ` it is complex conjugation on both sides. -/
lemma evalLocal_star (z : trivialNet.localObservables) :
    evalLocal (star z) = star (evalLocal z) := by
  induction z using NormedDirectLimit.induction with
  | _ O X => rw [GradedLocalNet.star_mk]; rfl

/-- Evaluation is `ℂ`-linear: scalars act componentwise on the limit. -/
lemma evalLocal_smul (c : ℂ) (z : trivialNet.localObservables) :
    evalLocal (c • z) = c • evalLocal z := by
  induction z using NormedDirectLimit.induction with
  | _ O X => rw [← NormedDirectLimit.mk_smul]; rfl

/-- **Evaluation is isometric**: the C⋆-norm of the limit is the norm of the component. -/
lemma norm_evalLocal (z : trivialNet.localObservables) : ‖evalLocal z‖ = ‖z‖ := by
  induction z using NormedDirectLimit.induction with
  | _ O X => rw [GradedLocalNet.norm_mk]; rfl

/-- Evaluation extended to the quasi-local C⋆-algebra, by continuity from the dense image of the
    local observables. -/
noncomputable def evalQuasiLocal : trivialNet.quasiLocalCStarAlgebra →+* ℂ :=
  UniformSpace.Completion.extensionHom (β := ℂ) evalLocal
    (AddMonoidHomClass.isometry_of_norm _ norm_evalLocal).continuous

/-- The extension agrees with evaluation on the local observables. -/
@[simp] lemma evalQuasiLocal_coe (z : trivialNet.localObservables) :
    evalQuasiLocal (↑z : trivialNet.quasiLocalCStarAlgebra) = evalLocal z :=
  UniformSpace.Completion.extensionHom_coe _ _ z

/-- The extension is continuous, being the continuous extension of a uniformly continuous map. -/
lemma continuous_evalQuasiLocal : Continuous evalQuasiLocal :=
  UniformSpace.Completion.continuous_extension

/-- The extension preserves the involution: it does so on the dense image, and both sides are
    continuous. -/
lemma evalQuasiLocal_star (z : trivialNet.quasiLocalCStarAlgebra) :
    evalQuasiLocal (star z) = star (evalQuasiLocal z) := by
  refine UniformSpace.Completion.induction_on z
    (isClosed_eq (continuous_evalQuasiLocal.comp continuous_star)
      (continuous_star.comp continuous_evalQuasiLocal)) fun w => ?_
  rw [UniformSpace.Completion.star_coe, evalQuasiLocal_coe, evalQuasiLocal_coe, evalLocal_star]

/-- The extension is `ℂ`-linear: it is on the dense image, and both sides are continuous. -/
lemma evalQuasiLocal_smul (c : ℂ) (z : trivialNet.quasiLocalCStarAlgebra) :
    evalQuasiLocal (c • z) = c • evalQuasiLocal z := by
  refine UniformSpace.Completion.induction_on z
    (isClosed_eq (continuous_evalQuasiLocal.comp (continuous_const_smul c))
      ((continuous_const_smul c).comp continuous_evalQuasiLocal)) fun w => ?_
  rw [← UniformSpace.Completion.coe_smul, evalQuasiLocal_coe, evalQuasiLocal_coe, evalLocal_smul]

/-- **The unital `*`-representation of the quasi-local algebra of the trivial net on `ℂ`**:
    evaluate the quasi-local observable to a scalar, then let that scalar multiply. Unlike
    `zeroHom` it carries `1` to `1` (`unitalRep_π_one`). -/
noncomputable def unitalHom : trivialNet.quasiLocalCStarAlgebra →⋆ₙₐ[ℂ] (ℂ →L[ℂ] ℂ) where
  toFun z := evalQuasiLocal z • (1 : ℂ →L[ℂ] ℂ)
  map_smul' c z := by simp only [evalQuasiLocal_smul, smul_assoc, MonoidHom.id_apply]
  map_zero' := by
    rw [map_zero]
    exact ContinuousLinearMap.ext fun z => by simp
  map_add' _ _ := by
    rw [map_add]
    exact ContinuousLinearMap.ext fun z => by simp [add_mul]
  map_mul' _ _ := by rw [map_mul, smul_mul_assoc, one_mul, smul_smul]
  map_star' _ := by rw [evalQuasiLocal_star, star_smul, star_one]

/-- The unital representation of the trivial net's quasi-local C⋆-algebra, on `ℂ`. -/
noncomputable def unitalRep : CStarRep trivialNet.quasiLocalCStarAlgebra where
  H := ℂ
  π := unitalHom

/-- **The unital representation is unital**: `π 1 = 1`. This is what `zeroRep` fails, and the
    reason this second witness exists — without it the representation-level split property would be
    inhabited only by a `π` that annihilates the whole algebra. -/
@[simp] lemma unitalRep_π_one : unitalRep.π 1 = 1 := by
  change evalQuasiLocal 1 • (1 : ℂ →L[ℂ] ℂ) = 1
  rw [map_one, one_smul]

/-- **The trivial net has the split property in the unital representation too.** Like
    `trivialNet_splitProperty` this is an instance of `VonNeumannNet.splitProperty_of_complex`: the
    representation being unital changes the `*`-map but not the Hilbert space, and it is
    `dim H = 1` that makes the property hold. Recorded so that the witness set for
    `LocalNet.SplitProperty` is not confined to a degenerate representation. -/
lemma unitalRep_splitProperty : trivialNet.SplitProperty unitalRep :=
  VonNeumannNet.splitProperty_of_complex (trivialNet.vonNeumannNet unitalRep)

/-! ### The half-chain split property for a state

The evaluation of the trivial net's quasi-local algebra is a multiplicative state, so its GNS
representation acts by scalars and every pair of regions splits
(`LocalNet.IsSplitPairAt.of_map_mul`). This inhabits `LocalNet.HasHalfChainSplit`, for every order
on the quasi-local algebra compatible with its star structure; it is evidence of inhabitation only.
-/

/-- The evaluation of the quasi-local algebra of the trivial net is isometric. -/
lemma norm_evalQuasiLocal (z : trivialNet.quasiLocalCStarAlgebra) :
    ‖evalQuasiLocal z‖ = ‖z‖ := by
  refine UniformSpace.Completion.induction_on z
    (isClosed_eq (continuous_norm.comp continuous_evalQuasiLocal) continuous_norm) fun w => ?_
  rw [evalQuasiLocal_coe, norm_evalLocal, UniformSpace.Completion.norm_coe]

/-- The evaluation of the quasi-local algebra of the trivial net, as a continuous linear
    functional. -/
noncomputable def evalCLM : trivialNet.quasiLocalCStarAlgebra →L[ℂ] ℂ where
  toFun := evalQuasiLocal
  map_add' := map_add _
  map_smul' := evalQuasiLocal_smul
  cont := continuous_evalQuasiLocal

/-- The evaluation functional has norm one: it is isometric and sends `1` to `1`. -/
lemma norm_evalCLM : ‖evalCLM‖ = 1 := by
  have : Nontrivial trivialNet.quasiLocalCStarAlgebra := evalQuasiLocal.domain_nontrivial
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_) ?_
  · change ‖evalQuasiLocal z‖ ≤ 1 * ‖z‖
    rw [norm_evalQuasiLocal, one_mul]
  · have h := evalCLM.le_opNorm 1
    change ‖evalQuasiLocal 1‖ ≤ _ at h
    rwa [map_one, norm_one, norm_one, mul_one] at h

section HalfChainState

variable [PartialOrder trivialNet.quasiLocalCStarAlgebra]
  [StarOrderedRing trivialNet.quasiLocalCStarAlgebra]

open scoped ComplexOrder in
/-- **The evaluation state** of the trivial net's quasi-local algebra. Positivity holds for any
    order compatible with the star structure, since `ω (a* a) = |ω a|²`. -/
noncomputable def evalState : State trivialNet.quasiLocalCStarAlgebra :=
  State.ofContinuousLinearMap evalCLM
    (fun _ => StarOrderedRing.map_nonneg_of_star_mul_self_nonneg evalCLM fun a => by
      change 0 ≤ evalQuasiLocal (star a * a)
      rw [map_mul, evalQuasiLocal_star]
      exact star_mul_self_nonneg _)
    norm_evalCLM

/-- **The evaluation state has the half-chain split property.** It is multiplicative, so this
    is an instance of `LocalNet.IsSplitPairAt.of_map_mul`; it shows `LocalNet.HasHalfChainSplit` is
    inhabited, and nothing about states whose GNS algebras are not scalar. -/
theorem evalState_hasHalfChainSplit : trivialNet.HasHalfChainSplit evalState :=
  LocalNet.IsSplitPairAt.of_map_mul _ (fun a b => map_mul evalQuasiLocal a b) _ _

end HalfChainState

section NonemptyFinset

variable (α : Type*)

/-- **Disjointness on the nonempty finite sets of sites.** Causal orthogonality on
    `{s : Finset α // s.Nonempty}` is disjointness of the underlying sets, as on `Finset α`. A
    `def` rather than an instance, activated by `attribute [local instance]` below, so that the
    aggregate root does not fix a causal orthogonality on this subtype downstream. -/
@[reducible] def nonemptyFinsetOrthogonality :
    CausalOrthogonality {s : Finset α // s.Nonempty} where
  Orthogonal s t := Disjoint (s : Finset α) t
  orthogonal_symm _ _ h := h.symm
  orthogonal_mono_left _ _ _ h₀ h := h.mono_left h₀

attribute [local instance] nonemptyFinsetOrthogonality

/-- The nonempty finite sets of sites of an infinite `α` form a causal index set: a nonempty finite
    `s` is disjoint from `{p}` for a site `p ∉ s`. Unlike `Finset α`, the causal complement is not
    supplied by an empty region. -/
lemma nonemptyFinset_causalIndexSet [Infinite α] : CausalIndexSet {s : Finset α // s.Nonempty} :=
  ⟨fun s =>
    let ⟨p, hp⟩ := Infinite.exists_notMem_finset (s : Finset α)
    ⟨⟨{p}, Finset.singleton_nonempty p⟩, Finset.disjoint_singleton_right.2 hp⟩⟩

attribute [local instance] nonemptyFinset_causalIndexSet

variable {α} in
/-- No nonempty finite set of sites is causally orthogonal to itself. -/
lemma not_orthogonal_self_nonemptyFinset (s : {s : Finset α // s.Nonempty}) : ¬ s ⟂ s :=
  fun h => s.2.ne_empty (disjoint_self.1 h)

/-- **Localisation in the regions of the net, inhabited.** The nonempty finite sets of sites of an
    infinite `α` are their own localisation regions (`LocalizationRegions.ofOrthogonal`), with
    `Outside` disjointness and `Inside` inclusion. -/
@[reducible] def nonemptyFinsetLocalizationRegions [Infinite α] :
    LocalizationRegions {s : Finset α // s.Nonempty} {s : Finset α // s.Nonempty} :=
  LocalizationRegions.ofOrthogonal _ not_orthogonal_self_nonemptyFinset

end NonemptyFinset

section SpectralOrder

attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

/-- **The evaluation state at the canonical order has the half-chain split property**: the
    order hypotheses of `evalState_hasHalfChainSplit` are satisfiable, and are discharged here by
    the spectral order of the quasi-local C⋆-algebra (`CStarAlgebra.spectralOrder`), so
    `LocalNet.HasHalfChainSplit` is inhabited outright. -/
lemma evalState_hasHalfChainSplit_spectralOrder : trivialNet.HasHalfChainSplit evalState :=
  evalState_hasHalfChainSplit

end SpectralOrder

/-! ### A graded-local net that is not local: two Majorana modes -/

section MajoranaModes

/-- The **regions of two modes**: the left mode, the right mode and the whole system. The two modes
    are causally orthogonal, and both lie in the whole. -/
inductive TwoModeRegion
  | left | right | whole
  deriving DecidableEq

open TwoModeRegion

/-- A mode lies in itself and in the whole system. -/
instance : Preorder TwoModeRegion where
  le a b := a = b ∨ b = whole
  le_refl _ := Or.inl rfl
  le_trans a b c hab hbc := by
    rcases hab with rfl | rfl
    · exact hbc
    · rcases hbc with rfl | rfl <;> exact Or.inr rfl

/-- The two modes are causally orthogonal to each other, and nothing else is. -/
instance : CausalOrthogonality TwoModeRegion where
  Orthogonal a b := (a = left ∧ b = right) ∨ (a = right ∧ b = left)
  orthogonal_symm _ _ h := h.symm.imp And.symm And.symm
  orthogonal_mono_left O₀ O₁ O₂ h ho := by
    rcases h with rfl | rfl
    · exact ho
    · rcases ho with ⟨h, -⟩ | ⟨h, -⟩ <;> cases h

/-- The whole system contains both modes, so the regions are directed. -/
instance : IsDirectedOrder TwoModeRegion where
  directed _ _ := ⟨whole, Or.inr rfl, Or.inr rfl⟩

instance : Nonempty TwoModeRegion :=
  ⟨whole⟩

section Majorana

variable {A : Type*} [CStarAlgebra A]

/-- The algebra of **one Majorana mode** `γ` inside `A`: the ⋆-subalgebra generated by `γ`. For a
    self-adjoint unitary `γ` its elements are the `α + β γ` (`mem_majoranaSubalgebra`) and it is
    closed (`isClosed_majoranaSubalgebra`); for such a `γ` not a scalar it is the Clifford algebra of
    one generator. -/
def majoranaSubalgebra (γ : A) : StarSubalgebra ℂ A :=
  StarAlgebra.adjoin ℂ {γ}

/-- For a self-adjoint unitary `γ`, the elements of the algebra of the Majorana mode `γ` are the
    `α + β γ`. -/
lemma mem_majoranaSubalgebra {γ : A} (hγ : star γ = γ) (hγ2 : γ * γ = 1) {a : A} :
    a ∈ majoranaSubalgebra γ ↔ ∃ α β : ℂ, a = α • 1 + β • γ := by
  constructor
  · intro ha
    induction ha using StarAlgebra.adjoin_induction with
    | mem x hx =>
      obtain rfl := hx
      exact ⟨0, 1, by simp⟩
    | algebraMap r => exact ⟨r, 0, by simp [Algebra.algebraMap_eq_smul_one]⟩
    | add x y _ _ hx hy =>
      obtain ⟨α, β, rfl⟩ := hx
      obtain ⟨α', β', rfl⟩ := hy
      exact ⟨α + α', β + β', by module⟩
    | mul x y _ _ hx hy =>
      obtain ⟨α, β, rfl⟩ := hx
      obtain ⟨α', β', rfl⟩ := hy
      refine ⟨α * α' + β * β', α * β' + β * α', ?_⟩
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hγ2]
      module
    | star x _ hx =>
      obtain ⟨α, β, rfl⟩ := hx
      exact ⟨star α, star β, by simp [hγ]⟩
  · rintro ⟨α, β, rfl⟩
    exact add_mem (SMulMemClass.smul_mem α (one_mem _))
      (SMulMemClass.smul_mem β (StarAlgebra.subset_adjoin ℂ {γ} rfl))

/-- The mode `γ` lies in its own algebra. -/
lemma self_mem_majoranaSubalgebra (γ : A) : γ ∈ majoranaSubalgebra γ :=
  StarAlgebra.subset_adjoin ℂ {γ} rfl

/-- For a self-adjoint unitary `γ`, the algebra of the Majorana mode `γ` is closed, being
    finite-dimensional. -/
lemma isClosed_majoranaSubalgebra {γ : A} (hγ : star γ = γ) (hγ2 : γ * γ = 1) :
    IsClosed (majoranaSubalgebra γ : Set A) := by
  have h : (majoranaSubalgebra γ : Set A) = (Submodule.span ℂ {1, γ} : Set A) := by
    ext a
    simp only [SetLike.mem_coe, mem_majoranaSubalgebra hγ hγ2, Submodule.mem_span_pair]
    exact ⟨fun ⟨α, β, h⟩ => ⟨α, β, h.symm⟩, fun ⟨α, β, h⟩ => ⟨α, β, h.symm⟩⟩
  rw [h]
  have : FiniteDimensional ℂ (Submodule.span ℂ ({1, γ} : Set A)) :=
    FiniteDimensional.span_of_finite ℂ (Set.toFinite _)
  exact Submodule.closed_of_finiteDimensional _

variable (Θ : A ≃⋆ₐ[ℂ] A)

/-- For a parity `Θ` reversing `γ`, the even elements of the algebra of the Majorana mode `γ` are
    the scalars. -/
lemma exists_eq_smul_one_of_even {γ : A} (hγ : star γ = γ) (hγ2 : γ * γ = 1) (hΘγ : Θ γ = -γ)
    {a : A} (ha : a ∈ majoranaSubalgebra γ) (h : Θ a = a) : ∃ α : ℂ, a = α • 1 := by
  obtain ⟨α, β, rfl⟩ := (mem_majoranaSubalgebra hγ hγ2).mp ha
  refine ⟨α, ?_⟩
  rw [map_add, map_smul, map_smul, map_one, hΘγ, smul_neg] at h
  have := HasUniqueDiv.of_isTorsionFree ℂ A
  rw [neg_eq_self.mp (add_left_cancel h), add_zero]

/-- For a parity `Θ` reversing `γ`, the odd elements of the algebra of the Majorana mode `γ` are
    the multiples of `γ`. -/
lemma exists_eq_smul_of_odd {γ : A} (hγ : star γ = γ) (hγ2 : γ * γ = 1) (hΘγ : Θ γ = -γ)
    {a : A} (ha : a ∈ majoranaSubalgebra γ) (h : Θ a = -a) : ∃ β : ℂ, a = β • γ := by
  obtain ⟨α, β, rfl⟩ := (mem_majoranaSubalgebra hγ hγ2).mp ha
  refine ⟨β, ?_⟩
  rw [map_add, map_smul, map_smul, map_one, hΘγ, smul_neg, neg_add] at h
  have := HasUniqueDiv.of_isTorsionFree ℂ A
  have h0 : α • (1 : A) = 0 := neg_eq_self.mp (add_right_cancel h).symm
  rw [h0, zero_add]

/-- The **graded-local net of two Majorana modes** `γ₁`, `γ₂` — anticommuting self-adjoint
    unitaries of a C⋆-algebra `A`, both reversed by an involutive automorphism `Θ` — over the
    regions of two modes: the left region carries the algebra of `γ₁`, the right one that of `γ₂`,
    the whole system carries `A`, and `Θ` is the parity. Even elements of a mode are scalars and
    commute with everything; the odd ones are the multiples of `γ₁` and of `γ₂`, which
    anticommute. -/
noncomputable def majoranaNet (γ₁ γ₂ : A) (h₁ : star γ₁ = γ₁) (h₂ : star γ₂ = γ₂)
    (h₁2 : γ₁ * γ₁ = 1) (h₂2 : γ₂ * γ₂ = 1) (hanti : γ₁ * γ₂ = -(γ₂ * γ₁))
    (hΘ : ∀ a, Θ (Θ a) = a) (hΘ₁ : Θ γ₁ = -γ₁) (hΘ₂ : Θ γ₂ = -γ₂) :
    GradedLocalNet TwoModeRegion :=
  let S : TwoModeRegion → StarSubalgebra ℂ A := fun O =>
    match O with
    | left => majoranaSubalgebra γ₁
    | right => majoranaSubalgebra γ₂
    | whole => ⊤
  haveI : ∀ O, IsClosed (S O : Set A) := fun O => by
    cases O
    · exact isClosed_majoranaSubalgebra h₁ h₁2
    · exact isClosed_majoranaSubalgebra h₂ h₂2
    · exact isClosed_univ
  have hΘS : ∀ O, ∀ a ∈ S O, Θ a ∈ S O := fun O a ha => by
    cases O
    · obtain ⟨α, β, rfl⟩ := (mem_majoranaSubalgebra h₁ h₁2).mp ha
      exact (mem_majoranaSubalgebra h₁ h₁2).mpr ⟨α, -β, by simp [hΘ₁]⟩
    · obtain ⟨α, β, rfl⟩ := (mem_majoranaSubalgebra h₂ h₂2).mp ha
      exact (mem_majoranaSubalgebra h₂ h₂2).mpr ⟨α, -β, by simp [hΘ₂]⟩
    · exact StarSubalgebra.mem_top
  GradedLocalNet.ofStarSubalgebras S
    (fun O O' h => by
      rcases h with rfl | rfl
      · exact le_rfl
      · exact le_top)
    Θ hΘ hΘS
    (fun {O₁ O₂} hd a ha b _ hΘa => by
      rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · obtain ⟨α, rfl⟩ := exists_eq_smul_one_of_even Θ h₁ h₁2 hΘ₁ ha hΘa
        exact (Commute.one_left b).smul_left α
      · obtain ⟨α, rfl⟩ := exists_eq_smul_one_of_even Θ h₂ h₂2 hΘ₂ ha hΘa
        exact (Commute.one_left b).smul_left α)
    (fun {O₁ O₂} hd a ha b hb hΘa hΘb => by
      rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · obtain ⟨α, rfl⟩ := exists_eq_smul_of_odd Θ h₁ h₁2 hΘ₁ ha hΘa
        obtain ⟨β, rfl⟩ := exists_eq_smul_of_odd Θ h₂ h₂2 hΘ₂ hb hΘb
        rw [smul_mul_smul_comm, smul_mul_smul_comm, hanti, smul_neg, mul_comm α β]
      · obtain ⟨α, rfl⟩ := exists_eq_smul_of_odd Θ h₂ h₂2 hΘ₂ ha hΘa
        obtain ⟨β, rfl⟩ := exists_eq_smul_of_odd Θ h₁ h₁2 hΘ₁ hb hΘb
        rw [smul_mul_smul_comm, smul_mul_smul_comm, hanti, smul_neg, neg_neg, mul_comm α β])

/-- The net of two Majorana modes is faithful: its isotony embeddings are inclusions. -/
instance instFaithfulMajoranaNet (γ₁ γ₂ : A) (h₁ : star γ₁ = γ₁) (h₂ : star γ₂ = γ₂)
    (h₁2 : γ₁ * γ₁ = 1) (h₂2 : γ₂ * γ₂ = 1) (hanti : γ₁ * γ₂ = -(γ₂ * γ₁))
    (hΘ : ∀ a, Θ (Θ a) = a) (hΘ₁ : Θ γ₁ = -γ₁) (hΘ₂ : Θ γ₂ = -γ₂) :
    (majoranaNet Θ γ₁ γ₂ h₁ h₂ h₁2 h₂2 hanti hΘ hΘ₁ hΘ₂).Faithful where
  incl_injective _ _ _ h := by
    have h' := congrArg Subtype.val h
    exact Subtype.ext h'

end Majorana

section Pauli

open Matrix Complex

/-- The algebra `M₂(ℂ)` of operators on `ℂ²`, in which the Pauli matrices live. -/
abbrev PauliAlgebra : Type := EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)

/-- The Pauli matrix `σ_x`, as an operator on `ℂ²`. -/
noncomputable def pauliX : PauliAlgebra :=
  Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) !![0, 1; 1, 0]

/-- The Pauli matrix `σ_y`, as an operator on `ℂ²`. -/
noncomputable def pauliY : PauliAlgebra :=
  Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) !![0, -I; I, 0]

/-- The Pauli matrix `σ_z`, as an operator on `ℂ²`. -/
noncomputable def pauliZ : PauliAlgebra :=
  Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) !![1, 0; 0, -1]

/-- An identity between operators on `ℂ²` given by matrices is checked on the matrices, entry by
entry. -/
lemma toEuclideanCLM_congr {M N : Matrix (Fin 2) (Fin 2) ℂ} (h : ∀ i j, M i j = N i j) :
    Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) M = Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) N :=
  congrArg _ (Matrix.ext h)

/-- `σ_x` is self-adjoint. -/
lemma star_pauliX : star pauliX = pauliX := by
  rw [pauliX, ← map_star]
  exact toEuclideanCLM_congr (by simp [Fin.forall_fin_two])

/-- `σ_y` is self-adjoint. -/
lemma star_pauliY : star pauliY = pauliY := by
  rw [pauliY, ← map_star]
  exact toEuclideanCLM_congr (by simp [Fin.forall_fin_two])

/-- `σ_z` is self-adjoint. -/
lemma star_pauliZ : star pauliZ = pauliZ := by
  rw [pauliZ, ← map_star]
  exact toEuclideanCLM_congr (by simp [Fin.forall_fin_two])

/-- `σ_x² = 1`. -/
lemma pauliX_mul_self : pauliX * pauliX = 1 := by
  rw [pauliX, ← map_mul, ← map_one (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ))]
  exact toEuclideanCLM_congr (by simp [Fin.forall_fin_two])

/-- `σ_y² = 1`. -/
lemma pauliY_mul_self : pauliY * pauliY = 1 := by
  rw [pauliY, ← map_mul, ← map_one (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ))]
  exact toEuclideanCLM_congr (by simp [Fin.forall_fin_two])

/-- `σ_z² = 1`. -/
lemma pauliZ_mul_self : pauliZ * pauliZ = 1 := by
  rw [pauliZ, ← map_mul, ← map_one (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ))]
  exact toEuclideanCLM_congr (by simp [Fin.forall_fin_two])

/-- `σ_x` and `σ_y` anticommute. -/
lemma pauliX_mul_pauliY : pauliX * pauliY = -(pauliY * pauliX) := by
  rw [pauliX, pauliY, ← map_mul (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)),
    ← map_mul (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)), ← map_neg (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ))]
  exact toEuclideanCLM_congr (by simp [Fin.forall_fin_two])

/-- `σ_z` and `σ_x` anticommute. -/
lemma pauliZ_mul_pauliX : pauliZ * pauliX = -(pauliX * pauliZ) := by
  rw [pauliX, pauliZ, ← map_mul (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)),
    ← map_mul (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)), ← map_neg (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ))]
  exact toEuclideanCLM_congr (by simp [Fin.forall_fin_two])

/-- `σ_z` and `σ_y` anticommute. -/
lemma pauliZ_mul_pauliY : pauliZ * pauliY = -(pauliY * pauliZ) := by
  rw [pauliY, pauliZ, ← map_mul (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)),
    ← map_mul (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)), ← map_neg (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ))]
  exact toEuclideanCLM_congr (by simp [Fin.forall_fin_two])

/-- The **parity** of `M₂(ℂ)`: conjugation by `σ_z`. -/
noncomputable def pauliParity : PauliAlgebra ≃⋆ₐ[ℂ] PauliAlgebra :=
  Unitary.conjStarAlgAut ℂ PauliAlgebra
    ⟨pauliZ, by rw [Unitary.mem_iff, star_pauliZ, pauliZ_mul_self]; exact ⟨rfl, rfl⟩⟩

/-- The parity is `a ↦ σ_z a σ_z`. -/
lemma pauliParity_apply (a : PauliAlgebra) : pauliParity a = pauliZ * a * pauliZ := by
  rw [pauliParity, Unitary.conjStarAlgAut_apply]
  exact congrArg (pauliZ * a * ·) star_pauliZ

/-- The parity of `M₂(ℂ)` is an involution. -/
lemma pauliParity_pauliParity (a : PauliAlgebra) : pauliParity (pauliParity a) = a := by
  rw [pauliParity_apply, pauliParity_apply]
  calc pauliZ * (pauliZ * a * pauliZ) * pauliZ
      = (pauliZ * pauliZ) * a * (pauliZ * pauliZ) := by noncomm_ring
    _ = a := by rw [pauliZ_mul_self, one_mul, mul_one]

/-- An operator anticommuting with `σ_z` is odd. -/
lemma pauliParity_eq_neg_of_anticommute {a : PauliAlgebra} (h : pauliZ * a = -(a * pauliZ)) :
    pauliParity a = -a := by
  rw [pauliParity_apply, h]
  calc -(a * pauliZ) * pauliZ = -(a * (pauliZ * pauliZ)) :=
        (neg_mul (a * pauliZ) pauliZ).trans (congrArg Neg.neg (mul_assoc _ _ _))
    _ = -a := by rw [pauliZ_mul_self, mul_one]

/-- `σ_x` is odd. -/
lemma pauliParity_pauliX : pauliParity pauliX = -pauliX :=
  pauliParity_eq_neg_of_anticommute pauliZ_mul_pauliX

/-- `σ_y` is odd. -/
lemma pauliParity_pauliY : pauliParity pauliY = -pauliY :=
  pauliParity_eq_neg_of_anticommute pauliZ_mul_pauliY

/-- **Two Majorana modes in `M₂(ℂ)`**: the graded-local net of the modes `σ_x` and `σ_y`, with the
    parity `a ↦ σ_z a σ_z`. The left region carries `ℂ[σ_x]`, the right one `ℂ[σ_y]` and the whole
    `M₂(ℂ)`, the Clifford algebra of two generators. Its parity is not trivial and its odd elements
    do not commute (`not_commute_pauliMajoranaNet`), so it is not a `LocalNet`
    (`not_locality_pauliMajoranaNet`). -/
noncomputable def pauliMajoranaNet : GradedLocalNet TwoModeRegion :=
  majoranaNet pauliParity pauliX pauliY star_pauliX star_pauliY pauliX_mul_self pauliY_mul_self
    pauliX_mul_pauliY pauliParity_pauliParity pauliParity_pauliX pauliParity_pauliY

instance : pauliMajoranaNet.Faithful :=
  instFaithfulMajoranaNet ..

/-- `σ_x` and `σ_y` do not commute. -/
lemma pauliX_mul_pauliY_ne : pauliX * pauliY ≠ pauliY * pauliX := fun h => by
  have := HasUniqueDiv.of_isTorsionFree ℂ PauliAlgebra
  have h0 : pauliX * pauliY = 0 := neg_eq_self.mp <|
    calc -(pauliX * pauliY) = -(pauliY * pauliX) := by rw [h]
      _ = pauliX * pauliY := pauliX_mul_pauliY.symm
  have h1 : (1 : PauliAlgebra) = 0 := by
    calc (1 : PauliAlgebra) = pauliX * (pauliX * pauliY) * pauliY := by
          rw [← mul_assoc, pauliX_mul_self, one_mul, pauliY_mul_self]
      _ = 0 := by rw [h0, mul_zero, zero_mul]
  exact one_ne_zero h1

/-- The mode `σ_x`, as a local observable of the left region. -/
noncomputable def pauliMajoranaLeft : pauliMajoranaNet.algebra left :=
  (⟨pauliX, self_mem_majoranaSubalgebra pauliX⟩ : majoranaSubalgebra pauliX)

/-- The mode `σ_y`, as a local observable of the right region. -/
noncomputable def pauliMajoranaRight : pauliMajoranaNet.algebra right :=
  (⟨pauliY, self_mem_majoranaSubalgebra pauliY⟩ : majoranaSubalgebra pauliY)

/-- The mode of the left region is odd. -/
lemma parity_pauliMajoranaLeft :
    pauliMajoranaNet.parity left pauliMajoranaLeft = -pauliMajoranaLeft :=
  Subtype.ext pauliParity_pauliX

/-- The mode of the right region is odd. -/
lemma parity_pauliMajoranaRight :
    pauliMajoranaNet.parity right pauliMajoranaRight = -pauliMajoranaRight :=
  Subtype.ext pauliParity_pauliY

/-- **The two Majorana modes do not commute**, although their regions are causally orthogonal:
    they anticommute, by graded locality. So the graded locality of `pauliMajoranaNet` is not
    commutation, and the net is not a `LocalNet` (`not_locality_pauliMajoranaNet`). -/
theorem not_commute_pauliMajoranaNet :
    ¬ Commute (pauliMajoranaNet.incl (O := left) (O' := whole) (Or.inr rfl) pauliMajoranaLeft)
      (pauliMajoranaNet.incl (O := right) (O' := whole) (Or.inr rfl) pauliMajoranaRight) :=
  fun h => pauliX_mul_pauliY_ne (congrArg Subtype.val h.eq)

/-- **The Majorana net is not a local net, even with its parity forgotten**: its local algebras and
    isotony embeddings fail the locality hypothesis of `LocalNet.ofLocality`, the two modes of the
    causally orthogonal regions not commuting inside the whole system. -/
theorem not_locality_pauliMajoranaNet :
    ¬ ∀ {O₁ O₂ O : TwoModeRegion} (h₁ : O₁ ≤ O) (h₂ : O₂ ≤ O), O₁ ⟂ O₂ →
      ∀ (x : pauliMajoranaNet.algebra O₁) (y : pauliMajoranaNet.algebra O₂),
        Commute (pauliMajoranaNet.incl h₁ x) (pauliMajoranaNet.incl h₂ y) :=
  fun h => not_commute_pauliMajoranaNet (h (Or.inr rfl) (Or.inr rfl) (Or.inl ⟨rfl, rfl⟩) _ _)

/-! #### The quasi-local algebra of the Majorana net -/

/-- `σ_x` is not zero. -/
lemma pauliX_ne_zero : pauliX ≠ 0 := fun h =>
  one_ne_zero (by rw [← pauliX_mul_self, h, zero_mul] : (1 : PauliAlgebra) = 0)

/-- **The two Majorana modes anticommute in the quasi-local algebra**, by graded locality
(`GradedLocalNet.ιLocalCStar_mul_eq_neg_of_orthogonal_of_odd`). Both sides are not zero, the modes
not commuting there (`not_commute_ιLocalCStar_pauliMajorana`). -/
theorem ιLocalCStar_pauliMajoranaLeft_mul_pauliMajoranaRight :
    pauliMajoranaNet.ιLocalCStar left pauliMajoranaLeft *
        pauliMajoranaNet.ιLocalCStar right pauliMajoranaRight =
      -(pauliMajoranaNet.ιLocalCStar right pauliMajoranaRight *
        pauliMajoranaNet.ιLocalCStar left pauliMajoranaLeft) :=
  pauliMajoranaNet.ιLocalCStar_mul_eq_neg_of_orthogonal_of_odd (Or.inl ⟨rfl, rfl⟩) _ _
    parity_pauliMajoranaLeft parity_pauliMajoranaRight

/-- **The two Majorana modes do not commute in the quasi-local algebra**: the local embedding of
the whole system is injective, and the modes do not commute there (`not_commute_pauliMajoranaNet`). -/
theorem not_commute_ιLocalCStar_pauliMajorana :
    ¬ Commute (pauliMajoranaNet.ιLocalCStar left pauliMajoranaLeft)
      (pauliMajoranaNet.ιLocalCStar right pauliMajoranaRight) := fun h =>
  not_commute_pauliMajoranaNet <| pauliMajoranaNet.ιLocalCStar_injective whole <| by
    rw [map_mul, map_mul, GradedLocalNet.ιLocalCStar_incl, GradedLocalNet.ιLocalCStar_incl]
    exact h

/-- The quasi-local parity of the Majorana net reverses the mode `σ_x`. -/
theorem quasiLocalParity_ιLocalCStar_pauliMajoranaLeft :
    pauliMajoranaNet.quasiLocalParity (pauliMajoranaNet.ιLocalCStar left pauliMajoranaLeft) =
      -pauliMajoranaNet.ιLocalCStar left pauliMajoranaLeft := by
  rw [GradedLocalNet.quasiLocalParity_ιLocalCStar, parity_pauliMajoranaLeft, map_neg]

/-- **The quasi-local parity of the Majorana net is not trivial**: it moves the mode `σ_x`, which
is odd and not zero. -/
theorem quasiLocalParity_ιLocalCStar_pauliMajoranaLeft_ne :
    pauliMajoranaNet.quasiLocalParity (pauliMajoranaNet.ιLocalCStar left pauliMajoranaLeft) ≠
      pauliMajoranaNet.ιLocalCStar left pauliMajoranaLeft := fun h => by
  rw [quasiLocalParity_ιLocalCStar_pauliMajoranaLeft] at h
  have := HasUniqueDiv.of_isTorsionFree ℂ pauliMajoranaNet.quasiLocalCStarAlgebra
  have h0 : pauliMajoranaLeft = 0 :=
    pauliMajoranaNet.ιLocalCStar_injective left ((neg_eq_self.mp h).trans (map_zero _).symm)
  exact pauliX_ne_zero (congrArg Subtype.val h0)

/-- `σ_z` is even. -/
lemma pauliParity_pauliZ : pauliParity pauliZ = pauliZ := by
  rw [pauliParity_apply, pauliZ_mul_self, one_mul]

/-- The operator `σ_z`, as a local observable of the whole system. -/
noncomputable def pauliMajoranaZ : pauliMajoranaNet.algebra whole :=
  (⟨pauliZ, StarSubalgebra.mem_top⟩ : (⊤ : StarSubalgebra ℂ PauliAlgebra))

/-- **`σ_z` is even in the quasi-local algebra of the Majorana net**, an element of the even subnet
of the whole system. -/
theorem ιLocalCStar_pauliMajoranaZ_mem_quasiLocalEvenPart :
    pauliMajoranaNet.ιLocalCStar whole pauliMajoranaZ ∈ pauliMajoranaNet.quasiLocalEvenPart :=
  pauliMajoranaNet.ιLocalCStar_mem_quasiLocalEvenPart_iff.mpr
    (pauliMajoranaNet.mem_evenPart.mpr (Subtype.ext pauliParity_pauliZ))

/-- **The mode `σ_x` is not even in the quasi-local algebra**: the even part of the quasi-local
algebra of the Majorana net is a proper subalgebra. -/
theorem ιLocalCStar_pauliMajoranaLeft_notMem_quasiLocalEvenPart :
    pauliMajoranaNet.ιLocalCStar left pauliMajoranaLeft ∉ pauliMajoranaNet.quasiLocalEvenPart :=
  fun h => quasiLocalParity_ιLocalCStar_pauliMajoranaLeft_ne
    (pauliMajoranaNet.mem_quasiLocalEvenPart.mp h)

end Pauli

/-! ### A continuous on-site symmetry of a quantum spin chain -/

section SpinChain

open scoped TensorProduct PiMinTensorProduct

/-- The operator `diag(1, z)` on `ℂ²`, in the eigenbasis of `σ_z`. -/
noncomputable def phaseOp (z : ℂ) : PauliAlgebra :=
  Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) !![1, 0; 0, z]

/-- `diag(1, z) diag(1, w) = diag(1, z w)`. -/
lemma phaseOp_mul (z w : ℂ) : phaseOp z * phaseOp w = phaseOp (z * w) := by
  rw [phaseOp, phaseOp, phaseOp, ← map_mul]
  exact toEuclideanCLM_congr (by simp)

/-- `diag(1, z)⋆ = diag(1, z̄)`. -/
lemma star_phaseOp (z : ℂ) : star (phaseOp z) = phaseOp (star z) := by
  rw [phaseOp, phaseOp, ← map_star]
  exact toEuclideanCLM_congr (by simp [Fin.forall_fin_two])

/-- `diag(1, 1) = 1`. -/
lemma phaseOp_one : phaseOp 1 = 1 := by
  rw [phaseOp, ← map_one (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ))]
  exact toEuclideanCLM_congr (by simp [Fin.forall_fin_two])

/-- `diag(1, -1) = σ_z`. -/
lemma phaseOp_neg_one : phaseOp (-1) = pauliZ := by
  rw [phaseOp, pauliZ]

/-- `z ↦ diag(1, z)` is continuous. -/
lemma continuous_phaseOp : Continuous phaseOp :=
  (LinearMap.continuous_of_finiteDimensional (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] PauliAlgebra)).comp (by fun_prop)

/-- For `z` on the circle, `diag(1, z)` is unitary. -/
lemma phaseOp_mem_unitary (z : Circle) : phaseOp z ∈ unitary PauliAlgebra := by
  have h : star (z : ℂ) * z = 1 := by
    rw [Complex.star_def, ← Circle.coe_inv_eq_conj, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]
  rw [Unitary.mem_iff, star_phaseOp, phaseOp_mul, phaseOp_mul, h, mul_comm, h, phaseOp_one]
  exact ⟨rfl, rfl⟩

/-- The phases `z ↦ diag(1, z)` of a spin, as a homomorphism of the circle into the unitaries of
`M₂(ℂ)`. -/
noncomputable def phaseUnitary : Circle →* unitary PauliAlgebra where
  toFun z := ⟨phaseOp z, phaseOp_mem_unitary z⟩
  map_one' := Subtype.ext ((congrArg phaseOp Circle.coe_one).trans phaseOp_one)
  map_mul' z w := Subtype.ext ((congrArg phaseOp (Circle.coe_mul z w)).trans (phaseOp_mul z w).symm)

/-- **The phase rotations of a spin**: the circle acting on `M₂(ℂ)` by `x ↦ diag(1, z) x diag(1, z)⋆`,
a C⋆-dynamical system. -/
noncomputable def phaseRotation : Circle →ₜ* (PauliAlgebra ≃⋆ₐ[ℂ] PauliAlgebra) :=
  ⟨(Unitary.conjStarAlgAut ℂ PauliAlgebra).comp phaseUnitary,
    StarAlgEquiv.continuous_iff.mpr fun a => by
      change Continuous fun z : Circle => phaseOp z * a * star (phaseOp z)
      simp_rw [star_phaseOp]
      have hz : Continuous fun z : Circle => (z : ℂ) := by fun_prop
      exact ((continuous_phaseOp.comp hz).mul continuous_const).mul
        (continuous_phaseOp.comp (continuous_star.comp hz))⟩

/-- The rotation by `-1` is the parity `a ↦ σ_z a σ_z`. -/
lemma phaseRotation_neg_one (a : PauliAlgebra) : phaseRotation (-1) a = pauliParity a := by
  change phaseOp ((-1 : Circle) : ℂ) * a * star (phaseOp ((-1 : Circle) : ℂ)) = _
  rw [Circle.coe_neg, Circle.coe_one, phaseOp_neg_one, star_pauliZ, pauliParity_apply]

/-- **The phase rotations of a spin chain**: the circle acting on the quasi-local C⋆-algebra of the
spin chain on `ℤ`, the tensor product net of `M₂(ℂ)`, by the phase rotation of every spin: a
C⋆-dynamical system (`LocalNet.onSiteDynamicalSystem`) whose group is not discrete, on a net whose
isotony embeddings are not identities. -/
noncomputable def spinChainPhaseRotation :
    Circle →ₜ* ((tensorNet ℤ PauliAlgebra).quasiLocalCStarAlgebra ≃⋆ₐ[ℂ]
      (tensorNet ℤ PauliAlgebra).quasiLocalCStarAlgebra) :=
  onSiteDynamicalSystem ℤ phaseRotation

/-- The spin `σ_x` at the site `0`, as a local observable of the region `{0}`. -/
noncomputable def pauliXAtZero : ⨂ₘᵢₙ _ : ({0} : Finset ℤ), PauliAlgebra :=
  PiMinTensorProduct.of _ (⨂ₜ[ℂ] _ : ({0} : Finset ℤ), pauliX)

/-- **The rotation by `-1` reverses the spin `σ_x` at the site `0`**: it is the parity
`a ↦ σ_z a σ_z` on every site, and `σ_z σ_x σ_z = -σ_x`. -/
theorem spinChainPhaseRotation_neg_one_pauliXAtZero :
    spinChainPhaseRotation (-1) ((tensorNet ℤ PauliAlgebra).ιLocalCStar {0} pauliXAtZero) =
      (tensorNet ℤ PauliAlgebra).ιLocalCStar {0} (-pauliXAtZero) := by
  refine (onSiteDynamicalSystem_ιLocalCStar_of_tprod phaseRotation (-1) {0}
    fun _ => pauliX).trans (congrArg _ ?_)
  change _ = -PiMinTensorProduct.of _ (⨂ₜ[ℂ] _ : ({0} : Finset ℤ), pauliX)
  rw [← map_neg]
  congr 1
  simp only [phaseRotation_neg_one, pauliParity_pauliX]
  have h := (PiTensorProduct.tprod ℂ).map_smul_univ (fun _ : ({0} : Finset ℤ) => (-1 : ℂ))
    (fun _ => pauliX)
  simp only [neg_one_smul, Finset.prod_const, Finset.card_univ, Fintype.card_coe,
    Finset.card_singleton, pow_one] at h
  exact h

/-- The spin `σ_x` at the site `0` is not zero. -/
lemma pauliXAtZero_ne_zero : pauliXAtZero ≠ 0 := fun h => by
  have : Subsingleton ({0} : Finset ℤ) := ⟨fun a b => Subtype.ext
    ((Finset.mem_singleton.mp a.2).trans (Finset.mem_singleton.mp b.2).symm)⟩
  have h2 := congrArg (PiMinTensorProduct.subsingletonEquiv (fun _ : ({0} : Finset ℤ) => PauliAlgebra)
    ⟨0, Finset.mem_singleton_self 0⟩) h
  rw [pauliXAtZero, PiMinTensorProduct.subsingletonEquiv_of,
    PiTensorProduct.subsingletonStarAlgEquiv_tprod, map_zero] at h2
  have h3 := pauliX_mul_self
  rw [h2, zero_mul] at h3
  exact zero_ne_one h3

/-- **The phase rotations act non-trivially**: the rotation by `-1` moves the spin `σ_x` at the site
`0`, which it reverses (`spinChainPhaseRotation_neg_one_pauliXAtZero`). -/
theorem spinChainPhaseRotation_neg_one_ne :
    spinChainPhaseRotation (-1) ((tensorNet ℤ PauliAlgebra).ιLocalCStar {0} pauliXAtZero) ≠
      (tensorNet ℤ PauliAlgebra).ιLocalCStar {0} pauliXAtZero := by
  rw [spinChainPhaseRotation_neg_one_pauliXAtZero]
  refine ((tensorNet ℤ PauliAlgebra).ιLocalCStar_injective {0}).ne fun h => ?_
  have := HasUniqueDiv.of_isTorsionFree ℂ (⨂ₘᵢₙ _ : ({0} : Finset ℤ), PauliAlgebra)
  exact pauliXAtZero_ne_zero (neg_eq_self.mp h)

end SpinChain

end MajoranaModes

end LocalNet.Examples
