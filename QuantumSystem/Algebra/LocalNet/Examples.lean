/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Algebra.LocalNet.InfiniteRegion

/-!
# Witnesses for the local-net interfaces

Every class and structure the local-net development introduces is inhabited here, by explicit
construction. Without such witnesses the theorems of `LocalNet.Net`, `LocalNet.QuasiLocalAlgebra`
and `LocalNet.SplitProperty` would be unfalsifiable: nobody could apply them, and no construction
could contradict them. In particular the split property, being a `Prop`-valued hypothesis that
nothing in the development proves, needs a model exhibited before it can be believed consistent.

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
* **A faithful local net.** `LocalNet.Examples.trivialNet` assigns `ℂ` to every region of the
  integer chain, with identity isotony embeddings, built through the join-semilattice smart
  constructor `LocalNet.mk'`; its `Faithful` instance is immediate.
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
* **Matsui's gap-free half-chain pair.** `LocalNet.Examples.not_isSplitPair_diagonalNet_extend`
  refutes `VonNeumannNet.IsSplitPair` at `(-∞, 0]`, `[1, ∞)` for the diagonal net, and
  `LocalNet.Examples.scalarNet_extend_isSplitPair` inhabits it. At the state level,
  `LocalNet.Examples.evalState_hasHalfChainSplit` inhabits `LocalNet.HasHalfChainSplit` with the
  evaluation state of the trivial net, a multiplicative state whose GNS algebras are scalar, for
  every order on the quasi-local algebra compatible with its star structure; at the canonical
  spectral order it holds outright (`LocalNet.Examples.evalState_hasHalfChainSplit_spectralOrder`).

What is deliberately *not* built here is a spin-system net with genuine tensor-product local
algebras — the physically interesting lattice model the module docs of `LocalNet.Net` and
`LocalNet.Covariance` describe. That is a construction in its own right, not a witness; these
witnesses establish consistency and applicability of the interfaces, nothing more.

**The residual degeneracy, stated so it is not mistaken for evidence.** Every Hilbert space
appearing below is `ℂ`, and on `ℂ` the split property is *automatic*: the only von Neumann algebra
there is `𝓑(ℂ)` (`VonNeumannAlgebra.eq_boundedLinearOperators_complex`), so every net of von
Neumann algebras on `ℂ` splits (`VonNeumannNet.splitProperty_of_complex`), and both
representation-level witnesses below are instances of that one theorem. So the degeneracy is
`dim H = 1` — *not* the zero representation, which is why exchanging it for a unital one changes
nothing mathematically. This is the one reason the literature explicitly sets aside:
Halvorson–Müger's type III₁ proposition carries the escape clause "either `𝓡 = ℂ1` or `𝓡` is a
type III₁ factor", and a reflexive proper containment is rejected precisely because it would force
every local algebra to be type I. These witnesses show the interfaces are inhabited and applicable;
they are **not** evidence about nets whose local algebras are type III₁, and no argument should
treat them as such. The degeneracy is also forced rather than chosen at the C⋆ level: over
`Finset ℤ` with `⟂ = Disjoint`, any two disjoint regions lie under their union, so locality makes
every *constant* net commutative — a noncommutative witness needs the tensor-product net descoped
above.

**Finite versus infinite regions.** Even a genuine spin net would make the split property on
`Finset ℤ` say nothing: every finite-region algebra is then a finite-dimensional factor, and every
inclusion between such factors splits. The property has content only on infinite regions, which
`QuantumSystem.Algebra.LocalNet.InfiniteRegion` makes expressible and the `halfChain` witnesses
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

/-- The **trivial local net** over the integer chain: every region carries the C⋆-algebra `ℂ`, and
    every isotony embedding is the identity. Locality holds because `ℂ` is commutative, and is
    supplied only for the join region `Λ₁ ∪ Λ₂` — the smart constructor `LocalNet.mk'` pushes it
    forward to every common superregion. -/
noncomputable def trivialNet : LocalNet (Finset ℤ) :=
  LocalNet.mk' (fun _ : Finset ℤ => ℂ) (fun _ => StarAlgHom.id ℂ ℂ) (fun _ => rfl)
    (fun _ _ _ => rfl) (fun _ x y => mul_comm x y)

/-- The trivial net is faithful: its isotony embeddings are identities. -/
instance : trivialNet.Faithful where
  incl_injective _ := fun _ _ h => h

/-! ### A covariance moving the regions -/

/-- **The unit translation of the integer chain**, as a covariance of the trivial net: the site
    permutation `x ↦ x + 1` induces the region automorphism `Λ ↦ Λ + 1`, and every local algebra
    being `ℂ` the covariance `*`-isomorphisms are identities.

    This is the witness that makes the covariance API testable. `LocalNet.Covariance.id` inhabits
    the structure, but at the identity region map every naturality square of `Covariance` closes by
    `rfl` and `Covariance.sitePerm`, `Covariance.exists_sitePerm` and
    `Covariance.exists_eq_ofSitePerm` all speak about the trivial permutation. Here the region map
    genuinely moves (`σ_shiftCovariance`), so those statements have content. -/
noncomputable def shiftCovariance : trivialNet.Covariance :=
  LocalNet.Covariance.ofSitePerm (N := trivialNet) (Equiv.addRight (1 : ℤ))
    (fun _ => StarAlgEquiv.refl ℂ _) (fun _ _ => rfl)

/-- **The unit translation moves regions**: it carries the site `0` to the site `1`. So
    `shiftCovariance` is not the identity covariance, and the site permutation recovered from it by
    `LocalNet.Covariance.exists_sitePerm` is not the identity permutation. -/
@[simp] lemma σ_shiftCovariance : shiftCovariance.σ ({0} : Finset ℤ) = {1} := rfl

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
    inclusion split. This keeps `VonNeumannNet.IsSplitPair` at Matsui's pair from being automatic. -/
theorem not_isSplitPair_diagonalNet_extend :
    ¬ diagonalNet.extend.IsSplitPair (Set.Iic 0) (Set.Ici 1) := fun h => by
  rw [VonNeumannNet.IsSplitPair, diagonalNet_extend_algebra, diagonalNet_extend_algebra,
    VonNeumannAlgebra.commutant_multiplicationAlgebra] at h
  exact VonNeumannAlgebra.not_isSplitInclusion_multiplicationAlgebra_count h

/-- **The extended constant net at `𝓑(ℂ)` has the infinite-region split property.** Evidence of
    inhabitation only: it is an instance of `VonNeumannNet.splitProperty_of_complex`, and on `ℂ`
    every net splits. A non-trivial positive model needs a spin net, which is not built here. -/
theorem scalarNet_extend_splitProperty : scalarNet.extend.SplitProperty :=
  VonNeumannNet.splitProperty_of_complex _

/-- **Every pair of regions splits for the extended constant net at `𝓑(ℂ)`**, in particular
    Matsui's gap-free half-chain pair. Evidence of inhabitation only: on `ℂ` every von Neumann
    algebra, commutants included, is `𝓑(ℂ)`. -/
theorem scalarNet_extend_isSplitPair (S₁ S₂ : Set ℤ) : scalarNet.extend.IsSplitPair S₁ S₂ := by
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
theorem trivialNet_splitProperty : trivialNet.SplitProperty zeroRep :=
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
  DirectLimit.Ring.lift trivialNet.algebra (fun _ _ h => trivialNet.incl h) ℂ
    (fun _ => RingHom.id ℂ) (fun _ _ _ _ => rfl)

/-- Evaluation reads off the component of a local observable. -/
@[simp] lemma evalLocal_mk (O : Finset ℤ) (x : ℂ) :
    evalLocal (⟦⟨O, x⟩⟧ : trivialNet.localObservables) = x := rfl

/-- Evaluation preserves the involution: the involution of the limit acts componentwise, and on
    `ℂ` it is complex conjugation on both sides. -/
lemma evalLocal_star (z : trivialNet.localObservables) :
    evalLocal (star z) = star (evalLocal z) := by
  induction z using DirectLimit.induction with
  | _ O X => rw [LocalNet.star_mk]; rfl

/-- Evaluation is `ℂ`-linear: scalars act componentwise on the limit. -/
lemma evalLocal_smul (c : ℂ) (z : trivialNet.localObservables) :
    evalLocal (c • z) = c • evalLocal z := by
  induction z using DirectLimit.induction with
  | _ O X => rw [DirectLimit.smul_def]; rfl

/-- **Evaluation is isometric**: the C⋆-norm of the limit is the norm of the component. -/
lemma norm_evalLocal (z : trivialNet.localObservables) : ‖evalLocal z‖ = ‖z‖ := by
  induction z using DirectLimit.induction with
  | _ O X => rw [LocalNet.norm_mk]; rfl

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
theorem unitalRep_splitProperty : trivialNet.SplitProperty unitalRep :=
  VonNeumannNet.splitProperty_of_complex (trivialNet.vonNeumannNet unitalRep)

/-! ### Matsui's half-chain split property for a state

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

/-- **The evaluation state has Matsui's half-chain split property.** It is multiplicative, so this
    is an instance of `LocalNet.IsSplitPairAt.of_map_mul`; it shows `LocalNet.HasHalfChainSplit` is
    inhabited, and nothing about states whose GNS algebras are not scalar. -/
theorem evalState_hasHalfChainSplit : trivialNet.HasHalfChainSplit evalState :=
  LocalNet.IsSplitPairAt.of_map_mul _ (fun a b => map_mul evalQuasiLocal a b) _ _

end HalfChainState

section SpectralOrder

attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

/-- **The evaluation state at the canonical order has the half-chain split property**: the
    order hypotheses of `evalState_hasHalfChainSplit` are satisfiable, and are discharged here by
    the spectral order of the quasi-local C⋆-algebra (`CStarAlgebra.spectralOrder`), so
    `LocalNet.HasHalfChainSplit` is inhabited outright. -/
theorem evalState_hasHalfChainSplit_spectralOrder : trivialNet.HasHalfChainSplit evalState :=
  evalState_hasHalfChainSplit

end SpectralOrder

end LocalNet.Examples
