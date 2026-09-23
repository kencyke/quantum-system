module

public import QuantumSystem.Algebra.LocalNet.SplitProperty

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
  `nbhd` enlarges in both directions, so the collar `Λ₂ \ nbhd Λ₁` can touch `Λ₁` from neither side
  and *touching* pairs are excluded. Strict enlargement alone would not do this — see the docstring
  of `ProperContainment.ofThicken`, and `ProperContainment.ofSSubset` for the degenerate model the
  class axioms admit. `ProperContainment.properlyContained_singleton` exhibits an actual pair, so
  `⋐` is not empty and the split property below is not vacuously true.
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
* **A refuter.** All the witnesses here inhabit the *positive* side of the interfaces; the negation
  of `IsSplitInclusion` is kept inhabited by `VonNeumannAlgebra.not_isSplitInclusion_diagonalAlgebra`
  (in `QuantumSystem.Algebra.VonNeumannAlgebra.SplitInclusion`, next to the predicate it refutes).

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

/-- The 1-neighbourhood **strictly** enlarges every nonempty region: it adds the site just above
    the largest one. This is the hypothesis `ProperContainment.ofThicken` needs. -/
lemma ssubset_nbhd (Λ : Finset ℤ) (hne : Λ.Nonempty) : Λ ⊂ nbhd Λ := by
  refine (Finset.ssubset_iff_of_subset (subset_nbhd Λ)).2 ⟨Λ.max' hne + 1, ?_, ?_⟩
  · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨Λ.max' hne, Λ.max'_mem hne, rfl⟩)
  · exact fun hmem => absurd (Λ.le_max' _ hmem) (by omega)

/-- **The 1-neighbourhood absorbs both neighbours of every site of the region.** This — and not
    the strict enlargement `ssubset_nbhd` — is what makes the induced proper containment
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
    sides (`add_mem_nbhd_of_mem`), so touching pairs — which the literature excludes, since local
    algebras of touching regions are not statistically independent — do not satisfy this relation.

    Deliberately a `def` rather than a global `instance`: this file is re-exported by the aggregate
    root, so a global instance would silently resolve every downstream `⋐` on `Finset ℤ` to the
    nearest-neighbour relation of this one witness. It is activated by `attribute [local instance]`
    where this file needs it; a model that wants it elsewhere says so, either the same way or by
    rebuilding it from the public `nbhd`, `ssubset_nbhd` and `monotone_nbhd`. -/
@[reducible] noncomputable def integerChain : ProperContainment (Finset ℤ) :=
  ProperContainment.ofThicken nbhd ssubset_nbhd monotone_nbhd

attribute [local instance] integerChain

/-- **`⋐` is inhabited on the integer chain**: the single site `{0}`, whose 1-neighbourhood is
    `{-1, 0, 1}`, is properly contained in `{-2, -1, 0, 1, 2}`. Recorded so that the split property
    over this index set is not vacuously true. -/
lemma properlyContained_singleton : ({0} : Finset ℤ) ⋐ ({-2, -1, 0, 1, 2} : Finset ℤ) := by
  change nbhd {0} ⊂ ({-2, -1, 0, 1, 2} : Finset ℤ)
  decide

end ProperContainment

namespace LocalNet.Examples

attribute [local instance] ProperContainment.integerChain

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
    (fun _ => StarAlgEquiv.refl) (fun _ _ => rfl)

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
  | _ O X => rw [LocalNet.star_mk, evalLocal_mk, evalLocal_mk]; rfl

/-- Evaluation is `ℂ`-linear: scalars act componentwise on the limit. -/
lemma evalLocal_smul (c : ℂ) (z : trivialNet.localObservables) :
    evalLocal (c • z) = c • evalLocal z := by
  induction z using DirectLimit.induction with
  | _ O X => rw [DirectLimit.smul_def, evalLocal_mk, evalLocal_mk]; rfl

/-- **Evaluation is isometric**: the C⋆-norm of the limit is the norm of the component. -/
lemma norm_evalLocal (z : trivialNet.localObservables) : ‖evalLocal z‖ = ‖z‖ := by
  induction z using DirectLimit.induction with
  | _ O X => rw [evalLocal_mk, LocalNet.norm_mk]; rfl

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

end LocalNet.Examples
