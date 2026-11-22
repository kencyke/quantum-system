/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.ForMathlib.Analysis.Normed.Group.DirectLimit
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.Completion
public import QuantumSystem.Analysis.CStarAlgebra.StarAlgEquiv
public import QuantumSystem.Physics.LocalNet.Covariance

/-!
# The quasi-local algebra of a local net

The **algebra of local observables** and the **quasi-local C⋆-algebra** of an abstract local net
`LocalNet`. These constructions apply to any local net over a *directed* causal index set
(`IsDirectedOrder`, with a region to start from, `Nonempty`): directedness is what makes the
union of the local algebras an algebra. Lattice nets (`K = Finset sites`) are directed by unions
with the empty region as base point.

* `GradedLocalNet.localObservables` is the algebraic inductive limit `⋃_O 𝔄(O)` of the local algebras
  along the isotony embeddings, with cocone `ιLocal`, exhaustion (`exists_ιLocal`) and locality
  (`ιLocal_commute_of_orthogonal`); the cocone is injective for a `Faithful` net
  (`ιLocal_injective`).
* For a `Faithful` net the connecting maps are isometric, so the algebra of local observables
  carries a C⋆-norm whose completion `GradedLocalNet.quasiLocalCStarAlgebra` is the AQFT quasi-local
  algebra `𝔄 = ‾⋃_O 𝔄(O)` (Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §1.3), with
  isometric local embeddings `ιLocalCStar` — unital `*`-homomorphisms `𝔄(O) →⋆ₐ[ℂ] 𝔄`, injective
  and with *closed* range, whose ranges are dense
  in `𝔄` only taken together (`denseRange_iUnion_ιLocalCStar`).

A `GradedLocalNet.Covariance` (defined in `QuantumSystem.Physics.LocalNet.Covariance`) acts on these
algebras: its per-region `*`-isomorphisms assemble into a ring endomorphism
`localObservableCovariance` of the algebra of local observables, which is functorial and is shown
`ℂ`-linear and `*`-preserving — hence bundled as a `*`-automorphism
`localObservableCovarianceEquiv`, assembled into a group homomorphism
`localObservableCovarianceHom`. For a `Faithful` net it is isometric and extends to a
`*`-automorphism `quasiLocalCStarCovarianceEquiv` of the quasi-local C⋆-algebra, assembled into
`quasiLocalCStarCovarianceHom`. A monoid `G` with a topology acting through `φ : G →* N.Covariance`
acts on the quasi-local C⋆-algebra as a C⋆-dynamical system `G →ₜ* (𝔄 ≃⋆ₐ[ℂ] 𝔄)`
(`quasiLocalCStarDynamicalSystem`) when the action is continuous in the point-norm topology, which
is checked on local observables (`continuous_quasiLocalCStarCovarianceHom_comp_iff`) and holds for
every `φ` when `G` is discrete. The covariances carry no topology of their own.

Everything here is stated for graded-local nets (`GradedLocalNet`), whose isotony embeddings are
all the construction uses. Graded locality passes to the quasi-local algebra: even local observables
of causally orthogonal regions commute with everything
(`ιLocalCStar_commute_of_orthogonal_of_even`), odd ones anticommute
(`ιLocalCStar_mul_eq_neg_of_orthogonal_of_odd`); for a `LocalNet` this is commutation
(`LocalNet.ιLocalCStar_commute_of_orthogonal`). The parities of the local algebras assemble into the
parity automorphism `GradedLocalNet.quasiLocalParity` of the quasi-local C⋆-algebra, an involution;
its fixed points, the even part, are in `QuantumSystem.Physics.LocalNet.Graded`.

## Notation

`𝔄(O)` and `𝓡(O)` in the prose above are documentation shorthand for the local C⋆-algebra
`N.algebra O` and the local von Neumann algebra `N.localVonNeumannAlgebra R O`; the convention —
and why neither is a Lean notation — is stated in full in `QuantumSystem.Physics.LocalNet.Basic`.
-/

@[expose] public section

namespace GradedLocalNet

open scoped CausalOrthogonality

variable {K : Type*} [Preorder K] [CausalOrthogonality K] [IsDirectedOrder K] [Nonempty K]
variable (N : GradedLocalNet K)

/-! ### Algebra of local observables

These constructions apply to any abstract local net over a directed causal index set.
-/

/-- The **algebra of local observables** of the net: the algebraic inductive limit of the local
    algebras along the isotony embeddings. Its C⋆-completion is the quasi-local algebra. -/
noncomputable abbrev localObservables : Type _ :=
  NormedDirectLimit N.algebra (fun _ _ h => N.incl h)

omit [Nonempty K] in
/-- Componentwise behaviour of the involution on the algebra of local observables. The
    `Star`, `StarRing`, `Algebra ℂ` and `StarModule ℂ` instances come from the general
    direct-limit constructions, since each `algebra O` is a `ℂ`-`*`-algebra and `incl` is a
    `*`-algebra homomorphism. -/
@[simp] lemma star_mk {O : K} (X : N.algebra O) :
    star (NormedDirectLimit.mk O X : N.localObservables) = NormedDirectLimit.mk O (star X) :=
  (NormedDirectLimit.mk_star O X).symm

/-- The canonical map `𝔄(O) → 𝔄_loc` of a local algebra into the algebra of local observables, as
    a unital ring homomorphism (the cocone of the inductive limit). It need not be injective: an
    isotony map that kills `X` makes `X` vanish in the limit. For a `Faithful` net it is
    (`ιLocal_injective`). -/
noncomputable def ιLocal (O : K) :
    N.algebra O →+* N.localObservables :=
  (NormedDirectLimit.ofAlgHom ℂ O).toRingHom

/-- The cocone takes the class of a local observable. -/
lemma ιLocal_apply (O : K) (X : N.algebra O) : N.ιLocal O X = NormedDirectLimit.mk O X :=
  rfl

/-- Compatibility of the cocone with the isotony embeddings: including `X` from `O` into the
    larger region `O'` and then into `𝔄_loc` is the same as including `X` directly. -/
@[simp] lemma ιLocal_incl {O O' : K} (h : O ≤ O') (X : N.algebra O) :
    N.ιLocal O' (N.incl h X) = N.ιLocal O X :=
  NormedDirectLimit.mk_map (G := N.algebra) (f := fun _ _ h => N.incl h) O O' h X

/-- The cocone is a `*`-homomorphism: it intertwines the local and quasi-local involutions. -/
@[simp] lemma ιLocal_star {O : K} (X : N.algebra O) :
    N.ιLocal O (star X) = star (N.ιLocal O X) :=
  (star_mk (N := N) X).symm

/-- The cocone is `ℂ`-linear: scalars act componentwise on the inductive limit. -/
@[simp] lemma ιLocal_smul (c : ℂ) {O : K} (X : N.algebra O) :
    N.ιLocal O (c • X) = c • N.ιLocal O X :=
  NormedDirectLimit.mk_smul O c X

/-- The cocone of the inductive limit absorbs the region-equality transport. -/
@[simp] lemma ιLocal_algebraCongr {O O' : K} (h : O = O') (x : N.algebra O) :
    N.ιLocal O' (N.algebraCongr h x) = N.ιLocal O x := by
  subst h; rfl

/-- **Exhaustion**: every element of the algebra of local observables is the image of a local
    observable from some region — the union of the local algebras is the whole limit. -/
lemma exists_ιLocal (z : N.localObservables) :
    ∃ (O : K) (X : N.algebra O), z = N.ιLocal O X := by
  induction z using NormedDirectLimit.induction with
  | _ O X => exact ⟨O, X, rfl⟩

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

/-! ### Faithful nets and the quasi-local C⋆-algebra

For a faithful net the connecting maps are isometric, so the algebra of local observables carries
a C⋆-norm whose completion is the quasi-local C⋆-algebra `𝔄 = ‾⋃_O 𝔄(O)`.
-/

section CStar

variable [N.Faithful]

/-- For a faithful net the cocone `ιLocal O : 𝔄(O) → 𝔄_loc` is injective: two local observables
    identified in the limit already agree in some larger region, where the isotony embedding is
    injective. -/
lemma ιLocal_injective (O : K) : Function.Injective (N.ιLocal O) :=
  DirectLimit.mk_injective _ (fun _ _ h => Faithful.incl_injective h) O

/-- The isotony embeddings of a faithful net are isometric, being injective `*`-homomorphisms of
    C⋆-algebras. The algebra of local observables therefore carries the norm of the normed direct
    limit — a normed `ℂ`-algebra, a normed `*`-group and a C⋆-ring. -/
instance : DirectLimit.IsometricSystem (G := N.algebra) (fun _ _ h => N.incl h) :=
  .of_injective fun _ _ h => Faithful.incl_injective h

/-- The C⋆-norm of a local observable, viewed in the algebra of local observables, is its norm in
    its own region's algebra: the connecting maps are isometric. -/
@[simp] lemma norm_mk {O : K} (X : N.algebra O) :
    ‖(NormedDirectLimit.mk O X : N.localObservables)‖ = ‖X‖ := rfl

/-- The **quasi-local C⋆-algebra** of a faithful net: the completion of the algebra of local
    observables. This is the AQFT quasi-local algebra `𝔄 = ‾⋃_O 𝔄(O)`. -/
noncomputable abbrev quasiLocalCStarAlgebra : Type _ :=
  UniformSpace.Completion N.localObservables

/-- The quasi-local algebra is a C⋆-algebra, by the completion instances. Recorded as a shortcut
    instance: deriving it through the completion each time is expensive enough to exhaust the
    instance-search budget inside larger searches, e.g. the operator ring of the conjugated
    representation `(R.conjBy U).H →L[ℂ] (R.conjBy U).H` of a representation of `𝔄`. -/
noncomputable instance : CStarAlgebra N.quasiLocalCStarAlgebra := inferInstance

/-- The canonical **local embedding** `𝔄(O) → 𝔄` of a local algebra into the quasi-local
    C⋆-algebra: the completion coercion composed with the inductive-limit cocone, bundled as a
    unital `*`-homomorphism of `ℂ`-algebras. It is isometric (`norm_ιLocalCStar`) and therefore
    injective (`ιLocalCStar_injective`), so each `𝔄(O)` sits in `𝔄` as an isomorphic copy — the
    non-degeneracy the AQFT literature builds into its net axioms, here inherited from `Faithful`.

    A *single* such range is not dense: an isometric image of a complete space is complete, hence
    closed, so it is dense only when it is all of `𝔄`. What is dense is the union over all regions
    (`denseRange_iUnion_ιLocalCStar`), which is the `‾⋃_O 𝔄(O)` of the literature. -/
noncomputable def ιLocalCStar (O : K) :
    N.algebra O →⋆ₐ[ℂ] N.quasiLocalCStarAlgebra where
  toFun := (↑) ∘ N.ιLocal O
  map_one' := by simp
  map_mul' X Y := by
    simp only [Function.comp_apply, map_mul, UniformSpace.Completion.coe_mul]
  map_zero' := by simp
  map_add' X Y := by
    simp only [Function.comp_apply, map_add, UniformSpace.Completion.coe_add]
  commutes' c := by
    simp only [Function.comp_apply, Algebra.algebraMap_eq_smul_one, N.ιLocal_smul, map_one,
      UniformSpace.Completion.coe_smul, UniformSpace.Completion.coe_one]
  map_star' X := by
    simp only [Function.comp_apply, ιLocal_star, UniformSpace.Completion.star_coe]

/-- The local embedding is the completion coercion after the inductive-limit cocone. -/
lemma coe_ιLocalCStar (O : K) : ⇑(N.ιLocalCStar O) = (↑) ∘ N.ιLocal O := rfl

/-- The local embedding is compatible with the isotony embeddings: including into a larger
    region first does not change the image in the quasi-local C⋆-algebra. -/
@[simp] lemma ιLocalCStar_incl {O O' : K} (h : O ≤ O') (X : N.algebra O) :
    N.ιLocalCStar O' (N.incl h X) = N.ιLocalCStar O X := by
  simp only [coe_ιLocalCStar, Function.comp_apply, ιLocal_incl]

/-- The local embedding is a `*`-map: it intertwines the local and quasi-local involutions. -/
@[simp] lemma ιLocalCStar_star {O : K} (X : N.algebra O) :
    N.ιLocalCStar O (star X) = star (N.ιLocalCStar O X) :=
  map_star _ X

/-- **The local embedding is isometric**: the connecting maps of a faithful net are isometric, so
    the C⋆-norm of `𝔄(O)` is the one it inherits from the quasi-local algebra. -/
@[simp] lemma norm_ιLocalCStar {O : K} (X : N.algebra O) :
    ‖N.ιLocalCStar O X‖ = ‖X‖ := by
  rw [coe_ιLocalCStar, Function.comp_apply, UniformSpace.Completion.norm_coe]
  exact N.norm_mk X

/-- The local embedding is an isometry (bundled form of `norm_ιLocalCStar`). -/
lemma isometry_ιLocalCStar (O : K) : Isometry (N.ιLocalCStar O) :=
  AddMonoidHomClass.isometry_of_norm _ (N.norm_ιLocalCStar (O := O))

/-- **The local embedding is injective**: it is isometric, so it is an embedding of `𝔄(O)` onto a
    closed C⋆-subalgebra of the quasi-local algebra. -/
lemma ιLocalCStar_injective (O : K) : Function.Injective (N.ιLocalCStar O) :=
  (N.isometry_ιLocalCStar O).injective

/-- The local algebras are dense in the quasi-local C⋆-algebra: every element is a norm-limit of
    local observables. Note the union: a single local algebra has *closed*, not dense, image
    (`isometry_ιLocalCStar`). -/
theorem denseRange_iUnion_ιLocalCStar :
    Dense (⋃ O : K, Set.range (N.ιLocalCStar O)) :=
  NormedDirectLimit.dense_iUnion_range_coe_mk (G := N.algebra) (f := fun _ _ h => N.incl h)

/-- **Graded locality in the quasi-local C⋆-algebra**, even elements: an even observable
    localised in a region commutes inside `𝔄` with every observable localised in a causally
    orthogonal region. -/
theorem ιLocalCStar_commute_of_orthogonal_of_even {O₁ O₂ : K} (hd : O₁ ⟂ O₂)
    (X : N.algebra O₁) (Y : N.algebra O₂) (hX : N.parity O₁ X = X) :
    Commute (N.ιLocalCStar O₁ X) (N.ιLocalCStar O₂ Y) :=
  (N.ιLocal_commute_of_orthogonal_of_even hd X Y hX).map UniformSpace.Completion.coeRingHom

/-- **Graded locality in the quasi-local C⋆-algebra**, odd elements: odd observables localised in
    causally orthogonal regions anticommute inside `𝔄`. -/
theorem ιLocalCStar_mul_eq_neg_of_orthogonal_of_odd {O₁ O₂ : K} (hd : O₁ ⟂ O₂)
    (X : N.algebra O₁) (Y : N.algebra O₂) (hX : N.parity O₁ X = -X) (hY : N.parity O₂ Y = -Y) :
    N.ιLocalCStar O₁ X * N.ιLocalCStar O₂ Y = -(N.ιLocalCStar O₂ Y * N.ιLocalCStar O₁ X) := by
  have h := congrArg (UniformSpace.Completion.coeRingHom (α := N.localObservables))
    (N.ιLocal_mul_eq_neg_of_orthogonal_of_odd hd X Y hX hY)
  rw [map_mul, map_neg, map_mul] at h
  exact h

end CStar

namespace Covariance

variable {N} (a : N.Covariance)

/-! ### The induced covariance action -/

/-- The **covariance action** `β_a ⟦⟨O, X⟩⟧ = ⟦⟨σO, β_O X⟩⟧` of a covariance on the algebra of local
    observables, as a ring homomorphism. Well-defined by naturality (`β_incl`). -/
noncomputable def localObservableCovariance : N.localObservables →+* N.localObservables :=
  NormedDirectLimit.liftRingHom
    (fun O => (N.ιLocal (a.σ O)).comp (a.β O).toAlgEquiv.toAlgHom.toRingHom)
    (fun O O' h X => by
      change N.ιLocal (a.σ O') (a.β O' (N.incl h X)) = N.ιLocal (a.σ O) (a.β O X)
      rw [a.β_incl h]
      exact N.ιLocal_incl _ _)

/-- Componentwise formula for the covariance action: `β_a ⟦⟨O, X⟩⟧ = ⟦⟨σO, β_O X⟩⟧`. -/
@[simp] lemma localObservableCovariance_mk {O : K} (X : N.algebra O) :
  a.localObservableCovariance (NormedDirectLimit.mk O X : N.localObservables) =
    NormedDirectLimit.mk (a.σ O) (a.β O X) :=
  rfl

/-- The covariance action of the identity covariance is the identity: `β_{id} = id`. -/
@[simp] lemma localObservableCovariance_id :
  (Covariance.id N).localObservableCovariance = RingHom.id N.localObservables := by
  refine RingHom.ext fun z => ?_
  induction z using NormedDirectLimit.induction with
  | _ O X => rw [localObservableCovariance_mk, RingHom.id_apply]; rfl

/-- **Functoriality of the covariance action**: composing covariances composes their actions,
    `β_{a∘b} = β_a ∘ β_b`. -/
@[simp] lemma localObservableCovariance_comp (a b : N.Covariance) :
  (a.comp b).localObservableCovariance = a.localObservableCovariance.comp b.localObservableCovariance := by
  refine RingHom.ext fun z => ?_
  induction z using NormedDirectLimit.induction with
  | _ O X =>
    simp only [RingHom.comp_apply, localObservableCovariance_mk]
    rfl

/-- The covariance action sends the unit covariance to the identity: `β_1 = id`. -/
@[simp] lemma localObservableCovariance_one :
    (1 : N.Covariance).localObservableCovariance = RingHom.id N.localObservables := by
  rw [one_def, localObservableCovariance_id]

/-- The covariance action is multiplicative: `β_{a·b} = β_a ∘ β_b`. -/
lemma localObservableCovariance_mul (a b : N.Covariance) :
    (a * b).localObservableCovariance = a.localObservableCovariance.comp b.localObservableCovariance := by
  rw [mul_def, localObservableCovariance_comp]

/-! #### The covariance action as a `*`-automorphism -/

/-- The covariance action is `ℂ`-linear: `β_a (c • z) = c • β_a z`, since each `β` is. -/
lemma localObservableCovariance_smul (c : ℂ) (z : N.localObservables) :
  a.localObservableCovariance (c • z) = c • a.localObservableCovariance z := by
  induction z using NormedDirectLimit.induction with
  | _ O X =>
    rw [← NormedDirectLimit.mk_smul, localObservableCovariance_mk, localObservableCovariance_mk,
      ← NormedDirectLimit.mk_smul, map_smul]

/-- The covariance action preserves the involution: `β_a (star z) = star (β_a z)`, since each `β`
    is a `*`-isomorphism. -/
lemma localObservableCovariance_star (z : N.localObservables) :
  a.localObservableCovariance (star z) = star (a.localObservableCovariance z) := by
  induction z using NormedDirectLimit.induction with
  | _ O X =>
    rw [star_mk, localObservableCovariance_mk, localObservableCovariance_mk, star_mk, map_star]

/-- The covariance action as a `*`-algebra automorphism of the algebra of local observables, with
  the action of the inverse covariance `a⁻¹` as its inverse. -/
noncomputable def localObservableCovarianceEquiv :
    N.localObservables ≃⋆ₐ[ℂ] N.localObservables where
  toFun := a.localObservableCovariance
  invFun := a⁻¹.localObservableCovariance
  left_inv z := by
    rw [← RingHom.comp_apply, ← localObservableCovariance_mul, inv_mul_cancel, localObservableCovariance_one,
      RingHom.id_apply]
  right_inv z := by
    rw [← RingHom.comp_apply, ← localObservableCovariance_mul, mul_inv_cancel, localObservableCovariance_one,
      RingHom.id_apply]
  map_mul' := map_mul a.localObservableCovariance
  map_add' := map_add a.localObservableCovariance
  map_smul' := a.localObservableCovariance_smul
  map_star' := a.localObservableCovariance_star

/-- The bundled `*`-automorphism agrees with the underlying ring homomorphism. -/
@[simp] lemma localObservableCovarianceEquiv_apply (z : N.localObservables) :
    a.localObservableCovarianceEquiv z = a.localObservableCovariance z := rfl

/-- The inverse of the bundled `*`-automorphism is the action of the inverse covariance. -/
@[simp] lemma localObservableCovarianceEquiv_symm_apply (z : N.localObservables) :
    a.localObservableCovarianceEquiv.symm z = a⁻¹.localObservableCovariance z := rfl

/-- A covariance of the net acts on the algebra of local observables by `*`-algebra automorphisms,
    assembled as a group homomorphism into the `*`-automorphism group. -/
noncomputable def localObservableCovarianceHom :
    N.Covariance →* (N.localObservables ≃⋆ₐ[ℂ] N.localObservables) where
  toFun a := a.localObservableCovarianceEquiv
  map_one' := by
    ext z
    simp only [localObservableCovarianceEquiv_apply, localObservableCovariance_one, RingHom.id_apply,
      StarAlgEquiv.one_apply]
  map_mul' a b := by
    ext z
    simp only [localObservableCovarianceEquiv_apply, localObservableCovariance_mul, RingHom.comp_apply,
      StarAlgEquiv.mul_apply]

/-- The group homomorphism evaluates to the covariance action. -/
@[simp] lemma localObservableCovarianceHom_apply (z : N.localObservables) :
    localObservableCovarianceHom a z = a.localObservableCovariance z := rfl

/-! #### The covariance automorphism of the quasi-local C⋆-algebra -/

section CStarCovariance

variable [N.Faithful]

/-- The covariance action is **isometric** on the algebra of local observables: each `β` is a
    `*`-isomorphism of C⋆-algebras, hence norm-preserving. -/
lemma localObservableCovariance_norm (z : N.localObservables) :
  ‖a.localObservableCovariance z‖ = ‖z‖ := by
  induction z using NormedDirectLimit.induction with
  | _ O X =>
    rw [localObservableCovariance_mk, norm_mk, norm_mk]
    exact StarAlgEquiv.norm_map _ X

/-- The covariance automorphism of the algebra of local observables is uniformly continuous (it is
    an isometry), so it extends to the C⋆-completion. -/
lemma localObservableCovarianceEquiv_uniformContinuous :
    UniformContinuous a.localObservableCovarianceEquiv :=
  (AddMonoidHomClass.isometry_of_norm _ (fun z => by
    rw [localObservableCovarianceEquiv_apply]; exact a.localObservableCovariance_norm z)).uniformContinuous

/-- The inverse covariance automorphism is uniformly continuous as well (the action of `a⁻¹` is
    also an isometry). -/
lemma localObservableCovarianceEquiv_symm_uniformContinuous :
    UniformContinuous a.localObservableCovarianceEquiv.symm := by
  have h : ∀ z, ‖a.localObservableCovarianceEquiv.symm z‖ = ‖z‖ := fun z => by
    rw [localObservableCovarianceEquiv_symm_apply]; exact a⁻¹.localObservableCovariance_norm z
  exact (AddMonoidHomClass.isometry_of_norm _ h).uniformContinuous

/-- The covariance automorphism of the quasi-local C⋆-algebra: the continuous extension of
    `localObservableCovarianceEquiv` to the completion. -/
noncomputable def quasiLocalCStarCovarianceEquiv :
    N.quasiLocalCStarAlgebra ≃⋆ₐ[ℂ] N.quasiLocalCStarAlgebra :=
  UniformSpace.Completion.mapStarAlgEquiv a.localObservableCovarianceEquiv
    a.localObservableCovarianceEquiv_uniformContinuous
    a.localObservableCovarianceEquiv_symm_uniformContinuous

/-- On local observables the extension to the completion agrees with the covariance action they
    already carry. -/
@[simp] lemma quasiLocalCStarCovarianceEquiv_coe (z : N.localObservables) :
    a.quasiLocalCStarCovarianceEquiv (↑z : N.quasiLocalCStarAlgebra) =
      ↑(a.localObservableCovariance z) :=
  UniformSpace.Completion.mapStarAlgEquiv_coe _ _ _ z

/-- The covariance automorphism of the quasi-local C⋆-algebra is continuous, being the continuous
    extension of an isometry to the completion. -/
lemma quasiLocalCStarCovarianceEquiv_continuous :
    Continuous (⇑a.quasiLocalCStarCovarianceEquiv) :=
  UniformSpace.Completion.continuous_map

/-- A covariance of a faithful net acts on the quasi-local C⋆-algebra by `*`-automorphisms,
    assembled as a group homomorphism into the `*`-automorphism group. -/
noncomputable def quasiLocalCStarCovarianceHom :
    N.Covariance →* (N.quasiLocalCStarAlgebra ≃⋆ₐ[ℂ] N.quasiLocalCStarAlgebra) where
  toFun a := a.quasiLocalCStarCovarianceEquiv
  map_one' := by
    refine StarAlgEquiv.ext fun z => ?_
    rw [StarAlgEquiv.one_apply]
    refine UniformSpace.Completion.induction_on z
      (isClosed_eq (1 : N.Covariance).quasiLocalCStarCovarianceEquiv_continuous
        continuous_id) ?_
    intro w
    simp only [quasiLocalCStarCovarianceEquiv_coe, localObservableCovariance_one, RingHom.id_apply]
  map_mul' a b := by
    refine StarAlgEquiv.ext fun z => ?_
    rw [StarAlgEquiv.mul_apply]
    refine UniformSpace.Completion.induction_on z
      (isClosed_eq (a * b).quasiLocalCStarCovarianceEquiv_continuous
        (a.quasiLocalCStarCovarianceEquiv_continuous.comp
          b.quasiLocalCStarCovarianceEquiv_continuous)) ?_
    intro w
    simp only [quasiLocalCStarCovarianceEquiv_coe, localObservableCovariance_mul, RingHom.comp_apply]

/-- The group homomorphism evaluates to the covariance automorphism of the quasi-local
    C⋆-algebra. -/
@[simp] lemma quasiLocalCStarCovarianceHom_apply
    (z : N.quasiLocalCStarAlgebra) :
  quasiLocalCStarCovarianceHom a z = a.quasiLocalCStarCovarianceEquiv z := rfl

/-- The covariance automorphism of the quasi-local C⋆-algebra on a local observable:
    `β_a (ι_O X) = ι_{σO} (β_O X)`. -/
@[simp] lemma quasiLocalCStarCovarianceEquiv_ιLocalCStar (O : K) (X : N.algebra O) :
    a.quasiLocalCStarCovarianceEquiv (N.ιLocalCStar O X) = N.ιLocalCStar (a.σ O) (a.β O X) :=
  a.quasiLocalCStarCovarianceEquiv_coe (N.ιLocal O X)

/-- **Continuity of a family of covariances is checked on local observables**: a map `f` into the
    covariances acts continuously on the quasi-local C⋆-algebra in the point-norm topology iff
    `y ↦ ι_{σ_y O} (β_{y,O} X)` is continuous for every region `O` and every local observable
    `X ∈ 𝔄(O)`. The local algebras are dense (`denseRange_iUnion_ιLocalCStar`) and the covariance
    automorphisms are isometric, so `StarAlgEquiv.continuous_of_dense` applies. -/
theorem continuous_quasiLocalCStarCovarianceHom_comp_iff {X : Type*} [TopologicalSpace X]
    {f : X → N.Covariance} :
    Continuous (fun y => quasiLocalCStarCovarianceHom (f y)) ↔
      ∀ (O : K) (x : N.algebra O), Continuous fun y => N.ιLocalCStar ((f y).σ O) ((f y).β O x) := by
  refine ⟨fun h O x => ?_, fun h => ?_⟩
  · simpa using StarAlgEquiv.continuous_iff.mp h (N.ιLocalCStar O x)
  · refine StarAlgEquiv.continuous_of_dense N.denseRange_iUnion_ιLocalCStar fun z hz => ?_
    obtain ⟨O, x, rfl⟩ := Set.mem_iUnion.mp hz
    simpa using h O x

variable {G : Type*} [Monoid G] [TopologicalSpace G]

/-- A symmetry group (or monoid) `G` of a faithful net, acting through `φ : G →* N.Covariance`
    **continuously** — `g ↦ β_{φ g} z` is norm-continuous for every `z` in the quasi-local
    C⋆-algebra, the hypothesis `hφ` — acts on the quasi-local C⋆-algebra as a C⋆-dynamical system:
    the composite of `φ` with `quasiLocalCStarCovarianceHom`. The continuity is a property of the
    action of `G`, whose topology is given; the covariances themselves carry no topology. It is
    checked on local observables (`continuous_quasiLocalCStarCovarianceHom_comp_iff`), and holds
    for every `φ` when `G` is discrete (`continuous_of_discreteTopology`). -/
noncomputable def quasiLocalCStarDynamicalSystem (φ : G →* N.Covariance)
    (hφ : Continuous fun g => quasiLocalCStarCovarianceHom (φ g)) :
    G →ₜ* (N.quasiLocalCStarAlgebra ≃⋆ₐ[ℂ] N.quasiLocalCStarAlgebra) :=
  ⟨quasiLocalCStarCovarianceHom.comp φ, hφ⟩

/-- The C⋆-dynamical system of a symmetry group acts by the covariance automorphisms. -/
@[simp] lemma quasiLocalCStarDynamicalSystem_apply (φ : G →* N.Covariance)
    (hφ : Continuous fun g => quasiLocalCStarCovarianceHom (φ g)) (g : G)
    (z : N.quasiLocalCStarAlgebra) :
    quasiLocalCStarDynamicalSystem φ hφ g z = (φ g).quasiLocalCStarCovarianceEquiv z :=
  rfl

end CStarCovariance

end Covariance

/-! ### The parity automorphism of the quasi-local algebra -/

section Parity

variable [N.Faithful]

/-- The **parity automorphism** `Θ` of the quasi-local C⋆-algebra of a faithful graded-local net:
    the automorphism restricting to the parity of every local algebra, obtained as the action of
    the parity covariance (`GradedLocalNet.parityCovariance`). For a `LocalNet` it is the
    identity (`GradedLocalNet.quasiLocalParity_toGradedLocalNet`). -/
noncomputable def quasiLocalParity : N.quasiLocalCStarAlgebra ≃⋆ₐ[ℂ] N.quasiLocalCStarAlgebra :=
  (parityCovariance N).quasiLocalCStarCovarianceEquiv

/-- The quasi-local parity restricts to the parity of each local algebra. -/
@[simp] lemma quasiLocalParity_ιLocalCStar (O : K) (X : N.algebra O) :
    N.quasiLocalParity (N.ιLocalCStar O X) = N.ιLocalCStar O (N.parity O X) :=
  (parityCovariance N).quasiLocalCStarCovarianceEquiv_ιLocalCStar O X

/-- The quasi-local parity is an involution. -/
@[simp] lemma quasiLocalParity_quasiLocalParity (z : N.quasiLocalCStarAlgebra) :
    N.quasiLocalParity (N.quasiLocalParity z) = z := by
  have h := congrArg (fun e : N.quasiLocalCStarAlgebra ≃⋆ₐ[ℂ] N.quasiLocalCStarAlgebra => e z)
    ((map_mul Covariance.quasiLocalCStarCovarianceHom (parityCovariance N)
      (parityCovariance N)).symm.trans (congrArg _ (parityCovariance_mul_self N)))
  rwa [map_one] at h

/-- For a `LocalNet` the quasi-local parity is the identity. -/
lemma quasiLocalParity_toGradedLocalNet (L : LocalNet K) [L.Faithful]
    (z : L.quasiLocalCStarAlgebra) : L.quasiLocalParity z = z := by
  have h := congrArg (fun e : L.quasiLocalCStarAlgebra ≃⋆ₐ[ℂ] L.quasiLocalCStarAlgebra => e z)
    (congrArg Covariance.quasiLocalCStarCovarianceHom (parityCovariance_toGradedLocalNet L))
  rwa [map_one] at h

end Parity

end GradedLocalNet

namespace LocalNet

open scoped CausalOrthogonality

variable {K : Type*} [Preorder K] [CausalOrthogonality K] [IsDirectedOrder K] [Nonempty K]
variable (N : LocalNet K)

/-- **Locality in the algebra of local observables**: observables localised in causally orthogonal
    regions commute inside `𝔄_loc`: graded locality for the trivial parity of a local net. -/
lemma ιLocal_commute_of_orthogonal {O₁ O₂ : K} (hd : O₁ ⟂ O₂)
    (X : N.algebra O₁) (Y : N.algebra O₂) :
    Commute (N.ιLocal O₁ X) (N.ιLocal O₂ Y) :=
  N.ιLocal_commute_of_orthogonal_of_even hd X Y (N.parity_apply X)

/-- **Locality in the quasi-local C⋆-algebra**: observables localised in causally orthogonal
    regions commute inside `𝔄`: graded locality for the trivial parity of a local net. -/
theorem ιLocalCStar_commute_of_orthogonal [N.Faithful] {O₁ O₂ : K} (hd : O₁ ⟂ O₂)
    (X : N.algebra O₁) (Y : N.algebra O₂) :
    Commute (N.ιLocalCStar O₁ X) (N.ιLocalCStar O₂ Y) :=
  N.ιLocalCStar_commute_of_orthogonal_of_even hd X Y (N.parity_apply X)

end LocalNet
