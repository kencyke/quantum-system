module

public import QuantumSystem.Algebra.LocalNet.Covariance
public import QuantumSystem.ForMathlib.Algebra.Colimit.DirectLimitStar
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.DirectLimit
public import QuantumSystem.ForMathlib.Topology.Algebra.CStarCompletion

/-!
# The quasi-local algebra of a local net

The **algebra of local observables** and the **quasi-local C⋆-algebra** of an abstract local net
`LocalNet`. These constructions apply to any local net over a *directed* causal index set
(`IsDirectedOrder`, with a region to start from, `Nonempty`): directedness is what makes the
union of the local algebras an algebra. Lattice nets (`K = Finset sites`) are directed by unions
with the empty region as base point.

* `LocalNet.localObservables` is the algebraic inductive limit `‾⋃_O 𝔄(O)` of the local algebras
  along the isotony embeddings, with cocone `ιLocal`, exhaustion (`exists_ιLocal`) and locality
  (`ιLocal_commute_of_orthogonal`).
* For a `Faithful` net the connecting maps are isometric, so the algebra of local observables
  carries a C⋆-norm whose completion `LocalNet.quasiLocalCStarAlgebra` is the AQFT quasi-local
  algebra `𝔄 = ‾⋃_O 𝔄(O)` (Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §1.3;
  Bratteli–Robinson Vol.2 §6.2), with isometric local embeddings `ιLocalCStar` — unital
  `*`-homomorphisms `𝔄(O) →⋆ₐ[ℂ] 𝔄`, injective and with *closed* range, whose ranges are dense
  in `𝔄` only taken together (`denseRange_iUnion_ιLocalCStar`).

A `LocalNet.Covariance` (defined in `LocalNet.Covariance`) acts on these algebras: its per-region
`*`-isomorphisms assemble into a ring endomorphism `localObservableCovariance` of the algebra of local
observables, which is functorial and is shown `ℂ`-linear and `*`-preserving — hence bundled as a
`*`-automorphism `localObservableCovarianceEquiv`, assembled into a group homomorphism
`localObservableCovarianceHom`. For a `Faithful` net it is isometric and extends to a `*`-automorphism
`quasiLocalCStarCovarianceEquiv` of the quasi-local C⋆-algebra.

## Notation

`𝔄(O)` and `𝓡(O)` in the prose above are documentation shorthand for the local C⋆-algebra
`N.algebra O` and the local von Neumann algebra `N.localVonNeumannAlgebra R O`; the convention —
and why neither is a Lean notation — is stated in full in `QuantumSystem.Algebra.LocalNet.Net`.
-/

@[expose] public section

namespace LocalNet

open scoped CausalOrthogonality

variable {K : Type*} [Preorder K] [CausalOrthogonality K] [IsDirectedOrder K] [Nonempty K]
variable (N : LocalNet K)

/-! ### Algebra of local observables

These constructions apply to any abstract local net over a directed causal index set.
-/

/-- The **algebra of local observables** of the net: the algebraic inductive limit of the local
    algebras along the isotony embeddings. Its C⋆-completion is the quasi-local algebra. -/
noncomputable abbrev localObservables : Type _ :=
  DirectLimit N.algebra (fun _ _ h => N.incl h)

omit [Nonempty K] in
/-- Componentwise behaviour of the involution on the algebra of local observables. The
    `Star`, `StarRing`, `Algebra ℂ` and `StarModule ℂ` instances come from the general
    direct-limit constructions, since each `algebra O` is a `ℂ`-`*`-algebra and `incl` is a
    `*`-algebra homomorphism. -/
@[simp] lemma star_mk {O : K} (X : N.algebra O) :
    star (⟦⟨O, X⟩⟧ : N.localObservables) = ⟦⟨O, star X⟩⟧ := rfl

/-- The canonical embedding `𝔄(O) ↪ 𝔄_loc` of a local algebra into the algebra of local
    observables, as a unital ring homomorphism (the cocone of the inductive limit). -/
noncomputable def ιLocal (O : K) :
    N.algebra O →+* N.localObservables :=
  DirectLimit.Ring.of N.algebra (fun _ _ h => N.incl h) O

/-- Compatibility of the cocone with the isotony embeddings: including `X` from `O` into the
    larger region `O'` and then into `𝔄_loc` is the same as including `X` directly. -/
@[simp] lemma ιLocal_incl {O O' : K} (h : O ≤ O') (X : N.algebra O) :
    N.ιLocal O' (N.incl h X) = N.ιLocal O X :=
  DirectLimit.Ring.of_f (G := N.algebra) (f := fun _ _ h => N.incl h) h X

/-- The cocone is a `*`-homomorphism: it intertwines the local and quasi-local involutions. -/
@[simp] lemma ιLocal_star {O : K} (X : N.algebra O) :
    N.ιLocal O (star X) = star (N.ιLocal O X) :=
  (star_mk (N := N) X).symm

/-- The cocone is `ℂ`-linear: scalars act componentwise on the inductive limit. -/
@[simp] lemma ιLocal_smul (c : ℂ) {O : K} (X : N.algebra O) :
    N.ιLocal O (c • X) = c • N.ιLocal O X :=
  (DirectLimit.smul_def O X c).symm

/-- The cocone of the inductive limit absorbs the region-equality transport. -/
@[simp] lemma ιLocal_algebraCongr {O O' : K} (h : O = O') (x : N.algebra O) :
    N.ιLocal O' (N.algebraCongr h x) = N.ιLocal O x := by
  subst h; rfl

/-- **Exhaustion**: every element of the algebra of local observables is the image of a local
    observable from some region — the union of the local algebras is the whole limit. -/
theorem exists_ιLocal (z : N.localObservables) :
    ∃ (O : K) (X : N.algebra O), z = N.ιLocal O X := by
  induction z using DirectLimit.induction with
  | _ O X => exact ⟨O, X, rfl⟩

/-- **Locality in the algebra of local observables**: observables localised in causally orthogonal
    regions commute inside `𝔄_loc`. Pushes both observables into a directed upper bound of the two
    regions and lifts the net's `locality` along the ring-hom cocone. -/
theorem ιLocal_commute_of_orthogonal {O₁ O₂ : K} (hd : O₁ ⟂ O₂)
    (X : N.algebra O₁) (Y : N.algebra O₂) :
    Commute (N.ιLocal O₁ X) (N.ιLocal O₂ Y) := by
  obtain ⟨O, h₁, h₂⟩ := directed_of (· ≤ ·) O₁ O₂
  rw [← N.ιLocal_incl h₁ X, ← N.ιLocal_incl h₂ Y]
  exact (N.locality h₁ h₂ hd X Y).map (N.ιLocal O)

/-! ### Faithful nets and the quasi-local C⋆-algebra

For a faithful net the connecting maps are isometric, so the algebra of local observables carries
a C⋆-norm whose completion is the quasi-local C⋆-algebra `𝔄 = ‾⋃_O 𝔄(O)`.
-/

section CStar

variable [N.Faithful]

/-- The algebra of local observables is a normed ring under the C⋆-norm of the inductive limit
    (the inclusions are injective, hence isometric). -/
noncomputable instance : NormedRing N.localObservables :=
  DirectLimit.cstarNormedRing (fun _ _ h => Faithful.incl_injective h)

/-- The C⋆-norm of a local observable, viewed in the algebra of local observables, is its norm in
    its own region's algebra: the connecting maps are isometric. -/
@[simp] lemma norm_mk {O : K} (X : N.algebra O) :
    ‖(⟦⟨O, X⟩⟧ : N.localObservables)‖ = ‖X‖ := rfl

/-- The C⋆-norm is compatible with the `ℂ`-algebra structure. -/
noncomputable instance : NormedAlgebra ℂ N.localObservables where
  norm_smul_le c x := by
    induction x using DirectLimit.induction with
    | _ O X => rw [DirectLimit.smul_def, norm_mk, norm_mk]; exact norm_smul_le c X

/-- `star` is isometric on the algebra of local observables. -/
instance : NormedStarGroup N.localObservables where
  norm_star_le x := by
    induction x using DirectLimit.induction with
    | _ O X => rw [star_mk, norm_mk, norm_mk]; exact (norm_star X).le

/-- The C⋆-identity holds on the algebra of local observables. -/
instance : CStarRing N.localObservables where
  norm_mul_self_le x := by
    induction x using DirectLimit.induction with
    | _ O X => rw [star_mk, DirectLimit.mul_def, norm_mk, norm_mk]
               exact CStarRing.norm_mul_self_le X

/-- The **quasi-local C⋆-algebra** of a faithful net: the completion of the algebra of local
    observables. This is the AQFT quasi-local algebra `𝔄 = ‾⋃_O 𝔄(O)`. -/
noncomputable abbrev quasiLocalCStarAlgebra : Type _ :=
  UniformSpace.Completion N.localObservables

noncomputable example : CStarAlgebra N.quasiLocalCStarAlgebra := inferInstance

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
  map_star' X := by simp

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
    Dense (⋃ O : K, Set.range (N.ιLocalCStar O)) := by
  refine UniformSpace.Completion.denseRange_coe.mono ?_
  rintro _ ⟨z, rfl⟩
  obtain ⟨O, X, rfl⟩ := N.exists_ιLocal z
  exact Set.mem_iUnion.2 ⟨O, X, rfl⟩

/-- **Locality in the quasi-local C⋆-algebra**: observables localised in causally orthogonal
    regions commute inside `𝔄`. Transports `ιLocal_commute_of_orthogonal` along the completion
    coercion. -/
theorem ιLocalCStar_commute_of_orthogonal {O₁ O₂ : K} (hd : O₁ ⟂ O₂)
    (X : N.algebra O₁) (Y : N.algebra O₂) :
    Commute (N.ιLocalCStar O₁ X) (N.ιLocalCStar O₂ Y) :=
  (N.ιLocal_commute_of_orthogonal hd X Y).map UniformSpace.Completion.coeRingHom

end CStar

namespace Covariance

variable {N} (a : N.Covariance)

/-! ### The induced covariance action -/

/-- The **covariance action** `β_a ⟦⟨O, X⟩⟧ = ⟦⟨σO, β_O X⟩⟧` of a covariance on the algebra of local
    observables, as a ring homomorphism. Well-defined by naturality (`β_incl`). -/
noncomputable def localObservableCovariance : N.localObservables →+* N.localObservables :=
  DirectLimit.Ring.lift N.algebra (fun _ _ h => N.incl h) N.localObservables
    (fun O => (N.ιLocal (a.σ O)).comp (a.β O).toAlgEquiv.toAlgHom.toRingHom)
    (fun O O' h X => by
      change N.ιLocal (a.σ O') (a.β O' (N.incl h X)) = N.ιLocal (a.σ O) (a.β O X)
      rw [a.β_incl h]
      exact N.ιLocal_incl _ _)

/-- Componentwise formula for the covariance action: `β_a ⟦⟨O, X⟩⟧ = ⟦⟨σO, β_O X⟩⟧`. -/
@[simp] lemma localObservableCovariance_mk {O : K} (X : N.algebra O) :
  a.localObservableCovariance (⟦⟨O, X⟩⟧ : N.localObservables) = ⟦⟨a.σ O, a.β O X⟩⟧ :=
  rfl

/-- The covariance action of the identity covariance is the identity: `β_{id} = id`. -/
@[simp] lemma localObservableCovariance_id :
  (Covariance.id N).localObservableCovariance = RingHom.id N.localObservables := by
  refine RingHom.ext fun z => ?_
  induction z using DirectLimit.induction with
  | _ O X => rw [localObservableCovariance_mk, RingHom.id_apply]; rfl

/-- **Functoriality of the covariance action**: composing covariances composes their actions,
    `β_{a∘b} = β_a ∘ β_b`. -/
@[simp] lemma localObservableCovariance_comp (a b : N.Covariance) :
  (a.comp b).localObservableCovariance = a.localObservableCovariance.comp b.localObservableCovariance := by
  refine RingHom.ext fun z => ?_
  induction z using DirectLimit.induction with
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
  induction z using DirectLimit.induction with
  | _ O X =>
    rw [DirectLimit.smul_def, localObservableCovariance_mk, localObservableCovariance_mk,
      DirectLimit.smul_def, map_smul]

/-- The covariance action preserves the involution: `β_a (star z) = star (β_a z)`, since each `β`
    is a `*`-isomorphism. -/
lemma localObservableCovariance_star (z : N.localObservables) :
  a.localObservableCovariance (star z) = star (a.localObservableCovariance z) := by
  induction z using DirectLimit.induction with
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
  induction z using DirectLimit.induction with
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

end CStarCovariance

end Covariance

end LocalNet
