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

* `LocalNet.quasiLocalAlgebra` is the algebraic inductive limit `‾⋃_O 𝔄(O)` of the local algebras
  along the isotony embeddings, with cocone `ιLocal`, exhaustion (`exists_ιLocal`) and locality
  (`ιLocal_commute_of_orthogonal`).
* For a `Faithful` net the connecting maps are isometric, so the algebra of local observables
  carries a C⋆-norm whose completion `LocalNet.quasiLocalCStarAlgebra` is the AQFT quasi-local
  algebra `𝔄 = ‾⋃_O 𝔄(O)` (Naaijkens 2012 §1.3, Bratteli–Robinson Vol.2 §6.2), with dense local
  embeddings `ιLocalCStar`.

A `LocalNet.Covariance` (defined in `LocalNet.Covariance`) acts on these algebras: its per-region
`*`-isomorphisms assemble into a ring endomorphism `quasiLocalCovariance` of the algebra of local
observables, which is functorial and is shown `ℂ`-linear and `*`-preserving — hence bundled as a
`*`-automorphism `quasiLocalCovarianceEquiv`, assembled into a group homomorphism
`quasiLocalCovarianceHom`. For a `Faithful` net it is isometric and extends to a `*`-automorphism
`quasiLocalCStarCovarianceEquiv` of the quasi-local C⋆-algebra.
-/

@[expose] public section

namespace LocalNet

open scoped CausalOrthogonality

variable {K : Type*} [PartialOrder K] [CausalOrthogonality K] [IsDirectedOrder K] [Nonempty K]
variable (N : LocalNet K)

/-! ### Algebra of local observables

These constructions apply to any abstract local net over a directed causal index set.
-/

/-- The **algebra of local observables** of the net: the algebraic inductive limit of the local
    algebras along the isotony embeddings. Its C⋆-completion is the quasi-local algebra. -/
noncomputable abbrev quasiLocalAlgebra : Type _ :=
  DirectLimit N.algebra (fun _ _ h => N.incl h)

omit [Nonempty K] in
/-- Componentwise behaviour of the involution on the algebra of local observables. The
    `Star`, `StarRing`, `Algebra ℂ` and `StarModule ℂ` instances come from the general
    direct-limit constructions, since each `algebra O` is a `ℂ`-`*`-algebra and `incl` is a
    `*`-algebra homomorphism. -/
@[simp] lemma star_mk {O : K} (X : N.algebra O) :
    star (⟦⟨O, X⟩⟧ : N.quasiLocalAlgebra) = ⟦⟨O, star X⟩⟧ := rfl

/-- The canonical embedding `𝔄(O) ↪ 𝔄_loc` of a local algebra into the algebra of local
    observables, as a unital ring homomorphism (the cocone of the inductive limit). -/
noncomputable def ιLocal (O : K) :
    N.algebra O →+* N.quasiLocalAlgebra :=
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

/-- The cocone of the inductive limit absorbs the region-equality transport. -/
@[simp] lemma ιLocal_algebraCongr {O O' : K} (h : O = O') (x : N.algebra O) :
    N.ιLocal O' (N.algebraCongr h x) = N.ιLocal O x := by
  subst h; rfl

/-- **Exhaustion**: every element of the algebra of local observables is the image of a local
    observable from some region — the union of the local algebras is the whole limit. -/
theorem exists_ιLocal (z : N.quasiLocalAlgebra) :
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
noncomputable instance : NormedRing N.quasiLocalAlgebra :=
  DirectLimit.cstarNormedRing (fun _ _ h => Faithful.incl_injective h)

@[simp] lemma norm_mk {O : K} (X : N.algebra O) :
    ‖(⟦⟨O, X⟩⟧ : N.quasiLocalAlgebra)‖ = ‖X‖ := rfl

/-- The C⋆-norm is compatible with the `ℂ`-algebra structure. -/
noncomputable instance : NormedAlgebra ℂ N.quasiLocalAlgebra where
  norm_smul_le c x := by
    induction x using DirectLimit.induction with
    | _ O X => rw [DirectLimit.smul_def, norm_mk, norm_mk]; exact norm_smul_le c X

/-- `star` is isometric on the algebra of local observables. -/
instance : NormedStarGroup N.quasiLocalAlgebra where
  norm_star_le x := by
    induction x using DirectLimit.induction with
    | _ O X => rw [star_mk, norm_mk, norm_mk]; exact (norm_star X).le

/-- The C⋆-identity holds on the algebra of local observables. -/
instance : CStarRing N.quasiLocalAlgebra where
  norm_mul_self_le x := by
    induction x using DirectLimit.induction with
    | _ O X => rw [star_mk, DirectLimit.mul_def, norm_mk, norm_mk]
               exact CStarRing.norm_mul_self_le X

/-- The **quasi-local C⋆-algebra** of a faithful net: the completion of the algebra of local
    observables. This is the AQFT quasi-local algebra `𝔄 = ‾⋃_O 𝔄(O)`. -/
noncomputable abbrev quasiLocalCStarAlgebra : Type _ :=
  UniformSpace.Completion N.quasiLocalAlgebra

noncomputable example : CStarAlgebra N.quasiLocalCStarAlgebra := inferInstance

/-- The canonical embedding `𝔄(O) → 𝔄` of a local algebra into the quasi-local C⋆-algebra,
    as the completion coercion composed with the inductive-limit cocone. Its range is dense. -/
noncomputable def ιLocalCStar (O : K) :
    N.algebra O → N.quasiLocalCStarAlgebra :=
  (↑) ∘ N.ιLocal O

/-- The dense embedding is compatible with the isotony embeddings: including into a larger
    region first does not change the image in the quasi-local C⋆-algebra. -/
@[simp] lemma ιLocalCStar_incl {O O' : K} (h : O ≤ O') (X : N.algebra O) :
    N.ιLocalCStar O' (N.incl h X) = N.ιLocalCStar O X :=
  congrArg _ (N.ιLocal_incl h X)

/-- The dense embedding is a `*`-map: it intertwines the local and quasi-local involutions. -/
@[simp] lemma ιLocalCStar_star {O : K} (X : N.algebra O) :
    N.ιLocalCStar O (star X) = star (N.ιLocalCStar O X) := by
  simp [ιLocalCStar]

/-- The local algebras are dense in the quasi-local C⋆-algebra: every element is a norm-limit of
    local observables. -/
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
noncomputable def quasiLocalCovariance : N.quasiLocalAlgebra →+* N.quasiLocalAlgebra :=
  DirectLimit.Ring.lift N.algebra (fun _ _ h => N.incl h) N.quasiLocalAlgebra
    (fun O => (N.ιLocal (a.region O)).comp (a.β O).toAlgEquiv.toAlgHom.toRingHom)
    (fun O O' h X => by
      change N.ιLocal (a.region O') (a.β O' (N.incl h X)) = N.ιLocal (a.region O) (a.β O X)
      rw [a.β_incl h]
      exact N.ιLocal_incl _ _)

@[simp] lemma quasiLocalCovariance_mk {O : K} (X : N.algebra O) :
  a.quasiLocalCovariance (⟦⟨O, X⟩⟧ : N.quasiLocalAlgebra) = ⟦⟨a.region O, a.β O X⟩⟧ :=
  rfl

/-- The covariance action of the identity covariance is the identity: `β_{id} = id`. -/
@[simp] lemma quasiLocalCovariance_id :
  (Covariance.id N).quasiLocalCovariance = RingHom.id N.quasiLocalAlgebra := by
  refine RingHom.ext fun z => ?_
  induction z using DirectLimit.induction with
  | _ O X => rw [quasiLocalCovariance_mk, RingHom.id_apply]; rfl

/-- **Functoriality of the covariance action**: composing covariances composes their actions,
    `β_{a∘b} = β_a ∘ β_b`. -/
@[simp] lemma quasiLocalCovariance_comp (a b : N.Covariance) :
  (a.comp b).quasiLocalCovariance = a.quasiLocalCovariance.comp b.quasiLocalCovariance := by
  refine RingHom.ext fun z => ?_
  induction z using DirectLimit.induction with
  | _ O X =>
    simp only [RingHom.comp_apply, quasiLocalCovariance_mk]
    rfl

/-- The covariance action sends the unit covariance to the identity: `β_1 = id`. -/
@[simp] lemma quasiLocalCovariance_one :
    (1 : N.Covariance).quasiLocalCovariance = RingHom.id N.quasiLocalAlgebra := by
  rw [one_def, quasiLocalCovariance_id]

/-- The covariance action is multiplicative: `β_{a·b} = β_a ∘ β_b`. -/
lemma quasiLocalCovariance_mul (a b : N.Covariance) :
    (a * b).quasiLocalCovariance = a.quasiLocalCovariance.comp b.quasiLocalCovariance := by
  rw [mul_def, quasiLocalCovariance_comp]

/-! #### The covariance action as a `*`-automorphism -/

/-- The covariance action is `ℂ`-linear: `β_a (c • z) = c • β_a z`, since each `β` is. -/
lemma quasiLocalCovariance_smul (c : ℂ) (z : N.quasiLocalAlgebra) :
  a.quasiLocalCovariance (c • z) = c • a.quasiLocalCovariance z := by
  induction z using DirectLimit.induction with
  | _ O X =>
    rw [DirectLimit.smul_def, quasiLocalCovariance_mk, quasiLocalCovariance_mk, DirectLimit.smul_def,
      map_smul]
    rfl

/-- The covariance action preserves the involution: `β_a (star z) = star (β_a z)`, since each `β`
    is a `*`-isomorphism. -/
lemma quasiLocalCovariance_star (z : N.quasiLocalAlgebra) :
  a.quasiLocalCovariance (star z) = star (a.quasiLocalCovariance z) := by
  induction z using DirectLimit.induction with
  | _ O X =>
    rw [star_mk, quasiLocalCovariance_mk, quasiLocalCovariance_mk, star_mk, map_star]
    rfl

/-- The covariance action as a `*`-algebra automorphism of the algebra of local observables, with
  the action of the inverse covariance `a⁻¹` as its inverse. -/
noncomputable def quasiLocalCovarianceEquiv :
    N.quasiLocalAlgebra ≃⋆ₐ[ℂ] N.quasiLocalAlgebra where
  toFun := a.quasiLocalCovariance
  invFun := a⁻¹.quasiLocalCovariance
  left_inv z := by
    rw [← RingHom.comp_apply, ← quasiLocalCovariance_mul, inv_mul_cancel, quasiLocalCovariance_one,
      RingHom.id_apply]
  right_inv z := by
    rw [← RingHom.comp_apply, ← quasiLocalCovariance_mul, mul_inv_cancel, quasiLocalCovariance_one,
      RingHom.id_apply]
  map_mul' := map_mul a.quasiLocalCovariance
  map_add' := map_add a.quasiLocalCovariance
  map_smul' := a.quasiLocalCovariance_smul
  map_star' := a.quasiLocalCovariance_star

@[simp] lemma quasiLocalCovarianceEquiv_apply (z : N.quasiLocalAlgebra) :
    a.quasiLocalCovarianceEquiv z = a.quasiLocalCovariance z := rfl

@[simp] lemma quasiLocalCovarianceEquiv_symm_apply (z : N.quasiLocalAlgebra) :
    a.quasiLocalCovarianceEquiv.symm z = a⁻¹.quasiLocalCovariance z := rfl

/-- A covariance of the net acts on the algebra of local observables by `*`-algebra automorphisms,
    assembled as a group homomorphism into the `*`-automorphism group. -/
noncomputable def quasiLocalCovarianceHom :
    N.Covariance →* (N.quasiLocalAlgebra ≃⋆ₐ[ℂ] N.quasiLocalAlgebra) where
  toFun a := a.quasiLocalCovarianceEquiv
  map_one' := by
    ext z
    simp only [quasiLocalCovarianceEquiv_apply, quasiLocalCovariance_one, RingHom.id_apply,
      StarAlgEquiv.one_apply]
  map_mul' a b := by
    ext z
    simp only [quasiLocalCovarianceEquiv_apply, quasiLocalCovariance_mul, RingHom.comp_apply,
      StarAlgEquiv.mul_apply]

@[simp] lemma quasiLocalCovarianceHom_apply (z : N.quasiLocalAlgebra) :
    quasiLocalCovarianceHom a z = a.quasiLocalCovariance z := rfl

/-! #### The covariance automorphism of the quasi-local C⋆-algebra -/

section CStarCovariance

variable [N.Faithful]

/-- The covariance action is **isometric** on the algebra of local observables: each `β` is a
    `*`-isomorphism of C⋆-algebras, hence norm-preserving. -/
lemma quasiLocalCovariance_norm (z : N.quasiLocalAlgebra) :
  ‖a.quasiLocalCovariance z‖ = ‖z‖ := by
  induction z using DirectLimit.induction with
  | _ O X =>
    rw [quasiLocalCovariance_mk, norm_mk, norm_mk]
    exact StarAlgEquiv.norm_map _ X

/-- The covariance automorphism of the algebra of local observables is uniformly continuous (it is
    an isometry), so it extends to the C⋆-completion. -/
lemma quasiLocalCovarianceEquiv_uniformContinuous :
    UniformContinuous a.quasiLocalCovarianceEquiv :=
  (AddMonoidHomClass.isometry_of_norm _ (fun z => by
    rw [quasiLocalCovarianceEquiv_apply]; exact a.quasiLocalCovariance_norm z)).uniformContinuous

/-- The inverse covariance automorphism is uniformly continuous as well (the action of `a⁻¹` is
    also an isometry). -/
lemma quasiLocalCovarianceEquiv_symm_uniformContinuous :
    UniformContinuous a.quasiLocalCovarianceEquiv.symm := by
  have h : ∀ z, ‖a.quasiLocalCovarianceEquiv.symm z‖ = ‖z‖ := fun z => by
    rw [quasiLocalCovarianceEquiv_symm_apply]; exact a⁻¹.quasiLocalCovariance_norm z
  exact (AddMonoidHomClass.isometry_of_norm _ h).uniformContinuous

/-- The covariance automorphism of the quasi-local C⋆-algebra: the continuous extension of
    `quasiLocalCovarianceEquiv` to the completion. -/
noncomputable def quasiLocalCStarCovarianceEquiv :
    N.quasiLocalCStarAlgebra ≃⋆ₐ[ℂ] N.quasiLocalCStarAlgebra :=
  UniformSpace.Completion.mapStarAlgEquiv a.quasiLocalCovarianceEquiv
    a.quasiLocalCovarianceEquiv_uniformContinuous
    a.quasiLocalCovarianceEquiv_symm_uniformContinuous

@[simp] lemma quasiLocalCStarCovarianceEquiv_coe (z : N.quasiLocalAlgebra) :
    a.quasiLocalCStarCovarianceEquiv (↑z : N.quasiLocalCStarAlgebra) =
      ↑(a.quasiLocalCovariance z) :=
  UniformSpace.Completion.mapStarAlgEquiv_coe _ _ _ z

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
    simp only [quasiLocalCStarCovarianceEquiv_coe, quasiLocalCovariance_one, RingHom.id_apply]
  map_mul' a b := by
    refine StarAlgEquiv.ext fun z => ?_
    rw [StarAlgEquiv.mul_apply]
    refine UniformSpace.Completion.induction_on z
      (isClosed_eq (a * b).quasiLocalCStarCovarianceEquiv_continuous
        (a.quasiLocalCStarCovarianceEquiv_continuous.comp
          b.quasiLocalCStarCovarianceEquiv_continuous)) ?_
    intro w
    simp only [quasiLocalCStarCovarianceEquiv_coe, quasiLocalCovariance_mul, RingHom.comp_apply]

@[simp] lemma quasiLocalCStarCovarianceHom_apply
    (z : N.quasiLocalCStarAlgebra) :
  quasiLocalCStarCovarianceHom a z = a.quasiLocalCStarCovarianceEquiv z := rfl

end CStarCovariance

end Covariance

end LocalNet
