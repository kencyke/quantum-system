/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.CStarAlgebra.StarAlgEquiv
public import QuantumSystem.Physics.LocalNet.Covariance.Basic

/-!
# The action of the covariances on the quasi-local algebra

A covariance of a graded-local net (`GradedLocalNet.Covariance`, defined in
`QuantumSystem.Physics.LocalNet.Covariance.Basic`) over a directed index set acts on the algebras of
`QuantumSystem.Physics.LocalNet.QuasiLocalAlgebra`: its per-region `*`-isomorphisms assemble into a
ring endomorphism `localObservableCovariance` of the algebra of local observables, which is
functorial and is shown `ℂ`-linear and `*`-preserving — hence bundled as a `*`-automorphism
`localObservableCovarianceEquiv`, assembled into a group homomorphism
`localObservableCovarianceHom`. For a `Faithful` net it is isometric and extends to a
`*`-automorphism `quasiLocalCStarCovarianceEquiv` of the quasi-local C⋆-algebra, assembled into
`quasiLocalCStarCovarianceHom`.

A symmetry group `G` acts on the net by a group homomorphism `φ : G →* N.Covariance`; composing it
with `localObservableCovarianceHom` — or, for a `Faithful` net, `quasiLocalCStarCovarianceHom` —
yields the automorphic action of `G` on the (quasi-local) algebra. The covariances themselves carry
no topology: continuity is a property of the action of a symmetry group `G` whose topology is
given. When `g ↦ β_{φ g} z` is norm-continuous for every `z` in the quasi-local C⋆-algebra — it
suffices to check local observables (`continuous_quasiLocalCStarCovarianceHom_comp_iff`), and it
holds for every discrete `G` — the action is a C⋆-dynamical system `G →ₜ* (𝔄 ≃⋆ₐ[ℂ] 𝔄)`
(`quasiLocalCStarDynamicalSystem`).

The parities of the local algebras assemble in this way into the parity automorphism
`GradedLocalNet.quasiLocalParity` of the quasi-local C⋆-algebra, an involution; its fixed points,
the even part, are in `QuantumSystem.Physics.LocalNet.Subnet`.

## Notation

`𝔄(O)` in the prose is documentation shorthand for the local C⋆-algebra `N.algebra O`; the
convention is stated in full in `QuantumSystem.Physics.LocalNet.Isotony`.
-/

@[expose] public section

namespace GradedLocalNet

open CStarNet

variable {K : Type*} [Preorder K] [CausalOrthogonality K] [IsDirectedOrder K] [Nonempty K]
variable (N : GradedLocalNet K)

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
    the parity covariance (`GradedLocalNet.parityCovariance`). For a local net it is the
    identity (`GradedLocalNet.quasiLocalParity_apply_of_isLocal`). -/
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

/-- For a local net the quasi-local parity is the identity. -/
lemma quasiLocalParity_apply_of_isLocal [N.IsLocal] (z : N.quasiLocalCStarAlgebra) :
    N.quasiLocalParity z = z := by
  have h := congrArg (fun e : N.quasiLocalCStarAlgebra ≃⋆ₐ[ℂ] N.quasiLocalCStarAlgebra => e z)
    (congrArg Covariance.quasiLocalCStarCovarianceHom (parityCovariance_eq_one N))
  rwa [map_one] at h

end Parity

end GradedLocalNet
