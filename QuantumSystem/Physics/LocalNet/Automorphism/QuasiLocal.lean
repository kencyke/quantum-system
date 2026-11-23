/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.CStarAlgebra.StarAlgEquiv
public import QuantumSystem.Physics.LocalNet.Automorphism.Basic

/-!
# The action of the automorphisms on the quasi-local algebra

An automorphism of a graded-local net (`GradedLocalNet.Automorphism`, defined in
`QuantumSystem.Physics.LocalNet.Automorphism.Basic`) over a directed index set acts on the algebras of
`QuantumSystem.Physics.LocalNet.QuasiLocalAlgebra`: its per-region `*`-isomorphisms assemble into a
ring endomorphism `localObservableEndomorphism` of the algebra of local observables, which is
functorial and is shown `ℂ`-linear and `*`-preserving — hence bundled as a `*`-automorphism
`localObservableAutomorphismEquiv`, assembled into a group homomorphism
`localObservableAutomorphismHom`. For a `Faithful` net it is isometric and extends to a
`*`-automorphism `quasiLocalCStarAutomorphismEquiv` of the quasi-local C⋆-algebra, assembled into
`quasiLocalCStarAutomorphismHom`.

A symmetry group `G` acts on the net by a group homomorphism `φ : G →* N.Automorphism`; composing it
with `localObservableAutomorphismHom` — or, for a `Faithful` net, `quasiLocalCStarAutomorphismHom` —
yields the automorphic action of `G` on the (quasi-local) algebra. The automorphisms themselves carry
no topology: continuity is a property of the action of a symmetry group `G` whose topology is
given. When `g ↦ β_{φ g} z` is norm-continuous for every `z` in the quasi-local C⋆-algebra — it
suffices to check local observables (`continuous_quasiLocalCStarAutomorphismHom_comp_iff`), and it
holds for every discrete `G` — the action is a C⋆-dynamical system `G →ₜ* (𝔄 ≃⋆ₐ[ℂ] 𝔄)`
(`quasiLocalCStarDynamicalSystem`).

The parities of the local algebras assemble in this way into the parity automorphism
`GradedLocalNet.quasiLocalParity` of the quasi-local C⋆-algebra, an involution; its fixed points,
the even part, are in `QuantumSystem.Physics.LocalNet.Subnet`.

## Notation

`𝔄(O)` in the prose is documentation shorthand for the local C⋆-algebra `N.algebra O`; the
convention is stated in full in `QuantumSystem.Physics.LocalNet.Isotony`.

`ι_O` is the local embedding `N.ιLocalCStar O`. For an automorphism `a`, `σ` and `β_O` are its
fields `a.σ` and `a.β O`, and `β_a` is its action `a.quasiLocalCStarAutomorphismEquiv` on the
quasi-local algebra; `Θ` is that of the parity, `N.quasiLocalParity`.
-/

@[expose] public section

namespace GradedLocalNet

open CStarNet

variable {K : Type*} [Preorder K] [CausalOrthogonality K] [IsDirectedOrder K] [Nonempty K]
variable (N : GradedLocalNet K)

namespace Automorphism

variable {N} (a : N.Automorphism)

/-! ### The induced action -/

/-- The **induced action** `β_a ⟦⟨O, X⟩⟧ = ⟦⟨σO, β_O X⟩⟧` of an automorphism on the algebra of local
    observables, as a ring homomorphism. Well-defined by naturality (`β_incl`). -/
noncomputable def localObservableEndomorphism : N.localObservables →+* N.localObservables :=
  NormedDirectLimit.liftRingHom
    (fun O => (N.ιLocal (a.σ O)).toRingHom.comp (a.β O).toAlgEquiv.toAlgHom.toRingHom)
    (fun O O' h X => by
      change N.ιLocal (a.σ O') (a.β O' (N.incl h X)) = N.ιLocal (a.σ O) (a.β O X)
      rw [a.β_incl h]
      exact N.ιLocal_incl _ _)

/-- Componentwise formula for the induced action: `β_a ⟦⟨O, X⟩⟧ = ⟦⟨σO, β_O X⟩⟧`. -/
@[simp] lemma localObservableEndomorphism_mk {O : K} (X : N.algebra O) :
  a.localObservableEndomorphism (NormedDirectLimit.mk O X : N.localObservables) =
    NormedDirectLimit.mk (a.σ O) (a.β O X) :=
  rfl

/-- The induced action of the identity automorphism is the identity: `β_{id} = id`. -/
@[simp] lemma localObservableEndomorphism_id :
  (Automorphism.id N).localObservableEndomorphism = RingHom.id N.localObservables := by
  refine RingHom.ext fun z => ?_
  induction z using NormedDirectLimit.induction with
  | _ O X => rw [localObservableEndomorphism_mk, RingHom.id_apply]; rfl

/-- **Functoriality of the induced action**: composing automorphisms composes their actions,
    `β_{a∘b} = β_a ∘ β_b`. -/
@[simp] lemma localObservableEndomorphism_comp (a b : N.Automorphism) :
  (a.comp b).localObservableEndomorphism = a.localObservableEndomorphism.comp b.localObservableEndomorphism := by
  refine RingHom.ext fun z => ?_
  induction z using NormedDirectLimit.induction with
  | _ O X =>
    simp only [RingHom.comp_apply, localObservableEndomorphism_mk]
    rfl

/-- The induced action sends the unit automorphism to the identity: `β_1 = id`. -/
@[simp] lemma localObservableEndomorphism_one :
    (1 : N.Automorphism).localObservableEndomorphism = RingHom.id N.localObservables := by
  rw [one_def, localObservableEndomorphism_id]

/-- The induced action is multiplicative: `β_{a·b} = β_a ∘ β_b`. -/
lemma localObservableEndomorphism_mul (a b : N.Automorphism) :
    (a * b).localObservableEndomorphism = a.localObservableEndomorphism.comp b.localObservableEndomorphism := by
  rw [mul_def, localObservableEndomorphism_comp]

/-! #### The induced action as a `*`-automorphism -/

/-- The induced action is `ℂ`-linear: `β_a (c • z) = c • β_a z`, since each `β` is. -/
lemma localObservableEndomorphism_smul (c : ℂ) (z : N.localObservables) :
  a.localObservableEndomorphism (c • z) = c • a.localObservableEndomorphism z := by
  induction z using NormedDirectLimit.induction with
  | _ O X =>
    rw [← NormedDirectLimit.mk_smul, localObservableEndomorphism_mk, localObservableEndomorphism_mk,
      ← NormedDirectLimit.mk_smul, map_smul]

/-- The induced action preserves the involution: `β_a (star z) = star (β_a z)`, since each `β`
    is a `*`-isomorphism. -/
lemma localObservableEndomorphism_star (z : N.localObservables) :
  a.localObservableEndomorphism (star z) = star (a.localObservableEndomorphism z) := by
  induction z using NormedDirectLimit.induction with
  | _ O X =>
    rw [star_mk, localObservableEndomorphism_mk, localObservableEndomorphism_mk, star_mk, map_star]

/-- The induced action as a `*`-algebra automorphism of the algebra of local observables, with
  the action of the inverse automorphism `a⁻¹` as its inverse. -/
noncomputable def localObservableAutomorphismEquiv :
    N.localObservables ≃⋆ₐ[ℂ] N.localObservables where
  toFun := a.localObservableEndomorphism
  invFun := a⁻¹.localObservableEndomorphism
  left_inv z := by
    rw [← RingHom.comp_apply, ← localObservableEndomorphism_mul, inv_mul_cancel, localObservableEndomorphism_one,
      RingHom.id_apply]
  right_inv z := by
    rw [← RingHom.comp_apply, ← localObservableEndomorphism_mul, mul_inv_cancel, localObservableEndomorphism_one,
      RingHom.id_apply]
  map_mul' := map_mul a.localObservableEndomorphism
  map_add' := map_add a.localObservableEndomorphism
  map_smul' := a.localObservableEndomorphism_smul
  map_star' := a.localObservableEndomorphism_star

/-- The bundled `*`-automorphism agrees with the underlying ring homomorphism. -/
@[simp] lemma localObservableAutomorphismEquiv_apply (z : N.localObservables) :
    a.localObservableAutomorphismEquiv z = a.localObservableEndomorphism z := rfl

/-- The inverse of the bundled `*`-automorphism is the action of the inverse automorphism. -/
@[simp] lemma localObservableAutomorphismEquiv_symm_apply (z : N.localObservables) :
    a.localObservableAutomorphismEquiv.symm z = a⁻¹.localObservableEndomorphism z := rfl

/-- An automorphism of the net acts on the algebra of local observables by `*`-algebra automorphisms,
    assembled as a group homomorphism into the `*`-automorphism group. -/
noncomputable def localObservableAutomorphismHom :
    N.Automorphism →* (N.localObservables ≃⋆ₐ[ℂ] N.localObservables) where
  toFun a := a.localObservableAutomorphismEquiv
  map_one' := by
    ext z
    simp only [localObservableAutomorphismEquiv_apply, localObservableEndomorphism_one, RingHom.id_apply,
      StarAlgEquiv.one_apply]
  map_mul' a b := by
    ext z
    simp only [localObservableAutomorphismEquiv_apply, localObservableEndomorphism_mul, RingHom.comp_apply,
      StarAlgEquiv.mul_apply]

/-- The group homomorphism evaluates to the induced action. -/
@[simp] lemma localObservableAutomorphismHom_apply (z : N.localObservables) :
    localObservableAutomorphismHom a z = a.localObservableEndomorphism z := rfl

/-! #### The automorphism induced on the quasi-local C⋆-algebra -/

section CStarAutomorphism

variable [N.Faithful]

/-- The induced action is **isometric** on the algebra of local observables: each `β` is a
    `*`-isomorphism of C⋆-algebras, hence norm-preserving. -/
lemma norm_localObservableEndomorphism (z : N.localObservables) :
  ‖a.localObservableEndomorphism z‖ = ‖z‖ := by
  induction z using NormedDirectLimit.induction with
  | _ O X =>
    rw [localObservableEndomorphism_mk, norm_mk, norm_mk]
    exact StarAlgEquiv.norm_map _ X

/-- The automorphism induced on the algebra of local observables is uniformly continuous (it is
    an isometry), so it extends to the C⋆-completion. -/
lemma uniformContinuous_localObservableAutomorphismEquiv :
    UniformContinuous a.localObservableAutomorphismEquiv :=
  (AddMonoidHomClass.isometry_of_norm _ (fun z => by
    rw [localObservableAutomorphismEquiv_apply]; exact a.norm_localObservableEndomorphism z)).uniformContinuous

/-- The inverse induced automorphism is uniformly continuous as well (the action of `a⁻¹` is
    also an isometry). -/
lemma uniformContinuous_localObservableAutomorphismEquiv_symm :
    UniformContinuous a.localObservableAutomorphismEquiv.symm := by
  have h : ∀ z, ‖a.localObservableAutomorphismEquiv.symm z‖ = ‖z‖ := fun z => by
    rw [localObservableAutomorphismEquiv_symm_apply]; exact a⁻¹.norm_localObservableEndomorphism z
  exact (AddMonoidHomClass.isometry_of_norm _ h).uniformContinuous

/-- The automorphism induced on the quasi-local C⋆-algebra: the continuous extension of
    `localObservableAutomorphismEquiv` to the completion. -/
noncomputable def quasiLocalCStarAutomorphismEquiv :
    N.quasiLocalCStarAlgebra ≃⋆ₐ[ℂ] N.quasiLocalCStarAlgebra :=
  UniformSpace.Completion.mapStarAlgEquiv a.localObservableAutomorphismEquiv
    a.uniformContinuous_localObservableAutomorphismEquiv
    a.uniformContinuous_localObservableAutomorphismEquiv_symm

/-- On local observables the extension to the completion agrees with the induced action they
    already carry. -/
@[simp] lemma quasiLocalCStarAutomorphismEquiv_coe (z : N.localObservables) :
    a.quasiLocalCStarAutomorphismEquiv (↑z : N.quasiLocalCStarAlgebra) =
      ↑(a.localObservableEndomorphism z) :=
  UniformSpace.Completion.mapStarAlgEquiv_coe _ _ _ z

/-- The automorphism induced on the quasi-local C⋆-algebra is continuous, being the continuous
    extension of an isometry to the completion. -/
lemma continuous_quasiLocalCStarAutomorphismEquiv :
    Continuous (⇑a.quasiLocalCStarAutomorphismEquiv) :=
  UniformSpace.Completion.continuous_map

/-- An automorphism of a faithful net acts on the quasi-local C⋆-algebra by `*`-automorphisms,
    assembled as a group homomorphism into the `*`-automorphism group. -/
noncomputable def quasiLocalCStarAutomorphismHom :
    N.Automorphism →* (N.quasiLocalCStarAlgebra ≃⋆ₐ[ℂ] N.quasiLocalCStarAlgebra) where
  toFun a := a.quasiLocalCStarAutomorphismEquiv
  map_one' := by
    refine StarAlgEquiv.ext fun z => ?_
    rw [StarAlgEquiv.one_apply]
    refine UniformSpace.Completion.induction_on z
      (isClosed_eq (1 : N.Automorphism).continuous_quasiLocalCStarAutomorphismEquiv
        continuous_id) ?_
    intro w
    simp only [quasiLocalCStarAutomorphismEquiv_coe, localObservableEndomorphism_one, RingHom.id_apply]
  map_mul' a b := by
    refine StarAlgEquiv.ext fun z => ?_
    rw [StarAlgEquiv.mul_apply]
    refine UniformSpace.Completion.induction_on z
      (isClosed_eq (a * b).continuous_quasiLocalCStarAutomorphismEquiv
        (a.continuous_quasiLocalCStarAutomorphismEquiv.comp
          b.continuous_quasiLocalCStarAutomorphismEquiv)) ?_
    intro w
    simp only [quasiLocalCStarAutomorphismEquiv_coe, localObservableEndomorphism_mul, RingHom.comp_apply]

/-- The group homomorphism evaluates to the automorphism induced on the quasi-local
    C⋆-algebra. -/
@[simp] lemma quasiLocalCStarAutomorphismHom_apply
    (z : N.quasiLocalCStarAlgebra) :
  quasiLocalCStarAutomorphismHom a z = a.quasiLocalCStarAutomorphismEquiv z := rfl

/-- The automorphism induced on the quasi-local C⋆-algebra on a local observable:
    `β_a (ι_O X) = ι_{σO} (β_O X)`. -/
@[simp] lemma quasiLocalCStarAutomorphismEquiv_ιLocalCStar (O : K) (X : N.algebra O) :
    a.quasiLocalCStarAutomorphismEquiv (N.ιLocalCStar O X) = N.ιLocalCStar (a.σ O) (a.β O X) :=
  a.quasiLocalCStarAutomorphismEquiv_coe (N.ιLocal O X)

/-- **Continuity of a family of automorphisms is checked on local observables**: a map `f` into the
    automorphisms acts continuously on the quasi-local C⋆-algebra in the point-norm topology iff
    `y ↦ ι_{σ_y O} (β_{y,O} X)` is continuous for every region `O` and every local observable
    `X ∈ 𝔄(O)`. The local algebras are dense (`dense_iUnion_range_ιLocalCStar`) and the
    automorphisms are isometric, so `StarAlgEquiv.continuous_of_dense` applies. -/
lemma continuous_quasiLocalCStarAutomorphismHom_comp_iff {X : Type*} [TopologicalSpace X]
    {f : X → N.Automorphism} :
    Continuous (fun y => quasiLocalCStarAutomorphismHom (f y)) ↔
      ∀ (O : K) (x : N.algebra O), Continuous fun y => N.ιLocalCStar ((f y).σ O) ((f y).β O x) := by
  refine ⟨fun h O x => ?_, fun h => ?_⟩
  · simpa using StarAlgEquiv.continuous_iff.mp h (N.ιLocalCStar O x)
  · refine StarAlgEquiv.continuous_of_dense N.dense_iUnion_range_ιLocalCStar fun z hz => ?_
    obtain ⟨O, x, rfl⟩ := Set.mem_iUnion.mp hz
    simpa using h O x

variable {G : Type*} [Monoid G] [TopologicalSpace G]

/-- A symmetry group (or monoid) `G` of a faithful net, acting through `φ : G →* N.Automorphism`
    **continuously** — `g ↦ β_{φ g} z` is norm-continuous for every `z` in the quasi-local
    C⋆-algebra, the hypothesis `hφ` — acts on the quasi-local C⋆-algebra as a C⋆-dynamical system:
    the composite of `φ` with `quasiLocalCStarAutomorphismHom`. The continuity is a property of the
    action of `G`, whose topology is given; the automorphisms themselves carry no topology. It is
    checked on local observables (`continuous_quasiLocalCStarAutomorphismHom_comp_iff`), and holds
    for every `φ` when `G` is discrete (`continuous_of_discreteTopology`). -/
noncomputable def quasiLocalCStarDynamicalSystem (φ : G →* N.Automorphism)
    (hφ : Continuous fun g => quasiLocalCStarAutomorphismHom (φ g)) :
    G →ₜ* (N.quasiLocalCStarAlgebra ≃⋆ₐ[ℂ] N.quasiLocalCStarAlgebra) :=
  ⟨quasiLocalCStarAutomorphismHom.comp φ, hφ⟩

/-- The C⋆-dynamical system of a symmetry group acts by the induced automorphisms. -/
@[simp] lemma quasiLocalCStarDynamicalSystem_apply (φ : G →* N.Automorphism)
    (hφ : Continuous fun g => quasiLocalCStarAutomorphismHom (φ g)) (g : G)
    (z : N.quasiLocalCStarAlgebra) :
    quasiLocalCStarDynamicalSystem φ hφ g z = (φ g).quasiLocalCStarAutomorphismEquiv z :=
  rfl

end CStarAutomorphism

end Automorphism

/-! ### The parity automorphism of the quasi-local algebra -/

section Parity

variable [N.Faithful]

/-- The **parity automorphism** `Θ` of the quasi-local C⋆-algebra of a faithful graded-local net:
    the automorphism restricting to the parity of every local algebra, obtained as the action of
    the parity automorphism (`GradedLocalNet.parityAutomorphism`). For a local net it is the
    identity (`GradedLocalNet.quasiLocalParity_apply_of_isTriviallyGraded`). -/
noncomputable def quasiLocalParity : N.quasiLocalCStarAlgebra ≃⋆ₐ[ℂ] N.quasiLocalCStarAlgebra :=
  (parityAutomorphism N).quasiLocalCStarAutomorphismEquiv

/-- The quasi-local parity restricts to the parity of each local algebra. -/
@[simp] lemma quasiLocalParity_ιLocalCStar (O : K) (X : N.algebra O) :
    N.quasiLocalParity (N.ιLocalCStar O X) = N.ιLocalCStar O (N.parity O X) :=
  (parityAutomorphism N).quasiLocalCStarAutomorphismEquiv_ιLocalCStar O X

/-- The quasi-local parity is an involution. -/
@[simp] lemma quasiLocalParity_quasiLocalParity (z : N.quasiLocalCStarAlgebra) :
    N.quasiLocalParity (N.quasiLocalParity z) = z := by
  have h := congrArg (fun e : N.quasiLocalCStarAlgebra ≃⋆ₐ[ℂ] N.quasiLocalCStarAlgebra => e z)
    ((map_mul Automorphism.quasiLocalCStarAutomorphismHom (parityAutomorphism N)
      (parityAutomorphism N)).symm.trans (congrArg _ (parityAutomorphism_mul_self N)))
  rwa [map_one] at h

/-- For a local net the quasi-local parity is the identity. -/
lemma quasiLocalParity_apply_of_isTriviallyGraded [N.IsTriviallyGraded] (z : N.quasiLocalCStarAlgebra) :
    N.quasiLocalParity z = z := by
  have h := congrArg (fun e : N.quasiLocalCStarAlgebra ≃⋆ₐ[ℂ] N.quasiLocalCStarAlgebra => e z)
    (congrArg Automorphism.quasiLocalCStarAutomorphismHom (parityAutomorphism_eq_one N))
  rwa [map_one] at h

end Parity

end GradedLocalNet
