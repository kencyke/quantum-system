/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.ForMathlib.Analysis.Normed.Group.DirectLimit
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.Completion
public import QuantumSystem.Physics.LocalNet.Isotony

/-!
# The quasi-local algebra of a net

The **algebra of local observables** and the **quasi-local C⋆-algebra** of a net of C⋆-algebras
`CStarNet`. These constructions use the isotony embeddings alone and apply to any net over a
*directed* index set (`IsDirectedOrder`, with a region to start from, `Nonempty`): directedness is
what makes the union of the local algebras an algebra. Lattice nets (`K = Finset sites`) are
directed by unions with the empty region as base point.

* `CStarNet.localObservables` is the algebraic inductive limit `⋃_O 𝔄(O)` of the local algebras
  along the isotony embeddings, with cocone `ιLocal` and exhaustion (`exists_ιLocal`); the cocone is
  injective for a `Faithful` net (`ιLocal_injective`).
* For a `Faithful` net the connecting maps are isometric, so the algebra of local observables
  carries a C⋆-norm whose completion `CStarNet.quasiLocalCStarAlgebra` is the AQFT quasi-local
  algebra `𝔄 = ‾⋃_O 𝔄(O)` (Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §1.3), with
  isometric local embeddings `ιLocalCStar` — unital `*`-homomorphisms `𝔄(O) →⋆ₐ[ℂ] 𝔄`, injective
  and with *closed* range, whose ranges are dense
  in `𝔄` only taken together (`denseRange_iUnion_ιLocalCStar`).

What the further structure of a net does to these algebras is with that structure: graded locality
passes to the quasi-local algebra in `QuantumSystem.Physics.LocalNet.Basic`, and the covariances of
a net act on it in `QuantumSystem.Physics.LocalNet.Covariance.QuasiLocal`.

## Notation

`𝔄(O)` and `𝓡(O)` in the prose above are documentation shorthand for the local C⋆-algebra
`N.algebra O` and the local von Neumann algebra `N.localVonNeumannAlgebra R O`; the convention —
and why neither is a Lean notation — is stated in full in `QuantumSystem.Physics.LocalNet.Isotony`.
-/

@[expose] public section

namespace CStarNet

variable {K : Type*} [Preorder K] [IsDirectedOrder K] [Nonempty K]
variable (N : CStarNet K)

/-! ### Algebra of local observables

These constructions apply to any net over a directed index set.
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

end CStar

end CStarNet
