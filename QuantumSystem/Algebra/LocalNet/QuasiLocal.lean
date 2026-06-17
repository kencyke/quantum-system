module

public import QuantumSystem.Algebra.LocalNet.Locality
public import QuantumSystem.ForMathlib.Algebra.Colimit.DirectLimitStar
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.DirectLimit
public import QuantumSystem.ForMathlib.Topology.Algebra.CStarCompletion
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Quasi-local algebra of the local net

For a `LocalNet` on a (possibly infinite) lattice of sites, the **algebra of local observables**
is the algebraic inductive limit of the directed system of finite-region matrix algebras
`{𝔄(Λ) : Λ : Finset sites}` with the isotony embeddings `includeAlgebra (h : Λ ⊆ Λ')` as
connecting maps, and the **quasi-local C⋆-algebra** is its norm completion (Naaijkens 2012 §1.3,
Bratteli–Robinson Vol.2 §6.2).

* The directed system is genuine: the connecting maps compose (`includeAlgebra_trans_apply`)
  and the identity inclusion is the identity (`includeAlgebra_refl_apply`).
* `quasiLocalAlgebra` (the algebraic inductive limit) is a `ℂ`-`*`-algebra with cocone `ιLocal`,
  exhaustion `exists_ιLocal`, and locality `ιLocal_commute_of_disjoint`.
* In `section CStar` (assuming each site has a non-empty local index type, so the embeddings are
  injective hence isometric), the C⋆-norm makes it a pre-C⋆-algebra and `quasiLocalCStarAlgebra`
  (its completion) is a `CStarAlgebra`, with dense embeddings `ιLocalCStar`.
-/

@[expose] public section

namespace LocalNet

variable (L : LocalNet)

/-- The local net forms a directed system of `*`-algebras: the isotony embeddings compose
    and the identity inclusion is the identity (Phase 1 functoriality). -/
instance directedSystem :
    DirectedSystem (fun Λ : Finset L.sites => L.localAlgebra Λ)
      (fun _ _ h => ⇑(L.includeAlgebra h)) where
  map_self _ x := L.includeAlgebra_refl_apply x
  map_map _ _ _ hij hjk x := L.includeAlgebra_trans_apply hij hjk x

/-- The **algebra of local observables**: the algebraic inductive limit of the finite-region
    matrix algebras along the isotony embeddings. Its C*-completion is the quasi-local
    algebra of AQFT. -/
noncomputable abbrev quasiLocalAlgebra : Type _ :=
  DirectLimit (fun Λ : Finset L.sites => L.localAlgebra Λ)
    (fun _ _ h => L.includeAlgebra h)

/-- Componentwise behaviour of the involution (from the general `DirectLimit` `*`-ring
    instance in `ForMathlib`). The quasi-local algebra is a `*`-algebra over `ℂ`: its
    `Star`, `StarRing`, `Algebra ℂ` and `StarModule ℂ` instances come from the general
    direct-limit constructions, since `localAlgebra` is a `ℂ`-`*`-algebra and `includeAlgebra`
    is a `*`-algebra homomorphism. -/
@[simp] theorem star_mk {Λ : Finset L.sites} (X : L.localAlgebra Λ) :
    star (⟦⟨Λ, X⟩⟧ : L.quasiLocalAlgebra) = ⟦⟨Λ, star X⟩⟧ := rfl

/-- The canonical embedding `𝔄(Λ) ↪ 𝔄_loc` of a local algebra into the quasi-local algebra,
    as a unital ring homomorphism (the cocone of the inductive limit). -/
noncomputable def ιLocal (Λ : Finset L.sites) :
    L.localAlgebra Λ →+* L.quasiLocalAlgebra :=
  DirectLimit.Ring.of (fun Λ : Finset L.sites => L.localAlgebra Λ)
    (fun _ _ h => L.includeAlgebra h) Λ

/-- Compatibility of the cocone with the isotony embeddings: including `X` from `Λ` into the
    larger region `Λ'` and then into `𝔄_loc` is the same as including `X` directly. -/
@[simp] theorem ιLocal_includeAlgebra {Λ Λ' : Finset L.sites} (h : Λ ⊆ Λ') (X : L.localAlgebra Λ) :
    L.ιLocal Λ' (L.includeAlgebra h X) = L.ιLocal Λ X :=
  DirectLimit.Ring.of_f (G := fun Λ : Finset L.sites => L.localAlgebra Λ)
    (f := fun _ _ h => L.includeAlgebra h) h X

/-- The cocone is a `*`-homomorphism: it intertwines the local adjoint with the quasi-local
    adjoint. -/
@[simp] theorem ιLocal_star {Λ : Finset L.sites} (X : L.localAlgebra Λ) :
    L.ιLocal Λ (star X) = star (L.ιLocal Λ X) :=
  (star_mk (L := L) X).symm

/-- **Exhaustion**: every element of the quasi-local algebra is the image of a local
    observable from some finite region — the union of the local algebras is the whole limit. -/
theorem exists_ιLocal (z : L.quasiLocalAlgebra) : ∃ (Λ : Finset L.sites) (X : L.localAlgebra Λ),
    z = L.ιLocal Λ X := by
  induction z using DirectLimit.induction with
  | _ Λ X => exact ⟨Λ, X, rfl⟩

/-- **Locality in the quasi-local algebra**: observables localised in disjoint regions commute
    inside `𝔄_loc`. Lifts the bipartite locality (`includeAlgebra_commute_union`) along the
    ring-hom cocone. -/
theorem ιLocal_commute_of_disjoint {Λ₁ Λ₂ : Finset L.sites} (hd : Disjoint Λ₁ Λ₂)
    (X : L.localAlgebra Λ₁) (Y : L.localAlgebra Λ₂) :
    Commute (L.ιLocal Λ₁ X) (L.ιLocal Λ₂ Y) := by
  have h1 : L.ιLocal Λ₁ X
      = L.ιLocal (Λ₁ ∪ Λ₂) (L.includeAlgebra Finset.subset_union_left X) :=
    (L.ιLocal_includeAlgebra Finset.subset_union_left X).symm
  have h2 : L.ιLocal Λ₂ Y
      = L.ιLocal (Λ₁ ∪ Λ₂) (L.includeAlgebra Finset.subset_union_right Y) :=
    (L.ιLocal_includeAlgebra Finset.subset_union_right Y).symm
  rw [h1, h2]
  exact (L.includeAlgebra_commute_of_disjoint Finset.subset_union_left
    Finset.subset_union_right hd X Y).map (L.ιLocal (Λ₁ ∪ Λ₂))

/-! ### Quasi-local C⋆-algebra

Equipping the algebra of local observables with the C⋆-norm of the inductive limit (the isotony
embeddings are injective — using non-empty local dimensions — hence isometric) and completing
yields the quasi-local C⋆-algebra. The general construction lives in `ForMathlib`
(`DirectLimit.cstarNormedRing`, `UniformSpace.Completion.instCStarAlgebra`); here we supply the
net-specific inputs (matrix C⋆-algebras + injectivity). -/

section CStar

open scoped Matrix.Norms.L2Operator

variable [∀ s, Nonempty (L.localIdx s)]

/-- Each finite-region matrix algebra is a (complex) C⋆-algebra under the `L2Operator` norm.
    Stated for `localAlgebra` so the choice of the `L2Operator` norm does not leak to arbitrary
    matrices. -/
noncomputable instance instCStarAlgebraLocal (Λ : Finset L.sites) :
    CStarAlgebra (L.localAlgebra Λ) where

/-- The algebra of local observables is a normed ring under the C⋆-norm of the inductive limit. -/
noncomputable instance : NormedRing (L.quasiLocalAlgebra) :=
  DirectLimit.cstarNormedRing (fun _ _ h => L.includeAlgebra_injective h)

@[simp] theorem norm_mk {Λ : Finset L.sites} (X : L.localAlgebra Λ) :
    ‖(⟦⟨Λ, X⟩⟧ : L.quasiLocalAlgebra)‖ = ‖X‖ := rfl

/-- The C⋆-norm is compatible with the `ℂ`-algebra structure. -/
noncomputable instance : NormedAlgebra ℂ (L.quasiLocalAlgebra) where
  norm_smul_le c x := by
    induction x using DirectLimit.induction with
    | _ Λ X => rw [DirectLimit.smul_def, norm_mk, norm_mk]; exact norm_smul_le c X

/-- `star` is isometric on the algebra of local observables. -/
instance : NormedStarGroup (L.quasiLocalAlgebra) where
  norm_star_le x := by
    induction x using DirectLimit.induction with
    | _ Λ X => rw [star_mk, norm_mk, norm_mk]; exact (norm_star X).le

/-- The C⋆-identity holds on the algebra of local observables. -/
instance : CStarRing (L.quasiLocalAlgebra) where
  norm_mul_self_le x := by
    induction x using DirectLimit.induction with
    | _ Λ X => rw [star_mk, DirectLimit.mul_def, norm_mk, norm_mk]
               exact CStarRing.norm_mul_self_le X

/-- The **quasi-local C⋆-algebra** of the net: the completion of the algebra of local
    observables. This is the AQFT quasi-local algebra `𝔄 = ‾⋃_Λ 𝔄(Λ)` (Naaijkens 2012 §1.3,
    Bratteli–Robinson Vol.2 §6.2), obtained as the C⋆-inductive limit of the finite-region
    matrix algebras. -/
noncomputable abbrev quasiLocalCStarAlgebra : Type _ :=
  UniformSpace.Completion L.quasiLocalAlgebra

noncomputable example : CStarAlgebra L.quasiLocalCStarAlgebra := inferInstance

/-- The canonical embedding `𝔄(Λ) → 𝔄` of a local algebra into the quasi-local C⋆-algebra,
    as the completion coercion composed with the inductive-limit cocone. Its range is dense. -/
noncomputable def ιLocalCStar (Λ : Finset L.sites) :
    L.localAlgebra Λ → L.quasiLocalCStarAlgebra :=
  (↑) ∘ L.ιLocal Λ

/-- The local algebras are dense in the quasi-local C⋆-algebra: the union of the images of the
    `ιLocalCStar Λ` is dense (every element is a norm-limit of local observables). -/
theorem denseRange_iUnion_ιLocalCStar :
    Dense (⋃ Λ : Finset L.sites, Set.range (L.ιLocalCStar Λ)) := by
  refine UniformSpace.Completion.denseRange_coe.mono ?_
  rintro _ ⟨z, rfl⟩
  obtain ⟨Λ, X, rfl⟩ := L.exists_ιLocal z
  exact Set.mem_iUnion.2 ⟨Λ, X, rfl⟩

end CStar

end LocalNet
