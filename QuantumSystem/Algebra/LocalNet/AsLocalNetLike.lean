module

public import QuantumSystem.Algebra.LocalNetLike

/-!
# `LocalNet` as a `LocalNetLike` instance

This module witnesses the finite-dimensional `LocalNet` carrier as an instance of the
abstract `LocalNetLike` typeclass.  All structural data (per-site indices, region
algebras, isotony embedding, locality) come from the existing `LocalNet` API; only the
identity functor law `isotony_refl` requires a fresh proof at this layer, since it was
not previously needed by the concrete-finite formalization.
-/

@[expose] public section

namespace LocalNet

variable (L : LocalNet)

/-- The first projection of `(combineIdx (Subset.refl Λ)).symm` is the identity on
    `L.regionIdx Λ`: every site in the larger region (which equals `Λ`) lies in `Λ`,
    so the inner conditional in `combineIdx` always selects the first component. -/
private lemma combineIdx_subset_refl_symm_fst {Λ : Finset L.sites}
    (s : L.regionIdx Λ) :
    ((L.combineIdx (Finset.Subset.refl Λ)).symm s).1 = s := by
  funext ⟨v, hv⟩
  rfl

/-- The second component of `(combineIdx (Subset.refl Λ)).symm` lives in
    `L.regionIdx (Λ \ Λ)`, which is empty since `Λ \ Λ = ∅`.  Hence any two
    elements of this type are equal, giving a `Subsingleton` instance. -/
private instance regionIdx_sdiff_self_subsingleton (Λ : Finset L.sites) :
    Subsingleton (L.regionIdx (Λ \ Λ)) := by
  refine ⟨fun f g => ?_⟩
  funext ⟨v, hv⟩
  rw [Finset.sdiff_self] at hv
  exact absurd hv (Finset.notMem_empty _)

/-- **Functor law (identity):** the isotony embedding along `Subset.refl Λ` equals the
    identity `*`-algebra homomorphism on `L.localAlgebra Λ`. -/
theorem includeAlgebra_subset_refl (Λ : Finset L.sites) :
    L.includeAlgebra (Finset.Subset.refl Λ)
      = StarAlgHom.id ℂ (L.localAlgebra Λ) := by
  ext X s s'
  rw [includeAlgebra_apply]
  rw [if_pos (Subsingleton.elim _ _)]
  rw [combineIdx_subset_refl_symm_fst, combineIdx_subset_refl_symm_fst]
  rfl

/-- The finite-dimensional `LocalNet` is a `LocalNetLike` carrier on its site type.
    All data is reused from the concrete API; only the identity functor law is added
    here.  The instance is `noncomputable` because `includeAlgebra` and the underlying
    `Matrix`-based C*-algebra structure depend on classical choice. -/
noncomputable instance : LocalNetLike L.sites where
  localIdx := L.localIdx
  localAlgebra := L.localAlgebra
  isotony h := L.includeAlgebra h
  isotony_refl Λ := L.includeAlgebra_subset_refl Λ
  isLocal h₁ h₂ hd a b := L.isLocal h₁ h₂ hd a b

end LocalNet
