module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import QuantumSystem.Algebra.LocalNet
public import QuantumSystem.Algebra.QuasiLocalAlgebra.Isotony

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

/-- Concrete matrix local nets have injective isotony maps when every one-site
Hilbert-space index type is nonempty.  This is the concrete instance of the
optional `LocalNetLike.IsotonyInjective` mixin. -/
noncomputable instance [∀ s : L.sites, Nonempty (L.localIdx s)] :
    LocalNetLike.IsotonyInjective L.sites where
  isotony_injective {Λ Λ'} h := by
    change Function.Injective (L.includeAlgebra h)
    exact L.includeAlgebra_injective h

/-- Concrete matrix local nets satisfy the `*`-algebra-hom composition law for
isotony embeddings.  This is the concrete instance of the optional
`LocalNetLike.IsFunctorial` mixin and witnesses that `LocalNet` is an honest
functor from the inclusion preorder to `*`-algebras. -/
instance : LocalNetLike.IsFunctorial L.sites where
  isotony_comp {Λ₁ Λ₂ Λ₃} h₁₂ h₂₃ := by
    change L.includeAlgebra (h₁₂.trans h₂₃)
        = (L.includeAlgebra h₂₃).comp (L.includeAlgebra h₁₂)
    exact L.includeAlgebra_comp h₁₂ h₂₃

/-- Concrete matrix local nets carry a canonical local representation: the
matrix algebra `L.localAlgebra Λ = Matrix (L.regionIdx Λ) (L.regionIdx Λ) ℂ`
acts on `regionHilbert Λ = EuclideanSpace ℂ (regionIdx Λ)` via
`Matrix.toEuclideanCLM`.  This is the concrete instance of the optional
`LocalNetLike.HasLocalRepresentation` mixin. -/
noncomputable instance : LocalNetLike.HasLocalRepresentation L.sites where
  localRep Λ :=
    StarAlgHomClass.toStarAlgHom
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := L.regionIdx Λ))

/-- Concrete matrix local nets have a *faithful* local representation:
`Matrix.toEuclideanCLM` is a `*`-algebra equiv, so the bundled `localRep` is
injective.  This is the concrete instance of the optional
`LocalNetLike.HasFaithfulLocalRepresentation` mixin. -/
instance : LocalNetLike.HasFaithfulLocalRepresentation L.sites where
  localRep_injective Λ := by
    -- `localRep Λ` is the StarAlgHom coercion of the bijective StarAlgEquiv.
    -- Injectivity follows from the underlying bijection.
    intro X Y hXY
    have h := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := L.regionIdx Λ)
              |>.injective
    exact h hXY

/-! ### Compatibility between matrix isotony and operator-level lift

The concrete `includeAlgebra` and the abstract `regionLift` realise the same
"`M ⊗ 1_{Λ_total \ Λ}`" embedding from two different sides: `includeAlgebra`
acts on matrix entries, while `regionLift` acts on operators.  The lemma
below ties them together through `Matrix.toEuclideanCLM`, which is the
concrete instance of the abstract `HasIsotonyCompatibleLocalRep` mixin. -/

variable {L} in
private lemma combineIdx_pair_eq_regionLiftSwap
    {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    (b : L.regionIdx Λ) (a' : L.regionIdx Λ_total) :
    L.combineIdx h (b, ((L.combineIdx h).symm a').2)
      = LocalNetLike.regionLiftSwap (L := L.sites) h b a' := by
  funext s
  by_cases hs : s.val ∈ Λ
  · rw [combineIdx_apply_mem h b _ s hs,
      LocalNetLike.regionLiftSwap_apply_of_mem (L := L.sites) h b a' s hs]
  · rw [combineIdx_apply_not_mem h b _ s hs,
      LocalNetLike.regionLiftSwap_apply_of_not_mem (L := L.sites) h b a' s hs]
    rfl

variable {L} in
/-- **Concrete-vs-abstract compatibility.**  The matrix-level isotony
embedding `includeAlgebra`, viewed as a concrete operator on
`regionHilbert Λ_total` via `Matrix.toEuclideanCLM`, agrees with the
operator-level lift `regionLift` of `Matrix.toEuclideanCLM M`.

This is exactly the data demanded by `HasIsotonyCompatibleLocalRep` once
specialised to `LocalNet.sites` with `localRep = Matrix.toEuclideanCLM`. -/
theorem toEuclideanCLM_includeAlgebra
    {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total) (M : L.localAlgebra Λ) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := L.regionIdx Λ_total))
        (L.includeAlgebra h M)
      = LocalNetLike.regionLift (L := L.sites) h
          ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := L.regionIdx Λ)) M) := by
  ext v a'
  -- Goal coordinate-form via `ofLp_toEuclideanCLM`.
  change (Matrix.mulVec (L.includeAlgebra h M)
            (fun k : L.regionIdx Λ_total => (v : L.regionIdx Λ_total → ℂ) k)) a'
        = (LocalNetLike.regionLift (L := L.sites) h
              ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := L.regionIdx Λ)) M) v
            : L.regionIdx Λ_total → ℂ) a'
  rw [LocalNetLike.regionLift_apply_apply (L := L.sites)]
  unfold LocalNetLike.regionLiftCoeff
  change _ = Matrix.mulVec M
              (fun b : L.regionIdx Λ =>
                (LocalNetLike.vRestrict (L := L.sites) h v a'
                  : L.regionIdx Λ → ℂ) b)
              (LocalNetLike.regionLiftRestrict (L := L.sites) h a')
  -- Unfold both sides to `Finset.sum` form and align indices.
  simp only [Matrix.mulVec, dotProduct,
    LocalNetLike.vRestrict_apply (L := L.sites)]
  -- LHS: ∑ k, includeAlgebra h M a' k * v k
  -- RHS: ∑ b, M (regionLiftRestrict h a') b
  --             * v (regionLiftSwap h b a')
  rw [← (L.combineIdx h).sum_comp
        (fun k => L.includeAlgebra h M a' k * (v : L.regionIdx Λ_total → ℂ) k)]
  rw [Fintype.sum_prod_type]
  -- ∑ b, ∑ c, includeAlgebra h M a' (combineIdx h (b, c))
  --            * v (combineIdx h (b, c))
  have ha'_eq : a' = L.combineIdx h ((L.combineIdx h).symm a') :=
    ((L.combineIdx h).apply_symm_apply a').symm
  refine Finset.sum_congr rfl (fun b _ => ?_)
  -- For each b, evaluate the c-sum using `includeAlgebra_apply_combineIdx`.
  have hb_sum :
      (∑ c : L.regionIdx (Λ_total \ Λ),
          L.includeAlgebra h M a' (L.combineIdx h (b, c))
            * (v : L.regionIdx Λ_total → ℂ) (L.combineIdx h (b, c)))
        = M ((L.combineIdx h).symm a').1 b
            * (v : L.regionIdx Λ_total → ℂ)
                (L.combineIdx h (b, ((L.combineIdx h).symm a').2)) := by
    have hrewrite :
        (fun c : L.regionIdx (Λ_total \ Λ) =>
            L.includeAlgebra h M a' (L.combineIdx h (b, c))
              * (v : L.regionIdx Λ_total → ℂ) (L.combineIdx h (b, c)))
          = (fun c : L.regionIdx (Λ_total \ Λ) =>
              (if ((L.combineIdx h).symm a').2 = c then
                  M ((L.combineIdx h).symm a').1 b else 0)
                * (v : L.regionIdx Λ_total → ℂ) (L.combineIdx h (b, c))) := by
      funext c
      conv_lhs => rw [ha'_eq]
      rw [includeAlgebra_apply_combineIdx]
    rw [hrewrite]
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq Finset.univ ((L.combineIdx h).symm a').2
          (fun c => M ((L.combineIdx h).symm a').1 b
                      * (v : L.regionIdx Λ_total → ℂ)
                          (L.combineIdx h (b, c)))]
    rw [if_pos (Finset.mem_univ _)]
  rw [hb_sum]
  -- Match remaining indices via `combineIdx_pair_eq_regionLiftSwap` and the
  -- definitional identity `regionLiftRestrict h a' = ((combineIdx h).symm a').1`.
  rw [combineIdx_pair_eq_regionLiftSwap (L := L) h b a']
  rfl

/-- Concrete matrix local nets satisfy the abstract isotony / `localRep`
compatibility: applying `localRep` after `isotony` agrees with applying
`regionLift` after `localRep`.  This is the concrete instance of the
optional `LocalNetLike.HasIsotonyCompatibleLocalRep` mixin. -/
noncomputable instance [∀ s : L.sites, Nonempty (L.localIdx s)] :
    LocalNetLike.HasIsotonyCompatibleLocalRep L.sites where
  localRep_isotony h a := L.toEuclideanCLM_includeAlgebra h a

/-! ### C⋆-algebra structure on the concrete local algebras

The matrix algebra `L.localAlgebra Λ = Matrix (L.regionIdx Λ) (L.regionIdx Λ) ℂ`
is canonically a finite-dimensional C⋆-algebra under the operator norm pulled
back from `EuclideanSpace ℂ (L.regionIdx Λ) →L[ℂ] EuclideanSpace ℂ (L.regionIdx Λ)`
along `Matrix.toEuclideanCLM`.  Mathlib provides this via the scoped instances
in `Matrix.Norms.L2Operator`; we open that scope and re-export the resulting
`CStarAlgebra` instances. -/

open scoped Matrix.Norms.L2Operator in
/-- Concrete matrix local nets are unital C⋆-algebras at every finite region.
The structure is the L2 operator-norm pullback along `Matrix.toEuclideanCLM`. -/
noncomputable instance instCStarAlgebra_localAlgebra (Λ : Finset L.sites) :
    CStarAlgebra (L.localAlgebra Λ) := by
  unfold LocalNet.localAlgebra
  letI : NormedRing (Matrix (L.regionIdx Λ) (L.regionIdx Λ) ℂ) :=
    Matrix.instL2OpNormedRing
  letI : NormedAlgebra ℂ (Matrix (L.regionIdx Λ) (L.regionIdx Λ) ℂ) :=
    Matrix.instL2OpNormedAlgebra
  letI : CStarRing (Matrix (L.regionIdx Λ) (L.regionIdx Λ) ℂ) :=
    Matrix.instCStarRing
  haveI : CompleteSpace (Matrix (L.regionIdx Λ) (L.regionIdx Λ) ℂ) :=
    FiniteDimensional.complete ℂ _
  exact CStarAlgebra.mk

/-- Re-expose the C⋆-algebra structure at the abstract `LocalNetLike.localAlgebra`
projection, so downstream consumers working through the typeclass interface
inherit the C⋆-instance automatically. -/
noncomputable instance instCStarAlgebra_localNetLike_localAlgebra
    (Λ : Finset L.sites) :
    CStarAlgebra (LocalNetLike.localAlgebra (L := L.sites) Λ) :=
  inferInstanceAs (CStarAlgebra (L.localAlgebra Λ))

end LocalNet
