module

public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Normed.Operator.Extend
public import QuantumSystem.Algebra.QuasiLocalAlgebra.InfiniteTensor.RegionDirectedOmega
public import QuantumSystem.Algebra.QuasiLocalAlgebra.RegionColimit

/-!
# `globalHilbert` as the reference-basis sector of the incomplete tensor product

For the canonical reference family
`Ω_ref s := EuclideanSpace.single (referenceBasis L s) 1`, the
incomplete-infinite-tensor-product reference sector
`globalHilbertOmega L Ω_ref` introduced in
`InfiniteTensor/RegionDirectedOmega.lean` is canonically isometrically
isomorphic to the basis-indexed `lp 2`-model `globalHilbert L` of
`GlobalHilbert.lean`.

The proof spike of Phase 3:

1. The Ω-extended basis vector `mkRegionVectorΩ Ω_ref h f` collapses to the
   ordinary region basis vector `EuclideanSpace.single (extendRegionTupleLe h f) 1`
   used in `RegionDirected.lean`.
2. The Ω-lift of `regionEmbed Λ` along the directed system gives a linear map
   `tensorPreHilbertΩ L Ω_ref →ₗ[ℂ] globalHilbert L` whose action on each
   region matches `regionEmbed Λ` (Phase 1).
3. This lift is an isometry on the algebraic colimit: inner products factor
   through a common upper bound `Λ ∪ Λ'`, where both sides reduce to the
   region-Hilbert inner product via `regionEmbed.inner_map_map` and
   `regionEmbedLeΩ.inner_map_map`.
4. Extending to the Cauchy completion gives a linear isometry
   `globalHilbertOmega L Ω_ref →ₗᵢ[ℂ] globalHilbert L`. Density of
   `⋃ Λ, range (regionEmbed Λ)` (Phase 2-b) makes the image dense, hence
   the isometry is surjective (closed isometric image + dense ⇒ everything),
   yielding the desired isomorphism.

## Main definitions

* `LocalNetLike.Ω_referenceBasis` — the canonical reference-basis unit family
  `s ↦ EuclideanSpace.single (referenceBasis L s) 1`.
* `LocalNetLike.globalHilbertOmegaReferenceBasisEquiv` — the linear isometry
  equivalence `globalHilbertOmega L Ω_referenceBasis ≃ₗᵢ[ℂ] globalHilbert L`.

## References

* Bratteli, Robinson, *Operator Algebras and Quantum Statistical Mechanics II*,
  §2.7.2 (incomplete infinite tensor product).
* Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §3.5.
-/

@[expose] public section

open scoped LocalNetLike InnerProductSpace
open Module

namespace LocalNetLike

variable {L : Type*} [DecidableEq L] [LocalNetLike L]
    [hL : ∀ s : L, Nonempty (LocalNetLike.localIdx (L := L) s)]

/-! ### The canonical reference-basis unit family -/

/-- The canonical reference-basis unit-vector family at each site,
`s ↦ EuclideanSpace.single (referenceBasis L s) 1`. -/
noncomputable def Ω_referenceBasis (s : L) : siteHilbert (L := L) s :=
  EuclideanSpace.single (referenceBasis L s) (1 : ℂ)

/-- The canonical reference-basis family is a unit family. -/
theorem Ω_referenceBasis_norm (s : L) :
    ‖Ω_referenceBasis (L := L) s‖ = 1 := by
  unfold Ω_referenceBasis
  rw [PiLp.norm_single]
  simp

/-! ### `mkRegionVectorΩ` reduces to the ordinary basis vector -/

/-- The Ω-extension at the reference-basis family collapses to the ordinary
region basis vector with index extended by `referenceBasis L`. -/
theorem mkRegionVectorΩ_referenceBasis {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (f : regionIdx (L := L) Λ) :
    mkRegionVectorΩ (L := L) (Ω_referenceBasis (L := L)) h f
      = (EuclideanSpace.single (extendRegionTupleLe h f) (1 : ℂ) :
          regionHilbert (L := L) Λ') := by
  ext g
  rw [mkRegionVectorΩ_ofLp_apply]
  -- Reduce each factor of the product:
  -- For s.1 ∈ Λ, the factor is [g s = f ⟨s.1, hs⟩].
  -- For s.1 ∉ Λ, the factor is (Ω_ref s.1) (g s) = [g s = referenceBasis L s.1].
  -- In both cases, the product is [g s = extendRegionTupleLe h f s].
  have hfac : ∀ s : Λ',
      (if hs : s.1 ∈ Λ then
         (if g s = f ⟨s.1, hs⟩ then (1 : ℂ) else 0)
       else (Ω_referenceBasis (L := L) s.1) (g s))
        = (if g s = extendRegionTupleLe h f s then (1 : ℂ) else 0) := by
    intro s
    by_cases hs : s.1 ∈ Λ
    · rw [dif_pos hs]
      rw [extendRegionTupleLe_apply_of_mem h _ hs]
    · rw [dif_neg hs]
      unfold Ω_referenceBasis
      rw [extendRegionTupleLe_apply_of_not_mem h _ hs]
      change (EuclideanSpace.single (referenceBasis L s.1) (1 : ℂ)).ofLp (g s) = _
      rw [PiLp.single_apply]
  simp_rw [hfac]
  -- Now the product is the indicator of `g = extendRegionTupleLe h f`.
  by_cases hgf : g = extendRegionTupleLe h f
  · subst hgf
    simp [EuclideanSpace.single]
  · obtain ⟨t, ht⟩ := Function.ne_iff.mp hgf
    rw [Finset.prod_eq_zero (Finset.mem_univ t) (by simp [ht])]
    rw [PiLp.single_apply, if_neg hgf]

/-! ### `regionEmbedLeΩ` at the reference basis equals `regionEmbedLe` -/

/-- The Ω-extension at the reference-basis family agrees with the
ordinary region-to-region isometric embedding `regionEmbedLe` from
`RegionDirected.lean`. -/
theorem regionEmbedLeΩ_referenceBasis_apply
    {Λ Λ' : Finset L} (h : Λ ⊆ Λ') (ξ : regionHilbert (L := L) Λ) :
    regionEmbedLeΩ (Ω_referenceBasis (L := L)) (Ω_referenceBasis_norm) h ξ
      = regionEmbedLe h ξ := by
  -- Both sides are linear; check on the basis of regionHilbert Λ.
  have hbasis :
      (regionEmbedLeΩ (Ω_referenceBasis (L := L)) Ω_referenceBasis_norm h).toLinearMap
        = (regionEmbedLe (L := L) h).toLinearMap := by
    refine ((EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).toBasis).ext ?_
    intro f
    simp [OrthonormalBasis.coe_toBasis,
          EuclideanSpace.basisFun_apply, mkRegionVectorΩ_referenceBasis]
  exact LinearMap.congr_fun hbasis ξ

/-! ### Coherence for the lift `tensorPreHilbertΩ → globalHilbert L` -/

/-- The family `regionEmbed Λ : regionHilbert Λ →ₗᵢ globalHilbert L` is a
co-cone over the directed system extended by `Ω_referenceBasis`. -/
theorem regionEmbed_apply_regionEmbedLeΩ_referenceBasis
    {Λ Λ' : Finset L} (h : Λ ⊆ Λ') (ξ : regionHilbert (L := L) Λ) :
    regionEmbed Λ' (regionEmbedLeΩ (Ω_referenceBasis (L := L))
        Ω_referenceBasis_norm h ξ)
      = regionEmbed Λ ξ := by
  rw [regionEmbedLeΩ_referenceBasis_apply, regionEmbed_apply_regionEmbedLe]

/-! ### The lift to `globalHilbert L` -/

/-- The linear lift of the Ω-tensor pre-Hilbert colimit (at the reference
basis) into the basis-indexed `lp 2`-model `globalHilbert L`. -/
noncomputable def liftRefMap :
    tensorPreHilbertΩ L (Ω_referenceBasis (L := L)) Ω_referenceBasis_norm
      →ₗ[ℂ] globalHilbert L :=
  Module.DirectLimit.lift (R := ℂ) (ι := Finset L)
    (G := fun Λ : Finset L => regionHilbert (L := L) Λ)
    (f := fun _ _ h =>
      (regionEmbedLeΩ (Ω_referenceBasis (L := L)) Ω_referenceBasis_norm h).toLinearMap)
    (g := fun Λ => (regionEmbed (L := L) Λ).toLinearMap)
    (Hg := fun _ _ h x => regionEmbed_apply_regionEmbedLeΩ_referenceBasis h x)

@[simp]
theorem liftRefMap_of (Λ : Finset L) (ξ : regionHilbert (L := L) Λ) :
    liftRefMap (tensorPreHilbertΩ.of (Ω_referenceBasis (L := L))
        Ω_referenceBasis_norm Λ ξ)
      = regionEmbed Λ ξ :=
  Module.DirectLimit.lift_of (R := ℂ) (ι := Finset L)
    (G := fun Λ : Finset L => regionHilbert (L := L) Λ)
    (f := fun _ _ h =>
      (regionEmbedLeΩ (Ω_referenceBasis (L := L)) Ω_referenceBasis_norm h).toLinearMap)
    (g := fun Λ => (regionEmbed (L := L) Λ).toLinearMap)
    (Hg := fun _ _ h x => regionEmbed_apply_regionEmbedLeΩ_referenceBasis h x)
    (i := Λ) ξ

/-! ### `liftRefMap` is an isometry on the algebraic colimit -/

/-- `liftRefMap` preserves the inner product on the algebraic colimit. -/
theorem liftRefMap_inner
    (z w : tensorPreHilbertΩ L (Ω_referenceBasis (L := L)) Ω_referenceBasis_norm) :
    ⟪liftRefMap z, liftRefMap w⟫_ℂ = ⟪z, w⟫_ℂ := by
  refine z.induction_on (fun Λ x => ?_)
  refine w.induction_on (fun Λ' y => ?_)
  -- Bridge between the raw `DirectLimit.of` produced by `induction_on` and the
  -- bundled `tensorPreHilbertΩ.of` used by `liftRefMap_of` and `inner_of_of`.
  change ⟪liftRefMap (tensorPreHilbertΩ.of (Ω_referenceBasis (L := L))
                Ω_referenceBasis_norm Λ x),
            liftRefMap (tensorPreHilbertΩ.of (Ω_referenceBasis (L := L))
                Ω_referenceBasis_norm Λ' y)⟫_ℂ
       = ⟪tensorPreHilbertΩ.of (Ω_referenceBasis (L := L))
                Ω_referenceBasis_norm Λ x,
            tensorPreHilbertΩ.of (Ω_referenceBasis (L := L))
                Ω_referenceBasis_norm Λ' y⟫_ℂ
  rw [liftRefMap_of, liftRefMap_of, tensorPreHilbertΩ.inner_of_of]
  -- Lift the LHS to the common region `Λ' ∪ Λ`.
  rw [show (regionEmbed Λ x : globalHilbert L)
        = regionEmbed (Λ' ∪ Λ) (regionEmbedLe
            (Finset.subset_union_right (s₁ := Λ') (s₂ := Λ)) x)
      from (regionEmbed_apply_regionEmbedLe _ _).symm,
      show (regionEmbed Λ' y : globalHilbert L)
        = regionEmbed (Λ' ∪ Λ) (regionEmbedLe
            (Finset.subset_union_left (s₁ := Λ') (s₂ := Λ)) y)
      from (regionEmbed_apply_regionEmbedLe _ _).symm]
  rw [(regionEmbed (L := L) (Λ' ∪ Λ)).inner_map_map]
  -- Unfold the RHS `innerWithLin`-shape and rewrite via
  -- `regionEmbedLeΩ_referenceBasis_apply`.
  change _ = star ⟪regionEmbedLeΩ (Ω_referenceBasis (L := L))
                      Ω_referenceBasis_norm
                      (Finset.subset_union_left (s₁ := Λ') (s₂ := Λ)) y,
                    regionEmbedLeΩ (Ω_referenceBasis (L := L))
                      Ω_referenceBasis_norm
                      (Finset.subset_union_right (s₁ := Λ') (s₂ := Λ)) x⟫_ℂ
  rw [regionEmbedLeΩ_referenceBasis_apply,
      regionEmbedLeΩ_referenceBasis_apply]
  exact (inner_conj_symm _ _).symm

/-! ### `liftRefMap` packaged as a linear isometry -/

/-- Linear-isometry packaging of `liftRefMap`: the algebraic colimit
`tensorPreHilbertΩ L Ω_referenceBasis` embeds isometrically into the basis
ℓ²-model `globalHilbert L`. -/
noncomputable def liftRefIsometry :
    tensorPreHilbertΩ L (Ω_referenceBasis (L := L)) Ω_referenceBasis_norm
      →ₗᵢ[ℂ] globalHilbert L :=
  (liftRefMap (L := L)).isometryOfInner liftRefMap_inner

@[simp]
theorem liftRefIsometry_of (Λ : Finset L) (ξ : regionHilbert (L := L) Λ) :
    liftRefIsometry (tensorPreHilbertΩ.of (Ω_referenceBasis (L := L))
        Ω_referenceBasis_norm Λ ξ)
      = regionEmbed Λ ξ := by
  change liftRefMap _ = _
  rw [liftRefMap_of]

/-! ### Density of the image of `liftRefMap` -/

/-- The image of `liftRefMap` contains every `regionEmbed Λ`-image, hence
the union over `Λ` of those, which is dense in `globalHilbert L`. -/
theorem denseRange_liftRefMap : DenseRange ⇑(liftRefMap (L := L)) := by
  refine Dense.mono ?_ dense_iUnion_regionEmbed_range
  intro y hy
  rw [Set.mem_iUnion] at hy
  obtain ⟨Λ, ξ, hξ⟩ := hy
  refine ⟨tensorPreHilbertΩ.of (Ω_referenceBasis (L := L)) Ω_referenceBasis_norm Λ ξ, ?_⟩
  rw [liftRefMap_of, hξ]

/-! ### The reference-basis sector identification -/

/-- The reference-basis sector of the incomplete infinite tensor product is
canonically (linear-)isometrically isomorphic to the basis ℓ²-model
`globalHilbert L`.

This is the Phase 3 proof spike: it identifies the existing concrete
`globalHilbert` with the special case `globalHilbertOmega L Ω_referenceBasis`
of the abstract Bratteli–Robinson §2.7.2 construction. -/
noncomputable def globalHilbertOmegaReferenceBasisEquiv :
    globalHilbertOmega L (Ω_referenceBasis (L := L)) Ω_referenceBasis_norm
      ≃ₗᵢ[ℂ] globalHilbert L :=
  LinearEquiv.extendOfIsometry
    (f := LinearEquiv.refl ℂ
            (tensorPreHilbertΩ L (Ω_referenceBasis (L := L)) Ω_referenceBasis_norm))
    (e₁ := (UniformSpace.Completion.toComplₗᵢ
              (E := tensorPreHilbertΩ L (Ω_referenceBasis (L := L))
                Ω_referenceBasis_norm)).toLinearMap)
    (e₂ := (liftRefMap (L := L)))
    (h_dense₁ := UniformSpace.Completion.denseRange_coe)
    (h_dense₂ := denseRange_liftRefMap)
    (h_norm := fun x => by
      -- Both `‖e₂ (f x)‖ = ‖liftRefMap x‖` and `‖e₁ x‖ = ‖toCompl x‖`
      -- collapse to `‖x‖` via the respective isometry lemmas.
      trans ‖x‖
      · exact liftRefIsometry.norm_map x
      · exact (UniformSpace.Completion.norm_coe x).symm)

end LocalNetLike
