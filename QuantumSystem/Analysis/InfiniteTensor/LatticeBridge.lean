module

public import QuantumSystem.Algebra.QuasiLocalAlgebra.Isotony
public import QuantumSystem.Algebra.QuasiLocalAlgebra.Locality
public import QuantumSystem.Algebra.QuasiLocalAlgebra.RegionColimit
public import QuantumSystem.Algebra.QuasiLocalAlgebra.Vacuum
public import QuantumSystem.Analysis.InfiniteTensor.SectorDecomp
public import QuantumSystem.Analysis.InfiniteTensor.SectorIsometry
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.PiTensorProduct

/-!
# Bridge from the pure ITP to the lattice/decomposable layer

This file is the boundary between the **pure ITP layer** (Phase 1–3) and
the **lattice layer** (`LocalNetLike` + `siteHilbert` + `referenceSectorHilbert`).
It first proves the reference-sector bridge

```
ITPSector (fun s => siteHilbert s) (referenceUnitFamily L)
    ≃ₗᵢ[ℂ] referenceSectorHilbert L
```

and then uses it to build the lattice-side decomposable Bratteli--Robinson
sector space and its local-operator API.

The pure layer's `ITPSector H Ω`, specialised to the lattice family
`H s := siteHilbert s` and the reference unit family
`Ω := referenceUnitFamily L`, is canonically isometric to the basis-indexed
`ℓ²` model `referenceSectorHilbert L` already present in
`QuantumSystem.Algebra.QuasiLocalAlgebra.GlobalHilbert`.  The decomposable
space `decomposableLatticeITP L` is the `ℓ²` direct sum over C₀ sector
classes of unit families on `siteHilbert`.

The finite-dimensionality of `siteHilbert s` (via `Fintype (localIdx s)`) is
used here to identify finite pure tensor products with the concrete lattice
finite-region spaces:

```
regionTensor (H := siteHilbert) Λ ≃ₗᵢ[ℂ] regionHilbert Λ.
```

This underwrites the `Basis.piTensorProduct`-based identification of finite
tensor products with `EuclideanSpace ℂ (regionIdx Λ)`, which in turn
embeds into `referenceSectorHilbert L` by extending tuples with
`referenceBasis L` outside the finite region.

## Main definitions and results

* `LocalNetLike.referenceUnitFamily L` — the unit-vector family at each
  site, given by `EuclideanSpace.single (referenceBasis L s) 1`.
* `LocalNetLike.regionTensorEquivRegionHilbert L Λ` — the finite-region
  isometric equivalence `regionTensor (H := siteHilbert) Λ ≃ₗᵢ[ℂ]
  regionHilbert Λ`.
* `LocalNetLike.combinedRegionEmbed L Λ` — the compatible finite-region map
  into `referenceSectorHilbert L`.
* `LocalNetLike.preReferenceSectorMap L`, `sectorReferenceIsom L`, and
  `referenceSectorEquiv L` — the colimit/completion bridge from the pure
  reference sector to the concrete reference-sector Hilbert space.
* `LocalNetLike.localEmbedRefSector`, `localEmbedSector`, and
  `localEmbedDecomp` — reference-sector, sectorwise, and decomposable-space
  local operators, with algebraic laws and locality/isotony results.
* `LocalNetLike.decomposableLatticeITP L` and `LocalNetLike.globalHilbert L`
  — the lattice BR sector-decomposition Hilbert space.
* `LocalNetLike.decomposableUnitaryActionLIE` and
  `LocalNetLike.decomposableVacuumVector L` — the current non-canonical
  sector-permuting unitary and the chosen reference-sector vacuum vector.

## Caveats

The arbitrary-sector constructions use `InfiniteTensor.UnitFamily.noncanonicalSectorEquivAny`,
which chooses per-site unitary rotations by `Classical.choice`.  Thus
`localEmbedSector`, `localEmbedDecomp`, and `decomposableUnitaryActionLIE`
are Hilbert-space constructions with good algebraic properties, but they are
not the canonical Bratteli--Robinson phase-coherent/functorial constructions.

The canonical replacement at the same-index level is now available in
`QuantumSystem/Analysis/InfiniteTensor/SectorIsometry.lean` as
`SectorEquivData` / `sectorEquivOfData`, with proven identity, inverse,
and composition laws (`sectorEquivOfData_refl`, `sectorEquivOfData_symm`,
`sectorEquivOfData_trans`).  Migrating the constructions in this file to
consume `SectorEquivData` (and its reindexed-transport extension for
group actions) is the path to functorial group representation laws — see
the closing `Phase 8 functoriality obstruction` discussion at the end of
this file for the residual gap.

## References

* Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §3.5.
* Bratteli, Robinson, *Operator Algebras and Quantum Statistical
  Mechanics II*, §2.7.2.
-/

@[expose] public section

namespace LocalNetLike

open InfiniteTensor

variable (L : Type*) [DecidableEq L] [LocalNetLike L]
  [hL : ∀ s : L, Nonempty (LocalNetLike.localIdx (L := L) s)]

/-- The reference unit-vector family at each site: the standard basis
vector `EuclideanSpace.single (referenceBasis L s) 1` in `siteHilbert s`.

This is the unit family `Ω` whose `ITPSector` is canonically isometric to
the lattice-side `referenceSectorHilbert L`. -/
noncomputable def referenceUnitFamily :
    UnitFamily (fun s : L => siteHilbert (L := L) s) where
  vec s := EuclideanSpace.single (referenceBasis L s) (1 : ℂ)
  norm_vec s := by
    change ‖EuclideanSpace.single (referenceBasis L s) (1 : ℂ)‖ = 1
    rw [show EuclideanSpace.single (referenceBasis L s) (1 : ℂ)
          = PiLp.single 2 (referenceBasis L s) (1 : ℂ) from rfl]
    rw [PiLp.norm_single]
    simp

@[simp]
theorem referenceUnitFamily_apply (s : L) :
    referenceUnitFamily L s
      = EuclideanSpace.single (referenceBasis L s) (1 : ℂ) := rfl

/-! ## Layer 1: regionTensor Λ ≃ₗᵢ regionHilbert Λ via Basis.piTensorProduct -/

/-- The basis on `regionTensor (siteHilbert ·) Λ` indexed by `regionIdx Λ`,
obtained by tensoring the EuclideanSpace standard bases per site. -/
noncomputable def regionTensorBasis (Λ : Finset L) :
    Module.Basis (regionIdx (L := L) Λ) ℂ
      (InfiniteTensor.regionTensor (H := siteHilbert (L := L)) Λ) :=
  Basis.piTensorProduct (fun s : {x // x ∈ Λ} =>
    (EuclideanSpace.basisFun (localIdx (L := L) s.val) ℂ).toBasis)

omit hL in
theorem regionTensorBasis_apply (Λ : Finset L) (f : regionIdx (L := L) Λ) :
    regionTensorBasis L Λ f
      = PiTensorProduct.tprod ℂ
          (fun s : {x // x ∈ Λ} => EuclideanSpace.single (f s) (1 : ℂ)) := by
  unfold regionTensorBasis
  rw [Basis.piTensorProduct_apply]
  refine congrArg (PiTensorProduct.tprod ℂ) ?_
  funext s
  rw [show ((EuclideanSpace.basisFun (localIdx (L := L) s.val) ℂ).toBasis (f s)
        : siteHilbert (L := L) s.val)
      = (EuclideanSpace.basisFun (localIdx (L := L) s.val) ℂ) (f s) by
    rw [OrthonormalBasis.coe_toBasis]]
  rw [EuclideanSpace.basisFun_apply]

omit hL in
/-- The basis vectors of `regionTensorBasis L Λ` are orthonormal with respect
to the inner product on `regionTensor (siteHilbert ·) Λ` from
`ForMathlib.Analysis.InnerProductSpace.PiTensorProduct`. -/
theorem regionTensorBasis_orthonormal (Λ : Finset L) :
    Orthonormal ℂ (regionTensorBasis L Λ) := by
  rw [orthonormal_iff_ite]
  intro f f'
  rw [regionTensorBasis_apply, regionTensorBasis_apply,
    ForMathlib.PiTensorProduct.inner_tprod_tprod]
  by_cases hff : f = f'
  · subst hff
    rw [if_pos rfl]
    refine (Finset.prod_eq_one (fun s _ => ?_)).trans rfl
    rw [@inner_self_eq_norm_sq_to_K ℂ]
    have hnorm : ‖EuclideanSpace.single (f s) (1 : ℂ)‖ = 1 := by
      rw [show EuclideanSpace.single (f s) (1 : ℂ) = PiLp.single 2 (f s) (1 : ℂ) from rfl]
      rw [PiLp.norm_single]
      simp
    rw [hnorm]
    simp
  · rw [if_neg hff]
    -- f ≠ f' means there is some s with f s ≠ f' s. The product has a zero factor.
    obtain ⟨s, hs⟩ : ∃ s, f s ≠ f' s := by
      by_contra hall
      push Not at hall
      exact hff (funext hall)
    refine Finset.prod_eq_zero (Finset.mem_univ s) ?_
    -- ⟨single (f s) 1, single (f' s) 1⟩ = 0 since f s ≠ f' s.
    rw [EuclideanSpace.inner_single_left]
    rw [show (EuclideanSpace.single (f' s) (1 : ℂ)).ofLp (f s)
        = if f s = f' s then (1 : ℂ) else 0 from PiLp.single_apply 2 ℂ _ _ _]
    rw [if_neg hs]
    simp

/-- The orthonormal basis on `regionTensor (siteHilbert ·) Λ` indexed by
`regionIdx Λ`. -/
noncomputable def regionTensorONB (Λ : Finset L) :
    OrthonormalBasis (regionIdx (L := L) Λ) ℂ
      (InfiniteTensor.regionTensor (H := siteHilbert (L := L)) Λ) :=
  (regionTensorBasis L Λ).toOrthonormalBasis (regionTensorBasis_orthonormal L Λ)

/-- **Layer 1**: the canonical isometric equivalence between the
algebraic tensor product `regionTensor (siteHilbert ·) Λ` and the
basis-indexed Hilbert space `regionHilbert Λ = EuclideanSpace ℂ (regionIdx Λ)`.

Built by pairing `regionTensorONB L Λ` with the standard ONB on
`regionHilbert Λ` via `OrthonormalBasis.equiv` along `Equiv.refl _`. -/
noncomputable def regionTensorEquivRegionHilbert (Λ : Finset L) :
    InfiniteTensor.regionTensor (H := siteHilbert (L := L)) Λ ≃ₗᵢ[ℂ]
      regionHilbert (L := L) Λ :=
  (regionTensorONB L Λ).equiv (EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ)
    (Equiv.refl _)

omit hL in
@[simp]
theorem regionTensorEquivRegionHilbert_basis (Λ : Finset L)
    (f : regionIdx (L := L) Λ) :
    regionTensorEquivRegionHilbert L Λ (regionTensorONB L Λ f)
      = EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ f := by
  unfold regionTensorEquivRegionHilbert
  rw [OrthonormalBasis.equiv_apply_basis]
  rfl

omit hL in
/-- Specialised form: image of the basis tprod `tprod (fun s => single (f s) 1)`
under `regionTensorEquivRegionHilbert L Λ` is the basis vector
`EuclideanSpace.single f 1` of `regionHilbert Λ`. -/
theorem regionTensorEquivRegionHilbert_tprod_basis (Λ : Finset L)
    (f : regionIdx (L := L) Λ) :
    regionTensorEquivRegionHilbert L Λ
        (PiTensorProduct.tprod ℂ
          (fun s : {x // x ∈ Λ} => EuclideanSpace.single (f s) (1 : ℂ)))
      = (EuclideanSpace.single f (1 : ℂ) : regionHilbert (L := L) Λ) := by
  have hONB : regionTensorONB L Λ f
      = PiTensorProduct.tprod ℂ
          (fun s : {x // x ∈ Λ} => EuclideanSpace.single (f s) (1 : ℂ)) := by
    have hcoe : (regionTensorONB L Λ f : InfiniteTensor.regionTensor (H := siteHilbert (L := L)) Λ)
        = regionTensorBasis L Λ f := by
      unfold regionTensorONB
      exact congrFun (Module.Basis.coe_toOrthonormalBasis _ _) f
    rw [hcoe]
    rw [regionTensorBasis_apply]
  rw [← hONB, regionTensorEquivRegionHilbert_basis]
  rw [EuclideanSpace.basisFun_apply]

/-! ## Layer 1+2 composition: regionTensor → referenceSectorHilbert -/

/-- The combined isometric embedding `regionTensor (siteHilbert ·) Λ →ₗᵢ[ℂ]
referenceSectorHilbert L`, obtained by composing Layer 1 (regionTensor ↔
regionHilbert) with Layer 2 (regionEmbed). -/
noncomputable def combinedRegionEmbed (Λ : Finset L) :
    InfiniteTensor.regionTensor (H := siteHilbert (L := L)) Λ →ₗᵢ[ℂ]
      referenceSectorHilbert L :=
  (regionEmbed Λ).comp (regionTensorEquivRegionHilbert L Λ).toLinearIsometry

@[simp]
theorem combinedRegionEmbed_tprod_basis (Λ : Finset L) (f : regionIdx (L := L) Λ) :
    combinedRegionEmbed L Λ
        (PiTensorProduct.tprod ℂ
          (fun s : {x // x ∈ Λ} => EuclideanSpace.single (f s) (1 : ℂ)))
      = (lp.single 2 (extendRegionTuple Λ f) (1 : ℂ) : referenceSectorHilbert L) := by
  unfold combinedRegionEmbed
  change regionEmbed Λ (regionTensorEquivRegionHilbert L Λ
    (PiTensorProduct.tprod ℂ
      (fun s : {x // x ∈ Λ} => EuclideanSpace.single (f s) (1 : ℂ)))) = _
  rw [regionTensorEquivRegionHilbert_tprod_basis, regionEmbed_apply_basis]

/-! ## Layer 3 (partial): cocycle compatibility on basis vectors -/

/-- **Cocycle compatibility on basis tprods**: the combined embedding
factors through the pure-side `regionEmbedLe` (with reference unit family).

For `f : regionIdx Λ` and `h : Λ ⊆ Λ'`, applying `regionEmbedLe (referenceUnitFamily L) h`
to the basis tprod `tprod (single (f s) 1)` and then `combinedRegionEmbed Λ'`
yields the same `lp.single` vector as `combinedRegionEmbed Λ` applied directly,
because both global tuples reduce to `extendRegionTuple Λ f`. -/
theorem combinedRegionEmbed_cocycle_basis {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (f : regionIdx (L := L) Λ) :
    combinedRegionEmbed L Λ'
        (InfiniteTensor.UnitFamily.regionEmbedLe (referenceUnitFamily L) h
          (PiTensorProduct.tprod ℂ
            (fun s : {x // x ∈ Λ} => EuclideanSpace.single (f s) (1 : ℂ))))
      = combinedRegionEmbed L Λ
          (PiTensorProduct.tprod ℂ
            (fun s : {x // x ∈ Λ} => EuclideanSpace.single (f s) (1 : ℂ))) := by
  rw [InfiniteTensor.UnitFamily.regionEmbedLe_tprod]
  -- LHS becomes combinedRegionEmbed Λ' (tprod (extendVec Ω h ξ))
  -- where ξ s = single (f s) 1, and extendVec Ω h ξ s' = single (extendRegionTupleLe h f s') 1.
  have hext : ((referenceUnitFamily L).extendVec h
        (fun s : {x // x ∈ Λ} => EuclideanSpace.single (f s) (1 : ℂ)))
      = (fun s' : {x // x ∈ Λ'} =>
          EuclideanSpace.single (extendRegionTupleLe h f s') (1 : ℂ)) := by
    funext s'
    by_cases hsΛ : s'.val ∈ Λ
    · rw [InfiniteTensor.UnitFamily.extendVec_inside _ _ _ _ hsΛ]
      rw [extendRegionTupleLe_apply_of_mem h _ hsΛ]
    · rw [InfiniteTensor.UnitFamily.extendVec_outside _ _ _ _ hsΛ]
      rw [extendRegionTupleLe_apply_of_not_mem h _ hsΛ]
      rfl
  rw [hext]
  rw [combinedRegionEmbed_tprod_basis, combinedRegionEmbed_tprod_basis]
  congr 1
  exact extendRegionTuple_extendRegionTupleLe h f

/-- **Cocycle compatibility on all of regionTensor**: the combined
embedding factors through the pure-side `regionEmbedLe` for arbitrary
elements (extended from basis tprods via `Basis.ext`). -/
theorem combinedRegionEmbed_cocycle {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (x : InfiniteTensor.regionTensor (H := siteHilbert (L := L)) Λ) :
    combinedRegionEmbed L Λ'
        (InfiniteTensor.UnitFamily.regionEmbedLe (referenceUnitFamily L) h x)
      = combinedRegionEmbed L Λ x := by
  have hext : (combinedRegionEmbed L Λ').toLinearMap.comp
        (InfiniteTensor.UnitFamily.regionEmbedLe (referenceUnitFamily L) h)
      = (combinedRegionEmbed L Λ).toLinearMap := by
    apply Module.Basis.ext (regionTensorBasis L Λ)
    intro f
    rw [LinearMap.comp_apply]
    rw [regionTensorBasis_apply]
    exact combinedRegionEmbed_cocycle_basis L h f
  exact congrFun (congrArg DFunLike.coe hext) x

/-! ## Layer 3 (continued): directed-system lift to preITPSector -/

/-- The directed-system lift: a single linear map from the algebraic colimit
`preITPSector (referenceUnitFamily L)` to the lattice reference sector
Hilbert space `referenceSectorHilbert L`. -/
noncomputable def preReferenceSectorMap :
    InfiniteTensor.UnitFamily.preITPSector (referenceUnitFamily L) →ₗ[ℂ]
      referenceSectorHilbert L :=
  Module.DirectLimit.lift ℂ (Finset L)
    (fun Λ : Finset L =>
      InfiniteTensor.regionTensor (H := siteHilbert (L := L)) Λ)
    (InfiniteTensor.UnitFamily.regionDirectedLink (referenceUnitFamily L))
    (fun Λ => (combinedRegionEmbed L Λ).toLinearMap)
    (fun _ _ h => combinedRegionEmbed_cocycle L h)

@[simp]
theorem preReferenceSectorMap_of (Λ : Finset L)
    (x : InfiniteTensor.regionTensor (H := siteHilbert (L := L)) Λ) :
    preReferenceSectorMap L
        (InfiniteTensor.UnitFamily.preITPSector.of (referenceUnitFamily L) Λ x)
      = combinedRegionEmbed L Λ x :=
  Module.DirectLimit.lift_of (R := ℂ)
    (G := fun Λ : Finset L =>
      InfiniteTensor.regionTensor (H := siteHilbert (L := L)) Λ)
    (f := InfiniteTensor.UnitFamily.regionDirectedLink (referenceUnitFamily L))
    _ _ x

/-- Inner-product preservation by `preReferenceSectorMap`: each finite-region
contribution preserves inner products via `combinedRegionEmbed`'s isometry. -/
theorem preReferenceSectorMap_inner
    (x y : InfiniteTensor.UnitFamily.preITPSector (referenceUnitFamily L)) :
    inner ℂ (preReferenceSectorMap L x) (preReferenceSectorMap L y)
      = inner ℂ x y := by
  obtain ⟨Λ, x', y', hx, hy⟩ :=
    InfiniteTensor.UnitFamily.preITPSector.exists_of₂ (referenceUnitFamily L) x y
  rw [← hx, ← hy, preReferenceSectorMap_of, preReferenceSectorMap_of]
  rw [InfiniteTensor.UnitFamily.inner_of_of (referenceUnitFamily L)]
  exact (combinedRegionEmbed L Λ).inner_map_map x' y'

/-- Bundle `preReferenceSectorMap` as a linear isometry on the pre-Hilbert
space `preITPSector (referenceUnitFamily L)`. -/
noncomputable def preReferenceSectorIsom :
    InfiniteTensor.UnitFamily.preITPSector (referenceUnitFamily L) →ₗᵢ[ℂ]
      referenceSectorHilbert L :=
  { preReferenceSectorMap L with
    norm_map' := fun x => by
      rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ]
      congr 1
      exact congrArg RCLike.re (preReferenceSectorMap_inner L x x) }

/-! ## Layer 3 (continued): completion lift to ITPSector

The completion lift extends `preReferenceSectorIsom` from the algebraic
colimit `preITPSector (referenceUnitFamily L)` to its Hilbert completion
`ITPSector (siteHilbert ·) (referenceUnitFamily L)`, with codomain the
already-complete `referenceSectorHilbert L`.

The construction uses `UniformSpace.Completion.extension` (which works
because the codomain is `CompleteSpace`), and verifies linearity,
continuity, and norm-preservation via `UniformSpace.Completion.induction_on`
density arguments. -/

/-- The completion lift as a function: extends `preReferenceSectorIsom`
along the dense embedding `preITPSector → ITPSector`, with values in the
complete `referenceSectorHilbert L`. -/
noncomputable def sectorReferenceFun :
    InfiniteTensor.UnitFamily.ITPSector (H := siteHilbert (L := L))
        (referenceUnitFamily L) → referenceSectorHilbert L :=
  UniformSpace.Completion.extension (preReferenceSectorIsom L)

theorem sectorReferenceFun_continuous :
    Continuous (sectorReferenceFun L) :=
  UniformSpace.Completion.continuous_extension

theorem sectorReferenceFun_coe' (x : InfiniteTensor.UnitFamily.preITPSector
    (referenceUnitFamily L)) :
    sectorReferenceFun L
        ((↑x : UniformSpace.Completion
            (InfiniteTensor.UnitFamily.preITPSector (referenceUnitFamily L))))
      = preReferenceSectorIsom L x :=
  UniformSpace.Completion.extension_coe
    ((preReferenceSectorIsom L).lipschitz.uniformContinuous) x

theorem sectorReferenceFun_coe (x : InfiniteTensor.UnitFamily.preITPSector
    (referenceUnitFamily L)) :
    sectorReferenceFun L
        ((InfiniteTensor.UnitFamily.ITPSector.fromPre (referenceUnitFamily L)) x)
      = preReferenceSectorIsom L x :=
  sectorReferenceFun_coe' L x

/-- `sectorReferenceFun` is linear. -/
theorem sectorReferenceFun_add
    (x y : InfiniteTensor.UnitFamily.ITPSector (H := siteHilbert (L := L))
        (referenceUnitFamily L)) :
    sectorReferenceFun L (x + y) = sectorReferenceFun L x + sectorReferenceFun L y := by
  refine UniformSpace.Completion.induction_on₂ x y
    (isClosed_eq ((sectorReferenceFun_continuous L).comp continuous_add)
      (((sectorReferenceFun_continuous L).comp continuous_fst).add
        ((sectorReferenceFun_continuous L).comp continuous_snd))) ?_
  intro a b
  change sectorReferenceFun L (((↑a : UniformSpace.Completion
        (InfiniteTensor.UnitFamily.preITPSector (referenceUnitFamily L))))
      + ((↑b : UniformSpace.Completion
        (InfiniteTensor.UnitFamily.preITPSector (referenceUnitFamily L)))))
    = sectorReferenceFun L ((↑a : UniformSpace.Completion
        (InfiniteTensor.UnitFamily.preITPSector (referenceUnitFamily L))))
    + sectorReferenceFun L ((↑b : UniformSpace.Completion
        (InfiniteTensor.UnitFamily.preITPSector (referenceUnitFamily L))))
  rw [← UniformSpace.Completion.coe_add a b]
  rw [sectorReferenceFun_coe' L (a + b),
    sectorReferenceFun_coe' L a, sectorReferenceFun_coe' L b]
  exact (preReferenceSectorIsom L).map_add a b

theorem sectorReferenceFun_smul (c : ℂ)
    (x : InfiniteTensor.UnitFamily.ITPSector (H := siteHilbert (L := L))
        (referenceUnitFamily L)) :
    sectorReferenceFun L (c • x) = c • sectorReferenceFun L x := by
  have hsmul_cont :
      Continuous fun y : InfiniteTensor.UnitFamily.ITPSector
          (H := siteHilbert (L := L)) (referenceUnitFamily L) => c • y :=
    Continuous.const_smul continuous_id c
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq ((sectorReferenceFun_continuous L).comp hsmul_cont)
      (Continuous.const_smul (sectorReferenceFun_continuous L) c)) ?_
  intro a
  change sectorReferenceFun L (c • ((↑a : UniformSpace.Completion
        (InfiniteTensor.UnitFamily.preITPSector (referenceUnitFamily L)))))
    = c • sectorReferenceFun L ((↑a : UniformSpace.Completion
        (InfiniteTensor.UnitFamily.preITPSector (referenceUnitFamily L))))
  rw [← UniformSpace.Completion.coe_smul c a]
  rw [sectorReferenceFun_coe' L (c • a), sectorReferenceFun_coe' L a]
  exact (preReferenceSectorIsom L).map_smul c a

/-- `sectorReferenceFun` is norm-preserving. -/
theorem sectorReferenceFun_norm
    (x : InfiniteTensor.UnitFamily.ITPSector (H := siteHilbert (L := L))
        (referenceUnitFamily L)) :
    ‖sectorReferenceFun L x‖ = ‖x‖ := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (continuous_norm.comp (sectorReferenceFun_continuous L))
      continuous_norm) ?_
  intro a
  rw [sectorReferenceFun_coe' L a]
  rw [(preReferenceSectorIsom L).norm_map a]
  exact (UniformSpace.Completion.norm_coe a).symm

/-- The completion lift bundled as a `LinearIsometry`. -/
noncomputable def sectorReferenceIsom :
    InfiniteTensor.UnitFamily.ITPSector (H := siteHilbert (L := L))
        (referenceUnitFamily L) →ₗᵢ[ℂ] referenceSectorHilbert L :=
  { toFun := sectorReferenceFun L
    map_add' := sectorReferenceFun_add L
    map_smul' := sectorReferenceFun_smul L
    norm_map' := sectorReferenceFun_norm L }

/-! ## Layer 3 (continued): surjectivity via density of regionEmbed images -/

/-- Image agreement: `combinedRegionEmbed L Λ x = sectorReferenceIsom L (fromPre (of Λ x))`. -/
theorem combinedRegionEmbed_eq_sectorReferenceIsom (Λ : Finset L)
    (x : InfiniteTensor.regionTensor (H := siteHilbert (L := L)) Λ) :
    combinedRegionEmbed L Λ x
      = sectorReferenceIsom L
          ((InfiniteTensor.UnitFamily.ITPSector.fromPre (referenceUnitFamily L))
            (InfiniteTensor.UnitFamily.preITPSector.of (referenceUnitFamily L)
              Λ x)) := by
  change combinedRegionEmbed L Λ x = sectorReferenceFun L _
  rw [sectorReferenceFun_coe]
  change combinedRegionEmbed L Λ x = preReferenceSectorMap L _
  rw [preReferenceSectorMap_of]

/-- Range of `regionEmbed Λ` is contained in range of `sectorReferenceIsom L`,
because `regionEmbed Λ` factors as `combinedRegionEmbed L Λ ∘
(regionTensorEquivRegionHilbert L Λ).symm`, and `combinedRegionEmbed L Λ`
factors through `sectorReferenceIsom L`. -/
theorem regionEmbed_range_subset_sectorReferenceIsom_range (Λ : Finset L) :
    Set.range (⇑(regionEmbed (L := L) Λ))
      ⊆ Set.range (sectorReferenceIsom L) := by
  rintro y ⟨ξ, rfl⟩
  -- ξ : regionHilbert Λ. ξ = regionTensorEquivRegionHilbert L Λ x for some x.
  let x := (regionTensorEquivRegionHilbert L Λ).symm ξ
  have hxξ : regionTensorEquivRegionHilbert L Λ x = ξ :=
    (regionTensorEquivRegionHilbert L Λ).apply_symm_apply ξ
  refine ⟨(InfiniteTensor.UnitFamily.ITPSector.fromPre (referenceUnitFamily L))
    (InfiniteTensor.UnitFamily.preITPSector.of (referenceUnitFamily L) Λ x), ?_⟩
  rw [← combinedRegionEmbed_eq_sectorReferenceIsom]
  unfold combinedRegionEmbed
  change regionEmbed Λ (regionTensorEquivRegionHilbert L Λ x) = regionEmbed Λ ξ
  rw [hxξ]

/-- The range of `sectorReferenceIsom L` is dense in `referenceSectorHilbert L`. -/
theorem dense_range_sectorReferenceIsom :
    DenseRange (sectorReferenceIsom L) := by
  refine Dense.mono ?_ (dense_iUnion_regionEmbed_range (L := L))
  intro y hy
  obtain ⟨Λ, hyΛ⟩ := Set.mem_iUnion.mp hy
  exact regionEmbed_range_subset_sectorReferenceIsom_range L Λ hyΛ

/-- The range of `sectorReferenceIsom L` is closed (LinearIsometry from
complete domain). -/
theorem isClosed_range_sectorReferenceIsom :
    IsClosed (Set.range (sectorReferenceIsom L)) := by
  exact (sectorReferenceIsom L).isometry.isUniformInducing.isComplete_range.isClosed

/-- `sectorReferenceIsom L` is surjective: combination of dense range +
closed range. -/
theorem sectorReferenceIsom_surjective :
    Function.Surjective (sectorReferenceIsom L) := by
  have hrange : Set.range (sectorReferenceIsom L) = Set.univ := by
    have hclosed : closure (Set.range (sectorReferenceIsom L))
        = Set.range (sectorReferenceIsom L) :=
      (isClosed_range_sectorReferenceIsom L).closure_eq
    have hdense : closure (Set.range (sectorReferenceIsom L)) = Set.univ :=
      (dense_range_sectorReferenceIsom L).closure_eq
    exact hclosed.symm.trans hdense
  exact Set.range_eq_univ.mp hrange

/-- **Phase 5 main result**: the canonical isometric equivalence between
the pure incomplete infinite tensor product sector at the reference unit
family and the lattice reference sector Hilbert space. -/
noncomputable def referenceSectorEquiv :
    InfiniteTensor.UnitFamily.ITPSector (H := siteHilbert (L := L))
        (referenceUnitFamily L) ≃ₗᵢ[ℂ] referenceSectorHilbert L :=
  LinearIsometryEquiv.ofSurjective (sectorReferenceIsom L)
    (sectorReferenceIsom_surjective L)

/-! ## Phase 6a (reference sector): transport `localEmbed` via the bridge

The migration plan's Phase 6a calls for *sectorwise* local operators
`localEmbedSector Ω Λ M : ITPSector siteHilbert Ω →L[ℂ] ITPSector
siteHilbert Ω` for arbitrary unit families `Ω`.

For the **reference sector** specifically (`Ω = referenceUnitFamily L`),
the existing `LocalEmbed.lean` infrastructure provides a fully developed
`localEmbed Λ M : referenceSectorHilbert L →L[ℂ] referenceSectorHilbert L`
with all algebraic and norm-bound properties.  Phase 5's
`referenceSectorEquiv` lets us transport this canonically to an action on
`ITPSector siteHilbert (referenceUnitFamily L)`, giving Phase 6a's
deliverable on the reference sector.

The general-`Ω` case requires a colimit-level "M ⊗ id_{S\Λ}"
construction directly on `regionTensor S` for each finite `S ⊇ Λ`, then
`Module.DirectLimit.lift` and completion lift.  This is structurally
parallel to Phase 5's `combinedRegionEmbed` chain but acts on operators
rather than vectors.  That canonical colimit-level construction remains a
follow-up; this file provides the non-canonical transport version below. -/

/-- **Phase 6a (reference sector)**: the sectorwise local-operator action
for the reference sector, transported from the existing
`localEmbed Λ M : referenceSectorHilbert L →L[ℂ] referenceSectorHilbert L`
through `referenceSectorEquiv L`. -/
noncomputable def localEmbedRefSector (Λ : Finset L)
    (M : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ) :
    InfiniteTensor.UnitFamily.ITPSector (H := siteHilbert (L := L))
        (referenceUnitFamily L)
      →L[ℂ] InfiniteTensor.UnitFamily.ITPSector
        (H := siteHilbert (L := L)) (referenceUnitFamily L) :=
  let e := (referenceSectorEquiv L).toContinuousLinearEquiv
  e.symm.toContinuousLinearMap.comp ((localEmbed Λ M).comp e.toContinuousLinearMap)

@[simp]
theorem localEmbedRefSector_apply (Λ : Finset L)
    (M : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ)
    (x : InfiniteTensor.UnitFamily.ITPSector (H := siteHilbert (L := L))
        (referenceUnitFamily L)) :
    localEmbedRefSector L Λ M x
      = (referenceSectorEquiv L).symm
          (localEmbed Λ M (referenceSectorEquiv L x)) := rfl

/-- Compatibility: `localEmbedRefSector` agrees with `localEmbed Λ M`
through `referenceSectorEquiv`.  This is the conjugation diagram

```
ITPSector siteHilbert (referenceUnitFamily L) ──localEmbedRefSector L Λ M──→ ITPSector …
            │                                                                  │
            │ referenceSectorEquiv L                referenceSectorEquiv L      │
            ↓                                                                  ↓
      referenceSectorHilbert L  ─────────localEmbed Λ M────────→  referenceSectorHilbert L
```

commuting. -/
theorem referenceSectorEquiv_localEmbedRefSector (Λ : Finset L)
    (M : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ)
    (x : InfiniteTensor.UnitFamily.ITPSector (H := siteHilbert (L := L))
        (referenceUnitFamily L)) :
    referenceSectorEquiv L (localEmbedRefSector L Λ M x)
      = localEmbed Λ M (referenceSectorEquiv L x) := by
  rw [localEmbedRefSector_apply]
  exact (referenceSectorEquiv L).apply_symm_apply _

/-! ### Algebraic laws for `localEmbedRefSector`, transported from `localEmbed` -/

/-- `localEmbedRefSector L Λ` is additive in `M`. -/
theorem localEmbedRefSector_add (Λ : Finset L)
    (M N : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ) :
    localEmbedRefSector L Λ (M + N)
      = localEmbedRefSector L Λ M + localEmbedRefSector L Λ N := by
  ext x
  rw [localEmbedRefSector_apply, localEmbed_add, ContinuousLinearMap.add_apply,
    map_add, ContinuousLinearMap.add_apply, localEmbedRefSector_apply,
    localEmbedRefSector_apply]

/-- `localEmbedRefSector L Λ` is ℂ-linear in `M`. -/
theorem localEmbedRefSector_smul (Λ : Finset L) (c : ℂ)
    (M : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ) :
    localEmbedRefSector L Λ (c • M)
      = c • localEmbedRefSector L Λ M := by
  ext x
  rw [localEmbedRefSector_apply, localEmbed_smul, ContinuousLinearMap.smul_apply,
    map_smul, ContinuousLinearMap.smul_apply, localEmbedRefSector_apply]

/-- `localEmbedRefSector L Λ` sends 0 to 0. -/
theorem localEmbedRefSector_zero (Λ : Finset L) :
    localEmbedRefSector L Λ 0 = 0 := by
  ext x
  rw [localEmbedRefSector_apply, localEmbed_zero, ContinuousLinearMap.zero_apply,
    map_zero, ContinuousLinearMap.zero_apply]

/-- Composition law: applying `localEmbedRefSector L Λ` to a product of
two operators on the same region is the product of their sector
embeddings.  Inherited from `localEmbed_mul` via the
`referenceSectorEquiv` conjugation. -/
theorem localEmbedRefSector_comp (Λ : Finset L)
    (M N : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ) :
    localEmbedRefSector L Λ (M.comp N)
      = (localEmbedRefSector L Λ M).comp (localEmbedRefSector L Λ N) := by
  ext x
  rw [localEmbedRefSector_apply, localEmbed_mul, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, localEmbedRefSector_apply,
    localEmbedRefSector_apply, LinearIsometryEquiv.apply_symm_apply]

/-- Bundled star algebra structure: `localEmbedRefSector L Λ` is a
non-unital `*`-algebra homomorphism (additive, scalar-linear,
multiplicative, star-preserving) inherited from `localEmbedHom Λ` via
conjugation by `referenceSectorEquiv L`.

This packages the additive, scalar, multiplicative, and (when needed)
star laws into a single bundled object for downstream use. -/
noncomputable def localEmbedRefSectorHom (Λ : Finset L) :
    (regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ) →ₗ[ℂ]
      InfiniteTensor.UnitFamily.ITPSector (H := siteHilbert (L := L))
          (referenceUnitFamily L)
        →L[ℂ] InfiniteTensor.UnitFamily.ITPSector
          (H := siteHilbert (L := L)) (referenceUnitFamily L) :=
  { toFun := localEmbedRefSector L Λ
    map_add' := localEmbedRefSector_add L Λ
    map_smul' := localEmbedRefSector_smul L Λ }

@[simp]
theorem localEmbedRefSectorHom_apply (Λ : Finset L)
    (M : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ) :
    localEmbedRefSectorHom L Λ M = localEmbedRefSector L Λ M := rfl

/-- The unit law: `localEmbedRefSector L Λ` sends `1` to `1`. -/
theorem localEmbedRefSector_one (Λ : Finset L) :
    localEmbedRefSector L Λ 1 = 1 := by
  ext x
  rw [localEmbedRefSector_apply]
  rw [show (1 : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ)
      = ContinuousLinearMap.id ℂ (regionHilbert (L := L) Λ) from rfl]
  rw [localEmbed_one]
  change (referenceSectorEquiv L).symm
      (ContinuousLinearMap.id ℂ _ ((referenceSectorEquiv L) x)) = x
  rw [ContinuousLinearMap.id_apply]
  exact (referenceSectorEquiv L).symm_apply_apply x

/-- Multiplication law on the same region. -/
theorem localEmbedRefSector_mul (Λ : Finset L)
    (M N : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ) :
    localEmbedRefSector L Λ (M * N)
      = localEmbedRefSector L Λ M * localEmbedRefSector L Λ N := by
  rw [show (M * N : regionHilbert (L := L) Λ →L[ℂ] _) = M.comp N from rfl,
    localEmbedRefSector_comp]
  rfl

/-- Star (adjoint) law: `localEmbedRefSector L Λ` is star-preserving.
Inherited from `localEmbed_star` via the unitary `referenceSectorEquiv L`. -/
theorem localEmbedRefSector_star (Λ : Finset L)
    (M : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ) :
    star (localEmbedRefSector L Λ M) = localEmbedRefSector L Λ (star M) := by
  unfold localEmbedRefSector
  change ContinuousLinearMap.adjoint
      (((referenceSectorEquiv L).toContinuousLinearEquiv.symm.toContinuousLinearMap.comp
        ((localEmbed Λ M).comp
          (referenceSectorEquiv L).toContinuousLinearEquiv.toContinuousLinearMap)))
    = (referenceSectorEquiv L).toContinuousLinearEquiv.symm.toContinuousLinearMap.comp
        ((localEmbed Λ (star M)).comp
          (referenceSectorEquiv L).toContinuousLinearEquiv.toContinuousLinearMap)
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp]
  rw [show ContinuousLinearMap.adjoint
        ((referenceSectorEquiv L).toContinuousLinearEquiv.symm.toContinuousLinearMap)
      = (referenceSectorEquiv L).toContinuousLinearEquiv.toContinuousLinearMap from
    LinearIsometryEquiv.adjoint_eq_symm (referenceSectorEquiv L).symm]
  rw [show ContinuousLinearMap.adjoint
        ((referenceSectorEquiv L).toContinuousLinearEquiv.toContinuousLinearMap)
      = (referenceSectorEquiv L).toContinuousLinearEquiv.symm.toContinuousLinearMap from
    LinearIsometryEquiv.adjoint_eq_symm (referenceSectorEquiv L)]
  rw [show ContinuousLinearMap.adjoint (localEmbed Λ M) = localEmbed Λ (star M) from
    (localEmbed_star Λ M).symm]
  rfl

/-! ## Phase 9b transports: vacuum vector and group action on the sector -/

/-- The vacuum vector transported into the pure-ITP reference sector. -/
noncomputable def vacuumVectorSector :
    InfiniteTensor.UnitFamily.ITPSector (H := siteHilbert (L := L))
        (referenceUnitFamily L) :=
  (referenceSectorEquiv L).symm (vacuumVector L)

@[simp]
theorem referenceSectorEquiv_vacuumVectorSector :
    referenceSectorEquiv L (vacuumVectorSector L) = vacuumVector L := by
  unfold vacuumVectorSector
  exact (referenceSectorEquiv L).apply_symm_apply _

/-- The group-action unitary transported to the pure-ITP reference sector. -/
noncomputable def unitaryActionSector
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G) :
    InfiniteTensor.UnitFamily.ITPSector (H := siteHilbert (L := L))
        (referenceUnitFamily L) ≃ₗᵢ[ℂ] InfiniteTensor.UnitFamily.ITPSector
        (H := siteHilbert (L := L)) (referenceUnitFamily L) :=
  (referenceSectorEquiv L).trans
    ((act.unitaryAction g).trans (referenceSectorEquiv L).symm)

@[simp]
theorem unitaryActionSector_apply
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G)
    (x : InfiniteTensor.UnitFamily.ITPSector (H := siteHilbert (L := L))
        (referenceUnitFamily L)) :
    unitaryActionSector L act g x
      = (referenceSectorEquiv L).symm
          (act.unitaryAction g (referenceSectorEquiv L x)) := rfl

/-- **`G`-invariance of the transported vacuum**: `unitaryActionSector` fixes
`vacuumVectorSector L`.  Inherited from `unitaryAction_vacuumVector` via
`referenceSectorEquiv L`. -/
theorem unitaryActionSector_vacuumVectorSector
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G) :
    unitaryActionSector L act g (vacuumVectorSector L) = vacuumVectorSector L := by
  rw [unitaryActionSector_apply, referenceSectorEquiv_vacuumVectorSector,
    HasGroupAction.unitaryAction_vacuumVector]
  rfl

/-- The `g = 1` action is the identity.  Inherited from `unitaryAction_one`. -/
theorem unitaryActionSector_one
    {G : Type*} [Group G] (act : HasGroupAction L G) [act.IsGenuineAction] :
    unitaryActionSector L act (1 : G) = LinearIsometryEquiv.refl ℂ _ := by
  ext x
  rw [unitaryActionSector_apply, act.unitaryAction_one]
  exact (referenceSectorEquiv L).symm_apply_apply x

/-- Multiplicativity: `unitaryActionSector (g₁ * g₂) = unitaryActionSector g₁ ∘
unitaryActionSector g₂`.  Inherited from `unitaryAction_mul`. -/
theorem unitaryActionSector_mul
    {G : Type*} [Group G] (act : HasGroupAction L G) [act.IsGenuineAction]
    (g₁ g₂ : G) :
    unitaryActionSector L act (g₁ * g₂)
      = (unitaryActionSector L act g₂).trans (unitaryActionSector L act g₁) := by
  ext x
  rw [unitaryActionSector_apply, act.unitaryAction_mul,
    LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.trans_apply]
  rw [unitaryActionSector_apply, unitaryActionSector_apply,
    LinearIsometryEquiv.apply_symm_apply]

/-! ## Phase 6a (general Ω): sectorwise local operators via sectorEquivAny

The migration plan's Phase 6a calls for a *canonical* construction of
`localEmbedSector Ω Λ M : ITPSector siteHilbert Ω →L[ℂ] ITPSector
siteHilbert Ω` that preserves the finite-deviation structure
(`(M ξ)_s = ξ_s = Ω_s` for `s ∉ Λ`).  The canonical construction goes
via the colimit-level "M ⊗ id_{S\Λ}" action on `regionTensor S` for
each `S ⊇ Λ`, which requires the tensor-product splitting
`regionTensor S ≃ regionTensor Λ ⊗ regionTensor (S \ Λ)`.  That is
substantial mathematics deferred to a follow-up.

Here we provide the **non-canonical** version via `sectorEquivAny`
transport from the reference sector.  This satisfies the Phase 6a
type signature and uniform norm bound, but the action depends on the
`Classical.choose` of unitary rotations between Ω and the reference
family (Phase 3a's `chooseRotation`), so it does *not* canonically
preserve the finite-deviation property.

The reference-sector specialisation `localEmbedRefSector` (above) is
canonical via `referenceSectorEquiv`. -/

/-- **Phase 6a (general Ω)**: sectorwise local operator on
`ITPSector siteHilbert Ω` for arbitrary `Ω : UnitFamily (siteHilbert ·)`,
defined by transporting `localEmbedRefSector` through Phase 3a's
`sectorEquivAny`.  Non-canonical: depends on the (Classical-choice
driven) unitary rotations in `sectorEquivAny`. -/
noncomputable def localEmbedSector
    (Ω : InfiniteTensor.UnitFamily (siteHilbert (L := L) ·))
    (Λ : Finset L)
    (M : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ) :
    InfiniteTensor.UnitFamily.ITPSector (H := siteHilbert (L := L)) Ω
      →L[ℂ] InfiniteTensor.UnitFamily.ITPSector
        (H := siteHilbert (L := L)) Ω :=
  let e := InfiniteTensor.UnitFamily.noncanonicalSectorEquivAny Ω (referenceUnitFamily L)
  e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((localEmbedRefSector L Λ M).comp e.toContinuousLinearEquiv.toContinuousLinearMap)

@[simp]
theorem localEmbedSector_apply
    (Ω : InfiniteTensor.UnitFamily (siteHilbert (L := L) ·)) (Λ : Finset L)
    (M : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ)
    (x : InfiniteTensor.UnitFamily.ITPSector (H := siteHilbert (L := L)) Ω) :
    localEmbedSector L Ω Λ M x
      = (InfiniteTensor.UnitFamily.noncanonicalSectorEquivAny Ω (referenceUnitFamily L)).symm
          (localEmbedRefSector L Λ M
            (InfiniteTensor.UnitFamily.noncanonicalSectorEquivAny Ω (referenceUnitFamily L) x)) :=
  rfl

/-! ### Algebraic laws for `localEmbedSector` -/

theorem localEmbedSector_add
    (Ω : InfiniteTensor.UnitFamily (siteHilbert (L := L) ·)) (Λ : Finset L)
    (M N : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ) :
    localEmbedSector L Ω Λ (M + N)
      = localEmbedSector L Ω Λ M + localEmbedSector L Ω Λ N := by
  ext x
  rw [localEmbedSector_apply, localEmbedRefSector_add, ContinuousLinearMap.add_apply,
    map_add, ContinuousLinearMap.add_apply, localEmbedSector_apply,
    localEmbedSector_apply]

theorem localEmbedSector_smul
    (Ω : InfiniteTensor.UnitFamily (siteHilbert (L := L) ·)) (Λ : Finset L)
    (c : ℂ) (M : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ) :
    localEmbedSector L Ω Λ (c • M)
      = c • localEmbedSector L Ω Λ M := by
  ext x
  rw [localEmbedSector_apply, localEmbedRefSector_smul,
    ContinuousLinearMap.smul_apply, map_smul, ContinuousLinearMap.smul_apply,
    localEmbedSector_apply]

theorem localEmbedSector_zero
    (Ω : InfiniteTensor.UnitFamily (siteHilbert (L := L) ·)) (Λ : Finset L) :
    localEmbedSector L Ω Λ 0 = 0 := by
  ext x
  rw [localEmbedSector_apply, localEmbedRefSector_zero,
    ContinuousLinearMap.zero_apply, map_zero, ContinuousLinearMap.zero_apply]

theorem localEmbedSector_comp
    (Ω : InfiniteTensor.UnitFamily (siteHilbert (L := L) ·)) (Λ : Finset L)
    (M N : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ) :
    localEmbedSector L Ω Λ (M.comp N)
      = (localEmbedSector L Ω Λ M).comp (localEmbedSector L Ω Λ N) := by
  ext x
  rw [localEmbedSector_apply, localEmbedRefSector_comp,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    localEmbedSector_apply, localEmbedSector_apply,
    LinearIsometryEquiv.apply_symm_apply]

/-- Unit law: `localEmbedSector L Ω Λ` sends `1` to `1`. -/
theorem localEmbedSector_one
    (Ω : InfiniteTensor.UnitFamily (siteHilbert (L := L) ·)) (Λ : Finset L) :
    localEmbedSector L Ω Λ 1 = 1 := by
  ext x
  rw [localEmbedSector_apply, localEmbedRefSector_one,
    ContinuousLinearMap.one_apply]
  exact (InfiniteTensor.UnitFamily.noncanonicalSectorEquivAny Ω
    (referenceUnitFamily L)).symm_apply_apply x

/-- Multiplication law: `localEmbedSector L Ω Λ (M * N) = (sector M) * (sector N)`. -/
theorem localEmbedSector_mul
    (Ω : InfiniteTensor.UnitFamily (siteHilbert (L := L) ·)) (Λ : Finset L)
    (M N : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ) :
    localEmbedSector L Ω Λ (M * N)
      = localEmbedSector L Ω Λ M * localEmbedSector L Ω Λ N := by
  rw [show (M * N : regionHilbert (L := L) Λ →L[ℂ] _) = M.comp N from rfl,
    localEmbedSector_comp]
  rfl

/-- Star (adjoint) law: `localEmbedSector L Ω Λ` is star-preserving.
Inherited from `localEmbedRefSector_star` via the unitary
`InfiniteTensor.UnitFamily.noncanonicalSectorEquivAny Ω (referenceUnitFamily L)`.
The proof uses `eq_adjoint_iff` to avoid heavy `change`-driven kernel
unification on the long `sectorEquivAny`-conjugated composition. -/
theorem localEmbedSector_star
    (Ω : InfiniteTensor.UnitFamily (siteHilbert (L := L) ·)) (Λ : Finset L)
    (M : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ) :
    star (localEmbedSector L Ω Λ M) = localEmbedSector L Ω Λ (star M) := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  rw [localEmbedSector_apply, localEmbedSector_apply,
    ← LinearIsometryEquiv.inner_map_map
      (InfiniteTensor.UnitFamily.noncanonicalSectorEquivAny Ω (referenceUnitFamily L))
      ((InfiniteTensor.UnitFamily.noncanonicalSectorEquivAny Ω (referenceUnitFamily L)).symm
        (localEmbedRefSector L Λ (star M)
          (InfiniteTensor.UnitFamily.noncanonicalSectorEquivAny Ω (referenceUnitFamily L) x))) y,
    LinearIsometryEquiv.apply_symm_apply,
    ← LinearIsometryEquiv.inner_map_map
      (InfiniteTensor.UnitFamily.noncanonicalSectorEquivAny Ω (referenceUnitFamily L)) x
      ((InfiniteTensor.UnitFamily.noncanonicalSectorEquivAny Ω (referenceUnitFamily L)).symm
        (localEmbedRefSector L Λ M
          (InfiniteTensor.UnitFamily.noncanonicalSectorEquivAny Ω (referenceUnitFamily L) y))),
    LinearIsometryEquiv.apply_symm_apply,
    show localEmbedRefSector L Λ (star M)
        = ContinuousLinearMap.adjoint (localEmbedRefSector L Λ M) from
      (localEmbedRefSector_star L Λ M).symm]
  exact (localEmbedRefSector L Λ M).adjoint_inner_left _ _

/-! ## Phase 6b: fiberwise lift to the decomposable BR sector space -/

/-- The norm of `localEmbedSector` is bounded uniformly in Ω by the norm
of the underlying `localEmbed Λ M`.  Uniform boundedness across sectors
is the prerequisite for assembling a single operator on
`decomposableTensorProduct`. -/
theorem norm_localEmbedSector_le_localEmbed
    (Ω : InfiniteTensor.UnitFamily (siteHilbert (L := L) ·)) (Λ : Finset L)
    (M : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ)
    (x : InfiniteTensor.UnitFamily.ITPSector (H := siteHilbert (L := L)) Ω) :
    ‖localEmbedSector L Ω Λ M x‖ ≤ ‖localEmbed Λ M‖ * ‖x‖ := by
  rw [localEmbedSector_apply]
  have h1 : ‖(InfiniteTensor.UnitFamily.noncanonicalSectorEquivAny Ω (referenceUnitFamily L)).symm
        (localEmbedRefSector L Λ M
          (InfiniteTensor.UnitFamily.noncanonicalSectorEquivAny Ω (referenceUnitFamily L) x))‖
      = ‖localEmbedRefSector L Λ M
          (InfiniteTensor.UnitFamily.noncanonicalSectorEquivAny Ω (referenceUnitFamily L) x)‖ :=
    LinearIsometryEquiv.norm_map _ _
  rw [h1]
  have h2 : ‖localEmbedRefSector L Λ M
        (InfiniteTensor.UnitFamily.noncanonicalSectorEquivAny Ω (referenceUnitFamily L) x)‖
      = ‖(referenceSectorEquiv L).symm
          (localEmbed Λ M (referenceSectorEquiv L
            (InfiniteTensor.UnitFamily.noncanonicalSectorEquivAny Ω (referenceUnitFamily L) x)))‖ :=
    rfl
  rw [h2, LinearIsometryEquiv.norm_map]
  refine (ContinuousLinearMap.le_opNorm (localEmbed Λ M) _).trans ?_
  rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]

/-- The lattice-side decomposable Bratteli–Robinson sector decomposition
Hilbert space, specialised to `H = siteHilbert (L := L)`.

Defined directly as the underlying `lp` (rather than going through
`InfiniteTensor.decomposableTensorProduct`) so the FunLike coercion
`↥(lp E 2) → ∀ q, E q` is reducibly available downstream and the
elaboration of Phase 6b stays under the heartbeat budget. -/
noncomputable abbrev decomposableLatticeITP : Type _ :=
  lp (fun q : Quotient (InfiniteTensor.UnitFamily.c0Equiv
        (H := fun s : L => siteHilbert (L := L) s)) =>
      InfiniteTensor.UnitFamily.ITPSector
        (H := fun s : L => siteHilbert (L := L) s) q.out) 2

/-- **Phase 9c**: the infinite-site Hilbert space of the lattice quantum
system is the BR sector decomposition Hilbert space
`decomposableLatticeITP L`.  The single-sector model
`referenceSectorHilbert L` is retained as one fiber, embedded via
`referenceSectorClass L` and `referenceSectorEquiv L`. -/
noncomputable abbrev globalHilbert : Type _ := decomposableLatticeITP L

/-! ## Phase 6b: fiberwise lift to the decomposable BR sector space

The construction is split into smaller lemmas, each operating on a
narrower type, to keep individual `whnf` /`isDefEq` calls under the
heartbeat budget for elaboration through

```
decomposableTensorProduct ⊃ lp E 2 ⊃ ↥AddSubgroup with
  E q = ITPSector H q.out
```

Helper lemmas use generic dependent-function and operator-family
variables (no `lp` wrapping, no `localEmbedSector` unfolding) so the
outer-level type-class chain and definitional unfolding are avoided. -/

/-- Generic Memℓp 2 closure under uniformly-bounded fiberwise operators.
This avoids unfolding `localEmbedSector` in the type signature. -/
theorem memℓp_uniform_apply_aux
    {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℂ (E i)]
    (T : (i : ι) → E i →L[ℂ] E i)
    {C : ℝ} (hC_nn : 0 ≤ C) (hT : ∀ i a, ‖T i a‖ ≤ C * ‖a‖)
    (f : (i : ι) → E i)
    (hf : Memℓp f 2) :
    Memℓp (fun i => T i (f i)) 2 := by
  have hCf : Memℓp ((C : ℝ) • f) 2 := hf.const_smul _
  refine hCf.mono' (fun i => ?_)
  show ‖T i (f i)‖ ≤ ‖((C : ℝ) • f) i‖
  rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hC_nn]
  exact hT i (f i)


/-! ### Generic norm bound aux (avoids unfolding `localEmbedSector`) -/

/-- Generic uniform norm bound on the lp version of fiberwise application. -/
theorem norm_uniform_apply_aux
    {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℂ (E i)]
    (T : (i : ι) → E i →L[ℂ] E i)
    {C : ℝ} (hC_nn : 0 ≤ C) (hT : ∀ i a, ‖T i a‖ ≤ C * ‖a‖)
    (x : lp E 2) :
    ‖(⟨fun i => T i (x i),
        memℓp_uniform_apply_aux T hC_nn hT _ (lp.memℓp x)⟩ : lp E 2)‖
      ≤ C * ‖x‖ := by
  have htwo : (0 : ℝ) < (2 : ENNReal).toReal := by
    rw [ENNReal.toReal_ofNat]; norm_num
  set y : lp E 2 := ⟨fun i => T i (x i),
    memℓp_uniform_apply_aux T hC_nn hT _ (lp.memℓp x)⟩ with hy
  have h_y_sq : ‖y‖ ^ (2 : ℕ) = ∑' i, ‖T i (x i)‖ ^ (2 : ℕ) := by
    have h := lp.norm_rpow_eq_tsum (p := 2) htwo y
    rw [show ((2 : ENNReal).toReal : ℝ) = 2 from by norm_num] at h
    simpa [Real.rpow_two] using h
  have h_x_sq : ‖x‖ ^ (2 : ℕ) = ∑' i, ‖x i‖ ^ (2 : ℕ) := by
    have h := lp.norm_rpow_eq_tsum (p := 2) htwo x
    rw [show ((2 : ENNReal).toReal : ℝ) = 2 from by norm_num] at h
    simpa [Real.rpow_two] using h
  have h_pointwise : ∀ i, ‖T i (x i)‖ ^ (2 : ℕ) ≤ C ^ 2 * ‖x i‖ ^ (2 : ℕ) := by
    intro i
    have h := hT i (x i)
    have h_nn := norm_nonneg (T i (x i))
    have hsq : ‖T i (x i)‖ ^ (2 : ℕ) ≤ (C * ‖x i‖) ^ 2 :=
      pow_le_pow_left₀ h_nn h 2
    rw [mul_pow] at hsq
    exact hsq
  have h_sum_le : ∑' i, ‖T i (x i)‖ ^ (2 : ℕ) ≤ C ^ 2 * ∑' i, ‖x i‖ ^ (2 : ℕ) := by
    rw [← tsum_mul_left]
    refine Summable.tsum_le_tsum h_pointwise ?_ ?_
    · have h := (memℓp_uniform_apply_aux T hC_nn hT _ (lp.memℓp x)).summable htwo
      rw [show ((2 : ENNReal).toReal : ℝ) = 2 from by norm_num] at h
      simpa [Real.rpow_two] using h
    · have h := ((lp.memℓp x).summable htwo).mul_left (C ^ 2)
      rw [show ((2 : ENNReal).toReal : ℝ) = 2 from by norm_num] at h
      simpa [Real.rpow_two] using h
  have h_y_sq_le : ‖y‖ ^ (2 : ℕ) ≤ (C * ‖x‖) ^ 2 := by
    rw [h_y_sq, mul_pow, h_x_sq]; exact h_sum_le
  have h_rhs_nn : 0 ≤ C * ‖x‖ := mul_nonneg hC_nn (norm_nonneg _)
  exact (abs_le_of_sq_le_sq' h_y_sq_le h_rhs_nn).2

/-- Generic linear-map version of fiberwise application. -/
noncomputable def linearMap_uniform_apply_aux
    {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℂ (E i)]
    (T : (i : ι) → E i →L[ℂ] E i)
    {C : ℝ} (hC_nn : 0 ≤ C) (hT : ∀ i a, ‖T i a‖ ≤ C * ‖a‖) :
    lp E 2 →ₗ[ℂ] lp E 2 where
  toFun x := ⟨fun i => T i (x i), memℓp_uniform_apply_aux T hC_nn hT _ (lp.memℓp x)⟩
  map_add' x y := by
    apply lp.ext
    funext i
    change T i ((x + y) i) = T i (x i) + T i (y i)
    rw [lp.coeFn_add, Pi.add_apply, map_add]
  map_smul' c x := by
    apply lp.ext
    funext i
    change T i ((c • x) i) = c • T i (x i)
    rw [lp.coeFn_smul, Pi.smul_apply, map_smul]

/-- Generic continuous linear map version of fiberwise application. -/
noncomputable def clm_uniform_apply_aux
    {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℂ (E i)]
    (T : (i : ι) → E i →L[ℂ] E i)
    {C : ℝ} (hC_nn : 0 ≤ C) (hT : ∀ i a, ‖T i a‖ ≤ C * ‖a‖) :
    lp E 2 →L[ℂ] lp E 2 :=
  LinearMap.mkContinuous (linearMap_uniform_apply_aux T hC_nn hT) C
    (fun x => norm_uniform_apply_aux T hC_nn hT x)

theorem clm_uniform_apply_aux_apply_coord
    {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℂ (E i)]
    (T : (i : ι) → E i →L[ℂ] E i)
    {C : ℝ} (hC_nn : 0 ≤ C) (hT : ∀ i a, ‖T i a‖ ≤ C * ‖a‖)
    (x : lp E 2) (i : ι) :
    (clm_uniform_apply_aux T hC_nn hT x) i = T i (x i) := rfl

/-- Norm bound on `star (T i)` inherited from the bound on `T i`.
The op-norm of the adjoint equals the op-norm of the original, so the
fiberwise bound `‖T i a‖ ≤ C * ‖a‖` upgrades to `‖star (T i) a‖ ≤
C * ‖a‖`. -/
theorem clm_uniform_apply_aux_star_bound
    {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℂ (E i)] [∀ i, CompleteSpace (E i)]
    (T : (i : ι) → E i →L[ℂ] E i)
    {C : ℝ} (hC_nn : 0 ≤ C) (hT : ∀ i a, ‖T i a‖ ≤ C * ‖a‖)
    (i : ι) (a : E i) :
    ‖(star (T i)) a‖ ≤ C * ‖a‖ := by
  have hT_norm : ‖T i‖ ≤ C :=
    ContinuousLinearMap.opNorm_le_bound _ hC_nn (hT i)
  have h_star_norm : ‖star (T i)‖ = ‖T i‖ :=
    LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint (T i)
  calc ‖(star (T i)) a‖
      ≤ ‖star (T i)‖ * ‖a‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖T i‖ * ‖a‖ := by rw [h_star_norm]
    _ ≤ C * ‖a‖ := mul_le_mul_of_nonneg_right hT_norm (norm_nonneg _)

/-- Generic fiberwise-diagonal `clm_uniform_apply_aux` adjoint formula:
the star of the diagonal action is the diagonal of the fiberwise stars.
The proof uses `lp.inner_eq_tsum` and the uniqueness of adjoints
(`ContinuousLinearMap.eq_adjoint_iff`). -/
theorem clm_uniform_apply_aux_star
    {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℂ (E i)] [∀ i, CompleteSpace (E i)]
    (T : (i : ι) → E i →L[ℂ] E i)
    {C : ℝ} (hC_nn : 0 ≤ C) (hT : ∀ i a, ‖T i a‖ ≤ C * ‖a‖) :
    star (clm_uniform_apply_aux T hC_nn hT)
      = clm_uniform_apply_aux (fun i => star (T i)) hC_nn
          (clm_uniform_apply_aux_star_bound T hC_nn hT) := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  congr 1
  funext i
  change inner ℂ (ContinuousLinearMap.adjoint (T i) (x i)) (y i)
    = inner ℂ (x i) ((T i) (y i))
  exact (T i).adjoint_inner_left _ _

/-! ### Phase 6b deliverable: instantiate the generic aux -/

/-- **Phase 6b main result**: the fiberwise sectorwise local-operator action,
bundled as a continuous linear map on the decomposable BR sector
decomposition Hilbert space `decomposableLatticeITP L`. -/
noncomputable def localEmbedDecomp (Λ : Finset L)
    (M : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ) :
    decomposableLatticeITP L →L[ℂ] decomposableLatticeITP L :=
  clm_uniform_apply_aux
    (E := fun q : Quotient (InfiniteTensor.UnitFamily.c0Equiv
          (H := fun s : L => siteHilbert (L := L) s)) =>
        InfiniteTensor.UnitFamily.ITPSector
          (H := fun s : L => siteHilbert (L := L) s) q.out)
    (T := fun q => localEmbedSector L q.out Λ M)
    (C := ‖localEmbed Λ M‖)
    (norm_nonneg _)
    (fun q a => norm_localEmbedSector_le_localEmbed L q.out Λ M a)

@[simp]
theorem localEmbedDecomp_apply_coord (Λ : Finset L)
    (M : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ)
    (x : decomposableLatticeITP L) (q) :
    (localEmbedDecomp L Λ M x) q
      = localEmbedSector L q.out Λ M (x q) := rfl

/-! ### Algebraic laws on `localEmbedDecomp Λ` (in `M`) -/

theorem localEmbedDecomp_zero (Λ : Finset L) :
    localEmbedDecomp L Λ 0 = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext q
  rw [localEmbedDecomp_apply_coord, localEmbedSector_zero,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.zero_apply,
    lp.coeFn_zero, Pi.zero_apply]

theorem localEmbedDecomp_add (Λ : Finset L)
    (M N : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ) :
    localEmbedDecomp L Λ (M + N)
      = localEmbedDecomp L Λ M + localEmbedDecomp L Λ N := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext q
  rw [localEmbedDecomp_apply_coord, localEmbedSector_add,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
    lp.coeFn_add, Pi.add_apply, localEmbedDecomp_apply_coord,
    localEmbedDecomp_apply_coord]

theorem localEmbedDecomp_smul (Λ : Finset L) (c : ℂ)
    (M : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ) :
    localEmbedDecomp L Λ (c • M) = c • localEmbedDecomp L Λ M := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext q
  rw [localEmbedDecomp_apply_coord, localEmbedSector_smul,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
    lp.coeFn_smul, Pi.smul_apply, localEmbedDecomp_apply_coord]

theorem localEmbedDecomp_one (Λ : Finset L) :
    localEmbedDecomp L Λ 1 = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext q
  rw [localEmbedDecomp_apply_coord, localEmbedSector_one,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.one_apply]

theorem localEmbedDecomp_mul (Λ : Finset L)
    (M N : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ) :
    localEmbedDecomp L Λ (M * N)
      = localEmbedDecomp L Λ M * localEmbedDecomp L Λ N := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext q
  rw [localEmbedDecomp_apply_coord, localEmbedSector_mul,
    ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
    localEmbedDecomp_apply_coord, localEmbedDecomp_apply_coord]

/-- Star (adjoint) law for `localEmbedDecomp`: it is star-preserving.
The proof uses `eq_adjoint_iff` + `lp.inner_eq_tsum` to reduce to
fiberwise `localEmbedSector_star` + `adjoint_inner_left`. -/
theorem localEmbedDecomp_star (Λ : Finset L)
    (M : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ) :
    star (localEmbedDecomp L Λ M) = localEmbedDecomp L Λ (star M) := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr (fun q => ?_)
  rw [localEmbedDecomp_apply_coord, localEmbedDecomp_apply_coord,
    show localEmbedSector L q.out Λ (star M)
        = ContinuousLinearMap.adjoint (localEmbedSector L q.out Λ M) from
      (localEmbedSector_star L q.out Λ M).symm]
  exact (localEmbedSector L q.out Λ M).adjoint_inner_left _ _

/-! ### `localEmbedDecomp` bundled as a unital algebra homomorphism -/

/-- The map `M ↦ localEmbedDecomp Λ M` is a non-unital `*`-algebra-style ring
homomorphism from operators on `regionHilbert Λ` to operators on
`decomposableLatticeITP L` (treating `Λ`-region operators with composition
as multiplication). -/
noncomputable def localEmbedDecompRingHom (Λ : Finset L) :
    (regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ) →+*
      (decomposableLatticeITP L →L[ℂ] decomposableLatticeITP L) where
  toFun := localEmbedDecomp L Λ
  map_one' := localEmbedDecomp_one L Λ
  map_mul' := localEmbedDecomp_mul L Λ
  map_zero' := localEmbedDecomp_zero L Λ
  map_add' := localEmbedDecomp_add L Λ

@[simp]
theorem localEmbedDecompRingHom_apply (Λ : Finset L)
    (M : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ) :
    localEmbedDecompRingHom L Λ M = localEmbedDecomp L Λ M := rfl

/-- The map `M ↦ localEmbedDecomp Λ M` bundled as a unital `*`-algebra
homomorphism from operators on `regionHilbert Λ` to operators on
`decomposableLatticeITP L`.  This upgrades `localEmbedDecompRingHom`
with `commutes'` (algebra structure) and `map_star'`
(`localEmbedDecomp_star`). -/
noncomputable def localEmbedDecompStarHom (Λ : Finset L) :
    (regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ) →⋆ₐ[ℂ]
      (decomposableLatticeITP L →L[ℂ] decomposableLatticeITP L) where
  toFun := localEmbedDecomp L Λ
  map_one' := localEmbedDecomp_one L Λ
  map_mul' := localEmbedDecomp_mul L Λ
  map_zero' := localEmbedDecomp_zero L Λ
  map_add' := localEmbedDecomp_add L Λ
  commutes' c := by
    rw [show algebraMap ℂ
          (regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ) c
        = c • (1 : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ)
        from Algebra.algebraMap_eq_smul_one c]
    rw [localEmbedDecomp_smul, localEmbedDecomp_one]
    exact (Algebra.algebraMap_eq_smul_one c).symm
  map_star' M := (localEmbedDecomp_star L Λ M).symm

@[simp]
theorem localEmbedDecompStarHom_apply (Λ : Finset L)
    (M : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ) :
    localEmbedDecompStarHom L Λ M = localEmbedDecomp L Λ M := rfl

/-! ### Phase 7: Decomposable-space subalgebras and quasi-local algebra -/

/-- The local subalgebra at finite region `Λ`, viewed as a (non-star)
subalgebra of `decomposableLatticeITP L →L[ℂ] decomposableLatticeITP L`.
This is the decomposable-space variant of `localSubalgebra Λ`.

The smul-compatibility making this a `Subalgebra ℂ ...` (rather than just
a `Subring`) is supplied via `localEmbedDecomp_smul`. -/
noncomputable def localSubalgebraDecomp (Λ : Finset L) :
    Subalgebra ℂ (decomposableLatticeITP L →L[ℂ] decomposableLatticeITP L) where
  __ := (localEmbedDecompRingHom L Λ).range
  algebraMap_mem' c := by
    refine ⟨c • ContinuousLinearMap.id ℂ _, ?_⟩
    change localEmbedDecomp L Λ (c • ContinuousLinearMap.id ℂ _) =
      algebraMap ℂ _ c
    rw [localEmbedDecomp_smul]
    rw [show (ContinuousLinearMap.id ℂ (regionHilbert (L := L) Λ)
        : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ) = 1 from rfl]
    rw [localEmbedDecomp_one]
    rfl

/-- Algebraic core for the decomposable space:
`⨆ Λ : Finset L, localSubalgebraDecomp Λ`. -/
noncomputable def quasiLocalSubalgDecomp :
    Subalgebra ℂ (decomposableLatticeITP L →L[ℂ] decomposableLatticeITP L) :=
  ⨆ Λ : Finset L, localSubalgebraDecomp L Λ

/-- The **quasi-local algebra on the decomposable BR sector decomposition**:
the norm closure of the local algebraic core. -/
noncomputable def quasiLocalDecomp :
    Subalgebra ℂ (decomposableLatticeITP L →L[ℂ] decomposableLatticeITP L) :=
  (quasiLocalSubalgDecomp L).topologicalClosure

/-- The local subalgebra at finite region `Λ`, bundled as a
`StarSubalgebra` using `localEmbedDecomp_star` for the closure under
star. -/
noncomputable def localStarSubalgebraDecomp (Λ : Finset L) :
    StarSubalgebra ℂ (decomposableLatticeITP L →L[ℂ] decomposableLatticeITP L) where
  toSubalgebra := localSubalgebraDecomp L Λ
  star_mem' := by
    rintro T ⟨M, hM⟩
    refine ⟨star M, ?_⟩
    rw [localEmbedDecompRingHom_apply, ← localEmbedDecomp_star, ← hM,
      localEmbedDecompRingHom_apply]

/-- Algebraic core for the decomposable space, bundled as a
`StarSubalgebra`. -/
noncomputable def quasiLocalStarSubalgDecomp :
    StarSubalgebra ℂ (decomposableLatticeITP L →L[ℂ] decomposableLatticeITP L) :=
  ⨆ Λ : Finset L, localStarSubalgebraDecomp L Λ

/-- The **quasi-local *-algebra on the decomposable BR sector
decomposition**: the norm closure of the local algebraic core, viewed as
a `StarSubalgebra`. -/
noncomputable def quasiLocalStarDecomp :
    StarSubalgebra ℂ (decomposableLatticeITP L →L[ℂ] decomposableLatticeITP L) :=
  (quasiLocalStarSubalgDecomp L).topologicalClosure

/-- Each local subalgebra is contained in the algebraic quasi-local core. -/
theorem localSubalgebraDecomp_le_quasiLocalSubalgDecomp (Λ : Finset L) :
    localSubalgebraDecomp L Λ ≤ quasiLocalSubalgDecomp L :=
  le_iSup (fun Λ : Finset L => localSubalgebraDecomp L Λ) Λ

/-- Each local subalgebra is contained in the quasi-local algebra. -/
theorem localSubalgebraDecomp_le_quasiLocalDecomp (Λ : Finset L) :
    localSubalgebraDecomp L Λ ≤ quasiLocalDecomp L :=
  (localSubalgebraDecomp_le_quasiLocalSubalgDecomp L Λ).trans
    (Subalgebra.le_topologicalClosure _)

/-- The algebraic quasi-local core is contained in the quasi-local algebra. -/
theorem quasiLocalSubalgDecomp_le_quasiLocalDecomp :
    quasiLocalSubalgDecomp L ≤ quasiLocalDecomp L :=
  Subalgebra.le_topologicalClosure _

/-! ### Isotony at the decomposable subalgebra level -/

/-- Compatibility lemma: lifting `M` from `Λ` to `Λ'` and embedding via
`localEmbedRefSector L Λ'` gives the same operator on the reference sector
`ITPSector (referenceUnitFamily L)` as embedding `M` directly via
`localEmbedRefSector L Λ`.  Inherited from `localEmbed_regionLift_eq`. -/
theorem localEmbedRefSector_regionLift_eq {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (M : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ) :
    localEmbedRefSector L Λ' (regionLift h M) = localEmbedRefSector L Λ M := by
  ext x
  rw [localEmbedRefSector_apply, localEmbedRefSector_apply,
    localEmbed_regionLift_eq]

/-- Compatibility lemma: lifting `M` from `Λ` to `Λ'` and embedding via
`localEmbedSector L Ω Λ'` gives the same operator on `ITPSector Ω` as
embedding `M` directly via `localEmbedSector L Ω Λ`. -/
theorem localEmbedSector_regionLift_eq {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (Ω : InfiniteTensor.UnitFamily (siteHilbert (L := L) ·))
    (M : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ) :
    localEmbedSector L Ω Λ' (regionLift h M) = localEmbedSector L Ω Λ M := by
  ext x
  rw [localEmbedSector_apply, localEmbedSector_apply,
    localEmbedRefSector_regionLift_eq]

/-- Compatibility lemma at the decomposable space level. -/
theorem localEmbedDecomp_regionLift_eq {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (M : regionHilbert (L := L) Λ →L[ℂ] regionHilbert (L := L) Λ) :
    localEmbedDecomp L Λ' (regionLift h M) = localEmbedDecomp L Λ M := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext q
  rw [localEmbedDecomp_apply_coord, localEmbedDecomp_apply_coord,
    localEmbedSector_regionLift_eq]

/-- **Phase 7 isotony**: for `Λ ⊆ Λ'`, the decomposable local subalgebra at
`Λ` is contained in the one at `Λ'`. -/
theorem localSubalgebraDecomp_le_of_subset {Λ Λ' : Finset L} (h : Λ ⊆ Λ') :
    localSubalgebraDecomp L Λ ≤ localSubalgebraDecomp L Λ' := by
  rintro T ⟨M, hM⟩
  refine ⟨regionLift h M, ?_⟩
  rw [localEmbedDecompRingHom_apply, localEmbedDecomp_regionLift_eq]
  exact hM

/-! ### Locality at the decomposable subalgebra level -/

/-- Per-fiber locality on the reference sector: operators on disjoint
finite regions commute under `localEmbedRefSector`. -/
theorem localEmbedRefSector_commute_of_disjoint
    {Λ₁ Λ₂ : Finset L} (hd : Disjoint Λ₁ Λ₂)
    (M₁ : regionHilbert (L := L) Λ₁ →L[ℂ] regionHilbert (L := L) Λ₁)
    (M₂ : regionHilbert (L := L) Λ₂ →L[ℂ] regionHilbert (L := L) Λ₂) :
    Commute (localEmbedRefSector L Λ₁ M₁) (localEmbedRefSector L Λ₂ M₂) := by
  change localEmbedRefSector L Λ₁ M₁ * localEmbedRefSector L Λ₂ M₂
      = localEmbedRefSector L Λ₂ M₂ * localEmbedRefSector L Λ₁ M₁
  apply ContinuousLinearMap.ext
  intro x
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply]
  rw [localEmbedRefSector_apply, localEmbedRefSector_apply,
    localEmbedRefSector_apply, localEmbedRefSector_apply]
  rw [LinearIsometryEquiv.apply_symm_apply,
    LinearIsometryEquiv.apply_symm_apply]
  congr 1
  have h := localEmbed_commute_of_disjoint hd M₁ M₂
  change localEmbed Λ₁ M₁ ((localEmbed Λ₂ M₂) ((referenceSectorEquiv L) x))
    = localEmbed Λ₂ M₂ ((localEmbed Λ₁ M₁) ((referenceSectorEquiv L) x))
  rw [← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, h]

/-- Per-fiber locality on a general sector: operators on disjoint finite
regions commute under `localEmbedSector L Ω _`. -/
theorem localEmbedSector_commute_of_disjoint
    (Ω : InfiniteTensor.UnitFamily (siteHilbert (L := L) ·))
    {Λ₁ Λ₂ : Finset L} (hd : Disjoint Λ₁ Λ₂)
    (M₁ : regionHilbert (L := L) Λ₁ →L[ℂ] regionHilbert (L := L) Λ₁)
    (M₂ : regionHilbert (L := L) Λ₂ →L[ℂ] regionHilbert (L := L) Λ₂) :
    Commute (localEmbedSector L Ω Λ₁ M₁) (localEmbedSector L Ω Λ₂ M₂) := by
  change localEmbedSector L Ω Λ₁ M₁ * localEmbedSector L Ω Λ₂ M₂
      = localEmbedSector L Ω Λ₂ M₂ * localEmbedSector L Ω Λ₁ M₁
  apply ContinuousLinearMap.ext
  intro x
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply]
  rw [localEmbedSector_apply, localEmbedSector_apply,
    localEmbedSector_apply, localEmbedSector_apply]
  rw [LinearIsometryEquiv.apply_symm_apply,
    LinearIsometryEquiv.apply_symm_apply]
  congr 1
  have h := localEmbedRefSector_commute_of_disjoint L hd M₁ M₂
  change localEmbedRefSector L Λ₁ M₁ (localEmbedRefSector L Λ₂ M₂
        ((InfiniteTensor.UnitFamily.noncanonicalSectorEquivAny Ω
          (referenceUnitFamily L)) x))
    = localEmbedRefSector L Λ₂ M₂ (localEmbedRefSector L Λ₁ M₁
        ((InfiniteTensor.UnitFamily.noncanonicalSectorEquivAny Ω
          (referenceUnitFamily L)) x))
  rw [← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, h]

/-- Decomposable locality at the operator level: `localEmbedDecomp` of
disjoint regions commute. -/
theorem localEmbedDecomp_commute_of_disjoint
    {Λ₁ Λ₂ : Finset L} (hd : Disjoint Λ₁ Λ₂)
    (M₁ : regionHilbert (L := L) Λ₁ →L[ℂ] regionHilbert (L := L) Λ₁)
    (M₂ : regionHilbert (L := L) Λ₂ →L[ℂ] regionHilbert (L := L) Λ₂) :
    Commute (localEmbedDecomp L Λ₁ M₁) (localEmbedDecomp L Λ₂ M₂) := by
  change localEmbedDecomp L Λ₁ M₁ * localEmbedDecomp L Λ₂ M₂
      = localEmbedDecomp L Λ₂ M₂ * localEmbedDecomp L Λ₁ M₁
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext q
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
    localEmbedDecomp_apply_coord, localEmbedDecomp_apply_coord,
    localEmbedDecomp_apply_coord, localEmbedDecomp_apply_coord]
  have h := localEmbedSector_commute_of_disjoint L q.out hd M₁ M₂
  change localEmbedSector L q.out Λ₁ M₁
        (localEmbedSector L q.out Λ₂ M₂ (x q))
    = localEmbedSector L q.out Λ₂ M₂
        (localEmbedSector L q.out Λ₁ M₁ (x q))
  rw [← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, h]

/-- **Phase 7 locality**: operators in the decomposable local subalgebras
on disjoint finite regions commute. -/
theorem localSubalgebraDecomp_commute_of_disjoint
    {Λ₁ Λ₂ : Finset L} (hd : Disjoint Λ₁ Λ₂)
    {T₁ T₂ : decomposableLatticeITP L →L[ℂ] decomposableLatticeITP L}
    (h₁ : T₁ ∈ localSubalgebraDecomp L Λ₁)
    (h₂ : T₂ ∈ localSubalgebraDecomp L Λ₂) :
    Commute T₁ T₂ := by
  obtain ⟨M₁, hM₁⟩ := h₁
  obtain ⟨M₂, hM₂⟩ := h₂
  rw [← hM₁, ← hM₂]
  rw [localEmbedDecompRingHom_apply, localEmbedDecompRingHom_apply]
  exact localEmbedDecomp_commute_of_disjoint L hd M₁ M₂


/-! ## Phase 5 bridge construction summary

The bridge `referenceSectorEquiv L : ITPSector (siteHilbert ·) (referenceUnitFamily L)
≃ₗᵢ[ℂ] referenceSectorHilbert L` is constructed in three layers:

### Layer 1: regionTensor ≃ regionHilbert (per finite region)

For each finite `Λ : Finset L`, identify:

```
regionTensor (H := siteHilbert) Λ = ⨂[ℂ] s : Λ, EuclideanSpace ℂ (localIdx s.val)
        ≃ₗᵢ[ℂ]
regionHilbert Λ = EuclideanSpace ℂ ((s : Λ) → localIdx s.val)
```

via `Basis.piTensorProduct` applied to the standard `EuclideanSpace.basisFun
(localIdx s.val) ℂ` at each factor.  The `finrank ℂ (siteHilbert s) =
Fintype.card (localIdx s)` equality + `Fintype.equivFin` gives the
reindexing from `Π s, Fin (finrank ℂ (siteHilbert s.val))` to `regionIdx Λ`.

### Layer 2: regionHilbert Λ → referenceSectorHilbert L

Embed `EuclideanSpace ℂ (regionIdx Λ)` into `referenceSectorHilbert L =
↥(lp (fun _ : referenceSectorIdx L => ℂ) 2)` by sending each basis tuple
`f : (s : Λ) → localIdx s.val` to the global tuple agreeing with `f` on
`Λ` and with `referenceBasis L` outside `Λ`, then pushing forward via
`lp.single`.

This is essentially the `mkRegionVectorΩ` / `regionEmbed`-style
construction from the deleted `RegionDirectedOmega.lean`, now derived from
the pure-layer `forwardFiber`-style machinery.

### Layer 3: directed-system compatibility + completion lift

The Layer 1 + 2 maps are compatible with `regionEmbedLe (referenceUnitFamily L)`
on the pure side (extending with `EuclideanSpace.single (referenceBasis L _)
1`) and with the corresponding tuple-extension on the `referenceSectorHilbert
L` side (extending with `referenceBasis L _`).  Hence they descend to
`preITPSector (referenceUnitFamily L) →ₗᵢ[ℂ] referenceSectorHilbert L`,
and lift to `ITPSector` via `ContinuousLinearMap.completion` (the same
density argument as `sectorEquivOfReferenceRel` from
`SectorIsometry.lean`).

Surjectivity of the completion lift follows because finite-region images are
dense in `referenceSectorHilbert L`, and every `regionEmbed Λ` range is in the
range of `sectorReferenceIsom L`.  The implemented bridge is the theorem-like
definition `referenceSectorEquiv L` above; downstream sectorwise and
decomposable constructions in this file transit through it. -/

/-! ## Phase 8: Vacuum on the decomposable space

The reference-sector vacuum (`vacuumVector L : referenceSectorHilbert L`)
embeds into the BR sector decomposition `decomposableLatticeITP L` via
the canonical sector inclusion `lp.single 2 [referenceUnitFamily L] (·)`,
applied to `vacuumVectorSector L : ITPSector siteHilbert
(referenceUnitFamily L)` (the pure-layer transport from Phase 9b).

The migration plan emphasises that the decomposable space has **no
canonical vacuum** without specifying a reference sector: any vacuum in
the decomposable space depends on the choice of sector class.  Here we
explicitly realise the *reference-sector* vacuum at the
`[referenceUnitFamily L]` position; downstream code that requires a
"vacuum" must pick a sector and document the choice.

Phase 8 now provides the lattice-side unit-family action, its descent to
`Quotient c0Equiv`, a non-canonical sector-permuting isometry on the
decomposable space, and the reference-sector vacuum vector.  The remaining
gap is functorial/canonical covariance: `decomposableUnitaryActionLIE` uses
`sectorEquivAny`, so its fibers are chosen non-canonically and the assignment
`g ↦ decomposableUnitaryActionLIE L act g` is not yet proved to be a group
representation.  The final section records the obstruction and the path to a
canonical colimit-level group action. -/

/-- The reference sector class in the BR sector decomposition. -/
noncomputable def referenceSectorClass :
    Quotient (InfiniteTensor.UnitFamily.c0Equiv
      (H := fun s : L => siteHilbert (L := L) s)) :=
  Quotient.mk
    (InfiniteTensor.UnitFamily.c0Equiv
      (H := fun s : L => siteHilbert (L := L) s))
    (referenceUnitFamily L)

/-! ### Phase 8 covariance: site-action shift on `siteHilbert` -/

/-- Per-site Hilbert-space identification induced by the group action:
`siteHilbert s ≃ₗᵢ[ℂ] siteHilbert (act.siteAction g s)`.

This is the lift to `EuclideanSpace ℂ (localIdx _)` of the per-site
`siteIdxEquiv g s : localIdx s ≃ localIdx (siteAction g s)` from
`HasGroupAction`. -/
noncomputable def siteHilbertEquiv
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G) (s : L) :
    siteHilbert (L := L) s ≃ₗᵢ[ℂ] siteHilbert (act.siteAction g s) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (act.siteIdxEquiv g s)

@[simp]
theorem siteHilbertEquiv_norm_map
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G) (s : L)
    (v : siteHilbert (L := L) s) :
    ‖siteHilbertEquiv L act g s v‖ = ‖v‖ :=
  LinearIsometryEquiv.norm_map _ _

/-! ### Phase 8 covariance: site-action lifted to `UnitFamily` -/

/-- The group action on `UnitFamily (siteHilbert ·)`: a permutation of
sites combined with the per-site Hilbert isometry.

At site `t : L`, the value is `siteHilbertEquiv g s (Ω.vec s)` where
`s = (siteAction g).symm t`, transported through the propositional
equality `siteAction g s = t`.

Implemented via `Equiv.piCongr`, which packages the dependent-type cast. -/
noncomputable def unitFamilyAction
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G)
    (Ω : InfiniteTensor.UnitFamily (fun s : L => siteHilbert (L := L) s)) :
    InfiniteTensor.UnitFamily (fun s : L => siteHilbert (L := L) s) where
  vec := Equiv.piCongr (act.siteAction g)
    (fun s => (siteHilbertEquiv L act g s).toEquiv) Ω.vec
  norm_vec t := by
    -- Reformulate using `Equiv.piCongr_apply_apply` at site `s := siteAction g⁻¹·t`,
    -- where `siteAction g s = t` by `Equiv.apply_symm_apply`.
    set s := (act.siteAction g).symm t with hs_def
    have hst : act.siteAction g s = t := by
      rw [hs_def]; exact (act.siteAction g).apply_symm_apply t
    have hpc :
        (Equiv.piCongr (act.siteAction g)
            (fun s => (siteHilbertEquiv L act g s).toEquiv) Ω.vec)
          (act.siteAction g s)
          = siteHilbertEquiv L act g s (Ω.vec s) :=
      Equiv.piCongr_apply_apply (act.siteAction g)
        (fun s => (siteHilbertEquiv L act g s).toEquiv) Ω.vec s
    rw [show t = act.siteAction g s from hst.symm]
    rw [hpc]
    rw [siteHilbertEquiv_norm_map]
    exact Ω.norm_vec _

/-- Inner product between the action-transported unit families equals the
inner product of the originals, reindexed: `⟨(g·Ω) (siteAction g s),
(g·Ω') (siteAction g s)⟩ = ⟨Ω s, Ω' s⟩`. -/
theorem unitFamilyAction_inner_at_siteAction
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G)
    (Ω Ω' : InfiniteTensor.UnitFamily (fun s : L => siteHilbert (L := L) s))
    (s : L) :
    inner ℂ (unitFamilyAction L act g Ω (act.siteAction g s))
        (unitFamilyAction L act g Ω' (act.siteAction g s))
      = inner ℂ (Ω s) (Ω' s) := by
  change inner ℂ
      (Equiv.piCongr (act.siteAction g)
        (fun s => (siteHilbertEquiv L act g s).toEquiv) Ω.vec
        (act.siteAction g s))
      (Equiv.piCongr (act.siteAction g)
        (fun s => (siteHilbertEquiv L act g s).toEquiv) Ω'.vec
        (act.siteAction g s))
    = _
  rw [Equiv.piCongr_apply_apply, Equiv.piCongr_apply_apply]
  exact (siteHilbertEquiv L act g s).inner_map_map (Ω.vec s) (Ω'.vec s)

/-- **Phase 8 c0Rel preservation**: the group action on `UnitFamily`
preserves the Bratteli–Robinson `c0Rel` relation. -/
theorem unitFamilyAction_c0Rel
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G)
    {Ω Ω' : InfiniteTensor.UnitFamily (fun s : L => siteHilbert (L := L) s)}
    (h : InfiniteTensor.UnitFamily.c0Rel Ω Ω') :
    InfiniteTensor.UnitFamily.c0Rel
      (unitFamilyAction L act g Ω) (unitFamilyAction L act g Ω') := by
  -- c0Rel is defined as `Summable (fun s => 1 - ‖⟨Ω s, Ω' s⟩‖)`.
  -- After action: `1 - ‖⟨(g·Ω)(siteAction g s), (g·Ω')(siteAction g s)⟩‖
  --              = 1 - ‖⟨Ω s, Ω' s⟩‖`.
  -- Summability is preserved by reindexing via `act.siteAction g`.
  change Summable _
  refine ((act.siteAction g).summable_iff (f := fun t => 1
      - ‖inner ℂ (unitFamilyAction L act g Ω t)
          (unitFamilyAction L act g Ω' t)‖)).mp ?_
  -- Show summability of the function precomposed with `act.siteAction g`.
  have hreindex : ∀ s : L,
      (1 - ‖inner ℂ (unitFamilyAction L act g Ω (act.siteAction g s))
          (unitFamilyAction L act g Ω' (act.siteAction g s))‖)
        = 1 - ‖inner ℂ (Ω s) (Ω' s)‖ := by
    intro s
    rw [unitFamilyAction_inner_at_siteAction]
  change Summable ((fun t => 1 -
      ‖inner ℂ (unitFamilyAction L act g Ω t)
        (unitFamilyAction L act g Ω' t)‖) ∘ act.siteAction g)
  rw [show ((fun t => 1 - ‖inner ℂ (unitFamilyAction L act g Ω t)
        (unitFamilyAction L act g Ω' t)‖) ∘ act.siteAction g)
      = (fun s => 1 - ‖inner ℂ (Ω s) (Ω' s)‖) from funext hreindex]
  exact h

/-- The action carries the per-site reference basis through
`siteHilbertEquiv` to the per-site reference basis at the shifted site,
matching `siteIdxEquiv_referenceBasis`. -/
theorem siteHilbertEquiv_referenceBasis
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G) (s : L) :
    siteHilbertEquiv L act g s
        (EuclideanSpace.single (referenceBasis L s) (1 : ℂ))
      = EuclideanSpace.single (referenceBasis L (act.siteAction g s))
          (1 : ℂ) := by
  unfold siteHilbertEquiv
  rw [EuclideanSpace.piLpCongrLeft_single,
    act.siteIdxEquiv_referenceBasis]

/-- **Phase 8 reference-fixing**: the unit-family group action fixes the
reference unit family. -/
theorem unitFamilyAction_referenceUnitFamily
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G) :
    unitFamilyAction L act g (referenceUnitFamily L)
      = referenceUnitFamily L := by
  refine InfiniteTensor.UnitFamily.ext (fun t => ?_)
  change (Equiv.piCongr (act.siteAction g)
        (fun s => (siteHilbertEquiv L act g s).toEquiv)
        (referenceUnitFamily L).vec) t
      = (referenceUnitFamily L) t
  set s := (act.siteAction g).symm t with hs_def
  have hst : act.siteAction g s = t := by
    rw [hs_def]; exact (act.siteAction g).apply_symm_apply t
  have hpc :
      (Equiv.piCongr (act.siteAction g)
          (fun s => (siteHilbertEquiv L act g s).toEquiv)
          (referenceUnitFamily L).vec)
        (act.siteAction g s)
        = siteHilbertEquiv L act g s ((referenceUnitFamily L).vec s) :=
    Equiv.piCongr_apply_apply (act.siteAction g)
      (fun s => (siteHilbertEquiv L act g s).toEquiv)
      (referenceUnitFamily L).vec s
  rw [show t = act.siteAction g s from hst.symm]
  rw [hpc]
  change siteHilbertEquiv L act g s ((referenceUnitFamily L).vec s)
    = (referenceUnitFamily L) (act.siteAction g s)
  rw [show (referenceUnitFamily L).vec s
      = EuclideanSpace.single (referenceBasis L s) (1 : ℂ) from rfl]
  rw [siteHilbertEquiv_referenceBasis]
  rfl

/-- **Phase 8 sector-class action**: the descent of the unit-family
group action to `Quotient c0Equiv`.

`unitFamilyAction_c0Rel` ensures the action descends to a well-defined
permutation of sector classes. -/
noncomputable def sectorClassAction
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G) :
    Quotient (InfiniteTensor.UnitFamily.c0Equiv
        (H := fun s : L => siteHilbert (L := L) s))
      → Quotient (InfiniteTensor.UnitFamily.c0Equiv
        (H := fun s : L => siteHilbert (L := L) s)) :=
  Quotient.map (unitFamilyAction L act g)
    (fun _ _ h => unitFamilyAction_c0Rel L act g h)

@[simp]
theorem sectorClassAction_mk
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G)
    (Ω : InfiniteTensor.UnitFamily (fun s : L => siteHilbert (L := L) s)) :
    sectorClassAction L act g (Quotient.mk _ Ω)
      = Quotient.mk _ (unitFamilyAction L act g Ω) :=
  rfl

/-- **Phase 8 reference-class fixing**: the sector-class action fixes the
reference sector class.  Inherited from
`unitFamilyAction_referenceUnitFamily`. -/
theorem sectorClassAction_referenceSectorClass
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G) :
    sectorClassAction L act g (referenceSectorClass L)
      = referenceSectorClass L := by
  unfold referenceSectorClass
  rw [sectorClassAction_mk, unitFamilyAction_referenceUnitFamily]

/-! ### Reindexed finite-region transport for the geometric action -/

@[simp]
theorem unitFamilyAction_apply_siteAction
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G)
    (Ω : InfiniteTensor.UnitFamily (fun s : L => siteHilbert (L := L) s))
    (s : L) :
    unitFamilyAction L act g Ω (act.siteAction g s)
      = siteHilbertEquiv L act g s (Ω s) := by
  change (Equiv.piCongr (act.siteAction g)
      (fun s => (siteHilbertEquiv L act g s).toEquiv) Ω.vec)
        (act.siteAction g s) = siteHilbertEquiv L act g s (Ω.vec s)
  simp

/-- The finite-region action on `Finset L` induced by `siteAction g`. -/
noncomputable def regionImageEquiv
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G) :
    Finset L ≃ Finset L where
  toFun := act.regionImage g
  invFun := fun S => S.image (act.siteAction g).symm
  left_inv S := by
    ext s
    constructor
    · intro hs
      rcases Finset.mem_image.mp hs with ⟨t, ht, hts⟩
      rcases Finset.mem_image.mp ht with ⟨u, hu, hut⟩
      have : u = s := by
        apply (act.siteAction g).injective
        have hs' : t = act.siteAction g s := by
          simpa using congrArg (act.siteAction g) hts
        rw [hut, ← hs']
      simpa [this] using hu
    · intro hs
      exact Finset.mem_image.mpr ⟨act.siteAction g s,
        Finset.mem_image.mpr ⟨s, hs, rfl⟩, by simp⟩
  right_inv S := by
    ext s
    constructor
    · intro hs
      rcases Finset.mem_image.mp hs with ⟨t, ht, hts⟩
      rcases Finset.mem_image.mp ht with ⟨u, hu, hut⟩
      have : u = s := by
        apply (act.siteAction g).symm.injective
        have hs' : t = (act.siteAction g).symm s := by
          simpa using congrArg (act.siteAction g).symm hts
        rw [hut, ← hs']
      simpa [this] using hu
    · intro hs
      exact Finset.mem_image.mpr ⟨(act.siteAction g).symm s,
        Finset.mem_image.mpr ⟨s, hs, by simp⟩, by simp⟩

theorem regionImage_mono
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G)
    {S T : Finset L} (h : S ⊆ T) :
    act.regionImage g S ⊆ act.regionImage g T := by
  intro t ht
  rcases Finset.mem_image.mp ht with ⟨s, hs, rfl⟩
  exact Finset.mem_image.mpr ⟨s, h hs, rfl⟩

theorem regionImageEquiv_symm_mono
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G)
    {S T : Finset L} (h : S ⊆ T) :
    (regionImageEquiv L act g).symm S ⊆ (regionImageEquiv L act g).symm T := by
  intro t ht
  rcases Finset.mem_image.mp ht with ⟨s, hs, rfl⟩
  exact Finset.mem_image.mpr ⟨s, h hs, rfl⟩

@[simp]
theorem siteAction_siteSubtypeEquiv_symm_val
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G)
    (S : Finset L) (t : ↥(act.regionImage g S)) :
    act.siteAction g ((act.siteSubtypeEquiv g S).symm t).val = t.val := by
  change act.siteAction g ((act.siteAction g).symm t.val) = t.val
  exact (act.siteAction g).apply_symm_apply _

/-- The site Hilbert equivalence indexed by an image-region subtype.  The
codomain cast is absorbed using `siteSubtypeEquiv`.

Defined as a term-level `Eq.recOn` transport of `siteHilbertEquiv`,
which lets us reason about its action via `eqRec_heq`. -/
noncomputable def siteHilbertSubtypeEquiv
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G)
    (S : Finset L) (t : ↥(act.regionImage g S)) :
    siteHilbert (L := L) ((act.siteSubtypeEquiv g S).symm t).val ≃ₗᵢ[ℂ]
      siteHilbert (L := L) t.val :=
  (siteAction_siteSubtypeEquiv_symm_val L act g S t) ▸
    siteHilbertEquiv L act g ((act.siteSubtypeEquiv g S).symm t).val


theorem siteSubtypeEquiv_symm_mem_iff_mem_regionImage
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G)
    {S T : Finset L} (t : ↥(act.regionImage g T)) :
    ((act.siteSubtypeEquiv g T).symm t).val ∈ S ↔ t.val ∈ act.regionImage g S := by
  constructor
  · intro hs
    exact Finset.mem_image.mpr ⟨((act.siteSubtypeEquiv g T).symm t).val, hs,
      siteAction_siteSubtypeEquiv_symm_val L act g T t⟩
  · intro ht
    rcases Finset.mem_image.mp ht with ⟨s, hs, hst⟩
    change (act.siteAction g).symm t.val ∈ S
    have : (act.siteAction g).symm t.val = s := by
      rw [← hst]
      exact (act.siteAction g).symm_apply_apply s
    simpa [this] using hs

/-- Tuple-level form of the geometric action on a finite-region tensor. -/
noncomputable def regionTensorActionTuple
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G)
    (S : Finset L)
    (ξ : (s : {x // x ∈ S}) → siteHilbert (L := L) s.val) :
    (t : {x // x ∈ act.regionImage g S}) → siteHilbert (L := L) t.val :=
  fun t => siteHilbertSubtypeEquiv L act g S t (ξ ((act.siteSubtypeEquiv g S).symm t))

/-- The finite-region tensor-product action induced by the site action and the
per-site Hilbert equivalences. -/
noncomputable def regionTensorActionEquiv
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G)
    (S : Finset L) :
    InfiniteTensor.regionTensor (H := fun s : L => siteHilbert (L := L) s) S
      ≃ₗᵢ[ℂ]
    InfiniteTensor.regionTensor (H := fun s : L => siteHilbert (L := L) s)
      (act.regionImage g S) := by
  let reindex :=
    ForMathlib.PiTensorProduct.piTensorReindexIsom
      (ι := {x // x ∈ S})
      (ι' := {x // x ∈ act.regionImage g S})
      (H := fun s : {x // x ∈ S} => siteHilbert (L := L) s.val)
      (act.siteSubtypeEquiv g S)
  let pointwise :=
    ForMathlib.PiTensorProduct.piTensorCongrIsom
      (ι := {x // x ∈ act.regionImage g S})
      (H := fun t : {x // x ∈ act.regionImage g S} =>
        siteHilbert (L := L) ((act.siteSubtypeEquiv g S).symm t).val)
      (K := fun t : {x // x ∈ act.regionImage g S} => siteHilbert (L := L) t.val)
      (fun t => siteHilbertSubtypeEquiv L act g S t)
  exact reindex.trans pointwise

theorem regionTensorActionEquiv_tprod
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G)
    (S : Finset L)
    (ξ : (s : {x // x ∈ S}) → siteHilbert (L := L) s.val) :
    regionTensorActionEquiv L act g S (_root_.PiTensorProduct.tprod ℂ ξ)
      = _root_.PiTensorProduct.tprod ℂ (regionTensorActionTuple L act g S ξ) := by
  unfold regionTensorActionEquiv regionTensorActionTuple
  simp [ForMathlib.PiTensorProduct.piTensorReindexIsom_tprod,
    ForMathlib.PiTensorProduct.piTensorCongrIsom_tprod]

/-! ### Reindexed sector transport from a geometric site action

The data inputs `regionImageEquiv`, `regionImage_mono`,
`regionImageEquiv_symm_mono` and `regionTensorActionEquiv` are bundled
into `ReindexedSectorTransportData.ofGroupAction`.  The cocycle
compatibility `regionMap_compat` (commutativity with `regionEmbedLe`)
is proved by `tprod` induction reducing to a pointwise tuple identity,
which splits on whether each output site is in the image of the source
region. -/

/-- Generic HEq-level distribution of `Eq.recOn` over `LinearIsometryEquiv`
application: transporting an LIE along a codomain-type equation, then
applying to a value, gives the same value (up to HEq) as applying the
original LIE. -/
theorem _root_.LinearIsometryEquiv.eqRec_apply_heq
    {R : Type*} [Semiring R]
    {A : Type*} [SeminormedAddCommGroup A] [Module R A]
    {ι : Type*} {β : ι → Type*}
    [(i : ι) → SeminormedAddCommGroup (β i)] [(i : ι) → Module R (β i)]
    {a b : ι} (h : a = b) (e : A ≃ₗᵢ[R] β a) (v : A) :
    HEq ((h ▸ e) v) (e v) := by
  subst h
  rfl

/-- HEq form of the apply equation for `siteHilbertSubtypeEquiv`: the
codomain cast is propositionally trivial under HEq. -/
theorem siteHilbertSubtypeEquiv_apply_heq
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G)
    (S : Finset L) (t : ↥(act.regionImage g S))
    (v : siteHilbert (L := L) ((act.siteSubtypeEquiv g S).symm t).val) :
    HEq (siteHilbertSubtypeEquiv L act g S t v)
        (siteHilbertEquiv L act g ((act.siteSubtypeEquiv g S).symm t).val v) :=
  LinearIsometryEquiv.eqRec_apply_heq
    (siteAction_siteSubtypeEquiv_symm_val L act g S t)
    (siteHilbertEquiv L act g ((act.siteSubtypeEquiv g S).symm t).val) v

/-- `siteHilbertSubtypeEquiv L act g S t (Ω.vec _)` equals
`(unitFamilyAction L act g Ω).vec t.val`: both reduce to
`siteHilbertEquiv L act g s (Ω.vec s)` for the underlying site
`s := ((siteSubtypeEquiv g S).symm t).val`. -/
theorem siteHilbertSubtypeEquiv_apply_vec
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G)
    (S : Finset L) (t : ↥(act.regionImage g S))
    (Ω : InfiniteTensor.UnitFamily (fun s : L => siteHilbert (L := L) s)) :
    siteHilbertSubtypeEquiv L act g S t
        (Ω.vec ((act.siteSubtypeEquiv g S).symm t).val)
      = (unitFamilyAction L act g Ω).vec t.val := by
  set s := ((act.siteSubtypeEquiv g S).symm t).val with hs_def
  have ht : act.siteAction g s = t.val :=
    siteAction_siteSubtypeEquiv_symm_val L act g S t
  apply eq_of_heq
  refine HEq.trans (siteHilbertSubtypeEquiv_apply_heq L act g S t (Ω.vec s)) ?_
  -- Goal: HEq (siteHilbertEquiv L act g s (Ω.vec s)) ((unitFamilyAction L act g Ω).vec t.val).
  rw [← ht]
  -- Goal: HEq (siteHilbertEquiv L act g s (Ω.vec s))
  --           ((unitFamilyAction L act g Ω).vec (act.siteAction g s)).
  -- Use `unitFamilyAction_apply_siteAction` to rewrite the RHS via the FunLike coe.
  change HEq (siteHilbertEquiv L act g s (Ω.vec s))
    ((unitFamilyAction L act g Ω) (act.siteAction g s))
  rw [unitFamilyAction_apply_siteAction]
  rfl

/-- Build a reindexed sector transport datum from a geometric group action.

The site action `siteAction g : L ≃ L` and per-site Hilbert isometries
`siteHilbertEquiv L act g s` lift to a region-level transport
`regionTensor S ≃ₗᵢ regionTensor (act.regionImage g S)`.  The cocycle
compatibility comes from the equivariance of `extendVec`: filling new
sites with `Ω` outside `S` corresponds, after the action, to filling
with `unitFamilyAction g Ω` outside `act.regionImage g S`. -/
noncomputable def ReindexedSectorTransportData.ofGroupAction
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G)
    (Ω : InfiniteTensor.UnitFamily (fun s : L => siteHilbert (L := L) s)) :
    InfiniteTensor.UnitFamily.ReindexedSectorTransportData
      (H := fun s : L => siteHilbert (L := L) s) Ω
      (unitFamilyAction L act g Ω) where
  target := regionImageEquiv L act g
  target_mono := fun {_ _} h => regionImage_mono L act g h
  target_symm_mono := fun {_ _} h => regionImageEquiv_symm_mono L act g h
  regionMap S := regionTensorActionEquiv L act g S
  regionMap_compat := by
    intro S T h x
    -- The goal involves `regionEmbedLe Ω h x` and the `regionMap = regionTensorActionEquiv`.
    -- Use `show` to refresh the goal to `regionTensorActionEquiv` native types so subsequent
    -- rewrites match syntactically (the displayed `(regionImageEquiv L act g)` is
    -- definitionally `act.regionImage g`, but rewrites match syntactically).
    change regionTensorActionEquiv L act g T
          (InfiniteTensor.UnitFamily.regionEmbedLe Ω h x)
        = InfiniteTensor.UnitFamily.regionEmbedLe (unitFamilyAction L act g Ω)
            (regionImage_mono L act g h)
            (regionTensorActionEquiv L act g S x)
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r ξ =>
      simp only [map_smul, InfiniteTensor.UnitFamily.regionEmbedLe_tprod,
        regionTensorActionEquiv_tprod]
      congr
      funext t
      by_cases hmem : t.val ∈ act.regionImage g S
      · -- Inside: both sides apply the per-site action to ξ at the same underlying site.
        have hs : ((act.siteSubtypeEquiv g T).symm t).val ∈ S :=
          (siteSubtypeEquiv_symm_mem_iff_mem_regionImage L act g
            (S := S) (T := T) t).mpr hmem
        unfold regionTensorActionTuple
        rw [InfiniteTensor.UnitFamily.extendVec_inside _ _ _ _ hs,
            InfiniteTensor.UnitFamily.extendVec_inside _ _ _ _ hmem]
        apply eq_of_heq
        refine HEq.trans
          (siteHilbertSubtypeEquiv_apply_heq L act g T t
            (ξ ⟨((act.siteSubtypeEquiv g T).symm t).val, hs⟩)) ?_
        refine HEq.symm <| HEq.trans
          (siteHilbertSubtypeEquiv_apply_heq L act g S ⟨t.val, hmem⟩
            (ξ ((act.siteSubtypeEquiv g S).symm ⟨t.val, hmem⟩))) ?_
        -- HEq (siteHilbertEquiv L act g s₂ (ξ a₂)) (siteHilbertEquiv L act g s₁ (ξ a₁))
        -- where s₁ = ((siteSubtypeEquiv g T).symm t).val,
        --       s₂ = ((siteSubtypeEquiv g S).symm ⟨t.val, hmem⟩).val.
        -- Both equal (act.siteAction g).symm t.val by definition.
        rfl
      · -- Outside: LHS uses `Ω.vec` shifted by `siteHilbertSubtypeEquiv`,
        -- RHS uses `(unitFamilyAction L act g Ω).vec` directly.
        have hs : ((act.siteSubtypeEquiv g T).symm t).val ∉ S := fun hs_in => hmem
          ((siteSubtypeEquiv_symm_mem_iff_mem_regionImage L act g
            (S := S) (T := T) t).mp hs_in)
        unfold regionTensorActionTuple
        rw [InfiniteTensor.UnitFamily.extendVec_outside _ _ _ _ hs,
            InfiniteTensor.UnitFamily.extendVec_outside _ _ _ _ hmem]
        exact siteHilbertSubtypeEquiv_apply_vec L act g T t Ω
    | add x₁ x₂ ih₁ ih₂ =>
      simp only [map_add, ih₁, ih₂]

/-! ### Phase 8 sector-permuting unitary: per-fiber carrier

The migration plan's full Phase 8 deliverable is a sector-permuting
unitary `decomposableLatticeITP L ≃ₗᵢ[ℂ] decomposableLatticeITP L`
indexed by `g : G`.  The action permutes lp fibers via `sectorClassAction
g` and uses Phase 3a's `sectorEquivAny` (which works for any pair of
unit families, not just `c0Rel`-equivalent ones) as the per-fiber
carrier between fibers in different group-related classes.

The declarations below build the per-fiber carrier.  Later sections package
it into `decomposableUnitaryActionLI` and `decomposableUnitaryActionLIE` using
generic `lp` permutation/isometry helpers.  The resulting action is still
non-canonical because the fiber maps use `sectorEquivAny`; functoriality in
`g` remains a follow-up and is analysed in the final section. -/

/-- The Equiv on dependent function spaces underlying `unitFamilyAction`. -/
noncomputable def unitFamilyActionPiEquiv
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G) :
    ((s : L) → siteHilbert (L := L) s)
      ≃ ((s : L) → siteHilbert (L := L) s) :=
  Equiv.piCongr (act.siteAction g)
    (fun s => (siteHilbertEquiv L act g s).toEquiv)

theorem unitFamilyAction_vec
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G)
    (Ω : InfiniteTensor.UnitFamily (fun s : L => siteHilbert (L := L) s)) :
    (unitFamilyAction L act g Ω).vec
      = unitFamilyActionPiEquiv L act g Ω.vec := rfl

/-- The unit-family action obtained from the **inverse** Equiv (NOT the
action of `g⁻¹`).  Without per-site group coherence data, this differs
from `unitFamilyAction L act g⁻¹` in general.  But it does serve as a
two-sided inverse to `unitFamilyAction L act g`. -/
noncomputable def unitFamilyActionSymm
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G)
    (Ω : InfiniteTensor.UnitFamily (fun s : L => siteHilbert (L := L) s)) :
    InfiniteTensor.UnitFamily (fun s : L => siteHilbert (L := L) s) where
  vec := (unitFamilyActionPiEquiv L act g).symm Ω.vec
  norm_vec t := by
    -- `(unitFamilyActionPiEquiv L act g).symm Ω.vec t`
    --   = `(siteHilbertEquiv L act g t).toEquiv.symm (Ω.vec ((siteAction g) t))`
    -- by `Equiv.piCongr_symm_apply`, which has type siteHilbert t.
    rw [show (unitFamilyActionPiEquiv L act g).symm Ω.vec t
        = (siteHilbertEquiv L act g t).symm (Ω.vec (act.siteAction g t)) from
      congrFun (Equiv.piCongr_symm_apply _ _ _) t]
    rw [LinearIsometryEquiv.norm_map]
    exact Ω.norm_vec _

/-- Two-sided inverse: `unitFamilyActionSymm g (unitFamilyAction g Ω) = Ω`. -/
theorem unitFamilyActionSymm_unitFamilyAction
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G)
    (Ω : InfiniteTensor.UnitFamily (fun s : L => siteHilbert (L := L) s)) :
    unitFamilyActionSymm L act g (unitFamilyAction L act g Ω) = Ω := by
  refine InfiniteTensor.UnitFamily.ext (fun t => ?_)
  change ((unitFamilyActionPiEquiv L act g).symm
      ((unitFamilyActionPiEquiv L act g) Ω.vec)) t = Ω.vec t
  rw [(unitFamilyActionPiEquiv L act g).symm_apply_apply]

theorem unitFamilyAction_unitFamilyActionSymm
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G)
    (Ω : InfiniteTensor.UnitFamily (fun s : L => siteHilbert (L := L) s)) :
    unitFamilyAction L act g (unitFamilyActionSymm L act g Ω) = Ω := by
  refine InfiniteTensor.UnitFamily.ext (fun t => ?_)
  change ((unitFamilyActionPiEquiv L act g)
      ((unitFamilyActionPiEquiv L act g).symm Ω.vec)) t = Ω.vec t
  rw [(unitFamilyActionPiEquiv L act g).apply_symm_apply]

/-- The reverse direction of c0Rel preservation: under `unitFamilyActionSymm`. -/
theorem unitFamilyActionSymm_c0Rel
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G)
    {Ω Ω' : InfiniteTensor.UnitFamily (fun s : L => siteHilbert (L := L) s)}
    (h : InfiniteTensor.UnitFamily.c0Rel Ω Ω') :
    InfiniteTensor.UnitFamily.c0Rel
      (unitFamilyActionSymm L act g Ω) (unitFamilyActionSymm L act g Ω') := by
  -- (unitFamilyActionSymm g Ω) s = (siteHilbertEquiv g s).symm (Ω (siteAction g s))
  -- Inner product reduces to ⟨Ω (siteAction g s), Ω' (siteAction g s)⟩.
  -- Summability reindexes by siteAction g back to ∑_t (...) over Ω, Ω'.
  have hreindex : ∀ s : L,
      (1 - ‖inner ℂ ((unitFamilyActionSymm L act g Ω) s)
          ((unitFamilyActionSymm L act g Ω') s)‖)
        = 1 - ‖inner ℂ (Ω (act.siteAction g s)) (Ω' (act.siteAction g s))‖ := by
    intro s
    have hΩ : (unitFamilyActionSymm L act g Ω) s
        = (siteHilbertEquiv L act g s).symm (Ω (act.siteAction g s)) :=
      congrFun (Equiv.piCongr_symm_apply _ _ Ω.vec) s
    have hΩ' : (unitFamilyActionSymm L act g Ω') s
        = (siteHilbertEquiv L act g s).symm (Ω' (act.siteAction g s)) :=
      congrFun (Equiv.piCongr_symm_apply _ _ Ω'.vec) s
    rw [hΩ, hΩ']
    rw [(siteHilbertEquiv L act g s).symm.inner_map_map]
  change Summable _
  rw [show (fun s => 1 - ‖inner ℂ ((unitFamilyActionSymm L act g Ω) s)
          ((unitFamilyActionSymm L act g Ω') s)‖)
      = (fun s => 1 - ‖inner ℂ (Ω (act.siteAction g s)) (Ω' (act.siteAction g s))‖)
      from funext hreindex]
  exact ((act.siteAction g).summable_iff (f := fun t => 1
      - ‖inner ℂ (Ω t) (Ω' t)‖)).mpr h

/-- The unit-family group action as an Equiv on `UnitFamily`. -/
noncomputable def unitFamilyActionEquiv
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G) :
    InfiniteTensor.UnitFamily (fun s : L => siteHilbert (L := L) s)
      ≃ InfiniteTensor.UnitFamily (fun s : L => siteHilbert (L := L) s) where
  toFun := unitFamilyAction L act g
  invFun := unitFamilyActionSymm L act g
  left_inv := unitFamilyActionSymm_unitFamilyAction L act g
  right_inv := unitFamilyAction_unitFamilyActionSymm L act g

/-- The sector-class action as an Equiv on `Quotient c0Equiv`. -/
noncomputable def sectorClassActionEquiv
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G) :
    Quotient (InfiniteTensor.UnitFamily.c0Equiv
        (H := fun s : L => siteHilbert (L := L) s))
      ≃ Quotient (InfiniteTensor.UnitFamily.c0Equiv
        (H := fun s : L => siteHilbert (L := L) s)) where
  toFun := sectorClassAction L act g
  invFun := Quotient.map (unitFamilyActionSymm L act g)
    (fun _ _ h => unitFamilyActionSymm_c0Rel L act g h)
  left_inv q := by
    induction q using Quotient.ind with
    | _ Ω =>
      change Quotient.map (unitFamilyActionSymm L act g) _
        (sectorClassAction L act g (Quotient.mk _ Ω)) = _
      rw [sectorClassAction_mk]
      change Quotient.mk _ (unitFamilyActionSymm L act g
        (unitFamilyAction L act g Ω)) = _
      rw [unitFamilyActionSymm_unitFamilyAction]
  right_inv q := by
    induction q using Quotient.ind with
    | _ Ω =>
      change sectorClassAction L act g
        (Quotient.map (unitFamilyActionSymm L act g) _ (Quotient.mk _ Ω)) = _
      change sectorClassAction L act g
        (Quotient.mk _ (unitFamilyActionSymm L act g Ω)) = _
      rw [sectorClassAction_mk, unitFamilyAction_unitFamilyActionSymm]

/-- **Per-fiber action carrier**: the isometric equivalence between
fibers `ITPSector ((sectorClassActionEquiv g).symm q).out` and
`ITPSector q.out`, realised via Phase 3a's `sectorEquivAny`.  This is
the data needed to move a vector at sector class `(sectorClassActionEquiv
g).symm q` to sector class `q` under the group action.

Non-canonicity: `sectorEquivAny` uses `Classical.choice` per site for
the unitary rotations, so this carrier is not functorial in `g`.  A
canonical functorial version would require lifting the per-site
`siteHilbertEquiv g s` action through the colimit construction, mirroring
Phase 3a's V_s rotation pattern but with the geometric per-site action
data. -/
noncomputable def fiberActionEquiv
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G)
    (q : Quotient (InfiniteTensor.UnitFamily.c0Equiv
        (H := fun s : L => siteHilbert (L := L) s))) :
    InfiniteTensor.UnitFamily.ITPSector
        (H := fun s : L => siteHilbert (L := L) s)
        ((sectorClassActionEquiv L act g).symm q).out
      ≃ₗᵢ[ℂ] InfiniteTensor.UnitFamily.ITPSector
        (H := fun s : L => siteHilbert (L := L) s) q.out :=
  InfiniteTensor.UnitFamily.noncanonicalSectorEquivAny _ _

@[simp]
theorem fiberActionEquiv_norm_map
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G)
    (q : Quotient (InfiniteTensor.UnitFamily.c0Equiv
        (H := fun s : L => siteHilbert (L := L) s)))
    (a : InfiniteTensor.UnitFamily.ITPSector
        (H := fun s : L => siteHilbert (L := L) s)
        ((sectorClassActionEquiv L act g).symm q).out) :
    ‖fiberActionEquiv L act g q a‖ = ‖a‖ :=
  LinearIsometryEquiv.norm_map _ _

/-- Memℓp 2 condition for the fiberwise sector-permuted action. -/
theorem memℓp_decomposableUnitaryAction
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G)
    (x : decomposableLatticeITP L) :
    Memℓp (fun q => fiberActionEquiv L act g q
      (x ((sectorClassActionEquiv L act g).symm q))) 2 := by
  have hx : Memℓp ⇑x 2 := lp.memℓp x
  have htwo : (0 : ℝ) < (2 : ENNReal).toReal := by
    rw [ENNReal.toReal_ofNat]; norm_num
  -- The reindexed family is in Memℓp 2 via Equiv.summable_iff.
  have hx_sum : Summable (fun q => ‖⇑x q‖ ^ ((2 : ENNReal).toReal)) :=
    hx.summable htwo
  have hreindex_sum : Summable (fun q =>
      ‖⇑x ((sectorClassActionEquiv L act g).symm q)‖
        ^ ((2 : ENNReal).toReal)) :=
    ((sectorClassActionEquiv L act g).symm.summable_iff).mpr hx_sum
  have hreindex_memℓp :
      Memℓp (fun q => ⇑x ((sectorClassActionEquiv L act g).symm q)) 2 :=
    (memℓp_gen_iff htwo).mpr hreindex_sum
  refine hreindex_memℓp.mono' (fun q => ?_)
  rw [fiberActionEquiv_norm_map]

/-- **Phase 8 sector-permuting unitary** as a function on the
decomposable BR sector decomposition Hilbert space. -/
noncomputable def decomposableUnitaryActionFun
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G)
    (x : decomposableLatticeITP L) :
    decomposableLatticeITP L :=
  ⟨fun q => fiberActionEquiv L act g q
      (x ((sectorClassActionEquiv L act g).symm q)),
    memℓp_decomposableUnitaryAction L act g x⟩

theorem decomposableUnitaryActionFun_apply_coord
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G)
    (x : decomposableLatticeITP L)
    (q : Quotient (InfiniteTensor.UnitFamily.c0Equiv
        (H := fun s : L => siteHilbert (L := L) s))) :
    (decomposableUnitaryActionFun L act g x) q
      = fiberActionEquiv L act g q
          (x ((sectorClassActionEquiv L act g).symm q)) := rfl

/-! ### Generic lp permute-map auxiliaries

To avoid `whnf` heartbeat timeouts when bundling
`decomposableUnitaryActionFun` as a `LinearIsometry`, we work through a
generic `lp` permute-and-map auxiliary that hides `decomposableLatticeITP`'s
type chain behind abstract `(ι, E, π, T)` parameters. -/

/-- Memℓp 2 closure under index permutation + per-fiber isometric
equivalences. -/
theorem memℓp_permute_isometry_aux
    {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℂ (E i)]
    (π : ι ≃ ι) (T : (i : ι) → E (π.symm i) ≃ₗᵢ[ℂ] E i)
    (f : (i : ι) → E i) (hf : Memℓp f 2) :
    Memℓp (fun i => T i (f (π.symm i))) 2 := by
  have htwo : (0 : ℝ) < (2 : ENNReal).toReal := by
    rw [ENNReal.toReal_ofNat]; norm_num
  have hf_sum : Summable (fun i => ‖f i‖ ^ ((2 : ENNReal).toReal)) :=
    hf.summable htwo
  have hreindex_sum : Summable (fun i =>
      ‖f (π.symm i)‖ ^ ((2 : ENNReal).toReal)) :=
    (π.symm.summable_iff).mpr hf_sum
  have hreindex_memℓp : Memℓp (fun i => f (π.symm i)) 2 :=
    (memℓp_gen_iff htwo).mpr hreindex_sum
  refine hreindex_memℓp.mono' (fun i => ?_)
  rw [LinearIsometryEquiv.norm_map]

/-- The lp-level fiberwise application after index permutation. -/
noncomputable def lp_permute_map_apply
    {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℂ (E i)]
    (π : ι ≃ ι) (T : (i : ι) → E (π.symm i) ≃ₗᵢ[ℂ] E i)
    (x : lp E 2) : lp E 2 :=
  ⟨fun i => T i (x (π.symm i)),
    memℓp_permute_isometry_aux π T _ (lp.memℓp x)⟩

theorem lp_permute_map_apply_coord
    {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℂ (E i)]
    (π : ι ≃ ι) (T : (i : ι) → E (π.symm i) ≃ₗᵢ[ℂ] E i)
    (x : lp E 2) (i : ι) :
    (lp_permute_map_apply π T x) i = T i (x (π.symm i)) := rfl

theorem lp_permute_map_add
    {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℂ (E i)]
    (π : ι ≃ ι) (T : (i : ι) → E (π.symm i) ≃ₗᵢ[ℂ] E i)
    (x y : lp E 2) :
    lp_permute_map_apply π T (x + y)
      = lp_permute_map_apply π T x + lp_permute_map_apply π T y := by
  apply lp.ext
  funext i
  change T i ((x + y) (π.symm i))
    = (lp_permute_map_apply π T x + lp_permute_map_apply π T y) i
  rw [lp.coeFn_add, Pi.add_apply, map_add, lp.coeFn_add, Pi.add_apply]
  rfl

theorem lp_permute_map_smul
    {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℂ (E i)]
    (π : ι ≃ ι) (T : (i : ι) → E (π.symm i) ≃ₗᵢ[ℂ] E i)
    (c : ℂ) (x : lp E 2) :
    lp_permute_map_apply π T (c • x) = c • lp_permute_map_apply π T x := by
  apply lp.ext
  funext i
  change T i ((c • x) (π.symm i))
    = (c • lp_permute_map_apply π T x) i
  rw [lp.coeFn_smul, Pi.smul_apply, map_smul, lp.coeFn_smul, Pi.smul_apply]
  rfl

theorem lp_permute_map_norm
    {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℂ (E i)]
    (π : ι ≃ ι) (T : (i : ι) → E (π.symm i) ≃ₗᵢ[ℂ] E i)
    (x : lp E 2) :
    ‖lp_permute_map_apply π T x‖ = ‖x‖ := by
  have htwo : (0 : ℝ) < (2 : ENNReal).toReal := by
    rw [ENNReal.toReal_ofNat]; norm_num
  have hLHS := lp.norm_rpow_eq_tsum (p := 2) htwo
    (lp_permute_map_apply π T x)
  have hRHS := lp.norm_rpow_eq_tsum (p := 2) htwo x
  have hpointwise : ∀ i,
      ‖(lp_permute_map_apply π T x : ∀ j, E j) i‖
        ^ ((2 : ENNReal).toReal)
        = ‖(x : ∀ j, E j) (π.symm i)‖ ^ ((2 : ENNReal).toReal) := by
    intro i
    change ‖T i ((x : ∀ j, E j) (π.symm i))‖ ^ _ = _
    rw [LinearIsometryEquiv.norm_map]
  have hsum_eq :
      ∑' i, ‖(lp_permute_map_apply π T x : ∀ j, E j) i‖
            ^ ((2 : ENNReal).toReal)
        = ∑' i, ‖(x : ∀ j, E j) i‖ ^ ((2 : ENNReal).toReal) := by
    rw [show (fun i => ‖(lp_permute_map_apply π T x : ∀ j, E j) i‖
            ^ ((2 : ENNReal).toReal))
        = (fun i => ‖(x : ∀ j, E j) (π.symm i)‖
            ^ ((2 : ENNReal).toReal))
      from funext hpointwise]
    exact π.symm.tsum_eq (fun i' => ‖(x : ∀ j, E j) i'‖
      ^ ((2 : ENNReal).toReal))
  have hpow_eq : ‖lp_permute_map_apply π T x‖ ^ ((2 : ENNReal).toReal)
      = ‖x‖ ^ ((2 : ENNReal).toReal) := by
    rw [hLHS, hRHS, hsum_eq]
  have h2real : ((2 : ENNReal).toReal : ℝ) = 2 := by norm_num
  rw [h2real] at hpow_eq
  -- Convert ‖·‖^(2:ℝ) to ‖·‖^(2:ℕ) and use sq_eq_sq₀.
  rw [Real.rpow_two, Real.rpow_two] at hpow_eq
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hpow_eq

/-- Generic lp index-permutation + per-fiber isometry as a
`LinearIsometry`. -/
noncomputable def lp_permute_map_LI
    {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℂ (E i)]
    (π : ι ≃ ι) (T : (i : ι) → E (π.symm i) ≃ₗᵢ[ℂ] E i) :
    lp E 2 →ₗᵢ[ℂ] lp E 2 where
  toFun := lp_permute_map_apply π T
  map_add' := lp_permute_map_add π T
  map_smul' := lp_permute_map_smul π T
  norm_map' := lp_permute_map_norm π T

/-- Surjectivity of the generic `lp` permute-and-map operator.
The preimage of `y` is built via `Equiv.piCongrLeft'.symm` applied to
the fiberwise inverse `j ↦ (T j).symm (y j)`; this provides the
cast-free identity
`inv_fun (π.symm b) = (T b).symm (y b)` (instead of the awkward
`Equiv.symm_apply_apply π a ▸ ...` form), which makes the round-trip
computation `lp_permute_map_apply π T (B y) = y` close with one
`apply_symm_apply`. -/
theorem lp_permute_map_surjective
    {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℂ (E i)]
    (π : ι ≃ ι) (T : (i : ι) → E (π.symm i) ≃ₗᵢ[ℂ] E i) :
    Function.Surjective (lp_permute_map_apply π T) := by
  intro y
  let g : (j : ι) → E (π.symm j) := fun j => (T j).symm (y j)
  let inv_fun : (a : ι) → E a := (Equiv.piCongrLeft' E π).symm g
  have h_inv_at_symm : ∀ b, inv_fun (π.symm b) = (T b).symm (y b) := fun b =>
    Equiv.piCongrLeft'_symm_apply_apply E π g b
  have htwo : (0 : ℝ) < (2 : ENNReal).toReal := by
    rw [ENNReal.toReal_ofNat]; norm_num
  have hy_sum : Summable (fun i => ‖y i‖ ^ ((2 : ENNReal).toReal)) :=
    (lp.memℓp y).summable htwo
  have hreindex_sum :
      Summable (fun b => ‖inv_fun (π.symm b)‖ ^ ((2 : ENNReal).toReal)) := by
    refine hy_sum.congr (fun b => ?_)
    rw [h_inv_at_symm, LinearIsometryEquiv.norm_map]
  have hsum : Summable (fun a => ‖inv_fun a‖ ^ ((2 : ENNReal).toReal)) :=
    π.symm.summable_iff.mp hreindex_sum
  have hinv_mem : Memℓp inv_fun 2 := (memℓp_gen_iff htwo).mpr hsum
  refine ⟨⟨inv_fun, hinv_mem⟩, ?_⟩
  apply lp.ext
  funext i
  change T i (inv_fun (π.symm i)) = y i
  rw [h_inv_at_symm]
  exact (T i).apply_symm_apply (y i)

/-- Generic lp index-permutation + per-fiber isometry as a
`LinearIsometryEquiv`.  Bundles `lp_permute_map_LI` with the surjectivity
proof from `lp_permute_map_surjective`. -/
noncomputable def lp_permute_map_LIE
    {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℂ (E i)]
    (π : ι ≃ ι) (T : (i : ι) → E (π.symm i) ≃ₗᵢ[ℂ] E i) :
    lp E 2 ≃ₗᵢ[ℂ] lp E 2 :=
  LinearIsometryEquiv.ofSurjective (lp_permute_map_LI π T)
    (lp_permute_map_surjective π T)

@[simp]
theorem lp_permute_map_LIE_apply_coord
    {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℂ (E i)]
    (π : ι ≃ ι) (T : (i : ι) → E (π.symm i) ≃ₗᵢ[ℂ] E i)
    (x : lp E 2) (i : ι) :
    (lp_permute_map_LIE π T x) i = T i (x (π.symm i)) := rfl

/-! ### Phase 8 deliverable: instantiate the generic lp aux -/

/-- **Phase 8 sector-permuting unitary**: bundled as a `LinearIsometry`
on `decomposableLatticeITP L`. -/
noncomputable def decomposableUnitaryActionLI
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G) :
    decomposableLatticeITP L →ₗᵢ[ℂ] decomposableLatticeITP L :=
  lp_permute_map_LI
    (E := fun q : Quotient (InfiniteTensor.UnitFamily.c0Equiv
          (H := fun s : L => siteHilbert (L := L) s)) =>
        InfiniteTensor.UnitFamily.ITPSector
          (H := fun s : L => siteHilbert (L := L) s) q.out)
    (sectorClassActionEquiv L act g)
    (fiberActionEquiv L act g)

@[simp]
theorem decomposableUnitaryActionLI_apply_coord
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G)
    (x : decomposableLatticeITP L)
    (q : Quotient (InfiniteTensor.UnitFamily.c0Equiv
        (H := fun s : L => siteHilbert (L := L) s))) :
    (decomposableUnitaryActionLI L act g x) q
      = fiberActionEquiv L act g q
          (x ((sectorClassActionEquiv L act g).symm q)) := rfl

/-- The norm of `decomposableUnitaryActionLI L act g x` agrees with `‖x‖`.
This is `LinearIsometry.norm_map` specialised to our deliverable. -/
@[simp]
theorem decomposableUnitaryActionLI_norm_map
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G)
    (x : decomposableLatticeITP L) :
    ‖decomposableUnitaryActionLI L act g x‖ = ‖x‖ :=
  (decomposableUnitaryActionLI L act g).norm_map x

/-- Additivity of `decomposableUnitaryActionLI L act g`. -/
theorem decomposableUnitaryActionLI_map_add
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G)
    (x y : decomposableLatticeITP L) :
    decomposableUnitaryActionLI L act g (x + y)
      = decomposableUnitaryActionLI L act g x
        + decomposableUnitaryActionLI L act g y :=
  (decomposableUnitaryActionLI L act g).map_add x y

/-- ℂ-linearity of `decomposableUnitaryActionLI L act g`. -/
theorem decomposableUnitaryActionLI_map_smul
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G)
    (c : ℂ) (x : decomposableLatticeITP L) :
    decomposableUnitaryActionLI L act g (c • x)
      = c • decomposableUnitaryActionLI L act g x :=
  (decomposableUnitaryActionLI L act g).map_smul c x

/-- Injectivity of `decomposableUnitaryActionLI L act g`. -/
theorem decomposableUnitaryActionLI_injective
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G) :
    Function.Injective (decomposableUnitaryActionLI L act g) :=
  (decomposableUnitaryActionLI L act g).injective

/-- **Phase 8 sector-permuting unitary**: bundled as a
`LinearIsometryEquiv` on `decomposableLatticeITP L`.  Surjectivity is
inherited from the generic `lp_permute_map_LIE`. -/
noncomputable def decomposableUnitaryActionLIE
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G) :
    decomposableLatticeITP L ≃ₗᵢ[ℂ] decomposableLatticeITP L :=
  lp_permute_map_LIE
    (E := fun q : Quotient (InfiniteTensor.UnitFamily.c0Equiv
          (H := fun s : L => siteHilbert (L := L) s)) =>
        InfiniteTensor.UnitFamily.ITPSector
          (H := fun s : L => siteHilbert (L := L) s) q.out)
    (sectorClassActionEquiv L act g)
    (fiberActionEquiv L act g)

@[simp]
theorem decomposableUnitaryActionLIE_apply_coord
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G)
    (x : decomposableLatticeITP L)
    (q : Quotient (InfiniteTensor.UnitFamily.c0Equiv
        (H := fun s : L => siteHilbert (L := L) s))) :
    (decomposableUnitaryActionLIE L act g x) q
      = fiberActionEquiv L act g q
          (x ((sectorClassActionEquiv L act g).symm q)) := rfl

/-- The underlying function of `decomposableUnitaryActionLIE` agrees
with `decomposableUnitaryActionLI`. -/
@[simp]
theorem decomposableUnitaryActionLIE_coe
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G) :
    ⇑(decomposableUnitaryActionLIE L act g)
      = ⇑(decomposableUnitaryActionLI L act g) := rfl

/-- Surjectivity of `decomposableUnitaryActionLI L act g`, obtained via
the LIE bundle. -/
theorem decomposableUnitaryActionLI_surjective
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G) :
    Function.Surjective (decomposableUnitaryActionLI L act g) :=
  (decomposableUnitaryActionLIE L act g).surjective

/-- Bijectivity of `decomposableUnitaryActionLI L act g`. -/
theorem decomposableUnitaryActionLI_bijective
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G) :
    Function.Bijective (decomposableUnitaryActionLI L act g) :=
  ⟨decomposableUnitaryActionLI_injective L act g,
   decomposableUnitaryActionLI_surjective L act g⟩

/-! ### Phase 8 final form: `LinearIsometryEquiv` characterisation

`decomposableUnitaryActionLIE L act g` is the Phase 8 deliverable as a
bundled `LinearIsometryEquiv` on `decomposableLatticeITP L`, with the
underlying `LinearIsometry` being `decomposableUnitaryActionLI L act g`.
The bundle provides:

* coordinate access (`decomposableUnitaryActionLIE_apply_coord`);
* underlying-LI agreement (`decomposableUnitaryActionLIE_coe`);
* injectivity (`decomposableUnitaryActionLI_injective`);
* surjectivity (`decomposableUnitaryActionLI_surjective`);
* bijectivity (`decomposableUnitaryActionLI_bijective`);
* norm preservation (`decomposableUnitaryActionLI_norm_map`);
* additivity / ℂ-linearity (`decomposableUnitaryActionLI_map_add`,
  `decomposableUnitaryActionLI_map_smul`).

The surjectivity proof avoids the awkward
`Equiv.symm_apply_apply π q ▸ ((T (π q)).symm (y (π q)))` cast by
constructing the preimage via `Equiv.piCongrLeft'.symm`, which yields
the cast-free `inv_fun (π.symm b) = (T b).symm (y b)` identity used
in `lp_permute_map_surjective`.

Note that **`g`-functoriality** (`one`/`mul` for the family
`g ↦ decomposableUnitaryActionLIE L act g`) still does not hold: the
per-fiber `fiberActionEquiv` is built via `sectorEquivAny`, which uses
`Classical.choice` and so picks independent unitaries for different
`g`s.  A canonical functorial sector-permuting unitary would require
lifting the per-site `siteHilbertEquiv g s` action through the colimit
construction (mirroring Phase 3a's V_s rotation but with the geometric
group-action data) — substantial new mathematics beyond the present
plan. -/

/-- The reference sector class is fixed by the inverse permutation
`(sectorClassActionEquiv L act g).symm`.

This is the analogue of `sectorClassAction_referenceSectorClass`
applied to the Equiv-inverse direction of the sector permutation. -/
theorem sectorClassActionEquiv_symm_referenceSectorClass
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G) :
    (sectorClassActionEquiv L act g).symm (referenceSectorClass L)
      = referenceSectorClass L := by
  -- (sectorClassActionEquiv L act g).symm = Quotient.map (unitFamilyActionSymm L act g) ...
  -- referenceSectorClass = Quotient.mk' (referenceUnitFamily L)
  -- The map sends [referenceUnitFamily L] to [unitFamilyActionSymm L act g (referenceUnitFamily L)].
  -- We need: unitFamilyActionSymm L act g (referenceUnitFamily L) is c0Rel-related to
  -- referenceUnitFamily L.  This holds by applying unitFamilyAction_referenceUnitFamily
  -- to the symm: the symm of the action also fixes the reference family up to c0Rel
  -- (by InfiniteTensor.UnitFamily.c0Equiv.iseqv.refl).
  -- Concrete proof: apply the action g to both sides, using the right-inv property.
  apply (sectorClassActionEquiv L act g).injective
  rw [Equiv.apply_symm_apply]
  exact (sectorClassAction_referenceSectorClass L act g).symm


/-- Sector-equivalent transport of the reference-sector vacuum to the
arbitrary `Quotient.out` representative chosen at `referenceSectorClass L`.

Since `Quotient.out` picks a non-canonical representative of the
`c0Equiv`-class, `(referenceSectorClass L).out` may differ from
`referenceUnitFamily L`.  Phase 3a's `sectorEquivAny` bridges fibers in
the same `c0Equiv`-class. -/
noncomputable def vacuumVectorAtClassOut :
    InfiniteTensor.UnitFamily.ITPSector
        (H := fun s : L => siteHilbert (L := L) s)
        (referenceSectorClass L).out :=
  InfiniteTensor.UnitFamily.noncanonicalSectorEquivAny
    (referenceUnitFamily L) (referenceSectorClass L).out (vacuumVectorSector L)

/-- The **decomposable-space vacuum vector**: the reference-sector vacuum
embedded at the reference-sector position `referenceSectorClass L` of the
BR sector decomposition Hilbert space.

This vector is **not canonical**: the decomposable space has no
distinguished sector without further data.  The choice here is the
reference sector class.  Inside that class, the `Quotient.out`
representative `(referenceSectorClass L).out` is non-canonical; the
reference-sector vacuum `vacuumVectorSector L` (living in `ITPSector
(referenceUnitFamily L)`) is transported there via `sectorEquivAny`. -/
noncomputable def decomposableVacuumVector :
    decomposableLatticeITP L :=
  lp.single (E := fun q : Quotient (InfiniteTensor.UnitFamily.c0Equiv
        (H := fun s : L => siteHilbert (L := L) s)) =>
      InfiniteTensor.UnitFamily.ITPSector
        (H := fun s : L => siteHilbert (L := L) s) q.out) 2
    (referenceSectorClass L) (vacuumVectorAtClassOut L)

/-! ## Phase 9a preparatory bridges: fiberwise region embeddings -/

/-- The `lp.lsingle` map at index `i`, packaged as a `LinearIsometry`
from the fiber `E i` to `lp E 2`.  Norm preservation is
`lp.norm_single` after `lp.lsingle_apply`.  This is a generic helper
used by the fiberwise region embeddings below. -/
noncomputable def lp_single_LI
    {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℂ (E i)] [DecidableEq ι] (i : ι) :
    E i →ₗᵢ[ℂ] lp E 2 where
  toLinearMap := lp.lsingle 2 i
  norm_map' x := by
    rw [lp.lsingle_apply]
    exact lp.norm_single (by norm_num : (0 : ENNReal) < 2) i x

@[simp]
theorem lp_single_LI_apply
    {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℂ (E i)] [DecidableEq ι] (i : ι) (x : E i) :
    lp_single_LI (E := E) i x = lp.single 2 i x := lp.lsingle_apply 2 i x

/-- **Phase 9a forward-looking bridge**: the region-to-decomposable
embedding sends a region vector `ξ : regionHilbert Λ` to its image at
the reference sector class of `decomposableLatticeITP L`.  The chain is

```
regionHilbert Λ ──regionEmbed Λ──→ referenceSectorHilbert L
                                       ↓ (referenceSectorEquiv L).symm
                                 ITPSector (referenceUnitFamily L)
                                       ↓ sectorEquivAny ⋯ (refSecCls L).out
                                 ITPSector (referenceSectorClass L).out
                                       ↓ lp.lsingle 2 (referenceSectorClass L)
                                 decomposableLatticeITP L
```

Once Phase 9c switches `globalHilbert L := decomposableLatticeITP L`,
this is the new spelling of `regionEmbed Λ`; the existing
`regionEmbed Λ : regionHilbert Λ →ₗᵢ[ℂ] referenceSectorHilbert L` is
the layer-1 component of this composite. -/
noncomputable def regionEmbedDecomp (Λ : Finset L) :
    regionHilbert (L := L) Λ →ₗᵢ[ℂ] decomposableLatticeITP L :=
  (lp_single_LI
      (E := fun q : Quotient (InfiniteTensor.UnitFamily.c0Equiv
            (H := fun s : L => siteHilbert (L := L) s)) =>
          InfiniteTensor.UnitFamily.ITPSector
            (H := fun s : L => siteHilbert (L := L) s) q.out)
      (referenceSectorClass L)).comp
    ((InfiniteTensor.UnitFamily.noncanonicalSectorEquivAny (referenceUnitFamily L)
        (referenceSectorClass L).out).toLinearIsometry.comp
      ((referenceSectorEquiv L).symm.toLinearIsometry.comp
        (regionEmbed Λ)))

@[simp]
theorem regionEmbedDecomp_apply (Λ : Finset L)
    (ξ : regionHilbert (L := L) Λ) :
    regionEmbedDecomp L Λ ξ
      = lp.single (E := fun q : Quotient (InfiniteTensor.UnitFamily.c0Equiv
            (H := fun s : L => siteHilbert (L := L) s)) =>
          InfiniteTensor.UnitFamily.ITPSector
            (H := fun s : L => siteHilbert (L := L) s) q.out) 2
        (referenceSectorClass L)
        (InfiniteTensor.UnitFamily.noncanonicalSectorEquivAny (referenceUnitFamily L)
          (referenceSectorClass L).out
          ((referenceSectorEquiv L).symm (regionEmbed Λ ξ))) := by
  change lp_single_LI _ _ = _
  rw [lp_single_LI_apply]
  rfl

/-- **Cocone compatibility**: `regionEmbedDecomp` factors through any
larger finite region, i.e. `regionEmbedDecomp Λ' ∘ regionEmbedLe h =
regionEmbedDecomp Λ`.  Inherited from
`regionEmbed_apply_regionEmbedLe` via the lp-single chain. -/
theorem regionEmbedDecomp_apply_regionEmbedLe {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (ξ : regionHilbert (L := L) Λ) :
    regionEmbedDecomp L Λ' (regionEmbedLe h ξ) = regionEmbedDecomp L Λ ξ := by
  rw [regionEmbedDecomp_apply, regionEmbedDecomp_apply,
    regionEmbed_apply_regionEmbedLe h ξ]

/-- The region-to-decomposable embedding preserves inner products.
Inherited from the `LinearIsometry` structure of `regionEmbedDecomp`. -/
theorem regionEmbedDecomp_inner (Λ : Finset L)
    (ξ η : regionHilbert (L := L) Λ) :
    inner ℂ (regionEmbedDecomp L Λ ξ) (regionEmbedDecomp L Λ η)
      = inner ℂ ξ η :=
  (regionEmbedDecomp L Λ).inner_map_map ξ η

/-- The reference-sector-to-`globalHilbert` isometric embedding.  After
Phase 9c (`globalHilbert L = decomposableLatticeITP L`), this is the
identification of the old single-sector model `referenceSectorHilbert L`
with one fiber of the decomposition (the reference sector class). -/
noncomputable def referenceSectorHilbertEmbedDecomp :
    referenceSectorHilbert L →ₗᵢ[ℂ] globalHilbert L :=
  (lp_single_LI
      (E := fun q : Quotient (InfiniteTensor.UnitFamily.c0Equiv
            (H := fun s : L => siteHilbert (L := L) s)) =>
          InfiniteTensor.UnitFamily.ITPSector
            (H := fun s : L => siteHilbert (L := L) s) q.out)
      (referenceSectorClass L)).comp
    ((InfiniteTensor.UnitFamily.noncanonicalSectorEquivAny (referenceUnitFamily L)
        (referenceSectorClass L).out).toLinearIsometry.comp
      (referenceSectorEquiv L).symm.toLinearIsometry)

@[simp]
theorem referenceSectorHilbertEmbedDecomp_apply
    (v : referenceSectorHilbert L) :
    referenceSectorHilbertEmbedDecomp L v
      = lp.single (E := fun q : Quotient (InfiniteTensor.UnitFamily.c0Equiv
            (H := fun s : L => siteHilbert (L := L) s)) =>
          InfiniteTensor.UnitFamily.ITPSector
            (H := fun s : L => siteHilbert (L := L) s) q.out) 2
        (referenceSectorClass L)
        (InfiniteTensor.UnitFamily.noncanonicalSectorEquivAny (referenceUnitFamily L)
          (referenceSectorClass L).out
          ((referenceSectorEquiv L).symm v)) := by
  change lp_single_LI _ _ = _
  rw [lp_single_LI_apply]
  rfl

/-- `regionEmbedDecomp` factors through `regionEmbed` followed by the
reference-to-decomposable embedding. -/
theorem regionEmbedDecomp_eq_referenceSectorHilbertEmbedDecomp_comp
    (Λ : Finset L) (ξ : regionHilbert (L := L) Λ) :
    regionEmbedDecomp L Λ ξ
      = referenceSectorHilbertEmbedDecomp L (regionEmbed Λ ξ) := by
  rw [regionEmbedDecomp_apply, referenceSectorHilbertEmbedDecomp_apply]

/-- `range (regionEmbedDecomp L Λ)` is the image under
`referenceSectorHilbertEmbedDecomp L` of `range (regionEmbed Λ)`. -/
theorem range_regionEmbedDecomp (Λ : Finset L) :
    Set.range (regionEmbedDecomp L Λ : regionHilbert (L := L) Λ → globalHilbert L)
      = (referenceSectorHilbertEmbedDecomp L) ''
          (Set.range (regionEmbed Λ : regionHilbert (L := L) Λ → _)) := by
  ext y
  constructor
  · rintro ⟨ξ, hξ⟩
    exact ⟨regionEmbed Λ ξ, ⟨ξ, rfl⟩,
      by rw [← hξ, regionEmbedDecomp_eq_referenceSectorHilbertEmbedDecomp_comp]⟩
  · rintro ⟨v, ⟨ξ, hvξ⟩, hv⟩
    exact ⟨ξ, by
      rw [regionEmbedDecomp_eq_referenceSectorHilbertEmbedDecomp_comp, hvξ]
      exact hv⟩

/-- `⋃Λ, range (regionEmbedDecomp Λ)` is the image under
`referenceSectorHilbertEmbedDecomp L` of `⋃Λ, range (regionEmbed Λ)`. -/
theorem iUnion_range_regionEmbedDecomp :
    (⋃ Λ : Finset L, Set.range
        (regionEmbedDecomp L Λ : regionHilbert (L := L) Λ → globalHilbert L))
      = (referenceSectorHilbertEmbedDecomp L) ''
          (⋃ Λ : Finset L, Set.range
            (regionEmbed Λ : regionHilbert (L := L) Λ → _)) := by
  rw [Set.image_iUnion]
  exact Set.iUnion_congr (fun Λ => range_regionEmbedDecomp L Λ)

/-- **Closure compatibility**: the closure of the union of fiberwise
region-embedding ranges in the decomposable space equals the range of
the reference-sector embedding.  In other words, the fiberwise
embeddings span exactly the reference-sector subspace inside
`globalHilbert L = decomposableLatticeITP L`.

This is the post-9c analogue of `dense_iUnion_regionEmbed_range`: the
old density statement held in `referenceSectorHilbert L` because that
**is** the reference sector; in the decomposable space the union is no
longer dense, but its closure picks out exactly the reference-sector
fiber. -/
theorem closure_iUnion_range_regionEmbedDecomp :
    closure (⋃ Λ : Finset L, Set.range
        (regionEmbedDecomp L Λ : regionHilbert (L := L) Λ → globalHilbert L))
      = Set.range (referenceSectorHilbertEmbedDecomp L
          : referenceSectorHilbert L → globalHilbert L) := by
  rw [iUnion_range_regionEmbedDecomp L]
  set f : referenceSectorHilbert L → globalHilbert L :=
    ⇑(referenceSectorHilbertEmbedDecomp L) with hf
  have hf_isom : Isometry f := (referenceSectorHilbertEmbedDecomp L).isometry
  have hf_closed : Topology.IsClosedEmbedding f := hf_isom.isClosedEmbedding
  have hf_cont : Continuous f := hf_closed.continuous
  set S : Set (referenceSectorHilbert L) :=
    ⋃ Λ : Finset L, Set.range (regionEmbed Λ
      : regionHilbert (L := L) Λ → referenceSectorHilbert L) with hS
  have hS_dense : Dense S :=
    dense_iUnion_regionEmbed_range (L := L)
  apply le_antisymm
  · -- closure (f '' S) ⊆ range f
    refine closure_minimal ?_ hf_closed.isClosed_range
    intro y hy
    obtain ⟨v, _, rfl⟩ := hy
    exact ⟨v, rfl⟩
  · -- range f ⊆ closure (f '' S)
    rintro y ⟨v, rfl⟩
    have hv_in : v ∈ closure S := hS_dense.closure_eq ▸ Set.mem_univ v
    have h_im : f v ∈ f '' (closure S) := ⟨v, hv_in, rfl⟩
    exact image_closure_subset_closure_image hf_cont h_im

/-! ### Phase 8 functoriality obstruction (analysis)

The migration spec notes that `decomposableUnitaryActionLIE L act g`
is **not** functorial in `g` — i.e. `decomposableUnitaryActionLIE L act
1 ≠ LinearIsometryEquiv.refl ℂ _` and
`decomposableUnitaryActionLIE L act (g₁*g₂) ≠
(decomposableUnitaryActionLIE L act g₂).trans
(decomposableUnitaryActionLIE L act g₁)` in general.

**Where the obstruction lives.**  The fibre-permuting datum
`fiberActionEquiv L act g q` is built via
`InfiniteTensor.UnitFamily.noncanonicalSectorEquivAny`, which uses
`Classical.choice` per site to pick the per-site V-rotation aligning
two `c0Rel`-related representatives.  Different group elements `g`
produce independent (Classical-choice-based) unitaries even between the
same pair of representatives, so `fiberActionEquiv L act g₁ q ∘L
fiberActionEquiv L act g₂ ((π_{g₁}).symm q) ≠ fiberActionEquiv L act
(g₁*g₂) q`.

**What functoriality WOULD hold.**  The sector-class permutation
`sectorClassActionEquiv L act g` IS functorial in `g` (under
`IsGenuineAction`): this would follow from `unitFamilyAction_one`
and `unitFamilyAction_mul` at the `Quotient c0Equiv` level.  Hence the
"index part" of the action composes correctly; only the "fibre part"
(via `noncanonicalSectorEquivAny`) fails.

**Resolution path (sector-equivalence half).**  The new
`SectorEquivData` / `sectorEquivOfData` API in
`QuantumSystem/Analysis/InfiniteTensor/SectorIsometry.lean` resolves the
"same-index" half of the obstruction: it accepts coherent finite-region
transport data and yields a canonical equivalence
`ITPSector Ω ≃ₗᵢ[ℂ] ITPSector Ω'` that does satisfy
`sectorEquivOfData_refl`, `sectorEquivOfData_symm`, and
`sectorEquivOfData_trans`.  Any future canonical wiring of
`fiberActionEquiv` should consume `SectorEquivData` (or a
reindexed-transport extension thereof) rather than `c0Rel` directly.

**Remaining gap (reindexed-transport half).**  Group actions translate
finite supports `S ↦ S.image (act.siteAction g)`, so the appropriate
input is a *reindexed* transport
`regionTensor S ≃ₗᵢ[ℂ] regionTensor (S.image (act.siteAction g))`,
not the same-index `SectorEquivData`.  A `ReindexedSectorTransportData`
structure plus an `ofGroupAction` constructor (lifting per-site
`siteHilbertEquiv L act g s`) would close this gap; once present, the
reference-sector special case (where
`unitFamilyAction L act g (referenceUnitFamily L) = referenceUnitFamily L`
already holds) yields a `referenceFiberActionEquiv` satisfying
`referenceFiberActionEquiv_one` and `referenceFiberActionEquiv_mul`
under `IsGenuineAction`.  See `plan.md` (§ Phase 3, Phase 4) for the
detailed construction; the present file does not consume that
extension. -/

/-! ### Phase 3.2: reindexed group-action sector transport — outstanding gap

The data inputs for `ReindexedSectorTransportData.ofGroupAction` are
all available in this file:

* `regionImageEquiv L act g : Finset L ≃ Finset L` for the `target` field;
* `regionImage_mono` and `regionImageEquiv_symm_mono` for the
  `target_mono` / `target_symm_mono` fields;
* `regionTensorActionEquiv L act g S : regionTensor S ≃ₗᵢ[ℂ]
  regionTensor (act.regionImage g S)` for the `regionMap` field.

The remaining `regionMap_compat` cocycle, however, requires showing that
the action commutes with `regionEmbedLe`, which on tprod's tuple-level
reduces to:

```
regionTensorActionTuple L act g T (extendVec Ω hST ξ) t
  = extendVec (unitFamilyAction L act g Ω) (regionImage_mono ... hST)
      (regionTensorActionTuple L act g S ξ) t
```

The "inside the smaller region" branch (`((siteSubtypeEquiv g T).symm
t).val ∈ S`) closes by `rfl` after `extendVec_inside` rewrites.  The
"outside" branch reduces to the equation

```
siteHilbertSubtypeEquiv L act g T t (Ω.vec ((siteSubtypeEquiv g T).symm t).val)
  = (unitFamilyAction L act g Ω).vec t.val
```

which is mathematically true but requires `Eq.rec`-level cast
manipulation:  both sides factor through the same propositional equation
`(act.siteAction g).symm_apply_apply` applied through
`(siteSubtypeEquiv g T).symm`'s definitional reduction, but the two
casts have syntactically distinct proof terms.  Discharging this in Lean
requires HEq machinery (`cast_heq` for the `Eq.mpr` in
`siteHilbertSubtypeEquiv`'s definition, paired with `congr_arg_heq` for
the `Subtype.ext`-driven index propagation) that does not yet
materialize cleanly through the available tactic stack.

**Current status.**  Phase 1 (`SectorEquivData` + `sectorEquivOfData`),
Phase 2 (`FiniteSiteIsoData` + `ofFiniteSiteIso` + `ofReferenceRel`),
and Phase 3.1 (`ReindexedSectorTransportData` structure +
`sectorEquivOfReindexedData`) are all in place in
`SectorIsometry.lean`.  Phase 3.2's `ofGroupAction` constructor is the
last piece; once the dependent-type cocycle proof above is settled, the
`referenceFiberActionEquiv` below (Phase 4 reference fiber, already
implemented) generalizes to arbitrary fibers via the reindexed transport
machinery.

See `plan.md` (§ Phase 3, Phase 4) for the design doc. -/

/-! ### Phase 4: canonical reference-sector group action

For the **reference sector** specifically (`Ω = referenceUnitFamily L`),
the obstruction can be sidestepped: the canonical isometric equivalence
`referenceSectorEquiv L : ITPSector ref ≃ₗᵢ[ℂ] referenceSectorHilbert L`
already exists, and the lattice-side `unitaryAction g` is a canonical,
functorial unitary representation (under `IsGenuineAction`) by
`Covariance.unitaryAction_one` / `unitaryAction_mul`.  Pulling back
through `referenceSectorEquiv L` yields a canonical group action on
`ITPSector ref` that satisfies the corresponding `_one` and `_mul`
laws — without invoking `noncanonicalSectorEquivAny`.

This delivers the Phase 4 deliverable for the reference fiber.  Extending
to general fibers requires the reindexed-transport machinery discussed
in the obstruction comment above. -/

/-- **Phase 4 reference-sector canonical action**: pull back the
lattice-side `unitaryAction g` through `referenceSectorEquiv L` to
obtain a canonical isometric equivalence on `ITPSector ref`. -/
noncomputable def referenceFiberActionEquiv
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G) :
    InfiniteTensor.UnitFamily.ITPSector (H := siteHilbert (L := L))
        (referenceUnitFamily L)
      ≃ₗᵢ[ℂ] InfiniteTensor.UnitFamily.ITPSector
        (H := siteHilbert (L := L)) (referenceUnitFamily L) :=
  (referenceSectorEquiv L).trans
    ((act.unitaryAction g).trans (referenceSectorEquiv L).symm)

@[simp]
theorem referenceFiberActionEquiv_apply
    {G : Type*} [Group G] (act : HasGroupAction L G) (g : G)
    (x : InfiniteTensor.UnitFamily.ITPSector (H := siteHilbert (L := L))
        (referenceUnitFamily L)) :
    referenceFiberActionEquiv L act g x
      = (referenceSectorEquiv L).symm
          (act.unitaryAction g (referenceSectorEquiv L x)) := rfl

/-- **Phase 4 identity law**: under `IsGenuineAction`, the canonical
reference-sector action sends the group identity to the identity
isometry. -/
@[simp]
theorem referenceFiberActionEquiv_one
    {G : Type*} [Group G] (act : HasGroupAction L G) [act.IsGenuineAction] :
    referenceFiberActionEquiv L act (1 : G)
      = LinearIsometryEquiv.refl ℂ
          (InfiniteTensor.UnitFamily.ITPSector (H := siteHilbert (L := L))
            (referenceUnitFamily L)) := by
  ext x
  rw [referenceFiberActionEquiv_apply, act.unitaryAction_one]
  change (referenceSectorEquiv L).symm
      (referenceSectorEquiv L x)
    = x
  rw [LinearIsometryEquiv.symm_apply_apply]

/-- **Phase 4 composition law**: under `IsGenuineAction`, the canonical
reference-sector action satisfies the group multiplication rule. -/
theorem referenceFiberActionEquiv_mul
    {G : Type*} [Group G] (act : HasGroupAction L G) [act.IsGenuineAction]
    (g h : G) :
    referenceFiberActionEquiv L act (g * h)
      = (referenceFiberActionEquiv L act h).trans
          (referenceFiberActionEquiv L act g) := by
  ext x
  rw [referenceFiberActionEquiv_apply, act.unitaryAction_mul]
  change (referenceSectorEquiv L).symm
      (act.unitaryAction g (act.unitaryAction h (referenceSectorEquiv L x)))
    = referenceFiberActionEquiv L act g
        (referenceFiberActionEquiv L act h x)
  rw [referenceFiberActionEquiv_apply, referenceFiberActionEquiv_apply,
    LinearIsometryEquiv.apply_symm_apply]

end LocalNetLike
