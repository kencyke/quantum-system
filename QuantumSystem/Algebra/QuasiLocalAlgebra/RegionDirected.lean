module

public import QuantumSystem.Algebra.QuasiLocalAlgebra.RegionEmbed

/-!
# Directed system of region Hilbert spaces (Phase 2-a)

For each pair `Λ ⊆ Λ'` of finite regions we build the canonical isometric
embedding

`regionEmbedLe h : regionHilbert Λ →ₗᵢ[ℂ] regionHilbert Λ'`

obtained by extending region tuples by the reference basis on `Λ' \ Λ`.
The collection of such embeddings makes `Λ ↦ regionHilbert Λ` a directed
system of finite-dimensional Hilbert spaces in the `Finset L` order, with
the *vector* embedding `regionEmbed Λ : regionHilbert Λ →ₗᵢ[ℂ] globalHilbert L`
of `RegionEmbed.lean` as a co-cone.

The density of the union of `regionEmbed Λ`-images and the universal property
realising `globalHilbert L` as the Hilbert co-limit are the content of the
companion file (Phase 2-b).

## Main definitions

* `LocalNetLike.extendRegionTupleLe h` — extension of a region tuple from
  `Λ` to `Λ'`, filling new sites with `referenceBasis L`.
* `LocalNetLike.regionEmbedLe h` — region-to-region isometric embedding
  `regionHilbert Λ →ₗᵢ[ℂ] regionHilbert Λ'`.

## Main results

* `LocalNetLike.regionEmbedLe_apply_basis` — basis-vector behaviour.
* `LocalNetLike.regionEmbed_apply_regionEmbedLe` — co-cone compatibility:
  `regionEmbed Λ' ∘ regionEmbedLe h = regionEmbed Λ`.

## References

* Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §3.5.
* Bratteli, Robinson, *Operator Algebras and Quantum Statistical Mechanics II*,
  §2.7.2.
-/

@[expose] public section

open scoped LocalNetLike InnerProductSpace
open Module

namespace LocalNetLike

variable {L : Type*} [DecidableEq L] [LocalNetLike L]
    [hL : ∀ s : L, Nonempty (LocalNetLike.localIdx (L := L) s)]

/-! ### Region-to-region tuple extension -/

/-- Extension of a region tuple `f : regionIdx Λ` to a region tuple in a larger
region `Λ' ⊇ Λ` by filling the new sites with `referenceBasis L`.  The
hypothesis `_h : Λ ⊆ Λ'` is purely intentional (the `if`-test on `s.1 ∈ Λ`
makes the body well-defined without it) and is required by every theorem
asserting a property of the resulting tuple. -/
noncomputable def extendRegionTupleLe {Λ Λ' : Finset L} (_h : Λ ⊆ Λ')
    (f : regionIdx (L := L) Λ) : regionIdx (L := L) Λ' :=
  fun s => if hs : s.1 ∈ Λ then f ⟨s.1, hs⟩ else referenceBasis L s.1

@[simp]
theorem extendRegionTupleLe_apply_of_mem {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (f : regionIdx (L := L) Λ) {s : Λ'} (hs : s.1 ∈ Λ) :
    extendRegionTupleLe h f s = f ⟨s.1, hs⟩ :=
  dif_pos hs

@[simp]
theorem extendRegionTupleLe_apply_of_not_mem {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (f : regionIdx (L := L) Λ) {s : Λ'} (hs : s.1 ∉ Λ) :
    extendRegionTupleLe h f s = referenceBasis L s.1 :=
  dif_neg hs

theorem extendRegionTupleLe_injective {Λ Λ' : Finset L} (h : Λ ⊆ Λ') :
    Function.Injective (extendRegionTupleLe (L := L) h) := by
  intro f g hfg
  funext ⟨s, hsΛ⟩
  have hsΛ' : s ∈ Λ' := h hsΛ
  have heq := congrFun hfg ⟨s, hsΛ'⟩
  simpa [extendRegionTupleLe, hsΛ] using heq

/-- Compatibility of the two-stage extension: `Λ → Λ' → L` agrees with the
direct extension `Λ → L` from `LocalEmbed.lean`. -/
theorem extendRegionTuple_extendRegionTupleLe {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (f : regionIdx (L := L) Λ) :
    extendRegionTuple Λ' (extendRegionTupleLe h f) = extendRegionTuple Λ f := by
  apply Subtype.ext
  funext s
  by_cases hsΛ' : s ∈ Λ'
  · rw [extendRegionTuple_val_apply_of_mem _ _ hsΛ']
    by_cases hsΛ : s ∈ Λ
    · rw [extendRegionTupleLe_apply_of_mem h _ hsΛ,
          extendRegionTuple_val_apply_of_mem _ _ hsΛ]
    · rw [extendRegionTupleLe_apply_of_not_mem h _ hsΛ,
          extendRegionTuple_val_apply_of_not_mem _ _ hsΛ]
  · rw [extendRegionTuple_val_apply_of_not_mem _ _ hsΛ']
    have hsΛ : s ∉ Λ := fun h' => hsΛ' (h h')
    rw [extendRegionTuple_val_apply_of_not_mem _ _ hsΛ]

/-! ### Region-to-region isometric embedding -/

/-- Region-to-region isometric embedding for a finite-region inclusion
`h : Λ ⊆ Λ'`.  Sends a region-basis vector `EuclideanSpace.single f 1` to the
basis vector `EuclideanSpace.single (extendRegionTupleLe h f) 1` of the larger
region. -/
noncomputable def regionEmbedLe {Λ Λ' : Finset L} (h : Λ ⊆ Λ') :
    regionHilbert Λ →ₗᵢ[ℂ] regionHilbert Λ' :=
  LinearMap.isometryOfOrthonormal
    (v := (EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).toBasis)
    ((EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).toBasis.constr ℂ
      fun f : regionIdx (L := L) Λ =>
        (EuclideanSpace.single (extendRegionTupleLe h f) (1 : ℂ) :
          regionHilbert Λ'))
    (by
      change Orthonormal ℂ ⇑((EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).toBasis)
      rw [OrthonormalBasis.coe_toBasis]
      exact (EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).orthonormal)
    (by
      have hbasis := (EuclideanSpace.basisFun (regionIdx (L := L) Λ') ℂ).orthonormal
      have hext := hbasis.comp (extendRegionTupleLe h) (extendRegionTupleLe_injective h)
      have hfun :
          (⇑((EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).toBasis.constr ℂ
                fun f : regionIdx (L := L) Λ =>
                  (EuclideanSpace.single (extendRegionTupleLe h f) (1 : ℂ) :
                    regionHilbert Λ'))
              ∘ ⇑((EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).toBasis))
            = ((fun g : regionIdx (L := L) Λ' =>
                  (EuclideanSpace.basisFun (regionIdx (L := L) Λ') ℂ) g)
                ∘ extendRegionTupleLe h) := by
        funext i
        simp [Function.comp_apply, EuclideanSpace.basisFun_apply]
      rw [hfun]
      exact hext)

@[simp]
theorem regionEmbedLe_apply_basis {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (f : regionIdx (L := L) Λ) :
    regionEmbedLe h (EuclideanSpace.single f (1 : ℂ))
      = (EuclideanSpace.single (extendRegionTupleLe h f) (1 : ℂ) :
          regionHilbert Λ') := by
  change ((EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).toBasis.constr ℂ
      fun f' : regionIdx (L := L) Λ =>
        (EuclideanSpace.single (extendRegionTupleLe h f') (1 : ℂ) :
          regionHilbert Λ'))
      (EuclideanSpace.single f (1 : ℂ)) = _
  rw [show (EuclideanSpace.single f (1 : ℂ) : regionHilbert Λ)
        = (EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).toBasis f
      from by rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]]
  simp

/-! ### Co-cone compatibility with `regionEmbed` -/

/-- `regionEmbed` is a co-cone over the directed system: the global embedding
factors through any larger finite region. -/
theorem regionEmbed_apply_regionEmbedLe {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (ξ : regionHilbert Λ) :
    regionEmbed Λ' (regionEmbedLe h ξ) = regionEmbed Λ ξ := by
  -- Both sides are linear in ξ; check on the basis of regionHilbert Λ.
  have hbasis :
      ((regionEmbed Λ').toLinearMap.comp (regionEmbedLe h).toLinearMap)
        = (regionEmbed Λ).toLinearMap := by
    refine ((EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).toBasis).ext ?_
    intro f
    simp [LinearMap.comp_apply, OrthonormalBasis.coe_toBasis,
          EuclideanSpace.basisFun_apply, extendRegionTuple_extendRegionTupleLe]
  exact LinearMap.congr_fun hbasis ξ

end LocalNetLike
