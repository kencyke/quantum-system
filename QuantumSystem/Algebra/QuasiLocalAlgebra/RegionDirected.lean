module

public import QuantumSystem.Algebra.QuasiLocalAlgebra.RegionEmbed

/-!
# Directed system of region Hilbert spaces

For each pair `Λ ⊆ Λ'` of finite regions, the canonical isometric embedding

`regionEmbedLe h : regionHilbert Λ →ₗᵢ[ℂ] regionHilbert Λ'`,

obtained by extending region tuples by `Ω` on `Λ' \ Λ`.  This makes
`Λ ↦ regionHilbert Λ` a directed system in the `Finset L` order, with
`regionEmbed Λ : regionHilbert Λ →ₗᵢ[ℂ] globalHilbert L Ω` as a co-cone.

The companion file `RegionColimit.lean` proves density of the union of
`regionEmbed Λ`-images.

## Main definitions

* `LocalNetLike.extendRegionTupleLe h` — extension of a region tuple, filling
  new sites with `Ω`.
* `LocalNetLike.regionEmbedLe h` — region-to-region isometric embedding.

## Main results

* `LocalNetLike.regionEmbedLe_apply_basis` — basis-vector behaviour.
* `LocalNetLike.regionEmbed_apply_regionEmbedLe` — co-cone compatibility.

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
variable (Ω : (s : L) → LocalNetLike.localIdx (L := L) s)

/-! ### Region-to-region tuple extension -/

/-- Extension of a region tuple from `Λ` to a larger region `Λ' ⊇ Λ` by filling
new sites with `Ω`.  The hypothesis `_h : Λ ⊆ Λ'` is unused in the construction
but required by downstream lemmas. -/
noncomputable def extendRegionTupleLe {Λ Λ' : Finset L} (_h : Λ ⊆ Λ')
    (f : regionIdx (L := L) Λ) : regionIdx (L := L) Λ' :=
  fun s => if hs : s.1 ∈ Λ then f ⟨s.1, hs⟩ else Ω s.1

variable {Ω}

@[simp]
theorem extendRegionTupleLe_apply_of_mem {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (f : regionIdx (L := L) Λ) {s : Λ'} (hs : s.1 ∈ Λ) :
    extendRegionTupleLe Ω h f s = f ⟨s.1, hs⟩ :=
  dif_pos hs

@[simp]
theorem extendRegionTupleLe_apply_of_not_mem {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (f : regionIdx (L := L) Λ) {s : Λ'} (hs : s.1 ∉ Λ) :
    extendRegionTupleLe Ω h f s = Ω s.1 :=
  dif_neg hs

theorem extendRegionTupleLe_injective {Λ Λ' : Finset L} (h : Λ ⊆ Λ') :
    Function.Injective (extendRegionTupleLe (L := L) Ω h) := by
  intro f g hfg
  funext ⟨s, hsΛ⟩
  have hsΛ' : s ∈ Λ' := h hsΛ
  have heq := congrFun hfg ⟨s, hsΛ'⟩
  simpa [extendRegionTupleLe, hsΛ] using heq

/-- Compatibility of the two-stage extension: `Λ → Λ' → L` agrees with the
direct extension `Λ → L` from `LocalEmbed.lean`. -/
theorem extendRegionTuple_extendRegionTupleLe {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (f : regionIdx (L := L) Λ) :
    extendRegionTuple (Ω := Ω) Λ' (extendRegionTupleLe Ω h f)
      = extendRegionTuple (Ω := Ω) Λ f := by
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

variable (Ω)

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
        (EuclideanSpace.single (extendRegionTupleLe Ω h f) (1 : ℂ) :
          regionHilbert Λ'))
    (by
      change Orthonormal ℂ ⇑((EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).toBasis)
      rw [OrthonormalBasis.coe_toBasis]
      exact (EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).orthonormal)
    (by
      have hbasis := (EuclideanSpace.basisFun (regionIdx (L := L) Λ') ℂ).orthonormal
      have hext := hbasis.comp (extendRegionTupleLe (Ω := Ω) h)
        (extendRegionTupleLe_injective h)
      have hfun :
          (⇑((EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).toBasis.constr ℂ
                fun f : regionIdx (L := L) Λ =>
                  (EuclideanSpace.single (extendRegionTupleLe Ω h f) (1 : ℂ) :
                    regionHilbert Λ'))
              ∘ ⇑((EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).toBasis))
            = ((fun g : regionIdx (L := L) Λ' =>
                  (EuclideanSpace.basisFun (regionIdx (L := L) Λ') ℂ) g)
                ∘ extendRegionTupleLe (Ω := Ω) h) := by
        funext i
        simp [Function.comp_apply, EuclideanSpace.basisFun_apply]
      rw [hfun]
      exact hext)

@[simp]
theorem regionEmbedLe_apply_basis {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (f : regionIdx (L := L) Λ) :
    regionEmbedLe Ω h (EuclideanSpace.single f (1 : ℂ))
      = (EuclideanSpace.single (extendRegionTupleLe Ω h f) (1 : ℂ) :
          regionHilbert Λ') := by
  change ((EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).toBasis.constr ℂ
      fun f' : regionIdx (L := L) Λ =>
        (EuclideanSpace.single (extendRegionTupleLe Ω h f') (1 : ℂ) :
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
    regionEmbed Ω Λ' (regionEmbedLe Ω h ξ) = regionEmbed Ω Λ ξ := by
  -- Both sides are linear in ξ; check on the basis of regionHilbert Λ.
  have hbasis :
      ((regionEmbed Ω Λ').toLinearMap.comp (regionEmbedLe Ω h).toLinearMap)
        = (regionEmbed Ω Λ).toLinearMap := by
    refine ((EuclideanSpace.basisFun (regionIdx (L := L) Λ) ℂ).toBasis).ext ?_
    intro f
    simp [LinearMap.comp_apply, OrthonormalBasis.coe_toBasis,
          EuclideanSpace.basisFun_apply, extendRegionTuple_extendRegionTupleLe]
  exact LinearMap.congr_fun hbasis ξ

end LocalNetLike
