module

public import QuantumSystem.Algebra.QuasiLocalAlgebra.RegionDirected

/-!
# Density and Hilbert co-limit (Phase 2-b)

We show that the union of `regionEmbed Λ`-images is dense in
`globalHilbert L`, exhibiting `globalHilbert L` as the Hilbert
co-limit of the directed system of finite-region Hilbert spaces.

Concretely, every basis vector `lp.single 2 g 1` of `globalHilbert L` lies
in `regionEmbed Λ` for any finite region `Λ` containing the support of
`g : globalIdx L`.  Combined with `regionEmbedLe` and `regionEmbed`'s
co-cone compatibility from `RegionDirected.lean`, the union of images is
closed under the linear operations and contains the spanning set
`{lp.single 2 g 1 : g : globalIdx L}` of the basis-Hilbert structure on
`globalHilbert L`.  Density follows from `HilbertBasis.dense_span`.

## Main definitions

* (none new — see `RegionEmbed.lean` and `RegionDirected.lean`)

## Main results

* `LocalNetLike.extendRegionTuple_regionRestrict_of_complement` — every
  global tuple factors as `extendRegionTuple Λ (regionRestrict Λ g)` for
  any `Λ` containing its non-reference support.
* `LocalNetLike.lpSingle_mem_regionEmbed_range` — every basis vector
  `lp.single 2 g 1` is in the image of `regionEmbed Λ` for some `Λ`.
* `LocalNetLike.dense_iUnion_regionEmbed_range` — the union of
  `regionEmbed Λ`-images is dense in `globalHilbert L`.

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

/-! ### Factoring `globalIdx` tuples through `extendRegionTuple` -/

/-- Every global tuple `g` agreeing with `referenceBasis L` outside `Λ`
factors as `extendRegionTuple Λ (regionRestrict Λ g)`. -/
theorem extendRegionTuple_regionRestrict_of_complement {Λ : Finset L}
    (g : globalIdx L) (h : ∀ s ∉ Λ, g.val s = referenceBasis L s) :
    extendRegionTuple Λ (regionRestrict Λ g) = g := by
  apply Subtype.ext
  funext s
  by_cases hsΛ : s ∈ Λ
  · rw [extendRegionTuple_val_apply_of_mem _ _ hsΛ, regionRestrict_apply]
  · rw [extendRegionTuple_val_apply_of_not_mem _ _ hsΛ, h s hsΛ]

/-- Every global basis vector `lp.single 2 g 1` lies in the image of
`regionEmbed Λ` for some finite region `Λ`. -/
theorem lpSingle_mem_regionEmbed_range (g : globalIdx L) :
    ∃ Λ : Finset L, ∃ ξ : regionHilbert Λ,
      regionEmbed Λ ξ = (lp.single 2 g (1 : ℂ) : globalHilbert L) := by
  obtain ⟨Λ, hΛ⟩ := g.property
  refine ⟨Λ, EuclideanSpace.single (regionRestrict Λ g) (1 : ℂ), ?_⟩
  rw [regionEmbed_apply_basis,
      extendRegionTuple_regionRestrict_of_complement g hΛ]

/-! ### Density of the union of region embeddings -/

/-- The union of `regionEmbed Λ`-images is dense in `globalHilbert L`. -/
theorem dense_iUnion_regionEmbed_range :
    Dense (⋃ Λ : Finset L, Set.range (⇑(regionEmbed (L := L) Λ))) := by
  -- Build the standard HilbertBasis on `globalHilbert L`.
  let b : HilbertBasis (globalIdx L) ℂ (globalHilbert L) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ (globalHilbert L))
  have hb_apply : ∀ g : globalIdx L,
      b g = (lp.single 2 g (1 : ℂ) : globalHilbert L) := by
    intro g
    change (LinearIsometryEquiv.refl ℂ (globalHilbert L)).symm
        (lp.single 2 g (1 : ℂ) : globalHilbert L) = _
    rfl
  -- The span of the HilbertBasis is dense; reduce to showing
  -- `span ℂ (Set.range b) ⊆ ⋃_Λ Set.range (regionEmbed Λ)` as sets.
  have hbasis_dense : Dense
      (↑(Submodule.span ℂ (Set.range (⇑b))) : Set (globalHilbert L)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span
  refine Dense.mono ?_ hbasis_dense
  -- Show every element of the span lies in some `regionEmbed Λ`-image.
  intro x hx
  -- `hx : x ∈ Submodule.span ℂ (Set.range b)`, induct.
  refine Submodule.span_induction
      (p := fun y _ => y ∈ ⋃ Λ : Finset L, Set.range (⇑(regionEmbed (L := L) Λ)))
      ?mem ?zero ?add ?smul hx
  case mem =>
    intro y hy
    obtain ⟨g, rfl⟩ := hy
    rw [hb_apply g]
    obtain ⟨Λ, ξ, hξ⟩ := lpSingle_mem_regionEmbed_range g
    exact Set.mem_iUnion.mpr ⟨Λ, ξ, hξ⟩
  case zero =>
    refine Set.mem_iUnion.mpr ⟨∅, 0, ?_⟩
    exact map_zero (regionEmbed (L := L) ∅)
  case add =>
    intro y z _ _ hy hz
    obtain ⟨Λy, ξy, hξy⟩ := Set.mem_iUnion.mp hy
    obtain ⟨Λz, ξz, hξz⟩ := Set.mem_iUnion.mp hz
    refine Set.mem_iUnion.mpr ⟨Λy ∪ Λz,
      regionEmbedLe Finset.subset_union_left ξy
        + regionEmbedLe Finset.subset_union_right ξz, ?_⟩
    rw [map_add, regionEmbed_apply_regionEmbedLe,
        regionEmbed_apply_regionEmbedLe, hξy, hξz]
  case smul =>
    intro c y _ hy
    obtain ⟨Λ, ξ, hξ⟩ := Set.mem_iUnion.mp hy
    refine Set.mem_iUnion.mpr ⟨Λ, c • ξ, ?_⟩
    rw [map_smul, hξ]

end LocalNetLike
