module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import QuantumSystem.Algebra.QuasiLocalAlgebra.Hilbert

/-!
# Basis-index decomposition for finite regions

For a pair of finite regions `Λ ⊆ Λ'`, the basis-index type `regionIdx Λ'`
decomposes as a product

`regionIdx Λ' ≃ regionIdx Λ × regionIdx (Λ' \ Λ)`,

reflecting the fact that an assignment of local-basis indices on `Λ'` is the
same data as a pair of assignments on `Λ` and on `Λ' \ Λ`.

This is the Type-level building block for the corresponding finite-region
Hilbert-space tensor decomposition
`regionHilbert Λ' ≃ regionHilbert Λ ⊗_ℂ regionHilbert (Λ' \ Λ)`,
which underlies the construction of "operator `M ⊗ 1_{Λ' \ Λ}`" actions
needed for an operator-algebra action on the incomplete-tensor-product
sectors at arbitrary unit-vector reference families.

## Main definitions

* `LocalNetLike.regionIdxSplit h` — split a region tuple over `Λ'` into its
  `Λ`-part and `Λ' \ Λ`-part.
* `LocalNetLike.regionIdxCombine h` — recombine a pair of `Λ` and `Λ' \ Λ`
  tuples into a `Λ'` tuple.
* `LocalNetLike.regionIdxEquiv h` — the resulting `Equiv`.
-/

@[expose] public section

namespace LocalNetLike

variable {L : Type*} [DecidableEq L] [LocalNetLike L]

/-- Forward direction of the basis-index decomposition: split a tuple on
`Λ'` into its `Λ`-part and `Λ' \ Λ`-part. -/
def regionIdxSplit {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (f : regionIdx (L := L) Λ') :
    regionIdx (L := L) Λ × regionIdx (L := L) (Λ' \ Λ) :=
  (fun s : Λ => f ⟨s.1, h s.2⟩,
   fun s : (Λ' \ Λ : Finset L) => f ⟨s.1, (Finset.mem_sdiff.mp s.2).1⟩)

/-- Inverse direction: combine a pair of `Λ` and `Λ' \ Λ` tuples into a
single `Λ'` tuple. -/
noncomputable def regionIdxCombine {Λ Λ' : Finset L} (_h : Λ ⊆ Λ')
    (g : regionIdx (L := L) Λ) (g' : regionIdx (L := L) (Λ' \ Λ)) :
    regionIdx (L := L) Λ' :=
  fun s : Λ' =>
    if hs : s.1 ∈ Λ then g ⟨s.1, hs⟩
    else g' ⟨s.1, Finset.mem_sdiff.mpr ⟨s.2, hs⟩⟩

@[simp]
theorem regionIdxCombine_of_mem {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (g : regionIdx (L := L) Λ) (g' : regionIdx (L := L) (Λ' \ Λ))
    {s : Λ'} (hs : s.1 ∈ Λ) :
    regionIdxCombine h g g' s = g ⟨s.1, hs⟩ :=
  dif_pos hs

@[simp]
theorem regionIdxCombine_of_not_mem {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (g : regionIdx (L := L) Λ) (g' : regionIdx (L := L) (Λ' \ Λ))
    {s : Λ'} (hs : s.1 ∉ Λ) :
    regionIdxCombine h g g' s
      = g' ⟨s.1, Finset.mem_sdiff.mpr ⟨s.2, hs⟩⟩ :=
  dif_neg hs

/-- The basis-index decomposition is an equivalence of types. -/
noncomputable def regionIdxEquiv {Λ Λ' : Finset L} (h : Λ ⊆ Λ') :
    regionIdx (L := L) Λ' ≃ (regionIdx (L := L) Λ × regionIdx (L := L) (Λ' \ Λ)) where
  toFun := regionIdxSplit h
  invFun p := regionIdxCombine h p.1 p.2
  left_inv f := by
    funext s
    change regionIdxCombine h (regionIdxSplit h f).1 (regionIdxSplit h f).2 s = f s
    by_cases hs : s.1 ∈ Λ
    · rw [regionIdxCombine_of_mem h _ _ hs]
      rfl
    · rw [regionIdxCombine_of_not_mem h _ _ hs]
      rfl
  right_inv p := by
    obtain ⟨g, g'⟩ := p
    ext s
    · change regionIdxCombine h g g' ⟨s.1, h s.2⟩ = g s
      rw [regionIdxCombine_of_mem h _ _ s.2]
    · change regionIdxCombine h g g' ⟨s.1, (Finset.mem_sdiff.mp s.2).1⟩ = g' s
      rw [regionIdxCombine_of_not_mem h _ _ (Finset.mem_sdiff.mp s.2).2]

@[simp]
theorem regionIdxEquiv_apply {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (f : regionIdx (L := L) Λ') :
    regionIdxEquiv h f = regionIdxSplit h f := rfl

@[simp]
theorem regionIdxEquiv_symm_apply {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (p : regionIdx (L := L) Λ × regionIdx (L := L) (Λ' \ Λ)) :
    (regionIdxEquiv h).symm p = regionIdxCombine h p.1 p.2 := rfl

/-! ### Hilbert-space relabelling -/

/-- The corresponding `regionHilbert` relabelling: lifting the basis-index
decomposition `regionIdx Λ' ≃ regionIdx Λ × regionIdx (Λ' \ Λ)` to a linear
isometric equivalence of Hilbert spaces

`regionHilbert Λ' ≃ₗᵢ[ℂ] EuclideanSpace ℂ (regionIdx Λ × regionIdx (Λ' \ Λ))`.

This is the basis-relabelled form of the tensor decomposition
`regionHilbert Λ' ≃ₗᵢ[ℂ] regionHilbert Λ ⊗_ℂ regionHilbert (Λ' \ Λ)`
under `EuclideanSpace ℂ ι × EuclideanSpace ℂ κ ≃ EuclideanSpace ℂ (ι × κ)`. -/
noncomputable def regionHilbertSplitEquiv {Λ Λ' : Finset L} (h : Λ ⊆ Λ') :
    regionHilbert (L := L) Λ'
      ≃ₗᵢ[ℂ] EuclideanSpace ℂ
          (regionIdx (L := L) Λ × regionIdx (L := L) (Λ' \ Λ)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (regionIdxEquiv h)

end LocalNetLike
