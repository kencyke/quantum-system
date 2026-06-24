module

public import QuantumSystem.Analysis.Entropy.KroneckerProduct
public import QuantumSystem.Analysis.Matrix.PartialTrace

/-!
# LocalNet bridge: restriction as an equivalence-indexed partial trace

These lemmas identify the `LocalNet` restriction `Matrix.restrict` with the equivalence-indexed
partial trace `Matrix.partialTrace` of the reindexed matrix induced by `LocalNet.combineIdx`.
They are factored out of `Analysis/Entropy/KroneckerProduct.lean` so that the Kronecker-product
and product-type partial-trace API there stays `LocalNet`-free.
-/

@[expose] public section

namespace Matrix

open scoped Kronecker MatrixOrder ComplexOrder

/-! ### LocalNet bridge

These lemmas identify `Matrix.restrict` on a `LocalNet` with the equivalence-indexed
partial trace of the reindexed matrix induced by `LocalNet.combineIdx`. -/

section LocalNetBridge

variable {L : LocalNet}

/-- Combining via `h : Λ ⊆ Λ_total` agrees with combining via the complementary split,
after transporting the remaining factor along `Λ_total \ (Λ_total \ Λ) = Λ`. -/
private lemma combineIdx_swap_apply
    {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    (x : L.regionIdx Λ) (y : L.regionIdx (Λ_total \ Λ)) :
    L.combineIdx h (x, y) =
      L.combineIdx Finset.sdiff_subset
        (y, L.regionIdxCongr (sdiff_sdiff_eq_self h).symm x) := by
  have h_eq : Λ_total \ (Λ_total \ Λ) = Λ := sdiff_sdiff_eq_self h
  funext ⟨s, hs⟩
  by_cases hsΛ : s ∈ Λ
  · have hns_compl : s ∉ Λ_total \ Λ := fun h_in => (Finset.mem_sdiff.mp h_in).2 hsΛ
    have hs_recast : s ∈ Λ_total \ (Λ_total \ Λ) := by
      rw [h_eq]
      exact hsΛ
    rw [LocalNet.combineIdx_apply_mem h _ _ ⟨s, hs⟩ hsΛ,
        LocalNet.combineIdx_apply_not_mem Finset.sdiff_subset _ _ ⟨s, hs⟩ hns_compl,
      LocalNet.regionIdxCongr_apply (L := L) h_eq.symm x hsΛ hs_recast]
  · have hs_compl : s ∈ Λ_total \ Λ := Finset.mem_sdiff.mpr ⟨hs, hsΛ⟩
    rw [LocalNet.combineIdx_apply_not_mem h _ _ ⟨s, hs⟩ hsΛ,
        LocalNet.combineIdx_apply_mem Finset.sdiff_subset _ _ ⟨s, hs⟩ hs_compl]

/-- Restriction to `Λ` equals the partial trace of the reindexed matrix induced by
`combineIdx h`, retaining the `Λ` factor. -/
theorem restrict_eq_partialTrace_combineIdx
    {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    (ρ : L.localAlgebra Λ_total) (x x' : L.regionIdx Λ) :
    Matrix.restrict h ρ x x' =
      Matrix.partialTrace
        (A := L.regionIdx Λ) (B := L.regionIdx (Λ_total \ Λ))
        (Equiv.refl (L.regionIdx Λ × L.regionIdx (Λ_total \ Λ)))
        (ρ.submatrix (L.combineIdx h) (L.combineIdx h)) x x' := by
  rw [Matrix.partialTrace_refl_apply, Matrix.restrict_apply]
  simp [Matrix.submatrix_apply]

/-- Restriction to the complement of `Λ` equals the partial trace of the reindexed matrix
induced by `combineIdx h`, retaining the complementary factor. -/
theorem restrict_compl_eq_partialTrace_combineIdx
    {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    (ρ : L.localAlgebra Λ_total) (y y' : L.regionIdx (Λ_total \ Λ)) :
    Matrix.restrict Finset.sdiff_subset ρ y y' =
      Matrix.partialTrace
        (A := L.regionIdx (Λ_total \ Λ)) (B := L.regionIdx Λ)
        (Equiv.prodComm (L.regionIdx Λ) (L.regionIdx (Λ_total \ Λ)))
        (ρ.submatrix (L.combineIdx h) (L.combineIdx h)) y y' := by
  rw [Matrix.partialTrace_prodComm_apply, Matrix.restrict_apply]
  rw [← (L.regionIdxCongr (sdiff_sdiff_eq_self h).symm).sum_comp
        (fun z => ρ (L.combineIdx Finset.sdiff_subset (y, z))
          (L.combineIdx Finset.sdiff_subset (y', z)))]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.submatrix_apply, combineIdx_swap_apply h x y, combineIdx_swap_apply h x y']

end LocalNetBridge

end Matrix
