module

public import QuantumSystem.Analysis.Entropy.KroneckerProduct
public import QuantumSystem.Analysis.Entropy.RelativeEntropy
public import QuantumSystem.Analysis.Entropy.Regularize
public import QuantumSystem.Analysis.Matrix.PartialTrace

/-!
# Strong subadditivity of the von Neumann entropy (LocalNet form)

For a quantum system on a `LocalNet L`, the public theorem in this file is stated
in a **common-region-explicit** form. Given regions

- `ΛAB ⊆ ΛABC`,
- `ΛBC ⊆ ΛABC`,
- `ΛB ⊆ ΛABC`,
- `ΛA ⊆ ΛAB`,
- `ΛAB \ ΛA = ΛB`,
- `ΛABC \ ΛA = ΛBC`,

the **strong subadditivity** inequality states:

  `S(ρ ↾ ΛAB) + S(ρ ↾ ΛBC) ≥ S(ρ) + S(ρ ↾ ΛB)`

This avoids encoding the theorem through positional subsystem names such as
`A/B/C` or a distinguished three-site tuple. The familiar three-site statement

  `S(ρ ↾ {a, b}) + S(ρ ↾ {b, c}) ≥ S(ρ) + S(ρ ↾ {b})`

is recovered by instantiating

- `ΛABC = {a, b, c}`,
- `ΛAB = {a, b}`,
- `ΛBC = {b, c}`,
- `ΛB = {b}`,
- `ΛA = {a}`.

This file first establishes the **mutual-information identity** in product-type form,

  `D(ρ_AB ‖ ρ_A ⊗ ρ_B) = -S(ρ_AB) + S(ρ_A) + S(ρ_B)`,

for a PosDef bipartite density matrix `ρ_AB : DensityMatrix (n × m)` whose canonical
partial traces coincide with PosDef factor states `ρ_A` and `ρ_B`. It then uses this
identity together with the data-processing inequality to prove SSA in the
AQFT-natural form:

1. The bipartite **mutual-information identity** (`relativeEntropy_kronecker_marginals_product`)
  applied twice — once for the `(ΛA vs ΛABC \ ΛA)` bipartition of the full system,
  once for the `(ΛA vs ΛAB \ ΛA)` bipartition of the `ΛAB`-marginal.
2. The **data-processing inequality** for relative entropy
   (`Matrix.relativeEntropy_channel_le`) applied to the LocalNet
  `Matrix.QuantumChannel.restrict` channel for the inclusion `ΛAB ⊆ ΛABC`.

## Main results

* `Matrix.relativeEntropy_kronecker_marginals_product` — product-type mutual-information
  identity.
* `DensityMatrix.vonNeumannEntropy_SSA` — SSA for arbitrary states on a
  `LocalNet`, with the common region and split equalities explicit.

## References

* Nielsen, Chuang, *Quantum Computation and Quantum Information* §11.3 — quantum mutual
  information `I(A:B) = S(ρ_A) + S(ρ_B) − S(ρ_AB)` and the relative-entropy identity
  `D(ρ_AB ‖ ρ_A ⊗ ρ_B) = I(A:B)`.
-/

@[expose] public section

namespace Matrix

open scoped Kronecker MatrixOrder ComplexOrder QuantumInfo

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-! ### Product-type relative-entropy identity -/

/-- **Mutual-information identity (product-type form)**: for a bipartite density
matrix `ρ_AB : DensityMatrix (n × m)` whose canonical partial traces coincide with PosDef
factor states `ρ_A` and `ρ_B`, the relative entropy w.r.t. the product `ρ_A ⊗ ρ_B`
equals `-S(ρ_AB) + S(ρ_A) + S(ρ_B)`. -/
theorem relativeEntropy_kronecker_marginals_product
    (ρ_AB : DensityMatrix (n × m))
    (ρ_A : DensityMatrix n) (hρ_A : ρ_A.toMatrix.PosDef)
    (ρ_B : DensityMatrix m) (hρ_B : ρ_B.toMatrix.PosDef)
    (h_A_partialTrace : tr₂(ρ_AB.toMatrix) = ρ_A.toMatrix)
    (h_B_partialTrace : tr₁(ρ_AB.toMatrix) = ρ_B.toMatrix) :
    D(ρ_AB ∥ ρ_A ⊗ ρ_B) = -S(ρ_AB) + S(ρ_A) + S(ρ_B) := by
  classical
  have hρ_A_kron_pos : (ρ_A ⊗ ρ_B).toMatrix.PosDef := by
    rw [DensityMatrix.kronecker_toMatrix]; exact hρ_A.kronecker hρ_B
  -- supp(ρ) ⊆ supp(ρ_A ⊗ ρ_B) holds for PosDef σ.
  have h_supp : suppSubset ρ_AB.toMatrix (ρ_A ⊗ ρ_B).toMatrix := by
    intro v hv
    have hinj : Function.Injective (ρ_A ⊗ ρ_B).toMatrix.mulVec :=
      Matrix.mulVec_injective_iff_isUnit.mpr hρ_A_kron_pos.isUnit
    have h0 : (ρ_A ⊗ ρ_B).toMatrix.mulVec 0 = 0 := by simp
    have hv_zero : v = 0 := hinj (hv.trans h0.symm)
    rw [hv_zero]; simp
  unfold relativeEntropy
  simp only [h_supp, if_true]
  -- log of ρ_A ⊗ ρ_B decomposes via matrixLog_kronecker_posDef.
  -- The two `IsHermitian` proofs differ proof-wise but match by Prop irrelevance.
  have h_log_kron : matrixLog (ρ_A ⊗ ρ_B).toMatrix (ρ_A ⊗ ρ_B).isHermitian =
      matrixLog ρ_A.toMatrix hρ_A.1 ⊗ₖ (1 : Matrix m m ℂ) +
        (1 : Matrix n n ℂ) ⊗ₖ matrixLog ρ_B.toMatrix hρ_B.1 :=
    matrixLog_kronecker_posDef hρ_A hρ_B
  -- The trace identity after substitution.
  have h_trace_log_kron :
      Tr (ρ_AB.toMatrix * matrixLog (ρ_A ⊗ ρ_B).toMatrix (ρ_A ⊗ ρ_B).isHermitian) =
        Tr (ρ_A.toMatrix * matrixLog ρ_A.toMatrix hρ_A.1) +
        Tr (ρ_B.toMatrix * matrixLog ρ_B.toMatrix hρ_B.1) := by
    rw [h_log_kron, Matrix.mul_add, Matrix.trace_add, trace_mul_kronecker_one_right,
      trace_mul_kronecker_one_left, h_A_partialTrace, h_B_partialTrace]
  -- Split (log ρ - log(ρ_A⊗ρ_B)) and reduce trace.
  have h_split : Tr (ρ_AB.toMatrix * (matrixLog ρ_AB.toMatrix ρ_AB.isHermitian -
        matrixLog (ρ_A ⊗ ρ_B).toMatrix (ρ_A ⊗ ρ_B).isHermitian)) =
      Tr (ρ_AB.toMatrix * matrixLog ρ_AB.toMatrix ρ_AB.isHermitian) -
        Tr (ρ_AB.toMatrix * matrixLog (ρ_A ⊗ ρ_B).toMatrix (ρ_A ⊗ ρ_B).isHermitian) := by
    rw [Matrix.mul_sub, Matrix.trace_sub]
  -- Translate to the goal in EReal.
  change (↑(Tr (ρ_AB.toMatrix * (matrixLog ρ_AB.toMatrix ρ_AB.isHermitian -
        matrixLog (ρ_A ⊗ ρ_B).toMatrix (ρ_A ⊗ ρ_B).isHermitian))).re : EReal) =
      -S(ρ_AB) + S(ρ_A) + S(ρ_B)
  rw [h_split, Complex.sub_re, h_trace_log_kron, Complex.add_re]
  -- Now: ↑((Tr(ρ · log ρ)).re - ((Tr(ρ_A · log ρ_A)).re + (Tr(ρ_B · log ρ_B)).re))
  --      = -S(ρ) + S(ρ_A) + S(ρ_B)
  -- Express the LHS Real value:
  set α : ℝ := (Tr (ρ_AB.toMatrix * matrixLog ρ_AB.toMatrix ρ_AB.isHermitian)).re with hα
  set β : ℝ := (Tr (ρ_A.toMatrix * matrixLog ρ_A.toMatrix hρ_A.1)).re with hβ
  set γ : ℝ := (Tr (ρ_B.toMatrix * matrixLog ρ_B.toMatrix hρ_B.1)).re with hγ
  -- And the S values:
  change (↑(α - (β + γ)) : EReal) = -S(ρ_AB) + S(ρ_A) + S(ρ_B)
  have hSρ : S(ρ_AB) = -α := by
    change -(Tr (ρ_AB.toMatrix * DensityMatrix.log ρ_AB)).re = -α
    rfl
  have hSρ_A : S(ρ_A) = -β := by
    change -(Tr (ρ_A.toMatrix * DensityMatrix.log ρ_A)).re = -β
    rfl
  have hSρ_B : S(ρ_B) = -γ := by
    change -(Tr (ρ_B.toMatrix * DensityMatrix.log ρ_B)).re = -γ
    rfl
  rw [hSρ, hSρ_A, hSρ_B]
  -- Goal in EReal: ↑(α - (β + γ)) = -↑(-α) + ↑(-β) + ↑(-γ)
  -- Equivalent Real identity:
  have h_real : α - (β + γ) = -(-α) + (-β) + (-γ) := by ring
  exact_mod_cast h_real

end Matrix

/-! ### Strong subadditivity (LocalNet form, PosDef case)

The main theorem. We use the bipartite mutual-information identity twice
(for `(A vs BC)` and for `(A vs B)` within `ρ ↾ {A, B}`) and the data-processing
inequality on the LocalNet `restrict` channel for `{A, B} ⊆ univ`. -/

namespace DensityMatrix

open scoped Kronecker MatrixOrder ComplexOrder
open scoped Matrix.QuantumInfo
open scoped LocalNet.QuantumInfo

variable {L : LocalNet}

/-! #### Split-explicit nested-region SSA

The next theorem is the region-level core of the three-site wrapper below. It is
parameterised by nested inclusions `ΛA ⊆ ΛAB ⊆ ΛABC`; the common/middle region is the
explicit complement `ΛAB \ ΛA`, and the other side is `ΛABC \ ΛA`.
-/

/-- **Strong subadditivity (PosDef case, split-explicit nested-region form).**

Given nested regions `ΛA ⊆ ΛAB ⊆ ΛABC`, write the middle/common region as
`ΛAB \ ΛA` and the complementary side as `ΛABC \ ΛA`. For a PosDef state `ρ_ABC` on
`ΛABC`, assuming the relevant marginals are PosDef, strong subadditivity is

`S(ρ_ABC ↾ ΛAB) + S(ρ_ABC ↾ (ΛABC \ ΛA)) ≥ S(ρ_ABC) + S(ρ_ABC ↾ (ΛAB \ ΛA))`.

This statement contains the split subset in the hypotheses and does not rely on
site names such as `a b c` or product-factor names such as `A/B`. -/
private lemma vonNeumannEntropy_SSA_posDef_nested
    {L : LocalNet} {ΛA ΛAB ΛABC : Finset L.sites}
    (h_AB : ΛAB ⊆ ΛABC) (h_A : ΛA ⊆ ΛAB)
    (ρ_ABC : L.densityMatrix ΛABC)
    (h_ABC_pos : ρ_ABC.toMatrix.PosDef)
    (h_A_pos : (ρ_ABC ↾[h_A.trans h_AB]).toMatrix.PosDef)
    (h_AB_pos : (ρ_ABC ↾[h_AB]).toMatrix.PosDef)
    (h_BC_pos : (ρ_ABC ↾[(Finset.sdiff_subset : ΛABC \ ΛA ⊆ ΛABC)]).toMatrix.PosDef)
    (h_B_pos : (ρ_ABC ↾[(Finset.sdiff_subset_sdiff h_AB (le_refl ΛA)).trans Finset.sdiff_subset]).toMatrix.PosDef) :
    S(ρ_ABC ↾ ΛAB) +
        S(ρ_ABC ↾[(Finset.sdiff_subset : ΛABC \ ΛA ⊆ ΛABC)]) ≥
      S(ρ_ABC) +
        S(ρ_ABC ↾[(Finset.sdiff_subset_sdiff h_AB (le_refl ΛA)).trans Finset.sdiff_subset]) := by
  classical
  set h_B_in_BC : (ΛAB \ ΛA) ⊆ (ΛABC \ ΛA) :=
    Finset.sdiff_subset_sdiff h_AB (le_refl ΛA) with hh_B_in_BC
  set ρ_A : DensityMatrix (L.regionIdx ΛA) :=
    ρ_ABC ↾[h_A.trans h_AB] with hh_ρ_A
  set ρ_AB : DensityMatrix (L.regionIdx ΛAB) :=
    ρ_ABC ↾[h_AB] with hh_ρ_AB
  set ρ_BC : DensityMatrix (L.regionIdx (ΛABC \ ΛA)) :=
    ρ_ABC ↾[(Finset.sdiff_subset : ΛABC \ ΛA ⊆ ΛABC)] with hh_ρ_BC
  set ρ_B : DensityMatrix (L.regionIdx (ΛAB \ ΛA)) :=
    ρ_ABC ↾[h_B_in_BC.trans Finset.sdiff_subset] with hh_ρ_B
  have hρ_A : ρ_A.toMatrix.PosDef := h_A_pos
  have hρ_AB : ρ_AB.toMatrix.PosDef := h_AB_pos
  have hρ_BC : ρ_BC.toMatrix.PosDef := h_BC_pos
  have hρ_B : ρ_B.toMatrix.PosDef := h_B_pos
  -- Bipartite views of `ρ` and `ρ_AB` via the explicit split subset.
  set ρ_pt : DensityMatrix (L.regionIdx ΛA × L.regionIdx (ΛABC \ ΛA)) :=
    ρ_ABC.mapEquiv (L.combineIdx (h_A.trans h_AB)) with hρ_pt_def
  have hρ_pt : ρ_pt.toMatrix.PosDef := h_ABC_pos.mapEquiv _
  set ρ_AB_pt : DensityMatrix (L.regionIdx ΛA × L.regionIdx (ΛAB \ ΛA)) :=
    ρ_AB.mapEquiv (L.combineIdx h_A) with hρ_AB_pt_def
  have hρ_AB_pt : ρ_AB_pt.toMatrix.PosDef := hρ_AB.mapEquiv _
  have hρ_pt_sub : ρ_pt.toMatrix =
      ρ_ABC.toMatrix.submatrix (L.combineIdx (h_A.trans h_AB))
        (L.combineIdx (h_A.trans h_AB)) := by
    simp [hρ_pt_def, DensityMatrix.mapEquiv_toMatrix]
  have hρ_AB_pt_sub : ρ_AB_pt.toMatrix =
      ρ_AB.toMatrix.submatrix (L.combineIdx h_A) (L.combineIdx h_A) := by
    simp [hρ_AB_pt_def, DensityMatrix.mapEquiv_toMatrix]
  -- Product reference state for the full split and its lift back to `ΛABC`.
  set σ_pt : DensityMatrix (L.regionIdx ΛA × L.regionIdx (ΛABC \ ΛA)) :=
    ρ_A ⊗ ρ_BC with hσ_pt_def
  have hσ_pt : σ_pt.toMatrix.PosDef := by
    rw [hσ_pt_def, DensityMatrix.kronecker_toMatrix]
    exact hρ_A.kronecker hρ_BC
  set σ_full : L.densityMatrix ΛABC :=
    σ_pt.mapEquiv (L.combineIdx (h_A.trans h_AB)).symm with hσ_full_def
  have hσ_full : σ_full.toMatrix.PosDef := hσ_pt.mapEquiv _
  -- Mutual-information identity for the full split.
  have h_ptA_ρ_pt : tr₂(ρ_pt.toMatrix) = ρ_A.toMatrix := by
    ext x x'
    rw [hρ_pt_sub, ← Matrix.restrict_eq_partialTrace_combineIdx]
    rfl
  have h_ptBC_ρ_pt : tr₁(ρ_pt.toMatrix) = ρ_BC.toMatrix := by
    ext y y'
    rw [hρ_pt_sub, ← Matrix.restrict_compl_eq_partialTrace_combineIdx
      (h_A.trans h_AB)]
    rfl
  have h_mut_full :
      D(ρ_pt ∥ σ_pt) = -S(ρ_pt) + S(ρ_A) + S(ρ_BC) :=
    Matrix.relativeEntropy_kronecker_marginals_product ρ_pt ρ_A hρ_A ρ_BC hρ_BC
      h_ptA_ρ_pt h_ptBC_ρ_pt
  -- Mutual-information identity for the `ΛA ⊆ ΛAB` split.
  have h_ptA_AB : tr₂(ρ_AB_pt.toMatrix) = ρ_A.toMatrix := by
    ext x x'
    rw [hρ_AB_pt_sub, ← Matrix.restrict_eq_partialTrace_combineIdx]
    change ((ρ_ABC ↾[h_AB]) ↾[h_A]).toMatrix x x' =
      (ρ_ABC ↾[h_A.trans h_AB]).toMatrix x x'
    rw [DensityMatrix.restrict_restrict]
  have h_ptB_AB : tr₁(ρ_AB_pt.toMatrix) = ρ_B.toMatrix := by
    ext y y'
    rw [hρ_AB_pt_sub, ← Matrix.restrict_compl_eq_partialTrace_combineIdx h_A]
    change ((ρ_ABC ↾[h_AB]) ↾[(Finset.sdiff_subset :
        ΛAB \ ΛA ⊆ ΛAB)]).toMatrix y y' =
      (ρ_ABC ↾[h_B_in_BC.trans Finset.sdiff_subset]).toMatrix y y'
    rw [DensityMatrix.restrict_restrict]
  have h_mut_AB :
      D(ρ_AB_pt ∥ ρ_A ⊗ ρ_B) = -S(ρ_AB_pt) + S(ρ_A) + S(ρ_B) :=
    Matrix.relativeEntropy_kronecker_marginals_product ρ_AB_pt ρ_A hρ_A ρ_B hρ_B
      h_ptA_AB h_ptB_AB
  -- DPI for restriction from `ΛABC` to `ΛAB`.
  set Φ : Matrix.QuantumChannel (L.regionIdx ΛABC) (L.regionIdx ΛAB) :=
    Matrix.QuantumChannel.restrict h_AB with hΦ_def
  have h_Φρ_mat : ((Φ : Matrix.QuantumChannel _ _) ρ_ABC).toMatrix = ρ_AB.toMatrix := by
    change (ρ_ABC ↾[h_AB]).toMatrix = ρ_AB.toMatrix
    rfl
  have h_Φρ_pos : ((Φ : Matrix.QuantumChannel _ _) ρ_ABC).toMatrix.PosDef := h_Φρ_mat ▸ hρ_AB
  -- Restricting the lifted product state gives the product of the restricted factors.
  have h_Φσ_mat :
      ((Φ : Matrix.QuantumChannel _ _) σ_full).toMatrix =
        (ρ_A ⊗ ρ_B).toMatrix.submatrix
          (L.combineIdx h_A).symm (L.combineIdx h_A).symm := by
    change Matrix.restrict h_AB σ_full.toMatrix = _
    ext s s'
    rw [show s = (L.combineIdx h_A)
            ((L.combineIdx h_A).symm s) from
          ((L.combineIdx h_A).apply_symm_apply s).symm,
        show s' = (L.combineIdx h_A)
            ((L.combineIdx h_A).symm s') from
          ((L.combineIdx h_A).apply_symm_apply s').symm]
    set p := (L.combineIdx h_A).symm s with hp
    set p' := (L.combineIdx h_A).symm s' with hp'
    rw [Matrix.restrict_apply, Matrix.submatrix_apply]
    simp only [Equiv.symm_apply_apply]
    simp_rw [Matrix.combineIdx_assoc_eq h_AB h_A]
    have h_σ_full_apply : ∀ (x x' : L.regionIdx ΛA)
        (y y' : L.regionIdx (ΛABC \ ΛA)),
        σ_full.toMatrix
            (L.combineIdx (h_A.trans h_AB) (x, y))
            (L.combineIdx (h_A.trans h_AB) (x', y')) =
          σ_pt.toMatrix (x, y) (x', y') := by
      intro x x' y y'
      simp [hσ_full_def, DensityMatrix.mapEquiv_toMatrix,
            Matrix.submatrix_apply, Equiv.symm_apply_apply]
    simp_rw [h_σ_full_apply]
    rw [hσ_pt_def, DensityMatrix.kronecker_toMatrix]
    simp only [Matrix.kronecker_apply]
    rw [← Finset.mul_sum]
    rw [DensityMatrix.kronecker_toMatrix, Matrix.kronecker_apply]
    congr 1
    rw [show ρ_B.toMatrix p.2 p'.2 = Matrix.restrict h_B_in_BC ρ_BC.toMatrix p.2 p'.2
        from by
          change Matrix.restrict (h_B_in_BC.trans Finset.sdiff_subset) ρ_ABC.toMatrix p.2 p'.2 =
            Matrix.restrict h_B_in_BC (Matrix.restrict Finset.sdiff_subset ρ_ABC.toMatrix) p.2 p'.2
          rw [Matrix.restrict_restrict],
        Matrix.restrict_eq_partialTrace_combineIdx h_B_in_BC,
        Matrix.partialTrace_refl_apply]
    have h_compl_eq : (ΛABC \ ΛA) \ (ΛAB \ ΛA) = ΛABC \ ΛAB := by
      ext x
      simp only [Finset.mem_sdiff]
      constructor
      · rintro ⟨⟨hxABC, hxA⟩, hx_not_BminusA⟩
        exact ⟨hxABC, fun hxAB => hx_not_BminusA ⟨hxAB, hxA⟩⟩
      · rintro ⟨hxABC, hxAB⟩
        exact ⟨⟨hxABC, fun hxA => hxAB (h_A hxA)⟩,
          fun hxBminusA => hxAB hxBminusA.1⟩
    rw [← (L.regionIdxCongr h_compl_eq.symm).sum_comp
        (fun b => ρ_BC.toMatrix.submatrix (L.combineIdx h_B_in_BC) (L.combineIdx h_B_in_BC)
          (p.2, b) (p'.2, b))]
    refine Finset.sum_congr rfl fun γ _ => ?_
    have hR_eq : ∀ (z : L.regionIdx (ΛAB \ ΛA)),
        Matrix.restrictAssocEquiv h_AB h_A (z, γ) =
          L.combineIdx h_B_in_BC (z, L.regionIdxCongr h_compl_eq.symm γ) := by
      intro z
      funext ⟨v, hv⟩
      by_cases hv_in_AB : v ∈ ΛAB
      · have hv_in_combine : v ∈ ΛAB \ ΛA :=
          Finset.mem_sdiff.mpr ⟨hv_in_AB, (Finset.mem_sdiff.mp hv).2⟩
        rw [LocalNet.combineIdx_apply_mem h_B_in_BC _ _ ⟨v, hv⟩ hv_in_combine]
        exact dif_pos hv_in_AB
      · have hv_not_in_combine : v ∉ ΛAB \ ΛA := fun h_in =>
          hv_in_AB (Finset.mem_sdiff.mp h_in).1
        have hv_compl : v ∈ ΛABC \ ΛAB :=
          Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hv).1, hv_in_AB⟩
        have hv_compl_compl : v ∈ (ΛABC \ ΛA) \ (ΛAB \ ΛA) :=
          Finset.mem_sdiff.mpr ⟨hv, hv_not_in_combine⟩
        rw [LocalNet.combineIdx_apply_not_mem h_B_in_BC _ _ ⟨v, hv⟩ hv_not_in_combine,
            show L.regionIdxCongr h_compl_eq.symm γ ⟨v, hv_compl_compl⟩ = γ ⟨v, hv_compl⟩
          from LocalNet.regionIdxCongr_apply (L := L) h_compl_eq.symm γ hv_compl hv_compl_compl]
        exact dif_neg hv_in_AB
    rw [hR_eq p.2, hR_eq p'.2]
    rfl
  have h_Φσ_pos : ((Φ : Matrix.QuantumChannel _ _) σ_full).toMatrix.PosDef := by
    rw [h_Φσ_mat]
    have h_kron_pos : (ρ_A ⊗ ρ_B).toMatrix.PosDef := by
      rw [DensityMatrix.kronecker_toMatrix]
      exact hρ_A.kronecker hρ_B
    exact h_kron_pos.mapEquiv _
  have h_dpi :
      D((Φ : Matrix.QuantumChannel _ _) ρ_ABC ∥ (Φ : Matrix.QuantumChannel _ _) σ_full) ≤
        D(ρ_ABC ∥ σ_full) :=
    Matrix.relativeEntropy_channel_le Φ ρ_ABC σ_full
  have h_dpi_lhs :
      D((Φ : Matrix.QuantumChannel _ _) ρ_ABC ∥ (Φ : Matrix.QuantumChannel _ _) σ_full) =
        D(ρ_AB_pt ∥ ρ_A ⊗ ρ_B) := by
    have h_Φρ_dm : (Φ : Matrix.QuantumChannel _ _) ρ_ABC =
        ρ_AB_pt.mapEquiv (L.combineIdx h_A).symm := by
      apply DensityMatrix.ext
      rw [h_Φρ_mat, DensityMatrix.mapEquiv_toMatrix, hρ_AB_pt_sub,
          Matrix.submatrix_submatrix]
      simp
    have h_Φσ_dm : (Φ : Matrix.QuantumChannel _ _) σ_full =
        (ρ_A ⊗ ρ_B).mapEquiv (L.combineIdx h_A).symm := by
      apply DensityMatrix.ext
      exact h_Φσ_mat
    rw [h_Φρ_dm, h_Φσ_dm]
    have h_kron_pos : (ρ_A ⊗ ρ_B).toMatrix.PosDef := by
      rw [DensityMatrix.kronecker_toMatrix]
      exact hρ_A.kronecker hρ_B
    exact Matrix.relativeEntropy_mapEquiv_posDef _ _ hρ_AB_pt h_kron_pos _
  have h_ρ_eq_pt : ρ_ABC = ρ_pt.mapEquiv (L.combineIdx (h_A.trans h_AB)).symm := by
    apply DensityMatrix.ext
    rw [DensityMatrix.mapEquiv_toMatrix, hρ_pt_sub, Matrix.submatrix_submatrix]
    simp
  have h_σ_full_eq_pt :
      σ_full = σ_pt.mapEquiv (L.combineIdx (h_A.trans h_AB)).symm := rfl
  have h_dpi_rhs : D(ρ_ABC ∥ σ_full) = D(ρ_pt ∥ σ_pt) := by
    rw [h_ρ_eq_pt, h_σ_full_eq_pt]
    exact Matrix.relativeEntropy_mapEquiv_posDef _ _ hρ_pt hσ_pt _
  have h_Sρ_eq : S(ρ_ABC) = S(ρ_pt) := by
    rw [h_ρ_eq_pt]
    exact Matrix.vonNeumannEntropy_mapEquiv_posDef _ hρ_pt _
  have h_SρAB_eq : S(ρ_AB) = S(ρ_AB_pt) := by
    rw [show ρ_AB = ρ_AB_pt.mapEquiv (L.combineIdx h_A).symm from by
      apply DensityMatrix.ext
      rw [DensityMatrix.mapEquiv_toMatrix, hρ_AB_pt_sub, Matrix.submatrix_submatrix]
      simp]
    exact Matrix.vonNeumannEntropy_mapEquiv_posDef _ hρ_AB_pt _
  rw [h_dpi_lhs, h_dpi_rhs] at h_dpi
  rw [h_mut_AB, h_mut_full] at h_dpi
  rw [h_Sρ_eq, h_SρAB_eq]
  have h_real :
      -S(ρ_AB_pt) + S(ρ_A) + S(ρ_B) ≤
        -S(ρ_pt) + S(ρ_A) + S(ρ_BC) := by
    exact_mod_cast h_dpi
  linarith

/-! #### Finset-equality bridges for the user-facing wrapper

For two `Λ ⊆ Λ_total` and `Λ' ⊆ Λ_total` Subset proofs whose Finsets are propositionally
equal (`Λ = Λ'`), the partial-trace `restrict h ρ` and `restrict h' ρ` are essentially
identical: their entropies and PosDef status agree. Discharged by `subst h_eq` plus
proof-irrelevance for `Subset`. Used in `vonNeumannEntropy_SSA_posDef` to bridge
user-facing `S(restrict h_BC ρ)` (with `{b,c}`) to the bipartite-natural form
`S(restrict sdiff_subset ρ)` (with `{a,b,c} \ {a}`). -/

private lemma vonNeumannEntropy_restrict_finset_eq
    {L : LocalNet} {Λ Λ' Λ_total : Finset L.sites} (h_eq : Λ = Λ')
    (h : Λ ⊆ Λ_total) (h' : Λ' ⊆ Λ_total) (ρ : L.densityMatrix Λ_total) :
    S(ρ ↾[h]) = S(ρ ↾[h']) := by
  subst h_eq
  rfl

private lemma posDef_restrict_finset_eq
    {L : LocalNet} {Λ Λ' Λ_total : Finset L.sites} (h_eq : Λ = Λ')
    (h : Λ ⊆ Λ_total) (h' : Λ' ⊆ Λ_total) (ρ : L.densityMatrix Λ_total) :
    (ρ ↾[h]).toMatrix.PosDef ↔ (ρ ↾[h']).toMatrix.PosDef := by
  subst h_eq
  rfl

/-- **Strong subadditivity (PosDef case, common-region-explicit form).**

This is the public region-level wrapper around
`vonNeumannEntropy_SSA_posDef_nested`. The theorem does not infer the common region from
the names `a b c` or from a product-factor order. Instead it receives explicit data:

* `ΛAB ⊆ ΛABC`, the first two-block marginal,
* `ΛA ⊆ ΛAB`, the split used inside `ΛAB`,
* `ΛBC ⊆ ΛABC`, the other two-block marginal,
* `ΛB ⊆ ΛABC`, the common/middle marginal,
* `ΛAB \ ΛA = ΛB`, identifying the common region,
* `ΛABC \ ΛA = ΛBC`, identifying the side obtained by tracing out `ΛA`.

Under PosDef hypotheses for the displayed marginals, the conclusion is exactly
`S(ρ_ABC ↾ ΛAB) + S(ρ_ABC ↾ ΛBC) ≥ S(ρ_ABC) + S(ρ_ABC ↾ ΛB)`. -/
private lemma vonNeumannEntropy_SSA_posDef
    {L : LocalNet} {ΛA ΛB ΛAB ΛBC ΛABC : Finset L.sites}
    (h_AB_total : ΛAB ⊆ ΛABC) (h_A_in_AB : ΛA ⊆ ΛAB)
    (h_BC_total : ΛBC ⊆ ΛABC) (h_B_total : ΛB ⊆ ΛABC)
    (h_B_eq : ΛAB \ ΛA = ΛB) (h_BC_eq : ΛABC \ ΛA = ΛBC)
    (ρ_ABC : L.densityMatrix ΛABC)
    (h_ABC_pos : ρ_ABC.toMatrix.PosDef)
    (h_A_pos : (ρ_ABC ↾[h_A_in_AB.trans h_AB_total]).toMatrix.PosDef)
    (h_AB_pos : (ρ_ABC ↾[h_AB_total]).toMatrix.PosDef)
    (h_BC_pos : (ρ_ABC ↾[h_BC_total]).toMatrix.PosDef)
    (h_B_pos : (ρ_ABC ↾[h_B_total]).toMatrix.PosDef) :
    S(ρ_ABC ↾[h_AB_total]) + S(ρ_ABC ↾[h_BC_total]) ≥
      S(ρ_ABC) + S(ρ_ABC ↾[h_B_total]) := by
  classical
  let h_B_nested : (ΛAB \ ΛA) ⊆ ΛABC :=
    (Finset.sdiff_subset_sdiff h_AB_total (le_refl ΛA)).trans Finset.sdiff_subset
  have h_BC_pos_nested :
      (ρ_ABC ↾[(Finset.sdiff_subset : ΛABC \ ΛA ⊆ ΛABC)]).toMatrix.PosDef :=
    posDef_restrict_finset_eq h_BC_eq.symm h_BC_total Finset.sdiff_subset ρ_ABC |>.mp h_BC_pos
  have h_B_pos_nested : (ρ_ABC ↾[h_B_nested]).toMatrix.PosDef :=
    posDef_restrict_finset_eq h_B_eq.symm h_B_total h_B_nested ρ_ABC |>.mp h_B_pos
  have h_nested := vonNeumannEntropy_SSA_posDef_nested h_AB_total h_A_in_AB ρ_ABC h_ABC_pos
    h_A_pos h_AB_pos h_BC_pos_nested h_B_pos_nested
  have h_S_BC : S(ρ_ABC ↾[h_BC_total]) =
      S(ρ_ABC ↾[(Finset.sdiff_subset : ΛABC \ ΛA ⊆ ΛABC)]) :=
    vonNeumannEntropy_restrict_finset_eq h_BC_eq.symm
      h_BC_total Finset.sdiff_subset ρ_ABC
  have h_S_B : S(ρ_ABC ↾[h_B_total]) = S(ρ_ABC ↾[h_B_nested]) :=
    vonNeumannEntropy_restrict_finset_eq h_B_eq.symm h_B_total h_B_nested ρ_ABC
  rwa [← h_S_BC, ← h_S_B] at h_nested


/-- **Strong subadditivity (common-region-explicit form, no PosDef hypothesis).**

PosDef-free version of `vonNeumannEntropy_SSA_posDef`. Given the geometric data of a
common-region split

* `ΛAB ⊆ ΛABC`, `ΛA ⊆ ΛAB`, `ΛBC ⊆ ΛABC`, `ΛB ⊆ ΛABC`,
* `ΛAB \ ΛA = ΛB`, `ΛABC \ ΛA = ΛBC`,

and `[Nonempty (L.regionIdx ΛABC)]` (which propagates to every sub-region by
`regionIdx_nonempty_of_subset`), strong subadditivity holds for every density matrix
`ρ_ABC : L.densityMatrix ΛABC`:

  `S(ρ_ABC ↾ ΛAB) + S(ρ_ABC ↾ ΛBC) ≥ S(ρ_ABC) + S(ρ_ABC ↾ ΛB)`.

The proof regularises `ρ` to the PosDef state `(1 - ε) ρ + ε · π_ΛABC` for `ε ∈ (0, 1]`,
applies `vonNeumannEntropy_SSA_posDef`, and passes to the limit `ε → 0⁺`
via the eigenvalue continuity formulas in `Regularize.lean`. -/
theorem vonNeumannEntropy_SSA
    {L : LocalNet} {ΛA ΛB ΛAB ΛBC ΛABC : Finset L.sites}
    (h_AB : ΛAB ⊆ ΛABC) (h_A : ΛA ⊆ ΛAB)
    (h_BC : ΛBC ⊆ ΛABC) (h_B : ΛB ⊆ ΛABC)
    (h_B_eq : ΛAB \ ΛA = ΛB) (h_BC_eq : ΛABC \ ΛA = ΛBC)
    [Nonempty (L.regionIdx ΛABC)]
    (ρ_ABC : L.densityMatrix ΛABC) :
    S(ρ_ABC ↾[h_AB]) + S(ρ_ABC ↾[h_BC]) ≥
      S(ρ_ABC) + S(ρ_ABC ↾[h_B]) := by
  -- Sub-region Nonempty instances, derived from `Nonempty (regionIdx ΛABC)`.
  haveI : Nonempty (L.regionIdx ΛAB) := L.regionIdx_nonempty_of_subset h_AB
  haveI : Nonempty (L.regionIdx ΛBC) := L.regionIdx_nonempty_of_subset h_BC
  haveI : Nonempty (L.regionIdx ΛB)  := L.regionIdx_nonempty_of_subset h_B
  haveI : Nonempty (L.regionIdx ΛA)  :=
    L.regionIdx_nonempty_of_subset (h_A.trans h_AB)
  -- Marginals and eigenvalue-formula functions.
  set ρ_AB := ρ_ABC ↾[h_AB] with hρ_AB
  set ρ_BC := ρ_ABC ↾[h_BC] with hρ_BC
  set ρ_B  := ρ_ABC ↾[h_B]  with hρ_B
  let f_AB : ℝ → ℝ := fun ε =>
    ∑ i, Real.negMulLog ((1 - ε) * ρ_AB.isHermitian.eigenvalues i +
      ε / Fintype.card (L.regionIdx ΛAB))
  let f_BC : ℝ → ℝ := fun ε =>
    ∑ i, Real.negMulLog ((1 - ε) * ρ_BC.isHermitian.eigenvalues i +
      ε / Fintype.card (L.regionIdx ΛBC))
  let f_full : ℝ → ℝ := fun ε =>
    ∑ i, Real.negMulLog ((1 - ε) * ρ_ABC.isHermitian.eigenvalues i +
      ε / Fintype.card (L.regionIdx ΛABC))
  let f_B : ℝ → ℝ := fun ε =>
    ∑ i, Real.negMulLog ((1 - ε) * ρ_B.isHermitian.eigenvalues i +
      ε / Fintype.card (L.regionIdx ΛB))
  -- For ε ∈ (0, 1]: regularised state and its 4 marginals are PosDef, so the PosDef
  -- common-region SSA applies.
  have h_ineq_pos : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      f_full ε + f_B ε ≤ f_AB ε + f_BC ε := by
    intro ε hε_pos hε_le
    have hρ_reg_pos :
        (DensityMatrix.regularize ρ_ABC hε_pos.le hε_le).toMatrix.PosDef :=
      DensityMatrix.regularize_posDef ρ_ABC hε_pos hε_le
    have h_AB_eq_reg :=
      regularize_restrict_toMatrix h_AB ρ_ABC hε_pos.le hε_le
    have h_BC_eq_reg :=
      regularize_restrict_toMatrix h_BC ρ_ABC hε_pos.le hε_le
    have h_A_eq_reg :=
      regularize_restrict_toMatrix (h_A.trans h_AB) ρ_ABC hε_pos.le hε_le
    have h_B_eq_reg :=
      regularize_restrict_toMatrix h_B ρ_ABC hε_pos.le hε_le
    have hAB_reg_pos :
        ((DensityMatrix.regularize ρ_ABC hε_pos.le hε_le) ↾[h_AB]).toMatrix.PosDef
        := by
      change (Matrix.restrict h_AB
        (DensityMatrix.regularize ρ_ABC hε_pos.le hε_le).toMatrix).PosDef
      rw [h_AB_eq_reg]; exact DensityMatrix.regularize_posDef _ hε_pos hε_le
    have hBC_reg_pos :
        ((DensityMatrix.regularize ρ_ABC hε_pos.le hε_le) ↾[h_BC]).toMatrix.PosDef
        := by
      change (Matrix.restrict h_BC
        (DensityMatrix.regularize ρ_ABC hε_pos.le hε_le).toMatrix).PosDef
      rw [h_BC_eq_reg]; exact DensityMatrix.regularize_posDef _ hε_pos hε_le
    have hA_reg_pos :
        ((DensityMatrix.regularize ρ_ABC hε_pos.le hε_le)
            ↾[h_A.trans h_AB]).toMatrix.PosDef := by
      change (Matrix.restrict (h_A.trans h_AB)
        (DensityMatrix.regularize ρ_ABC hε_pos.le hε_le).toMatrix).PosDef
      rw [h_A_eq_reg]; exact DensityMatrix.regularize_posDef _ hε_pos hε_le
    have hB_reg_pos :
        ((DensityMatrix.regularize ρ_ABC hε_pos.le hε_le) ↾[h_B]).toMatrix.PosDef
        := by
      change (Matrix.restrict h_B
        (DensityMatrix.regularize ρ_ABC hε_pos.le hε_le).toMatrix).PosDef
      rw [h_B_eq_reg]; exact DensityMatrix.regularize_posDef _ hε_pos hε_le
    have h_ssa := vonNeumannEntropy_SSA_posDef
      h_AB h_A h_BC h_B h_B_eq h_BC_eq
      (DensityMatrix.regularize ρ_ABC hε_pos.le hε_le)
      hρ_reg_pos hA_reg_pos hAB_reg_pos hBC_reg_pos hB_reg_pos
    have h_AB_dm := regularize_restrict h_AB ρ_ABC hε_pos.le hε_le
    have h_BC_dm := regularize_restrict h_BC ρ_ABC hε_pos.le hε_le
    have h_B_dm  := regularize_restrict h_B  ρ_ABC hε_pos.le hε_le
    rw [h_AB_dm, h_BC_dm, h_B_dm] at h_ssa
    have ef_AB :=
      Matrix.vonNeumannEntropy_regularize_eq_negMulLog_sum ρ_AB hε_pos.le hε_le
    have ef_BC :=
      Matrix.vonNeumannEntropy_regularize_eq_negMulLog_sum ρ_BC hε_pos.le hε_le
    have ef_full :=
      Matrix.vonNeumannEntropy_regularize_eq_negMulLog_sum ρ_ABC hε_pos.le hε_le
    have ef_B :=
      Matrix.vonNeumannEntropy_regularize_eq_negMulLog_sum ρ_B hε_pos.le hε_le
    rw [ef_AB, ef_BC, ef_full, ef_B] at h_ssa
    exact h_ssa
  have h_cont_AB : Filter.Tendsto f_AB (nhds 0) (nhds S(ρ_AB)) :=
    Matrix.tendsto_negMulLog_regularize_sum_zero ρ_AB
  have h_cont_BC : Filter.Tendsto f_BC (nhds 0) (nhds S(ρ_BC)) :=
    Matrix.tendsto_negMulLog_regularize_sum_zero ρ_BC
  have h_cont_full : Filter.Tendsto f_full (nhds 0) (nhds S(ρ_ABC)) :=
    Matrix.tendsto_negMulLog_regularize_sum_zero ρ_ABC
  have h_cont_B : Filter.Tendsto f_B (nhds 0) (nhds S(ρ_B)) :=
    Matrix.tendsto_negMulLog_regularize_sum_zero ρ_B
  have h_within : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      f_full ε + f_B ε ≤ f_AB ε + f_BC ε := by
    rw [eventually_nhdsWithin_iff]
    have h_le_one : ∀ᶠ ε in nhds (0 : ℝ), ε ≤ 1 :=
      Filter.eventually_of_mem (IsOpen.mem_nhds isOpen_Iio (by norm_num : (0 : ℝ) < 1)) <| by
        intros ε hε
        exact le_of_lt hε
    filter_upwards [h_le_one] with ε hε_le_one hε_pos
    exact h_ineq_pos ε hε_pos hε_le_one
  have h_LHS_lim :
      Filter.Tendsto (fun ε => f_AB ε + f_BC ε) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (S(ρ_AB) + S(ρ_BC))) :=
    (h_cont_AB.add h_cont_BC).mono_left nhdsWithin_le_nhds
  have h_RHS_lim :
      Filter.Tendsto (fun ε => f_full ε + f_B ε) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (S(ρ_ABC) + S(ρ_B))) :=
    (h_cont_full.add h_cont_B).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto_of_tendsto h_RHS_lim h_LHS_lim h_within

end DensityMatrix
