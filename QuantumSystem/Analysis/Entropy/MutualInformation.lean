module

public import QuantumSystem.Analysis.Entropy.KroneckerProduct
public import QuantumSystem.Analysis.Entropy.RelativeEntropy
public import QuantumSystem.Analysis.Entropy.VonNeumannEntropy

/-!
# Mutual-information identity

The relative-entropy form of quantum mutual information for a bipartite density matrix on a plain
product index type `n × m`:

  `D(ρ_AB ‖ ρ_A ⊗ ρ_B) = -S(ρ_AB) + S(ρ_A) + S(ρ_B)`.

It is representation-free; the analytic core reused by the direct proof
(`Analysis/Entropy/StrongSubadditivity.lean`) and, via transport, by the planned split-net proof
(`Analysis/Entropy/SplitSSA.lean`, not yet formalised — the split property it rests on is
`LocalNet.SplitProperty`).
-/

@[expose] public section

namespace Matrix

open scoped Kronecker MatrixOrder ComplexOrder QuantumInfo

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-! ### Relative-entropy identity -/

/-- **Mutual-information identity**: for a bipartite density
matrix `ρ_AB : DensityMatrix (n × m)` whose canonical partial traces coincide with PosDef
factor states `ρ_A` and `ρ_B`, the relative entropy w.r.t. the product `ρ_A ⊗ ρ_B`
equals `-S(ρ_AB) + S(ρ_A) + S(ρ_B)`. -/
theorem relativeEntropy_kronecker_marginals
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
  -- log of ρ_A ⊗ ρ_B decomposes via cfc_log_kronecker_posDef.
  have h_log_kron : cfc Real.log (ρ_A ⊗ ρ_B).toMatrix =
      cfc Real.log ρ_A.toMatrix ⊗ₖ (1 : Matrix m m ℂ) +
        (1 : Matrix n n ℂ) ⊗ₖ cfc Real.log ρ_B.toMatrix :=
    cfc_log_kronecker_posDef hρ_A hρ_B
  -- The trace identity after substitution.
  have h_trace_log_kron :
      Tr (ρ_AB.toMatrix * cfc Real.log (ρ_A ⊗ ρ_B).toMatrix) =
        Tr (ρ_A.toMatrix * cfc Real.log ρ_A.toMatrix) +
        Tr (ρ_B.toMatrix * cfc Real.log ρ_B.toMatrix) := by
    rw [h_log_kron, Matrix.mul_add, Matrix.trace_add, trace_mul_kronecker_one_right,
      trace_mul_kronecker_one_left, h_A_partialTrace, h_B_partialTrace]
  -- Split (log ρ - log(ρ_A⊗ρ_B)) and reduce trace.
  have h_split : Tr (ρ_AB.toMatrix * (cfc Real.log ρ_AB.toMatrix -
        cfc Real.log (ρ_A ⊗ ρ_B).toMatrix)) =
      Tr (ρ_AB.toMatrix * cfc Real.log ρ_AB.toMatrix) -
        Tr (ρ_AB.toMatrix * cfc Real.log (ρ_A ⊗ ρ_B).toMatrix) := by
    rw [Matrix.mul_sub, Matrix.trace_sub]
  -- Translate to the goal in EReal.
  change (↑(Tr (ρ_AB.toMatrix * (cfc Real.log ρ_AB.toMatrix -
        cfc Real.log (ρ_A ⊗ ρ_B).toMatrix))).re : EReal) =
      -S(ρ_AB) + S(ρ_A) + S(ρ_B)
  rw [h_split, Complex.sub_re, h_trace_log_kron, Complex.add_re]
  -- Now: ↑((Tr(ρ · log ρ)).re - ((Tr(ρ_A · log ρ_A)).re + (Tr(ρ_B · log ρ_B)).re))
  --      = -S(ρ) + S(ρ_A) + S(ρ_B)
  -- Express the LHS Real value:
  set α : ℝ := (Tr (ρ_AB.toMatrix * cfc Real.log ρ_AB.toMatrix)).re with hα
  set β : ℝ := (Tr (ρ_A.toMatrix * cfc Real.log ρ_A.toMatrix)).re with hβ
  set γ : ℝ := (Tr (ρ_B.toMatrix * cfc Real.log ρ_B.toMatrix)).re with hγ
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
