module

public import QuantumSystem.Algebra.LocalNet.MatrixModel.TensorDecomposition
public import QuantumSystem.Analysis.Matrix.PartialTrace
public import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# The partial trace is the operator form of `restrict`

Completing the operator-level tensor decomposition (`SiteIndexSystem.tensorEquiv`,
`SiteIndexSystem.opEquiv_includeAlgebra`), this file shows that the marginal `Matrix.restrict` is, under
the operator identifications, exactly the **partial trace** over the complementary Hilbert-space
factor: tracing out `ℋ (Λ_total \ Λ)`.

`opEquiv_restrict`: `opEquiv Λ (restrict h M) = LinearMap.partialTrace (regionBipartition h)
(opEquiv Λ_total M)`, with the traced-out subspace `ℋ (Λ_total \ Λ)` named explicitly by
`regionBipartition h` (defined in `TensorDecomposition`).

Together with `opEquiv_includeAlgebra` (isotony as the ampliation `LinearMap.ampliate`), this is the
Schrödinger/Heisenberg pair witnessing that `combineIdx` is a genuine tensor factorisation of
operators on Hilbert spaces.
-/

@[expose] public section

open WithLp
open scoped TensorProduct Matrix

namespace SiteIndexSystem

variable (L : SiteIndexSystem)

/-- Matrix entries of `(opEquiv Λ).symm T`: the `(i, j)` entry is the `i`-coordinate of the image
of the `j`-th standard basis vector under the operator `T`. (Internal helper.) -/
private lemma opEquiv_symm_apply_apply (Λ : Finset L.sites) (T : Module.End ℂ (L.ℋ Λ))
    (i j : L.regionIdx Λ) :
    (L.opEquiv Λ).symm T i j = ofLp (T (EuclideanSpace.single j (1 : ℂ))) i := by
  have hh := L.ofLp_opEquiv Λ ((L.opEquiv Λ).symm T) (EuclideanSpace.single j (1 : ℂ))
  rw [AlgEquiv.apply_symm_apply, PiLp.ofLp_single] at hh
  simpa [Matrix.mulVec_single_one, Matrix.col_apply] using (congrFun hh i).symm

/-- Internal: `restrict` as the `End A ⊗ End B`-level partial trace against the operator tensor
decomposition `tensorEquiv`. The public, explicit-subspace form is `opEquiv_restrict` below. -/
private theorem opEquiv_restrict_aux {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    (M : L.localAlgebra Λ_total) :
    L.opEquiv Λ (Matrix.restrict h M)
      = TensorProduct.partialTraceRight ((L.tensorEquiv h).symm (L.opEquiv Λ_total M)) := by
  suffices H : ∀ T : Module.End ℂ (L.ℋ Λ) ⊗[ℂ] Module.End ℂ (L.ℋ (Λ_total \ Λ)),
      L.opEquiv Λ (Matrix.restrict h ((L.opEquiv Λ_total).symm (L.tensorEquiv h T)))
        = TensorProduct.partialTraceRight T by
    have key := H ((L.tensorEquiv h).symm (L.opEquiv Λ_total M))
    rwa [AlgEquiv.apply_symm_apply, AlgEquiv.symm_apply_apply] at key
  intro T
  induction T using TensorProduct.induction_on with
  | zero => simp
  | add T₁ T₂ hT₁ hT₂ =>
    have hadd : ∀ A B : L.localAlgebra Λ_total,
        Matrix.restrict h (A + B) = Matrix.restrict h A + Matrix.restrict h B := by
      intro A B; ext a a'; simp [Matrix.restrict_apply, Finset.sum_add_distrib]
    simp only [map_add, hadd, hT₁, hT₂]
  | tmul Y Z =>
    rw [TensorProduct.partialTraceRight_tmul]
    have htrace : LinearMap.trace ℂ (L.ℋ (Λ_total \ Λ)) Z
        = ∑ b : L.regionIdx (Λ_total \ Λ), ofLp (Z (EuclideanSpace.single b (1 : ℂ))) b := by
      rw [LinearMap.trace_eq_sum_inner Z (EuclideanSpace.basisFun (L.regionIdx (Λ_total \ Λ)) ℂ)]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left, map_one, one_mul]
    refine (EuclideanSpace.basisFun (L.regionIdx Λ) ℂ).toBasis.ext fun a' => ?_
    rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
    apply WithLp.ofLp_injective (p := 2)
    funext a
    rw [ofLp_opEquiv, PiLp.ofLp_single, Matrix.mulVec_single_one, Matrix.col_apply,
      Matrix.restrict_apply]
    simp only [L.opEquiv_symm_apply_apply, tensorEquiv_tmul_apply,
      L.combineIdx_tensorEquiv_symm_single, TensorProduct.map_tmul,
      EuclideanSpace.ofLp_tensorEquiv_tmul, Equiv.symm_apply_apply, LinearMap.smul_apply]
    rw [← Finset.mul_sum, ← htrace]
    simp [mul_comm]

/-- **`restrict` is the partial trace** that explicitly traces out `ℋ (Λ_total \ Λ)`, via the named
bipartition `regionBipartition h`. The operator analogue of `Matrix.partialTrace (e : X ≃ A × B)`
applied to the AQFT marginal: combined with `opEquiv_includeAlgebra` (isotony as the ampliation)
and `LinearMap.partialTrace_ampliate_mul`, it gives the `𝔄(Λ)`-module ("pull-out") law of the
conditional expectation `𝔄(Λ_total) → 𝔄(Λ)`. -/
theorem opEquiv_restrict {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    (M : L.localAlgebra Λ_total) :
    L.opEquiv Λ (Matrix.restrict h M)
      = LinearMap.partialTrace (L.regionBipartition h) (L.opEquiv Λ_total M) := by
  rw [L.opEquiv_restrict_aux, LinearMap.partialTrace_apply]
  congr 1

end SiteIndexSystem
