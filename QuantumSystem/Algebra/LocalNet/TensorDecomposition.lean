module

public import QuantumSystem.Algebra.LocalNet.Isotony
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.TensorProduct
public import QuantumSystem.ForMathlib.LinearAlgebra.Trace

/-!
# Operator-level tensor decomposition of the local net

The combinatorial index bijection `combineIdx h : regionIdx Λ × regionIdx (Λ_total \ Λ) ≃
regionIdx Λ_total` is promoted here to a genuine **tensor factorisation of operators on Hilbert
spaces**, rather than a matrix Kronecker product.

For each finite region we take the Hilbert space `ℋ Λ := EuclideanSpace ℂ (regionIdx Λ)` and
identify the local matrix algebra `𝔄(Λ) = localAlgebra Λ` with the operator algebra
`End ℂ (ℋ Λ)` via `opEquiv`. The index bijection then induces a Hilbert-space tensor isometry
`ℋ Λ ⊗ ℋ (Λ_total \ Λ) ≃ ℋ Λ_total`, conjugation by which assembles, with
`endTensorEndAlgEquiv`, into an algebra isomorphism

  `tensorEquiv h : End ℂ (ℋ Λ) ⊗ End ℂ (ℋ (Λ_total \ Λ)) ≃ₐ End ℂ (ℋ Λ_total)`.

The isotony embedding is then literally "tensoring with the identity on the complement"
(`opEquiv_includeAlgebra`): `includeAlgebra h X` corresponds to `(op X) ⊗ 1`.
-/

@[expose] public section

open WithLp
open scoped TensorProduct Matrix

namespace LocalNet

variable (L : LocalNet)

/-- The Hilbert space of a region: the Euclidean space on its index type. -/
abbrev ℋ (Λ : Finset L.sites) : Type _ := EuclideanSpace ℂ (L.regionIdx Λ)

/-- The local matrix algebra `𝔄(Λ)`, identified with the algebra of operators on the region
Hilbert space `ℋ Λ` (matrices acting by multiplication on `EuclideanSpace`). -/
noncomputable def opEquiv (Λ : Finset L.sites) :
    L.localAlgebra Λ ≃ₐ[ℂ] Module.End ℂ (L.ℋ Λ) :=
  Matrix.toLinAlgEquiv'.trans
    ((EuclideanSpace.equiv (L.regionIdx Λ) ℂ).symm.toLinearEquiv.conjAlgEquiv ℂ)

@[simp]
lemma ofLp_opEquiv (Λ : Finset L.sites) (X : L.localAlgebra Λ) (v : L.ℋ Λ) :
    ofLp (L.opEquiv Λ X v) = X *ᵥ ofLp v :=
  rfl

/-- The **operator tensor decomposition** induced by the index bijection `combineIdx h`:
`End ℂ (ℋ Λ) ⊗ End ℂ (ℋ (Λ_total \ Λ)) ≃ₐ End ℂ (ℋ Λ_total)`. It is the operator-algebra tensor
equivalence followed by conjugation along the Hilbert-space tensor isometry. -/
noncomputable def tensorEquiv {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total) :
    Module.End ℂ (L.ℋ Λ) ⊗[ℂ] Module.End ℂ (L.ℋ (Λ_total \ Λ)) ≃ₐ[ℂ]
      Module.End ℂ (L.ℋ Λ_total) :=
  TensorProduct.endTensorEndAlgEquiv.trans
    ((EuclideanSpace.tensorEquiv (𝕜 := ℂ) (L.combineIdx h)).toLinearEquiv.conjAlgEquiv ℂ)

/-- Action of `tensorEquiv` on an operator tensor: conjugate `f ⊗ g` (as `TensorProduct.map f g`)
by the Hilbert-space tensor isometry. -/
lemma tensorEquiv_tmul_apply {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    (f : Module.End ℂ (L.ℋ Λ)) (g : Module.End ℂ (L.ℋ (Λ_total \ Λ))) (v : L.ℋ Λ_total) :
    L.tensorEquiv h (f ⊗ₜ[ℂ] g) v
      = EuclideanSpace.tensorEquiv (𝕜 := ℂ) (L.combineIdx h)
          (TensorProduct.map f g
            ((EuclideanSpace.tensorEquiv (𝕜 := ℂ) (L.combineIdx h)).symm v)) := by
  rw [tensorEquiv, AlgEquiv.trans_apply, TensorProduct.endTensorEndAlgEquiv_tmul,
    LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  rfl

/-- The inverse Hilbert-space tensor isometry sends a combined basis vector `single (combineIdx h
(a, b))` back to the pure tensor `single a ⊗ single b`. -/
lemma combineIdx_tensorEquiv_symm_single {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    (a : L.regionIdx Λ) (b : L.regionIdx (Λ_total \ Λ)) :
    (EuclideanSpace.tensorEquiv (𝕜 := ℂ) (L.combineIdx h)).symm
        (EuclideanSpace.single (L.combineIdx h (a, b)) (1 : ℂ))
      = EuclideanSpace.single a (1 : ℂ) ⊗ₜ[ℂ] EuclideanSpace.single b (1 : ℂ) := by
  rw [← EuclideanSpace.tensorEquiv_single_tmul (𝕜 := ℂ) (L.combineIdx h) a b]
  exact (EuclideanSpace.tensorEquiv (𝕜 := ℂ) (L.combineIdx h)).symm_apply_apply _

/-- Internal: isotony embedding as `(op X) ⊗ 1` against the operator tensor decomposition
`tensorEquiv`. The public, explicit-subspace form is `opEquiv_includeAlgebra` below. -/
private theorem opEquiv_includeAlgebra_aux {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    (X : L.localAlgebra Λ) :
    L.opEquiv Λ_total (L.includeAlgebra h X)
      = L.tensorEquiv h
          (L.opEquiv Λ X ⊗ₜ[ℂ] (1 : Module.End ℂ (L.ℋ (Λ_total \ Λ)))) := by
  refine (EuclideanSpace.basisFun (L.regionIdx Λ_total) ℂ).toBasis.ext fun s' => ?_
  obtain ⟨⟨a', b'⟩, rfl⟩ := (L.combineIdx h).surjective s'
  rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  apply WithLp.ofLp_injective (p := 2)
  funext s
  obtain ⟨⟨a, b⟩, rfl⟩ := (L.combineIdx h).surjective s
  rw [tensorEquiv_tmul_apply, L.combineIdx_tensorEquiv_symm_single h a' b',
    TensorProduct.map_tmul, Module.End.one_apply, EuclideanSpace.ofLp_tensorEquiv_tmul,
    Equiv.symm_apply_apply, ofLp_opEquiv, ofLp_opEquiv, PiLp.ofLp_single, PiLp.ofLp_single]
  simp

/-- The bipartition of the total Hilbert space induced by `combineIdx h`, with the complementary
factor `ℋ (Λ_total \ Λ)` as the (traced-out) second factor. Feeding this to
`LinearMap.partialTrace` / `LinearMap.ampliate` names the traced-out subspace explicitly. -/
noncomputable def regionBipartition {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total) :
    L.ℋ Λ_total ≃ₗ[ℂ] L.ℋ Λ ⊗[ℂ] L.ℋ (Λ_total \ Λ) :=
  (EuclideanSpace.tensorEquiv (𝕜 := ℂ) (L.combineIdx h)).toLinearEquiv.symm

/-- **Isotony is the ampliation along the named bipartition**: `includeAlgebra h X` acts as `X` on
`ℋ Λ` and the identity on the traced-out factor `ℋ (Λ_total \ Λ)`. This is the formal sense in which
`combineIdx` realises the tensor factorisation, with the complementary subspace named by
`regionBipartition h`. -/
theorem opEquiv_includeAlgebra {Λ Λ_total : Finset L.sites} (h : Λ ⊆ Λ_total)
    (X : L.localAlgebra Λ) :
    L.opEquiv Λ_total (L.includeAlgebra h X)
      = LinearMap.ampliate (L.regionBipartition h) (L.opEquiv Λ X) := by
  rw [L.opEquiv_includeAlgebra_aux, LinearMap.ampliate, tensorEquiv, AlgEquiv.trans_apply,
    TensorProduct.endTensorEndAlgEquiv_tmul, regionBipartition, LinearEquiv.symm_conjAlgEquiv,
    LinearEquiv.symm_symm]

end LocalNet
