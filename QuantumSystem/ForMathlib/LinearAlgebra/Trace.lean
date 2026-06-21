module

public import Mathlib.LinearAlgebra.Trace

/-!
# Tensor product of endomorphism algebras and the partial trace

For finite-dimensional free modules `M`, `N` over a commutative ring `R`, the canonical algebra
homomorphism `Module.endTensorEndAlgHom : End R M ⊗ End R N →ₐ End R (M ⊗ N)` is an isomorphism.
This file packages it as an `AlgEquiv` and uses it to define the **partial trace** over the second
factor `partialTraceRight : End R (M ⊗ N) →ₗ End R M`, characterised on operator tensors by
`Y ⊗ Z ↦ (trace Z) • Y`.

These are the abstract, basis-free ingredients of the tensor factorisation of operator algebras
on (finite-dimensional) Hilbert spaces.
-/

@[expose] public section

open scoped TensorProduct

namespace TensorProduct

variable {R : Type*} [CommRing R] {M N : Type*}
  [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Free R M]
  [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Free R N]

/-- For finite-dimensional free modules, `Module.endTensorEndAlgHom` is an algebra isomorphism
`End R M ⊗ End R N ≃ₐ End R (M ⊗ N)`. -/
noncomputable def endTensorEndAlgEquiv :
    Module.End R M ⊗[R] Module.End R N ≃ₐ[R] Module.End R (M ⊗[R] N) :=
  AlgEquiv.ofBijective Module.endTensorEndAlgHom <| by
    have h : (Module.endTensorEndAlgHom (R := R) (S := R) (A := R) (M := M) (N := N)).toLinearMap
        = (homTensorHomEquiv R M N M N).toLinearMap := by
      apply TensorProduct.ext'
      intro f g
      rw [AlgHom.toLinearMap_apply, Module.endTensorEndAlgHom_apply,
        LinearEquiv.coe_coe, homTensorHomEquiv_apply]
      apply TensorProduct.ext'
      intro m n
      rw [TensorProduct.AlgebraTensorModule.map_tmul, TensorProduct.homTensorHomMap_apply,
        TensorProduct.map_tmul]
    have hcoe : ⇑(Module.endTensorEndAlgHom (R := R) (S := R) (A := R) (M := M) (N := N))
        = ⇑(homTensorHomEquiv R M N M N) := funext fun x => LinearMap.congr_fun h x
    rw [hcoe]
    exact (homTensorHomEquiv R M N M N).bijective

@[simp]
lemma endTensorEndAlgEquiv_tmul (f : Module.End R M) (g : Module.End R N) :
    (endTensorEndAlgEquiv (R := R) (M := M) (N := N)) (f ⊗ₜ[R] g) = TensorProduct.map f g := by
  rw [endTensorEndAlgEquiv, AlgEquiv.coe_ofBijective, Module.endTensorEndAlgHom_apply]
  apply TensorProduct.ext'
  intro m n
  rw [TensorProduct.AlgebraTensorModule.map_tmul, TensorProduct.map_tmul]

/-- The **partial trace over the second factor** `End R M ⊗ End R N →ₗ End R M`: trace out the
`N`-factor of an operator tensor, characterised by `Y ⊗ Z ↦ (trace Z) • Y`. This is the abstract
partial trace paired with the operator tensor decomposition `endTensorEndAlgEquiv`. -/
noncomputable def partialTraceRight :
    Module.End R M ⊗[R] Module.End R N →ₗ[R] Module.End R M :=
  (TensorProduct.rid R (Module.End R M)).toLinearMap ∘ₗ
    TensorProduct.map LinearMap.id (LinearMap.trace R N)

omit [Module.Finite R M] [Module.Free R M] [Module.Finite R N] [Module.Free R N] in
@[simp]
lemma partialTraceRight_tmul (Y : Module.End R M) (Z : Module.End R N) :
    partialTraceRight (Y ⊗ₜ[R] Z) = (LinearMap.trace R N Z) • Y := by
  rw [partialTraceRight, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    LinearEquiv.coe_coe, TensorProduct.rid_tmul]

omit [Module.Finite R M] [Module.Free R M] [Module.Finite R N] [Module.Free R N] in
/-- **Left module property** (pull-out): the partial trace pulls a left factor `Y ⊗ 1` out of the
first tensor factor, `partialTraceRight ((Y ⊗ 1) * S) = Y * partialTraceRight S`. Internal building
block for `LinearMap.partialTrace_ampliate_mul`. -/
private lemma partialTraceRight_includeLeft_mul (Y : Module.End R M)
    (S : Module.End R M ⊗[R] Module.End R N) :
    partialTraceRight ((Y ⊗ₜ[R] (1 : Module.End R N)) * S) = Y * partialTraceRight S := by
  induction S using TensorProduct.induction_on with
  | zero => simp
  | tmul Y' Z' =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, partialTraceRight_tmul,
      partialTraceRight_tmul, mul_smul_comm]
  | add S₁ S₂ h₁ h₂ => rw [mul_add, map_add, map_add, h₁, h₂, mul_add]

end TensorProduct

namespace LinearMap

open scoped TensorProduct

variable {𝕜 ℋ A B : Type*} [Field 𝕜]
  [AddCommGroup ℋ] [Module 𝕜 ℋ]
  [AddCommGroup A] [Module 𝕜 A] [Module.Finite 𝕜 A] [Module.Free 𝕜 A]
  [AddCommGroup B] [Module 𝕜 B] [Module.Finite 𝕜 B] [Module.Free 𝕜 B]

/-- **Partial trace along an explicit decomposition** `e : ℋ ≃ₗ A ⊗ B`: trace out the named second
factor `B` and retain `A`. This is the operator analogue of `Matrix.partialTrace (e : X ≃ A × B)` —
the subspace traced out is named by `e`, and the retained subsystem `A` appears in the codomain. -/
noncomputable def partialTrace (e : ℋ ≃ₗ[𝕜] A ⊗[𝕜] B) :
    Module.End 𝕜 ℋ →ₗ[𝕜] Module.End 𝕜 A :=
  TensorProduct.partialTraceRight ∘ₗ
    (TensorProduct.endTensorEndAlgEquiv (R := 𝕜) (M := A) (N := B)).symm.toLinearMap ∘ₗ
    (e.conjAlgEquiv 𝕜).toLinearMap

theorem partialTrace_apply (e : ℋ ≃ₗ[𝕜] A ⊗[𝕜] B) (ρ : Module.End 𝕜 ℋ) :
    partialTrace e ρ = TensorProduct.partialTraceRight
      ((TensorProduct.endTensorEndAlgEquiv (R := 𝕜) (M := A) (N := B)).symm (e.conjAlgEquiv 𝕜 ρ)) :=
  rfl

/-- **Ampliation along `e`**: lift an operator `M` on the retained factor `A` to `ℋ`, acting as
`M` on `A` and the identity on the traced-out factor `B` (i.e. `M ⊗ 1` transported by `e`). -/
noncomputable def ampliate (e : ℋ ≃ₗ[𝕜] A ⊗[𝕜] B) (M : Module.End 𝕜 A) : Module.End 𝕜 ℋ :=
  (e.conjAlgEquiv 𝕜).symm (TensorProduct.map M 1)

private theorem endTensorEndAlgEquiv_symm_map_one (M : Module.End 𝕜 A) :
    (TensorProduct.endTensorEndAlgEquiv (R := 𝕜) (M := A) (N := B)).symm
        (TensorProduct.map M 1) = M ⊗ₜ[𝕜] 1 := by
  rw [← TensorProduct.endTensorEndAlgEquiv_tmul]
  exact (TensorProduct.endTensorEndAlgEquiv (R := 𝕜) (M := A) (N := B)).symm_apply_apply _

/-- **`Tr_B((M⊗1)·ρ) = M·Tr_B(ρ)`**: the partial trace along `e` is a left module map over the
ampliation, with `B` (the traced-out subspace) named explicitly by `e`. -/
theorem partialTrace_ampliate_mul (e : ℋ ≃ₗ[𝕜] A ⊗[𝕜] B) (M : Module.End 𝕜 A)
    (ρ : Module.End 𝕜 ℋ) :
    partialTrace e (ampliate e M * ρ) = M * partialTrace e ρ := by
  rw [partialTrace_apply, partialTrace_apply, ampliate, map_mul (e.conjAlgEquiv 𝕜),
    AlgEquiv.apply_symm_apply,
    map_mul (TensorProduct.endTensorEndAlgEquiv (R := 𝕜) (M := A) (N := B)).symm,
    endTensorEndAlgEquiv_symm_map_one, TensorProduct.partialTraceRight_includeLeft_mul]

end LinearMap
