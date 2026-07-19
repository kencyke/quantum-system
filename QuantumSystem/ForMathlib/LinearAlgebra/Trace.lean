module

public import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
public import Mathlib.Algebra.Central.End
public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Trace

/-!
# Tensor product of endomorphism algebras, partial trace, and the commutant

For finite-dimensional free modules `M`, `N` over a commutative ring `R`, the canonical algebra
homomorphism `Module.endTensorEndAlgHom : End R M ⊗ End R N →ₐ End R (M ⊗ N)` is an isomorphism.
This file packages it as an `AlgEquiv` and uses it to define the **partial trace** over the second
factor `partialTraceRight : End R (M ⊗ N) →ₗ End R M`, characterised on operator tensors by
`Y ⊗ Z ↦ (trace Z) • Y`.

It also records the **commutant of `End A ⊗ 1`**: for finite-dimensional `ℂ`-spaces `A`, `B`, an
operator on `A ⊗ B` commuting with every ampliation `f ⊗ 1` is itself an ampliation `1 ⊗ g` of the
second factor (equivalently, the commutant of `B(A) ⊗ 1` is `1 ⊗ B(B)`). This is the
operator-algebraic uniqueness underlying the fact that a partial trace depends only on the subsystem
traced out, not on the chosen factorisation of its complement; it is assembled from Mathlib's
`Subalgebra.centralizer_coe_range_includeLeft_eq_center_tensorProduct` together with the centrality
of `End ℂ A` (`Algebra.IsCentral`), so that `Z(End ℂ A) = ℂ·1`.

These are the abstract, basis-free ingredients of the tensor factorisation of operator algebras
on (finite-dimensional) Hilbert spaces.

## Main statements

* `TensorProduct.endTensorEndAlgEquiv` — the algebra isomorphism `End R M ⊗ End R N ≃ End R (M ⊗ N)`.
* `LinearMap.partialTrace` — the partial trace along an explicit decomposition `e : ℋ ≃ A ⊗ B`.
* `Algebra.TensorProduct.exists_includeRight_of_commute_includeLeft` — algebra form of the commutant:
  in `End A ⊗ End B`, an element commuting with all `includeLeft f` is `includeRight g`.
* `LinearMap.exists_map_one_of_commute_map_id` — operator form: `T : End (A ⊗ B)` commuting with
  all `f ⊗ 1` equals `1 ⊗ g`.
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

lemma partialTrace_apply (e : ℋ ≃ₗ[𝕜] A ⊗[𝕜] B) (ρ : Module.End 𝕜 ℋ) :
    partialTrace e ρ = TensorProduct.partialTraceRight
      ((TensorProduct.endTensorEndAlgEquiv (R := 𝕜) (M := A) (N := B)).symm (e.conjAlgEquiv 𝕜 ρ)) :=
  rfl

/-- **Ampliation along `e`**: lift an operator `M` on the retained factor `A` to `ℋ`, acting as
`M` on `A` and the identity on the traced-out factor `B` (i.e. `M ⊗ 1` transported by `e`). -/
noncomputable def ampliate (e : ℋ ≃ₗ[𝕜] A ⊗[𝕜] B) (M : Module.End 𝕜 A) : Module.End 𝕜 ℋ :=
  (e.conjAlgEquiv 𝕜).symm (TensorProduct.map M 1)

/-- **Co-ampliation along `e`**: lift an operator `M` on the *complementary* factor `B` to `ℋ`,
acting as the identity on `A` and as `M` on `B` (i.e. `1 ⊗ M` transported by `e`). -/
noncomputable def coampliate (e : ℋ ≃ₗ[𝕜] A ⊗[𝕜] B) (M : Module.End 𝕜 B) : Module.End 𝕜 ℋ :=
  (e.conjAlgEquiv 𝕜).symm (TensorProduct.map 1 M)

private theorem endTensorEndAlgEquiv_symm_map_one (M : Module.End 𝕜 A) :
    (TensorProduct.endTensorEndAlgEquiv (R := 𝕜) (M := A) (N := B)).symm
        (TensorProduct.map M 1) = M ⊗ₜ[𝕜] 1 := by
  rw [← TensorProduct.endTensorEndAlgEquiv_tmul]
  exact (TensorProduct.endTensorEndAlgEquiv (R := 𝕜) (M := A) (N := B)).symm_apply_apply _

/-- **`Tr_B((M⊗1)·ρ) = M·Tr_B(ρ)`**: the partial trace along `e` is a left module map over the
ampliation, with `B` (the traced-out subspace) named explicitly by `e`. -/
lemma partialTrace_ampliate_mul (e : ℋ ≃ₗ[𝕜] A ⊗[𝕜] B) (M : Module.End 𝕜 A)
    (ρ : Module.End 𝕜 ℋ) :
    partialTrace e (ampliate e M * ρ) = M * partialTrace e ρ := by
  rw [partialTrace_apply, partialTrace_apply, ampliate, map_mul (e.conjAlgEquiv 𝕜),
    AlgEquiv.apply_symm_apply,
    map_mul (TensorProduct.endTensorEndAlgEquiv (R := 𝕜) (M := A) (N := B)).symm,
    endTensorEndAlgEquiv_symm_map_one, TensorProduct.partialTraceRight_includeLeft_mul]

end LinearMap

/-! ### The commutant of `End A ⊗ 1` in `End (A ⊗ B)` -/

namespace Algebra.TensorProduct

variable {A B : Type*} [AddCommGroup A] [Module ℂ A] [Module.Finite ℂ A] [Module.Free ℂ A]
  [AddCommGroup B] [Module ℂ B] [Module.Finite ℂ B] [Module.Free ℂ B]

omit [Module.Finite ℂ A] [Module.Finite ℂ B] [Module.Free ℂ B] in
/-- **Commutant of `End A ⊗ 1`, algebra form.** An element of `End ℂ A ⊗ End ℂ B` that commutes
with every `includeLeft f = f ⊗ 1` is of the form `includeRight g = 1 ⊗ g`. -/
theorem exists_includeRight_of_commute_includeLeft
    (S : Module.End ℂ A ⊗[ℂ] Module.End ℂ B)
    (hS : ∀ f : Module.End ℂ A,
      (Algebra.TensorProduct.includeLeft (R := ℂ) (S := ℂ) (A := Module.End ℂ A)
        (B := Module.End ℂ B) f) * S
      = S * Algebra.TensorProduct.includeLeft (R := ℂ) (S := ℂ) (A := Module.End ℂ A)
        (B := Module.End ℂ B) f) :
    ∃ g, S = Algebra.TensorProduct.includeRight g := by
  -- Every element of `(⊥ : Subalgebra) ⊗ End B` is `1 ⊗ g`.
  have hext : ∀ x : (⊥ : Subalgebra ℂ (Module.End ℂ A)) ⊗[ℂ] Module.End ℂ B,
      ∃ g, Algebra.TensorProduct.map (⊥ : Subalgebra ℂ (Module.End ℂ A)).val
          (AlgHom.id ℂ (Module.End ℂ B)) x = Algebra.TensorProduct.includeRight g := by
    intro x
    induction x with
    | zero => exact ⟨0, by simp⟩
    | tmul a' g =>
      obtain ⟨c, hc⟩ := Algebra.mem_bot.mp a'.2
      refine ⟨c • g, ?_⟩
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        Algebra.TensorProduct.includeRight_apply]
      rw [show (Subalgebra.val ⊥) a' = algebraMap ℂ (Module.End ℂ A) c from hc.symm,
        Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    | add x y hx hy =>
      obtain ⟨g₁, h₁⟩ := hx; obtain ⟨g₂, h₂⟩ := hy
      exact ⟨g₁ + g₂, by rw [map_add, h₁, h₂, ← map_add]⟩
  -- `S` lies in the centralizer of `range includeLeft`, which (by centrality of `End A`) is
  -- `range includeRight`.
  have hmem : S ∈ Subalgebra.centralizer ℂ
      (↑(Algebra.TensorProduct.includeLeft (R := ℂ) (S := ℂ) (A := Module.End ℂ A)
        (B := Module.End ℂ B)).range : Set _) := by
    rw [Subalgebra.mem_centralizer_iff]
    rintro s ⟨f, rfl⟩
    exact hS f
  rw [Subalgebra.centralizer_coe_range_includeLeft_eq_center_tensorProduct,
    Algebra.IsCentral.center_eq_bot, AlgHom.mem_range] at hmem
  obtain ⟨x, hx⟩ := hmem
  obtain ⟨g, hg⟩ := hext x
  exact ⟨g, by rw [← hx, hg]⟩

omit [Module.Finite ℂ A] [Module.Free ℂ A] [Module.Finite ℂ B] [Module.Free ℂ B] in
/-- **Commutant of `1 ⊗ End B`, algebra form.** An element of `End ℂ A ⊗ End ℂ B` that commutes
with every `includeRight g = 1 ⊗ g` is of the form `includeLeft f = f ⊗ 1`. -/
lemma exists_includeLeft_of_commute_includeRight
    (S : Module.End ℂ A ⊗[ℂ] Module.End ℂ B)
    (hS : ∀ g : Module.End ℂ B,
      (Algebra.TensorProduct.includeRight (R := ℂ) (A := Module.End ℂ A)
        (B := Module.End ℂ B) g) * S
      = S * Algebra.TensorProduct.includeRight (R := ℂ) (A := Module.End ℂ A)
        (B := Module.End ℂ B) g) :
    ∃ f, S = Algebra.TensorProduct.includeLeft (R := ℂ) (S := ℂ) (A := Module.End ℂ A)
      (B := Module.End ℂ B) f := by
  have hext : ∀ x : Module.End ℂ A ⊗[ℂ] (⊥ : Subalgebra ℂ (Module.End ℂ B)),
      ∃ f, Algebra.TensorProduct.map (AlgHom.id ℂ (Module.End ℂ A))
          (⊥ : Subalgebra ℂ (Module.End ℂ B)).val x
        = Algebra.TensorProduct.includeLeft (R := ℂ) (S := ℂ) (A := Module.End ℂ A)
          (B := Module.End ℂ B) f := by
    intro x
    induction x with
    | zero => exact ⟨0, by simp⟩
    | tmul a b' =>
      obtain ⟨c, hc⟩ := Algebra.mem_bot.mp b'.2
      refine ⟨c • a, ?_⟩
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        Algebra.TensorProduct.includeLeft_apply]
      rw [show (Subalgebra.val ⊥) b' = algebraMap ℂ (Module.End ℂ B) c from hc.symm,
        Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    | add x y hx hy =>
      obtain ⟨f₁, h₁⟩ := hx; obtain ⟨f₂, h₂⟩ := hy
      exact ⟨f₁ + f₂, by rw [map_add, h₁, h₂, ← map_add]⟩
  have hmem : S ∈ Subalgebra.centralizer ℂ
      (↑(Algebra.TensorProduct.includeRight (R := ℂ) (A := Module.End ℂ A)
        (B := Module.End ℂ B)).range : Set _) := by
    rw [Subalgebra.mem_centralizer_iff]
    rintro s ⟨g, rfl⟩
    exact hS g
  rw [Subalgebra.centralizer_range_includeRight_eq_center_tensorProduct,
    Algebra.IsCentral.center_eq_bot, AlgHom.mem_range] at hmem
  obtain ⟨x, hx⟩ := hmem
  obtain ⟨f, hf⟩ := hext x
  exact ⟨f, by rw [← hx, hf]⟩

end Algebra.TensorProduct

namespace LinearMap

variable {A B : Type*} [AddCommGroup A] [Module ℂ A] [Module.Finite ℂ A] [Module.Free ℂ A]
  [AddCommGroup B] [Module ℂ B] [Module.Finite ℂ B] [Module.Free ℂ B]

/-- **Commutant of `End A ⊗ 1`, operator form.** An operator `T : End (A ⊗ B)` commuting with every
ampliation `f ⊗ 1 = TensorProduct.map f 1` is an ampliation `1 ⊗ g = TensorProduct.map 1 g` of the
second factor. -/
theorem exists_map_one_of_commute_map_id
    (T : Module.End ℂ (A ⊗[ℂ] B))
    (hT : ∀ f : Module.End ℂ A,
      T ∘ₗ TensorProduct.map f LinearMap.id = TensorProduct.map f LinearMap.id ∘ₗ T) :
    ∃ g : Module.End ℂ B, T = TensorProduct.map LinearMap.id g := by
  have hcomm : ∀ f : Module.End ℂ A,
      Algebra.TensorProduct.includeLeft (R := ℂ) (S := ℂ) (A := Module.End ℂ A)
          (B := Module.End ℂ B) f * TensorProduct.endTensorEndAlgEquiv.symm T
      = TensorProduct.endTensorEndAlgEquiv.symm T
          * Algebra.TensorProduct.includeLeft (R := ℂ) (S := ℂ) (A := Module.End ℂ A)
            (B := Module.End ℂ B) f := by
    intro f
    have key : TensorProduct.endTensorEndAlgEquiv (Algebra.TensorProduct.includeLeft
          (R := ℂ) (S := ℂ) (A := Module.End ℂ A) (B := Module.End ℂ B) f)
        = TensorProduct.map f (LinearMap.id : Module.End ℂ B) := by
      rw [Algebra.TensorProduct.includeLeft_apply, TensorProduct.endTensorEndAlgEquiv_tmul,
        Module.End.one_eq_id]
    apply TensorProduct.endTensorEndAlgEquiv.injective
    rw [map_mul, map_mul, AlgEquiv.apply_symm_apply, key]
    exact (hT f).symm
  obtain ⟨g, hg⟩ :=
    Algebra.TensorProduct.exists_includeRight_of_commute_includeLeft
      (TensorProduct.endTensorEndAlgEquiv.symm T) hcomm
  refine ⟨g, ?_⟩
  have heq := congrArg TensorProduct.endTensorEndAlgEquiv hg
  rw [AlgEquiv.apply_symm_apply, Algebra.TensorProduct.includeRight_apply,
    TensorProduct.endTensorEndAlgEquiv_tmul] at heq
  exact heq

/-- **Commutant of `1 ⊗ End B`, operator form.** An operator `T : End (A ⊗ B)` commuting with every
`1 ⊗ g = TensorProduct.map 1 g` is an ampliation `f ⊗ 1 = TensorProduct.map f 1` of the first
factor. -/
lemma exists_map_id_of_commute_map_one
    (T : Module.End ℂ (A ⊗[ℂ] B))
    (hT : ∀ g : Module.End ℂ B,
      T ∘ₗ TensorProduct.map LinearMap.id g = TensorProduct.map LinearMap.id g ∘ₗ T) :
    ∃ f : Module.End ℂ A, T = TensorProduct.map f LinearMap.id := by
  have hcomm : ∀ g : Module.End ℂ B,
      Algebra.TensorProduct.includeRight (R := ℂ) (A := Module.End ℂ A)
          (B := Module.End ℂ B) g * TensorProduct.endTensorEndAlgEquiv.symm T
      = TensorProduct.endTensorEndAlgEquiv.symm T
          * Algebra.TensorProduct.includeRight (R := ℂ) (A := Module.End ℂ A)
            (B := Module.End ℂ B) g := by
    intro g
    have key : TensorProduct.endTensorEndAlgEquiv (Algebra.TensorProduct.includeRight
          (R := ℂ) (A := Module.End ℂ A) (B := Module.End ℂ B) g)
        = TensorProduct.map (LinearMap.id : Module.End ℂ A) g := by
      rw [Algebra.TensorProduct.includeRight_apply, TensorProduct.endTensorEndAlgEquiv_tmul,
        Module.End.one_eq_id]
    apply TensorProduct.endTensorEndAlgEquiv.injective
    rw [map_mul, map_mul, AlgEquiv.apply_symm_apply, key]
    exact (hT g).symm
  obtain ⟨f, hf⟩ :=
    Algebra.TensorProduct.exists_includeLeft_of_commute_includeRight
      (TensorProduct.endTensorEndAlgEquiv.symm T) hcomm
  refine ⟨f, ?_⟩
  have heq := congrArg TensorProduct.endTensorEndAlgEquiv hf
  rw [AlgEquiv.apply_symm_apply, Algebra.TensorProduct.includeLeft_apply,
    TensorProduct.endTensorEndAlgEquiv_tmul, Module.End.one_eq_id] at heq
  exact heq

end LinearMap
