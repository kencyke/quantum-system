/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
public import Mathlib.Algebra.Central.End
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Contraction

/-!
# Tensor product of endomorphism algebras and the commutant of `End A ⊗ 1`

For finite-dimensional free modules `M`, `N` over a commutative ring `R`, the canonical algebra
homomorphism `Module.endTensorEndAlgHom : End R M ⊗ End R N →ₐ End R (M ⊗ N)` is an isomorphism.
This file packages it as an `AlgEquiv`.

It also records the **commutant of `End A ⊗ 1`**: for finite-dimensional `ℂ`-spaces `A`, `B`, an
operator on `A ⊗ B` commuting with every ampliation `f ⊗ 1` is itself an ampliation `1 ⊗ g` of the
second factor (equivalently, the commutant of `B(A) ⊗ 1` is `1 ⊗ B(B)`). This is the uniqueness
statement needed to show that a partial trace along a decomposition `ℋ ≃ A ⊗ B` depends only on the
subsystem traced out (not formalised here); it is assembled from Mathlib's
`Subalgebra.centralizer_coe_range_includeLeft_eq_center_tensorProduct` together with the centrality
of `End ℂ A` (`Algebra.IsCentral`), so that `Z(End ℂ A) = ℂ·1`.

These are the abstract, basis-free ingredients of the tensor factorisation of operator algebras
on (finite-dimensional) Hilbert spaces.

## Main statements

* `TensorProduct.endTensorEndAlgEquiv` — the algebra isomorphism `End R M ⊗ End R N ≃ End R (M ⊗ N)`.
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

/-- `endTensorEndAlgEquiv` sends `f ⊗ g` to the tensor product map `TensorProduct.map f g`. -/
@[simp]
lemma endTensorEndAlgEquiv_tmul (f : Module.End R M) (g : Module.End R N) :
    (endTensorEndAlgEquiv (R := R) (M := M) (N := N)) (f ⊗ₜ[R] g) = TensorProduct.map f g := by
  rw [endTensorEndAlgEquiv, AlgEquiv.coe_ofBijective, Module.endTensorEndAlgHom_apply]
  apply TensorProduct.ext'
  intro m n
  rw [TensorProduct.AlgebraTensorModule.map_tmul, TensorProduct.map_tmul]

end TensorProduct

/-! ### The commutant of `End A ⊗ 1` in `End (A ⊗ B)` -/

namespace Algebra.TensorProduct

variable {A B : Type*} [AddCommGroup A] [Module ℂ A] [Module.Finite ℂ A] [Module.Free ℂ A]
  [AddCommGroup B] [Module ℂ B] [Module.Finite ℂ B] [Module.Free ℂ B]

omit [Module.Finite ℂ A] [Module.Finite ℂ B] [Module.Free ℂ B] in
/-- **Commutant of `End A ⊗ 1`, algebra form.** An element of `End ℂ A ⊗ End ℂ B` that commutes
with every `includeLeft f = f ⊗ 1` is of the form `includeRight g = 1 ⊗ g`. -/
lemma exists_includeRight_of_commute_includeLeft
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
