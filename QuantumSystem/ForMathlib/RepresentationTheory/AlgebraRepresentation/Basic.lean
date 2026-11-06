/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic

/-!
# Irreducible representations over an algebraically closed field are onto the endomorphisms

An algebra `A` over an algebraically closed field `k`, acting on a finite-dimensional space `V`
with no invariant subspaces other than `0` and `V`, is onto `Module.End k V`: by Schur's lemma
(`IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed`) the commutant of the action is `k`, and
Jacobson density (`Module.Finite.toModuleEnd_moduleEnd_surjective`) makes the action onto the
endomorphisms commuting with it.

## Main results

* **`IsSimpleModule.lsmul_surjective_of_isAlgClosed`**: a simple module `V` over a `k`-algebra `A`,
  finite-dimensional over an algebraically closed `k`, has `A` acting onto `Module.End k V`.
* `AlgHom.surjective_of_forall_eq_bot_or_eq_top`: the same for an algebra homomorphism
  `A →ₐ[k] Module.End k V` whose only invariant subspaces are `⊥` and `⊤`.
-/

@[expose] public section

section IsSimpleModule

variable {A V : Type*} (k : Type*) [Field k] [Ring A] [Algebra k A] [AddCommGroup V] [Module k V]
  [Module A V] [IsScalarTower k A V] [IsSimpleModule A V] [FiniteDimensional k V] [IsAlgClosed k]

/-- A simple module `V` over a `k`-algebra `A`, finite-dimensional over an algebraically closed
field `k`: every `k`-linear endomorphism of `V` is the action of an element of `A`. -/
theorem IsSimpleModule.lsmul_surjective_of_isAlgClosed :
    Function.Surjective (Algebra.lsmul k k V : A →ₐ[k] Module.End k V) := by
  have hschur := IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k (A := A) (V := V)
  have : IsScalarTower k (Module.End A V) V := ⟨fun c f x ↦ by
    change (c • f) x = c • f x
    rw [LinearMap.smul_apply]⟩
  have : Module.Finite k (Module.End A V) :=
    .of_injective (LinearMap.restrictScalarsₗ k A V V k) (LinearMap.restrictScalars_injective k)
  have : Module.Finite (Module.End A V) V := .of_restrictScalars_finite k _ V
  intro T
  -- `T` commutes with the commutant, which is `k`
  let T' : V →ₗ[Module.End A V] V :=
    { toFun := T
      map_add' := map_add T
      map_smul' := fun f x ↦ by
        obtain ⟨c, rfl⟩ := hschur.2 f
        change T (algebraMap k (Module.End A V) c x) = algebraMap k (Module.End A V) c (T x)
        rw [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, LinearMap.smul_apply,
          Module.End.one_apply, Module.End.one_apply, map_smul] }
  obtain ⟨a, ha⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R := A) (M := V) T'
  exact ⟨a, LinearMap.ext fun x ↦ congr($ha x)⟩

end IsSimpleModule

variable {A V k : Type*} [Field k] [Ring A] [Algebra k A] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] [IsAlgClosed k]

/-- An algebra homomorphism `π : A →ₐ[k] Module.End k V` over an algebraically closed field `k`,
with `V` finite-dimensional, is onto `Module.End k V` when it is irreducible: the only subspaces of
`V` invariant under every `π a` are `⊥` and `⊤`. -/
lemma AlgHom.surjective_of_forall_eq_bot_or_eq_top (π : A →ₐ[k] Module.End k V)
    (h : ∀ L : Submodule k V, (∀ a, L ∈ Module.End.invtSubmodule (π a)) → L = ⊥ ∨ L = ⊤) :
    Function.Surjective π := by
  rcases subsingleton_or_nontrivial V with _ | _
  · exact fun T ↦ ⟨0, Subsingleton.elim _ _⟩
  let _ : Module A V := Module.compHom V π.toRingHom
  have : IsScalarTower k A V := ⟨fun c a x ↦ by
    change π (c • a) x = c • π a x
    rw [map_smul, LinearMap.smul_apply]⟩
  have : IsSimpleOrder (Submodule A V) :=
    { toNontrivial := inferInstance
      eq_bot_or_eq_top := fun N ↦ by
        rcases h (N.restrictScalars k) (fun a x hx ↦ N.smul_mem a hx) with hN | hN
        · exact Or.inl (by simpa using hN)
        · exact Or.inr (by simpa using hN) }
  have : IsSimpleModule A V := ⟨⟩
  exact IsSimpleModule.lsmul_surjective_of_isAlgClosed k (A := A) (V := V)
