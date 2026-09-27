/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# Intertwiners and the continuous functional calculus

Let `a` and `b` be normal operators on complex Hilbert spaces `E` and `F`, and `V : E →L[ℂ] F` a
bounded operator intertwining both `a` with `b` and `a†` with `b†`:
`V a = b V` and `V a† = b† V`. Then `V` intertwines every continuous function of them:
`V (cfc f a) = (cfc f b) V` for `f` continuous on the spectra of `a` and `b`. The proof runs the
Stone–Weierstrass induction over `C(σ(a) ∪ σ(b), ℂ)`.

Both intertwining relations are assumed, as in Mathlib's `Commute.cfc`. By the
Fuglede–Putnam–Rosenblum theorem the second follows from the first: for `E = F` this is
`SemiconjBy.star_right`, and for `E ≠ F` it follows by Berberian's trick (apply it to `a ⊕ b` and
the off-diagonal block `V` on `E ⊕ F`). That reduction is not formalised here; the consumer of this
lemma (spectral measures of self-adjoint operators) obtains both relations directly.

## Main results

* `ContinuousLinearMap.comp_cfc_eq_cfc_comp` — `V a = b V` and `V a† = b† V` imply
  `V (cfc f a) = (cfc f b) V`.
-/

@[expose] public section

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {a : E →L[ℂ] E} {b : F →L[ℂ] F} {V : E →L[ℂ] F}

/-- An operator `V` with `V a = b V` and `V a† = b† V`, for normal `a` and `b`, intertwines
`cfc f a` with `cfc f b` for every `f` continuous on the spectra of `a` and `b`. -/
theorem comp_cfc_eq_cfc_comp (ha : IsStarNormal a) (hb : IsStarNormal b) (h₁ : V ∘L a = b ∘L V)
    (h₂ : V ∘L adjoint a = adjoint b ∘L V) {f : ℂ → ℂ} (hfa : ContinuousOn f (spectrum ℂ a))
    (hfb : ContinuousOn f (spectrum ℂ b)) : V ∘L cfc f a = cfc f b ∘L V := by
  set K := spectrum ℂ a ∪ spectrum ℂ b
  have : CompactSpace K :=
    isCompact_iff_compactSpace.mp ((spectrum.isCompact a).union (spectrum.isCompact b))
  let ia : C(spectrum ℂ a, K) := ⟨Set.inclusion Set.subset_union_left, continuous_inclusion _⟩
  let ib : C(spectrum ℂ b, K) := ⟨Set.inclusion Set.subset_union_right, continuous_inclusion _⟩
  let Φa := (cfcHom ha).comp (ContinuousMap.compStarAlgHom' ℂ ℂ ia)
  let Φb := (cfcHom hb).comp (ContinuousMap.compStarAlgHom' ℂ ℂ ib)
  have hΦa : Continuous Φa := (cfcHom_continuous ha).comp (ContinuousMap.continuous_precomp ia)
  have hΦb : Continuous Φb := (cfcHom_continuous hb).comp (ContinuousMap.continuous_precomp ib)
  have key : ∀ g : C(K, ℂ), V ∘L Φa g = Φb g ∘L V := fun g => by
    induction g using ContinuousMap.induction_on_of_compact with
    | const r =>
      rw [show ContinuousMap.const K r = algebraMap ℂ _ r from rfl, AlgHomClass.commutes,
        AlgHomClass.commutes, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        comp_smul, smul_comp, one_def, one_def, comp_id, id_comp]
    | id =>
      have ea : Φa (.restrict K (.id ℂ)) = a := by
        rw [← cfcHom_id (R := ℂ) ha]
        rfl
      have eb : Φb (.restrict K (.id ℂ)) = b := by
        rw [← cfcHom_id (R := ℂ) hb]
        rfl
      rw [ea, eb, h₁]
    | star_id =>
      have ea : Φa (star (.restrict K (.id ℂ))) = adjoint a := by
        rw [map_star, ← star_eq_adjoint, ← cfcHom_id (R := ℂ) ha]
        rfl
      have eb : Φb (star (.restrict K (.id ℂ))) = adjoint b := by
        rw [map_star, ← star_eq_adjoint, ← cfcHom_id (R := ℂ) hb]
        rfl
      rw [ea, eb, h₂]
    | add f g hf hg => rw [map_add, map_add, comp_add, add_comp, hf, hg]
    | mul f g hf hg =>
      rw [map_mul, map_mul, mul_def, mul_def, ← comp_assoc, hf, comp_assoc, hg, comp_assoc]
    | frequently f hf =>
      have hcl : IsClosed {g : C(K, ℂ) | V ∘L Φa g = Φb g ∘L V} :=
        isClosed_eq ((compL ℂ E E F V).continuous.comp hΦa)
          (((compL ℂ E F F).flip V).continuous.comp hΦb)
      exact hcl.closure_subset (mem_closure_of_frequently_of_tendsto hf Filter.tendsto_id)
  have hK : ContinuousOn f K :=
    hfa.union_of_isClosed hfb (spectrum.isClosed a) (spectrum.isClosed b)
  rw [cfc_apply f a ha hfa, cfc_apply f b hb hfb]
  exact key ⟨K.domRestrict f, hK.domRestrict⟩

end ContinuousLinearMap
