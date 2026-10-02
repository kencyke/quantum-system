/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Fuglede
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Intertwiners and the continuous functional calculus

Let `a` and `b` be normal operators on complex Hilbert spaces `E` and `F`, and `V : E →L[ℂ] F` a
bounded operator intertwining `a` with `b`: `V a = b V`. Then `V` intertwines every continuous
function of them: `V (cfc f a) = (cfc f b) V` for `f` continuous on the spectra of `a` and `b`.

By the **Fuglede–Putnam–Rosenblum theorem** `V` also intertwines the adjoints, `V a† = b† V`.
Mathlib proves it inside one C⋆-algebra (`SemiconjBy.star_right`); for operators on different
spaces it follows by Berberian's trick: on the Hilbert direct sum `E ⊕ F = WithLp 2 (E × F)` the
off-diagonal corner `(0 0; V 0)` commutes with the normal diagonal operator `a ⊕ b`, hence with
its adjoint `a† ⊕ b†`, and the corner of that commutation is `V a† = b† V`. With both relations,
`V (cfc f a) = (cfc f b) V` follows by the Stone–Weierstrass induction over `C(σ(a) ∪ σ(b), ℂ)`.

## Main results

* `ContinuousLinearMap.comp_adjoint_eq_adjoint_comp` — Fuglede–Putnam–Rosenblum for operators
  between Hilbert spaces: `V a = b V` with `a`, `b` normal implies `V a† = b† V`.
* `ContinuousLinearMap.comp_cfc_eq_cfc_comp` — `V a = b V` implies `V (cfc f a) = (cfc f b) V`.
-/

@[expose] public section

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {a : E →L[ℂ] E} {b : F →L[ℂ] F} {V : E →L[ℂ] F}

open WithLp

/-! ### Fuglede–Putnam–Rosenblum between Hilbert spaces -/

/-- The diagonal operator `a ⊕ b` on the Hilbert direct sum `WithLp 2 (E × F)`. -/
private noncomputable def diagL2 (a : E →L[ℂ] E) (b : F →L[ℂ] F) :
    WithLp 2 (E × F) →L[ℂ] WithLp 2 (E × F) :=
  (prodContinuousLinearEquiv 2 ℂ E F).symm.toContinuousLinearMap ∘L a.prodMap b ∘L
    (prodContinuousLinearEquiv 2 ℂ E F).toContinuousLinearMap

omit [CompleteSpace E] [CompleteSpace F] in
private lemma diagL2_apply (a : E →L[ℂ] E) (b : F →L[ℂ] F) (z : WithLp 2 (E × F)) :
    diagL2 a b z = toLp 2 (a (ofLp z).1, b (ofLp z).2) := rfl

/-- The off-diagonal corner `(0 0; V 0)` on the Hilbert direct sum `WithLp 2 (E × F)`. -/
private noncomputable def cornerL2 (V : E →L[ℂ] F) : WithLp 2 (E × F) →L[ℂ] WithLp 2 (E × F) :=
  (prodContinuousLinearEquiv 2 ℂ E F).symm.toContinuousLinearMap ∘L
    (inr ℂ E F ∘L V ∘L fstL 2 ℂ E F)

omit [CompleteSpace E] [CompleteSpace F] in
private lemma cornerL2_apply (V : E →L[ℂ] F) (z : WithLp 2 (E × F)) :
    cornerL2 V z = toLp 2 (0, V (ofLp z).1) := rfl

private lemma adjoint_diagL2 (a : E →L[ℂ] E) (b : F →L[ℂ] F) :
    adjoint (diagL2 a b) = diagL2 (adjoint a) (adjoint b) := by
  refine ((eq_adjoint_iff _ _).mpr fun x y => ?_).symm
  simp only [diagL2_apply, prod_inner_apply, adjoint_inner_left]

/-- **Fuglede–Putnam–Rosenblum theorem** for operators between Hilbert spaces: if `V a = b V` with
`a` and `b` normal, then `V a† = b† V`. By Berberian's trick, the corner `(0 0; V 0)` of
`E ⊕ F` commutes with the normal operator `a ⊕ b`, hence with its adjoint by
`IsStarNormal.commute_star_right`. -/
theorem comp_adjoint_eq_adjoint_comp (ha : IsStarNormal a) (hb : IsStarNormal b)
    (h : V ∘L a = b ∘L V) : V ∘L adjoint a = adjoint b ∘L V := by
  have hd : IsStarNormal (diagL2 a b) := by
    refine ⟨?_⟩
    have ea := ha.star_comm_self
    have eb := hb.star_comm_self
    simp only [star_eq_adjoint, adjoint_diagL2, commute_iff_eq, mul_def] at ea eb ⊢
    refine ContinuousLinearMap.ext fun z => ?_
    simp only [comp_apply, diagL2_apply]
    rw [← comp_apply (adjoint a), ea, ← comp_apply (adjoint b), eb, comp_apply, comp_apply]
  have hw : Commute (cornerL2 V) (diagL2 a b) := by
    rw [commute_iff_eq, mul_def, mul_def]
    refine ContinuousLinearMap.ext fun z => ?_
    simp only [comp_apply, diagL2_apply, cornerL2_apply, map_zero]
    rw [← comp_apply V a, h, comp_apply]
  have hw' := hd.commute_star_right hw
  rw [star_eq_adjoint, adjoint_diagL2, commute_iff_eq, mul_def, mul_def] at hw'
  refine ContinuousLinearMap.ext fun u => ?_
  have := congrArg (fun x => (ofLp x).2) (congrArg (fun T => T (toLp 2 (u, 0))) hw')
  simpa [diagL2_apply, cornerL2_apply] using this

/-! ### Intertwining the continuous functional calculus -/

/-- An operator `V` with `V a = b V`, for normal `a` and `b`, intertwines `cfc f a` with `cfc f b`
for every `f` continuous on the spectra of `a` and `b`. -/
theorem comp_cfc_eq_cfc_comp (ha : IsStarNormal a) (hb : IsStarNormal b) (h₁ : V ∘L a = b ∘L V)
    {f : ℂ → ℂ} (hfa : ContinuousOn f (spectrum ℂ a)) (hfb : ContinuousOn f (spectrum ℂ b)) :
    V ∘L cfc f a = cfc f b ∘L V := by
  have h₂ := comp_adjoint_eq_adjoint_comp ha hb h₁
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
