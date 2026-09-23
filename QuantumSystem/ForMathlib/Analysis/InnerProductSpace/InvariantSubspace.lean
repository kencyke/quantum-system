/-
Copyright (c) 2025 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Reducing subspaces for sets of bounded operators

This file provides a minimal API for invariant / reducing subspaces for a set of operators
`S : Set (H →L[ℂ] H)` on a Hilbert space `H`.  Invariance of `K` under a single operator `T` is
Mathlib's `K ∈ Module.End.invtSubmodule T`.

## Main definitions

* `IsReducing S K`: `K` is reducing for `S` if `K` is invariant under `T` and `T†` for all `T ∈ S`.

## Main results

* `commutes_starProjection_of_mem_invtSubmodule`: if `K` and `Kᗮ` are both invariant under `T`,
  then `T` commutes with the orthogonal projection onto `K`.
* `mem_invtSubmodule_of_commutes_starProjection`: conversely, if `T` commutes with
  `K.starProjection`, then `K` is invariant under `T`.
* `orthogonal_mem_invtSubmodule_of_commutes_starProjection`: if `T` commutes with
  `K.starProjection`, then `Kᗮ` is invariant under `T`.
* `orthogonal_mem_invtSubmodule_of_adjoint`: if `K` is invariant under `T†`, then
  `Kᗮ` is invariant under `T`.
* `starProjection_mem_centralizer_of_isReducing`: if `K` is reducing for `S`, then
  `K.starProjection ∈ Set.centralizer S`.
* `ActsNondegenerately S`: no nonzero vector is annihilated by every element of `S`; the
  hypothesis of the non-unital double commutant theorem.
-/

@[expose] public section

namespace InnerProductSpace

local notation "⟪" x ", " y "⟫" => inner ℂ x y
open scoped InnerProduct

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

section NonComplete

/-- If `K` and `Kᗮ` are both invariant under `T`, then `T` commutes with the orthogonal projection
onto `K` (as `K.starProjection`). -/
lemma commutes_starProjection_of_mem_invtSubmodule
    {T : H →L[ℂ] H} {K : Submodule ℂ H} [K.HasOrthogonalProjection]
    (hK : K ∈ Module.End.invtSubmodule (T : Module.End ℂ H))
    (hKorth : Kᗮ ∈ Module.End.invtSubmodule (T : Module.End ℂ H)) :
    T * K.starProjection = K.starProjection * T := by
  ext x
  -- Unfold multiplication as composition.
  -- After this, the goal is `T (P x) = P (T x)`.
  simp only [mul_apply_eq_comp]
  have hxK : K.starProjection x ∈ K := Submodule.starProjection_apply_mem (U := K) x
  have hxKorth : x - K.starProjection x ∈ Kᗮ := Submodule.sub_starProjection_mem_orthogonal (K := K) x
  have hTxK : T (K.starProjection x) ∈ K :=
    (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).1 hK _ hxK
  have hTxKorth : T (x - K.starProjection x) ∈ Kᗮ :=
    (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).1 hKorth _ hxKorth
  have h1 : K.starProjection (T (K.starProjection x)) = T (K.starProjection x) :=
    (Submodule.starProjection_eq_self_iff (K := K)).2 hTxK
  have h2 : K.starProjection (T (x - K.starProjection x)) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff (K := K)).2 hTxKorth
  have hxDecomp : K.starProjection x + (x - K.starProjection x) = x := by
    simp [sub_eq_add_neg]
  -- Rewrite `T x` as `T (P x + (x - P x))` and project.
  have hproj : K.starProjection (T x) = T (K.starProjection x) := by
    have hx1 :
        K.starProjection (T x) = K.starProjection (T (K.starProjection x + (x - K.starProjection x))) :=
      congrArg (fun z => K.starProjection (T z)) hxDecomp.symm
    calc
      K.starProjection (T x)
          = K.starProjection (T (K.starProjection x + (x - K.starProjection x))) := hx1
      _ = K.starProjection (T (K.starProjection x) + T (x - K.starProjection x)) := by
          exact
            congrArg (fun w => K.starProjection w)
              (T.map_add (K.starProjection x) (x - K.starProjection x))
      _ = K.starProjection (T (K.starProjection x)) + K.starProjection (T (x - K.starProjection x)) := by
          exact
            (K.starProjection.map_add (T (K.starProjection x)) (T (x - K.starProjection x)))
      _ = T (K.starProjection x) + K.starProjection (T (x - K.starProjection x)) := by
          simp [h1]
      _ = T (K.starProjection x) + 0 := by
          rw [h2]
      _ = T (K.starProjection x) := by
          simp
  exact hproj.symm

/-- If `T` commutes with the orthogonal projection onto `K`, then `K` is invariant under `T`. -/
lemma mem_invtSubmodule_of_commutes_starProjection
    {T : H →L[ℂ] H} {K : Submodule ℂ H} [K.HasOrthogonalProjection]
    (hcomm : K.starProjection * T = T * K.starProjection) :
    K ∈ Module.End.invtSubmodule (T : Module.End ℂ H) := by
  refine (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).2 ?_
  intro x hx
  have hxPx : K.starProjection x = x :=
    (Submodule.starProjection_eq_self_iff (K := K)).2 hx
  have hcomm_apply : (K.starProjection * T) x = (T * K.starProjection) x :=
    congrArg (fun f => f x) hcomm
  have hxTx : K.starProjection (T x) = T x := by
    simpa [mul_apply_eq_comp, hxPx] using hcomm_apply
  exact (Submodule.starProjection_eq_self_iff (K := K)).1 hxTx

/-- If `T` commutes with the orthogonal projection onto `K`, then `Kᗮ` is invariant under `T`. -/
lemma orthogonal_mem_invtSubmodule_of_commutes_starProjection
    {T : H →L[ℂ] H} {K : Submodule ℂ H} [K.HasOrthogonalProjection]
    (hcomm : K.starProjection * T = T * K.starProjection) :
    Kᗮ ∈ Module.End.invtSubmodule (T : Module.End ℂ H) := by
  refine (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).2 ?_
  intro y hy
  have hyPy : K.starProjection y = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff (K := K)).2 hy
  have hcomm_apply : (K.starProjection * T) y = (T * K.starProjection) y :=
    congrArg (fun f => f y) hcomm
  have hyTy : K.starProjection (T y) = 0 := by
    simpa [mul_apply_eq_comp, hyPy] using hcomm_apply
  exact (Submodule.starProjection_apply_eq_zero_iff (K := K)).1 hyTy

end NonComplete

section WithComplete

variable [CompleteSpace H]

/-- A subspace `K` is reducing for a set of operators `S` if it is invariant under every operator
in `S` and also invariant under every adjoint operator. -/
def IsReducing (S : Set (H →L[ℂ] H)) (K : Submodule ℂ H) : Prop :=
  ∀ T ∈ S, K ∈ Module.End.invtSubmodule (T : Module.End ℂ H) ∧
    K ∈ Module.End.invtSubmodule ((T†) : Module.End ℂ H)

/-- If `K` is invariant under `T†`, then `Kᗮ` is invariant under `T`. -/
lemma orthogonal_mem_invtSubmodule_of_adjoint
    {T : H →L[ℂ] H} {K : Submodule ℂ H}
    (hK : K ∈ Module.End.invtSubmodule ((T†) : Module.End ℂ H)) :
    Kᗮ ∈ Module.End.invtSubmodule (T : Module.End ℂ H) := by
  -- Unfold to the pointwise characterization.
  refine (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).2 ?_
  intro y hy
  -- Show `T y ∈ Kᗮ` via the inner-product characterization.
  refine (K.mem_orthogonal (T y)).2 ?_
  intro x hx
  have hx' : (T†) x ∈ K :=
    (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).1 hK x hx
  -- `y ∈ Kᗮ` implies `⟪(T†) x, y⟫ = 0`, hence also `⟪x, T y⟫ = 0`.
  have hy0 : ⟪(T†) x, y⟫ = 0 :=
    (K.mem_orthogonal y).1 hy ((T†) x) hx'
  -- Use adjointness: `⟪(T†) x, y⟫ = ⟪x, T y⟫`.
  have hAdj : ⟪x, T y⟫ = ⟪(T†) x, y⟫ := by
    -- `adjoint_inner_left` is: `⟪(T†) y, x⟫ = ⟪y, T x⟫`.
    simpa using (ContinuousLinearMap.adjoint_inner_left (A := T) (x := y) (y := x)).symm
  exact hAdj.trans hy0

/-- If `K` is reducing for `S`, then the orthogonal projection onto `K` lies in the commutant
(`Set.centralizer S`). -/
lemma starProjection_mem_centralizer_of_isReducing
    (S : Set (H →L[ℂ] H)) (K : Submodule ℂ H) [K.HasOrthogonalProjection]
    (hK : IsReducing S K) : K.starProjection ∈ Set.centralizer S := by
  intro T hT
  have hInv : K ∈ Module.End.invtSubmodule (T : Module.End ℂ H) := (hK T hT).1
  have hInvAdj : K ∈ Module.End.invtSubmodule ((T†) : Module.End ℂ H) := (hK T hT).2
  have hInvOrth : Kᗮ ∈ Module.End.invtSubmodule (T : Module.End ℂ H) :=
    orthogonal_mem_invtSubmodule_of_adjoint (T := T) hInvAdj
  exact commutes_starProjection_of_mem_invtSubmodule (T := T) (K := K) hInv hInvOrth

end WithComplete

section Nondegenerate

/-- A set of operators `S` *acts non-degenerately* on `H` if the only vector annihilated by
every element of `S` is `0`.

This is the *joint-kernel* form of non-degeneracy. The operator-algebra literature usually states
it as "the span of `S • H` is dense in `H`"; the two agree when `S` is closed under `star`, and
only then. Without self-adjointness they come apart: `span {e₁₁, e₁₂} ⊆ M₂(ℂ)` has trivial joint
kernel but its range `ℂ • e₁` is not dense. Every
use in this development supplies a `NonUnitalStarSubalgebra`, where the readings coincide.

This is strictly weaker than `1 ∈ S` (see `actsNondegenerately_of_one_mem`): for example the
compact operators act non-degenerately on an infinite-dimensional `H` without containing `1`.
It is the hypothesis under which the double commutant theorem holds for a possibly non-unital
`*`-subalgebra. -/
def ActsNondegenerately (S : Set (H →L[ℂ] H)) : Prop :=
  ∀ x : H, (∀ T ∈ S, T x = 0) → x = 0

/-- A set of operators containing the identity acts non-degenerately. -/
lemma actsNondegenerately_of_one_mem {S : Set (H →L[ℂ] H)}
    (h : (1 : H →L[ℂ] H) ∈ S) : ActsNondegenerately S := by
  intro x hx
  simpa using hx 1 h

/-- Non-degeneracy is monotone: it passes from a set to any superset. -/
lemma ActsNondegenerately.mono {S S' : Set (H →L[ℂ] H)} (hSS' : S ⊆ S')
    (hS : ActsNondegenerately S) : ActsNondegenerately S' := by
  intro x hx
  exact hS x fun T hT => hx T (hSS' hT)

end Nondegenerate

end InnerProductSpace
