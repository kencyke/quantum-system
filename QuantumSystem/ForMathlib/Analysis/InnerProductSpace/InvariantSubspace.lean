module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Reducing subspaces for sets of bounded operators

This file provides a minimal API for invariant / reducing subspaces for a set of operators
`S : Set (H →L[ℂ] H)` on a Hilbert space `H`.

## Main definitions

* `IsInvariant T K`: a subspace `K` is invariant under `T` if `T(K) ⊆ K`.
* `IsReducing S K`: `K` is reducing for `S` if `K` is invariant under `T` and `T†` for all `T ∈ S`.

## Main results

* `IsInvariant.iff_forall_mem`: pointwise characterization of invariance.
* `commutes_starProjection_of_invariant`: if `K` and `Kᗮ` are both invariant under `T`, then
  `T` commutes with the orthogonal projection onto `K`.
* `isInvariant_of_commutes_starProjection`: conversely, if `T` commutes with `K.starProjection`,
  then `K` is invariant under `T`.
* `isInvariant_orthogonal_of_commutes_starProjection`: if `T` commutes with `K.starProjection`,
  then `Kᗮ` is invariant under `T`.
* `orthogonalComplement_invariant_of_adjoint_invariant`: if `K` is invariant under `T†`, then
  `Kᗮ` is invariant under `T`.
* `starProjection_mem_centralizer_of_isReducing`: if `K` is reducing for `S`, then
  `K.starProjection ∈ Set.centralizer S`.
-/

@[expose] public section

namespace InnerProductSpace

local notation "⟪" x ", " y "⟫" => inner ℂ x y

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A subspace `K` is invariant under an operator `T` if `T(K) ⊆ K`. -/
def IsInvariant (T : H →L[ℂ] H) (K : Submodule ℂ H) : Prop :=
  K ∈ Module.End.invtSubmodule (T : Module.End ℂ H)

namespace IsInvariant

variable {T : H →L[ℂ] H} {K : Submodule ℂ H}

lemma iff_forall_mem : IsInvariant T K ↔ ∀ x ∈ K, T x ∈ K := by
  -- `Module.End.mem_invtSubmodule_iff_forall_mem_of_mem` is the pointwise characterization.
  simpa [IsInvariant] using
    (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem (f := (T : Module.End ℂ H)) (p := K))

end IsInvariant

section NonComplete

/-- If `K` and `Kᗮ` are both invariant under `T`, then `T` commutes with the orthogonal projection
onto `K` (as `K.starProjection`). -/
lemma commutes_starProjection_of_invariant
    {T : H →L[ℂ] H} {K : Submodule ℂ H} [K.HasOrthogonalProjection]
    (hK : IsInvariant T K) (hKorth : IsInvariant T Kᗮ) :
    T * K.starProjection = K.starProjection * T := by
  ext x
  -- Unfold multiplication as composition.
  -- After this, the goal is `T (P x) = P (T x)`.
  simp only [ContinuousLinearMap.mul_apply]
  have hxK : K.starProjection x ∈ K := Submodule.starProjection_apply_mem (U := K) x
  have hxKorth : x - K.starProjection x ∈ Kᗮ := Submodule.sub_starProjection_mem_orthogonal (K := K) x
  have hTxK : T (K.starProjection x) ∈ K :=
    (IsInvariant.iff_forall_mem (T := T) (K := K)).1 hK _ hxK
  have hTxKorth : T (x - K.starProjection x) ∈ Kᗮ :=
    (IsInvariant.iff_forall_mem (T := T) (K := Kᗮ)).1 hKorth _ hxKorth
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


lemma isInvariant_of_commutes_starProjection
    {T : H →L[ℂ] H} {K : Submodule ℂ H} [K.HasOrthogonalProjection]
    (hcomm : K.starProjection * T = T * K.starProjection) :
    IsInvariant T K := by
  refine (IsInvariant.iff_forall_mem (T := T) (K := K)).2 ?_
  intro x hx
  have hxPx : K.starProjection x = x :=
    (Submodule.starProjection_eq_self_iff (K := K)).2 hx
  have hcomm_apply : (K.starProjection * T) x = (T * K.starProjection) x :=
    congrArg (fun f => f x) hcomm
  have hxTx : K.starProjection (T x) = T x := by
    simpa [ContinuousLinearMap.mul_apply, hxPx] using hcomm_apply
  exact (Submodule.starProjection_eq_self_iff (K := K)).1 hxTx


lemma isInvariant_orthogonal_of_commutes_starProjection
    {T : H →L[ℂ] H} {K : Submodule ℂ H} [K.HasOrthogonalProjection]
    (hcomm : K.starProjection * T = T * K.starProjection) :
    IsInvariant T Kᗮ := by
  refine (IsInvariant.iff_forall_mem (T := T) (K := Kᗮ)).2 ?_
  intro y hy
  have hyPy : K.starProjection y = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff (K := K)).2 hy
  have hcomm_apply : (K.starProjection * T) y = (T * K.starProjection) y :=
    congrArg (fun f => f y) hcomm
  have hyTy : K.starProjection (T y) = 0 := by
    simpa [ContinuousLinearMap.mul_apply, hyPy] using hcomm_apply
  exact (Submodule.starProjection_apply_eq_zero_iff (K := K)).1 hyTy

end NonComplete

section WithComplete

variable [CompleteSpace H]

/-- A subspace `K` is reducing for a set of operators `S` if it is invariant under every operator
in `S` and also invariant under every adjoint operator. -/
def IsReducing (S : Set (H →L[ℂ] H)) (K : Submodule ℂ H) : Prop :=
  ∀ T ∈ S, IsInvariant T K ∧ IsInvariant (ContinuousLinearMap.adjoint T) K

/-- If `K` is invariant under `T†`, then `Kᗮ` is invariant under `T`. -/
lemma orthogonalComplement_invariant_of_adjoint_invariant
    {T : H →L[ℂ] H} {K : Submodule ℂ H}
  (hK : IsInvariant (ContinuousLinearMap.adjoint T) K) : IsInvariant T Kᗮ := by
  -- Unfold to the pointwise characterization.
  refine (IsInvariant.iff_forall_mem (T := T) (K := Kᗮ)).2 ?_
  intro y hy
  -- Show `T y ∈ Kᗮ` via the inner-product characterization.
  refine (K.mem_orthogonal (T y)).2 ?_
  intro x hx
  have hx' : (ContinuousLinearMap.adjoint T) x ∈ K :=
    (IsInvariant.iff_forall_mem (T := ContinuousLinearMap.adjoint T) (K := K)).1 hK x hx
  -- `y ∈ Kᗮ` implies `⟪(T†) x, y⟫ = 0`, hence also `⟪x, T y⟫ = 0`.
  have hy0 : ⟪(ContinuousLinearMap.adjoint T) x, y⟫ = 0 :=
    (K.mem_orthogonal y).1 hy ((ContinuousLinearMap.adjoint T) x) hx'
  -- Use adjointness: `⟪(T†) x, y⟫ = ⟪x, T y⟫`.
  have hAdj : ⟪x, T y⟫ = ⟪(ContinuousLinearMap.adjoint T) x, y⟫ := by
    -- `adjoint_inner_left` is: `⟪(T†) y, x⟫ = ⟪y, T x⟫`.
    simpa using (ContinuousLinearMap.adjoint_inner_left (A := T) (x := y) (y := x)).symm
  exact hAdj.trans hy0

/-- If `K` is reducing for `S`, then the orthogonal projection onto `K` lies in the commutant
(`Set.centralizer S`). -/
lemma starProjection_mem_centralizer_of_isReducing
    (S : Set (H →L[ℂ] H)) (K : Submodule ℂ H) [K.HasOrthogonalProjection]
    (hK : IsReducing S K) : K.starProjection ∈ Set.centralizer S := by
  intro T hT
  have hInv : IsInvariant T K := (hK T hT).1
  have hInvAdj : IsInvariant (ContinuousLinearMap.adjoint T) K := (hK T hT).2
  have hInvOrth : IsInvariant T Kᗮ :=
    orthogonalComplement_invariant_of_adjoint_invariant (T := T) hInvAdj
  exact commutes_starProjection_of_invariant (T := T) (K := K) hInv hInvOrth

end WithComplete

end InnerProductSpace
