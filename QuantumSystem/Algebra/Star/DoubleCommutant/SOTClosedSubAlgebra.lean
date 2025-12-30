module

public import QuantumSystem.Algebra.Star.DoubleCommutant.WOTClosedSubAlgebra
public import QuantumSystem.ForMathlib.Analysis.LocallyConvex.StrongOperatorTopology

/-!
# Double commutant theorem for SOT-closed *-subalgebras

This file proves the SOT version of the double commutant theorem by reducing to the WOT version.

## Main results

* `mem_sotClosure_of_mem_doubleCommutant`: any `T ∈ A''` lies in the SOT-closure of `A`.
  This is the key technical result, using diagonal amplification and the cyclic subspace argument.
* `isWOTClosed_of_isSOTClosed_starSubalgebra`: a SOT-closed *-subalgebra is WOT-closed.
* `doubleCommutant_eq_of_isSOTClosed`: if a *-subalgebra is SOT-closed, it equals its double
  commutant (the "hard half" of the SOT double commutant theorem).

## Strategy

The proof proceeds in two main steps:

1. **Double commutant membership implies SOT approximability**: For any `T ∈ A''` and any finite
   set of points `x₁, ..., xₙ ∈ H`, we show that the tuple `(Tx₁, ..., Txₙ)` lies in the closure
   of `{(Sx₁, ..., Sxₙ) | S ∈ A}`. This uses diagonal amplification: embed `A` into operators on
   `H^n`, show that `diagonal T` lies in the double commutant of the amplified algebra, hence
   preserves reducing subspaces, and apply the cyclic subspace argument.

2. **SOT-closed implies WOT-closed**: From step 1, any `T ∈ A''` lies in the SOT-closure of `A`
   (`mem_sotClosure_of_mem_doubleCommutant`). If `A` is SOT-closed, this means `A'' ⊆ A`,
   hence `A = A''`. Since double commutants are WOT-closed, `A` is WOT-closed.

The final theorem `doubleCommutant_eq_of_isSOTClosed` then reduces to the WOT version via
`isWOTClosed_of_isSOTClosed_starSubalgebra`.
-/

@[expose] public section

namespace SOTClosedSubalgebra

open InnerProductSpace StrongOperatorTopology WeakOperatorTopology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "B" => (H →L[ℂ] H)
local notation "BSOT" => ContinuousLinearMapSOT H
local notation "BWOT" => (H →WOT[ℂ] H)

/-- Any element of the double commutant of a *-subalgebra lies in the SOT-closure of the algebra.

This is the key technical result: we show that for any `T ∈ A''` and any finite set of points
`x₁, ..., xₙ ∈ H`, the tuple `(Tx₁, ..., Txₙ)` lies in the closure of `{(Sx₁, ..., Sxₙ) | S ∈ A}`.
This uses diagonal amplification and the cyclic subspace argument.
-/
lemma mem_sotClosure_of_mem_doubleCommutant (A : StarSubalgebra ℂ B) (T : B)
    (hT : T ∈ Set.centralizer (Set.centralizer (A : Set B))) :
    (⟨T⟩ : BSOT) ∈ closure (Set.toSOT (H := H) (A : Set B)) := by
  -- The SOT is induced by inducingFn : BSOT → (H → H).
  -- Use the criterion: T ∈ closure(S) iff inducingFn T ∈ closure(inducingFn '' S) in product topology
  rw [ContinuousLinearMapSOT.isInducing_inducingFn.closure_eq_preimage_closure_image]
  simp only [Set.mem_preimage]
  -- Need to show T (as a function H → H) is in the closure of {S : H → H | S ∈ A}
  -- in the product topology on H → H.
  rw [mem_closure_iff_nhds]
  intro U hU
  -- U is a neighborhood of (T ·) in the product topology
  rw [nhds_pi] at hU
  rw [Filter.mem_pi] at hU
  obtain ⟨I, hI_finite, t, ht, htU⟩ := hU
  -- I is a finite set of points in H, t x is a neighborhood of T x for each x
  -- htU says: if S x ∈ t x for all x ∈ I, then S ∈ U
  classical
  by_cases hI_nonempty : I.Nonempty
  · -- I is nonempty
    -- For each x ∈ I, find ε_x > 0 such that B(Tx, ε_x) ⊆ t x
    have heps : ∀ x ∈ I, ∃ ε > 0, Metric.ball (T x) ε ⊆ t x := fun x hx => by
      have hmem : T x ∈ t x := mem_of_mem_nhds (ht x)
      exact Metric.nhds_basis_ball.mem_iff.mp (ht x)
    -- Choose ε as the min of all ε_x
    let I_fin : Finset H := hI_finite.toFinset
    have hI_eq : (I_fin : Set H) = I := hI_finite.coe_toFinset
    have hI_fin_ne : I_fin.Nonempty := by
      rw [← Finset.coe_nonempty, hI_eq]
      exact hI_nonempty
    -- Use choose on finset elements
    have heps' : ∀ x : I_fin, ∃ ε > 0, Metric.ball (T x.val) ε ⊆ t x.val :=
      fun x => heps x.val (hI_eq ▸ x.2)
    -- The finite set I gives us n points; use amplification to H^n
    let n := I_fin.card
    have hn : 0 < n := Finset.card_pos.mpr hI_fin_ne
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    let e : Fin n ≃ I_fin := Fintype.equivOfCardEq (by simp [n])
    let xVec : Fin n → H := fun i => (e i).val
    let x_amp : Hn (H := H) n := (WithLp.equiv _ _).symm xVec
    let Aamp : StarSubalgebra ℂ (Hn (H := H) n →L[ℂ] Hn (H := H) n) :=
      A.map (diagonalStarAlgHom (H := H) n)
    -- Choose a uniform ε
    let ε := I_fin.attach.inf' hI_fin_ne.attach (fun x => (heps' x).choose)
    have hε_pos' : ε > 0 := by
      change 0 < I_fin.attach.inf' hI_fin_ne.attach (fun x => (heps' x).choose)
      rw [Finset.lt_inf'_iff]
      intro x _
      exact (heps' x).choose_spec.1
    have hε_ball : ∀ x : I_fin, Metric.ball (T x.val) ε ⊆ t x.val := fun x => by
      have hle : ε ≤ (heps' x).choose := Finset.inf'_le _ (Finset.mem_attach _ x)
      intro y hy
      apply (heps' x).choose_spec.2
      exact Metric.ball_subset_ball hle hy
    -- T^(n) ∈ (A^(n))''
    have hTn : diagonal (H := H) (n := n) T ∈
        Set.centralizer (Set.centralizer (Aamp : Set _)) := by
      have hdiag := diagonal_mem_double_commutant (H := H) (n := n) (A := (A : Set _)) (T := T) hT
      simp only [StarSubalgebra.coe_map, Aamp, diagonalStarAlgHom]
      simpa using hdiag
    -- T^(n) preserves reducing subspaces of A^(n)
    have hPres : WOTClosedSubalgebra.PreservesReducingSubspaces (H := Hn (H := H) n)
        (Aamp : Set _) (diagonal (H := H) (n := n) T) :=
      WOTClosedSubalgebra.preservesReducingSubspaces_of_mem_centralizer_centralizer
        (H := Hn (H := H) n) _ hTn
    -- T^(n) x ∈ cyclicSubspace A^(n) x
    have hxmem : diagonal (H := H) (n := n) T x_amp ∈
        WOTClosedSubalgebra.cyclicSubspace (H := Hn (H := H) n) Aamp x_amp :=
      WOTClosedSubalgebra.mem_cyclicSubspace_of_preservesReducingSubspaces
        (H := Hn (H := H) n) Aamp hPres x_amp
    -- The set {a x | a ∈ Aamp} equals {diagonal S x | S ∈ A}
    have hAamp_orbit : Set.range (fun a : Aamp => (a : Hn (H := H) n →L[ℂ] Hn (H := H) n) x_amp) =
        {y | ∃ S ∈ (A : Set _), y = diagonal (H := H) (n := n) S x_amp} := by
      ext y
      simp only [Set.mem_range, Set.mem_setOf_eq]
      constructor
      · rintro ⟨⟨a, ha⟩, rfl⟩
        simp only [Aamp, StarSubalgebra.mem_map, diagonalStarAlgHom, StarAlgHom.coe_mk',
          AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk] at ha
        rcases ha with ⟨S, hS, rfl⟩
        exact ⟨S, hS, rfl⟩
      · rintro ⟨S, hS, rfl⟩
        refine ⟨⟨diagonal (H := H) (n := n) S, ?_⟩, rfl⟩
        simp only [Aamp, StarSubalgebra.mem_map, diagonalStarAlgHom, StarAlgHom.coe_mk',
          AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
        exact ⟨S, hS, rfl⟩
    -- The map S ↦ diagonal S x_amp is linear, so the orbit is a submodule
    let evalAt : (Hn (H := H) n →L[ℂ] Hn (H := H) n) →ₗ[ℂ] Hn (H := H) n :=
      { toFun := fun S => S x_amp
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let diagMap : (H →L[ℂ] H) →ₗ[ℂ] Hn (H := H) n →L[ℂ] Hn (H := H) n :=
      (diagonalStarAlgHom (H := H) n).toLinearMap
    -- The orbit set equals the image of A.toSubmodule under the composed linear map
    have hset_is_image : {y | ∃ S ∈ (A : Set _), y = diagonal (H := H) (n := n) S x_amp} =
        A.toSubmodule.map (evalAt.comp diagMap) := by
      ext y
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨S, hS, rfl⟩
        exact ⟨S, hS, rfl⟩
      · rintro ⟨S, hS, rfl⟩
        exact ⟨S, hS, rfl⟩
    -- The image of a submodule under a linear map is a submodule, so span of it equals itself
    have hspan_eq : Submodule.span ℂ {y | ∃ S ∈ (A : Set _), y = diagonal (H := H) (n := n) S x_amp} =
        A.toSubmodule.map (evalAt.comp diagMap) := by
      rw [hset_is_image, Submodule.span_eq]
    -- cyclicSubspace uses range of Aamp elements, rewrite using our orbit equality
    rw [WOTClosedSubalgebra.cyclicSubspace, hAamp_orbit, hspan_eq] at hxmem
    -- hxmem : diagonal T x_amp ∈ (A.toSubmodule.map (evalAt ∘ₗ diagMap)).topologicalClosure
    -- Since we're in the topological closure, we can approximate
    have hxmem' : diagonal (H := H) (n := n) T x_amp ∈ closure {y | ∃ S ∈ (A : Set _),
        y = diagonal (H := H) (n := n) S x_amp} := by
      rw [hset_is_image, ← Submodule.topologicalClosure_coe]
      exact hxmem
    rw [Metric.mem_closure_iff] at hxmem'
    obtain ⟨y, hy, hdist⟩ := hxmem' ε hε_pos'
    obtain ⟨S, hS, rfl⟩ := hy
    -- S ∈ A and ‖diagonal T x_amp - diagonal S x_amp‖ < ε
    -- Show S is in the neighborhood U
    use S
    constructor
    · -- Show S ∈ U
      apply htU
      -- Need S · ∈ Set.pi I t, i.e., for all z ∈ I, S z ∈ t z
      intro z hz_in_I
      -- z ∈ I means z = xVec j for some j
      have hz_in_fin : z ∈ I_fin := hI_finite.mem_toFinset.mpr hz_in_I
      have ⟨j, hj⟩ := e.surjective ⟨z, hz_in_fin⟩
      have hzj : xVec j = z := by simp only [xVec, hj]
      -- Need S z ∈ t z
      apply hε_ball ⟨z, hz_in_fin⟩
      rw [Metric.mem_ball]
      -- ‖S z - T z‖ ≤ ‖(Sx₁,...,Sxₙ) - (Tx₁,...,Txₙ)‖ < ε
      have hcomp : ∀ i, (diagonal (H := H) (n := n) T x_amp - diagonal (H := H) (n := n) S x_amp).ofLp i =
          T (xVec i) - S (xVec i) := by
        intro i
        rw [WithLp.ofLp_sub, Pi.sub_apply, diagonal_apply, diagonal_apply]
        simp only [x_amp, xVec, WithLp.equiv_symm_apply]
      have hnorm_ineq : ‖S z - T z‖ ≤ dist (diagonal (H := H) (n := n) T x_amp)
          (diagonal (H := H) (n := n) S x_amp) := by
        rw [dist_eq_norm, ← hzj]
        have hcomp_j : (diagonal (H := H) (n := n) T x_amp - diagonal (H := H) (n := n) S x_amp).ofLp j =
            T (xVec j) - S (xVec j) := hcomp j
        rw [norm_sub_rev (S (xVec j)) (T (xVec j)), ← hcomp_j]
        exact PiLp.norm_apply_le _ j
      rw [dist_eq_norm]
      calc ‖S z - T z‖
        _ ≤ dist (diagonal (H := H) (n := n) T x_amp) (diagonal (H := H) (n := n) S x_amp) := hnorm_ineq
        _ < ε := hdist
    · -- Show S ∈ inducingFn '' Set.toSOT A
      simp only [Set.mem_image]
      exact ⟨⟨S⟩, Set.mem_toSOT_iff.mpr hS, rfl⟩
  · -- I is empty, so the pi set is the whole space
    simp only [Set.not_nonempty_iff_eq_empty] at hI_nonempty
    use (1 : H →L[ℂ] H)
    constructor
    · apply htU
      rw [hI_nonempty, Set.empty_pi]
      exact Set.mem_univ _
    · exact ⟨⟨1⟩, Set.mem_toSOT_iff.mpr A.one_mem, rfl⟩

theorem isWOTClosed_of_isSOTClosed_starSubalgebra (A : StarSubalgebra ℂ B)
    (hSOT : IsSOTClosed (H := H) (A : Set B)) :
    IsWOTClosed (H := H) (A : Set B) := by
  -- Strategy: Show A = A'', then use that A'' is WOT-closed.
  -- Key: any T ∈ A'' lies in SOT-closure(A), so if A is SOT-closed, then T ∈ A.
  have hA_eq_Acc : (A : Set B) = Set.centralizer (Set.centralizer (A : Set B)) := by
    apply Set.eq_of_subset_of_subset Set.subset_centralizer_centralizer
    intro T hT
    -- T ∈ A'' → T ∈ SOT-closure(A) → T ∈ A (since A is SOT-closed)
    have hT_in_SOT := mem_sotClosure_of_mem_doubleCommutant A T hT
    simp only [Set.toSOT] at hT_in_SOT
    rwa [IsClosed.closure_eq hSOT, Set.mem_setOf_eq] at hT_in_SOT
  rw [hA_eq_Acc]
  exact isWOTClosed_centralizer_centralizer (H := H) (A : Set B)

/-- The double commutant theorem (hard half) for SOT-closed *-subalgebras.

A SOT-closed *-subalgebra equals its double commutant.
-/
theorem doubleCommutant_eq_of_isSOTClosed (A : StarSubalgebra ℂ B)
    (hSOT : IsSOTClosed (H := H) (A : Set B)) :
    Set.centralizer (Set.centralizer (A : Set B)) = (A : Set B) := by
  -- Reduce to the WOT version.
  have hWOT : IsWOTClosed (H := H) (A : Set B) := isWOTClosed_of_isSOTClosed_starSubalgebra A hSOT
  exact WOTClosedSubalgebra.doubleCommutant_eq_of_isWOTClosed (H := H) A hWOT

end SOTClosedSubalgebra
