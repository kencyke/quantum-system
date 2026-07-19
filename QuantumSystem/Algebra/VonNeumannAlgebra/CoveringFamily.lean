module

public import QuantumSystem.Algebra.VonNeumannAlgebra.Comparison
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Towards the type I factor structure theorem: a covering family of minimal projections

For a type I factor `N` with minimal projection `e`, this file produces (by Zorn's lemma and the
comparison theorem `IsMinimalProjection.mvNSub_of_isFactor`) a family of mutually orthogonal
projections, each Murray–von Neumann equivalent to `e`, whose ranges span densely — the
projection-theoretic backbone `Σ eᵢ = 1` of the structure theorem `N ≅ B(H₁) ⊗̄ 1`.

The spatial identification (Hilbert sum and `U • N = B(H₁) ⊗̄ 1`) is a further step.

The dense span is expressed as
`(Submodule.span ℂ {y | ∃ f ∈ F, ∃ x, f x = y}).topologicalClosure = ⊤`, i.e. the closed linear
span of the union of the ranges is the whole space; this is the operator-friendly form of
`⨆ᵢ ranges = 1` and matches the central-support construction `IsFactor.exists_mul_ne`.

## Main definitions

* `VonNeumannAlgebra.OrthEquivFam N e F` — `F` is a set of pairwise-orthogonal nonzero projections
  in `N`, each Murray–von Neumann equivalent to `e`.

## Main results

* `VonNeumannAlgebra.IsFactor.exists_orthEquivFam_top` — in a factor, there is a maximal such
  family whose ranges have dense span.
-/

@[expose] public section

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The range projection of a Murray–von Neumann equivalence with nonzero source is nonzero. -/
lemma MvNEquiv.ne_zero {N : VonNeumannAlgebra H} {p q : H →L[ℂ] H}
    (h : p ∼[N] q) (hp : p ≠ 0) : q ≠ 0 := by
  obtain ⟨v, _, hvpi, hvp, hvq⟩ := h
  intro hq0
  apply hp
  have hv0 : v = 0 := by
    have hpi : v * star v * v = v := hvpi
    rw [hvq, hq0, zero_mul] at hpi
    exact hpi.symm
  rw [← hvp, hv0]; simp

/-- **Minimality transports along Murray–von Neumann equivalence.** If `e` is a minimal projection
and `e ∼[N] p`, then `p` is minimal: with `v⋆v = e` and `vv⋆ = p`, the corner computes as
`p a p = v (e (v⋆ a v) e) v⋆ = c • v e v⋆ = c • p`. -/
lemma IsMinimalProjection.of_mvNEquiv {N : VonNeumannAlgebra H} {e p : H →L[ℂ] H}
    (he : IsMinimalProjection N e) (h : e ∼[N] p) : IsMinimalProjection N p := by
  have hpproj : IsStarProjection p := h.isStarProjection_right
  have hp0 : p ≠ 0 := h.ne_zero he.2.2.1
  obtain ⟨v, hvN, hvpi, hvp, hvq⟩ := h
  have hpN : p ∈ N := by rw [← hvq]; exact mul_mem hvN (star_mem hvN)
  have hve : v * e = v := by rw [← hvp]; exact IsPartialIsometry.mul_source hvpi
  have hev : e * star v = star v := by
    have := congrArg star hve
    rwa [star_mul, he.1.isSelfAdjoint.star_eq] at this
  refine ⟨hpproj, hpN, hp0, fun a haN => ?_⟩
  obtain ⟨c, hc⟩ := he.2.2.2 (star v * a * v) (mul_mem (mul_mem (star_mem hvN) haN) hvN)
  refine ⟨c, ?_⟩
  calc p * a * p
      = (v * star v) * a * (v * star v) := by rw [hvq]
    _ = (v * e) * (star v * a * v) * (e * star v) := by
        rw [hve, hev]; simp only [mul_assoc]
    _ = v * (e * (star v * a * v) * e) * star v := by simp only [mul_assoc]
    _ = v * (c • e) * star v := by rw [hc]
    _ = c • (v * e * star v) := by simp only [mul_smul_comm, smul_mul_assoc]
    _ = c • p := by rw [hve, hvq]

/-- A family of pairwise-orthogonal nonzero projections in `N`, each Murray–von Neumann equivalent
to `e`. -/
def OrthEquivFam (N : VonNeumannAlgebra H) (e : H →L[ℂ] H) (F : Set (H →L[ℂ] H)) : Prop :=
  (∀ p ∈ F, IsStarProjection p ∧ p ∈ N ∧ p ≠ 0 ∧ e ∼[N] p) ∧
    F.Pairwise (fun p q => p * q = 0)

/-- When `e` is minimal, every member of an `OrthEquivFam` for `e` is itself a minimal
projection, since minimality transports along `∼[N]` (`IsMinimalProjection.of_mvNEquiv`). -/
lemma OrthEquivFam.isMinimalProjection_of_mem {N : VonNeumannAlgebra H} {e : H →L[ℂ] H}
    {F : Set (H →L[ℂ] H)} (hF : OrthEquivFam N e F) (he : IsMinimalProjection N e)
    {p : H →L[ℂ] H} (hp : p ∈ F) : IsMinimalProjection N p :=
  he.of_mvNEquiv (hF.1 p hp).2.2.2

/-- By Zorn's lemma, there is a maximal orthogonal family of `e`-equivalent projections. -/
lemma exists_maximal_orthEquivFam (N : VonNeumannAlgebra H) (e : H →L[ℂ] H) :
    ∃ F, OrthEquivFam N e F ∧ ∀ G, OrthEquivFam N e G → F ⊆ G → G ⊆ F := by
  obtain ⟨F, hFmax⟩ := zorn_subset {F | OrthEquivFam N e F} (by
    intro c hcsub hchain
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    · rintro p ⟨s, hsc, hps⟩; exact (hcsub hsc).1 p hps
    · rintro p ⟨s, hsc, hps⟩ q ⟨t, htc, hqt⟩ hpq
      rcases hchain.total hsc htc with h | h
      · exact (hcsub htc).2 (h hps) hqt hpq
      · exact (hcsub hsc).2 hps (h hqt) hpq)
  exact ⟨F, hFmax.1, fun G hG hFG => hFmax.2 hG hFG⟩

/-- The orthogonal projection onto the closed span of the ranges of an `OrthEquivFam` lies in `N`,
because that subspace is invariant under the commutant `N'`: for `y ∈ N'` and `f ∈ F ⊆ N`,
`y (f x) = (y f) x = (f y) x = f (y x)` lies in the range of `f`. -/
lemma OrthEquivFam.starProjection_mem {N : VonNeumannAlgebra H} {e : H →L[ℂ] H}
    {F : Set (H →L[ℂ] H)} (hF : OrthEquivFam N e F) :
    (Submodule.span ℂ {y | ∃ f ∈ F, ∃ x, f x = y}).topologicalClosure.starProjection ∈ N := by
  set S : Set H := {y | ∃ f ∈ F, ∃ x, f x = y} with hS
  set M : Submodule ℂ H := (Submodule.span ℂ S).topologicalClosure with hM
  set p : H →L[ℂ] H := M.starProjection with hp
  have hpproj : IsStarProjection p := isStarProjection_starProjection
  rw [IsStarProjection.mem_iff hpproj N]
  intro y hyN'
  rw [hp, Submodule.range_starProjection]
  have hcl : IsClosed ((M.comap (y : H →ₗ[ℂ] H)) : Set H) := by
    rw [Submodule.comap_coe]
    exact ((Submodule.span ℂ S).isClosed_topologicalClosure).preimage y.continuous
  have hle : M ≤ M.comap (y : H →ₗ[ℂ] H) := by
    refine Submodule.topologicalClosure_minimal (Submodule.span ℂ S) ?_ hcl
    rw [Submodule.span_le]
    rintro s ⟨f, hf, x, rfl⟩
    simp only [Submodule.comap_coe, Set.mem_preimage, SetLike.mem_coe, ContinuousLinearMap.coe_coe]
    have hfy : f * y = y * f := mem_commutant_iff.mp hyN' f (hF.1 f hf).2.1
    rw [show y (f x) = (y * f) x from rfl, ← hfy]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨f, hf, y x, rfl⟩)
  exact hle

/-- **Covering family of minimal projections (factor case).** In a factor, there is a family `F`
of pairwise-orthogonal nonzero projections in `N`, each equivalent to the minimal projection `e`,
whose ranges span densely: the closed linear span of the union of their ranges is `⊤`. This is the
`Σ eᵢ = 1` input of the type I structure theorem.

The proof takes a *maximal* such family `F` (Zorn) and lets `p` be the orthogonal projection onto
the closed span `M` of the ranges; `p ∈ N`. If `M ≠ ⊤` then `r = 1 - p` is a nonzero projection in
`N`, so by the comparison theorem some nonzero `q' ≼ r` is equivalent to `e`; `q'` is orthogonal to
every `f ∈ F`, contradicting maximality. -/
theorem IsFactor.exists_orthEquivFam_top [Nontrivial H] {N : VonNeumannAlgebra H}
    (hN : IsFactor N) {e : H →L[ℂ] H} (he : IsMinimalProjection N e) :
    ∃ F : Set (H →L[ℂ] H), OrthEquivFam N e F ∧
      (Submodule.span ℂ {y | ∃ f ∈ F, ∃ x, f x = y}).topologicalClosure = ⊤ := by
  obtain ⟨F, hF, hFmax⟩ := exists_maximal_orthEquivFam N e
  refine ⟨F, hF, ?_⟩
  set S : Set H := {y | ∃ f ∈ F, ∃ x, f x = y} with hS
  set M : Submodule ℂ H := (Submodule.span ℂ S).topologicalClosure with hM
  set p : H →L[ℂ] H := M.starProjection with hp
  have hpproj : IsStarProjection p := isStarProjection_starProjection
  have hpN : p ∈ N := hF.starProjection_mem
  have hpf : ∀ f ∈ F, p * f = f := by
    intro f hf
    ext x
    simp only [ContinuousLinearMap.mul_apply, hp]
    rw [Submodule.starProjection_eq_self_iff]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨f, hf, x, rfl⟩)
  by_contra hMtop
  set r : H →L[ℂ] H := 1 - p with hr
  have hrproj : IsStarProjection r := by
    refine ⟨?_, ?_⟩
    · change (1 - p) * (1 - p) = 1 - p
      rw [mul_sub, sub_mul, sub_mul, one_mul, one_mul, mul_one, hpproj.isIdempotentElem,
        sub_self, sub_zero]
    · change star (1 - p) = 1 - p
      rw [star_sub, star_one, hpproj.isSelfAdjoint.star_eq]
  have hrN : r ∈ N := by rw [hr]; exact sub_mem (one_mem _) hpN
  have hr0 : r ≠ 0 := by
    intro h
    apply hMtop
    have hp1 : p = 1 := by rw [hr, sub_eq_zero] at h; exact h.symm
    have hMrange : M = p.range := (Submodule.range_starProjection M).symm
    rw [hMrange, hp1]
    exact Submodule.eq_top_iff'.2 fun y => ⟨y, rfl⟩
  obtain ⟨q', hq'N, hrq', heq'⟩ := he.mvNSub_of_isFactor hN hrproj hrN hr0
  have hq'proj : IsStarProjection q' := heq'.isStarProjection_right
  have hq'0 : q' ≠ 0 := heq'.ne_zero he.2.2.1
  have hpq' : p * q' = 0 := by
    have h := hrq'
    rw [hr, sub_mul, one_mul, sub_eq_self] at h
    exact h
  have horth : ∀ f ∈ F, q' * f = 0 ∧ f * q' = 0 := by
    intro f hf
    have hq'p : q' * p = 0 := by
      have h := congrArg star hpq'
      rwa [star_mul, hq'proj.isSelfAdjoint.star_eq, hpproj.isSelfAdjoint.star_eq, star_zero] at h
    have h1 : q' * f = 0 := by
      calc q' * f = q' * (p * f) := by rw [hpf f hf]
        _ = (q' * p) * f := by rw [mul_assoc]
        _ = 0 := by rw [hq'p, zero_mul]
    refine ⟨h1, ?_⟩
    have h := congrArg star h1
    rwa [star_mul, (hF.1 f hf).1.isSelfAdjoint.star_eq, hq'proj.isSelfAdjoint.star_eq,
      star_zero] at h
  have hq'notF : q' ∉ F := fun hq'F =>
    hq'0 (by have := (horth q' hq'F).1; rwa [hq'proj.isIdempotentElem] at this)
  have hbigger : OrthEquivFam N e (insert q' F) := by
    refine ⟨?_, ?_⟩
    · rintro x (rfl | hx)
      · exact ⟨hq'proj, hq'N, hq'0, heq'⟩
      · exact hF.1 x hx
    · rintro x (rfl | hx) z (rfl | hz) hxz
      · exact absurd rfl hxz
      · exact (horth z hz).1
      · exact (horth x hx).2
      · exact hF.2 hx hz hxz
  have hsub := hFmax (insert q' F) hbigger (Set.subset_insert _ _)
  exact hq'notF (hsub (Set.mem_insert _ _))

end VonNeumannAlgebra
