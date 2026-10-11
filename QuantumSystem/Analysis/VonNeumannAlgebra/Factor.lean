/-
Copyright (c) 2025 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.Projection
public import QuantumSystem.Analysis.VonNeumannAlgebra.BoundedOperators
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.RankOne
public import QuantumSystem.ForMathlib.Analysis.VonNeumannAlgebra.Commutant

/-!
# Factors and central projections

A von Neumann algebra `N` is a **factor** when its centre `N ∩ N′` is trivial. This file defines
factors and the central projections, the projections of the centre, and proves the facts about
them that the comparison theory of projections needs. It is organised in four parts:

1. **Factors** — the definition `IsFactor`, and `𝓑(H)` as the first example of a factor.
2. **Central projections** — projections in the centre `N ∩ N'`; in a factor these are trivial,
   the seed of the central-support lemma `IsFactor.exists_mul_ne`.
3. **Invariance under spatial isomorphisms** `N ↦ U N U⋆`.
4. **Invariance under abstract `⋆`-isomorphisms** `N ≃⋆ₐ M`: being a factor is intrinsic to the
   `⋆`-algebra `N`.

Minimal and abelian projections are defined in
`QuantumSystem.Analysis.VonNeumannAlgebra.MinimalProjection`, and Murray–von Neumann equivalence
and the comparison of projections in
`QuantumSystem.Analysis.VonNeumannAlgebra.MurrayVonNeumann`.

## Main definitions

* `VonNeumannAlgebra.IsFactor N` — `N` has trivial centre: every element of `N ∩ N'` is a scalar.
* `VonNeumannAlgebra.IsCentralProjection N e` — `e` is a projection in `N ∩ N'`.

## Main results

* `VonNeumannAlgebra.isFactor_boundedLinearOperators` — `𝓑(H)` is a factor.
* `VonNeumannAlgebra.IsFactor.commutant` / `isFactor_commutant_iff` — `N` is a factor iff `N′` is.
* `VonNeumannAlgebra.IsFactor.central_projection_eq` — in a factor every central projection is
  `0` or `1`.
* `VonNeumannAlgebra.isStarProjection_mem_commutant_iff` — a star projection lies in the commutant
  `N'` exactly when its range is invariant under every element of `N` (the projection–reducing
  subspace bridge used to build central supports).
* `VonNeumannAlgebra.IsFactor.exists_mul_ne` — the central-support lemma: in a factor, a nonzero
  `q` meets the `N`-orbit of any nonzero `e ∈ N`.
* `VonNeumannAlgebra.isFactor_conj_iff` — factors are invariant under spatial isomorphisms
  `N ↦ U N U⋆`.
* `VonNeumannAlgebra.isFactor_iff_of_starAlgEquiv` — more generally, they are invariant under
  abstract `⋆`-isomorphisms `N ≃⋆ₐ M`, being intrinsic to the `⋆`-algebra
  (`VonNeumannAlgebra.isFactor_iff_forall_commute`).
-/

@[expose] public section

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Factors -/

/-- A von Neumann algebra `N` is a **factor** when its centre is trivial: every operator lying in
both `N` and its commutant is a scalar multiple of the identity. -/
def IsFactor (N : VonNeumannAlgebra H) : Prop :=
  ∀ x : H →L[ℂ] H, x ∈ N → x ∈ N.commutant → ∃ c : ℂ, x = c • 1

/-- **The commutant of a factor is a factor.** The centre `N ∩ N′` is also the centre
`N′ ∩ N″` of the commutant, since `N″ = N`. -/
theorem IsFactor.commutant {N : VonNeumannAlgebra H} (hN : IsFactor N) : IsFactor N.commutant :=
  fun x hx hx' => hN x (by rwa [VonNeumannAlgebra.commutant_commutant] at hx') hx

/-- A von Neumann algebra is a factor iff its commutant is. -/
lemma isFactor_commutant_iff {N : VonNeumannAlgebra H} : IsFactor N.commutant ↔ IsFactor N :=
  ⟨fun h => VonNeumannAlgebra.commutant_commutant N ▸ h.commutant, IsFactor.commutant⟩

/-- **`B(H)` is a factor.** The centre of the full algebra is trivial: an operator lying in the
commutant of `𝓑(H)` commutes with every operator, in particular with every rank-one operator, hence
is a scalar (`ContinuousLinearMap.exists_eq_smul_one_of_forall_rankOne_comm`). -/
theorem isFactor_boundedLinearOperators : IsFactor 𝓑(H) := by
  intro x _ hxComm
  rw [VonNeumannAlgebra.mem_commutant_iff] at hxComm
  refine ContinuousLinearMap.exists_eq_smul_one_of_forall_rankOne_comm (fun a b => ?_)
  have hg := hxComm (InnerProductSpace.rankOne ℂ a b) (mem_boundedLinearOperators _)
  rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def] at hg
  exact hg.symm

omit [CompleteSpace H] in
/-- **A nonzero operator witnesses a nonzero space.** On a subsingleton `H` every operator is `0`,
so exhibiting any `x ≠ 0` already gives `Nontrivial H`. This is why almost none of the results
below need `[Nontrivial H]` as a hypothesis: they carry a nonzero projection, which supplies it.
The exceptions are the statements that quantify over projections without asserting one exists
(`IsFactor.isTypeI_iff_exists_isMinimalProjection`, `isTypeIFactor_iff_isFactor_and_isTypeI`) and
the ones producing a minimal projection of `𝓑(H)` out of nothing. -/
lemma nontrivial_of_ne_zero {x : H →L[ℂ] H} (hx : x ≠ 0) : Nontrivial H :=
  let ⟨y, hy⟩ := ContinuousLinearMap.exists_ne_zero hx
  ⟨⟨x y, 0, hy⟩⟩

/-! ### Central projections -/

/-- A **central projection** of `N`: a star projection lying in both `N` and its commutant
(equivalently, in the centre `N ∩ N'`). -/
def IsCentralProjection (N : VonNeumannAlgebra H) (e : H →L[ℂ] H) : Prop :=
  IsStarProjection e ∧ e ∈ N ∧ e ∈ N.commutant

/-- `0` is a central projection. -/
lemma isCentralProjection_zero (N : VonNeumannAlgebra H) : IsCentralProjection N 0 :=
  ⟨IsStarProjection.zero _, zero_mem _, zero_mem _⟩

/-- `1` is a central projection. -/
lemma isCentralProjection_one (N : VonNeumannAlgebra H) : IsCentralProjection N 1 :=
  ⟨IsStarProjection.one _, one_mem _, one_mem _⟩

/-- In a factor, every central projection is trivial: it is `0` or `1`. This is the
projection-level form of the triviality of the centre. On a subsingleton `H` the conclusion is
vacuous (every operator is `0 = 1`), which is why no nontriviality hypothesis is needed. -/
lemma IsFactor.central_projection_eq {N : VonNeumannAlgebra H}
    (hN : IsFactor N) {e : H →L[ℂ] H} (he : IsCentralProjection N e) :
    e = 0 ∨ e = 1 := by
  rcases subsingleton_or_nontrivial H with hH | hH
  · have := hH
    exact Or.inl (Subsingleton.elim _ _)
  obtain ⟨c, hc⟩ := hN e he.2.1 he.2.2
  have hidem : e * e = e := he.1.isIdempotentElem
  rw [hc] at hidem
  have hcc : (c * c) • (1 : H →L[ℂ] H) = c • 1 := by
    rw [← hidem, smul_mul_smul_comm, mul_one]
  have hc2 : c * c = c := smul_left_injective ℂ one_ne_zero hcc
  have h0 : c * (c - 1) = 0 := by rw [mul_sub, mul_one, hc2, sub_self]
  rcases mul_eq_zero.mp h0 with h | h
  · exact Or.inl (by rw [hc, h, zero_smul])
  · exact Or.inr (by rw [hc, sub_eq_zero.mp h, one_smul])

/-- A star projection lies in the commutant `N'` exactly when its range is invariant under every
element of `N`. This is the bridge between reducing subspaces and (eventually central)
projections: it follows from the double-commutant characterisation
`VonNeumannAlgebra.IsStarProjection.mem_iff` together with `commutant_commutant`. -/
lemma isStarProjection_mem_commutant_iff {N : VonNeumannAlgebra H} {e : H →L[ℂ] H}
    (he : IsStarProjection e) :
    e ∈ N.commutant ↔ ∀ y ∈ N, (e.range) ∈ Module.End.invtSubmodule (y : Module.End ℂ H) := by
  rw [IsStarProjection.mem_iff he N.commutant, commutant_commutant]

/-- **Central support (factor case).** In a factor, a nonzero operator `q` meets the
"`N`-orbit" of any nonzero `e ∈ N`: there is `a ∈ N` with `q a e ≠ 0`. The statement needs no
projection hypothesis on `e` or `q`, only `e ∈ N`, `e ≠ 0` and `q ≠ 0`. The proof takes the
orthogonal projection `P` onto the closed `N`-invariant subspace generated by `e H`; `P` reduces
both `N` and `N'`, so it is central, hence `0` or `1`; since `P` acts as the identity on `e H`
(so `P ≠ 0`, as `e ≠ 0`), `P = 1`, so the generated subspace is the whole space and `q` cannot
annihilate it. This is the geometric input of the comparison theorem. -/
lemma IsFactor.exists_mul_ne {N : VonNeumannAlgebra H} (hN : IsFactor N)
    {e q : H →L[ℂ] H} (heN : e ∈ N) (he0 : e ≠ 0) (hq0 : q ≠ 0) : ∃ a ∈ N, q * a * e ≠ 0 := by
  have : Nontrivial H := nontrivial_of_ne_zero he0
  by_contra hcon
  have hcon' : ∀ a ∈ N, q * a * e = 0 := fun a haN => by
    by_contra h; exact hcon ⟨a, haN, h⟩
  set S : Set H := {y | ∃ a ∈ N, ∃ x, (a : H →L[ℂ] H) (e x) = y} with hS
  set M : Submodule ℂ H := (Submodule.span ℂ S).topologicalClosure with hM
  set P : H →L[ℂ] H := M.starProjection with hP
  have hPproj : IsStarProjection P := isStarProjection_starProjection
  have hSsub : S ⊆ M := Submodule.subset_span.trans (Submodule.le_topologicalClosure _)
  have hSmem : ∀ (a : H →L[ℂ] H), a ∈ N → ∀ x, (a : H →L[ℂ] H) (e x) ∈ M :=
    fun a haN x => hSsub ⟨a, haN, x, rfl⟩
  have hinv : ∀ (y : H →L[ℂ] H), (∀ s ∈ S, y s ∈ M) →
      P.range ∈ Module.End.invtSubmodule (y : Module.End ℂ H) := by
    intro y hyS
    have hcomapclosed : IsClosed ((M.comap (y : H →ₗ[ℂ] H)) : Set H) := by
      rw [Submodule.comap_coe]
      exact ((Submodule.span ℂ S).isClosed_topologicalClosure).preimage y.continuous
    have hle : M ≤ M.comap (y : H →ₗ[ℂ] H) := by
      apply Submodule.topologicalClosure_minimal (Submodule.span ℂ S) _ hcomapclosed
      rw [Submodule.span_le]
      intro s hs
      simp only [Submodule.comap_coe, Set.mem_preimage, SetLike.mem_coe]
      exact hyS s hs
    rw [hP, Submodule.range_starProjection]; exact hle
  have hPcomm : P ∈ N.commutant := by
    rw [isStarProjection_mem_commutant_iff hPproj]
    intro y hyN
    refine hinv y ?_
    rintro s ⟨a, haN, x, rfl⟩
    rw [show y ((a : H →L[ℂ] H) (e x)) = (y * a) (e x) from rfl]
    exact hSmem (y * a) (mul_mem hyN haN) x
  have hPN : P ∈ N := by
    rw [IsStarProjection.mem_iff hPproj N]
    intro y hyN'
    refine hinv y ?_
    rintro s ⟨a, haN, x, rfl⟩
    have hay : a * y = y * a := mem_commutant_iff.mp hyN' a haN
    have hey : e * y = y * e := mem_commutant_iff.mp hyN' e heN
    have heq : y ((a : H →L[ℂ] H) (e x)) = (a : H →L[ℂ] H) (e (y x)) := by
      rw [show y ((a : H →L[ℂ] H) (e x)) = (y * a) (e x) from rfl, ← hay]
      rw [show (a * y) (e x) = (a : H →L[ℂ] H) (y (e x)) from rfl]
      rw [show y (e x) = (y * e) x from rfl, ← hey]; rfl
    rw [heq]; exact hSmem a haN (y x)
  have hPcentral : IsCentralProjection N P := ⟨hPproj, hPN, hPcomm⟩
  have hP1 : P = 1 := by
    rcases hN.central_projection_eq hPcentral with h0 | h1
    · exact absurd (by
        ext x
        have hpx : P (e x) = e x := by
          rw [hP, Submodule.starProjection_eq_self_iff]; exact hSmem 1 (one_mem _) x
        rw [h0] at hpx; simpa using hpx.symm : e = 0) he0
    · exact h1
  have hMtop : M = ⊤ := by
    have hMr : M = P.range := (Submodule.range_starProjection M).symm
    rw [hMr, hP1]; exact Submodule.eq_top_iff'.2 fun y => ⟨y, rfl⟩
  have hqM : M ≤ LinearMap.ker (q : H →ₗ[ℂ] H) := by
    apply Submodule.topologicalClosure_minimal (Submodule.span ℂ S) _ q.isClosed_ker
    rw [Submodule.span_le]
    rintro s ⟨a, haN, x, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    rw [show q ((a : H →L[ℂ] H) (e x)) = (q * a * e) x from rfl, hcon' a haN]; rfl
  apply hq0
  ext x
  have hx : x ∈ LinearMap.ker (q : H →ₗ[ℂ] H) := hqM (hMtop ▸ Submodule.mem_top)
  simpa using hx

/-! ### Invariance under spatial isomorphisms -/

section Conj

variable {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']

/-- **Factors are spatially invariant**: if `N` is a factor, so is `U N U⋆`. -/
lemma IsFactor.conj {N : VonNeumannAlgebra H} (hN : IsFactor N) (U : H ≃ₗᵢ[ℂ] H') :
    IsFactor (conj U N) := fun y hy hy' => by
  rw [conj_commutant, mem_conj_iff] at hy'
  rw [mem_conj_iff] at hy
  obtain ⟨c, hc⟩ := hN _ hy hy'
  refine ⟨c, ?_⟩
  have := congrArg U.conjStarAlgEquiv hc
  rwa [StarAlgEquiv.apply_symm_apply, map_smul, map_one] at this

/-- `U N U⋆` is a factor iff `N` is. -/
lemma isFactor_conj_iff {N : VonNeumannAlgebra H} (U : H ≃ₗᵢ[ℂ] H') :
    IsFactor (conj U N) ↔ IsFactor N := by
  refine ⟨fun h x hx hx' => ?_, fun h => h.conj U⟩
  obtain ⟨c, hc⟩ := h _ ((conjStarAlgEquiv_mem_conj_iff U N).mpr hx)
    (by rw [conj_commutant]; exact (conjStarAlgEquiv_mem_conj_iff U _).mpr hx')
  refine ⟨c, ?_⟩
  have := congrArg U.conjStarAlgEquiv.symm hc
  rwa [StarAlgEquiv.symm_apply_apply, map_smul, map_one] at this

end Conj

/-! ### Invariance under abstract `⋆`-isomorphisms

Being a factor is a property of the abstract `⋆`-algebra `N`, not of the way it sits inside
`B(H)`: the centre `N ∩ N′` is the centre of the ring `N`. It is therefore carried along
any `⋆`-algebra isomorphism `N ≃⋆ₐ M` between von Neumann algebras on possibly different Hilbert
spaces — not only along the spatial ones `N ↦ U N U⋆` of the previous section. A `⋆`-isomorphism
`N ≃⋆ₐ (K →L[ℂ] K)` onto the operator type is covered by composing with
`boundedLinearOperators.starAlgEquiv.symm`, which lands in `𝓑(K)`. -/

section StarAlgEquiv

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {N : VonNeumannAlgebra H} {M : VonNeumannAlgebra K}

/-- **Being a factor is intrinsic to the `⋆`-algebra.** `N` is a factor iff every element of the
ring `N` commuting with all of `N` is a scalar: the centre `N ∩ N′` is computed inside `N`. -/
lemma isFactor_iff_forall_commute :
    IsFactor N ↔ ∀ x : N, (∀ y : N, y * x = x * y) → ∃ c : ℂ, x = c • 1 := by
  refine ⟨fun h x hx => ?_, fun h x hxN hx' => ?_⟩
  · obtain ⟨c, hc⟩ := h x x.2 (mem_commutant_iff.mpr fun y hy => congrArg Subtype.val (hx ⟨y, hy⟩))
    exact ⟨c, Subtype.ext hc⟩
  · obtain ⟨c, hc⟩ := h ⟨x, hxN⟩ fun y => Subtype.ext (mem_commutant_iff.mp hx' y y.2)
    exact ⟨c, congrArg Subtype.val hc⟩

/-- A `⋆`-isomorphism carries a factor to a factor: it preserves the centre and the scalars. -/
private lemma IsFactor.of_starAlgEquiv (φ : N ≃⋆ₐ[ℂ] M) (hN : IsFactor N) : IsFactor M := by
  rw [isFactor_iff_forall_commute] at hN ⊢
  intro x hx
  obtain ⟨c, hc⟩ := hN (φ.symm x) fun y => EquivLike.injective φ (by
    rw [map_mul, map_mul, StarAlgEquiv.apply_symm_apply, hx])
  exact ⟨c, by rw [← φ.apply_symm_apply x, hc, map_smul, map_one]⟩

/-- **Factors are invariant under `⋆`-isomorphisms**: if `N ≃⋆ₐ M`, then `M` is a factor iff `N`
is. -/
lemma isFactor_iff_of_starAlgEquiv (φ : N ≃⋆ₐ[ℂ] M) : IsFactor M ↔ IsFactor N :=
  ⟨IsFactor.of_starAlgEquiv φ.symm, IsFactor.of_starAlgEquiv φ⟩

end StarAlgEquiv

end VonNeumannAlgebra
