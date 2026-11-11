/-
Copyright (c) 2025 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.VonNeumannAlgebra.BoundedOperators
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.RankOne
public import QuantumSystem.ForMathlib.Algebra.Central.Basic
public import QuantumSystem.ForMathlib.Analysis.VonNeumannAlgebra.Commutant
public import QuantumSystem.ForMathlib.RingTheory.SimpleModule.Central
public import QuantumSystem.ForMathlib.Topology.Algebra.Module.ContinuousLinearMap.Nontrivial

/-!
# Factors and central projections

A von Neumann algebra `N` is a **factor** when its centre `N ∩ N′` is trivial. The centre of the
ring `N` is `N ∩ N′`, so a factor is a von Neumann algebra that is a central `ℂ`-algebra in Mathlib's
sense, `Algebra.IsCentral ℂ N`; no separate predicate is defined. Nothing restricts the dimension:
`B(H)` is a factor for every `H`. In particular the zero algebra on `H = 0` is a factor, since its
centre `{0} = ℂ • 1` consists of scalars; a statement that needs a nonzero factor assumes
`Nontrivial H`. This file proves the facts about factors and central projections,
the projections of the centre, that the comparison theory of projections needs. It is organised in
three parts, followed by a remark:

1. **Factors** — the characterisation `isCentral_iff` through the commutant, and `𝓑(H)` as the
   first example of a factor.
2. **Central projections** — projections in the centre `N ∩ N′`. Every `e ∈ N` is carried by a
   central projection that detects whether `q N e = 0`
   (`VonNeumannAlgebra.exists_isCentralProjection_mul_eq_zero_iff`); in a factor central
   projections are trivial, which gives `VonNeumannAlgebra.exists_mul_mul_ne_zero_of_isCentral`.
3. **Invariance under spatial isomorphisms** `N ↦ U N U⋆`.

Being a factor is intrinsic to the algebra `N`, so it is invariant under algebra isomorphisms
`N ≃ₐ[ℂ] M` between von Neumann algebras on possibly different Hilbert spaces, not only under the
spatial ones `N ↦ U N U⋆`: this is `Algebra.IsCentral.of_algEquiv'`, which allows the two algebras
in different universes.

Nonzero finite-dimensional factors are full matrix algebras: this is
`CStarAlgebra.exists_starAlgEquiv_cstarMatrix_of_isCentral`, stated for central C⋆-algebras in
`QuantumSystem.Analysis.CStarAlgebra.FiniteDimensional`.

Minimal and abelian projections are defined in
`QuantumSystem.Analysis.VonNeumannAlgebra.MinimalProjection`, and Murray–von Neumann equivalence
and the comparison of projections in
`QuantumSystem.Analysis.VonNeumannAlgebra.MurrayVonNeumann`.

## Main definitions

* `VonNeumannAlgebra.IsCentralProjection N e` — `e` is a projection in `N ∩ N′`.

## Main results

* `VonNeumannAlgebra.isCentral_iff` — `N` is a factor iff every element of `N ∩ N′` is a scalar.
* `VonNeumannAlgebra.isCentral_boundedLinearOperators` — `𝓑(H)` is a factor.
* `VonNeumannAlgebra.isCentral_commutant` / `isCentral_commutant_iff` — `N` is a factor iff `N′`
  is.
* `VonNeumannAlgebra.IsCentralProjection.eq_zero_or_eq_one` — in a factor every
  central projection is `0` or `1`.
* `VonNeumannAlgebra.IsStarProjection.mem_commutant_iff` — a star projection lies in the commutant
  `N′` exactly when its range is invariant under every element of `N` (the projection–reducing
  subspace bridge used to build central supports).
* `VonNeumannAlgebra.exists_isCentralProjection_mul_eq_zero_iff` — for `e ∈ N` there is a central
  projection `P` of `N` with `P e = e` such that `q N e = 0` exactly when `q P = 0`.
* `VonNeumannAlgebra.exists_mul_mul_ne_zero_of_isCentral` — the central-support lemma: in a factor,
  `q N e ≠ 0` for nonzero `q` and nonzero `e ∈ N`: there is `a ∈ N` with `q a e ≠ 0`.
* `VonNeumannAlgebra.isCentral_conj_iff` — factors are invariant under spatial isomorphisms
  `N ↦ U N U⋆`.

## TODO

Define factors for abstract von Neumann algebras, Mathlib's `WStarAlgebra`, as the
`Algebra.IsCentral ℂ` ones, and transfer the results here through Sakai's characterisation, which
represents a `WStarAlgebra` as a von Neumann algebra on a Hilbert space.
-/

@[expose] public section

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Factors

A von Neumann algebra `N` is a **factor** when its centre `N ∩ N′` is trivial. The centre of the
ring `N` is `N ∩ N′`, so this is Mathlib's `Algebra.IsCentral ℂ N`: the centre of `N` is the image
of `ℂ`. Factors are stated with that class throughout, as `[Algebra.IsCentral ℂ N]`; the
characterisation through the commutant is `VonNeumannAlgebra.isCentral_iff`. -/

/-- **`N` is a factor iff `N ∩ N′` consists of scalars**: `Algebra.IsCentral ℂ N` holds iff every
operator lying in both `N` and its commutant is a scalar multiple of the identity. -/
lemma isCentral_iff {N : VonNeumannAlgebra H} :
    Algebra.IsCentral ℂ N ↔ ∀ x : H →L[ℂ] H, x ∈ N → x ∈ N′ → ∃ c : ℂ, x = c • 1 := by
  refine ⟨fun h x hx hx' => ?_, fun h => ⟨fun z hz => ?_⟩⟩
  · obtain ⟨c, hc⟩ := (Algebra.IsCentral.mem_center_iff ℂ (x := (⟨x, hx⟩ : N))).mp
      (Subalgebra.mem_center_iff.mpr fun g => Subtype.ext (mem_commutant_iff.mp hx' g g.2))
    exact ⟨c, by simpa [Algebra.algebraMap_eq_smul_one] using congrArg Subtype.val hc⟩
  · obtain ⟨c, hc⟩ := h z z.2 (mem_commutant_iff.mpr fun y hy =>
      congrArg Subtype.val (Subalgebra.mem_center_iff.mp hz ⟨y, hy⟩))
    exact ⟨c, Subtype.ext (by simp [Algebra.algebraMap_eq_smul_one, hc])⟩

/-- In a factor, an operator lying in both `N` and its commutant is a scalar multiple of the
identity. -/
lemma exists_eq_smul_one_of_isCentral {N : VonNeumannAlgebra H} [h : Algebra.IsCentral ℂ N]
    {x : H →L[ℂ] H} (hx : x ∈ N) (hx' : x ∈ N′) : ∃ c : ℂ, x = c • 1 :=
  isCentral_iff.mp h x hx hx'

/-- **The commutant of a factor is a factor.** The centre `N ∩ N′` is also the centre
`N′ ∩ N″` of the commutant, since `N″ = N`. -/
instance isCentral_commutant {N : VonNeumannAlgebra H} [Algebra.IsCentral ℂ N] :
    Algebra.IsCentral ℂ N′ :=
  isCentral_iff.mpr fun x hx hx' =>
    exists_eq_smul_one_of_isCentral (by rwa [commutant_commutant] at hx') hx

/-- A von Neumann algebra is a factor iff its commutant is. -/
lemma isCentral_commutant_iff {N : VonNeumannAlgebra H} :
    Algebra.IsCentral ℂ N′ ↔ Algebra.IsCentral ℂ N :=
  ⟨fun _ => commutant_commutant N ▸ isCentral_commutant (N := N′),
    fun _ => inferInstance⟩

/-- **`B(H)` is a factor.** `𝓑(H)` is `⋆`-isomorphic to `H →L[ℂ] H`, which is central by Mathlib's
`Algebra.IsCentral.instContinuousLinearMap`. -/
instance isCentral_boundedLinearOperators : Algebra.IsCentral ℂ 𝓑(H) :=
  .of_algEquiv' (boundedLinearOperators.starAlgEquiv (H := H)).symm.toAlgEquiv

/-! ### Central projections -/

/-- A **central projection** of `N`: a star projection lying in both `N` and its commutant
(equivalently, in the centre `N ∩ N′`). -/
def IsCentralProjection (N : VonNeumannAlgebra H) (e : H →L[ℂ] H) : Prop :=
  IsStarProjection e ∧ e ∈ N ∧ e ∈ N′

/-- `0` is a central projection. -/
lemma IsCentralProjection.zero (N : VonNeumannAlgebra H) : IsCentralProjection N 0 :=
  ⟨IsStarProjection.zero _, zero_mem _, zero_mem _⟩

/-- `1` is a central projection. -/
lemma IsCentralProjection.one (N : VonNeumannAlgebra H) : IsCentralProjection N 1 :=
  ⟨IsStarProjection.one _, one_mem _, one_mem _⟩

/-- In a factor, every central projection is trivial: it is `0` or `1`. This is the
projection-level form of the triviality of the centre: a nonzero central idempotent of a central
algebra is `1` (`Algebra.IsCentral.eq_one_of_isIdempotentElem`). On a subsingleton `H` the
conclusion holds trivially (every operator is `0 = 1`), which is why no nontriviality hypothesis is
needed. -/
lemma IsCentralProjection.eq_zero_or_eq_one {N : VonNeumannAlgebra H} [Algebra.IsCentral ℂ N]
    {e : H →L[ℂ] H} (he : IsCentralProjection N e) :
    e = 0 ∨ e = 1 := by
  by_cases he0 : e = 0
  · exact Or.inl he0
  have : Nontrivial H := ContinuousLinearMap.nontrivial_of_ne_zero he0
  have h1 : (⟨e, he.2.1⟩ : N) = 1 :=
    Algebra.IsCentral.eq_one_of_isIdempotentElem (K := ℂ)
      (Subalgebra.mem_center_iff.mpr fun g => Subtype.ext (mem_commutant_iff.mp he.2.2 g g.2))
      (Subtype.ext he.1.isIdempotentElem) fun h => he0 (congrArg Subtype.val h)
  exact Or.inr (congrArg Subtype.val h1)

/-- A star projection lies in the commutant `N′` exactly when its range is invariant under every
element of `N`. This is the bridge between reducing subspaces and (eventually central)
projections: it follows from the double-commutant characterisation
`VonNeumannAlgebra.IsStarProjection.mem_iff` together with `commutant_commutant`. -/
lemma IsStarProjection.mem_commutant_iff {N : VonNeumannAlgebra H} {e : H →L[ℂ] H}
    (he : IsStarProjection e) :
    e ∈ N′ ↔ ∀ y ∈ N, (e.range) ∈ Module.End.invtSubmodule (y : Module.End ℂ H) := by
  rw [IsStarProjection.mem_iff he N′, commutant_commutant]

/-- **A central projection carrying `e`.** For `e ∈ N` there is a central projection `P` of `N`
with `P e = e` such that an operator `q` satisfies `q a e = 0` for every `a ∈ N` exactly when
`q P = 0`. Neither `e` nor `q` need be a projection, and `q` need not lie in `N`. `P` is the
orthogonal projection onto the closed subspace generated by the vectors `a (e x)` with `a ∈ N`:
that subspace is invariant under `N` and under `N′`, so `P` lies in `N′` and in `N″ = N`. -/
theorem exists_isCentralProjection_mul_eq_zero_iff {N : VonNeumannAlgebra H} {e : H →L[ℂ] H}
    (heN : e ∈ N) :
    ∃ P : H →L[ℂ] H, IsCentralProjection N P ∧ P * e = e ∧
      ∀ q : H →L[ℂ] H, (∀ a ∈ N, q * a * e = 0) ↔ q * P = 0 := by
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
  have hPcomm : P ∈ N′ := by
    rw [IsStarProjection.mem_commutant_iff hPproj]
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
  have hPfix : ∀ (a : H →L[ℂ] H), a ∈ N → ∀ x, P ((a : H →L[ℂ] H) (e x)) = a (e x) :=
    fun a haN x => by rw [hP, Submodule.starProjection_eq_self_iff]; exact hSmem a haN x
  refine ⟨P, ⟨hPproj, hPN, hPcomm⟩, ?_, fun q => ⟨fun hq => ?_, fun hq a haN => ?_⟩⟩
  · ext x
    exact hPfix 1 (one_mem _) x
  · have hqM : M ≤ LinearMap.ker (q : H →ₗ[ℂ] H) := by
      apply Submodule.topologicalClosure_minimal (Submodule.span ℂ S) _ q.isClosed_ker
      rw [Submodule.span_le]
      rintro s ⟨a, haN, x, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
      rw [show q ((a : H →L[ℂ] H) (e x)) = (q * a * e) x from rfl, hq a haN]; rfl
    ext x
    have hx : P x ∈ LinearMap.ker (q : H →ₗ[ℂ] H) := hqM (Submodule.starProjection_apply_mem M x)
    simpa using hx
  · ext x
    rw [show (q * a * e) x = q ((a : H →L[ℂ] H) (e x)) from rfl, ← hPfix a haN x,
      show q (P ((a : H →L[ℂ] H) (e x))) = (q * P) (a (e x)) from rfl, hq]; rfl

/-- **Central support (factor case).** In a factor, `q N e ≠ 0` for a nonzero operator `q` and a
nonzero `e ∈ N`: there is `a ∈ N` with `q a e ≠ 0`. The statement needs no projection hypothesis
on `e` or `q`, only `e ∈ N`, `e ≠ 0` and `q ≠ 0`. The central projection `P` carrying `e`
(`exists_isCentralProjection_mul_eq_zero_iff`) is `0` or `1` in a factor; `P e = e ≠ 0` excludes
`0`, so `P = 1`, and `q P = 0` would give `q = 0`. This is the geometric input of the comparison
theorem. -/
lemma exists_mul_mul_ne_zero_of_isCentral {N : VonNeumannAlgebra H} [Algebra.IsCentral ℂ N]
    {e q : H →L[ℂ] H} (heN : e ∈ N) (he0 : e ≠ 0) (hq0 : q ≠ 0) : ∃ a ∈ N, q * a * e ≠ 0 := by
  obtain ⟨P, hPcentral, hPe, hP⟩ := exists_isCentralProjection_mul_eq_zero_iff heN
  by_contra hcon
  have hqP : q * P = 0 := (hP q).mp fun a haN => by
    by_contra h; exact hcon ⟨a, haN, h⟩
  rcases hPcentral.eq_zero_or_eq_one with h0 | h1
  · exact he0 (by rw [← hPe, h0, zero_mul])
  · exact hq0 (by rw [← mul_one q, ← h1, hqP])

/-! ### Invariance under spatial isomorphisms -/

section Conj

variable {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']

/-- **Factors are spatially invariant**: if `N` is a factor, so is `U N U⋆`, since `conjEquiv U N`
is a `⋆`-isomorphism `N ≃⋆ₐ U N U⋆`. -/
instance isCentral_conj {N : VonNeumannAlgebra H} [Algebra.IsCentral ℂ N] (U : H ≃ₗᵢ[ℂ] H') :
    Algebra.IsCentral ℂ (conj U N) :=
  .of_algEquiv' (conjEquiv U N).toAlgEquiv

/-- `U N U⋆` is a factor iff `N` is. -/
lemma isCentral_conj_iff {N : VonNeumannAlgebra H} (U : H ≃ₗᵢ[ℂ] H') :
    Algebra.IsCentral ℂ (conj U N) ↔ Algebra.IsCentral ℂ N :=
  (Algebra.IsCentral.iff_of_algEquiv (conjEquiv U N).toAlgEquiv).symm

end Conj

end VonNeumannAlgebra
