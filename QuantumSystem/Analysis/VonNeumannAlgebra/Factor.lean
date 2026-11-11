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
2. **Central projections** — projections in the centre `N ∩ N′`; in a factor these are trivial,
   the seed of the central-support lemma `VonNeumannAlgebra.exists_mul_ne_of_isCentral`.
3. **Invariance under spatial isomorphisms** `N ↦ U N U⋆`.

Being a factor is intrinsic to the algebra `N`, so it is invariant under algebra isomorphisms
`N ≃ₐ[ℂ] M` between von Neumann algebras on possibly different Hilbert spaces, not only under the
spatial ones `N ↦ U N U⋆`: this is `Algebra.IsCentral.of_algEquiv'`, which allows the two algebras
in different universes.

Finite-dimensional factors are full matrix algebras: this is
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
* `VonNeumannAlgebra.isStarProjection_mem_commutant_iff` — a star projection lies in the commutant
  `N′` exactly when its range is invariant under every element of `N` (the projection–reducing
  subspace bridge used to build central supports).
* `VonNeumannAlgebra.exists_mul_ne_of_isCentral` — the central-support lemma: in a factor, a nonzero `q` meets
  the `N`-orbit of any nonzero `e ∈ N`.
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
    exists_eq_smul_one_of_isCentral (by rwa [VonNeumannAlgebra.commutant_commutant] at hx') hx

/-- A von Neumann algebra is a factor iff its commutant is. -/
lemma isCentral_commutant_iff {N : VonNeumannAlgebra H} :
    Algebra.IsCentral ℂ N′ ↔ Algebra.IsCentral ℂ N :=
  ⟨fun _ => VonNeumannAlgebra.commutant_commutant N ▸ isCentral_commutant (N := N′),
    fun _ => inferInstance⟩

/-- **`B(H)` is a factor.** `𝓑(H)` is `⋆`-isomorphic to `H →L[ℂ] H`, which is central by Mathlib's
`Algebra.IsCentral.instContinuousLinearMap`. -/
instance isCentral_boundedLinearOperators : Algebra.IsCentral ℂ 𝓑(H) :=
  .of_algEquiv' (boundedLinearOperators.starAlgEquiv (H := H)).symm.toAlgEquiv

omit [CompleteSpace H] in
/-- **A nonzero operator witnesses a nonzero space.** On a subsingleton `H` every operator is `0`,
so exhibiting any `x ≠ 0` already gives `Nontrivial H`. This is why almost none of the results
below need `[Nontrivial H]` as a hypothesis: they carry a nonzero projection, which supplies it.
The exceptions are the statements that quantify over projections without asserting one exists
(`isTypeI_iff_exists_isMinimalProjection_of_isCentral`, `IsTypeIFactor.exists_isMinimalProjection`) and
the ones producing a minimal projection of `𝓑(H)` out of nothing. -/
lemma nontrivial_of_ne_zero {x : H →L[ℂ] H} (hx : x ≠ 0) : Nontrivial H :=
  let ⟨y, hy⟩ := ContinuousLinearMap.exists_ne_zero hx
  ⟨⟨x y, 0, hy⟩⟩

/-! ### Central projections -/

/-- A **central projection** of `N`: a star projection lying in both `N` and its commutant
(equivalently, in the centre `N ∩ N′`). -/
def IsCentralProjection (N : VonNeumannAlgebra H) (e : H →L[ℂ] H) : Prop :=
  IsStarProjection e ∧ e ∈ N ∧ e ∈ N′

/-- `0` is a central projection. -/
lemma isCentralProjection_zero (N : VonNeumannAlgebra H) : IsCentralProjection N 0 :=
  ⟨IsStarProjection.zero _, zero_mem _, zero_mem _⟩

/-- `1` is a central projection. -/
lemma isCentralProjection_one (N : VonNeumannAlgebra H) : IsCentralProjection N 1 :=
  ⟨IsStarProjection.one _, one_mem _, one_mem _⟩

/-- In a factor, every central projection is trivial: it is `0` or `1`. This is the
projection-level form of the triviality of the centre. On a subsingleton `H` the conclusion is
vacuous (every operator is `0 = 1`), which is why no nontriviality hypothesis is needed. -/
lemma IsCentralProjection.eq_zero_or_eq_one {N : VonNeumannAlgebra H} [Algebra.IsCentral ℂ N]
    {e : H →L[ℂ] H} (he : IsCentralProjection N e) :
    e = 0 ∨ e = 1 := by
  rcases subsingleton_or_nontrivial H with hH | hH
  · have := hH
    exact Or.inl (Subsingleton.elim _ _)
  obtain ⟨c, hc⟩ := exists_eq_smul_one_of_isCentral he.2.1 he.2.2
  have hidem : e * e = e := he.1.isIdempotentElem
  rw [hc] at hidem
  have hcc : (c * c) • (1 : H →L[ℂ] H) = c • 1 := by
    rw [← hidem, smul_mul_smul_comm, mul_one]
  have hc2 : c * c = c := smul_left_injective ℂ one_ne_zero hcc
  have h0 : c * (c - 1) = 0 := by rw [mul_sub, mul_one, hc2, sub_self]
  rcases mul_eq_zero.mp h0 with h | h
  · exact Or.inl (by rw [hc, h, zero_smul])
  · exact Or.inr (by rw [hc, sub_eq_zero.mp h, one_smul])

/-- A star projection lies in the commutant `N′` exactly when its range is invariant under every
element of `N`. This is the bridge between reducing subspaces and (eventually central)
projections: it follows from the double-commutant characterisation
`VonNeumannAlgebra.IsStarProjection.mem_iff` together with `commutant_commutant`. -/
lemma isStarProjection_mem_commutant_iff {N : VonNeumannAlgebra H} {e : H →L[ℂ] H}
    (he : IsStarProjection e) :
    e ∈ N′ ↔ ∀ y ∈ N, (e.range) ∈ Module.End.invtSubmodule (y : Module.End ℂ H) := by
  rw [IsStarProjection.mem_iff he N.commutant, commutant_commutant]

/-- **Central support (factor case).** In a factor, a nonzero operator `q` meets the
"`N`-orbit" of any nonzero `e ∈ N`: there is `a ∈ N` with `q a e ≠ 0`. The statement needs no
projection hypothesis on `e` or `q`, only `e ∈ N`, `e ≠ 0` and `q ≠ 0`. The proof takes the
orthogonal projection `P` onto the closed `N`-invariant subspace generated by `e H`; `P` reduces
both `N` and `N′`, so it is central, hence `0` or `1`; since `P` acts as the identity on `e H`
(so `P ≠ 0`, as `e ≠ 0`), `P = 1`, so the generated subspace is the whole space and `q` cannot
annihilate it. This is the geometric input of the comparison theorem. -/
lemma exists_mul_ne_of_isCentral {N : VonNeumannAlgebra H} [Algebra.IsCentral ℂ N]
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
    rcases hPcentral.eq_zero_or_eq_one with h0 | h1
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
