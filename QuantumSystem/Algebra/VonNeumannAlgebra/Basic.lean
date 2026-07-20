module

public import Mathlib.Analysis.VonNeumannAlgebra.Basic
public import QuantumSystem.ForMathlib.Algebra.Star.PartialIsometry

/-!
# Basic theory of von Neumann factors and the comparison of projections

This file sets up the basic vocabulary of the comparison theory of projections in a von Neumann
algebra, the foundation of the type classification (and, downstream, of the type I factor
structure theorem). It also supplies `𝓑(H)`, the von Neumann algebra of *all* bounded operators
— the object the literature writes `B(H)` — which Mathlib's `VonNeumannAlgebra H` does not provide
as a distinguished element.

The file is organised in three parts:

1. **Factors, minimal projections and Murray–von Neumann equivalence** — the basic definitions
   `IsFactor`, `IsMinimalProjection`, `IsAbelianProjection` and the equivalence relation
   `p ∼[N] q`.
2. **Central projections** — projections in the centre `N ∩ N'`; in a factor these are trivial,
   the seed of the central-support lemma `IsFactor.exists_mul_ne`.
3. **Comparison of projections** — the calculus of partial isometries, the subordination relation
   `p ≼[N] q`, and the comparison theorem for minimal projections
   (`IsMinimalProjection.mvNSub_of_isFactor`).

## Main definitions

* `VonNeumannAlgebra.boundedLinearOperators H` — the algebra of all bounded operators, with carrier
  `Set.univ`, denoted `𝓑(H)` (`VonNeumannAlgebra.coe_boundedLinearOperators` /
  `VonNeumannAlgebra.mem_boundedLinearOperators`).
* `VonNeumannAlgebra.boundedLinearOperators.starAlgEquiv` — the canonical `⋆`-isomorphism
  `𝓑(H) ≃⋆ₐ[ℂ] (H →L[ℂ] H)` identifying the bundled von Neumann algebra with the operator type
  (the `⋆`-algebra analogue of `Subalgebra.topEquiv`).
* `VonNeumannAlgebra.IsFactor N` — `N` has trivial centre: every element of `N ∩ N'` is a scalar.
* `VonNeumannAlgebra.IsMinimalProjection N e` — `e` is a nonzero star projection in `N` with
  trivial corner `e N e = ℂ e`. This implies the order-theoretic minimality (no proper nonzero
  subprojection in `N`, expressed algebraically as: any projection `f ∈ N` with `e * f = f`, i.e.
  the Loewner relation `f ≤ e`, is `0` or `e`), recorded as
  `IsMinimalProjection.no_proper_subprojection`.
* `VonNeumannAlgebra.IsAbelianProjection N p` — `p` is a star projection in `N` with commutative
  corner `p N p`.
* `VonNeumannAlgebra.MvNEquiv N p q` — `p` and `q` are Murray–von Neumann equivalent inside `N`:
  there is a partial isometry `v ∈ N` with source `v⋆v = p` and range `vv⋆ = q`. Written `p ∼[N] q`.
* `VonNeumannAlgebra.IsCentralProjection N e` — `e` is a projection in `N ∩ N'`.
* `VonNeumannAlgebra.MvNSub N p q` — `p ≼[N] q`: `p` is Murray–von Neumann equivalent to a
  subprojection of `q`.

## Main results

* `VonNeumannAlgebra.MvNEquiv.refl` / `symm` / `trans` — Murray–von Neumann equivalence is an
  equivalence relation on the projections of `N`.
* `VonNeumannAlgebra.IsFactor.central_projection_eq` — in a factor every central projection is
  `0` or `1`.
* `VonNeumannAlgebra.isStarProjection_mem_commutant_iff` — a star projection lies in the commutant
  `N'` exactly when its range is invariant under every element of `N` (the projection–reducing
  subspace bridge used to build central supports).
* `VonNeumannAlgebra.IsFactor.exists_mul_ne` — the central-support lemma: in a factor, a nonzero
  `q` meets the `N`-orbit of any nonzero `e ∈ N`.
* `VonNeumannAlgebra.MvNSub.refl` / `MvNSub.trans` — subordination is a preorder on projections.
* `VonNeumannAlgebra.mvNSub_of_posCorner` — the scaling step of the comparison theorem: a positive
  scalar corner `(q a e)⋆(q a e) = c • e`, `c > 0`, yields `e ≼[N] q`.
* `VonNeumannAlgebra.IsMinimalProjection.mvNSub_of_isFactor` — the comparison theorem for minimal
  projections: in a factor, a minimal projection is subordinate to every nonzero projection.

The full comparison theorem (any two projections in a factor are comparable) requires central
supports and polar decomposition for general projections and is not developed here; the
minimal-projection case above is the form the type I structure theorem needs.

## Notation

The symbols of the operator-algebra literature live in the opt-in `VonNeumannAlgebra` scope;
activate them with `open scoped VonNeumannAlgebra`.

| Symbol | Expansion | How to activate |
|---|---|---|
| `p ∼[N] q` | `VonNeumannAlgebra.MvNEquiv N p q` | `open scoped VonNeumannAlgebra` |
| `p ≼[N] q` | `VonNeumannAlgebra.MvNSub N p q` | `open scoped VonNeumannAlgebra` |
| `𝓑(H)` | `VonNeumannAlgebra.boundedLinearOperators H` | `open scoped VonNeumannAlgebra` |

The `𝓑(H)` glyph overloads the type-level notation `𝓑(H) = H →L[ℂ] H` of
`ForMathlib.Analysis.CStarAlgebra.HilbertSpace`; the two denote the same object B(H) at different
levels and are related by `boundedLinearOperators.starAlgEquiv`. The expected type disambiguates.
-/

@[expose] public section

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### The full algebra `𝓑(H)` of all bounded operators -/

/-- The von Neumann algebra `𝓑(H)` of **all bounded linear operators** on `H` — the object the
literature writes `B(H)`. Its carrier is `Set.univ`; the double-commutant property is the
bicommutant inclusion `s ⊆ s''` applied to `s = univ`, together with `univ` being the largest set.
Mathlib's bundled `VonNeumannAlgebra H` provides no such distinguished element, so this file
supplies it. -/
noncomputable def boundedLinearOperators (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] : VonNeumannAlgebra H where
  toStarSubalgebra := ⊤
  centralizer_centralizer' :=
    Set.Subset.antisymm (Set.subset_univ _) Set.subset_centralizer_centralizer

/-- `𝓑(H)` denotes the von Neumann algebra of all bounded operators on `H`
(`VonNeumannAlgebra.boundedLinearOperators H`). This overloads the type-level notation
`𝓑(H) = H →L[ℂ] H` of `ForMathlib.Analysis.CStarAlgebra.HilbertSpace`: the two denote the same
mathematical object B(H) at different levels (the operator *type* vs. the bundled *von Neumann
algebra* of all operators), and the expected type disambiguates. The two levels are related by the
canonical `⋆`-isomorphism `boundedLinearOperators.starAlgEquiv`. -/
scoped notation:max "𝓑(" H ")" => VonNeumannAlgebra.boundedLinearOperators H

@[simp] lemma coe_boundedLinearOperators :
    ((𝓑(H) : VonNeumannAlgebra H) : Set (H →L[ℂ] H)) = Set.univ := rfl

/-- Every bounded operator lies in `𝓑(H)`. -/
@[simp] lemma mem_boundedLinearOperators (x : H →L[ℂ] H) : x ∈ (𝓑(H) : VonNeumannAlgebra H) :=
  Set.mem_univ x

/-- **The two levels of `𝓑(H)` agree.** The underlying `⋆`-subalgebra of the bundled von Neumann
algebra `𝓑(H)`, coerced to a type, is canonically `⋆`-isomorphic to the operator type
`H →L[ℂ] H` (itself the type-level `𝓑(H)` of `ForMathlib.Analysis.CStarAlgebra.HilbertSpace`).
This is the `⋆`-algebra analogue of `Subalgebra.topEquiv` / `Submodule.topEquiv`, making explicit
that the notation overload denotes one and the same object B(H). The equivalence is phrased on
`(𝓑(H)).toStarSubalgebra` because Mathlib equips the `⋆`-subalgebra — not the bundled
`VonNeumannAlgebra` — with the `ℂ`-algebra structure. -/
noncomputable def boundedLinearOperators.starAlgEquiv :
    (𝓑(H) : VonNeumannAlgebra H).toStarSubalgebra ≃⋆ₐ[ℂ] (H →L[ℂ] H) :=
  StarAlgEquiv.ofStarAlgHom
    (𝓑(H) : VonNeumannAlgebra H).toStarSubalgebra.subtype
    ({ toFun := fun x => ⟨x, StarSubalgebra.mem_top⟩
       map_one' := rfl
       map_mul' := fun _ _ => rfl
       map_zero' := rfl
       map_add' := fun _ _ => rfl
       commutes' := fun _ => rfl
       map_star' := fun _ => rfl } :
      (H →L[ℂ] H) →⋆ₐ[ℂ] (𝓑(H) : VonNeumannAlgebra H).toStarSubalgebra)
    (fun _ => rfl) (fun _ => rfl)

/-! ### Factors, minimal projections and Murray–von Neumann equivalence -/

/-- A von Neumann algebra is closed under scalar multiplication. -/
lemma smul_mem {N : VonNeumannAlgebra H} (c : ℂ) {x : H →L[ℂ] H} (hx : x ∈ N) : c • x ∈ N := by
  rw [Algebra.smul_def]
  exact mul_mem (algebraMap_mem N.toStarSubalgebra c) hx

/-- A von Neumann algebra `N` is a **factor** when its centre is trivial: every operator lying in
both `N` and its commutant is a scalar multiple of the identity. -/
def IsFactor (N : VonNeumannAlgebra H) : Prop :=
  ∀ x : H →L[ℂ] H, x ∈ N → x ∈ N.commutant → ∃ c : ℂ, x = c • 1

/-- A **minimal projection** of `N`: a nonzero star projection `e ∈ N` whose corner is trivial,
`e N e = ℂ e`. This is the conventional operator-algebraic definition (Takesaki, Kadison–Ringrose);
it implies minimality in the order sense (no proper nonzero subprojection), recorded as
`IsMinimalProjection.no_proper_subprojection`. The corner formulation is the one that
supports comparison theory without invoking Borel functional calculus. -/
def IsMinimalProjection (N : VonNeumannAlgebra H) (e : H →L[ℂ] H) : Prop :=
  IsStarProjection e ∧ e ∈ N ∧ e ≠ 0 ∧ ∀ a ∈ N, ∃ c : ℂ, e * a * e = c • e

/-- A von Neumann algebra with a minimal projection acts on a nonzero space: the minimal
projection is nonzero, so it sends some vector to a nonzero vector, witnessing `Nontrivial H`. -/
lemma IsMinimalProjection.nontrivial {N : VonNeumannAlgebra H} {e : H →L[ℂ] H}
    (he : IsMinimalProjection N e) : Nontrivial H :=
  let ⟨x, hx⟩ := ContinuousLinearMap.exists_ne_zero he.2.2.1
  ⟨⟨e x, 0, hx⟩⟩

/-- A minimal projection has no proper nonzero subprojection in `N`: if a projection `f ∈ N`
satisfies `f ≤ e` (the Loewner order on projections, equivalently the range inclusion
`ran f ⊆ ran e`, written algebraically as `e * f = f`), then `f = 0` or `f = e`. This recovers the
order-theoretic form of minimality from the corner definition `e N e = ℂ e`. -/
lemma IsMinimalProjection.no_proper_subprojection {N : VonNeumannAlgebra H}
    {e : H →L[ℂ] H} (he : IsMinimalProjection N e)
    {f : H →L[ℂ] H} (hf : IsStarProjection f) (hfN : f ∈ N) (hsub : e * f = f) :
    f = 0 ∨ f = e := by
  have hfe : f * e = f := by
    have := congrArg star hsub
    rwa [star_mul, he.1.isSelfAdjoint.star_eq, hf.isSelfAdjoint.star_eq] at this
  have hefe : e * f * e = f := by rw [hsub, hfe]
  obtain ⟨c, hc⟩ := he.2.2.2 f hfN
  rw [hefe] at hc
  have hidem : f * f = f := hf.isIdempotentElem
  rw [hc] at hidem
  have h2 : (c • e) * (c • e) = (c * c) • (e : H →L[ℂ] H) := by
    rw [smul_mul_smul_comm, he.1.isIdempotentElem]
  have hcc : (c * c) • (e : H →L[ℂ] H) = c • e := by rw [← h2, hidem]
  have hc2 : c * c = c := smul_left_injective ℂ he.2.2.1 hcc
  have h0 : c * (c - 1) = 0 := by rw [mul_sub, mul_one, hc2, sub_self]
  rcases mul_eq_zero.mp h0 with h | h
  · exact Or.inl (by rw [hc, h, zero_smul])
  · exact Or.inr (by rw [hc, sub_eq_zero.mp h, one_smul])

/-- An **abelian projection** of `N`: a star projection `p ∈ N` whose corner `p N p` is
commutative. Minimal projections are abelian (`IsMinimalProjection.isAbelianProjection`); the
general type I property (`IsTypeI`) is phrased through abelian projections. -/
def IsAbelianProjection (N : VonNeumannAlgebra H) (p : H →L[ℂ] H) : Prop :=
  IsStarProjection p ∧ p ∈ N ∧
    ∀ a ∈ N, ∀ b ∈ N, (p * a * p) * (p * b * p) = (p * b * p) * (p * a * p)

/-- A minimal projection is abelian: its corner `e N e = ℂ e` is one-dimensional, hence
commutative. -/
lemma IsMinimalProjection.isAbelianProjection {N : VonNeumannAlgebra H} {e : H →L[ℂ] H}
    (he : IsMinimalProjection N e) : IsAbelianProjection N e := by
  refine ⟨he.1, he.2.1, fun a haN b hbN => ?_⟩
  obtain ⟨c, hc⟩ := he.2.2.2 a haN
  obtain ⟨d, hd⟩ := he.2.2.2 b hbN
  rw [hc, hd, smul_mul_smul_comm, smul_mul_smul_comm, mul_comm c d]

/-- **Murray–von Neumann equivalence** of projections inside `N`: there is a partial isometry
`v ∈ N` with source projection `v⋆v = p` and range projection `vv⋆ = q`. -/
def MvNEquiv (N : VonNeumannAlgebra H) (p q : H →L[ℂ] H) : Prop :=
  ∃ v : H →L[ℂ] H, v ∈ N ∧ IsPartialIsometry v ∧ star v * v = p ∧ v * star v = q

/-- `p ∼[N] q` denotes Murray–von Neumann equivalence `MvNEquiv N p q` of projections inside `N`. -/
scoped notation:50 p:51 " ∼[" N "] " q:51 => MvNEquiv N p q

/-- Murray–von Neumann equivalence is reflexive on projections of `N`. -/
theorem MvNEquiv.refl {N : VonNeumannAlgebra H} {p : H →L[ℂ] H}
    (hp : IsStarProjection p) (hpN : p ∈ N) : p ∼[N] p :=
  ⟨p, hpN, hp.isPartialIsometry, by rw [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq],
    by rw [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]⟩

/-- Murray–von Neumann equivalence is symmetric. -/
theorem MvNEquiv.symm {N : VonNeumannAlgebra H} {p q : H →L[ℂ] H}
    (h : p ∼[N] q) : q ∼[N] p := by
  obtain ⟨v, hv, hpi, hvp, hvq⟩ := h
  exact ⟨star v, star_mem hv, IsPartialIsometry.star hpi, by rw [star_star, hvq],
    by rw [star_star, hvp]⟩

/-- Murray–von Neumann equivalence is transitive. -/
theorem MvNEquiv.trans {N : VonNeumannAlgebra H} {p q r : H →L[ℂ] H}
    (hpq : p ∼[N] q) (hqr : q ∼[N] r) : p ∼[N] r := by
  obtain ⟨v, hv, hvpi, hvp, hvq⟩ := hpq
  obtain ⟨w, hw, hwpi, hwq, hwr⟩ := hqr
  have hq : IsStarProjection q := hvq ▸ hvpi.isStarProjection_mul_star_self
  refine ⟨w * v, mul_mem hw hv, ?_, ?_, ?_⟩
  · unfold IsPartialIsometry
    calc w * v * star (w * v) * (w * v)
        = w * (v * star v) * (star w * w) * v := by simp only [star_mul, mul_assoc]
      _ = w * q * q * v := by rw [hvq, hwq]
      _ = w * q * v := by rw [mul_assoc w q q, hq.isIdempotentElem]
      _ = w * (star w * w) * v := by rw [hwq]
      _ = w * v := by rw [← mul_assoc w (star w) w, hwpi]
  · calc star (w * v) * (w * v) = star v * (star w * w) * v := by simp only [star_mul, mul_assoc]
      _ = star v * (v * star v) * v := by rw [hwq, hvq]
      _ = (star v * v) * (star v * v) := by simp only [mul_assoc]
      _ = star v * v := hvpi.isStarProjection_star_mul_self.isIdempotentElem
      _ = p := hvp
  · calc (w * v) * star (w * v) = w * (v * star v) * star w := by simp only [star_mul, mul_assoc]
      _ = w * (star w * w) * star w := by rw [hvq, ← hwq]
      _ = (w * star w) * (w * star w) := by simp only [mul_assoc]
      _ = w * star w := hwpi.isStarProjection_mul_star_self.isIdempotentElem
      _ = r := hwr

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
projection-level form of the triviality of the centre. -/
theorem IsFactor.central_projection_eq [Nontrivial H] {N : VonNeumannAlgebra H}
    (hN : IsFactor N) {e : H →L[ℂ] H} (he : IsCentralProjection N e) :
    e = 0 ∨ e = 1 := by
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
theorem isStarProjection_mem_commutant_iff {N : VonNeumannAlgebra H} {e : H →L[ℂ] H}
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
theorem IsFactor.exists_mul_ne [Nontrivial H] {N : VonNeumannAlgebra H} (hN : IsFactor N)
    {e q : H →L[ℂ] H} (heN : e ∈ N) (he0 : e ≠ 0) (hq0 : q ≠ 0) : ∃ a ∈ N, q * a * e ≠ 0 := by
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

/-! ### Comparison of projections -/

/-- The source projection of a Murray–von Neumann equivalence is a star projection. -/
lemma MvNEquiv.isStarProjection_left {N : VonNeumannAlgebra H} {p q : H →L[ℂ] H}
    (h : p ∼[N] q) : IsStarProjection p := by
  obtain ⟨v, _, hpi, hvp, _⟩ := h; exact hvp ▸ hpi.isStarProjection_star_mul_self

/-- The range projection of a Murray–von Neumann equivalence is a star projection. -/
lemma MvNEquiv.isStarProjection_right {N : VonNeumannAlgebra H} {p q : H →L[ℂ] H}
    (h : p ∼[N] q) : IsStarProjection q := by
  obtain ⟨v, _, hpi, _, hvq⟩ := h; exact hvq ▸ hpi.isStarProjection_mul_star_self

/-- For projections, the subprojection relation `e * f = f` is left/right symmetric. -/
lemma isStarProjection_subproj_comm {R : Type*} [Ring R] [StarRing R] {e f : R}
    (he : IsStarProjection e) (hf : IsStarProjection f) (h : e * f = f) : f * e = f := by
  have := congrArg star h
  rwa [star_mul, he.isSelfAdjoint.star_eq, hf.isSelfAdjoint.star_eq] at this

/-- The source projection of a partial isometry acts as a right identity. -/
lemma IsPartialIsometry.mul_source {R : Type*} [Monoid R] [StarMul R] {v : R}
    (h : IsPartialIsometry v) : v * (star v * v) = v := by rw [← mul_assoc]; exact h

/-- `p ≼ q` in `N`: `p` is Murray–von Neumann equivalent to a subprojection of `q`. -/
def MvNSub (N : VonNeumannAlgebra H) (p q : H →L[ℂ] H) : Prop :=
  ∃ q' : H →L[ℂ] H, q' ∈ N ∧ q * q' = q' ∧ p ∼[N] q'

/-- `p ≼[N] q` denotes the subordination relation `MvNSub N p q`: `p` is Murray–von Neumann
equivalent to a subprojection of `q` inside `N`. -/
scoped notation:50 p:51 " ≼[" N "] " q:51 => MvNSub N p q

/-- Subordination is reflexive on projections of `N`. -/
lemma MvNSub.refl {N : VonNeumannAlgebra H} {p : H →L[ℂ] H}
    (hp : IsStarProjection p) (hpN : p ∈ N) : p ≼[N] p :=
  ⟨p, hpN, hp.isIdempotentElem, MvNEquiv.refl hp hpN⟩

/-- An equivalence `q ∼[N] r'` transports a subprojection `q' ≤ q` to a subprojection of `r'` that
is Murray–von Neumann equivalent to `q'`. -/
theorem MvNEquiv.exists_subproj_equiv {N : VonNeumannAlgebra H} {q r' q' : H →L[ℂ] H}
    (hqr : q ∼[N] r') (hq' : IsStarProjection q') (hq'N : q' ∈ N) (hsub : q * q' = q') :
    ∃ r'' : H →L[ℂ] H, IsStarProjection r'' ∧ r'' ∈ N ∧ r' * r'' = r'' ∧ q' ∼[N] r'' := by
  obtain ⟨w, hwN, hwpi, hwq, hwr⟩ := hqr
  refine ⟨w * q' * star w, ⟨?_, ?_⟩, mul_mem (mul_mem hwN hq'N) (star_mem hwN), ?_, ?_⟩
  · change (w * q' * star w) * (w * q' * star w) = w * q' * star w
    simp only [mul_assoc]
    rw [← mul_assoc (star w) w (q' * star w), hwq, ← mul_assoc q q' (star w), hsub,
      ← mul_assoc q' q' (star w), hq'.isIdempotentElem]
  · change star (w * q' * star w) = w * q' * star w
    rw [star_mul, star_mul, star_star, hq'.isSelfAdjoint.star_eq, mul_assoc]
  · rw [← hwr]
    simp only [mul_assoc]
    rw [← mul_assoc (star w) w (q' * star w), hwq, ← mul_assoc q q' (star w), hsub]
  · refine ⟨w * q', mul_mem hwN hq'N, ?_, ?_, ?_⟩
    · change (w * q') * star (w * q') * (w * q') = w * q'
      rw [star_mul, hq'.isSelfAdjoint.star_eq]
      simp only [mul_assoc]
      rw [← mul_assoc (star w) w q', hwq, hsub, hq'.isIdempotentElem, hq'.isIdempotentElem]
    · change star (w * q') * (w * q') = q'
      rw [star_mul, hq'.isSelfAdjoint.star_eq, mul_assoc, ← mul_assoc (star w) w q', hwq, hsub,
        hq'.isIdempotentElem]
    · change (w * q') * star (w * q') = w * q' * star w
      rw [star_mul, hq'.isSelfAdjoint.star_eq]
      simp only [mul_assoc]
      rw [← mul_assoc q' q' (star w), hq'.isIdempotentElem]

/-- Subordination is transitive: `≼` is a preorder on the projections of `N`. -/
lemma MvNSub.trans {N : VonNeumannAlgebra H} {p q r : H →L[ℂ] H}
    (hpq : p ≼[N] q) (hqr : q ≼[N] r) : p ≼[N] r := by
  obtain ⟨q', hq'N, hqsub, hpq'⟩ := hpq
  obtain ⟨r', hr'N, hrsub, hqr'⟩ := hqr
  obtain ⟨r'', _, hr''N, hr'sub, hq'r''⟩ :=
    hqr'.exists_subproj_equiv hpq'.isStarProjection_right hq'N hqsub
  refine ⟨r'', hr''N, ?_, hpq'.trans hq'r''⟩
  calc r * r'' = r * (r' * r'') := by rw [hr'sub]
    _ = (r * r') * r'' := by rw [mul_assoc]
    _ = r' * r'' := by rw [hrsub]
    _ = r'' := hr'sub

/-- **Scaling step of the comparison theorem.** If the positive corner element
`(q a e)⋆ (q a e)` equals a positive scalar multiple `c • e` of `e` (with `c > 0`), then `e` is
subordinate to `q`: the normalised element `(√c)⁻¹ • (q a e)` is a partial isometry with source
`e` and range a subprojection of `q`. The hypotheses isolate the two analytic inputs of the
comparison theorem — the corner being scalar (minimality) and its positivity. -/
theorem mvNSub_of_posCorner {N : VonNeumannAlgebra H} {e q a : H →L[ℂ] H}
    (he : IsStarProjection e) (hq : IsStarProjection q)
    (heN : e ∈ N) (hqN : q ∈ N) (haN : a ∈ N)
    {c : ℝ} (hc : 0 < c)
    (hcorner : star (q * a * e) * (q * a * e) = (c : ℂ) • e) :
    e ≼[N] q := by
  set γ : ℂ := ((Real.sqrt c)⁻¹ : ℂ) with hγ
  set v : H →L[ℂ] H := γ • (q * a * e) with hv
  have hvN : v ∈ N := smul_mem γ (mul_mem (mul_mem hqN haN) heN)
  have hsrc : star v * v = e := by
    rw [hv, star_smul, smul_mul_smul_comm, hcorner, smul_smul]
    have hstar : star γ = γ := by rw [hγ, star_inv₀, ← starRingEnd_apply, Complex.conj_ofReal]
    rw [hstar, hγ, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt hc.le,
      inv_mul_cancel₀ (by exact_mod_cast hc.ne'), one_smul]
  have hve : v * e = v := by
    rw [hv, smul_mul_assoc, mul_assoc (q * a) e e, he.isIdempotentElem]
  have hvpi : IsPartialIsometry v := by
    unfold IsPartialIsometry
    rw [mul_assoc, hsrc, hve]
  refine ⟨v * star v, mul_mem hvN (star_mem hvN), ?_, ⟨v, hvN, hvpi, hsrc, rfl⟩⟩
  have hqv : q * v = v := by
    rw [hv, mul_smul_comm, ← mul_assoc, ← mul_assoc, hq.isIdempotentElem]
  rw [← mul_assoc, hqv]

/-- **Positivity of the corner scalar.** For a minimal projection `e` and `a ∈ N` with
`q a e ≠ 0`, the corner element `(q a e)⋆ (q a e) = e (a⋆ q a) e` equals a *strictly positive
real* scalar multiple of `e`. (Reality comes from self-adjointness; strict positivity from
evaluating on a nonzero vector of `e H` on which `q a e` does not vanish.) -/
lemma IsMinimalProjection.posCorner {N : VonNeumannAlgebra H} {e : H →L[ℂ] H}
    (he : IsMinimalProjection N e) {q a : H →L[ℂ] H} (hq : IsStarProjection q)
    (hqN : q ∈ N) (haN : a ∈ N) (hne : q * a * e ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ star (q * a * e) * (q * a * e) = (c : ℂ) • e := by
  set x := q * a * e with hx
  have hxx : star x * x = e * (star a * q * a) * e := by
    rw [hx, star_mul, star_mul, he.1.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq]
    rw [mul_assoc, mul_assoc, mul_assoc, ← mul_assoc q q, hq.isIdempotentElem]
    simp only [mul_assoc]
  obtain ⟨c', hc'⟩ := he.2.2.2 (star a * q * a) (mul_mem (mul_mem (star_mem haN) hqN) haN)
  rw [← hxx] at hc'
  have hconj : (starRingEnd ℂ) c' = c' := by
    have hsa : star (star x * x) = star x * x := by rw [star_mul, star_star]
    rw [hc', star_smul, he.1.isSelfAdjoint.star_eq] at hsa
    rw [starRingEnd_apply]; exact smul_left_injective ℂ he.2.2.1 hsa
  have hxe : x * e = x := by rw [hx, mul_assoc, he.1.isIdempotentElem]
  obtain ⟨η, hη⟩ : ∃ η, x η ≠ 0 := by
    by_contra h
    exact hne (by ext η; exact not_not.mp (not_exists.mp h η))
  set ξ := e η with hξ
  have hxξ : x ξ ≠ 0 := by
    rw [hξ, ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, hxe]; exact hη
  have heξ : e ξ = ξ := by
    rw [hξ, ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, he.1.isIdempotentElem]
  have hξne : ξ ≠ 0 := fun h => hxξ (by rw [h, map_zero])
  have hinner : ‖x ξ‖ ^ 2 = c'.re * ‖ξ‖ ^ 2 := by
    have e1 : inner ℂ ((star x * x) ξ) ξ = inner ℂ (x ξ) (x ξ) := by
      rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_left]
    have e2 : inner ℂ ((star x * x) ξ) ξ = (starRingEnd ℂ) c' * inner ℂ ξ ξ := by
      rw [hc', ContinuousLinearMap.smul_apply, heξ, inner_smul_left]
    have e3 : inner ℂ (x ξ) (x ξ) = (starRingEnd ℂ) c' * inner ℂ ξ ξ := e1.symm.trans e2
    have hre := congrArg RCLike.re e3
    rw [inner_self_eq_norm_sq, inner_self_eq_norm_sq_to_K] at hre
    simp only [RCLike.mul_re, RCLike.mul_im, RCLike.conj_re, RCLike.conj_im, RCLike.ofReal_re,
      RCLike.ofReal_im, pow_two, mul_zero, zero_mul, add_zero, sub_zero] at hre
    rw [show RCLike.re c' = c'.re from rfl] at hre
    nlinarith [hre]
  have hξpos : 0 < ‖ξ‖ ^ 2 := pow_pos (norm_pos_iff.mpr hξne) 2
  have hxξpos : 0 < ‖x ξ‖ ^ 2 := pow_pos (norm_pos_iff.mpr hxξ) 2
  have hcre : c' = (c'.re : ℂ) := (Complex.conj_eq_iff_re.mp hconj).symm
  refine ⟨c'.re, by nlinarith [hinner, hξpos, hxξpos], ?_⟩
  rw [hc']; exact congrArg (· • e) hcre

/-- A minimal projection is subordinate to any projection it "meets": if some `a ∈ N` has
`q a e ≠ 0`, then `e ≼ q`. Combined with central supports (which guarantee `q a e ≠ 0` for every
nonzero `q` in a factor) this yields the comparison theorem `minimal e ≼ q`. -/
lemma IsMinimalProjection.mvNSub_of_ne {N : VonNeumannAlgebra H} {e : H →L[ℂ] H}
    (he : IsMinimalProjection N e) {q a : H →L[ℂ] H} (hq : IsStarProjection q)
    (hqN : q ∈ N) (haN : a ∈ N) (hne : q * a * e ≠ 0) : e ≼[N] q := by
  obtain ⟨c, hcpos, hcorner⟩ := he.posCorner hq hqN haN hne
  exact mvNSub_of_posCorner he.1 hq he.2.1 hqN haN hcpos hcorner

/-- **Comparison theorem (minimal projection case).** In a factor, a minimal projection `e` is
Murray–von Neumann subordinate to *every* nonzero projection `q`: `e ≼ q`. This combines the
scaling lemma (via `mvNSub_of_ne`) with the central-support input
(`IsFactor.exists_mul_ne`, which supplies an `a ∈ N` with `q a e ≠ 0`). It is the form of
comparison needed to show a maximal orthogonal family of minimal projections exhausts the
identity. -/
theorem IsMinimalProjection.mvNSub_of_isFactor [Nontrivial H] {N : VonNeumannAlgebra H}
    (hN : IsFactor N) {e : H →L[ℂ] H} (he : IsMinimalProjection N e)
    {q : H →L[ℂ] H} (hq : IsStarProjection q) (hqN : q ∈ N) (hq0 : q ≠ 0) :
    e ≼[N] q := by
  obtain ⟨a, haN, hane⟩ := hN.exists_mul_ne he.2.1 he.2.2.1 hq0
  exact he.mvNSub_of_ne hq hqN haN hane

end VonNeumannAlgebra
