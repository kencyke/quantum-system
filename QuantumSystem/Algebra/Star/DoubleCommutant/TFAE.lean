module

public import QuantumSystem.Algebra.Star.DoubleCommutant.SOTClosedSubAlgebra
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.FiniteRank
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.RankOne
public import QuantumSystem.ForMathlib.Analysis.VonNeumannAlgebra.Commutant
public import Mathlib.Tactic.TFAE

@[expose] public section

/-!
# The bicommutant theorem as a list of equivalent conditions

This file packages the two halves proved in
`QuantumSystem.Algebra.Star.DoubleCommutant.WOTClosedSubAlgebra` and
`QuantumSystem.Algebra.Star.DoubleCommutant.SOTClosedSubAlgebra` into the three-condition form of
von Neumann's bicommutant theorem: for a `*`-subalgebra `A ⊆ B(H)` acting non-degenerately,

1. `A` equals its own double commutant,
2. `A` is closed in the weak operator topology,
3. `A` is closed in the strong operator topology

are equivalent.

## Main results

* `DoubleCommutant.bicommutant_tfae`: the equivalence for a possibly non-unital `*`-subalgebra
  acting non-degenerately.
* `DoubleCommutant.bicommutant_tfae_starSubalgebra`: the unital special case, where non-degeneracy
  is automatic. This is the form in which the theorem is usually quoted.
* `DoubleCommutant.bicommutant_tfae_image` (and its unital special case
  `DoubleCommutant.bicommutant_tfae_image_starSubalgebra`): the two closedness conditions spelled
  out as closedness of the image of `A` in the corresponding Mathlib type-copy.
* `DoubleCommutant.one_mem_of_isSOTClosed` (and `WOTClosedSubalgebra.one_mem_of_isWOTClosed`): a
  non-degenerate `*`-subalgebra satisfying any of the three conditions contains `1`. This is what
  the non-unital form adds over the unital one, and it is also what makes the extra scope purely
  negative.
* `DoubleCommutant.bicommutant_tfae_finiteRankOperators`: the witness that the non-unital
  generality is inhabited — on an infinite-dimensional `H` the theorem applies to `F(H)`, which
  does not contain `1`. That it is inhabited only *negatively* is
  `DoubleCommutant.not_isWOTClosed_finiteRankOperators`,
  `DoubleCommutant.not_isSOTClosed_finiteRankOperators` and
  `DoubleCommutant.centralizer_centralizer_ne_finiteRankOperators`.
* `VonNeumannAlgebra.ofIsWOTClosed`, `VonNeumannAlgebra.ofIsSOTClosed`: the payoff — a WOT-closed
  (resp. SOT-closed) unital `*`-subalgebra *is* a von Neumann algebra, which is what makes the
  topological definition of a von Neumann algebra usable against Mathlib's algebraic one.

## Which form is standard

The literature overwhelmingly quotes the **unital** three-condition form
(`bicommutant_tfae_starSubalgebra`); the non-degenerate form of `bicommutant_tfae` is the more
general one, adopted here because it also covers algebras that do not contain `1` — the compact
operators `K(H)` and the finite-rank operators `F(H)` on an infinite-dimensional `H` are
non-degenerate and non-unital, and the unital form says nothing about them. Norm-closedness, which
some sources additionally assume, is deliberately *not* assumed: no step of the proof consumes it
and each of the three conditions implies it.

The extra scope so gained is inhabited only by algebras for which all three conditions *fail*:
by `one_mem_of_isSOTClosed`, a non-degenerate algebra satisfying any one of them contains `1` and
is therefore already covered by the unital form. That is not a defect — it is what the general
form is for, since the unital form cannot so much as state that `F(H)` is not WOT-closed.

## Note on non-degeneracy

Non-degeneracy is not a technical convenience: without it the equivalence is false. For a
decomposition `H = H₁ ⊕ H₂` with `H₂ ≠ 0` the algebra `B(H₁) ⊕ 0` is WOT-closed but is strictly
smaller than its double commutant, which is `B(H₁) ⊕ ℂ1`. (For `H₂ = 0` there is nothing to
separate and the algebra is all of `B(H)`.) Containing `1` is the standard sufficient condition,
which is why the unital corollaries carry no extra hypothesis; conversely, non-degeneracy plus any
one of the three conditions *implies* `1 ∈ A` (`WOTClosedSubalgebra.one_mem_of_isWOTClosed`,
`one_mem_of_isSOTClosed`), so the two hypothesis packages differ exactly on the algebras where the
equivalence holds negatively.

Non-degeneracy is consumed **only** by the implication 3 → 1. The other two implications are
hypothesis-free: 1 → 2 because every double commutant is WOT-closed, and 2 → 3 because the SOT is
finer than the WOT (`StrongOperatorTopology.isSOTClosed_of_isWOTClosed`). The proof below is
routed as the cycle 1 → 2 → 3 → 1 precisely so that `hnd` is used at that one point and nowhere
else.
-/

/-!
## `F(H)` against the rest of the development

The finite-rank operators are defined in
`QuantumSystem.ForMathlib.Analysis.InnerProductSpace.FiniteRank`, which imports Mathlib only. The
facts below combine them with declarations from *other* `ForMathlib` files
(`InnerProductSpace.ActsNondegenerately`,
`ContinuousLinearMap.exists_eq_smul_one_of_forall_rankOne_comm`), so they live here.
-/

/-- `S′` denotes the commutant `Set.centralizer S` of a set of operators, the prime notation of the
operator-algebra literature (see `docs/math/bicommutant-theorem.md`, convention (C8)). Local to this
file: the file never opens the `VonNeumannAlgebra` scope, so this does not collide with
`VonNeumannAlgebra.commutant`'s own `′` (`QuantumSystem.ForMathlib.Analysis.VonNeumannAlgebra.Commutant`),
which is the same notation one level up, for a `VonNeumannAlgebra` rather than a bare `Set`. -/
local postfix:max "′" => Set.centralizer

namespace InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **`F(H)` acts non-degenerately**, on every Hilbert space: the rank-one operator
`|x⟩⟨x| : z ↦ ⟪x, z⟫ • x` does not annihilate `x` unless `x = 0`. -/
theorem actsNondegenerately_finiteRankOperators :
    ActsNondegenerately (finiteRankOperators (H := H) : Set (H →L[ℂ] H)) := by
  intro x hx
  have h := hx (rankOne ℂ x x) (rankOne_mem_finiteRankOperators x x)
  have h' : (inner ℂ x x : ℂ) • x = 0 := by simpa using h
  rcases smul_eq_zero.mp h' with h1 | h1
  · exact inner_self_eq_zero.mp h1
  · exact h1

/-- **The commutant of `F(H)` is the scalars.** An operator commuting with every finite-rank
operator commutes in particular with every rank-one operator `|x⟩⟨y|`, and that already forces it
to be a multiple of the identity
(`ContinuousLinearMap.exists_eq_smul_one_of_forall_rankOne_comm`). -/
theorem centralizer_finiteRankOperators :
    (finiteRankOperators (H := H) : Set (H →L[ℂ] H))′
      = Set.range fun c : ℂ => c • (1 : H →L[ℂ] H) := by
  refine Set.Subset.antisymm (fun S hS => ?_) ?_
  · have hcomm : ∀ x y : H, S ∘L rankOne ℂ x y = rankOne ℂ x y ∘L S := by
      intro x y
      have h := hS _ (rankOne_mem_finiteRankOperators x y)
      simpa [ContinuousLinearMap.mul_def] using h.symm
    obtain ⟨c, hc⟩ := ContinuousLinearMap.exists_eq_smul_one_of_forall_rankOne_comm hcomm
    exact ⟨c, hc.symm⟩
  · rintro _ ⟨c, rfl⟩
    exact Set.center_subset_centralizer _ (Set.smul_mem_center c Set.one_mem_center)

/-- **`F(H)'' = B(H)`.** The double commutant of the finite-rank operators is everything, because
their commutant is the scalars (`centralizer_finiteRankOperators`) and the scalars are central.

On an infinite-dimensional `H` this is strictly larger than `F(H)`, which is why all three
conditions of the bicommutant theorem fail for `F(H)`; on a finite-dimensional `H` it is an
equality, `F(H)` being all of `B(H)` there. -/
theorem centralizer_centralizer_finiteRankOperators :
    (finiteRankOperators (H := H) : Set (H →L[ℂ] H))′′ = Set.univ := by
  rw [centralizer_finiteRankOperators, Set.centralizer_eq_top_iff_subset]
  rintro _ ⟨c, rfl⟩
  exact Set.smul_mem_center c Set.one_mem_center

end InnerProductSpace

namespace DoubleCommutant

open InnerProductSpace StrongOperatorTopology WeakOperatorTopology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "B" => (H →L[ℂ] H)

/-- **The bicommutant theorem.** For a possibly non-unital `*`-subalgebra of `B(H)` acting
non-degenerately, equalling its own double commutant, being WOT-closed, and being SOT-closed are
all equivalent.

Only the implication 3 → 1 consumes the non-degeneracy hypothesis; see the module docstring. -/
theorem bicommutant_tfae (A : NonUnitalStarSubalgebra ℂ B) (hnd : ActsNondegenerately (A : Set B)) :
    List.TFAE [
      (A : Set B)′′ = (A : Set B),
      IsWOTClosed (H := H) (A : Set B),
      IsSOTClosed (H := H) (A : Set B)] := by
  tfae_have 1 → 2 := by
    intro h
    rw [← h]
    exact isWOTClosed_centralizer_centralizer (H := H) (A : Set B)
  tfae_have 2 → 3 := isSOTClosed_of_isWOTClosed (H := H)
  tfae_have 3 → 1 := SOTClosedSubalgebra.doubleCommutant_eq_of_isSOTClosed A hnd
  tfae_finish

/-- Unital special case of `DoubleCommutant.bicommutant_tfae`, and the form in which the theorem is
usually quoted: since `1 ∈ A`, the algebra acts non-degenerately and no extra hypothesis is
needed. -/
theorem bicommutant_tfae_starSubalgebra (A : StarSubalgebra ℂ B) :
    List.TFAE [
      (A : Set B)′′ = (A : Set B),
      IsWOTClosed (H := H) (A : Set B),
      IsSOTClosed (H := H) (A : Set B)] :=
  bicommutant_tfae A.toNonUnitalStarSubalgebra (actsNondegenerately_of_one_mem A.one_mem)

/-- `DoubleCommutant.bicommutant_tfae` with the two closedness conditions spelled out as closedness
of the image of `A` in the WOT resp. pointwise-convergence type-copy of `B(H)`. Stated at the same
generality as `DoubleCommutant.bicommutant_tfae`, since `isWOTClosed_iff_isClosed_image` and
`isSOTClosed_iff_isClosed_image` hold for an arbitrary set of operators. -/
theorem bicommutant_tfae_image (A : NonUnitalStarSubalgebra ℂ B)
    (hnd : ActsNondegenerately (A : Set B)) :
    List.TFAE [
      (A : Set B)′′ = (A : Set B),
      IsClosed (ContinuousLinearMapWOT.ContinuousLinearMap.toWOTCLM
        (σ := RingHom.id ℂ) (E := H) (F := H) '' (A : Set B)),
      IsClosed (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
        '' (A : Set B))] := by
  rw [← isWOTClosed_iff_isClosed_image, ← isSOTClosed_iff_isClosed_image]
  exact bicommutant_tfae A hnd

/-- Unital special case of `DoubleCommutant.bicommutant_tfae_image`; equivalently,
`DoubleCommutant.bicommutant_tfae_starSubalgebra` with the two closedness conditions spelled out as
closedness of the image of `A` in the WOT resp. pointwise-convergence type-copy of `B(H)`. -/
theorem bicommutant_tfae_image_starSubalgebra (A : StarSubalgebra ℂ B) :
    List.TFAE [
      (A : Set B)′′ = (A : Set B),
      IsClosed (ContinuousLinearMapWOT.ContinuousLinearMap.toWOTCLM
        (σ := RingHom.id ℂ) (E := H) (F := H) '' (A : Set B)),
      IsClosed (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
        '' (A : Set B))] :=
  bicommutant_tfae_image A.toNonUnitalStarSubalgebra (actsNondegenerately_of_one_mem A.one_mem)

/-- **A non-degenerate `*`-subalgebra satisfying any one of the three conditions contains `1`.**
Stated for the WOT in `WOTClosedSubalgebra.one_mem_of_isWOTClosed`; this is the SOT companion.

Together the two say that the extra scope of the non-unital form over the unital one contains only
*negative* instances: a non-degenerate `*`-subalgebra that does not contain `1` fails all three
conditions. -/
theorem one_mem_of_isSOTClosed (A : NonUnitalStarSubalgebra ℂ B)
    (hnd : ActsNondegenerately (A : Set B)) (hA : IsSOTClosed (H := H) (A : Set B)) :
    (1 : B) ∈ A :=
  WOTClosedSubalgebra.one_mem_of_isWOTClosed A hnd
    (SOTClosedSubalgebra.isWOTClosed_of_isSOTClosed A hnd hA)

/-- **The non-unital generality is inhabited.** On an infinite-dimensional Hilbert space the
finite-rank operators `F(H)` act non-degenerately and do not contain `1`, so
`DoubleCommutant.bicommutant_tfae` applies to them while
`DoubleCommutant.bicommutant_tfae_starSubalgebra` does not. This is the witness that the
non-degeneracy hypothesis really is weaker than unitality, and not merely formally so.

It is inhabited only *negatively*, and necessarily so: by `DoubleCommutant.one_mem_of_isSOTClosed`
a non-degenerate `*`-subalgebra satisfying any of the three conditions contains `1`. For `F(H)` all
three therefore fail together, exactly as the equivalence demands — see
`DoubleCommutant.not_isWOTClosed_finiteRankOperators`,
`DoubleCommutant.not_isSOTClosed_finiteRankOperators` and
`DoubleCommutant.centralizer_centralizer_ne_finiteRankOperators`, the last of which sharpens the
failure to `F(H)'' = B(H) ≠ F(H)`. -/
theorem bicommutant_tfae_finiteRankOperators (h : ¬ FiniteDimensional ℂ H) :
    (1 : B) ∉ finiteRankOperators (H := H) ∧
      List.TFAE [
        (finiteRankOperators (H := H) : Set B)′′ = (finiteRankOperators (H := H) : Set B),
        IsWOTClosed (H := H) (finiteRankOperators (H := H) : Set B),
        IsSOTClosed (H := H) (finiteRankOperators (H := H) : Set B)] :=
  ⟨one_notMem_finiteRankOperators h,
    bicommutant_tfae _ actsNondegenerately_finiteRankOperators⟩

/-- On an infinite-dimensional `H` the finite-rank operators are **not** WOT-closed: they act
non-degenerately, so WOT-closedness would force `1 ∈ F(H)`. -/
theorem not_isWOTClosed_finiteRankOperators (h : ¬ FiniteDimensional ℂ H) :
    ¬ IsWOTClosed (H := H) (finiteRankOperators (H := H) : Set B) := fun hA =>
  one_notMem_finiteRankOperators h
    (WOTClosedSubalgebra.one_mem_of_isWOTClosed _ actsNondegenerately_finiteRankOperators hA)

/-- On an infinite-dimensional `H` the finite-rank operators are **not** SOT-closed. -/
theorem not_isSOTClosed_finiteRankOperators (h : ¬ FiniteDimensional ℂ H) :
    ¬ IsSOTClosed (H := H) (finiteRankOperators (H := H) : Set B) := fun hA =>
  one_notMem_finiteRankOperators h
    (one_mem_of_isSOTClosed _ actsNondegenerately_finiteRankOperators hA)

/-- On an infinite-dimensional `H` the finite-rank operators are **not** their own double
commutant: `F(H)'' = B(H)` by `InnerProductSpace.centralizer_centralizer_finiteRankOperators`,
while `1 ∉ F(H)`. -/
theorem centralizer_centralizer_ne_finiteRankOperators (h : ¬ FiniteDimensional ℂ H) :
    (finiteRankOperators (H := H) : Set B)′′ ≠ (finiteRankOperators (H := H) : Set B) := by
  intro heq
  refine one_notMem_finiteRankOperators h ?_
  change (1 : B) ∈ (finiteRankOperators (H := H) : Set B)
  rw [← heq, centralizer_centralizer_finiteRankOperators]
  trivial

end DoubleCommutant

namespace VonNeumannAlgebra

open InnerProductSpace StrongOperatorTopology WeakOperatorTopology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **A WOT-closed unital `*`-subalgebra is a von Neumann algebra.** This is the reason the
bicommutant theorem is proved: Mathlib defines `VonNeumannAlgebra` by the *algebraic* condition
`A'' = A`, and this constructor supplies that field from the *topological* condition, so that an
algebra produced as a weak limit closure can be used as a von Neumann algebra. -/
noncomputable def ofIsWOTClosed (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (hA : IsWOTClosed (H := H) (A : Set (H →L[ℂ] H))) : VonNeumannAlgebra H where
  toStarSubalgebra := A
  centralizer_centralizer' :=
    WOTClosedSubalgebra.doubleCommutant_eq_of_isWOTClosed_starSubalgebra A hA

/-- The carrier of `VonNeumannAlgebra.ofIsWOTClosed A hA` is `A` itself: the constructor supplies
only the `centralizer_centralizer'` field and leaves the underlying `*`-subalgebra untouched. -/
@[simp] lemma coe_ofIsWOTClosed (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (hA : IsWOTClosed (H := H) (A : Set (H →L[ℂ] H))) :
    (ofIsWOTClosed A hA : Set (H →L[ℂ] H)) = (A : Set (H →L[ℂ] H)) := rfl

/-- **An SOT-closed unital `*`-subalgebra is a von Neumann algebra.** The SOT companion of
`VonNeumannAlgebra.ofIsWOTClosed`. -/
noncomputable def ofIsSOTClosed (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (hA : IsSOTClosed (H := H) (A : Set (H →L[ℂ] H))) : VonNeumannAlgebra H :=
  ofIsWOTClosed A (SOTClosedSubalgebra.isWOTClosed_of_isSOTClosed_starSubalgebra A hA)

/-- The carrier of `VonNeumannAlgebra.ofIsSOTClosed A hA` is `A` itself; the SOT companion of
`VonNeumannAlgebra.coe_ofIsWOTClosed`. -/
@[simp] lemma coe_ofIsSOTClosed (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (hA : IsSOTClosed (H := H) (A : Set (H →L[ℂ] H))) :
    (ofIsSOTClosed A hA : Set (H →L[ℂ] H)) = (A : Set (H →L[ℂ] H)) := rfl

/-- A WOT-closed unital `*`-subalgebra is the von Neumann algebra it generates: the topological
closedness condition and `VonNeumannAlgebra.generated` agree on it. -/
lemma generated_coe_of_isWOTClosed (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (hA : IsWOTClosed (H := H) (A : Set (H →L[ℂ] H))) :
    (generated (A : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H)) = (A : Set (H →L[ℂ] H)) := by
  rw [coe_generated_of_star_eq (StarMemClass.star_coe_eq A),
    WOTClosedSubalgebra.doubleCommutant_eq_of_isWOTClosed_starSubalgebra A hA]

end VonNeumannAlgebra
