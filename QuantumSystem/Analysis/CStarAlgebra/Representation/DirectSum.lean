/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.Hom
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Lp.lpHolder
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import QuantumSystem.Analysis.CStarAlgebra.Representation.Basic
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.InvariantSubspace

/-!
# Direct sum of a family of representations

For a family `R : ι → CStarRep A` of representations of a non-unital C\*-algebra `A`, this file
constructs:

* `CStarRep.directSumHilbert R` — the `ℓ²`-direct sum Hilbert space `⨁ᵢ (R i).H`.
* `CStarRep.directSumRep R` — the block-diagonal representation
  `A →⋆ₙₐ[ℂ] (directSumHilbert R →L[ℂ] directSumHilbert R)`, and `CStarRep.directSum R` its
  bundled form.
* `CStarRep.directSumRep_norm_le` — the operator-norm bound `‖directSumRep R a‖ ≤ ‖a‖`.

`directSumRep R` is faithful exactly when the family separates points
(`CStarRep.SeparatesPoints R`); see `CStarRep.directSumRep_injective_iff`.

## Instances

Both Gelfand–Naimark witnesses are such direct sums: `GNS.DirectSum.rep` sums the GNS
representations of *all* pure states (`GNS.DirectSum.pureStateFamily`), and `GNS.normingRep` a
countable norming subfamily. Two pure states whose GNS representations are unitarily equivalent
contribute two unitarily equivalent summands, so the pure-state direct sum repeats each
unitary-equivalence class once per pure state realising it.

## Main definitions

* `CStarRep.directSumHilbert` — the direct-sum Hilbert space.
* `CStarRep.directSumRep` — the block-diagonal `*`-representation, and `CStarRep.directSum` its
  bundled form.
* `CStarRep.SeparatesPoints` — the family separates the points of `A`.

## Main results

* `CStarRep.directSumRep_injective_iff` — the direct sum is faithful iff the family separates
  points.
* `CStarRep.directSumRep_injective_of`, `directSumRep_isometry_of`,
  `directSumRep_isClosed_range_of` — faithfulness, isometry and closed range for a family that
  separates points.
* `CStarRep.directSumRep_actsNondegenerately_of` — non-degeneracy is inherited from the members.
-/

@[expose] public section

open ENNReal
open scoped InnerProduct

namespace CStarRep

universe u v w

variable {A : Type u} [NonUnitalCStarAlgebra A] {ι : Type w} (R : ι → CStarRep.{u, v} A)

/-- The `ℓ²` direct-sum Hilbert space `⨁ᵢ (R i).H` of a family of representations. -/
noncomputable abbrev directSumHilbert :=
  ↥(lp (fun i : ι => (R i).H) 2)

/-- The block-diagonal action of `a` on the direct-sum Hilbert space: Mathlib's `lp.mapCLM` of
the fibrewise operators `π_i a`, each of norm at most `‖a‖`. -/
noncomputable def directSumCLM (a : A) : directSumHilbert R →L[ℂ] directSumHilbert R :=
  lp.mapCLM 2 (fun i => (R i).π a) (norm_nonneg a)
    fun i => NonUnitalStarAlgHom.norm_apply_le (R i).π a

/-- The `i`-th coordinate of the block-diagonal action is the action of `π_i a`. -/
@[simp] lemma directSumCLM_apply (a : A) (x : directSumHilbert R) (i : ι) :
    (directSumCLM R a x : ∀ i, (R i).H) i = (R i).π a (x i) := rfl

/-- Block-diagonality is compatible with the `*`-structure. -/
lemma directSumCLM_adjoint (a : A) : (directSumCLM R a)† = directSumCLM R (star a) := by
  refine ContinuousLinearMap.ext fun x => ?_
  apply ext_inner_right ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  congr with i
  rw [directSumCLM_apply, directSumCLM_apply, ← ContinuousLinearMap.adjoint_inner_left]
  rw [map_star]
  rw [ContinuousLinearMap.star_eq_adjoint]

/-- The block-diagonal `*`-representation on the direct sum of a family of representations. -/
noncomputable def directSumRep : A →⋆ₙₐ[ℂ] (directSumHilbert R →L[ℂ] directSumHilbert R) where
  toFun a := directSumCLM R a
  map_mul' a b := by ext x i; simp
  map_zero' := by ext x i; simp
  map_add' a b := by ext x i; simp
  map_smul' c a := by ext x i; simp
  map_star' a := by
    rw [← directSumCLM_adjoint]
    rfl

/-- The operator-norm bound `‖directSumRep R a‖ ≤ ‖a‖`. -/
lemma directSumRep_norm_le (a : A) : ‖directSumRep R a‖ ≤ ‖a‖ :=
  lp.norm_mapCLM_le _ _ (norm_nonneg a) fun i => NonUnitalStarAlgHom.norm_apply_le (R i).π a

/-- A family of representations *separates points* if whenever every member annihilates `a`, we
have `a = 0`. -/
def SeparatesPoints : Prop :=
  ∀ a : A, (∀ i : ι, (R i).π a = 0) → a = 0

variable {R}

/-- **Faithfulness of the direct-sum representation** under a points-separation condition on the
family: if the family separates `A`, then `directSumRep R` is injective. -/
lemma directSumRep_injective_of (h_sep : SeparatesPoints R) :
    Function.Injective (directSumRep R) := by
  classical
  intro a b hab
  rw [← sub_eq_zero]
  have h_diff_zero : directSumRep R (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  apply h_sep
  intro i
  ext v
  -- Evaluate `directSumRep R (a - b) = 0` at the vector `lp.single 2 i v`.
  have h0 := congrArg (fun y : directSumHilbert R => y.val i)
    (DFunLike.congr_fun h_diff_zero (lp.single 2 i v))
  simpa [directSumRep, lp.single_apply_self] using h0

/-- **The direct-sum representation is faithful iff the family separates points.** The forward
direction: an `a` that every member annihilates acts as `0` on every coordinate, so
`directSumRep R a = 0 = directSumRep R 0`. -/
lemma directSumRep_injective_iff : Function.Injective (directSumRep R) ↔ SeparatesPoints R := by
  refine ⟨fun h a ha => h ?_, directSumRep_injective_of⟩
  rw [map_zero]
  ext x i
  simp [directSumRep, ha]

variable (R) in
/-- The direct sum of a family of representations, bundled as a `CStarRep`: the Hilbert space
`directSumHilbert R` with the block-diagonal representation `directSumRep R`. -/
noncomputable def directSum : CStarRep.{u, max w v} A where
  H := directSumHilbert R
  π := directSumRep R

variable (R) in
/-- The action of the bundled direct sum `directSum R` is `directSumRep R`. -/
@[simp] lemma directSum_π : (directSum R).π = directSumRep R :=
  rfl

/-- If the family separates points, the direct-sum representation is isometric: an injective
`*`-homomorphism between C\*-algebras is isometric. -/
lemma directSumRep_isometry_of (h_sep : SeparatesPoints R) : Isometry (directSumRep R) :=
  AddMonoidHomClass.isometry_of_norm _ fun a =>
    NonUnitalStarAlgHom.norm_map _ (directSumRep_injective_of h_sep) a

/-- If the family separates points, the image of the direct-sum representation is norm closed,
hence a C\*-subalgebra of `directSumHilbert R →L[ℂ] directSumHilbert R`. -/
lemma directSumRep_isClosed_range_of (h_sep : SeparatesPoints R) :
    IsClosed (NonUnitalStarAlgHom.range (directSumRep R) :
      Set (directSumHilbert R →L[ℂ] directSumHilbert R)) := by
  rw [NonUnitalStarAlgHom.coe_range]
  exact (directSumRep_isometry_of h_sep).isClosedEmbedding.isClosed_range

/-- A direct sum of non-degenerate representations is non-degenerate: a vector killed by every
`directSumRep R a` has every coordinate killed by the whole image of the corresponding member. -/
lemma directSumRep_actsNondegenerately_of
    (h : ∀ i, InnerProductSpace.ActsNondegenerately
      (Set.range ((R i).π : A → ((R i).H →L[ℂ] (R i).H)))) :
    InnerProductSpace.ActsNondegenerately
      (Set.range (directSumRep R : A → (directSumHilbert R →L[ℂ] directSumHilbert R))) := by
  intro x hx
  apply Subtype.ext
  funext i
  have hi : ∀ a : A, (R i).π a (x.val i) = 0 := by
    intro a
    have h0 := congrArg (fun y : directSumHilbert R => y.val i) (hx _ ⟨a, rfl⟩)
    simpa [directSumRep] using h0
  simpa using h i _ (by rintro _ ⟨a, rfl⟩; exact hi a)

end CStarRep
