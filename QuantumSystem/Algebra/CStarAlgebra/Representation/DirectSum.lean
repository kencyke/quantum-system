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
public import QuantumSystem.Algebra.CStarAlgebra.Representation.Family
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.InvariantSubspace

/-!
# Direct sum of a sector family

For a sector family `F : SectorFamily A` on a non-unital C\*-algebra
`A`, this file constructs:

* `F.directSumHilbert` — the `ℓ²`-direct sum Hilbert space
  `⨁_{α : F.Index} (F.rep α).H`.
* `F.directSumRep` — the block-diagonal universal representation
  `A →⋆ₙₐ[ℂ] 𝓑(F.directSumHilbert)`.
* `F.directSumRep_norm_le` — the operator-norm bound
  `‖F.directSumRep a‖ ≤ ‖a‖`.

The construction is criterion-agnostic: it depends only on the
indexed family of representations, not on any selection predicate
`P : CStarRep A → Prop`.  Faithfulness of `directSumRep` requires that
the family separates points (`F.SeparatesPoints`); see the
`directSumRep_injective_of` theorem.

## Instances

Both Gelfand–Naimark witnesses are direct sums of sector families:
`GNS.DirectSum.rep` sums the GNS representations of *all* pure states
(`GNS.DirectSum.pureStateFamily`), and `GNS.normingRep` a countable
norming subfamily.  Two pure states whose GNS representations are
unitarily equivalent contribute the "same sector" twice (once per
state), so the pure-state direct sum is not a true sector
decomposition.  Applied to a family satisfying `SectorFamily.IsSkeleton`
(one representative per unitary-equivalence class), the construction of
this file avoids the over-counting.

## Main definitions

* `SectorFamily.directSumHilbert` — the direct-sum Hilbert space.
* `SectorFamily.sectorComponent` / `.sectorEmbed` — coordinate
  projection / embedding.
* `SectorFamily.directSumRep` — the block-diagonal universal
  `*`-representation, and `SectorFamily.toCStarRep` its bundled form.

## Main results

* `SectorFamily.directSumRep_injective_of`, `directSumRep_isometry_of`,
  `directSumRep_isClosed_range_of` — faithfulness, isometry and closed
  range for a family that separates points.
* `SectorFamily.directSumRep_actsNondegenerately_of` — non-degeneracy is
  inherited from the members.
-/

@[expose] public section

open ENNReal
open scoped InnerProduct ComplexHilbertSpace

namespace SectorFamily

universe u v w

variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- The `ℓ²` direct-sum Hilbert space of the family. -/
noncomputable abbrev directSumHilbert (F : SectorFamily.{u, v, w} A) :=
  ↥(lp (fun α : F.Index => (F.rep α).H) 2)

noncomputable instance (F : SectorFamily.{u, v, w} A) :
    ComplexHilbertSpace F.directSumHilbert where
  toNormedAddCommGroup := inferInstance
  toInnerProductSpace := inferInstance
  toCompleteSpace := inferInstance

/-! ### Coordinate API

For each `α : F.Index`, the `α`-th coordinate of the direct-sum
Hilbert space is `(F.rep α).H`.  We provide:

* `sectorComponent F α` — coordinate projection
  `F.directSumHilbert →L[ℂ] (F.rep α).H`.
* `sectorEmbed F α` — coordinate embedding
  `(F.rep α).H →ₗᵢ[ℂ] F.directSumHilbert` (Mathlib `lp.single`
  packaged as a `LinearIsometry`).
-/

/-- The coordinate projection onto the `α`-th sector component, as a
continuous linear map. -/
noncomputable def sectorComponent (F : SectorFamily.{u, v, w} A)
    (α : F.Index) : F.directSumHilbert →L[ℂ] (F.rep α).H :=
  lp.evalCLM (𝕜 := ℂ) (fun α' : F.Index => (F.rep α').H) 2 α

/-- The coordinate embedding of `(F.rep α).H` into the direct-sum
Hilbert space at the `α`-th component, as a linear isometry. -/
noncomputable def sectorEmbed (F : SectorFamily.{u, v, w} A)
    (α : F.Index) : (F.rep α).H →ₗᵢ[ℂ] F.directSumHilbert :=
  letI : DecidableEq F.Index := Classical.decEq _
  { toLinearMap :=
      (lp.singleContinuousLinearMap (𝕜 := ℂ)
        (E := fun α' : F.Index => (F.rep α').H) 2 α).toLinearMap
    norm_map' := fun x =>
      lp.norm_single (E := fun α' : F.Index => (F.rep α').H)
        (by norm_num : (0 : ℝ≥0∞) < 2) α x }

@[simp] lemma sectorEmbed_apply_coord (F : SectorFamily.{u, v, w} A)
    (α : F.Index) (v : (F.rep α).H) :
    (sectorEmbed F α v).val α = v := by
  let : DecidableEq F.Index := Classical.decEq _
  change (lp.single (E := fun α' : F.Index => (F.rep α').H) 2 α v) α = v
  exact lp.single_apply_self
    (E := fun α' : F.Index => (F.rep α').H) 2 α v

lemma sectorEmbed_apply_coord_ne (F : SectorFamily.{u, v, w} A)
    (α : F.Index) (v : (F.rep α).H)
    {α' : F.Index} (h : α' ≠ α) :
    (sectorEmbed F α v).val α' = 0 := by
  let : DecidableEq F.Index := Classical.decEq _
  change (lp.single (E := fun α'' : F.Index => (F.rep α'').H) 2 α v) α' = 0
  exact lp.single_apply_ne
    (E := fun α'' : F.Index => (F.rep α'').H) 2 α v h

@[simp] lemma sectorComponent_sectorEmbed (F : SectorFamily.{u, v, w} A)
    (α : F.Index) (v : (F.rep α).H) :
    sectorComponent F α (sectorEmbed F α v) = v := by
  change (sectorEmbed F α v).val α = v
  exact sectorEmbed_apply_coord F α v

/-- Generic helper: from a `LinearIsometryEquiv` between a Hilbert space
`H` and the `α`-th fiber of the family, produce a `LinearIsometry`
embedding of `H` into the direct-sum Hilbert space.

Defined generically (the family `F` stays a variable so that the
costly `directSumHilbert`-family typeclass synthesis only fires here,
not at downstream specialized call sites). -/
noncomputable def sectorEmbedOfEquiv (F : SectorFamily.{u, v, w} A)
    (α : F.Index) {H : Type v} [ComplexHilbertSpace H]
    (eq : H ≃ₗᵢ[ℂ] (F.rep α).H) :
    H →ₗᵢ[ℂ] F.directSumHilbert :=
  (sectorEmbed F α).comp eq.toLinearIsometry

/-- The block-diagonal action of `a` on the direct-sum Hilbert space: Mathlib's `lp.mapCLM` of
the fibrewise operators `π_α a`, each of norm at most `‖a‖`. -/
noncomputable def directSumCLM (F : SectorFamily.{u, v, w} A) (a : A) :
    𝓑(F.directSumHilbert) :=
  lp.mapCLM 2 (fun α => (F.rep α).π a) (norm_nonneg a)
    fun α => NonUnitalStarAlgHom.norm_apply_le (F.rep α).π a

/-- The `α`-th coordinate of the block-diagonal action is the action of `π_α a`. -/
@[simp] lemma directSumCLM_apply (F : SectorFamily.{u, v, w} A) (a : A)
    (x : F.directSumHilbert) (α : F.Index) :
    (F.directSumCLM a x : ∀ α, (F.rep α).H) α = (F.rep α).π a (x α) := rfl

/-- Block-diagonality is compatible with the `*`-structure. -/
lemma directSumCLM_adjoint (F : SectorFamily.{u, v, w} A) (a : A) :
    (F.directSumCLM a)† = F.directSumCLM (star a) := by
  refine ContinuousLinearMap.ext fun x => ?_
  apply ext_inner_right ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  congr with α
  rw [directSumCLM_apply, directSumCLM_apply, ← ContinuousLinearMap.adjoint_inner_left]
  rw [map_star]
  rw [ContinuousLinearMap.star_eq_adjoint]

/-- The block-diagonal universal `*`-representation associated with a
sector family. -/
noncomputable def directSumRep (F : SectorFamily.{u, v, w} A) :
    A →⋆ₙₐ[ℂ] 𝓑(F.directSumHilbert) where
  toFun a := F.directSumCLM a
  map_mul' a b := by ext x α; simp
  map_zero' := by ext x α; simp
  map_add' a b := by ext x α; simp
  map_smul' c a := by ext x α; simp
  map_star' a := by
    rw [← directSumCLM_adjoint]
    rfl

/-- The operator-norm bound `‖F.directSumRep a‖ ≤ ‖a‖`. -/
lemma directSumRep_norm_le (F : SectorFamily.{u, v, w} A) (a : A) :
    ‖F.directSumRep a‖ ≤ ‖a‖ :=
  lp.norm_mapCLM_le _ _ (norm_nonneg a) fun α => NonUnitalStarAlgHom.norm_apply_le (F.rep α).π a

/-- A sector family *separates points* if the family of representations
separates `A`: whenever every member annihilates `a`, we have `a = 0`. -/
def SeparatesPoints (F : SectorFamily.{u, v, w} A) : Prop :=
  ∀ a : A, (∀ α : F.Index, (F.rep α).π a = 0) → a = 0

/-- **Faithfulness of the direct-sum representation** under a
points-separation condition on the family: if the family separates `A`,
then `F.directSumRep` is injective. -/
theorem directSumRep_injective_of (F : SectorFamily.{u, v, w} A)
    (h_sep : F.SeparatesPoints) :
    Function.Injective F.directSumRep := by
  intro a b hab
  -- It suffices to show `a - b = 0`.
  rw [← sub_eq_zero]
  -- `F.directSumRep (a - b) = 0` from `hab` by linearity.
  have h_diff_zero : F.directSumRep (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  -- Apply separation: every family member annihilates `a - b`.
  apply h_sep
  intro α
  ext v
  -- Evaluate `F.directSumRep (a - b) = 0` on the `δ_α`-vector `sectorEmbed F α v`.
  have h0 := congrArg (fun y : F.directSumHilbert => y.val α)
    (DFunLike.congr_fun h_diff_zero (sectorEmbed F α v))
  simpa [directSumRep] using h0

/-- The direct sum of a sector family, bundled as a `CStarRep`: the Hilbert space
`F.directSumHilbert` with the block-diagonal representation `F.directSumRep`. -/
noncomputable def toCStarRep (F : SectorFamily.{u, v, w} A) : CStarRep A where
  H := F.directSumHilbert
  π := F.directSumRep

@[simp] lemma toCStarRep_π (F : SectorFamily.{u, v, w} A) : F.toCStarRep.π = F.directSumRep :=
  rfl

/-- If the family separates points, the direct-sum representation is isometric: an injective
`*`-homomorphism between C\*-algebras is isometric. -/
theorem directSumRep_isometry_of (F : SectorFamily.{u, v, w} A) (h_sep : F.SeparatesPoints) :
    Isometry F.directSumRep :=
  AddMonoidHomClass.isometry_of_norm _ fun a =>
    NonUnitalStarAlgHom.norm_map _ (F.directSumRep_injective_of h_sep) a

/-- If the family separates points, the image of the direct-sum representation is norm closed,
hence a C\*-subalgebra of `𝓑(F.directSumHilbert)`. -/
theorem directSumRep_isClosed_range_of (F : SectorFamily.{u, v, w} A)
    (h_sep : F.SeparatesPoints) :
    IsClosed (NonUnitalStarAlgHom.range F.directSumRep : Set 𝓑(F.directSumHilbert)) := by
  rw [NonUnitalStarAlgHom.coe_range]
  exact (F.directSumRep_isometry_of h_sep).isClosedEmbedding.isClosed_range

/-- A direct sum of non-degenerate representations is non-degenerate: a vector killed by every
`F.directSumRep a` has every coordinate killed by the whole image of the corresponding member. -/
theorem directSumRep_actsNondegenerately_of (F : SectorFamily.{u, v, w} A)
    (h : ∀ α, InnerProductSpace.ActsNondegenerately
      (Set.range ((F.rep α).π : A → 𝓑((F.rep α).H)))) :
    InnerProductSpace.ActsNondegenerately
      (Set.range (F.directSumRep : A → 𝓑(F.directSumHilbert))) := by
  intro x hx
  apply Subtype.ext
  funext α
  have hα : ∀ a : A, (F.rep α).π a (x.val α) = 0 := by
    intro a
    have h0 := congrArg (fun y : F.directSumHilbert => y.val α) (hx _ ⟨a, rfl⟩)
    simpa [directSumRep] using h0
  simpa using h α _ (by rintro _ ⟨a, rfl⟩; exact hα a)

end SectorFamily
