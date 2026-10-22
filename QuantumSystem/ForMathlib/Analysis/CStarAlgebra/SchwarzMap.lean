/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Schwarz maps

A linear map `f : A₁ →ₗ[ℂ] A₂` between C⋆-algebras is a **Schwarz map** if it satisfies the
Kadison–Schwarz inequality `f(a)⋆ f(a) ≤ f(a⋆ a)` for every `a`. The *unital normal*
Schwarz maps form a class of maps along which the data-processing inequality for Araki's relative
entropy holds; unitality cannot be dropped, as `½ • id` shows once the entropy is
taken between general positive functionals, where it can be negative: for `σ = 2ρ`,
`S(½ρ‖½σ) = ½ S(ρ‖σ) = -½ log 2 > S(ρ‖σ)`.

Positivity, star-preservation and contractivity are *consequences* of the inequality.
Positivity is proved here: a positive element is of the form `b⋆ b`, so
`f(b⋆ b) ≥ f(b)⋆ f(b) ≥ 0`. Star-preservation is not proved here but supplied by Mathlib's
`StarHomClass` instance for positive ℂ-linear maps. Contractivity is proved here: a positive
linear map is bounded (Mathlib's `ContinuousLinearMapClass` instance for positive maps), and
`‖f a‖² = ‖f(a)⋆ f(a)‖ ≤ ‖f(a⋆ a)‖ ≤ ‖f‖ ‖a‖²` forces `‖f‖ ≤ 1`.

The main examples are the non-unital ⋆-homomorphisms (with equality), the Kraus maps
(`SchwarzMap.ofKraus`) and, by the Kadison–Schwarz inequality, the `2`-positive maps with
`φ 1 ≤ 1`, in particular the completely positive ones. The `k`-positive maps and that inequality
are in `ForMathlib/Analysis/CStarAlgebra/KPositiveMap.lean`
(`KPositiveMapClass.le_map_star_mul`); a `2`-positive map with `φ 1 ≤ 1` is packaged as a Schwarz
map by `KPositiveMapClass.toSchwarzMap` in `Analysis/CStarAlgebra/KPositiveMapSchwarz.lean`.

The equality case of the inequality is the **multiplicative domain**. For a ⋆-linear map `f`,
`LinearMap.multiplicativeDomain f` is the ⋆-subalgebra of the `a` with `f (a * b) = f a * f b` and
`f (b * a) = f b * f a` for every `b`, closed when `f` is continuous. For a Schwarz map, equality
at `a` and at `a⋆` already puts `a` in it (`SchwarzMapClass.mem_multiplicativeDomain_iff`): the
defect `D(x, y) = f(x⋆ y) - f(x)⋆ f(y)` has `D(x, x) ≥ 0`, and expanding `D(a + t b, a + t b) ≥ 0`
for real `t → 0`, at `b` and at `I • b`, shows that `D(a, a) = 0` forces `D(a, b) = 0`. It is thus
the largest ⋆-subalgebra on which `f` is multiplicative
(`SchwarzMapClass.le_multiplicativeDomain_iff`).

**Rigidity.** A Schwarz map `f` with a Schwarz inverse `g` is a ⋆-isomorphism
(`SchwarzMapClass.starAlgEquivOfInverse`): the inequality for `g` at `f a` and the positivity of
`f` give `f(a⋆ a) ≤ f(g(f(a)⋆ f(a))) = f(a)⋆ f(a)`, so equality holds everywhere. Both inverse
identities are needed: the unital completely positive maps `(x, y) ↦ diag(x, y, (x + y) / 2)`
from `ℂ²` to `3 × 3` matrices and the map reading off the first two diagonal entries compose to
the identity on `ℂ²` only, and neither is multiplicative. The normalisation built into the
inequality is needed too: `2 • id` and `2⁻¹ • id` are mutually inverse completely positive maps,
and `2 • id` is not a Schwarz map.

## Main definitions

* `SchwarzMap A₁ A₂` — linear maps satisfying `f(a)⋆ f(a) ≤ f(a⋆ a)`.
* `SchwarzMapClass F A₁ A₂` — the corresponding morphism class. It records only the inequality
  and is meant to be used together with `LinearMapClass`, as `CompletelyPositiveMapClass` is;
  unlike that class, `A₁` and `A₂` are `outParam`s, so that `le_map_star_mul f a` elaborates
  without an expected type.
* `SchwarzMap.comp`, `SchwarzMap.id`.
* `SchwarzMap.ofKraus` — the Kraus map `x ↦ Σᵢ Cᵢ† x Cᵢ` between operator algebras, for
  `Cᵢ : H → K` with `Σᵢ Cᵢ† Cᵢ ≤ 1`, as a Schwarz map. The inequality is proved directly, as
  `T(x⋆x) - T(x)⋆T(x) = Σᵢ Dᵢ† Dᵢ + T(x)⋆ (1 - Σᵢ Cᵢ† Cᵢ) T(x)` for `Dᵢ = x Cᵢ - Cᵢ T(x)`,
  without passing through complete positivity.
* `LinearMap.multiplicativeDomain` — the multiplicative domain of a ⋆-linear map, a
  ⋆-subalgebra; `LinearMap.restrictMultiplicativeDomain` — the map restricted to it, a
  ⋆-homomorphism.
* `SchwarzMapClass.starAlgEquivOfInverse` — a Schwarz map with a Schwarz inverse as a
  ⋆-isomorphism.

## Main results

* `SchwarzMapClass.instOrderHomClass` — Schwarz maps are positive.
* `SchwarzMapClass.norm_apply_le`, `SchwarzMapClass.nnnorm_apply_le` — Schwarz maps are contractive:
  `‖f a‖ ≤ ‖a‖`.
* `SchwarzMapClass.map_one_le_one` — `f 1 ≤ 1` for a Schwarz map between unital C⋆-algebras.
* `LinearMap.isClosed_multiplicativeDomain` — the multiplicative domain of a continuous ⋆-linear
  map is closed; for a Schwarz map it is therefore a C⋆-algebra.
* `SchwarzMapClass.map_star_mul_of_map_star_mul_self` — the equality case: `f(a⋆ a) = f(a)⋆ f(a)`
  implies `f(a⋆ b) = f(a)⋆ f(b)` for every `b`.
* `SchwarzMapClass.mem_multiplicativeDomain_iff` — the multiplicative domain of a Schwarz map is
  the set of `a` at which the inequality is an equality at both `a` and `a⋆`;
  `SchwarzMapClass.le_multiplicativeDomain_iff` — it is the largest ⋆-subalgebra on which the map
  is multiplicative.
* `SchwarzMapClass.multiplicativeDomain_eq_top_of_inverse` — a Schwarz map with a Schwarz inverse
  has the whole algebra as its multiplicative domain.
-/

@[expose] public section

open scoped CStarAlgebra InnerProduct

/-- A **Schwarz map** is a ℂ-linear map `f` between C⋆-algebras satisfying the Kadison–Schwarz
inequality `star (f a) * f a ≤ f (star a * a)`. Positivity, `map_star` and contractivity follow
(`SchwarzMapClass.instOrderHomClass`, `SchwarzMap.instStarHomClass` via Mathlib's instance for
positive ℂ-linear maps, `SchwarzMapClass.norm_apply_le`). -/
structure SchwarzMap (A₁ : Type*) (A₂ : Type*) [NonUnitalCStarAlgebra A₁]
    [NonUnitalCStarAlgebra A₂] [PartialOrder A₁] [PartialOrder A₂] [StarOrderedRing A₁]
    [StarOrderedRing A₂] extends A₁ →ₗ[ℂ] A₂ where
  /-- The Kadison–Schwarz inequality. -/
  le_map_star_mul' (a : A₁) : star (toFun a) * toFun a ≤ toFun (star a * a)

/-- A class of maps satisfying the Kadison–Schwarz inequality `star (f a) * f a ≤ f (star a * a)`.
It records only the inequality and is meant to be used together with `LinearMapClass`. -/
class SchwarzMapClass (F : Type*) (A₁ A₂ : outParam Type*) [NonUnitalCStarAlgebra A₁]
    [NonUnitalCStarAlgebra A₂] [PartialOrder A₁] [PartialOrder A₂] [StarOrderedRing A₁]
    [StarOrderedRing A₂] [FunLike F A₁ A₂] : Prop where
  /-- The Kadison–Schwarz inequality. -/
  le_map_star_mul (f : F) (a : A₁) : star (f a) * f a ≤ f (star a * a)

namespace SchwarzMapClass

section NonUnital

variable {F A₁ A₂ : Type*} [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂]
  [PartialOrder A₁] [PartialOrder A₂] [StarOrderedRing A₁] [StarOrderedRing A₂]
  [FunLike F A₁ A₂] [LinearMapClass F ℂ A₁ A₂] [SchwarzMapClass F A₁ A₂]

/-- Reinterpret an element of a type of Schwarz maps as a `SchwarzMap`. -/
@[coe]
def toSchwarzMap (f : F) : SchwarzMap A₁ A₂ :=
  { (f : A₁ →ₗ[ℂ] A₂) with le_map_star_mul' := le_map_star_mul f }

/-- An element of a type of Schwarz maps coerces to a `SchwarzMap`. -/
instance instCoeToSchwarzMap : CoeHead F (SchwarzMap A₁ A₂) where
  coe f := toSchwarzMap f

/-- Schwarz maps are positive: `0 ≤ b⋆ b` gives `0 ≤ f(b)⋆ f(b) ≤ f(b⋆ b)`. -/
instance (priority := 100) instOrderHomClass : OrderHomClass F A₁ A₂ :=
  .of_addMonoidHom fun f a ha => by
    obtain ⟨b, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha
    exact (star_mul_self_nonneg (f b)).trans (le_map_star_mul f b)

/-- The Kadison–Schwarz inequality in the form `f(a) f(a)⋆ ≤ f(a a⋆)`. -/
lemma le_map_mul_star (f : F) (a : A₁) : f a * star (f a) ≤ f (a * star a) := by
  simpa only [map_star, star_star] using le_map_star_mul f (star a)

/-- Schwarz maps are contractive: `‖f a‖² = ‖f(a)⋆ f(a)‖ ≤ ‖f(a⋆ a)‖ ≤ ‖f‖ ‖a‖²`, so `‖f‖ ≤ 1`. -/
lemma norm_apply_le (f : F) (a : A₁) : ‖f a‖ ≤ ‖a‖ := by
  let g : A₁ →L[ℂ] A₂ := ⟨(f : A₁ →ₗ[ℂ] A₂), map_continuous f⟩
  have hg (x : A₁) : g x = f x := rfl
  have hsq (x : A₁) : ‖f x‖ ^ 2 ≤ ‖g‖ * ‖x‖ ^ 2 := by
    calc ‖f x‖ ^ 2 = ‖star (f x) * f x‖ := by rw [CStarRing.norm_star_mul_self, sq]
      _ ≤ ‖f (star x * x)‖ :=
        CStarAlgebra.norm_le_norm_of_le_of_nonneg (le_map_star_mul f x) (star_mul_self_nonneg _)
      _ ≤ ‖g‖ * ‖star x * x‖ := hg _ ▸ g.le_opNorm _
      _ = ‖g‖ * ‖x‖ ^ 2 := by rw [CStarRing.norm_star_mul_self, sq]
  have hle : ‖g‖ ≤ √‖g‖ := g.opNorm_le_bound (Real.sqrt_nonneg _) fun x => by
    rw [hg, ← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, mul_pow,
      Real.sq_sqrt g.opNorm_nonneg]
    exact hsq x
  have hg1 : ‖g‖ ≤ 1 := by
    have h2 := (Real.le_sqrt g.opNorm_nonneg g.opNorm_nonneg).mp hle
    nlinarith [g.opNorm_nonneg]
  calc ‖f a‖ = ‖g a‖ := rfl
    _ ≤ ‖g‖ * ‖a‖ := g.le_opNorm a
    _ ≤ ‖a‖ := mul_le_of_le_one_left (norm_nonneg _) hg1

/-- Schwarz maps are contractive, `‖f a‖₊ ≤ ‖a‖₊`. -/
lemma nnnorm_apply_le (f : F) (a : A₁) : ‖f a‖₊ ≤ ‖a‖₊ := norm_apply_le f a

end NonUnital

section Unital

variable {F A₁ A₂ : Type*} [CStarAlgebra A₁] [CStarAlgebra A₂]
  [PartialOrder A₁] [PartialOrder A₂] [StarOrderedRing A₁] [StarOrderedRing A₂]
  [FunLike F A₁ A₂] [LinearMapClass F ℂ A₁ A₂] [SchwarzMapClass F A₁ A₂]

/-- A Schwarz map between unital C⋆-algebras is sub-unital: `f 1 ≤ 1`. -/
lemma map_one_le_one (f : F) : f 1 ≤ 1 := by
  have h₀ : 0 ≤ f 1 := map_nonneg f zero_le_one
  have h₁ : ‖f 1‖ ≤ 1 := (norm_apply_le f 1).trans (IsStarProjection.norm_le 1 (.one A₁))
  calc f 1 ≤ algebraMap ℝ A₂ ‖f 1‖ := IsSelfAdjoint.le_algebraMap_norm_self (f 1) h₀.isSelfAdjoint
    _ ≤ algebraMap ℝ A₂ 1 := by gcongr
    _ = 1 := map_one _

end Unital

end SchwarzMapClass

namespace SchwarzMap

variable {A₁ A₂ A₃ : Type*} [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂]
  [NonUnitalCStarAlgebra A₃] [PartialOrder A₁] [PartialOrder A₂] [PartialOrder A₃]
  [StarOrderedRing A₁] [StarOrderedRing A₂] [StarOrderedRing A₃]

instance : FunLike (SchwarzMap A₁ A₂) A₁ A₂ where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective
    exact h

/-- A Schwarz map is `ℂ`-linear. -/
instance : LinearMapClass (SchwarzMap A₁ A₂) ℂ A₁ A₂ where
  map_add f := map_add f.toLinearMap
  map_smulₛₗ f := map_smulₛₗ f.toLinearMap

/-- A bundled Schwarz map satisfies the Kadison–Schwarz inequality in the sense of
`SchwarzMapClass`. -/
instance : SchwarzMapClass (SchwarzMap A₁ A₂) A₁ A₂ where
  le_map_star_mul f := f.le_map_star_mul'

/-- Schwarz maps are positive; `SchwarzMapClass.instOrderHomClass` specialised to `SchwarzMap`.
On algebras whose order instances are expensive to synthesise (e.g. a von Neumann algebra `↥M`),
the generic search first tries `CompletelyPositiveMapClass.instOrderHomClass` and runs out of
heartbeats before reaching the Schwarz instance. -/
instance instOrderHomClass : OrderHomClass (SchwarzMap A₁ A₂) A₁ A₂ :=
  SchwarzMapClass.instOrderHomClass

/-- Schwarz maps preserve `⋆`; Mathlib's instance for positive ℂ-linear maps specialised to
`SchwarzMap`, for the same reason as `SchwarzMap.instOrderHomClass`. -/
instance instStarHomClass : StarHomClass (SchwarzMap A₁ A₂) A₁ A₂ :=
  inferInstance

/-- Two Schwarz maps agreeing pointwise are equal. -/
@[ext]
lemma ext {f g : SchwarzMap A₁ A₂} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

/-- The underlying linear map has the same coercion to a function. -/
@[simp] lemma coe_toLinearMap (f : SchwarzMap A₁ A₂) : ⇑f.toLinearMap = f := rfl

/-- The coercion of a Schwarz map built from a linear map `f` is `f`. -/
@[simp] lemma coe_mk (f : A₁ →ₗ[ℂ] A₂) (h) : ⇑(⟨f, h⟩ : SchwarzMap A₁ A₂) = f := rfl

variable (A₁) in
/-- The identity as a Schwarz map. -/
protected def id : SchwarzMap A₁ A₁ where
  __ := LinearMap.id
  le_map_star_mul' _ := le_rfl

/-- The identity Schwarz map evaluates as the identity. -/
@[simp] lemma id_apply (a : A₁) : SchwarzMap.id A₁ a = a := rfl

/-- The composite of two Schwarz maps is a Schwarz map:
`g(f a)⋆ g(f a) ≤ g(f(a)⋆ f(a)) ≤ g(f(a⋆ a))`, the second step by positivity of `g`. -/
def comp (g : SchwarzMap A₂ A₃) (f : SchwarzMap A₁ A₂) : SchwarzMap A₁ A₃ where
  toLinearMap := g.toLinearMap.comp f.toLinearMap
  le_map_star_mul' a :=
    (SchwarzMapClass.le_map_star_mul g (f a)).trans (OrderHomClass.mono g
      (SchwarzMapClass.le_map_star_mul f a))

/-- The composite Schwarz map evaluates as the composite. -/
@[simp] lemma comp_apply (g : SchwarzMap A₂ A₃) (f : SchwarzMap A₁ A₂) (a : A₁) :
    g.comp f a = g (f a) := rfl

/-- Composing with the identity on the right. -/
@[simp] lemma comp_id (f : SchwarzMap A₁ A₂) : f.comp (SchwarzMap.id A₁) = f := rfl

/-- Composing with the identity on the left. -/
@[simp] lemma id_comp (f : SchwarzMap A₁ A₂) : (SchwarzMap.id A₂).comp f = f := rfl

/-- Composition of Schwarz maps is associative. -/
lemma comp_assoc {A₄ : Type*} [NonUnitalCStarAlgebra A₄] [PartialOrder A₄] [StarOrderedRing A₄]
    (h : SchwarzMap A₃ A₄) (g : SchwarzMap A₂ A₃) (f : SchwarzMap A₁ A₂) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl

end SchwarzMap

namespace NonUnitalStarAlgHomClass

variable {F A₁ A₂ : Type*} [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂] [PartialOrder A₁]
  [PartialOrder A₂] [StarOrderedRing A₁] [StarOrderedRing A₂] [FunLike F A₁ A₂]
  [NonUnitalAlgHomClass F ℂ A₁ A₂] [StarHomClass F A₁ A₂]

/-- Non-unital ⋆-homomorphisms are Schwarz maps, with equality `f(a)⋆ f(a) = f(a⋆ a)`. -/
instance instSchwarzMapClass : SchwarzMapClass F A₁ A₂ where
  le_map_star_mul f a := by rw [map_mul, map_star]

end NonUnitalStarAlgHomClass

namespace SchwarzMap

open ContinuousLinearMap

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] {ι : Type*} [Fintype ι]

/-- **Kraus maps are Schwarz maps.** For `Cᵢ : H →L[ℂ] K` with `Σᵢ Cᵢ† Cᵢ ≤ 1`, the map
`T x = Σᵢ Cᵢ† x Cᵢ` from `B(K)` to `B(H)` satisfies `T(x)⋆ T(x) ≤ T(x⋆ x)`: with `S = T x`,
`Dᵢ = x Cᵢ - Cᵢ S` and `P = Σᵢ Cᵢ† Cᵢ`, `T(x⋆ x) - S⋆ S = Σᵢ Dᵢ† Dᵢ + S⋆ (1 - P) S ≥ 0`. The map is
unital exactly when `P = 1` (`SchwarzMap.ofKraus_one`). -/
noncomputable def ofKraus (C : ι → H →L[ℂ] K) (hC : ∑ i, (C i)† ∘L C i ≤ 1) :
    SchwarzMap (K →L[ℂ] K) (H →L[ℂ] H) where
  toFun x := ∑ i, (C i)† ∘L x ∘L C i
  map_add' x y := by
    simp only [add_comp, comp_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [smul_comp, comp_smul, Finset.smul_sum, RingHom.id_apply]
  le_map_star_mul' x := by
    set S := ∑ i, (C i)† ∘L x ∘L C i with hSdef
    set P := ∑ i, (C i)† ∘L C i with hPdef
    have hS : star S = ∑ i, (C i)† ∘L x† ∘L C i := by
      rw [hSdef, star_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [star_eq_adjoint, adjoint_comp, adjoint_comp, adjoint_adjoint,
        ContinuousLinearMap.comp_assoc]
    have key : (∑ i, (C i)† ∘L (star x * x) ∘L C i) - star S * S =
        ∑ i, (x ∘L C i - C i ∘L S)† ∘L (x ∘L C i - C i ∘L S) + star S * (1 - P) * S := by
      have e : ∀ i, (x ∘L C i - C i ∘L S)† ∘L (x ∘L C i - C i ∘L S) =
          (C i)† ∘L (star x * x) ∘L C i - ((C i)† ∘L x† ∘L C i) ∘L S
            - S† ∘L ((C i)† ∘L x ∘L C i)
            + S† ∘L ((C i)† ∘L C i) ∘L S := fun i => by
        rw [map_sub, adjoint_comp, adjoint_comp, sub_comp, comp_sub, comp_sub, star_eq_adjoint,
          mul_def]
        simp only [ContinuousLinearMap.comp_assoc]
        abel
      simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← finsetSum_comp,
        ← comp_finsetSum, ← hS, ← hSdef, ← hPdef]
      simp only [← mul_def, ← star_eq_adjoint, mul_sub, sub_mul, mul_one]
      noncomm_ring
    rw [← sub_nonneg, key]
    exact add_nonneg
      (Finset.sum_nonneg fun i _ => nonneg_iff_isPositive.mpr (isPositive_adjoint_comp_self _))
      (star_left_conjugate_nonneg (sub_nonneg.mpr hC) S)

/-- The Kraus Schwarz map is `x ↦ Σᵢ Cᵢ† x Cᵢ`. -/
@[simp] lemma ofKraus_apply (C : ι → H →L[ℂ] K) (hC : ∑ i, (C i)† ∘L C i ≤ 1)
    (x : K →L[ℂ] K) : ofKraus C hC x = ∑ i, (C i)† ∘L x ∘L C i := rfl

/-- `T 1 = Σᵢ Cᵢ† Cᵢ`: the Kraus map is unital iff `Σᵢ Cᵢ† Cᵢ = 1`. -/
lemma ofKraus_one (C : ι → H →L[ℂ] K) (hC : ∑ i, (C i)† ∘L C i ≤ 1) :
    ofKraus C hC 1 = ∑ i, (C i)† ∘L C i := by
  rw [ofKraus_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [one_def, ContinuousLinearMap.id_comp]

end SchwarzMap

/-! ### The multiplicative domain -/

namespace LinearMap

section NonUnital

variable {R A B F : Type*} [CommSemiring R] [NonUnitalSemiring A] [StarRing A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [NonUnitalSemiring B] [StarRing B] [Module R B]
  [IsScalarTower R B B] [SMulCommClass R B B] [FunLike F A B] [LinearMapClass F R A B]
  [StarHomClass F A B]

/-- The **multiplicative domain** of a ⋆-linear map `f`: the ⋆-subalgebra of the `a` with
`f (a * b) = f a * f b` and `f (b * a) = f b * f a` for every `b`. For a Schwarz map it is the set
of `a` at which the Kadison–Schwarz inequality is an equality at `a` and at `a⋆`
(`SchwarzMapClass.mem_multiplicativeDomain_iff`). When `f 1 = 1` it contains `1`
(`LinearMap.one_mem_multiplicativeDomain`), and
`(multiplicativeDomain f).toStarSubalgebra (one_mem_multiplicativeDomain hf)` is its unital
form. -/
def multiplicativeDomain (f : F) : NonUnitalStarSubalgebra R A where
  carrier := {a | ∀ b, f (a * b) = f a * f b ∧ f (b * a) = f b * f a}
  add_mem' {a a'} ha ha' b := by
    simp only [add_mul, mul_add, map_add, (ha b).1, (ha' b).1, (ha b).2, (ha' b).2, and_self]
  zero_mem' b := by simp
  mul_mem' {a a'} ha ha' b := by
    refine ⟨?_, ?_⟩
    · rw [mul_assoc, (ha _).1, (ha' b).1, (ha a').1, mul_assoc]
    · rw [← mul_assoc, (ha' _).2, (ha b).2, (ha' a).2, mul_assoc]
  smul_mem' r a ha b := by
    simp only [smul_mul_assoc, mul_smul_comm, map_smul, (ha b).1, (ha b).2, and_self]
  star_mem' {a} ha b := by
    refine ⟨?_, ?_⟩
    · simpa only [star_mul, ← map_star, star_star] using congr(star $((ha (star b)).2))
    · simpa only [star_mul, ← map_star, star_star] using congr(star $((ha (star b)).1))

/-- Membership in the multiplicative domain, by definition. -/
lemma mem_multiplicativeDomain {f : F} {a : A} :
    a ∈ multiplicativeDomain f ↔ ∀ b, f (a * b) = f a * f b ∧ f (b * a) = f b * f a :=
  Iff.rfl

/-- The restriction of `f` to its multiplicative domain, a non-unital ⋆-homomorphism. -/
@[simps]
def restrictMultiplicativeDomain (f : F) : multiplicativeDomain f →⋆ₙₐ[R] B where
  toFun a := f a
  map_smul' r a := map_smul f r (a : A)
  map_zero' := map_zero f
  map_add' a a' := map_add f (a : A) a'
  map_mul' a a' := (a.2 a').1
  map_star' a := map_star f (a : A)

/-- The multiplicative domain of a continuous ⋆-linear map is closed. For a Schwarz map it is
therefore a C⋆-algebra, by `NonUnitalStarSubalgebra.nonUnitalCStarAlgebra`. -/
instance isClosed_multiplicativeDomain [TopologicalSpace A] [TopologicalSpace B]
    [ContinuousMul A] [ContinuousMul B] [T2Space B] [ContinuousMapClass F A B] (f : F) :
    IsClosed (multiplicativeDomain f : Set A) := by
  have : (multiplicativeDomain f : Set A) =
      ⋂ b, ({a | f (a * b) = f a * f b} ∩ {a | f (b * a) = f b * f a}) := by
    ext a
    simp [mem_multiplicativeDomain]
  rw [this]
  exact isClosed_iInter fun b => (isClosed_eq (by fun_prop) (by fun_prop)).inter
    (isClosed_eq (by fun_prop) (by fun_prop))

end NonUnital

section Unital

variable {R A B F : Type*} [CommSemiring R] [Semiring A] [StarRing A] [Algebra R A]
  [Semiring B] [StarRing B] [Algebra R B] [FunLike F A B] [LinearMapClass F R A B]
  [StarHomClass F A B]

/-- The multiplicative domain of a unital ⋆-linear map contains `1`. -/
lemma one_mem_multiplicativeDomain {f : F} (hf : f 1 = 1) : 1 ∈ multiplicativeDomain f :=
  fun b => by simp [hf]

end Unital

end LinearMap

namespace SchwarzMapClass

open Filter Topology

section Aux

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- If `H + t • K` is positive for every `t > 0`, then so is `H`, the positive cone being closed. -/
private lemma nonneg_of_forall_nonneg_add_smul {H K : A} (h : ∀ t : ℝ, 0 < t → 0 ≤ H + t • K) :
    0 ≤ H := by
  have hc : Continuous fun t : ℝ => H + t • K := by fun_prop
  have hT : Tendsto (fun t : ℝ => H + t • K) (𝓝[>] 0) (𝓝 H) := by
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hT (eventually_nhdsWithin_of_forall fun t ht => h t ht)

/-- If `t • H + t² • K` is positive for every real `t`, then `H = 0`: dividing by `t` and `-t`
gives `0 ≤ H` and `0 ≤ -H`. -/
private lemma eq_zero_of_forall_nonneg_smul_add_sq_smul {H K : A}
    (h : ∀ t : ℝ, 0 ≤ t • H + t ^ 2 • K) : H = 0 := by
  have hpos : 0 ≤ H := nonneg_of_forall_nonneg_add_smul (K := K) fun t ht => by
    simpa [smul_add, smul_smul, ht.ne', sq] using smul_nonneg (inv_nonneg.mpr ht.le) (h t)
  have hneg : 0 ≤ -H := nonneg_of_forall_nonneg_add_smul (K := K) fun t ht => by
    simpa [smul_add, smul_smul, ht.ne', sq] using smul_nonneg (inv_nonneg.mpr ht.le) (h (-t))
  exact le_antisymm (neg_nonneg.mp hneg) hpos

end Aux

section MultiplicativeDomain

variable {F A₁ A₂ : Type*} [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂]
  [PartialOrder A₁] [PartialOrder A₂] [StarOrderedRing A₁] [StarOrderedRing A₂]
  [FunLike F A₁ A₂] [LinearMapClass F ℂ A₁ A₂] [SchwarzMapClass F A₁ A₂]

/-- With `X = f(a⋆ b) - f(a)⋆ f(b)`, equality at `a` gives `X + X⋆ = 0`: the inequality at
`a + t • b` reads `0 ≤ t • (X + X⋆) + t² • (f(b⋆ b) - f(b)⋆ f(b))` for real `t`. -/
private lemma add_star_eq_zero (f : F) {a : A₁} (ha : f (star a * a) = star (f a) * f a)
    (b : A₁) :
    f (star a * b) - star (f a) * f b + star (f (star a * b) - star (f a) * f b) = 0 := by
  refine eq_zero_of_forall_nonneg_smul_add_sq_smul
    (K := f (star b * b) - star (f b) * f b) fun t => ?_
  have hr (x : A₁) : f (t • x) = t • f x := LinearMapClass.map_smul_of_tower f t x
  have hs : star (f (star a * b)) = f (star b * a) := by rw [← map_star, star_mul, star_star]
  convert sub_nonneg.mpr (le_map_star_mul f (a + t • b)) using 1
  simp only [star_add, star_smul, star_trivial, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    map_add, hr, star_sub, star_mul, star_star, hs, ha]
  module

/-- **The equality case of the Kadison–Schwarz inequality.** If `f(a⋆ a) = f(a)⋆ f(a)`, then
`f(a⋆ b) = f(a)⋆ f(b)` for every `b`. With `X = f(a⋆ b) - f(a)⋆ f(b)`, the inequality at `a + t • b`
for real `t` gives `X + X⋆ = 0`, and at `a + t • (I • b)` gives `X - X⋆ = 0`. -/
theorem map_star_mul_of_map_star_mul_self (f : F) {a : A₁}
    (ha : f (star a * a) = star (f a) * f a) (b : A₁) :
    f (star a * b) = star (f a) * f b := by
  set X := f (star a * b) - star (f a) * f b
  have h₁ : X + star X = 0 := add_star_eq_zero f ha b
  have hI : f (star a * (Complex.I • b)) - star (f a) * f (Complex.I • b) = Complex.I • X := by
    rw [mul_smul_comm, map_smul, map_smul, mul_smul_comm, ← smul_sub]
  have h₂ := add_star_eq_zero f ha (Complex.I • b)
  rw [hI, star_smul, Complex.star_def, Complex.conj_I, neg_smul, ← sub_eq_add_neg, ← smul_sub,
    smul_eq_zero] at h₂
  have h₃ : X - star X = 0 := h₂.resolve_left Complex.I_ne_zero
  have h₄ : (2 : ℂ) • X = 0 :=
    calc (2 : ℂ) • X = (X + star X) + (X - star X) := by rw [two_smul]; abel
      _ = 0 := by rw [h₁, h₃, add_zero]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h₄).resolve_left two_ne_zero)

/-- The equality case of the Kadison–Schwarz inequality, multiplying on the right:
`f(a⋆ a) = f(a)⋆ f(a)` implies `f(b a) = f(b) f(a)` for every `b`. -/
lemma map_mul_of_map_star_mul_self (f : F) {a : A₁}
    (ha : f (star a * a) = star (f a) * f a) (b : A₁) : f (b * a) = f b * f a := by
  simpa [star_mul, ← map_star] using congr(star $(map_star_mul_of_map_star_mul_self f ha (star b)))

/-- The equality case of the Kadison–Schwarz inequality at `a⋆`: `f(a a⋆) = f(a) f(a)⋆` implies
`f(a b) = f(a) f(b)` for every `b`. -/
lemma map_mul_of_map_mul_star_self (f : F) {a : A₁}
    (ha : f (a * star a) = f a * star (f a)) (b : A₁) : f (a * b) = f a * f b := by
  simpa [map_star] using
    map_star_mul_of_map_star_mul_self f (a := star a) (by simpa [map_star] using ha) b

/-- The multiplicative domain of a Schwarz map consists of the `a` at which the Kadison–Schwarz
inequality is an equality, both at `a` and at `a⋆`. -/
theorem mem_multiplicativeDomain_iff {f : F} {a : A₁} :
    a ∈ LinearMap.multiplicativeDomain f ↔
      f (star a * a) = star (f a) * f a ∧ f (a * star a) = f a * star (f a) := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨h₁, h₂⟩ b =>
    ⟨map_mul_of_map_mul_star_self f h₂ b, map_mul_of_map_star_mul_self f h₁ b⟩⟩
  · rw [(h _).2, map_star]
  · rw [(h _).1, map_star]

/-- The multiplicative domain of a Schwarz map is the largest ⋆-subalgebra on which the map is
multiplicative. The restriction to ⋆-subalgebras matters: the condition only gives
`f(a⋆ a) = f(a)⋆ f(a)` when `a⋆` lies in `S` too. -/
lemma le_multiplicativeDomain_iff {f : F} {S : NonUnitalStarSubalgebra ℂ A₁} :
    S ≤ LinearMap.multiplicativeDomain f ↔ ∀ x ∈ S, ∀ y ∈ S, f (x * y) = f x * f y := by
  refine ⟨fun h x hx y _ => (h hx y).1, fun h x hx => mem_multiplicativeDomain_iff.mpr ⟨?_, ?_⟩⟩
  · rw [h _ (star_mem hx) _ hx, map_star]
  · rw [h _ hx _ (star_mem hx), map_star]

variable {G : Type*} [FunLike G A₂ A₁] [SchwarzMapClass G A₂ A₁]

/-- A Schwarz map `f` with a Schwarz inverse `g` attains equality in the Kadison–Schwarz
inequality: `f(a⋆ a) ≤ f(g(f(a)⋆ f(a))) = f(a)⋆ f(a)`, by the inequality for `g` at `f a` and the
positivity of `f`. Here `h₁` and `h₂` say `g ∘ f = id` and `f ∘ g = id`. -/
lemma map_star_mul_self_of_inverse (f : F) (g : G) (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) (a : A₁) : f (star a * a) = star (f a) * f a := by
  refine le_antisymm ?_ (le_map_star_mul f a)
  have := OrderHomClass.mono f (le_map_star_mul g (f a))
  rwa [h₁ a, h₂] at this

/-- **Rigidity.** A Schwarz map with a Schwarz inverse has the whole algebra as its multiplicative
domain. Here `h₁` and `h₂` say `g ∘ f = id` and `f ∘ g = id`. -/
theorem multiplicativeDomain_eq_top_of_inverse (f : F) (g : G) (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : LinearMap.multiplicativeDomain f = ⊤ :=
  eq_top_iff.mpr fun a _ => mem_multiplicativeDomain_iff.mpr
    ⟨map_star_mul_self_of_inverse f g h₁ h₂ a,
      by simpa [map_star] using map_star_mul_self_of_inverse f g h₁ h₂ (star a)⟩

/-- A Schwarz map with a Schwarz inverse is multiplicative. Here `h₁` and `h₂` say `g ∘ f = id`
and `f ∘ g = id`. -/
lemma map_mul_of_inverse (f : F) (g : G) (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) (a b : A₁) : f (a * b) = f a * f b := by
  have ha : a ∈ LinearMap.multiplicativeDomain f := by
    rw [multiplicativeDomain_eq_top_of_inverse f g h₁ h₂]
    exact NonUnitalStarAlgebra.mem_top
  exact (ha b).1

/-- A Schwarz map with a Schwarz inverse as a ⋆-isomorphism. Here `h₁` and `h₂` say `g ∘ f = id`
and `f ∘ g = id`. -/
@[simps apply symm_apply]
def starAlgEquivOfInverse (f : F) (g : G) (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : A₁ ≃⋆ₐ[ℂ] A₂ where
  toFun := f
  invFun := g
  left_inv := h₁
  right_inv := h₂
  map_mul' := map_mul_of_inverse f g h₁ h₂
  map_add' := map_add f
  map_star' := map_star f
  map_smul' := map_smul f

end MultiplicativeDomain

end SchwarzMapClass
