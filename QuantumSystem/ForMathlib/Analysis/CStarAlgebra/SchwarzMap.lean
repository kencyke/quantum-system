/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# Schwarz maps

A linear map `f : A₁ →ₗ[ℂ] A₂` between C⋆-algebras is a **Schwarz map** if it satisfies the
Kadison–Schwarz inequality `f(a)⋆ f(a) ≤ f(a⋆ a)` for every `a` (Choi, *A Schwarz inequality for
positive linear maps on C⋆-algebras*, Illinois J. Math. 18 (1974); Ohya–Petz, *Quantum Entropy
and Its Use*, §1.C; Petz, *Quasi-entropies for finite quantum systems* (1986)). The *unital normal*
Schwarz maps form a class of maps along which the data-processing inequality for Araki's relative
entropy holds (Uhlmann; Petz); unitality cannot be dropped, as `½ • id` shows once the entropy is
taken between general positive functionals, where it can be negative: for `σ = 2ρ`,
`S(½ρ‖½σ) = ½ S(ρ‖σ) = -½ log 2 > S(ρ‖σ)`.

Positivity, star-preservation and contractivity are *consequences* of the inequality.
Positivity is proved here: a positive element is of the form `b⋆ b`, so
`f(b⋆ b) ≥ f(b)⋆ f(b) ≥ 0`. Star-preservation is not proved here but supplied by Mathlib's
`StarHomClass` instance for positive ℂ-linear maps. Contractivity is proved here: a positive
linear map is bounded (Mathlib's `ContinuousLinearMapClass` instance for positive maps), and
`‖f a‖² = ‖f(a)⋆ f(a)‖ ≤ ‖f(a⋆ a)‖ ≤ ‖f‖ ‖a‖²` forces `‖f‖ ≤ 1`.

The main examples are the non-unital ⋆-homomorphisms (with equality), the Kraus maps
(`SchwarzMap.ofKraus`) and, by the Kadison–Schwarz inequality of Choi, the `2`-positive maps with
`φ 1 ≤ 1`, in particular the completely positive ones. The `k`-positive maps and that inequality
are in `ForMathlib/Analysis/CStarAlgebra/KPositiveMap.lean`
(`KPositiveMapClass.le_map_star_mul`); a `2`-positive map with `φ 1 ≤ 1` is packaged as a Schwarz
map by `KPositiveMapClass.toSchwarzMap` in `Analysis/CStarAlgebra/KadisonSchwarz.lean`.

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

## Main results

* `SchwarzMapClass.instOrderHomClass` — Schwarz maps are positive.
* `SchwarzMapClass.norm_apply_le`, `SchwarzMapClass.nnnorm_apply_le` — Schwarz maps are contractive:
  `‖f a‖ ≤ ‖a‖`.
* `SchwarzMapClass.map_one_le_one` — `f 1 ≤ 1` for a Schwarz map between unital C⋆-algebras.
-/

@[expose] public section

open scoped CStarAlgebra

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
theorem le_map_mul_star (f : F) (a : A₁) : f a * star (f a) ≤ f (a * star a) := by
  simpa only [map_star, star_star] using le_map_star_mul f (star a)

/-- Schwarz maps are contractive: `‖f a‖² = ‖f(a)⋆ f(a)‖ ≤ ‖f(a⋆ a)‖ ≤ ‖f‖ ‖a‖²`, so `‖f‖ ≤ 1`. -/
theorem norm_apply_le (f : F) (a : A₁) : ‖f a‖ ≤ ‖a‖ := by
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
theorem nnnorm_apply_le (f : F) (a : A₁) : ‖f a‖₊ ≤ ‖a‖₊ := norm_apply_le f a

end NonUnital

section Unital

variable {F A₁ A₂ : Type*} [CStarAlgebra A₁] [CStarAlgebra A₂]
  [PartialOrder A₁] [PartialOrder A₂] [StarOrderedRing A₁] [StarOrderedRing A₂]
  [FunLike F A₁ A₂] [LinearMapClass F ℂ A₁ A₂] [SchwarzMapClass F A₁ A₂]

/-- A Schwarz map between unital C⋆-algebras is sub-unital: `f 1 ≤ 1`. -/
theorem map_one_le_one (f : F) : f 1 ≤ 1 := by
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

instance : LinearMapClass (SchwarzMap A₁ A₂) ℂ A₁ A₂ where
  map_add f := map_add f.toLinearMap
  map_smulₛₗ f := map_smulₛₗ f.toLinearMap

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
noncomputable def ofKraus (C : ι → H →L[ℂ] K) (hC : ∑ i, adjoint (C i) ∘L C i ≤ 1) :
    SchwarzMap (K →L[ℂ] K) (H →L[ℂ] H) where
  toFun x := ∑ i, adjoint (C i) ∘L x ∘L C i
  map_add' x y := by
    simp only [add_comp, comp_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [smul_comp, comp_smul, Finset.smul_sum, RingHom.id_apply]
  le_map_star_mul' x := by
    set S := ∑ i, adjoint (C i) ∘L x ∘L C i with hSdef
    set P := ∑ i, adjoint (C i) ∘L C i with hPdef
    have hS : star S = ∑ i, adjoint (C i) ∘L adjoint x ∘L C i := by
      rw [hSdef, star_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [star_eq_adjoint, adjoint_comp, adjoint_comp, adjoint_adjoint,
        ContinuousLinearMap.comp_assoc]
    have key : (∑ i, adjoint (C i) ∘L (star x * x) ∘L C i) - star S * S =
        ∑ i, adjoint (x ∘L C i - C i ∘L S) ∘L (x ∘L C i - C i ∘L S) + star S * (1 - P) * S := by
      have e : ∀ i, adjoint (x ∘L C i - C i ∘L S) ∘L (x ∘L C i - C i ∘L S) =
          adjoint (C i) ∘L (star x * x) ∘L C i - (adjoint (C i) ∘L adjoint x ∘L C i) ∘L S
            - adjoint S ∘L (adjoint (C i) ∘L x ∘L C i)
            + adjoint S ∘L (adjoint (C i) ∘L C i) ∘L S := fun i => by
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
@[simp] lemma ofKraus_apply (C : ι → H →L[ℂ] K) (hC : ∑ i, adjoint (C i) ∘L C i ≤ 1)
    (x : K →L[ℂ] K) : ofKraus C hC x = ∑ i, adjoint (C i) ∘L x ∘L C i := rfl

/-- `T 1 = Σᵢ Cᵢ† Cᵢ`: the Kraus map is unital iff `Σᵢ Cᵢ† Cᵢ = 1`. -/
lemma ofKraus_one (C : ι → H →L[ℂ] K) (hC : ∑ i, adjoint (C i) ∘L C i ≤ 1) :
    ofKraus C hC 1 = ∑ i, adjoint (C i) ∘L C i := by
  rw [ofKraus_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [one_def, ContinuousLinearMap.id_comp]

end SchwarzMap
