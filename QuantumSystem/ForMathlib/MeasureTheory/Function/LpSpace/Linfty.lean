/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# `L∞` as a C⋆-algebra

For a normed ring `R`, the space `L∞(μ, R) = Lp R ∞ μ` is a normed ring under pointwise
multiplication, which is Mathlib's Hölder multiplication `Lp R ∞ μ × Lp R ∞ μ → Lp R ∞ μ`; for a
C⋆-algebra `R` it is a C⋆-algebra, with Mathlib's `Star (Lp R p μ)` as involution.

The multiplication representation `MeasureTheory.Linfty.mulL2 : L∞ →⋆ₐ[ℂ] B(L²)`, `f ↦ M_f`, is
built on the same Hölder multiplication. The function `f` takes values in the spectrum of `M_f`
wherever an `L²` vector does not vanish (almost everywhere, for a σ-finite measure), and the
continuous functional calculus of `M_f` is composition: `g(M_f) = M_{g ∘ f}`, for every measure.

## Main definitions

* `MeasureTheory.Linfty.instRing`, `instCommRing`, `instNormedRing`, `instNormedAlgebra`,
  `instStarRing`, `instCStarRing`, `instCStarAlgebra` — the algebraic structure of `L∞`.
* `MeasureTheory.Linfty.mulL2` — the multiplication representation `f ↦ M_f` of `L∞(μ, ℂ)` on
  `L²(μ, ℂ)`.
* `MeasureTheory.Linfty.compBCF g f` — the element `g ∘ f` of `L∞` for a bounded continuous `g`.
* `MeasureTheory.Linfty.indicatorConst hs c` — the indicator `c 1_s ∈ L∞` of any measurable set,
  of finite or infinite measure; Mathlib's `indicatorConstLp` requires `μ s ≠ ∞` for every `p`.

## Main results

* `MeasureTheory.Linfty.coeFn_mulL2`, `MeasureTheory.Linfty.norm_mulL2_le` — `M_f u = f u`
  almost everywhere, and `‖M_f‖ ≤ ‖f‖`.
* `MeasureTheory.Linfty.inner_mulL2_self_eq_integral` — `⟪u, M_f u⟫ = ∫ f d(|u|² μ)`.
* `MeasureTheory.Linfty.ae_mem_spectrum_mulL2_of_ne_zero` — `f x ∈ σ(M_f)` for almost every `x`
  with `u x ≠ 0`, for any `u ∈ L²`; `MeasureTheory.Linfty.ae_mem_spectrum_mulL2` — for almost
  every `x`, when `μ` is σ-finite.
* `MeasureTheory.Linfty.cfc_mulL2` — `g(M_f) = M_{g ∘ f}`.
* `MeasureTheory.L2.exists_ae_ne_zero` — for σ-finite `μ`, `L²` has an almost everywhere
  nonvanishing vector.

* `MeasureTheory.Linfty.coeFn_mul`, `MeasureTheory.Linfty.coeFn_one` — multiplication and unit are
  pointwise almost everywhere.
* `MeasureTheory.Linfty.norm_le_of_ae_norm_le`, `MeasureTheory.Linfty.ae_norm_le_norm` — the norm
  is the essential supremum of the pointwise norm.
-/

@[expose] public section

open ENNReal Filter
open scoped BoundedContinuousFunction

namespace MeasureTheory

namespace Linfty

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α}

section NormedRing

variable {R : Type*} [NormedRing R]

/-- Pointwise multiplication on `L∞`, as Mathlib's Hölder multiplication. -/
noncomputable instance instMul : Mul (Lp R ∞ μ) where
  mul f g := f • g

lemma mul_def (f g : Lp R ∞ μ) : f * g = f • g := rfl

lemma coeFn_mul (f g : Lp R ∞ μ) : ⇑(f * g) =ᵐ[μ] ⇑f * ⇑g :=
  Lp.coeFn_lpSMul f g

/-- The constant function `1` in `L∞`. -/
noncomputable instance instOne : One (Lp R ∞ μ) where
  one := (memLp_top_const (1 : R)).toLp _

lemma coeFn_one : ⇑(1 : Lp R ∞ μ) =ᵐ[μ] 1 :=
  (memLp_top_const (μ := μ) (1 : R)).coeFn_toLp

/-- `L∞` is a ring under pointwise operations. -/
noncomputable instance instRing : Ring (Lp R ∞ μ) :=
  { (inferInstance : AddCommGroup (Lp R ∞ μ)), instMul, instOne with
    mul_assoc f g h := Lp.ext <| by
      filter_upwards [coeFn_mul (f * g) h, coeFn_mul f (g * h), coeFn_mul f g, coeFn_mul g h]
        with x h₁ h₂ h₃ h₄
      simp [h₁, h₂, h₃, h₄, mul_assoc]
    one_mul f := Lp.ext <| by
      filter_upwards [coeFn_mul 1 f, coeFn_one (R := R) (μ := μ)] with x h₁ h₂
      simp [h₁, h₂]
    mul_one f := Lp.ext <| by
      filter_upwards [coeFn_mul f 1, coeFn_one (R := R) (μ := μ)] with x h₁ h₂
      simp [h₁, h₂]
    left_distrib f g h := Lp.add_smul f g h
    right_distrib f g h := Lp.smul_add f g h
    zero_mul f := Lp.zero_smul R ∞ f
    mul_zero f := Lp.smul_zero R ∞ f }

/-- `L∞` is a normed ring: `‖f g‖ ≤ ‖f‖ ‖g‖`. -/
noncomputable instance instNormedRing : NormedRing (Lp R ∞ μ) where
  dist_eq _ _ := rfl
  norm_mul_le f g := Lp.norm_smul_le f g

/-- The norm on `L∞` bounds the pointwise norm almost everywhere. -/
lemma ae_norm_le_norm (f : Lp R ∞ μ) : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖f‖ := by
  filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := μ)] with x hx
  rw [← eLpNorm_exponent_top (Lp.aestronglyMeasurable f)] at hx
  have h := ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) hx
  rwa [toReal_enorm, ← Lp.norm_def] at h

/-- An almost everywhere bound on the pointwise norm bounds the norm on `L∞`. -/
lemma norm_le_of_ae_norm_le (f : Lp R ∞ μ) {c : ℝ} (hc : 0 ≤ c) (hf : ∀ᵐ x ∂μ, ‖f x‖ ≤ c) :
    ‖f‖ ≤ c := by
  rw [Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable f)]
  exact ENNReal.toReal_le_of_le_ofReal hc (eLpNormEssSup_le_of_ae_bound hf)

section NormedAlgebra

variable {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra 𝕜 R]

instance : IsScalarTower 𝕜 (Lp R ∞ μ) (Lp R ∞ μ) where
  smul_assoc := Lp.smul_assoc

instance : SMulCommClass 𝕜 (Lp R ∞ μ) (Lp R ∞ μ) where
  smul_comm := Lp.smul_comm

/-- `L∞` is a normed `𝕜`-algebra. -/
noncomputable instance instNormedAlgebra : NormedAlgebra 𝕜 (Lp R ∞ μ) where
  __ := Algebra.ofModule (fun r x y => smul_mul_assoc r x y) (fun r x y => mul_smul_comm r x y)
  norm_smul_le := norm_smul_le

end NormedAlgebra

end NormedRing

/-- `L∞` of a commutative normed ring is commutative. -/
noncomputable instance instCommRing {R : Type*} [NormedCommRing R] : CommRing (Lp R ∞ μ) :=
  { instRing with
    mul_comm f g := Lp.ext <| by
      filter_upwards [coeFn_mul f g, coeFn_mul g f] with x h₁ h₂
      rw [h₁, h₂, Pi.mul_apply, Pi.mul_apply, mul_comm] }

section StarRing

variable {R : Type*} [NormedRing R] [StarRing R] [NormedStarGroup R]

/-- `L∞` is a star ring under pointwise conjugation. -/
noncomputable instance instStarRing : StarRing (Lp R ∞ μ) where
  star_mul f g := Lp.ext <|
    calc ⇑(star (f * g)) =ᵐ[μ] star (⇑f * ⇑g) := (Lp.coeFn_star _).trans (coeFn_mul f g).star
      _ = star ⇑g * star ⇑f := star_mul _ _
      _ =ᵐ[μ] ⇑(star g * star f) :=
        ((Lp.coeFn_star g).mul (Lp.coeFn_star f)).symm.trans (coeFn_mul _ _).symm
  star_add f g := Lp.ext <|
    calc ⇑(star (f + g)) =ᵐ[μ] star (⇑f + ⇑g) := (Lp.coeFn_star _).trans (Lp.coeFn_add f g).star
      _ = star ⇑f + star ⇑g := star_add _ _
      _ =ᵐ[μ] ⇑(star f + star g) :=
        ((Lp.coeFn_star f).add (Lp.coeFn_star g)).symm.trans (Lp.coeFn_add _ _).symm

/-- `L∞` of a C⋆-ring is a C⋆-ring. -/
instance instCStarRing [CStarRing R] : CStarRing (Lp R ∞ μ) where
  norm_mul_self_le f := by
    rw [← sq, ← Real.le_sqrt (norm_nonneg _) (norm_nonneg _)]
    refine norm_le_of_ae_norm_le _ (Real.sqrt_nonneg _) ?_
    filter_upwards [ae_norm_le_norm (star f * f), Lp.coeFn_star f, coeFn_mul (star f) f]
      with x hx hstar hmul
    rw [Real.le_sqrt (norm_nonneg _) (norm_nonneg _), sq]
    convert hx using 1
    rw [hmul, Pi.mul_apply, hstar, Pi.star_apply, CStarRing.norm_star_mul_self]

end StarRing

section CStarAlgebra

variable {R : Type*} [CStarAlgebra R]

noncomputable instance : StarModule ℂ (Lp R ∞ μ) where
  star_smul c f := Lp.ext <| by
    filter_upwards [Lp.coeFn_star (c • f), Lp.coeFn_smul c f, Lp.coeFn_smul (star c) (star f),
      Lp.coeFn_star f] with x h₁ h₂ h₃ h₄
    rw [h₁, Pi.star_apply, h₂, Pi.smul_apply, star_smul, h₃, Pi.smul_apply, h₄, Pi.star_apply]

/-- `L∞` of a C⋆-algebra is a C⋆-algebra. -/
noncomputable instance instCStarAlgebra : CStarAlgebra (Lp R ∞ μ) where

end CStarAlgebra

section Indicator

variable {E : Type*} [NormedAddCommGroup E] {s : Set α}

/-- The indicator `c 1_s` of a measurable set as an element of `L∞`: the constant `c` lies in
`L∞` (`MeasureTheory.memLp_top_const`) and so does its restriction to `s`
(`MeasureTheory.MemLp.indicator`). Mathlib's `MeasureTheory.indicatorConstLp` requires `μ s ≠ ∞`
for every `p`, a hypothesis that is spurious for `p = ∞`, so it cannot be used here.

TODO (upstream): relax the hypothesis of `MeasureTheory.memLp_indicator_const` to
`c = 0 ∨ μ s ≠ ∞ ∨ p = ∞`, generalise `MeasureTheory.indicatorConstLp` accordingly, and replace
this definition by `indicatorConstLp ∞ hs _ c`. -/
noncomputable def indicatorConst (hs : MeasurableSet s) (c : E) : Lp E ∞ μ :=
  ((memLp_top_const c).indicator hs).toLp _

lemma coeFn_indicatorConst (hs : MeasurableSet s) (c : E) :
    ⇑(indicatorConst (μ := μ) hs c) =ᵐ[μ] s.indicator fun _ => c :=
  MemLp.coeFn_toLp _

end Indicator

section Multiplication

/-! ### The multiplication representation on `L²` -/

open scoped InnerProductSpace

/-- Multiplication by `f ∈ L∞`, as a bounded operator on `L²`. -/
noncomputable def mulL2CLM (f : Lp ℂ ∞ μ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous
    { toFun u := f • u
      map_add' u v := Lp.add_smul f u v
      map_smul' c u := (Lp.smul_comm c f u).symm }
    ‖f‖ fun u => Lp.norm_smul_le f u

lemma mulL2CLM_apply (f : Lp ℂ ∞ μ) (u : Lp ℂ 2 μ) : mulL2CLM f u = f • u := rfl

lemma coeFn_mulL2CLM (f : Lp ℂ ∞ μ) (u : Lp ℂ 2 μ) : ⇑(mulL2CLM f u) =ᵐ[μ] ⇑f * ⇑u :=
  Lp.coeFn_lpSMul f u

/-- The **multiplication representation** of `L∞` on `L²`: `f ↦ (u ↦ f u)`, a unital
`⋆`-homomorphism. -/
noncomputable def mulL2 : Lp ℂ ∞ μ →⋆ₐ[ℂ] (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) where
  toFun := mulL2CLM
  map_one' := ContinuousLinearMap.ext fun u => Lp.ext <| by
    filter_upwards [coeFn_mulL2CLM 1 u, coeFn_one (R := ℂ) (μ := μ)] with x h₁ h₂
    rw [h₁, Pi.mul_apply, h₂, Pi.one_apply, one_mul, one_apply_eq_self]
  map_mul' f g := ContinuousLinearMap.ext fun u => Lp.ext <| by
    filter_upwards [coeFn_mulL2CLM (f * g) u, coeFn_mul f g, coeFn_mulL2CLM f (mulL2CLM g u),
      coeFn_mulL2CLM g u] with x h₁ h₂ h₃ h₄
    rw [h₁, mul_apply_eq_comp, h₃, Pi.mul_apply, Pi.mul_apply, h₂, h₄, Pi.mul_apply,
      Pi.mul_apply, mul_assoc]
  map_zero' := ContinuousLinearMap.ext fun u => Lp.zero_smul ℂ ∞ u
  map_add' f g := ContinuousLinearMap.ext fun u => Lp.smul_add f g u
  commutes' c := ContinuousLinearMap.ext fun u => by
    change ((algebraMap ℂ (Lp ℂ ∞ μ) c) • u) = (algebraMap ℂ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) c) u
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Lp.smul_assoc,
      _root_.smul_apply, one_apply_eq_self]
    congr 1
    exact Lp.ext <| by
      filter_upwards [Lp.coeFn_lpSMul (r := 2) (1 : Lp ℂ ∞ μ) u, coeFn_one (R := ℂ) (μ := μ)]
        with x h₁ h₂
      rw [h₁, Pi.smul_apply', h₂, Pi.one_apply, one_smul]
  map_star' f := by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.eq_adjoint_iff]
    intro u v
    rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_mulL2CLM (star f) u, coeFn_mulL2CLM f v, Lp.coeFn_star f] with x h₁ h₂ h₃
    rw [h₁, h₂, Pi.mul_apply, Pi.mul_apply, h₃, Pi.star_apply]
    simp only [RCLike.inner_apply, map_mul, RCLike.star_def, Complex.conj_conj]
    ring

lemma mulL2_apply (f : Lp ℂ ∞ μ) (u : Lp ℂ 2 μ) : mulL2 f u = f • u := rfl

lemma coeFn_mulL2 (f : Lp ℂ ∞ μ) (u : Lp ℂ 2 μ) : ⇑(mulL2 f u) =ᵐ[μ] ⇑f * ⇑u :=
  Lp.coeFn_lpSMul f u

lemma norm_mulL2_le (f : Lp ℂ ∞ μ) : ‖mulL2 f‖ ≤ ‖f‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg f) fun u => Lp.norm_smul_le f u

/-- `algebraMap c` in `L∞` is the constant function `c`. -/
lemma coeFn_algebraMap (c : ℂ) : ⇑(algebraMap ℂ (Lp ℂ ∞ μ) c) =ᵐ[μ] fun _ => c := by
  rw [Algebra.algebraMap_eq_smul_one]
  filter_upwards [Lp.coeFn_smul c (1 : Lp ℂ ∞ μ), coeFn_one (R := ℂ) (μ := μ)] with x h₁ h₂
  rw [h₁, Pi.smul_apply, h₂, Pi.one_apply, smul_eq_mul, mul_one]

/-- A multiplication operator is normal. -/
lemma isStarNormal_mulL2 (f : Lp ℂ ∞ μ) : IsStarNormal (mulL2 f) :=
  ⟨by rw [← map_star, Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]⟩

/-- Two elements of `L∞` agreeing wherever some `u ∈ L²` does not vanish give the same
multiplication operator. -/
lemma mulL2_eq_of_ae {a b : Lp ℂ ∞ μ}
    (h : ∀ u : Lp ℂ 2 μ, ∀ᵐ x ∂μ, u x ≠ 0 → a x = b x) : mulL2 a = mulL2 b := by
  ext1 u
  refine Lp.ext ?_
  filter_upwards [coeFn_mulL2 a u, coeFn_mulL2 b u, h u] with x h₁ h₂ h₃
  rw [h₁, h₂, Pi.mul_apply, Pi.mul_apply]
  by_cases hu : u x = 0
  · rw [hu, mul_zero, mul_zero]
  · rw [h₃ hu]

/-- **The values of `f` lie in the spectrum of `M_f`** wherever a vector `u ∈ L²` does not
vanish. A point `l` outside the spectrum has a ball around it whose preimage under `f` meets
`{u ≠ 0}` in a null set: otherwise, for some `n`, the set `t` where `|f - l| < ε` and
`|u| ≥ 1 / n` has finite positive measure, and its indicator has `‖(l - M_f) 1_t‖ ≤ ε ‖1_t‖`,
against the boundedness of `(l - M_f)⁻¹` for small `ε`. No hypothesis on `μ` is needed: the parts
of `μ` carrying no `L²` vectors, such as `∞ • δ` on a point, are not seen by `M_f`. -/
lemma ae_mem_spectrum_mulL2_of_ne_zero (f : Lp ℂ ∞ μ) (u : Lp ℂ 2 μ) :
    ∀ᵐ x ∂μ, u x ≠ 0 → f x ∈ spectrum ℂ (mulL2 f) := by
  set σ := spectrum ℂ (mulL2 f)
  have hfm : Measurable (⇑f) := (Lp.stronglyMeasurable f).measurable
  have hum : Measurable (⇑u) := (Lp.stronglyMeasurable u).measurable
  have key : ∀ l : (σᶜ : Set ℂ), ∃ ε > 0,
      μ (⇑f ⁻¹' Metric.ball (l : ℂ) ε ∩ {x | u x ≠ 0}) = 0 := by
    rintro ⟨l, hl⟩
    rw [Set.mem_compl_iff, spectrum.notMem_iff] at hl
    set T := algebraMap ℂ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) l - mulL2 f
    set B : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ := ↑hl.unit⁻¹
    refine ⟨(‖B‖ + 1)⁻¹, by positivity, ?_⟩
    by_contra hne
    -- some level set `{|u| ≥ 1 / n}` meets the preimage of the ball in positive measure
    set t : ℕ → Set α := fun n =>
      ⇑f ⁻¹' Metric.ball (l : ℂ) (‖B‖ + 1)⁻¹ ∩ {x | (n : ℝ≥0∞)⁻¹ ≤ ‖u x‖ₑ}
    have hcover : ⇑f ⁻¹' Metric.ball (l : ℂ) (‖B‖ + 1)⁻¹ ∩ {x | u x ≠ 0} ⊆ ⋃ n, t n := by
      rintro x ⟨hx, hu⟩
      obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (enorm_ne_zero.mpr hu)
      exact Set.mem_iUnion.mpr ⟨n, hx, hn.le⟩
    obtain ⟨n, hn⟩ : ∃ n, μ (t n) ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (measure_mono_null hcover (measure_iUnion_null_iff.mpr h))
    have ht : MeasurableSet (t n) :=
      (hfm Metric.isOpen_ball.measurableSet).inter (measurableSet_le measurable_const hum.enorm)
    have hfin : μ (t n) < ∞ :=
      (measure_mono Set.inter_subset_right).trans_lt
        ((Lp.memLp u).meas_ge_lt_top'_enorm two_ne_zero ENNReal.ofNat_ne_top (by simp)
          fun _ => by simp)
    have hts : t n ⊆ ⇑f ⁻¹' Metric.ball (l : ℂ) (‖B‖ + 1)⁻¹ := Set.inter_subset_left
    have hpos : 0 < μ (t n) := pos_iff_ne_zero.mpr hn
    set v := indicatorConstLp 2 ht hfin.ne (1 : ℂ)
    have hμt : 0 < μ.real (t n) := ENNReal.toReal_pos hpos.ne' hfin.ne
    have hv : 0 < ‖v‖ := by
      rw [norm_indicatorConstLp two_ne_zero ENNReal.ofNat_ne_top, norm_one, one_mul]
      positivity
    have hT : T = mulL2 (algebraMap ℂ (Lp ℂ ∞ μ) l - f) := by
      rw [map_sub, AlgHomClass.commutes]
    have hTv : ‖T v‖ ≤ (‖B‖ + 1)⁻¹ * ‖v‖ := by
      rw [hT]
      refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
      filter_upwards [coeFn_mulL2 (algebraMap ℂ (Lp ℂ ∞ μ) l - f) v,
        Lp.coeFn_sub (algebraMap ℂ (Lp ℂ ∞ μ) l) f, coeFn_algebraMap (μ := μ) l,
        indicatorConstLp_coeFn (p := 2) (hs := ht) (hμs := hfin.ne) (c := (1 : ℂ))]
        with x h₁ h₂ h₃ h₄
      rw [h₁, Pi.mul_apply, h₂, Pi.sub_apply, h₃, h₄]
      by_cases hx : x ∈ t n
      · have hball := hts hx
        rw [Set.mem_preimage, Metric.mem_ball, dist_comm, dist_eq_norm] at hball
        rw [Set.indicator_of_mem hx, mul_one, norm_one, mul_one]
        exact hball.le
      · rw [Set.indicator_of_notMem hx, mul_zero, norm_zero, mul_zero]
    have hBT : B (T v) = v := by
      rw [← mul_apply_eq_comp, show B * T = 1 from by
        rw [show T = ↑hl.unit from hl.unit_spec.symm]
        exact Units.inv_mul _, one_apply_eq_self]
    have hlt : ‖B‖ * ((‖B‖ + 1)⁻¹ * ‖v‖) < ‖v‖ := by
      rw [← mul_assoc]
      refine mul_lt_of_lt_one_left hv ?_
      rw [← div_eq_mul_inv, div_lt_one (by positivity)]
      linarith
    have hle : ‖v‖ ≤ ‖B‖ * ((‖B‖ + 1)⁻¹ * ‖v‖) := by
      conv_lhs => rw [← hBT]
      exact (B.le_opNorm _).trans (by gcongr)
    linarith
  choose ε hε hnull using key
  obtain ⟨S, hS, hU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun l : (σᶜ : Set ℂ) => Metric.ball (l : ℂ) (ε l)) fun _ => Metric.isOpen_ball
  have hsub : {x | ¬ (u x ≠ 0 → f x ∈ σ)} ⊆
      ⋃ l ∈ S, ⇑f ⁻¹' Metric.ball (l : ℂ) (ε l) ∩ {x | u x ≠ 0} := by
    intro x hx
    rw [Set.mem_ofPred_eq, not_imp] at hx
    have hmem : f x ∈ ⋃ l : (σᶜ : Set ℂ), Metric.ball (l : ℂ) (ε l) :=
      Set.mem_iUnion.mpr ⟨⟨f x, hx.2⟩, Metric.mem_ball_self (hε ⟨f x, hx.2⟩)⟩
    rw [← hU] at hmem
    obtain ⟨l, hlS, hl⟩ := Set.mem_iUnion₂.mp hmem
    exact Set.mem_iUnion₂.mpr ⟨l, hlS, hl, hx.1⟩
  exact ae_iff.mpr (measure_mono_null hsub ((measure_biUnion_null_iff hS).mpr fun l _ => hnull l))

/-- For a σ-finite measure, `L²` contains an almost everywhere nonvanishing vector, `√g` for a
strictly positive integrable `g`. -/
lemma _root_.MeasureTheory.L2.exists_ae_ne_zero [SigmaFinite μ] :
    ∃ u : Lp ℂ 2 μ, ∀ᵐ x ∂μ, u x ≠ 0 := by
  obtain ⟨g, hgpos, hgm, hgint⟩ := exists_pos_lintegral_lt_of_sigmaFinite μ one_ne_zero
  set ω₀ : α → ℂ := fun x => (Real.sqrt (g x) : ℂ)
  have hω₀m : Measurable ω₀ := by fun_prop
  have hω₀ : MemLp ω₀ 2 μ := by
    refine (memLp_two_iff_integrable_sq_norm hω₀m.aestronglyMeasurable).mpr ?_
    have : (fun x => ‖ω₀ x‖ ^ 2) = fun x => ((g x : ℝ≥0∞)).toReal := by
      ext x
      simp [ω₀, Real.sq_sqrt (NNReal.coe_nonneg _)]
    rw [this]
    exact integrable_toReal_of_lintegral_ne_top (by fun_prop) (hgint.trans ENNReal.one_lt_top).ne
  refine ⟨hω₀.toLp ω₀, ?_⟩
  filter_upwards [hω₀.coeFn_toLp] with x hx
  rw [hx]
  simp [ω₀, (hgpos x).ne']

/-- **The values of `f` lie in the spectrum of `M_f`** almost everywhere, for a σ-finite `μ`:
the case of `MeasureTheory.Linfty.ae_mem_spectrum_mulL2_of_ne_zero` at an almost everywhere
nonvanishing `u ∈ L²`. Some such hypothesis is needed: for the measure `∞ • δ` on a point,
`L²(μ) = 0`, so `M_f` has empty spectrum, while the point is not null. -/
lemma ae_mem_spectrum_mulL2 [SigmaFinite μ] (f : Lp ℂ ∞ μ) :
    ∀ᵐ x ∂μ, f x ∈ spectrum ℂ (mulL2 f) := by
  obtain ⟨u, hu⟩ := L2.exists_ae_ne_zero (μ := μ)
  filter_upwards [ae_mem_spectrum_mulL2_of_ne_zero f u, hu] with x h₁ h₂
  exact h₁ h₂

/-- The element `g ∘ f` of `L∞`, for a bounded continuous `g`. -/
noncomputable def compBCF (g : ℂ →ᵇ ℂ) (f : Lp ℂ ∞ μ) : Lp ℂ ∞ μ :=
  (memLp_top_of_bound (g.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f)) ‖g‖
    (Eventually.of_forall fun x => g.norm_coe_le_norm (f x))).toLp _

lemma coeFn_compBCF (g : ℂ →ᵇ ℂ) (f : Lp ℂ ∞ μ) : ⇑(compBCF g f) =ᵐ[μ] g ∘ f :=
  MemLp.coeFn_toLp _

/-- **Continuous functional calculus of a multiplication operator**: `g(M_f) = M_{g ∘ f}` for a
bounded continuous `g`. The map `k ↦ M_{k̃ ∘ f}`, with `k̃` the extension of `k` by `0` off the
spectrum, is a continuous `⋆`-homomorphism sending the identity to `M_f`, because `f` takes
values in the spectrum wherever an `L²` vector does not vanish
(`MeasureTheory.Linfty.ae_mem_spectrum_mulL2_of_ne_zero`); so it is `cfcHom`. No hypothesis on
`μ` is needed. -/
theorem cfc_mulL2 (g : ℂ →ᵇ ℂ) (f : Lp ℂ ∞ μ) :
    cfc (⇑g) (mulL2 f) = mulL2 (compBCF g f) := by
  classical
  have hN := isStarNormal_mulL2 f
  set σ := spectrum ℂ (mulL2 f)
  have hσ : MeasurableSet σ := (spectrum.isClosed _).measurableSet
  have hae : ∀ u : Lp ℂ 2 μ, ∀ᵐ x ∂μ, u x ≠ 0 → f x ∈ σ := ae_mem_spectrum_mulL2_of_ne_zero f
  let G : C(σ, ℂ) → ℂ → ℂ := fun k z => if hz : z ∈ σ then k ⟨z, hz⟩ else 0
  have hGσ : ∀ k (z : ℂ) (hz : z ∈ σ), G k z = k ⟨z, hz⟩ := fun k z hz => by simp [G, hz]
  have hGm : ∀ k, Measurable (G k) := fun k =>
    Measurable.dite k.continuous.measurable measurable_const hσ
  have hGb : ∀ k z, ‖G k z‖ ≤ ‖k‖ := fun k z => by
    by_cases hz : z ∈ σ
    · rw [hGσ k z hz]
      exact k.norm_coe_le_norm _
    · simp [G, hz, norm_nonneg k]
  have hmem : ∀ k, MemLp (G k ∘ f) ∞ μ := fun k =>
    memLp_top_of_bound ((hGm k).comp_aemeasurable (Lp.aestronglyMeasurable f).aemeasurable
      |>.aestronglyMeasurable) ‖k‖ (Eventually.of_forall fun x => hGb k (f x))
  let L : C(σ, ℂ) → Lp ℂ ∞ μ := fun k => (hmem k).toLp _
  have hL : ∀ k, ⇑(L k) =ᵐ[μ] G k ∘ f := fun k => MemLp.coeFn_toLp _
  let φ : C(σ, ℂ) →⋆ₐ[ℂ] (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :=
    { toFun := fun k => mulL2 (L k)
      map_one' := by
        rw [← map_one mulL2]
        refine mulL2_eq_of_ae fun u => ?_
        filter_upwards [hL 1, coeFn_one (R := ℂ) (μ := μ), hae u] with x h₁ h₂ h₃ hu
        rw [h₁, h₂, Function.comp_apply, hGσ _ _ (h₃ hu), Pi.one_apply, ContinuousMap.one_apply]
      map_mul' k₁ k₂ := by
        rw [← map_mul]
        refine mulL2_eq_of_ae fun u => ?_
        filter_upwards [hL (k₁ * k₂), coeFn_mul (L k₁) (L k₂), hL k₁, hL k₂, hae u]
          with x h₁ h₂ h₃ h₄ h₅ hu
        rw [h₁, h₂, Pi.mul_apply, h₃, h₄, Function.comp_apply, Function.comp_apply,
          Function.comp_apply, hGσ _ _ (h₅ hu), hGσ _ _ (h₅ hu), hGσ _ _ (h₅ hu),
          ContinuousMap.mul_apply]
      map_zero' := by
        rw [← map_zero mulL2]
        congr 1
        refine Lp.ext ?_
        filter_upwards [hL 0, Lp.coeFn_zero ℂ ∞ μ] with x h₁ h₂
        rw [h₁, h₂]
        simp [G]
      map_add' k₁ k₂ := by
        rw [← map_add]
        refine mulL2_eq_of_ae fun u => ?_
        filter_upwards [hL (k₁ + k₂), Lp.coeFn_add (L k₁) (L k₂), hL k₁, hL k₂, hae u]
          with x h₁ h₂ h₃ h₄ h₅ hu
        rw [h₁, h₂, Pi.add_apply, h₃, h₄, Function.comp_apply, Function.comp_apply,
          Function.comp_apply, hGσ _ _ (h₅ hu), hGσ _ _ (h₅ hu), hGσ _ _ (h₅ hu),
          ContinuousMap.add_apply]
      commutes' c := by
        rw [← AlgHomClass.commutes mulL2 c]
        refine mulL2_eq_of_ae fun u => ?_
        filter_upwards [hL (algebraMap ℂ _ c), coeFn_algebraMap (μ := μ) c, hae u]
          with x h₁ h₂ h₃ hu
        rw [h₁, h₂, Function.comp_apply, hGσ _ _ (h₃ hu)]
        rfl
      map_star' k := by
        rw [← map_star mulL2]
        refine mulL2_eq_of_ae fun u => ?_
        filter_upwards [hL (star k), Lp.coeFn_star (L k), hL k, hae u] with x h₁ h₂ h₃ h₄ hu
        rw [h₁, h₂, Pi.star_apply, h₃, Function.comp_apply, Function.comp_apply, hGσ _ _ (h₄ hu),
          hGσ _ _ (h₄ hu), ContinuousMap.star_apply] }
  have hφ : Continuous φ := by
    refine AddMonoidHomClass.continuous_of_bound φ 1 fun k => ?_
    rw [one_mul]
    refine (norm_mulL2_le (L k)).trans (norm_le_of_ae_norm_le _ (norm_nonneg k) ?_)
    filter_upwards [hL k] with x hx
    rw [hx]
    exact hGb k (f x)
  have hid : φ (.restrict σ (.id ℂ)) = mulL2 f := by
    refine mulL2_eq_of_ae fun u => ?_
    filter_upwards [hL (.restrict σ (.id ℂ)), hae u] with x h₁ h₂ hu
    rw [h₁, Function.comp_apply, hGσ _ _ (h₂ hu)]
    rfl
  rw [cfc_apply (⇑g) (mulL2 f) hN g.continuous.continuousOn,
    cfcHom_eq_of_continuous_of_map_id hN φ hφ hid]
  refine mulL2_eq_of_ae fun u => ?_
  filter_upwards [hL ⟨(spectrum ℂ (mulL2 f)).domRestrict g, g.continuous.continuousOn.domRestrict⟩,
    coeFn_compBCF g f, hae u] with x h₁ h₂ h₃ hu
  rw [h₁, h₂, Function.comp_apply, hGσ _ _ (h₃ hu)]
  rfl

/-! ### Bounded functions and indicators -/

/-- The density `|u|²` of the scalar spectral measures of multiplication operators. -/
lemma measurable_enorm_sq (u : Lp ℂ 2 μ) : Measurable fun x => ‖u x‖ₑ ^ 2 :=
  (Lp.stronglyMeasurable u).measurable.enorm.pow_const 2

instance isFiniteMeasure_withDensity_enorm_sq (u : Lp ℂ 2 μ) :
    IsFiniteMeasure (μ.withDensity fun x => ‖u x‖ₑ ^ 2) := by
  refine isFiniteMeasure_withDensity ?_
  have h := ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp
    (Lp.memLp u)).lintegral_lt_top
  refine ne_of_lt (lt_of_eq_of_lt (lintegral_congr fun x => ?_) h)
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]

/-- A bounded measurable function as an element of `L∞`. -/
noncomputable def boundedLinfty (f : α → ℂ) (hf : Measurable f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    Lp ℂ ∞ μ :=
  (memLp_top_of_bound hf.aestronglyMeasurable C (Eventually.of_forall hC)).toLp f

lemma coeFn_boundedLinfty (f : α → ℂ) (hf : Measurable f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    ⇑(boundedLinfty (μ := μ) f hf C hC) =ᵐ[μ] f :=
  MemLp.coeFn_toLp _

/-- `‖1_T w‖² = ∫_T |w|²`, the measure of `T` for `|w|² μ`. -/
lemma norm_mulL2_indicatorConst_sq (w : Lp ℂ 2 μ) {T : Set α} (hT : MeasurableSet T) :
    ‖mulL2 (indicatorConst hT (1 : ℂ)) w‖ ^ 2 = (μ.withDensity fun x => ‖w x‖ₑ ^ 2).real T := by
  rw [@norm_sq_eq_re_inner ℂ, MeasureTheory.L2.inner_def,
    ← show ∫ a, (⟪(mulL2 (indicatorConst hT (1 : ℂ)) w) a,
          (mulL2 (indicatorConst hT (1 : ℂ)) w) a⟫_ℂ).re ∂μ
        = RCLike.re (∫ a, ⟪(mulL2 (indicatorConst hT (1 : ℂ)) w) a,
          (mulL2 (indicatorConst hT (1 : ℂ)) w) a⟫_ℂ ∂μ) by
      simpa using integral_re (𝕜 := ℂ) (MeasureTheory.L2.integrable_inner (𝕜 := ℂ)
        (mulL2 (indicatorConst hT (1 : ℂ)) w) (mulL2 (indicatorConst hT (1 : ℂ)) w)),
    measureReal_def, withDensity_apply _ hT]
  have hint : Integrable (fun x => ‖w x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable w)).mp (Lp.memLp w)
  have hae : (fun a => (⟪(mulL2 (indicatorConst hT (1 : ℂ)) w) a,
      (mulL2 (indicatorConst hT (1 : ℂ)) w) a⟫_ℂ).re) =ᵐ[μ] T.indicator fun x => ‖w x‖ ^ 2 := by
    filter_upwards [coeFn_mulL2 (indicatorConst hT (1 : ℂ)) w,
      coeFn_indicatorConst (μ := μ) hT (1 : ℂ)] with x h₁ h₂
    rw [h₁, Pi.mul_apply, h₂, inner_self_eq_norm_sq_to_K]
    by_cases hx : x ∈ T
    · simp [hx]
      norm_cast
    · simp [hx]
  rw [integral_congr_ae hae, integral_indicator hT, integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun x => sq_nonneg _) hint.aestronglyMeasurable.restrict]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]

/-- **Monotone truncation**: if measurable `Bₙ` increase inside `S` and cover it, then
`1_{Bₙ} w → 1_S w` in `L²`. -/
lemma tendsto_mulL2_indicatorConst (w : Lp ℂ 2 μ) {S : Set α} (hS : MeasurableSet S)
    {B : ℕ → Set α} (hB : ∀ n, MeasurableSet (B n)) (hmono : Monotone B) (hBS : ∀ n, B n ⊆ S)
    (hcover : S ⊆ ⋃ n, B n) :
    Tendsto (fun n => mulL2 (indicatorConst (hB n) (1 : ℂ)) w) atTop
      (nhds (mulL2 (indicatorConst hS (1 : ℂ)) w)) := by
  set ν := μ.withDensity fun x => ‖w x‖ₑ ^ 2
  have hdiff : ∀ n, mulL2 (indicatorConst (hB n) (1 : ℂ)) w - mulL2 (indicatorConst hS (1 : ℂ)) w =
      -mulL2 (indicatorConst (hS.diff (hB n)) (1 : ℂ)) w := fun n => Lp.ext <| by
    filter_upwards [Lp.coeFn_sub (mulL2 (indicatorConst (hB n) (1 : ℂ)) w)
        (mulL2 (indicatorConst hS (1 : ℂ)) w),
      Lp.coeFn_neg (mulL2 (indicatorConst (hS.diff (hB n)) (1 : ℂ)) w),
      coeFn_mulL2 (indicatorConst (hB n) (1 : ℂ)) w, coeFn_mulL2 (indicatorConst hS (1 : ℂ)) w,
      coeFn_mulL2 (indicatorConst (hS.diff (hB n)) (1 : ℂ)) w,
      coeFn_indicatorConst (μ := μ) (hB n) (1 : ℂ), coeFn_indicatorConst (μ := μ) hS (1 : ℂ),
      coeFn_indicatorConst (μ := μ) (hS.diff (hB n)) (1 : ℂ)] with x h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
    rw [h₁, h₂, Pi.sub_apply, Pi.neg_apply, h₃, h₄, h₅, Pi.mul_apply, Pi.mul_apply, Pi.mul_apply,
      h₆, h₇, h₈]
    by_cases hxB : x ∈ B n
    · simp [hxB, hBS n hxB]
    · by_cases hxS : x ∈ S <;> simp [hxB, hxS]
  have hmeas : Tendsto (fun n => ν (S \ B n)) atTop (nhds 0) := by
    have h := tendsto_measure_iInter_atTop (μ := ν) (s := fun n => S \ B n)
      (fun n => (hS.diff (hB n)).nullMeasurableSet)
      (fun n m hnm => Set.sdiff_subset_sdiff_right (hmono hnm)) ⟨0, measure_ne_top _ _⟩
    have hempty : (⋂ n, S \ B n) = ∅ := by
      ext x
      simp only [Set.mem_iInter, Set.mem_sdiff, Set.mem_empty_iff_false, iff_false, not_forall,
        not_and, not_not]
      by_cases hxS : x ∈ S
      · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hcover hxS)
        exact ⟨n, fun _ => hn⟩
      · exact ⟨0, fun h => absurd h hxS⟩
    rwa [hempty, measure_empty] at h
  have hreal : Tendsto (fun n => ν.real (S \ B n)) atTop (nhds 0) := by
    exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hmeas
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : ∀ n, ‖mulL2 (indicatorConst (hB n) (1 : ℂ)) w - mulL2 (indicatorConst hS (1 : ℂ)) w‖ =
      Real.sqrt (ν.real (S \ B n)) := fun n => by
    rw [hdiff, norm_neg, ← norm_mulL2_indicatorConst_sq, Real.sqrt_sq (norm_nonneg _)]
  simp_rw [hsq]
  have h' := (Real.continuous_sqrt.tendsto 0).comp hreal
  rw [Real.sqrt_zero] at h'
  exact h'

/-- **Vector functionals of multiplication operators**: `⟪u, M_f u⟫ = ∫ f d(|u|² μ)`. -/
lemma inner_mulL2_self_eq_integral (u : Lp ℂ 2 μ) (f : Lp ℂ ∞ μ) :
    ⟪u, mulL2 f u⟫_ℂ = ∫ x, f x ∂(μ.withDensity fun x => ‖u x‖ₑ ^ 2) := by
  rw [integral_withDensity_eq_integral_toReal_smul (measurable_enorm_sq u)
    (Eventually.of_forall fun x => ENNReal.pow_lt_top enorm_lt_top), MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_mulL2 f u] with x hx
  rw [hx, Pi.mul_apply, RCLike.inner_apply, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ENNReal.toReal_ofReal (by positivity), Complex.real_smul, Complex.ofReal_pow,
    ← Complex.mul_conj']
  ring

end Multiplication

end Linfty

end MeasureTheory
