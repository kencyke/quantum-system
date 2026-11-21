/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.CStarAlgebra.TensorProduct.Minimal

import Mathlib.Analysis.Normed.Module.HahnBanach
import QuantumSystem.Analysis.CStarAlgebra.GNS.DirectSum
import QuantumSystem.Analysis.CStarAlgebra.GNS.Irreducible
import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.Quotient

/-!
# C⋆-norms on the algebraic tensor product

A C⋆-norm on the algebraic tensor product `A ⊗[ℂ] B` of two C⋆-algebras is the norm `x ↦ ‖Φ x‖` of
an injective `⋆`-homomorphism `Φ : A ⊗[ℂ] B → C` into a C⋆-algebra `C`; the completion of
`A ⊗[ℂ] B` for it is the closure `Φ.closureRange` of the range of `Φ`
(`QuantumSystem/ForMathlib/Analysis/CStarAlgebra/ClosureRange.lean`). Every C⋆-norm is a cross norm,
and the norm of the minimal tensor product `A ⊗ₘᵢₙ B` is the least of them.

The algebras are not assumed unital, and `Φ` is not assumed to have dense range.

## Main definitions

* `MinTensorProduct.ofClosureRange hΦ` — for an injective `Φ`, the `⋆`-homomorphism of the
  completion `Φ.closureRange` of `A ⊗[ℂ] B` onto `A ⊗ₘᵢₙ B` that is the identity on `A ⊗[ℂ] B`.

## Main results

* `NonUnitalStarAlgHom.norm_apply_tmul_le` — `‖Φ (a ⊗ b)‖ ≤ ‖a‖ * ‖b‖` for every `⋆`-homomorphism
  `Φ` of `A ⊗[ℂ] B` into a C⋆-algebra.
* `NonUnitalStarAlgHom.norm_apply_tmul` — a C⋆-norm is a cross norm: `‖Φ (a ⊗ b)‖ = ‖a‖ * ‖b‖` for
  an injective `Φ`.
* `MinTensorProduct.norm_of_le_norm_apply` — the norm of `A ⊗ₘᵢₙ B` is the least C⋆-norm:
  `‖x‖ ≤ ‖Φ x‖` for an injective `Φ`.
* `MinTensorProduct.ofClosureRange_surjective` — the completion of `A ⊗[ℂ] B` for a C⋆-norm maps
  onto `A ⊗ₘᵢₙ B`, by `MinTensorProduct.ofClosureRange`.
-/

@[expose] public section

open scoped TensorProduct InnerProductSpace InnerProduct MinTensorProduct ComplexOrder

open Filter Topology

universe u v w

variable {A : Type u} {B : Type v} {C : Type w}

namespace NonUnitalStarAlgHom

/-! ### Positivity on pure tensors -/

section Order

variable [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  (Φ : A ⊗[ℂ] B →⋆ₙₐ[ℂ] C)

/-- A positive contraction `e` of a C⋆-algebra satisfies `e * e ≤ e`. -/
private lemma mul_self_le_self {D : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D]
    [StarOrderedRing D] {e : D} (he : 0 ≤ e) (hn : ‖e‖ ≤ 1) : e * e ≤ e := by
  have hsa : IsSelfAdjoint e := IsSelfAdjoint.of_nonneg he
  have h1 : e * e = cfcₙ (fun x : ℝ => x * x) e := by
    rw [cfcₙ_mul (fun x : ℝ => x) (fun x : ℝ => x) e, cfcₙ_id' ℝ e]
  have h2 : cfcₙ (fun x : ℝ => x) e = e := cfcₙ_id' ℝ e
  rw [h1]
  nth_rewrite 2 [← h2]
  refine cfcₙ_mono fun x hx => ?_
  have h0 : 0 ≤ x := quasispectrum_nonneg_of_nonneg e he x hx
  have hx1 : x ≤ 1 :=
    (Real.le_norm_self x).trans ((quasispectrum.norm_le_norm_of_mem hx).trans hn)
  nlinarith

/-- The square of a positive element is positive. -/
private lemma mul_self_nonneg_of_nonneg {D : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D]
    [StarOrderedRing D] {e : D} (he : 0 ≤ e) : 0 ≤ e * e := by
  have h := star_mul_self_nonneg e
  rwa [(IsSelfAdjoint.of_nonneg he).star_eq] at h

/-- `Φ` is positive on the tensors of positive elements: `a ⊗ b = (c ⊗ d)⋆ (c ⊗ d)` for
`a = c⋆ c` and `b = d⋆ d`. -/
private lemma apply_tmul_nonneg {a : A} {b : B} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ Φ (a ⊗ₜ[ℂ] b) := by
  obtain ⟨c, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha
  obtain ⟨d, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hb
  have h : (star c * c) ⊗ₜ[ℂ] (star d * d) = star (c ⊗ₜ[ℂ] d) * (c ⊗ₜ[ℂ] d) := by
    rw [TensorProduct.star_tmul, Algebra.TensorProduct.tmul_mul_tmul]
  rw [h, map_mul, map_star]
  exact star_mul_self_nonneg _

private lemma apply_tmul_mono_left {a a' : A} {b : B} (h : a ≤ a') (hb : 0 ≤ b) :
    Φ (a ⊗ₜ[ℂ] b) ≤ Φ (a' ⊗ₜ[ℂ] b) := by
  rw [← sub_nonneg, ← map_sub, ← TensorProduct.sub_tmul]
  exact apply_tmul_nonneg Φ (sub_nonneg.2 h) hb

private lemma apply_tmul_mono_right {a : A} {b b' : B} (ha : 0 ≤ a) (h : b ≤ b') :
    Φ (a ⊗ₜ[ℂ] b) ≤ Φ (a ⊗ₜ[ℂ] b') := by
  rw [← sub_nonneg, ← map_sub, ← TensorProduct.tmul_sub]
  exact apply_tmul_nonneg Φ ha (sub_nonneg.2 h)

/-- For positive contractions `p` and `q`, `x = Φ (p ⊗ q)` is positive with `x * x ≤ x`, so it is a
contraction. -/
private lemma norm_apply_tmul_le_one_of_nonneg {p : A} {q : B} (hp : 0 ≤ p) (hpn : ‖p‖ ≤ 1)
    (hq : 0 ≤ q) (hqn : ‖q‖ ≤ 1) : ‖Φ (p ⊗ₜ[ℂ] q)‖ ≤ 1 := by
  have hx0 : 0 ≤ Φ (p ⊗ₜ[ℂ] q) := apply_tmul_nonneg Φ hp hq
  have hxx : Φ (p ⊗ₜ[ℂ] q) * Φ (p ⊗ₜ[ℂ] q) ≤ Φ (p ⊗ₜ[ℂ] q) := by
    calc Φ (p ⊗ₜ[ℂ] q) * Φ (p ⊗ₜ[ℂ] q) = Φ ((p * p) ⊗ₜ[ℂ] (q * q)) := by
          rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul]
      _ ≤ Φ (p ⊗ₜ[ℂ] (q * q)) :=
          apply_tmul_mono_left Φ (mul_self_le_self hp hpn) (mul_self_nonneg_of_nonneg hq)
      _ ≤ Φ (p ⊗ₜ[ℂ] q) := apply_tmul_mono_right Φ hp (mul_self_le_self hq hqn)
  have hn : ‖Φ (p ⊗ₜ[ℂ] q)‖ ^ 2 ≤ ‖Φ (p ⊗ₜ[ℂ] q)‖ := by
    rw [← (IsSelfAdjoint.of_nonneg hx0).norm_mul_self]
    exact CStarAlgebra.norm_le_norm_of_le_of_nonneg hxx (mul_self_nonneg_of_nonneg hx0)
  by_contra hlt
  push Not at hlt
  nlinarith [norm_nonneg (Φ (p ⊗ₜ[ℂ] q))]

/-- `‖Φ (a ⊗ b)‖ ≤ 1` for contractions `a` and `b`. -/
private lemma norm_apply_tmul_le_one {a : A} {b : B} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖Φ (a ⊗ₜ[ℂ] b)‖ ≤ 1 := by
  have h : ‖Φ (a ⊗ₜ[ℂ] b)‖ ^ 2 ≤ 1 := by
    rw [sq, ← CStarRing.norm_star_mul_self, ← map_star, ← map_mul, TensorProduct.star_tmul,
      Algebra.TensorProduct.tmul_mul_tmul]
    refine norm_apply_tmul_le_one_of_nonneg Φ (star_mul_self_nonneg a) ?_ (star_mul_self_nonneg b) ?_
    · rw [CStarRing.norm_star_mul_self]
      nlinarith [norm_nonneg a]
    · rw [CStarRing.norm_star_mul_self]
      nlinarith [norm_nonneg b]
  by_contra hlt
  push Not at hlt
  nlinarith [norm_nonneg (Φ (a ⊗ₜ[ℂ] b))]

/-- A positive `p` with `s < ‖p‖` has a nonzero positive `p'`, a function of `p` supported in the
part of the spectrum above `s`, with `s p' ≤ p p'`. -/
private lemma exists_nonneg_smul_le_mul {D : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D]
    [StarOrderedRing D] {p : D} (hp : 0 ≤ p) {s : ℝ} (hs : 0 ≤ s) (hsp : s < ‖p‖) :
    ∃ p' : D, p' ≠ 0 ∧ 0 ≤ p' ∧ 0 ≤ p * p' ∧ 0 ≤ (s : ℂ) • p' ∧ (s : ℂ) • p' ≤ p * p' := by
  have hsa : IsSelfAdjoint p := IsSelfAdjoint.of_nonneg hp
  have hspec (x : ℝ) (hx : x ∈ quasispectrum ℝ p) : 0 ≤ x :=
    quasispectrum_nonneg_of_nonneg p hp x hx
  have hf : Continuous fun x : ℝ => max (x - s) 0 := by fun_prop
  have hf0 : max ((0 : ℝ) - s) 0 = 0 := by simp [hs]
  have h1 : p * cfcₙ (fun x : ℝ => max (x - s) 0) p =
      cfcₙ (fun x : ℝ => x * max (x - s) 0) p := by
    rw [cfcₙ_mul (fun x : ℝ => x) (fun x : ℝ => max (x - s) 0) p, cfcₙ_id' ℝ p]
  have h2 : (s : ℂ) • cfcₙ (fun x : ℝ => max (x - s) 0) p =
      cfcₙ (fun x : ℝ => s * max (x - s) 0) p := by
    rw [Complex.coe_smul]
    exact (cfcₙ_smul s (fun x : ℝ => max (x - s) 0) p).symm
  refine ⟨cfcₙ (fun x : ℝ => max (x - s) 0) p, fun h0 => ?_,
    cfcₙ_nonneg fun x _ => le_max_right _ _, ?_, ?_, ?_⟩
  · have hle : ‖p‖ ≤ s := by
      rw [← cfcₙ_id' ℝ p]
      refine norm_cfcₙ_le fun x hx => ?_
      have h3 := norm_apply_le_norm_cfcₙ (fun x : ℝ => max (x - s) 0) p hx
      rw [h0, norm_zero, norm_le_zero_iff] at h3
      have h4 := le_max_left (x - s) 0
      rw [Real.norm_of_nonneg (hspec x hx)]
      linarith
    linarith
  · rw [h1]
    exact cfcₙ_nonneg fun x hx => mul_nonneg (hspec x hx) (le_max_right _ _)
  · rw [h2]
    exact cfcₙ_nonneg fun x _ => mul_nonneg hs (le_max_right _ _)
  · rw [h1, h2]
    refine cfcₙ_mono fun x hx => ?_
    by_cases hxs : x ≤ s
    · simp [max_eq_right (sub_nonpos.2 hxs)]
    · exact mul_le_mul_of_nonneg_right (le_of_not_ge hxs) (le_max_right _ _)

/-- For positive `p` and `q` and an injective `Φ`, `s t ≤ ‖Φ (p ⊗ q)‖` whenever `s < ‖p‖` and
`t < ‖q‖`: with `p'` and `q'` supported above `s` and `t`, `s t Φ (p' ⊗ q') ≤ Φ (p ⊗ q) Φ (p' ⊗ q')`
and `Φ (p' ⊗ q') ≠ 0`. -/
private lemma mul_le_norm_apply_tmul_of_nonneg (hΦ : Function.Injective Φ) {p : A} {q : B}
    (hp : 0 ≤ p) (hq : 0 ≤ q) {s t : ℝ} (hs : 0 ≤ s) (hsp : s < ‖p‖) (ht : 0 ≤ t) (htq : t < ‖q‖) :
    s * t ≤ ‖Φ (p ⊗ₜ[ℂ] q)‖ := by
  obtain ⟨p', hp'0, hp', hpp', hsp'0, hsp'⟩ := exists_nonneg_smul_le_mul hp hs hsp
  obtain ⟨q', hq'0, hq', hqq', htq'0, htq'⟩ := exists_nonneg_smul_le_mul hq ht htq
  have hw0 : Φ (p' ⊗ₜ[ℂ] q') ≠ 0 := fun h => by
    have h0 : p' ⊗ₜ[ℂ] q' = 0 := hΦ (h.trans (map_zero Φ).symm)
    have hn := MinTensorProduct.norm_of_tmul p' q'
    rw [h0, map_zero, norm_zero] at hn
    rcases mul_eq_zero.1 hn.symm with h | h
    exacts [hp'0 (norm_eq_zero.1 h), hq'0 (norm_eq_zero.1 h)]
  have e1 : Φ (p ⊗ₜ[ℂ] q) * Φ (p' ⊗ₜ[ℂ] q') = Φ ((p * p') ⊗ₜ[ℂ] (q * q')) := by
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul]
  have e2 : ((s * t : ℝ) : ℂ) • Φ (p' ⊗ₜ[ℂ] q') = Φ (((s : ℂ) • p') ⊗ₜ[ℂ] ((t : ℂ) • q')) := by
    rw [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, map_smul,
      Complex.ofReal_mul]
  have h0 : 0 ≤ ((s * t : ℝ) : ℂ) • Φ (p' ⊗ₜ[ℂ] q') := by
    rw [e2]
    exact apply_tmul_nonneg Φ hsp'0 htq'0
  have hle : ((s * t : ℝ) : ℂ) • Φ (p' ⊗ₜ[ℂ] q') ≤ Φ (p ⊗ₜ[ℂ] q) * Φ (p' ⊗ₜ[ℂ] q') := by
    rw [e1, e2]
    exact (apply_tmul_mono_right Φ hsp'0 htq').trans (apply_tmul_mono_left Φ hsp' hqq')
  have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg hle h0
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hs ht)] at hn
  have hw : 0 < ‖Φ (p' ⊗ₜ[ℂ] q')‖ := norm_pos_iff.2 hw0
  exact le_of_mul_le_mul_right (hn.trans (norm_mul_le _ _)) hw

/-- For positive `p` and `q` and an injective `Φ`, `‖p‖ * ‖q‖ ≤ ‖Φ (p ⊗ q)‖`. -/
private lemma mul_norm_le_norm_apply_tmul_of_nonneg (hΦ : Function.Injective Φ) {p : A} {q : B}
    (hp : 0 ≤ p) (hq : 0 ≤ q) : ‖p‖ * ‖q‖ ≤ ‖Φ (p ⊗ₜ[ℂ] q)‖ := by
  by_contra hlt
  push Not at hlt
  have hpos : 0 < ‖p‖ * ‖q‖ := (norm_nonneg _).trans_lt hlt
  have hq0 : 0 < ‖q‖ := lt_of_le_of_ne (norm_nonneg q) fun h => by
    rw [← h, mul_zero] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨s, hs1, hs2⟩ := exists_between ((div_lt_iff₀ hq0).2 hlt)
  have hs0 : 0 < s := (div_nonneg (norm_nonneg _) hq0.le).trans_lt hs1
  obtain ⟨t, ht1, ht2⟩ := exists_between ((div_lt_iff₀' hs0).2 ((div_lt_iff₀ hq0).1 hs1))
  have ht0 : 0 < t := (div_nonneg (norm_nonneg _) hs0.le).trans_lt ht1
  have h := mul_le_norm_apply_tmul_of_nonneg Φ hΦ hp hq hs0.le hs2 ht0.le ht2
  have h' := (div_lt_iff₀' hs0).1 ht1
  linarith

end Order

/-! ### C⋆-norms are cross norms -/

section CrossNorm

variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]

/-- **A `⋆`-homomorphism of the algebraic tensor product of two C⋆-algebras into a C⋆-algebra is
bounded by the cross norm on pure tensors**: `‖Φ (a ⊗ b)‖ ≤ ‖a‖ * ‖b‖`. No injectivity is
assumed. -/
theorem norm_apply_tmul_le (Φ : A ⊗[ℂ] B →⋆ₙₐ[ℂ] C) (a : A) (b : B) :
    ‖Φ (a ⊗ₜ[ℂ] b)‖ ≤ ‖a‖ * ‖b‖ := by
  let := CStarAlgebra.spectralOrder A
  have := CStarAlgebra.spectralOrderedRing A
  let := CStarAlgebra.spectralOrder B
  have := CStarAlgebra.spectralOrderedRing B
  let := CStarAlgebra.spectralOrder C
  have := CStarAlgebra.spectralOrderedRing C
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  have ha' : ‖a‖ ≠ 0 := norm_ne_zero_iff.2 ha
  have hb' : ‖b‖ ≠ 0 := norm_ne_zero_iff.2 hb
  have h := norm_apply_tmul_le_one Φ (a := (‖a‖⁻¹ : ℂ) • a) (b := (‖b‖⁻¹ : ℂ) • b)
    (by rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ ha'])
    (by rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hb'])
  rw [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, map_smul, norm_smul,
    norm_mul, norm_inv, norm_inv, Complex.norm_real, Complex.norm_real, norm_norm, norm_norm] at h
  have hpos : 0 < ‖a‖ * ‖b‖ := mul_pos (norm_pos_iff.2 ha) (norm_pos_iff.2 hb)
  have h2 : ‖a‖⁻¹ * ‖b‖⁻¹ * ‖Φ (a ⊗ₜ[ℂ] b)‖ = ‖Φ (a ⊗ₜ[ℂ] b)‖ / (‖a‖ * ‖b‖) := by
    field_simp
  rw [h2, div_le_one hpos] at h
  exact h

/-- **A C⋆-norm on the algebraic tensor product of two C⋆-algebras is a cross norm**: for an
injective `⋆`-homomorphism `Φ` of `A ⊗[ℂ] B` into a C⋆-algebra, `‖Φ (a ⊗ b)‖ = ‖a‖ * ‖b‖`. -/
theorem norm_apply_tmul {Φ : A ⊗[ℂ] B →⋆ₙₐ[ℂ] C} (hΦ : Function.Injective Φ) (a : A) (b : B) :
    ‖Φ (a ⊗ₜ[ℂ] b)‖ = ‖a‖ * ‖b‖ := by
  refine le_antisymm (norm_apply_tmul_le Φ a b) ?_
  let := CStarAlgebra.spectralOrder A
  have := CStarAlgebra.spectralOrderedRing A
  let := CStarAlgebra.spectralOrder B
  have := CStarAlgebra.spectralOrderedRing B
  let := CStarAlgebra.spectralOrder C
  have := CStarAlgebra.spectralOrderedRing C
  have h := mul_norm_le_norm_apply_tmul_of_nonneg Φ hΦ (star_mul_self_nonneg a)
    (star_mul_self_nonneg b)
  rw [CStarRing.norm_star_mul_self, CStarRing.norm_star_mul_self,
    ← Algebra.TensorProduct.tmul_mul_tmul, ← TensorProduct.star_tmul, map_mul, map_star,
    CStarRing.norm_star_mul_self] at h
  nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg (Φ (a ⊗ₜ[ℂ] b)),
    mul_nonneg (norm_nonneg a) (norm_nonneg b)]

/-- **Dense subspaces of the factors give a dense subspace of a C⋆-tensor product**: for linear maps
`f` and `g` with dense ranges in `A` and `B`, and a `⋆`-homomorphism `Φ` of `A ⊗[ℂ] B` with dense
range, `Φ ∘ (f ⊗ g)` has dense range. The maps `a ↦ Φ (a ⊗ b)` and `b ↦ Φ (a ⊗ b)` are continuous by
the cross norm bound `NonUnitalStarAlgHom.norm_apply_tmul_le`. -/
lemma denseRange_comp_map {A₁ B₁ : Type*} [AddCommGroup A₁] [Module ℂ A₁] [AddCommGroup B₁]
    [Module ℂ B₁] (Φ : A ⊗[ℂ] B →⋆ₙₐ[ℂ] C) (hΦ : DenseRange Φ) {f : A₁ →ₗ[ℂ] A} {g : B₁ →ₗ[ℂ] B}
    (hf : DenseRange f) (hg : DenseRange g) : DenseRange fun x => Φ (TensorProduct.map f g x) := by
  let L : A₁ ⊗[ℂ] B₁ →ₗ[ℂ] C := (Φ : A ⊗[ℂ] B →ₗ[ℂ] C) ∘ₗ TensorProduct.map f g
  let K := (LinearMap.range L).topologicalClosure
  have hK : IsClosed (K : Set C) := (LinearMap.range L).isClosed_topologicalClosure
  have hcont₁ (b : B) : Continuous fun a : A => Φ (a ⊗ₜ[ℂ] b) :=
    AddMonoidHomClass.continuous_of_bound
      ((Φ : A ⊗[ℂ] B →ₗ[ℂ] C) ∘ₗ (TensorProduct.mk ℂ A B).flip b) ‖b‖ fun a => by
        simpa [mul_comm] using norm_apply_tmul_le Φ a b
  have hcont₂ (a : A) : Continuous fun b : B => Φ (a ⊗ₜ[ℂ] b) :=
    AddMonoidHomClass.continuous_of_bound
      ((Φ : A ⊗[ℂ] B →ₗ[ℂ] C) ∘ₗ TensorProduct.mk ℂ A B a) ‖a‖ fun b => by
        simpa using norm_apply_tmul_le Φ a b
  have htmul (a : A) (b : B) : Φ (a ⊗ₜ[ℂ] b) ∈ K := by
    refine hg.induction_on b (hK.preimage (hcont₂ a)) fun b₁ => ?_
    refine hf.induction_on a (hK.preimage (hcont₁ (g b₁))) fun a₁ => ?_
    exact Submodule.le_topologicalClosure _ ⟨a₁ ⊗ₜ[ℂ] b₁, by simp [L]⟩
  have hall (x : A ⊗[ℂ] B) : Φ x ∈ K := by
    induction x using TensorProduct.inductionOn with
    | tmul a b => exact htmul a b
    | add x x' hx hx' => rw [map_add]; exact K.add_mem hx hx'
  refine Dense.of_closure (hΦ.mono ?_)
  rintro _ ⟨x, rfl⟩
  exact hall x

end CrossNorm

/-! ### Extending a functional to a positive functional -/

section Extension

variable [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

/-- A complex number in the closed unit discs about `0` and about `2` is `1`. -/
private lemma eq_one_of_norm_le_one_of_norm_sub_two_le_one {c : ℂ} (h1 : ‖c‖ ≤ 1)
    (h2 : ‖c - 2‖ ≤ 1) : c = 1 := by
  have hre1 : c.re ≤ 1 := (Complex.re_le_norm c).trans h1
  have hre2 : 1 ≤ c.re := by
    have h := (Complex.re_le_norm (2 - c)).trans ((norm_sub_rev 2 c).le.trans h2)
    rw [Complex.sub_re, Complex.re_ofNat] at h
    linarith
  have hre : c.re = 1 := le_antisymm hre1 hre2
  have him : c.im = 0 := by
    have h := Complex.sq_norm c
    rw [Complex.normSq_apply, hre] at h
    nlinarith [norm_nonneg c]
  exact Complex.ext hre him

/-- For a positive contraction `y` of a unital C⋆-algebra, `1 - 2 y` is a contraction: its square
is `1 - 4 (y - y²) ≤ 1`. -/
private lemma norm_one_sub_add_self_le {U : Type*} [CStarAlgebra U] [PartialOrder U]
    [StarOrderedRing U] {y : U} (hy : 0 ≤ y) (hyn : ‖y‖ ≤ 1) : ‖1 - (y + y)‖ ≤ 1 := by
  have hysa : IsSelfAdjoint y := IsSelfAdjoint.of_nonneg hy
  have hsa : IsSelfAdjoint (1 - (y + y)) := (IsSelfAdjoint.one U).sub (hysa.add hysa)
  have hyy : 0 ≤ y - y * y := sub_nonneg.2 (mul_self_le_self hy hyn)
  have hzz : (1 - (y + y)) * (1 - (y + y)) ≤ 1 := by
    rw [← sub_nonneg]
    have e : (1 : U) - (1 - (y + y)) * (1 - (y + y)) =
        (y - y * y) + (y - y * y) + (y - y * y) + (y - y * y) := by noncomm_ring
    rw [e]
    exact add_nonneg (add_nonneg (add_nonneg hyy hyy) hyy) hyy
  have h0 : 0 ≤ (1 - (y + y)) * (1 - (y + y)) := by
    have h := star_mul_self_nonneg (1 - (y + y))
    rwa [hsa.star_eq] at h
  have hn : ‖1 - (y + y)‖ ^ 2 ≤ 1 := by
    rw [← hsa.norm_mul_self]
    exact (CStarAlgebra.norm_le_one_iff_of_nonneg _ h0).2 hzz
  by_contra hlt
  push Not at hlt
  nlinarith [norm_nonneg (1 - (y + y))]

/-- **A functional on the range of a linear map into a C⋆-algebra `C` that is bounded by the norm
of `C` and tends to `1` along positive contractions extends to a positive functional of norm at
most one.** A Hahn–Banach extension to the unitization of `C` has norm at most `1` and the value `1`
at `1`, since `‖1 - 2 e‖ ≤ 1` for a positive contraction `e`; so it is positive. -/
private lemma exists_positive_extension {E ι : Type*} [AddCommGroup E] [Module ℂ E]
    (L : E →ₗ[ℂ] C) (lam : E →ₗ[ℂ] ℂ) (hbound : ∀ z, ‖lam z‖ ≤ ‖L z‖)
    {l : Filter ι} [l.NeBot] (e : ι → E) (he : ∀ᶠ i in l, 0 ≤ L (e i) ∧ ‖L (e i)‖ ≤ 1)
    (hlim : Tendsto (fun i => lam (e i)) l (𝓝 1)) :
    ∃ Ω : C →L[ℂ] ℂ, ‖Ω‖ ≤ 1 ∧ (∀ d, 0 ≤ d → 0 ≤ Ω d) ∧ ∀ z, Ω (L z) = lam z := by
  let inrL : C →ₗ[ℂ] Unitization ℂ C :=
    { toFun := Unitization.inr
      map_add' := map_add (Unitization.inrNonUnitalStarAlgHom ℂ C)
      map_smul' := map_smul (Unitization.inrNonUnitalStarAlgHom ℂ C) }
  have hinr (d : C) : ‖inrL d‖ = ‖d‖ := Unitization.norm_inr d
  let inrCLM : C →L[ℂ] Unitization ℂ C := inrL.mkContinuous 1 fun d => by rw [one_mul, hinr]
  let L' : E →ₗ[ℂ] Unitization ℂ C := inrL ∘ₗ L
  have hker : LinearMap.ker L' ≤ LinearMap.ker lam := fun z hz => by
    rw [LinearMap.mem_ker] at hz ⊢
    have h0 : ‖L z‖ = 0 := by rw [← hinr, show inrL (L z) = L' z from rfl, hz, norm_zero]
    exact norm_le_zero_iff.1 ((hbound z).trans h0.le)
  let f₀ : LinearMap.range L' →ₗ[ℂ] ℂ :=
    (LinearMap.ker L').liftQ lam hker ∘ₗ
      (L'.quotKerEquivRange.symm : LinearMap.range L' →ₗ[ℂ] E ⧸ LinearMap.ker L')
  have hf₀ (z : E) : f₀ ⟨L' z, LinearMap.mem_range_self L' z⟩ = lam z := by
    change (LinearMap.ker L').liftQ lam hker
      (L'.quotKerEquivRange.symm ⟨L' z, LinearMap.mem_range_self L' z⟩) = lam z
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  let f : LinearMap.range L' →L[ℂ] ℂ := f₀.mkContinuous 1 fun v => by
    obtain ⟨z, hz⟩ := v.2
    have hv : v = ⟨L' z, LinearMap.mem_range_self L' z⟩ := Subtype.ext hz.symm
    rw [hv, hf₀, one_mul]
    exact (hbound z).trans_eq (hinr (L z)).symm
  have hfn : ‖f‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _
  obtain ⟨g, hg, hgn⟩ := exists_extension_norm_eq (LinearMap.range L') f
  have hgL (z : E) : g (inrL (L z)) = lam z :=
    (hg ⟨L' z, LinearMap.mem_range_self L' z⟩).trans (hf₀ z)
  have hgn1 : ‖g‖ ≤ 1 := hgn.le.trans hfn
  have hg1 : g 1 = 1 := by
    refine eq_one_of_norm_le_one_of_norm_sub_two_le_one ?_ ?_
    · calc ‖g 1‖ ≤ ‖g‖ * ‖(1 : Unitization ℂ C)‖ := g.le_opNorm 1
        _ ≤ 1 := by rw [norm_one, mul_one]; exact hgn1
    · have hev : ∀ᶠ i in l, ‖g 1 - 2 * lam (e i)‖ ≤ 1 := he.mono fun i hi => by
        have hy : 0 ≤ inrL (L (e i)) := Unitization.inr_nonneg_iff.2 hi.1
        have hn := norm_one_sub_add_self_le hy (by rw [hinr]; exact hi.2)
        have hval : g (1 - (inrL (L (e i)) + inrL (L (e i)))) = g 1 - 2 * lam (e i) := by
          rw [map_sub, map_add, hgL]
          ring
        rw [← hval]
        calc ‖g (1 - (inrL (L (e i)) + inrL (L (e i))))‖
            ≤ ‖g‖ * ‖1 - (inrL (L (e i)) + inrL (L (e i)))‖ := g.le_opNorm _
          _ ≤ 1 * 1 := mul_le_mul hgn1 hn (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      have hten : Tendsto (fun i => ‖g 1 - 2 * lam (e i)‖) l (𝓝 ‖g 1 - 2‖) := by
        have h := ((hlim.const_mul 2).const_sub (g 1)).norm
        rwa [mul_one] at h
      exact le_of_tendsto hten hev
  have hgnorm : ‖g‖ = 1 := le_antisymm hgn1 (by
    have h := g.le_opNorm 1
    rwa [hg1, norm_one, norm_one, mul_one] at h)
  have hgpos : ∀ x : Unitization ℂ C, 0 ≤ x → 0 ≤ g x :=
    nonneg_of_norm_eq_one_map_one (StrongDual.toWeakDual g) hgnorm hg1
  refine ⟨g.comp inrCLM, ?_, fun d hd => hgpos _ (Unitization.inr_nonneg_iff.2 hd), hgL⟩
  calc ‖g.comp inrCLM‖ ≤ ‖g‖ * ‖inrCLM‖ := g.opNorm_comp_le _
    _ ≤ 1 * 1 :=
      mul_le_mul hgn1 (LinearMap.mkContinuous_norm_le _ zero_le_one _) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- **A positive functional of norm at most one is concentrated where a positive contraction `G`
has the value one**: `‖Ω d - Ω (G d G)‖ ≤ 2 ‖d‖ √(1 - Ω G)`. In the GNS representation of `Ω`, with
cyclic vector `ξ`, `‖ξ - π(G) ξ‖² ≤ 1 - Ω G`. -/
private lemma norm_apply_sub_apply_mul_mul_le (Ω : C →L[ℂ] ℂ) (hΩ : ‖Ω‖ ≤ 1)
    (hpos : ∀ d, 0 ≤ d → 0 ≤ Ω d) {G : C} (hG : 0 ≤ G) (hGn : ‖G‖ ≤ 1) (d : C) :
    ‖Ω d - Ω (G * d * G)‖ ≤ 2 * ‖d‖ * √(1 - (Ω G).re) := by
  let f : C →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ Ω.toLinearMap hpos
  let T := GNS.Representation.canonical f
  have hf (c : C) : Ω c = ⟪T.ξ, T.π c T.ξ⟫_ℂ := T.gns_condition c
  have hξsq : ‖T.ξ‖ ^ 2 ≤ 1 := by
    rw [T.norm_ξ_sq, PositiveLinearMap.opNorm_def]
    exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun c =>
      (Ω.le_opNorm c).trans (mul_le_mul_of_nonneg_right hΩ (norm_nonneg c))
  have hξ : ‖T.ξ‖ ≤ 1 := by
    by_contra hlt
    push Not at hlt
    nlinarith [norm_nonneg T.ξ]
  have hGsa : star G = G := (IsSelfAdjoint.of_nonneg hG).star_eq
  have hπ (c : C) : ‖T.π c‖ ≤ ‖c‖ := NonUnitalStarAlgHom.norm_apply_le T.π c
  have hηn : ‖T.π G T.ξ‖ ≤ 1 :=
    ((T.π G).le_opNorm _).trans
      ((mul_le_mul ((hπ G).trans hGn) hξ (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
  have hηsq : ‖T.π G T.ξ‖ ^ 2 ≤ (Ω G).re := by
    rw [T.norm_apply_cyclic G, Real.sq_sqrt (norm_nonneg _), hGsa]
    have h2 : 0 ≤ Ω (G * G) := hpos _ (mul_self_nonneg_of_nonneg hG)
    have h3 : Ω (G * G) ≤ Ω G := by
      rw [← sub_nonneg, ← map_sub]
      exact hpos _ (sub_nonneg.2 (mul_self_le_self hG hGn))
    change ‖Ω (G * G)‖ ≤ _
    rw [← Complex.re_eq_norm.mpr h2]
    exact (Complex.le_def.1 h3).1
  have hdist : ‖T.ξ - T.π G T.ξ‖ ≤ √(1 - (Ω G).re) := by
    rw [← Real.sqrt_sq (norm_nonneg (T.ξ - T.π G T.ξ))]
    refine Real.sqrt_le_sqrt ?_
    rw [@norm_sub_sq ℂ, ← hf G]
    change ‖T.ξ‖ ^ 2 - 2 * (Ω G).re + ‖T.π G T.ξ‖ ^ 2 ≤ 1 - (Ω G).re
    linarith
  have hval : Ω (G * d * G) = ⟪T.π G T.ξ, T.π d (T.π G T.ξ)⟫_ℂ := by
    rw [hf, map_mul, map_mul]
    refine (ContinuousLinearMap.adjoint_inner_left (T.π G) (T.π d (T.π G T.ξ)) T.ξ).symm.trans ?_
    rw [T.adjoint_π, hGsa]
  have hsplit : Ω d - Ω (G * d * G) = ⟪T.ξ - T.π G T.ξ, T.π d T.ξ⟫_ℂ +
      ⟪T.π G T.ξ, T.π d (T.ξ - T.π G T.ξ)⟫_ℂ := by
    rw [hf d, hval, inner_sub_left, map_sub, inner_sub_right]
    ring
  rw [hsplit]
  calc ‖⟪T.ξ - T.π G T.ξ, T.π d T.ξ⟫_ℂ + ⟪T.π G T.ξ, T.π d (T.ξ - T.π G T.ξ)⟫_ℂ‖
      ≤ ‖⟪T.ξ - T.π G T.ξ, T.π d T.ξ⟫_ℂ‖ + ‖⟪T.π G T.ξ, T.π d (T.ξ - T.π G T.ξ)⟫_ℂ‖ :=
        norm_add_le _ _
    _ ≤ ‖T.ξ - T.π G T.ξ‖ * (‖d‖ * 1) + 1 * (‖d‖ * ‖T.ξ - T.π G T.ξ‖) := by
      refine add_le_add ((norm_inner_le_norm _ _).trans ?_) ((norm_inner_le_norm _ _).trans ?_)
      · exact mul_le_mul_of_nonneg_left (((T.π d).le_opNorm _).trans
          (mul_le_mul (hπ d) hξ (norm_nonneg _) (norm_nonneg _))) (norm_nonneg _)
      · exact mul_le_mul hηn (((T.π d).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hπ d) (norm_nonneg _))) (norm_nonneg _) zero_le_one
    _ = 2 * ‖d‖ * ‖T.ξ - T.π G T.ξ‖ := by ring
    _ ≤ 2 * ‖d‖ * √(1 - (Ω G).re) :=
      mul_le_mul_of_nonneg_left hdist (mul_nonneg zero_le_two (norm_nonneg d))

end Extension

/-! ### Slices along a pure state

For a pure state `ψ` of `B` and an injective `Φ`, the slice map `id ⊗ ψ : A ⊗[ℂ] B → A` is a
contraction for the norm `x ↦ ‖Φ x‖`. Given a positive `a` of norm one, the functional
`Φ (a ⊗ b) ↦ ψ b` is bounded by the cross norm, and extends to a positive functional `Ω` of norm at
most one. As `Ω` is concentrated where `Φ (a ⊗ u)` is one, `b ↦ Ω (Φ (a' ⊗ b))` is dominated by `ψ`
for a positive contraction `a'`, hence a multiple of `ψ`: `Ω ∘ Φ = φ ⊗ ψ` for a functional `φ` with
`φ a = 1`. Taking `a = r⋆ r / ‖r‖²` for `r = (id ⊗ ψ)(x)` gives `‖r‖ ≤ ‖Φ x‖`. -/

section Slice

open scoped GNS

open UniformSpace

variable [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  {Φ : A ⊗[ℂ] B →⋆ₙₐ[ℂ] C}

/-- If a positive functional `Ω` of norm at most one has `Ω (Φ (a ⊗ b)) = ψ b` for a positive
contraction `a` and a state `ψ`, then `Ω (Φ (a' ⊗ b)) ≤ ψ b` for positive contractions `a'` and
positive `b`. -/
private lemma apply_tmul_le_of_apply_tmul_eq {ψ : State B} {a : A} (ha : 0 ≤ a) (han : ‖a‖ ≤ 1)
    {Ω : C →L[ℂ] ℂ} (hΩn : ‖Ω‖ ≤ 1) (hΩpos : ∀ d, 0 ≤ d → 0 ≤ Ω d)
    (hΩa : ∀ b, Ω (Φ (a ⊗ₜ[ℂ] b)) = ψ b) {a' : A} (ha' : 0 ≤ a') (ha'n : ‖a'‖ ≤ 1) {b : B}
    (hb : 0 ≤ b) : Ω (Φ (a' ⊗ₜ[ℂ] b)) ≤ ψ b := by
  have hl := CStarAlgebra.increasingApproximateUnit B
  have hlim : Tendsto (fun u : B => ψ u) (CStarAlgebra.approximateUnit B) (𝓝 1) :=
    ψ.tendsto_approximateUnit hl
  have h0 : 0 ≤ Ω (Φ (a' ⊗ₜ[ℂ] b)) := hΩpos _ (apply_tmul_nonneg Φ ha' hb)
  have h1 : 0 ≤ ψ b := ψ.apply_nonneg hb
  refine Complex.le_def.2 ⟨?_, ?_⟩
  swap
  · rw [← (Complex.nonneg_iff.1 h0).2, ← (Complex.nonneg_iff.1 h1).2]
  have hasa : star a = a := (IsSelfAdjoint.of_nonneg ha).star_eq
  have haa : a * a' * a ≤ a := by
    have h := CStarAlgebra.star_left_conjugate_le_norm_smul a a' (IsSelfAdjoint.of_nonneg ha')
    rw [hasa] at h
    refine h.trans ((smul_le_smul_of_nonneg_right ha'n (mul_self_nonneg_of_nonneg ha)).trans ?_)
    rw [one_smul]
    exact mul_self_le_self ha han
  have hev : ∀ᶠ u in CStarAlgebra.approximateUnit B, (Ω (Φ (a' ⊗ₜ[ℂ] b))).re ≤
      (ψ b).re + (2 * ‖Φ (a' ⊗ₜ[ℂ] b)‖ + 2 * ‖b‖) * √(1 - (ψ u).re) := by
    filter_upwards [hl.eventually_nonneg, hl.eventually_norm] with u hu hun
    have husa : star u = u := (IsSelfAdjoint.of_nonneg hu).star_eq
    have hG : 0 ≤ Φ (a ⊗ₜ[ℂ] u) := apply_tmul_nonneg Φ ha hu
    have hGn : ‖Φ (a ⊗ₜ[ℂ] u)‖ ≤ 1 :=
      (norm_apply_tmul_le Φ a u).trans
        ((mul_le_mul han hun (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
    have c1 := norm_apply_sub_apply_mul_mul_le Ω hΩn hΩpos hG hGn (Φ (a' ⊗ₜ[ℂ] b))
    rw [hΩa u] at c1
    have c2 : ‖ψ b - ψ (u * b * u)‖ ≤ 2 * ‖b‖ * √(1 - (ψ u).re) :=
      norm_apply_sub_apply_mul_mul_le (WeakDual.toStrongDual ψ.val) ψ.norm_eq_one.le
        (fun b hb => ψ.apply_nonneg hb) hu hun b
    have hubu : 0 ≤ u * b * u := by
      have h := star_left_conjugate_nonneg hb u
      rwa [husa] at h
    have hGdG : Φ (a ⊗ₜ[ℂ] u) * Φ (a' ⊗ₜ[ℂ] b) * Φ (a ⊗ₜ[ℂ] u) =
        Φ ((a * a' * a) ⊗ₜ[ℂ] (u * b * u)) := by
      rw [← map_mul, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul]
    have hle : Ω (Φ (a ⊗ₜ[ℂ] u) * Φ (a' ⊗ₜ[ℂ] b) * Φ (a ⊗ₜ[ℂ] u)) ≤ ψ (u * b * u) := by
      rw [hGdG, ← hΩa, ← sub_nonneg, ← map_sub]
      exact hΩpos _ (sub_nonneg.2 (apply_tmul_mono_left Φ haa hubu))
    have hre := (Complex.le_def.1 hle).1
    have r1 := Complex.re_le_norm
      (Ω (Φ (a' ⊗ₜ[ℂ] b)) - Ω (Φ (a ⊗ₜ[ℂ] u) * Φ (a' ⊗ₜ[ℂ] b) * Φ (a ⊗ₜ[ℂ] u)))
    have r2 := Complex.re_le_norm (ψ (u * b * u) - ψ b)
    rw [Complex.sub_re] at r1 r2
    rw [norm_sub_rev] at r2
    linarith
  have hten : Tendsto (fun u : B => (ψ b).re +
      (2 * ‖Φ (a' ⊗ₜ[ℂ] b)‖ + 2 * ‖b‖) * √(1 - (ψ u).re)) (CStarAlgebra.approximateUnit B)
      (𝓝 (ψ b).re) := by
    have h := (((((Complex.continuous_re.tendsto 1).comp hlim).const_sub 1).sqrt).const_mul
      (2 * ‖Φ (a' ⊗ₜ[ℂ] b)‖ + 2 * ‖b‖)).const_add (ψ b).re
    simpa using h
  exact ge_of_tendsto hten hev

/-- For a pure state `ψ` of `B`, an injective `Φ` and a positive `a` of norm one, there are a
functional `Ω` of norm at most one on `C` and a functional `φ` on `A` with
`Ω (Φ (a' ⊗ b)) = φ a' * ψ b` and `φ a = 1`. -/
private lemma exists_apply_tmul_eq_mul (hΦ : Function.Injective Φ) {ψ : State B} (hψ : ψ.IsPure)
    {a : A} (ha : 0 ≤ a) (han : ‖a‖ = 1) :
    ∃ (Ω : C →L[ℂ] ℂ) (φ : A →L[ℂ] ℂ), ‖Ω‖ ≤ 1 ∧
      (∀ (a' : A) (b : B), Ω (Φ (a' ⊗ₜ[ℂ] b)) = φ a' * ψ b) ∧ φ a = 1 := by
  have hl := CStarAlgebra.increasingApproximateUnit B
  have hlim : Tendsto (fun u : B => ψ u) (CStarAlgebra.approximateUnit B) (𝓝 1) :=
    ψ.tendsto_approximateUnit hl
  obtain ⟨Ω, hΩn, hΩpos, hΩa⟩ := exists_positive_extension
    ((Φ : A ⊗[ℂ] B →ₗ[ℂ] C) ∘ₗ TensorProduct.mk ℂ A B a) (ψ : B →ₗ[ℂ] ℂ)
    (fun b => by
      change ‖ψ b‖ ≤ ‖Φ (a ⊗ₜ[ℂ] b)‖
      rw [norm_apply_tmul hΦ, han, one_mul]
      exact ψ.norm_apply_le b)
    (l := CStarAlgebra.approximateUnit B) id
    ((hl.eventually_nonneg.and hl.eventually_norm).mono fun u hu =>
      ⟨apply_tmul_nonneg Φ ha hu.1,
        (norm_apply_tmul_le Φ a u).trans (by rw [han, one_mul]; exact hu.2)⟩)
    hlim
  have hΩa' (b : B) : Ω (Φ (a ⊗ₜ[ℂ] b)) = ψ b := hΩa b
  obtain ⟨b₀, hb₀⟩ := (hlim.eventually_ne one_ne_zero).exists
  let Lb : A →L[ℂ] C :=
    ((Φ : A ⊗[ℂ] B →ₗ[ℂ] C) ∘ₗ (TensorProduct.mk ℂ A B).flip b₀).mkContinuous ‖b₀‖ fun a' => by
      rw [mul_comm]
      exact norm_apply_tmul_le Φ a' b₀
  let La (a' : A) : B →L[ℂ] C :=
    ((Φ : A ⊗[ℂ] B →ₗ[ℂ] C) ∘ₗ TensorProduct.mk ℂ A B a').mkContinuous ‖a'‖
      fun b => norm_apply_tmul_le Φ a' b
  let φ : A →L[ℂ] ℂ := (ψ b₀)⁻¹ • Ω.comp Lb
  have hφ (a' : A) : φ a' = (ψ b₀)⁻¹ * Ω (Φ (a' ⊗ₜ[ℂ] b₀)) := rfl
  have hunit (a' : A) (ha' : 0 ≤ a') (ha'n : ‖a'‖ ≤ 1) (b : B) :
      Ω (Φ (a' ⊗ₜ[ℂ] b)) = φ a' * ψ b := by
    obtain ⟨t, -, -, ht⟩ := hψ.exists_eq_smul_of_le (φ := StrongDual.toWeakDual (Ω.comp (La a')))
      (fun b hb => hΩpos _ (apply_tmul_nonneg Φ ha' hb))
      (fun b hb => apply_tmul_le_of_apply_tmul_eq ha han.le hΩn hΩpos hΩa' ha' ha'n hb)
    have ht' (b : B) : Ω (Φ (a' ⊗ₜ[ℂ] b)) = (t : ℂ) * ψ b := DFunLike.congr_fun ht b
    rw [hφ, ht' b₀, ht' b]
    field_simp
  let S : Submodule ℂ A :=
    { carrier := {a' | ∀ b, Ω (Φ (a' ⊗ₜ[ℂ] b)) = φ a' * ψ b}
      add_mem' := fun {x y} hx hy b => by
        rw [TensorProduct.add_tmul, map_add, map_add, hx b, hy b, map_add, add_mul]
      zero_mem' := fun b => by
        rw [TensorProduct.zero_tmul, map_zero, map_zero, map_zero, zero_mul]
      smul_mem' := fun c x hx b => by
        rw [← TensorProduct.smul_tmul', map_smul, map_smul, hx b, map_smul, smul_eq_mul,
          smul_eq_mul, mul_assoc] }
  have hS : S = ⊤ := by
    rw [eq_top_iff, ← CStarAlgebra.span_nonneg_inter_unitClosedBall, Submodule.span_le]
    rintro a' ⟨ha', ha'n⟩
    exact hunit a' ha' (mem_closedBall_zero_iff.1 ha'n)
  refine ⟨Ω, φ, hΩn, fun a' b => (hS ▸ Submodule.mem_top : a' ∈ S) b, ?_⟩
  rw [hφ, hΩa', inv_mul_cancel₀ hb₀]

/-- **For a pure state `ψ` of `B`, the slice map `id ⊗ ψ : A ⊗[ℂ] B → A` is a contraction for
every C⋆-norm on `A ⊗[ℂ] B`**: `‖(id ⊗ ψ)(x)‖ ≤ ‖Φ x‖` for an injective `Φ`. -/
private lemma norm_rid_lTensor_le (hΦ : Function.Injective Φ) {ψ : State B} (hψ : ψ.IsPure)
    (x : A ⊗[ℂ] B) :
    ‖TensorProduct.rid ℂ A ((ψ : B →ₗ[ℂ] ℂ).lTensor A x)‖ ≤ ‖Φ x‖ := by
  let R : A ⊗[ℂ] B →ₗ[ℂ] A :=
    (TensorProduct.rid ℂ A).toLinearMap ∘ₗ (ψ : B →ₗ[ℂ] ℂ).lTensor A
  have hRt (a' : A) (b : B) : R (a' ⊗ₜ[ℂ] b) = ψ b • a' := by simp [R]
  change ‖R x‖ ≤ ‖Φ x‖
  by_cases hr : R x = 0
  · rw [hr, norm_zero]
    exact norm_nonneg _
  have hrn : ‖R x‖ ≠ 0 := norm_ne_zero_iff.2 hr
  obtain ⟨r', hr'n, hrr'⟩ : ∃ r' : A, ‖r'‖ = 1 ∧ R x = (‖R x‖ : ℂ) • r' := by
    refine ⟨((‖R x‖⁻¹ : ℝ) : ℂ) • R x, ?_, ?_⟩
    · rw [norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hrn]
    · rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hrn, Complex.ofReal_one, one_smul]
  obtain ⟨Ω, φ, hΩn, hΩφ, hφ1⟩ := exists_apply_tmul_eq_mul hΦ hψ (star_mul_self_nonneg r')
    (by rw [CStarRing.norm_star_mul_self, hr'n, mul_one])
  have hΩR (y : A ⊗[ℂ] B) : Ω (Φ y) = φ (R y) := by
    induction y using TensorProduct.inductionOn with
    | tmul a' b => rw [hΩφ, hRt, map_smul, smul_eq_mul, mul_comm]
    | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  have hl := CStarAlgebra.increasingApproximateUnit B
  have hten (y : A ⊗[ℂ] B) : Tendsto (fun u : B => R ((star r' ⊗ₜ[ℂ] u) * y))
      (CStarAlgebra.approximateUnit B) (𝓝 (star r' * R y)) := by
    induction y using TensorProduct.inductionOn with
    | tmul a' b =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, hRt, mul_smul_comm]
      exact ((ψ.continuous.tendsto b).comp (hl.tendsto_mul_right b)).smul_const (star r' * a')
    | add p q hp hq =>
      simp only [mul_add, map_add]
      exact hp.add hq
  have hev : ∀ᶠ u in CStarAlgebra.approximateUnit B,
      ‖φ (R ((star r' ⊗ₜ[ℂ] u) * x))‖ ≤ ‖Φ x‖ := by
    filter_upwards [hl.eventually_norm] with u hu
    rw [← hΩR, map_mul]
    calc ‖Ω (Φ (star r' ⊗ₜ[ℂ] u) * Φ x)‖ ≤ ‖Ω‖ * ‖Φ (star r' ⊗ₜ[ℂ] u) * Φ x‖ := Ω.le_opNorm _
      _ ≤ 1 * (1 * ‖Φ x‖) := by
        refine mul_le_mul hΩn ((norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))) (norm_nonneg _) zero_le_one
        exact (norm_apply_tmul_le Φ _ u).trans (by rw [norm_star, hr'n, one_mul]; exact hu)
      _ = ‖Φ x‖ := by rw [one_mul, one_mul]
  have hlim := le_of_tendsto (((φ.continuous.tendsto _).comp (hten x)).norm) hev
  rw [hrr', mul_smul_comm, map_smul, hφ1, smul_eq_mul, mul_one, Complex.norm_real,
    norm_norm] at hlim
  exact hlim

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
/-- A representation `P` of `A ⊗[ℂ] B` with a cyclic vector `v` whose vector functional is `Ω ∘ Φ`
for a positive functional `Ω` on `C` is bounded by the norm `x ↦ ‖Φ x‖`:
`‖P (x y) v‖² = Ω (Φ(y)⋆ Φ(x⋆ x) Φ(y)) ≤ ‖Φ x‖² Ω (Φ(y)⋆ Φ(y)) = ‖Φ x‖² ‖P y v‖²`. -/
private lemma norm_apply_le_of_apply_eq_inner {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (P : A ⊗[ℂ] B →⋆ₙₐ[ℂ] (K →L[ℂ] K)) {v : K}
    (hdense : DenseRange fun y : A ⊗[ℂ] B => P y v) {Ω : C →L[ℂ] ℂ}
    (hΩpos : ∀ d, 0 ≤ d → 0 ≤ Ω d) (hΩ : ∀ z, Ω (Φ z) = ⟪v, P z v⟫_ℂ) (x : A ⊗[ℂ] B) :
    ‖P x‖ ≤ ‖Φ x‖ := by
  have hPP (z : A ⊗[ℂ] B) : P (star z * z) v = ((P z)†) (P z v) :=
    congrArg (fun T : K →L[ℂ] K => T v)
      ((map_mul P (star z) z).trans (congrArg (· * P z) (map_star P z)))
  have hsq (z : A ⊗[ℂ] B) : Ω (Φ (star z * z)) = ((‖P z v‖ ^ 2 : ℝ) : ℂ) := by
    rw [hΩ, hPP, ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  have hkey (y : A ⊗[ℂ] B) : ‖P x (P y v)‖ ≤ ‖Φ x‖ * ‖P y v‖ := by
    have h := CStarAlgebra.star_left_conjugate_le_norm_smul (Φ y) (Φ (star x * x))
      (by rw [map_mul, map_star]; exact IsSelfAdjoint.star_mul_self _)
    have h' := hΩpos _ (sub_nonneg.2 h)
    have e1 : star (Φ y) * Φ (star x * x) * Φ y = Φ (star (x * y) * (x * y)) := by
      simp only [map_mul, map_star, star_mul, mul_assoc]
    have e2 : ‖Φ (star x * x)‖ = ‖Φ x‖ ^ 2 := by
      rw [map_mul, map_star, CStarRing.norm_star_mul_self, sq]
    have e3 : P (x * y) v = P x (P y v) :=
      congrArg (fun T : K →L[ℂ] K => T v) (map_mul P x y)
    rw [map_sub, sub_nonneg, e1, e2, ← Complex.coe_smul, map_smul, smul_eq_mul, ← map_star,
      ← map_mul, hsq, hsq, ← Complex.ofReal_mul, Complex.real_le_real, e3] at h'
    have h2 : ‖P x (P y v)‖ ^ 2 ≤ (‖Φ x‖ * ‖P y v‖) ^ 2 := by
      rw [mul_pow]
      exact h'
    exact (abs_le_of_sq_le_sq' h2 (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun w => ?_
  exact hdense.induction_on w
    (isClosed_le (P x).continuous.norm (continuous_const.mul continuous_norm)) hkey

/-- For a state `ω` of `A`, a pure state `ψ` of `B` and an injective `Φ`, the tensor product of the
GNS representations of `ω` and `ψ` is bounded by the norm `x ↦ ‖Φ x‖`: the product functional
`ω ⊗ ψ`, the vector functional of `ξ_ω ⊗ ξ_ψ`, is `ω ∘ (id ⊗ ψ)`, which is bounded by `‖Φ x‖`, so
it extends to a positive functional on `C`. -/
private lemma norm_spatial_gns_le (hΦ : Function.Injective Φ) (ω : State A) {ψ : State B}
    (hψ : ψ.IsPure) (x : A ⊗[ℂ] B) :
    ‖(GNS[ω].toCStarRep).spatial (GNS[ψ].toCStarRep) x‖ ≤ ‖Φ x‖ := by
  let R : A ⊗[ℂ] B →ₗ[ℂ] A :=
    (TensorProduct.rid ℂ A).toLinearMap ∘ₗ (ψ : B →ₗ[ℂ] ℂ).lTensor A
  have hRt (a' : A) (b : B) : R (a' ⊗ₜ[ℂ] b) = ψ b • a' := by simp [R]
  let Λ : A ⊗[ℂ] B →ₗ[ℂ] ℂ := (ω : A →ₗ[ℂ] ℂ) ∘ₗ R
  have hΛt (a : A) (b : B) : Λ (a ⊗ₜ[ℂ] b) = ω a * ψ b := by
    change ω (R (a ⊗ₜ[ℂ] b)) = _
    rw [hRt, map_smul, smul_eq_mul, mul_comm]
  have hlA := CStarAlgebra.increasingApproximateUnit A
  have hlB := CStarAlgebra.increasingApproximateUnit B
  obtain ⟨Ω, hΩn, hΩpos, hΩΦ⟩ := exists_positive_extension (Φ : A ⊗[ℂ] B →ₗ[ℂ] C) Λ
    (fun z => (ω.norm_apply_le _).trans (norm_rid_lTensor_le hΦ hψ z))
    (l := CStarAlgebra.approximateUnit A ×ˢ CStarAlgebra.approximateUnit B)
    (fun p => p.1 ⊗ₜ[ℂ] p.2)
    (((hlA.eventually_nonneg.and hlA.eventually_norm).prod_mk
      (hlB.eventually_nonneg.and hlB.eventually_norm)).mono fun p hp =>
        ⟨apply_tmul_nonneg Φ hp.1.1 hp.2.1, (norm_apply_tmul_le Φ p.1 p.2).trans
          ((mul_le_mul hp.1.2 hp.2.2 (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))⟩)
    (by
      have h := ((ω.tendsto_approximateUnit hlA).comp tendsto_fst).mul
        ((ψ.tendsto_approximateUnit hlB).comp tendsto_snd)
      rw [one_mul] at h
      exact h.congr fun p => (hΛt p.1 p.2).symm)
  have hΛ : Λ = (innerSL ℂ ((GNS[ω].ξ ⊗ₜ[ℂ] GNS[ψ].ξ : GNS[ω].H ⊗[ℂ] GNS[ψ].H) :
      Completion (GNS[ω].H ⊗[ℂ] GNS[ψ].H)) : Completion (GNS[ω].H ⊗[ℂ] GNS[ψ].H) →L[ℂ] ℂ).toLinearMap ∘ₗ
      (ContinuousLinearMap.apply ℂ (Completion (GNS[ω].H ⊗[ℂ] GNS[ψ].H))
        ((GNS[ω].ξ ⊗ₜ[ℂ] GNS[ψ].ξ : GNS[ω].H ⊗[ℂ] GNS[ψ].H) :
          Completion (GNS[ω].H ⊗[ℂ] GNS[ψ].H))).toLinearMap ∘ₗ
        ((GNS[ω].toCStarRep).spatial (GNS[ψ].toCStarRep) : A ⊗[ℂ] B →ₗ[ℂ] _) :=
    TensorProduct.ext' fun a b => (hΛt a b).trans
      ((congrArg₂ (· * ·) (GNS[ω].gns_condition a) (GNS[ψ].gns_condition b)).trans
        (CStarRep.inner_tmul_spatial_tmul_apply_tmul _ _ a b _ _).symm)
  exact norm_apply_le_of_apply_eq_inner _
    (CStarRep.denseRange_spatial_apply_tmul _ _ GNS[ω].denseRange_orbit GNS[ψ].denseRange_orbit)
    hΩpos (fun z => (hΩΦ z).trans (LinearMap.congr_fun hΛ z)) x

end Slice

end NonUnitalStarAlgHom

/-! ### The minimal norm is the least C⋆-norm -/

namespace MinTensorProduct

variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]

/-- **The norm of the minimal tensor product is the least C⋆-norm on the algebraic tensor
product**: for an injective `⋆`-homomorphism `Φ` of `A ⊗[ℂ] B` into a C⋆-algebra, the
norm of `x` in `A ⊗ₘᵢₙ B` is at most `‖Φ x‖`. The minimal norm is computed in the tensor products of
the GNS representations of the pure states of `A` and of `B`
(`CStarRep.norm_spatial_le_of_forall`), each of which is bounded by `‖Φ x‖`. -/
theorem norm_of_le_norm_apply {Φ : A ⊗[ℂ] B →⋆ₙₐ[ℂ] C} (hΦ : Function.Injective Φ)
    (x : A ⊗[ℂ] B) : ‖of A B x‖ ≤ ‖Φ x‖ := by
  let := CStarAlgebra.spectralOrder A
  have := CStarAlgebra.spectralOrderedRing A
  let := CStarAlgebra.spectralOrder B
  have := CStarAlgebra.spectralOrderedRing B
  let := CStarAlgebra.spectralOrder C
  have := CStarAlgebra.spectralOrderedRing C
  rw [norm_of]
  exact CStarRep.norm_spatial_le_of_forall (GNS.DirectSum.pureStateFamily_separatesPoints A)
    (GNS.DirectSum.pureStateFamily_separatesPoints B) _ _ (norm_nonneg _)
    fun ω ψ => NonUnitalStarAlgHom.norm_spatial_gns_le hΦ ω.1 ψ.2 x

/-- For an injective `⋆`-homomorphism `Φ` of `A ⊗[ℂ] B` into a C⋆-algebra, the `⋆`-homomorphism of
the completion `Φ.closureRange` of `A ⊗[ℂ] B` for the C⋆-norm `x ↦ ‖Φ x‖` onto the minimal tensor
product that is the identity on `A ⊗[ℂ] B`: it sends `Φ x` to `x`. -/
noncomputable def ofClosureRange {Φ : A ⊗[ℂ] B →⋆ₙₐ[ℂ] C} (hΦ : Function.Injective Φ) :
    Φ.closureRange →⋆ₙₐ[ℂ] A ⊗ₘᵢₙ B :=
  NonUnitalStarAlgHom.closureRangeMap (φ := Φ) (ψ := π₀[A, B]) fun x => norm_of_le_norm_apply hΦ x

/-- `MinTensorProduct.ofClosureRange` sends `Φ x` to `x`. -/
@[simp] lemma ofClosureRange_closureRangeRestrict {Φ : A ⊗[ℂ] B →⋆ₙₐ[ℂ] C}
    (hΦ : Function.Injective Φ) (x : A ⊗[ℂ] B) :
    ofClosureRange hΦ (Φ.closureRangeRestrict x) = of A B x :=
  NonUnitalStarAlgHom.closureRangeMap_closureRangeRestrict _ x

/-- **Every completion of `A ⊗[ℂ] B` for a C⋆-norm maps onto the minimal tensor product**:
`MinTensorProduct.ofClosureRange` is surjective, its range being closed and containing the algebraic
tensor product. -/
theorem ofClosureRange_surjective {Φ : A ⊗[ℂ] B →⋆ₙₐ[ℂ] C} (hΦ : Function.Injective Φ) :
    Function.Surjective (ofClosureRange hΦ) := by
  have hclosed : IsClosed (Set.range (ofClosureRange hΦ)) :=
    NonUnitalStarAlgHom.isClosed_range (ofClosureRange hΦ)
  rw [← Set.range_eq_univ, ← hclosed.closure_eq]
  exact (denseRange_of.mono (by
    rintro _ ⟨x, rfl⟩
    exact ⟨Φ.closureRangeRestrict x, ofClosureRange_closureRangeRestrict hΦ x⟩)).closure_eq

end MinTensorProduct
