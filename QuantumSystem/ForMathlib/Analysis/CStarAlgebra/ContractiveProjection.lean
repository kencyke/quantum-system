/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.LinearAlgebra.Projection

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range

/-!
# Contractive projections onto C⋆-subalgebras are bimodule maps

Let `φ` be a linear projection of a C⋆-algebra `A` onto a ⋆-subalgebra `S`
(`LinearMap.IsProj S.toSubmodule φ`), with `‖φ x‖ ≤ ‖x‖` for every `x`. Then `φ (s * x) = s * φ x`
and `φ (x * s) = φ x * s` for `s ∈ S`. The range `S` is closed, being the set of fixed points of
the continuous map `φ` (`LinearMap.IsProj.isClosed`).

The proof uses only the norm and the continuous functional calculus of a self-adjoint `b ∈ S`,
computed in the unitization `A⁺¹`, so that `A` need not be unital.

* **Localization.** Let `f = u(b)` and `g = v(b)` for functions `u`, `v` vanishing on
  `|x - μ| ≥ ρ₁` and on `|x - μ| ≤ ρ₂` respectively, `ρ₁ < ρ₂`, with `|u|, |v| ≤ 1`. Then
  `g φ(f a) = 0`. For `z = φ(f a)` and functions `e` of `b` with `g e = g`, `f e = 0` and `‖g‖ ≤ 1`,
  the element `w = f a + t e z` has `φ(w) = z + t e z`, so `g φ(w) = (1 + t) g z`, while
  `‖w‖² ≤ ‖a‖² + t² ‖e z‖²`. A chain `g = e₀, e₁, …, e_N` of ramps between the two supports gives
  `(1 + t)² ‖eₖ z‖² ≤ ‖a‖² + t² ‖eₖ₊₁ z‖²`, hence `‖g z‖² ≤ ‖a‖² / (N + 1)` for every `N`.
* **Left `S`-linearity.** Cover the spectrum of `b` by tents `fₖ` of half-width `δ` at
  `λₖ = (k - M) δ`, with `Σ fₖ = 1`. With `D(y) = φ(y a) - y φ(a)` and `D(1) = 0`,
  `D(b) = D(Σ (b - λₖ) fₖ(b)) + Σ (λₖ - b) eₖ(b) D(fₖ(b))` by localization, for plateaus `eₖ` of
  half-width `2 δ` around `λₖ`. The first term is at most `2 δ ‖a‖`; in the second, the
  coefficients `(λₖ - b) eₖ(b)` have norm at most `2 δ` and are orthogonal within each residue class
  of `k` modulo `4`, so it is `O(√δ)`. Letting `δ → 0`, `φ(b a) = b φ(a)`; a general `s ∈ S` is
  `ℜ s + I ℑ s`.
* **Right `S`-linearity** is left `S`-linearity in `Aᵐᵒᵖ`.

## Main results

* `LinearMap.IsProj.isClosed` — the range of a continuous projection is closed.
* `LinearMap.IsProj.map_mul_left_of_norm_apply_le`,
  `LinearMap.IsProj.map_mul_right_of_norm_apply_le`, `LinearMap.IsProj.map_mul_mul_of_norm_apply_le`
  — **a contractive projection onto a ⋆-subalgebra `S` is `S`-linear on both sides**.
-/

@[expose] public section

open scoped CStarAlgebra ComplexStarModule

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- `S⁺¹` inside `A⁺¹`: the elements whose `A`-component lies in `S`. -/
private def unitizationSubalgebra (S : NonUnitalStarSubalgebra ℂ A) : StarSubalgebra ℂ A⁺¹ where
  carrier := {y | y.snd ∈ S}
  mul_mem' {y z} (hy : y.snd ∈ S) (hz : z.snd ∈ S) := by
    change (y * z).snd ∈ S
    rw [Unitization.snd_mul]
    exact add_mem (add_mem (SMulMemClass.smul_mem _ hz) (SMulMemClass.smul_mem _ hy)) (mul_mem hy hz)
  add_mem' {y z} hy hz := by simpa [Unitization.snd_add] using add_mem hy hz
  algebraMap_mem' r := by simp [Unitization.algebraMap_eq_inl, zero_mem]
  star_mem' {y} hy := by simpa [Unitization.snd_star] using star_mem hy

private lemma mem_unitizationSubalgebra {S : NonUnitalStarSubalgebra ℂ A} {y : A⁺¹} :
    y ∈ unitizationSubalgebra S ↔ y.snd ∈ S :=
  Iff.rfl

private instance {S : NonUnitalStarSubalgebra ℂ A} [hS : IsClosed (S : Set A)] :
    IsClosed (unitizationSubalgebra S : Set A⁺¹) :=
  hS.preimage Unitization.continuous_snd

/-- `y a` lies in `A` for `y ∈ A⁺¹` and `a ∈ A`. -/
private lemma inr_snd_mul_inr (y : A⁺¹) (a : A) : (((y * a).snd : A) : A⁺¹) = y * a := by
  ext <;> simp [Unitization.fst_mul, Unitization.snd_mul]

/-- One step of the localization estimate. For `x = f a` and `z = E x`, with `g e = g`, `f e = 0` and
`e z` fixed by `E`, the element `w = x + t e z` has `E w = z + t e z`, so `g E(w) = (1 + t) g z`,
while `‖w‖² ≤ ‖a‖² + t² ‖e z‖²` by orthogonality. -/
private lemma sq_mul_norm_mul_le {E : A →ₗ[ℂ] A} (hE : ∀ x, ‖E x‖ ≤ ‖x‖) {f g e : A⁺¹} {a y : A}
    (hf : IsSelfAdjoint f) (he : IsSelfAdjoint e) (hfn : ‖f‖ ≤ 1) (hgn : ‖g‖ ≤ 1)
    (hfe : f * e = 0) (hge : g * e = g) (hy : (y : A⁺¹) = e * (E (f * a).snd : A⁺¹))
    (hEy : E y = y) {t : ℝ} (ht : 0 ≤ t) :
    (1 + t) ^ 2 * ‖g * (E (f * a).snd : A⁺¹)‖ ^ 2 ≤
      ‖a‖ ^ 2 + t ^ 2 * ‖e * (E (f * a).snd : A⁺¹)‖ ^ 2 := by
  set x := (f * a).snd
  set z : A⁺¹ := (E x : A⁺¹)
  have hx : (x : A⁺¹) = f * a := inr_snd_mul_inr f a
  have hef : e * f = 0 := by simpa [hf.star_eq, he.star_eq] using congr(star $hfe)
  set w : A := x + (t : ℂ) • y
  have hgw : g * (E w : A⁺¹) = ((1 + t : ℝ) : ℂ) • (g * z) := by
    rw [map_add, map_smul, hEy, Unitization.inr_add, Unitization.inr_smul, hy, mul_add,
      mul_smul_comm, ← mul_assoc, hge]
    push_cast
    module
  have h₁ : (1 + t) * ‖g * z‖ ≤ ‖w‖ := by
    calc (1 + t) * ‖g * z‖ = ‖g * (E w : A⁺¹)‖ := by
          rw [hgw, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      _ ≤ ‖g‖ * ‖(E w : A⁺¹)‖ := norm_mul_le _ _
      _ ≤ 1 * ‖E w‖ := by rw [Unitization.norm_inr]; gcongr
      _ ≤ ‖w‖ := by rw [one_mul]; exact hE w
  have hw : (w : A⁺¹) = f * a + (t : ℂ) • (e * z) := by
    rw [Unitization.inr_add, Unitization.inr_smul, hx, hy]
  have h₂ : ‖w‖ ^ 2 ≤ ‖a‖ ^ 2 + t ^ 2 * ‖e * z‖ ^ 2 := by
    have hww : star (w : A⁺¹) * w =
        star (f * (a : A⁺¹)) * (f * a) + ((t : ℂ) ^ 2) • (star (e * z) * (e * z)) := by
      have c₁ : star (f * (a : A⁺¹)) * (e * z) = 0 := by
        rw [star_mul, hf.star_eq, mul_assoc, ← mul_assoc f, hfe, zero_mul, mul_zero]
      have c₂ : star (e * z) * (f * (a : A⁺¹)) = 0 := by
        rw [star_mul, he.star_eq, mul_assoc, ← mul_assoc e, hef, zero_mul, mul_zero]
      rw [hw, star_add, star_smul, add_mul, mul_add, mul_add, smul_mul_assoc, mul_smul_comm,
        smul_mul_assoc, mul_smul_comm, c₁, c₂, smul_zero, smul_smul, Complex.star_def,
        Complex.conj_ofReal]
      simp [sq]
    calc ‖w‖ ^ 2 = ‖star (w : A⁺¹) * w‖ := by
          rw [CStarRing.norm_star_mul_self, Unitization.norm_inr, sq]
      _ ≤ ‖star (f * (a : A⁺¹)) * (f * a)‖ + ‖((t : ℂ) ^ 2) • (star (e * z) * (e * z))‖ := by
          rw [hww]; exact norm_add_le _ _
      _ = ‖f * (a : A⁺¹)‖ ^ 2 + t ^ 2 * ‖e * z‖ ^ 2 := by
          rw [norm_smul, CStarRing.norm_star_mul_self, CStarRing.norm_star_mul_self, norm_pow,
            Complex.norm_real, Real.norm_eq_abs, sq_abs]
          ring
      _ ≤ ‖a‖ ^ 2 + t ^ 2 * ‖e * z‖ ^ 2 := by
          gcongr
          calc ‖f * (a : A⁺¹)‖ ≤ ‖f‖ * ‖(a : A⁺¹)‖ := norm_mul_le _ _
            _ ≤ 1 * ‖a‖ := by rw [Unitization.norm_inr]; gcongr
            _ = ‖a‖ := one_mul _
  calc (1 + t) ^ 2 * ‖g * z‖ ^ 2 = ((1 + t) * ‖g * z‖) ^ 2 := by ring
    _ ≤ ‖w‖ ^ 2 := by gcongr
    _ ≤ _ := h₂

/-- The recursion `(1 + t)² sₖ ≤ C + t² sₖ₊₁` for every `t ≥ 0` and `k < N`, with `s_N ≤ C`, gives
`s₀ ≤ C / (N + 1)`: by induction `s_{N-m} ≤ C / (m + 1)`, taking `t = m + 1`. -/
private lemma le_div_of_forall_sq_mul_le {s : ℕ → ℝ} {C : ℝ} {N : ℕ} (hN : s N ≤ C)
    (h : ∀ k < N, ∀ t : ℝ, 0 ≤ t → (1 + t) ^ 2 * s k ≤ C + t ^ 2 * s (k + 1)) :
    s 0 ≤ C / (N + 1) := by
  have key : ∀ m ≤ N, s (N - m) ≤ C / (m + 1) := by
    intro m
    induction m with
    | zero => simpa using hN
    | succ m ih =>
      intro hm
      have hk : N - (m + 1) < N := by omega
      have hk1 : N - (m + 1) + 1 = N - m := by omega
      have h' := h _ hk (m + 1) (by positivity)
      rw [hk1] at h'
      have hih := ih (by omega)
      have hm1 : (0 : ℝ) < m + 1 := by positivity
      rw [le_div_iff₀ (by positivity)]
      push_cast
      have : (1 + ((m : ℝ) + 1)) ^ 2 * s (N - (m + 1)) ≤ C * (m + 2) := by
        calc (1 + ((m : ℝ) + 1)) ^ 2 * s (N - (m + 1)) ≤ C + ((m : ℝ) + 1) ^ 2 * s (N - m) := h'
          _ ≤ C + ((m : ℝ) + 1) ^ 2 * (C / (m + 1)) := by gcongr
          _ = C * (m + 2) := by field_simp; ring
      nlinarith
  simpa using key N le_rfl

/-- The ramp `x ↦ max 0 (min 1 ((|x - μ| - r) / w))`: `0` for `|x - μ| ≤ r` and `1` for
`|x - μ| ≥ r + w`. -/
private noncomputable def ramp (μ r w x : ℝ) : ℝ := max 0 (min 1 ((|x - μ| - r) / w))

private lemma continuous_ramp (μ r w : ℝ) : Continuous (ramp μ r w) := by
  unfold ramp; fun_prop

private lemma ramp_eq_zero {μ r w x : ℝ} (hw : 0 < w) (h : |x - μ| ≤ r) : ramp μ r w x = 0 := by
  have : (|x - μ| - r) / w ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hw.le
  simp only [ramp]
  exact max_eq_left ((min_le_right _ _).trans this)

private lemma ramp_eq_one {μ r w x : ℝ} (hw : 0 < w) (h : r + w ≤ |x - μ|) : ramp μ r w x = 1 := by
  have : 1 ≤ (|x - μ| - r) / w := by rw [le_div_iff₀ hw]; linarith
  simp [ramp, min_eq_left this]

private lemma abs_ramp_le (μ r w x : ℝ) : |ramp μ r w x| ≤ 1 := by
  rw [abs_of_nonneg (le_max_left _ _)]
  exact max_le zero_le_one (min_le_left _ _)

/-- **Localization.** Let `b ∈ S` be self-adjoint, and let `φ` vanish where `|x - μ| ≥ ρ₁` and `ψ`
where `|x - μ| ≤ ρ₂`, with `ρ₁ < ρ₂` and `|φ|, |ψ| ≤ 1`. Then `ψ(b) E(φ(b) a) = 0`, computed in
`A⁺¹`. Between `ψ` and `φ` fit `N` ramps `e₁, …, e_N` with `eₖ eₖ₊₁ = eₖ` and `φ eₖ = 0`, so
`sₖ = ‖eₖ E(φ(b) a)‖²` satisfies `(1 + t)² sₖ ≤ ‖a‖² + t² sₖ₊₁` (`sq_mul_norm_mul_le`), and
`s₀ ≤ ‖a‖² / (N + 1)` for every `N`. -/
private lemma cfc_mul_map_cfc_mul_eq_zero {E : A →ₗ[ℂ] A} (hE : ∀ x, ‖E x‖ ≤ ‖x‖)
    {S : NonUnitalStarSubalgebra ℂ A} [IsClosed (S : Set A)]
    (hP : LinearMap.IsProj S.toSubmodule E) {b : A} (hbS : b ∈ S) (hb : IsSelfAdjoint b)
    {φ ψ : ℝ → ℝ} (hφc : Continuous φ) (hψc : Continuous ψ) {μ ρ₁ ρ₂ : ℝ} (hρ : ρ₁ < ρ₂)
    (hφ : ∀ x, ρ₁ ≤ |x - μ| → φ x = 0) (hψ : ∀ x, |x - μ| ≤ ρ₂ → ψ x = 0)
    (hφ1 : ∀ x, |φ x| ≤ 1) (hψ1 : ∀ x, |ψ x| ≤ 1) (a : A) :
    cfc ψ (b : A⁺¹) * (E (cfc φ (b : A⁺¹) * a).snd : A⁺¹) = 0 := by
  set β : A⁺¹ := Unitization.inr b
  have hβ : IsSelfAdjoint β := hb.inr ℂ
  have hβS : β ∈ unitizationSubalgebra S :=
    mem_unitizationSubalgebra.mpr (by rw [Unitization.snd_inr]; exact hbS)
  set f := cfc φ β
  set z : A⁺¹ := (E (f * a).snd : A⁺¹)
  have hzS : z ∈ unitizationSubalgebra S :=
    mem_unitizationSubalgebra.mpr (by rw [Unitization.snd_inr]; exact hP.map_mem _)
  have hfixS (c : A⁺¹) (hc : c ∈ unitizationSubalgebra S) :
      ((c * z).snd : A⁺¹) = c * z ∧ E (c * z).snd = (c * z).snd :=
    ⟨inr_snd_mul_inr c _, hP.map_id _ (mul_mem hc hzS)⟩
  have hnorm (χ : ℝ → ℝ) (h : ∀ x, |χ x| ≤ 1) : ‖cfc χ β‖ ≤ 1 :=
    norm_cfc_le zero_le_one fun x _ => by simpa using h x
  have hz : ‖z‖ ≤ ‖a‖ := by
    calc ‖z‖ = ‖E (f * a).snd‖ := Unitization.norm_inr _
      _ ≤ ‖((f * a).snd : A⁺¹)‖ := by rw [Unitization.norm_inr]; exact hE _
      _ ≤ ‖f‖ * ‖(a : A⁺¹)‖ := by rw [inr_snd_mul_inr]; exact norm_mul_le _ _
      _ ≤ 1 * ‖a‖ := by rw [Unitization.norm_inr]; gcongr; exact hnorm φ hφ1
      _ = ‖a‖ := one_mul _
  have hN (N : ℕ) : ‖cfc ψ β * z‖ ^ 2 ≤ ‖a‖ ^ 2 / (N + 1) := by
    set w : ℝ := (ρ₂ - ρ₁) / (N + 1)
    have hw : 0 < w := div_pos (by linarith) (by positivity)
    have hNw : N * w < ρ₂ - ρ₁ := by
      rw [show N * w = (ρ₂ - ρ₁) * (N / (N + 1)) by simp only [w]; ring]
      exact mul_lt_of_lt_one_right (by linarith) ((div_lt_one (by positivity)).mpr (by linarith))
    let χ : ℕ → ℝ → ℝ := fun k => if k = 0 then ψ else ramp μ (ρ₂ - k * w) w
    have hχc (k : ℕ) : Continuous (χ k) := by
      by_cases hk : k = 0
      · simpa [χ, hk] using hψc
      · simpa [χ, hk] using continuous_ramp μ (ρ₂ - k * w) w
    have hχ1 (k : ℕ) (x : ℝ) : |χ k x| ≤ 1 := by
      by_cases hk : k = 0
      · simpa [χ, hk] using hψ1 x
      · simpa [χ, hk] using abs_ramp_le μ (ρ₂ - k * w) w x
    have hχ0 (k : ℕ) (x : ℝ) (hx : |x - μ| ≤ ρ₂ - k * w) : χ k x = 0 := by
      by_cases hk : k = 0
      · simpa [χ, hk] using hψ x (by simpa [hk] using hx)
      · simpa [χ, hk] using ramp_eq_zero hw hx
    have hχmul (k : ℕ) : (fun x => χ k x * χ (k + 1) x) = χ k := by
      funext x
      by_cases hx : |x - μ| ≤ ρ₂ - k * w
      · rw [hχ0 k x hx, zero_mul]
      · have : χ (k + 1) x = 1 := by
          simp only [χ, Nat.add_one_ne_zero, ↓reduceIte]
          exact ramp_eq_one hw (by push_cast; linarith)
        rw [this, mul_one]
    have hφχ (k : ℕ) (hk : k < N) : (fun x => φ x * χ (k + 1) x) = 0 := by
      funext x
      by_cases hx : ρ₁ ≤ |x - μ|
      · rw [Pi.zero_apply, hφ x hx, zero_mul]
      · have hk' : ((k + 1 : ℕ) : ℝ) * w ≤ N * w := by gcongr; exact_mod_cast hk
        rw [Pi.zero_apply, hχ0 (k + 1) x (by linarith), mul_zero]
    set c : ℕ → A⁺¹ := fun k => cfc (χ k) β
    have hc0 : c 0 = cfc ψ β := by simp [c, χ]
    rw [← hc0]
    refine le_div_of_forall_sq_mul_le (s := fun k => ‖c k * z‖ ^ 2) ?_ fun k hk t ht => ?_
    · calc ‖c N * z‖ ^ 2 ≤ (‖c N‖ * ‖z‖) ^ 2 := by gcongr; exact norm_mul_le _ _
        _ ≤ (1 * ‖a‖) ^ 2 := by gcongr; exact hnorm _ (hχ1 N)
        _ = ‖a‖ ^ 2 := by rw [one_mul]
    · have hcS : c (k + 1) ∈ unitizationSubalgebra S := cfc_mem _ hβS
      have hge : c k * c (k + 1) = c k := by
        simp only [c]
        rw [← cfc_mul (χ k) (χ (k + 1)) β (hχc k).continuousOn (hχc (k + 1)).continuousOn,
          hχmul k]
      have hfe : f * c (k + 1) = 0 := by
        simp only [f, c]
        rw [← cfc_mul φ (χ (k + 1)) β hφc.continuousOn (hχc (k + 1)).continuousOn, hφχ k hk]
        exact cfc_zero ℝ β
      exact sq_mul_norm_mul_le hE (cfc_predicate _ _) (cfc_predicate _ _) (hnorm φ hφ1)
        (hnorm _ (hχ1 k)) hfe hge (hfixS _ hcS).1 (hfixS _ hcS).2 ht
  have h0 : ‖cfc ψ β * z‖ ^ 2 ≤ 0 := by
    by_contra hpos
    rw [not_le] at hpos
    obtain ⟨N, hN'⟩ := exists_nat_gt (‖a‖ ^ 2 / ‖cfc ψ β * z‖ ^ 2)
    have h := hN N
    rw [le_div_iff₀ (by positivity)] at h
    rw [div_lt_iff₀ hpos] at hN'
    nlinarith
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm h0 (by positivity)))

/-- If the `c i` are pairwise orthogonal, `c i⋆ c j = 0` for `i ≠ j`, then
`‖Σ c i y i‖² ≤ Σ ‖c i‖² ‖y i‖²`: the cross terms of `(Σ c i y i)⋆ (Σ c i y i)` vanish. -/
private lemma sq_norm_sum_mul_le {B : Type*} [NonUnitalCStarAlgebra B] {ι : Type*} (s : Finset ι)
    (c y : ι → B) (hc : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → star (c i) * c j = 0) :
    ‖∑ i ∈ s, c i * y i‖ ^ 2 ≤ ∑ i ∈ s, ‖c i‖ ^ 2 * ‖y i‖ ^ 2 := by
  have h : star (∑ i ∈ s, c i * y i) * (∑ i ∈ s, c i * y i) =
      ∑ i ∈ s, star (y i) * (star (c i) * c i) * y i := by
    rw [star_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_eq_single i (fun j hj hji => by
      rw [star_mul, mul_assoc, ← mul_assoc (star (c i)), hc i hi j hj (Ne.symm hji), zero_mul,
        mul_zero]) (fun h => absurd hi h)]
    rw [star_mul]
    noncomm_ring
  rw [sq, ← CStarRing.norm_star_mul_self, h]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  calc ‖star (y i) * (star (c i) * c i) * y i‖
      ≤ ‖star (y i)‖ * ‖star (c i) * c i‖ * ‖y i‖ := by
        refine (norm_mul_le _ _).trans ?_
        gcongr
        exact norm_mul_le _ _
    _ = ‖c i‖ ^ 2 * ‖y i‖ ^ 2 := by
        rw [norm_star, CStarRing.norm_star_mul_self]; ring

/-- `max 0 (min 1 v)`. -/
private noncomputable def clamp (v : ℝ) : ℝ := max 0 (min 1 v)

private lemma clamp_nonneg (v : ℝ) : 0 ≤ clamp v := le_max_left _ _

private lemma clamp_le_one (v : ℝ) : clamp v ≤ 1 := max_le zero_le_one (min_le_left _ _)

private lemma clamp_of_nonpos {v : ℝ} (hv : v ≤ 0) : clamp v = 0 :=
  max_eq_left ((min_le_right _ _).trans hv)

private lemma clamp_of_one_le {v : ℝ} (hv : 1 ≤ v) : clamp v = 1 := by
  simp [clamp, min_eq_left hv]

private lemma clamp_mono {v w : ℝ} (h : v ≤ w) : clamp v ≤ clamp w :=
  max_le_max le_rfl (min_le_min le_rfl h)

/-- The tent of height `1` at `μ` with half-width `δ`, as a difference of clamps. -/
private noncomputable def tent (μ δ x : ℝ) : ℝ := clamp ((x - μ) / δ + 1) - clamp ((x - μ) / δ)

private lemma continuous_tent (μ δ : ℝ) : Continuous (tent μ δ) := by
  unfold tent clamp; fun_prop

private lemma tent_nonneg (μ δ x : ℝ) : 0 ≤ tent μ δ x :=
  sub_nonneg.mpr (clamp_mono (by linarith))

private lemma tent_le_one (μ δ x : ℝ) : tent μ δ x ≤ 1 := by
  unfold tent; linarith [clamp_le_one ((x - μ) / δ + 1), clamp_nonneg ((x - μ) / δ)]

private lemma tent_eq_zero {μ δ x : ℝ} (hδ : 0 < δ) (h : δ ≤ |x - μ|) : tent μ δ x = 0 := by
  unfold tent
  rcases le_abs'.mp h with h | h
  · have : (x - μ) / δ ≤ -1 := by rw [div_le_iff₀ hδ]; linarith
    rw [clamp_of_nonpos (by linarith), clamp_of_nonpos (by linarith), sub_zero]
  · have : 1 ≤ (x - μ) / δ := by rw [le_div_iff₀ hδ]; linarith
    rw [clamp_of_one_le (by linarith), clamp_of_one_le this, sub_self]

/-- The tents at `(k - M) δ`, `k < 2 M + 1`, sum to `1` on `[-M δ, M δ]`: the sum telescopes. -/
private lemma sum_tent {δ x : ℝ} (hδ : 0 < δ) (M : ℕ) (hx : |x| ≤ M * δ) :
    ∑ k ∈ Finset.range (2 * M + 1), tent (((k : ℝ) - M) * δ) δ x = 1 := by
  set P : ℕ → ℝ := fun k => clamp ((x - ((k : ℝ) - M) * δ) / δ + 1)
  have hP (k : ℕ) : tent (((k : ℝ) - M) * δ) δ x = P k - P (k + 1) := by
    simp only [tent, P]
    congr 2
    field_simp
    push_cast
    ring
  simp only [hP]
  rw [Finset.sum_range_sub']
  have h0 : P 0 = 1 := clamp_of_one_le (by
    rw [abs_le] at hx
    have : 0 ≤ (x - ((0 : ℕ) - (M : ℝ)) * δ) / δ := div_nonneg (by push_cast; linarith) hδ.le
    linarith)
  have hn : P (2 * M + 1) = 0 := clamp_of_nonpos (by
    rw [abs_le] at hx
    have : (x - (((2 * M + 1 : ℕ) : ℝ) - M) * δ) / δ ≤ -1 := by
      rw [div_le_iff₀ hδ]; push_cast; linarith
    linarith)
  rw [h0, hn, sub_zero]

/-- The defect `D(y) = E(y a) - y E(a)` of `E` as a left `A⁺¹`-module map, at `a`. -/
private noncomputable def defect (E : A →ₗ[ℂ] A) (a : A) : A⁺¹ →ₗ[ℂ] A⁺¹ :=
  Unitization.inrHom ℂ ℂ A ∘ₗ E ∘ₗ Unitization.sndHom ℂ ℂ A ∘ₗ LinearMap.mulRight ℂ (a : A⁺¹) -
    LinearMap.mulRight ℂ (E a : A⁺¹)

private lemma defect_apply (E : A →ₗ[ℂ] A) (a : A) (y : A⁺¹) :
    defect E a y = (E (y * a).snd : A⁺¹) - y * E a :=
  rfl

private lemma defect_one (E : A →ₗ[ℂ] A) (a : A) : defect E a 1 = 0 := by
  simp [defect_apply]

private lemma norm_defect_le {E : A →ₗ[ℂ] A} (hE : ∀ x, ‖E x‖ ≤ ‖x‖) (a : A) (y : A⁺¹) :
    ‖defect E a y‖ ≤ 2 * ‖y‖ * ‖a‖ := by
  rw [defect_apply]
  refine (norm_sub_le _ _).trans ?_
  have h₁ : ‖(E (y * a).snd : A⁺¹)‖ ≤ ‖y‖ * ‖a‖ := by
    rw [Unitization.norm_inr]
    refine (hE _).trans ?_
    rw [← Unitization.norm_inr (𝕜 := ℂ), inr_snd_mul_inr, ← Unitization.norm_inr (𝕜 := ℂ) a]
    exact norm_mul_le _ _
  have h₂ : ‖y * (E a : A⁺¹)‖ ≤ ‖y‖ * ‖a‖ := by
    refine (norm_mul_le _ _).trans ?_
    rw [Unitization.norm_inr]
    gcongr
    exact hE a
  linarith

/-- **Left `S`-linearity, for self-adjoint `b`.** A contraction `E` of `A` into a closed
⋆-subalgebra `S` which fixes `S` satisfies `E(b a) = b E(a)` for self-adjoint `b ∈ S`.

Cover the spectrum of `b` by tents `fₖ` at `λₖ = (k - M) δ`, with `Σ fₖ = 1`. With
`D(y) = E(y a) - y E(a)`, `D(1) = 0` gives `D(b) = D(Σ (b - λₖ) fₖ(b)) + Σ (λₖ - b) D(fₖ(b))`. The
first term is at most `2 δ ‖a‖`. By localization, `D(fₖ(b)) = eₖ(b) D(fₖ(b))` for a plateau `eₖ`
around `λₖ` of half-width `2 δ`, so the second term is `Σ cₖ D(fₖ(b))` with `‖cₖ‖ ≤ 2 δ`, and the
`cₖ` with `k` in one residue class modulo `4` are orthogonal. So `‖D(b)‖ = O(√δ)`. -/
private lemma map_mul_left_of_isSelfAdjoint {E : A →ₗ[ℂ] A} (hE : ∀ x, ‖E x‖ ≤ ‖x‖)
    {S : NonUnitalStarSubalgebra ℂ A} [IsClosed (S : Set A)]
    (hP : LinearMap.IsProj S.toSubmodule E) {b : A} (hbS : b ∈ S) (hb : IsSelfAdjoint b) (a : A) :
    E (b * a) = b * E a := by
  set β : A⁺¹ := Unitization.inr b
  have hβ : IsSelfAdjoint β := hb.inr ℂ
  set D := defect E a
  suffices hD : D β = 0 by
    rw [defect_apply, sub_eq_zero] at hD
    apply Unitization.inr_injective (R := ℂ)
    rw [Unitization.inr_mul]
    simpa [β] using hD
  -- `‖D β‖ ≤ g δ` for every `δ > 0`, with `g δ → 0`.
  set g : ℝ → ℝ := fun δ => 2 * δ * ‖a‖ + 4 * Real.sqrt (16 * ‖a‖ ^ 2 * (2 * ‖b‖ * δ + 3 * δ ^ 2))
  suffices hg : ∀ δ : ℝ, 0 < δ → ‖D β‖ ≤ g δ by
    have hlim : Filter.Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have : Continuous g := by fun_prop
      simpa [g] using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    exact norm_le_zero_iff.mp (ge_of_tendsto hlim (eventually_nhdsWithin_of_forall hg))
  intro δ hδ
  set M : ℕ := ⌈‖b‖ / δ⌉₊
  set n : ℕ := 2 * M + 1
  have hMδ : ‖b‖ ≤ M * δ := (div_le_iff₀ hδ).mp (Nat.le_ceil _)
  have hσ : ∀ x ∈ spectrum ℝ β, |x| ≤ M * δ := fun x hx => by
    have := spectrum.norm_le_norm_of_mem hx
    rw [Real.norm_eq_abs, Unitization.norm_inr] at this
    linarith
  set lam : ℕ → ℝ := fun k => ((k : ℝ) - M) * δ
  set f : ℕ → ℝ → ℝ := fun k => tent (lam k) δ
  set ψ : ℕ → ℝ → ℝ := fun k => ramp (lam k) (3 / 2 * δ) (δ / 2)
  set c : ℕ → ℝ → ℝ := fun k x => (lam k - x) * (1 - ψ k x)
  set kf : ℝ → ℝ := fun x => ∑ k ∈ Finset.range n, (x - lam k) * f k x
  have hfc (k : ℕ) : Continuous (f k) := continuous_tent _ _
  have hψc (k : ℕ) : Continuous (ψ k) := continuous_ramp _ _ _
  have hcc (k : ℕ) : Continuous (c k) := by
    have := hψc k
    simp only [c]; fun_prop
  have hkfc : Continuous kf := by
    simp only [kf]
    exact continuous_finsetSum _ fun k _ => (continuous_id.sub continuous_const).mul (hfc k)
  set F : ℕ → A⁺¹ := fun k => cfc (f k) β
  set Ψ : ℕ → A⁺¹ := fun k => cfc (ψ k) β
  set C : ℕ → A⁺¹ := fun k => cfc (c k) β
  set K : A⁺¹ := cfc kf β
  -- `β = K + Σ λₖ Fₖ` and `Σ Fₖ = 1`.
  have hsum (x : ℝ) (hx : x ∈ spectrum ℝ β) : ∑ k ∈ Finset.range n, f k x = 1 :=
    sum_tent hδ M (hσ x hx)
  have hβK : β = K + ∑ k ∈ Finset.range n, lam k • F k := by
    have e₁ : cfc (fun x => kf x + ∑ k ∈ Finset.range n, lam k * f k x) β = cfc (id : ℝ → ℝ) β := by
      refine cfc_congr fun x hx => ?_
      simp only [kf, id, ← Finset.sum_add_distrib]
      rw [show ∑ k ∈ Finset.range n, ((x - lam k) * f k x + lam k * f k x) =
          x * ∑ k ∈ Finset.range n, f k x by rw [Finset.mul_sum]; congr 1; ext k; ring,
        hsum x hx, mul_one]
    rw [cfc_add (a := β) kf (fun x => ∑ k ∈ Finset.range n, lam k * f k x) hkfc.continuousOn
      (continuous_finsetSum _ fun k _ => continuous_const.mul (hfc k)).continuousOn,
      cfc_id ℝ β hβ] at e₁
    rw [← e₁]
    congr 1
    rw [show (fun x => ∑ k ∈ Finset.range n, lam k * f k x) =
        ∑ k ∈ Finset.range n, fun x => lam k * f k x by ext; simp,
      cfc_sum _ β _ fun k _ => ((hfc k).const_mul _).continuousOn]
    exact Finset.sum_congr rfl fun k _ => cfc_const_mul _ _ β (hfc k).continuousOn
  have hF1 : ∑ k ∈ Finset.range n, F k = 1 := by
    rw [← cfc_sum _ β _ fun k _ => (hfc k).continuousOn, ← cfc_one ℝ β hβ]
    refine cfc_congr fun x hx => ?_
    simpa using hsum x hx
  -- Localization: `(1 - Ψₖ) D(Fₖ) = D(Fₖ)`.
  have hloc (k : ℕ) : (1 - Ψ k) * D (F k) = D (F k) := by
    have hΨF : Ψ k * F k = 0 := by
      simp only [Ψ, F]
      rw [← cfc_mul _ _ β (hψc k).continuousOn (hfc k).continuousOn, ← cfc_zero ℝ β]
      refine cfc_congr fun x _ => ?_
      rw [Pi.zero_apply, mul_eq_zero]
      by_cases hx : |x - lam k| ≤ 3 / 2 * δ
      · exact Or.inl (ramp_eq_zero (by positivity) hx)
      · exact Or.inr (tent_eq_zero hδ (by linarith))
    have h := cfc_mul_map_cfc_mul_eq_zero hE hP hbS hb (hfc k) (hψc k)
      (μ := lam k) (ρ₁ := δ) (ρ₂ := 3 / 2 * δ) (by linarith) (fun x hx => tent_eq_zero hδ hx)
      (fun x hx => ramp_eq_zero (by positivity) hx)
      (fun x => abs_le.mpr ⟨by linarith [tent_nonneg (lam k) δ x], tent_le_one _ _ _⟩)
      (fun x => abs_ramp_le _ _ _ _) a
    rw [sub_mul, one_mul, sub_eq_self, defect_apply, mul_sub, ← mul_assoc, hΨF, zero_mul,
      sub_zero]
    exact h
  -- `Cₖ = (λₖ - β)(1 - Ψₖ)`.
  have hC (k : ℕ) : C k = (algebraMap ℝ A⁺¹ (lam k) - β) * (1 - Ψ k) := by
    simp only [C, c, Ψ]
    rw [cfc_mul (fun x => lam k - x) (fun x => 1 - ψ k x) β (by fun_prop)
      ((continuous_const.sub (hψc k)).continuousOn),
      cfc_sub (fun _ => lam k) (fun x => x) β, cfc_sub (fun _ => (1 : ℝ)) (ψ k) β (by fun_prop)
        (hψc k).continuousOn, cfc_const _ β hβ, cfc_const _ β hβ, cfc_id' ℝ β hβ, map_one]
  -- `D β = D K + Σ Cₖ D(Fₖ)`.
  have hDβ : D β = D K + ∑ k ∈ Finset.range n, C k * D (F k) := by
    have hD0 : ∑ k ∈ Finset.range n, D (F k) = 0 := by
      rw [← map_sum, hF1, defect_one]
    rw [hβK, map_add, map_sum]
    congr 1
    calc ∑ k ∈ Finset.range n, D (lam k • F k)
        = ∑ k ∈ Finset.range n, D (lam k • F k) - β * ∑ k ∈ Finset.range n, D (F k) := by
          rw [hD0, mul_zero, sub_zero]
      _ = ∑ k ∈ Finset.range n, (algebraMap ℝ A⁺¹ (lam k) - β) * D (F k) := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [LinearMap.map_smul_of_tower, sub_mul, Algebra.smul_def]
      _ = ∑ k ∈ Finset.range n, C k * D (F k) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hC, mul_assoc, hloc]
  -- The estimates.
  have hK : ‖K‖ ≤ δ := by
    refine norm_cfc_le hδ.le fun x hx => ?_
    rw [Real.norm_eq_abs]
    calc |kf x| ≤ ∑ k ∈ Finset.range n, |(x - lam k) * f k x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range n, δ * f k x := Finset.sum_le_sum fun k _ => by
          rw [abs_mul, abs_of_nonneg (tent_nonneg _ _ _)]
          by_cases h : δ ≤ |x - lam k|
          · simp [f, tent_eq_zero hδ h]
          · exact mul_le_mul_of_nonneg_right (not_le.mp h).le (tent_nonneg _ _ _)
      _ = δ := by rw [← Finset.mul_sum, hsum x hx, mul_one]
  have hDK : ‖D K‖ ≤ 2 * δ * ‖a‖ :=
    (norm_defect_le hE a K).trans (by gcongr)
  have hψ01 (k : ℕ) (x : ℝ) : 0 ≤ ψ k x ∧ ψ k x ≤ 1 :=
    ⟨le_max_left _ _, (le_abs_self _).trans (abs_ramp_le _ _ _ _)⟩
  have hc0 (k : ℕ) (x : ℝ) (h : 2 * δ ≤ |x - lam k|) : c k x = 0 := by
    simp only [c, ψ]
    rw [ramp_eq_one (by positivity) (by linarith), sub_self, mul_zero]
  have hCn (k : ℕ) : ‖C k‖ ≤ 2 * δ := by
    refine norm_cfc_le (by positivity) fun x _ => ?_
    rw [Real.norm_eq_abs]
    by_cases h : 2 * δ ≤ |x - lam k|
    · rw [hc0 k x h, abs_zero]; positivity
    · simp only [c]
      rw [abs_mul]
      have h1 : |1 - ψ k x| ≤ 1 := abs_le.mpr ⟨by linarith [(hψ01 k x).2], by linarith [(hψ01 k x).1]⟩
      calc |lam k - x| * |1 - ψ k x| ≤ (2 * δ) * 1 :=
            mul_le_mul (by rw [abs_sub_comm]; linarith) h1 (abs_nonneg _) (by positivity)
        _ = 2 * δ := mul_one _
  have hDF (k : ℕ) : ‖D (F k)‖ ≤ 2 * ‖a‖ := by
    have hF : ‖F k‖ ≤ 1 := norm_cfc_le zero_le_one fun x _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (tent_nonneg _ _ _)]; exact tent_le_one _ _ _
    calc ‖D (F k)‖ ≤ 2 * ‖F k‖ * ‖a‖ := norm_defect_le hE a _
      _ ≤ 2 * 1 * ‖a‖ := by gcongr
      _ = 2 * ‖a‖ := by ring
  have hCC (k l : ℕ) (hkl : k ≠ l) (hmod : k % 4 = l % 4) : star (C k) * C l = 0 := by
    rw [(show IsSelfAdjoint (C k) from cfc_predicate _ _).star_eq]
    simp only [C]
    rw [← cfc_mul _ _ β (hcc k).continuousOn (hcc l).continuousOn, ← cfc_zero ℝ β]
    refine cfc_congr fun x _ => ?_
    have hsep : 4 * δ ≤ |lam k - lam l| := by
      have h4 : (4 : ℝ) ≤ |(k : ℝ) - l| := by
        rcases (by omega : k + 4 ≤ l ∨ l + 4 ≤ k) with h | h
        · have : (k : ℝ) + 4 ≤ l := by exact_mod_cast h
          exact le_abs.mpr (Or.inr (by linarith))
        · have : (l : ℝ) + 4 ≤ k := by exact_mod_cast h
          exact le_abs.mpr (Or.inl (by linarith))
      simp only [lam]
      rw [show ((k : ℝ) - M) * δ - ((l : ℝ) - M) * δ = ((k : ℝ) - l) * δ by ring, abs_mul,
        abs_of_pos hδ]
      nlinarith
    rw [Pi.zero_apply, mul_eq_zero]
    by_cases h : 2 * δ ≤ |x - lam k|
    · exact Or.inl (hc0 k x h)
    · refine Or.inr (hc0 l x ?_)
      have := abs_sub_le (lam k) x (lam l)
      rw [abs_sub_comm (lam k) x] at this
      linarith
  have hn : (n : ℝ) * δ ^ 2 ≤ 2 * ‖b‖ * δ + 3 * δ ^ 2 := by
    have hM : (M : ℝ) < ‖b‖ / δ + 1 := Nat.ceil_lt_add_one (by positivity)
    have hMδ' : (M : ℝ) * δ < ‖b‖ + δ := by
      have := mul_lt_mul_of_pos_right hM hδ
      rwa [add_mul, div_mul_cancel₀ _ hδ.ne', one_mul] at this
    simp only [n]
    push_cast
    nlinarith
  set B : ℝ := 16 * ‖a‖ ^ 2 * (2 * ‖b‖ * δ + 3 * δ ^ 2)
  have hinner (r : ℕ) :
      ‖∑ k ∈ Finset.range n with k % 4 = r, C k * D (F k)‖ ≤ Real.sqrt B := by
    refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
    calc ‖∑ k ∈ Finset.range n with k % 4 = r, C k * D (F k)‖ ^ 2
        ≤ ∑ k ∈ Finset.range n with k % 4 = r, ‖C k‖ ^ 2 * ‖D (F k)‖ ^ 2 :=
          sq_norm_sum_mul_le _ _ _ fun i hi j hj hij => hCC i j hij (by
            simp only [Finset.mem_filter] at hi hj; omega)
      _ ≤ ∑ k ∈ Finset.range n with k % 4 = r, (2 * δ) ^ 2 * (2 * ‖a‖) ^ 2 :=
          Finset.sum_le_sum fun k _ => by gcongr; exacts [hCn k, hDF k]
      _ ≤ ∑ k ∈ Finset.range n, (2 * δ) ^ 2 * (2 * ‖a‖) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun _ _ _ => by positivity
      _ = 16 * ‖a‖ ^ 2 * (n * δ ^ 2) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      _ ≤ B := mul_le_mul_of_nonneg_left hn (by positivity)
  have hsumC : ‖∑ k ∈ Finset.range n, C k * D (F k)‖ ≤ 4 * Real.sqrt B := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun k => k % 4) (t := Finset.range 4)
      fun k _ => Finset.mem_range.mpr (Nat.mod_lt _ (by norm_num))]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ r ∈ Finset.range 4, ‖∑ k ∈ Finset.range n with k % 4 = r, C k * D (F k)‖
        ≤ ∑ _r ∈ Finset.range 4, Real.sqrt B := Finset.sum_le_sum fun r _ => hinner r
      _ = 4 * Real.sqrt B := by simp
  rw [hDβ]
  exact (norm_add_le _ _).trans (add_le_add hDK hsumC)

/-- Left `S`-linearity for every `s ∈ S`, from `s = ℜ s + I ℑ s`. -/
private lemma map_mul_left_of_mem {E : A →ₗ[ℂ] A} (hE : ∀ x, ‖E x‖ ≤ ‖x‖)
    {S : NonUnitalStarSubalgebra ℂ A} [IsClosed (S : Set A)]
    (hP : LinearMap.IsProj S.toSubmodule E) {s : A} (hs : s ∈ S) (a : A) : E (s * a) = s * E a := by
  have h₁ : (ℜ s : A) ∈ S := by
    rw [realPart_apply_coe, ← Complex.coe_smul]
    exact SMulMemClass.smul_mem _ (add_mem hs (star_mem hs))
  have h₂ : (ℑ s : A) ∈ S := by
    rw [imaginaryPart_apply_coe, ← Complex.coe_smul]
    exact SMulMemClass.smul_mem _ (SMulMemClass.smul_mem _ (sub_mem hs (star_mem hs)))
  conv_lhs => rw [← realPart_add_I_smul_imaginaryPart s]
  rw [add_mul, smul_mul_assoc, map_add, map_smul,
    map_mul_left_of_isSelfAdjoint hE hP h₁ (ℜ s).2,
    map_mul_left_of_isSelfAdjoint hE hP h₂ (ℑ s).2, ← smul_mul_assoc, ← add_mul,
    realPart_add_I_smul_imaginaryPart]

/-- `S` inside `Aᵐᵒᵖ`. -/
private def opSubalgebra (S : NonUnitalStarSubalgebra ℂ A) : NonUnitalStarSubalgebra ℂ Aᵐᵒᵖ where
  carrier := MulOpposite.unop ⁻¹' S
  add_mem' {x y} (hx : x.unop ∈ S) (hy : y.unop ∈ S) := add_mem hx hy
  zero_mem' := zero_mem S
  mul_mem' {x y} (hx : x.unop ∈ S) (hy : y.unop ∈ S) := mul_mem hy hx
  smul_mem' r {x} (hx : x.unop ∈ S) := SMulMemClass.smul_mem r hx
  star_mem' {x} (hx : x.unop ∈ S) := star_mem hx

private instance {S : NonUnitalStarSubalgebra ℂ A} [hS : IsClosed (S : Set A)] :
    IsClosed (opSubalgebra S : Set Aᵐᵒᵖ) := by
  change IsClosed (MulOpposite.unop ⁻¹' (S : Set A))
  exact hS.preimage MulOpposite.continuous_unop

/-- Right `S`-linearity: left `S`-linearity in `Aᵐᵒᵖ`. -/
private lemma map_mul_right_of_mem {E : A →ₗ[ℂ] A} (hE : ∀ x, ‖E x‖ ≤ ‖x‖)
    {S : NonUnitalStarSubalgebra ℂ A} [IsClosed (S : Set A)]
    (hP : LinearMap.IsProj S.toSubmodule E) {s : A} (hs : s ∈ S) (a : A) : E (a * s) = E a * s := by
  let E' : Aᵐᵒᵖ →ₗ[ℂ] Aᵐᵒᵖ :=
    (MulOpposite.opLinearEquiv ℂ).toLinearMap ∘ₗ E ∘ₗ (MulOpposite.opLinearEquiv ℂ).symm.toLinearMap
  have h := map_mul_left_of_mem (E := E') (S := opSubalgebra S) (fun x => hE x.unop)
    ⟨fun x => show E x.unop ∈ S from hP.map_mem x.unop,
      fun x (hx : x.unop ∈ S) => congrArg MulOpposite.op (hP.map_id x.unop hx)⟩
    (s := MulOpposite.op s) hs (MulOpposite.op a)
  exact congrArg MulOpposite.unop h

namespace LinearMap.IsProj

/-- **The range of a continuous projection is closed**, being its set of fixed points. -/
lemma isClosed {R M F : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [T2Space M] [FunLike F M M] {m : Submodule R M} {f : F} (h : IsProj m f) (hf : Continuous f) :
    IsClosed (m : Set M) := by
  have : (m : Set M) = {x | f x = x} := Set.ext fun x => ⟨h.map_id x, fun hx => hx ▸ h.map_mem x⟩
  exact this ▸ isClosed_eq hf continuous_id

variable {F : Type*} [FunLike F A A] [LinearMapClass F ℂ A A] {φ : F}
  {S : NonUnitalStarSubalgebra ℂ A} (hφ : IsProj S.toSubmodule φ) (hn : ∀ x, ‖φ x‖ ≤ ‖x‖)

include hφ hn

/-- **A contractive projection onto a C⋆-subalgebra is left `S`-linear.** If `φ` is a linear
projection of a C⋆-algebra `A` onto a ⋆-subalgebra `S` with `‖φ x‖ ≤ ‖x‖` for every `x`, then
`φ (s * x) = s * φ x` for `s ∈ S`. -/
theorem map_mul_left_of_norm_apply_le {s : A} (hs : s ∈ S) (x : A) : φ (s * x) = s * φ x := by
  have := hφ.isClosed (AddMonoidHomClass.continuous_of_bound φ 1 fun x => by simpa using hn x)
  exact map_mul_left_of_mem (E := (φ : A →ₗ[ℂ] A)) hn ⟨hφ.map_mem, hφ.map_id⟩ hs x

/-- **A contractive projection onto a C⋆-subalgebra is right `S`-linear.** If `φ` is a linear
projection of a C⋆-algebra `A` onto a ⋆-subalgebra `S` with `‖φ x‖ ≤ ‖x‖` for every `x`, then
`φ (x * s) = φ x * s` for `s ∈ S`. -/
theorem map_mul_right_of_norm_apply_le {s : A} (hs : s ∈ S) (x : A) : φ (x * s) = φ x * s := by
  have := hφ.isClosed (AddMonoidHomClass.continuous_of_bound φ 1 fun x => by simpa using hn x)
  exact map_mul_right_of_mem (E := (φ : A →ₗ[ℂ] A)) hn ⟨hφ.map_mem, hφ.map_id⟩ hs x

/-- **A contractive projection onto a C⋆-subalgebra is an `S`-bimodule map**:
`φ (a * x * b) = a * φ x * b` for `a, b ∈ S`. -/
theorem map_mul_mul_of_norm_apply_le {a b : A} (ha : a ∈ S) (hb : b ∈ S) (x : A) :
    φ (a * x * b) = a * φ x * b := by
  rw [hφ.map_mul_right_of_norm_apply_le hn hb, hφ.map_mul_left_of_norm_apply_le hn ha]

end LinearMap.IsProj
