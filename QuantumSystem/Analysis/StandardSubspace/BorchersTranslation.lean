/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.SpectralTheory.SpectralCone
public import QuantumSystem.Analysis.StandardSubspace.Borchers

/-!
# Borchers' theorem on translations and boosts

Let `T` be a strongly continuous unitary representation of a finite-dimensional real vector space
`V` on `H` and `K ⊆ H` a standard subspace, with modular group `Δ^{it}` and modular conjugation
`J`. The **translation cone** `C_K = {a | T(s a) K ⊆ K for all s ≥ 0}`
(`AddChar.IsStronglyContinuous.translationCone`) is a closed convex cone, and the
**spectral cone** (`AddChar.IsStronglyContinuous.spectralCone`) is the cone of directions `a`
whose one-parameter group `s ↦ T(s a)` has a positive generator.

**Borchers' theorem** (Borchers 1992; 1995, Theorem 4.1(b)) in the directional form: if `a` lies in
both cones, then
* `Δ^{it} T(s a) Δ^{-it} = T(e^{-2πt} s a)`
  (`AddChar.IsStronglyContinuous.modularGroup_mul_mul_eq_of_mem_spectralCone`), and
* `J T(s a) J = T(-s a)` (`AddChar.IsStronglyContinuous.modularConj_apply_eq_of_mem_spectralCone`).

With a negative generator (`-a` in the spectral cone) the dilation is `e^{2πt}` instead
(`…_of_neg_mem_spectralCone`), and translations along the lineality space of `C_K` (`a` and `-a`
both in `C_K`) commute with `Δ^{it}` and `J` (`…_of_neg_mem_translationCone`). Combined, for
`a ∈ C_K` with positive generator, `b ∈ C_K` with negative generator and `z` in the lineality
space, **Borchers' theorem** in the boost form
(`AddChar.IsStronglyContinuous.modularGroup_mul_mul_eq_boost`,
`AddChar.IsStronglyContinuous.modularConj_apply_eq_reflection`) states
`Δ^{it} T(r a + s b + z) Δ^{-it} = T(e^{-2πt} r a + e^{2πt} s b + z)` and
`J T(r a + s b + z) J = T(-r a - s b + z)`: the modular group acts as a boost, the modular
conjugation as a reflection.

## Proof

For `a` in both cones, let `P ≥ 0` be the generator of `s ↦ T(s a)` with projection-valued measure
`E`. The bounded operators `W(z) = ∫ exp (i e^{2πz} λ) dE(λ)` are defined and of norm at most `1`
on the strip `0 ≤ im z ≤ 1/2`, since `e^{2πz}` then lies in the closed upper half-plane, and their
matrix coefficients are holomorphic there (`ProjectionValuedMeasure.diffContOnCl_integralApply_cexp_of_nonneg`).
On the boundary, `W(t) = T(e^{2πt} a)` maps `K` into `K`, and `W(t + i/2) = T(-e^{2πt} a)`, the
adjoint of `T(e^{2πt} a)`, maps `K'` into `K'`. Borchers' Theorem B
(`StandardSubspace.modularGroup_apply_eq_of_upperStrip`,
`StandardSubspace.modularConj_apply_eq_of_upperStrip`) gives `Δ^{it} W(s) Δ^{-it} = W(s - t)` and
`J W(s) J = W(s + i/2)`, which are the two identities for `s > 0`; the case `s < 0` follows by
taking inverses. The negative generator case is the positive one for `K'` and `-a`, since
`-a ∈ C_{K'}`, `Δ_{K'}^{it} = Δ_K^{-it}` and `J_{K'} = J_K`. For the lineality space,
`T(s z) K = K`, and covariance (`StandardSubspace.modularGroup_map`,
`StandardSubspace.modularConj_map`) shows that `T(s z)` commutes with `Δ^{it}` and `J`.

## Main definitions

* `AddChar.IsStronglyContinuous.translationCone hT K` — the closed convex cone of directions `a`
  with `T(s a) K ⊆ K` for `s ≥ 0`.

## Main results

* `AddChar.IsStronglyContinuous.modularGroup_mul_mul_eq_of_mem_spectralCone`,
  `AddChar.IsStronglyContinuous.modularConj_apply_eq_of_mem_spectralCone` — **Borchers'
  theorem**: positive generator.
* `AddChar.IsStronglyContinuous.modularGroup_mul_mul_eq_of_neg_mem_spectralCone`,
  `AddChar.IsStronglyContinuous.modularConj_apply_eq_of_neg_mem_spectralCone` — negative
  generator.
* `AddChar.IsStronglyContinuous.modularGroup_mul_mul_eq_of_neg_mem_translationCone`,
  `AddChar.IsStronglyContinuous.modularConj_apply_eq_of_neg_mem_translationCone` — the lineality
  space.
* `AddChar.IsStronglyContinuous.modularGroup_mul_mul_eq_boost`,
  `AddChar.IsStronglyContinuous.modularConj_apply_eq_reflection` — **Borchers' theorem**, boost
  form.

## References

* H.-J. Borchers, *The CPT-theorem in two-dimensional theories of local observables*,
  Comm. Math. Phys. 143 (1992), 315–332
* H.-J. Borchers, *On the use of modular groups in quantum field theory*,
  Ann. Inst. H. Poincaré Phys. Théor. 63 (1995), 331–382, Theorem 4.1
* [R. Longo, *Lectures on Conformal Nets, Part I*](https://www.mat.uniroma2.it/longo/Lecture-Notes_files/LN-Part1.pdf),
  §2.2
-/

@[expose] public section

open Set Filter Topology MeasureTheory Complex ClosedSubmodule
open scoped InnerProductSpace StandardSubspace Real

namespace AddChar.IsStronglyContinuous

variable {V H : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {T : AddChar V (unitary (H →L[ℂ] H))} (hT : T.IsStronglyContinuous)
  (K : StandardSubspace H)

/-! ### The translation cone -/

include hT in
/-- The **translation cone** of `K`: the closed convex cone of directions `a` with
`T(s a) K ⊆ K` for all `s ≥ 0`. Convexity comes from the group law, closedness from strong
continuity and the closedness of `K`. -/
noncomputable def translationCone : ProperCone ℝ V where
  carrier := {a | ∀ s : ℝ, 0 ≤ s → ∀ ξ ∈ K, (T (s • a) : H →L[ℂ] H) ξ ∈ K}
  zero_mem' s _ ξ hξ := by simpa using hξ
  add_mem' {a b} ha hb s hs ξ hξ := by
    rw [smul_add, ← T.apply_apply_unitary]
    exact ha s hs _ (hb s hs ξ hξ)
  smul_mem' c a ha s hs ξ hξ := by
    rw [show c • a = (c : ℝ) • a from rfl, smul_smul]
    exact ha _ (mul_nonneg hs c.2) ξ hξ
  isClosed' := by
    have : {a : V | ∀ s : ℝ, 0 ≤ s → ∀ ξ ∈ K, (T (s • a) : H →L[ℂ] H) ξ ∈ K} =
        ⋂ s ∈ Ici (0 : ℝ), ⋂ ξ ∈ (K : Set H),
          (fun a => (T (s • a) : H →L[ℂ] H) ξ) ⁻¹' (K : Set H) := by
      ext a
      simp
    rw [this]
    refine isClosed_biInter fun s _ => isClosed_biInter fun ξ _ =>
      K.toClosedSubmodule.isClosed.preimage ?_
    exact (isStronglyContinuous_iff.mp hT ξ).comp (continuous_const_smul s)

variable {K}

omit [IsTopologicalAddGroup V] in
/-- `a ∈ C_K` iff `T(s a) K ⊆ K` for all `s ≥ 0`. -/
lemma mem_translationCone {a : V} :
    a ∈ hT.translationCone K ↔ ∀ s : ℝ, 0 ≤ s → ∀ ξ ∈ K, (T (s • a) : H →L[ℂ] H) ξ ∈ K :=
  Iff.rfl

omit [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] in
/-- If a unitary `U` maps `K` into `K`, its adjoint `U⁻¹` maps `K'` into `K'`. -/
private lemma apply_neg_mem_symplComp {v : V} (hv : ∀ ξ ∈ K, (T v : H →L[ℂ] H) ξ ∈ K) {ξ : H}
    (hξ : ξ ∈ K.symplComp) : (T (-v) : H →L[ℂ] H) ξ ∈ K.symplComp := by
  refine mem_symplComp_iff.mpr fun η hη => ?_
  rw [← T.inner_apply_unitary_left]
  exact mem_symplComp_iff.mp hξ _ (hv η hη)

omit [IsTopologicalAddGroup V] in
/-- If `a ∈ C_K`, then `-a ∈ C_{K'}`. -/
lemma neg_mem_translationCone_symplComp {a : V} (ha : a ∈ hT.translationCone K) :
    -a ∈ hT.translationCone K.symplComp := fun s hs ξ hξ => by
  rw [smul_neg]
  exact apply_neg_mem_symplComp (ha s hs) hξ

/-! ### The boosted family -/

section Boost

variable [FiniteDimensional ℝ V] [T2Space V]

/-- On the closed upper half-plane, `|exp (i w max(λ, 0))| ≤ 1`. -/
private lemma norm_cexp_le_one {w : ℂ} (hw : 0 ≤ w.im) (l : ℝ) :
    ‖cexp (I * w * (max l 0 : ℝ))‖ ≤ 1 := by
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  have : (I * w * (max l 0 : ℝ)).re = -(w.im * max l 0) := by simp
  rw [this, neg_nonpos]
  exact mul_nonneg hw (le_max_right l 0)

/-- `e^{2πz}` maps the closed strip `0 ≤ im z ≤ 1/2` into the closed upper half-plane. -/
private lemma im_cexp_nonneg {z : ℂ} (hz : z ∈ im ⁻¹' Icc 0 (1 / 2)) :
    0 ≤ (cexp (2 * π * z)).im := by
  obtain ⟨h0, h1⟩ := hz
  rw [Complex.exp_im, show (2 * π * z : ℂ) = ((2 * π : ℝ) : ℂ) * z by push_cast; ring,
    im_ofReal_mul]
  exact mul_nonneg (Real.exp_pos _).le (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
    (by nlinarith [Real.pi_pos]))

/-- `e^{2πz}` maps the open strip `0 < im z < 1/2` into the open upper half-plane. -/
private lemma mapsTo_cexp :
    MapsTo (fun z : ℂ => cexp (2 * π * z)) (im ⁻¹' Ioo 0 (1 / 2)) (im ⁻¹' Ioi 0) := by
  intro z ⟨h0, h1⟩
  change 0 < (cexp (2 * π * z)).im
  rw [Complex.exp_im, show (2 * π * z : ℂ) = ((2 * π : ℝ) : ℂ) * z by push_cast; ring,
    im_ofReal_mul]
  exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi (by positivity)
    (by nlinarith [Real.pi_pos]))

/-- **The boosted family**: for `a` in the spectral cone, with positive generator `P` and
projection-valued measure `E`, the operators `W(z) = ∫ exp (i e^{2πz} max(λ, 0)) dE(λ)` have
holomorphic matrix coefficients on the strip `0 < im z < 1/2`, continuous up to the boundary, are
bounded by `1` there, and `W(t) = T(e^{2πt} a)`, `W(t + i/2) = T(-e^{2πt} a)`. -/
private lemma exists_boostFamily {a : V} (ha : a ∈ hT.spectralCone) :
    ∃ W : ℂ → H →L[ℂ] H,
      (∀ x y, DiffContOnCl ℂ (fun z => ⟪y, W z x⟫_ℂ) (im ⁻¹' Ioo 0 (1 / 2))) ∧
      BddAbove ((norm ∘ W) '' (im ⁻¹' Icc 0 (1 / 2))) ∧
      (∀ t : ℝ, W t = (T (Real.exp (2 * π * t) • a) : H →L[ℂ] H)) ∧
      ∀ t : ℝ, W (t + I / 2) = (T (-(Real.exp (2 * π * t) • a)) : H →L[ℂ] H) := by
  set hP := hT.isSelfAdjoint_selfAdjointGeneratorAlong a
  set E := hP.pvm
  have hpos := (hT.mem_spectralCone_iff_isPositive).mp ha
  have hE : ∀ y, ∀ᵐ l ∂(E.measure y), 0 ≤ l := fun y => hP.ae_nonneg_measure_pvm y hpos
  have hφ : Measurable fun l : ℝ => max l 0 := by fun_prop
  set f : ℂ → ℝ → ℂ := fun w l => cexp (I * w * (max l 0 : ℝ))
  have hfm : ∀ w, Measurable (f w) := fun w => by fun_prop
  have hfb : ∀ w : ℂ, 0 ≤ w.im → ∃ C, ∀ l, ‖f w l‖ ≤ C := fun w hw =>
    ⟨1, norm_cexp_le_one hw⟩
  have hreal : ∀ r : ℝ, E.integral (f r) = (T (r • a) : H →L[ℂ] H) := fun r => by
    rw [← hT.unitaryGroup_selfAdjointGeneratorAlong a r, IsSelfAdjoint.coe_unitaryGroup_apply]
    refine E.integral_congr_ae (hfm _) (by fun_prop) fun y => (hE y).mono fun l hl => ?_
    simp only [f, max_eq_left hl]
    ring_nf
  refine ⟨fun z => E.integral (f (cexp (2 * π * z))), fun x y => ?_, ⟨1, ?_⟩, fun t => ?_,
    fun t => ?_⟩
  · -- holomorphy of the matrix coefficients
    set G : ℂ → H := fun w => E.integralApply (f w) x
    have hG : DiffContOnCl ℂ G (im ⁻¹' Ioi 0) :=
      E.diffContOnCl_integralApply_cexp_of_nonneg hφ (ae_of_all _ fun l => le_max_right l 0)
    have hexp : DiffContOnCl ℂ (fun z : ℂ => cexp (2 * π * z)) (im ⁻¹' Ioo 0 (1 / 2)) :=
      (differentiable_exp.comp (differentiable_id.const_mul _)).diffContOnCl
    have hH := (innerSL ℂ y).differentiable.comp_diffContOnCl (hG.comp hexp mapsTo_cexp)
    have heq : EqOn (fun z => ⟪y, E.integral (f (cexp (2 * π * z))) x⟫_ℂ)
        ((innerSL ℂ y) ∘ (G ∘ fun z => cexp (2 * π * z))) (im ⁻¹' Icc 0 (1 / 2)) :=
      fun z hz => by
        simp only [Function.comp_apply, innerSL_apply_apply, G]
        rw [E.integral_apply (hfm _) (hfb _ (im_cexp_nonneg hz))]
    have hcl : closure (im ⁻¹' Ioo (0 : ℝ) (1 / 2)) = im ⁻¹' Icc 0 (1 / 2) := by
      rw [closure_preimage_im, closure_Ioo (by norm_num)]
    exact ⟨hH.differentiableOn.congr fun z hz => heq (Ioo_subset_Icc_self hz),
      hH.continuousOn.congr (hcl ▸ heq)⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact E.norm_integral_le (hfm _) (hfb _ (im_cexp_nonneg hz))
      (norm_cexp_le_one (im_cexp_nonneg hz)) zero_le_one
  · change E.integral (f (cexp (2 * π * t))) = _
    rw [show (2 * π * t : ℂ) = ((2 * π * t : ℝ) : ℂ) by push_cast; ring, ← ofReal_exp, hreal]
  · change E.integral (f (cexp (2 * π * (t + I / 2)))) = _
    have h : cexp (2 * π * (t + I / 2)) = ((-Real.exp (2 * π * t) : ℝ) : ℂ) := by
      rw [show (2 * π * (t + I / 2) : ℂ) = ((2 * π * t : ℝ) : ℂ) + π * I by push_cast; ring,
        Complex.exp_add, exp_pi_mul_I, ofReal_neg, ofReal_exp, mul_neg_one]
    rw [h, hreal, neg_smul]

end Boost

/-! ### Borchers' theorem -/

section Borchers

variable [FiniteDimensional ℝ V] [T2Space V] {a b z : V}

/-- Borchers' theorem for `s > 0`, from Theorem B applied to the boosted family at
`s' = log s / 2π`. -/
private lemma eq_of_pos (haK : a ∈ hT.translationCone K) (haC : a ∈ hT.spectralCone) {s : ℝ}
    (hs : 0 < s) :
    (∀ (t : ℝ) (x : H), Δ[K]^{i t} ((T (s • a) : H →L[ℂ] H) (Δ[K]^{i (-t)} x)) =
      (T ((Real.exp (-2 * π * t) * s) • a) : H →L[ℂ] H) x) ∧
    ∀ x, J[K] ((T (s • a) : H →L[ℂ] H) (J[K] x)) = (T (-(s • a)) : H →L[ℂ] H) x := by
  obtain ⟨W, hW, hB, hWt, hWt'⟩ := hT.exists_boostFamily haC
  have hK : ∀ t : ℝ, ∀ ξ ∈ K, W t ξ ∈ K := fun t ξ hξ => by
    rw [hWt]
    exact haK _ (Real.exp_pos _).le ξ hξ
  have hK' : ∀ t : ℝ, ∀ ξ ∈ K.symplComp, W (t + I / 2) ξ ∈ K.symplComp := fun t ξ hξ => by
    rw [hWt']
    exact apply_neg_mem_symplComp (haK _ (Real.exp_pos _).le) hξ
  set s' := Real.log s / (2 * π)
  have hs' : Real.exp (2 * π * s') = s := by
    rw [mul_div_cancel₀ _ (by positivity), Real.exp_log hs]
  refine ⟨fun t x => ?_, fun x => ?_⟩
  · have h := StandardSubspace.modularGroup_apply_eq_of_upperStrip hW hB hK hK' s' t x
    rw [hWt, hs', ← ofReal_sub, hWt] at h
    rw [h, show 2 * π * (s' - t) = -2 * π * t + 2 * π * s' by ring, Real.exp_add, hs']
  · have h := StandardSubspace.modularConj_apply_eq_of_upperStrip hW hB hK hK' s' x
    rwa [hWt, hs', hWt', hs'] at h

/-- **Borchers' theorem**, modular group (Borchers 1995, Theorem 4.1(b)): if `T(s a) K ⊆ K` for
`s ≥ 0` and `s ↦ T(s a)` has a positive generator, then `Δ^{it} T(s a) Δ^{-it} = T(e^{-2πt} s a)`
for all real `s` and `t`. -/
theorem modularGroup_mul_mul_eq_of_mem_spectralCone (haK : a ∈ hT.translationCone K)
    (haC : a ∈ hT.spectralCone) (s t : ℝ) :
    K.modularGroup t * T (s • a) * K.modularGroup (-t) = T ((Real.exp (-2 * π * t) * s) • a) := by
  have hpos : ∀ s : ℝ, 0 < s →
      K.modularGroup t * T (s • a) * K.modularGroup (-t) =
        T ((Real.exp (-2 * π * t) * s) • a) := fun s hs =>
    Subtype.ext <| ContinuousLinearMap.ext fun x => by
      simpa [mul_apply_eq_comp] using (eq_of_pos hT haK haC hs).1 t x
  rcases lt_trichotomy s 0 with hs | rfl | hs
  · have h := hpos (-s) (neg_pos.mpr hs)
    have e₁ : T (s • a) = (T ((-s) • a))⁻¹ := by
      rw [← AddChar.map_neg_eq_inv, neg_smul, neg_neg]
    have e₂ : T ((Real.exp (-2 * π * t) * s) • a) = (T ((Real.exp (-2 * π * t) * -s) • a))⁻¹ := by
      rw [← AddChar.map_neg_eq_inv, mul_neg, neg_smul, neg_neg]
    rw [e₁, e₂, ← h, AddChar.map_neg_eq_inv]
    group
  · simp [AddChar.map_neg_eq_inv]
  · exact hpos s hs

/-- **Borchers' theorem**, modular conjugation: if `T(s a) K ⊆ K` for `s ≥ 0` and `s ↦ T(s a)` has
a positive generator, then `J T(s a) J = T(-s a)` for all real `s`. -/
theorem modularConj_apply_eq_of_mem_spectralCone (haK : a ∈ hT.translationCone K)
    (haC : a ∈ hT.spectralCone) (s : ℝ) (x : H) :
    J[K] ((T (s • a) : H →L[ℂ] H) (J[K] x)) = (T (-(s • a)) : H →L[ℂ] H) x := by
  rcases lt_trichotomy s 0 with hs | rfl | hs
  · have h := (eq_of_pos hT haK haC (neg_pos.mpr hs)).2 (J[K] x)
    rw [StandardSubspace.modularConj_modularConj, show -((-s) • a) = s • a by
      rw [neg_smul, neg_neg]] at h
    rw [← h, StandardSubspace.modularConj_modularConj, neg_smul]
  · simp
  · exact (eq_of_pos hT haK haC hs).2 x

/-- **Borchers' theorem with a negative generator**, modular group: if `T(s b) K ⊆ K` for `s ≥ 0`
and `s ↦ T(s b)` has a negative generator, then `Δ^{it} T(s b) Δ^{-it} = T(e^{2πt} s b)`. It is the
positive case for `K'` and `-b`. -/
lemma modularGroup_mul_mul_eq_of_neg_mem_spectralCone (hbK : b ∈ hT.translationCone K)
    (hbC : -b ∈ hT.spectralCone) (s t : ℝ) :
    K.modularGroup t * T (s • b) * K.modularGroup (-t) = T ((Real.exp (2 * π * t) * s) • b) := by
  have h := hT.modularGroup_mul_mul_eq_of_mem_spectralCone
    (hT.neg_mem_translationCone_symplComp hbK) hbC (-s) (-t)
  have hK' : ∀ t, K.symplComp.modularGroup t = K.modularGroup (-t) := fun t =>
    Subtype.ext (K.modularGroup_symplComp t)
  have e₁ : (-s) • -b = s • b := by rw [smul_neg, neg_smul, neg_neg]
  have e₂ : (Real.exp (-2 * π * -t) * -s) • -b = (Real.exp (2 * π * t) * s) • b := by
    rw [show -2 * π * -t = 2 * π * t by ring, smul_neg, mul_neg, neg_smul, neg_neg]
  simp only [hK', neg_neg] at h
  rwa [e₁, e₂] at h

/-- **Borchers' theorem with a negative generator**, modular conjugation: if `T(s b) K ⊆ K` for
`s ≥ 0` and `s ↦ T(s b)` has a negative generator, then `J T(s b) J = T(-s b)`. -/
lemma modularConj_apply_eq_of_neg_mem_spectralCone (hbK : b ∈ hT.translationCone K)
    (hbC : -b ∈ hT.spectralCone) (s : ℝ) (x : H) :
    J[K] ((T (s • b) : H →L[ℂ] H) (J[K] x)) = (T (-(s • b)) : H →L[ℂ] H) x := by
  have h := hT.modularConj_apply_eq_of_mem_spectralCone
    (hT.neg_mem_translationCone_symplComp hbK) hbC (-s) x
  simp only [StandardSubspace.modularConj_symplComp, smul_neg, neg_smul, neg_neg] at h
  exact h

omit [IsTopologicalAddGroup V] [FiniteDimensional ℝ V] [T2Space V] in
/-- On the lineality space of `C_K` (`z` and `-z` in `C_K`), `T(s z) K = K` for every real `s`. -/
private lemma apply_mem_iff_of_neg_mem (hzK : z ∈ hT.translationCone K)
    (hzK' : -z ∈ hT.translationCone K) (s : ℝ) (ξ : H) :
    (T (s • z) : H →L[ℂ] H) ξ ∈ K ↔ ξ ∈ K := by
  have hmaps : ∀ r : ℝ, ∀ ξ ∈ K, (T (r • z) : H →L[ℂ] H) ξ ∈ K := fun r ξ hξ => by
    rcases le_total 0 r with hr | hr
    · exact hzK r hr ξ hξ
    · rw [show r • z = (-r) • -z by rw [smul_neg, neg_smul, neg_neg]]
      exact hzK' (-r) (neg_nonneg.mpr hr) ξ hξ
  refine ⟨fun h => ?_, hmaps s ξ⟩
  have := hmaps (-s) _ h
  rwa [show (-s) • z = -(s • z) by rw [neg_smul], T.apply_apply_unitary, neg_add_cancel,
    AddChar.map_zero_eq_one, OneMemClass.coe_one, one_apply_eq_self] at this

omit [IsTopologicalAddGroup V] [FiniteDimensional ℝ V] [T2Space V] in
/-- **Translations along the lineality space commute with the modular group**: if `z` and `-z`
lie in `C_K`, then `Δ^{it} T(s z) Δ^{-it} = T(s z)`. -/
lemma modularGroup_mul_mul_eq_of_neg_mem_translationCone (hzK : z ∈ hT.translationCone K)
    (hzK' : -z ∈ hT.translationCone K) (s t : ℝ) :
    K.modularGroup t * T (s • z) * K.modularGroup (-t) = T (s • z) := by
  have h : K.modularGroup t * T (s • z) = T (s • z) * K.modularGroup t :=
    Subtype.ext <| ContinuousLinearMap.ext fun x => by
      have h := StandardSubspace.modularGroup_map (Unitary.linearIsometryEquiv (T (s • z)))
        (hT.apply_mem_iff_of_neg_mem hzK hzK' s) t x
      simp only [Submonoid.coe_mul, mul_apply_eq_comp]
      exact h
  rw [h, AddChar.map_neg_eq_inv, mul_inv_cancel_right]

omit [IsTopologicalAddGroup V] [FiniteDimensional ℝ V] [T2Space V] in
/-- **Translations along the lineality space commute with the modular conjugation**: if `z` and
`-z` lie in `C_K`, then `J T(s z) J = T(s z)`. -/
lemma modularConj_apply_eq_of_neg_mem_translationCone (hzK : z ∈ hT.translationCone K)
    (hzK' : -z ∈ hT.translationCone K) (s : ℝ) (x : H) :
    J[K] ((T (s • z) : H →L[ℂ] H) (J[K] x)) = (T (s • z) : H →L[ℂ] H) x := by
  have h := StandardSubspace.modularConj_map (K₁ := K) (K₂ := K)
    (Unitary.linearIsometryEquiv (T (s • z))) (hT.apply_mem_iff_of_neg_mem hzK hzK' s) (J[K] x)
  rw [StandardSubspace.modularConj_modularConj] at h
  exact h

/-- **Borchers' theorem**, boost form: for `a ∈ C_K` with positive generator, `b ∈ C_K` with
negative generator and `z` in the lineality space of `C_K`, the modular group acts as a boost,
`Δ^{it} T(r a + s b + z) Δ^{-it} = T(e^{-2πt} r a + e^{2πt} s b + z)`. -/
theorem modularGroup_mul_mul_eq_boost (haK : a ∈ hT.translationCone K) (haC : a ∈ hT.spectralCone)
    (hbK : b ∈ hT.translationCone K) (hbC : -b ∈ hT.spectralCone) (hzK : z ∈ hT.translationCone K)
    (hzK' : -z ∈ hT.translationCone K) (r s t : ℝ) :
    K.modularGroup t * T (r • a + s • b + z) * K.modularGroup (-t) =
      T ((Real.exp (-2 * π * t) * r) • a + (Real.exp (2 * π * t) * s) • b + z) := by
  have hz := hT.modularGroup_mul_mul_eq_of_neg_mem_translationCone hzK hzK' 1 t
  rw [one_smul] at hz
  rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul,
    AddChar.map_add_eq_mul]
  conv_rhs => rw [← hT.modularGroup_mul_mul_eq_of_mem_spectralCone haK haC,
    ← hT.modularGroup_mul_mul_eq_of_neg_mem_spectralCone hbK hbC, ← hz]
  rw [AddChar.map_neg_eq_inv]
  group

/-- **Borchers' theorem**, boost form, modular conjugation: under the hypotheses of
`AddChar.IsStronglyContinuous.modularGroup_mul_mul_eq_boost`, the modular conjugation acts as the
reflection `J T(r a + s b + z) J = T(-r a - s b + z)`. -/
theorem modularConj_apply_eq_reflection (haK : a ∈ hT.translationCone K) (haC : a ∈ hT.spectralCone)
    (hbK : b ∈ hT.translationCone K) (hbC : -b ∈ hT.spectralCone) (hzK : z ∈ hT.translationCone K)
    (hzK' : -z ∈ hT.translationCone K) (r s : ℝ) (x : H) :
    J[K] ((T (r • a + s • b + z) : H →L[ℂ] H) (J[K] x)) =
      (T (-(r • a) - s • b + z) : H →L[ℂ] H) x := by
  have hz := hT.modularConj_apply_eq_of_neg_mem_translationCone hzK hzK' 1
  simp only [one_smul] at hz
  have hJ : ∀ y, J[K] (J[K] y) = y := StandardSubspace.modularConj_modularConj K
  rw [← T.apply_apply_unitary, ← T.apply_apply_unitary, ← hJ ((T z : H →L[ℂ] H) (J[K] x)),
    ← hJ ((T (s • b) : H →L[ℂ] H) (J[K] (J[K] ((T z : H →L[ℂ] H) (J[K] x))))), hz,
    hT.modularConj_apply_eq_of_neg_mem_spectralCone hbK hbC,
    hT.modularConj_apply_eq_of_mem_spectralCone haK haC, T.apply_apply_unitary,
    T.apply_apply_unitary, sub_eq_add_neg]

end Borchers

end AddChar.IsStronglyContinuous
