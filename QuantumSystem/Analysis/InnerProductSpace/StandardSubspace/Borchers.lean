/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.InnerProductSpace.StandardSubspace
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import QuantumSystem.Analysis.InnerProductSpace.StandardSubspace.Tomita
public import QuantumSystem.Analysis.SpectralTheory.Interpolation
public import QuantumSystem.ForMathlib.Analysis.Complex.Strip
public import QuantumSystem.ForMathlib.Analysis.Complex.WeakHolomorphic
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.StandardSubspace

/-!
# Borchers' Theorems A and B for standard subspaces

Let `K₁ ⊆ H₁` and `K₂ ⊆ H₂` be standard subspaces of complex Hilbert spaces, with modular
operators `Δ₁`, `Δ₂` and modular conjugations `J₁`, `J₂`.

## Theorem A

Let `V : H₁ →L[ℂ] H₂` be a bounded operator with `V K₁ ⊆ K₂`. **Borchers' Theorem A** (Borchers
1995, Theorem A) states that `V(t) = Δ₂^{-it} V Δ₁^{it}` extends to a family `V(z)` of bounded
operators on the strip `0 ≤ im z ≤ 1/2`, holomorphic in the operator norm in the interior and
`*`-strongly continuous on the closed strip, with `‖V(z)‖ ≤ ‖V‖` and `V(t + i/2) = J₂ V(t) J₁`
(`StandardSubspace.exists_modularGroup_continuation`). The proof: `V S₁ ⊆ S₂ V`
(`StandardSubspace.compPMap_tomita_le_of_apply_mem`), and Theorem A for semilinear operators in polar
decomposition form (`IsSelfAdjoint.exists_stripContinuation_polarIsometry`), for `Sᵢ = Jᵢ Δᵢ^{1/2}`,
continues `Δ₂^{-it} V Δ₁^{it}` to the strip, with boundary value `Δ₂^{-it} J₂† V J₁ Δ₁^{it}` on
`im z = 1/2`, where the antilinear adjoint `J₂†` is `J₂` (`StandardSubspace.adjointₛₗ_modularConj`);
here `J` commutes with `Δ^{it}`, and the modular operators are injective, so the imaginary powers
are the modular groups. Borchers states
the theorem for a unitary `V` on a single Hilbert space; here `V` is any bounded operator between
two Hilbert spaces.

## Theorem B

Let `W : ℂ → (H₁ →L[ℂ] H₂)` be a
family of operators, bounded on the strip `0 ≤ im z ≤ 1/2`, whose matrix coefficients
`z ↦ ⟪η, W z ξ⟫` are holomorphic on `0 < im z < 1/2` and continuous up to the boundary. If
`W(t) K₁ ⊆ K₂` and `W(t + i/2) K₁' ⊆ K₂'` for all real `t`, then **Borchers' Theorem B**
(Borchers 1995, Theorem B) states that

* `Δ₂^{it} W(s) Δ₁^{-it} = W(s - t)` (`StandardSubspace.modularGroup_apply_eq_of_upperStrip`), and
* `J₂ W(s) J₁ = W(s + i/2)` (`StandardSubspace.modularConj_apply_eq_of_upperStrip`).

Borchers states the theorem for a single Hilbert space, with `W` unitary on both boundary lines and
`‖W‖ ≤ 1`; neither unitarity nor the norm bound is needed, only boundedness. The hypotheses are
also only weak ones (holomorphy and continuity of the matrix coefficients), which suffices by
`Complex.differentiableOn_continuousLinearMap_of_inner` and `ContinuousOn.inner_apply_of_inner`.

The **lower-strip version** (`modularGroup_apply_eq_of_lowerStrip`,
`modularConj_apply_eq_of_lowerStrip`): if `W` lives on `-1/2 ≤ im z ≤ 0` with `W(t) K₁ ⊆ K₂` and
`W(t - i/2) K₁' ⊆ K₂'`, then `Δ₂^{it} W(s) Δ₁^{-it} = W(s + t)` and `J₂ W(s) J₁ = W(s - i/2)`. It is
Theorem B for `z ↦ W(z - i/2)` and the symplectic complements, using `Δ_{K'}^{it} = Δ_K^{-it}` and
`J_{K'} = J_K`; it is the form used for translations with negative generator.

The proof of Theorem B is not Borchers' original one but uses a single scalar function. For `ξ ∈ K₁` and
`η ∈ K₂`, the modular orbits continue analytically to the strip
(`StandardSubspace.exists_diffContOnCl_modularGroup`), with `Δ^{-i(t + i/2)} ξ = J Δ^{-it} ξ`, and
`F(z) = ⟪J₂ Δ₂^{-iz} η, W(s + z) Δ₁^{-iz} ξ⟫` is holomorphic and bounded on the strip (it is the
complex-bilinear form `(u, v) ↦ ⟪J₂ v, u⟫` evaluated on holomorphic functions). On `im z = 0`,
`F(t)` pairs `J₂ Δ₂^{-it} η ∈ K₂'` with `W(s + t) Δ₁^{-it} ξ ∈ K₂`, and on `im z = 1/2`, `F` pairs
`Δ₂^{-it} η ∈ K₂` with `W(s + t + i/2) J₁ Δ₁^{-it} ξ ∈ K₂'`, so `F` is real on both boundary
lines and hence constant (`eqOn_const_of_im_eq_zero_on_boundary`). Comparing `F(t)` and `F(i/2)`
with `F(0)` gives both identities on `K₁ × K₂`, and cyclicity of `K₁`, `K₁'`, `K₂`, `K₂'`
(`StandardSubspace.ext_continuousLinearMap`, `StandardSubspace.eq_zero_of_forall_inner_eq_zero`)
extends them to all vectors.

## Main results

* `StandardSubspace.exists_modularGroup_continuation` — Theorem A.
* `StandardSubspace.modularGroup_apply_eq_of_upperStrip`, `StandardSubspace.modularConj_apply_eq_of_upperStrip`
  — Theorem B.
* `StandardSubspace.modularGroup_apply_eq_of_lowerStrip`,
  `StandardSubspace.modularConj_apply_eq_of_lowerStrip` — Theorem B on the lower strip.

## TODO

* The converse of Theorem A (an operator `V` with such a continuation maps `K₁` into `K₂`), and the
  half-sided modular inclusions built on it (Borchers 1995, Theorem 4.1(a); Wiesbrock).

The von Neumann algebra versions, including Theorem A for relative modular operators, are in
`QuantumSystem.Analysis.VonNeumannAlgebra.Modular.Borchers`, and Borchers' theorem on half-sided
translations is `QuantumSystem.Analysis.InnerProductSpace.StandardSubspace.BorchersTranslation`.

## References

* H.-J. Borchers, *On the use of modular groups in quantum field theory*, Ann. Inst. H. Poincaré
  Phys. Théor. 63 (1995), 331–382, Theorems A and B
-/

@[expose] public section

open Set Filter Topology Complex ClosedSubmodule
open scoped InnerProductSpace ComplexConjugate InnerProduct

namespace StandardSubspace

variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
  {K₁ : StandardSubspace H₁} {K₂ : StandardSubspace H₂} {W : ℂ → H₁ →L[ℂ] H₂}

/-! ### Theorem A -/

/-- **Borchers' Theorem A**: if `V K₁ ⊆ K₂`, then `t ↦ Δ₂^{-it} V Δ₁^{it}` extends to a bounded
family `V(z)` on the strip `0 ≤ im z ≤ 1/2`, holomorphic in the operator norm in the interior,
`*`-strongly continuous on the closed strip, with `‖V(z)‖ ≤ ‖V‖` and `V(t + i/2) = J₂ V(t) J₁`. -/
theorem exists_modularGroup_continuation (V : H₁ →L[ℂ] H₂)
    (hV : ∀ ξ ∈ K₁, V ξ ∈ K₂) :
    ∃ F : ℂ → H₁ →L[ℂ] H₂, DifferentiableOn ℂ F (im ⁻¹' Ioo 0 (1 / 2)) ∧
      (∀ x, ContinuousOn (fun z => F z x) (im ⁻¹' Icc 0 (1 / 2))) ∧
      (∀ y, ContinuousOn (fun z => ((F z)†) y) (im ⁻¹' Icc 0 (1 / 2))) ∧
      (∀ z ∈ im ⁻¹' Icc 0 (1 / 2), ‖F z‖ ≤ ‖V‖) ∧
      (∀ t : ℝ, F t = Δ[K₂]^{-i t} ∘L V ∘L Δ[K₁]^{i t}) ∧
      ∀ (t : ℝ) (x : H₁), F (t + I / 2) x = J[K₂] (F t (J[K₁] x)) := by
  obtain ⟨F, hFd, hFs, hFs', hFb, hF0, hF1⟩ :=
    K₁.isSelfAdjoint_modular.exists_stripContinuation_polarIsometry K₂.isSelfAdjoint_modular
      K₁.modular_def K₂.modular_def K₁.isClosed_tomita K₂.isClosed_tomita V
      (compPMap_tomita_le_of_apply_mem V hV)
  refine ⟨F, hFd, hFs, hFs', hFb, hF0, fun t x => ?_⟩
  rw [hF1, hF0]
  change Δ[K₂]^{-i t} ((J[K₂] : H₂ →L⋆[ℂ] H₂).adjointₛₗ (V (J[K₁] (Δ[K₁]^{i t} x)))) =
    J[K₂] (Δ[K₂]^{-i t} (V (Δ[K₁]^{i t} (J[K₁] x))))
  rw [K₂.adjointₛₗ_modularConj]
  change Δ[K₂]^{-i t} (J[K₂] (V (J[K₁] (Δ[K₁]^{i t} x)))) =
    J[K₂] (Δ[K₂]^{-i t} (V (Δ[K₁]^{i t} (J[K₁] x))))
  rw [K₁.modularConj_comm_modularGroup, K₂.modularConj_comm_modularGroup]

/-! ### Theorem B on the upper strip -/

section UpperStrip

variable (hW : ∀ x y, DiffContOnCl ℂ (fun z => ⟪y, W z x⟫_ℂ) (im ⁻¹' Ioo 0 (1 / 2)))
  (hB : BddAbove ((norm ∘ W) '' (im ⁻¹' Icc 0 (1 / 2))))
  (hK : ∀ t : ℝ, ∀ ξ ∈ K₁, W t ξ ∈ K₂)
  (hK' : ∀ t : ℝ, ∀ ξ ∈ K₁.symplComp,
    W (t + I / 2) ξ ∈ K₂.symplComp)
include hW hB hK hK'

/-- The auxiliary function of Theorem B: for `ξ ∈ K₁` and `η ∈ K₂`, the function
`z ↦ ⟪J₂ Δ₂^{-iz} η, W(s + z) Δ₁^{-iz} ξ⟫` is holomorphic and bounded on the strip
`0 < im z < 1/2` and real on both boundary lines, hence constant. Its values at `t`, `i/2` and `0`
give the three identities below. -/
private lemma inner_eq_aux (s : ℝ) {ξ : H₁} (hξ : ξ ∈ K₁) {η : H₂}
    (hη : η ∈ K₂) :
    (∀ t : ℝ, ⟪J[K₂] (Δ[K₂]^{-i t} η),
        W (s + t) (Δ[K₁]^{-i t} ξ)⟫_ℂ =
      ⟪J[K₂] η, W s ξ⟫_ℂ) ∧
    ⟪η, W (s + I / 2) (J[K₁] ξ)⟫_ℂ = ⟪J[K₂] η, W s ξ⟫_ℂ ∧
    (⟪J[K₂] η, W s ξ⟫_ℂ).im = 0 := by
  obtain ⟨a, ha, ⟨Ca, hCa⟩, ha0, ha1, -⟩ := K₁.exists_diffContOnCl_modularGroup hξ
  obtain ⟨b, hb, ⟨Cb, hCb⟩, hb0, hb1, -⟩ := K₂.exists_diffContOnCl_modularGroup hη
  obtain ⟨C, hC⟩ := hB
  have hU : IsOpen (im ⁻¹' Ioo (0 : ℝ) (1 / 2)) := isOpen_Ioo.preimage continuous_im
  have hcl : closure (im ⁻¹' Ioo (0 : ℝ) (1 / 2)) = im ⁻¹' Icc 0 (1 / 2) :=
    closure_preimage_im_Ioo (by norm_num)
  have hshift : ∀ {S : Set ℝ} {z : ℂ}, z ∈ im ⁻¹' S → (s + z : ℂ) ∈ im ⁻¹' S := fun hz => by
    simpa using hz
  have hWC : ∀ z ∈ im ⁻¹' Icc (0 : ℝ) (1 / 2), ‖W (s + z)‖ ≤ C := fun z hz =>
    hC ⟨_, hshift hz, rfl⟩
  -- `z ↦ W (s + z)` is holomorphic in the operator norm
  have hWd : DifferentiableOn ℂ (fun z => W (s + z)) (im ⁻¹' Ioo 0 (1 / 2)) := by
    exact Complex.differentiableOn_continuousLinearMap_of_inner hU fun x y =>
      (hW x y).differentiableOn.comp (differentiableOn_const _ |>.add differentiableOn_id)
        fun w hw => hshift hw
  set F : ℂ → ℂ := fun z => ⟪J[K₂] (b z), W (s + z) (a z)⟫_ℂ
  -- `F` is the bilinear form `(u, v) ↦ ⟪J₂ u, v⟫` evaluated on holomorphic functions
  let L : H₂ →L[ℂ] H₂ →L[ℂ] ℂ :=
    (innerSL ℂ (E := H₂)).comp J[K₂].toLinearIsometry.toContinuousLinearMap
  have hFL : F = fun z => L (W (s + z) (a z)) (b z) := funext fun z => by
    simp only [F, L, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry, innerSL_apply_apply]
    exact K₂.inner_modularConj_left _ _
  have hFd : DiffContOnCl ℂ F (im ⁻¹' Ioo 0 (1 / 2)) := by
    refine ⟨?_, ?_⟩
    · rw [hFL]
      exact (L.differentiable.comp_differentiableOn (hWd.clm_apply ha.differentiableOn)).clm_apply
        hb.differentiableOn
    · rw [hcl]
      refine ContinuousOn.inner_apply_of_inner (C := C) (fun x y => ?_) hWC
        (hcl ▸ ha.continuousOn) (J[K₂].continuous.comp_continuousOn (hcl ▸ hb.continuousOn))
      exact (hcl ▸ (hW x y).continuousOn).comp (continuousOn_const.add continuousOn_id)
        fun w hw => hshift hw
  have hFB : BddAbove ((norm ∘ F) '' (im ⁻¹' Icc 0 (1 / 2))) := by
    refine ⟨Cb * (C * Ca), ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have hCz : 0 ≤ C := (norm_nonneg _).trans (hWC z hz)
    calc ‖F z‖ ≤ ‖J[K₂] (b z)‖ * ‖W (s + z) (a z)‖ := norm_inner_le_norm _ _
      _ ≤ Cb * (C * Ca) := by
        rw [LinearIsometryEquiv.norm_map]
        exact mul_le_mul (hCb ⟨z, hz, rfl⟩) (((W (s + z)).le_opNorm _).trans
          (mul_le_mul (hWC z hz) (hCa ⟨z, hz, rfl⟩) (norm_nonneg _) hCz))
          (norm_nonneg _) ((norm_nonneg _).trans (hCb ⟨z, hz, rfl⟩))
  -- the boundary values
  have hFt : ∀ t : ℝ, F t = ⟪J[K₂] (Δ[K₂]^{-i t} η),
      W (s + t) (Δ[K₁]^{-i t} ξ)⟫_ℂ := fun t => by
    simp only [F, ha0, hb0]
  have hFt' : ∀ t : ℝ, F (t + I / 2) = ⟪Δ[K₂]^{-i t} η,
      W (s + t + I / 2) (J[K₁] (Δ[K₁]^{-i t} ξ))⟫_ℂ := fun t => by
    simp only [F, ha1, hb1, modularConj_modularConj, add_assoc]
  have hre : ∀ z : ℂ, z.im = 0 → z = (z.re : ℂ) := fun z hz => Complex.ext (by simp) (by simp [hz])
  have hre' : ∀ z : ℂ, z.im = 1 / 2 → z = (z.re : ℂ) + I / 2 := fun z hz =>
    Complex.ext (by simp) (by simp [hz])
  have hF0 : ∀ z : ℂ, z.im = 0 → (F z).im = 0 := fun z hz => by
    rw [hre z hz, hFt, ← inner_conj_symm, conj_im, neg_eq_zero]
    refine mem_symplComp_iff.mp (K₂.modularConj_mem_symplComp_iff.mpr
      (K₂.modularGroup_apply_mem hη _)) _ ?_
    rw [← ofReal_add]
    exact hK _ _ (K₁.modularGroup_apply_mem hξ _)
  have hF1 : ∀ z : ℂ, z.im = 1 / 2 → (F z).im = 0 := fun z hz => by
    rw [hre' z hz, hFt']
    refine mem_symplComp_iff.mp ?_ _ (K₂.modularGroup_apply_mem hη _)
    rw [← ofReal_add]
    exact hK' _ _ (K₁.modularConj_mem_symplComp_iff.mpr (K₁.modularGroup_apply_mem hξ _))
  have hconst := eqOn_const_of_im_eq_zero_on_boundary (w := 0) (by norm_num) hFd hFB hF0 hF1
    (by simp)
  have hF00 : F 0 = ⟪J[K₂] η, W s ξ⟫_ℂ := by
    have := hFt 0
    simp only [ofReal_zero, neg_zero, modularGroupOp_zero, one_apply_eq_self, add_zero] at this
    exact this
  refine ⟨fun t => ?_, ?_, ?_⟩
  · rw [← hFt, ← hF00]
    exact hconst (by simp)
  · have h := hFt' 0
    simp only [ofReal_zero, neg_zero, modularGroupOp_zero, one_apply_eq_self, add_zero, zero_add] at h
    rw [← h, ← hF00]
    exact hconst (by simp)
  · rw [← hF00]
    exact hF0 0 (by simp)

/-- **Borchers' Theorem B**, modular group: `Δ₂^{it} W(s) Δ₁^{-it} = W(s - t)`. -/
theorem modularGroup_apply_eq_of_upperStrip (s t : ℝ) (x : H₁) :
    Δ[K₂]^{i t} (W s (Δ[K₁]^{-i t} x)) =
      W (s - t) x := by
  let D : H₁ →L[ℂ] H₂ := Δ[K₂]^{i t} ∘L W s ∘L
    Δ[K₁]^{-i t} - W (s - t)
  suffices hD : D = 0 by
    have := congrArg (fun f : H₁ →L[ℂ] H₂ => f x) hD
    simpa [D, sub_eq_zero] using this
  refine K₁.ext_continuousLinearMap fun ξ hξ => ?_
  refine K₂.symplComp.eq_zero_of_forall_inner_eq_zero fun y hy => ?_
  have h := (inner_eq_aux hW hB hK hK' (s - t) hξ (K₂.modularConj_mem_of_mem_symplComp hy)).1 t
  rw [modularConj_modularConj, K₂.modularConj_comm_modularGroup, modularConj_modularConj,
    inner_modularGroup_neg_left] at h
  rw [show ((s - t : ℝ) : ℂ) + t = s by push_cast; ring, ofReal_sub] at h
  simp only [D, sub_apply, ContinuousLinearMap.comp_apply, inner_sub_right]
  rw [sub_eq_zero, h]

/-- **Borchers' Theorem B**, modular conjugation: `J₂ W(s) J₁ = W(s + i/2)`. -/
theorem modularConj_apply_eq_of_upperStrip (s : ℝ) (x : H₁) :
    J[K₂] (W s (J[K₁] x)) = W (s + I / 2) x := by
  let J₁ : H₁ →L⋆[ℂ] H₁ := J[K₁].toLinearIsometry.toContinuousLinearMap
  let J₂ : H₂ →L⋆[ℂ] H₂ := J[K₂].toLinearIsometry.toContinuousLinearMap
  let D : H₁ →L[ℂ] H₂ := W (s + I / 2) - (J₂.comp ((W s).comp J₁) : H₁ →L[ℂ] H₂)
  suffices hD : D = 0 by
    have := congrArg (fun f : H₁ →L[ℂ] H₂ => f x) hD
    simp only [D, J₁, J₂, sub_apply, ContinuousLinearMap.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
      zero_apply] at this
    exact (sub_eq_zero.mp this).symm
  refine K₁.symplComp.ext_continuousLinearMap fun ξ hξ => ?_
  refine K₂.eq_zero_of_forall_inner_eq_zero fun η hη => ?_
  obtain ⟨-, h₂, h₃⟩ :=
    inner_eq_aux hW hB hK hK' s (K₁.modularConj_mem_of_mem_symplComp hξ) hη
  rw [modularConj_modularConj] at h₂
  have h₄ : ⟪η, J[K₂] (W s (J[K₁] ξ))⟫_ℂ =
      ⟪J[K₂] η, W s (J[K₁] ξ)⟫_ℂ := by
    rw [← inner_conj_symm, K₂.inner_modularConj_left (W s (J[K₁] ξ)) η]
    exact Complex.conj_eq_iff_im.mpr h₃
  simp only [D, J₁, J₂, sub_apply, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    inner_sub_right]
  rw [h₂, h₄, sub_self]

end UpperStrip

/-! ### Theorem B on the lower strip -/

section LowerStrip

variable (hW : ∀ x y, DiffContOnCl ℂ (fun z => ⟪y, W z x⟫_ℂ) (im ⁻¹' Ioo (-(1 / 2)) 0))
  (hB : BddAbove ((norm ∘ W) '' (im ⁻¹' Icc (-(1 / 2)) 0)))
  (hK : ∀ t : ℝ, ∀ ξ ∈ K₁, W t ξ ∈ K₂)
  (hK' : ∀ t : ℝ, ∀ ξ ∈ K₁.symplComp,
    W (t - I / 2) ξ ∈ K₂.symplComp)
include hW hB hK hK'

/-- The lower strip reduces to the upper one: `z ↦ W (z - i/2)` satisfies the hypotheses of
Theorem B for the symplectic complements `K₁'` and `K₂'`. -/
private lemma upper_of_lower :
    (∀ x y, DiffContOnCl ℂ (fun z => ⟪y, W (z - I / 2) x⟫_ℂ) (im ⁻¹' Ioo 0 (1 / 2))) ∧
    BddAbove ((norm ∘ fun z => W (z - I / 2)) '' (im ⁻¹' Icc 0 (1 / 2))) ∧
    (∀ t : ℝ, ∀ ξ ∈ K₁.symplComp,
      W (t - I / 2) ξ ∈ K₂.symplComp) ∧
    (∀ t : ℝ, ∀ ξ ∈ K₁.symplComp.symplComp,
      W (t + I / 2 - I / 2) ξ ∈ K₂.symplComp.symplComp) := by
  have hmaps : ∀ {a b : ℝ}, MapsTo (fun z : ℂ => z - I / 2) (im ⁻¹' Icc a b)
      (im ⁻¹' Icc (a - 1 / 2) (b - 1 / 2)) := @fun a b z hz => by
    simp only [mem_preimage, mem_Icc, sub_im, div_ofNat_im, I_im] at hz ⊢
    constructor <;> linarith [hz.1, hz.2]
  refine ⟨fun x y => (hW x y).comp ((differentiable_id.sub_const _).diffContOnCl) fun z hz => ?_,
    hB.mono ?_, hK', fun t ξ hξ => ?_⟩
  · simp only [mem_preimage, mem_Ioo, sub_im, div_ofNat_im, I_im] at hz ⊢
    constructor <;> linarith [hz.1, hz.2]
  · rintro _ ⟨z, hz, rfl⟩
    refine ⟨z - I / 2, ?_, rfl⟩
    have := hmaps hz
    norm_num at this ⊢
    exact this
  · rw [symplComp_symplComp_eq] at hξ ⊢
    rw [add_sub_cancel_right]
    exact hK t ξ hξ

/-- **Borchers' Theorem B on the lower strip**, modular conjugation: `J₂ W(s) J₁ = W(s - i/2)`. -/
lemma modularConj_apply_eq_of_lowerStrip (s : ℝ) (x : H₁) :
    J[K₂] (W s (J[K₁] x)) = W (s - I / 2) x := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := upper_of_lower hW hB hK hK'
  have h := modularConj_apply_eq_of_upperStrip (W := fun z => W (z - I / 2)) h₁ h₂ h₃ h₄ s
    (J[K₁] x)
  simp only [modularConj_symplComp, modularConj_modularConj, add_sub_cancel_right] at h
  rw [← h, modularConj_modularConj]

/-- **Borchers' Theorem B on the lower strip**, modular group: `Δ₂^{it} W(s) Δ₁^{-it} = W(s + t)`.
-/
lemma modularGroup_apply_eq_of_lowerStrip (s t : ℝ) (x : H₁) :
    Δ[K₂]^{i t} (W s (Δ[K₁]^{-i t} x)) =
      W (s + t) x := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := upper_of_lower hW hB hK hK'
  have h := modularGroup_apply_eq_of_upperStrip (W := fun z => W (z - I / 2)) h₁ h₂ h₃ h₄ s (-t)
    (J[K₁] x)
  simp only [modularGroup_symplComp, neg_neg, ofReal_neg, sub_neg_eq_add] at h
  -- `W(r) = J₂ W(r - i/2) J₁`
  have hW' : ∀ (r : ℝ) (y : H₁), W r y = J[K₂] (W (r - I / 2) (J[K₁] y)) :=
    fun r y => by
      have := modularConj_apply_eq_of_lowerStrip hW hB hK hK' r (J[K₁] y)
      rw [modularConj_modularConj] at this
      rw [← this, modularConj_modularConj]
  have hst := hW' (s + t) x
  push_cast at hst
  rw [hW' s, K₁.modularConj_comm_modularGroup, ← K₂.modularConj_comm_modularGroup, h, hst]

end LowerStrip

end StandardSubspace
