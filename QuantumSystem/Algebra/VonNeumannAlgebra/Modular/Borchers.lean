/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Algebra.VonNeumannAlgebra.Modular.TomitaAdjoint
public import QuantumSystem.Analysis.StandardSubspace.Borchers
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Borchers' Theorems A and B for von Neumann algebras

Let `Ω₁`, `Ω₂` be cyclic and separating for von Neumann algebras `M₁` on `H₁` and `M₂` on `H₂`,
with modular groups `Δ₁^{it}`, `Δ₂^{it}` and modular conjugations `J₁`, `J₂`: those of the
standard subspaces `H_{M₁}`, `H_{M₂}` (`VonNeumannAlgebra.standardSubspace`). Borchers' theorems
for standard subspaces (`QuantumSystem.Analysis.StandardSubspace.Borchers`) give the von Neumann
algebra versions, since a bounded `V` with `V† Ω₂ = Ω₁` and `V M₁ V† ⊆ M₂` maps `H_{M₁}` into
`H_{M₂}` (`VonNeumannAlgebra.apply_mem_standardSubspace_of_adjoint_apply`) and the symplectic
complement of `H_M` is `H_{M′}` (`VonNeumannAlgebra.standardSubspace_commutant_eq_symplComp`).
For a unitary `V` the conditions read `V Ω₁ = Ω₂` and `V M₁ V⋆ ⊆ M₂`, Borchers' hypotheses.

* **Theorem A** (`VonNeumannAlgebra.exists_modularGroup_continuation`): for such a `V`,
  `V(t) = Δ₂^{-it} V Δ₁^{it}` continues to the strip `0 ≤ im z ≤ 1/2`, holomorphic in the interior
  and weakly continuous up to the boundary, with `‖V(z)‖ ≤ ‖V‖` and `V(t + i/2) = J₂ V(t) J₁`.
* **Theorem B** (`VonNeumannAlgebra.modularGroup_apply_eq_of_upperStrip`,
  `VonNeumannAlgebra.modularConj_apply_eq_of_upperStrip`): let `W(z)` be bounded on the strip with
  holomorphic matrix coefficients, continuous up to the boundary, such that `W(t)† Ω₂ = Ω₁`,
  `W(t) M₁ W(t)† ⊆ M₂` and `W(t + i/2) M₁′ W(t + i/2)† ⊆ M₂′`. Then
  `Δ₂^{it} W(s) Δ₁^{-it} = W(s - t)` and `J₂ W(s) J₁ = W(s + i/2)`. No unitarity is assumed;
  `W(t + i/2)† Ω₂ = Ω₁` on the upper boundary follows from the real line, since a bounded
  holomorphic function on the strip vanishing on one boundary line vanishes
  (`Complex.eqOn_zero_of_eqOn_zero_im_eq_lower`).

Borchers (1995) states both theorems for unitaries on one Hilbert space with `Ω₁ = Ω₂`.

## Main results

* `VonNeumannAlgebra.exists_modularGroup_continuation` — **Borchers' Theorem A**.
* `VonNeumannAlgebra.modularGroup_apply_eq_of_upperStrip`,
  `VonNeumannAlgebra.modularConj_apply_eq_of_upperStrip` — **Borchers' Theorem B**.

## TODO

* Theorem A: the boundary values are attained `*`-strongly (Borchers); only weak continuity up to
  the boundary is proved, as in the standard subspace version
  (`QuantumSystem.Analysis.StandardSubspace.Borchers`).
* Versions for pairs of vectors, with the relative modular operators of Araki and Araki–Masuda in
  place of `Δ_{H_M}`; they need `S_{η,ξ}† = F̄_{η,ξ}` beyond the case of
  `QuantumSystem.Algebra.VonNeumannAlgebra.Modular.TomitaAdjoint`.

## References

* H.-J. Borchers, *On the use of modular groups in quantum field theory*,
  Ann. Inst. H. Poincaré Phys. Théor. 63 (1995), 331–382, Theorems A and B
* H. Araki, T. Masuda, *Positive cones and Lp-spaces for von Neumann algebras*, Publ. RIMS 18
  (1982), 339–411, §2
-/

@[expose] public section

open InnerProductSpace (IsCyclicVector IsSeparatingVector)

open Set Complex
open scoped InnerProductSpace VonNeumannAlgebra StandardSubspace InnerProduct

namespace VonNeumannAlgebra

variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
  {M₁ : VonNeumannAlgebra H₁} {M₂ : VonNeumannAlgebra H₂} {Ω₁ : H₁} {Ω₂ : H₂}
  (hc₁ : IsCyclicVector M₁ Ω₁) (hs₁ : IsSeparatingVector M₁ Ω₁)
  (hc₂ : IsCyclicVector M₂ Ω₂) (hs₂ : IsSeparatingVector M₂ Ω₂)

/-! ### Theorem A -/

/-- **Borchers' Theorem A** for von Neumann algebras (Borchers 1995, Theorem A): let `Ω₁`, `Ω₂` be
cyclic and separating for `M₁`, `M₂`, with modular groups `Δ₁^{it}`, `Δ₂^{it}` and modular
conjugations `J₁`, `J₂`, and let `V` be bounded with `V† Ω₂ = Ω₁` and `V M₁ V† ⊆ M₂` (for a
unitary `V`: `V Ω₁ = Ω₂` and `V M₁ V⋆ ⊆ M₂`). Then `V(t) = Δ₂^{-it} V Δ₁^{it}` extends to the strip
`0 ≤ im z ≤ 1/2`, holomorphic in the operator norm in the interior and weakly continuous up to the
boundary, with `‖V(z)‖ ≤ ‖V‖` and `V(t + i/2) = J₂ V(t) J₁`. -/
theorem exists_modularGroup_continuation {V : H₁ →L[ℂ] H₂}
    (hVΩ : (V†) Ω₂ = Ω₁)
    (hVM : ∀ x ∈ M₁, V ∘L x ∘L V† ∈ M₂) :
    ∃ F : ℂ → H₁ →L[ℂ] H₂, DifferentiableOn ℂ F (im ⁻¹' Ioo 0 (1 / 2)) ∧
      (∀ x y, DiffContOnCl ℂ (fun z => ⟪y, F z x⟫_ℂ) (im ⁻¹' Ioo 0 (1 / 2))) ∧
      (∀ z ∈ im ⁻¹' Icc 0 (1 / 2), ‖F z‖ ≤ ‖V‖) ∧
      (∀ t : ℝ, F t = Δ[H[M₂, Ω₂]]^{i (-t)} ∘L V ∘L
        Δ[H[M₁, Ω₁]]^{i t}) ∧
      ∀ (t : ℝ) (x : H₁), F (t + I / 2) x =
        J[H[M₂, Ω₂]] (F t (J[H[M₁, Ω₁]] x)) :=
  StandardSubspace.exists_modularGroup_continuation
    (K₁ := H[M₁, Ω₁]) (K₂ := H[M₂, Ω₂]) V
    fun _ hξ => apply_mem_standardSubspace_of_adjoint_apply hc₁ hs₁ hc₂ hs₂ hVΩ hVM hξ

/-! ### Theorem B -/

section TheoremB

variable {W : ℂ → H₁ →L[ℂ] H₂}
  (hW : ∀ x y, DiffContOnCl ℂ (fun z => ⟪y, W z x⟫_ℂ) (im ⁻¹' Ioo 0 (1 / 2)))
  (hB : BddAbove ((norm ∘ W) '' (im ⁻¹' Icc 0 (1 / 2))))
  (hΩ : ∀ t : ℝ, ((W t)†) Ω₂ = Ω₁)
  (hM : ∀ t : ℝ, ∀ x ∈ M₁, W t ∘L x ∘L (W t)† ∈ M₂)
  (hM' : ∀ t : ℝ, ∀ x ∈ M₁′,
    W (t + I / 2) ∘L x ∘L (W (t + I / 2))† ∈ M₂′)

include hW hB hΩ in
/-- `W(t + i/2)† Ω₂ = Ω₁`: the function `z ↦ ⟪Ω₂, W(z) y⟫ - ⟪Ω₁, y⟫` is bounded and holomorphic on
the strip and vanishes on the real line, hence vanishes on the closed strip. -/
private lemma adjoint_apply_add_half_I_eq (t : ℝ) :
    ((W (t + I / 2))†) Ω₂ = Ω₁ := by
  obtain ⟨C, hC⟩ := hB
  refine ext_inner_right ℂ fun y => ?_
  rw [ContinuousLinearMap.adjoint_inner_left]
  refine sub_eq_zero.mp ?_
  have hzero := Complex.eqOn_zero_of_eqOn_zero_im_eq_lower
    (f := fun z => ⟪Ω₂, W z y⟫_ℂ - ⟪Ω₁, y⟫_ℂ) ((hW y Ω₂).sub_const _)
    ⟨‖Ω₂‖ * C * ‖y‖ + ‖Ω₁‖ * ‖y‖, by
      rintro _ ⟨z, hz, rfl⟩
      have hWz : ‖W z‖ ≤ C := hC ⟨z, hz, rfl⟩
      refine (norm_sub_le _ _).trans (add_le_add ?_ (norm_inner_le_norm _ _))
      calc ‖⟪Ω₂, W z y⟫_ℂ‖ ≤ ‖Ω₂‖ * ‖W z y‖ := norm_inner_le_norm _ _
        _ ≤ ‖Ω₂‖ * (C * ‖y‖) := by
          gcongr
          exact (W z).le_of_opNorm_le hWz y
        _ = ‖Ω₂‖ * C * ‖y‖ := by ring⟩
    (fun z hz => by
      have : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hz])
      change ⟪Ω₂, W z y⟫_ℂ - ⟪Ω₁, y⟫_ℂ = 0
      rw [this, ← ContinuousLinearMap.adjoint_inner_left, hΩ, sub_self])
    (show t + I / 2 ∈ im ⁻¹' Icc 0 (1 / 2) by simp)
  simpa using hzero

include hc₁ hs₁ hc₂ hs₂ hW hB hΩ hM hM' in
/-- The hypotheses of the standard subspace Theorem B hold for `H_{M₁}` and `H_{M₂}`. -/
private lemma mem_standardSubspace_of_hyp :
    (∀ t : ℝ, ∀ ξ ∈ H[M₁, Ω₁], W t ξ ∈ H[M₂, Ω₂]) ∧
    (∀ t : ℝ, ∀ ξ ∈ H[M₁, Ω₁].symplComp,
      W (t + I / 2) ξ ∈ H[M₂, Ω₂].symplComp) := by
  refine ⟨fun t ξ hξ => apply_mem_standardSubspace_of_adjoint_apply hc₁ hs₁ hc₂ hs₂ (hΩ t)
    (hM t) hξ, fun t ξ hξ => ?_⟩
  rw [← standardSubspace_commutant_eq_symplComp hc₁ hs₁] at hξ
  rw [← standardSubspace_commutant_eq_symplComp hc₂ hs₂]
  exact apply_mem_standardSubspace_of_adjoint_apply _ _ _ _
    (adjoint_apply_add_half_I_eq hW hB hΩ t) (hM' t) hξ

include hc₁ hs₁ hc₂ hs₂ hW hB hΩ hM hM' in
/-- **Borchers' Theorem B** for von Neumann algebras (Borchers 1995, Theorem B), modular group:
`Δ₂^{it} W(s) Δ₁^{-it} = W(s - t)`. -/
theorem modularGroup_apply_eq_of_upperStrip (s t : ℝ) (x : H₁) :
    Δ[H[M₂, Ω₂]]^{i t} (W s (Δ[H[M₁, Ω₁]]^{i (-t)} x)) =
      W (s - t) x :=
  have h := mem_standardSubspace_of_hyp hc₁ hs₁ hc₂ hs₂ hW hB hΩ hM hM'
  StandardSubspace.modularGroup_apply_eq_of_upperStrip hW hB h.1 h.2 s t x

include hc₁ hs₁ hc₂ hs₂ hW hB hΩ hM hM' in
/-- **Borchers' Theorem B** for von Neumann algebras, modular conjugation:
`J₂ W(s) J₁ = W(s + i/2)`. -/
theorem modularConj_apply_eq_of_upperStrip (s : ℝ) (x : H₁) :
    J[H[M₂, Ω₂]] (W s (J[H[M₁, Ω₁]] x)) =
      W (s + I / 2) x :=
  have h := mem_standardSubspace_of_hyp hc₁ hs₁ hc₂ hs₂ hW hB hΩ hM hM'
  StandardSubspace.modularConj_apply_eq_of_upperStrip hW hB h.1 h.2 s x

end TheoremB

end VonNeumannAlgebra
