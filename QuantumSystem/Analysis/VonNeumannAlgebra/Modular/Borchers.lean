/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.InnerProductSpace.StandardSubspace.Borchers
public import QuantumSystem.Analysis.VonNeumannAlgebra.Modular.RelativeModularConj
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Borchers' Theorems A and B for von Neumann algebras

Let `Ω₁`, `Ω₂` be cyclic and separating for von Neumann algebras `M₁` on `H₁` and `M₂` on `H₂`,
with modular groups `Δ₁^{it}`, `Δ₂^{it}` and modular conjugations `J₁`, `J₂`: those of the
standard subspaces `H_{M₁}`, `H_{M₂}` (`VonNeumannAlgebra.standardSubspace`). Borchers' theorems
for standard subspaces (`QuantumSystem.Analysis.InnerProductSpace.StandardSubspace.Borchers`) give the von Neumann
algebra versions, since a bounded `V` with `V† Ω₂ = Ω₁` and `V M₁ V† ⊆ M₂` maps `H_{M₁}` into
`H_{M₂}` (`VonNeumannAlgebra.apply_mem_standardSubspace_of_adjoint_apply`) and the symplectic
complement of `H_M` is `H_{M′}` (`VonNeumannAlgebra.standardSubspace_commutant_eq_symplComp`).
For a unitary `V` the conditions read `V Ω₁ = Ω₂` and `V M₁ V⋆ ⊆ M₂`, Borchers' hypotheses.

* **Theorem A** (`VonNeumannAlgebra.exists_modularGroup_continuation`): for such a `V`,
  `V(t) = Δ₂^{-it} V Δ₁^{it}` continues to the strip `0 ≤ im z ≤ 1/2`, holomorphic in the interior
  and `*`-strongly continuous on the closed strip, with `‖V(z)‖ ≤ ‖V‖` and
  `V(t + i/2) = J₂ V(t) J₁`.
* **Theorem B** (`VonNeumannAlgebra.modularGroup_apply_eq_of_upperStrip`,
  `VonNeumannAlgebra.modularConj_apply_eq_of_upperStrip`): let `W(z)` be bounded on the strip with
  holomorphic matrix coefficients, continuous up to the boundary, such that `W(t)† Ω₂ = Ω₁`,
  `W(t) M₁ W(t)† ⊆ M₂` and `W(t + i/2) M₁′ W(t + i/2)† ⊆ M₂′`. Then
  `Δ₂^{it} W(s) Δ₁^{-it} = W(s - t)` and `J₂ W(s) J₁ = W(s + i/2)`. No unitarity is assumed;
  `W(t + i/2)† Ω₂ = Ω₁` on the upper boundary follows from the real line, since a bounded
  holomorphic function on the strip vanishing on one boundary line vanishes
  (`Complex.eqOn_zero_of_eqOn_zero_im_eq_lower`).
* **Relative version of Theorem A**
  (`VonNeumannAlgebra.exists_relativeModularGroup_continuation_of_le`): for arbitrary vectors
  `ηᵢ`, `Ωᵢ` and `V` with `V S̄_{η₁,Ω₁} ⊆ S̄_{η₂,Ω₂} V`, `t ↦ Δ_{η₂,Ω₂}^{-it} V Δ_{η₁,Ω₁}^{it}`
  continues to the strip in the same way, with
  `V(t + i/2) = Δ_{η₂,Ω₂}^{-it} J_{Ω₂,η₂} V J_{η₁,Ω₁} Δ_{η₁,Ω₁}^{it}`; here `Δ^{it}` are the
  imaginary powers, partial isometries vanishing on `ker Δ`, and `J_{Ω₂,η₂} = J_{η₂,Ω₂}†`
  (`VonNeumannAlgebra.inner_relativeModularConj_left`) inverts `J_{η₂,Ω₂}` on the range of
  `Δ_{η₂,Ω₂}^{1/2}`. It is Theorem A for semilinear operators in polar decomposition form
  (`IsSelfAdjoint.exists_stripContinuation_polarIsometry`) applied to the closed relative Tomita
  operators. The intertwining holds for `V† Ω₂ = Ω₁`, `V† η₂ = η₁`, `V M₁ V† ⊆ M₂`, `V` mapping
  `s(Ω₁) H₁` into `s(Ω₂) H₂` for the support projections `s(Ωᵢ) ∈ Mᵢ`, and `V` mapping `[M₁ Ω₁]ᗮ`
  into `[M₂ Ω₂]ᗮ` (`VonNeumannAlgebra.compPMap_closure_relativeTomita_le_of_adjoint_apply`), in
  particular for cyclic `Ω₁`, separating `Ω₂` and arbitrary `ηᵢ`
  (`VonNeumannAlgebra.exists_relativeModularGroup_continuation`).

Borchers (1995) states both theorems for unitaries on one Hilbert space with `Ω₁ = Ω₂`.

## Main results

* `VonNeumannAlgebra.exists_modularGroup_continuation` — **Borchers' Theorem A**.
* `VonNeumannAlgebra.exists_relativeModularGroup_continuation_of_le`,
  `VonNeumannAlgebra.exists_relativeModularGroup_continuation` — the relative version of Theorem A,
  for the relative modular group `Δ_{η,Ω}^{it}` (`VonNeumannAlgebra.relativeModularGroup`), for
  arbitrary vectors and for cyclic `Ω₁` and separating `Ω₂`.
* `VonNeumannAlgebra.compPMap_closure_relativeTomita_le_of_adjoint_apply` — `V S̄_{η₁,Ω₁} ⊆
  S̄_{η₂,Ω₂} V` from algebraic conditions on `V`.
* `VonNeumannAlgebra.modularGroup_apply_eq_of_upperStrip`,
  `VonNeumannAlgebra.modularConj_apply_eq_of_upperStrip` — **Borchers' Theorem B**.

## TODO

* The boundary value of the relative Theorem A in conjugated form: with
  `Δ_{ξ,η}^{it} = J_{η,ξ} Δ_{η,ξ}^{it} J_{η,ξ}†` (Araki–Masuda 1982), which is not formalised
  (see `VonNeumannAlgebra.adjointₛₗ_relativeModularConj`), it reads
  `V(t + i/2) = J_{Ω₂,η₂} Ṽ(t) J_{η₁,Ω₁}` with `Ṽ(t) = Δ_{Ω₂,η₂}^{-it} V Δ_{Ω₁,η₁}^{it}` the family
  for the swapped pairs. It is Borchers' form `V(t + i/2) = J V(t) J` only for `ηᵢ = Ωᵢ`.
* Theorem B for relative modular operators. The proof of Theorem B uses that the auxiliary
  function is real on both boundary lines, because the vectors involved lie in the real subspaces
  `H_M` and `(H_M)'`; a relative Tomita operator `S_{η,Ω}` with `η ≠ Ω` is not an involution and
  has no such real subspace, so the argument does not carry over, and the right relative statement
  (the conditions on `W` and the boundary identity for `J_{η,Ω}`) still has to be formulated.

## References

* H.-J. Borchers, *On the use of modular groups in quantum field theory*,
  Ann. Inst. H. Poincaré Phys. Théor. 63 (1995), 331–382, Theorems A and B
* H. Araki, T. Masuda, *Positive cones and Lp-spaces for von Neumann algebras*, Publ. RIMS 18
  (1982), 339–411, §2
-/

@[expose] public section

open InnerProductSpace (IsCyclicVector IsSeparatingVector)

open Set Complex
open scoped InnerProductSpace VonNeumannAlgebra StandardSubspace InnerProduct LinearPMap

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
`0 ≤ im z ≤ 1/2`, holomorphic in the operator norm in the interior and `*`-strongly continuous on
the closed strip, with `‖V(z)‖ ≤ ‖V‖` and `V(t + i/2) = J₂ V(t) J₁`. -/
theorem exists_modularGroup_continuation {V : H₁ →L[ℂ] H₂}
    (hVΩ : (V†) Ω₂ = Ω₁)
    (hVM : ∀ x ∈ M₁, V ∘L x ∘L V† ∈ M₂) :
    ∃ F : ℂ → H₁ →L[ℂ] H₂, DifferentiableOn ℂ F (im ⁻¹' Ioo 0 (1 / 2)) ∧
      (∀ x, ContinuousOn (fun z => F z x) (im ⁻¹' Icc 0 (1 / 2))) ∧
      (∀ y, ContinuousOn (fun z => ((F z)†) y) (im ⁻¹' Icc 0 (1 / 2))) ∧
      (∀ z ∈ im ⁻¹' Icc 0 (1 / 2), ‖F z‖ ≤ ‖V‖) ∧
      (∀ t : ℝ, F t = Δ[H[M₂, Ω₂]]^{-i t} ∘L V ∘L Δ[H[M₁, Ω₁]]^{i t}) ∧
      ∀ (t : ℝ) (x : H₁), F (t + I / 2) x =
        J[H[M₂, Ω₂]] (F t (J[H[M₁, Ω₁]] x)) :=
  StandardSubspace.exists_modularGroup_continuation
    (K₁ := H[M₁, Ω₁]) (K₂ := H[M₂, Ω₂]) V
    fun _ hξ => apply_mem_standardSubspace_of_adjoint_apply hc₁ hs₁ hc₂ hs₂ hVΩ hVM hξ

/-! ### Theorem A for relative modular operators -/

section Relative

variable {η₁ : H₁} {η₂ : H₂} {V : H₁ →L[ℂ] H₂}

/-- `s(Ω₂) V (1 - s(Ω₁)) = 0` for `V† Ω₂ = Ω₁` and `V M₁ V† ⊆ M₂`: with `P = 1 - s(Ω₁) ∈ M₁`, the
operator `V P V† ∈ M₂` kills `Ω₂`, hence `V P V† s(Ω₂) = 0`
(`VonNeumannAlgebra.mul_supportProj_eq_zero_iff`), and `G = s(Ω₂) V P` has
`G G† = s(Ω₂) V P V† s(Ω₂) = 0`. -/
lemma supportProj_comp_comp_one_sub_supportProj_eq_zero (hVΩ : (V†) Ω₂ = Ω₁)
    (hVM : ∀ x ∈ M₁, V ∘L x ∘L V† ∈ M₂) :
    M₂.supportProj Ω₂ ∘L V ∘L (1 - M₁.supportProj Ω₁) = 0 := by
  set P := 1 - M₁.supportProj Ω₁
  set s₂ := M₂.supportProj Ω₂
  have hP : P ∈ M₁ := sub_mem (one_mem M₁) (M₁.supportProj_mem Ω₁)
  have hPp : IsStarProjection P := (M₁.isStarProjection_supportProj Ω₁).one_sub
  have hs₂ : IsStarProjection s₂ := M₂.isStarProjection_supportProj Ω₂
  have hQ : (V ∘L P ∘L V†) * s₂ = 0 := by
    rw [mul_supportProj_eq_zero_iff (hVM P hP)]
    simp [P, hVΩ, supportProj_apply_self]
  -- `‖P V† s(Ω₂) z‖² = ⟪s(Ω₂) z, V P V† s(Ω₂) z⟫ = 0`
  have hT : P ∘L V† ∘L s₂ = 0 := by
    ext z
    have hz : V (P ((V†) (s₂ z))) = 0 := congr($hQ z)
    have h : ⟪P ((V†) (s₂ z)), P ((V†) (s₂ z))⟫_ℂ = 0 := by
      rw [← ContinuousLinearMap.adjoint_inner_right P, ← ContinuousLinearMap.star_eq_adjoint,
        hPp.isSelfAdjoint.star_eq, ← mul_apply_eq_comp, hPp.isIdempotentElem.eq,
        ContinuousLinearMap.adjoint_inner_left, hz, inner_zero_right]
    exact inner_self_eq_zero.mp h
  have hadj : (P ∘L V† ∘L s₂)† = s₂ ∘L V ∘L P := by
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint, ← ContinuousLinearMap.star_eq_adjoint,
      ← ContinuousLinearMap.star_eq_adjoint, hPp.isSelfAdjoint.star_eq, hs₂.isSelfAdjoint.star_eq,
      ContinuousLinearMap.comp_assoc]
  rw [← hadj, hT, map_zero]

/-- `V S_{η₁,Ω₁} ⊆ S_{η₂,Ω₂} V`, pointwise on the generating vectors, for `V† Ω₂ = Ω₁`,
`V† η₂ = η₁`, `V M₁ V† ⊆ M₂`, `V` mapping `s(Ω₁) H₁` into `s(Ω₂) H₂` for the support projections
`s(Ωᵢ)` of `Ωᵢ` in `Mᵢ`, and `V` mapping `[M₁ Ω₁]ᗮ` into `[M₂ Ω₂]ᗮ`: `V x Ω₁ = (V x V†) Ω₂` and
`V s(Ω₁) x⋆ η₁ = s(Ω₂) (V x V†)⋆ η₂`. The rest of the intertwining `V s(Ω₁) = s(Ω₂) V`,
`s(Ω₂) V (1 - s(Ω₁)) = 0`, follows from the other hypotheses
(`VonNeumannAlgebra.supportProj_comp_comp_one_sub_supportProj_eq_zero`), and so does the half
`V [M₁ Ω₁] ⊆ [M₂ Ω₂]` of the intertwining of the support projections in `Mᵢ′`; neither is
assumed. -/
private lemma apply_mem_graph_relativeTomita_of_supportProj (hVΩ : (V†) Ω₂ = Ω₁) (hVη : (V†) η₂ = η₁)
    (hVM : ∀ x ∈ M₁, V ∘L x ∘L V† ∈ M₂)
    (hVs : M₂.supportProj Ω₂ ∘L V ∘L M₁.supportProj Ω₁ = V ∘L M₁.supportProj Ω₁)
    (hVs' : ∀ ζ ∈ (InnerProductSpace.cyclicSubspace M₁ Ω₁).toSubmoduleᗮ,
      V ζ ∈ (InnerProductSpace.cyclicSubspace M₂ Ω₂).toSubmoduleᗮ) {u v : H₁}
    (h : (u, v) ∈ (S[M₁]⟦η₁, Ω₁⟧).graphₛₗ) : (V u, V v) ∈ (S[M₂]⟦η₂, Ω₂⟧).graphₛₗ := by
  have hVs₀ : V ∘L M₁.supportProj Ω₁ = M₂.supportProj Ω₂ ∘L V := by
    ext z
    have h₀ := congr($(supportProj_comp_comp_one_sub_supportProj_eq_zero hVΩ hVM) z)
    have h₁ := congr($hVs z)
    simp only [ContinuousLinearMap.comp_apply, sub_apply, one_apply_eq_self, zero_apply, map_sub,
      sub_eq_zero] at h₀ h₁
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← h₁, h₀]
  obtain ⟨x, hx, ζ, hζ, hp⟩ := mem_graph_relativeTomita.mp h
  simp only [Prod.mk.injEq] at hp
  obtain ⟨rfl, rfl⟩ := hp
  have h₂ := mk_mem_graph_relativeTomita (η := η₂) (hVM x hx) (hVs' ζ hζ)
  convert h₂ using 2
  · simp [hVΩ]
  · rw [ContinuousLinearMap.star_eq_adjoint (V ∘L x ∘L V†), ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
      ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.comp_apply V, hVs₀]
    simp [hVη]

/-- **`V S̄_{η₁,Ω₁} ⊆ S̄_{η₂,Ω₂} V`** for `V† Ω₂ = Ω₁`, `V† η₂ = η₁`, `V M₁ V† ⊆ M₂`, `V` mapping
`s(Ω₁) H₁` into `s(Ω₂) H₂` and `[M₁ Ω₁]ᗮ` into `[M₂ Ω₂]ᗮ`: `V S_{η₁,Ω₁} ⊆ S_{η₂,Ω₂} V` on the
generating vectors, hence `V S̄_{η₁,Ω₁} ⊆ closure (V S_{η₁,Ω₁}) ⊆ closure (S_{η₂,Ω₂} V) ⊆ S̄_{η₂,Ω₂} V`
(`LinearPMap.compPMap_closureₛₗ_le_closureₛₗ_compNat_toPMap`). -/
lemma compPMap_closure_relativeTomita_le_of_adjoint_apply (hVΩ : (V†) Ω₂ = Ω₁)
    (hVη : (V†) η₂ = η₁) (hVM : ∀ x ∈ M₁, V ∘L x ∘L V† ∈ M₂)
    (hVs : M₂.supportProj Ω₂ ∘L V ∘L M₁.supportProj Ω₁ = V ∘L M₁.supportProj Ω₁)
    (hVs' : ∀ ζ ∈ (InnerProductSpace.cyclicSubspace M₁ Ω₁).toSubmoduleᗮ,
      V ζ ∈ (InnerProductSpace.cyclicSubspace M₂ Ω₂).toSubmoduleᗮ) :
    (V : H₁ →ₗ[ℂ] H₂).compPMap (S[M₁]⟦η₁, Ω₁⟧).closureₛₗ ≤
      (S[M₂]⟦η₂, Ω₂⟧).closureₛₗ.compNat ((V : H₁ →ₗ[ℂ] H₂).toPMap ⊤) :=
  -- `V S ⊆ S V` on the generating vectors of the domain
  LinearPMap.compPMap_closureₛₗ_le_closureₛₗ_compNat_toPMap (isClosable_relativeTomita M₁ η₁ Ω₁)
    (isClosable_relativeTomita M₂ η₂ Ω₂) V V
    (LinearPMap.compPMap_le_compNat_toPMap_iffₛₗ.mpr fun _ _ h =>
      apply_mem_graph_relativeTomita_of_supportProj hVΩ hVη hVM hVs hVs' h)

/-- **Relative version of Borchers' Theorem A** for arbitrary vectors: let `Δᵢ = Δ_{ηᵢ,Ωᵢ}` be the
relative modular operators of `(Mᵢ, ηᵢ, Ωᵢ)`, with imaginary powers `Δᵢ^{it}` (partial isometries
vanishing on `ker Δᵢ`) and relative modular conjugations `J_{ηᵢ,Ωᵢ}`, and let `V` be bounded with
`V S̄_{η₁,Ω₁} ⊆ S̄_{η₂,Ω₂} V`. Then `t ↦ Δ₂^{-it} V Δ₁^{it}` extends to the strip
`0 ≤ im z ≤ 1/2`, holomorphic in the operator norm in the interior and `*`-strongly continuous on
the closed strip, with `‖V(z)‖ ≤ ‖V‖` and `V(t + i/2) = Δ₂^{-it} J_{Ω₂,η₂} V J_{η₁,Ω₁} Δ₁^{it}`.

It is Theorem A for semilinear operators in polar decomposition form
(`IsSelfAdjoint.exists_stripContinuation_polarIsometry`) applied to the closed relative Tomita
operators `S̄_{ηᵢ,Ωᵢ} = J_{ηᵢ,Ωᵢ} Δᵢ^{1/2}`, where the antilinear adjoint of `J_{η₂,Ω₂}` is
`J_{Ω₂,η₂}` (`VonNeumannAlgebra.adjointₛₗ_relativeModularConj`). The intertwining
holds for `V† Ω₂ = Ω₁`, `V† η₂ = η₁`, `V M₁ V† ⊆ M₂`, `V` mapping `s(Ω₁) H₁` into `s(Ω₂) H₂` and
`V` mapping `[M₁ Ω₁]ᗮ` into `[M₂ Ω₂]ᗮ`
(`VonNeumannAlgebra.compPMap_closure_relativeTomita_le_of_adjoint_apply`); for cyclic `Ω₁` and
separating `Ω₂` this is `VonNeumannAlgebra.exists_relativeModularGroup_continuation`. -/
lemma exists_relativeModularGroup_continuation_of_le
    (hV : (V : H₁ →ₗ[ℂ] H₂).compPMap (S[M₁]⟦η₁, Ω₁⟧).closureₛₗ ≤
      (S[M₂]⟦η₂, Ω₂⟧).closureₛₗ.compNat ((V : H₁ →ₗ[ℂ] H₂).toPMap ⊤)) :
    ∃ F : ℂ → H₁ →L[ℂ] H₂, DifferentiableOn ℂ F (im ⁻¹' Ioo 0 (1 / 2)) ∧
      (∀ x, ContinuousOn (fun z => F z x) (im ⁻¹' Icc 0 (1 / 2))) ∧
      (∀ y, ContinuousOn (fun z => ((F z)†) y) (im ⁻¹' Icc 0 (1 / 2))) ∧
      (∀ z ∈ im ⁻¹' Icc 0 (1 / 2), ‖F z‖ ≤ ‖V‖) ∧
      (∀ t : ℝ, F t = Δ[M₂]⟦η₂, Ω₂⟧^{-i t} ∘L V ∘L Δ[M₁]⟦η₁, Ω₁⟧^{i t}) ∧
      ∀ (t : ℝ) (x : H₁), F (t + I / 2) x =
        Δ[M₂]⟦η₂, Ω₂⟧^{-i t} (J[M₂]⟦Ω₂, η₂⟧ (V (J[M₁]⟦η₁, Ω₁⟧ (Δ[M₁]⟦η₁, Ω₁⟧^{i t} x)))) := by
  obtain ⟨F, hFd, hFs, hFs', hFb, hF0, hF1⟩ :=
    (isSelfAdjoint_relativeModular M₁ η₁ Ω₁).exists_stripContinuation_polarIsometry
      (isSelfAdjoint_relativeModular M₂ η₂ Ω₂) (relativeModular_def M₁ η₁ Ω₁)
      (relativeModular_def M₂ η₂ Ω₂) (isClosed_closure_relativeTomita M₁ η₁ Ω₁)
      (isClosed_closure_relativeTomita M₂ η₂ Ω₂) V hV
  refine ⟨F, hFd, hFs, hFs', hFb, hF0, fun t x => ?_⟩
  rw [hF1]
  change Δ[M₂]⟦η₂, Ω₂⟧^{-i t} (J[M₂]⟦η₂, Ω₂⟧.adjointₛₗ
    (V (J[M₁]⟦η₁, Ω₁⟧ (Δ[M₁]⟦η₁, Ω₁⟧^{i t} x)))) = _
  rw [adjointₛₗ_relativeModularConj]

include hc₁ hs₂ in
/-- **Relative version of Borchers' Theorem A** for a cyclic `Ω₁`, a separating `Ω₂` and arbitrary
`ηᵢ`: for `V` bounded with `V† Ω₂ = Ω₁`, `V† η₂ = η₁` and `V M₁ V† ⊆ M₂`, the family
`t ↦ Δ_{η₂,Ω₂}^{-it} V Δ_{η₁,Ω₁}^{it}` extends to the strip `0 ≤ im z ≤ 1/2`, holomorphic in the
operator norm in the interior and `*`-strongly continuous on the closed strip, with
`‖V(z)‖ ≤ ‖V‖` and `V(t + i/2) = Δ_{η₂,Ω₂}^{-it} J_{Ω₂,η₂} V J_{η₁,Ω₁} Δ_{η₁,Ω₁}^{it}`
(`VonNeumannAlgebra.exists_relativeModularGroup_continuation_of_le`; the support projection
of `Ω₂` in `M₂` is `1`, and `[M₁ Ω₁]ᗮ = 0`). For `ηᵢ` not separating and `Ωᵢ` cyclic,
`Δ_{ηᵢ,Ωᵢ}` has the kernel `[Mᵢ′ ηᵢ]ᗮ`
(`VonNeumannAlgebra.ker_relativeModular_eq_orthogonal`), on which
`Δ_{ηᵢ,Ωᵢ}^{it}` vanishes. For `ηᵢ = Ωᵢ` the relative modular groups and conjugations are those of
the standard subspaces (`VonNeumannAlgebra.relativeModularGroup_self`,
`VonNeumannAlgebra.relativeModularConj_self`; these need `Ωᵢ` cyclic and separating), and with
`J Δ^{it} = Δ^{it} J` (`StandardSubspace.modularConj_comm_modularGroup`) the theorem specialises to
`VonNeumannAlgebra.exists_modularGroup_continuation`. -/
theorem exists_relativeModularGroup_continuation (hVΩ : (V†) Ω₂ = Ω₁) (hVη : (V†) η₂ = η₁)
    (hVM : ∀ x ∈ M₁, V ∘L x ∘L V† ∈ M₂) :
    ∃ F : ℂ → H₁ →L[ℂ] H₂, DifferentiableOn ℂ F (im ⁻¹' Ioo 0 (1 / 2)) ∧
      (∀ x, ContinuousOn (fun z => F z x) (im ⁻¹' Icc 0 (1 / 2))) ∧
      (∀ y, ContinuousOn (fun z => ((F z)†) y) (im ⁻¹' Icc 0 (1 / 2))) ∧
      (∀ z ∈ im ⁻¹' Icc 0 (1 / 2), ‖F z‖ ≤ ‖V‖) ∧
      (∀ t : ℝ, F t = Δ[M₂]⟦η₂, Ω₂⟧^{-i t} ∘L V ∘L Δ[M₁]⟦η₁, Ω₁⟧^{i t}) ∧
      ∀ (t : ℝ) (x : H₁), F (t + I / 2) x =
        Δ[M₂]⟦η₂, Ω₂⟧^{-i t} (J[M₂]⟦Ω₂, η₂⟧ (V (J[M₁]⟦η₁, Ω₁⟧ (Δ[M₁]⟦η₁, Ω₁⟧^{i t} x)))) := by
  have h₂ : M₂.supportProj Ω₂ = 1 := supportProj_eq_one_iff.mpr hs₂.isCyclicVector_commutant
  refine exists_relativeModularGroup_continuation_of_le
    (compPMap_closure_relativeTomita_le_of_adjoint_apply hVΩ hVη hVM ?_ fun ζ hζ => ?_)
  · rw [h₂]
    ext
    simp
  · have hζ0 : ζ = 0 := by
      rw [hc₁] at hζ
      simpa using hζ
    simp [hζ0]

end Relative

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
    Δ[H[M₂, Ω₂]]^{i t} (W s (Δ[H[M₁, Ω₁]]^{-i t} x)) =
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
