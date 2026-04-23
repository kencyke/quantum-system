module

public import QuantumSystem.Algebra.VonNeumannAlgebra.NormalState
public import QuantumSystem.Algebra.VonNeumannAlgebra.NormalStarAlgHom
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-!
# Araki relative entropy (Donald–Petz variational form)

This file defines the **Araki relative entropy** `S(ω ∥ φ)` of two normal states
on a von Neumann algebra, via the Donald–Petz variational formula

  `S(ω ∥ φ) := sup_{h ∈ S_sa, bounded} { Re(ω̃(h)) − log Re(φ̃(exp h)) }`,

where `ω̃`, `φ̃` denote the normal extensions of `ω`, `φ` to `B(H)` and `h`
ranges over bounded self-adjoint elements of `S.carrier`. By Donald (1986) and
Petz (1988), this coincides with Araki's original modular-operator definition
`-⟨Ω_ω, log Δ_{φ,ω} Ω_ω⟩` on normal faithful states, so we call it the Araki
relative entropy without qualification.

## Main definitions

* `VonNeumannAlgebra.arakiRelativeEntropy`: the `EReal`-valued variational entropy.

## Main results

* `arakiRelativeEntropy_nonneg`: `S(ω ∥ φ) ≥ 0`, witnessed at `h = 0`.

## References

* [Donald, M. J., *On the relative entropy*, Commun. Math. Phys. 105 (1986),
  13–34.][Donald1986]
* [Petz, D., *Sufficient subalgebras and the relative entropy of states of a
  von Neumann algebra*, Commun. Math. Phys. 105 (1988), 123–131.][Petz1988]
* Ohya, M., Petz, D., *Quantum Entropy and Its Use* (1993), Chapter 5.
-/

@[expose] public section

namespace VonNeumannAlgebra

open NormedSpace
open scoped CStarAlgebra

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [WStarAlgebra (H →L[ℂ] H)]

/-- **Variational Araki relative entropy** `S(ω ∥ φ)` for two normal states on a
von Neumann algebra `S ⊆ B(H)`.

Concretely,
`S(ω ∥ φ) = sup { (ω̃ h).re − log (φ̃ (exp h)).re | h ∈ S.carrier, IsSelfAdjoint h }`
where `ω̃ = ω.extension` is the normal extension of `ω` to `B(H)` and `exp`
denotes the operator exponential `NormedSpace.exp ℝ`.

By Donald–Petz this equals the modular-operator definition
`-⟨Ω_ω, (log Δ_{φ,ω}) Ω_ω⟩` on normal faithful states. -/
noncomputable def arakiRelativeEntropy {S : VonNeumannAlgebra H}
    (ω φ : NormalState S) : EReal :=
  ⨆ h : {h : H →L[ℂ] H // h ∈ S.carrier ∧ IsSelfAdjoint h},
    (((ω.extension h.1).re - Real.log (φ.extension (exp ℝ h.1)).re : ℝ) : EReal)

/-- Paper notation for Araki relative entropy, matching the
Ohya–Petz / Donald–Petz form `S(ω ∥ φ)` used throughout e.g.
`references/arxiv-1210.5190/INDEX.md` §Proof strategy and
Ohya–Petz *Quantum Entropy and Its Use* (1993), Chapter 5.

The algebra is inferred from the types of `ω` and `φ`. Activate with
`open scoped QuantumInfo`. -/
scoped[QuantumInfo] notation "S(" ω:max " ∥ " φ:max ")" =>
  VonNeumannAlgebra.arakiRelativeEntropy ω φ

/-- At the admissible element `h = 0` the variational functional vanishes:
`(ω̃ 0).re − log (φ̃ (exp 0)).re = 0 − log 1 = 0`. -/
private lemma arakiRelativeEntropy_term_zero {S : VonNeumannAlgebra H}
    (ω φ : NormalState S) :
    (((ω.extension (0 : H →L[ℂ] H)).re
        - Real.log (φ.extension (exp ℝ (0 : H →L[ℂ] H))).re : ℝ) : EReal) = 0 := by
  have h_extω : ω.extension (0 : H →L[ℂ] H) = 0 := map_zero _
  have h_exp_zero : (exp ℝ (0 : H →L[ℂ] H)) = 1 := NormedSpace.exp_zero
  rw [h_extω, h_exp_zero]
  have h_extφ1 : φ.extension (1 : H →L[ℂ] H) = 1 := by
    -- ω.extension extends ω from S to B(H); ω.extension (↑(1 : S)) = ω 1 = 1.
    -- Since ((1 : S) : H →L[ℂ] H) = 1, we can rewrite.
    have h1S : ((1 : S) : H →L[ℂ] H) = (1 : H →L[ℂ] H) := rfl
    have := φ.extension_extends (1 : S)
    rw [h1S] at this
    rw [this, φ.apply_one]
  rw [h_extφ1]
  simp [Real.log_one]

section PaperNotation

open scoped QuantumInfo

/-- **Non-negativity of Araki relative entropy.** `S(ω ∥ φ) ≥ 0`, witnessed at
`h = 0`. -/
theorem arakiRelativeEntropy_nonneg {S : VonNeumannAlgebra H}
    (ω φ : NormalState S) :
    0 ≤ S(ω ∥ φ) := by
  have h0_mem : (0 : H →L[ℂ] H) ∈ S.carrier ∧ IsSelfAdjoint (0 : H →L[ℂ] H) :=
    ⟨S.zero_mem', .zero _⟩
  have h_term := arakiRelativeEntropy_term_zero ω φ
  calc (0 : EReal)
      = _ := h_term.symm
    _ ≤ S(ω ∥ φ) := by
        unfold arakiRelativeEntropy
        exact le_iSup (f := fun h : {h : H →L[ℂ] H // h ∈ S.carrier ∧ IsSelfAdjoint h} =>
            (((ω.extension h.1).re -
                Real.log (φ.extension (exp ℝ h.1)).re : ℝ) : EReal))
          ⟨(0 : H →L[ℂ] H), h0_mem⟩

/-! ## Monotonicity under normal unital *-homomorphisms -/

section Monotonicity

universe v
variable {K : Type v}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [WStarAlgebra (K →L[ℂ] K)]


/-- **Monotonicity of Araki relative entropy under a unital *-homomorphism.**

For a unital *-homomorphism `α : B(H) → B(K)` mapping `N.carrier` into `M.carrier`,
and normal states `ωN, φN : NormalState N` that are pullbacks of normal states
`ωM, φM : NormalState M` along `α`,
  `S(ωN ∥ φN) ≤ S(ωM ∥ φM)`.

The pullback relationship is encoded via the intertwining identities `hω`, `hφ` at the
B(H)-extension level, evaluated on bounded self-adjoint elements of `N.carrier` and
their operator exponentials (which remain in `N.carrier` by CFC-closedness of von
Neumann algebras).

Users who have an `α : NormalStarAlgHom N M` can apply this with
`α.toStarAlgHom` and `α.mapsInto`; the theorem only requires those two pieces
of data, not the `normalPullback` field.

**Proof.** Let `h ∈ N.carrier` be bounded self-adjoint. The variational term at `h` is
`(ωN.extension h).re − log (φN.extension (exp ℝ h)).re`.

By `hω`, the first summand equals `(ωM.extension (α h)).re`. By `hφ`, the second
equals `log (φM.extension (α (exp ℝ h))).re`. By `StarAlgHom.map_cfc`,
`α (exp ℝ h) = exp ℝ (α h)`. So the term equals
`(ωM.extension (α h)).re − log (φM.extension (exp ℝ (α h))).re`, which is a term in
the variational sup for `S(ωM ∥ φM)` at `α h ∈ M.carrier`. Take the supremum. -/
theorem arakiRelativeEntropy_mono
    {N : VonNeumannAlgebra H} {M : VonNeumannAlgebra K}
    (α : (H →L[ℂ] H) →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hα_mapsInto : ∀ x ∈ N.carrier, α x ∈ M.carrier)
    (ωN φN : NormalState N) (ωM φM : NormalState M)
    (hω : ∀ h : H →L[ℂ] H, h ∈ N.carrier → IsSelfAdjoint h →
      (ωN.extension h).re = (ωM.extension (α h)).re)
    (hφ : ∀ h : H →L[ℂ] H, h ∈ N.carrier → IsSelfAdjoint h →
      (φN.extension (exp ℝ h)).re = (φM.extension (α (exp ℝ h))).re) :
    S(ωN ∥ φN) ≤ S(ωM ∥ φM) := by
  unfold arakiRelativeEntropy
  refine iSup_le ?_
  rintro ⟨h, hh_mem, hh_sa⟩
  -- The α-image `k := α h` lies in `M.carrier` and is self-adjoint.
  set k : K →L[ℂ] K := α h with k_def
  have hk_mem : k ∈ M.carrier := hα_mapsInto h hh_mem
  have hk_sa : IsSelfAdjoint k := hh_sa.map α
  -- `α (exp ℝ h) = exp ℝ k`, via StarAlgHom.map_cfc and the exp↔cfc identification.
  have hα_exp : α (exp ℝ h) = exp ℝ k := by
    have h_cfc_h : cfc Real.exp h = exp ℝ h := CFC.real_exp_eq_normedSpace_exp (ha := hh_sa)
    have h_cfc_k : cfc Real.exp k = exp ℝ k := CFC.real_exp_eq_normedSpace_exp (ha := hk_sa)
    have h_map : α (cfc Real.exp h) = cfc Real.exp (α h) :=
      StarAlgHom.map_cfc α Real.exp h
    rw [← h_cfc_h, h_map, k_def, h_cfc_k]
  -- Rewrite the term at h in terms of α h = k.
  have h_re_ω : (ωN.extension h).re = (ωM.extension k).re := by
    rw [k_def]; exact hω h hh_mem hh_sa
  have h_re_φ : (φN.extension (exp ℝ h)).re = (φM.extension (exp ℝ k)).re := by
    rw [hφ h hh_mem hh_sa, hα_exp]
  -- Bound by the supremum at k in the target algebra.
  have h_le : (((ωN.extension h).re -
        Real.log (φN.extension (exp ℝ h)).re : ℝ) : EReal) ≤
      (((ωM.extension k).re -
        Real.log (φM.extension (exp ℝ k)).re : ℝ) : EReal) := by
    rw [h_re_ω, h_re_φ]
  exact h_le.trans <|
    le_iSup (f := fun h : {h : K →L[ℂ] K // h ∈ M.carrier ∧ IsSelfAdjoint h} =>
        (((ωM.extension h.1).re -
            Real.log (φM.extension (exp ℝ h.1)).re : ℝ) : EReal))
      ⟨k, hk_mem, hk_sa⟩

end Monotonicity

end PaperNotation

end VonNeumannAlgebra
