/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Physics.LocalNet.Isotony

/-!
# Gradings of a net

A **grading** `CStarNet.Grading` of a net of C⋆-algebras (`QuantumSystem.Physics.LocalNet.Isotony`)
is a **parity** automorphism of every local algebra, involutive and preserved by the isotony
embeddings. An element `x` of `𝔄(O)` is *even* if the parity fixes it and *odd* if the parity sends
it to `-x`; every element is the sum of its even part `(x + parity O x) / 2` and its odd part
`(x - parity O x) / 2` (`CStarNet.Grading.exists_even_add_odd`). In a system with fermions the
even elements are the bosonic ones and the odd elements the fermionic ones.

The parity is carried region by region because the net is given by its local algebras and
embeddings, not as subalgebras of one algebra. A grading needs the order of the index set alone;
what it demands of causally orthogonal regions is graded locality, in
`QuantumSystem.Physics.LocalNet.Locality`. Every net carries the trivial grading
(`CStarNet.Grading.trivial`), for which every element is even.

## Main definitions

* `CStarNet.Grading N` — a grading of the net `N`.
* `CStarNet.Grading.trivial N` — the grading by the identity.

## Notation

`𝔄(O)` in the prose is documentation shorthand for the local C⋆-algebra `N.algebra O`; the
convention is stated in full in `QuantumSystem.Physics.LocalNet.Isotony`.
-/

@[expose] public section

namespace CStarNet

variable {K : Type*} [Preorder K]

/-- A **grading** of a net of C⋆-algebras: a **parity** automorphism of every local algebra,
    involutive (`parity_parity`) and natural for the isotony embeddings (`parity_incl`). An element
    `x` is *even* if `parity O x = x` and *odd* if `parity O x = -x`. -/
structure Grading (N : CStarNet K) where
  /-- The **parity** automorphism of a local algebra: `+1` on the even (bosonic) elements and `-1`
      on the odd (fermionic) ones. -/
  parity : ∀ O : K, N.algebra O ≃⋆ₐ[ℂ] N.algebra O
  /-- The parity is an involution. -/
  parity_parity : ∀ {O : K} (x : N.algebra O), parity O (parity O x) = x
  /-- The isotony embeddings preserve the parity. -/
  parity_incl : ∀ {O O' : K} (h : O ≤ O') (x : N.algebra O),
      parity O' (N.incl h x) = N.incl h (parity O x)

namespace Grading

variable {N : CStarNet K} (γ : N.Grading)

/-- The parity is natural with respect to the region-equality transport. -/
lemma parity_algebraCongr {O O' : K} (e : O = O') (x : N.algebra O) :
    N.algebraCongr e (γ.parity O x) = γ.parity O' (N.algebraCongr e x) := by
  subst e; rfl

/-- **Every element is the sum of an even and an odd one**:
    `x = (x + parity O x) / 2 + (x - parity O x) / 2`. -/
lemma exists_even_add_odd {O : K} (x : N.algebra O) :
    ∃ x₀ x₁ : N.algebra O, γ.parity O x₀ = x₀ ∧ γ.parity O x₁ = -x₁ ∧ x₀ + x₁ = x := by
  refine ⟨(2⁻¹ : ℂ) • (x + γ.parity O x), (2⁻¹ : ℂ) • (x - γ.parity O x), ?_, ?_, ?_⟩
  · rw [map_smul, map_add, γ.parity_parity, add_comm]
  · rw [map_smul, map_sub, γ.parity_parity, ← smul_neg, neg_sub]
  · rw [← smul_add, add_add_sub_cancel, ← two_smul ℂ x, smul_smul, inv_mul_cancel₀ two_ne_zero,
      one_smul]

variable (N) in
/-- The **trivial grading** of a net: the parity is the identity, so every element is even. -/
protected def trivial : N.Grading where
  parity _ := StarAlgEquiv.refl ℂ _
  parity_parity _ := rfl
  parity_incl _ _ := rfl

/-- The parity of the trivial grading fixes every element. -/
@[simp] lemma trivial_parity_apply {O : K} (x : N.algebra O) :
    (Grading.trivial N).parity O x = x :=
  rfl

end Grading

end CStarNet
