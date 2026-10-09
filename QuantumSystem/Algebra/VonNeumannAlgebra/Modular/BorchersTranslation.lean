/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Algebra.VonNeumannAlgebra.Modular.StandardSubspace
public import QuantumSystem.Analysis.StandardSubspace.BorchersTranslation

/-!
# Borchers' theorem on translations for von Neumann algebras

Let `M` be a von Neumann algebra on `H`, `Ω` a cyclic and separating vector, with modular group
`Δ^{it}` and modular conjugation `J` (those of the standard subspace `H_M`,
`VonNeumannAlgebra.standardSubspace`), and `T` a strongly continuous unitary representation of a
finite-dimensional real vector space `V`. A translation `T(v)` with `T(v) Ω = Ω` and
`T(v) M T(v)⋆ ⊆ M` maps `H_M` into itself, so the directions `a` with `T(s a) Ω = Ω` and
`T(s a) M T(s a)⋆ ⊆ M` for `s ≥ 0` lie in the translation cone of `H_M`
(`VonNeumannAlgebra.mem_translationCone_standardSubspace`), and the standard subspace versions of
Borchers' theorem apply (`QuantumSystem.Analysis.StandardSubspace.BorchersTranslation`).

* **Borchers' theorem** (Borchers 1992; 1995, Theorem 4.1(b)): for a strongly continuous
  one-parameter unitary group `U(s) = e^{isP}` with `P ≥ 0`, `U(s) Ω = Ω` and
  `U(s) M U(s)⋆ ⊆ M` for `s ≥ 0`, `Δ^{it} U(s) Δ^{-it} = U(e^{-2πt} s)` and `J U(s) J = U(-s)`
  (`VonNeumannAlgebra.modularGroup_mul_mul_eq_of_isPositive`,
  `VonNeumannAlgebra.modularConj_apply_eq_of_isPositive`).
* **Borchers' theorem**, boost form: if `T(v) Ω = Ω` and `T(v) M T(v)⋆ ⊆ M` for `v` in a closed
  convex cone `W`, then for `a ∈ W` with positive generator, `b ∈ W` with negative generator and
  `z ∈ W ∩ -W`,
  `Δ^{it} T(r a + s b + z) Δ^{-it} = T(e^{-2πt} r a + e^{2πt} s b + z)` and
  `J T(r a + s b + z) J = T(-r a - s b + z)` (`VonNeumannAlgebra.modularGroup_mul_mul_eq_boost`,
  `VonNeumannAlgebra.modularConj_apply_eq_reflection`).

## Main results

* `VonNeumannAlgebra.mem_translationCone_standardSubspace` — half-sided translations of `M` are
  half-sided translations of `H_M`.
* `VonNeumannAlgebra.modularGroup_mul_mul_eq_of_isPositive`,
  `VonNeumannAlgebra.modularConj_apply_eq_of_isPositive` — **Borchers' theorem**.
* `VonNeumannAlgebra.modularGroup_mul_mul_eq_boost`,
  `VonNeumannAlgebra.modularConj_apply_eq_reflection` — **Borchers' theorem**, boost form, for von
  Neumann algebras.

## References

* H.-J. Borchers, *The CPT-theorem in two-dimensional theories of local observables*,
  Comm. Math. Phys. 143 (1992), 315–332
* H.-J. Borchers, *On the use of modular groups in quantum field theory*,
  Ann. Inst. H. Poincaré Phys. Théor. 63 (1995), 331–382, Theorem 4.1
-/

@[expose] public section

open InnerProductSpace (IsCyclicVector IsSeparatingVector)

open Set Complex
open scoped InnerProductSpace VonNeumannAlgebra StandardSubspace Real

namespace VonNeumannAlgebra

variable {V H : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H} {Ω : H} (hc : IsCyclicVector M Ω)
  (hs : IsSeparatingVector M Ω) {T : AddChar V (unitary (H →L[ℂ] H))}
  (hT : T.IsStronglyContinuous)

/-- A unitary `u` with `u Ω = Ω` and `u M u* ⊆ M` maps `H_M` into itself. -/
private lemma unitary_apply_mem_standardSubspace (u : unitary (H →L[ℂ] H))
    (huΩ : (u : H →L[ℂ] H) Ω = Ω)
    (huM : ∀ x ∈ M, (u : H →L[ℂ] H) * x * star (u : H →L[ℂ] H) ∈ M) {ξ : H}
    (hξ : ξ ∈ H[M, Ω]) :
    (u : H →L[ℂ] H) ξ ∈ H[M, Ω] := by
  refine apply_mem_standardSubspace_of_adjoint_apply hc hs hc hs ?_ (fun x hx => ?_) hξ
  · rw [← ContinuousLinearMap.star_eq_adjoint]
    conv_lhs => rw [← huΩ]
    rw [← mul_apply_eq_comp, ← Unitary.coe_star, ← Submonoid.coe_mul, Unitary.star_mul_self,
      OneMemClass.coe_one, one_apply_eq_self]
  · have h := huM x hx
    rwa [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.mul_def] at h

include hc hs in
omit [IsTopologicalAddGroup V] in
/-- **Half-sided translations of `M` are half-sided translations of `H_M`**: if `T(s a) Ω = Ω` and
`T(s a) M T(s a)⋆ ⊆ M` for `s ≥ 0`, then `a` lies in the translation cone of `H_M`. -/
lemma mem_translationCone_standardSubspace {a : V}
    (hTΩ : ∀ s : ℝ, 0 ≤ s → (T (s • a) : H →L[ℂ] H) Ω = Ω)
    (ha : ∀ s : ℝ, 0 ≤ s → ∀ x ∈ M,
      (T (s • a) : H →L[ℂ] H) * x * star (T (s • a) : H →L[ℂ] H) ∈ M) :
    a ∈ hT.translationCone H[M, Ω] := fun s hs' _ hξ =>
  unitary_apply_mem_standardSubspace hc hs _ (hTΩ s hs') (ha s hs') hξ

/-! ### Borchers' theorem -/

section OneParameter

variable {U : AddChar ℝ (unitary (H →L[ℂ] H))} (hU : U.IsStronglyContinuous)
  (hpos : U.selfAdjointGenerator.IsPositive) (hUΩ : ∀ s : ℝ, 0 ≤ s → (U s : H →L[ℂ] H) Ω = Ω)
  (hUM : ∀ s : ℝ, 0 ≤ s → ∀ x ∈ M, (U s : H →L[ℂ] H) * x * star (U s : H →L[ℂ] H) ∈ M)
include hU hpos hUΩ hUM

/-- `1` lies in the translation cone of `H_M` and in the spectral cone of `U`. -/
private lemma one_mem_cones :
    (1 : ℝ) ∈ hU.translationCone H[M, Ω] ∧ (1 : ℝ) ∈ hU.spectralCone :=
  ⟨mem_translationCone_standardSubspace hc hs hU (fun s hs' => by simpa using hUΩ s hs')
    fun s hs' x hx => by
    simpa using hUM s hs' x hx, hU.one_mem_spectralCone_iff.mpr hpos⟩

/-- **Borchers' theorem** (Borchers 1992; 1995, Theorem 4.1(b)), modular group: let `Ω` be cyclic
and separating for `M` and `U(s) = e^{isP}` a strongly continuous unitary group with positive
generator `P ≥ 0`, `U(s) Ω = Ω` and `U(s) M U(s)⋆ ⊆ M` for `s ≥ 0`. Then
`Δ^{it} U(s) Δ^{-it} = U(e^{-2πt} s)`. -/
theorem modularGroup_mul_mul_eq_of_isPositive (s t : ℝ) :
    H[M, Ω].modularGroup t * U s *
      H[M, Ω].modularGroup (-t) = U (Real.exp (-2 * π * t) * s) := by
  obtain ⟨h₁, h₂⟩ := one_mem_cones hc hs hU hpos hUΩ hUM
  simpa using hU.modularGroup_mul_mul_eq_of_mem_spectralCone h₁ h₂ s t

/-- **Borchers' theorem**, modular conjugation: under the hypotheses of
`VonNeumannAlgebra.modularGroup_mul_mul_eq_of_isPositive`, `J U(s) J = U(-s)`. -/
theorem modularConj_apply_eq_of_isPositive (s : ℝ) (x : H) :
    J[H[M, Ω]] ((U s : H →L[ℂ] H) (J[H[M, Ω]] x)) =
      (U (-s) : H →L[ℂ] H) x := by
  obtain ⟨h₁, h₂⟩ := one_mem_cones hc hs hU hpos hUΩ hUM
  simpa using hU.modularConj_apply_eq_of_mem_spectralCone h₁ h₂ s x

end OneParameter

/-! ### Borchers' theorem, boost form -/

section Boost

variable [FiniteDimensional ℝ V] [T2Space V] {W : ProperCone ℝ V}
  (hTΩ : ∀ v ∈ W, (T v : H →L[ℂ] H) Ω = Ω)
  (hW : ∀ v ∈ W, ∀ x ∈ M, (T v : H →L[ℂ] H) * x * star (T v : H →L[ℂ] H) ∈ M)
  {a b z : V}
include hTΩ hW

omit [IsTopologicalAddGroup V] [FiniteDimensional ℝ V] [T2Space V] in
/-- The cone `W` of half-sided translations of `M` lies in the translation cone of `H_M`. -/
private lemma le_translationCone : W ≤ hT.translationCone H[M, Ω] :=
  fun _ hv => mem_translationCone_standardSubspace hc hs hT (fun _ hs' => hTΩ _ (W.smul_mem hv hs'))
    fun _ hs' => hW _ (W.smul_mem hv hs')

/-- **Borchers' theorem**, boost form, for von Neumann algebras: let `Ω` be cyclic and separating
for `M`, and `T(v) Ω = Ω` and `T(v) M T(v)⋆ ⊆ M` for `v` in a closed convex cone `W`. For `a ∈ W`
with positive generator, `b ∈ W` with negative generator and `z ∈ W ∩ -W`,
`Δ^{it} T(r a + s b + z) Δ^{-it} = T(e^{-2πt} r a + e^{2πt} s b + z)`. -/
theorem modularGroup_mul_mul_eq_boost (ha : a ∈ W) (haC : a ∈ hT.spectralCone) (hb : b ∈ W)
    (hbC : -b ∈ hT.spectralCone) (hz : z ∈ W) (hz' : -z ∈ W) (r s t : ℝ) :
    H[M, Ω].modularGroup t * T (r • a + s • b + z) *
      H[M, Ω].modularGroup (-t) =
        T ((Real.exp (-2 * π * t) * r) • a + (Real.exp (2 * π * t) * s) • b + z) :=
  have hle := le_translationCone hc hs hT hTΩ hW
  hT.modularGroup_mul_mul_eq_boost (hle ha) haC (hle hb) hbC (hle hz) (hle hz') r s t

/-- **Borchers' theorem**, boost form, for von Neumann algebras, modular conjugation:
`J T(r a + s b + z) J = T(-r a - s b + z)`. -/
theorem modularConj_apply_eq_reflection (ha : a ∈ W) (haC : a ∈ hT.spectralCone) (hb : b ∈ W)
    (hbC : -b ∈ hT.spectralCone) (hz : z ∈ W) (hz' : -z ∈ W) (r s : ℝ) (x : H) :
    J[H[M, Ω]] ((T (r • a + s • b + z) : H →L[ℂ] H)
      (J[H[M, Ω]] x)) = (T (-(r • a) - s • b + z) : H →L[ℂ] H) x :=
  have hle := le_translationCone hc hs hT hTΩ hW
  hT.modularConj_apply_eq_reflection (hle ha) haC (hle hb) hbC (hle hz) (hle hz') r s x

end Boost

end VonNeumannAlgebra
