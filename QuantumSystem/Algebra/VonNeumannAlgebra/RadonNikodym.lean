/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Algebra.CStarAlgebra.Representation.RadonNikodym
public import QuantumSystem.ForMathlib.Analysis.VonNeumannAlgebra.Commutant

/-!
# Radon–Nikodym theorem for `ω ≤ ω_ζ` on a von Neumann algebra

For a von Neumann algebra `N` on `K`, `ζ ∈ K`, and a positive functional `ω` on `N` dominated by
the vector functional of `ζ`, `ω(x⋆x) ≤ ‖x ζ‖²` for all `x ∈ N`, there is `T ∈ N′` with
`0 ≤ T ≤ 1` and `ω(x) = ⟪T ζ, x ζ⟫`; with `R = √T ∈ N′`, `ω = ω_{R ζ}` is itself a vector
functional (Sakai, *C\*-algebras and W\*-algebras*, 1.24.4; Bratteli–Robinson, *Operator
Algebras and Quantum Statistical Mechanics 1*, Thm. 2.3.19).

This is the representation form `CStarAlgebra.exists_commute_of_apply_star_mul_self_le`
(`QuantumSystem.Algebra.CStarAlgebra.Representation.RadonNikodym`) applied to the inclusion
`N → B(K)`.

## Main results

* `VonNeumannAlgebra.exists_mem_commutant_of_apply_star_mul_self_le` — `ω(x) = ⟪T ζ, x ζ⟫` with
  `T ∈ N′`, `0 ≤ T ≤ 1`.
* `VonNeumannAlgebra.exists_mem_commutant_inner_eq_of_apply_star_mul_self_le` — `ω = ω_{R ζ}` with
  `0 ≤ R ∈ N′`.
-/

@[expose] public section

open scoped InnerProductSpace ComplexOrder VonNeumannAlgebra

namespace VonNeumannAlgebra

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable {N : VonNeumannAlgebra K}

variable (N) in
/-- The inclusion `N → B(K)`, as a unital ⋆-homomorphism. -/
def inclₐ : N →⋆ₐ[ℂ] (K →L[ℂ] K) where
  toFun := Subtype.val
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

/-- **Radon–Nikodym theorem for `ω ≤ ω_ζ`.** If a positive functional `ω` on a von Neumann algebra
`N` satisfies `ω(x⋆x) ≤ ‖x ζ‖²` for all `x ∈ N`, there is `T ∈ N′` with `0 ≤ T ≤ 1` and
`ω(x) = ⟪T ζ, x ζ⟫` for all `x ∈ N`. -/
theorem exists_mem_commutant_of_apply_star_mul_self_le {ω : N →ₚ[ℂ] ℂ} {ζ : K}
    (hω : ∀ x : N, ‖ω (star x * x)‖ ≤ ‖(x : K →L[ℂ] K) ζ‖ ^ 2) :
    ∃ T ∈ N′, 0 ≤ T ∧ T ≤ 1 ∧ ∀ x : N, ω x = ⟪T ζ, (x : K →L[ℂ] K) ζ⟫_ℂ := by
  obtain ⟨T, hc, h0, h1, h⟩ :=
    CStarAlgebra.exists_commute_of_apply_star_mul_self_le (ρ := inclₐ N) (f := ω) hω
  exact ⟨T, mem_commutant_iff.mpr fun a ha => (hc ⟨a, ha⟩).eq.symm, h0, h1, h⟩

/-- **Radon–Nikodym, vector form.** If `ω(x⋆x) ≤ ‖x ζ‖²` for all `x ∈ N`, then `ω` is the vector
functional of `R ζ` for some positive `R ∈ N′`: `ω(x) = ⟪R ζ, x (R ζ)⟫`. -/
theorem exists_mem_commutant_inner_eq_of_apply_star_mul_self_le {ω : N →ₚ[ℂ] ℂ} {ζ : K}
    (hω : ∀ x : N, ‖ω (star x * x)‖ ≤ ‖(x : K →L[ℂ] K) ζ‖ ^ 2) :
    ∃ R ∈ N′, 0 ≤ R ∧ ∀ x : N, ω x = ⟪R ζ, (x : K →L[ℂ] K) (R ζ)⟫_ℂ := by
  obtain ⟨R, hc, h0, h⟩ :=
    CStarAlgebra.exists_commute_inner_eq_of_apply_star_mul_self_le (ρ := inclₐ N) (f := ω) hω
  exact ⟨R, mem_commutant_iff.mpr fun a ha => (hc ⟨a, ha⟩).eq.symm, h0, h⟩

end VonNeumannAlgebra
