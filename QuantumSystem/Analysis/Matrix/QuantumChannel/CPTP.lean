/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import QuantumSystem.Notation

/-!
# Quantum channels (completely positive trace-preserving maps)

This file defines quantum channels on finite-dimensional matrix algebras. A quantum channel is a
linear map `Φ : M_n(ℂ) → M_m(ℂ)` that is
1. completely positive (CP): it has a Kraus representation `Φ(ρ) = Σᵢ Kᵢ ρ Kᵢᴴ`;
2. trace preserving (TP): `Tr (Φ A) = Tr A` for all `A`.

## Main definitions

* `Matrix.IsTracePreserving`: a linear map preserves trace.
* `Matrix.IsCompletelyPositive`: a linear map has a Kraus representation.
* `Matrix.IsQuantumChannel`: a linear map is both CP and TP.
* `Matrix.QuantumChannel n m`: the subtype of CPTP maps `M_n(ℂ) → M_m(ℂ)`.

## Main statements

* `Matrix.isQuantumChannel_id`, `Matrix.QuantumChannel.comp`: identity and composition.
* `Matrix.IsCompletelyPositive.map_isHermitian`, `Matrix.IsCompletelyPositive.posSemidef_map`:
  CP maps preserve Hermitian and positive semidefinite matrices.

## Mathematical Background

By the Choi–Kraus theorem, a linear map `Φ : M_n(ℂ) → M_m(ℂ)` is completely positive iff it has a
Kraus representation `Φ(ρ) = Σᵢ Kᵢ ρ Kᵢᴴ`; complete positivity is *defined* here by the Kraus
form. The completeness relation `Σᵢ Kᵢᴴ Kᵢ = I` for trace-preserving maps is in
`QuantumSystem/Analysis/Matrix/QuantumChannel/Kraus.lean`.

## References

* Nielsen, Chuang, *Quantum Computation and Quantum Information*, Chapter 8
* Watrous, *The Theory of Quantum Information*, Chapter 2
-/
@[expose] public section

namespace Matrix

variable {n m k : Type*} [Fintype n] [Fintype m] [Fintype k]

open scoped ComplexOrder

/-! ### Trace-Preserving Maps -/

/-- A linear map is trace-preserving if Tr(Φ(A)) = Tr(A) for all A. -/
def IsTracePreserving (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Prop :=
  ∀ A : Matrix n n ℂ, Tr (Φ A) = Tr A

/-! ### Completely Positive Maps -/

/-- A linear map is completely positive if it has a Kraus representation.

TODO: This is a surrogate for the genuine definition "`Φ ⊗ id_n` is positive for every `n`". The
two are equivalent by the Choi–Kraus theorem; when the forward direction is formalised, this
definition should be replaced and the Kraus form kept only as a characterisation. -/
def IsCompletelyPositive (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Prop :=
  ∃ (r : ℕ) (K : Fin r → Matrix m n ℂ),
    ∀ A, Φ A = ∑ i, K i * A * (K i)ᴴ

/-! ### Quantum Channels -/

/-- A quantum channel is a completely positive trace-preserving (CPTP) map.
These are the physically realizable operations on quantum states. -/
structure IsQuantumChannel (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Prop where
  /-- The map is completely positive -/
  completelyPositive : IsCompletelyPositive Φ
  /-- The map preserves trace -/
  tracePreserving : IsTracePreserving Φ

/-- Quantum channel as a subtype for cleaner API. -/
abbrev QuantumChannel (n : Type*) (m : Type*) [Fintype n] [Fintype m] :=
  { Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ // IsQuantumChannel Φ }

/-- The identity map is a quantum channel. -/
lemma isQuantumChannel_id : IsQuantumChannel (LinearMap.id : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) where
  completelyPositive := by
    classical
    -- id has Kraus representation with single operator K = I
    use 1, fun _ => 1
    intro A
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
    simp [Matrix.conjTranspose_one]
  tracePreserving := fun _ => rfl

/-- Composition of quantum channels is a quantum channel. -/
noncomputable def QuantumChannel.comp
    (Φ : QuantumChannel n m) (Ψ : QuantumChannel m k) : QuantumChannel n k where
  val := Ψ.val.comp Φ.val
  property.completelyPositive := by
    classical
    -- Composition of CP maps is CP
    -- If Φ(A) = Σᵢ Kᵢ A Kᵢ† and Ψ(B) = Σⱼ Lⱼ B Lⱼ†
    -- Then (Ψ∘Φ)(A) = Σⱼ Lⱼ (Σᵢ Kᵢ A Kᵢ†) Lⱼ† = Σᵢⱼ (Lⱼ Kᵢ) A (Lⱼ Kᵢ)†
    obtain ⟨r, K, hK⟩ := Φ.property.completelyPositive
    obtain ⟨s, L, hL⟩ := Ψ.property.completelyPositive
    -- Use product Kraus operators indexed by Fin s × Fin r
    use s * r
    -- Define the combined Kraus operators via equivalence Fin (s * r) ≃ Fin s × Fin r
    let e : Fin (s * r) ≃ Fin s × Fin r := finProdFinEquiv.symm
    use fun p => L (e p).1 * K (e p).2
    intro A
    simp only [LinearMap.comp_apply, hK, hL]
    -- Ψ(Σᵢ Kᵢ A Kᵢ†) = Σⱼ Lⱼ (Σᵢ Kᵢ A Kᵢ†) Lⱼ†
    simp_rw [Matrix.mul_sum, Matrix.sum_mul]
    -- Reindex: ∑_{j,i} = ∑_p via Equiv.sum_comp
    rw [← Fintype.sum_prod_type']
    rw [(Equiv.sum_comp e (fun x => L x.1 * (K x.2 * A * (K x.2)ᴴ) * (L x.1)ᴴ)).symm]
    apply Finset.sum_congr rfl
    intro p _
    -- Need to show: L (e p).1 * (K (e p).2 * A * (K (e p).2)†) * (L (e p).1)†
    --             = L (e p).1 * K (e p).2 * A * (L (e p).1 * K (e p).2)†
    rw [Matrix.conjTranspose_mul]
    -- Now use matrix associativity
    simp only [Matrix.mul_assoc]
  property.tracePreserving := by
    intro A
    simp only [LinearMap.comp_apply]
    rw [Ψ.property.tracePreserving, Φ.property.tracePreserving]

omit [Fintype m] in
/-- A completely positive map preserves Hermitianity of matrices.
If Φ(A) = Σᵢ Kᵢ A Kᵢ† and A is Hermitian, then Φ(A) is Hermitian. -/
lemma IsCompletelyPositive.map_isHermitian
    {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ} (hΦ : IsCompletelyPositive Φ)
    {A : Matrix n n ℂ} (hA : A.IsHermitian) : (Φ A).IsHermitian := by
  classical
  obtain ⟨r, K, hK⟩ := hΦ
  rw [hK]
  rw [Matrix.IsHermitian, Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [Matrix.mul_assoc]
  congr 1
  rw [hA.eq]

omit [Fintype m] in
/-- A completely positive map sends positive semidefinite matrices to positive semidefinite
matrices. -/
lemma IsCompletelyPositive.posSemidef_map [Finite m]
    {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ} (hΦ : IsCompletelyPositive Φ)
    {A : Matrix n n ℂ} (hA : A.PosSemidef) : (Φ A).PosSemidef := by
  classical
  have := Fintype.ofFinite m
  obtain ⟨r, K, hK⟩ := hΦ
  rw [hK]
  exact posSemidef_sum _ fun i _ => hA.mul_mul_conjTranspose_same (K i)

end Matrix
