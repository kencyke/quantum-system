/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.Matrix.QuantumChannel.Choi

/-!
# Kraus representations of quantum channels

Every Kraus representation `Φ(A) = Σᵢ Kᵢ A Kᵢᴴ` of a trace-preserving linear map satisfies the
completeness relation `Σᵢ Kᵢᴴ Kᵢ = I`; complete positivity is not used. Conversely a Kraus map with
`Σᵢ Kᵢᴴ Kᵢ = I` is trace preserving, so a linear map is a quantum channel iff it has a Kraus
representation satisfying the completeness relation, with `rank J(Φ)` operators.

## Main definitions

* `Matrix.QuantumChannel.ofKraus`: the quantum channel of a Kraus representation with
  `Σᵢ Kᵢᴴ Kᵢ = I`.

## Main statements

* `Matrix.IsTracePreserving.kraus_sum_eq_one`: the completeness relation `Σᵢ Kᵢᴴ Kᵢ = I`.
* `Matrix.QuantumChannel.exists_kraus`: a quantum channel has a Kraus representation with
  `rank J(Φ)` operators satisfying `Σᵢ Kᵢᴴ Kᵢ = I`.
* `Matrix.QuantumChannel.exists_coe_eq_iff_exists_kraus`: **Kraus representation of
  quantum channels**, a linear map is a quantum channel iff `Φ(A) = Σᵢ Kᵢ A Kᵢᴴ` with
  `Σᵢ Kᵢᴴ Kᵢ = I`.

## References

* Nielsen, Chuang, *Quantum Computation and Quantum Information*, §8.2.3 and Theorem 8.1
* Watrous, *The Theory of Quantum Information*, Corollary 2.27
-/

@[expose] public section

namespace Matrix

variable {n m : Type*} [Fintype n] [Fintype m]
variable {F : Type*} [FunLike F (Matrix n n ℂ) (Matrix m m ℂ)]

open scoped ComplexOrder

/-! ### Kraus Completeness -/

/-- If `Tr(M * A) = Tr(A)` for all `A`, then `M = 1`. -/
private lemma matrix_eq_one_of_trace_mul [DecidableEq n]
    (M : Matrix n n ℂ) (h : ∀ A : Matrix n n ℂ, Tr (M * A) = Tr A) : M = 1 :=
  Matrix.ext_iff_trace_mul_right.mpr fun A => by rw [one_mul]; exact h A

/-- Kraus representations of trace-preserving maps satisfy the completeness relation
`Σᵢ Kᵢᴴ Kᵢ = I`. Complete positivity is not needed. -/
lemma IsTracePreserving.kraus_sum_eq_one [DecidableEq n] {Φ : F} (hΦ : IsTracePreserving Φ)
    {ι : Type*} [Fintype ι] {K : ι → Matrix m n ℂ} (hK : ∀ A, Φ A = ∑ i, K i * A * (K i)ᴴ) :
    ∑ i, (K i)ᴴ * K i = 1 := by
  apply matrix_eq_one_of_trace_mul
  intro A
  have key : ∀ i, ((K i)ᴴ * K i * A).trace = (K i * A * (K i)ᴴ).trace := fun i => by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm (K i)ᴴ]
  rw [Finset.sum_mul]
  simp_rw [Matrix.trace_sum, key, ← Matrix.trace_sum]
  have := hΦ A
  rwa [hK] at this

/-! ### Kraus representation of quantum channels -/

variable [DecidableEq n] [DecidableEq m]

omit [DecidableEq m] in
/-- A Kraus map with `Σᵢ Kᵢᴴ Kᵢ = I` is trace preserving: `Tr (Σᵢ Kᵢ A Kᵢᴴ) = Tr ((Σᵢ Kᵢᴴ Kᵢ) A)`. -/
lemma isTracePreserving_of_kraus {Φ : F} {ι : Type*} [Fintype ι] {K : ι → Matrix m n ℂ}
    (hK : ∀ A, Φ A = ∑ i, K i * A * (K i)ᴴ) (hKK : ∑ i, (K i)ᴴ * K i = 1) :
    IsTracePreserving Φ := fun A => by
  rw [hK, Matrix.trace_sum]
  simp_rw [Matrix.trace_mul_cycle _ A]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, hKK, Matrix.one_mul]

/-- The quantum channel of a Kraus representation `Φ(A) = Σᵢ Kᵢ A Kᵢᴴ` with `Σᵢ Kᵢᴴ Kᵢ = I`. -/
noncomputable def QuantumChannel.ofKraus (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) {ι : Type*}
    [Fintype ι] (K : ι → Matrix m n ℂ) (hK : ∀ A, Φ A = ∑ i, K i * A * (K i)ᴴ)
    (hKK : ∑ i, (K i)ᴴ * K i = 1) : QuantumChannel n m :=
  ⟨.ofKraus Φ K hK, isTracePreserving_of_kraus (Φ := Φ) hK hKK⟩

/-- The quantum channel `Matrix.QuantumChannel.ofKraus Φ K hK hKK` is `Φ` as a function. -/
@[simp] lemma QuantumChannel.coe_ofKraus (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) {ι : Type*}
    [Fintype ι] (K : ι → Matrix m n ℂ) (hK : ∀ A, Φ A = ∑ i, K i * A * (K i)ᴴ)
    (hKK : ∑ i, (K i)ᴴ * K i = 1) : ⇑(QuantumChannel.ofKraus Φ K hK hKK) = Φ :=
  rfl

/-- A quantum channel has a Kraus representation `Φ(A) = Σₐ Kₐ A Kₐᴴ` with `rank J(Φ)` operators,
the minimal number (`Matrix.rank_choiMatrix_le_card_of_kraus`), satisfying the completeness
relation `Σₐ Kₐᴴ Kₐ = I`. -/
theorem QuantumChannel.exists_kraus (Φ : QuantumChannel n m) :
    ∃ K : Fin (choiMatrix Φ).rank → Matrix m n ℂ,
      (∀ A, Φ A = ∑ a, K a * A * (K a)ᴴ) ∧ ∑ a, (K a)ᴴ * K a = 1 := by
  obtain ⟨K, hK⟩ := Φ.toCompletelyPositiveMap.exists_kraus_rank
  exact ⟨K, hK, Φ.isTracePreserving.kraus_sum_eq_one hK⟩

/-- **Kraus representation of quantum channels** (Nielsen–Chuang, Theorem 8.1): a linear map
`Φ : M_n(ℂ) → M_m(ℂ)` is a quantum channel iff `Φ(A) = Σₐ Kₐ A Kₐᴴ` with `Σₐ Kₐᴴ Kₐ = I`, and then
with `rank J(Φ)` operators. -/
theorem QuantumChannel.exists_coe_eq_iff_exists_kraus
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    (∃ Ψ : QuantumChannel n m, (Ψ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) = Φ) ↔
      ∃ K : Fin (choiMatrix Φ).rank → Matrix m n ℂ,
        (∀ A, Φ A = ∑ a, K a * A * (K a)ᴴ) ∧ ∑ a, (K a)ᴴ * K a = 1 :=
  ⟨fun ⟨Ψ, hΨ⟩ => hΨ ▸ Ψ.exists_kraus,
    fun ⟨K, hK, hKK⟩ => ⟨QuantumChannel.ofKraus Φ K hK hKK, rfl⟩⟩

end Matrix
