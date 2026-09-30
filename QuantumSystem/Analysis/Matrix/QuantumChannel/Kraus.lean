/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.Matrix.QuantumChannel.CPTP

/-!
# Kraus completeness for quantum channels

Every Kraus representation `Φ(A) = Σᵢ Kᵢ A Kᵢᴴ` of a trace-preserving linear map satisfies the
completeness relation `Σᵢ Kᵢᴴ Kᵢ = I`; complete positivity is not used.

## Main statements

* `Matrix.IsTracePreserving.kraus_sum_eq_one`: the completeness relation `Σᵢ Kᵢᴴ Kᵢ = I`.

## References

* Nielsen, Chuang, *Quantum Computation and Quantum Information*, §8.2.3
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

end Matrix
