/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.Matrix.QuantumChannel.CPTP

/-!
# Kraus completeness for quantum channels

Every Kraus representation `Φ(A) = Σᵢ Kᵢ A Kᵢᴴ` of a trace-preserving map satisfies the
completeness relation `Σᵢ Kᵢᴴ Kᵢ = I`.

## Main statements

* `Matrix.QuantumChannel.kraus_sum_eq_one`: the completeness relation `Σᵢ Kᵢᴴ Kᵢ = I`.

## References

* Nielsen, Chuang, *Quantum Computation and Quantum Information*, §8.2.3
-/

@[expose] public section

namespace Matrix

variable {n m : Type*} [Fintype n] [Fintype m]

open scoped ComplexOrder

/-! ### Kraus Completeness -/

/-- If `Tr(M * A) = Tr(A)` for all `A`, then `M = 1`. -/
private lemma matrix_eq_one_of_trace_mul [DecidableEq n]
    (M : Matrix n n ℂ) (h : ∀ A : Matrix n n ℂ, Tr (M * A) = Tr A) : M = 1 :=
  Matrix.ext_iff_trace_mul_right.mpr fun A => by rw [one_mul]; exact h A

/-- Trace-preserving Kraus channels satisfy the completeness relation: ∑ₖ Kₖ† Kₖ = I. -/
lemma QuantumChannel.kraus_sum_eq_one [DecidableEq n]
    (Φ : QuantumChannel n m)
    {r : ℕ} {K : Fin r → Matrix m n ℂ} (hK : ∀ A, Φ.val A = ∑ i, K i * A * (K i)ᴴ) :
    ∑ i, (K i)ᴴ * K i = 1 := by
  apply matrix_eq_one_of_trace_mul
  intro A
  have key : ∀ i : Fin r, ((K i)ᴴ * K i * A).trace = (K i * A * (K i)ᴴ).trace := fun i => by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm (K i)ᴴ]
  rw [Finset.sum_mul]
  simp_rw [Matrix.trace_sum, key, ← Matrix.trace_sum]
  have := Φ.property.tracePreserving A
  rwa [hK] at this

end Matrix
