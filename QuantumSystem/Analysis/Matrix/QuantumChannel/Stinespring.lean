/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.Matrix.QuantumChannel.CPTP

/-!
# The Stinespring isometry of a Kraus family

Stacking Kraus operators `Kᵢ : M_{m×n}(ℂ)` gives a single matrix
`V : Matrix (Fin r × m) n ℂ`, `V (i, a) b = Kᵢ a b`, which is an isometry `Vᴴ V = I` whenever
the family satisfies the completeness relation `Σᵢ Kᵢᴴ Kᵢ = I`.

## Main definitions

* `Matrix.stinespringIsometry K`: the stacked Kraus operators.

## Main statements

* `Matrix.stinespringIsometry_conjTranspose_mul`: `Vᴴ V = I` under Kraus completeness.

## References

* Watrous, *The Theory of Quantum Information*, §2.2
-/

@[expose] public section

namespace Matrix

variable {n m : Type*} [Fintype n] [Fintype m]

open scoped ComplexOrder

/-! ### Stinespring Isometry -/

/-- Stinespring isometry: stack Kraus operators into a single isometry
V : Matrix (Fin r × m) n ℂ defined by V (i, a) b = Kᵢ a b.
Then V†V = I (from Kraus completeness) and Φ(A) = Σᵢ (i-th block of VAV†). -/
noncomputable def stinespringIsometry {r : ℕ} (K : Fin r → Matrix m n ℂ) :
    Matrix (Fin r × m) n ℂ :=
  Matrix.of fun ⟨i, a⟩ b => K i a b

omit [Fintype n] in
lemma stinespringIsometry_conjTranspose_mul {r : ℕ} [DecidableEq n]
    {K : Fin r → Matrix m n ℂ} (hK : ∑ i, (K i)ᴴ * K i = 1) :
    (stinespringIsometry K)ᴴ * stinespringIsometry K = 1 := by
  ext a b
  simp only [stinespringIsometry, Matrix.conjTranspose_apply, Matrix.mul_apply,
    Matrix.of_apply, Matrix.one_apply, Fintype.sum_prod_type]
  have heq : ∀ i, ∑ j : m, star (K i j a) * K i j b = ((K i)ᴴ * K i) a b := fun i => by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp only [heq]
  rw [← Matrix.sum_apply, hK, Matrix.one_apply]

end Matrix
