/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.Matrix.QuantumChannel.Choi
public import QuantumSystem.Analysis.Matrix.QuantumChannel.Kraus
public import QuantumSystem.ForMathlib.LinearAlgebra.Matrix.PartialTrace

/-!
# Stinespring's theorem for matrix channels

Stacking Kraus operators `Kᵢ : M_{m×n}(ℂ)`, `i : ι`, gives a single matrix
`V : Matrix (ι × m) n ℂ`, `V (i, a) b = Kᵢ a b`, which is an isometry `Vᴴ V = I` whenever
the family satisfies the completeness relation `Σᵢ Kᵢᴴ Kᵢ = I`. The Kraus map
`A ↦ Σᵢ Kᵢ A Kᵢᴴ` is recovered as the partial trace over the environment `ι` of `V A Vᴴ`.

Conversely the diagonal blocks of any `V : Matrix (ι × m) n ℂ` are Kraus operators for
`A ↦ Tr_ι (V A Vᴴ)`. Together with Choi's theorem this gives **Stinespring's theorem**: a linear
map is completely positive iff it is `A ↦ Tr_E (V A Vᴴ)` for some `V`, and a quantum channel iff
moreover `V` is an isometry. The environment `E = Fin r` has dimension `r ≤ nm`.

This is the Schrödinger-picture form of Stinespring's dilation (Watrous, Theorem 2.22 and
Corollary 2.27). Stinespring's original Heisenberg-picture statement `Φ*(B) = Vᴴ (1 ⊗ B) V` for the
trace dual is equivalent to it.

The environment is the **left** factor of `E × ℂᵐ` and is removed by `Matrix.traceLeft`.

## Main definitions

* `Matrix.stinespringIsometry K`: the stacked Kraus operators.

## Main statements

* `Matrix.stinespringIsometry_conjTranspose_mul`: `Vᴴ V = I` under Kraus completeness.
* `Matrix.traceLeft_stinespringIsometry_mul_mul_conjTranspose`: `Σᵢ Kᵢ A Kᵢᴴ` is the partial
  trace over `ι` of `V A Vᴴ`, the sum of its diagonal blocks.
* `Matrix.isCompletelyPositive_of_stinespring`: `A ↦ Tr_ι (V A Vᴴ)` is completely positive.
* `Matrix.isCompletelyPositive_iff_exists_stinespring`: **Stinespring's theorem** for completely
  positive maps.
* `Matrix.isQuantumChannel_iff_exists_stinespring`: a linear map is a quantum channel iff it is
  `A ↦ Tr_E (V A Vᴴ)` for an isometry `V`.

## References

* W. F. Stinespring, *Positive functions on C*-algebras*, Proc. Amer. Math. Soc. 6 (1955),
  211–216.
* Watrous, *The Theory of Quantum Information*, §2.2
-/

@[expose] public section

namespace Matrix

variable {n m : Type*} [Fintype n] [Fintype m]

open scoped ComplexOrder

/-! ### Stinespring Isometry -/

/-- Stinespring isometry: stack Kraus operators into a single matrix
`V : Matrix (ι × m) n ℂ` defined by `V (i, a) b = Kᵢ a b`.
Then `Vᴴ V = I` under Kraus completeness (`stinespringIsometry_conjTranspose_mul`) and
`Σᵢ Kᵢ A Kᵢᴴ` is the sum of the diagonal blocks of `V A Vᴴ`
(`traceLeft_stinespringIsometry_mul_mul_conjTranspose`). -/
noncomputable def stinespringIsometry {ι : Type*} (K : ι → Matrix m n ℂ) :
    Matrix (ι × m) n ℂ :=
  Matrix.of fun ⟨i, a⟩ b => K i a b

omit [Fintype n] in
lemma stinespringIsometry_conjTranspose_mul {ι : Type*} [Fintype ι] [DecidableEq n]
    {K : ι → Matrix m n ℂ} (hK : ∑ i, (K i)ᴴ * K i = 1) :
    (stinespringIsometry K)ᴴ * stinespringIsometry K = 1 := by
  ext a b
  simp only [stinespringIsometry, Matrix.conjTranspose_apply, Matrix.mul_apply,
    Matrix.of_apply, Matrix.one_apply, Fintype.sum_prod_type]
  have heq : ∀ i, ∑ j : m, star (K i j a) * K i j b = ((K i)ᴴ * K i) a b := fun i => by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp only [heq]
  rw [← Matrix.sum_apply, hK, Matrix.one_apply]

omit [Fintype m] in
/-- The Kraus map is the partial trace over `ι` of conjugation by the Stinespring isometry:
`Σᵢ Kᵢ A Kᵢᴴ = Tr_ι (V A Vᴴ)`, the sum of the diagonal blocks of `V A Vᴴ`. -/
lemma traceLeft_stinespringIsometry_mul_mul_conjTranspose {ι : Type*} [Fintype ι]
    (K : ι → Matrix m n ℂ)
    (A : Matrix n n ℂ) :
    traceLeft (stinespringIsometry K * A * (stinespringIsometry K)ᴴ) =
      ∑ i, K i * A * (K i)ᴴ := by
  ext a b
  simp only [traceLeft_apply, Matrix.sum_apply, stinespringIsometry, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.of_apply]

omit [Fintype n] [Fintype m] in
/-- Every matrix `V : Matrix (ι × m) n ℂ` is the Stinespring isometry of its diagonal blocks
`Kᵢ a b = V (i, a) b`. -/
lemma stinespringIsometry_blocks {ι : Type*} (V : Matrix (ι × m) n ℂ) :
    stinespringIsometry (fun i => Matrix.of fun a b => V (i, a) b) = V := by
  ext ⟨i, a⟩ b
  rfl

/-! ### Stinespring's theorem -/

variable [DecidableEq n] [DecidableEq m]

/-- Conjugation by `V : Matrix (ι × m) n ℂ` followed by tracing out the environment `ι` is
completely positive: its Kraus operators are the diagonal blocks of `V`. -/
theorem isCompletelyPositive_of_stinespring {ι : Type*} [Fintype ι]
    {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ} (V : Matrix (ι × m) n ℂ)
    (hV : ∀ A, Φ A = traceLeft (V * A * Vᴴ)) : IsCompletelyPositive Φ := by
  refine isCompletelyPositive_of_kraus (fun i => Matrix.of fun a b => V (i, a) b) fun A => ?_
  rw [hV, ← traceLeft_stinespringIsometry_mul_mul_conjTranspose, stinespringIsometry_blocks]

/-- **Stinespring's theorem** for matrix algebras: `Φ : M_n(ℂ) → M_m(ℂ)` is completely positive
iff `Φ(A) = Tr_E (V A Vᴴ)` for some `V : ℂⁿ → ℂ^E ⊗ ℂᵐ` with environment `E = Fin r`,
`r ≤ nm`. -/
theorem isCompletelyPositive_iff_exists_stinespring {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ} :
    IsCompletelyPositive Φ ↔ ∃ r ≤ Fintype.card n * Fintype.card m,
      ∃ V : Matrix (Fin r × m) n ℂ, ∀ A, Φ A = traceLeft (V * A * Vᴴ) := by
  refine ⟨fun hΦ => ?_, fun ⟨_, _, V, hV⟩ => isCompletelyPositive_of_stinespring V hV⟩
  obtain ⟨r, hr, K, hK⟩ := isCompletelyPositive_iff_exists_kraus.1 hΦ
  exact ⟨r, hr, stinespringIsometry K, fun A => by
    rw [hK, traceLeft_stinespringIsometry_mul_mul_conjTranspose]⟩

/-- **Stinespring's theorem** for quantum channels: `Φ : M_n(ℂ) → M_m(ℂ)` is completely positive
and trace preserving iff `Φ(A) = Tr_E (V A Vᴴ)` for an isometry `V : ℂⁿ → ℂ^E ⊗ ℂᵐ`,
`Vᴴ V = I`, with environment `E = Fin r`, `r ≤ nm`. -/
theorem isQuantumChannel_iff_exists_stinespring {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ} :
    IsQuantumChannel Φ ↔ ∃ r ≤ Fintype.card n * Fintype.card m,
      ∃ V : Matrix (Fin r × m) n ℂ, Vᴴ * V = 1 ∧ ∀ A, Φ A = traceLeft (V * A * Vᴴ) := by
  constructor
  · rintro ⟨hCP, hTP⟩
    obtain ⟨r, hr, K, hK⟩ := isCompletelyPositive_iff_exists_kraus.1 hCP
    exact ⟨r, hr, stinespringIsometry K,
      stinespringIsometry_conjTranspose_mul (hTP.kraus_sum_eq_one hK),
      fun A => by rw [hK, traceLeft_stinespringIsometry_mul_mul_conjTranspose]⟩
  · rintro ⟨_, _, V, hVV, hV⟩
    refine ⟨isCompletelyPositive_of_stinespring V hV, fun A => ?_⟩
    rw [hV, trace_traceLeft, Matrix.trace_mul_cycle, hVV, Matrix.one_mul]

end Matrix
