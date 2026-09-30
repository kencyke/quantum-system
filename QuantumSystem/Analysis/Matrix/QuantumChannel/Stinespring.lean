/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.Matrix.DensityMatrix.Kronecker
public import QuantumSystem.Analysis.Matrix.QuantumChannel.Choi
public import QuantumSystem.Analysis.Matrix.QuantumChannel.Kraus
public import QuantumSystem.ForMathlib.LinearAlgebra.Matrix.PartialTrace
public import QuantumSystem.ForMathlib.LinearAlgebra.Matrix.Trace

/-!
# Stinespring's theorem for matrix channels

Stacking Kraus operators `Kᵢ : M_{m×n}(ℂ)`, `i : ι`, gives a single matrix
`V : Matrix (ι × m) n ℂ`, `V (i, a) b = Kᵢ a b`, which is an isometry `Vᴴ V = I` whenever
the family satisfies the completeness relation `Σᵢ Kᵢᴴ Kᵢ = I`. The Kraus map
`A ↦ Σᵢ Kᵢ A Kᵢᴴ` is recovered as the partial trace `tr₁(V A Vᴴ)` over the environment `ι`.

Conversely the diagonal blocks of any `V : Matrix (ι × m) n ℂ` are Kraus operators for
`A ↦ tr₁(V A Vᴴ)`. Together with Choi's theorem this gives **Stinespring's theorem**: a linear
map is completely positive iff it is `A ↦ tr₁(V A Vᴴ)` for some `V`, and a quantum channel iff
moreover `V` is an isometry (`CompletelyPositiveMap.exists_toLinearMap_eq_iff_exists_stinespring`,
`Matrix.QuantumChannel.exists_toLinearMap_eq_iff_exists_stinespring`). The environment
`E = Fin r` has dimension `r ≤ nm`.

This is the Schrödinger-picture form of Stinespring's dilation (Watrous, Theorem 2.22 and
Corollary 2.27). Stinespring's original Heisenberg-picture statement, that the trace dual is
`Φ*(B) = Vᴴ (1 ⊗ B) V`, is `CompletelyPositiveMap.exists_traceDual_eq_stinespring`, and
`Matrix.QuantumChannel.exists_traceDual_eq_stinespring` with `V` an isometry. For a fixed `V`
the two pictures are equivalent (`Matrix.traceDual_eq_iff_stinespring`).

The environment is the **left** factor of `E × ℂᵐ` and is removed by the partial trace
`tr₁ = Matrix.traceLeft` (the notation of
`QuantumSystem/Analysis/Matrix/DensityMatrix/Kronecker.lean`).

This file treats the finite-dimensional matrix algebras `M_n(ℂ)` only: complete positivity is
Mathlib's `CompletelyPositiveMap` condition for general C⋆-algebras, specialised to `Matrix n n ℂ`.
The operator-algebraic side is not confined to matrices. The Kadison–Schwarz inequality
`φ(a)⋆ φ(a) ≤ ‖φ 1‖ • φ(a⋆ a)` for `2`-positive, in particular completely positive, maps between
arbitrary unital C⋆-algebras is `KPositiveMapClass.le_norm_smul_map_star_mul`, with the normalised
form `KPositiveMapClass.le_map_star_mul` under `φ 1 ≤ 1`
(`QuantumSystem/ForMathlib/Analysis/CStarAlgebra/KPositiveMap.lean`), and Kraus maps between the
operator algebras of arbitrary Hilbert spaces are `SchwarzMap.ofKraus`
(`QuantumSystem/ForMathlib/Analysis/CStarAlgebra/SchwarzMap.lean`). A matrix channel enters that
setting through its trace dual, a Schwarz map on `B(ℂᵐ)` (`Matrix.QuantumChannel.dualSchwarzMap` in
`QuantumSystem/Analysis/Matrix/QuantumChannel/Dual.lean`).

## Main definitions

* `Matrix.stinespringIsometry K`: the stacked Kraus operators.
* `CompletelyPositiveMap.ofStinespring`: `A ↦ tr₁(V A Vᴴ)` as a completely positive map.
* `Matrix.QuantumChannel.ofStinespring`: `A ↦ tr₁(V A Vᴴ)` for an isometry `V` as a quantum
  channel.

## Main statements

* `Matrix.stinespringIsometry_conjTranspose_mul`: `Vᴴ V = I` under Kraus completeness.
* `Matrix.traceLeft_stinespringIsometry_mul_mul_conjTranspose`: `Σᵢ Kᵢ A Kᵢᴴ = tr₁(V A Vᴴ)`,
  the sum of the diagonal blocks of `V A Vᴴ`.
* `Matrix.traceDual_eq_iff_stinespring`: for a fixed `V`, the trace dual is
  `Φ*(B) = Vᴴ (1 ⊗ B) V` for all `B` iff `Φ(A) = tr₁(V A Vᴴ)` for all `A`.
* `CompletelyPositiveMap.exists_toLinearMap_eq_iff_exists_stinespring`: **Stinespring's theorem**:
  a linear map is completely positive iff it is `A ↦ tr₁(V A Vᴴ)` for some `V`.
* `CompletelyPositiveMap.exists_stinespring`: a CP map is `A ↦ tr₁(V A Vᴴ)` for some `V`; the
  converse is `CompletelyPositiveMap.ofStinespring`.
* `CompletelyPositiveMap.exists_traceDual_eq_stinespring`: **Stinespring's theorem, Heisenberg
  picture**: the trace dual of a CP map is `B ↦ Vᴴ (1 ⊗ B) V` for some `V`.
* `Matrix.QuantumChannel.exists_toLinearMap_eq_iff_exists_stinespring`: a linear map is a
  quantum channel iff it is `A ↦ tr₁(V A Vᴴ)` for an isometry `V`.
* `Matrix.QuantumChannel.exists_stinespring`: a quantum channel is `A ↦ tr₁(V A Vᴴ)` for an
  isometry `V`; the converse is `Matrix.QuantumChannel.ofStinespring`.
* `Matrix.QuantumChannel.exists_traceDual_eq_stinespring`: the trace dual of a quantum channel is
  `B ↦ Vᴴ (1 ⊗ B) V` for an isometry `V`.

## References

* W. F. Stinespring, *Positive functions on C*-algebras*, Proc. Amer. Math. Soc. 6 (1955),
  211–216.
* Watrous, *The Theory of Quantum Information*, §2.2
-/

@[expose] public section

namespace Matrix

variable {n m : Type*} [Fintype n] [Fintype m]

open scoped ComplexOrder Kronecker

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
/-- Under the Kraus completeness relation `Σᵢ Kᵢᴴ Kᵢ = I` the Stinespring matrix `V` is an
isometry, `Vᴴ V = I`. -/
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
`Σᵢ Kᵢ A Kᵢᴴ = tr₁(V A Vᴴ)`, the sum of the diagonal blocks of `V A Vᴴ`. -/
lemma traceLeft_stinespringIsometry_mul_mul_conjTranspose {ι : Type*} [Fintype ι]
    (K : ι → Matrix m n ℂ) (A : Matrix n n ℂ) :
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

/-! ### Heisenberg picture -/

section Heisenberg

variable [DecidableEq n] {F : Type*} [FunLike F (Matrix n n ℂ) (Matrix m m ℂ)]
  [LinearMapClass F ℂ (Matrix n n ℂ) (Matrix m m ℂ)]

omit [DecidableEq n] in
/-- The Stinespring pairing: `Tr (tr₁(V A Vᴴ) B) = Tr (A Vᴴ (1 ⊗ B) V)`. -/
lemma trace_traceLeft_mul_mul_conjTranspose_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : Matrix (ι × m) n ℂ) (A : Matrix n n ℂ) (B : Matrix m m ℂ) :
    Tr (traceLeft (V * A * Vᴴ) * B) = Tr (A * (Vᴴ * ((1 : Matrix ι ι ℂ) ⊗ₖ B) * V)) := by
  rw [← trace_mul_kronecker_one_left]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm V]
  simp only [Matrix.mul_assoc]

/-- Heisenberg and Schrödinger pictures of a Stinespring operator `V`: the trace dual of `Φ` is
`Φ*(B) = Vᴴ (1 ⊗ B) V` for all `B` iff `Φ(A) = tr₁(V A Vᴴ)` for all `A`. -/
theorem traceDual_eq_iff_stinespring {ι : Type*} [Fintype ι] [DecidableEq ι] {Φ : F}
    (V : Matrix (ι × m) n ℂ) :
    (∀ B, traceDual Φ B = Vᴴ * ((1 : Matrix ι ι ℂ) ⊗ₖ B) * V) ↔
      ∀ A, Φ A = traceLeft (V * A * Vᴴ) := by
  constructor
  · intro h A
    refine Matrix.ext_iff_trace_mul_right.mpr fun B => ?_
    rw [trace_mul_traceDual, h, trace_traceLeft_mul_mul_conjTranspose_mul]
  · intro hV B
    refine Matrix.ext_iff_trace_mul_left.mpr fun A => ?_
    rw [← trace_mul_traceDual, hV, trace_traceLeft_mul_mul_conjTranspose_mul]

/-- If `Φ(A) = tr₁(V A Vᴴ)` for all `A`, then the trace dual of `Φ` is `Φ*(B) = Vᴴ (1 ⊗ B) V`. -/
theorem traceDual_eq_of_stinespring {ι : Type*} [Fintype ι] [DecidableEq ι] {Φ : F}
    (V : Matrix (ι × m) n ℂ) (hV : ∀ A, Φ A = traceLeft (V * A * Vᴴ)) (B : Matrix m m ℂ) :
    traceDual Φ B = Vᴴ * ((1 : Matrix ι ι ℂ) ⊗ₖ B) * V :=
  (traceDual_eq_iff_stinespring V).2 hV B

end Heisenberg

end Matrix

/-! ### Stinespring's theorem for completely positive maps -/

namespace CompletelyPositiveMap

open Matrix
open scoped ComplexOrder CStarAlgebra

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- **Stinespring's theorem**, converse: conjugation by `V : Matrix (ι × m) n ℂ` followed by
tracing out the environment `ι` is completely positive; its Kraus operators are the diagonal blocks
of `V`. -/
def ofStinespring (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) {ι : Type*} [Fintype ι]
    (V : Matrix (ι × m) n ℂ) (hV : ∀ A, Φ A = traceLeft (V * A * Vᴴ)) :
    Matrix n n ℂ →CP Matrix m m ℂ :=
  ofKraus Φ (fun i => Matrix.of fun a b => V (i, a) b) fun A => by
    rw [hV, ← traceLeft_stinespringIsometry_mul_mul_conjTranspose, stinespringIsometry_blocks]

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- The completely positive map `CompletelyPositiveMap.ofStinespring Φ V hV` is `Φ` as a function. -/
@[simp] lemma coe_ofStinespring (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) {ι : Type*} [Fintype ι]
    (V : Matrix (ι × m) n ℂ) (hV : ∀ A, Φ A = traceLeft (V * A * Vᴴ)) :
    ⇑(ofStinespring Φ V hV) = Φ :=
  rfl

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- **Stinespring's theorem** for matrix algebras: a completely positive map
`φ : M_n(ℂ) → M_m(ℂ)` is `φ(A) = tr₁(V A Vᴴ)` for some `V : ℂⁿ → ℂ^E ⊗ ℂᵐ` with environment
`E = Fin r`, `r ≤ nm`. Conversely every such map is completely positive
(`CompletelyPositiveMap.ofStinespring`). -/
theorem exists_stinespring (φ : Matrix n n ℂ →CP Matrix m m ℂ) :
    ∃ r ≤ Fintype.card n * Fintype.card m,
      ∃ V : Matrix (Fin r × m) n ℂ, ∀ A, φ A = traceLeft (V * A * Vᴴ) := by
  obtain ⟨r, hr, K, hK⟩ := φ.exists_kraus
  exact ⟨r, hr, stinespringIsometry K, fun A => by
    rw [hK, traceLeft_stinespringIsometry_mul_mul_conjTranspose]⟩

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- **Stinespring's theorem** for matrix algebras: a linear map `Φ : M_n(ℂ) → M_m(ℂ)` is
completely positive, i.e. it is the linear map of some `φ : M_n(ℂ) →CP M_m(ℂ)`, iff
`Φ(A) = tr₁(V A Vᴴ)` for some `V : ℂⁿ → ℂ^E ⊗ ℂᵐ` with environment `E = Fin r`, `r ≤ nm`. -/
theorem exists_toLinearMap_eq_iff_exists_stinespring (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    (∃ φ : Matrix n n ℂ →CP Matrix m m ℂ, φ.toLinearMap = Φ) ↔
      ∃ r ≤ Fintype.card n * Fintype.card m,
        ∃ V : Matrix (Fin r × m) n ℂ, ∀ A, Φ A = traceLeft (V * A * Vᴴ) :=
  ⟨fun ⟨φ, hφ⟩ => hφ ▸ φ.exists_stinespring, fun ⟨_, _, V, hV⟩ => ⟨ofStinespring Φ V hV, rfl⟩⟩

open scoped Matrix.Norms.L2Operator MatrixOrder Kronecker in
/-- **Stinespring's theorem, Heisenberg picture**, for matrix algebras: the trace dual of a
completely positive map `φ : M_n(ℂ) → M_m(ℂ)` is `φ*(B) = Vᴴ (1 ⊗ B) V` for some
`V : ℂⁿ → ℂ^E ⊗ ℂᵐ` with environment `E = Fin r`, `r ≤ nm`. -/
theorem exists_traceDual_eq_stinespring (φ : Matrix n n ℂ →CP Matrix m m ℂ) :
    ∃ r ≤ Fintype.card n * Fintype.card m, ∃ V : Matrix (Fin r × m) n ℂ,
      ∀ B, traceDual φ B = Vᴴ * ((1 : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ B) * V := by
  obtain ⟨r, hr, V, hV⟩ := φ.exists_stinespring
  exact ⟨r, hr, V, traceDual_eq_of_stinespring V hV⟩

end CompletelyPositiveMap

namespace Matrix

variable {n m : Type*} [Fintype n] [Fintype m]

open scoped ComplexOrder Kronecker

/-! ### Quantum channels -/

variable [DecidableEq n] [DecidableEq m]

/-- **Stinespring's theorem** for quantum channels: a quantum channel `Φ : M_n(ℂ) → M_m(ℂ)` is
`Φ(A) = tr₁(V A Vᴴ)` for an isometry `V : ℂⁿ → ℂ^E ⊗ ℂᵐ`, `Vᴴ V = I`, with environment
`E = Fin r`, `r ≤ nm`. Conversely every such map is a quantum channel
(`Matrix.QuantumChannel.ofStinespring`). -/
theorem QuantumChannel.exists_stinespring (Φ : QuantumChannel n m) :
    ∃ r ≤ Fintype.card n * Fintype.card m,
      ∃ V : Matrix (Fin r × m) n ℂ, Vᴴ * V = 1 ∧ ∀ A, Φ.val A = traceLeft (V * A * Vᴴ) := by
  obtain ⟨r, hr, K, hK⟩ := Φ.val.exists_kraus
  exact ⟨r, hr, stinespringIsometry K,
    stinespringIsometry_conjTranspose_mul (Φ.property.kraus_sum_eq_one hK),
    fun A => by rw [hK, traceLeft_stinespringIsometry_mul_mul_conjTranspose]⟩

/-- **Stinespring's theorem, Heisenberg picture**, for quantum channels: the trace dual of a
quantum channel `Φ : M_n(ℂ) → M_m(ℂ)` is the unital map `Φ*(B) = Vᴴ (1 ⊗ B) V` for an isometry
`V : ℂⁿ → ℂ^E ⊗ ℂᵐ`, `Vᴴ V = I`, with environment `E = Fin r`, `r ≤ nm`. -/
theorem QuantumChannel.exists_traceDual_eq_stinespring (Φ : QuantumChannel n m) :
    ∃ r ≤ Fintype.card n * Fintype.card m, ∃ V : Matrix (Fin r × m) n ℂ, Vᴴ * V = 1 ∧
      ∀ B, traceDual Φ.toLinearMap B = Vᴴ * ((1 : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ B) * V := by
  obtain ⟨r, hr, V, hVV, hV⟩ := Φ.exists_stinespring
  exact ⟨r, hr, V, hVV, traceDual_eq_of_stinespring V hV⟩

/-- **Stinespring's theorem** for quantum channels, converse: `A ↦ tr₁(V A Vᴴ)` for an isometry
`V`, `Vᴴ V = I`, is a quantum channel. -/
noncomputable def QuantumChannel.ofStinespring (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) {ι : Type*} [Fintype ι]
    (V : Matrix (ι × m) n ℂ) (hVV : Vᴴ * V = 1) (hV : ∀ A, Φ A = traceLeft (V * A * Vᴴ)) : QuantumChannel n m :=
  ⟨.ofStinespring Φ V hV, fun A => by
    change Tr (Φ A) = Tr A
    rw [hV, trace_traceLeft, Matrix.trace_mul_cycle, hVV, Matrix.one_mul]⟩

/-- The quantum channel `Matrix.QuantumChannel.ofStinespring Φ V hVV hV` is `Φ` as a function. -/
@[simp] lemma QuantumChannel.coe_ofStinespring (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) {ι : Type*} [Fintype ι]
    (V : Matrix (ι × m) n ℂ) (hVV : Vᴴ * V = 1) (hV : ∀ A, Φ A = traceLeft (V * A * Vᴴ)) :
    ⇑(QuantumChannel.ofStinespring Φ V hVV hV).val = Φ :=
  rfl

/-- **Stinespring's theorem** for quantum channels: a linear map `Φ : M_n(ℂ) → M_m(ℂ)` is a quantum
channel iff `Φ(A) = tr₁(V A Vᴴ)` for an isometry `V : ℂⁿ → ℂ^E ⊗ ℂᵐ`, `Vᴴ V = I`, with
environment `E = Fin r`, `r ≤ nm`. -/
theorem QuantumChannel.exists_toLinearMap_eq_iff_exists_stinespring (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    (∃ Ψ : QuantumChannel n m, Ψ.toLinearMap = Φ) ↔
      ∃ r ≤ Fintype.card n * Fintype.card m,
        ∃ V : Matrix (Fin r × m) n ℂ, Vᴴ * V = 1 ∧ ∀ A, Φ A = traceLeft (V * A * Vᴴ) :=
  ⟨fun ⟨Ψ, hΨ⟩ => hΨ ▸ Ψ.exists_stinespring,
    fun ⟨_, _, V, hVV, hV⟩ => ⟨QuantumChannel.ofStinespring Φ V hVV hV, rfl⟩⟩

end Matrix
