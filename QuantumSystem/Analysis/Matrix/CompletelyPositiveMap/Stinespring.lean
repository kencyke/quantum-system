/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.Matrix.CompletelyPositiveMap.Choi
public import QuantumSystem.ForMathlib.LinearAlgebra.Matrix.PartialTrace
public import QuantumSystem.Notation

/-!
# Stinespring's theorem for completely positive maps of matrices

A linear map `Φ : M_n(ℂ) → M_m(ℂ)` is completely positive iff it is `A ↦ tr₂(V A Vᴴ)` for some
`V : Matrix (m × Fin r) n ℂ` (`CompletelyPositiveMap.exists_coe_eq_iff_exists_stinespringMatrix`).
The environment `E = Fin r` has the dimension `r = rank J(Φ) ≤ nm` of the Choi matrix `J(Φ)`, and
this is minimal: every such `V` has an environment with at least `rank J(Φ)` elements
(`Matrix.rank_choiMatrix_le_card_of_stinespring`), with equality iff its Kraus blocks are linearly
independent (`Matrix.rank_choiMatrix_eq_card_iff_linearIndependent_krausBlock`). Here
`tr₂ = Matrix.traceRight` traces out the environment.

This is the Schrödinger-picture form of Stinespring's dilation (Watrous, Theorem 2.22 and
Corollary 2.27). Stinespring's original Heisenberg-picture statement is about the trace dual
`Φ*`, which is defined once, for bounded operators (`ContinuousLinearMap.traceDual`): for the
operator form `Ψ : B(ℂⁿ) → B(ℂᵐ)` of `Φ`, `Ψ(A') = Φ(A)'` with `A' = Matrix.toEuclideanCLM A`,
the trace dual is `Ψ*(B') = (Vᴴ (B ⊗ 1) V)'`
(`CompletelyPositiveMap.exists_traceDual_eq_stinespringMatrix`). For a fixed `V` the two pictures
are equivalent (`Matrix.traceDual_eq_iff_stinespring`), by the trace duality
`tr(Ψ(A') ∘ B') = tr(A' ∘ Ψ*(B'))` and `tr(A' ∘ B') = Tr (A B)` (`Matrix.trace_toEuclideanCLM`).

Completely positive trace-preserving maps, and the isometry `V† V = 1` of their Stinespring dilations, are treated only for
bounded operators on finite-dimensional Hilbert spaces
(`CPTPMap.exists_coe_eq_iff_exists_stinespring`, and in the Heisenberg picture
`CPTPMap.exists_traceDual_eq_stinespring`, in
`QuantumSystem/Analysis/CStarAlgebra/CompletelyPositiveMap/Stinespring.lean`); matrices reach them through
`Matrix.toEuclideanCLM : M_n(ℂ) ≃ B(ℂⁿ)`.

## Kraus blocks

Write `V : Matrix (m × ι) n ℂ` as `V = Σᵢ Kᵢ ⊗ eᵢ` with the Kraus blocks `Kᵢ a b = V (a, i) b`
(`Matrix.krausBlock V i`). They are Kraus operators for `A ↦ tr₂(V A Vᴴ) = Σᵢ Kᵢ A Kᵢᴴ`
(`Matrix.traceRight_mul_mul_conjTranspose`), and every family of Kraus operators is the family of
Kraus blocks of `Σᵢ Kᵢ ⊗ eᵢ` (`Matrix.exists_krausBlock_eq`). Since `Vᴴ V = Σᵢ Kᵢᴴ Kᵢ`, the matrix
`V` is an isometry iff its Kraus blocks satisfy the completeness relation `Σᵢ Kᵢᴴ Kᵢ = I`.

Stinespring's theorem for matrices is therefore the Choi–Kraus theorem
(`QuantumSystem/Analysis/Matrix/CompletelyPositiveMap/Choi.lean`): `V` stacks a Kraus representation with
`rank J(φ)` operators (`CompletelyPositiveMap.exists_kraus_rank`). That representation in turn comes
from Stinespring's theorem for bounded operators
(`QuantumSystem/Analysis/CStarAlgebra/CompletelyPositiveMap/Stinespring.lean`), applied to the operator form
of `φ` on `B(ℂⁿ)`, where the minimality of the Stinespring dilation makes the Kraus blocks linearly
independent.

## Conventions

The environment is the **right** factor of `ℂᵐ ⊗ ℂ^E`, indexed by `m × E`, and is removed by the
partial trace `tr₂ = Matrix.traceRight`. This is Watrous's convention, `Φ(X) = Tr_Z (A X A*)` with
`A : X → Y ⊗ Z`, and Stinespring's `π(B) = B ⊗ 1` on `ℂᵐ ⊗ ℂʳ`. The Choi matrix keeps Choi's
ordering, input first (`QuantumSystem/Analysis/Matrix/CompletelyPositiveMap/Choi.lean`).

This file treats the finite-dimensional matrix algebras `M_n(ℂ)`: complete positivity is
Mathlib's `CompletelyPositiveMap` condition for general C⋆-algebras, specialised to `Matrix n n ℂ`.
The operator-algebraic side is not confined to matrices. Stinespring's theorem itself holds for
completely positive maps `A → B(H)` on arbitrary, possibly non-unital, C⋆-algebras
(`CompletelyPositiveMap.exists_stinespring_dilation`). The Kadison–Schwarz inequality
`φ(a)⋆ φ(a) ≤ ‖φ 1‖ • φ(a⋆ a)` for `2`-positive, in particular completely positive, maps on an
arbitrary unital C⋆-algebra, into a possibly non-unital one, is
`KPositiveMapClass.le_norm_smul_map_star_mul`, with `‖φ‖` in place of `‖φ 1‖` on a non-unital
domain (`KPositiveMapClass.le_opNorm_smul_map_star_mul`) and the normalised form
`KPositiveMapClass.le_map_star_mul` under `φ 1 ≤ 1` between unital C⋆-algebras
(`QuantumSystem/ForMathlib/Analysis/CStarAlgebra/KPositiveMap.lean`), and Kraus maps between the
operator algebras of arbitrary Hilbert spaces are `SchwarzMap.ofKraus`
(`QuantumSystem/ForMathlib/Analysis/CStarAlgebra/SchwarzMap.lean`).

## Main definitions

* `Matrix.krausBlock V i`: the Kraus block `Kᵢ a b = V (a, i) b` of `V : Matrix (m × ι) n ℂ`,
  so that `V = Σᵢ Kᵢ ⊗ eᵢ`.

## Main statements

* `Matrix.conjTranspose_mul_self_eq_sum_krausBlock`: `Vᴴ V = Σᵢ Kᵢᴴ Kᵢ`.
* `Matrix.traceRight_mul_mul_conjTranspose`: `tr₂(V A Vᴴ) = Σᵢ Kᵢ A Kᵢᴴ`, the sum of the diagonal
  blocks of `V A Vᴴ`.
* `Matrix.traceDual_eq_iff_stinespring`: for a fixed `V`, the trace dual of the operator form `Ψ`
  of `Φ` is `Ψ*(B') = (Vᴴ (B ⊗ 1) V)'` for all `B` iff `Φ(A) = tr₂(V A Vᴴ)` for all `A`.
* `Matrix.rank_choiMatrix_le_card_of_stinespring`: **minimality**: every `V` with
  `Φ(A) = tr₂(V A Vᴴ)` has an environment with at least `rank J(Φ)` elements;
  `Matrix.rank_choiMatrix_eq_card_iff_linearIndependent_krausBlock`: with equality iff its Kraus
  blocks are linearly independent.
* `CompletelyPositiveMap.exists_stinespringMatrix`: a CP map is `A ↦ tr₂(V A Vᴴ)` for some `V`
  with environment `Fin (rank J(φ))`.
* `CompletelyPositiveMap.exists_traceDual_eq_stinespringMatrix`: **Stinespring's theorem,
  Heisenberg picture**: the trace dual of the operator form of a CP map is `B' ↦ (Vᴴ (B ⊗ 1) V)'`
  for some `V` with environment `Fin (rank J(φ))`.
* `CompletelyPositiveMap.exists_coe_eq_iff_exists_stinespringMatrix`: **Stinespring's
  theorem**: a linear map is completely positive iff it is `A ↦ tr₂(V A Vᴴ)` for some `V`.

## References

* W. F. Stinespring, *Positive functions on C*-algebras*, Proc. Amer. Math. Soc. 6 (1955),
  211–216.
* Watrous, *The Theory of Quantum Information*, §2.2
-/

@[expose] public section

namespace Matrix

variable {n m : Type*} [Fintype n] [Fintype m]

open scoped ComplexOrder Kronecker Matrix

/-! ### Kraus blocks -/

section KrausBlock

variable {ι R : Type*}

omit [Fintype n] [Fintype m] in
/-- The Kraus blocks `Kᵢ a b = V (a, i) b` of `V : Matrix (m × ι) n R`, so that `V = Σᵢ Kᵢ ⊗ eᵢ`.
They are the Kraus operators
of `A ↦ tr₂(V A Vᴴ)` (`traceRight_mul_mul_conjTranspose`), and every family of matrices arises this
way (`exists_krausBlock_eq`). -/
def krausBlock (V : Matrix (m × ι) n R) (i : ι) : Matrix m n R :=
  Matrix.of fun a b => V (a, i) b

omit [Fintype n] [Fintype m] in
/-- `Kᵢ a b = V (a, i) b`. -/
@[simp] lemma krausBlock_apply (V : Matrix (m × ι) n R) (i : ι) (a : m) (b : n) :
    krausBlock V i a b = V (a, i) b :=
  rfl

omit [Fintype n] [Fintype m] in
/-- Every family `Kᵢ : Matrix m n R` is the family of Kraus blocks of the matrix
`V (a, i) b = Kᵢ a b`, that is, of `V = Σᵢ Kᵢ ⊗ eᵢ`. -/
lemma exists_krausBlock_eq (K : ι → Matrix m n R) :
    ∃ V : Matrix (m × ι) n R, ∀ i, krausBlock V i = K i :=
  ⟨Matrix.of fun p b => K p.2 p.1 b, fun _ => rfl⟩

omit [Fintype n] in
/-- `Vᴴ V = Σᵢ Kᵢᴴ Kᵢ` for the Kraus blocks `Kᵢ` of `V`. In particular `V` is an isometry,
`Vᴴ V = I`, iff its Kraus blocks satisfy the Kraus completeness relation `Σᵢ Kᵢᴴ Kᵢ = I`. -/
lemma conjTranspose_mul_self_eq_sum_krausBlock [Fintype ι] [NonUnitalSemiring R] [StarRing R]
    (V : Matrix (m × ι) n R) : Vᴴ * V = ∑ i, (krausBlock V i)ᴴ * krausBlock V i := by
  ext a b
  simp [Matrix.mul_apply, Matrix.sum_apply, Fintype.sum_prod_type_right]

omit [Fintype m] in
/-- Conjugation by `V` followed by the partial trace over `ι` is the Kraus map of the Kraus blocks
`Kᵢ` of `V`: `tr₂(V A Vᴴ) = Σᵢ Kᵢ A Kᵢᴴ`, the sum over `i` of the `((·, i), (·, i))` blocks of
`V A Vᴴ`. -/
lemma traceRight_mul_mul_conjTranspose [Fintype ι] [NonUnitalSemiring R] [StarRing R]
    (V : Matrix (m × ι) n R) (A : Matrix n n R) :
    traceRight (V * A * Vᴴ) = ∑ i, krausBlock V i * A * (krausBlock V i)ᴴ := by
  ext a b
  simp [traceRight_apply, Matrix.sum_apply, Matrix.mul_apply]

end KrausBlock

/-! ### Heisenberg picture -/

section Heisenberg

variable [DecidableEq n] [DecidableEq m] {F : Type*} [FunLike F (Matrix n n ℂ) (Matrix m m ℂ)]
  {G : Type*} [FunLike G (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (EuclideanSpace ℂ m →L[ℂ] EuclideanSpace ℂ m)]
  [LinearMapClass G ℂ (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (EuclideanSpace ℂ m →L[ℂ] EuclideanSpace ℂ m)]

omit [DecidableEq n] [DecidableEq m] in
/-- The Stinespring pairing: `Tr (tr₂(V A Vᴴ) B) = Tr (A Vᴴ (B ⊗ 1) V)`. -/
lemma trace_traceRight_mul_mul_conjTranspose_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : Matrix (m × ι) n ℂ) (A : Matrix n n ℂ) (B : Matrix m m ℂ) :
    Tr (traceRight (V * A * Vᴴ) * B) = Tr (A * (Vᴴ * (B ⊗ₖ (1 : Matrix ι ι ℂ)) * V)) := by
  rw [← trace_mul_kronecker_one_right]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm V]
  simp only [Matrix.mul_assoc]

/-- Heisenberg and Schrödinger pictures of conjugation by a matrix `V`: if `Ψ : B(ℂⁿ) → B(ℂᵐ)` is
the operator form of `Φ : M_n(ℂ) → M_m(ℂ)`, `Ψ(A') = Φ(A)'` for the operator
`A' = Matrix.toEuclideanCLM A` of each matrix `A`, then the trace dual of `Ψ` is
`Ψ*(B') = (Vᴴ (B ⊗ 1) V)'` for all `B` iff `Φ(A) = tr₂(V A Vᴴ)` for all `A`. Both sides pair
`A` against `B` in the trace: `tr(Ψ(A') ∘ B') = Tr (Φ(A) B)` and
`tr(A' ∘ Ψ*(B')) = Tr (A Vᴴ (B ⊗ 1) V)`. -/
theorem traceDual_eq_iff_stinespring {ι : Type*} [Fintype ι] [DecidableEq ι] {Φ : F} {Ψ : G}
    (h : ∀ A, Ψ (toEuclideanCLM (𝕜 := ℂ) A) = toEuclideanCLM (𝕜 := ℂ) (Φ A))
    (V : Matrix (m × ι) n ℂ) :
    (∀ B, ContinuousLinearMap.traceDual Ψ (toEuclideanCLM (𝕜 := ℂ) B) =
        toEuclideanCLM (𝕜 := ℂ) (Vᴴ * (B ⊗ₖ (1 : Matrix ι ι ℂ)) * V)) ↔
      ∀ A, Φ A = traceRight (V * A * Vᴴ) := by
  constructor
  · intro hΨ A
    refine Matrix.ext_iff_trace_mul_right.mpr fun B => ?_
    rw [← trace_toEuclideanCLM_comp_toEuclideanCLM, ← h,
      ContinuousLinearMap.trace_comp_traceDual, hΨ, trace_toEuclideanCLM_comp_toEuclideanCLM,
      trace_traceRight_mul_mul_conjTranspose_mul]
  · intro hV B
    rw [eq_comm, ContinuousLinearMap.eq_traceDual_iff]
    intro X
    obtain ⟨A, rfl⟩ := EquivLike.surjective (toEuclideanCLM (𝕜 := ℂ)) X
    rw [h, trace_toEuclideanCLM_comp_toEuclideanCLM, trace_toEuclideanCLM_comp_toEuclideanCLM, hV,
      trace_traceRight_mul_mul_conjTranspose_mul]

/-- If `Φ(A) = tr₂(V A Vᴴ)` for all `A`, then the trace dual of the operator form `Ψ` of `Φ` is
`Ψ*(B') = (Vᴴ (B ⊗ 1) V)'`. -/
theorem traceDual_eq_of_stinespring {ι : Type*} [Fintype ι] [DecidableEq ι] {Φ : F} {Ψ : G}
    (h : ∀ A, Ψ (toEuclideanCLM (𝕜 := ℂ) A) = toEuclideanCLM (𝕜 := ℂ) (Φ A))
    (V : Matrix (m × ι) n ℂ) (hV : ∀ A, Φ A = traceRight (V * A * Vᴴ)) (B : Matrix m m ℂ) :
    ContinuousLinearMap.traceDual Ψ (toEuclideanCLM (𝕜 := ℂ) B) =
      toEuclideanCLM (𝕜 := ℂ) (Vᴴ * (B ⊗ₖ (1 : Matrix ι ι ℂ)) * V) :=
  (traceDual_eq_iff_stinespring h V).2 hV B

end Heisenberg

end Matrix

/-! ### Stinespring's theorem for completely positive maps -/

namespace CompletelyPositiveMap

open Matrix
open scoped ComplexOrder CStarAlgebra

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- **Stinespring's theorem** for matrix algebras: a completely positive map
`φ : M_n(ℂ) → M_m(ℂ)` is `φ(A) = tr₂(V A Vᴴ)` for some `V : ℂⁿ → ℂᵐ ⊗ ℂ^E` with environment
`E = Fin r` of the minimal dimension `r = rank J(φ)` (`Matrix.rank_choiMatrix_le_card_of_stinespring`),
at most `nm` (`Matrix.rank_le_card_width`): the matrix `V = Σₐ Kₐ ⊗ eₐ` stacking a Kraus
representation `φ(A) = Σₐ Kₐ A Kₐᴴ` with `rank J(φ)` operators
(`CompletelyPositiveMap.exists_kraus_rank`, `Matrix.exists_krausBlock_eq`). Conversely every such
map is completely positive: its Kraus blocks are Kraus operators (the `←` direction of
`CompletelyPositiveMap.exists_coe_eq_iff_exists_stinespringMatrix`, via
`CompletelyPositiveMap.exists_coe_eq_iff_exists_kraus`). -/
theorem exists_stinespringMatrix (φ : Matrix n n ℂ →CP Matrix m m ℂ) :
    ∃ V : Matrix (m × Fin (choiMatrix φ).rank) n ℂ, ∀ A, φ A = traceRight (V * A * Vᴴ) := by
  obtain ⟨K, hK⟩ := φ.exists_kraus_rank
  obtain ⟨V, hV⟩ := exists_krausBlock_eq K
  exact ⟨V, fun A => by rw [traceRight_mul_mul_conjTranspose, hK]; simp only [hV]⟩

open scoped Matrix.Norms.L2Operator MatrixOrder Kronecker in
/-- **Stinespring's theorem, Heisenberg picture**, for matrix algebras: if `ψ : B(ℂⁿ) → B(ℂᵐ)` is
the operator form of a completely positive map `φ : M_n(ℂ) → M_m(ℂ)`, `ψ(A') = φ(A)'` with
`A' = Matrix.toEuclideanCLM A`, then its trace dual is `ψ*(B') = (Vᴴ (B ⊗ 1) V)'` for some
`V : ℂⁿ → ℂᵐ ⊗ ℂ^E` with environment `E = Fin r` of the minimal dimension `r = rank J(φ)`
(`Matrix.rank_choiMatrix_le_card_of_stinespring`), at most `nm`: the Schrödinger form
`CompletelyPositiveMap.exists_stinespringMatrix` read through `Matrix.traceDual_eq_iff_stinespring`.
The operator form of `φ` is `CompletelyPositiveMap.arrowCongr toEuclideanCLM toEuclideanCLM φ`. -/
theorem exists_traceDual_eq_stinespringMatrix (φ : Matrix n n ℂ →CP Matrix m m ℂ)
    {G : Type*} [FunLike G (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
      (EuclideanSpace ℂ m →L[ℂ] EuclideanSpace ℂ m)]
    [LinearMapClass G ℂ (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
      (EuclideanSpace ℂ m →L[ℂ] EuclideanSpace ℂ m)] {ψ : G}
    (h : ∀ A, ψ (toEuclideanCLM (𝕜 := ℂ) A) = toEuclideanCLM (𝕜 := ℂ) (φ A)) :
    ∃ V : Matrix (m × Fin (choiMatrix φ).rank) n ℂ, ∀ B,
      ContinuousLinearMap.traceDual ψ (toEuclideanCLM (𝕜 := ℂ) B) =
        toEuclideanCLM (𝕜 := ℂ) (Vᴴ *
          (B ⊗ₖ (1 : Matrix (Fin (choiMatrix φ).rank) (Fin (choiMatrix φ).rank) ℂ)) * V) := by
  obtain ⟨V, hV⟩ := φ.exists_stinespringMatrix
  exact ⟨V, (traceDual_eq_iff_stinespring h V).2 hV⟩

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- **Stinespring's theorem** for matrix algebras: a linear map `Φ : M_n(ℂ) → M_m(ℂ)` is
completely positive, i.e. it is the linear map of some `φ : M_n(ℂ) →CP M_m(ℂ)`, iff
`Φ(A) = tr₂(V A Vᴴ)` for some `V : ℂⁿ → ℂᵐ ⊗ ℂ^E` with environment `E = Fin r` of the minimal
dimension `r = rank J(Φ) ≤ nm`. The converse holds since the Kraus blocks of `V` are a Kraus
representation (`CompletelyPositiveMap.exists_coe_eq_iff_exists_kraus`). -/
theorem exists_coe_eq_iff_exists_stinespringMatrix
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    (∃ φ : Matrix n n ℂ →CP Matrix m m ℂ, (φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) = Φ) ↔
      ∃ V : Matrix (m × Fin (choiMatrix Φ).rank) n ℂ, ∀ A, Φ A = traceRight (V * A * Vᴴ) :=
  ⟨fun ⟨φ, hφ⟩ => hφ ▸ φ.exists_stinespringMatrix,
    fun ⟨V, hV⟩ => (exists_coe_eq_iff_exists_kraus Φ).2
      ⟨_, (rank_le_card_width (choiMatrix Φ)).trans_eq (Fintype.card_prod n m), krausBlock V,
        fun A => by rw [hV, traceRight_mul_mul_conjTranspose]⟩⟩

end CompletelyPositiveMap

namespace Matrix

variable {n m : Type*} [Fintype n] [Fintype m]

open scoped ComplexOrder Kronecker Matrix

/-! ### Minimality -/

section Minimality

variable [DecidableEq n] {F : Type*} [FunLike F (Matrix n n ℂ) (Matrix m m ℂ)]

/-- **Minimality of the environment**: if `Φ(A) = tr₂(V A Vᴴ)` for `V : Matrix (m × ι) n ℂ`, the
environment `ι` has at least `rank J(Φ)` elements, the dimension attained for completely positive
maps (`CompletelyPositiveMap.exists_stinespringMatrix`): the Kraus blocks of `V` are Kraus operators
of `Φ` (`Matrix.rank_choiMatrix_le_card_of_kraus`). -/
theorem rank_choiMatrix_le_card_of_stinespring {Φ : F} {ι : Type*} [Fintype ι]
    (V : Matrix (m × ι) n ℂ) (hV : ∀ A, Φ A = traceRight (V * A * Vᴴ)) :
    (choiMatrix Φ).rank ≤ Fintype.card ι :=
  rank_choiMatrix_le_card_of_kraus (krausBlock V) fun A => by
    rw [hV, traceRight_mul_mul_conjTranspose]

/-- The environment of `Φ(A) = tr₂(V A Vᴴ)` has the minimal dimension `rank J(Φ)` iff the Kraus
blocks `Kᵢ = Matrix.krausBlock V i` of `V` are linearly independent. -/
theorem rank_choiMatrix_eq_card_iff_linearIndependent_krausBlock {Φ : F} {ι : Type*} [Fintype ι]
    (V : Matrix (m × ι) n ℂ) (hV : ∀ A, Φ A = traceRight (V * A * Vᴴ)) :
    (choiMatrix Φ).rank = Fintype.card ι ↔ LinearIndependent ℂ (krausBlock V) :=
  rank_choiMatrix_eq_card_iff_linearIndependent (krausBlock V) fun A => by
    rw [hV, traceRight_mul_mul_conjTranspose]

end Minimality

end Matrix
