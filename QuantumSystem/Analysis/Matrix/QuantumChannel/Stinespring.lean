/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.Matrix.DensityMatrix.Kronecker
public import QuantumSystem.Analysis.Matrix.QuantumChannel.Choi
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.Stinespring
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.MatrixRepresentation
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.TensorProductCompletion
public import QuantumSystem.ForMathlib.LinearAlgebra.Matrix.PartialTrace
public import QuantumSystem.ForMathlib.LinearAlgebra.Matrix.Trace

/-!
# Stinespring's theorem for matrix channels

A linear map `Φ : M_n(ℂ) → M_m(ℂ)` is completely positive iff it is `A ↦ tr₂(V A Vᴴ)` for some
`V : Matrix (m × Fin r) n ℂ`, and a quantum channel iff moreover `V` is an isometry, `Vᴴ V = I`
(`CompletelyPositiveMap.exists_coe_eq_iff_exists_stinespringMatrix`,
`Matrix.QuantumChannel.exists_coe_eq_iff_exists_stinespringMatrix`). The environment
`E = Fin r` has the dimension `r = rank J(Φ) ≤ nm` of the Choi matrix `J(Φ)`, and this is minimal:
every such `V` has an environment with at least `rank J(Φ)` elements
(`Matrix.rank_choiMatrix_le_card_of_stinespring`), with equality iff its Kraus blocks are linearly
independent (`Matrix.rank_choiMatrix_eq_card_iff_linearIndependent_krausBlock`).

This is the Schrödinger-picture form of Stinespring's dilation (Watrous, Theorem 2.22 and
Corollary 2.27). Stinespring's original Heisenberg-picture statement, that the trace dual is
`Φ*(B) = Vᴴ (B ⊗ 1) V`, is `CompletelyPositiveMap.exists_traceDual_eq_stinespringMatrix`, and
`Matrix.QuantumChannel.exists_traceDual_eq_stinespringMatrix` with `V` an isometry. For a fixed `V`
the two pictures are equivalent (`Matrix.traceDual_eq_iff_stinespring`).

## Derivation from the general theorem

The existence of `V` is derived from Stinespring's theorem for completely positive maps into
`B(H)` (`QuantumSystem/ForMathlib/Analysis/CStarAlgebra/Stinespring.lean`) rather than by stacking
Kraus operators; no Kraus representation of `φ` is used. The trace dual `φ* : M_m(ℂ) → M_n(ℂ)` is
completely positive by self-duality of the positive semidefinite cone for the trace pairing
(`CompletelyPositiveMap.matrixTraceDual`). Hence so is `ψ = φ* : M_m(ℂ) →CP B(ℂⁿ)`, and the general
theorem gives `ψ(B) = W† π(B) W` for a unital ⋆-representation `π` of `M_m(ℂ)` on the Stinespring
space `K` and the Stinespring operator `W : ℂⁿ → K`. The space `K` is the completion of
`M_m(ℂ) ⊗ ℂⁿ`, so `dim K ≤ m² n`. A unital ⋆-representation of `M_m(ℂ)` is a multiple of the
identity representation (`QuantumSystem/ForMathlib/Analysis/InnerProductSpace/MatrixRepresentation.lean`):
`K ≅ ℂᵐ ⊗ ℂʳ` with `π(B) = B ⊗ 1`, where `m · r = dim K`, hence `r ≤ nm`. For an orthonormal basis
`e` of the multiplicity space `ℂʳ`, `W` is in the adapted basis `Matrix.multiplicityBasis π e` of
`K` the matrix `V = CompletelyPositiveMap.stinespringMatrix φ e`
(`CompletelyPositiveMap.toLin_stinespringMatrix`), and `ψ(B) = W† π(B) W` reads
`φ*(B) = Vᴴ (B ⊗ 1) V`. The name "Stinespring operator" is reserved for the operator `W` of the
general theorem; `V` is its matrix.

The minimality of the Stinespring representation, that the vectors `π(B) W ξ` span `K`, makes the
Kraus blocks of `V` linearly independent
(`CompletelyPositiveMap.linearIndependent_krausBlock_stinespringMatrix`). They are Kraus operators
of `φ`, so `r = rank J(φ)` (`CompletelyPositiveMap.card_eq_rank_choiMatrix`): the general theorem
produces an environment of the minimal dimension without any choice of Kraus operators.

## Kraus blocks

Conversely, write `V : Matrix (m × ι) n ℂ` as `V = Σᵢ Kᵢ ⊗ eᵢ` with the Kraus blocks
`Kᵢ a b = V (a, i) b` (`Matrix.krausBlock V i`). They are Kraus operators for
`A ↦ tr₂(V A Vᴴ) = Σᵢ Kᵢ A Kᵢᴴ`, so that map is completely positive
(`CompletelyPositiveMap.ofMatrixStinespring`). Since `Vᴴ V = Σᵢ Kᵢᴴ Kᵢ`, the matrix `V` is an
isometry iff
its Kraus blocks satisfy the completeness relation `Σᵢ Kᵢᴴ Kᵢ = I`, and every family of Kraus
operators is the family of Kraus blocks of `Σᵢ Kᵢ ⊗ eᵢ` (`Matrix.exists_krausBlock_eq`).

## Conventions

The environment is the **right** factor of `ℂᵐ ⊗ ℂ^E`, indexed by `m × E`, and is removed by the
partial trace `tr₂ = Matrix.traceRight` (the notation of
`QuantumSystem/Analysis/Matrix/DensityMatrix/Kronecker.lean`). This is Watrous's convention,
`Φ(X) = Tr_Z (A X A*)` with `A : X → Y ⊗ Z`, and Stinespring's `π(B) = B ⊗ 1` on `ℂᵐ ⊗ ℂʳ`, the
order of the multiplicity decomposition
(`QuantumSystem/ForMathlib/Analysis/InnerProductSpace/MatrixRepresentation.lean`). The Choi matrix
keeps Choi's ordering, input first (`QuantumSystem/Analysis/Matrix/QuantumChannel/Choi.lean`).

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
(`QuantumSystem/ForMathlib/Analysis/CStarAlgebra/SchwarzMap.lean`). A matrix channel enters that
setting through its trace dual, a Schwarz map on `B(ℂᵐ)` (`Matrix.QuantumChannel.dualSchwarzMap` in
`QuantumSystem/Analysis/Matrix/QuantumChannel/Dual.lean`).

## Main definitions

* `Matrix.krausBlock V i`: the Kraus block `Kᵢ a b = V (a, i) b` of `V : Matrix (m × ι) n ℂ`,
  so that `V = Σᵢ Kᵢ ⊗ eᵢ`.
* `CompletelyPositiveMap.stinespringEnvDim φ i₀`: the environment dimension `r`, the dimension of
  the multiplicity space at `i₀` of the Stinespring representation.
* `CompletelyPositiveMap.stinespringMatrix φ e`: the matrix of the Stinespring operator of
  `φ.matrixTraceDual.toEuclidean` in the basis of the Stinespring space adapted to `K ≅ ℂᵐ ⊗ ℂ^ι` by an
  orthonormal basis `e` of the multiplicity space indexed by `ι`, with environment `ι`.
* `CompletelyPositiveMap.ofMatrixStinespring`: `A ↦ tr₂(V A Vᴴ)` as a completely positive map.
* `Matrix.QuantumChannel.ofStinespring`: `A ↦ tr₂(V A Vᴴ)` for an isometry `V` as a quantum
  channel.

## Main statements

* `Matrix.conjTranspose_mul_self_eq_sum_krausBlock`: `Vᴴ V = Σᵢ Kᵢᴴ Kᵢ`.
* `Matrix.traceRight_mul_mul_conjTranspose`: `tr₂(V A Vᴴ) = Σᵢ Kᵢ A Kᵢᴴ`, the sum of the diagonal
  blocks of `V A Vᴴ`.
* `Matrix.traceDual_eq_iff_stinespring`: for a fixed `V`, the trace dual is
  `Φ*(B) = Vᴴ (B ⊗ 1) V` for all `B` iff `Φ(A) = tr₂(V A Vᴴ)` for all `A`.
* `CompletelyPositiveMap.traceDual_eq_stinespringMatrix`,
  `CompletelyPositiveMap.apply_eq_traceRight_stinespringMatrix`: `φ*(B) = Vᴴ (B ⊗ 1) V` and
  `φ(A) = tr₂(V A Vᴴ)` for the Stinespring matrix `V`.
* `CompletelyPositiveMap.linearIndependent_krausBlock_stinespringMatrix`,
  `CompletelyPositiveMap.card_eq_rank_choiMatrix`,
  `CompletelyPositiveMap.stinespringEnvDim_eq_rank_choiMatrix`: the Kraus blocks of the Stinespring
  matrix are linearly independent, and its environment has dimension `r = rank J(φ)`; in
  particular `r ≤ nm` (`CompletelyPositiveMap.stinespringEnvDim_le`).
* `Matrix.rank_choiMatrix_le_card_of_stinespring`: **minimality**: every `V` with
  `Φ(A) = tr₂(V A Vᴴ)` has an environment with at least `rank J(Φ)` elements;
  `Matrix.rank_choiMatrix_eq_card_iff_linearIndependent_krausBlock`: with equality iff its Kraus
  blocks are linearly independent.
* `CompletelyPositiveMap.exists_traceDual_eq_stinespringMatrix`: **Stinespring's theorem,
  Heisenberg picture**: the trace dual of a CP map is `B ↦ Vᴴ (B ⊗ 1) V` for some `V` with
  environment `Fin (rank J(φ))`.
* `CompletelyPositiveMap.exists_stinespringMatrix`: a CP map is `A ↦ tr₂(V A Vᴴ)` for some `V`
  with environment `Fin (rank J(φ))`; the converse is `CompletelyPositiveMap.ofMatrixStinespring`.
* `CompletelyPositiveMap.exists_coe_eq_iff_exists_stinespringMatrix`: **Stinespring's
  theorem**: a linear map is completely positive iff it is `A ↦ tr₂(V A Vᴴ)` for some `V`.
* `Matrix.QuantumChannel.exists_traceDual_eq_stinespringMatrix`: the trace dual of a quantum channel is
  `B ↦ Vᴴ (B ⊗ 1) V` for an isometry `V`.
* `Matrix.QuantumChannel.exists_stinespringMatrix`: a quantum channel is `A ↦ tr₂(V A Vᴴ)` for an
  isometry `V`; the converse is `Matrix.QuantumChannel.ofStinespring`.
* `Matrix.QuantumChannel.exists_coe_eq_iff_exists_stinespringMatrix`: a linear map is a
  quantum channel iff it is `A ↦ tr₂(V A Vᴴ)` for an isometry `V`.

## References

* W. F. Stinespring, *Positive functions on C*-algebras*, Proc. Amer. Math. Soc. 6 (1955),
  211–216.
* Watrous, *The Theory of Quantum Information*, §2.2
-/

@[expose] public section

open scoped Matrix.QuantumInfo

namespace Matrix

variable {n m : Type*} [Fintype n] [Fintype m]

open scoped ComplexOrder Kronecker

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
    tr₂(V * A * Vᴴ) = ∑ i, krausBlock V i * A * (krausBlock V i)ᴴ := by
  ext a b
  simp [traceRight_apply, Matrix.sum_apply, Matrix.mul_apply]

end KrausBlock

/-! ### Heisenberg picture -/

section Heisenberg

variable [DecidableEq n] {F : Type*} [FunLike F (Matrix n n ℂ) (Matrix m m ℂ)]
  [LinearMapClass F ℂ (Matrix n n ℂ) (Matrix m m ℂ)]

omit [DecidableEq n] in
/-- The Stinespring pairing: `Tr (tr₂(V A Vᴴ) B) = Tr (A Vᴴ (B ⊗ 1) V)`. -/
lemma trace_traceRight_mul_mul_conjTranspose_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : Matrix (m × ι) n ℂ) (A : Matrix n n ℂ) (B : Matrix m m ℂ) :
    Tr (tr₂(V * A * Vᴴ) * B) = Tr (A * (Vᴴ * (B ⊗ₖ (1 : Matrix ι ι ℂ)) * V)) := by
  rw [← trace_mul_kronecker_one_right]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm V]
  simp only [Matrix.mul_assoc]

/-- Heisenberg and Schrödinger pictures of conjugation by a matrix `V`: the trace dual of `Φ` is
`Φ*(B) = Vᴴ (B ⊗ 1) V` for all `B` iff `Φ(A) = tr₂(V A Vᴴ)` for all `A`. -/
theorem traceDual_eq_iff_stinespring {ι : Type*} [Fintype ι] [DecidableEq ι] {Φ : F}
    (V : Matrix (m × ι) n ℂ) :
    (∀ B, traceDual Φ B = Vᴴ * (B ⊗ₖ (1 : Matrix ι ι ℂ)) * V) ↔
      ∀ A, Φ A = tr₂(V * A * Vᴴ) := by
  constructor
  · intro h A
    refine Matrix.ext_iff_trace_mul_right.mpr fun B => ?_
    rw [trace_mul_traceDual, h, trace_traceRight_mul_mul_conjTranspose_mul]
  · intro hV B
    refine Matrix.ext_iff_trace_mul_left.mpr fun A => ?_
    rw [← trace_mul_traceDual, hV, trace_traceRight_mul_mul_conjTranspose_mul]

/-- If `Φ(A) = tr₂(V A Vᴴ)` for all `A`, then the trace dual of `Φ` is `Φ*(B) = Vᴴ (B ⊗ 1) V`. -/
theorem traceDual_eq_of_stinespring {ι : Type*} [Fintype ι] [DecidableEq ι] {Φ : F}
    (V : Matrix (m × ι) n ℂ) (hV : ∀ A, Φ A = tr₂(V * A * Vᴴ)) (B : Matrix m m ℂ) :
    traceDual Φ B = Vᴴ * (B ⊗ₖ (1 : Matrix ι ι ℂ)) * V :=
  (traceDual_eq_iff_stinespring V).2 hV B

end Heisenberg

end Matrix

/-! ### Stinespring's theorem for completely positive maps -/

namespace CompletelyPositiveMap

open Matrix
open scoped ComplexOrder CStarAlgebra

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- **Stinespring's theorem**, converse: conjugation by `V : Matrix (m × ι) n ℂ` followed by
tracing out the environment `ι` is completely positive; its Kraus operators are the Kraus
blocks `Matrix.krausBlock V i` of `V`. -/
def ofMatrixStinespring (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) {ι : Type*} [Fintype ι]
    (V : Matrix (m × ι) n ℂ) (hV : ∀ A, Φ A = tr₂(V * A * Vᴴ)) :
    Matrix n n ℂ →CP Matrix m m ℂ :=
  ofMatrixKraus Φ (krausBlock V) fun A => by rw [hV, traceRight_mul_mul_conjTranspose]

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- The completely positive map `CompletelyPositiveMap.ofMatrixStinespring Φ V hV` is `Φ` as a
function. -/
@[simp] lemma coe_ofMatrixStinespring (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) {ι : Type*} [Fintype ι]
    (V : Matrix (m × ι) n ℂ) (hV : ∀ A, Φ A = tr₂(V * A * Vᴴ)) :
    ⇑(ofMatrixStinespring Φ V hV) = Φ :=
  rfl

/-! ### The Stinespring matrix -/

section StinespringMatrix

open scoped Matrix.Norms.L2Operator MatrixOrder InnerProductSpace

/-- The Stinespring space of `φ.matrixTraceDual.toEuclidean` is finite-dimensional: it is the completion of the
finite-dimensional space `M_m(ℂ) ⊗ ℂⁿ`. -/
instance (φ : Matrix n n ℂ →CP Matrix m m ℂ) : FiniteDimensional ℂ φ.matrixTraceDual.toEuclidean.Stinespring :=
  FiniteDimensional.completion

/-- The dimension `r` of the environment of the Stinespring matrix: the dimension of the multiplicity
space at `i₀` of the Stinespring representation of `φ.matrixTraceDual.toEuclidean`. It does not depend on `i₀`
(`CompletelyPositiveMap.stinespringEnvDim_eq`), and it is the rank of the Choi matrix
(`CompletelyPositiveMap.stinespringEnvDim_eq_rank_choiMatrix`). -/
noncomputable def stinespringEnvDim (φ : Matrix n n ℂ →CP Matrix m m ℂ) (i₀ : m) : ℕ :=
  Module.finrank ℂ (multiplicitySpace φ.matrixTraceDual.toEuclidean.stinespringStarAlgHom i₀)

variable {ι : Type*} [Fintype ι]

/-- The **Stinespring matrix** `V : Matrix (m × ι) n ℂ` of a completely positive map
`φ : M_n(ℂ) → M_m(ℂ)`, for an orthonormal basis `e` indexed by `ι` of the multiplicity space at
`i₀` of the Stinespring representation `π` of `φ.matrixTraceDual.toEuclidean`: the matrix of the
Stinespring operator `φ.matrixTraceDual.toEuclidean.stinespringOperator : ℂⁿ → K`
(`CompletelyPositiveMap.toLin_stinespringMatrix`) in the standard basis of `ℂⁿ` and the basis
`b (i, k) = multiplicityIsometry π i₀ i (e k)` of `K` adapted to `K ≅ ℂᵐ ⊗ ℂ^ι`
(`Matrix.multiplicityBasis π e`). It satisfies `φ*(B) = Vᴴ (B ⊗ 1) V`
(`CompletelyPositiveMap.traceDual_eq_stinespringMatrix`) and `φ(A) = tr₂(V A Vᴴ)`
(`CompletelyPositiveMap.apply_eq_traceRight_stinespringMatrix`). It depends on the choices of `i₀`
and of `e`; its environment dimension `card ι = rank J(φ)` does not
(`CompletelyPositiveMap.card_eq_rank_choiMatrix`). -/
noncomputable def stinespringMatrix (φ : Matrix n n ℂ →CP Matrix m m ℂ) {i₀ : m}
    (e : OrthonormalBasis ι ℂ (multiplicitySpace φ.matrixTraceDual.toEuclidean.stinespringStarAlgHom i₀)) :
    Matrix (m × ι) n ℂ :=
  LinearMap.toMatrix (EuclideanSpace.basisFun n ℂ).toBasis
    (multiplicityBasis φ.matrixTraceDual.toEuclidean.stinespringStarAlgHom e).toBasis
    (φ.matrixTraceDual.toEuclidean.stinespringOperator :
      EuclideanSpace ℂ n →ₗ[ℂ] φ.matrixTraceDual.toEuclidean.Stinespring)

/-- The Stinespring matrix is the matrix of the Stinespring operator of `φ.matrixTraceDual.toEuclidean`: read back
in the same bases, it is that operator. -/
lemma toLin_stinespringMatrix (φ : Matrix n n ℂ →CP Matrix m m ℂ) {i₀ : m}
    (e : OrthonormalBasis ι ℂ (multiplicitySpace φ.matrixTraceDual.toEuclidean.stinespringStarAlgHom i₀)) :
    Matrix.toLin (EuclideanSpace.basisFun n ℂ).toBasis
      (multiplicityBasis φ.matrixTraceDual.toEuclidean.stinespringStarAlgHom e).toBasis
      (φ.stinespringMatrix e) = φ.matrixTraceDual.toEuclidean.stinespringOperator :=
  Matrix.toLin_toMatrix _ _ _

/-- The entries of the Stinespring matrix are `V ((a, k), j) = ⟪V_a (e k), W eⱼ⟫`, with `W` the
Stinespring operator and `V_a = multiplicityIsometry π i₀ a`. -/
lemma stinespringMatrix_apply (φ : Matrix n n ℂ →CP Matrix m m ℂ) {i₀ : m}
    (e : OrthonormalBasis ι ℂ (multiplicitySpace φ.matrixTraceDual.toEuclidean.stinespringStarAlgHom i₀))
    (a : m) (k : ι) (j : n) :
    φ.stinespringMatrix e (a, k) j =
      ⟪multiplicityIsometry φ.matrixTraceDual.toEuclidean.stinespringStarAlgHom i₀ a (e k),
        φ.matrixTraceDual.toEuclidean.stinespringOperator (EuclideanSpace.basisFun n ℂ j)⟫_ℂ := by
  simp only [stinespringMatrix, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis, ContinuousLinearMap.coe_coe]
  exact congrArg (fun x => ⟪x, _⟫_ℂ) (multiplicityBasis_apply _ e (a, k))

/-- The environment dimension is `r = dim K / m`, independently of `i₀`. -/
lemma stinespringEnvDim_eq (φ : Matrix n n ℂ →CP Matrix m m ℂ) (i₀ : m) :
    φ.stinespringEnvDim i₀ = Module.finrank ℂ φ.matrixTraceDual.toEuclidean.Stinespring / Fintype.card m := by
  rw [stinespringEnvDim,
    finrank_eq_card_mul_finrank_multiplicitySpace φ.matrixTraceDual.toEuclidean.stinespringStarAlgHom i₀,
    Nat.mul_div_cancel_left _ (Fintype.card_pos_iff.mpr ⟨i₀⟩)]

/-- The environment has dimension `r ≤ nm`: `m · r = dim K ≤ dim (M_m(ℂ) ⊗ ℂⁿ) = m² n`. -/
lemma stinespringEnvDim_le (φ : Matrix n n ℂ →CP Matrix m m ℂ) (i₀ : m) :
    φ.stinespringEnvDim i₀ ≤ Fintype.card n * Fintype.card m := by
  have hK : Module.finrank ℂ φ.matrixTraceDual.toEuclidean.Stinespring ≤
      Fintype.card m * Fintype.card m * Fintype.card n := by
    refine Module.finrank_completion_le.trans_eq ?_
    rw [finrank_preStinespring, Module.finrank_matrix, Module.finrank_self, mul_one,
      finrank_euclideanSpace]
  rw [finrank_eq_card_mul_finrank_multiplicitySpace φ.matrixTraceDual.toEuclidean.stinespringStarAlgHom i₀] at hK
  refine Nat.le_of_mul_le_mul_left ?_ (Fintype.card_pos_iff.mpr ⟨i₀⟩)
  rw [stinespringEnvDim]
  linarith [hK]

open scoped Kronecker in
/-- **Stinespring's theorem, Heisenberg picture**, for the Stinespring matrix `V`:
`φ*(B) = Vᴴ (B ⊗ 1) V`. This is the general theorem
(`CompletelyPositiveMap.apply_eq_adjoint_comp_stinespringStarAlgHom_comp`) for `φ.matrixTraceDual.toEuclidean`,
read in the basis `Matrix.multiplicityBasis π e`, in which the unital ⋆-representation `π` of `M_m(ℂ)`
is `B ⊗ 1` (`Matrix.toMatrix_multiplicityBasis`). -/
theorem traceDual_eq_stinespringMatrix [DecidableEq ι] (φ : Matrix n n ℂ →CP Matrix m m ℂ) {i₀ : m}
    (e : OrthonormalBasis ι ℂ (multiplicitySpace φ.matrixTraceDual.toEuclidean.stinespringStarAlgHom i₀))
    (B : Matrix m m ℂ) :
    Matrix.traceDual φ B = (φ.stinespringMatrix e)ᴴ * (B ⊗ₖ (1 : Matrix ι ι ℂ)) *
      φ.stinespringMatrix e := by
  set f := (EuclideanSpace.basisFun n ℂ).toBasis
  have hmat : ∀ X : Matrix n n ℂ,
      LinearMap.toMatrix f f (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) X :
        EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n) = X := fun X => by
    rw [coe_toEuclideanCLM_eq_toEuclideanLin, toEuclideanLin_eq_toLin_orthonormal,
      LinearMap.toMatrix_toLin]
  have hψ : Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (Matrix.traceDual φ B) =
      ContinuousLinearMap.adjoint φ.matrixTraceDual.toEuclidean.stinespringOperator ∘L
        φ.matrixTraceDual.toEuclidean.stinespringStarAlgHom B ∘L
          φ.matrixTraceDual.toEuclidean.stinespringOperator :=
    φ.matrixTraceDual.toEuclidean.apply_eq_adjoint_comp_stinespringStarAlgHom_comp B
  rw [← hmat (Matrix.traceDual φ B), hψ,
    ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.toMatrix_comp f (multiplicityBasis _ e).toBasis f,
    LinearMap.toMatrix_comp f (multiplicityBasis _ e).toBasis (multiplicityBasis _ e).toBasis,
    ← ContinuousLinearMap.adjoint_toLinearMap,
    LinearMap.toMatrix_adjoint (EuclideanSpace.basisFun n ℂ) (multiplicityBasis _ e),
    Matrix.mul_assoc]
  congr 2
  exact toMatrix_multiplicityBasis _ e B

/-- **Stinespring's theorem** for the Stinespring matrix `V`: `φ(A) = tr₂(V A Vᴴ)`. -/
theorem apply_eq_traceRight_stinespringMatrix (φ : Matrix n n ℂ →CP Matrix m m ℂ) {i₀ : m}
    (e : OrthonormalBasis ι ℂ (multiplicitySpace φ.matrixTraceDual.toEuclidean.stinespringStarAlgHom i₀))
    (A : Matrix n n ℂ) :
    φ A = tr₂(φ.stinespringMatrix e * A * (φ.stinespringMatrix e)ᴴ) := by
  classical
  exact (traceDual_eq_iff_stinespring (φ.stinespringMatrix e)).1
    (φ.traceDual_eq_stinespringMatrix e) A

/-- **Minimality of the Stinespring matrix**: its Kraus blocks `Kₖ = Matrix.krausBlock V k` are
linearly independent. This is the minimality of the Stinespring representation
(`CompletelyPositiveMap.topologicalClosure_span_stinespringNonUnitalStarAlgHom_apply_stinespringOperator_eq_top`):
if `Σₖ gₖ Kₖ = 0`, the vector `x = V_{i₀} (Σₖ ḡₖ e k)` is orthogonal to `W ξ`, hence, as
`π(B)† V_{i₀} = Σⱼ B̄_{i₀ j} Vⱼ`, to every `π(B) W ξ`, so `x = 0` and `g = 0`. -/
theorem linearIndependent_krausBlock_stinespringMatrix (φ : Matrix n n ℂ →CP Matrix m m ℂ)
    {i₀ : m}
    (e : OrthonormalBasis ι ℂ (multiplicitySpace φ.matrixTraceDual.toEuclidean.stinespringStarAlgHom i₀)) :
    LinearIndependent ℂ (krausBlock (φ.stinespringMatrix e)) := by
  set W := φ.matrixTraceDual.toEuclidean.stinespringOperator
  set f := EuclideanSpace.basisFun n ℂ
  set U := multiplicityIsometry φ.matrixTraceDual.toEuclidean.stinespringStarAlgHom i₀
  rw [Fintype.linearIndependent_iff]
  intro g hg
  set y := ∑ k, star (g k) • e k
  have h1 : ∀ a ξ, ⟪U a y, W ξ⟫_ℂ = 0 := by
    intro a ξ
    rw [← f.sum_repr ξ]
    simp only [map_sum, map_smul, inner_sum, inner_smul_right]
    refine Finset.sum_eq_zero fun j _ => ?_
    have := congrFun (congrFun hg a) j
    simp only [Matrix.sum_apply, Matrix.smul_apply, krausBlock_apply, stinespringMatrix_apply,
      smul_eq_mul, Matrix.zero_apply] at this
    simp only [y, map_sum, map_smul, sum_inner, inner_smul_left, starRingEnd_apply, star_star]
    rw [this, mul_zero]
  have h2 : U i₀ y ∈ (Submodule.span ℂ (Set.range fun p : Matrix m m ℂ × EuclideanSpace ℂ n =>
      φ.matrixTraceDual.toEuclidean.stinespringNonUnitalStarAlgHom p.1 (W p.2)))ᗮ := by
    refine (Submodule.mem_orthogonal' _ _).2 fun u hu => ?_
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨B, ξ⟩, rfl⟩ := hx
      dsimp only
      rw [← stinespringStarAlgHom_apply, ← ContinuousLinearMap.adjoint_inner_left,
        ← ContinuousLinearMap.star_eq_adjoint, ← map_star, map_apply_multiplicityIsometry,
        sum_inner]
      exact Finset.sum_eq_zero fun i _ => by rw [inner_smul_left, h1, mul_zero]
    | zero => exact inner_zero_right _
    | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
    | smul c x _ hx => rw [inner_smul_right, hx, mul_zero]
  rw [(Submodule.topologicalClosure_eq_top_iff).1
    (CompletelyPositiveMap.topologicalClosure_span_stinespringNonUnitalStarAlgHom_apply_stinespringOperator_eq_top
      φ.matrixTraceDual.toEuclidean),
    Submodule.mem_bot, map_eq_zero_iff _ (U i₀).injective] at h2
  intro k
  simpa using Fintype.linearIndependent_iff.1 e.orthonormal.linearIndependent _ h2 k

/-- The environment of the Stinespring matrix has the minimal dimension `card ι = rank J(φ)`: its
Kraus blocks are a Kraus representation of `φ` (`Matrix.traceRight_mul_mul_conjTranspose`) by
linearly independent operators (`CompletelyPositiveMap.linearIndependent_krausBlock_stinespringMatrix`),
hence with exactly `rank J(φ)` of them (`Matrix.rank_choiMatrix_eq_card_iff_linearIndependent`). -/
theorem card_eq_rank_choiMatrix (φ : Matrix n n ℂ →CP Matrix m m ℂ) {i₀ : m}
    (e : OrthonormalBasis ι ℂ (multiplicitySpace φ.matrixTraceDual.toEuclidean.stinespringStarAlgHom i₀)) :
    Fintype.card ι = (choiMatrix φ).rank :=
  ((rank_choiMatrix_eq_card_iff_linearIndependent (krausBlock (φ.stinespringMatrix e)) fun A => by
    rw [← traceRight_mul_mul_conjTranspose, ← φ.apply_eq_traceRight_stinespringMatrix e]).2
    (φ.linearIndependent_krausBlock_stinespringMatrix e)).symm

/-- The environment dimension is the rank of the Choi matrix, `r = rank J(φ)`, for every `i₀`. -/
theorem stinespringEnvDim_eq_rank_choiMatrix (φ : Matrix n n ℂ →CP Matrix m m ℂ) (i₀ : m) :
    φ.stinespringEnvDim i₀ = (choiMatrix φ).rank := by
  rw [← φ.card_eq_rank_choiMatrix (stdOrthonormalBasis ℂ _), Fintype.card_fin, stinespringEnvDim]

end StinespringMatrix

open scoped Matrix.Norms.L2Operator MatrixOrder Kronecker in
/-- **Stinespring's theorem, Heisenberg picture**, for matrix algebras: the trace dual of a
completely positive map `φ : M_n(ℂ) → M_m(ℂ)` is `φ*(B) = Vᴴ (B ⊗ 1) V` for some
`V : ℂⁿ → ℂᵐ ⊗ ℂ^E` with environment `E = Fin r` of the minimal dimension `r = rank J(φ) ≤ nm`
(`Matrix.rank_choiMatrix_le_card_of_stinespring`). The explicit witness is the Stinespring matrix
(`CompletelyPositiveMap.traceDual_eq_stinespringMatrix`). -/
theorem exists_traceDual_eq_stinespringMatrix (φ : Matrix n n ℂ →CP Matrix m m ℂ) :
    ∃ V : Matrix (m × Fin (choiMatrix φ).rank) n ℂ, ∀ B, Matrix.traceDual φ B =
      Vᴴ * (B ⊗ₖ (1 : Matrix (Fin (choiMatrix φ).rank) (Fin (choiMatrix φ).rank) ℂ)) * V := by
  cases isEmpty_or_nonempty m with
  | inl _ =>
    refine ⟨0, fun B => ?_⟩
    rw [Subsingleton.elim B 0, map_zero, conjTranspose_zero, Matrix.zero_mul, Matrix.zero_mul]
  | inr hm =>
    suffices ∀ r, φ.stinespringEnvDim hm.some = r → ∃ V : Matrix (m × Fin r) n ℂ,
        ∀ B, Matrix.traceDual φ B = Vᴴ * (B ⊗ₖ (1 : Matrix (Fin r) (Fin r) ℂ)) * V from
      this _ (φ.stinespringEnvDim_eq_rank_choiMatrix hm.some)
    rintro r rfl
    exact ⟨_, φ.traceDual_eq_stinespringMatrix (stdOrthonormalBasis ℂ _)⟩

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- **Stinespring's theorem** for matrix algebras: a completely positive map
`φ : M_n(ℂ) → M_m(ℂ)` is `φ(A) = tr₂(V A Vᴴ)` for some `V : ℂⁿ → ℂᵐ ⊗ ℂ^E` with environment
`E = Fin r` of the minimal dimension `r = rank J(φ) ≤ nm`
(`Matrix.rank_choiMatrix_le_card_of_stinespring`). Conversely every such map is completely
positive (`CompletelyPositiveMap.ofMatrixStinespring`). -/
theorem exists_stinespringMatrix (φ : Matrix n n ℂ →CP Matrix m m ℂ) :
    ∃ V : Matrix (m × Fin (choiMatrix φ).rank) n ℂ, ∀ A, φ A = tr₂(V * A * Vᴴ) := by
  obtain ⟨V, hV⟩ := φ.exists_traceDual_eq_stinespringMatrix
  exact ⟨V, (traceDual_eq_iff_stinespring V).1 hV⟩

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- **Stinespring's theorem** for matrix algebras: a linear map `Φ : M_n(ℂ) → M_m(ℂ)` is
completely positive, i.e. it is the linear map of some `φ : M_n(ℂ) →CP M_m(ℂ)`, iff
`Φ(A) = tr₂(V A Vᴴ)` for some `V : ℂⁿ → ℂᵐ ⊗ ℂ^E` with environment `E = Fin r` of the minimal
dimension `r = rank J(Φ) ≤ nm`. -/
theorem exists_coe_eq_iff_exists_stinespringMatrix
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    (∃ φ : Matrix n n ℂ →CP Matrix m m ℂ, (φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) = Φ) ↔
      ∃ V : Matrix (m × Fin (choiMatrix Φ).rank) n ℂ, ∀ A, Φ A = tr₂(V * A * Vᴴ) :=
  ⟨fun ⟨φ, hφ⟩ => hφ ▸ φ.exists_stinespringMatrix,
    fun ⟨V, hV⟩ => ⟨ofMatrixStinespring Φ V hV, rfl⟩⟩

end CompletelyPositiveMap

namespace Matrix

variable {n m : Type*} [Fintype n] [Fintype m]

open scoped ComplexOrder Kronecker

/-! ### Minimality -/

section Minimality

variable [DecidableEq n] {F : Type*} [FunLike F (Matrix n n ℂ) (Matrix m m ℂ)]

/-- **Minimality of the environment**: if `Φ(A) = tr₂(V A Vᴴ)` for `V : Matrix (m × ι) n ℂ`, the
environment `ι` has at least `rank J(Φ)` elements, the dimension attained by the Stinespring matrix
(`CompletelyPositiveMap.card_eq_rank_choiMatrix`): the Kraus blocks of `V` are Kraus operators of
`Φ` (`Matrix.rank_choiMatrix_le_card_of_kraus`). -/
theorem rank_choiMatrix_le_card_of_stinespring {Φ : F} {ι : Type*} [Fintype ι]
    (V : Matrix (m × ι) n ℂ) (hV : ∀ A, Φ A = tr₂(V * A * Vᴴ)) :
    (choiMatrix Φ).rank ≤ Fintype.card ι :=
  rank_choiMatrix_le_card_of_kraus (krausBlock V) fun A => by
    rw [hV, traceRight_mul_mul_conjTranspose]

/-- The environment of `Φ(A) = tr₂(V A Vᴴ)` has the minimal dimension `rank J(Φ)` iff the Kraus
blocks `Kᵢ = Matrix.krausBlock V i` of `V` are linearly independent. -/
theorem rank_choiMatrix_eq_card_iff_linearIndependent_krausBlock {Φ : F} {ι : Type*} [Fintype ι]
    (V : Matrix (m × ι) n ℂ) (hV : ∀ A, Φ A = tr₂(V * A * Vᴴ)) :
    (choiMatrix Φ).rank = Fintype.card ι ↔ LinearIndependent ℂ (krausBlock V) :=
  rank_choiMatrix_eq_card_iff_linearIndependent (krausBlock V) fun A => by
    rw [hV, traceRight_mul_mul_conjTranspose]

end Minimality

/-! ### Quantum channels -/

variable [DecidableEq n] [DecidableEq m]

/-- **Stinespring's theorem, Heisenberg picture**, for quantum channels: the trace dual of a
quantum channel `Φ : M_n(ℂ) → M_m(ℂ)` is the unital map `Φ*(B) = Vᴴ (B ⊗ 1) V` for an isometry
`V : ℂⁿ → ℂᵐ ⊗ ℂ^E`, `Vᴴ V = I`, with environment `E = Fin r` of the minimal dimension
`r = rank J(Φ) ≤ nm`. The isometry is `Vᴴ V = Vᴴ (1 ⊗ 1) V = Φ*(1) = 1`. -/
theorem QuantumChannel.exists_traceDual_eq_stinespringMatrix (Φ : QuantumChannel n m) :
    ∃ V : Matrix (m × Fin (choiMatrix Φ).rank) n ℂ, Vᴴ * V = 1 ∧
      ∀ B, traceDual Φ B = Vᴴ *
        (B ⊗ₖ
          (1 : Matrix (Fin (choiMatrix Φ).rank) (Fin (choiMatrix Φ).rank) ℂ)) * V := by
  refine Φ.toCompletelyPositiveMap.exists_traceDual_eq_stinespringMatrix.imp fun V hV => ⟨?_, hV⟩
  rw [← Matrix.mul_one Vᴴ, ← one_kronecker_one, ← hV]
  exact traceDual_one Φ.isTracePreserving

/-- **Stinespring's theorem** for quantum channels: a quantum channel `Φ : M_n(ℂ) → M_m(ℂ)` is
`Φ(A) = tr₂(V A Vᴴ)` for an isometry `V : ℂⁿ → ℂᵐ ⊗ ℂ^E`, `Vᴴ V = I`, with environment
`E = Fin r` of the minimal dimension `r = rank J(Φ) ≤ nm`. Conversely every such map is a quantum
channel (`Matrix.QuantumChannel.ofStinespring`). -/
theorem QuantumChannel.exists_stinespringMatrix (Φ : QuantumChannel n m) :
    ∃ V : Matrix (m × Fin (choiMatrix Φ).rank) n ℂ,
      Vᴴ * V = 1 ∧ ∀ A, Φ A = tr₂(V * A * Vᴴ) := by
  obtain ⟨V, hVV, hV⟩ := Φ.exists_traceDual_eq_stinespringMatrix
  exact ⟨V, hVV, (traceDual_eq_iff_stinespring V).1 hV⟩

/-- **Stinespring's theorem** for quantum channels, converse: `A ↦ tr₂(V A Vᴴ)` for an isometry
`V`, `Vᴴ V = I`, is a quantum channel. -/
noncomputable def QuantumChannel.ofStinespring (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) {ι : Type*} [Fintype ι]
    (V : Matrix (m × ι) n ℂ) (hVV : Vᴴ * V = 1) (hV : ∀ A, Φ A = tr₂(V * A * Vᴴ)) : QuantumChannel n m :=
  ⟨.ofMatrixStinespring Φ V hV, fun A => by
    change Tr (Φ A) = Tr A
    rw [hV, trace_traceRight, Matrix.trace_mul_cycle, hVV, Matrix.one_mul]⟩

/-- The quantum channel `Matrix.QuantumChannel.ofStinespring Φ V hVV hV` is `Φ` as a function. -/
@[simp] lemma QuantumChannel.coe_ofStinespring (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) {ι : Type*} [Fintype ι]
    (V : Matrix (m × ι) n ℂ) (hVV : Vᴴ * V = 1) (hV : ∀ A, Φ A = tr₂(V * A * Vᴴ)) :
    ⇑(QuantumChannel.ofStinespring Φ V hVV hV) = Φ :=
  rfl

/-- **Stinespring's theorem** for quantum channels: a linear map `Φ : M_n(ℂ) → M_m(ℂ)` is a quantum
channel iff `Φ(A) = tr₂(V A Vᴴ)` for an isometry `V : ℂⁿ → ℂᵐ ⊗ ℂ^E`, `Vᴴ V = I`, with
environment `E = Fin r` of the minimal dimension `r = rank J(Φ) ≤ nm`. -/
theorem QuantumChannel.exists_coe_eq_iff_exists_stinespringMatrix
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    (∃ Ψ : QuantumChannel n m, (Ψ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) = Φ) ↔
      ∃ V : Matrix (m × Fin (choiMatrix Φ).rank) n ℂ, Vᴴ * V = 1 ∧ ∀ A, Φ A = tr₂(V * A * Vᴴ) :=
  ⟨fun ⟨Ψ, hΨ⟩ => hΨ ▸ Ψ.exists_stinespringMatrix,
    fun ⟨V, hVV, hV⟩ => ⟨QuantumChannel.ofStinespring Φ V hVV hV, rfl⟩⟩

end Matrix
