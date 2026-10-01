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

A linear map `Φ : M_n(ℂ) → M_m(ℂ)` is completely positive iff it is `A ↦ tr₁(V A Vᴴ)` for some
`V : Matrix (Fin r × m) n ℂ`, and a quantum channel iff moreover `V` is an isometry, `Vᴴ V = I`
(`CompletelyPositiveMap.exists_toLinearMap_eq_iff_exists_stinespringMatrix`,
`Matrix.QuantumChannel.exists_toLinearMap_eq_iff_exists_stinespringMatrix`). The environment
`E = Fin r` has the dimension `r = rank J(Φ) ≤ nm` of the Choi matrix `J(Φ)`, and this is minimal:
every such `V` has an environment with at least `rank J(Φ)` elements
(`Matrix.rank_choiMatrix_le_card_of_stinespring`), with equality iff its row blocks are linearly
independent (`Matrix.rank_choiMatrix_eq_card_iff_linearIndependent_krausBlock`).

This is the Schrödinger-picture form of Stinespring's dilation (Watrous, Theorem 2.22 and
Corollary 2.27). Stinespring's original Heisenberg-picture statement, that the trace dual is
`Φ*(B) = Vᴴ (1 ⊗ B) V`, is `CompletelyPositiveMap.exists_traceDual_eq_stinespringMatrix`, and
`Matrix.QuantumChannel.exists_traceDual_eq_stinespringMatrix` with `V` an isometry. For a fixed `V`
the two pictures are equivalent (`Matrix.traceDual_eq_iff_stinespring`).

## Derivation from the general theorem

The existence of `V` is derived from Stinespring's theorem for completely positive maps into
`B(H)` (`QuantumSystem/ForMathlib/Analysis/CStarAlgebra/Stinespring.lean`) rather than by stacking
Kraus operators; no Kraus representation of `φ` is used. The trace dual `φ* : M_m(ℂ) → M_n(ℂ)` is
completely positive by self-duality of the positive semidefinite cone for the trace pairing
(`CompletelyPositiveMap.traceDual`). Hence so is `ψ = φ* : M_m(ℂ) →CP B(ℂⁿ)`, and the general
theorem gives `ψ(B) = W† π(B) W` for a unital ⋆-representation `π` of `M_m(ℂ)` on the Stinespring
space `K` and the Stinespring operator `W : ℂⁿ → K`. The space `K` is the completion of
`M_m(ℂ) ⊗ ℂⁿ`, so `dim K ≤ m² n`. A unital ⋆-representation of `M_m(ℂ)` is a multiple of the
identity representation (`QuantumSystem/ForMathlib/Analysis/InnerProductSpace/MatrixRepresentation.lean`):
`K ≅ ℂʳ ⊗ ℂᵐ` with `π(B) = 1 ⊗ B`, where `r · m = dim K`, hence `r ≤ nm`. For an orthonormal basis
`e` of the multiplicity space `ℂʳ`, `W` is in the adapted basis `Matrix.multiplicityBasis π e` of
`K` the matrix `V = CompletelyPositiveMap.stinespringMatrix φ e`
(`CompletelyPositiveMap.toLin_stinespringMatrix`), and `ψ(B) = W† π(B) W` reads
`φ*(B) = Vᴴ (1 ⊗ B) V`. The name "Stinespring operator" is reserved for the operator `W` of the
general theorem; `V` is its matrix.

The minimality of the Stinespring representation, that the vectors `π(B) W ξ` span `K`, makes the
row blocks of `V` linearly independent
(`CompletelyPositiveMap.linearIndependent_krausBlock_stinespringMatrix`). They are Kraus operators
of `φ`, so `r = rank J(φ)` (`CompletelyPositiveMap.card_eq_rank_choiMatrix`): the general theorem
produces an environment of the minimal dimension without any choice of Kraus operators.

## Kraus blocks

Conversely, the row blocks `Kᵢ a b = V (i, a) b` (`Matrix.krausBlock V i`) of any
`V : Matrix (ι × m) n ℂ` are Kraus operators for `A ↦ tr₁(V A Vᴴ) = Σᵢ Kᵢ A Kᵢᴴ`, so that map is
completely positive (`CompletelyPositiveMap.ofStinespring`). Since `Vᴴ V = Σᵢ Kᵢᴴ Kᵢ`, the matrix
`V` is an isometry iff its row blocks satisfy the completeness relation `Σᵢ Kᵢᴴ Kᵢ = I`, and every
family of Kraus operators is the family of row blocks of the matrix obtained by stacking it
(`Matrix.exists_krausBlock_eq`).

## Conventions

The environment is the **left** factor of `E × ℂᵐ` and is removed by the partial trace
`tr₁ = Matrix.traceLeft` (the notation of
`QuantumSystem/Analysis/Matrix/DensityMatrix/Kronecker.lean`). Watrous places the environment
on the right, `Φ(X) = Tr_Z (A X A*)` with `A : X → Y ⊗ Z`; the two forms differ by a swap of
tensor factors, as for the Choi matrix (`QuantumSystem/Analysis/Matrix/QuantumChannel/Choi.lean`).

This file treats the finite-dimensional matrix algebras `M_n(ℂ)`: complete positivity is
Mathlib's `CompletelyPositiveMap` condition for general C⋆-algebras, specialised to `Matrix n n ℂ`.
The operator-algebraic side is not confined to matrices. Stinespring's theorem itself holds for
completely positive maps `A → B(H)` on arbitrary, possibly non-unital, C⋆-algebras
(`CompletelyPositiveMap.exists_stinespring_dilation`). The Kadison–Schwarz inequality
`φ(a)⋆ φ(a) ≤ ‖φ 1‖ • φ(a⋆ a)` for `2`-positive, in particular completely positive, maps between
arbitrary unital C⋆-algebras is `KPositiveMapClass.le_norm_smul_map_star_mul`, with the normalised
form `KPositiveMapClass.le_map_star_mul` under `φ 1 ≤ 1`
(`QuantumSystem/ForMathlib/Analysis/CStarAlgebra/KPositiveMap.lean`), and Kraus maps between the
operator algebras of arbitrary Hilbert spaces are `SchwarzMap.ofKraus`
(`QuantumSystem/ForMathlib/Analysis/CStarAlgebra/SchwarzMap.lean`). A matrix channel enters that
setting through its trace dual, a Schwarz map on `B(ℂᵐ)` (`Matrix.QuantumChannel.dualSchwarzMap` in
`QuantumSystem/Analysis/Matrix/QuantumChannel/Dual.lean`).

## Main definitions

* `Matrix.krausBlock V i`: the row block `Kᵢ a b = V (i, a) b` of `V : Matrix (ι × m) n ℂ`.
* `CompletelyPositiveMap.stinespringEnvDim φ i₀`: the environment dimension `r`, the dimension of
  the multiplicity space at `i₀` of the Stinespring representation.
* `CompletelyPositiveMap.stinespringMatrix φ e`: the matrix of the Stinespring operator of
  `φ.traceDual.toEuclidean` in the basis of the Stinespring space adapted to `K ≅ ℂ^ι ⊗ ℂᵐ` by an
  orthonormal basis `e` of the multiplicity space indexed by `ι`, with environment `ι`.
* `CompletelyPositiveMap.ofStinespring`: `A ↦ tr₁(V A Vᴴ)` as a completely positive map.
* `Matrix.QuantumChannel.ofStinespring`: `A ↦ tr₁(V A Vᴴ)` for an isometry `V` as a quantum
  channel.

## Main statements

* `Matrix.conjTranspose_mul_self_eq_sum_krausBlock`: `Vᴴ V = Σᵢ Kᵢᴴ Kᵢ`.
* `Matrix.traceLeft_mul_mul_conjTranspose`: `tr₁(V A Vᴴ) = Σᵢ Kᵢ A Kᵢᴴ`, the sum of the diagonal
  blocks of `V A Vᴴ`.
* `Matrix.traceDual_eq_iff_stinespring`: for a fixed `V`, the trace dual is
  `Φ*(B) = Vᴴ (1 ⊗ B) V` for all `B` iff `Φ(A) = tr₁(V A Vᴴ)` for all `A`.
* `CompletelyPositiveMap.traceDual_eq_stinespringMatrix`,
  `CompletelyPositiveMap.apply_eq_traceLeft_stinespringMatrix`: `φ*(B) = Vᴴ (1 ⊗ B) V` and
  `φ(A) = tr₁(V A Vᴴ)` for the Stinespring matrix `V`.
* `CompletelyPositiveMap.linearIndependent_krausBlock_stinespringMatrix`,
  `CompletelyPositiveMap.card_eq_rank_choiMatrix`,
  `CompletelyPositiveMap.stinespringEnvDim_eq_rank_choiMatrix`: the row blocks of the Stinespring
  matrix are linearly independent, and its environment has dimension `r = rank J(φ)`; in
  particular `r ≤ nm` (`CompletelyPositiveMap.stinespringEnvDim_le`).
* `Matrix.rank_choiMatrix_le_card_of_stinespring`: **minimality**: every `V` with
  `Φ(A) = tr₁(V A Vᴴ)` has an environment with at least `rank J(Φ)` elements;
  `Matrix.rank_choiMatrix_eq_card_iff_linearIndependent_krausBlock`: with equality iff its row
  blocks are linearly independent.
* `CompletelyPositiveMap.exists_traceDual_eq_stinespringMatrix`: **Stinespring's theorem,
  Heisenberg picture**: the trace dual of a CP map is `B ↦ Vᴴ (1 ⊗ B) V` for some `V` with
  environment `Fin (rank J(φ))`.
* `CompletelyPositiveMap.exists_stinespringMatrix`: a CP map is `A ↦ tr₁(V A Vᴴ)` for some `V`
  with environment `Fin (rank J(φ))`; the converse is `CompletelyPositiveMap.ofStinespring`.
* `CompletelyPositiveMap.exists_toLinearMap_eq_iff_exists_stinespringMatrix`: **Stinespring's
  theorem**: a linear map is completely positive iff it is `A ↦ tr₁(V A Vᴴ)` for some `V`.
* `Matrix.QuantumChannel.exists_traceDual_eq_stinespringMatrix`: the trace dual of a quantum channel is
  `B ↦ Vᴴ (1 ⊗ B) V` for an isometry `V`.
* `Matrix.QuantumChannel.exists_stinespringMatrix`: a quantum channel is `A ↦ tr₁(V A Vᴴ)` for an
  isometry `V`; the converse is `Matrix.QuantumChannel.ofStinespring`.
* `Matrix.QuantumChannel.exists_toLinearMap_eq_iff_exists_stinespringMatrix`: a linear map is a
  quantum channel iff it is `A ↦ tr₁(V A Vᴴ)` for an isometry `V`.

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
/-- The row blocks `Kᵢ a b = V (i, a) b` of `V : Matrix (ι × m) n R`. They are the Kraus operators
of `A ↦ tr₁(V A Vᴴ)` (`traceLeft_mul_mul_conjTranspose`), and every family of matrices arises this
way (`exists_krausBlock_eq`). -/
def krausBlock (V : Matrix (ι × m) n R) (i : ι) : Matrix m n R :=
  Matrix.of fun a b => V (i, a) b

omit [Fintype n] [Fintype m] in
/-- `Kᵢ a b = V (i, a) b`. -/
@[simp] lemma krausBlock_apply (V : Matrix (ι × m) n R) (i : ι) (a : m) (b : n) :
    krausBlock V i a b = V (i, a) b :=
  rfl

omit [Fintype n] [Fintype m] in
/-- Every family `Kᵢ : Matrix m n R` is the family of row blocks of the matrix `V (i, a) b = Kᵢ a b`
obtained by stacking it. -/
lemma exists_krausBlock_eq (K : ι → Matrix m n R) :
    ∃ V : Matrix (ι × m) n R, ∀ i, krausBlock V i = K i :=
  ⟨Matrix.of fun p b => K p.1 p.2 b, fun _ => rfl⟩

omit [Fintype n] in
/-- `Vᴴ V = Σᵢ Kᵢᴴ Kᵢ` for the row blocks `Kᵢ` of `V`. In particular `V` is an isometry,
`Vᴴ V = I`, iff its row blocks satisfy the Kraus completeness relation `Σᵢ Kᵢᴴ Kᵢ = I`. -/
lemma conjTranspose_mul_self_eq_sum_krausBlock [Fintype ι] [NonUnitalSemiring R] [StarRing R]
    (V : Matrix (ι × m) n R) : Vᴴ * V = ∑ i, (krausBlock V i)ᴴ * krausBlock V i := by
  ext a b
  simp [Matrix.mul_apply, Matrix.sum_apply, Fintype.sum_prod_type]

omit [Fintype m] in
/-- Conjugation by `V` followed by the partial trace over `ι` is the Kraus map of the row blocks
`Kᵢ` of `V`: `tr₁(V A Vᴴ) = Σᵢ Kᵢ A Kᵢᴴ`, the sum of the diagonal blocks of `V A Vᴴ`. -/
lemma traceLeft_mul_mul_conjTranspose [Fintype ι] [NonUnitalSemiring R] [StarRing R]
    (V : Matrix (ι × m) n R) (A : Matrix n n R) :
    tr₁(V * A * Vᴴ) = ∑ i, krausBlock V i * A * (krausBlock V i)ᴴ := by
  ext a b
  simp [traceLeft_apply, Matrix.sum_apply, Matrix.mul_apply]

end KrausBlock

/-! ### Heisenberg picture -/

section Heisenberg

variable [DecidableEq n] {F : Type*} [FunLike F (Matrix n n ℂ) (Matrix m m ℂ)]
  [LinearMapClass F ℂ (Matrix n n ℂ) (Matrix m m ℂ)]

omit [DecidableEq n] in
/-- The Stinespring pairing: `Tr (tr₁(V A Vᴴ) B) = Tr (A Vᴴ (1 ⊗ B) V)`. -/
lemma trace_traceLeft_mul_mul_conjTranspose_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : Matrix (ι × m) n ℂ) (A : Matrix n n ℂ) (B : Matrix m m ℂ) :
    Tr (tr₁(V * A * Vᴴ) * B) = Tr (A * (Vᴴ * ((1 : Matrix ι ι ℂ) ⊗ₖ B) * V)) := by
  rw [← trace_mul_kronecker_one_left]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm V]
  simp only [Matrix.mul_assoc]

/-- Heisenberg and Schrödinger pictures of conjugation by a matrix `V`: the trace dual of `Φ` is
`Φ*(B) = Vᴴ (1 ⊗ B) V` for all `B` iff `Φ(A) = tr₁(V A Vᴴ)` for all `A`. -/
theorem traceDual_eq_iff_stinespring {ι : Type*} [Fintype ι] [DecidableEq ι] {Φ : F}
    (V : Matrix (ι × m) n ℂ) :
    (∀ B, traceDual Φ B = Vᴴ * ((1 : Matrix ι ι ℂ) ⊗ₖ B) * V) ↔
      ∀ A, Φ A = tr₁(V * A * Vᴴ) := by
  constructor
  · intro h A
    refine Matrix.ext_iff_trace_mul_right.mpr fun B => ?_
    rw [trace_mul_traceDual, h, trace_traceLeft_mul_mul_conjTranspose_mul]
  · intro hV B
    refine Matrix.ext_iff_trace_mul_left.mpr fun A => ?_
    rw [← trace_mul_traceDual, hV, trace_traceLeft_mul_mul_conjTranspose_mul]

/-- If `Φ(A) = tr₁(V A Vᴴ)` for all `A`, then the trace dual of `Φ` is `Φ*(B) = Vᴴ (1 ⊗ B) V`. -/
theorem traceDual_eq_of_stinespring {ι : Type*} [Fintype ι] [DecidableEq ι] {Φ : F}
    (V : Matrix (ι × m) n ℂ) (hV : ∀ A, Φ A = tr₁(V * A * Vᴴ)) (B : Matrix m m ℂ) :
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
tracing out the environment `ι` is completely positive; its Kraus operators are the row blocks
`Matrix.krausBlock V i` of `V`. -/
def ofStinespring (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) {ι : Type*} [Fintype ι]
    (V : Matrix (ι × m) n ℂ) (hV : ∀ A, Φ A = tr₁(V * A * Vᴴ)) :
    Matrix n n ℂ →CP Matrix m m ℂ :=
  ofKraus Φ (krausBlock V) fun A => by rw [hV, traceLeft_mul_mul_conjTranspose]

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- The completely positive map `CompletelyPositiveMap.ofStinespring Φ V hV` is `Φ` as a function. -/
@[simp] lemma coe_ofStinespring (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) {ι : Type*} [Fintype ι]
    (V : Matrix (ι × m) n ℂ) (hV : ∀ A, Φ A = tr₁(V * A * Vᴴ)) :
    ⇑(ofStinespring Φ V hV) = Φ :=
  rfl

/-! ### The Stinespring matrix -/

section StinespringMatrix

open scoped Matrix.Norms.L2Operator MatrixOrder InnerProductSpace

/-- The Stinespring space of `φ.traceDual.toEuclidean` is finite-dimensional: it is the completion of the
finite-dimensional space `M_m(ℂ) ⊗ ℂⁿ`. -/
instance (φ : Matrix n n ℂ →CP Matrix m m ℂ) : FiniteDimensional ℂ φ.traceDual.toEuclidean.Stinespring :=
  FiniteDimensional.completion

/-- The dimension `r` of the environment of the Stinespring matrix: the dimension of the multiplicity
space at `i₀` of the Stinespring representation of `φ.traceDual.toEuclidean`. It does not depend on `i₀`
(`CompletelyPositiveMap.stinespringEnvDim_eq`), and it is the rank of the Choi matrix
(`CompletelyPositiveMap.stinespringEnvDim_eq_rank_choiMatrix`). -/
noncomputable def stinespringEnvDim (φ : Matrix n n ℂ →CP Matrix m m ℂ) (i₀ : m) : ℕ :=
  Module.finrank ℂ (multiplicitySpace φ.traceDual.toEuclidean.stinespringStarAlgHom i₀)

variable {ι : Type*} [Fintype ι]

/-- The **Stinespring matrix** `V : Matrix (ι × m) n ℂ` of a completely positive map
`φ : M_n(ℂ) → M_m(ℂ)`, for an orthonormal basis `e` indexed by `ι` of the multiplicity space at
`i₀` of the Stinespring representation `π` of `φ.traceDual.toEuclidean`: the matrix of the
Stinespring operator `φ.traceDual.toEuclidean.stinespringOperator : ℂⁿ → K`
(`CompletelyPositiveMap.toLin_stinespringMatrix`) in the standard basis of `ℂⁿ` and the basis
`b (k, i) = multiplicityIsometry π i₀ i (e k)` of `K` adapted to `K ≅ ℂ^ι ⊗ ℂᵐ`
(`Matrix.multiplicityBasis π e`). It satisfies `φ*(B) = Vᴴ (1 ⊗ B) V`
(`CompletelyPositiveMap.traceDual_eq_stinespringMatrix`) and `φ(A) = tr₁(V A Vᴴ)`
(`CompletelyPositiveMap.apply_eq_traceLeft_stinespringMatrix`). It depends on the choices of `i₀`
and of `e`; its environment dimension `card ι = rank J(φ)` does not
(`CompletelyPositiveMap.card_eq_rank_choiMatrix`). -/
noncomputable def stinespringMatrix (φ : Matrix n n ℂ →CP Matrix m m ℂ) {i₀ : m}
    (e : OrthonormalBasis ι ℂ (multiplicitySpace φ.traceDual.toEuclidean.stinespringStarAlgHom i₀)) :
    Matrix (ι × m) n ℂ :=
  LinearMap.toMatrix (EuclideanSpace.basisFun n ℂ).toBasis
    (multiplicityBasis φ.traceDual.toEuclidean.stinespringStarAlgHom e).toBasis
    (φ.traceDual.toEuclidean.stinespringOperator : EuclideanSpace ℂ n →ₗ[ℂ] φ.traceDual.toEuclidean.Stinespring)

/-- The Stinespring matrix is the matrix of the Stinespring operator of `φ.traceDual.toEuclidean`: read back
in the same bases, it is that operator. -/
lemma toLin_stinespringMatrix (φ : Matrix n n ℂ →CP Matrix m m ℂ) {i₀ : m}
    (e : OrthonormalBasis ι ℂ (multiplicitySpace φ.traceDual.toEuclidean.stinespringStarAlgHom i₀)) :
    Matrix.toLin (EuclideanSpace.basisFun n ℂ).toBasis
      (multiplicityBasis φ.traceDual.toEuclidean.stinespringStarAlgHom e).toBasis
      (φ.stinespringMatrix e) = φ.traceDual.toEuclidean.stinespringOperator :=
  Matrix.toLin_toMatrix _ _ _

/-- The entries of the Stinespring matrix are `V ((k, a), j) = ⟪V_a (e k), W eⱼ⟫`, with `W` the
Stinespring operator and `V_a = multiplicityIsometry π i₀ a`. -/
lemma stinespringMatrix_apply (φ : Matrix n n ℂ →CP Matrix m m ℂ) {i₀ : m}
    (e : OrthonormalBasis ι ℂ (multiplicitySpace φ.traceDual.toEuclidean.stinespringStarAlgHom i₀))
    (k : ι) (a : m) (j : n) :
    φ.stinespringMatrix e (k, a) j =
      ⟪multiplicityIsometry φ.traceDual.toEuclidean.stinespringStarAlgHom i₀ a (e k),
        φ.traceDual.toEuclidean.stinespringOperator (EuclideanSpace.basisFun n ℂ j)⟫_ℂ := by
  simp only [stinespringMatrix, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis, ContinuousLinearMap.coe_coe]
  exact congrArg (fun x => ⟪x, _⟫_ℂ) (multiplicityBasis_apply _ e (k, a))

/-- The environment dimension is `r = dim K / m`, independently of `i₀`. -/
lemma stinespringEnvDim_eq (φ : Matrix n n ℂ →CP Matrix m m ℂ) (i₀ : m) :
    φ.stinespringEnvDim i₀ = Module.finrank ℂ φ.traceDual.toEuclidean.Stinespring / Fintype.card m := by
  rw [stinespringEnvDim, finrank_eq_finrank_multiplicitySpace_mul φ.traceDual.toEuclidean.stinespringStarAlgHom i₀,
    Nat.mul_div_cancel _ (Fintype.card_pos_iff.mpr ⟨i₀⟩)]

/-- The environment has dimension `r ≤ nm`: `r · m = dim K ≤ dim (M_m(ℂ) ⊗ ℂⁿ) = m² n`. -/
lemma stinespringEnvDim_le (φ : Matrix n n ℂ →CP Matrix m m ℂ) (i₀ : m) :
    φ.stinespringEnvDim i₀ ≤ Fintype.card n * Fintype.card m := by
  have hK : Module.finrank ℂ φ.traceDual.toEuclidean.Stinespring ≤
      Fintype.card m * Fintype.card m * Fintype.card n := by
    refine Module.finrank_completion_le.trans_eq ?_
    rw [finrank_preStinespring, Module.finrank_matrix, Module.finrank_self, mul_one,
      finrank_euclideanSpace]
  rw [finrank_eq_finrank_multiplicitySpace_mul φ.traceDual.toEuclidean.stinespringStarAlgHom i₀] at hK
  refine Nat.le_of_mul_le_mul_right ?_ (Fintype.card_pos_iff.mpr ⟨i₀⟩)
  rw [stinespringEnvDim]
  linarith [hK]

open scoped Kronecker in
/-- **Stinespring's theorem, Heisenberg picture**, for the Stinespring matrix `V`:
`φ*(B) = Vᴴ (1 ⊗ B) V`. This is the general theorem
(`CompletelyPositiveMap.apply_eq_adjoint_comp_stinespringStarAlgHom_comp`) for `φ.traceDual.toEuclidean`,
read in the basis `Matrix.multiplicityBasis π e`, in which the unital ⋆-representation `π` of `M_m(ℂ)`
is `1 ⊗ B` (`Matrix.toMatrix_multiplicityBasis`). -/
theorem traceDual_eq_stinespringMatrix [DecidableEq ι] (φ : Matrix n n ℂ →CP Matrix m m ℂ) {i₀ : m}
    (e : OrthonormalBasis ι ℂ (multiplicitySpace φ.traceDual.toEuclidean.stinespringStarAlgHom i₀))
    (B : Matrix m m ℂ) :
    Matrix.traceDual φ B = (φ.stinespringMatrix e)ᴴ * ((1 : Matrix ι ι ℂ) ⊗ₖ B) *
      φ.stinespringMatrix e := by
  set f := (EuclideanSpace.basisFun n ℂ).toBasis
  have hmat : ∀ X : Matrix n n ℂ,
      LinearMap.toMatrix f f (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) X :
        EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n) = X := fun X => by
    rw [coe_toEuclideanCLM_eq_toEuclideanLin, toEuclideanLin_eq_toLin_orthonormal,
      LinearMap.toMatrix_toLin]
  have hψ : Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (Matrix.traceDual φ B) =
      ContinuousLinearMap.adjoint φ.traceDual.toEuclidean.stinespringOperator ∘L
        φ.traceDual.toEuclidean.stinespringStarAlgHom B ∘L
          φ.traceDual.toEuclidean.stinespringOperator :=
    φ.traceDual.toEuclidean.apply_eq_adjoint_comp_stinespringStarAlgHom_comp B
  rw [← hmat (Matrix.traceDual φ B), hψ,
    ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.toMatrix_comp f (multiplicityBasis _ e).toBasis f,
    LinearMap.toMatrix_comp f (multiplicityBasis _ e).toBasis (multiplicityBasis _ e).toBasis,
    ← ContinuousLinearMap.adjoint_toLinearMap,
    LinearMap.toMatrix_adjoint (EuclideanSpace.basisFun n ℂ) (multiplicityBasis _ e),
    Matrix.mul_assoc]
  congr 2
  exact toMatrix_multiplicityBasis _ e B

/-- **Stinespring's theorem** for the Stinespring matrix `V`: `φ(A) = tr₁(V A Vᴴ)`. -/
theorem apply_eq_traceLeft_stinespringMatrix (φ : Matrix n n ℂ →CP Matrix m m ℂ) {i₀ : m}
    (e : OrthonormalBasis ι ℂ (multiplicitySpace φ.traceDual.toEuclidean.stinespringStarAlgHom i₀))
    (A : Matrix n n ℂ) :
    φ A = tr₁(φ.stinespringMatrix e * A * (φ.stinespringMatrix e)ᴴ) := by
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
    (e : OrthonormalBasis ι ℂ (multiplicitySpace φ.traceDual.toEuclidean.stinespringStarAlgHom i₀)) :
    LinearIndependent ℂ (krausBlock (φ.stinespringMatrix e)) := by
  set W := φ.traceDual.toEuclidean.stinespringOperator
  set f := EuclideanSpace.basisFun n ℂ
  set U := multiplicityIsometry φ.traceDual.toEuclidean.stinespringStarAlgHom i₀
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
      φ.traceDual.toEuclidean.stinespringNonUnitalStarAlgHom p.1 (W p.2)))ᗮ := by
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
    φ.traceDual.toEuclidean.topologicalClosure_span_stinespringNonUnitalStarAlgHom_apply_stinespringOperator_eq_top,
    Submodule.mem_bot, map_eq_zero_iff _ (U i₀).injective] at h2
  intro k
  simpa using Fintype.linearIndependent_iff.1 e.orthonormal.linearIndependent _ h2 k

/-- The environment of the Stinespring matrix has the minimal dimension `card ι = rank J(φ)`: its
Kraus blocks are a Kraus representation of `φ` (`Matrix.traceLeft_mul_mul_conjTranspose`) by
linearly independent operators (`CompletelyPositiveMap.linearIndependent_krausBlock_stinespringMatrix`),
hence with exactly `rank J(φ)` of them (`Matrix.rank_choiMatrix_eq_card_iff_linearIndependent`). -/
theorem card_eq_rank_choiMatrix (φ : Matrix n n ℂ →CP Matrix m m ℂ) {i₀ : m}
    (e : OrthonormalBasis ι ℂ (multiplicitySpace φ.traceDual.toEuclidean.stinespringStarAlgHom i₀)) :
    Fintype.card ι = (choiMatrix φ).rank :=
  ((rank_choiMatrix_eq_card_iff_linearIndependent (krausBlock (φ.stinespringMatrix e)) fun A => by
    rw [← traceLeft_mul_mul_conjTranspose, ← φ.apply_eq_traceLeft_stinespringMatrix e]).2
    (φ.linearIndependent_krausBlock_stinespringMatrix e)).symm

/-- The environment dimension is the rank of the Choi matrix, `r = rank J(φ)`, for every `i₀`. -/
theorem stinespringEnvDim_eq_rank_choiMatrix (φ : Matrix n n ℂ →CP Matrix m m ℂ) (i₀ : m) :
    φ.stinespringEnvDim i₀ = (choiMatrix φ).rank := by
  rw [← φ.card_eq_rank_choiMatrix (stdOrthonormalBasis ℂ _), Fintype.card_fin, stinespringEnvDim]

end StinespringMatrix

open scoped Matrix.Norms.L2Operator MatrixOrder Kronecker in
/-- **Stinespring's theorem, Heisenberg picture**, for matrix algebras: the trace dual of a
completely positive map `φ : M_n(ℂ) → M_m(ℂ)` is `φ*(B) = Vᴴ (1 ⊗ B) V` for some
`V : ℂⁿ → ℂ^E ⊗ ℂᵐ` with environment `E = Fin r` of the minimal dimension `r = rank J(φ) ≤ nm`
(`Matrix.rank_choiMatrix_le_card_of_stinespring`). The explicit witness is the Stinespring matrix
(`CompletelyPositiveMap.traceDual_eq_stinespringMatrix`). -/
theorem exists_traceDual_eq_stinespringMatrix (φ : Matrix n n ℂ →CP Matrix m m ℂ) :
    ∃ V : Matrix (Fin (choiMatrix φ).rank × m) n ℂ, ∀ B, Matrix.traceDual φ B =
      Vᴴ * ((1 : Matrix (Fin (choiMatrix φ).rank) (Fin (choiMatrix φ).rank) ℂ) ⊗ₖ B) * V := by
  cases isEmpty_or_nonempty m with
  | inl _ =>
    refine ⟨0, fun B => ?_⟩
    rw [Subsingleton.elim B 0, map_zero, conjTranspose_zero, Matrix.zero_mul, Matrix.zero_mul]
  | inr hm =>
    suffices ∀ r, φ.stinespringEnvDim hm.some = r → ∃ V : Matrix (Fin r × m) n ℂ,
        ∀ B, Matrix.traceDual φ B = Vᴴ * ((1 : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ B) * V from
      this _ (φ.stinespringEnvDim_eq_rank_choiMatrix hm.some)
    rintro r rfl
    exact ⟨_, φ.traceDual_eq_stinespringMatrix (stdOrthonormalBasis ℂ _)⟩

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- **Stinespring's theorem** for matrix algebras: a completely positive map
`φ : M_n(ℂ) → M_m(ℂ)` is `φ(A) = tr₁(V A Vᴴ)` for some `V : ℂⁿ → ℂ^E ⊗ ℂᵐ` with environment
`E = Fin r` of the minimal dimension `r = rank J(φ) ≤ nm`
(`Matrix.rank_choiMatrix_le_card_of_stinespring`). Conversely every such map is completely
positive (`CompletelyPositiveMap.ofStinespring`). -/
theorem exists_stinespringMatrix (φ : Matrix n n ℂ →CP Matrix m m ℂ) :
    ∃ V : Matrix (Fin (choiMatrix φ).rank × m) n ℂ, ∀ A, φ A = tr₁(V * A * Vᴴ) := by
  obtain ⟨V, hV⟩ := φ.exists_traceDual_eq_stinespringMatrix
  exact ⟨V, (traceDual_eq_iff_stinespring V).1 hV⟩

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- **Stinespring's theorem** for matrix algebras: a linear map `Φ : M_n(ℂ) → M_m(ℂ)` is
completely positive, i.e. it is the linear map of some `φ : M_n(ℂ) →CP M_m(ℂ)`, iff
`Φ(A) = tr₁(V A Vᴴ)` for some `V : ℂⁿ → ℂ^E ⊗ ℂᵐ` with environment `E = Fin r` of the minimal
dimension `r = rank J(Φ) ≤ nm`. -/
theorem exists_toLinearMap_eq_iff_exists_stinespringMatrix
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    (∃ φ : Matrix n n ℂ →CP Matrix m m ℂ, φ.toLinearMap = Φ) ↔
      ∃ V : Matrix (Fin (choiMatrix Φ).rank × m) n ℂ, ∀ A, Φ A = tr₁(V * A * Vᴴ) :=
  ⟨fun ⟨φ, hφ⟩ => hφ ▸ φ.exists_stinespringMatrix,
    fun ⟨V, hV⟩ => ⟨ofStinespring Φ V hV, rfl⟩⟩

end CompletelyPositiveMap

namespace Matrix

variable {n m : Type*} [Fintype n] [Fintype m]

open scoped ComplexOrder Kronecker

/-! ### Minimality -/

section Minimality

variable [DecidableEq n] {F : Type*} [FunLike F (Matrix n n ℂ) (Matrix m m ℂ)]

/-- **Minimality of the environment**: if `Φ(A) = tr₁(V A Vᴴ)` for `V : Matrix (ι × m) n ℂ`, the
environment `ι` has at least `rank J(Φ)` elements, the dimension attained by the Stinespring matrix
(`CompletelyPositiveMap.card_eq_rank_choiMatrix`): the row blocks of `V` are Kraus operators of `Φ`
(`Matrix.rank_choiMatrix_le_card_of_kraus`). -/
theorem rank_choiMatrix_le_card_of_stinespring {Φ : F} {ι : Type*} [Fintype ι]
    (V : Matrix (ι × m) n ℂ) (hV : ∀ A, Φ A = tr₁(V * A * Vᴴ)) :
    (choiMatrix Φ).rank ≤ Fintype.card ι :=
  rank_choiMatrix_le_card_of_kraus (krausBlock V) fun A => by
    rw [hV, traceLeft_mul_mul_conjTranspose]

/-- The environment of `Φ(A) = tr₁(V A Vᴴ)` has the minimal dimension `rank J(Φ)` iff the row
blocks `Kᵢ = Matrix.krausBlock V i` of `V` are linearly independent. -/
theorem rank_choiMatrix_eq_card_iff_linearIndependent_krausBlock {Φ : F} {ι : Type*} [Fintype ι]
    (V : Matrix (ι × m) n ℂ) (hV : ∀ A, Φ A = tr₁(V * A * Vᴴ)) :
    (choiMatrix Φ).rank = Fintype.card ι ↔ LinearIndependent ℂ (krausBlock V) :=
  rank_choiMatrix_eq_card_iff_linearIndependent (krausBlock V) fun A => by
    rw [hV, traceLeft_mul_mul_conjTranspose]

end Minimality

/-! ### Quantum channels -/

variable [DecidableEq n] [DecidableEq m]

/-- **Stinespring's theorem, Heisenberg picture**, for quantum channels: the trace dual of a
quantum channel `Φ : M_n(ℂ) → M_m(ℂ)` is the unital map `Φ*(B) = Vᴴ (1 ⊗ B) V` for an isometry
`V : ℂⁿ → ℂ^E ⊗ ℂᵐ`, `Vᴴ V = I`, with environment `E = Fin r` of the minimal dimension
`r = rank J(Φ) ≤ nm`. The isometry is `Vᴴ V = Vᴴ (1 ⊗ 1) V = Φ*(1) = 1`. -/
theorem QuantumChannel.exists_traceDual_eq_stinespringMatrix (Φ : QuantumChannel n m) :
    ∃ V : Matrix (Fin (choiMatrix Φ.toLinearMap).rank × m) n ℂ, Vᴴ * V = 1 ∧
      ∀ B, traceDual Φ.toLinearMap B = Vᴴ *
        ((1 : Matrix (Fin (choiMatrix Φ.toLinearMap).rank) (Fin (choiMatrix Φ.toLinearMap).rank) ℂ) ⊗ₖ
          B) * V := by
  rw [show choiMatrix Φ.toLinearMap = choiMatrix Φ.val from rfl]
  obtain ⟨V, hV⟩ := Φ.val.exists_traceDual_eq_stinespringMatrix
  refine ⟨V, ?_, hV⟩
  rw [← Matrix.mul_one Vᴴ, ← one_kronecker_one, ← hV, traceDual_one Φ.property]

/-- **Stinespring's theorem** for quantum channels: a quantum channel `Φ : M_n(ℂ) → M_m(ℂ)` is
`Φ(A) = tr₁(V A Vᴴ)` for an isometry `V : ℂⁿ → ℂ^E ⊗ ℂᵐ`, `Vᴴ V = I`, with environment
`E = Fin r` of the minimal dimension `r = rank J(Φ) ≤ nm`. Conversely every such map is a quantum
channel (`Matrix.QuantumChannel.ofStinespring`). -/
theorem QuantumChannel.exists_stinespringMatrix (Φ : QuantumChannel n m) :
    ∃ V : Matrix (Fin (choiMatrix Φ.toLinearMap).rank × m) n ℂ,
      Vᴴ * V = 1 ∧ ∀ A, Φ.val A = tr₁(V * A * Vᴴ) := by
  obtain ⟨V, hVV, hV⟩ := Φ.exists_traceDual_eq_stinespringMatrix
  exact ⟨V, hVV, (traceDual_eq_iff_stinespring V).1 hV⟩

/-- **Stinespring's theorem** for quantum channels, converse: `A ↦ tr₁(V A Vᴴ)` for an isometry
`V`, `Vᴴ V = I`, is a quantum channel. -/
noncomputable def QuantumChannel.ofStinespring (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) {ι : Type*} [Fintype ι]
    (V : Matrix (ι × m) n ℂ) (hVV : Vᴴ * V = 1) (hV : ∀ A, Φ A = tr₁(V * A * Vᴴ)) : QuantumChannel n m :=
  ⟨.ofStinespring Φ V hV, fun A => by
    change Tr (Φ A) = Tr A
    rw [hV, trace_traceLeft, Matrix.trace_mul_cycle, hVV, Matrix.one_mul]⟩

/-- The quantum channel `Matrix.QuantumChannel.ofStinespring Φ V hVV hV` is `Φ` as a function. -/
@[simp] lemma QuantumChannel.coe_ofStinespring (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) {ι : Type*} [Fintype ι]
    (V : Matrix (ι × m) n ℂ) (hVV : Vᴴ * V = 1) (hV : ∀ A, Φ A = tr₁(V * A * Vᴴ)) :
    ⇑(QuantumChannel.ofStinespring Φ V hVV hV).val = Φ :=
  rfl

/-- **Stinespring's theorem** for quantum channels: a linear map `Φ : M_n(ℂ) → M_m(ℂ)` is a quantum
channel iff `Φ(A) = tr₁(V A Vᴴ)` for an isometry `V : ℂⁿ → ℂ^E ⊗ ℂᵐ`, `Vᴴ V = I`, with
environment `E = Fin r` of the minimal dimension `r = rank J(Φ) ≤ nm`. -/
theorem QuantumChannel.exists_toLinearMap_eq_iff_exists_stinespringMatrix (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    (∃ Ψ : QuantumChannel n m, Ψ.toLinearMap = Φ) ↔
      ∃ V : Matrix (Fin (choiMatrix Φ).rank × m) n ℂ, Vᴴ * V = 1 ∧ ∀ A, Φ A = tr₁(V * A * Vᴴ) :=
  ⟨fun ⟨Ψ, hΨ⟩ => hΨ ▸ Ψ.exists_stinespringMatrix,
    fun ⟨V, hVV, hV⟩ => ⟨QuantumChannel.ofStinespring Φ V hVV hV, rfl⟩⟩

end Matrix
