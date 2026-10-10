/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Positive

/-!
# Stinespring's dilation theorem

Let `φ : A →CP (H →L[ℂ] H)` be a completely positive map from a (possibly non-unital)
C⋆-algebra `A` to the bounded operators on a complex Hilbert space `H`. This file constructs the
**Stinespring representation** `(π, V, K)` of `φ`: a Hilbert space `K = φ.Stinespring`, a
⋆-representation `π : A →⋆ₙₐ[ℂ] B(K)` and a bounded operator `V : H →L[ℂ] K` with
`φ a = V† π(a) V`. The representation is minimal (the vectors `π(a) V ξ` span a dense subspace of
`K`), hence non-degenerate, and `‖V‖² = ‖φ‖`; a minimal dilation is unique up to unitary
equivalence. For unital `A` the representation `π` is unital,
`V† V = φ 1`, and `V` is an isometry iff `φ 1 = 1`. Here `V` is called the Stinespring operator
(`CompletelyPositiveMap.stinespringOperator`).

## Construction

The construction follows Mathlib's GNS construction
(`Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal`) for positive functionals `f : A → ℂ`, which
corresponds to `H = ℂ` after identifying `B(ℂ)` with `ℂ`.

* `K` is the completion of the algebraic tensor product `A ⊗[ℂ] H` for the semi-inner product
  `⟪a ⊗ ξ, b ⊗ η⟫ = ⟪ξ, φ (a⋆ b) η⟫`. For `z = ∑ᵢ aᵢ ⊗ ξᵢ`,
  `⟪z, z⟫ = ∑ᵢⱼ ⟪ξᵢ, φ (aᵢ⋆ aⱼ) ξⱼ⟫` is nonnegative because the Gram matrix `[aᵢ⋆ aⱼ]` is
  nonnegative and `φ` is completely positive. The completion identifies null vectors with `0`.
* `π(a) [b ⊗ ξ] = [a b ⊗ ξ]`. It is bounded by `‖a‖` since `[(a bᵢ)⋆ (a bⱼ)] ≤ ‖a‖² [bᵢ⋆ bⱼ]`.
* `V = T†`, where `T : K →L[ℂ] H` extends `[a ⊗ ξ] ↦ φ a ξ`. No unit of `A` is needed to bound
  `T`: along an approximate unit `e → 1` of `A`, `⟪[e ⊗ η], z⟫ → ⟪η, T z⟫` and
  `‖[e ⊗ η]‖ ≤ √‖φ‖ ‖η‖`, so `‖T‖ ≤ √‖φ‖`. Then `π(a) V ξ = [a ⊗ ξ]`, and applying `T` gives
  `φ a ξ = V† π(a) V ξ`.

Here `‖φ‖` is the operator norm of the continuous linear map underlying
`PositiveContinuousLinearMap.ofClass φ` (written `‖φ‖ₒₚ` in this file); positive maps between
C⋆-algebras are automatically bounded.

## Main definitions

* `CompletelyPositiveMap.Stinespring` — the Stinespring Hilbert space `K`.
* `CompletelyPositiveMap.stinespringMk` — the canonical map `A ⊗[ℂ] H →ₗ[ℂ] K`, `z ↦ [z]`.
* `CompletelyPositiveMap.stinespringNonUnitalStarAlgHom` — the representation `π`
  (`CompletelyPositiveMap.stinespringStarAlgHom` in the unital case).
* `CompletelyPositiveMap.stinespringOperator` — the operator `V : H →L[ℂ] K`.
* `CStarMatrix.toPiLpStarAlgEquiv` — the ⋆-isomorphism `M_n(B(H)) ≃ B(Hⁿ)` between operator
  matrices and operators on the Hilbert sum `Hⁿ`.

## Main statements

* `CStarMatrix.nonneg_iff_sum_inner_apply_nonneg` — an operator matrix `N` on `Hⁿ` is nonnegative
  iff `0 ≤ ∑ᵢⱼ ⟪ξᵢ, Nᵢⱼ ξⱼ⟫` for every `ξ`; this is how complete positivity of a map into `B(H)`
  is tested against vectors.
* `CompletelyPositiveMap.apply_eq_adjoint_comp_stinespringNonUnitalStarAlgHom_comp` —
  **Stinespring's theorem** `φ a = V† π(a) V`.
* `CompletelyPositiveMap.stinespringNonUnitalStarAlgHom_apply_stinespringOperator` —
  `π(a) V ξ = [a ⊗ ξ]`.
* `CompletelyPositiveMap.topologicalClosure_span_stinespringNonUnitalStarAlgHom_apply_stinespringOperator_eq_top`
  — minimality: the `π(a) V ξ` span a dense subspace of `K`.
* `CompletelyPositiveMap.topologicalClosure_span_stinespringNonUnitalStarAlgHom_apply_eq_top` —
  `π` is non-degenerate.
* `CompletelyPositiveMap.norm_stinespringOperator_sq` — `‖V‖² = ‖φ‖`.
* `CompletelyPositiveMap.exists_stinespring_dilation` — the theorem as an existence statement.
* `CompletelyPositiveMap.exists_linearIsometryEquiv_stinespring`,
  `CompletelyPositiveMap.exists_linearIsometryEquiv_of_stinespring_dilation` — **uniqueness**: a
  minimal dilation is unique up to a unitary intertwining the representations and the operators.
* Unital case: `CompletelyPositiveMap.stinespringNonUnitalStarAlgHom_one` (`π(1) = 1`),
  `CompletelyPositiveMap.stinespringOperator_apply` (`V ξ = [1 ⊗ ξ]`),
  `CompletelyPositiveMap.adjoint_stinespringOperator_comp_self` (`V† V = φ 1`),
  `CompletelyPositiveMap.isometry_stinespringOperator_iff` (`V` is an isometry iff `φ 1 = 1`),
  `CompletelyPositiveMap.norm_stinespringOperator_sq_eq_norm_map_one` (`‖V‖² = ‖φ 1‖`) and
  `CompletelyPositiveMap.exists_unital_stinespring_dilation`. Together with
  `CompletelyPositiveMap.norm_stinespringOperator_sq`, the identity `‖V‖² = ‖φ 1‖` gives
  `‖φ‖ = ‖φ 1‖`, which holds more generally for every positive map on a unital C⋆-algebra
  (Russo–Dye 1966; Paulsen, Corollary 2.9). That general statement is not restated here: it is
  proved in the module `QuantumSystem.Analysis.CStarAlgebra.PositiveMap`, which lies outside
  `ForMathlib/` because it combines several `ForMathlib` files, while a `ForMathlib` file imports
  Mathlib only.

## References

* W. F. Stinespring, *Positive functions on C⋆-algebras*, Proc. Amer. Math. Soc. 6 (1955),
  211–216 (the unital case).
* G. G. Kasparov, *Hilbert C⋆-modules: theorems of Stinespring and Voiculescu*,
  J. Operator Theory 4 (1980), 133–150.
* E. C. Lance, *Hilbert C⋆-Modules*, London Math. Soc. Lecture Note Ser. 210 (1995), Ch. 5
  (the KSGNS construction; its case of a Hilbert space `E = H` is the non-unital theorem above).
* V. Paulsen, *Completely Bounded Maps and Operator Algebras*, Cambridge Stud. Adv. Math. 78
  (2002), Ch. 4 (uniqueness of the minimal dilation) and Corollary 2.9.
* B. Russo, H. A. Dye, *A note on unitary operators in C⋆-algebras*, Duke Math. J. 33 (1966),
  413–416.
-/

@[expose] public section

open scoped CStarAlgebra InnerProductSpace ComplexOrder TensorProduct InnerProduct

namespace CStarMatrix

variable {n A : Type*} [Fintype n]

/-- Scalars acting on `A` compatibly with its multiplication act so on `CStarMatrix n n A`, as on
`Matrix n n A`. -/
instance instIsScalarTowerMul {R : Type*} [Monoid R] [NonUnitalNonAssocSemiring A]
    [DistribMulAction R A] [IsScalarTower R A A] :
    IsScalarTower R (CStarMatrix n n A) (CStarMatrix n n A) :=
  inferInstanceAs (IsScalarTower R (Matrix n n A) (Matrix n n A))

/-- Scalars commuting with the multiplication of `A` commute with that of `CStarMatrix n n A`, as
for `Matrix n n A`. -/
instance instSMulCommClassMul {R : Type*} [Monoid R] [NonUnitalNonAssocSemiring A]
    [DistribMulAction R A] [SMulCommClass R A A] :
    SMulCommClass R (CStarMatrix n n A) (CStarMatrix n n A) :=
  inferInstanceAs (SMulCommClass R (Matrix n n A) (Matrix n n A))

variable [NonUnitalCStarAlgebra A]

section DecidableEq

variable [DecidableEq n]

/-- For the matrix `X = updateRow 0 i₀ b`, with the single nonzero row `b`, `X⋆ X` is the Gram
matrix `[bᵢ⋆ bⱼ]`. -/
lemma star_mul_self_ofMatrix_updateRow_zero (i₀ : n) (b : n → A) :
    star (ofMatrix (Matrix.updateRow 0 i₀ b)) * ofMatrix (Matrix.updateRow 0 i₀ b) =
      ofMatrix (Matrix.of fun i j => star (b i) * b j) := by
  ext i j
  simp [mul_apply, star_apply, ofMatrix_apply, Matrix.updateRow_apply]

/-- The diagonal embedding `a ↦ diag(a, …, a)` as a non-unital ⋆-homomorphism. -/
def diagonalNonUnitalStarAlgHom : A →⋆ₙₐ[ℂ] CStarMatrix n n A where
  toFun a := ofMatrix (Matrix.diagonal fun _ => a)
  map_smul' c a := by ext i j; by_cases h : i = j <;> simp [h]
  map_zero' := by ext i j; by_cases h : i = j <;> simp [h]
  map_add' a b := by ext i j; by_cases h : i = j <;> simp [h]
  map_mul' a b := by ext i j; by_cases h : i = j <;> simp [Matrix.diagonal_apply, h, mul_apply]
  map_star' a := by ext i j; by_cases h : i = j <;> simp [h, star_apply, eq_comm]

/-- `diag(a, …, a) · updateRow 0 i₀ b = updateRow 0 i₀ (a b)`. -/
lemma diagonalNonUnitalStarAlgHom_mul_ofMatrix_updateRow_zero (a : A) (i₀ : n) (b : n → A) :
    diagonalNonUnitalStarAlgHom a * ofMatrix (Matrix.updateRow 0 i₀ b) =
      ofMatrix (Matrix.updateRow 0 i₀ fun j => a * b j) := by
  ext i j
  simp [diagonalNonUnitalStarAlgHom, mul_apply, Matrix.diagonal_apply, ofMatrix_apply,
    Matrix.updateRow_apply]

end DecidableEq

variable [PartialOrder A] [StarOrderedRing A]

/-- The Gram matrix `[bᵢ⋆ bⱼ]` of a finite family in a C⋆-algebra `A` is nonnegative. (This is the
Gram matrix of `A` as a right Hilbert `A`-module, `⟪x, y⟫ = x⋆ y`; Mathlib's instance
`CStarModule A A` of `A` as a C⋆-module over itself uses the convention `⟪x, y⟫ = y x⋆` instead,
`WithCStarModule.inner_def`.) -/
lemma gram_nonneg (b : n → A) :
    0 ≤ (ofMatrix (Matrix.of fun i j => star (b i) * b j) : CStarMatrix n n A) := by
  classical
  cases isEmpty_or_nonempty n with
  | inl _ => exact (ext fun i _ => isEmptyElim i).le
  | inr h =>
    rw [← star_mul_self_ofMatrix_updateRow_zero h.some]
    exact star_mul_self_nonneg _

/-- Left multiplication by `a` is bounded on Gram matrices: `[(a bᵢ)⋆ (a bⱼ)] ≤ ‖a‖² [bᵢ⋆ bⱼ]`.
With `X = updateRow 0 i₀ b` and `D = diag(a, …, a)`, the left side is `X⋆ (D⋆ D) X ≤ ‖D‖² X⋆ X`,
and `‖D‖ ≤ ‖a‖` since `diag` is a ⋆-homomorphism. -/
lemma gram_mul_left_le (a : A) (b : n → A) :
    (ofMatrix (Matrix.of fun i j => star (a * b i) * (a * b j)) : CStarMatrix n n A) ≤
      ‖a‖ ^ 2 • ofMatrix (Matrix.of fun i j => star (b i) * b j) := by
  classical
  cases isEmpty_or_nonempty n with
  | inl _ => exact (ext fun i _ => isEmptyElim i).le
  | inr h =>
    set D := diagonalNonUnitalStarAlgHom (n := n) a
    set X := ofMatrix (Matrix.updateRow 0 h.some b)
    have hD : ‖D‖ ≤ ‖a‖ := NonUnitalStarAlgHom.norm_apply_le _ a
    rw [← star_mul_self_ofMatrix_updateRow_zero h.some, ← star_mul_self_ofMatrix_updateRow_zero h.some,
      ← diagonalNonUnitalStarAlgHom_mul_ofMatrix_updateRow_zero]
    calc star (D * X) * (D * X) = star X * (star D * D) * X := by simp only [star_mul, mul_assoc]
      _ ≤ ‖star D * D‖ • (star X * X) :=
        CStarAlgebra.star_left_conjugate_le_norm_smul _ _ (.star_mul_self D)
      _ = ‖D‖ ^ 2 • (star X * X) := by rw [CStarRing.norm_star_mul_self, sq]
      _ ≤ ‖a‖ ^ 2 • (star X * X) := by
        rw [← sub_nonneg, ← sub_smul]
        exact smul_nonneg (sub_nonneg.mpr (by gcongr)) (star_mul_self_nonneg X)

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] in
/-- A nonnegative operator matrix `N` on `Hⁿ` has a nonnegative quadratic form,
`0 ≤ ∑ᵢⱼ ⟪ξᵢ, Nᵢⱼ ξⱼ⟫`. -/
lemma sum_inner_apply_nonneg {N : CStarMatrix n n (H →L[ℂ] H)} (hN : 0 ≤ N) (ξ : n → H) :
    0 ≤ ∑ i, ∑ j, ⟪ξ i, N i j (ξ j)⟫_ℂ := by
  obtain ⟨P, hP, rfl⟩ := (StarOrderedRing.le_iff 0 N).mp hN
  clear hN
  rw [zero_add]
  induction hP using AddSubmonoid.closure_induction with
  | mem _ h =>
    obtain ⟨Y, rfl⟩ := h
    have : ∑ i, ∑ j, ⟪ξ i, (star Y * Y) i j (ξ j)⟫_ℂ =
        ∑ l, ⟪∑ i, Y l i (ξ i), ∑ j, Y l j (ξ j)⟫_ℂ := by
      simp only [mul_apply, star_apply, FunLike.coe_sum, Finset.sum_apply, _root_.mul_apply_eq_comp,
        ContinuousLinearMap.star_eq_adjoint, inner_sum, sum_inner,
        ContinuousLinearMap.adjoint_inner_right]
      exact (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans
        (Finset.sum_comm.trans (Finset.sum_congr rfl fun l _ => Finset.sum_comm))
    rw [this]
    exact Finset.sum_nonneg fun l _ => CStarModule.inner_self_nonneg
  | zero => simp [zero_apply]
  | add P Q _ _ hP hQ =>
    simpa [add_apply, inner_add_right, Finset.sum_add_distrib] using add_nonneg hP hQ

omit [CompleteSpace H] in
/-- The operator `ξ ↦ (Σⱼ Nᵢⱼ ξⱼ)ᵢ` of an operator matrix `N` on the Hilbert sum
`Hⁿ = PiLp 2 (fun _ ↦ H)`, the underlying map of `CStarMatrix.toPiLpStarAlgEquiv`. -/
noncomputable def toPiLpCLM (N : CStarMatrix n n (H →L[ℂ] H)) :
    PiLp 2 (fun _ : n => H) →L[ℂ] PiLp 2 (fun _ : n => H) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : n => H)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun i => ∑ j, N i j ∘L ContinuousLinearMap.proj j) ∘L
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : n => H)).toContinuousLinearMap

omit [CompleteSpace H] in
/-- `toPiLpCLM N` acts on `ξ ∈ Hⁿ` as `(N ξ)ᵢ = Σⱼ Nᵢⱼ ξⱼ`. -/
@[simp] lemma toPiLpCLM_apply (N : CStarMatrix n n (H →L[ℂ] H)) (ξ : PiLp 2 (fun _ : n => H))
    (i : n) : (toPiLpCLM N ξ).ofLp i = ∑ j, N i j (ξ.ofLp j) := by
  simp [toPiLpCLM]

variable [DecidableEq n]

/-- Operator matrices are the operators on the Hilbert sum `Hⁿ = PiLp 2 (fun _ ↦ H)`: the
⋆-isomorphism `M_n(B(H)) ≃ B(Hⁿ)` sends `N` to `ξ ↦ (Σⱼ Nᵢⱼ ξⱼ)ᵢ`
(`CStarMatrix.toPiLpStarAlgEquiv_apply`), and its inverse sends `T` to its blocks
`Tᵢⱼ = projᵢ ∘ T ∘ injⱼ`. -/
noncomputable def toPiLpStarAlgEquiv :
    CStarMatrix n n (H →L[ℂ] H) ≃⋆ₐ[ℂ] (PiLp 2 (fun _ : n => H) →L[ℂ] PiLp 2 (fun _ : n => H)) where
  toFun := toPiLpCLM
  invFun T := ofMatrix (Matrix.of fun i j => PiLp.proj 2 (fun _ : n => H) i ∘L T ∘L
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : n => H)).symm.toContinuousLinearMap ∘L
      ContinuousLinearMap.single ℂ (fun _ : n => H) j)
  left_inv N := by
    ext i j x
    simp [ofMatrix_apply, toPiLpCLM_apply, apply_ite]
  right_inv T := by
    ext x i
    have hx : x = ∑ j, WithLp.toLp 2 (Pi.single j (x.ofLp j) : n → H) := by
      ext k
      simp [Pi.single_apply]
    conv_rhs => rw [hx]
    simp [ofMatrix_apply, toPiLpCLM_apply]
  map_mul' N M := by
    ext x i
    simp only [toPiLpCLM_apply, mul_apply, _root_.mul_apply_eq_comp, FunLike.coe_sum,
      Finset.sum_apply, map_sum]
    exact Finset.sum_comm
  map_add' N M := by
    ext x i
    simp [toPiLpCLM_apply, add_apply, Finset.sum_add_distrib]
  map_star' N := by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    simp only [PiLp.inner_apply, toPiLpCLM_apply, star_apply, ContinuousLinearMap.star_eq_adjoint,
      sum_inner, inner_sum, ContinuousLinearMap.adjoint_inner_left]
    exact Finset.sum_comm
  map_smul' c N := by
    ext x i
    simp [toPiLpCLM_apply, smul_apply, Finset.smul_sum]

/-- `toPiLpStarAlgEquiv N` acts on `ξ ∈ Hⁿ` as `(N ξ)ᵢ = Σⱼ Nᵢⱼ ξⱼ`. -/
@[simp] lemma toPiLpStarAlgEquiv_apply (N : CStarMatrix n n (H →L[ℂ] H))
    (ξ : PiLp 2 (fun _ : n => H)) (i : n) :
    (toPiLpStarAlgEquiv (n := n) (H := H) N ξ).ofLp i = ∑ j, N i j (ξ.ofLp j) :=
  toPiLpCLM_apply N ξ i

omit [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [DecidableEq n] in
/-- An operator matrix `N` on `Hⁿ` is nonnegative iff its quadratic form is nonnegative,
`0 ≤ ∑ᵢⱼ ⟪ξᵢ, Nᵢⱼ ξⱼ⟫` for every `ξ ∈ Hⁿ`. The forward direction is
`CStarMatrix.sum_inner_apply_nonneg`; conversely `N` is nonnegative as the operator
`toPiLpStarAlgEquiv N` on the Hilbert sum `Hⁿ`, whose quadratic form this is. -/
lemma nonneg_iff_sum_inner_apply_nonneg {N : CStarMatrix n n (H →L[ℂ] H)} :
    0 ≤ N ↔ ∀ ξ : n → H, 0 ≤ ∑ i, ∑ j, ⟪ξ i, N i j (ξ j)⟫_ℂ := by
  classical
  refine ⟨sum_inner_apply_nonneg, fun h => ?_⟩
  rw [← map_le_map_iff (toPiLpStarAlgEquiv (n := n) (H := H)), map_zero,
    ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff_complex]
  intro x
  have hx : ⟪toPiLpStarAlgEquiv (n := n) (H := H) N x, x⟫_ℂ =
      starRingEnd ℂ (∑ i, ∑ j, ⟪x.ofLp i, N i j (x.ofLp j)⟫_ℂ) := by
    rw [← inner_conj_symm, PiLp.inner_apply]
    simp [inner_sum]
  obtain ⟨h₁, h₂⟩ := Complex.nonneg_iff.mp (h x.ofLp)
  rw [hx]
  generalize ∑ i, ∑ j, ⟪x.ofLp i, N i j (x.ofLp j)⟫_ℂ = z at h₁ h₂ ⊢
  exact ⟨Complex.ext (by simp) (by simp [← h₂]), by simpa using h₁⟩

omit [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [DecidableEq n] in
/-- The block matrix `(|ξᵢ⟩⟨ξⱼ|)ᵢⱼ` of rank-one operators is nonnegative: it is the rank-one
operator `|ξ⟩⟨ξ|` on `Hⁿ`, with quadratic form `|Σⱼ ⟪ξⱼ, ηⱼ⟫|²`. -/
lemma rankOne_nonneg (ξ : n → H) :
    0 ≤ (ofMatrix (Matrix.of fun i j => InnerProductSpace.rankOne ℂ (ξ i) (ξ j)) :
      CStarMatrix n n (H →L[ℂ] H)) := by
  classical
  rw [nonneg_iff_sum_inner_apply_nonneg]
  intro η
  have h : ∑ i, ∑ j, ⟪η i, (ofMatrix (Matrix.of fun i j =>
      InnerProductSpace.rankOne ℂ (ξ i) (ξ j)) : CStarMatrix n n (H →L[ℂ] H)) i j (η j)⟫_ℂ =
      (∑ j, ⟪ξ j, η j⟫_ℂ) * starRingEnd ℂ (∑ j, ⟪ξ j, η j⟫_ℂ) := by
    simp [ofMatrix_apply, Finset.mul_sum, map_sum, mul_comm]
  rw [h, Complex.mul_conj]
  exact_mod_cast Complex.normSq_nonneg _

end Hilbert

end CStarMatrix

namespace CompletelyPositiveMap

/- The operator norm `‖φ‖ₒₚ` of `φ`, taken through `PositiveContinuousLinearMap.ofClass φ` (positive
linear maps between C⋆-algebras are automatically bounded), the spelling of Mathlib's norm lemmas
for positive maps. The notation only abbreviates that Mathlib term, which is what the scoped `‖f‖ₒₚ`
of `QuantumSystem.ForMathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal` (the definition
`PositiveLinearMap.opNorm`) unfolds to; it is spelled out here (`local`) because `ForMathlib` files
import Mathlib only. -/
local notation "‖" φ "‖ₒₚ" =>
  ‖PositiveContinuousLinearMap.toContinuousLinearMap (PositiveContinuousLinearMap.ofClass φ)‖

universe u v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open UniformSpace.Completion

section NonUnital

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (φ : A →CP (H →L[ℂ] H))

/-! ### The quadratic form of `φ` on a block matrix -/

section QuadraticForm

variable {n : Type*} [Fintype n]

/-- Complete positivity, tested against vectors: for `0 ≤ M` in `M_n(A)`,
`0 ≤ ∑ᵢⱼ ⟪ξᵢ, φ(Mᵢⱼ) ξⱼ⟫`. -/
lemma sum_inner_map_nonneg {M : CStarMatrix n n A} (hM : 0 ≤ M) (ξ : n → H) :
    0 ≤ ∑ i, ∑ j, ⟪ξ i, φ (M i j) (ξ j)⟫_ℂ :=
  CStarMatrix.sum_inner_apply_nonneg (φ.map_cstarMatrix_nonneg M hM) ξ

/-- Complete positivity, tested against vectors: `M ≤ N` in `M_n(A)` gives
`∑ᵢⱼ ⟪ξᵢ, φ(Mᵢⱼ) ξⱼ⟫ ≤ ∑ᵢⱼ ⟪ξᵢ, φ(Nᵢⱼ) ξⱼ⟫`. -/
lemma sum_inner_map_le {M N : CStarMatrix n n A} (hMN : M ≤ N) (ξ : n → H) :
    ∑ i, ∑ j, ⟪ξ i, φ (M i j) (ξ j)⟫_ℂ ≤ ∑ i, ∑ j, ⟪ξ i, φ (N i j) (ξ j)⟫_ℂ := by
  have := φ.sum_inner_map_nonneg (sub_nonneg.mpr hMN) ξ
  simpa [CStarMatrix.sub_apply, map_sub, inner_sub_right, Finset.sum_sub_distrib] using this

end QuadraticForm

/-! ### The pre-Stinespring space -/

/-- The sesquilinear form `⟪a ⊗ ξ, b ⊗ η⟫ = ⟪ξ, φ (a⋆ b) η⟫` on `A ⊗[ℂ] H`, conjugate linear in
the first argument. It is positive semidefinite by complete positivity
(`stinespringForm_self_nonneg`). -/
noncomputable def stinespringForm : A ⊗[ℂ] H →ₗ⋆[ℂ] A ⊗[ℂ] H →ₗ[ℂ] ℂ :=
  TensorProduct.lift <| LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (starRingEnd ℂ)
    (fun a ξ => TensorProduct.lift <| LinearMap.mk₂ ℂ (fun b η => ⟪ξ, φ (star a * b) η⟫_ℂ)
      (fun b₁ b₂ η => by simp [mul_add])
      (fun c b η => by simp [mul_smul_comm])
      (fun b η₁ η₂ => by simp)
      (fun c b η => by simp))
    (fun a₁ a₂ ξ => TensorProduct.ext' fun b η => by simp [add_mul])
    (fun c a ξ => TensorProduct.ext' fun b η => by simp [smul_mul_assoc])
    (fun a ξ₁ ξ₂ => TensorProduct.ext' fun b η => by simp)
    (fun c a ξ => TensorProduct.ext' fun b η => by simp [mul_comm])

/-- `⟪a ⊗ ξ, b ⊗ η⟫ = ⟪ξ, φ (a⋆ b) η⟫`. -/
@[simp] lemma stinespringForm_tmul (a b : A) (ξ η : H) :
    φ.stinespringForm (a ⊗ₜ ξ) (b ⊗ₜ η) = ⟪ξ, φ (star a * b) η⟫_ℂ := rfl

/-- `⟪∑ᵢ aᵢ ⊗ ξᵢ, ∑ⱼ bⱼ ⊗ ηⱼ⟫ = ∑ᵢⱼ ⟪ξᵢ, φ (aᵢ⋆ bⱼ) ηⱼ⟫`. -/
lemma stinespringForm_sum_tmul {ι κ : Type*} [Fintype ι] [Fintype κ] (a : ι → A) (ξ : ι → H)
    (b : κ → A) (η : κ → H) :
    φ.stinespringForm (∑ i, a i ⊗ₜ ξ i) (∑ j, b j ⊗ₜ η j) =
      ∑ i, ∑ j, ⟪ξ i, φ (star (a i) * b j) (η j)⟫_ℂ := by
  simp only [map_sum, LinearMap.sum_apply, stinespringForm_tmul]
  exact Finset.sum_comm

/-- The form is Hermitian: `conj ⟪w, z⟫ = ⟪z, w⟫`. -/
lemma conj_stinespringForm (z w : A ⊗[ℂ] H) :
    starRingEnd ℂ (φ.stinespringForm w z) = φ.stinespringForm z w := by
  induction z with
  | add z₁ z₂ h₁ h₂ => simp [h₁, h₂]
  | tmul a ξ =>
    induction w with
    | add w₁ w₂ h₁ h₂ => simp [h₁, h₂]
    | tmul b η =>
      rw [stinespringForm_tmul, stinespringForm_tmul, inner_conj_symm,
        ← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
        ← map_star, star_mul, star_star]

/-- The form is positive semidefinite: `0 ≤ ⟪z, z⟫`. For `z = ∑ᵢ aᵢ ⊗ ξᵢ` this is
`0 ≤ ∑ᵢⱼ ⟪ξᵢ, φ (aᵢ⋆ aⱼ) ξⱼ⟫`, complete positivity applied to the Gram matrix `[aᵢ⋆ aⱼ]`. -/
lemma stinespringForm_self_nonneg (z : A ⊗[ℂ] H) : 0 ≤ φ.stinespringForm z z := by
  obtain ⟨k, a, ξ, rfl⟩ := TensorProduct.exists_sum_tmul_eq z
  rw [stinespringForm_sum_tmul]
  simpa using φ.sum_inner_map_nonneg (CStarMatrix.gram_nonneg a) ξ

/-- The pre-Stinespring space of `φ`: the algebraic tensor product `A ⊗[ℂ] H` with the
semi-inner product `stinespringForm`. This is a type synonym of `A ⊗[ℂ] H`; its Hilbert space
completion is `CompletelyPositiveMap.Stinespring`. -/
def PreStinespring (_φ : A →CP (H →L[ℂ] H)) : Type (max u v) := A ⊗[ℂ] H

/-- The additive group structure of `A ⊗[ℂ] H`. -/
instance : AddCommGroup φ.PreStinespring := inferInstanceAs (AddCommGroup (A ⊗[ℂ] H))

/-- The `ℂ`-module structure of `A ⊗[ℂ] H`. -/
instance : Module ℂ φ.PreStinespring := inferInstanceAs (Module ℂ (A ⊗[ℂ] H))

/-- The identification of `A ⊗[ℂ] H` with the pre-Stinespring space. -/
def toPreStinespring : A ⊗[ℂ] H ≃ₗ[ℂ] φ.PreStinespring := LinearEquiv.refl ℂ _

/-- The identification of the pre-Stinespring space with `A ⊗[ℂ] H`. -/
def ofPreStinespring : φ.PreStinespring ≃ₗ[ℂ] A ⊗[ℂ] H := φ.toPreStinespring.symm

/-- `toPreStinespring` inverts `ofPreStinespring`. -/
@[simp]
lemma toPreStinespring_ofPreStinespring (z : φ.PreStinespring) :
    φ.toPreStinespring (φ.ofPreStinespring z) = z := rfl

/-- `ofPreStinespring` inverts `toPreStinespring`. -/
@[simp]
lemma ofPreStinespring_toPreStinespring (z : A ⊗[ℂ] H) :
    φ.ofPreStinespring (φ.toPreStinespring z) = z := rfl

/-- The pre-Stinespring space of finite-dimensional `A` and `H` is finite-dimensional. -/
instance [FiniteDimensional ℂ A] [FiniteDimensional ℂ H] : FiniteDimensional ℂ φ.PreStinespring :=
  inferInstanceAs (Module.Finite ℂ (A ⊗[ℂ] H))

/-- The semi-inner product `⟪z, w⟫ = stinespringForm z w` on the pre-Stinespring space. -/
noncomputable abbrev preStinespringCore : PreInnerProductSpace.Core ℂ φ.PreStinespring where
  inner z w := φ.stinespringForm (φ.ofPreStinespring z) (φ.ofPreStinespring w)
  conj_inner_symm z w := φ.conj_stinespringForm _ _
  re_inner_nonneg z := (RCLike.nonneg_iff.mp (φ.stinespringForm_self_nonneg _)).1
  add_left z z' w := by simp
  smul_left z w c := by simp

/-- The seminorm `‖z‖ = √⟪z, z⟫` of the semi-inner product `stinespringForm`. -/
noncomputable instance : SeminormedAddCommGroup φ.PreStinespring :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := φ.preStinespringCore)

/-- The pre-Stinespring space is a pre-inner product space with the semi-inner product
`stinespringForm`. -/
noncomputable instance : InnerProductSpace ℂ φ.PreStinespring :=
  InnerProductSpace.ofCore φ.preStinespringCore

/-- The inner product of the pre-Stinespring space is `stinespringForm`. -/
lemma preStinespring_inner_def (z w : φ.PreStinespring) :
    ⟪z, w⟫_ℂ = φ.stinespringForm (φ.ofPreStinespring z) (φ.ofPreStinespring w) := rfl

/-- `⟪[z], [w]⟫ = stinespringForm z w`. -/
lemma inner_toPreStinespring (z w : A ⊗[ℂ] H) :
    ⟪φ.toPreStinespring z, φ.toPreStinespring w⟫_ℂ = φ.stinespringForm z w := rfl

/-! ### Left multiplication -/

/-- Left multiplication by `a` is bounded on the pre-Stinespring space:
`‖[(a ⊗ 1) z]‖ ≤ ‖a‖ ‖[z]‖`. For `z = ∑ⱼ bⱼ ⊗ ξⱼ` this is complete positivity applied to
`[(a bᵢ)⋆ (a bⱼ)] ≤ ‖a‖² [bᵢ⋆ bⱼ]` (`CStarMatrix.gram_mul_left_le`). -/
lemma norm_toPreStinespring_rTensor_mul_le (a : A) (z : A ⊗[ℂ] H) :
    ‖φ.toPreStinespring ((LinearMap.mul ℂ A a).rTensor H z)‖ ≤ ‖a‖ * ‖φ.toPreStinespring z‖ := by
  obtain ⟨k, b, ξ, rfl⟩ := TensorProduct.exists_sum_tmul_eq z
  have h₁ := φ.sum_inner_map_le (CStarMatrix.gram_mul_left_le a b) ξ
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow,
    norm_sq_eq_re_inner (𝕜 := ℂ) (φ.toPreStinespring ((LinearMap.mul ℂ A a).rTensor H _)),
    norm_sq_eq_re_inner (𝕜 := ℂ) (φ.toPreStinespring _), inner_toPreStinespring,
    inner_toPreStinespring]
  have e : (LinearMap.mul ℂ A a).rTensor H (∑ j, b j ⊗ₜ ξ j) = ∑ j, (a * b j) ⊗ₜ ξ j := by
    simp [map_sum]
  rw [e, stinespringForm_sum_tmul, stinespringForm_sum_tmul]
  have hs (r : ℝ) (x : A) : φ (r • x) = r • φ x := LinearMapClass.map_smul_of_tower φ r x
  simp only [CStarMatrix.smul_apply, CStarMatrix.ofMatrix_apply, Matrix.of_apply, hs, smul_apply,
    CStarModule.inner_smul_right_real, Complex.real_smul, ← Finset.mul_sum] at h₁
  have h₂ := (Complex.le_def.mp h₁).1
  rwa [Complex.re_ofReal_mul] at h₂

/-- Left multiplication `[b ⊗ ξ] ↦ [a b ⊗ ξ]` on the pre-Stinespring space, a bounded operator of
norm at most `‖a‖` (`norm_toPreStinespring_rTensor_mul_le`). Its extension to the completion is the Stinespring
representation `CompletelyPositiveMap.stinespringNonUnitalStarAlgHom`. -/
noncomputable def leftMulMapPreStinespring (a : A) : φ.PreStinespring →L[ℂ] φ.PreStinespring :=
  (φ.toPreStinespring.toLinearMap ∘ₗ (LinearMap.mul ℂ A a).rTensor H ∘ₗ
    φ.ofPreStinespring.toLinearMap).mkContinuous ‖a‖ fun z =>
      φ.norm_toPreStinespring_rTensor_mul_le a (φ.ofPreStinespring z)

/-- `a · z` is `(a ⊗ 1) z`, left multiplication on the first tensor factor. -/
lemma leftMulMapPreStinespring_apply (a : A) (z : φ.PreStinespring) :
    φ.leftMulMapPreStinespring a z =
      φ.toPreStinespring ((LinearMap.mul ℂ A a).rTensor H (φ.ofPreStinespring z)) := rfl

/-- `a · [b ⊗ ξ] = [a b ⊗ ξ]`. -/
@[simp] lemma leftMulMapPreStinespring_tmul (a b : A) (ξ : H) :
    φ.leftMulMapPreStinespring a (φ.toPreStinespring (b ⊗ₜ ξ)) =
      φ.toPreStinespring ((a * b) ⊗ₜ ξ) := rfl

/-- Left multiplication by `a⋆` is the adjoint of left multiplication by `a`:
`⟪a⋆ · x, y⟫ = ⟪x, a · y⟫`. -/
lemma inner_leftMulMapPreStinespring_star (a : A) (x y : φ.PreStinespring) :
    ⟪φ.leftMulMapPreStinespring (star a) x, y⟫_ℂ = ⟪x, φ.leftMulMapPreStinespring a y⟫_ℂ := by
  obtain ⟨x, rfl⟩ := φ.toPreStinespring.surjective x
  obtain ⟨y, rfl⟩ := φ.toPreStinespring.surjective y
  induction x with
  | add x₁ x₂ h₁ h₂ => simp only [map_add, inner_add_left, h₁, h₂]
  | tmul b ξ =>
    induction y with
    | add y₁ y₂ h₁ h₂ => simp only [map_add, inner_add_right, h₁, h₂]
    | tmul c η =>
      simp only [leftMulMapPreStinespring_tmul, inner_toPreStinespring, stinespringForm_tmul,
        star_mul, star_star, mul_assoc]

/-! ### The map `[a ⊗ ξ] ↦ φ a ξ` -/

/-- The linear map `[a ⊗ ξ] ↦ φ a ξ` from the pre-Stinespring space to `H`. It is bounded
(`norm_stinespringOperatorAdjointₗ_le`), and its extension to the completion is the adjoint of
`CompletelyPositiveMap.stinespringOperator`. -/
noncomputable def stinespringOperatorAdjointₗ : φ.PreStinespring →ₗ[ℂ] H :=
  TensorProduct.lift (ContinuousLinearMap.coeLM ℂ ∘ₗ φ.toLinearMap) ∘ₗ
    φ.ofPreStinespring.toLinearMap

/-- `[a ⊗ ξ] ↦ φ a ξ`. -/
@[simp] lemma stinespringOperatorAdjointₗ_tmul (a : A) (ξ : H) :
    φ.stinespringOperatorAdjointₗ (φ.toPreStinespring (a ⊗ₜ ξ)) = φ a ξ := rfl

/-- `⟪a ⊗ ξ, z⟫ = ⟪ξ, T₀ (a⋆ · z)⟫`, where `T₀ [b ⊗ η] = φ b η`. -/
lemma inner_toPreStinespring_tmul_left (a : A) (ξ : H) (z : φ.PreStinespring) :
    ⟪φ.toPreStinespring (a ⊗ₜ ξ), z⟫_ℂ =
      ⟪ξ, φ.stinespringOperatorAdjointₗ (φ.leftMulMapPreStinespring (star a) z)⟫_ℂ := by
  obtain ⟨z, rfl⟩ := φ.toPreStinespring.surjective z
  induction z with
  | add z₁ z₂ h₁ h₂ => simp only [map_add, inner_add_right, h₁, h₂]
  | tmul b η => rfl

/-- `⟪T₀ (a⋆ · z), ζ⟫ = ⟪z, a ⊗ ζ⟫`, where `T₀ [b ⊗ η] = φ b η`. -/
lemma inner_stinespringOperatorAdjointₗ_leftMulMapPreStinespring_star (a : A) (z : φ.PreStinespring)
    (ζ : H) :
    ⟪φ.stinespringOperatorAdjointₗ (φ.leftMulMapPreStinespring (star a) z), ζ⟫_ℂ =
      ⟪z, φ.toPreStinespring (a ⊗ₜ ζ)⟫_ℂ := by
  obtain ⟨z, rfl⟩ := φ.toPreStinespring.surjective z
  induction z with
  | add z₁ z₂ h₁ h₂ => simp only [map_add, inner_add_left, h₁, h₂]
  | tmul b ξ =>
    rw [leftMulMapPreStinespring_tmul, stinespringOperatorAdjointₗ_tmul, inner_toPreStinespring,
      stinespringForm_tmul, ← ContinuousLinearMap.adjoint_inner_right,
      ← ContinuousLinearMap.star_eq_adjoint, ← map_star, star_mul, star_star]

/-- `‖[a ⊗ ξ]‖ ≤ √‖φ‖ ‖a‖ ‖ξ‖`. -/
lemma norm_toPreStinespring_tmul_le (a : A) (ξ : H) :
    ‖φ.toPreStinespring (a ⊗ₜ ξ)‖ ≤ √‖φ‖ₒₚ * ‖a‖ * ‖ξ‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), norm_sq_eq_re_inner (𝕜 := ℂ),
    inner_toPreStinespring, stinespringForm_tmul, mul_pow, mul_pow,
    Real.sq_sqrt (norm_nonneg _)]
  calc RCLike.re ⟪ξ, φ (star a * a) ξ⟫_ℂ ≤ ‖⟪ξ, φ (star a * a) ξ⟫_ℂ‖ := RCLike.re_le_norm _
    _ ≤ ‖ξ‖ * ‖φ (star a * a) ξ‖ := norm_inner_le_norm _ _
    _ ≤ ‖ξ‖ * (‖φ (star a * a)‖ * ‖ξ‖) := by gcongr; exact (φ (star a * a)).le_opNorm ξ
    _ ≤ ‖ξ‖ * (‖φ‖ₒₚ * ‖star a * a‖ * ‖ξ‖) := by
      gcongr
      exact (PositiveContinuousLinearMap.ofClass φ : A →L[ℂ] (H →L[ℂ] H)).le_opNorm (star a * a)
    _ = ‖φ‖ₒₚ * ‖a‖ ^ 2 * ‖ξ‖ ^ 2 := by
      rw [CStarRing.norm_star_mul_self]; ring

open Filter Topology in
/-- Along the approximate unit `e → 1` of `A`, the vectors `[e ⊗ η]` recover `T₀`:
`⟪[e ⊗ η], z⟫ → ⟪η, T₀ z⟫`, where `T₀ [b ⊗ ξ] = φ b ξ`. -/
lemma tendsto_inner_toPreStinespring_tmul (η : H) (z : φ.PreStinespring) :
    Tendsto (fun e => ⟪φ.toPreStinespring (e ⊗ₜ η), z⟫_ℂ) (CStarAlgebra.approximateUnit A)
      (𝓝 ⟪η, φ.stinespringOperatorAdjointₗ z⟫_ℂ) := by
  have hl := CStarAlgebra.increasingApproximateUnit A
  have key (w : A ⊗[ℂ] H) :
      Tendsto (fun e => φ.stinespringOperatorAdjointₗ
          (φ.leftMulMapPreStinespring (star e) (φ.toPreStinespring w)))
        (CStarAlgebra.approximateUnit A) (𝓝 (φ.stinespringOperatorAdjointₗ (φ.toPreStinespring w))) := by
    induction w with
    | add w₁ w₂ h₁ h₂ => simpa only [map_add] using h₁.add h₂
    | tmul b ξ =>
      simp only [leftMulMapPreStinespring_tmul, stinespringOperatorAdjointₗ_tmul]
      have hb : Tendsto (fun e => star e * b) (CStarAlgebra.approximateUnit A) (𝓝 b) :=
        (hl.tendsto_mul_right b).congr' (hl.eventually_star_eq.mono fun e he => by simp [he])
      exact (((ContinuousLinearMap.apply ℂ H ξ).continuous.comp (map_continuous φ)).tendsto
        b).comp hb
  refine (tendsto_const_nhds.inner (key (φ.ofPreStinespring z))).congr fun e => ?_
  rw [inner_toPreStinespring_tmul_left, toPreStinespring_ofPreStinespring]

/-- `‖⟪η, T₀ z⟫‖ ≤ √‖φ‖ ‖η‖ ‖z‖`, where `T₀ [b ⊗ ξ] = φ b ξ`: test `T₀ z` against `[e ⊗ η]` along
the approximate unit, with `‖[e ⊗ η]‖ ≤ √‖φ‖ ‖η‖` for `‖e‖ ≤ 1`. -/
lemma norm_inner_stinespringOperatorAdjointₗ_le (η : H) (z : φ.PreStinespring) :
    ‖⟪η, φ.stinespringOperatorAdjointₗ z⟫_ℂ‖ ≤ √‖φ‖ₒₚ * ‖η‖ * ‖z‖ := by
  refine le_of_tendsto (φ.tendsto_inner_toPreStinespring_tmul η z).norm ?_
  filter_upwards [(CStarAlgebra.increasingApproximateUnit A).eventually_norm] with e he
  calc ‖⟪φ.toPreStinespring (e ⊗ₜ η), z⟫_ℂ‖ ≤ ‖φ.toPreStinespring (e ⊗ₜ η)‖ * ‖z‖ :=
        norm_inner_le_norm _ _
    _ ≤ √‖φ‖ₒₚ * ‖e‖ * ‖η‖ * ‖z‖ := by
      gcongr; exact φ.norm_toPreStinespring_tmul_le e η
    _ ≤ √‖φ‖ₒₚ * 1 * ‖η‖ * ‖z‖ := by gcongr
    _ = √‖φ‖ₒₚ * ‖η‖ * ‖z‖ := by ring

/-- `‖T₀ z‖ ≤ √‖φ‖ ‖z‖`, where `T₀ [b ⊗ ξ] = φ b ξ`. -/
lemma norm_stinespringOperatorAdjointₗ_le (z : φ.PreStinespring) :
    ‖φ.stinespringOperatorAdjointₗ z‖ ≤ √‖φ‖ₒₚ * ‖z‖ := by
  set x := φ.stinespringOperatorAdjointₗ z
  have h := φ.norm_inner_stinespringOperatorAdjointₗ_le x z
  rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm] at h
  rcases (norm_nonneg x).eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · refine le_of_mul_le_mul_left ?_ hpos
    nlinarith

/-- The bounded operator `[a ⊗ ξ] ↦ φ a ξ` from the pre-Stinespring space to `H`, of norm at most
`√‖φ‖`. -/
noncomputable def stinespringOperatorAdjoint₀ : φ.PreStinespring →L[ℂ] H :=
  φ.stinespringOperatorAdjointₗ.mkContinuous _ φ.norm_stinespringOperatorAdjointₗ_le

/-- `stinespringOperatorAdjoint₀` is `stinespringOperatorAdjointₗ` as a function. -/
lemma stinespringOperatorAdjoint₀_apply (z : φ.PreStinespring) :
    φ.stinespringOperatorAdjoint₀ z = φ.stinespringOperatorAdjointₗ z := rfl

/-! ### The Stinespring space and the Stinespring representation -/

/-- The Stinespring Hilbert space `K` of `φ`: the completion of the pre-Stinespring space. The
null vectors of the semi-inner product are identified with `0` by the completion. -/
abbrev Stinespring := UniformSpace.Completion φ.PreStinespring

/-- The canonical map `A ⊗[ℂ] H →ₗ[ℂ] φ.Stinespring`, `z ↦ [z]`. -/
noncomputable def stinespringMk : A ⊗[ℂ] H →ₗ[ℂ] φ.Stinespring :=
  (toComplₗᵢ : φ.PreStinespring →ₗᵢ[ℂ] φ.Stinespring).toLinearMap ∘ₗ
    φ.toPreStinespring.toLinearMap

/-- `[z]` is the image in the completion of the class of `z` in the pre-Stinespring space. -/
lemma stinespringMk_apply (z : A ⊗[ℂ] H) :
    φ.stinespringMk z = (φ.toPreStinespring z : φ.Stinespring) := rfl

/-- The classes `[z]` are dense in the Stinespring space. -/
lemma denseRange_stinespringMk : DenseRange φ.stinespringMk :=
  denseRange_coe.comp φ.toPreStinespring.surjective.denseRange (continuous_coe _)

/-- `⟪[z], [w]⟫ = stinespringForm z w`. -/
lemma inner_stinespringMk (z w : A ⊗[ℂ] H) :
    ⟪φ.stinespringMk z, φ.stinespringMk w⟫_ℂ = φ.stinespringForm z w := by
  rw [stinespringMk_apply, stinespringMk_apply, inner_coe, inner_toPreStinespring]

/-- `⟪[a ⊗ ξ], [b ⊗ η]⟫ = ⟪ξ, φ (a⋆ b) η⟫`. -/
@[simp] lemma inner_stinespringMk_tmul (a b : A) (ξ η : H) :
    ⟪φ.stinespringMk (a ⊗ₜ ξ), φ.stinespringMk (b ⊗ₜ η)⟫_ℂ = ⟪ξ, φ (star a * b) η⟫_ℂ := by
  rw [inner_stinespringMk, stinespringForm_tmul]

/-- `(c a) · z = c (a · z)`. -/
lemma leftMulMapPreStinespring_smul (c : ℂ) (a : A) :
    φ.leftMulMapPreStinespring (c • a) = c • φ.leftMulMapPreStinespring a := by
  ext z
  obtain ⟨z, rfl⟩ := φ.toPreStinespring.surjective z
  induction z with
  | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | tmul b ξ =>
    simp only [leftMulMapPreStinespring_tmul, FunLike.coe_smul, Pi.smul_apply,
      smul_mul_assoc, ← TensorProduct.smul_tmul', map_smul]

/-- `(a + a') · z = a · z + a' · z`. -/
lemma leftMulMapPreStinespring_add (a a' : A) :
    φ.leftMulMapPreStinespring (a + a') =
      φ.leftMulMapPreStinespring a + φ.leftMulMapPreStinespring a' := by
  ext z
  obtain ⟨z, rfl⟩ := φ.toPreStinespring.surjective z
  induction z with
  | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | tmul b ξ => simp [add_mul, TensorProduct.add_tmul]

/-- `(a a') · z = a · (a' · z)`. -/
lemma leftMulMapPreStinespring_mul (a a' : A) :
    φ.leftMulMapPreStinespring (a * a') =
      φ.leftMulMapPreStinespring a ∘L φ.leftMulMapPreStinespring a' := by
  ext z
  obtain ⟨z, rfl⟩ := φ.toPreStinespring.surjective z
  induction z with
  | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | tmul b ξ => simp [mul_assoc]

/-- The completion of `(c a) ·` is `c` times the completion of `a ·`. -/
lemma completion_leftMulMapPreStinespring_smul (c : ℂ) (a : A) :
    (φ.leftMulMapPreStinespring (c • a)).completion =
      c • (φ.leftMulMapPreStinespring a).completion := by
  ext x
  induction x using induction_on with
  | hp =>
    exact isClosed_eq (φ.leftMulMapPreStinespring (c • a)).completion.continuous
      (c • (φ.leftMulMapPreStinespring a).completion).continuous
  | ih z => simp [leftMulMapPreStinespring_smul, UniformSpace.Completion.coe_smul]

/-- The **Stinespring representation** `π : A →⋆ₙₐ[ℂ] B(K)` of a completely positive map
`φ : A → B(H)` on a (possibly non-unital) C⋆-algebra: left multiplication
`π(a) [b ⊗ ξ] = [a b ⊗ ξ]` on the Stinespring space `K = φ.Stinespring`. -/
noncomputable def stinespringNonUnitalStarAlgHom :
    A →⋆ₙₐ[ℂ] (φ.Stinespring →L[ℂ] φ.Stinespring) where
  toFun a := (φ.leftMulMapPreStinespring a).completion
  map_smul' c a := φ.completion_leftMulMapPreStinespring_smul c a
  map_zero' := by simpa using φ.completion_leftMulMapPreStinespring_smul 0 0
  map_add' a a' := by
    ext x
    induction x using induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih z => simp [leftMulMapPreStinespring_add, UniformSpace.Completion.coe_add]
  map_mul' a a' := by
    ext x
    induction x using induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih z => simp [leftMulMapPreStinespring_mul]
  map_star' a := by
    refine (ContinuousLinearMap.eq_adjoint_iff (φ.leftMulMapPreStinespring (star a)).completion
      (φ.leftMulMapPreStinespring a).completion).mpr fun x y => ?_
    induction x, y using induction_on₂ with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x y => simp [inner_leftMulMapPreStinespring_star]

/-- `π(a)` is the extension to the completion of left multiplication by `a`. -/
lemma stinespringNonUnitalStarAlgHom_apply (a : A) :
    φ.stinespringNonUnitalStarAlgHom a = (φ.leftMulMapPreStinespring a).completion := rfl

/-- On the pre-Stinespring space, `π(a)` is left multiplication by `a`. -/
@[simp]
lemma stinespringNonUnitalStarAlgHom_apply_coe (a : A) (z : φ.PreStinespring) :
    φ.stinespringNonUnitalStarAlgHom a z = φ.leftMulMapPreStinespring a z := by
  simp [stinespringNonUnitalStarAlgHom_apply]

/-- `π(a) [b ⊗ ξ] = [a b ⊗ ξ]`. -/
@[simp]
lemma stinespringNonUnitalStarAlgHom_apply_stinespringMk_tmul (a b : A) (ξ : H) :
    φ.stinespringNonUnitalStarAlgHom a (φ.stinespringMk (b ⊗ₜ ξ)) =
      φ.stinespringMk ((a * b) ⊗ₜ ξ) := by
  simp [stinespringMk_apply]

/-! ### The operator `V` -/

/-- The **Stinespring operator** of `φ`: the component `V : H →L[ℂ] K` of the Stinespring
representation `(π, V, K)` (in the literature simply a bounded operator), with
`φ a = V† π(a) V` (`apply_eq_adjoint_comp_stinespringNonUnitalStarAlgHom_comp`) and
`‖V‖² = ‖φ‖`. It is the adjoint of the extension to `K` of the bounded map `[a ⊗ ξ] ↦ φ a ξ`. In
the unital case `V ξ = [1 ⊗ ξ]` (`stinespringOperator_apply`), and `V` is an isometry iff
`φ 1 = 1` (`isometry_stinespringOperator_iff`). -/
noncomputable def stinespringOperator : H →L[ℂ] φ.Stinespring :=
  ContinuousLinearMap.adjoint
    (φ.stinespringOperatorAdjoint₀.extend (toComplL : φ.PreStinespring →L[ℂ] φ.Stinespring))

/-- `V† [z] = φ a ξ` on `z = a ⊗ ξ`, extended linearly. -/
lemma adjoint_stinespringOperator_coe (z : φ.PreStinespring) :
    (φ.stinespringOperator†) z = φ.stinespringOperatorAdjointₗ z := by
  rw [stinespringOperator, ContinuousLinearMap.adjoint_adjoint]
  exact ContinuousLinearMap.extend_eq _ denseRange_coe (isUniformInducing_coe _) z

/-- `V† [a ⊗ ξ] = φ a ξ`. -/
@[simp]
lemma adjoint_stinespringOperator_stinespringMk_tmul (a : A) (ξ : H) :
    (φ.stinespringOperator†) (φ.stinespringMk (a ⊗ₜ ξ)) = φ a ξ :=
  φ.adjoint_stinespringOperator_coe _

/-- `‖V†‖ ≤ √‖φ‖`. -/
lemma norm_adjoint_stinespringOperator_le :
    ‖φ.stinespringOperator†‖ ≤ √‖φ‖ₒₚ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  induction x using induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih z =>
    rw [adjoint_stinespringOperator_coe, norm_coe]
    exact φ.norm_stinespringOperatorAdjointₗ_le z

/-- The fundamental identity `π(a) V ξ = [a ⊗ ξ]`. -/
@[simp]
lemma stinespringNonUnitalStarAlgHom_apply_stinespringOperator (a : A) (ξ : H) :
    φ.stinespringNonUnitalStarAlgHom a (φ.stinespringOperator ξ) = φ.stinespringMk (a ⊗ₜ ξ) := by
  refine ext_inner_left ℂ fun x => ?_
  induction x using induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih w =>
    rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
      ← map_star, stinespringNonUnitalStarAlgHom_apply_coe,
      ← ContinuousLinearMap.adjoint_inner_left, adjoint_stinespringOperator_coe,
      stinespringMk_apply, inner_coe]
    exact φ.inner_stinespringOperatorAdjointₗ_leftMulMapPreStinespring_star a w ξ

/-- **Stinespring's theorem** for a completely positive map `φ : A → B(H)` on a (possibly
non-unital) C⋆-algebra: `φ a = V† π(a) V` for the Stinespring representation
`π = φ.stinespringNonUnitalStarAlgHom` and `V = φ.stinespringOperator`. -/
theorem apply_eq_adjoint_comp_stinespringNonUnitalStarAlgHom_comp (a : A) :
    φ a = φ.stinespringOperator† ∘L
      φ.stinespringNonUnitalStarAlgHom a ∘L φ.stinespringOperator := by
  ext ξ
  simp

/-- Minimality of the Stinespring representation: the vectors `π(a) V ξ` span a dense subspace
of `K`. -/
lemma topologicalClosure_span_stinespringNonUnitalStarAlgHom_apply_stinespringOperator_eq_top :
    (Submodule.span ℂ (Set.range fun p : A × H =>
      φ.stinespringNonUnitalStarAlgHom p.1 (φ.stinespringOperator p.2))).topologicalClosure = ⊤ := by
  have h : (Set.range fun p : A × H =>
      φ.stinespringNonUnitalStarAlgHom p.1 (φ.stinespringOperator p.2)) =
      φ.stinespringMk '' {t | ∃ a ξ, a ⊗ₜ[ℂ] ξ = t} := by
    ext x
    simp
  rw [h, Submodule.span_image, TensorProduct.span_tmul_eq_top, Submodule.map_top,
    ← Submodule.dense_iff_topologicalClosure_eq_top, LinearMap.coe_range]
  exact φ.denseRange_stinespringMk

/-- The Stinespring representation is non-degenerate: the vectors `π(a) x` span a dense subspace
of `K`. -/
lemma topologicalClosure_span_stinespringNonUnitalStarAlgHom_apply_eq_top :
    (Submodule.span ℂ (Set.range fun p : A × φ.Stinespring =>
      φ.stinespringNonUnitalStarAlgHom p.1 p.2)).topologicalClosure = ⊤ :=
  top_unique <|
    (φ.topologicalClosure_span_stinespringNonUnitalStarAlgHom_apply_stinespringOperator_eq_top).ge.trans <|
      Submodule.topologicalClosure_mono <| Submodule.span_mono <|
        Set.range_subset_iff.mpr fun p => ⟨(p.1, φ.stinespringOperator p.2), rfl⟩

/-- `‖V‖² = ‖φ‖`. -/
lemma norm_stinespringOperator_sq :
    ‖φ.stinespringOperator‖ ^ 2 = ‖φ‖ₒₚ := by
  have hV := φ.norm_adjoint_stinespringOperator_le
  rw [LinearIsometryEquiv.norm_map] at hV
  refine le_antisymm ?_ ?_
  · calc ‖φ.stinespringOperator‖ ^ 2 ≤ √‖φ‖ₒₚ ^ 2 := by gcongr
      _ = ‖φ‖ₒₚ := Real.sq_sqrt (norm_nonneg _)
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun a => ?_
    change ‖φ a‖ ≤ _
    rw [apply_eq_adjoint_comp_stinespringNonUnitalStarAlgHom_comp]
    calc ‖φ.stinespringOperator† ∘L
          φ.stinespringNonUnitalStarAlgHom a ∘L φ.stinespringOperator‖
        ≤ ‖φ.stinespringOperator†‖ *
          (‖φ.stinespringNonUnitalStarAlgHom a‖ * ‖φ.stinespringOperator‖) :=
          (ContinuousLinearMap.opNorm_comp_le _ _).trans (by gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _)
      _ ≤ ‖φ.stinespringOperator‖ * (‖a‖ * ‖φ.stinespringOperator‖) := by
          rw [LinearIsometryEquiv.norm_map]
          gcongr
          exact NonUnitalStarAlgHom.norm_apply_le _ a
      _ = ‖φ.stinespringOperator‖ ^ 2 * ‖a‖ := by ring

/-- **Stinespring's theorem** for completely positive maps `φ : A → B(H)` on a (possibly
non-unital) C⋆-algebra `A`: there are a Hilbert space `K`, a ⋆-representation
`π : A →⋆ₙₐ[ℂ] B(K)` and a bounded operator `V : H → K` with `φ a = V† π(a) V`, such that the
vectors `π(a) V ξ` span a dense subspace of `K`, and `‖V‖² = ‖φ‖`. -/
theorem exists_stinespring_dilation :
    ∃ (K : Type (max u v)) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K)
      (_ : CompleteSpace K) (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K),
      (∀ a, φ a = V† ∘L π a ∘L V) ∧
      (Submodule.span ℂ (Set.range fun p : A × H => π p.1 (V p.2))).topologicalClosure = ⊤ ∧
      ‖V‖ ^ 2 = ‖φ‖ₒₚ :=
  ⟨φ.Stinespring, inferInstance, inferInstance, inferInstance, φ.stinespringNonUnitalStarAlgHom,
    φ.stinespringOperator, φ.apply_eq_adjoint_comp_stinespringNonUnitalStarAlgHom_comp,
    φ.topologicalClosure_span_stinespringNonUnitalStarAlgHom_apply_stinespringOperator_eq_top,
    φ.norm_stinespringOperator_sq⟩

/-! ### Uniqueness of the minimal dilation -/

/-- For any dilation `φ a = V† π(a) V`, `⟪π(a) V η, V ξ⟫ = ⟪η, φ(a⋆) ξ⟫`. -/
lemma inner_apply_apply_eq_inner_map_star {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] {π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)} {V : H →L[ℂ] K}
    (hφ : ∀ a, φ a = V† ∘L π a ∘L V) (a : A) (η ξ : H) :
    ⟪π a (V η), V ξ⟫_ℂ = ⟪η, φ (star a) ξ⟫_ℂ := by
  rw [hφ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, map_star, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

/-- **Uniqueness of the minimal Stinespring dilation**, against the Stinespring representation:
every minimal dilation `φ a = V† π(a) V` on a Hilbert space `K`, with the vectors `π(a) V ξ`
spanning a dense subspace, is unitarily equivalent to `(π_φ, V_φ, φ.Stinespring)`: there is a
unitary `U : φ.Stinespring ≃ K` with `U V_φ = V` and `U π_φ(a) = π(a) U`. The map
`U [a ⊗ ξ] = π(a) V ξ` preserves inner products, `⟪π(a) V ξ, π(b) V η⟫ = ⟪ξ, φ(a⋆ b) η⟫`, so it
extends from the pre-Stinespring space to an isometry of the completion, whose range is closed
and contains the dense span of the `π(a) V ξ`. -/
lemma exists_linearIsometryEquiv_stinespring {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K)
    (hφ : ∀ a, φ a = V† ∘L π a ∘L V)
    (hmin : (Submodule.span ℂ (Set.range fun p : A × H => π p.1 (V p.2))).topologicalClosure = ⊤) :
    ∃ U : φ.Stinespring ≃ₗᵢ[ℂ] K, (∀ ξ, U (φ.stinespringOperator ξ) = V ξ) ∧
      ∀ a x, U (φ.stinespringNonUnitalStarAlgHom a x) = π a (U x) := by
  let T : A ⊗[ℂ] H →ₗ[ℂ] K := TensorProduct.lift
    { toFun a := (π a : K →L[ℂ] K).toLinearMap ∘ₗ V.toLinearMap
      map_add' a b := by ext; simp
      map_smul' c a := by ext; simp }
  have hT : ∀ a ξ, T (a ⊗ₜ ξ) = π a (V ξ) := fun _ _ => rfl
  have hpair : ∀ a b ξ η, ⟪π a (V ξ), π b (V η)⟫_ℂ = ⟪ξ, φ (star a * b) η⟫_ℂ := by
    intro a b ξ η
    rw [hφ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_right, map_mul, map_star, mul_apply_eq_comp,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  have hinner : ∀ z w, ⟪T z, T w⟫_ℂ = φ.stinespringForm z w := by
    intro z w
    induction z with
    | add z₁ z₂ h₁ h₂ => simp [h₁, h₂]
    | tmul a ξ =>
      induction w with
      | add w₁ w₂ h₁ h₂ => simp [h₁, h₂]
      | tmul b η => rw [hT, hT, stinespringForm_tmul, hpair]
  let T₀ : φ.PreStinespring →ₗᵢ[ℂ] K :=
    LinearMap.isometryOfInner (T ∘ₗ φ.ofPreStinespring.toLinearMap) fun z w => hinner _ _
  let U₀ : φ.Stinespring →L[ℂ] K :=
    T₀.toContinuousLinearMap.extend (toComplL : φ.PreStinespring →L[ℂ] φ.Stinespring)
  have hU₀ (z : φ.PreStinespring) : U₀ z = T₀ z :=
    ContinuousLinearMap.extend_eq _ denseRange_coe (isUniformInducing_coe _) z
  have hnorm (x : φ.Stinespring) : ‖U₀ x‖ = ‖x‖ := by
    induction x using induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih z => rw [hU₀, T₀.norm_map, norm_coe]
  let U₁ : φ.Stinespring →ₗᵢ[ℂ] K := ⟨U₀.toLinearMap, hnorm⟩
  have hU₁ (a : A) (ξ : H) : U₁ (φ.stinespringMk (a ⊗ₜ ξ)) = π a (V ξ) := by
    change U₀ (φ.toPreStinespring (a ⊗ₜ ξ)) = _
    rw [hU₀]; rfl
  have hsurj : Function.Surjective U₁ := by
    have hclosed : IsClosed (LinearMap.range U₁.toLinearMap : Set K) := by
      rw [LinearMap.coe_range]
      exact U₁.isometry.isClosedEmbedding.isClosed_range
    have hle : Submodule.span ℂ (Set.range fun p : A × H => π p.1 (V p.2)) ≤
        LinearMap.range U₁.toLinearMap := by
      rw [Submodule.span_le]
      rintro _ ⟨⟨a, ξ⟩, rfl⟩
      exact ⟨_, hU₁ a ξ⟩
    have htop : (⊤ : Submodule ℂ K) ≤ LinearMap.range U₁.toLinearMap :=
      hmin ▸ Submodule.topologicalClosure_minimal _ hle hclosed
    exact fun y => htop (Submodule.mem_top (x := y))
  let U := LinearIsometryEquiv.ofSurjective U₁ hsurj
  have hUmk (a : A) (ξ : H) : U (φ.stinespringMk (a ⊗ₜ ξ)) = π a (V ξ) := hU₁ a ξ
  have hπ (a : A) (x : φ.Stinespring) :
      U (φ.stinespringNonUnitalStarAlgHom a x) = π a (U x) := by
    induction x using induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih z =>
      obtain ⟨z, rfl⟩ := φ.toPreStinespring.surjective z
      induction z with
      | add z₁ z₂ h₁ h₂ =>
        simp only [map_add, UniformSpace.Completion.coe_add] at h₁ h₂ ⊢
        rw [h₁, h₂]
      | tmul b ξ =>
        have := hUmk (a * b) ξ
        rw [← stinespringNonUnitalStarAlgHom_apply_stinespringMk_tmul] at this
        rw [show ((φ.toPreStinespring (b ⊗ₜ ξ) : φ.PreStinespring) : φ.Stinespring) =
          φ.stinespringMk (b ⊗ₜ ξ) from rfl, this, hUmk, map_mul, mul_apply_eq_comp]
  refine ⟨U, fun ξ => ?_, hπ⟩
  -- `U V_φ ξ - V ξ` is orthogonal to every `π(a) V η`: both pair with it to `⟪η, φ(a⋆) ξ⟫`.
  have horth : U (φ.stinespringOperator ξ) - V ξ ∈
      (Submodule.span ℂ (Set.range fun p : A × H => π p.1 (V p.2)))ᗮ := by
    refine (Submodule.mem_orthogonal _ _).2 fun u hu => ?_
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨a, η⟩, rfl⟩ := hx
      have h1 : ⟪π a (V η), U (φ.stinespringOperator ξ)⟫_ℂ = ⟪η, φ (star a) ξ⟫_ℂ := by
        rw [← hUmk, ← stinespringNonUnitalStarAlgHom_apply_stinespringOperator,
          LinearIsometryEquiv.inner_map_map]
        exact φ.inner_apply_apply_eq_inner_map_star
          φ.apply_eq_adjoint_comp_stinespringNonUnitalStarAlgHom_comp a η ξ
      dsimp only
      rw [inner_sub_right, h1, φ.inner_apply_apply_eq_inner_map_star hφ, sub_self]
    | zero => exact inner_zero_left _
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [inner_smul_left, hx, mul_zero]
  rw [(Submodule.topologicalClosure_eq_top_iff).1 hmin, Submodule.mem_bot, sub_eq_zero] at horth
  exact horth

/-- **Uniqueness of the minimal Stinespring dilation** (Paulsen, Ch. 4): two minimal
dilations `φ a = Vᵢ† πᵢ(a) Vᵢ` on Hilbert spaces `Kᵢ`, with the vectors `πᵢ(a) Vᵢ ξ` spanning dense
subspaces, are unitarily equivalent: there is a unitary `U : K₁ ≃ K₂` with `U V₁ = V₂` and
`U π₁(a) = π₂(a) U`. Both are equivalent to the Stinespring representation
(`CompletelyPositiveMap.exists_linearIsometryEquiv_stinespring`). -/
theorem exists_linearIsometryEquiv_of_stinespring_dilation {K₁ K₂ : Type*}
    [NormedAddCommGroup K₁] [InnerProductSpace ℂ K₁] [CompleteSpace K₁]
    [NormedAddCommGroup K₂] [InnerProductSpace ℂ K₂] [CompleteSpace K₂]
    (π₁ : A →⋆ₙₐ[ℂ] (K₁ →L[ℂ] K₁)) (V₁ : H →L[ℂ] K₁)
    (hφ₁ : ∀ a, φ a = V₁† ∘L π₁ a ∘L V₁)
    (hmin₁ : (Submodule.span ℂ (Set.range fun p : A × H => π₁ p.1 (V₁ p.2))).topologicalClosure = ⊤)
    (π₂ : A →⋆ₙₐ[ℂ] (K₂ →L[ℂ] K₂)) (V₂ : H →L[ℂ] K₂)
    (hφ₂ : ∀ a, φ a = V₂† ∘L π₂ a ∘L V₂)
    (hmin₂ : (Submodule.span ℂ (Set.range fun p : A × H => π₂ p.1 (V₂ p.2))).topologicalClosure = ⊤) :
    ∃ U : K₁ ≃ₗᵢ[ℂ] K₂, (∀ ξ, U (V₁ ξ) = V₂ ξ) ∧ ∀ a x, U (π₁ a x) = π₂ a (U x) := by
  obtain ⟨U₁, hV₁, hπ₁⟩ := φ.exists_linearIsometryEquiv_stinespring π₁ V₁ hφ₁ hmin₁
  obtain ⟨U₂, hV₂, hπ₂⟩ := φ.exists_linearIsometryEquiv_stinespring π₂ V₂ hφ₂ hmin₂
  refine ⟨U₁.symm.trans U₂, fun ξ => ?_, fun a x => ?_⟩
  · rw [LinearIsometryEquiv.trans_apply, ← hV₁, LinearIsometryEquiv.symm_apply_apply, hV₂]
  · obtain ⟨y, rfl⟩ := U₁.surjective x
    rw [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.trans_apply, ← hπ₁,
      LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.symm_apply_apply, hπ₂]

end NonUnital

/-! ### The unital case -/

section Unital

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (φ : A →CP (H →L[ℂ] H))

/-- On a unital algebra the Stinespring representation is unital: `π(1) = 1`. -/
lemma stinespringNonUnitalStarAlgHom_one : φ.stinespringNonUnitalStarAlgHom 1 = 1 := by
  ext x
  induction x using induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih z =>
    rw [stinespringNonUnitalStarAlgHom_apply_coe, one_apply_eq_self]
    congr 1
    obtain ⟨z, rfl⟩ := φ.toPreStinespring.surjective z
    induction z with
    | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | tmul b ξ => rw [leftMulMapPreStinespring_tmul, one_mul]

/-- The unital Stinespring representation `π : A →⋆ₐ[ℂ] B(K)` of a completely positive map
`φ : A → B(H)` on a unital C⋆-algebra. -/
noncomputable def stinespringStarAlgHom : A →⋆ₐ[ℂ] (φ.Stinespring →L[ℂ] φ.Stinespring) where
  __ := φ.stinespringNonUnitalStarAlgHom
  map_one' := φ.stinespringNonUnitalStarAlgHom_one
  commutes' r := by
    simp [Algebra.algebraMap_eq_smul_one, φ.stinespringNonUnitalStarAlgHom_one]

/-- The unital Stinespring representation has the operators of the non-unital one. -/
lemma stinespringStarAlgHom_apply (a : A) :
    φ.stinespringStarAlgHom a = φ.stinespringNonUnitalStarAlgHom a := rfl

/-- In the unital case `V ξ = [1 ⊗ ξ]`. -/
lemma stinespringOperator_apply (ξ : H) : φ.stinespringOperator ξ = φ.stinespringMk (1 ⊗ₜ ξ) := by
  rw [← φ.stinespringNonUnitalStarAlgHom_apply_stinespringOperator, stinespringNonUnitalStarAlgHom_one,
    one_apply_eq_self]

/-- **Stinespring's theorem**, unital case: `φ a = V† π(a) V` for the unital Stinespring
representation `π = φ.stinespringStarAlgHom`. -/
theorem apply_eq_adjoint_comp_stinespringStarAlgHom_comp (a : A) :
    φ a = φ.stinespringOperator† ∘L
      φ.stinespringStarAlgHom a ∘L φ.stinespringOperator :=
  φ.apply_eq_adjoint_comp_stinespringNonUnitalStarAlgHom_comp a

/-- `V† V = φ 1`. -/
lemma adjoint_stinespringOperator_comp_self :
    φ.stinespringOperator† ∘L φ.stinespringOperator = φ 1 := by
  rw [φ.apply_eq_adjoint_comp_stinespringNonUnitalStarAlgHom_comp,
    stinespringNonUnitalStarAlgHom_one, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]

/-- `V` is an isometry iff `φ` is unital. -/
lemma isometry_stinespringOperator_iff : Isometry φ.stinespringOperator ↔ φ 1 = 1 := by
  rw [ContinuousLinearMap.isometry_iff_adjoint_comp_self, adjoint_stinespringOperator_comp_self]

/-- `‖V‖² = ‖φ 1‖`. -/
lemma norm_stinespringOperator_sq_eq_norm_map_one : ‖φ.stinespringOperator‖ ^ 2 = ‖φ 1‖ := by
  rw [← adjoint_stinespringOperator_comp_self, ContinuousLinearMap.norm_adjoint_comp_self, sq]

/-- **Stinespring's theorem** for completely positive maps `φ : A → B(H)` on a unital C⋆-algebra
`A`: there are a Hilbert space `K`, a unital ⋆-representation `π : A →⋆ₐ[ℂ] B(K)` and a bounded
operator `V : H → K` with `φ a = V† π(a) V` and `V† V = φ 1`, such that the vectors `π(a) V ξ`
span a dense subspace of `K`. -/
theorem exists_unital_stinespring_dilation :
    ∃ (K : Type (max u v)) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K)
      (_ : CompleteSpace K) (π : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K),
      (∀ a, φ a = V† ∘L π a ∘L V) ∧
      V† ∘L V = φ 1 ∧
      (Submodule.span ℂ (Set.range fun p : A × H => π p.1 (V p.2))).topologicalClosure = ⊤ :=
  ⟨φ.Stinespring, inferInstance, inferInstance, inferInstance, φ.stinespringStarAlgHom,
    φ.stinespringOperator, φ.apply_eq_adjoint_comp_stinespringStarAlgHom_comp,
    φ.adjoint_stinespringOperator_comp_self,
    φ.topologicalClosure_span_stinespringNonUnitalStarAlgHom_apply_stinespringOperator_eq_top⟩

end Unital

end CompletelyPositiveMap
