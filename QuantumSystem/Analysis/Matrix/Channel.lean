/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.Matrix.DensityMatrix.Basic
public import QuantumSystem.ForMathlib.LinearAlgebra.Matrix.PartialTrace

/-!
# Quantum Channels (Completely Positive Trace-Preserving Maps)

This file defines quantum channels on finite-dimensional matrix algebras and establishes
their basic properties. A quantum channel is a linear map Φ: M_n(ℂ) → M_m(ℂ) that is:
1. Completely positive (CP): Has a Kraus representation Φ(ρ) = Σᵢ Kᵢ ρ Kᵢ†
2. Trace-preserving (TP): Tr(Φ(A)) = Tr(A) for all A, equivalently Σᵢ Kᵢ† Kᵢ = I

It also packages the **partial trace** on product index types as a quantum channel: tracing out a
factor of a matrix on `X × Y` (or `A × B × C`) is completely positive and trace preserving, and the
trace-out-`C` channel `QuantumChannel.traceOutC` realises the `lean-eval` marginal map.

## Main definitions

* `IsTracePreserving`: A linear map preserves trace.
* `IsCompletelyPositive`: A linear map has a Kraus representation.
* `IsQuantumChannel`: A linear map is both CP and TP.
* `Matrix.partialTraceRightₗ` — right partial trace as a `ℂ`-linear map.
* `Matrix.QuantumChannel.partialTraceRight` — bundled quantum channel tracing out `Y`.
* `Matrix.QuantumChannel.reindex` — conjugation by an index equivalence, as a channel.
* `Matrix.QuantumChannel.traceOutC` — trace out the `C` factor of `A × B × C`.
* `Matrix.traceDual Φ` — the trace dual (Heisenberg picture), `Tr (Φ A * B) = Tr (A * Φ* B)`
  (`Matrix.trace_mul_traceDual`); for a Kraus map it is `B ↦ Σᵢ Kᵢᴴ B Kᵢ`
  (`Matrix.traceDual_eq_of_kraus`), unital for trace-preserving `Φ` (`Matrix.traceDual_one`).

## Mathematical Background

### Choi-Kraus Theorem
A linear map Φ: M_n(ℂ) → M_m(ℂ) is completely positive if and only if it has a
Kraus representation:
  Φ(ρ) = Σᵢ Kᵢ ρ Kᵢ†
where Kᵢ: ℂⁿ → ℂᵐ are linear maps (Kraus operators).

The map is trace-preserving if and only if:
  Σᵢ Kᵢ† Kᵢ = I

## References

* Nielsen, Chuang, *Quantum Computation and Quantum Information*, Chapter 8
* Watrous, *The Theory of Quantum Information*, Chapter 2
-/

@[expose] public section

namespace Matrix

variable {n m k : Type*} [Fintype n] [Fintype m] [Fintype k]

open scoped ComplexOrder

/-! ### Trace-Preserving Maps -/

/-- A linear map is trace-preserving if Tr(Φ(A)) = Tr(A) for all A. -/
def IsTracePreserving (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Prop :=
  ∀ A : Matrix n n ℂ, Tr (Φ A) = Tr A

/-! ### Completely Positive Maps -/

/-- A linear map is completely positive if it has a Kraus representation.
This is equivalent to the Choi matrix being positive semi-definite. -/
def IsCompletelyPositive (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Prop :=
  ∃ (r : ℕ) (K : Fin r → Matrix m n ℂ),
    ∀ A, Φ A = ∑ i, K i * A * (K i)ᴴ

/-! ### Quantum Channels -/

/-- A quantum channel is a completely positive trace-preserving (CPTP) map.
These are the physically realizable operations on quantum states. -/
structure IsQuantumChannel (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Prop where
  /-- The map is completely positive -/
  completelyPositive : IsCompletelyPositive Φ
  /-- The map preserves trace -/
  tracePreserving : IsTracePreserving Φ

/-- Quantum channel as a subtype for cleaner API. -/
abbrev QuantumChannel (n : Type*) (m : Type*) [Fintype n] [Fintype m] :=
  { Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ // IsQuantumChannel Φ }

/-- The identity map is a quantum channel. -/
lemma isQuantumChannel_id : IsQuantumChannel (LinearMap.id : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) where
  completelyPositive := by
    classical
    -- id has Kraus representation with single operator K = I
    use 1, fun _ => 1
    intro A
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
    simp [Matrix.conjTranspose_one]
  tracePreserving := fun _ => rfl

/-- Composition of quantum channels is a quantum channel. -/
lemma QuantumChannel.comp
    (Φ : QuantumChannel n m) (Ψ : QuantumChannel m k) :
    IsQuantumChannel (Ψ.val.comp Φ.val) where
  completelyPositive := by
    classical
    -- Composition of CP maps is CP
    -- If Φ(A) = Σᵢ Kᵢ A Kᵢ† and Ψ(B) = Σⱼ Lⱼ B Lⱼ†
    -- Then (Ψ∘Φ)(A) = Σⱼ Lⱼ (Σᵢ Kᵢ A Kᵢ†) Lⱼ† = Σᵢⱼ (Lⱼ Kᵢ) A (Lⱼ Kᵢ)†
    obtain ⟨r, K, hK⟩ := Φ.property.completelyPositive
    obtain ⟨s, L, hL⟩ := Ψ.property.completelyPositive
    -- Use product Kraus operators indexed by Fin s × Fin r
    use s * r
    -- Define the combined Kraus operators via equivalence Fin (s * r) ≃ Fin s × Fin r
    let e : Fin (s * r) ≃ Fin s × Fin r := finProdFinEquiv.symm
    use fun p => L (e p).1 * K (e p).2
    intro A
    simp only [LinearMap.comp_apply, hK, hL]
    -- Ψ(Σᵢ Kᵢ A Kᵢ†) = Σⱼ Lⱼ (Σᵢ Kᵢ A Kᵢ†) Lⱼ†
    simp_rw [Matrix.mul_sum, Matrix.sum_mul]
    -- Reindex: ∑_{j,i} = ∑_p via Equiv.sum_comp
    rw [← Fintype.sum_prod_type']
    rw [(Equiv.sum_comp e (fun x => L x.1 * (K x.2 * A * (K x.2)ᴴ) * (L x.1)ᴴ)).symm]
    apply Finset.sum_congr rfl
    intro p _
    -- Need to show: L (e p).1 * (K (e p).2 * A * (K (e p).2)†) * (L (e p).1)†
    --             = L (e p).1 * K (e p).2 * A * (L (e p).1 * K (e p).2)†
    rw [Matrix.conjTranspose_mul]
    -- Now use matrix associativity
    simp only [Matrix.mul_assoc]
  tracePreserving := by
    intro A
    simp only [LinearMap.comp_apply]
    rw [Ψ.property.tracePreserving, Φ.property.tracePreserving]

omit [Fintype m] in
/-- A completely positive map preserves Hermitianity of matrices.
If Φ(A) = Σᵢ Kᵢ A Kᵢ† and A is Hermitian, then Φ(A) is Hermitian. -/
lemma IsCompletelyPositive.map_isHermitian
    {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ} (hΦ : IsCompletelyPositive Φ)
    {A : Matrix n n ℂ} (hA : A.IsHermitian) : (Φ A).IsHermitian := by
  classical
  obtain ⟨r, K, hK⟩ := hΦ
  rw [hK]
  rw [Matrix.IsHermitian, Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [Matrix.mul_assoc]
  congr 1
  rw [hA.eq]

/-- Apply a quantum channel to a density matrix. -/
noncomputable def QuantumChannel.apply [DecidableEq n] [DecidableEq m]
    (Φ : QuantumChannel n m) (ρ : DensityMatrix n) :
    DensityMatrix m where
  toMatrix := Φ.val ↑ρ
  posSemidef := by
    classical
    obtain ⟨r, K, hK⟩ := Φ.property.completelyPositive
    rw [hK]
    apply posSemidef_sum
    intro i _
    exact ρ.posSemidef.mul_mul_conjTranspose_same (K i)
  trace_eq_one := by
    rw [Φ.property.tracePreserving]
    exact ρ.trace_eq_one
/-- Quantum channels can be applied as functions from density matrices to density matrices. -/
noncomputable instance [DecidableEq n] [DecidableEq m] : CoeFun (QuantumChannel n m)
    (fun _ => DensityMatrix n → DensityMatrix m) where
  coe := QuantumChannel.apply

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

omit [Fintype m] in
/-- A completely positive map sends positive semidefinite matrices to positive semidefinite
matrices. -/
lemma IsCompletelyPositive.posSemidef_map [Finite m]
    {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ} (hΦ : IsCompletelyPositive Φ)
    {A : Matrix n n ℂ} (hA : A.PosSemidef) : (Φ A).PosSemidef := by
  classical
  have := Fintype.ofFinite m
  obtain ⟨r, K, hK⟩ := hΦ
  rw [hK]
  exact posSemidef_sum _ fun i _ => hA.mul_mul_conjTranspose_same (K i)

/-! ### Trace dual -/

section TraceDual

variable [DecidableEq n]

/-- The **trace dual** (Heisenberg picture) of a linear map on matrix algebras, characterised by
`Tr (Φ A * B) = Tr (A * traceDual Φ B)` (`Matrix.trace_mul_traceDual`). Its entries are
`(traceDual Φ B) j i = Tr (Φ (E_{ij}) B)` for the matrix units `E_{ij} = Matrix.single i j 1`. For
a Kraus map `A ↦ Σᵢ Kᵢ A Kᵢᴴ` it is `B ↦ Σᵢ Kᵢᴴ B Kᵢ` (`Matrix.traceDual_eq_of_kraus`); it is unital
exactly when `Φ` is trace preserving (`Matrix.traceDual_one`). -/
noncomputable def traceDual (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ where
  toFun B := Matrix.of fun j i => Tr (Φ (Matrix.single i j 1) * B)
  map_add' B C := by
    ext j i
    simp [Matrix.mul_add, Matrix.trace_add]
  map_smul' c B := by
    ext j i
    simp [Matrix.mul_smul, Matrix.trace_smul]

omit [Fintype n] in
lemma traceDual_apply (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) (B : Matrix m m ℂ) (j i : n) :
    traceDual Φ B j i = Tr (Φ (Matrix.single i j 1) * B) := rfl

/-- **The defining duality**: `Tr (Φ A * B) = Tr (A * traceDual Φ B)`. -/
theorem trace_mul_traceDual (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) (A : Matrix n n ℂ)
    (B : Matrix m m ℂ) : Tr (Φ A * B) = Tr (A * traceDual Φ B) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  simp only [map_sum, Finset.sum_mul, Matrix.trace_sum]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, traceDual_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show Matrix.single i j (A i j) = A i j • Matrix.single i j (1 : ℂ) by
      rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul]
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- The trace dual of a Kraus map `A ↦ Σᵢ Kᵢ A Kᵢᴴ` is `B ↦ Σᵢ Kᵢᴴ B Kᵢ`. -/
theorem traceDual_eq_of_kraus {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ} {r : ℕ}
    {K : Fin r → Matrix m n ℂ} (hK : ∀ A, Φ A = ∑ i, K i * A * (K i)ᴴ) (B : Matrix m m ℂ) :
    traceDual Φ B = ∑ i, (K i)ᴴ * B * K i := by
  refine Matrix.ext_iff_trace_mul_left.mpr fun x => ?_
  rw [← trace_mul_traceDual, hK, Finset.sum_mul, Matrix.trace_sum, Matrix.mul_sum,
    Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_assoc x]
  exact Matrix.trace_mul_comm _ _

/-- The trace dual of a trace-preserving map is unital. -/
theorem traceDual_one [DecidableEq m] {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ}
    (hΦ : IsTracePreserving Φ) : traceDual Φ 1 = 1 := by
  refine Matrix.ext_iff_trace_mul_left.mpr fun x => ?_
  rw [← trace_mul_traceDual, Matrix.mul_one, Matrix.mul_one, hΦ]

end TraceDual

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

/-! ### Partial trace as a quantum channel (product index types) -/

/-! #### Positive semidefiniteness and trace facts for the partial trace -/

/-- The right partial trace preserves positive semidefiniteness (it is a sum of principal
submatrices). -/
lemma traceRight_posSemidef {l n : Type*} [Fintype n]
    {M : Matrix (l × n) (l × n) ℂ} (hM : M.PosSemidef) : (Matrix.traceRight M).PosSemidef := by
  have hsum : Matrix.traceRight M
      = ∑ k : n, M.submatrix (fun i : l => (i, k)) (fun j : l => (j, k)) := by
    ext i j; simp [Matrix.traceRight_apply, Matrix.sum_apply, Matrix.submatrix_apply]
  rw [hsum]
  exact Matrix.posSemidef_sum _ (fun k _ => hM.submatrix _)

/-- The left partial trace preserves positive semidefiniteness. -/
lemma traceLeft_posSemidef {l n : Type*} [Fintype n]
    {M : Matrix (n × l) (n × l) ℂ} (hM : M.PosSemidef) : (Matrix.traceLeft M).PosSemidef := by
  have hsum : Matrix.traceLeft M
      = ∑ k : n, M.submatrix (fun i : l => (k, i)) (fun j : l => (k, j)) := by
    ext i j; simp [Matrix.traceLeft_apply, Matrix.sum_apply, Matrix.submatrix_apply]
  rw [hsum]
  exact Matrix.posSemidef_sum _ (fun k _ => hM.submatrix _)

/-- Reindexing by an index equivalence preserves the trace. -/
@[simp] lemma trace_reindex_self {n m : Type*} [Fintype n] [Fintype m] (e : n ≃ m)
    (M : Matrix n n ℂ) : (M.reindex e e).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp e.symm (fun i => M i i)

/-- The right partial trace of the identity scales by the cardinality of the traced factor. -/
lemma traceRight_one {X Y : Type*} [DecidableEq X] [Fintype Y] [DecidableEq Y] :
    Matrix.traceRight (1 : Matrix (X × Y) (X × Y) ℂ) = (Fintype.card Y : ℂ) • (1 : Matrix X X ℂ) := by
  ext i j
  simp only [traceRight_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, Prod.mk.injEq]
  by_cases hij : i = j
  · subst hij; simp [Finset.card_univ]
  · simp [hij]

/-- The left partial trace of the identity scales by the cardinality of the traced factor. -/
lemma traceLeft_one {X Y : Type*} [Fintype X] [DecidableEq X] [DecidableEq Y] :
    Matrix.traceLeft (1 : Matrix (X × Y) (X × Y) ℂ) = (Fintype.card X : ℂ) • (1 : Matrix Y Y ℂ) := by
  ext i j
  simp only [traceLeft_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, Prod.mk.injEq]
  by_cases hij : i = j
  · subst hij; simp [Finset.card_univ]
  · simp [hij]

/-! #### Right partial trace as a linear map -/

/-- `Matrix.traceRight` as a `ℂ`-linear map `Matrix (X × Y) (X × Y) ℂ →ₗ[ℂ] Matrix X X ℂ`. -/
noncomputable def partialTraceRightₗ {X Y : Type*} [Fintype Y] :
    Matrix (X × Y) (X × Y) ℂ →ₗ[ℂ] Matrix X X ℂ where
  toFun M := Matrix.traceRight M
  map_add' M N := by
    ext i j; simp only [traceRight_apply, Matrix.add_apply, Finset.sum_add_distrib]
  map_smul' c M := by
    ext i j
    simp only [traceRight_apply, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]

@[simp] lemma partialTraceRightₗ_apply {X Y : Type*} [Fintype Y] (M : Matrix (X × Y) (X × Y) ℂ) :
    partialTraceRightₗ M = Matrix.traceRight M := rfl

/-- `Matrix.traceLeft` as a `ℂ`-linear map `Matrix (X × Y) (X × Y) ℂ →ₗ[ℂ] Matrix Y Y ℂ`. -/
noncomputable def partialTraceLeftₗ {X Y : Type*} [Fintype X] :
    Matrix (X × Y) (X × Y) ℂ →ₗ[ℂ] Matrix Y Y ℂ where
  toFun M := Matrix.traceLeft M
  map_add' M N := by
    ext i j; simp only [traceLeft_apply, Matrix.add_apply, Finset.sum_add_distrib]
  map_smul' c M := by
    ext i j
    simp only [traceLeft_apply, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]

@[simp] lemma partialTraceLeftₗ_apply {X Y : Type*} [Fintype X] (M : Matrix (X × Y) (X × Y) ℂ) :
    partialTraceLeftₗ M = Matrix.traceLeft M := rfl

/-! #### Kraus operators and complete positivity -/

/-- Kraus operator for the right partial trace, indexed by `y : Y`: `K_y x p = [p = (x, y)]`. -/
def traceRightKraus {X Y : Type*} [DecidableEq X] [DecidableEq Y] (y : Y) :
    Matrix X (X × Y) ℂ :=
  Matrix.of fun x p => if p = (x, y) then (1 : ℂ) else 0

lemma isCompletelyPositive_partialTraceRight {X Y : Type*} [Fintype X] [Fintype Y] :
    IsCompletelyPositive (partialTraceRightₗ (X := X) (Y := Y)) := by
  classical
  refine ⟨Fintype.card Y, fun i => traceRightKraus ((Fintype.equivFin Y).symm i), fun M => ?_⟩
  rw [partialTraceRightₗ_apply]
  ext i j
  rw [traceRight_apply, Matrix.sum_apply, ← (Fintype.equivFin Y).symm.sum_comp
    (fun y => M (i, y) (j, y))]
  refine Finset.sum_congr rfl fun p _ => ?_
  -- Goal: M (i, y) (j, y) = (K_y * M * K_yᴴ) i j with `y = (equivFin Y).symm p`
  -- (mul is `Matrix.mul` from `IsCompletelyPositive`).
  symm
  rw [Matrix.mul_apply, Finset.sum_eq_single (j, (Fintype.equivFin Y).symm p)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (i, (Fintype.equivFin Y).symm p)]
    · simp [traceRightKraus, Matrix.conjTranspose_apply]
    · intro q _ hq
      simp only [traceRightKraus, Matrix.of_apply]
      rw [ite_eq_right hq]; ring
    · simp
  · intro q _ hq
    simp only [traceRightKraus, Matrix.conjTranspose_apply, Matrix.of_apply,
      apply_ite (star · : ℂ → ℂ), star_one, star_zero]
    rw [ite_eq_right hq]; simp
  · simp

lemma isTracePreserving_partialTraceRight {X Y : Type*} [Fintype X] [Fintype Y] :
    IsTracePreserving (partialTraceRightₗ (X := X) (Y := Y)) :=
  fun M => by rw [partialTraceRightₗ_apply]; exact trace_traceRight M

/-- Right partial trace (trace out `Y`) as a bundled `QuantumChannel`. -/
noncomputable def QuantumChannel.partialTraceRight {X Y : Type*} [Fintype X] [Fintype Y] :
    Matrix.QuantumChannel (X × Y) X :=
  ⟨partialTraceRightₗ, isCompletelyPositive_partialTraceRight, isTracePreserving_partialTraceRight⟩

/-! #### Conjugation by an index equivalence as a channel -/

/-- Conjugation by a reindex `e : Z ≃ W`: `M ↦ M.submatrix e.symm e.symm`, as a linear map. -/
noncomputable def reindexₗ {Z W : Type*} (e : Z ≃ W) :
    Matrix Z Z ℂ →ₗ[ℂ] Matrix W W ℂ where
  toFun M := M.submatrix e.symm e.symm
  map_add' M N := by ext w w'; simp [Matrix.submatrix_apply]
  map_smul' c M := by ext w w'; simp [Matrix.submatrix_apply]

@[simp] lemma reindexₗ_apply {Z W : Type*} (e : Z ≃ W) (M : Matrix Z Z ℂ) :
    reindexₗ e M = M.submatrix e.symm e.symm := rfl

/-- Kraus operator (permutation matrix) for `reindexₗ e`: `P w z = [z = e.symm w]`. -/
def reindexKraus {Z W : Type*} [DecidableEq Z] (e : Z ≃ W) : Matrix W Z ℂ :=
  Matrix.of fun w z => if z = e.symm w then (1 : ℂ) else 0

lemma isCompletelyPositive_reindexₗ {Z W : Type*} [Fintype Z] (e : Z ≃ W) :
    IsCompletelyPositive (reindexₗ e) := by
  classical
  refine ⟨1, fun _ => reindexKraus e, fun M => ?_⟩
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
  ext w w'
  rw [reindexₗ_apply, Matrix.submatrix_apply]
  symm
  rw [Matrix.mul_apply, Finset.sum_eq_single (e.symm w')]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (e.symm w)]
    · simp [reindexKraus]
    · intro q _ hq
      simp only [reindexKraus, Matrix.of_apply]
      rw [ite_eq_right hq]; ring
    · simp
  · intro z _ hz
    simp only [reindexKraus, Matrix.conjTranspose_apply, Matrix.of_apply,
      apply_ite (star · : ℂ → ℂ), star_one, star_zero]
    rw [ite_eq_right hz]; simp
  · simp

lemma isTracePreserving_reindexₗ {Z W : Type*} [Fintype Z] [Fintype W] (e : Z ≃ W) :
    IsTracePreserving (reindexₗ e) := by
  intro M
  rw [reindexₗ_apply]
  exact trace_reindex_self e M

/-- Conjugation by an index equivalence as a bundled `QuantumChannel`. -/
noncomputable def QuantumChannel.reindex {Z W : Type*} [Fintype Z] [Fintype W] (e : Z ≃ W) :
    Matrix.QuantumChannel Z W :=
  ⟨reindexₗ e, isCompletelyPositive_reindexₗ e, isTracePreserving_reindexₗ e⟩

/-! #### Trace-out-`C` channel for `A × B × C` -/

/-- Trace out the `C` factor of `A × B × C`, landing on `A × B`. Its action is the `lean-eval`
marginal map `M ↦ traceRight (M.reindex (prodAssoc).symm (prodAssoc).symm)`. -/
noncomputable def QuantumChannel.traceOutC {A B C : Type*} [Fintype A] [Fintype B] [Fintype C] :
    Matrix.QuantumChannel (A × B × C) (A × B) :=
  ⟨(partialTraceRightₗ (X := A × B) (Y := C)).comp (reindexₗ (Equiv.prodAssoc A B C).symm),
   QuantumChannel.comp (QuantumChannel.reindex (Equiv.prodAssoc A B C).symm)
     QuantumChannel.partialTraceRight⟩

@[simp] lemma QuantumChannel.traceOutC_val_apply {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C] (M : Matrix (A × B × C) (A × B × C) ℂ) :
    (QuantumChannel.traceOutC (A := A) (B := B) (C := C)).val M
      = Matrix.traceRight
          (M.reindex (Equiv.prodAssoc A B C).symm (Equiv.prodAssoc A B C).symm) := by
  change partialTraceRightₗ (reindexₗ (Equiv.prodAssoc A B C).symm M) = _
  rw [partialTraceRightₗ_apply, reindexₗ_apply, Matrix.reindex_apply]

end Matrix
