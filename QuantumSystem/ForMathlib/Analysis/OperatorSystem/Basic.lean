/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Operator systems and completely positive maps between them

A **matrix-ordered space** is a complex ⋆-vector space `V` with a partial order on each matrix space
`CStarMatrix (Fin k) (Fin k) V`, such that every level is an ordered additive group, positive elements
of `V` are self-adjoint, the conjugation `X ↦ α⋆ X α` by a scalar matrix `α` preserves positivity,
and the order at level `1` is the order of `V` (`MatrixOrdered`). An **operator system** is a
matrix-ordered space whose `1` is positive, lies above a real multiple of every self-adjoint element,
and is Archimedean at every level: a matrix is positive when it becomes positive after adding every
positive multiple of the identity matrix (`OperatorSystem`).

The axioms on positivity and on the order unit are stated at level `1` only; their matrix forms
follow from the scalar conjugations. A positive matrix is self-adjoint, since its compressions
`Xᵢᵢ + c Xᵢⱼ + c̄ Xⱼᵢ + |c|² Xⱼⱼ` along `eᵢ + c eⱼ` are
(`MatrixOrdered.isSelfAdjoint_of_cstarMatrix_nonneg`). The identity matrix is an order unit at every
level (`OperatorSystem.exists_le_smul_one_of_isSelfAdjoint`): a self-adjoint matrix is a sum of
matrices `(Mᵢⱼ • h)ᵢⱼ` with `M` a self-adjoint scalar matrix and `h` self-adjoint, and
`‖M‖ • 1 ± M ≥ 0` bounds each of them by a multiple of the identity matrix
(`OperatorSystem.smulRight_le`).

The matrix orders are instance arguments rather than data of the class, so that a C⋆-algebra uses
the order Mathlib already puts on `CStarMatrix (Fin k) (Fin k) A`: every unital C⋆-algebra is an
operator system (`CStarAlgebra.instOperatorSystem`). A unital ⋆-closed subspace `S` of an operator
system `T` (`OperatorSubsystem T`) is an operator system with the matrix orders of `T`.

Mathlib's completely positive maps (`CompletelyPositiveMap`) are defined between C⋆-algebras, though
the definition only uses the matrix orders. `CompletelyPositiveMap' A₁ A₂` is the same definition
with only the matrix orders assumed, written `A₁ →CP' A₂` under `open scoped CStarAlgebra`; it agrees
definitionally with Mathlib's between C⋆-algebras (`CompletelyPositiveMap'.equivCompletelyPositiveMap`).
It is meant to replace Mathlib's definition upstream, by weakening the hypotheses of the latter, and
to disappear from this file then.

## Main definitions

* `CStarMatrix.scalarMul α β` — the two-sided multiplication `X ↦ α X β` of a matrix over `V` by
  scalar matrices.
* `CStarMatrix.scalarConj α` — the conjugation `X ↦ α⋆ X α` of a matrix over `V` by a scalar matrix.
* `CStarMatrix.smulRight M v` — the matrix `(Mᵢⱼ • v)ᵢⱼ` of a scalar matrix `M` and a vector `v`.
* `MatrixOrdered V` — matrix-ordered complex ⋆-vector spaces.
* `OperatorSystem V` — matrix-ordered spaces with an Archimedean matrix order unit.
* `OperatorSubsystem T` — the unital ⋆-closed subspaces of `T`, with the induced matrix orders.
* `CompletelyPositiveMap' A₁ A₂`, `CompletelyPositiveMapClass' F A₁ A₂` — completely positive maps
  between matrix-ordered spaces.

## Main results

* `CStarMatrix.scalarConj_nonneg` — over a C⋆-algebra, `α⋆ X α` is positive when `X` is.
* `MatrixOrdered.isSelfAdjoint_of_cstarMatrix_nonneg` — positive matrices are self-adjoint.
* `OperatorSystem.exists_le_smul_one_of_isSelfAdjoint` — the identity matrix is an order unit at
  every level.
* `CStarAlgebra.nonneg_of_forall_add_smul_one_nonneg` — in a unital C⋆-algebra, `a` is positive when
  `a + ε • 1` is for every `ε > 0`.
* `CStarAlgebra.instOperatorSystem`, `OperatorSubsystem.instOperatorSystem` — C⋆-algebras and their
  operator subsystems are operator systems.
* `CompletelyPositiveMapClass'.instOrderHomClass` — completely positive maps are positive.
* `CompletelyPositiveMap'.equivCompletelyPositiveMap` — between C⋆-algebras, these are Mathlib's
  completely positive maps.

## TODO

* Upstream to Mathlib the weakening of the hypotheses of `CompletelyPositiveMap` and
  `CompletelyPositiveMapClass` from C⋆-algebras to the matrix orders on `CStarMatrix (Fin k) (Fin k) V`,
  following `CompletelyPositiveMap'` and `CompletelyPositiveMapClass'`, and then replace these and
  `CompletelyPositiveMap'.equivCompletelyPositiveMap` by Mathlib's definitions.
-/

@[expose] public section

open scoped CStarAlgebra ComplexOrder ComplexStarModule

/-! ### Scalar conjugation of matrices -/

namespace CStarMatrix

section scalarConj

variable {m n V W : Type*} [AddCommMonoid V] [Module ℂ V] [AddCommMonoid W] [Module ℂ W] [Fintype m]

/-- The two-sided multiplication `X ↦ α X β` of an `m × m` matrix over a complex vector space `V` by
scalar matrices `α : n × m` and `β : m × n`: `(α X β) i j = ∑ p q, α i p β q j • X p q`. -/
def scalarMul (α : Matrix n m ℂ) (β : Matrix m n ℂ) : CStarMatrix m m V →ₗ[ℂ] CStarMatrix n n V where
  toFun X := ofMatrix (Matrix.of fun i j => ∑ p, ∑ q, (α i p * β q j) • X p q)
  map_add' X Y := by ext i j; simp [Finset.sum_add_distrib, smul_add]
  map_smul' c X := by ext i j; simp [Finset.smul_sum, smul_comm c]

/-- The entries of a two-sided scalar multiplication `α X β`. -/
lemma scalarMul_apply (α : Matrix n m ℂ) (β : Matrix m n ℂ) (X : CStarMatrix m m V) (i j : n) :
    scalarMul α β X i j = ∑ p, ∑ q, (α i p * β q j) • X p q :=
  rfl

/-- Two-sided scalar multiplication commutes with applying a linear map entrywise. -/
lemma scalarMul_map (α : Matrix n m ℂ) (β : Matrix m n ℂ) (X : CStarMatrix m m V) (f : V →ₗ[ℂ] W) :
    (scalarMul α β X).map f = scalarMul α β (X.map f) := by
  ext i j
  simp [scalarMul_apply, map_sum, map_smul]

/-- The conjugation `X ↦ α⋆ X α` of an `m × m` matrix over a complex vector space `V` by a scalar
`m × n` matrix `α`: `(α⋆ X α) i j = ∑ p q, conj (α p i) α q j • X p q`. -/
def scalarConj (α : Matrix m n ℂ) : CStarMatrix m m V →ₗ[ℂ] CStarMatrix n n V :=
  scalarMul α.conjTranspose α

/-- The entries of a scalar conjugation `α⋆ X α`. -/
lemma scalarConj_apply (α : Matrix m n ℂ) (X : CStarMatrix m m V) (i j : n) :
    scalarConj α X i j = ∑ p, ∑ q, (star (α p i) * α q j) • X p q :=
  rfl

/-- Scalar conjugation commutes with applying a linear map entrywise. -/
lemma scalarConj_map (α : Matrix m n ℂ) (X : CStarMatrix m m V) (f : V →ₗ[ℂ] W) :
    (scalarConj α X).map f = scalarConj α (X.map f) :=
  scalarMul_map α.conjTranspose α X f

omit [Module ℂ V] [Fintype m] in
/-- An entry of a sum of matrices is the sum of the entries. This is `Matrix.sum_apply`, which does
not rewrite applications of a `CStarMatrix`. -/
lemma sum_apply {ι : Type*} (s : Finset ι) (f : ι → CStarMatrix m n V) (i : m) (j : n) :
    (∑ x ∈ s, f x) i j = ∑ x ∈ s, f x i j :=
  Matrix.sum_apply i j s f

/-- Conjugating by a scalar multiple `a • 1` of the identity matrix multiplies by `|a|²`. -/
lemma scalarConj_smul_one [DecidableEq m] (a : ℂ) (X : CStarMatrix m m V) :
    scalarConj (a • (1 : Matrix m m ℂ)) X = (star a * a) • X := by
  ext i j
  simp [scalarConj_apply, Matrix.one_apply, apply_ite (starRingEnd ℂ), ite_mul, ite_smul]

/-- The diagonal matrix with all diagonal entries `v` is the sum over `i` of the conjugations of
the `1 × 1` matrix `v` by the `i`-th unit row. -/
lemma diagonal_eq_sum_scalarConj [DecidableEq m] (v : V) :
    (ofMatrix (Matrix.of fun i j => if i = j then v else 0) : CStarMatrix m m V) =
      ∑ i, scalarConj (Matrix.of fun (_ : Fin 1) (j : m) => if j = i then (1 : ℂ) else 0)
        (ofMatrix (Matrix.of fun _ _ => v)) := by
  ext a b
  rw [sum_apply]
  change (if a = b then v else 0) = _
  simp only [scalarConj_apply, Matrix.of_apply]
  split_ifs with h <;> simp [h]

/-- Over a (possibly non-unital) C⋆-algebra, the conjugation `α⋆ X α` of a positive matrix `X` by a
scalar matrix is positive. The positive matrices are the additive closure of the `Y⋆ Y`
(`StarOrderedRing.le_iff`), and `α⋆ (Y⋆ Y) α = ∑_c Z_c⋆ Z_c` for the matrix `Z_c` whose only nonzero
row is `(∑_q α q b • Y c q)_b`. -/
lemma scalarConj_nonneg {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [Fintype n] (α : Matrix m n ℂ) {X : CStarMatrix m m A} (hX : 0 ≤ X) :
    0 ≤ scalarConj α X := by
  classical
  cases isEmpty_or_nonempty n with
  | inl _ => exact le_of_eq (ext fun i => isEmptyElim i)
  | inr hn =>
    obtain ⟨r₀⟩ := hn
    obtain ⟨P, hP, rfl⟩ := (StarOrderedRing.le_iff 0 X).mp hX
    clear hX
    rw [zero_add]
    induction hP using AddSubmonoid.closure_induction with
    | mem _ h =>
      obtain ⟨Y, rfl⟩ := h
      let Z : m → CStarMatrix n n A := fun c =>
        ofMatrix (Matrix.of fun r b => if r = r₀ then ∑ q, α q b • Y c q else 0)
      have hZ : scalarConj α (star Y * Y) = ∑ c, star (Z c) * Z c := by
        ext a b
        refine Eq.trans ?_ (map_sum (AddMonoidHom.mk' (fun M : CStarMatrix n n A => M a b)
          (fun _ _ => rfl)) _ _).symm
        change ∑ p, ∑ q, (star (α p a) * α q b) • ∑ c, star (Y c p) * Y c q =
          ∑ c, ∑ r, star (Z c r a) * Z c r b
        simp only [Z, ofMatrix_apply, Matrix.of_apply, apply_ite star, star_zero, ite_mul,
          zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, star_sum, star_smul,
          Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, Finset.smul_sum]
        conv_lhs => enter [2, p]; rw [Finset.sum_comm]
        rw [Finset.sum_comm]
      rw [hZ]
      exact Finset.sum_nonneg fun c _ => star_mul_self_nonneg _
    | zero => simp
    | add x y _ _ hx hy => simpa using add_nonneg hx hy

/-- The matrix `(Mᵢⱼ • v)ᵢⱼ` over `V` of a scalar matrix `M` and a vector `v`. -/
def smulRight {n : Type*} (M : CStarMatrix n n ℂ) (v : V) : CStarMatrix n n V :=
  M.map (· • v)

/-- The entries `Mᵢⱼ • v` of `smulRight M v`. -/
lemma smulRight_apply {n : Type*} (M : CStarMatrix n n ℂ) (v : V) (i j : n) :
    smulRight M v i j = M i j • v :=
  rfl

/-- `smulRight` is additive in the scalar matrix. -/
lemma smulRight_add_left {n : Type*} (M N : CStarMatrix n n ℂ) (v : V) :
    smulRight (M + N) v = smulRight M v + smulRight N v :=
  ext fun _ _ => add_smul _ _ v

/-- `smulRight` is additive in the vector. -/
lemma smulRight_add_right {n : Type*} (M : CStarMatrix n n ℂ) (v w : V) :
    smulRight M (v + w) = smulRight M v + smulRight M w :=
  ext fun _ _ => smul_add _ v w

/-- `smulRight` is ℂ-linear in the scalar matrix. -/
lemma smulRight_smul_left {n : Type*} (c : ℂ) (M : CStarMatrix n n ℂ) (v : V) :
    smulRight (c • M) v = c • smulRight M v :=
  ext fun i j => by
    change (c * M i j) • v = c • (M i j • v)
    exact (smul_smul c (M i j) v).symm

/-- A scalar factor of the vector moves to the scalar matrix. -/
lemma smulRight_smul_right {n : Type*} (c : ℂ) (M : CStarMatrix n n ℂ) (v : V) :
    smulRight M (c • v) = smulRight (c • M) v :=
  ext fun _ _ => (smul_smul _ c v).trans (congrArg (· • v) (mul_comm _ c))

/-- A matrix over `V` is the sum of `smulRight Eₚ_q Xₚ_q` over the scalar matrix units `Eₚ_q`. -/
lemma eq_sum_smulRight_single [DecidableEq m] (X : CStarMatrix m m V) :
    X = ∑ p, ∑ q, smulRight (ofMatrix (Matrix.single p q 1)) (X p q) := by
  ext i j
  simp only [sum_apply, smulRight_apply, ofMatrix_apply, Matrix.single_apply, ite_smul, one_smul,
    zero_smul, ite_and]
  simp

omit [Fintype m] in
/-- `star (smulRight M h) = smulRight (star M) h` for a self-adjoint `h`. -/
lemma star_smulRight [StarAddMonoid V] [StarModule ℂ V] (M : CStarMatrix m m ℂ) {h : V}
    (hh : IsSelfAdjoint h) : star (smulRight M h) = smulRight (star M) h :=
  ext fun i j => by
    change star (M j i • h) = star (M j i) • h
    rw [star_smul, hh.star_eq]

/-- The matrix `smulRight (B⋆ B) v` is the conjugation of the diagonal matrix with entries `v` by
the scalar matrix `B`. -/
lemma smulRight_star_mul_self [DecidableEq m] (B : CStarMatrix m m ℂ) (v : V) :
    smulRight (star B * B) v =
      scalarConj (ofMatrix.symm B) (ofMatrix (Matrix.of fun i j => if i = j then v else 0)) := by
  ext i j
  rw [smulRight_apply, scalarConj_apply, CStarMatrix.mul_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun p _ => ?_
  change (star (B p i) * B p j) • v = ∑ q, (star (B p i) * B q j) • (if p = q then v else 0)
  simp

end scalarConj

section OneByOne

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The `1 × 1` matrix with entry `a`. -/
abbrev single₁ {V : Type*} (a : V) : CStarMatrix (Fin 1) (Fin 1) V :=
  ofMatrix (Matrix.of fun _ _ => a)

/-- A `1 × 1` matrix over a C⋆-algebra is positive exactly when its entry is. Both directions are
inductions over the additive closure of the elements `x⋆ x` (`StarOrderedRing.le_iff`), using
`(Y⋆ Y) 0 0 = (Y 0 0)⋆ Y 0 0` for a `1 × 1` matrix `Y`. -/
lemma single₁_nonneg_iff {a : A} : 0 ≤ single₁ a ↔ 0 ≤ a := by
  have key : ∀ Y : CStarMatrix (Fin 1) (Fin 1) A, (star Y * Y) 0 0 = star (Y 0 0) * Y 0 0 := by
    intro Y
    change ∑ k, star (Y k 0) * Y k 0 = _
    simp
  constructor
  · intro h
    change 0 ≤ (single₁ a) 0 0
    obtain ⟨P, hP, hPa⟩ := (StarOrderedRing.le_iff 0 (single₁ a)).mp h
    rw [hPa, zero_add]
    clear hPa h
    induction hP using AddSubmonoid.closure_induction with
    | mem _ h =>
      obtain ⟨Y, rfl⟩ := h
      change 0 ≤ (star Y * Y) 0 0
      rw [key]
      exact star_mul_self_nonneg _
    | zero => exact le_rfl
    | add x y _ _ hx hy => exact add_nonneg hx hy
  · intro h
    obtain ⟨P, hP, rfl⟩ := (StarOrderedRing.le_iff 0 a).mp h
    rw [zero_add]
    clear h
    induction hP using AddSubmonoid.closure_induction with
    | mem _ h =>
      obtain ⟨b, rfl⟩ := h
      have : single₁ (star b * b) = star (single₁ b) * single₁ b := by
        ext i j
        rw [Subsingleton.elim i 0, Subsingleton.elim j 0, key]
        rfl
      rw [this]
      exact star_mul_self_nonneg _
    | zero => exact le_of_eq (ext fun _ _ => rfl)
    | add x y _ _ hx hy => exact (add_nonneg hx hy).trans_eq (ext fun _ _ => rfl)

end OneByOne

end CStarMatrix

/-! ### Matrix-ordered spaces and operator systems -/

open CStarMatrix

/-- A **matrix-ordered space**: a complex ⋆-vector space `V` with partial orders on the matrix spaces
`CStarMatrix (Fin k) (Fin k) V`, supplied as instances, such that every level is an ordered additive
group, positive elements are self-adjoint, conjugation by scalar matrices preserves positivity, and
the order at level `1` is the order of `V`. That positive matrices are self-adjoint at every level
follows (`MatrixOrdered.isSelfAdjoint_of_cstarMatrix_nonneg`). -/
class MatrixOrdered (V : Type*) [AddCommGroup V] [Module ℂ V] [StarAddMonoid V] [StarModule ℂ V]
    [PartialOrder V] [∀ k, PartialOrder (CStarMatrix (Fin k) (Fin k) V)] : Prop where
  /-- Each matrix level is an ordered additive group. -/
  isOrderedAddMonoid (k : ℕ) : IsOrderedAddMonoid (CStarMatrix (Fin k) (Fin k) V)
  /-- Positive elements are self-adjoint. -/
  isSelfAdjoint_of_nonneg {v : V} : 0 ≤ v → IsSelfAdjoint v
  /-- Conjugation `X ↦ α⋆ X α` by a scalar `k × l` matrix preserves positivity. -/
  scalarConj_nonneg {k l : ℕ} (α : Matrix (Fin k) (Fin l) ℂ) {X : CStarMatrix (Fin k) (Fin k) V} :
    0 ≤ X → 0 ≤ scalarConj α X
  /-- The order at level `1` is the order of `V`. -/
  le_iff_single₁_le (v w : V) : v ≤ w ↔ single₁ v ≤ single₁ w

/-- An **operator system**: a matrix-ordered space whose `1` is an Archimedean matrix order unit. The
unit is positive, each self-adjoint element lies below a real multiple of it, and at every level a
matrix is positive when adding any positive multiple of the identity matrix makes it positive. That
the identity matrix is an order unit at every level follows
(`OperatorSystem.exists_le_smul_one_of_isSelfAdjoint`). -/
class OperatorSystem (V : Type*) [AddCommGroup V] [Module ℂ V] [StarAddMonoid V] [StarModule ℂ V]
    [PartialOrder V] [∀ k, PartialOrder (CStarMatrix (Fin k) (Fin k) V)] [One V] : Prop
    extends MatrixOrdered V where
  /-- The unit is positive. -/
  zero_le_one' : (0 : V) ≤ 1
  /-- The unit is an order unit: each self-adjoint element lies below a multiple of it. -/
  exists_le_smul_one {v : V} : IsSelfAdjoint v → ∃ r : ℝ, v ≤ (r : ℂ) • 1
  /-- The order unit is Archimedean at every level. -/
  nonneg_of_forall_add_smul_one_nonneg {k : ℕ} {X : CStarMatrix (Fin k) (Fin k) V} :
    (∀ ε : ℝ, 0 < ε → 0 ≤ X + (ε : ℂ) • 1) → 0 ≤ X

attribute [instance] MatrixOrdered.isOrderedAddMonoid

namespace MatrixOrdered

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [StarAddMonoid V] [StarModule ℂ V]
  [PartialOrder V] [∀ k, PartialOrder (CStarMatrix (Fin k) (Fin k) V)] [MatrixOrdered V]

/-- The order of a matrix-ordered space is compatible with addition, as the order at level `1`
is. -/
instance instIsOrderedAddMonoid : IsOrderedAddMonoid V where
  add_le_add_left v w h u := by
    rw [le_iff_single₁_le] at h ⊢
    have := add_le_add_left h (single₁ u)
    exact (le_of_eq (ext fun _ _ => rfl)).trans (this.trans_eq (ext fun _ _ => rfl))

/-- A `1 × 1` matrix is positive exactly when its entry is. -/
lemma single₁_nonneg_iff' {v : V} : 0 ≤ single₁ v ↔ 0 ≤ v := by
  rw [le_iff_single₁_le 0 v]
  exact Iff.of_eq (congrArg (· ≤ single₁ v) (ext fun _ _ => rfl))

/-- Multiplying a positive matrix by a nonnegative real keeps it positive: it is the scalar
conjugation by `√c` times the identity matrix. -/
lemma smul_nonneg_of_nonneg {k : ℕ} {c : ℝ} (hc : 0 ≤ c) {X : CStarMatrix (Fin k) (Fin k) V}
    (hX : 0 ≤ X) : 0 ≤ (c : ℂ) • X := by
  classical
  have := scalarConj_nonneg ((Real.sqrt c : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ)) hX
  rwa [scalarConj_smul_one, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Real.mul_self_sqrt hc] at this

/-- Multiplying a positive element by a nonnegative real keeps it positive. -/
lemma smul_nonneg_of_nonneg' {c : ℝ} (hc : 0 ≤ c) {v : V} (hv : 0 ≤ v) : 0 ≤ (c : ℂ) • v := by
  rw [← single₁_nonneg_iff'] at hv ⊢
  exact (smul_nonneg_of_nonneg hc hv).trans_eq (ext fun _ _ => rfl)

/-- The quadratic form `∑ₚ_q conj(αₚ) α_q Xₚ_q` of a positive matrix `X` is positive: it is the entry
of the compression `α⋆ X α` to level `1`. -/
lemma sum_smul_nonneg {k : ℕ} {X : CStarMatrix (Fin k) (Fin k) V} (hX : 0 ≤ X) (α : Fin k → ℂ) :
    0 ≤ ∑ p, ∑ q, (star (α p) * α q) • X p q := by
  have h := scalarConj_nonneg (Matrix.of fun p (_ : Fin 1) => α p) hX
  rwa [show scalarConj (Matrix.of fun p (_ : Fin 1) => α p) X =
      single₁ (∑ p, ∑ q, (star (α p) * α q) • X p q) from ext fun i j => by
        rw [Subsingleton.elim i 0, Subsingleton.elim j 0]; rfl, single₁_nonneg_iff'] at h

omit [PartialOrder V] [∀ k, PartialOrder (CStarMatrix (Fin k) (Fin k) V)] [MatrixOrdered V] in
/-- If `a + b` and `i a - i b` are self-adjoint, then `a⋆ = b`. -/
private lemma star_eq_of_isSelfAdjoint {a b : V} (h₁ : IsSelfAdjoint (a + b))
    (h₂ : IsSelfAdjoint (Complex.I • a - Complex.I • b)) : star a = b := by
  have e₁ := h₁.star_eq
  have e₂ := h₂.star_eq
  simp only [star_add, star_sub, star_smul, Complex.star_def, Complex.conj_I] at e₁ e₂
  have e₃ := congrArg (Complex.I • ·) e₂
  simp only [smul_sub, smul_smul, neg_smul, Complex.I_mul_I, smul_neg, neg_neg, one_smul] at e₃
  refine smul_right_injective V (two_ne_zero : (2 : ℂ) ≠ 0) ?_
  calc (2 : ℂ) • star a = (star a + star b) + (star a - star b) := by module
    _ = (a + b) + (-a - -b) := by rw [e₁, e₃]
    _ = (2 : ℂ) • b := by module

/-- Positive matrices are self-adjoint at every level. The compressions
`Xᵢᵢ + c Xᵢⱼ + c̄ Xⱼᵢ + |c|² Xⱼⱼ` of a positive matrix to level `1` along `eᵢ + c eⱼ` are positive, hence
self-adjoint; `c = 0`, `c = 1` and `c = i` give `Xⱼᵢ⋆ = Xᵢⱼ`. -/
lemma isSelfAdjoint_of_cstarMatrix_nonneg {k : ℕ} {X : CStarMatrix (Fin k) (Fin k) V}
    (hX : 0 ≤ X) : IsSelfAdjoint X := by
  classical
  have hq : ∀ (i j : Fin k) (c : ℂ),
      IsSelfAdjoint (X i i + c • X i j + star c • X j i + (star c * c) • X j j) := by
    intro i j c
    have := isSelfAdjoint_of_nonneg (sum_smul_nonneg hX (Pi.single i 1 + c • Pi.single j 1))
    convert this using 1
    simp [Pi.single_apply, add_mul, mul_add, add_smul, Finset.sum_add_distrib, apply_ite star,
      ite_smul]
    abel
  have hd : ∀ i, IsSelfAdjoint (X i i) := fun i => by simpa using hq i i 0
  refine ext fun i j => ?_
  change star (X j i) = X i j
  refine star_eq_of_isSelfAdjoint ?_ ?_
  · have := ((hq j i 1).sub (hd j)).sub (hd i)
    convert this using 1
    simp only [one_smul, star_one, mul_one]
    abel
  · have := ((hq j i Complex.I).sub (hd j)).sub (hd i)
    convert this using 1
    simp only [Complex.star_def, Complex.conj_I, neg_mul, Complex.I_mul_I, neg_neg, one_smul,
      neg_smul]
    abel

end MatrixOrdered

namespace OperatorSystem

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [StarAddMonoid V] [StarModule ℂ V]
  [PartialOrder V] [∀ k, PartialOrder (CStarMatrix (Fin k) (Fin k) V)] [One V] [OperatorSystem V]

open MatrixOrdered

/-- The identity matrix at level `k` is positive: it is the sum over `i` of the conjugations of the
positive `1 × 1` matrix `1` by the `i`-th unit row. -/
lemma one_nonneg (k : ℕ) : 0 ≤ (1 : CStarMatrix (Fin k) (Fin k) V) := by
  classical
  have h₁ : 0 ≤ single₁ (1 : V) := single₁_nonneg_iff'.mpr zero_le_one'
  rw [show (1 : CStarMatrix (Fin k) (Fin k) V) = ofMatrix (Matrix.of fun i j => if i = j then 1 else 0)
    from ext fun _ _ => rfl, diagonal_eq_sum_scalarConj]
  exact Finset.sum_nonneg fun i _ => scalarConj_nonneg _ h₁

/-- A self-adjoint element lies between `-r` and `r` times the unit for some `r ≥ 0`. -/
lemma exists_abs_le_smul_one' {a : V} (ha : IsSelfAdjoint a) :
    ∃ r : ℝ, 0 ≤ r ∧ -((r : ℂ) • 1) ≤ a ∧ a ≤ (r : ℂ) • 1 := by
  obtain ⟨r₁, h₁⟩ := exists_le_smul_one ha
  obtain ⟨r₂, h₂⟩ := exists_le_smul_one ha.neg
  refine ⟨max (max r₁ r₂) 0, le_max_right _ _, ?_, ?_⟩
  · refine neg_le.mp (h₂.trans ?_)
    rw [← sub_nonneg, ← sub_smul, ← Complex.ofReal_sub]
    exact smul_nonneg_of_nonneg' (by simp) zero_le_one'
  · refine h₁.trans ?_
    rw [← sub_nonneg, ← sub_smul, ← Complex.ofReal_sub]
    exact smul_nonneg_of_nonneg' (by simp) zero_le_one'

/-- `smulRight P v` is positive for a positive scalar matrix `P` and a positive `v`: for `P = B⋆ B` it
is the conjugation by `B` of the positive diagonal matrix with entries `v`, and the positive scalar
matrices are the additive closure of the `B⋆ B`. -/
lemma smulRight_nonneg {k : ℕ} {P : CStarMatrix (Fin k) (Fin k) ℂ} (hP : 0 ≤ P) {v : V}
    (hv : 0 ≤ v) : 0 ≤ smulRight P v := by
  classical
  obtain ⟨Q, hQ, rfl⟩ := (StarOrderedRing.le_iff 0 P).mp hP
  rw [zero_add]
  clear hP
  induction hQ using AddSubmonoid.closure_induction with
  | mem _ h =>
    obtain ⟨B, rfl⟩ := h
    rw [smulRight_star_mul_self, diagonal_eq_sum_scalarConj, map_sum]
    exact Finset.sum_nonneg fun i _ => scalarConj_nonneg _
      (scalarConj_nonneg _ (single₁_nonneg_iff'.mpr hv))
  | zero => exact le_of_eq (ext fun _ _ => (zero_smul ℂ v).symm)
  | add x y _ _ hx hy =>
    exact (add_nonneg hx hy).trans_eq (ext fun _ _ => (add_smul _ _ v).symm)

/-- `smulRight M h ≤ r ‖M‖ • 1` for a self-adjoint scalar matrix `M` and `-r • 1 ≤ h ≤ r • 1`. With
`P = ‖M‖ • 1 + M ≥ 0` and `N = ‖M‖ • 1 - M ≥ 0`, the difference `r ‖M‖ • 1 - smulRight M h` is
`(smulRight P (r • 1 - h) + smulRight N (r • 1 + h)) / 2`. -/
lemma smulRight_le {k : ℕ} {M : CStarMatrix (Fin k) (Fin k) ℂ} (hM : IsSelfAdjoint M) {h : V}
    {r : ℝ} (h₁ : -((r : ℂ) • 1) ≤ h) (h₂ : h ≤ (r : ℂ) • 1) :
    smulRight M h ≤ ((r * ‖M‖ : ℝ) : ℂ) • 1 := by
  classical
  have hP : 0 ≤ (‖M‖ : ℂ) • 1 + M := by
    have := hM.neg.le_algebraMap_norm_self
    rw [norm_neg, Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul] at this
    exact neg_le_iff_add_nonneg'.mp this |>.trans_eq (add_comm _ _)
  have hN : 0 ≤ (‖M‖ : ℂ) • 1 - M := by
    have := hM.le_algebraMap_norm_self
    rw [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul] at this
    exact sub_nonneg.mpr this
  have key : ((r * ‖M‖ : ℝ) : ℂ) • (1 : CStarMatrix (Fin k) (Fin k) V) - smulRight M h =
      ((1 / 2 : ℝ) : ℂ) • (smulRight ((‖M‖ : ℂ) • 1 + M) ((r : ℂ) • 1 - h) +
        smulRight ((‖M‖ : ℂ) • 1 - M) ((r : ℂ) • 1 + h)) := by
    ext i j
    change ((r * ‖M‖ : ℝ) : ℂ) • (if i = j then (1 : V) else 0) - M i j • h =
      ((1 / 2 : ℝ) : ℂ) • ((((‖M‖ : ℂ) • (if i = j then (1 : ℂ) else 0)) + M i j) • ((r : ℂ) • 1 - h) +
        (((‖M‖ : ℂ) • (if i = j then (1 : ℂ) else 0)) - M i j) • ((r : ℂ) • 1 + h))
    split_ifs
    · push_cast
      module
    · push_cast
      module
  rw [← sub_nonneg, key]
  exact smul_nonneg_of_nonneg (by norm_num) (add_nonneg
    (smulRight_nonneg hP (sub_nonneg.mpr h₂)) (smulRight_nonneg hN (neg_le_iff_add_nonneg'.mp h₁)))

/-- **The identity matrix is an order unit at every level.** A self-adjoint matrix `X` is
`∑ₚ_q (smulRight Aₚ_q (ℜ Xₚ_q) + smulRight Bₚ_q (ℑ Xₚ_q))` for the self-adjoint scalar matrices
`Aₚ_q = (Eₚ_q + E_qₚ) / 2` and `Bₚ_q = i (Eₚ_q - E_qₚ) / 2`, and each term lies below a multiple of the
identity matrix (`OperatorSystem.smulRight_le`). -/
lemma exists_le_smul_one_of_isSelfAdjoint {k : ℕ} {X : CStarMatrix (Fin k) (Fin k) V}
    (hX : IsSelfAdjoint X) : ∃ r : ℝ, X ≤ (r : ℂ) • 1 := by
  classical
  let E : Fin k → Fin k → CStarMatrix (Fin k) (Fin k) ℂ := fun p q => ofMatrix (Matrix.single p q 1)
  let A : Fin k → Fin k → CStarMatrix (Fin k) (Fin k) ℂ := fun p q =>
    ((1 / 2 : ℝ) : ℂ) • (E p q + star (E p q))
  let B : Fin k → Fin k → CStarMatrix (Fin k) (Fin k) ℂ := fun p q =>
    ((1 / 2 : ℝ) : ℂ) • (Complex.I • E p q + star (Complex.I • E p q))
  have hA : ∀ p q, IsSelfAdjoint (A p q) := fun p q =>
    IsSelfAdjoint.smul (Complex.conj_ofReal _) (IsSelfAdjoint.add_star_self (E p q))
  have hB : ∀ p q, IsSelfAdjoint (B p q) := fun p q =>
    IsSelfAdjoint.smul (Complex.conj_ofReal _) (IsSelfAdjoint.add_star_self (Complex.I • E p q))
  have hsum : X = ∑ p, ∑ q, (smulRight (E p q) (ℜ (X p q) : V) +
      smulRight (Complex.I • E p q) (ℑ (X p q) : V)) := by
    conv_lhs => rw [eq_sum_smulRight_single X]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    conv_lhs => rw [← realPart_add_I_smul_imaginaryPart (X p q)]
    rw [smulRight_add_right, smulRight_smul_right]
  have hstar : star X = ∑ p, ∑ q, (smulRight (star (E p q)) (ℜ (X p q) : V) +
      smulRight (star (Complex.I • E p q)) (ℑ (X p q) : V)) := by
    have hre : ∀ a : V, IsSelfAdjoint (ℜ a : V) := fun a => (ℜ a).2
    have him : ∀ a : V, IsSelfAdjoint (ℑ a : V) := fun a => (ℑ a).2
    conv_lhs => rw [hsum]
    simp only [star_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [star_add, star_smulRight _ (hre _), star_smulRight _ (him _)]
  have hdecomp : X = ∑ p, ∑ q, (smulRight (A p q) (ℜ (X p q) : V) +
      smulRight (B p q) (ℑ (X p q) : V)) := by
    calc X = ((1 / 2 : ℝ) : ℂ) • (X + star X) := by
          rw [hX.star_eq, ← two_smul ℂ X, smul_smul]
          norm_num
      _ = _ := by
          conv_lhs => rw [hstar]; enter [2, 1]; rw [hsum]
          rw [← Finset.sum_add_distrib, Finset.smul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [← Finset.sum_add_distrib, Finset.smul_sum]
          refine Finset.sum_congr rfl fun q _ => ?_
          simp only [A, B, smulRight_smul_left, smulRight_add_left]
          module
  choose r hr using fun p q => exists_abs_le_smul_one' (ℜ (X p q)).2
  choose s hs using fun p q => exists_abs_le_smul_one' (ℑ (X p q)).2
  refine ⟨∑ p, ∑ q, (r p q * ‖A p q‖ + s p q * ‖B p q‖), ?_⟩
  rw [hdecomp, Complex.ofReal_sum, Finset.sum_smul]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [Complex.ofReal_sum, Finset.sum_smul]
  refine Finset.sum_le_sum fun q _ => ?_
  rw [Complex.ofReal_add, add_smul]
  exact add_le_add (smulRight_le (hA p q) (hr p q).2.1 (hr p q).2.2)
    (smulRight_le (hB p q) (hs p q).2.1 (hs p q).2.2)

/-- A self-adjoint matrix lies between `-r` and `r` times the identity matrix for some `r ≥ 0`. -/
lemma exists_abs_le_smul_one {k : ℕ} {X : CStarMatrix (Fin k) (Fin k) V} (hX : IsSelfAdjoint X) :
    ∃ r : ℝ, 0 ≤ r ∧ -((r : ℂ) • 1) ≤ X ∧ X ≤ (r : ℂ) • 1 := by
  obtain ⟨r₁, h₁⟩ := exists_le_smul_one_of_isSelfAdjoint hX
  obtain ⟨r₂, h₂⟩ := exists_le_smul_one_of_isSelfAdjoint hX.neg
  refine ⟨max (max r₁ r₂) 0, le_max_right _ _, ?_, ?_⟩
  · refine neg_le.mp (h₂.trans ?_)
    rw [← sub_nonneg, ← sub_smul, ← Complex.ofReal_sub]
    exact smul_nonneg_of_nonneg (by simp) (one_nonneg k)
  · refine h₁.trans ?_
    rw [← sub_nonneg, ← sub_smul, ← Complex.ofReal_sub]
    exact smul_nonneg_of_nonneg (by simp) (one_nonneg k)

end OperatorSystem

/-! ### C⋆-algebras as operator systems -/

namespace CStarAlgebra

/-- A (possibly non-unital) C⋆-algebra, with the order of `CStarMatrix (Fin k) (Fin k) A` that Mathlib
derives from its C⋆-structure, is matrix-ordered. -/
instance instMatrixOrdered {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] : MatrixOrdered A where
  isOrderedAddMonoid _ := inferInstance
  isSelfAdjoint_of_nonneg h := IsSelfAdjoint.of_nonneg h
  scalarConj_nonneg := fun {_ _} α {_} h => CStarMatrix.scalarConj_nonneg α h
  le_iff_single₁_le v w := by
    rw [← sub_nonneg, ← sub_nonneg (a := single₁ w), ← single₁_nonneg_iff]
    exact Iff.rfl

/-- In a unital C⋆-algebra, `a` is positive when `a + ε • 1` is for every `ε > 0`, since the positive
elements form a closed set. -/
lemma nonneg_of_forall_add_smul_one_nonneg {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {a : A} (h : ∀ ε : ℝ, 0 < ε → 0 ≤ a + (ε : ℂ) • 1) : 0 ≤ a := by
  have hlim : Filter.Tendsto (fun ε : ℝ => a + (ε : ℂ) • (1 : A)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds a) := by
    have : Filter.Tendsto (fun ε : ℝ => a + (ε : ℂ) • (1 : A)) (nhds 0)
        (nhds (a + ((0 : ℝ) : ℂ) • 1)) :=
      tendsto_const_nhds.add ((Complex.continuous_ofReal.tendsto 0).smul tendsto_const_nhds)
    simpa using this.mono_left nhdsWithin_le_nhds
  exact isClosed_Ici.mem_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε => h ε hε)

/-- A unital C⋆-algebra is an operator system, with order unit `1`: a self-adjoint `a` lies below
`‖a‖ • 1`, and the positive matrices form a closed set. -/
instance instOperatorSystem {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] :
    OperatorSystem A where
  zero_le_one' := zero_le_one
  exists_le_smul_one {a} ha := by
    refine ⟨‖a‖, ?_⟩
    have := IsSelfAdjoint.le_algebraMap_norm_self a ha
    rwa [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul] at this
  nonneg_of_forall_add_smul_one_nonneg h := CStarAlgebra.nonneg_of_forall_add_smul_one_nonneg h

end CStarAlgebra

/-! ### Operator subsystems -/

/-- An **operator subsystem** of `T`: a complex subspace of `T` closed under `star` and containing
`1`. Within an operator system `T` it is an operator system with the matrix orders of `T`
(`OperatorSubsystem.instOperatorSystem`). -/
structure OperatorSubsystem (T : Type*) [AddCommGroup T] [Module ℂ T] [StarAddMonoid T] [One T]
    extends Submodule ℂ T where
  /-- The subspace is closed under `star`. -/
  star_mem' {x : T} : x ∈ carrier → star x ∈ carrier
  /-- The subspace contains `1`. -/
  one_mem' : (1 : T) ∈ carrier

namespace OperatorSubsystem

variable {T : Type*} [AddCommGroup T] [Module ℂ T] [StarAddMonoid T] [One T]

instance : SetLike (OperatorSubsystem T) T where
  coe S := S.carrier
  coe_injective S S' h := by
    obtain ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _, _⟩ := S
    obtain ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _, _⟩ := S'
    congr

instance : AddSubgroupClass (OperatorSubsystem T) T where
  add_mem {S} := S.add_mem'
  zero_mem S := S.zero_mem'
  neg_mem {S} _ hx := S.toSubmodule.neg_mem hx

instance : SMulMemClass (OperatorSubsystem T) ℂ T where
  smul_mem {S} c _ hx := S.smul_mem' c hx

instance : StarMemClass (OperatorSubsystem T) T where
  star_mem {S} _ hx := S.star_mem' hx

instance : OneMemClass (OperatorSubsystem T) T where
  one_mem S := S.one_mem'

/-- The whole space, as an operator subsystem of itself. -/
instance : Top (OperatorSubsystem T) :=
  ⟨{ (⊤ : Submodule ℂ T) with
    star_mem' := fun _ => trivial
    one_mem' := trivial }⟩

/-- Every element lies in the operator subsystem `⊤`. -/
@[simp] lemma mem_top (x : T) : x ∈ (⊤ : OperatorSubsystem T) := trivial

/-- Operator subsystems with the same elements are equal. -/
@[ext]
lemma ext {S S' : OperatorSubsystem T} (h : ∀ x, x ∈ S ↔ x ∈ S') : S = S' := SetLike.ext h

/-- Membership in the underlying subspace is membership in the operator subsystem. -/
@[simp]
lemma mem_toSubmodule {S : OperatorSubsystem T} {x : T} : x ∈ S.toSubmodule ↔ x ∈ S := Iff.rfl

variable [PartialOrder T] [∀ k, PartialOrder (CStarMatrix (Fin k) (Fin k) T)] (S : OperatorSubsystem T)

/-- The matrix orders of an operator subsystem are those of the ambient space: a matrix over `S`
is positive when it is positive as a matrix over `T`. -/
instance instPartialOrderCStarMatrix (k : ℕ) : PartialOrder (CStarMatrix (Fin k) (Fin k) S) :=
  PartialOrder.lift (fun X => X.map Subtype.val) fun _ _ h =>
    CStarMatrix.ext fun i j => Subtype.val_injective (congrFun (congrFun h i) j)

variable {S}

omit [PartialOrder T] in
/-- Matrices over an operator subsystem are ordered as matrices over the ambient space. -/
lemma cstarMatrix_le_iff {k : ℕ} {X Y : CStarMatrix (Fin k) (Fin k) S} :
    X ≤ Y ↔ X.map Subtype.val ≤ Y.map Subtype.val :=
  Iff.rfl

omit [PartialOrder T] in
/-- A matrix over an operator subsystem is positive when it is positive over the ambient space. -/
lemma cstarMatrix_nonneg_iff {k : ℕ} {X : CStarMatrix (Fin k) (Fin k) S} :
    0 ≤ X ↔ 0 ≤ X.map Subtype.val :=
  Iff.rfl

variable [StarModule ℂ T]

/-- An operator subsystem of a matrix-ordered space is matrix-ordered: every axiom transfers along
the entrywise inclusion `X ↦ X.map Subtype.val`, which is injective, additive and commutes with
`star` and with scalar conjugation. -/
instance instMatrixOrdered [MatrixOrdered T] : MatrixOrdered S where
  isOrderedAddMonoid k :=
    { add_le_add_left := fun X Y h Z => by
        rw [cstarMatrix_le_iff] at h ⊢
        exact (add_le_add_left h (Z.map Subtype.val)).trans_eq' rfl }
  isSelfAdjoint_of_nonneg {_} h := Subtype.val_injective (MatrixOrdered.isSelfAdjoint_of_nonneg (V := T) h)
  scalarConj_nonneg := fun {_ _} α {X} h => by
    rw [cstarMatrix_nonneg_iff, show (scalarConj α X).map Subtype.val =
      scalarConj α (X.map Subtype.val) from scalarConj_map α X (S.toSubmodule.subtype)]
    exact MatrixOrdered.scalarConj_nonneg α (cstarMatrix_nonneg_iff.mp h)
  le_iff_single₁_le v w := MatrixOrdered.le_iff_single₁_le (v : T) w

omit [PartialOrder T] [∀ k, PartialOrder (CStarMatrix (Fin k) (Fin k) T)] [StarModule ℂ T] in
/-- The inclusion of an operator subsystem sends a multiple of the identity matrix to the same
multiple of the identity matrix. -/
lemma map_val_smul_one {k : ℕ} (c : ℂ) :
    ((c • 1 : CStarMatrix (Fin k) (Fin k) S)).map Subtype.val = c • 1 := by
  refine CStarMatrix.ext fun i j => ?_
  change ((c • (1 : Matrix (Fin k) (Fin k) S) i j : S) : T) = c • (1 : Matrix (Fin k) (Fin k) T) i j
  by_cases h : i = j <;> simp [h, Matrix.one_apply]

/-- An operator subsystem of an operator system is an operator system, with the same unit. -/
instance instOperatorSystem [OperatorSystem T] : OperatorSystem S where
  zero_le_one' := OperatorSystem.zero_le_one' (V := T)
  exists_le_smul_one {v} hv := by
    obtain ⟨r, hr⟩ := OperatorSystem.exists_le_smul_one (V := T) (congrArg Subtype.val hv)
    exact ⟨r, hr⟩
  nonneg_of_forall_add_smul_one_nonneg {k X} h :=
    OperatorSystem.nonneg_of_forall_add_smul_one_nonneg (V := T) fun ε hε => by
      have := cstarMatrix_nonneg_iff.mp (h ε hε)
      rwa [show (X + (ε : ℂ) • 1).map Subtype.val =
        X.map Subtype.val + ((ε : ℂ) • 1 : CStarMatrix (Fin k) (Fin k) S).map Subtype.val from rfl,
        map_val_smul_one] at this

end OperatorSubsystem

/-! ### Completely positive maps between matrix-ordered spaces -/

/-- A linear map `φ : A₁ →ₗ[ℂ] A₂` between complex vector spaces with matrix orders is
**completely positive** if applying it entrywise to a positive `k × k` matrix gives a positive
matrix, for every `k`. This is Mathlib's `CompletelyPositiveMap` with only the matrix orders
assumed; between C⋆-algebras the two agree definitionally
(`CompletelyPositiveMap'.equivCompletelyPositiveMap`). -/
structure CompletelyPositiveMap' (A₁ : Type*) (A₂ : Type*) [AddCommMonoid A₁] [Module ℂ A₁]
    [AddCommMonoid A₂] [Module ℂ A₂] [∀ k, PartialOrder (CStarMatrix (Fin k) (Fin k) A₁)]
    [∀ k, PartialOrder (CStarMatrix (Fin k) (Fin k) A₂)] extends A₁ →ₗ[ℂ] A₂ where
  map_cstarMatrix_nonneg' (k : ℕ) (M : CStarMatrix (Fin k) (Fin k) A₁) (hM : 0 ≤ M) :
    0 ≤ M.map toLinearMap

/-- The morphism class of completely positive maps between spaces with matrix orders. As
Mathlib's `CompletelyPositiveMapClass`, it records only the order property and is meant to be used
together with `LinearMapClass`. -/
class CompletelyPositiveMapClass' (F : Type*) (A₁ : Type*) (A₂ : Type*) [AddCommMonoid A₁]
    [Module ℂ A₁] [AddCommMonoid A₂] [Module ℂ A₂] [∀ k, PartialOrder (CStarMatrix (Fin k) (Fin k) A₁)]
    [∀ k, PartialOrder (CStarMatrix (Fin k) (Fin k) A₂)] [FunLike F A₁ A₂] : Prop where
  map_cstarMatrix_nonneg' (φ : F) (k : ℕ) (M : CStarMatrix (Fin k) (Fin k) A₁) (hM : 0 ≤ M) :
    0 ≤ M.map φ

/-- Notation for a `CompletelyPositiveMap'`. -/
scoped[CStarAlgebra] notation:25 A₁ " →CP' " A₂:0 => CompletelyPositiveMap' A₁ A₂

section Defs

variable {A₁ A₂ A₃ : Type*} [AddCommMonoid A₁] [Module ℂ A₁] [AddCommMonoid A₂] [Module ℂ A₂]
  [AddCommMonoid A₃] [Module ℂ A₃] [∀ k, PartialOrder (CStarMatrix (Fin k) (Fin k) A₁)]
  [∀ k, PartialOrder (CStarMatrix (Fin k) (Fin k) A₂)]
  [∀ k, PartialOrder (CStarMatrix (Fin k) (Fin k) A₃)]

namespace CompletelyPositiveMapClass'

variable {F : Type*} [FunLike F A₁ A₂] [LinearMapClass F ℂ A₁ A₂]

/-- Reinterpret an element of a type of completely positive maps as a completely positive linear
map. -/
@[coe]
def toCompletelyPositiveMap' [CompletelyPositiveMapClass' F A₁ A₂] (f : F) : A₁ →CP' A₂ :=
  { (f : A₁ →ₗ[ℂ] A₂) with
    map_cstarMatrix_nonneg' := CompletelyPositiveMapClass'.map_cstarMatrix_nonneg' f }

instance [CompletelyPositiveMapClass' F A₁ A₂] : CoeHead F (A₁ →CP' A₂) where
  coe f := toCompletelyPositiveMap' f

end CompletelyPositiveMapClass'

namespace CompletelyPositiveMap'

instance : FunLike (A₁ →CP' A₂) A₁ A₂ where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective
    exact h

instance : LinearMapClass (A₁ →CP' A₂) ℂ A₁ A₂ where
  map_add f := map_add f.toLinearMap
  map_smulₛₗ f := map_smulₛₗ f.toLinearMap

instance : CompletelyPositiveMapClass' (A₁ →CP' A₂) A₁ A₂ where
  map_cstarMatrix_nonneg' f := f.map_cstarMatrix_nonneg'

/-- The underlying linear map of `φ` is `φ` as a function. -/
@[simp] lemma coe_toLinearMap (φ : A₁ →CP' A₂) : ⇑φ.toLinearMap = φ := rfl

/-- Completely positive maps are equal if they agree at every point. -/
@[ext] lemma ext {φ ψ : A₁ →CP' A₂} (h : ∀ a, φ a = ψ a) : φ = ψ := DFunLike.ext _ _ h

/-- A completely positive map is determined by its underlying linear map. -/
lemma toLinearMap_injective : Function.Injective (toLinearMap : (A₁ →CP' A₂) → A₁ →ₗ[ℂ] A₂) :=
  fun _ _ h => ext fun a => LinearMap.congr_fun h a

/-- A completely positive map sends positive `k × k` matrices to positive matrices. -/
lemma map_cstarMatrix_nonneg (φ : A₁ →CP' A₂) {k : ℕ} {M : CStarMatrix (Fin k) (Fin k) A₁}
    (hM : 0 ≤ M) : 0 ≤ M.map φ :=
  φ.map_cstarMatrix_nonneg' k M hM

variable (A₁) in
/-- The identity map is completely positive. -/
protected def id : A₁ →CP' A₁ where
  toLinearMap := LinearMap.id
  map_cstarMatrix_nonneg' _ _ hM := by simpa using hM

/-- The identity completely positive map is the identity function. -/
@[simp] lemma coe_id : ⇑(CompletelyPositiveMap'.id A₁) = id := rfl

/-- The composition `ψ ∘ φ` of completely positive maps is completely positive: applying it
entrywise to a matrix is applying `φ` and then `ψ`. -/
def comp (ψ : A₂ →CP' A₃) (φ : A₁ →CP' A₂) : A₁ →CP' A₃ where
  toLinearMap := ψ.toLinearMap ∘ₗ φ.toLinearMap
  map_cstarMatrix_nonneg' k M hM :=
    ψ.map_cstarMatrix_nonneg' k _ (φ.map_cstarMatrix_nonneg' k M hM)

/-- The composition `ψ.comp φ` is `ψ ∘ φ` as a function. -/
@[simp] lemma coe_comp (ψ : A₂ →CP' A₃) (φ : A₁ →CP' A₂) : ⇑(ψ.comp φ) = ψ ∘ φ := rfl

/-- The composition `ψ.comp φ` sends `a` to `ψ (φ a)`. -/
lemma comp_apply (ψ : A₂ →CP' A₃) (φ : A₁ →CP' A₂) (a : A₁) : ψ.comp φ a = ψ (φ a) := rfl

/-- Composing with the identity on the right does nothing. -/
@[simp] lemma comp_id (φ : A₁ →CP' A₂) : φ.comp (CompletelyPositiveMap'.id A₁) = φ := rfl

/-- Composing with the identity on the left does nothing. -/
@[simp] lemma id_comp (φ : A₁ →CP' A₂) : (CompletelyPositiveMap'.id A₂).comp φ = φ := rfl

/-- Composition of completely positive maps is associative. -/
lemma comp_assoc {A₄ : Type*} [AddCommMonoid A₄] [Module ℂ A₄]
    [∀ k, PartialOrder (CStarMatrix (Fin k) (Fin k) A₄)] (χ : A₃ →CP' A₄) (ψ : A₂ →CP' A₃)
    (φ : A₁ →CP' A₂) : (χ.comp ψ).comp φ = χ.comp (ψ.comp φ) := rfl

end CompletelyPositiveMap'

end Defs

namespace CompletelyPositiveMapClass'

variable {F A₁ A₂ : Type*} [AddCommGroup A₁] [Module ℂ A₁] [StarAddMonoid A₁] [StarModule ℂ A₁]
  [PartialOrder A₁] [∀ k, PartialOrder (CStarMatrix (Fin k) (Fin k) A₁)] [MatrixOrdered A₁]
  [AddCommGroup A₂] [Module ℂ A₂] [StarAddMonoid A₂] [StarModule ℂ A₂] [PartialOrder A₂]
  [∀ k, PartialOrder (CStarMatrix (Fin k) (Fin k) A₂)] [MatrixOrdered A₂] [FunLike F A₁ A₂]
  [LinearMapClass F ℂ A₁ A₂] [CompletelyPositiveMapClass' F A₁ A₂]

/-- Completely positive maps between matrix-ordered spaces are positive: the order at level `1` is
the order of the space. -/
instance instOrderHomClass : OrderHomClass F A₁ A₂ := .of_addMonoidHom fun φ a ha => by
  have h₀ := (MatrixOrdered.le_iff_single₁_le 0 a).mp ha
  have h := map_cstarMatrix_nonneg' (A₂ := A₂) φ 1 _ (sub_nonneg.mpr h₀)
  rw [MatrixOrdered.le_iff_single₁_le, ← sub_nonneg]
  convert h using 1
  exact CStarMatrix.ext fun _ _ => by simp [CStarMatrix.map]; rfl

end CompletelyPositiveMapClass'

/-! ### Mathlib's completely positive maps -/

section CStarAlgebra

variable {F A₁ A₂ : Type*} [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂] [PartialOrder A₁]
  [PartialOrder A₂] [StarOrderedRing A₁] [StarOrderedRing A₂]

/-- Mathlib's completely positive maps between C⋆-algebras are completely positive maps between
the underlying matrix-ordered spaces. -/
instance CompletelyPositiveMapClass.instCompletelyPositiveMapClass' [FunLike F A₁ A₂]
    [CompletelyPositiveMapClass F A₁ A₂] : CompletelyPositiveMapClass' F A₁ A₂ where
  map_cstarMatrix_nonneg' := CompletelyPositiveMapClass.map_cstarMatrix_nonneg'

namespace CompletelyPositiveMap'

/-- Between C⋆-algebras, completely positive maps of matrix-ordered spaces are Mathlib's completely
positive maps; both directions are the identity on the underlying data. -/
def equivCompletelyPositiveMap : (A₁ →CP' A₂) ≃ (A₁ →CP A₂) where
  toFun φ := ⟨φ.toLinearMap, φ.map_cstarMatrix_nonneg'⟩
  invFun φ := ⟨φ.toLinearMap, φ.map_cstarMatrix_nonneg'⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `equivCompletelyPositiveMap` does not change the underlying function. -/
@[simp]
lemma coe_equivCompletelyPositiveMap (φ : A₁ →CP' A₂) : ⇑(equivCompletelyPositiveMap φ) = φ := rfl

/-- `equivCompletelyPositiveMap.symm` does not change the underlying function. -/
@[simp]
lemma coe_equivCompletelyPositiveMap_symm (φ : A₁ →CP A₂) :
    ⇑(equivCompletelyPositiveMap.symm φ) = φ :=
  rfl

end CompletelyPositiveMap'

end CStarAlgebra

/-! ### Inclusion and restriction to operator subsystems -/

namespace OperatorSubsystem

variable {T : Type*} [AddCommGroup T] [Module ℂ T] [StarAddMonoid T] [One T]
  [∀ k, PartialOrder (CStarMatrix (Fin k) (Fin k) T)] (S : OperatorSubsystem T)

/-- The inclusion of an operator subsystem is completely positive: the matrix orders of `S` are
those of `T`. -/
def subtype : S →CP' T where
  toLinearMap := S.toSubmodule.subtype
  map_cstarMatrix_nonneg' _ _ hM := hM

/-- The inclusion of an operator subsystem is `Subtype.val`. -/
@[simp] lemma coe_subtype : ⇑S.subtype = Subtype.val := rfl

end OperatorSubsystem

namespace CompletelyPositiveMap'

variable {T B : Type*} [AddCommGroup T] [Module ℂ T] [StarAddMonoid T] [One T]
  [∀ k, PartialOrder (CStarMatrix (Fin k) (Fin k) T)] [AddCommMonoid B] [Module ℂ B]
  [∀ k, PartialOrder (CStarMatrix (Fin k) (Fin k) B)]

/-- The restriction of a completely positive map to an operator subsystem. -/
def restrict (φ : T →CP' B) (S : OperatorSubsystem T) : S →CP' B := φ.comp S.subtype

/-- The restriction of `φ` to `S` sends `s` to `φ s`. -/
@[simp] lemma restrict_apply (φ : T →CP' B) (S : OperatorSubsystem T) (s : S) :
    φ.restrict S s = φ s :=
  rfl

end CompletelyPositiveMap'
