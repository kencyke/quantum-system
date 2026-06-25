module

public import QuantumSystem.Channel
public import QuantumSystem.ForMathlib.LinearAlgebra.Matrix.PartialTrace

/-!
# Partial trace as a quantum channel (product index types)

The **partial trace** on plain product index types `X × Y`, packaged as a completely positive
trace-preserving map (`QuantumChannel`). This is the `SiteIndexSystem`-free analogue of
`Matrix.QuantumChannel.restrict` (`Analysis/Matrix/PartialTrace.lean`): it traces out the right
factor `Y` of a matrix on `X × Y`, leaving a matrix on `X`. The construction mirrors the region
version with `SiteIndexSystem.combineIdx (a, b)` replaced by the plain pair `(x, y)`.

We also package conjugation by an index equivalence (`reindexₗ`) as a channel, and compose the two
into the trace-out-`C` channel `QuantumChannel.traceOutC : QuantumChannel (A × B × C) (A × B)`,
whose action is exactly the `lean-eval` marginal map
`M ↦ traceRight (M.reindex (prodAssoc).symm (prodAssoc).symm)`.

## Main definitions

* `Matrix.partialTraceRightₗ` — right partial trace as a `ℂ`-linear map.
* `Matrix.QuantumChannel.partialTraceRight` — bundled quantum channel tracing out `Y`.
* `Matrix.QuantumChannel.reindex` — conjugation by an index equivalence, as a channel.
* `Matrix.QuantumChannel.traceOutC` — trace out the `C` factor of `A × B × C`.
-/

@[expose] public section

namespace Matrix

open scoped ComplexOrder

/-! ### Positive semidefiniteness and trace facts for the partial trace -/

/-- The right partial trace preserves positive semidefiniteness (it is a sum of principal
submatrices). -/
theorem traceRight_posSemidef {l n : Type*} [Fintype n]
    {M : Matrix (l × n) (l × n) ℂ} (hM : M.PosSemidef) : (Matrix.traceRight M).PosSemidef := by
  have hsum : Matrix.traceRight M
      = ∑ k : n, M.submatrix (fun i : l => (i, k)) (fun j : l => (j, k)) := by
    ext i j; simp [Matrix.traceRight_apply, Matrix.sum_apply, Matrix.submatrix_apply]
  rw [hsum]
  exact Matrix.posSemidef_sum _ (fun k _ => hM.submatrix _)

/-- The left partial trace preserves positive semidefiniteness. -/
theorem traceLeft_posSemidef {l n : Type*} [Fintype n]
    {M : Matrix (n × l) (n × l) ℂ} (hM : M.PosSemidef) : (Matrix.traceLeft M).PosSemidef := by
  have hsum : Matrix.traceLeft M
      = ∑ k : n, M.submatrix (fun i : l => (k, i)) (fun j : l => (k, j)) := by
    ext i j; simp [Matrix.traceLeft_apply, Matrix.sum_apply, Matrix.submatrix_apply]
  rw [hsum]
  exact Matrix.posSemidef_sum _ (fun k _ => hM.submatrix _)

/-- Reindexing by an index equivalence preserves the trace. -/
@[simp] theorem trace_reindex_self {n m : Type*} [Fintype n] [Fintype m] (e : n ≃ m)
    (M : Matrix n n ℂ) : (M.reindex e e).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp e.symm (fun i => M i i)

/-- The right partial trace of the identity scales by the cardinality of the traced factor. -/
theorem traceRight_one {X Y : Type*} [DecidableEq X] [Fintype Y] [DecidableEq Y] :
    Matrix.traceRight (1 : Matrix (X × Y) (X × Y) ℂ) = (Fintype.card Y : ℂ) • (1 : Matrix X X ℂ) := by
  ext i j
  simp only [traceRight_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, Prod.mk.injEq]
  by_cases hij : i = j
  · subst hij; simp [Finset.card_univ]
  · simp [hij]

/-- The left partial trace of the identity scales by the cardinality of the traced factor. -/
theorem traceLeft_one {X Y : Type*} [Fintype X] [DecidableEq X] [DecidableEq Y] :
    Matrix.traceLeft (1 : Matrix (X × Y) (X × Y) ℂ) = (Fintype.card X : ℂ) • (1 : Matrix Y Y ℂ) := by
  ext i j
  simp only [traceLeft_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, Prod.mk.injEq]
  by_cases hij : i = j
  · subst hij; simp [Finset.card_univ]
  · simp [hij]

/-! ### Right partial trace as a linear map -/

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

/-! ### Kraus operators and complete positivity -/

/-- Kraus operator for the right partial trace, indexed by `y : Y`: `K_y x p = [p = (x, y)]`. -/
def traceRightKraus {X Y : Type*} [DecidableEq X] [DecidableEq Y] (y : Y) :
    Matrix X (X × Y) ℂ :=
  Matrix.of fun x p => if p = (x, y) then (1 : ℂ) else 0

theorem isCompletelyPositive_partialTraceRight {X Y : Type*} [Fintype X] [Fintype Y] :
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
      rw [if_neg hq]; ring
    · simp
  · intro q _ hq
    simp only [traceRightKraus, Matrix.conjTranspose_apply, Matrix.of_apply,
      apply_ite (star · : ℂ → ℂ), star_one, star_zero]
    rw [if_neg hq]; simp
  · simp

theorem isTracePreserving_partialTraceRight {X Y : Type*} [Fintype X] [Fintype Y] :
    IsTracePreserving (partialTraceRightₗ (X := X) (Y := Y)) :=
  fun M => by rw [partialTraceRightₗ_apply]; exact trace_traceRight M

/-- Right partial trace (trace out `Y`) as a bundled `QuantumChannel`. -/
noncomputable def QuantumChannel.partialTraceRight {X Y : Type*} [Fintype X] [Fintype Y] :
    Matrix.QuantumChannel (X × Y) X :=
  ⟨partialTraceRightₗ, isCompletelyPositive_partialTraceRight, isTracePreserving_partialTraceRight⟩

/-! ### Conjugation by an index equivalence as a channel -/

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

theorem isCompletelyPositive_reindexₗ {Z W : Type*} [Fintype Z] (e : Z ≃ W) :
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
      rw [if_neg hq]; ring
    · simp
  · intro z _ hz
    simp only [reindexKraus, Matrix.conjTranspose_apply, Matrix.of_apply,
      apply_ite (star · : ℂ → ℂ), star_one, star_zero]
    rw [if_neg hz]; simp
  · simp

theorem isTracePreserving_reindexₗ {Z W : Type*} [Fintype Z] [Fintype W] (e : Z ≃ W) :
    IsTracePreserving (reindexₗ e) := by
  intro M
  rw [reindexₗ_apply]
  exact trace_reindex_self e M

/-- Conjugation by an index equivalence as a bundled `QuantumChannel`. -/
noncomputable def QuantumChannel.reindex {Z W : Type*} [Fintype Z] [Fintype W] (e : Z ≃ W) :
    Matrix.QuantumChannel Z W :=
  ⟨reindexₗ e, isCompletelyPositive_reindexₗ e, isTracePreserving_reindexₗ e⟩

/-! ### Trace-out-`C` channel for `A × B × C` -/

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
