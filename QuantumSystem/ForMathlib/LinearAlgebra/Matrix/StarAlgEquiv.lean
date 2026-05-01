module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# `StarAlgEquiv` instances for matrix algebras

Provides

* `Matrix.reindexStarAlgEquiv` — `Matrix.reindexAlgEquiv` upgraded to a `StarAlgEquiv`,
  using `conjTranspose_submatrix` for the `map_star'` field.
* `Matrix.trace_submatrix_eq` — trace is preserved under `submatrix _ e e` for a type
  equivalence.
* `Matrix.trace_reindexStarAlgEquiv` — trace preservation specialised to
  `reindexStarAlgEquiv`.
* `Matrix.trace_conjStarAlgAut` — trace is preserved under unitary conjugation
  `Unitary.conjStarAlgAut` on a matrix algebra.
* `Matrix.IsHermitian.map_starAlgEquiv` / `Matrix.PosSemidef.map_starAlgEquiv` /
  `Matrix.PosDef.map_starAlgEquiv` — preservation of Hermitian / positive
  (semi)definite under a `*-`algebra equivalence between complex matrix algebras.
* `Matrix.PosSemidef.mapEquiv` / `Matrix.PosDef.mapEquiv` — reindex specialisations of
  the `map_starAlgEquiv` preservation lemmas.

`Unitary.conjStarAlgAut S R u : R ≃⋆ₐ[S] R` already exists upstream in
`Mathlib.Algebra.Star.UnitaryStarAlgAut`, so this file does not redefine it; only the
trace-preservation lemma specific to matrix algebras is added here.
-/

@[expose] public section

namespace Matrix

variable {R A : Type*} {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-! ### Reindex as a `StarAlgEquiv` -/

section Reindex

variable [CommSemiring R] [Semiring A] [StarRing A] [Algebra R A]

/-- The matrix-algebra equivalence induced by an index equivalence, upgraded to a
`*-`algebra equivalence. The `map_star'` field is `conjTranspose_submatrix`.

Compare with `Matrix.reindexAlgEquiv`, which gives only the algebra-equivalence version. -/
def reindexStarAlgEquiv (e : m ≃ n) : Matrix m m A ≃⋆ₐ[R] Matrix n n A :=
  StarAlgEquiv.ofAlgEquiv (reindexAlgEquiv R A e) <| fun M => by
    change (M.submatrix e.symm e.symm)ᴴ = (Mᴴ).submatrix e.symm e.symm
    exact conjTranspose_submatrix _ _ _

@[simp]
private lemma reindexStarAlgEquiv_apply (e : m ≃ n) (M : Matrix m m A) :
    reindexStarAlgEquiv (R := R) e M = reindex e e M := rfl

@[simp]
private lemma reindexStarAlgEquiv_symm (e : m ≃ n) :
    (reindexStarAlgEquiv (R := R) (A := A) e).symm = reindexStarAlgEquiv e.symm := by
  ext M
  rfl

end Reindex

/-! ### Trace preservation -/

omit [DecidableEq m] [DecidableEq n] in
/-- Trace is preserved under `Matrix.reindex` along a type equivalence. -/
private lemma trace_reindex {α : Type*} [AddCommMonoid α] (e : m ≃ n) (M : Matrix m m α) :
    (reindex e e M).trace = M.trace := by
  unfold Matrix.trace
  simp_rw [Matrix.diag_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact Finset.sum_equiv e.symm (by simp) (fun _ _ => rfl)

omit [DecidableEq m] [DecidableEq n] in
/-- Trace is preserved when reindexing the matrix indices via a bijection.
    This is the `submatrix _ e e` form (vs. `reindex` form in `trace_reindex`). -/
theorem trace_submatrix_eq {α : Type*} [AddCommMonoid α] (M : Matrix m m α) (e : n ≃ m) :
    (M.submatrix e e).trace = M.trace := by
  rw [show (M.submatrix e e) = reindex e.symm e.symm M from rfl]
  exact trace_reindex e.symm M

/-- Trace is preserved under `reindexStarAlgEquiv`. -/
theorem trace_reindexStarAlgEquiv [CommSemiring R] [Semiring A] [StarRing A] [Algebra R A]
    (e : m ≃ n) (M : Matrix m m A) :
    (reindexStarAlgEquiv (R := R) e M).trace = M.trace := by
  rw [reindexStarAlgEquiv_apply]
  exact trace_reindex e M

/-- Trace is preserved under unitary conjugation `Unitary.conjStarAlgAut`. -/
theorem trace_conjStarAlgAut [CommSemiring R] [CommSemiring A] [StarRing A] [Algebra R A]
    (u : unitary (Matrix n n A)) (M : Matrix n n A) :
    (Unitary.conjStarAlgAut R (Matrix n n A) u M).trace = M.trace := by
  rw [Unitary.conjStarAlgAut_apply, trace_mul_cycle,
      Unitary.star_mul_self_of_mem u.prop, Matrix.one_mul]

/-! ### Hermitian / PosSemidef / PosDef preservation under `StarAlgEquiv`

A `*-`algebra equivalence between complex matrix algebras preserves the
Hermitian, positive-semidefinite, and positive-definite predicates. The
`PosSemidef` proof uses the operator square root from the continuous
functional calculus on `Matrix m m ℂ`. -/

section StarAlgEquivPreservation

open scoped MatrixOrder ComplexOrder

omit [DecidableEq m] [DecidableEq n] in
/-- `*-`algebra homomorphisms preserve the Hermitian property.

This generalises the reindex case `IsHermitian.submatrix_equiv` to any `StarAlgEquiv`. -/
theorem IsHermitian.map_starAlgEquiv {M : Matrix m m ℂ} (hM : M.IsHermitian)
    (φ : Matrix m m ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ) :
    (φ M).IsHermitian := by
  unfold IsHermitian
  rw [← star_eq_conjTranspose, ← map_star, show star M = Mᴴ from rfl, hM]

omit [DecidableEq m] [DecidableEq n] in
/-- `*-`algebra equivalences preserve positive-semidefiniteness on matrix algebras over `ℂ`.

The proof goes via the eigenvalue characterisation of `PosSemidef`: any `*`-algebra equivalence
preserves the spectrum, and on Hermitian matrices the eigenvalues are exactly the real spectrum,
so non-negativity is preserved. -/
theorem PosSemidef.map_starAlgEquiv {M : Matrix m m ℂ} (hM : M.PosSemidef)
    (φ : Matrix m m ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ) :
    (φ M).PosSemidef := by
  classical
  -- Image is hermitian.
  have hφM_herm : (φ M).IsHermitian := IsHermitian.map_starAlgEquiv hM.isHermitian φ
  -- Reduce to spectrum-non-negativity using `posSemidef_iff_isHermitian_and_spectrum_nonneg`.
  rw [posSemidef_iff_isHermitian_and_spectrum_nonneg]
  refine ⟨hφM_herm, ?_⟩
  rw [posSemidef_iff_isHermitian_and_spectrum_nonneg] at hM
  -- `*-`-algebra equivalences preserve the spectrum.
  have hspec : spectrum ℂ (φ M) = spectrum ℂ M :=
    AlgEquiv.spectrum_eq φ.toAlgEquiv M
  rw [hspec]
  exact hM.2

omit [DecidableEq m] [DecidableEq n] in
/-- `*-`algebra equivalences preserve positive-definiteness: PSD + invertibility, both of
which are preserved by a `StarAlgEquiv`. -/
theorem PosDef.map_starAlgEquiv {M : Matrix m m ℂ} (hM : M.PosDef)
    (φ : Matrix m m ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ) :
    (φ M).PosDef := by
  classical
  refine (hM.posSemidef.map_starAlgEquiv φ).posDef_iff_isUnit.mpr ?_
  exact φ.toAlgEquiv.toAlgHom.isUnit_map hM.isUnit

/-! ### Reindex specialisations

`Equiv`-flavoured restatements derived from `PosSemidef.map_starAlgEquiv` and
`PosDef.map_starAlgEquiv`, useful when an index-set bijection `e : n ≃ m`
is naturally available (e.g. from `LocalNet` region equivalences). -/

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- `Matrix.PosSemidef` is preserved by reindexing the index set via a bijection.
    Specialisation of `PosSemidef.map_starAlgEquiv` to `reindexStarAlgEquiv`. -/
theorem PosSemidef.mapEquiv [Finite m] {M : Matrix m m ℂ} (hM : M.PosSemidef) (e : n ≃ m) :
    (M.submatrix e e).PosSemidef := by
  classical
  letI := Fintype.ofFinite m
  letI : Fintype n := Fintype.ofEquiv m e.symm
  exact Matrix.PosSemidef.map_starAlgEquiv hM
    (Matrix.reindexStarAlgEquiv (R := ℂ) e.symm)

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- `Matrix.PosDef` is preserved by reindexing the index set via a bijection.
    Specialisation of `PosDef.map_starAlgEquiv` to `reindexStarAlgEquiv`. -/
theorem PosDef.mapEquiv [Finite m] {M : Matrix m m ℂ} (hM : M.PosDef) (e : n ≃ m) :
    (M.submatrix e e).PosDef := by
  classical
  letI := Fintype.ofFinite m
  letI : Fintype n := Fintype.ofEquiv m e.symm
  exact Matrix.PosDef.map_starAlgEquiv hM
    (Matrix.reindexStarAlgEquiv (R := ℂ) e.symm)

end StarAlgEquivPreservation

end Matrix
