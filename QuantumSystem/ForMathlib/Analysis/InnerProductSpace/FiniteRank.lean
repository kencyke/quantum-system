module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Finite-rank operators as a non-unital `*`-subalgebra

An operator on a Hilbert space has *finite rank* if its range is finite-dimensional. The
finite-rank operators form a `*`-subalgebra `F(H)` of `B(H)` which, on an infinite-dimensional
`H`, does **not** contain `1` and yet acts non-degenerately: it is the standard witness that
non-degeneracy is strictly weaker than unitality, and hence that the non-unital form of the
bicommutant theorem has content the unital form does not reach.

The only step that is not immediate is closure under the adjoint. It uses that `T†` annihilates
`(ran T)ᗮ` (`ContinuousLinearMap.orthogonal_range`), so that `ran T† = T†(ran T)` is the image of
a finite-dimensional subspace.

## Main definitions

* `InnerProductSpace.IsFiniteRank`: the operator has finite-dimensional range.
* `InnerProductSpace.finiteRankOperators`: the finite-rank operators, bundled as a
  `NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)`.

## Main results

* `InnerProductSpace.rankOne_mem_finiteRankOperators`: every rank-one operator `|x⟩⟨y|` lies in
  `F(H)`.
* `InnerProductSpace.one_notMem_finiteRankOperators`: on an infinite-dimensional `H`, `1 ∉ F(H)`.

The results combining `F(H)` with the rest of the bicommutant development — that it acts
non-degenerately, and that `F(H)' = ℂ1` and hence `F(H)'' = B(H)` — live in
`QuantumSystem.Algebra.Star.DoubleCommutant.TFAE`: they consume declarations from other
`ForMathlib` files, and `ForMathlib` files import Mathlib only.
-/

@[expose] public section

namespace InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- An operator has **finite rank** if its range is finite-dimensional. -/
def IsFiniteRank (T : H →L[ℂ] H) : Prop :=
  FiniteDimensional ℂ (LinearMap.range (T : H →ₗ[ℂ] H))

lemma isFiniteRank_zero : IsFiniteRank (0 : H →L[ℂ] H) := by
  have h : LinearMap.range ((0 : H →L[ℂ] H) : H →ₗ[ℂ] H) = ⊥ := by simp
  rw [IsFiniteRank, h]
  infer_instance

lemma IsFiniteRank.add {S T : H →L[ℂ] H} (hS : IsFiniteRank S) (hT : IsFiniteRank T) :
    IsFiniteRank (S + T) := by
  haveI : FiniteDimensional ℂ (LinearMap.range (S : H →ₗ[ℂ] H)) := hS
  haveI : FiniteDimensional ℂ (LinearMap.range (T : H →ₗ[ℂ] H)) := hT
  refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range (S : H →ₗ[ℂ] H) ⊔
    LinearMap.range (T : H →ₗ[ℂ] H)) ?_
  rintro _ ⟨x, rfl⟩
  exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩

/-- Multiplying a finite-rank operator on the left keeps the rank finite: the range only shrinks
under the image. -/
lemma IsFiniteRank.mul_left {T : H →L[ℂ] H} (hT : IsFiniteRank T) (S : H →L[ℂ] H) :
    IsFiniteRank (S * T) := by
  haveI : FiniteDimensional ℂ (LinearMap.range (T : H →ₗ[ℂ] H)) := hT
  refine Submodule.finiteDimensional_of_le
    (S₂ := (LinearMap.range (T : H →ₗ[ℂ] H)).map (S : H →ₗ[ℂ] H)) ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨T x, ⟨x, rfl⟩, rfl⟩

/-- Multiplying a finite-rank operator on the right keeps the rank finite: the range is unchanged
or smaller. -/
lemma IsFiniteRank.mul_right {T : H →L[ℂ] H} (hT : IsFiniteRank T) (S : H →L[ℂ] H) :
    IsFiniteRank (T * S) := by
  haveI : FiniteDimensional ℂ (LinearMap.range (T : H →ₗ[ℂ] H)) := hT
  refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range (T : H →ₗ[ℂ] H)) ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨S x, rfl⟩

lemma IsFiniteRank.smul {T : H →L[ℂ] H} (hT : IsFiniteRank T) (c : ℂ) :
    IsFiniteRank (c • T) := by
  haveI : FiniteDimensional ℂ (LinearMap.range (T : H →ₗ[ℂ] H)) := hT
  refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range (T : H →ₗ[ℂ] H)) ?_
  rintro _ ⟨x, rfl⟩
  exact Submodule.smul_mem _ _ ⟨x, rfl⟩

/-- The rank-one operator `|x⟩⟨y| : z ↦ ⟪y, z⟫ • x` has finite rank: its range lies in
`span {x}`. -/
lemma isFiniteRank_rankOne (x y : H) : IsFiniteRank (rankOne ℂ x y : H →L[ℂ] H) := by
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {x}) ?_
  rintro _ ⟨z, rfl⟩
  simp only [ContinuousLinearMap.coe_coe, rankOne_apply]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)

variable [CompleteSpace H]

/-- The adjoint of a finite-rank operator has finite rank. Since `T†` annihilates `(ran T)ᗮ`, its
range is the image of the finite-dimensional subspace `ran T`. -/
lemma IsFiniteRank.adjoint {T : H →L[ℂ] H} (hT : IsFiniteRank T) :
    IsFiniteRank (ContinuousLinearMap.adjoint T) := by
  haveI : FiniteDimensional ℂ (LinearMap.range (T : H →ₗ[ℂ] H)) := hT
  refine Submodule.finiteDimensional_of_le
    (S₂ := (LinearMap.range (T : H →ₗ[ℂ] H)).map
      ((ContinuousLinearMap.adjoint T : H →L[ℂ] H) : H →ₗ[ℂ] H)) ?_
  rintro _ ⟨x, rfl⟩
  obtain ⟨p, hp, q, hq, rfl⟩ :=
    Submodule.exists_add_mem_mem_orthogonal (K := LinearMap.range (T : H →ₗ[ℂ] H)) x
  have hq0 : ContinuousLinearMap.adjoint T q = 0 := by
    have hmem : q ∈ LinearMap.ker ((ContinuousLinearMap.adjoint T : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
      rw [← ContinuousLinearMap.orthogonal_range]
      exact hq
    simpa using hmem
  exact ⟨p, hp, by simp [map_add, hq0]⟩

/-- **The finite-rank operators `F(H)`**, as a non-unital `*`-subalgebra of `B(H)`. It is a
two-sided ideal, but only the `*`-subalgebra structure is recorded here — that is what the
bicommutant theorem consumes. -/
noncomputable def finiteRankOperators : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H) where
  carrier := {T | IsFiniteRank T}
  add_mem' := IsFiniteRank.add
  zero_mem' := isFiniteRank_zero
  mul_mem' := fun {S _} _ hT => hT.mul_left S
  smul_mem' := fun c _ hT => IsFiniteRank.smul hT c
  star_mem' := fun hT => IsFiniteRank.adjoint hT

@[simp] lemma mem_finiteRankOperators_iff {T : H →L[ℂ] H} :
    T ∈ finiteRankOperators (H := H) ↔ IsFiniteRank T := Iff.rfl

/-- Every rank-one operator `|x⟩⟨y|` lies in `F(H)`. -/
lemma rankOne_mem_finiteRankOperators (x y : H) :
    (rankOne ℂ x y : H →L[ℂ] H) ∈ finiteRankOperators (H := H) :=
  isFiniteRank_rankOne x y

/-- **`F(H)` is not unital** when `H` is infinite-dimensional: `1` has range `H`.

Together with `InnerProductSpace.actsNondegenerately_finiteRankOperators` (proved in
`QuantumSystem.Algebra.Star.DoubleCommutant.TFAE`) this exhibits a `*`-subalgebra to which the
non-unital bicommutant theorem applies and the unital one does not. -/
theorem one_notMem_finiteRankOperators (h : ¬ FiniteDimensional ℂ H) :
    (1 : H →L[ℂ] H) ∉ finiteRankOperators (H := H) := by
  intro hmem
  refine h ?_
  have hr : LinearMap.range ((1 : H →L[ℂ] H) : H →ₗ[ℂ] H) = ⊤ := by
    ext y
    simp only [Submodule.mem_top, iff_true, LinearMap.mem_range]
    exact ⟨y, rfl⟩
  haveI : FiniteDimensional ℂ (LinearMap.range ((1 : H →L[ℂ] H) : H →ₗ[ℂ] H)) := hmem
  rw [hr] at this
  exact (Submodule.topEquiv (R := ℂ) (M := H)).finiteDimensional

end InnerProductSpace
