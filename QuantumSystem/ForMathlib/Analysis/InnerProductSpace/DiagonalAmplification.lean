module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Diagonal amplification of operators on Hilbert spaces

This file develops the theory of diagonal amplification: given an operator `T : H →L[ℂ] H`,
we construct its diagonal action on `H^n = Fin n → H` (with the L2 inner product).

This is a key ingredient in the von Neumann double commutant theorem: amplification allows
reducing the general case to the case with a cyclic vector.

## Main definitions

* `Hn n`: the Hilbert space `H^n` as `PiLp 2 (Fin n → H)`.
* `proj i`: the projection from `H^n` to the `i`-th component.
* `single i`: the injection from `H` to the `i`-th component of `H^n`.
* `diagonal T`: the diagonal action of `T` on `H^n`, i.e., `T` applied componentwise.
* `matrixComponent S i j`: the `(i, j)`-th matrix entry of an operator `S` on `H^n`.
* `diagonalStarAlgHom n`: the diagonal embedding as a `StarAlgHom`.

## Main results

* `commute_diagonal_iff`: `S` commutes with `diagonal T` iff all matrix components of `S`
  commute with `T`.
* `mem_commutant_diagonal_iff`: characterization of the commutant of the diagonal algebra.
* `diagonal_mem_double_commutant`: if `T ∈ A''`, then `diagonal T ∈ (diagonal '' A)''`.
* `diagonal_star`: diagonal commutes with the star operation.
-/

@[expose] public section

namespace InnerProductSpace

open scoped ENNReal

section NoComplete

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The Hilbert space `H^n` as `Fin n → H` with the L2 inner product. -/
abbrev Hn (n : ℕ) := PiLp (2 : ℝ≥0∞) (fun _ : Fin n => H)

/-- The projection from `H^n` to the `i`-th component `H`. -/
noncomputable def proj {n : ℕ} (i : Fin n) : Hn (H := H) n →L[ℂ] H :=
  PiLp.proj (p := (2 : ℝ≥0∞)) (𝕜 := ℂ) (β := fun _ : Fin n => H) i

@[simp]
lemma proj_apply {n : ℕ} (i : Fin n) (x : Hn (H := H) n) :
    proj (H := H) (n := n) i x = x.ofLp i := by
  simp [proj, PiLp.proj_apply]

/-- The injection from `H` to the `i`-th component of `H^n`. -/
noncomputable def single {n : ℕ} (i : Fin n) : H →L[ℂ] Hn (H := H) n :=
  LinearMap.mkContinuous
    { toFun := fun v => WithLp.toLp (2 : ℝ≥0∞) (fun k : Fin n => if k = i then v else 0)
      map_add' := fun x y => by
        apply PiLp.ext
        intro k
        by_cases hk : k = i
        · simp [hk]
        · simp [hk]
      map_smul' := fun c x => by
        apply PiLp.ext
        intro k
        by_cases hk : k = i
        · simp [hk]
        · simp [hk] }
    1
    (fun v => by
      rw [one_mul, PiLp.norm_eq_of_L2]
      rw [Finset.sum_eq_single i]
      · simp only [LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp, ite_true,
          Real.sqrt_sq (norm_nonneg v)]
        exact le_refl _
      · intro j _ hji
        simp only [LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp, hji, ite_false, norm_zero,
          OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true, zero_pow]
      · intro hi
        exact (hi (Finset.mem_univ i)).elim)

@[simp]
lemma single_apply {n : ℕ} (i : Fin n) (v : H) (k : Fin n) :
    (single (H := H) (n := n) i v).ofLp k = if k = i then v else 0 := by
  simp only [single, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.mkContinuous_apply,
    WithLp.ofLp_toLp]

/-- Diagonal action of an operator `T : H →L[ℂ] H` on `H^n`. -/
noncomputable def diagonal {n : ℕ} (T : H →L[ℂ] H) : Hn (H := H) n →L[ℂ] Hn (H := H) n := by
  classical
  exact ∑ i : Fin n, (single (H := H) (n := n) i).comp (T.comp (proj (H := H) (n := n) i))

@[simp]
lemma diagonal_apply {n : ℕ} (T : H →L[ℂ] H) (x : Hn (H := H) n) (i : Fin n) :
    (diagonal (H := H) (n := n) T x).ofLp i = T (x.ofLp i) := by
  classical
  unfold diagonal
  rw [ContinuousLinearMap.coe_sum']
  simp only [Finset.sum_apply, ContinuousLinearMap.coe_comp', Function.comp_apply, proj_apply]
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · rw [single_apply, if_pos rfl]
  · intro j _ hji
    rw [single_apply, if_neg (Ne.symm hji)]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- The projection of an operator `S` on `H^n` to its `(i, j)`-th component in `B(H)`. -/
noncomputable def matrixComponent {n : ℕ} (S : Hn (H := H) n →L[ℂ] Hn (H := H) n)
    (i j : Fin n) : H →L[ℂ] H :=
  (proj (H := H) (n := n) i).comp (S.comp (single (H := H) (n := n) j))

@[simp]
lemma matrixComponent_apply {n : ℕ} (S : Hn (H := H) n →L[ℂ] Hn (H := H) n)
    (i j : Fin n) (v : H) :
    matrixComponent (H := H) (n := n) S i j v = (S (single (H := H) (n := n) j v)).ofLp i := by
  rfl

lemma diagonal_single {n : ℕ} (T : H →L[ℂ] H) (j : Fin n) (v : H) :
    diagonal (H := H) (n := n) T (single (H := H) (n := n) j v) =
    single (H := H) (n := n) j (T v) := by
  apply PiLp.ext
  intro k
  rw [diagonal_apply, single_apply, single_apply]
  split_ifs with h
  · rfl
  · simp only [map_zero]

lemma single_sum_eq {n : ℕ} (x : Hn (H := H) n) :
    x = ∑ j : Fin n, single (H := H) (n := n) j (x.ofLp j) := by
  apply PiLp.ext
  intro l
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single l]
  · rw [single_apply, if_pos rfl]
  · intro j _ hjl
    rw [single_apply, if_neg (Ne.symm hjl)]
  · intro hl
    exact (hl (Finset.mem_univ l)).elim

/-- If `S` commutes with `diagonal T`, then its components satisfy a commutation relation. -/
lemma commute_diagonal_iff {n : ℕ} (S : Hn (H := H) n →L[ℂ] Hn (H := H) n) (T : H →L[ℂ] H) :
    S * (diagonal (H := H) (n := n) T) = (diagonal (H := H) (n := n) T) * S ↔
    ∀ i j, (matrixComponent (H := H) (n := n) S i j) * T =
           T * (matrixComponent (H := H) (n := n) S i j) := by
  constructor
  · intro h i j
    ext v
    simp only [ContinuousLinearMap.mul_apply, matrixComponent_apply]
    have h_eq := congrArg (fun A => (A (single (H := H) (n := n) j v)).ofLp i) h
    simp only [ContinuousLinearMap.mul_apply] at h_eq
    rw [diagonal_single] at h_eq
    rw [diagonal_apply] at h_eq
    exact h_eq
  · intro h
    ext x k
    simp only [ContinuousLinearMap.mul_apply]
    rw [diagonal_apply]
    conv_lhs => rw [single_sum_eq x]
    conv_rhs => rw [single_sum_eq x]
    simp only [map_sum, WithLp.ofLp_sum, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [diagonal_single]
    simp only [← matrixComponent_apply, ← ContinuousLinearMap.mul_apply]
    have := congrArg (fun f => f (x.ofLp j)) (h k j)
    simp only [ContinuousLinearMap.mul_apply] at this
    exact this

/-- Characterization of the commutant of the diagonal algebra. -/
lemma mem_commutant_diagonal_iff {n : ℕ}
    (S : Hn (H := H) n →L[ℂ] Hn (H := H) n) (A : Set (H →L[ℂ] H)) :
    S ∈ (diagonal (H := H) (n := n) '' A).centralizer ↔
      ∀ i j, matrixComponent (H := H) (n := n) S i j ∈ A.centralizer := by
  constructor
  · intro hS i j T hT
    simp only [Set.mem_centralizer_iff] at hS
    have h := hS (diagonal (H := H) (n := n) T) ⟨T, hT, rfl⟩
    rw [eq_comm, commute_diagonal_iff] at h
    exact (h i j).symm
  · intro hS S' hS'
    simp only [Set.mem_image] at hS'
    obtain ⟨T, hT, rfl⟩ := hS'
    rw [eq_comm, commute_diagonal_iff]
    intro i j
    exact (hS i j T hT).symm

/-- If `T` is in the double commutant of `A`, then `diagonal T` is in the double commutant of
`diagonal A`. -/
theorem diagonal_mem_double_commutant {n : ℕ} {A : Set (H →L[ℂ] H)} {T : H →L[ℂ] H}
    (hT : T ∈ A.centralizer.centralizer) :
    diagonal (H := H) (n := n) T ∈
      (diagonal (H := H) (n := n) '' A).centralizer.centralizer := by
  intro S hS
  rw [mem_commutant_diagonal_iff (H := H) (n := n)] at hS
  rw [commute_diagonal_iff (H := H) (n := n)]
  intro i j
  -- We need matrixComponent S i j * T = T * matrixComponent S i j
  -- We know matrixComponent S i j ∈ A.centralizer
  -- And T ∈ A.centralizer.centralizer
  have hij : matrixComponent (H := H) (n := n) S i j ∈ A.centralizer := hS i j
  exact hT (matrixComponent (H := H) (n := n) S i j) hij

end NoComplete

section WithComplete

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The diagonal operator commutes with the star operation. -/
lemma diagonal_star {n : ℕ} (T : H →L[ℂ] H) :
    diagonal (H := H) (n := n) (star T) = star (diagonal (H := H) (n := n) T) := by
  classical
  -- `star` on bounded operators is the adjoint.
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint]
  -- Characterize adjoints via inner products.
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  -- Expand the `PiLp` inner products and use the defining property of the adjoint.
  simp only [PiLp.inner_apply, diagonal_apply]
  refine Finset.sum_congr rfl ?_
  intro i _
  simpa using
    (ContinuousLinearMap.adjoint_inner_left (A := T) (x := y.ofLp i) (y := x.ofLp i))

/-- `diagonal` as a `StarAlgHom` (so we can map `StarSubalgebra`s). -/
noncomputable def diagonalStarAlgHom (n : ℕ) : (H →L[ℂ] H) →⋆ₐ[ℂ] (Hn (H := H) n →L[ℂ] Hn (H := H) n) where
  toFun := fun T => diagonal (H := H) (n := n) T
  map_one' := by
    ext x i
    simp [diagonal]
  map_mul' := by
    intro T U
    ext x i
    simp [diagonal_apply, ContinuousLinearMap.mul_apply]
  map_zero' := by
    ext x i
    simp [diagonal_apply]
  map_add' := by
    intro T U
    ext x i
    simp [diagonal_apply]
  commutes' := by
    intro c
    ext x i
    simp [diagonal_apply, Algebra.algebraMap_eq_smul_one]
  map_star' := fun T => diagonal_star (H := H) (n := n) T

end WithComplete

end InnerProductSpace
