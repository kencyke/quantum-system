/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Rank-one operators

## Operators commuting with all rank-one operators are scalar

A continuous linear operator on an inner product space that commutes with every rank-one operator
`|x⟩⟨y|` is a scalar multiple of the identity. This is the elementary computation behind
"the centre of `B(H)` is trivial" and, downstream, behind the factor property of the tensor
von Neumann algebras `B(H₁) ⊗̄ 1` and `1 ⊗̄ B(H₂)`. That a rank-one operator has finite- (in fact
at most one-) dimensional range is recorded as
`InnerProductSpace.isFiniteRank_rankOne` in
`QuantumSystem.ForMathlib.Analysis.InnerProductSpace.FiniteRank`.

## Notation

`⊗̄` in the prose above is documentation shorthand for the von Neumann (spatial) tensor product of
algebras; that convention is stated in full in `QuantumSystem.Analysis.VonNeumannAlgebra.TensorFactor`,
downstream of this file, where the algebras it names are defined.

## Expansions in rank-one operators

* `ContinuousLinearMap.eq_sum_inner_smul_rankOne` — an operator is expanded along an orthonormal
  basis as `A = Σᵢⱼ ⟪bᵢ, A bⱼ⟫ |bᵢ⟩⟨bⱼ|`.
* `InnerProductSpace.range_sum_rankOne_self` — the range of `Σₐ |vₐ⟩⟨vₐ|` is the span of the `vₐ`.
-/

@[expose] public section

/-- A continuous linear operator commuting with every rank-one operator `|x⟩⟨y|` is a scalar
multiple of the identity: testing the commutation relation on a fixed nonzero vector `y` yields
`⟪y, y⟫ • S x = ⟪y, S y⟫ • x` for *every* `x`, so `S = (⟪y, S y⟫ / ⟪y, y⟫) • 1`. -/
lemma ContinuousLinearMap.exists_eq_smul_one_of_forall_rankOne_comm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {S : H →L[ℂ] H}
    (h : ∀ x y : H, S ∘L InnerProductSpace.rankOne ℂ x y
      = InnerProductSpace.rankOne ℂ x y ∘L S) :
    ∃ c : ℂ, S = c • 1 := by
  by_cases hH : ∀ y : H, y = 0
  · refine ⟨0, ContinuousLinearMap.ext fun x => ?_⟩
    rw [hH x]
    simp
  push Not at hH
  obtain ⟨y, hy⟩ := hH
  have hyy : (inner ℂ y y : ℂ) ≠ 0 := inner_self_ne_zero.mpr hy
  refine ⟨inner ℂ y (S y) / inner ℂ y y, ContinuousLinearMap.ext fun x => ?_⟩
  have h1 := congrArg (fun L : H →L[ℂ] H => L y) (h x y)
  simp only [ContinuousLinearMap.comp_apply, InnerProductSpace.rankOne_apply, map_smul] at h1
  rw [smul_apply, one_apply_eq_self]
  calc S x = (inner ℂ y y)⁻¹ • ((inner ℂ y y : ℂ) • S x) := (inv_smul_smul₀ hyy _).symm
    _ = (inner ℂ y y)⁻¹ • (inner ℂ y (S y) • x) := by rw [h1]
    _ = (inner ℂ y (S y) / inner ℂ y y) • x := by rw [smul_smul, div_eq_inv_mul]

open InnerProductSpace in
/-- An operator is expanded along an orthonormal basis `b` in the rank-one operators `|bᵢ⟩⟨bⱼ|`:
`A = Σᵢⱼ ⟪bᵢ, A bⱼ⟫ |bᵢ⟩⟨bⱼ|`, from `1 = Σᵢ |bᵢ⟩⟨bᵢ|` on both sides of `A`. -/
lemma ContinuousLinearMap.eq_sum_inner_smul_rankOne {𝕜 E ι : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype ι] (b : OrthonormalBasis ι 𝕜 E)
    (A : E →L[𝕜] E) :
    A = ∑ i, ∑ j, inner 𝕜 (b i) (A (b j)) • rankOne 𝕜 (b i) (b j) := by
  conv_lhs => rw [← ContinuousLinearMap.comp_id A, ← b.sum_rankOne_eq_id]
  simp only [ContinuousLinearMap.comp_finsetSum, comp_rankOne]
  conv_lhs => enter [2, j]; rw [← b.sum_repr' (A (b j))]
  simp only [map_sum, map_smul, sum_apply, smul_apply]
  exact Finset.sum_comm

open InnerProductSpace in
/-- The range of the positive operator `Σₐ |vₐ⟩⟨vₐ|` is the span of the `vₐ`: its kernel is the
orthogonal complement of that span, since `⟪z, Σₐ |vₐ⟩⟨vₐ| z⟫ = Σₐ |⟪vₐ, z⟫|²`, and its range is the
orthogonal complement of its kernel. -/
lemma InnerProductSpace.range_sum_rankOne_self {𝕜 E ι : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [Fintype ι]
    (v : ι → E) :
    LinearMap.range ((∑ a, rankOne 𝕜 (v a) (v a) : E →L[𝕜] E) : E →ₗ[𝕜] E) =
      Submodule.span 𝕜 (Set.range v) := by
  have : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  set J := ∑ a, rankOne 𝕜 (v a) (v a)
  have hJ : J.IsPositive :=
    ContinuousLinearMap.isPositive_sum _ fun a _ => isPositive_rankOne_self (v a)
  have hker : LinearMap.ker (J : E →ₗ[𝕜] E) = (Submodule.span 𝕜 (Set.range v))ᗮ := by
    ext z
    have hJz : J z = ∑ a, inner 𝕜 (v a) z • v a := by simp [J, sum_apply]
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, Submodule.mem_orthogonal']
    constructor
    · intro h
      have hz : ∀ a, inner 𝕜 (v a) z = 0 := by
        have h0 : ∑ a, ‖inner 𝕜 (v a) z‖ ^ 2 = 0 := by
          have := congrArg (fun w => RCLike.re (inner 𝕜 z w)) h
          simp only [hJz, inner_sum, inner_smul_right, inner_zero_right, map_zero] at this
          rw [← this, map_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [← inner_conj_symm z (v a), RCLike.mul_conj]
          exact_mod_cast (RCLike.ofReal_re (K := 𝕜) _).symm
        intro a
        simpa using (Finset.sum_eq_zero_iff_of_nonneg fun a _ => sq_nonneg _).1 h0 a
          (Finset.mem_univ a)
      intro u hu
      induction hu using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, rfl⟩ := hx
        rw [← inner_conj_symm, hz, map_zero]
      | zero => exact inner_zero_right _
      | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
      | smul c x _ hx => rw [inner_smul_right, hx, mul_zero]
    · intro h
      have hz : ∀ a, inner 𝕜 (v a) z = 0 := fun a => by
        rw [← inner_conj_symm, h (v a) (Submodule.subset_span ⟨a, rfl⟩), map_zero]
      simp [hJz, hz]
  rw [← Submodule.orthogonal_orthogonal (LinearMap.range (J : E →ₗ[𝕜] E)),
    ContinuousLinearMap.orthogonal_range, hJ.isSelfAdjoint.adjoint_eq, hker,
    Submodule.orthogonal_orthogonal]
