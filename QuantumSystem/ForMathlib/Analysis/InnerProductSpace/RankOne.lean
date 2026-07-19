module

public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Operators commuting with all rank-one operators are scalar

A continuous linear operator on an inner product space that commutes with every rank-one operator
`|x⟩⟨y|` is a scalar multiple of the identity. This is the elementary computation behind
"the centre of `B(H)` is trivial" and, downstream, behind the factor property of the tensor
von Neumann algebras `B(H₁) ⊗̄ 1` and `1 ⊗̄ B(H₂)`.
-/

@[expose] public section

/-- A continuous linear operator commuting with every rank-one operator `|x⟩⟨y|` is a scalar
multiple of the identity: testing the commutation relation on a fixed nonzero vector `y` yields
`⟪y, y⟫ • S x = ⟪y, S y⟫ • x` for *every* `x`, so `S = (⟪y, S y⟫ / ⟪y, y⟫) • 1`. -/
theorem ContinuousLinearMap.exists_eq_smul_one_of_forall_rankOne_comm
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
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]
  calc S x = (inner ℂ y y)⁻¹ • ((inner ℂ y y : ℂ) • S x) := (inv_smul_smul₀ hyy _).symm
    _ = (inner ℂ y y)⁻¹ • (inner ℂ y (S y) • x) := by rw [h1]
    _ = (inner ℂ y (S y) / inner ℂ y y) • x := by rw [smul_smul, div_eq_inv_mul]
