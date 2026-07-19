module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Operators commuting with all rank-one operators are scalar

A continuous linear operator on an inner product space that commutes with every rank-one operator
`|x⟩⟨y|` is a scalar multiple of the identity. This is the elementary computation behind
"the centre of `B(H)` is trivial" and, downstream, behind the factor property of the tensor
von Neumann algebras `B(H₁) ⊗̄ 1` and `1 ⊗̄ B(H₂)`. We also record that a rank-one operator has
finite- (in fact one-) dimensional range, used to see that a rank-one minimal projection of `B(H)`
has one-dimensional multiplicity space.
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

/-- The range of a rank-one operator `|u⟩⟨u|` is finite-dimensional (it is contained in the line
`ℂ ∙ u`). For a unit vector this is the one-dimensional multiplicity space of the corresponding
minimal projection of `B(H)`. -/
theorem finiteDimensional_range_rankOne {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (u : H) :
    FiniteDimensional ℂ (LinearMap.range ((InnerProductSpace.rankOne ℂ u u : H →L[ℂ] H)
      : H →ₗ[ℂ] H)) := by
  have hle : LinearMap.range ((InnerProductSpace.rankOne ℂ u u : H →L[ℂ] H) : H →ₗ[ℂ] H)
      ≤ Submodule.span ℂ {u} := by
    rw [LinearMap.range_le_iff_comap, eq_top_iff]
    intro z _
    simp only [Submodule.mem_comap, ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
  exact Submodule.finiteDimensional_of_le hle
