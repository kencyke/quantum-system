module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

@[expose] public section

open scoped InnerProductSpace

/-- A complex *pre*-Hilbert space: a normed space with a complex inner product. -/
class ComplexPreHilbertSpace (H : Type*) extends NormedAddCommGroup H, InnerProductSpace ℂ H

/-- A complex Hilbert space: a complete normed space with a complex inner product. -/
class ComplexHilbertSpace (H : Type*) extends ComplexPreHilbertSpace H, CompleteSpace H

namespace ComplexHilbertSpace

variable {A : Type*} [NonUnitalCStarAlgebra A]
variable (H : Type*) [ComplexHilbertSpace H]

/-- The space of bounded linear operators on a complex Hilbert space. -/
abbrev BoundedLinearOperator := H →L[ℂ] H

/-- Notation for bounded linear operators on a Hilbert space. -/
notation:50 "𝓑(" H ")" => BoundedLinearOperator H

noncomputable instance : NonUnitalCStarAlgebra (𝓑(H)) := inferInstance

/-- Any complex Hilbert space is, in particular, a complex pre-Hilbert space. -/
noncomputable instance instPreComplexHilbertSpace [ComplexHilbertSpace H] : ComplexPreHilbertSpace H where
  toNormedAddCommGroup := (inferInstance : NormedAddCommGroup H)
  toInnerProductSpace := (inferInstance : InnerProductSpace ℂ H)

end ComplexHilbertSpace

section UnitaryMap

variable {H K : Type*} [ComplexHilbertSpace H] [ComplexHilbertSpace K]

/-- A unitary map between complex Hilbert spaces satisfies `U†U = 1` and `UU† = 1`.
This extends the notion of unitary elements to maps between possibly different Hilbert spaces. -/
structure UnitaryMap (H K : Type*) [ComplexHilbertSpace H] [ComplexHilbertSpace K] where
  /-- The underlying continuous linear map. -/
  toContinuousLinearMap : H →L[ℂ] K
  /-- The relation `U†U = 1`. -/
  adjoint_comp : toContinuousLinearMap.adjoint ∘L toContinuousLinearMap = 1
  /-- The relation `UU† = 1`. -/
  comp_adjoint : toContinuousLinearMap ∘L toContinuousLinearMap.adjoint = 1

instance : Coe (UnitaryMap H K) (H →L[ℂ] K) :=
  ⟨UnitaryMap.toContinuousLinearMap⟩

/-- A linear isometric equivalence yields a unitary-between map. -/
noncomputable def asUnitary (U : H ≃ₗᵢ[ℂ] K) : UnitaryMap H K where
  toContinuousLinearMap := (U : H →L[ℂ] K)
  adjoint_comp := by
    ext x
    simp [LinearIsometryEquiv.adjoint_eq_symm]
  comp_adjoint := by
    ext y
    simp [LinearIsometryEquiv.adjoint_eq_symm]

/-- The identity unitary map on a complex Hilbert space. -/
noncomputable def UnitaryMap.refl (H : Type*) [ComplexHilbertSpace H] :
    UnitaryMap H H where
  toContinuousLinearMap := ContinuousLinearMap.id ℂ H
  adjoint_comp := by rw [ContinuousLinearMap.adjoint_id]; ext; simp
  comp_adjoint := by rw [ContinuousLinearMap.adjoint_id]; ext; simp

@[simp] lemma UnitaryMap.refl_toContinuousLinearMap (H : Type*)
    [ComplexHilbertSpace H] :
    (UnitaryMap.refl H).toContinuousLinearMap = ContinuousLinearMap.id ℂ H :=
  rfl

/-- Unitary maps preserve the inner product. -/
lemma inner_map_eq (U : UnitaryMap H K) (x y : H) :
    ⟪U.toContinuousLinearMap x, U.toContinuousLinearMap y⟫_ℂ = ⟪x, y⟫_ℂ := by
  simp only [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.comp_apply,
    U.adjoint_comp, ContinuousLinearMap.one_apply]

/-- A `UnitaryMap` between complex Hilbert spaces canonically yields a
linear isometric equivalence (the inverse is the adjoint). -/
noncomputable def UnitaryMap.toLinearIsometryEquiv (U : UnitaryMap H K) :
    H ≃ₗᵢ[ℂ] K where
  toFun := U.toContinuousLinearMap
  invFun := U.toContinuousLinearMap.adjoint
  left_inv x := by
    have := congrArg (fun (f : H →L[ℂ] H) => f x) U.adjoint_comp
    simpa using this
  right_inv y := by
    have := congrArg (fun (f : K →L[ℂ] K) => f y) U.comp_adjoint
    simpa using this
  map_add' := map_add U.toContinuousLinearMap
  map_smul' := map_smul U.toContinuousLinearMap
  norm_map' x := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
    simp only [← @inner_self_eq_norm_sq ℂ]
    exact congr_arg RCLike.re (inner_map_eq U x x)

end UnitaryMap
