module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

@[expose] public section

/-- A complex Hilbert space: a complete normed space with a complex inner product. -/
class ComplexHilbertSpace (H : Type*) extends NormedAddCommGroup H, InnerProductSpace ℂ H, CompleteSpace H

namespace ComplexHilbertSpace

variable {A : Type*} [NonUnitalCStarAlgebra A]
variable (H : Type*) [ComplexHilbertSpace H]

/-- The space of bounded linear operators on a complex Hilbert space. -/
abbrev BoundedLinearOperator := H →L[ℂ] H

/-- Notation for bounded linear operators on a Hilbert space. -/
notation:50 "𝓑(" H ")" => BoundedLinearOperator H

noncomputable instance : NonUnitalCStarAlgebra (𝓑(H)) := inferInstance

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

/-- Unitary maps preserve the inner product. -/
lemma inner_map_eq (U : UnitaryMap H K) (x y : H) : inner ℂ (U.toContinuousLinearMap x) (U.toContinuousLinearMap y) = inner ℂ x y := by
  simp only [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.comp_apply,
    U.adjoint_comp, ContinuousLinearMap.one_apply]

end UnitaryMap
