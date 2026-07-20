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

/-- Notation `𝓑(H)` for the bounded linear operators on a Hilbert space, living in the opt-in
`ComplexHilbertSpace` scope; activate it with `open scoped ComplexHilbertSpace`. This is the
type-level counterpart of the von Neumann algebra `𝓑(H)` of `Algebra.VonNeumannAlgebra.Basic`
(they denote the same object B(H) at different levels; see `boundedLinearOperators.starAlgEquiv`). -/
scoped notation:max "𝓑(" H ")" => BoundedLinearOperator H

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

namespace UnitaryMap

/-- Unitary maps preserve the inner product. -/
lemma inner_map_eq (U : UnitaryMap H K) (x y : H) :
    ⟪U.toContinuousLinearMap x, U.toContinuousLinearMap y⟫_ℂ = ⟪x, y⟫_ℂ := by
  simp only [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.comp_apply,
    U.adjoint_comp, ContinuousLinearMap.one_apply]

/-- A unitary map between complex Hilbert spaces, viewed as a linear isometric
equivalence.  The forward map is `U.toContinuousLinearMap` and its inverse is the
adjoint `U.toContinuousLinearMap.adjoint`; the relations `U†U = 1` and `UU† = 1`
make these mutually inverse, and `inner_map_eq` makes the map an isometry. -/
noncomputable def toLinearIsometryEquiv (U : UnitaryMap H K) : H ≃ₗᵢ[ℂ] K :=
  LinearEquiv.isometryOfInner
    { U.toContinuousLinearMap.toLinearMap with
      invFun := U.toContinuousLinearMap.adjoint
      left_inv := fun x => by
        simpa using congrArg (fun f : H →L[ℂ] H => f x) U.adjoint_comp
      right_inv := fun y => by
        simpa using congrArg (fun f : K →L[ℂ] K => f y) U.comp_adjoint }
    U.inner_map_eq

@[simp] lemma toLinearIsometryEquiv_apply (U : UnitaryMap H K) (x : H) :
    U.toLinearIsometryEquiv x = U.toContinuousLinearMap x := rfl

@[simp] lemma toLinearIsometryEquiv_symm_apply (U : UnitaryMap H K) (y : K) :
    U.toLinearIsometryEquiv.symm y = U.toContinuousLinearMap.adjoint y := rfl

end UnitaryMap

end UnitaryMap
