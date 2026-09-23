/-
Copyright (c) 2025 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# Bundled complex (pre-)Hilbert spaces

This file introduces the bundled classes `ComplexPreHilbertSpace` (a complex inner product space)
and `ComplexHilbertSpace` (a complete one), the abbreviation
`ComplexHilbertSpace.BoundedLinearOperator` for `H →L[ℂ] H` with the scoped notation `𝓑(H)`, and
the instance making `ℂ` a complex Hilbert space.
-/

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

/-- `ℂ` is a complex Hilbert space over itself — the one-dimensional one. It is the smallest
nondegenerate space on which the bundled `ComplexHilbertSpace` interfaces can be exercised, and
the class has no instance for it otherwise, since its three parents are found separately. -/
noncomputable instance : ComplexHilbertSpace ℂ where
