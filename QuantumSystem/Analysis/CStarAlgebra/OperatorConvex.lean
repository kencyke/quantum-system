/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Algebra.CStarAlgebra.GNS.DirectSum
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.OperatorConvex

/-!
# Matrix convex functions are operator convex

For a function `f` continuous on `s`, matrix convexity (`IsMatrixConvexOn`, convexity of
`A ↦ f(A)` on the self-adjoint matrices of every size) implies operator convexity
(`IsOperatorConvexOn`, convexity of `a ↦ f(a)` in every unital C⋆-algebra), so the two notions
agree for continuous functions. In particular `IsOperatorConvexOn.{u} s f` does not depend on the
universe `u` of the C⋆-algebras it quantifies over. The case of bounded operators on a Hilbert
space, `IsMatrixConvexOn.convexOn_continuousLinearMap`, and the specialisation from operator
convexity to matrix convexity, `IsOperatorConvexOn.isMatrixConvexOn`, are in
`QuantumSystem/ForMathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/OperatorConvex.lean`.

## Main results

* `IsMatrixConvexOn.convexOn_cstarAlgebra`, `IsMatrixConvexOn.isOperatorConvexOn`: for `f`
  continuous and matrix convex on `s`, `a ↦ f(a)` is convex in every unital C⋆-algebra, in every
  universe.
* `isOperatorConvexOn_iff_continuousOn_and_isMatrixConvexOn`: `f` is operator convex on `s` iff it
  is continuous and matrix convex on `s`.
* `isOperatorConvexOn_congr_universe`, `IsOperatorConvexOn.convexOn_universe`: operator convexity
  in one universe gives it in every universe.

## Implementation notes

A unital C⋆-algebra `A` is represented faithfully on a Hilbert space by the unital
`*`-homomorphism `GNS.DirectSum.repStarAlgHom A` (Gelfand–Naimark). A faithful unital
`*`-homomorphism commutes with the continuous functional calculus and preserves the spectrum,
hence reflects the order, which transfers the inequality from `𝓑(H)` to `A`
(`ConvexOn.cfc_of_injective`). Only this transfer
needs the GNS construction of the project, and it is the reason this file lives outside
`ForMathlib/`.

## References

The equivalence is standard; cf. Hansen–Pedersen 1982, where operator convexity is defined on
`𝓑(H)`, and Bhatia, Chapter V, where it is defined on the matrices of every size.

* F. Hansen, G. K. Pedersen, *Jensen's inequality for operators and Löwner's theorem*,
  Math. Ann. 258 (1982), 229–241
* R. Bhatia, *Matrix Analysis*, Chapter V (1997)
-/

@[expose] public section

open Set Polynomial
open scoped InnerProductSpace InnerProduct ComplexHilbertSpace

/-! ### Every C⋆-algebra -/

section CStarAlgebra

open ContinuousLinearMap

universe u v

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {s : Set ℝ} {f : ℝ → ℝ}

variable (A) in
/-- **Matrix convexity implies operator convexity**: for `f` continuous and matrix convex on `s`,
`a ↦ f(a)` is convex on the self-adjoint elements with spectrum in `s` of every unital C⋆-algebra
`A`, in every universe. The faithful unital representation `GNS.DirectSum.repStarAlgHom A`
(Gelfand–Naimark) commutes with the functional calculus and reflects the order
(`ConvexOn.cfc_of_injective`), which reduces the inequality to bounded operators
(`IsMatrixConvexOn.convexOn_continuousLinearMap`). -/
theorem IsMatrixConvexOn.convexOn_cstarAlgebra (hc : ContinuousOn f s) (hf : IsMatrixConvexOn s f) :
    ConvexOn ℝ {a : A | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ s} (cfc f) :=
  ConvexOn.cfc_of_injective (GNS.DirectSum.repStarAlgHom A) GNS.DirectSum.repStarAlgHom_injective
    (hf.convexOn_continuousLinearMap _ hc)

/-- A continuous matrix convex function is operator convex. -/
theorem IsMatrixConvexOn.isOperatorConvexOn (hc : ContinuousOn f s) (hf : IsMatrixConvexOn s f) :
    IsOperatorConvexOn.{u} s f :=
  ⟨hc, fun B _ _ _ => hf.convexOn_cstarAlgebra B hc⟩

/-- A function is operator convex on `s` iff it is continuous and matrix convex on `s` (standard;
cf. Hansen–Pedersen 1982, Bhatia, Chapter V). -/
theorem isOperatorConvexOn_iff_continuousOn_and_isMatrixConvexOn :
    IsOperatorConvexOn.{u} s f ↔ ContinuousOn f s ∧ IsMatrixConvexOn s f :=
  ⟨fun h => ⟨h.continuousOn, h.isMatrixConvexOn⟩, fun h => h.2.isOperatorConvexOn h.1⟩

/-- Operator convexity does not depend on the universe of the C⋆-algebras it quantifies over:
`IsOperatorConvexOn.{u} s f ↔ IsOperatorConvexOn.{v} s f`, since both are equivalent to continuity
and matrix convexity. -/
theorem isOperatorConvexOn_congr_universe :
    IsOperatorConvexOn.{u} s f ↔ IsOperatorConvexOn.{v} s f := by
  rw [isOperatorConvexOn_iff_continuousOn_and_isMatrixConvexOn,
    isOperatorConvexOn_iff_continuousOn_and_isMatrixConvexOn]

/-- An operator convex function, given as `IsOperatorConvexOn.{u}`, is convex in every unital
C⋆-algebra of any universe `v` (`isOperatorConvexOn_congr_universe`); the structure field
`IsOperatorConvexOn.convexOn` covers only the universe `u`. -/
theorem IsOperatorConvexOn.convexOn_universe (hf : IsOperatorConvexOn.{u} s f) (B : Type v)
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] :
    ConvexOn ℝ {b : B | IsSelfAdjoint b ∧ spectrum ℝ b ⊆ s} (cfc f) :=
  (isOperatorConvexOn_congr_universe.{u, v}.1 hf).convexOn B

end CStarAlgebra
