module

public import Mathlib.Analysis.VonNeumannAlgebra.Basic

/-!
# The greatest von Neumann algebra: the algebra of all bounded operators

The von Neumann subalgebras of `B(H) = H →L[ℂ] H` form a bounded lattice under inclusion, whose
greatest element is `B(H)` itself — the algebra of *all* bounded linear operators (the operator-
algebra literature's name for it; "top element" is the order-theoretic name for the same object).
Mathlib's `VonNeumannAlgebra H` carries only a `PartialOrder` (via `SetLike`) and no `Top` instance,
so `(⊤ : VonNeumannAlgebra H)` does not yet elaborate. This file supplies that `Top` instance: the
carrier is all of `H →L[ℂ] H`, and the double-commutant law holds because the bicommutant of the
whole set is itself (`Set.subset_centralizer_centralizer` together with `Set.subset_univ`).

This is the natural home for further lattice structure on `VonNeumannAlgebra H` (meets as
intersections, joins as generated algebras) should it be added; only the top element is needed here.

## Main declarations

* `Top (VonNeumannAlgebra H)` — the greatest element `⊤`, the algebra of all bounded operators.
* `VonNeumannAlgebra.coe_top` / `VonNeumannAlgebra.mem_top` — its carrier is everything.
-/

@[expose] public section

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The **algebra of all bounded operators** `B(H) = H →L[ℂ] H`, as the greatest element `⊤` of the
inclusion order on `VonNeumannAlgebra H`. Its carrier is `Set.univ`; the double-commutant property is
the bicommutant inclusion `s ⊆ s''` applied to `s = univ`, together with `univ` being the largest
set. -/
noncomputable instance : Top (VonNeumannAlgebra H) where
  top :=
    { toStarSubalgebra := ⊤
      centralizer_centralizer' :=
        Set.Subset.antisymm (Set.subset_univ _) Set.subset_centralizer_centralizer }

@[simp] lemma coe_top : ((⊤ : VonNeumannAlgebra H) : Set (H →L[ℂ] H)) = Set.univ := rfl

/-- Every bounded operator lies in the full algebra `⊤ = B(H)`. -/
@[simp] lemma mem_top (x : H →L[ℂ] H) : x ∈ (⊤ : VonNeumannAlgebra H) := Set.mem_univ x

end VonNeumannAlgebra
