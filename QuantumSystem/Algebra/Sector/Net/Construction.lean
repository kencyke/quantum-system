module

public import QuantumSystem.Algebra.QuasiLocalAlgebra.QuasiLocal
public import QuantumSystem.Algebra.Sector.Category.Endomorphism

/-!
# The sector category of a local net

Given a local net (`LocalNetLike L`) and a sector vector `Ω`, the quasi-local
algebra `quasiLocal L Ω` is a unital C\*-algebra
(`LocalNetLike.instCStarAlgebra_quasiLocal`).  Applying the abstract
construction `End(A)` (`Sector/Category/Endomorphism.lean`) with
`A := ↥(quasiLocal L Ω)` realises the **DHR sector category** of the net as a
strict monoidal dagger category, with no further proof obligation: the monoidal
and dagger structure are inherited from the abstract `StarEndoCat` instances.

This is the "construction from a local net" step: the abstract monoidal
C\*-category specialises to the concrete net by choosing `A` to be the
quasi-local algebra.  The further refinements — a *symmetric* structure under a
high-dimensional (permutation-statistics) hypothesis, and a *rigid* structure
under existence of conjugates — are added on top in
`Sector/Net/Symmetric.lean` and `Sector/Net/Rigid.lean` (future work), where
the geometric/duality input enters as explicit hypotheses.
-/

@[expose] public section

namespace LocalNetLike

open CategoryTheory

variable (L : Type*) [DecidableEq L] [LocalNetLike L]
    (Ω : (s : L) → LocalNetLike.localIdx (L := L) s)

/-- The **DHR sector category** of the local net at sector vector `Ω`: the
category of `*`-endomorphisms of the quasi-local algebra, a strict monoidal
dagger category.  The `Category`, `MonoidalCategory` and
`DaggerMonoidalCategory` instances are inherited from `StarEndoCat`. -/
noncomputable abbrev sectorCat : Type _ := StarEndoCat ↥(quasiLocal L Ω)

end LocalNetLike
