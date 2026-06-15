module

public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.Analysis.Complex.Basic
public import QuantumSystem.Algebra.Sector.Category.Tannaka.CompactGroup

/-!
# The Peter–Weyl property — S18 (R7-E8, Müger Propositions 2.3–2.5)

The concrete Tannaka theorem needs the **Peter–Weyl theorem** for the reconstructed compact group
(Müger, *Abstract Duality Theory for Symmetric Tensor ∗-Categories*, Propositions 2.3–2.5): the
matrix coefficients of finite-dimensional continuous unitary representations — the *representative
functions* — are **dense** in `C(G, ℂ)`, and `G` is determined by them.  The full Peter–Weyl
decomposition (`L²(G) = ⊕ᵨ Hᵨ ⊗ Hᵨ*`) is Mathlib-absent and is one of the two large external
dependencies of the reconstruction (`implementation-notes.md`, "two great bottlenecks").

This file fixes the **interface** (roadmap S18): the class `HasPeterWeyl G` records the
representative functions as a star-subalgebra of `C(G, ℂ)` that **separates points** (the essential
content of Peter–Weyl — distinct group elements are distinguished by some representation).  From
this the genuine analytic consequence follows by the **complex Stone–Weierstrass theorem**:

* the representative functions are **dense** in `C(G, ℂ)` (`HasPeterWeyl.repFunctions_dense`).

This density is exactly what is fed into the Gelfand identification `𝓐(E) ≅ C(G_E, ℂ)` (roadmap
S16/S19) to conclude that the reconstructed group `G_E` is the full compact group.  This is **S18**
of the Tannaka roadmap (`implementation-notes.md` §4).
-/

@[expose] public section

namespace CategoryTheory

universe u

/-- **The Peter–Weyl property** of a compact group (Müger Propositions 2.3–2.5): the
*representative functions* (matrix coefficients of finite-dimensional continuous unitary
representations) form a star-subalgebra of `C(G, ℂ)` that **separates points**.  This is the
essential content of the Peter–Weyl theorem — the irreducible representations distinguish group
elements; the full harmonic-analytic decomposition is Mathlib-absent and deferred, so the property
is carried as a hypothesis class here. -/
class HasPeterWeyl (G : Type u) [Group G] [TopologicalSpace G] [CompactSpace G]
    [IsTopologicalGroup G] [T2Space G] where
  /-- The star-subalgebra of representative functions (matrix coefficients). -/
  repFunctions : StarSubalgebra ℂ C(G, ℂ)
  /-- The representative functions **separate points** (Peter–Weyl: irreducible representations
  distinguish distinct group elements). -/
  separatesPoints : repFunctions.SeparatesPoints

namespace HasPeterWeyl

variable (G : Type u) [Group G] [TopologicalSpace G] [CompactSpace G] [IsTopologicalGroup G]
    [T2Space G] [HasPeterWeyl G]

/-- **The representative functions are dense in `C(G, ℂ)`** (Müger Propositions 2.3–2.5, the
analytic form of Peter–Weyl): a point-separating star-subalgebra of `C(G, ℂ)` for a compact
Hausdorff `G` is dense, by the complex **Stone–Weierstrass theorem**
(`ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints`).  This is the genuine
consequence of the `HasPeterWeyl` interface fed into the Gelfand reconstruction. -/
theorem repFunctions_dense : (repFunctions (G := G)).topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
    (separatesPoints (G := G))

end HasPeterWeyl

end CategoryTheory
