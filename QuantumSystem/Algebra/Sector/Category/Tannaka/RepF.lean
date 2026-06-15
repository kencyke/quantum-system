module

public import QuantumSystem.Algebra.Sector.Category.Tannaka.TannakaTarget

/-!
# The reconstruction target: Tannakian structures (`RepF`) — R7-0e (S5)

The Doplicher–Roberts / Tannaka–Krein reconstruction (Müger, *Abstract Duality Theory for
Symmetric Tensor ∗-Categories*, Theorem 2.6/2.12/2.18) produces an equivalence
`C ≌ RepF(G)` of a symmetric tensor ∗-category with the category of finite-dimensional
continuous unitary representations of a compact (super)group `G`.  Abstractly — and this is the
content of Tannaka–Krein — `RepF(G)` is characterised among categories as exactly those that
carry a **∗-preserving symmetric fiber functor** to (finite-dimensional Hilbert spaces, i.e.) a
`TannakaTarget`.

This file fixes that **target interface** (roadmap R7-0e / S5): a `TannakianStructure` on `C` is a
∗-preserving fiber functor `C ⥤ V` into a Tannaka target.  Both endpoints of the reconstruction
are of this form — the reconstructed representation category `RepF(G)` with its forgetful functor
(built later, roadmap S12) and the source `C` once a fiber functor is produced (roadmap S20–S22) —
so the equivalence and its statement are phrased against this single interface.  No group `G`,
finite-dimensionality, or compactness is baked in here (that specialisation is S12); this is the
bare API the reconstruction maps into and out of.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory

universe v₁ v₂ u₁ u₂

/-- A **Tannakian structure** on a symmetric tensor ∗-category `C` (Müger §2, roadmap S5): a
∗-preserving symmetric fiber functor `C ⥤ V` into a Tannaka target `V`.  This is the abstract
form of "`C` is the representation category of a compact (super)group": by Tannaka–Krein a
category admits such a structure iff it is equivalent to `RepF(G)` for some `G`, the group being
reconstructed as the character space of the fiber-functor algebra (`FiberCStarCompletion.lean`,
roadmap S16).  The forgetful functor of `RepF(G)` is the canonical example. -/
structure TannakianStructure (C : Type u₁) [Category.{v₁} C] [Preadditive C] [Linear ℂ C]
    [MonoidalCategory C] [SymmetricCategory C] [DaggerCategory C]
    (V : Type u₂) [Category.{v₂} V] [Preadditive V] [Linear ℂ V]
    [MonoidalCategory V] [SymmetricCategory V] [DaggerMonoidalCategory V] [DaggerLinear V]
    [TannakaTarget V] where
  /-- The underlying fiber functor `C ⥤ V`. -/
  fiber : FiberFunctor C V
  /-- The fiber functor is a ∗-functor (∗-monoidal and ∗-preserving). -/
  isStar : fiber.IsStar

namespace TannakianStructure

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear ℂ C]
    [MonoidalCategory C] [SymmetricCategory C] [DaggerCategory C]
    {V : Type u₂} [Category.{v₂} V] [Preadditive V] [Linear ℂ V]
    [MonoidalCategory V] [SymmetricCategory V] [DaggerMonoidalCategory V] [DaggerLinear V]
    [TannakaTarget V]

instance (T : TannakianStructure C V) : T.fiber.IsStar := T.isStar

/-- The **reconstruction group** of a Tannakian structure (Müger Theorem 2.6): the monoidal
natural automorphisms of the fiber functor.  Its unitary part, topologised via Gelfand duality on
the fiber algebra (`FiberCStarCompletion.lean`), is the reconstructed compact (super)group. -/
noncomputable def reconstructionGroup (T : TannakianStructure C V) : Type (max u₁ v₂) :=
  T.fiber.reconstructionGroup

noncomputable instance (T : TannakianStructure C V) : Group T.reconstructionGroup :=
  inferInstanceAs (Group T.fiber.reconstructionGroup)

/-- The **unitary part** of the reconstruction group (the candidate reconstructed compact group,
Müger Theorem 2.6): the subgroup acting unitarily on every fibre. -/
def unitaryReconstructionSubgroup (T : TannakianStructure C V) :
    Subgroup T.reconstructionGroup :=
  T.fiber.unitaryReconstructionSubgroup

end TannakianStructure

end CategoryTheory
