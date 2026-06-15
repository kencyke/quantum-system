module

public import QuantumSystem.Algebra.Sector.Category.Tannaka.CompactGroup
public import QuantumSystem.Algebra.Sector.Category.Tannaka.FiberCStarCompletion

/-!
# The reconstructed group `G_E` and the fibre representation — S13 (R7-D/E1/E2)

For a ∗-preserving symmetric fiber functor `E : C ⥤ V` with a C\*-completion of its fiber
algebra (`HasCStarCompletion`, roadmap S4), the **reconstructed group** is the Gelfand
character space `G_E = χ(𝓐(E))` (`reconstructedSpace E`), a compact space (Müger, *Abstract
Duality Theory for Symmetric Tensor ∗-Categories*, Theorem 2.30).  The concrete Tannaka
theorem (Müger Theorem 2.6) endows `G_E` with the structure of a compact **topological
group** — the comultiplication coming from the tensor product of representations (the Hopf
structure of Theorem 2.30) — and produces the **reconstruction functor** `F_E : C ⥤ RepF(G_E)`
sending each object to its fibre with the tautological `G_E`-action.

This file fixes (roadmap S13):

* `HasReconstructedGroup E` — the interface recording that `G_E` is a compact topological
  group (the Hopf/group structure of Theorem 2.30 is the deferred analytic content);
* the **fibre representation** `reconstructionRep E X : Aut_⊗(E) →* Aut (E X)` (this is the
  existing `FiberFunctor.fibreRep`, the fibre-level content of `F_E`), proved genuinely
  *unitary* on the unitary reconstruction subgroup — the defining unitary representation the
  reconstruction functor assigns to `X`.

The target `V` is to be specialised to finite-dimensional Hilbert spaces (`Hilb_f`, roadmap
D1/S13); that specialisation and the full functor `F_E` into `RepF(G_E)` rest on the
density/fullness and Gelfand stages (roadmap S16/S17), so they are stated against the
`TannakianStructure`/`HasReconstructedGroup` interfaces.  This is **S13** of the Tannaka
roadmap (`implementation-notes.md` §4).
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear ℂ C]
    [MonoidalCategory C] [SymmetricCategory C] [DaggerCategory C]
    {V : Type u₂} [Category.{v₂} V] [Preadditive V] [Linear ℂ V]
    [MonoidalCategory V] [SymmetricCategory V] [MonoidalPreadditive V] [MonoidalLinear ℂ V]
    [DaggerMonoidalCategory V] [DaggerLinear V]

/-! ### The reconstructed group `G_E` -/

/-- The **reconstructed group** `G_E` of a fiber functor (Müger Theorem 2.30): the Gelfand
character space `χ(𝓐(E))` of the C\*-completion of the fiber algebra.  It is a compact space;
the compact-group structure is the content of `HasReconstructedGroup`. -/
noncomputable abbrev reconstructedGroup (E : FiberFunctor C V) [E.IsStar]
    [E.HasCStarCompletion] : Type (max u₁ v₂) :=
  FiberFunctor.HasCStarCompletion.reconstructedSpace E

/-- **The reconstructed group carries a compact topological group structure** (Müger Theorem
2.30): on the Gelfand spectrum `G_E = χ(𝓐(E))` the tensor product of representations induces a
comultiplication, making `G_E` a compact topological group (the reconstructed gauge group).
The construction of that group structure (the Hopf structure of Theorem 2.30) is the deferred
analytic content; it is carried as a hypothesis class here, in the style of the rest of this
development.  Compactness already holds (`FiberFunctor.HasCStarCompletion.reconstructedSpace`
is a `CompactSpace`). -/
class FiberFunctor.HasReconstructedGroup (E : FiberFunctor C V) [E.IsStar]
    [E.HasCStarCompletion] where
  /-- The group structure on the reconstructed space `G_E`. -/
  [group : Group (reconstructedGroup E)]
  /-- The group operations on `G_E` are continuous (it is a topological group). -/
  [isTopologicalGroup : IsTopologicalGroup (reconstructedGroup E)]

namespace FiberFunctor.HasReconstructedGroup

variable (E : FiberFunctor C V) [E.IsStar] [E.HasCStarCompletion] [h : E.HasReconstructedGroup]

/-- The group structure on the reconstructed group `G_E`, as an instance. -/
instance instGroup : Group (reconstructedGroup E) := h.group

/-- The reconstructed group `G_E` is a **topological group**, as an instance. -/
instance instIsTopologicalGroup : IsTopologicalGroup (reconstructedGroup E) :=
  letI := h.group; h.isTopologicalGroup

/-- The reconstructed group `G_E` is **compact** (Müger Theorem 2.30): the Gelfand spectrum of
a unital C\*-algebra is compact.  Together with the topological-group structure of
`HasReconstructedGroup` this exhibits `G_E` as a compact topological group. -/
instance instCompactSpace : CompactSpace (reconstructedGroup E) :=
  inferInstanceAs (CompactSpace (FiberFunctor.HasCStarCompletion.reconstructedSpace E))

end FiberFunctor.HasReconstructedGroup

/-! ### The fibre representation (the fibre-level reconstruction functor `F_E`) -/

namespace FiberFunctor

omit [DaggerCategory C] [MonoidalPreadditive V] [MonoidalLinear ℂ V] [DaggerMonoidalCategory V]
  [DaggerLinear V]

variable (E : FiberFunctor C V)

/-- The **fibre representation** of the reconstruction group on the fibre over `X` (Müger
Theorem 2.6, the fibre-level content of the reconstruction functor `F_E`): the group
homomorphism `Aut_⊗(E) →* Aut (E X)` sending a monoidal natural automorphism to its action on
`E X`.  This is exactly `FiberFunctor.fibreRep`; `F_E` assembles these into a functor
`C ⥤ RepF(G_E)`. -/
noncomputable def reconstructionRep (X : C) : E.reconstructionGroup →* Aut (E.functor.obj X) :=
  E.fibreRep X

@[simp] lemma reconstructionRep_apply (X : C) (g : E.reconstructionGroup) :
    (reconstructionRep E X g).hom = reconstructionGroup.act g X := rfl

/-- **The fibre representation is unitary on the unitary reconstruction subgroup** (Müger
Theorem 2.6): for `g` acting unitarily on every fibre, the operator `F_E(X)(g) = act g X` is
unitary.  This is the defining unitary representation the reconstruction functor assigns to the
object `X`. -/
lemma reconstructionRep_unitary [DaggerCategory V] {g : E.reconstructionGroup}
    (hg : g ∈ unitaryReconstructionSubgroup E) (X : C) :
    Unitary (reconstructionRep E X g).hom :=
  unitaryReconstructionSubgroup.unitary_act hg X

end FiberFunctor

end CategoryTheory
