module

public import QuantumSystem.Algebra.Sector.Category.Tannaka.TannakaTarget
public import QuantumSystem.Algebra.Sector.Category.Tannaka.FiberCStarNorm

/-!
# Characters of the fiber algebra and the ∗-structure — S15 (R7-E5, Müger Prop 2.27/2.28)

The concrete Tannaka theorem identifies the monoidal natural transformations `Nat_⊗(E)` of a
fiber functor with the **characters** of its coend algebra `A(E)` (Müger, *Abstract Duality
Theory for Symmetric Tensor ∗-Categories*, Propositions 2.27/2.28).  The **forward** half —
a monoidal natural automorphism `g` gives a character `reconstructionCharacter g : A(E) →ₐ[ℂ] ℂ`
via the trace pairing — was established in `TannakaTarget.lean` (roadmap S15-forward).

This file completes the ∗-structure of the correspondence (roadmap S15):

* `StarTannakaTarget V` — the refinement of `TannakaTarget` adding the ∗-compatibility of the
  trace, `Tr (f†) = conj (Tr f)`, with the genuine consequence that the trace of a self-adjoint
  endomorphism is real;
* the **antipode relation** `reconstructionCharacter g (a⋆) = conj (reconstructionCharacter g⁻¹ a)`
  (`reconstructionCharacter_starQ`): the ∗-involution of `A(E)` corresponds to inversion `g ↦ g⁻¹`
  on the reconstructed group (the antipode of the Hopf structure of Müger Theorem 2.30).  This is
  the genuine `C\*`-content showing the characters respect the ∗-algebra structure;
* `HasCharacterCorrespondence E` — the interface for the **reverse** half (every character of the
  completed algebra arises from a monoidal natural transformation), which rests on density /
  fullness and the C\*-completion (roadmap S16/S17) and so is carried as a hypothesis class.

This is **S15** of the Tannaka roadmap (`implementation-notes.md` §4).
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory FiberFunctor.preAlgebra Limits

universe v₁ v₂ u₁ u₂

/-! ### ∗-compatible Tannaka targets -/

/-- A **∗-compatible Tannaka target** (Müger §1.4, §2.3): a `TannakaTarget` whose categorical
trace is compatible with the dagger, `Tr (f†) = conj (Tr f)`.  This is the extra property the
*∗-characters* require (beyond the bare cyclic/multiplicative trace) and is the structure that
makes the character correspondence respect the ∗-algebra structure of `A(E)`.  It holds for the
intended model of finite-dimensional Hilbert spaces, where the trace is the operator trace and
`Tr (f*) = conj (Tr f)`. -/
class StarTannakaTarget (V : Type u₂) [Category.{v₂} V] [Preadditive V] [Linear ℂ V]
    [MonoidalCategory V] [DaggerCategory V] extends TannakaTarget V where
  /-- **∗-compatibility of the trace**: `Tr (f†) = conj (Tr f)`. -/
  trace_dagger : ∀ {X : V} (f : X ⟶ X),
    TannakaTarget.trace (DaggerCategory.dagger f) = starRingEnd ℂ (TannakaTarget.trace f)

namespace StarTannakaTarget

variable {V : Type u₂} [Category.{v₂} V] [Preadditive V] [Linear ℂ V]
    [MonoidalCategory V] [DaggerCategory V] [StarTannakaTarget V]

/-- The trace of a **self-adjoint** endomorphism is **real** (Müger §1.4): from
`Tr (f†) = conj (Tr f)` and `f† = f` we get `conj (Tr f) = Tr f`. -/
lemma trace_isReal_of_selfAdjoint {X : V} {f : X ⟶ X} (hf : DaggerCategory.dagger f = f) :
    starRingEnd ℂ (TannakaTarget.trace f) = TannakaTarget.trace f := by
  rw [← trace_dagger, hf]

end StarTannakaTarget

/-! ### The antipode relation for reconstruction characters -/

namespace FiberFunctor.preAlgebra

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear ℂ C]
    [MonoidalCategory C] [SymmetricCategory C] [DaggerCategory C] [HasBinaryBiproducts C]
    {V : Type u₂} [Category.{v₂} V] [Preadditive V] [Linear ℂ V]
    [MonoidalCategory V] [SymmetricCategory V] [MonoidalPreadditive V] [MonoidalLinear ℂ V]
    [DaggerMonoidalCategory V] [DaggerLinear V] [StarTannakaTarget V]

/-- **The antipode relation for reconstruction characters** (Müger Proposition 2.28): the
∗-involution of the coend algebra `A(E)` corresponds to inversion `g ↦ g⁻¹` on the reconstructed
group,
`⟨g, a⋆⟩ = conj ⟨g⁻¹, a⟩`,
for a **unitary** reconstruction-group element `g`.  On a generator `[X, s]` this is the chain
`Tr (s† ≫ act g X) = Tr (act g X ≫ s†) = Tr ((act g⁻¹ X)† ≫ s†) = conj (Tr (s ≫ act g⁻¹ X))`,
using cyclicity of the trace, the unitary adjoint relation `(act g⁻¹ X)† = act g X`, and the
∗-compatibility `Tr (f†) = conj (Tr f)` of the target.  This exhibits `reconstructionCharacter`
as respecting the ∗-algebra structure (the antipode of the Hopf structure of Müger Theorem 2.30). -/
lemma reconstructionCharacter_starQ {E : FiberFunctor C V} [E.IsStar]
    {g : E.reconstructionGroup} (hg : g ∈ FiberFunctor.unitaryReconstructionSubgroup E)
    (a : algebra E E) :
    reconstructionCharacter g (star a)
      = starRingEnd ℂ (reconstructionCharacter g⁻¹ a) := by
  obtain ⟨X, s, rfl⟩ := exists_toAlgebra_mk E a
  have hstar : (star (toAlgebra E E (mk X s)) : algebra E E)
      = toAlgebra E E (mk X (DaggerCategory.dagger s)) := by
    change starQ E ‹E.IsStar›.isStarPreserving (toAlgebra E E (mk X s)) = _
    rw [starQ_toAlgebra, starHom_mk]
  have hginv : g⁻¹ ∈ FiberFunctor.unitaryReconstructionSubgroup E := inv_mem hg
  rw [reconstructionCharacter_apply, reconstructionCharacter_apply, hstar,
    pairing_toAlgebra_mk, pairing_toAlgebra_mk,
    reconstructionGroup.toFunctorIso_hom_app, reconstructionGroup.toFunctorIso_hom_app,
    ← StarTannakaTarget.trace_dagger, DaggerCategory.dagger_comp,
    reconstructionGroup.dagger_act hginv X, inv_inv,
    TannakaTarget.trace_comp_comm (DaggerCategory.dagger s) (reconstructionGroup.act g X)]

end FiberFunctor.preAlgebra

/-! ### The reverse direction of the correspondence -/

section Reverse

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear ℂ C]
    [MonoidalCategory C] [SymmetricCategory C] [DaggerCategory C] [HasBinaryBiproducts C]
    {V : Type u₂} [Category.{v₂} V] [Preadditive V] [Linear ℂ V]
    [MonoidalCategory V] [SymmetricCategory V] [MonoidalPreadditive V] [MonoidalLinear ℂ V]
    [DaggerMonoidalCategory V] [DaggerLinear V] [TannakaTarget V]

/-- **The character correspondence is surjective** (Müger Propositions 2.27/2.28, reverse
direction): every `ℂ`-algebra character of the coend algebra `A(E)` arises as the trace pairing
`reconstructionCharacter g` against a (unitary) monoidal natural automorphism `g`.  This is the
content reconstructing the group from its function algebra; it rests on the density/fullness of
the trace pairing and the C\*-completion (roadmap S16/S17, Mathlib-absent), so it is carried as a
hypothesis class here, as with the other deferred statements of this development.  The forward
map `reconstructionCharacter` was constructed in `TannakaTarget.lean`. -/
class FiberFunctor.HasCharacterCorrespondence (E : FiberFunctor C V) [E.IsStar] : Prop where
  /-- Every character of `A(E)` is `reconstructionCharacter g` for some unitary reconstruction
  group element `g`. -/
  exists_reconstructionGroup : ∀ χ : algebra E E →ₐ[ℂ] ℂ,
    ∃ g : E.reconstructionGroup, g ∈ FiberFunctor.unitaryReconstructionSubgroup E ∧
      ∀ a : algebra E E, χ a = FiberFunctor.preAlgebra.reconstructionCharacter g a

end Reverse

end CategoryTheory
