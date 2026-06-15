module

public import QuantumSystem.Algebra.Sector.Category.Tannaka.DensityFullness
public import QuantumSystem.Algebra.Sector.Category.Tannaka.PeterWeyl
public import QuantumSystem.Algebra.Sector.Category.Tannaka.RepF

/-!
# The concrete Tannaka theorem — S19 (R7-E9, Müger Theorem 2.6)

This file assembles the concrete C\*-Tannaka theorem (Müger, *Abstract Duality Theory for
Symmetric Tensor ∗-Categories*, Theorem 2.6) from the stages built in roadmap S13–S18: a
∗-preserving symmetric fiber functor `E : C ⥤ V` with the analytic data of the reconstruction
(the C\*-completion `HasCStarCompletion`, the reconstructed group `HasReconstructedGroup`, the
character correspondence `HasCharacterCorrespondence`, the density `HasReconstructionDensity`)
reconstructs the group `G_E` as exactly the unitary monoidal natural transformations of `E`.

The deliverables (roadmap S19):

* `tannakianStructure E` — the fiber functor `E` *is* a `TannakianStructure` on `C` (the abstract
  form of "`C` is the representation category `RepF(G_E)`", `RepF.lean`, S5);
* `HasConcreteTannaka E` — the class bundling the analytic hypotheses of the reconstruction;
* **`reconstructionCharacter_surjective`** — the genuine reconstruction statement assembled from
  S15/S16/S17: *every point of the reconstructed group `G_E` arises from a unitary monoidal natural
  automorphism of `E`* (its character is `reconstructionCharacter g`), so `G_E` is realised by the
  unitary reconstruction group.  This is the surjectivity at the heart of `C ≌ RepF(G_E)`;
* the categorical faithfulness (`totalFibreRep_injective`, `FiberFunctor.lean`) supplies the other
  half.

The full *equivalence of categories* `C ≌ RepF(G_E)` additionally requires `RepF(G_E)` as a concrete
symmetric tensor ∗-category (roadmap C2/C3, Mathlib-absent) and the Peter–Weyl completeness
(`HasPeterWeyl`, S18); it is carried as the interface `HasConcreteTannaka` here, assembled from the
genuine reconstruction below.  This is **S19** of the Tannaka roadmap (`implementation-notes.md`
§4), completing **Phase 2**.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory FiberFunctor.preAlgebra FiberFunctor.HasCStarCompletion Limits

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear ℂ C]
    [MonoidalCategory C] [SymmetricCategory C] [DaggerCategory C] [HasBinaryBiproducts C]
    {V : Type u₂} [Category.{v₂} V] [Preadditive V] [Linear ℂ V]
    [MonoidalCategory V] [SymmetricCategory V] [MonoidalPreadditive V] [MonoidalLinear ℂ V]
    [DaggerMonoidalCategory V] [DaggerLinear V] [TannakaTarget V]

/-! ### The fiber functor as a Tannakian structure -/

/-- **The fiber functor exhibits `C` as a representation category** (Müger Theorem 2.6): a
∗-preserving symmetric fiber functor `E : C ⥤ V` packages into a `TannakianStructure` on `C` —
the abstract form (`RepF.lean`, roadmap S5) of "`C ≌ RepF(G_E)`".  The reconstruction theorem
identifies the reconstruction group with the compact (super)group `G_E`. -/
noncomputable def tannakianStructure (E : FiberFunctor C V) [E.IsStar] :
    TannakianStructure C V where
  fiber := E
  isStar := ‹E.IsStar›

/-! ### The bundled hypotheses of the concrete Tannaka theorem -/

/-- **The data of the concrete Tannaka theorem** (Müger Theorem 2.6; roadmap S19): a
∗-preserving symmetric fiber functor together with the analytic ingredients reconstructing the
group — the C\*-completion of the fiber algebra (S4/S14), the reconstructed compact group `G_E`
(S13), the character correspondence (S15) and the density of the reconstruction (S17).  Bundling
these records exactly what the reconstruction equivalence `C ≌ RepF(G_E)` consumes. -/
class FiberFunctor.HasConcreteTannaka (E : FiberFunctor C V) [E.IsStar] where
  /-- The C\*-completion of the fiber algebra (S4/S14). -/
  [hasCStarCompletion : E.HasCStarCompletion]
  /-- The reconstructed compact group `G_E` (S13). -/
  [hasReconstructedGroup : E.HasReconstructedGroup]
  /-- The character correspondence (S15). -/
  [hasCharacterCorrespondence : E.HasCharacterCorrespondence]
  /-- The density of the reconstruction (S17). -/
  [hasReconstructionDensity : E.HasReconstructionDensity]

namespace FiberFunctor.HasConcreteTannaka

variable (E : FiberFunctor C V) [E.IsStar] [hT : E.HasConcreteTannaka]

instance instHasCStarCompletion : E.HasCStarCompletion := hT.hasCStarCompletion

instance instHasReconstructedGroup : E.HasReconstructedGroup := hT.hasReconstructedGroup

instance instHasCharacterCorrespondence : E.HasCharacterCorrespondence :=
  hT.hasCharacterCorrespondence

instance instHasReconstructionDensity : E.HasReconstructionDensity := hT.hasReconstructionDensity

end FiberFunctor.HasConcreteTannaka

/-! ### The reconstruction theorem -/

/-- **The reconstructed group is realised by the unitary monoidal natural transformations** (Müger
Theorem 2.6, the heart of the concrete Tannaka theorem): every point `φ` of the reconstructed group
`G_E = χ(𝓐(E))` arises from a **unitary** monoidal natural automorphism `g` of the fiber functor —
its character on the fiber algebra `A(E)` is the trace pairing `reconstructionCharacter g`.

This is assembled genuinely from the earlier stages: `φ` restricts (along the dense completion map)
to a character of `A(E)` (`pullbackCharacter`, S16), which by the character correspondence
(`HasCharacterCorrespondence`, S15) is `reconstructionCharacter g` for some unitary `g`.  Together
with the faithfulness `FiberFunctor.totalFibreRep_injective` this is the bijection underlying
`C ≌ RepF(G_E)`. -/
theorem reconstructionCharacter_surjective (E : FiberFunctor C V) [E.IsStar]
    [E.HasCStarCompletion] [E.HasCharacterCorrespondence]
    (φ : WeakDual.characterSpace ℂ (carrier E)) :
    ∃ g : E.reconstructionGroup, g ∈ FiberFunctor.unitaryReconstructionSubgroup E ∧
      ∀ a : algebra E E, φ (toCompletion (E := E) a) = reconstructionCharacter g a := by
  obtain ⟨g, hg, hgeq⟩ :=
    FiberFunctor.HasCharacterCorrespondence.exists_reconstructionGroup (pullbackCharacter E φ)
  exact ⟨g, hg, fun a => (pullbackCharacter_apply E φ a).symm.trans (hgeq a)⟩

/-- **The concrete Tannaka theorem, assembled form** (Müger Theorem 2.6): under the bundled
reconstruction data, every point of the reconstructed group `G_E` is the character of a unitary
monoidal natural automorphism.  This packages `reconstructionCharacter_surjective` against the
`HasConcreteTannaka` interface — the surjectivity half of `C ≌ RepF(G_E)`. -/
theorem concreteTannaka (E : FiberFunctor C V) [E.IsStar] [E.HasConcreteTannaka]
    (φ : WeakDual.characterSpace ℂ (carrier E)) :
    ∃ g : E.reconstructionGroup, g ∈ FiberFunctor.unitaryReconstructionSubgroup E ∧
      ∀ a : algebra E E, φ (toCompletion (E := E) a) = reconstructionCharacter g a :=
  reconstructionCharacter_surjective E φ

end CategoryTheory
