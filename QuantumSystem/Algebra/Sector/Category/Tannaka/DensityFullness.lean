module

public import QuantumSystem.Algebra.Sector.Category.Tannaka.GelfandReconstruction

/-!
# Density and fullness of the reconstruction — S17 (R7-E7, Müger §2.3)

The last analytic ingredient of the concrete Tannaka theorem (Müger, *Abstract Duality Theory
for Symmetric Tensor ∗-Categories*, §2.3, Theorem 2.6) is the **density/fullness** of the trace
pairing: every `ℂ`-algebra character of the fiber algebra `A(E)` is *bounded* for the C\*-seminorm,
hence **extends** to a character of the completion `𝓐(E)` — a point of the reconstructed group
`G_E = χ(𝓐(E))`.  Equivalently, the pullback map `G_E → χ(A(E))` (`pullbackCharacter`, S16) is
*surjective*.

This file fixes that property as the interface `HasReconstructionDensity` (the bound /
extension is the Mathlib-absent analytic content, deferred in the style of the rest of this
development) and draws the genuine consequence:

* combined with the *injectivity* of `pullbackCharacter` proved in S16, density yields a genuine
  **bijection** `G_E ≃ χ(A(E))` (`pullbackCharacterEquiv`) — the reconstructed group is exactly
  the spectrum of the fiber algebra.

Composing with the character correspondence `HasCharacterCorrespondence` (S15, every character of
`A(E)` is `reconstructionCharacter g` for a unitary `g`) identifies `G_E` with the unitary
reconstruction group — the fullness underlying the equivalence `C ≌ RepF(G_E)` assembled in S19.
This is **S17** of the Tannaka roadmap (`implementation-notes.md` §4).
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory FiberFunctor.preAlgebra FiberFunctor.HasCStarCompletion

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear ℂ C]
    [MonoidalCategory C] [SymmetricCategory C] [DaggerCategory C]
    {V : Type u₂} [Category.{v₂} V] [Preadditive V] [Linear ℂ V]
    [MonoidalCategory V] [SymmetricCategory V] [MonoidalPreadditive V] [MonoidalLinear ℂ V]
    [DaggerMonoidalCategory V] [DaggerLinear V]

/-- **Density of the reconstruction** (Müger §2.3, Theorem 2.6): every `ℂ`-algebra character of
the fiber algebra `A(E)` extends to a character of the C\*-completion `𝓐(E)` — i.e. the pullback
map `G_E → χ(A(E))` is *surjective*.  Analytically this is the statement that characters of `A(E)`
are bounded for the C\*-seminorm (roadmap S14, Mathlib-absent), so it is carried as a hypothesis
class here, as with the other deferred analytic statements of this development. -/
class FiberFunctor.HasReconstructionDensity (E : FiberFunctor C V) [E.IsStar]
    [E.HasCStarCompletion] : Prop where
  /-- Every character of `A(E)` arises (by extension) from a point of `G_E = χ(𝓐(E))`. -/
  surjective_pullbackCharacter : Function.Surjective (pullbackCharacter E)

namespace FiberFunctor.HasCStarCompletion

variable (E : FiberFunctor C V) [E.IsStar] [E.HasCStarCompletion]
    [E.HasReconstructionDensity]

/-- **The reconstructed group is the spectrum of the fiber algebra** (Müger Theorem 2.6): the
pullback map is a *bijection* `G_E ≃ χ(A(E))` between the reconstructed group `G_E = χ(𝓐(E))` and
the characters of the pre-completion fiber algebra `A(E)`.  Injectivity is the faithfulness proved
in S16 (`pullbackCharacter_injective`); surjectivity is the density `HasReconstructionDensity`. -/
noncomputable def pullbackCharacterEquiv :
    WeakDual.characterSpace ℂ (carrier E) ≃ (algebra E E →ₐ[ℂ] ℂ) :=
  Equiv.ofBijective (pullbackCharacter E)
    ⟨pullbackCharacter_injective E,
      FiberFunctor.HasReconstructionDensity.surjective_pullbackCharacter⟩

@[simp] lemma pullbackCharacterEquiv_apply (φ : WeakDual.characterSpace ℂ (carrier E)) :
    pullbackCharacterEquiv E φ = pullbackCharacter E φ := rfl

/-- The bijection `G_E ≃ χ(A(E))` sends a point of `G_E` to its restriction to `A(E)`, and its
inverse recovers the unique extension to the completion. -/
@[simp] lemma pullbackCharacterEquiv_symm_apply (χ : algebra E E →ₐ[ℂ] ℂ) :
    pullbackCharacter E (pullbackCharacterEquiv E |>.symm χ) = χ :=
  (pullbackCharacterEquiv E).apply_symm_apply χ

end FiberFunctor.HasCStarCompletion

end CategoryTheory
