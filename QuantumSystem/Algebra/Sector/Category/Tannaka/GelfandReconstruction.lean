module

public import QuantumSystem.Algebra.Sector.Category.Tannaka.Characters
public import QuantumSystem.Algebra.Sector.Category.Tannaka.ReconstructedGroup

/-!
# Gelfand reconstruction of the group `G_E` — S16 (R7-E6, Müger Thm 2.30 / Lemma 2.31)

The concrete Tannaka theorem reconstructs the group as the Gelfand spectrum of the C\*-completion
of the fiber algebra (Müger, *Abstract Duality Theory for Symmetric Tensor ∗-Categories*, Theorem
2.30): `G_E = χ(𝓐(E))`, with `𝓐(E) ≅ C(G_E, ℂ)` by Gelfand duality (Mathlib `gelfandStarTransform`,
re-exported here as `gelfandReconstruction`).

Given the C\*-completion `HasCStarCompletion` (roadmap S4, providing the dense-range completion map
`A(E) → 𝓐(E)`), this file builds the genuine link between the Gelfand spectrum `G_E` and the
characters of the *pre-completion* algebra `A(E)`:

* `pullbackCharacter φ` — every point `φ ∈ G_E` (a character of `𝓐(E)`) pulls back along the
  completion map to a character of `A(E)` (Lemma 2.31);
* `pullbackCharacter_injective` — this pullback is **injective**: a point of `G_E` is determined by
  its restriction to the dense subalgebra `A(E)`.  This is the genuine faithfulness of Gelfand
  reconstruction, proved from the *dense range* of the completion map and the *continuity* of
  characters (`DenseRange.equalizer`).

The matching **surjectivity** onto the (unitary) reconstruction group — that every point of `G_E`
comes from a monoidal natural transformation, identifying `G_E` with the reconstructed group of
Müger Theorem 2.6 — rests on the density/fullness of the trace pairing (roadmap S17,
`HasCharacterCorrespondence`), so the full bijection is assembled there.  This is **S16** of the
Tannaka roadmap (`implementation-notes.md` §4).
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

namespace FiberFunctor.HasCStarCompletion

variable (E : FiberFunctor C V) [E.IsStar] [E.HasCStarCompletion]

/-- **Gelfand duality for the reconstructed group** (Müger Theorem 2.30): the C\*-completion
`𝓐(E)` of the fiber algebra is ∗-isomorphic to the continuous functions on the reconstructed
group `G_E = χ(𝓐(E))`.  This is the re-export of `gelfandCompletion` (Mathlib
`gelfandStarTransform`) under the reconstruction-group name. -/
noncomputable def gelfandReconstruction :
    carrier E ≃⋆ₐ[ℂ] C(reconstructedSpace E, ℂ) :=
  gelfandCompletion E

/-- **A point of `G_E` pulls back to a character of `A(E)`** (Müger Lemma 2.31): composing a
character `φ` of the completion `𝓐(E)` (a point of `G_E = reconstructedSpace E =
χ(𝓐(E))`) with the (dense-range) completion map `A(E) → 𝓐(E)` gives a `ℂ`-algebra character of
the pre-completion fiber algebra `A(E)`. -/
noncomputable def pullbackCharacter (φ : WeakDual.characterSpace ℂ (carrier E)) :
    algebra E E →ₐ[ℂ] ℂ :=
  (WeakDual.CharacterSpace.toAlgHom φ).comp (toCompletion (E := E)).toAlgHom

@[simp] lemma pullbackCharacter_apply (φ : WeakDual.characterSpace ℂ (carrier E))
    (a : algebra E E) : pullbackCharacter E φ a = φ (toCompletion (E := E) a) := rfl

/-- **The pullback of characters is injective** (Müger Lemma 2.31, the faithfulness of Gelfand
reconstruction): a point of `G_E` is determined by its values on the dense subalgebra `A(E)`.
Proved from the *dense range* of the completion map `A(E) → 𝓐(E)` (`denseRange_toCompletion`) and
the *continuity* of characters (`WeakDual.CharacterSpace.map_continuous`), via
`DenseRange.equalizer`. -/
lemma pullbackCharacter_injective : Function.Injective (pullbackCharacter E) := by
  intro φ ψ hφψ
  have hfun : (⇑φ : carrier E → ℂ) = ⇑ψ := by
    refine DenseRange.equalizer (denseRange_toCompletion (E := E))
      (map_continuous φ) (map_continuous ψ) (funext fun a => ?_)
    have h := DFunLike.congr_fun hφψ a
    rw [pullbackCharacter_apply, pullbackCharacter_apply] at h
    exact h
  exact WeakDual.CharacterSpace.ext fun x => congrFun hfun x

end FiberFunctor.HasCStarCompletion

end CategoryTheory
