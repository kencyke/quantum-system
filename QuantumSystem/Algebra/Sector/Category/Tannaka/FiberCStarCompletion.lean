module

public import Mathlib.Analysis.CStarAlgebra.GelfandDuality
public import QuantumSystem.Algebra.Sector.Category.Tannaka.FiberAlgebra

/-!
# The C\*-completion of the fiber algebra — R7-0d (S4)

For a ∗-preserving symmetric fiber functor `E : C ⥤ V` the coend algebra
`A(E) = ∫^X End_V(E X)` is a **commutative unital star `ℂ`-algebra** (`FiberAlgebra.lean`).
The concrete Tannaka theorem (Müger, *Abstract Duality Theory for Symmetric Tensor
∗-Categories*, Theorem 2.6 / Theorem 2.30) reconstructs the group as the **Gelfand
spectrum** of the *C\*-completion* of `A(E)`: one equips `A(E)` with a C\*-norm
(Proposition 2.22–2.24) — submultiplicative, satisfying `‖a⋆ a‖ = ‖a‖²` — completes it to a
commutative unital C\*-algebra `𝓐(E)`, and identifies `G_E = χ(𝓐(E))` via Gelfand duality
(`gelfandStarTransform`).

The *construction* of that norm (via GNS / states / positivity) is Mathlib-absent and is the
substantive analytic content deferred to the rest of R7-E (roadmap S14, "barrier 4").  This
file fixes the **intermediate specification** (roadmap R7-0d / S4): a class
`HasCStarCompletion E` recording a commutative unital C\*-algebra `𝓐(E)` together with a
dense-range ∗-algebra homomorphism `A(E) → 𝓐(E)`.  Downstream stages (S16) assume
`[E.HasCStarCompletion]` and obtain the reconstructed space `G_E := χ(𝓐(E))` and the Gelfand
isomorphism `𝓐(E) ≃⋆ₐ[ℂ] C(G_E, ℂ)` with no further analytic work; supplying the instance for
a concrete model is the remaining `S14` task.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory FiberFunctor.preAlgebra

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear ℂ C]
    [MonoidalCategory C] [SymmetricCategory C] [DaggerCategory C]
    {V : Type u₂} [Category.{v₂} V] [Preadditive V] [Linear ℂ V]
    [MonoidalCategory V] [SymmetricCategory V] [MonoidalPreadditive V] [MonoidalLinear ℂ V]
    [DaggerMonoidalCategory V] [DaggerLinear V]

/-- **A C\*-completion of the fiber algebra** (Müger §2.3, Proposition 2.22–2.24; roadmap
R7-0d / S4): a commutative unital C\*-algebra `carrier = 𝓐(E)` together with a ∗-algebra
homomorphism `A(E) → 𝓐(E)` with dense range.  This is the intermediate specification standing
in for the C\*-norm/completion of the coend algebra; the analytic construction of the norm
(GNS / positivity, Mathlib-absent) is deferred (roadmap S14).  Once available, the
reconstructed group is the Gelfand spectrum `χ(𝓐(E))` (`reconstructedSpace`). -/
class FiberFunctor.HasCStarCompletion (E : FiberFunctor C V) [E.IsStar] where
  /-- The completion `𝓐(E)`, a commutative unital C\*-algebra. -/
  carrier : Type (max u₁ v₂)
  /-- The commutative unital C\*-algebra structure on the completion. -/
  [commCStarAlgebra : CommCStarAlgebra carrier]
  /-- The completion map `A(E) → 𝓐(E)`, a unital ∗-algebra homomorphism. -/
  toCompletion : algebra E E →⋆ₐ[ℂ] carrier
  /-- The completion map has dense range (`𝓐(E)` is the closure of the image of `A(E)`). -/
  denseRange_toCompletion : DenseRange toCompletion

namespace FiberFunctor.HasCStarCompletion

/-- The commutative unital C\*-algebra structure on the completion, as an instance. -/
instance instCommCStarAlgebra (E : FiberFunctor C V) [E.IsStar] [h : E.HasCStarCompletion] :
    CommCStarAlgebra (carrier E) :=
  h.commCStarAlgebra

/-- The **reconstructed space** `G_E` (Müger Theorem 2.30): the Gelfand character space of the
C\*-completion `𝓐(E)`.  For the even reconstruction this carries the structure of a compact
group (the reconstructed gauge group); identifying that group structure is the substance of the
later Gelfand/Tannaka stages (roadmap S16/S19). -/
noncomputable def reconstructedSpace (E : FiberFunctor C V) [E.IsStar] [E.HasCStarCompletion] :
    Type (max u₁ v₂) :=
  WeakDual.characterSpace ℂ (carrier E)

noncomputable instance (E : FiberFunctor C V) [E.IsStar] [E.HasCStarCompletion] :
    TopologicalSpace (reconstructedSpace E) :=
  inferInstanceAs (TopologicalSpace (WeakDual.characterSpace ℂ (carrier E)))

instance (E : FiberFunctor C V) [E.IsStar] [E.HasCStarCompletion] :
    CompactSpace (reconstructedSpace E) :=
  inferInstanceAs (CompactSpace (WeakDual.characterSpace ℂ (carrier E)))

/-- **Gelfand duality for the fiber-algebra completion** (Müger Theorem 2.30): the C\*-completion
`𝓐(E)` is ∗-isomorphic to the continuous functions on its character space `G_E`.  This is the
analytic heart of the concrete Tannaka theorem — the reconstructed group sits inside `G_E` and
`𝓐(E)` is recovered as functions on it. -/
noncomputable def gelfandCompletion (E : FiberFunctor C V) [E.IsStar] [E.HasCStarCompletion] :
    carrier E ≃⋆ₐ[ℂ] C(reconstructedSpace E, ℂ) :=
  gelfandStarTransform (carrier E)

end FiberFunctor.HasCStarCompletion

end CategoryTheory
