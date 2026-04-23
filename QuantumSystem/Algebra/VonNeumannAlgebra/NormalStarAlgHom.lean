module

public import QuantumSystem.Algebra.VonNeumannAlgebra.NormalState

/-!
# Normal unital *-homomorphisms between von Neumann algebras

A **normal unital *-homomorphism** from `N ⊆ B(H)` into `M ⊆ B(K)`, expressed at
the `B(H) → B(K)` level as a `StarAlgHom` that maps `N.carrier` into `M.carrier`
and has a pullback that takes normal functionals to normal functionals.

This is the Heisenberg-picture counterpart of a quantum channel that embeds the
smaller algebra into the larger one. Araki relative entropy monotonicity is
stated with respect to these morphisms.

## Main definitions

* `VonNeumannAlgebra.NormalStarAlgHom`: the structure bundling `toStarAlgHom`
  (a `B(H) → B(K)` *-homomorphism), `mapsInto` (sending `N.carrier` into
  `M.carrier`), and `normalPullback` (pullback of normal functionals is normal).

Continuity of the underlying `StarAlgHom` is automatic on C*-algebras (*-homs
are contractive); we do not bundle it separately here.

Actually constructing the pulled-back normal state from `toStarAlgHom` +
`normalPullback` requires restricting a B(H)-level normal functional to `N`.
That construction is deferred to the use-site; the monotonicity theorem for
Araki relative entropy takes the pulled-back state as a hypothesis, together
with the extension-level intertwining identity
`ωN.extension h = ωM.extension (α.toStarAlgHom h)`.

## References

* Ohya, M., Petz, D., *Quantum Entropy and Its Use* (1993), Section 5.
* Araki, H., *Relative entropy of states of von Neumann algebras*, Publ. RIMS
  Kyoto Univ. 11 (1975), 809–833.
-/

@[expose] public section

namespace VonNeumannAlgebra

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable [WStarAlgebra (H →L[ℂ] H)] [WStarAlgebra (K →L[ℂ] K)]

/-- A **normal unital *-homomorphism** `α : N → M` between von Neumann algebras
`N ⊆ B(H)` and `M ⊆ B(K)`, presented at the ambient B(H) / B(K) level.

Concretely:
1. `toStarAlgHom : B(H) →⋆ₐ[ℂ] B(K)` is the underlying *-algebra homomorphism.
2. `mapsInto` says this restricts to a map `N.carrier → M.carrier`.
3. `normalPullback` witnesses that the pullback of any normal functional on
   `B(K)` is normal on `B(H)`.

Items 1 and 2 together make `α` a *-homomorphism `N → M`. Item 3 is the
normality condition (weak-* continuity with respect to preduals). The usual
unitality `α 1 = 1` is automatic from `StarAlgHom` (via `map_one`). -/
structure NormalStarAlgHom (N : VonNeumannAlgebra H) (M : VonNeumannAlgebra K) where
  /-- The underlying *-algebra homomorphism B(H) → B(K). -/
  toStarAlgHom : (H →L[ℂ] H) →⋆ₐ[ℂ] (K →L[ℂ] K)
  /-- The homomorphism takes `N.carrier` into `M.carrier`. -/
  mapsInto : ∀ x ∈ N.carrier, toStarAlgHom x ∈ M.carrier
  /-- Normality: the pullback of any normal functional on B(K) by the
  homomorphism is a normal functional on B(H). This is packaged as the
  existence of a matching normal functional on B(H). -/
  normalPullback :
    ∀ (f : (K →L[ℂ] K) →L[ℂ] ℂ), WStarAlgebra.IsNormal (M := K →L[ℂ] K) f →
      ∃ g : (H →L[ℂ] H) →L[ℂ] ℂ,
        WStarAlgebra.IsNormal (M := H →L[ℂ] H) g ∧
        ∀ x : H →L[ℂ] H, g x = f (toStarAlgHom x)

end VonNeumannAlgebra
