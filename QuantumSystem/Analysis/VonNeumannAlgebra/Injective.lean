/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.OperatorSystem.Injective.CStarAlgebra
public import QuantumSystem.Analysis.VonNeumannAlgebra.TypeI.Classification

/-!
# Injective von Neumann algebras

A von Neumann algebra `N` on `H` is **injective** when it is injective as an operator system
(`OperatorSystem.Injective N`): completely positive maps into `N` extend along unital complete order
embeddings. As `N` is a unital C⋆-subalgebra of the injective `B(H)`, this is the existence of a
completely positive retraction `E : B(H) → N`, `E x = x` for `x ∈ N`, and, by Tomiyama's theorem, of
a contractive projection from `B(H)` onto `N`, of norm one when `H ≠ 0`
(`LinearMap.IsProj.norm_mkContinuous_eq_one`); both criteria hold for C⋆-subalgebras of any injective
C⋆-algebra (`StarSubalgebra.injective_iff_exists_retraction`,
`StarSubalgebra.injective_iff_exists_isProj`).

Injectivity of C⋆-algebras is invariant under `⋆`-isomorphisms
(`OperatorSystem.Injective.of_starAlgEquiv`), and `B(K)` is injective. So every type I factor,
`⋆`-isomorphic to some `B(K)` by its structure theorem, is injective, and so is every
finite-dimensional von Neumann algebra (`CStarAlgebra.injective_of_finiteDimensional`).

## Main results

* **`VonNeumannAlgebra.injective_iff_exists_retraction`**: `N` is injective iff there is a
  completely positive `E : B(H) → N` restricting to the identity on `N`.
* **`VonNeumannAlgebra.injective_iff_exists_isProj`**: `N` is injective iff there is a projection of
  norm at most one from `B(H)` onto `N`.
* **`VonNeumannAlgebra.IsTypeIFactor.injective`**: a type I factor is injective.

Not formalized: the injectivity of every type I von Neumann algebra, not only of the type I
factors, which needs the decomposition of a type I algebra along its centre; and an example of a
von Neumann algebra that is not injective.
-/

@[expose] public section

open scoped CStarAlgebra

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **A von Neumann algebra is injective iff it is the range of a completely positive retraction of
`B(H)`**: `StarSubalgebra.injective_iff_exists_retraction` for the injective `B(H)`. -/
theorem injective_iff_exists_retraction (N : VonNeumannAlgebra H) :
    OperatorSystem.Injective N ↔ ∃ E : (H →L[ℂ] H) →CP' N, ∀ x : N, E x = x :=
  have : IsClosed (N.toStarSubalgebra : Set (H →L[ℂ] H)) := N.isClosed_coe
  N.toStarSubalgebra.injective_iff_exists_retraction (OperatorSystem.injective_continuousLinearMap H)

/-- **A von Neumann algebra is injective iff it is the range of a contractive projection of
`B(H)`**: `StarSubalgebra.injective_iff_exists_isProj` for the injective `B(H)`. For `H ≠ 0` such a
projection fixes `1 ≠ 0`, so it has norm one (`LinearMap.IsProj.norm_mkContinuous_eq_one`). -/
theorem injective_iff_exists_isProj (N : VonNeumannAlgebra H) :
    OperatorSystem.Injective N ↔ ∃ φ : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H),
      LinearMap.IsProj N.toStarSubalgebra.toNonUnitalStarSubalgebra.toSubmodule φ ∧
        ∀ x, ‖φ x‖ ≤ ‖x‖ :=
  have : IsClosed (N.toStarSubalgebra : Set (H →L[ℂ] H)) := N.isClosed_coe
  N.toStarSubalgebra.injective_iff_exists_isProj (OperatorSystem.injective_continuousLinearMap H)

/-- **A type I factor is injective**: it is `⋆`-isomorphic to some `B(K)`
(`IsTypeIFactor.exists_starAlgEquiv`). -/
theorem IsTypeIFactor.injective {N : VonNeumannAlgebra H} (hN : IsTypeIFactor N) :
    OperatorSystem.Injective N := by
  obtain ⟨K, _, _, _, ⟨e⟩⟩ := hN.exists_starAlgEquiv
  exact OperatorSystem.injective_of_starAlgEquiv_continuousLinearMap e

/-- `B(H)` is an injective factor. -/
example : Algebra.IsCentral ℂ 𝓑(H) ∧ OperatorSystem.Injective 𝓑(H) :=
  ⟨inferInstance, isTypeIFactor_boundedLinearOperators.injective⟩

/-- A finite-dimensional von Neumann algebra is injective. -/
example (N : VonNeumannAlgebra H) [FiniteDimensional ℂ N] : OperatorSystem.Injective N :=
  CStarAlgebra.injective_of_finiteDimensional N

end VonNeumannAlgebra
