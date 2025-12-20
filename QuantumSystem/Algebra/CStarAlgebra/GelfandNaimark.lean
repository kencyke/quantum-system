module

public import QuantumSystem.Algebra.CStarAlgebra.GNS.DirectSum

@[expose] public section

universe u


/--
The **Gelfand-Naimark Theorem** (non-unital version):
Every non-unital C*-algebra `A` is isometrically *-isomorphic to a C*-subalgebra of
bounded operators on some Hilbert space `H`.

We prove this by exhibiting:
1. A Hilbert space `H` (the ℓ²-direct sum of GNS Hilbert spaces over all pure states).
2. A non-unital *-homomorphism `φ : A →⋆ₙₐ[ℂ] 𝓑(H)` (the direct sum of GNS representations).
3. A proof that `φ` is injective and isometric (hence an isometric *-isomorphism onto its image).
-/
theorem gelfand_naimark_theorem :
    ∀ (A: Type u) [NonUnitalCStarAlgebra A],
    ∃ (H : Type u) (_ : ComplexHilbertSpace H),
      ∃ (φ : A →⋆ₙₐ[ℂ] 𝓑(H)), Isometry φ := by
  intro A _
  -- The Hilbert space is the ℓ²-direct sum of GNS Hilbert spaces over all pure states
  let H := GNS.DirectSum.Hilbert A
  -- The representation is the direct sum of all GNS representations
  let φ := GNS.DirectSum.directSumAlgHom (A := A)
  refine ⟨H, inferInstance, φ, ?_⟩
  -- To show φ is an isometry, it suffices to show it preserves norms
  -- (since it's already additive as a *-homomorphism)
  apply AddMonoidHomClass.isometry_of_norm
  intro a
  exact GNS.DirectSum.directSumAlgHom_isometry a
