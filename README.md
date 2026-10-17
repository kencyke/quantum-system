# QuantumSystem

A Lean 4 formalization of quantum systems from an operator-algebraic perspective.

> [!WARNING]
> This project is a work in progress. Breaking API changes — renamed or
> removed declarations, changed signatures, and reorganized modules — happen
> frequently without deprecation.

> [!NOTE]
> This project is currently not accepting contributors because the following areas still need to be addressed:
>
> * Contributing guidelines (including an AI policy)
> * Repository scope and roadmap, including what should and should not be included
> * Documentation (including Lean Blueprint)

## Usage

To depend on this library, add to your project's `lakefile.toml`:

```toml
[[require]]
name = "QuantumSystem"
git = "https://github.com/kencyke/quantum-system"
rev = "v4.x.y" # the release tag matching your lean-toolchain
```

## Highlights

Notable results formalized in this repository:

- **Borchers' Theorem A for relative modular groups, without faithfulness.** For von Neumann
  algebras M₁, M₂, Ω₁ cyclic, Ω₂ separating, arbitrary η₁, η₂ and a bounded V with V†Ω₂ = Ω₁,
  V†η₂ = η₁ and V M₁ V† ⊆ M₂, t ↦ Δ_{η₂,Ω₂}^{-it} V Δ_{η₁,Ω₁}^{it} (imaginary powers vanishing on
  the kernels) continues to the strip 0 ≤ Im z ≤ 1/2 with ‖V(z)‖ ≤ ‖V‖. For faithful ηᵢ, Ωᵢ the
  continuation is Araki–Zsidó's analytic extension theorem (Rev. Math. Phys. 17, 2005, Theorem 2.3)
  for invertible positive operators, once the intertwining V S̄_{η₁,Ω₁} ⊆ S̄_{η₂,Ω₂} V is
  established (their Lemma 2.11 does so for ηᵢ = Ωᵢ). Faulkner–Hollands (arXiv:2010.05513,
  Lemmas 3–4) bound Δ^z V Δ^{-z} on the strip for contractions V induced by channels and continue
  it on vectors, for faithful states, to which they reduce by compressing to the support
  projections.
  - [`Analysis/VonNeumannAlgebra/Modular/Borchers.lean`](QuantumSystem/Analysis/VonNeumannAlgebra/Modular/Borchers.lean) · `VonNeumannAlgebra.exists_relativeModularGroup_continuation` · `VonNeumannAlgebra.exists_relativeModularGroup_continuation_of_le`
- **Interpolation between imaginary powers of non-injective operators.** For self-adjoint A, B
  (only the positive parts enter: A^{1/2} and A^{it} vanish on E_A((−∞, 0])) and bounded V, V′ with
  B^{1/2} V ⊇ V′ A^{1/2}, t ↦ B^{-it} V A^{it} continues, as a family of operators, to the strip
  0 ≤ Im z ≤ 1/2 with ‖F(z)‖ ≤ ‖V‖^{1−2 Im z} ‖V′‖^{2 Im z} and F(t + i/2) = B^{-it} V′ A^{it}.
  Araki–Zsidó (Theorem 2.3) assume A, B invertible, and their proof bounds by max(‖V‖, ‖V′‖);
  Berta–Scholz–Tomamichel (Ann. Henri Poincaré 19, 2018, Lemma 16) allow non-injective A, B but
  state it for vectors, assuming the bounds on the boundary lines. The gap is small: compress to
  the supports.
  - [`Analysis/SpectralTheory/Interpolation.lean`](QuantumSystem/Analysis/SpectralTheory/Interpolation.lean) · `IsSelfAdjoint.exists_stripContinuation`
