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
> * Roadmap
> * Documentation (including Lean Blueprint)

## Scope

QuantumSystem aims to formalize **reconstruction**: recovering an algebraic or group-theoretic
structure from data that carry less of it. A functor sends structures to data: a compact group to
its symmetric tensor category of representations, a p-divisible group to its Tate module, a
C⋆-algebra to its underlying operator system or to a system of finite-dimensional completely
positive approximations. Each reconstruction asks whether this functor is fully faithful, up to
the isomorphisms its target allows, and what its essential image is:

- **Uniqueness.** Every morphism of the data comes from a morphism of the structures, unique up
  to the appropriate isomorphism: a symmetric tensor functor Rep H → Rep G from a homomorphism
  G → H unique up to conjugation, a Galois-equivariant map of Tate modules from a unique
  homomorphism of p-divisible groups. In particular, isomorphic data come from isomorphic
  structures.
- **Existence.** The data that come from a structure are characterized intrinsically, and the
  structure is rebuilt from them: a group, with its group law, as the tensor automorphisms of a
  fiber functor; an algebra, with its multiplication, on an operator system.

Four methods recur in the answers:

1. **Multiplication from positivity.** A unital completely positive map need not be
   multiplicative, but the image of an idempotent one, Φ, is a C⋆-algebra under the product
   Φ(XY), and a unital complete order isomorphism between C⋆-algebras is a ⋆-isomorphism: the
   matrix order determines the multiplication. Quantitatively, a finite-dimensional algebra
   satisfying the C⋆-axioms up to ε is O(ε)-isomorphic to a C⋆-algebra, with a constant
   independent of the dimension.
2. **Invariants under a group action.** For a group acting on a module, the fixed points are the
   first invariant: for a compact group acting by automorphisms of a C⋆-algebra, Haar averaging is
   a conditional expectation onto them; for a Galois group acting semilinearly on a p-adic Banach
   space, a normalized trace takes its place. Characters, or irreducible representations, then cut
   the rest into spectral subspaces, which span a dense subspace in the first case and, after
   extending scalars, the whole module in the second (the Hodge–Tate decomposition). The fixed
   points alone do not determine the whole: the input is the symmetric tensor category of
   endomorphisms of the fixed-point algebra induced by the spectral subspaces (the superselection
   sectors), which is equivalent to the representation category of the group and determines both
   the group and the whole.
3. **Finite stages.** An infinite object is an inductive limit of finite or finite-dimensional
   ones: a p-divisible group of its finite group schemes of pⁿ-torsion, a C⋆-algebra of
   finite-dimensional C⋆-algebras along completely positive contractions. Short exact sequences
   0 → X′ → X → X″ → 0 reduce it to simpler pieces. When the connecting maps are completely
   positive but not multiplicative, the limit is an operator system, and it is completely order
   isomorphic to a C⋆-algebra exactly when the connecting maps are asymptotically order zero: the
   product of two elements is then the limit of the images of their products at finite stages,
   a compressed product as in method 1. The stronger condition of asymptotic multiplicativity
   reaches only the quasidiagonal algebras.
4. **Rigidity and obstructions.** A quantity monotone under morphisms detects reversibility:
   relative entropy satisfies D(N(ρ) ‖ N(σ)) ≤ D(ρ ‖ σ) for a quantum channel N, with equality
   exactly when a recovery channel, the Petz map, inverts N on ρ and σ; when N is reversible on
   every state of a subalgebra, the dual of the recovery channel is a ⋆-homomorphism on it, and
   near-equality gives an approximate recovery that is approximately multiplicative. The defect
   of an approximate structure, such as the associativity defect of a multiplication, is a
   cocycle, and its class is the obstruction to removing it. Vanishing cohomology removes it only
   with bounds growing with the dimension, so the dimension-independent constant of method 1
   comes from building the C⋆-algebra inductively from approximate projections, cohomology
   reducing the error at each step.

Out of scope is what enters no reconstruction: quantum algorithms and circuits, and the numerical
or perturbative analysis of specific models.

## Usage

To depend on this library, add to your project's `lakefile.toml`:

```toml
[[require]]
name = "QuantumSystem"
git = "https://github.com/kencyke/quantum-system"
rev = "v4.x.y" # the release tag matching your lean-toolchain
```

## Highlights

Notable results formalized in this repository. Both are the analytic input to method 4 of the
Scope: the monotonicity of relative entropy and the Petz recovery, in the generality of von
Neumann algebras, rest on continuing t ↦ Δ^{-it} V Δ^{it} to a strip.

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
