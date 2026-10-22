# QuantumSystem

A Lean 4 formalization of quantum systems through reconstruction theorems and the
operator-algebraic and cohomological arguments they share.

> [!WARNING]
> This project is a work in progress. Breaking API changes — renamed or
> removed declarations, changed signatures, and reorganized modules — happen
> frequently without deprecation.

> [!NOTE]
> This project is currently not accepting contributors because the following areas still need to be addressed:
>
> * Contributing guidelines (including an AI policy)
> * Documentation (including Lean Blueprint)

## Scope

QuantumSystem aims to formalize **reconstruction**: recovering an algebraic or group-theoretic
structure from data that carry less of it. A functor sends structures to data, contravariantly
for groups and covariantly for algebras: a compact group G to the symmetric tensor C⋆-category
Rep G of its finite-dimensional unitary representations, a unital C⋆-algebra to its underlying
operator system. Each reconstruction asks how far this functor is full and faithful in the
2-categorical sense, matching morphisms up to the isomorphisms its target allows, and what its
essential image is:

- **Uniqueness.** Every morphism of the data comes from a morphism of the structures, unique up
  to the appropriate isomorphism: every symmetric tensor ⋆-functor Rep H → Rep G is, up to unitary
  tensor isomorphism, restriction along a continuous homomorphism G → H, unique up to
  conjugation in H. Where the data have more morphisms than the structures, as a unital
  completely positive map between C⋆-algebras need not be a ⋆-homomorphism, the functor is
  faithful and is asked to be full on isomorphisms only. In particular, isomorphic data come from
  isomorphic structures.
- **Existence.** The data that come from a structure are characterized intrinsically, and the
  structure is rebuilt from them: a compact group, with composition as its group law, as the
  unitary tensor automorphisms of a fiber functor; the multiplication of a unital C⋆-algebra, on
  an operator system that coincides with its C⋆-envelope.

Uniqueness and existence rest on shared arguments. Three recur across the reconstructions
above, M1–M3 below; the first two also have approximate versions, where the axioms hold up to a
small defect, and asymptotic ones, along inductive systems of finite-dimensional stages.

1. **M1. Multiplication from complete positivity.** The product is not part of the data; it is
   recovered from the matrix order. An idempotent morphism of the data, a unital completely
   positive projection, transports the ambient product to its image, compressed by the
   projection, and makes the image a C⋆-algebra in its own right, with the ambient involution and
   norm, even when it is not a subalgebra; when it is one, the projection is a conditional
   expectation and the product is the restricted one. Applied to the injective envelope of an
   operator system, the construction leads to its C⋆-envelope, and the operator systems that come
   from unital C⋆-algebras are exactly those that coincide with it. Positivity on matrices, not
   only on the algebra itself, is what carries the product: a unital order isomorphism need only
   preserve the Jordan product.
2. **M2. Rigidity.** The structure cannot move without the data moving: an isomorphism of the data
   is an isomorphism of the structures. The argument is an equality case. Every morphism of the
   data satisfies an inequality that measures how far it is from preserving the structure, and
   equality singles out where it does: for the product, a Schwarz inequality whose two-sided
   equality set is a C⋆-subalgebra on which the morphism is a ⋆-homomorphism; for a divergence
   such as the relative entropy, the monotonicity inequality, whose equality case, for faithful
   normal states of finite divergence under a unital 2-positive normal morphism, can be
   reversibility by another morphism of the data on the states compared. An isomorphism of the
   data attains equality everywhere, since its inverse is again a morphism of the data, so the
   matrix order determines the product. In approximate versions
   near-equality gives near-preservation or approximate reversibility, and rigidity becomes
   stability, which may need an input of its own, such as amenability, a vanishing of cohomology
   that averaging supplies: without it an approximately multiplicative map need not lie near a
   multiplicative one.
3. **M3. Duality.** A group is recovered from its representations as the automorphisms of a
   forgetful functor. The unitary tensor automorphisms of a fiber functor on a symmetric tensor
   C⋆-category form a compact group, with composition as group law, and the ⋆-structure is what
   singles it out among all tensor automorphisms, as positivity on matrices singles out the product
   in M1. The fiber functor is not an input: a symmetric tensor C⋆-category with conjugates, direct
   sums, subobjects and simple unit determines one, symmetric once the symmetry is twisted by the
   sign of the statistics and unique up to unitary tensor isomorphism among such, and with it the
   compact group, together with a central element of order at most two that records that sign.
   Together with M1, duality recovers not only the group but what it acts on: the fixed points of
   a continuous compact group action are the image of a conditional expectation, and, under
   suitable irreducibility conditions, the fixed-point algebra together with the symmetric
   category of endomorphisms induced by the group's representations inside the algebra determines
   both the algebra and the group.

## Roadmap

Abstraction first. Each phase builds the primitives the next one states its theorems in, and the
design is revisited at each step. **The Scope is meant to be stable; this roadmap is not**,
and Phase III in particular will be set as the foundations take shape.

**Phase I — Foundations**

1. Closed two-sided ideals, quotient C⋆-algebras and c₀-direct sums (M1, M2).
2. Finite-dimensional C⋆-algebras as finite direct sums of matrix algebras, from Mathlib's
   Wedderburn–Artin (M1, M2).
3. Minimal tensor product of C⋆-algebras and nuclearity; the projective tensor product of Banach
   algebras, which holds bounded approximate diagonals (M1, M2).
4. Operator systems as matrix-ordered ⋆-vector spaces with an Archimedean matrix order unit, with
   C⋆-algebras as examples; completely positive maps between them, by generalizing the hypotheses
   of Mathlib's definition upstream rather than by a parallel definition; completely bounded maps
   (M1, M2).
5. C⋆- and W⋆-dynamical systems: a group acting by ⋆-automorphisms, continuously in the point-norm
   (W⋆: point-σ-weak) topology; as an example, the action of the covariance group of a faithful
   local net by ⋆-automorphisms of its quasi-local algebra, already formalized, through which a
   discrete symmetry group acts by a homomorphism into it (M1, M3).
6. Symmetric tensor C⋆-categories with conjugates, direct sums, subobjects and simple unit;
   fiber functors and their unitary tensor automorphisms (M3).

**Phase II — Exact theory**

7. Von Neumann algebras: Kaplansky density, normal ⋆-homomorphisms, the predual; Sakai's
   characterization of von Neumann algebras as the C⋆-algebras with a predual; finite-dimensional
   factors as matrix algebras, through item 2 (M2).
8. Tomita–Takesaki theory, beyond the relative modular operators already formalized:
   JMJ = M′ and Δ^{it}MΔ^{-it} = M for a cyclic and separating vector, the modular automorphism
   group σ^φ of a faithful normal state, the KMS condition characterizing it (Takesaki), and the
   Connes cocycle [Dψ : Dφ] of two faithful normal states, a unitary 1-cocycle for σ^φ (M2).
9. Standard form: the natural cone, the unique vector in it representing each normal positive
   functional, and the unitary implementation of ⋆-automorphisms (M2).
10. Operator system theory: Arveson's extension theorem, giving the injectivity of B(H); the
    Choi–Effros characterization of abstract operator systems as concrete ones (M1, M2).
11. Multiplication from complete positivity: the Choi–Effros product X ∘ Y = Φ(XY) on the image
    of an idempotent unital completely positive map Φ, already formalized for idempotent Schwarz
    maps and hence for idempotent unital 2-positive maps; Tomiyama's theorem on conditional
    expectations; Hamana's injective envelope, built from a minimal idempotent unital completely
    positive map, and the C⋆-envelope as the C⋆-algebra generated in it (M1).
12. ~~Rigidity: the Kadison–Schwarz inequality for 2-positive maps Φ, already formalized in
    `ForMathlib` with Φ(1) ≤ 1 and, without the normalization, as Φ(X)⋆Φ(X) ≤ ‖Φ(1)‖ Φ(X⋆X);
    Choi's multiplicative domain, from its equality case, and with it that unital complete order
    isomorphisms are ⋆-isomorphisms, both already formalized for Schwarz maps and hence for
    unital 2-positive maps, while unital order isomorphisms are Jordan ⋆-isomorphisms (Kadison)
    (M2).~~
13. Reversibility: beyond the monotonicity of the relative entropy already formalized, its
    equality case — the Petz recovery of faithful normal states at finite divergence under a
    unital 2-positive normal map, built on the modular theory and standard form of items 8
    and 9 (M2).
14. Averaging: Peter–Weyl; for a compact group acting continuously by ⋆-automorphisms, Haar
    averaging as the conditional expectation onto the fixed points, and the density of the
    spectral subspaces; for a finite-dimensional C⋆-algebra, the diagonal ∫ U⋆ ⊗ U dU over its
    unitary group, of projective norm one whatever the dimension (M1, M2, M3).
15. Duality: Tannaka–Krein for compact groups, the group law being composition and the topology
    pointwise convergence, extending Mathlib's Tannaka duality for finite groups; the
    Doplicher–Roberts duality theorem on the categories of item 6: existence and uniqueness of the
    fiber functor that is symmetric for the twisted symmetry, and the equivalence with Rep G
    twisted by a central element k, k² = e; its form for a compact group acting faithfully on a
    unital C⋆-algebra F, A = F^G, with full Hilbert spectrum and A′ ∩ F = ℂ1: the endomorphisms
    of A induced by the G-invariant Hilbert spaces in F determine F and G (M3).

**Phase III — To be determined**

Candidates, which no theorem of Phase II is stated in:

- Inductive systems of operator systems along completely positive contractions, with limits in
  ∏Aₙ/⊕Aₙ, the ambient algebra of inductive limits (M1, M2).
- Approximate structures: ε-C⋆-algebras (an exact norm and involution; associativity,
  submultiplicativity, unit and C⋆-identity up to ε), δ-homomorphisms (⋆-preserving linear maps
  preserving the unit and the product up to δ) and δ-isomorphisms (Kitaev, arXiv:2405.02434)
  (M1, M2).
- Hochschild cohomology in low degree, after Mathlib's group cohomology in low degree: H²
  classifying the infinitesimal deformations of a multiplication, whose vanishing makes it rigid
  (Gerstenhaber), and H³ holding the obstructions to extending them; its bounded version for
  Banach algebras, amenability and virtual diagonals, in the bidual of the projective tensor
  product; for C⋆-algebras, amenability is nuclearity (Connes, Haagerup) (M1, M2).
- The Lefschetz–Hopf fixed-point theorem and Hopf's structure theorem for the real cohomology of
  connected H-spaces of finite type, the topological input to the stability theorem for
  ε-C⋆-algebras (Kitaev, arXiv:2405.02434) (M2).

## Usage

To depend on this library, add to your project's `lakefile.toml`:

```toml
[[require]]
name = "QuantumSystem"
git = "https://github.com/kencyke/quantum-system"
rev = "v4.x.y" # the release tag matching your lean-toolchain
```
