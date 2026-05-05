## Summary

This issue clarifies the scope and gap between three closely related concepts that appear across this codebase:

1. **`LocalNet`** (this codebase, `QuantumSystem/Algebra/LocalNet.lean`).
2. **Haag–Kastler net** — the general AQFT axiomatic framework.
3. **Naaijkens 2012's 𝒫_f(L)** — quantum spin systems on an infinite discrete lattice.

## Comparison

|                                        | `LocalNet` (current)                                | Haag–Kastler net (general)                                  | Naaijkens 2012 𝒫_f(L)                              |
| -------------------------------------- | --------------------------------------------------- | ----------------------------------------------------------- | -------------------------------------------------- |
| Region poset                           | `Finset L.sites` with `[Fintype sites]`             | abstract poset (open regions of spacetime, finite subsets…) | **finite** subsets of an infinite lattice `L`      |
| Local algebra `𝔄(Λ)`                   | `Matrix (regionIdx Λ) (regionIdx Λ) ℂ` (finite-dim) | general C\*-algebra (or vN factor)                          | finite-dim `⊗_{x ∈ Λ} M_{n_x}(ℂ)`                  |
| Global algebra                         | finite-dim, just `𝔄(Finset.univ)`                   | context-dependent                                           | quasi-local C\* `𝔄_∞ = ‖·‖-cl ⋃_Λ 𝔄(Λ)` (UHF type) |
| Isotony                                | ✅ (`includeAlgebra`, `includeAlgebra_injective`)   | axiom (i)                                                   | ✅                                                 |
| Locality (disjoint regions commute)    | ❌ not yet                                          | axiom (ii)                                                  | ✅                                                 |
| Covariance (`G`-action + intertwining) | ❌ not yet                                          | axiom (iii)                                                 | ✅ (lattice translation `ℤ^d`)                     |
| Vacuum / state                         | ❌ not yet                                          | axiom (iv) (or built as a separate state layer)             | C\*-state on `𝔄_∞` + GNS                           |
| Dimension                              | finite-dim everywhere                               | typically infinite-dim                                      | each `𝔄(Λ)` finite-dim, global infinite-dim        |

## What `LocalNet` currently is

`LocalNet` provides **only the kinematic data of an AQFT system, plus the isotony embedding**:

- Data: `sites : Type*` with `[Fintype]` and `[DecidableEq]`, and `localIdx : sites → Type*` with the same instances per site.
- Derived types: `regionIdx Λ`, `localAlgebra Λ`, `densityMatrix Λ`.
- Structural lemmas: `combineIdx` (the factorisation `regionIdx Λ × regionIdx (Λ_total \ Λ) ≃ regionIdx Λ_total`), `regionIdxInsertEquiv`, `regionIdxPairEquiv`, `regionIdxTripleEquiv(')`, the `regionIdxCompl{Left,Right}Site` / `regionIdxComplFirst` / `regionIdxComplPair{FirstTwo,LastTwo}` family.
- Isotony: `includeAlgebra : 𝔄(Λ) →⋆ₐ[ℂ] 𝔄(Λ_total)` (bundled `StarAlgHom` so `map_one`, `map_mul`, `map_star` come for free) together with `includeAlgebra_injective`.

Because `sites` itself carries `[Fintype]`, the index poset `Finset L.sites` is the **full power set** `P(L.sites)`, not the directed-cofinal `𝒫_f(L)`. The "global algebra" is just `𝔄(Finset.univ)` — again finite-dim — and no inductive limit is needed.

## What a Haag–Kastler net is

A Haag–Kastler net is, in modern phrasing, a covariant functor from a region poset to a category of \*-algebras, subject to four axioms:

1. **Isotony**: `Λ₁ ⊆ Λ₂ ⟹ 𝔄(Λ₁) ↪ 𝔄(Λ₂)` as a `*`-subalgebra.
2. **Locality (Einstein causality)**: spacelike-separated regions (or `disjoint` regions in the lattice version) have commuting images.
3. **Covariance**: a symmetry group `G` (Poincaré, translation, point group, …) acts by `*`-automorphisms `α_g : 𝔄(Λ) ≃⋆ₐ 𝔄(g · Λ)` intertwining isotony.
4. **Vacuum**: a `G`-invariant state `ω` together with its GNS cyclic vector `Ω`.

The framework is **agnostic to the choice of region poset and algebra type**: continuous spacetime + vN factors, infinite lattice + UHF C\*-algebras, and finite lattice + finite-dim matrix algebras are all instances.

References: Verch 2025 §1.2 ([arXiv:2507.00900](https://arxiv.org/abs/2507.00900)); Naaijkens 2012 §1.3 ([repository.ubn.ru.nl/handle/2066/92737](https://repository.ubn.ru.nl/handle/2066/92737)); Bratteli–Robinson Vol. 2 §6.2.

## What Naaijkens 2012's 𝒫_f(L) is

Naaijkens 2012 specialises the Haag–Kastler framework to **quantum spin systems on an infinite discrete lattice** `L` (typically `ℤ^d`):

- The index poset is `𝒫_f(L)` = the **directed poset of finite subsets of `L`**, ordered by inclusion.
- Each `𝔄(Λ)` for `Λ ∈ 𝒫_f(L)` is the *finite-dim* tensor product `⊗_{x ∈ Λ} M_{n_x}(ℂ)` — finite even though `L` is not.
- The **quasi-local algebra** is the C\*-completion of the algebraic inductive limit
  `𝔄_∞ = ‖·‖-cl ⋃_{Λ ∈ 𝒫_f(L)} 𝔄(Λ)`,
  which is a UHF C\*-algebra.
- States are C\*-states on `𝔄_∞`; the GNS construction yields the (typically inseparable) Hilbert-space representation.
- Locality reads `Disjoint Λ₁ Λ₂ ⟹ [𝔄(Λ₁), 𝔄(Λ₂)] = 0`; covariance is induced from the lattice symmetry (e.g. translation by `ℤ^d`).

This is **one concrete realisation of a Haag–Kastler net — the discrete-lattice / UHF instance — not a separate concept.**

## Hierarchy

```
Haag–Kastler net (general framework)
├── continuous-spacetime instance
│     regions = bounded open ⊂ Minkowski, 𝔄(Λ) = vN factor
└── lattice instance
    ├── infinite L  ⇒ regions = 𝒫_f(L), global = quasi-local C* (UHF)   [Naaijkens 2012]
    └── finite L    ⇒ regions = Finset L = P(L), global = 𝔄(Finset.univ) finite-dim
                      └── this is the slice currently inhabited by `LocalNet`
                          (data + isotony only; locality / covariance / vacuum NYI)
```

## References

- https://repository.ubn.ru.nl/handle/2066/92737
- https://github.com/xiyin137/OSreconstruction
