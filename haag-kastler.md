## Summary

This issue clarifies the scope and gap between three closely related concepts that appear across this codebase:

1. **`LocalNet`** (this codebase, `QuantumSystem/Algebra/LocalNet.lean`).
2. **Haag–Kastler net** — the general AQFT axiomatic framework.
3. **Naaijkens 2012's 𝒫_f(L)** — quantum spin systems on an infinite discrete lattice.

## Comparison

|                                        | `LocalNet` (current)                                | `LocalNetLike` + `QuasiLocalAlgebra/*` (current)              | Haag–Kastler net (general)                                  | Naaijkens 2012 𝒫_f(L)                              |
| -------------------------------------- | --------------------------------------------------- | ------------------------------------------------------------- | ----------------------------------------------------------- | -------------------------------------------------- |
| Region poset                           | `Finset L.sites` with `[Fintype sites]`             | `Finset L` (no `Fintype` on `L`)                              | abstract poset (open regions of spacetime, finite subsets…) | **finite** subsets of an infinite lattice `L`      |
| Local algebra `𝔄(Λ)`                   | `Matrix (regionIdx Λ) (regionIdx Λ) ℂ` (finite-dim) | abstract `localAlgebra Λ` + represented `localSubalgebra Λ`   | general C\*-algebra (or vN factor)                          | finite-dim `⊗_{x ∈ Λ} M_{n_x}(ℂ)`                  |
| Global algebra                         | finite-dim, just `𝔄(Finset.univ)`                   | quasi-local C\* `quasiLocal L = ‖·‖-cl ⨆ Λ, localSubalgebra Λ` | context-dependent                                           | quasi-local C\* `𝔄_∞ = ‖·‖-cl ⋃_Λ 𝔄(Λ)` (UHF type) |
| Isotony                                | ✅ (`includeAlgebra`, `includeAlgebra_injective`)   | ✅ (`HaagKastler.isotony`)                                    | axiom (i)                                                   | ✅                                                 |
| Locality (disjoint regions commute)    | ❌ (no global ambient)                              | ✅ (`HaagKastler.locality`)                                   | axiom (ii)                                                  | ✅                                                 |
| Covariance (`G`-action + intertwining) | ❌ (no group-action layer)                          | ✅ (`HaagKastler.covariance`)                                 | axiom (iii)                                                 | ✅ (lattice translation `ℤ^d`)                     |
| Vacuum / state                         | finite-density predicates only                      | ✅ reference vector `vacuumVector L` + reference-vector functional `vacuumFunctionalOnQuasiLocal L` (not yet a bundled C\*-state) | separate state / representation layer | C\*-state on `𝔄_∞` + GNS                           |
| Dimension                              | finite-dim everywhere                               | each `localAlgebra Λ` finite-dim, `quasiLocal L` infinite-dim | typically infinite-dim                                      | each `𝔄(Λ)` finite-dim, global infinite-dim        |

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
4. **State/representation layer**: often a `G`-invariant state `ω`, its GNS cyclic vector `Ω`, and for relativistic vacuum sectors a positive-energy / ground-state condition.  This layer is separate from the three local-net conditions above.

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
│       (NYI in this codebase)
└── lattice instance
    ├── infinite L  ⇒ regions = 𝒫_f(L), global = quasi-local C* (UHF)   [Naaijkens 2012]
    │     ✅ inhabited by `LocalNetLike` + `QuasiLocalAlgebra/*`:
    │        isotony, disjoint-locality, covariance,
    │        reference-vector and reference-functional invariance
    └── finite L    ⇒ regions = Finset L = P(L), global = 𝔄(Finset.univ) finite-dim
                      └── this is the slice inhabited by `LocalNet` proper
                          (kinematic data + isotony only; the lattice axioms
                          are imported via the `LocalNet → LocalNetLike` instance)
```

## Status: Phase 5 implementation of the Naaijkens 2012 lattice instance

`QuantumSystem/Algebra/LocalNet/QuasiLocalAlgebra/*` adds a basis-indexed
realisation of the **infinite-lattice Haag–Kastler local-net conditions**, sitting on top of
the new `LocalNetLike` typeclass.  The local-net conditions, the bundled
reference-vector functional on the quasi-local C⋆-algebra, and the
abstract-to-concrete bridge are all available:

| Condition / layer | Public theorem / definition | File |
| --- | --- | --- |
| (i) Isotony (represented) | `LocalNetLike.HaagKastler.isotony` | `HaagKastler.lean` |
| (ii) Locality (represented) | `LocalNetLike.HaagKastler.locality` | `HaagKastler.lean` |
| (iii) Covariance of `quasiLocal L` | `LocalNetLike.HaagKastler.covariance` | `HaagKastler.lean` |
| Reference-vector invariance | `LocalNetLike.HaagKastler.vacuum_vector_invariance` | `HaagKastler.lean` |
| Reference-functional invariance via `quasiLocalEnd` | `LocalNetLike.HaagKastler.vacuum_functional_invariance` | `HaagKastler.lean` |
| Reference-functional invariance via `quasiLocalAut` | `LocalNetLike.HaagKastler.vacuum_functional_invariance_aut` | `HaagKastler.lean` |
| Bundled reference-vector functional on `quasiLocal L` | `LocalNetLike.vacuumFunctionalOnQuasiLocal` | `Vacuum.lean` |
| Genuine-action predicate on a site action | `LocalNetLike.HasGroupAction.IsGenuineAction` | `Covariance.lean` |
| Bundled quasi-local automorphism | `LocalNetLike.HasGroupAction.quasiLocalAut` | `Covariance.lean` |
| Quasi-local automorphism laws | `LocalNetLike.HasGroupAction.{quasiLocalAut_one_apply, quasiLocalAut_mul_apply}` | `Covariance.lean` |
| Static public bundle | `LocalNetLike.HaagKastlerNet` | `HaagKastler.lean` |
| Covariant public bundle | `LocalNetLike.CovariantHaagKastlerNet` | `HaagKastler.lean` |
| Abstract-to-concrete `*`-algebra bridge | `LocalNetLike.localAlgebraEmbed` | `LocalEmbed.lean` |
| Embedded membership in `localSubalgebra Λ` | `LocalNetLike.localAlgebraEmbed_mem_localSubalgebra` | `LocalEmbed.lean` |
| Functoriality (composition law) | `LocalNet.includeAlgebra_comp`, `LocalNetLike.IsFunctorial` (auto for `LocalNet`) | `LocalNet.lean`, `AsLocalNetLike.lean` |
| C⋆-algebra structure on `↥(quasiLocal L)` | `LocalNetLike.instCStarAlgebra_quasiLocal` | `HaagKastler.lean` |
| C⋆-algebra structure on `localAlgebra Λ` | `LocalNet.instCStarAlgebra_localAlgebra` (L2 operator-norm pullback) | `AsLocalNetLike.lean` |

The quasi-local algebra `LocalNetLike.quasiLocal L : StarSubalgebra ℂ B(H)`
is the norm closure of `⨆ Λ : Finset L, localSubalgebra Λ` and carries an
automatic `CStarAlgebra` instance (`instCStarAlgebra_quasiLocal`), realising
the UHF / quasi-local construction at the operator-algebra level.  The
underlying global Hilbert space `globalHilbert L := ↥(lp _ 2)` is the
incomplete tensor product around the basis-indexed reference vector
`vacuumVector L := lp.single 2 (referenceTuple L) 1`.  The associated
bundled linear functional on the quasi-local algebra is
`vacuumFunctionalOnQuasiLocal L`; it is not yet a bundled positive,
normalised C\*-state.

The public entry points for the lattice local-net theorems, the
reference-vector / reference-functional invariance theorems, and
`instCStarAlgebra_quasiLocal` are gathered in `HaagKastler.lean` for downstream use.

### Public Haag–Kastler bundles

The base `LocalNetLike L` class is intentionally minimal: only `isotony` and
`isotony_refl` are bundled fields, while `IsFunctorial`, `IsotonyInjective`,
`HasLocalRepresentation`, `HasFaithfulLocalRepresentation`, and
`HasIsotonyCompatibleLocalRep` are optional `Prop` mixins.  This keeps the
kinematic abstraction lightweight, but it also means that the represented
theorems `LocalNetLike.HaagKastler.{isotony, locality, covariance}` are
phrased on `localSubalgebra Λ` (the image of
`regionHilbert Λ →L[ℂ] regionHilbert Λ` inside `B(globalHilbert L)`), not on
the abstract `LocalNetLike.localAlgebra Λ` directly.

Two public-entry-point classes bundle the optional mixins into stable
downstream assumptions:

* `LocalNetLike.HaagKastlerNet L` collects `IsFunctorial`, `IsotonyInjective`,
  `HasFaithfulLocalRepresentation`, `HasIsotonyCompatibleLocalRep`, and the
  per-site nondegeneracy condition `∀ s, Nonempty (localIdx s)`.  It is the
  public "single hypothesis" bundle for the static local-net side and also
  exposes per-site nondegeneracy through `HaagKastlerNet.instNonemptyLocalIdx`.
* `LocalNetLike.CovariantHaagKastlerNet L G act` adds
  `HasGroupAction.IsGenuineAction act`, the extra hypothesis needed to package
  the per-element quasi-local endomorphisms into bundled automorphisms
  `quasiLocalAut g` satisfying `quasiLocalAut_one_apply` and
  `quasiLocalAut_mul_apply`.

Both bundles are inhabited concretely by the spin-1/2 chain on `ℤ` with the
translation action, producing axiom-free `instance`-level witnesses in
`Examples/QubitChain.lean`.

### Concrete witness: spin-1/2 chain on `ℤ`

The local-net and reference-vector theorems above are universally quantified over any
`[LocalNetLike L]` and any `LocalNetLike.HasGroupAction L G`.  To make the
claimed lattice realisation non-vacuous,
`Examples/QubitChain.lean` constructs a concrete instance — the canonical
Naaijkens 2012 example:

* `qubitChain : LocalNet` with `sites := ℤ` and `localIdx _ := Fin 2`;
* the auto `LocalNetLike` instance via `LocalNet → LocalNetLike L.sites`,
  along with `IsotonyInjective`, `IsFunctorial`, `HasLocalRepresentation`,
  `HasFaithfulLocalRepresentation`, and `HasIsotonyCompatibleLocalRep` mixin
  instances inherited from `LocalNet`;
* the resulting `HaagKastlerNet qubitChain.sites` instance bundling all
  optional refinements together with per-site nondegeneracy;
* `qubitChainTranslationAction : LocalNetLike.HasGroupAction qubitChain.sites
  (Multiplicative ℤ)` for the lattice-translation action, together with
  `instQubitChainTranslationActionIsGenuineAction :
  qubitChainTranslationAction.IsGenuineAction` certifying that the
  dependent-index action is a *bona fide* group action;
* the resulting
  `CovariantHaagKastlerNet qubitChain.sites (Multiplicative ℤ)
  qubitChainTranslationAction` instance combining the static bundle with the
  genuine-action hypothesis.

These are all axiom-free `instance` / `example` declarations in
`Examples/QubitChain.lean`, witnessing that the lattice Haag–Kastler
conditions and the genuine-action strengthening are simultaneously realisable
in a non-trivial setting.

The `IsGenuineAction` instance promotes the per-element quasi-local
endomorphisms `quasiLocalEnd g` to bundled automorphisms `quasiLocalAut g`.
The implementation currently exposes the identity and multiplication laws as
theorems `quasiLocalAut_one_apply` and `quasiLocalAut_mul_apply`; it does not
yet package them as a monoid homomorphism `G →* Aut(quasiLocal L)`.

## References

- https://repository.ubn.ru.nl/handle/2066/92737
- https://github.com/xiyin137/OSreconstruction
- https://arxiv.org/abs/2507.00900
