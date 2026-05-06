module

public import QuantumSystem.Algebra.LocalNet.QuasiLocalAlgebra.Vacuum
public import QuantumSystem.Algebra.LocalNet.QuasiLocalAlgebra.Isotony
public import QuantumSystem.Algebra.LocalNet.QuasiLocalAlgebra.Locality
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# Lattice Haag–Kastler conditions for the quasi-local algebra

This file consolidates the discrete-lattice, quantum-spin-system instance of the
Haag–Kastler local-net framework.  The implemented region poset is `Finset L`,
and the causality relation used here is disjointness of finite lattice regions,
not spacelike separation of double cones in Minkowski spacetime.

For the basis-indexed quasi-local algebra construction, the following local-net
conditions are available:

1. **Isotony** (`isotony`): `Λ ⊆ Λ' → 𝔄(Λ) ≤ 𝔄(Λ')`.
2. **Locality** (`locality`): operators on disjoint regions commute.
3. **Covariance** (`covariance`): the operator-algebra automorphism induced
   by a `G`-action preserves the quasi-local algebra.

The canonical reference vector and its invariance under the implemented unitary
action are provided as a separate vacuum-vector layer.  This is not, by itself,
the full relativistic vacuum-state / positive-energy condition from Minkowski
AQFT.

In addition, the file installs a `CStarAlgebra` instance on
`↥(quasiLocal L)`, completing the structural side of the construction:
the quasi-local algebra is a unital C⋆-algebra acting on the global
Hilbert space.

## References

* Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §1.3.
* Verch, *Algebraic quantum field theory and operator algebras*, 2025, §1.2.
-/

@[expose] public section

namespace LocalNetLike

/-! ### Public Haag–Kastler bundles

The base `LocalNetLike` class is intentionally minimal: it only requires the
identity functor law and the disjoint-locality axiom on a finite-region
embedding family.  Most Haag–Kastler theorems however want a stronger
package: full functoriality, injective embeddings, a faithful local
representation on `regionHilbert Λ`, and compatibility between that
representation and the abstract isotony.

`HaagKastlerNet L` collects all those optional refinements into a single
public entry point so that Haag–Kastler statements can be quoted at the
abstract `LocalNetLike.localAlgebra` level without re-listing the mixins.
The covariant version `HaagKastlerCovariantNet` additionally records the
coherence law turning a `HasGroupAction` into a genuine group action on
the dependent-index permutations. -/

/-- **Public bundle for static Haag–Kastler data.**  Combines the four
optional mixins (`IsFunctorial`, `IsotonyInjective`, `HasFaithfulLocalRepresentation`,
`HasIsotonyCompatibleLocalRep`) with the per-site nondegeneracy condition
`∀ s, Nonempty (localIdx s)`.

A bare `LocalNetLike L` suffices for the kinematic constructions
(`regionHilbert`, `localEmbed`, `localSubalgebra`).  `HaagKastlerNet L` is
the strength one actually wants when stating Haag–Kastler axioms about
the abstract `localAlgebra` family rather than its represented image. -/
class HaagKastlerNet (L : Type*) [DecidableEq L] [LocalNetLike L]
    [LocalNetLike.HasLocalRepresentation L] : Prop
    extends
      LocalNetLike.IsFunctorial L,
      LocalNetLike.IsotonyInjective L,
      LocalNetLike.HasFaithfulLocalRepresentation L,
      LocalNetLike.HasIsotonyCompatibleLocalRep L where
  /-- Every site has a nonempty local Hilbert-space index type. -/
  nonempty_localIdx : ∀ s : L, Nonempty (LocalNetLike.localIdx (L := L) s)

/-- Per-site nondegeneracy is exposed as a typeclass instance so that
downstream constructions requiring `[∀ s, Nonempty (localIdx s)]` resolve
automatically once `[HaagKastlerNet L]` is in scope. -/
instance HaagKastlerNet.instNonemptyLocalIdx
    {L : Type*} [DecidableEq L] [LocalNetLike L]
    [LocalNetLike.HasLocalRepresentation L] [HaagKastlerNet L] (s : L) :
    Nonempty (LocalNetLike.localIdx (L := L) s) :=
  HaagKastlerNet.nonempty_localIdx s

/-- **Public bundle for covariant Haag–Kastler data.**  Pairs a
`HaagKastlerNet L` with a `G`-action `act` on `L` whose dependent-index
permutation lift `piAction` is coherent (sends the unit element to the
identity and the product to the composition).  Coherence is the
condition under which `algebraAut` and the unitary representation
become genuine group actions. -/
class HaagKastlerCovariantNet
    (L : Type*) [DecidableEq L] [LocalNetLike L]
    [LocalNetLike.HasLocalRepresentation L] [HaagKastlerNet L]
    (G : Type*) [Group G]
    (act : LocalNetLike.HasGroupAction L G) : Prop where
  /-- The dependent-index permutation lift respects the group structure. -/
  isCoherent : LocalNetLike.HasGroupAction.IsCoherent act

/-- The coherence record packed inside `HaagKastlerCovariantNet` is exposed
as a typeclass instance, so theorems requiring `[IsCoherent act]` resolve
automatically once `[HaagKastlerCovariantNet L G act]` is available. -/
instance HaagKastlerCovariantNet.instIsCoherent
    {L : Type*} [DecidableEq L] [LocalNetLike L]
    [LocalNetLike.HasLocalRepresentation L] [HaagKastlerNet L]
    {G : Type*} [Group G] {act : LocalNetLike.HasGroupAction L G}
    [HaagKastlerCovariantNet L G act] :
    LocalNetLike.HasGroupAction.IsCoherent act :=
  HaagKastlerCovariantNet.isCoherent

variable (L : Type*) [DecidableEq L] [LocalNetLike L]
    [hL : ∀ s : L, Nonempty (LocalNetLike.localIdx (L := L) s)]

/-- The quasi-local algebra `quasiLocal L` is a closed subset of
`B(globalHilbert L)`. -/
instance instIsClosed_quasiLocal :
    IsClosed (SetLike.coe (quasiLocal L)) :=
  isClosed_quasiLocal L

/-- The **quasi-local algebra is a unital C⋆-algebra**.  This instance is
derived from the closed-subalgebra `CStarAlgebra` instance
`StarSubalgebra.cstarAlgebra` and the closedness of `quasiLocal L`. -/
noncomputable instance instCStarAlgebra_quasiLocal :
    CStarAlgebra ↥(quasiLocal L) :=
  inferInstance

namespace HaagKastler

variable {L}

/-- **Isotony.**  If `Λ ⊆ Λ'`, then the local subalgebra at `Λ`
is contained in the local subalgebra at `Λ'`. -/
theorem isotony {Λ Λ' : Finset L} (h : Λ ⊆ Λ') :
    localSubalgebra Λ ≤ localSubalgebra Λ' :=
  localSubalgebra_le_of_subset h

/-- **Locality for disjoint finite lattice regions.**  Operators in `localSubalgebra Λ₁` commute with
operators in `localSubalgebra Λ₂` whenever `Λ₁` and `Λ₂` are disjoint. -/
theorem locality {Λ₁ Λ₂ : Finset L} (hd : Disjoint Λ₁ Λ₂)
    {T₁ T₂ : globalHilbert L →L[ℂ] globalHilbert L}
    (h₁ : T₁ ∈ localSubalgebra Λ₁) (h₂ : T₂ ∈ localSubalgebra Λ₂) :
    Commute T₁ T₂ :=
  localSubalgebra_commute_of_disjoint hd h₁ h₂

variable (L)

/-- **Covariance of the represented quasi-local algebra.**  For any
`G`-action `act : HasGroupAction L G`
and any `g : G`, the induced operator-algebra automorphism `algebraAut g`
maps the quasi-local algebra `quasiLocal L` into itself. -/
theorem covariance {G : Type*} [Group G] (act : HasGroupAction L G) (g : G) :
    ∀ T ∈ quasiLocal L, act.algebraAut g T ∈ quasiLocal L :=
  HasGroupAction.algebraAut_quasiLocal_le act g

/-- **Vacuum-vector invariance.**  For any `G`-action
`act : HasGroupAction L G` and any `g : G`, the unitary representation
`unitaryAction g` fixes the canonical reference vector `vacuumVector L`. -/
theorem vacuum_vector_invariance {G : Type*} [Group G]
    (act : HasGroupAction L G) (g : G) :
    act.unitaryAction g (vacuumVector L) = vacuumVector L :=
  HasGroupAction.unitaryAction_vacuumVector L act g

/-- Compatibility spelling for older files: this is invariance of the canonical
reference vector, not a bundled C⋆-algebra state or a positive-energy condition. -/
theorem vacuum_invariance {G : Type*} [Group G]
    (act : HasGroupAction L G) (g : G) :
    act.unitaryAction g (vacuumState L) = vacuumState L :=
  HasGroupAction.unitaryAction_vacuumState L act g

/-- **`G`-invariance of the vacuum state on the quasi-local algebra**.  This is
the proper C⋆-state form `ω(α_g T) = ω(T)` of vacuum invariance, complementing
the unitary-implementation statement `vacuum_vector_invariance`. -/
theorem vacuum_state_invariance {G : Type*} [Group G]
    (act : HasGroupAction L G) (g : G) (T : ↥(quasiLocal L)) :
    vacuumStateOnQuasiLocal L (act.quasiLocalEnd g T)
      = vacuumStateOnQuasiLocal L T :=
  HasGroupAction.vacuumStateOnQuasiLocal_quasiLocalEnd L act g T

/-! ### Abstract-algebra-level Haag–Kastler statements

The theorems above describe the represented quasi-local net.  Under
`[HaagKastlerNet L]`, the same content can be relayed at the abstract
`LocalNetLike.localAlgebra` level: every abstract local element is
realised inside `quasiLocal L` via `localAlgebraEmbed`, and the bundle
guarantees compatibility with isotony, locality and covariance. -/

variable {L}

/-- **Abstract isotony**: under `HaagKastlerNet L`, the global embedding
of an abstract local element factors through any larger region. -/
theorem abstract_isotony
    [LocalNetLike.HasLocalRepresentation L] [LocalNetLike.HaagKastlerNet L]
    {Λ Λ' : Finset L} (h : Λ ⊆ Λ')
    (a : LocalNetLike.localAlgebra (L := L) Λ) :
    localAlgebraEmbed Λ' (LocalNetLike.isotony h a) = localAlgebraEmbed Λ a :=
  localAlgebraEmbed_isotony h a

/-- **Abstract locality**: under `HaagKastlerNet L`, abstract local
elements on disjoint regions commute after global embedding. -/
theorem abstract_locality
    [LocalNetLike.HasLocalRepresentation L] [LocalNetLike.HaagKastlerNet L]
    {Λ₁ Λ₂ : Finset L} (hd : Disjoint Λ₁ Λ₂)
    (a : LocalNetLike.localAlgebra (L := L) Λ₁)
    (b : LocalNetLike.localAlgebra (L := L) Λ₂) :
    Commute (localAlgebraEmbed Λ₁ a) (localAlgebraEmbed Λ₂ b) :=
  localSubalgebra_commute_of_disjoint hd
    (localAlgebraEmbed_mem_localSubalgebra Λ₁ a)
    (localAlgebraEmbed_mem_localSubalgebra Λ₂ b)

/-- **Abstract membership in the quasi-local algebra**: every abstract
local element lands inside the quasi-local algebra after embedding. -/
theorem abstract_mem_quasiLocal
    [LocalNetLike.HasLocalRepresentation L] [LocalNetLike.HaagKastlerNet L]
    {Λ : Finset L} (a : LocalNetLike.localAlgebra (L := L) Λ) :
    localAlgebraEmbed Λ a ∈ quasiLocal L :=
  localSubalgebra_le_quasiLocal L Λ (localAlgebraEmbed_mem_localSubalgebra Λ a)

variable (L)

/-- **Abstract covariance**: under `HaagKastlerNet L` paired with a
coherent `HaagKastlerCovariantNet`, the represented operator-algebra
automorphism `algebraAut g` sends the global embedding of every abstract
local element at `Λ` into the represented local algebra of the translated
region `g · Λ`. -/
theorem abstract_covariance_local
    [LocalNetLike.HasLocalRepresentation L] [LocalNetLike.HaagKastlerNet L]
    {G : Type*} [Group G] (act : HasGroupAction L G)
    [LocalNetLike.HaagKastlerCovariantNet L G act] {Λ : Finset L}
    (a : LocalNetLike.localAlgebra (L := L) Λ) (g : G) :
    act.algebraAut g (localAlgebraEmbed Λ a) ∈ localSubalgebra (act.regionImage g Λ) :=
  HasGroupAction.algebraAut_localSubalgebra_le act g Λ _
    (localAlgebraEmbed_mem_localSubalgebra Λ a)

/-- **Abstract covariance into the quasi-local algebra**: the local covariance
statement `abstract_covariance_local` followed by the inclusion
`localSubalgebra (g · Λ) ≤ quasiLocal L`.  This convenient weaker spelling is
useful when working only in the completed quasi-local algebra. -/
theorem abstract_covariance
    [LocalNetLike.HasLocalRepresentation L] [LocalNetLike.HaagKastlerNet L]
    {G : Type*} [Group G] (act : HasGroupAction L G)
    [LocalNetLike.HaagKastlerCovariantNet L G act] {Λ : Finset L}
    (a : LocalNetLike.localAlgebra (L := L) Λ) (g : G) :
    act.algebraAut g (localAlgebraEmbed Λ a) ∈ quasiLocal L :=
  localSubalgebra_le_quasiLocal L (act.regionImage g Λ)
    (abstract_covariance_local (L := L) act a g)

end HaagKastler

end LocalNetLike
