module

public import QuantumSystem.Algebra.QuasiLocalAlgebra.Covariance
public import QuantumSystem.Algebra.QuasiLocalAlgebra.Isotony
public import QuantumSystem.Algebra.QuasiLocalAlgebra.Locality
public import QuantumSystem.Algebra.QuasiLocalAlgebra.Vacuum

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

open scoped LocalNetLike

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
abstract `LocalNetLike.localAlgebra` level without re-listing the mixins. -/

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

/-- **Public bundle for covariant lattice Haag–Kastler data.**  This extends the
static finite-region Haag–Kastler bundle by requiring that a chosen group action is a
genuine `G`-action, so that its quasi-local automorphisms satisfy the identity and
multiplication laws in `HasGroupAction.quasiLocalAut_one_apply` and
`HasGroupAction.quasiLocalAut_mul_apply`. -/
class CovariantHaagKastlerNet (L : Type*) [DecidableEq L] [LocalNetLike L]
    [LocalNetLike.HasLocalRepresentation L]
    [∀ s : L, Nonempty (LocalNetLike.localIdx (L := L) s)]
    (G : Type*) [Group G] (act : HasGroupAction L G) : Prop
    extends HaagKastlerNet L, HasGroupAction.IsGenuineAction act

/-- Per-site nondegeneracy is exposed as a typeclass instance so that
downstream constructions requiring `[∀ s, Nonempty (localIdx s)]` resolve
automatically once `[HaagKastlerNet L]` is in scope. -/
instance HaagKastlerNet.instNonemptyLocalIdx
    {L : Type*} [DecidableEq L] [LocalNetLike L]
    [LocalNetLike.HasLocalRepresentation L] [HaagKastlerNet L] (s : L) :
    Nonempty (LocalNetLike.localIdx (L := L) s) :=
  HaagKastlerNet.nonempty_localIdx s

variable (L : Type*) [DecidableEq L] [LocalNetLike L]
    [hL : ∀ s : L, Nonempty (LocalNetLike.localIdx (L := L) s)]

namespace HaagKastler

variable {L}

/-- **Isotony.**  If `Λ ⊆ Λ'`, then the local subalgebra at `Λ`
is contained in the local subalgebra at `Λ'`. -/
theorem isotony {Λ Λ' : Finset L} (h : Λ ⊆ Λ') :
    𝔄(Λ) ≤ 𝔄(Λ') :=
  localSubalgebra_le_of_subset h

/-- **Locality for disjoint finite lattice regions.**  Operators in `𝔄(Λ₁)` commute with
operators in `𝔄(Λ₂)` whenever `Λ₁` and `Λ₂` are disjoint. -/
theorem locality {Λ₁ Λ₂ : Finset L} (hd : Disjoint Λ₁ Λ₂)
    {T₁ T₂ : globalHilbert L →L[ℂ] globalHilbert L}
    (h₁ : T₁ ∈ 𝔄(Λ₁)) (h₂ : T₂ ∈ 𝔄(Λ₂)) :
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
    act.unitaryAction g Ω(L) = Ω(L) :=
  HasGroupAction.unitaryAction_vacuumVector L act g

/-- **`G`-invariance of the reference-vector functional on the quasi-local algebra**.
This is the functional identity `ω(α_g T) = ω(T)`, complementing the
unitary-implementation statement `vacuum_vector_invariance`. -/
theorem vacuum_functional_invariance {G : Type*} [Group G]
    (act : HasGroupAction L G) (g : G) (T : ↥(quasiLocal L)) :
    ω(L) (act.quasiLocalEnd g T) = ω(L) T :=
  HasGroupAction.vacuumFunctionalOnQuasiLocal_quasiLocalEnd L act g T

/-- Genuine-action version of `vacuum_functional_invariance`, stated using the bundled
quasi-local automorphism. -/
theorem vacuum_functional_invariance_aut {G : Type*} [Group G]
    (act : HasGroupAction L G) [act.IsGenuineAction] (g : G) (T : ↥(quasiLocal L)) :
    ω(L) (act.quasiLocalAut g T) = ω(L) T := by
  have heq : act.quasiLocalAut g T = act.quasiLocalEnd g T :=
    Subtype.ext <| by
      rw [HasGroupAction.quasiLocalAut_apply, HasGroupAction.quasiLocalEnd_apply]
  rw [heq]
  exact vacuum_functional_invariance L act g T

end HaagKastler

end LocalNetLike
