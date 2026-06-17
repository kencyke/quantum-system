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
`↥(quasiLocal L Ω)`, completing the structural side of the construction:
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

`HaagKastlerNet L` packages the strengthening of `LocalNetLike L` needed to
state Haag–Kastler axioms at the abstract `LocalNetLike.localAlgebra` level:
full functoriality, injective embeddings, a faithful local representation
on `regionHilbert Λ`, and compatibility with the abstract isotony. -/

/-- **Public bundle for static Haag–Kastler data.**  Combines the four
optional mixins (`IsFunctorial`, `IsotonyInjective`,
`HasFaithfulLocalRepresentation`, `HasIsotonyCompatibleLocalRep`) with the
per-site nondegeneracy `∀ s, Nonempty (localIdx s)`. -/
class HaagKastlerNet (L : Type*) [DecidableEq L] [LocalNetLike L]
    [LocalNetLike.HasLocalRepresentation L] : Prop
    extends
      LocalNetLike.IsFunctorial L,
      LocalNetLike.IsotonyInjective L,
      LocalNetLike.HasFaithfulLocalRepresentation L,
      LocalNetLike.HasIsotonyCompatibleLocalRep L where
  /-- Every site has a nonempty local Hilbert-space index type. -/
  nonempty_localIdx : ∀ s : L, Nonempty (LocalNetLike.localIdx (L := L) s)

/-- **Public bundle for covariant lattice Haag–Kastler data.**  Extends
`HaagKastlerNet` with a chosen group action `act`.  The genuineness of `act`
(functoriality of `piAction`) is no longer a hypothesis: it follows from the
fibre coherence laws bundled into `HasGroupAction`, so the quasi-local
automorphisms automatically satisfy `quasiLocalAut_one_apply` and
`quasiLocalAut_mul_apply`. -/
class CovariantHaagKastlerNet (L : Type*) [DecidableEq L] [LocalNetLike L]
    [LocalNetLike.HasLocalRepresentation L]
    [∀ s : L, Nonempty (LocalNetLike.localIdx (L := L) s)]
    (Ω : (s : L) → LocalNetLike.localIdx (L := L) s)
    (G : Type*) [Group G] (act : HasGroupAction L Ω G) : Prop
    extends HaagKastlerNet L

/-- Per-site nondegeneracy as a typeclass instance: `[∀ s, Nonempty (localIdx s)]`
resolves automatically once `[HaagKastlerNet L]` is in scope. -/
instance HaagKastlerNet.instNonemptyLocalIdx
    {L : Type*} [DecidableEq L] [LocalNetLike L]
    [LocalNetLike.HasLocalRepresentation L] [HaagKastlerNet L] (s : L) :
    Nonempty (LocalNetLike.localIdx (L := L) s) :=
  HaagKastlerNet.nonempty_localIdx s

variable (L : Type*) [DecidableEq L] [LocalNetLike L]
variable (Ω : (s : L) → LocalNetLike.localIdx (L := L) s)

namespace HaagKastler

variable {L Ω}

/-- **Isotony.**  If `Λ ⊆ Λ'`, then the local subalgebra at `Λ`
is contained in the local subalgebra at `Λ'`. -/
theorem isotony {Λ Λ' : Finset L} (h : Λ ⊆ Λ') :
    𝔄(Λ) ≤ (𝔄(Λ') : StarSubalgebra ℂ (globalHilbert L Ω →L[ℂ] globalHilbert L Ω)) :=
  localSubalgebra_le_of_subset h

/-- **Locality for disjoint finite lattice regions.**  Operators in `𝔄(Λ₁)` commute with
operators in `𝔄(Λ₂)` whenever `Λ₁` and `Λ₂` are disjoint. -/
theorem locality {Λ₁ Λ₂ : Finset L} (hd : Disjoint Λ₁ Λ₂)
    {T₁ T₂ : globalHilbert L Ω →L[ℂ] globalHilbert L Ω}
    (h₁ : T₁ ∈ (𝔄(Λ₁) :
        StarSubalgebra ℂ (globalHilbert L Ω →L[ℂ] globalHilbert L Ω)))
    (h₂ : T₂ ∈ (𝔄(Λ₂) :
        StarSubalgebra ℂ (globalHilbert L Ω →L[ℂ] globalHilbert L Ω))) :
    Commute T₁ T₂ :=
  localSubalgebra_commute_of_disjoint hd h₁ h₂

variable (L Ω)

/-- **Covariance.**  `algebraAut g` maps `quasiLocal L Ω` into itself. -/
theorem covariance {G : Type*} [Group G] (act : HasGroupAction L Ω G) (g : G) :
    ∀ T ∈ quasiLocal L Ω, act.algebraAut g T ∈ quasiLocal L Ω :=
  HasGroupAction.algebraAut_quasiLocal_le act g

/-- **Vacuum-vector invariance.**  `unitaryAction g` fixes `vacuumVector L Ω`. -/
theorem vacuum_vector_invariance {G : Type*} [Group G]
    (act : HasGroupAction L Ω G) (g : G) :
    act.unitaryAction g (vacuumVector L Ω) = vacuumVector L Ω :=
  HasGroupAction.unitaryAction_vacuumVector L Ω act g

/-- **`G`-invariance of the vacuum functional**: `ω(α_g T) = ω(T)`. -/
theorem vacuum_functional_invariance {G : Type*} [Group G]
    (act : HasGroupAction L Ω G) (g : G) (T : ↥(quasiLocal L Ω)) :
    vacuumFunctionalOnQuasiLocal L Ω (act.quasiLocalEnd g T) = vacuumFunctionalOnQuasiLocal L Ω T :=
  HasGroupAction.vacuumFunctionalOnQuasiLocal_quasiLocalEnd L Ω act g T

/-- Genuine-action version of `vacuum_functional_invariance`, stated using the bundled
quasi-local automorphism. -/
theorem vacuum_functional_invariance_aut {G : Type*} [Group G]
    (act : HasGroupAction L Ω G) (g : G) (T : ↥(quasiLocal L Ω)) :
    vacuumFunctionalOnQuasiLocal L Ω (act.quasiLocalAut g T) = vacuumFunctionalOnQuasiLocal L Ω T := by
  have heq : act.quasiLocalAut g T = act.quasiLocalEnd g T :=
    Subtype.ext <| by
      rw [HasGroupAction.quasiLocalAut_apply, HasGroupAction.quasiLocalEnd_apply]
  rw [heq]
  exact vacuum_functional_invariance L Ω act g T

end HaagKastler

end LocalNetLike
