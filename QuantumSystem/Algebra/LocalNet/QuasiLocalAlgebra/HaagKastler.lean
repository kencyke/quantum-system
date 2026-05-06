module

public import QuantumSystem.Algebra.LocalNet.QuasiLocalAlgebra.Vacuum
public import QuantumSystem.Algebra.LocalNet.QuasiLocalAlgebra.Isotony
public import QuantumSystem.Algebra.LocalNet.QuasiLocalAlgebra.Locality
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# Haag–Kastler axioms for the quasi-local algebra (Phase 5'e)

This file consolidates the four Haag–Kastler axioms (Naaijkens 2012 §1.3 /
Verch 2025 §1.2) that have been verified throughout
`QuantumSystem.Algebra.LocalNet.QuasiLocalAlgebra.*` for the basis-indexed
quasi-local algebra construction:

1. **Isotony** (`isotony`): `Λ ⊆ Λ' → 𝔄(Λ) ≤ 𝔄(Λ')`.
2. **Locality** (`locality`): operators on disjoint regions commute.
3. **Covariance** (`covariance`): the operator-algebra automorphism induced
   by a `G`-action preserves the quasi-local algebra.
4. **Vacuum invariance** (`vacuum_invariance`): the unitary representation
   fixes the canonical vacuum vector.

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

/-- **Axiom (i): Isotony.**  If `Λ ⊆ Λ'`, then the local subalgebra at `Λ`
is contained in the local subalgebra at `Λ'`. -/
theorem isotony {Λ Λ' : Finset L} (h : Λ ⊆ Λ') :
    localSubalgebra Λ ≤ localSubalgebra Λ' :=
  localSubalgebra_le_of_subset h

/-- **Axiom (ii): Locality.**  Operators in `localSubalgebra Λ₁` commute with
operators in `localSubalgebra Λ₂` whenever `Λ₁` and `Λ₂` are disjoint. -/
theorem locality {Λ₁ Λ₂ : Finset L} (hd : Disjoint Λ₁ Λ₂)
    {T₁ T₂ : globalHilbert L →L[ℂ] globalHilbert L}
    (h₁ : T₁ ∈ localSubalgebra Λ₁) (h₂ : T₂ ∈ localSubalgebra Λ₂) :
    Commute T₁ T₂ :=
  localSubalgebra_commute_of_disjoint hd h₁ h₂

variable (L)

/-- **Axiom (iii): Covariance.**  For any `G`-action `act : HasGroupAction L G`
and any `g : G`, the induced operator-algebra automorphism `algebraAut g`
maps the quasi-local algebra `quasiLocal L` into itself. -/
theorem covariance {G : Type*} [Group G] (act : HasGroupAction L G) (g : G) :
    ∀ T ∈ quasiLocal L, act.algebraAut g T ∈ quasiLocal L :=
  HasGroupAction.algebraAut_quasiLocal_le act g

/-- **Axiom (iv): Vacuum invariance.**  For any `G`-action
`act : HasGroupAction L G` and any `g : G`, the unitary representation
`unitaryAction g` fixes the canonical vacuum vector `vacuumState L`. -/
theorem vacuum_invariance {G : Type*} [Group G]
    (act : HasGroupAction L G) (g : G) :
    act.unitaryAction g (vacuumState L) = vacuumState L :=
  HasGroupAction.unitaryAction_vacuumState L act g

end HaagKastler

end LocalNetLike
