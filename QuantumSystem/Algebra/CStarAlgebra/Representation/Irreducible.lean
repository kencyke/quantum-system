/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Algebra.CStarAlgebra.Representation.UnitaryEquiv
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.InvariantSubspace

/-!
# Irreducibility for `CStarRep`

A `*`-representation `R : CStarRep A` is *(topologically) irreducible*
when it is non-null and the only members of its lattice of closed invariant subspaces
(`CStarRep.closedInvtSubmodule`, a sublattice of Mathlib's `ClosedSubmodule ℂ R.H`) are `⊥`
and `⊤`.  The predicate
is defined here for a general `CStarRep A` (no cyclic vector, no state); since
`GNS.Representation` extends `CStarRep`, a GNS triplet `T` uses it directly as
`T.IsIrreducible` (and `T.invtSubmodule`).  The file also proves that
irreducibility is preserved under unitary equivalence — a fact
required by sector well-definedness (a sector is an equivalence class
of irreducible representations, so the irreducibility predicate must
descend to the quotient).

## Main definitions

* `CStarRep.invtSubmodule R` — the sublattice of submodules stable under every `R.π a`, the
  C\*-analogue of Mathlib's `Representation.invtSubmodule`.
* `CStarRep.closedInvtSubmodule R` — the sublattice of closed submodules stable under every
  `R.π a`.
* `CStarRep.IsIrreducible R` — `R` is non-null and the only closed
  `R`-invariant submodules are `⊥` and `⊤`.

## Main results

* `CStarRep.UnitaryEquiv.isIrreducible_iff` — irreducibility transfers
  along a unitary equivalence.
-/

@[expose] public section

namespace CStarRep

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- The sublattice of *invariant* submodules of a representation: those stable under every
`R.π a`.  Built from `Module.End.invtSubmodule` exactly as Mathlib's
`Representation.invtSubmodule`; membership is membership in `Module.End.invtSubmodule (R.π a)`
for every `a` (`mem_invtSubmodule`). -/
noncomputable def invtSubmodule (R : CStarRep A) : Sublattice (Submodule ℂ R.H) :=
  ⨅ a : A, Module.End.invtSubmodule ((R.π a : R.H →L[ℂ] R.H) : Module.End ℂ R.H)

variable {R : CStarRep A} {W : Submodule ℂ R.H}

/-- Membership in `R.invtSubmodule` is invariance under each `R.π a`, in the form of Mathlib's
`Module.End.invtSubmodule`. -/
lemma mem_invtSubmodule : W ∈ R.invtSubmodule ↔
    ∀ a : A, W ∈ Module.End.invtSubmodule ((R.π a : R.H →L[ℂ] R.H) : Module.End ℂ R.H) := by
  rw [invtSubmodule, Sublattice.mem_iInf]

/-- Membership in `R.invtSubmodule`, pointwise: `R.π a x ∈ W` for every `a` and `x ∈ W`. -/
lemma mem_invtSubmodule_iff_forall_mem :
    W ∈ R.invtSubmodule ↔ ∀ (a : A), ∀ x ∈ W, R.π a x ∈ W := by
  simp only [mem_invtSubmodule, Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
  rfl

/-- An invariant submodule is stable under each `R.π a`. -/
lemma apply_mem_of_mem_invtSubmodule (hW : W ∈ R.invtSubmodule) (a : A) {x : R.H}
    (hx : x ∈ W) : R.π a x ∈ W :=
  mem_invtSubmodule_iff_forall_mem.mp hW a x hx

/-- The orthogonal complement of an invariant submodule is invariant: `W` is invariant under
`π (a*) = (π a)†`, so `Wᗮ` is invariant under `π a`
(`InnerProductSpace.orthogonal_mem_invtSubmodule_of_adjoint`). -/
lemma orthogonal_mem_invtSubmodule (hW : W ∈ R.invtSubmodule) : Wᗮ ∈ R.invtSubmodule :=
  mem_invtSubmodule.mpr fun a => InnerProductSpace.orthogonal_mem_invtSubmodule_of_adjoint <| by
    rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star]
    exact mem_invtSubmodule.mp hW (star a)

/-- `⊤` is invariant. -/
@[simp] protected lemma invtSubmodule.top_mem : (⊤ : Submodule ℂ R.H) ∈ R.invtSubmodule := by
  simp [invtSubmodule]

/-- `⊥` is invariant. -/
@[simp] protected lemma invtSubmodule.bot_mem : (⊥ : Submodule ℂ R.H) ∈ R.invtSubmodule := by
  simp [invtSubmodule]

/-- The sublattice of *closed* invariant submodules of a representation: the closed submodules
whose underlying submodule lies in `R.invtSubmodule`.  It is closed under the lattice operations
of `ClosedSubmodule` because the closure of an invariant submodule is invariant under the
continuous operators `R.π a` (`Submodule.topologicalClosure_mem_invtSubmodule`). -/
noncomputable def closedInvtSubmodule (R : CStarRep A) : Sublattice (ClosedSubmodule ℂ R.H) where
  carrier := {W | W.toSubmodule ∈ R.invtSubmodule}
  supClosed' _ h₁ _ h₂ := mem_invtSubmodule.mpr fun a =>
    Submodule.topologicalClosure_mem_invtSubmodule
      (mem_invtSubmodule.mp (R.invtSubmodule.sup_mem h₁ h₂) a)
  infClosed' _ h₁ _ h₂ := R.invtSubmodule.inf_mem h₁ h₂

/-- A closed submodule is a closed invariant submodule iff its underlying submodule is
invariant. -/
lemma mem_closedInvtSubmodule {W : ClosedSubmodule ℂ R.H} :
    W ∈ R.closedInvtSubmodule ↔ W.toSubmodule ∈ R.invtSubmodule := Iff.rfl

/-- `⊤` is a closed invariant submodule. -/
@[simp] protected lemma closedInvtSubmodule.top_mem :
    (⊤ : ClosedSubmodule ℂ R.H) ∈ R.closedInvtSubmodule := by
  simp [mem_closedInvtSubmodule]

/-- `⊥` is a closed invariant submodule. -/
@[simp] protected lemma closedInvtSubmodule.bot_mem :
    (⊥ : ClosedSubmodule ℂ R.H) ∈ R.closedInvtSubmodule := by
  simp [mem_closedInvtSubmodule]

/-- A representation is (topologically) irreducible if it is non-null and its only closed
invariant submodules are `⊥` and `⊤` (Murphy, *C\*-algebras and Operator Theory*, §5.1).

Non-nullness is part of the definition: without it the zero representation on a
one-dimensional space would be irreducible, and no family of non-null representations could
be a complete system of irreducible representatives (`SectorFamily.IsComplete`). -/
structure IsIrreducible (R : CStarRep A) : Prop where
  /-- The representation is non-null: `π ≠ 0`. -/
  ne_zero : R.π ≠ 0
  /-- The only closed invariant submodules are `⊥` and `⊤`. -/
  eq_bot_or_eq_top : ∀ W ∈ R.closedInvtSubmodule, W = ⊥ ∨ W = ⊤

namespace UnitaryEquiv

/-- The forward direction of `isIrreducible_iff`: a unitary equivalence
transports irreducibility. -/
private lemma isIrreducible_of {R₁ R₂ : CStarRep A}
    (U : UnitaryEquiv R₁ R₂) (h₁ : R₁.IsIrreducible) : R₂.IsIrreducible := by
  refine ⟨fun h₂ => h₁.ne_zero ?_, fun W hW => ?_⟩
  · -- If `π₂ = 0`, then `U (π₁ a x) = π₂ a (U x) = 0`, so `π₁ a x = 0` by injectivity of `U`.
    ext a x
    apply U.toLinearIsometryEquiv.injective
    rw [U.intertwines_apply, h₂]
    simp
  -- Pull `W` back along `U` to a closed invariant submodule of `R₁.H`; since `U` induces an
  -- order isomorphism of closed submodules (`ClosedSubmodule.mapEquiv`), `⊥` and `⊤` go back
  -- to `⊥` and `⊤`.
  set e : R₁.H ≃L[ℂ] R₂.H := U.toLinearIsometryEquiv.toContinuousLinearEquiv
  have hW' : W.mapEquiv e.symm ∈ R₁.closedInvtSubmodule := by
    refine mem_invtSubmodule_iff_forall_mem.mpr fun a x hx => ?_
    simp only [ClosedSubmodule.mem_toSubmodule_iff, ClosedSubmodule.mem_mapEquiv_iff,
      ContinuousLinearEquiv.symm_symm] at hx ⊢
    rw [show e (R₁.π a x) = R₂.π a (e x) from U.intertwines_apply a x]
    exact apply_mem_of_mem_invtSubmodule hW a hx
  have hW_eq : (W.mapEquiv e.symm).mapEquiv e = W := by
    rw [ClosedSubmodule.mapEquiv_symm, Equiv.apply_symm_apply]
  rcases h₁.eq_bot_or_eq_top _ hW' with h | h
  · exact Or.inl (by rw [← hW_eq, h, ClosedSubmodule.mapEquiv_bot_eq_bot])
  · exact Or.inr (by rw [← hW_eq, h, ClosedSubmodule.mapEquiv_top_eq_top])

/-- Irreducibility transfers along unitary equivalence. -/
lemma isIrreducible_iff {R₁ R₂ : CStarRep A} (U : UnitaryEquiv R₁ R₂) :
    R₁.IsIrreducible ↔ R₂.IsIrreducible :=
  ⟨isIrreducible_of U, isIrreducible_of U.symm⟩

end UnitaryEquiv

end CStarRep
