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
when it is non-null and its only closed invariant subspaces are `⊥` and `⊤`.  The predicate
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

/-- A representation is (topologically) irreducible if it is non-null and its only closed
invariant submodules are `⊥` and `⊤` (Murphy, *C\*-algebras and Operator Theory*, §5.1).

Non-nullness is part of the definition: without it the zero representation on a
one-dimensional space would be irreducible, and no family of non-null representations could
be a complete system of irreducible representatives (`SectorFamily.IsComplete`). -/
structure IsIrreducible (R : CStarRep A) : Prop where
  /-- The representation is non-null: `π ≠ 0`. -/
  ne_zero : R.π ≠ 0
  /-- The only closed invariant submodules are `⊥` and `⊤`. -/
  eq_bot_or_eq_top : ∀ W : Submodule ℂ R.H,
    IsClosed (W : Set R.H) → W ∈ R.invtSubmodule → (W = ⊥ ∨ W = ⊤)

namespace UnitaryEquiv

/-- The forward direction of `isIrreducible_iff`: a unitary equivalence
transports irreducibility. -/
private lemma isIrreducible_of {R₁ R₂ : CStarRep A}
    (U : UnitaryEquiv R₁ R₂) (h₁ : R₁.IsIrreducible) : R₂.IsIrreducible := by
  refine ⟨fun h₂ => h₁.ne_zero ?_, fun W hW_closed hW_inv => ?_⟩
  · -- If `π₂ = 0`, then `U (π₁ a x) = π₂ a (U x) = 0`, so `π₁ a x = 0` by injectivity of `U`.
    ext a x
    apply U.toLinearIsometryEquiv.injective
    rw [U.intertwines_apply, h₂]
    simp
  -- Pull `W` back along `U` to obtain a closed invariant submodule `W'` of `R₁.H`.
  set f : R₁.H →L[ℂ] R₂.H := (U.toLinearIsometryEquiv : R₁.H →L[ℂ] R₂.H) with hf
  let W' : Submodule ℂ R₁.H := W.comap f.toLinearMap
  have hW'_closed : IsClosed (W' : Set R₁.H) :=
    hW_closed.preimage f.continuous
  have hW'_inv : W' ∈ R₁.invtSubmodule := by
    refine mem_invtSubmodule_iff_forall_mem.mpr fun a x hx_mem => ?_
    -- `hx_mem : x ∈ W'` means `f x ∈ W`; the goal is `f (R₁.π a x) ∈ W`.
    change f ((R₁.π a) x) ∈ W
    rw [show f ((R₁.π a) x) = (R₂.π a) (f x) from U.intertwines_apply a x]
    exact apply_mem_of_mem_invtSubmodule hW_inv a hx_mem
  -- `U` is surjective, with inverse `U.symm`.
  have hsurj : ∀ w : R₂.H, f (U.toLinearIsometryEquiv.symm w) = w := fun w => by simp [hf]
  rcases h₁.eq_bot_or_eq_top W' hW'_closed hW'_inv with hbot | htop
  · -- `W' = ⊥`: every `w ∈ W` is `f x` with `x = U.symm w ∈ W' = ⊥`, hence `w = 0`.
    refine Or.inl (le_antisymm (fun w hw => ?_) bot_le)
    have hx_mem : U.toLinearIsometryEquiv.symm w ∈ W' := by
      change f _ ∈ W
      rw [hsurj]
      exact hw
    have hx_zero : U.toLinearIsometryEquiv.symm w = 0 := by
      simpa [hbot] using hx_mem
    have : w = 0 := by rw [← hsurj w, hx_zero, map_zero]
    simp [this]
  · -- `W' = ⊤`: every `w` is `f (U.symm w)` with `U.symm w ∈ W' = ⊤`, hence `w ∈ W`.
    refine Or.inr (le_antisymm le_top fun w _ => ?_)
    have hx_mem : U.toLinearIsometryEquiv.symm w ∈ W' := htop ▸ Submodule.mem_top
    simpa [W', hsurj] using hx_mem

/-- Irreducibility transfers along unitary equivalence. -/
lemma isIrreducible_iff {R₁ R₂ : CStarRep A} (U : UnitaryEquiv R₁ R₂) :
    R₁.IsIrreducible ↔ R₂.IsIrreducible :=
  ⟨isIrreducible_of U, isIrreducible_of U.symm⟩

end UnitaryEquiv

end CStarRep
