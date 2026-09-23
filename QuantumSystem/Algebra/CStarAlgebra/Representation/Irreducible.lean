module

public import QuantumSystem.Algebra.CStarAlgebra.Representation.UnitaryEquiv

/-!
# Irreducibility for `CStarRep`

A `*`-representation `R : CStarRep A` is *(topologically) irreducible*
when it is non-null and its only closed invariant subspaces are `⊥` and `⊤`.  The predicate
is defined here for a general `CStarRep A` (no cyclic vector, no state);
`GNS.Representation.IsIrreducible` is this predicate applied to the
underlying `CStarRep` of a GNS triplet.  The file also proves that
irreducibility is preserved under unitary equivalence — a fact
required by sector well-definedness (a sector is an equivalence class
of irreducible representations, so the irreducibility predicate must
descend to the quotient).

## Main definitions

* `CStarRep.IsInvariant R W` — `W` is stable under every `R.π a`.
* `CStarRep.IsIrreducible R` — `R` is non-null and the only closed
  `R`-invariant submodules are `⊥` and `⊤`.

## Main results

* `CStarRep.UnitaryEquiv.isIrreducible_iff` — irreducibility transfers
  along a unitary equivalence.
-/

@[expose] public section

namespace CStarRep

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- A submodule `W` of the carrier of a representation is *invariant* if
it is stable under the action of every `R.π a`. -/
def IsInvariant (R : CStarRep A) (W : Submodule ℂ R.H) : Prop :=
  ∀ a : A, W.map (R.π a).toLinearMap ≤ W

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
    IsClosed (W : Set R.H) → R.IsInvariant W → (W = ⊥ ∨ W = ⊤)

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
  have hW'_inv : R₁.IsInvariant W' := by
    intro a y hy
    obtain ⟨x, hx_mem, rfl⟩ := hy
    -- `hx_mem : x ∈ W'` means `f x ∈ W`; the goal is `f (R₁.π a x) ∈ W`.
    change f ((R₁.π a) x) ∈ W
    rw [show f ((R₁.π a) x) = (R₂.π a) (f x) from U.intertwines_apply a x]
    exact hW_inv a (Submodule.mem_map.mpr ⟨f x, hx_mem, rfl⟩)
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
