module

public import QuantumSystem.Algebra.CStarAlgebra.Representation.UnitaryEquiv
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.AdjointNotation

/-!
# Irreducibility for `CStarRep`

A `*`-representation `R : CStarRep A` is *(topologically) irreducible*
when its only closed invariant subspaces are `⊥` and `⊤`.  This file
lifts the irreducibility predicate from `GNS.Representation` (where it
is parameterised by a state `ω`) to the more general setting of
`CStarRep A` (no cyclic vector / no state attachment), and proves that
irreducibility is preserved under unitary equivalence — a fact
required by sector well-definedness (a sector is an equivalence class
of irreducible representations, so the irreducibility predicate must
descend to the quotient).

## Main definitions

* `CStarRep.IsInvariant R W` — `W` is stable under every `R.π a`.
* `CStarRep.IsIrreducible R` — the only closed `R`-invariant
  submodules are `⊥` and `⊤`.

## Main results

* `CStarRep.UnitaryEquiv.isIrreducible_iff` — irreducibility transfers
  along a unitary equivalence.
-/

@[expose] public section

open scoped Adjoint

namespace CStarRep

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- A submodule `W` of the carrier of a representation is *invariant* if
it is stable under the action of every `R.π a`. -/
def IsInvariant (R : CStarRep A) (W : Submodule ℂ R.H) : Prop :=
  ∀ a : A, W.map (R.π a).toLinearMap ≤ W

/-- A representation is (topologically) irreducible if the only closed
invariant submodules are `⊥` and `⊤`. -/
def IsIrreducible (R : CStarRep A) : Prop :=
  ∀ W : Submodule ℂ R.H,
    IsClosed (W : Set R.H) → R.IsInvariant W → (W = ⊥ ∨ W = ⊤)

namespace UnitaryEquiv

/-- The forward direction of `isIrreducible_iff`: a unitary equivalence
transports irreducibility. -/
private lemma isIrreducible_of {R₁ R₂ : CStarRep A}
    (U : UnitaryEquiv R₁ R₂) (h₁ : R₁.IsIrreducible) : R₂.IsIrreducible := by
  intro W hW_closed hW_inv
  -- Pull `W` back along `U` to obtain a closed invariant submodule `W'` of `R₁.H`.
  let f : R₁.H →L[ℂ] R₂.H := U.unitary_map.toContinuousLinearMap
  let W' : Submodule ℂ R₁.H := W.comap f.toLinearMap
  have hW'_closed : IsClosed (W' : Set R₁.H) :=
    hW_closed.preimage f.continuous
  have hW'_inv : R₁.IsInvariant W' := by
    intro a y hy
    obtain ⟨x, hx_mem, rfl⟩ := hy
    -- `hx_mem : x ∈ W'` means `f x ∈ W`.
    -- Goal: `(R₁.π a) x ∈ W'`, i.e. `f ((R₁.π a) x) ∈ W`.
    change f ((R₁.π a) x) ∈ W
    -- Use the intertwining property `f ∘L R₁.π a = R₂.π a ∘L f`.
    have hI := congrArg (fun (g : R₁.H →L[ℂ] R₂.H) => g x) (U.intertwines a)
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply] at hI
    rw [show f ((R₁.π a) x) = (R₂.π a) (f x) from hI]
    -- `f x ∈ W` and `W` is invariant under `R₂.π a`.
    have hfx : f x ∈ W := hx_mem
    have := hW_inv a (Submodule.mem_map.mpr ⟨f x, hfx, rfl⟩)
    exact this
  rcases h₁ W' hW'_closed hW'_inv with hbot | htop
  · -- `W' = ⊥`: then every `w ∈ W` has `w = f x` with `x ∈ W' = ⊥`, hence `x = 0`, so `w = 0`.
    refine Or.inl ?_
    refine le_antisymm ?_ bot_le
    intro w hw
    -- Surjectivity of `f`: `w = f (f† w)` since `f ∘L f† = 1`.
    have hsurj : f (f† w) = w := by
      have := congrArg (fun (g : R₂.H →L[ℂ] R₂.H) => g w) U.unitary_map.comp_adjoint
      simpa using this
    set x := f† w with hx_def
    have hx_mem : x ∈ W' := by
      change f x ∈ W
      rw [hx_def]; rw [hsurj]
      exact hw
    have hx_zero : x = 0 := by
      have : x ∈ (⊥ : Submodule ℂ R₁.H) := hbot ▸ hx_mem
      simpa using this
    have : w = 0 := by rw [← hsurj, hx_zero]; simp
    exact this ▸ Submodule.zero_mem _
  · -- `W' = ⊤`: then every `x ∈ R₁.H` has `f x ∈ W`; by surjectivity, every `w ∈ R₂.H` is in `W`.
    refine Or.inr ?_
    refine le_antisymm le_top ?_
    intro w _
    have hsurj : f (f† w) = w := by
      have := congrArg (fun (g : R₂.H →L[ℂ] R₂.H) => g w) U.unitary_map.comp_adjoint
      simpa using this
    have hx_mem : f† w ∈ W' :=
      htop ▸ Submodule.mem_top
    have hfx : f (f† w) ∈ W := hx_mem
    rw [hsurj] at hfx
    exact hfx

/-- Irreducibility transfers along unitary equivalence. -/
lemma isIrreducible_iff {R₁ R₂ : CStarRep A} (U : UnitaryEquiv R₁ R₂) :
    R₁.IsIrreducible ↔ R₂.IsIrreducible :=
  ⟨isIrreducible_of U, isIrreducible_of U.symm⟩

end UnitaryEquiv

end CStarRep
