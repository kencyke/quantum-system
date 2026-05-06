module

public import QuantumSystem.Algebra.LocalNet.QuasiLocalAlgebra.HaagKastler
public import QuantumSystem.Algebra.LocalNet.AsLocalNetLike
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Action.TypeTags

/-!
# Spin-1/2 chain on `ℤ`: a concrete Haag–Kastler example

This file is the canonical concrete instance of the abstract
`LocalNetLike.HaagKastler.{isotony, locality, covariance, vacuum_invariance}`
theorems: the **spin-1/2 chain on `ℤ` with translation action**, the canonical
infinite-lattice quantum spin system of Naaijkens 2012 §1.3.

The branch establishes that for any `[LocalNetLike L] [∀ s, Nonempty (localIdx s)]`
together with `(act : LocalNetLike.HasGroupAction L G)`, the four Haag–Kastler
axioms hold simultaneously.  This file witnesses that the hypotheses are
**non-vacuously inhabited** by a non-trivial example, by constructing all three
pieces of data:

1. `qubitChain : LocalNet` — the lattice `ℤ` with a qubit (`Fin 2`) at every site,
2. an `instance` populating `[∀ s : ℤ, Nonempty (localIdx s)]`,
3. `qubitChainTranslationAction : LocalNetLike.HasGroupAction ℤ (Multiplicative ℤ)` —
   translation of `ℤ` on itself.

The mere existence of `qubitChainTranslationAction` as an axiom-free term
constitutes the proof that the four Haag–Kastler axioms have a non-vacuous
common realisation.

## References

* Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §1.3 (canonical
  spin-chain instance).
* Verch 2025 §1.2 (axioms i–iv).
-/

@[expose] public section

/-- **Spin-1/2 chain on `ℤ`**: sites are `ℤ` and the local Hilbert-space index
at every site is `Fin 2` (a single qubit).  Declared as `def` (not `abbrev`)
so that `qubitChain.sites` stays as a non-reducible projection, allowing
typeclass inference to match the `LocalNet → LocalNetLike L.sites` instance
from `AsLocalNetLike` against `LocalNetLike qubitChain.sites` with
`L := qubitChain`. -/
def qubitChain : LocalNet := { sites := ℤ, localIdx := fun _ => Fin 2 }

/-- The spin-1/2 chain has a `Nonempty` local index set at every site.

Critically, this is a **constant-function** instance (`fun _ => ⟨0⟩`), which
makes `(hL s).some` and `(hL t).some` reduce to the same closed term
`Classical.choice ⟨0⟩` for every `s, t : ℤ`.  This is what allows
`siteIdxEquiv_referenceBasis := rfl` to typecheck in
`qubitChainTranslationAction` below — without uniformity the
`Classical.choice` opacity would block reflexivity. -/
instance instNonemptyQubitChainLocalIdx :
    ∀ s : qubitChain.sites,
      Nonempty (LocalNetLike.localIdx (L := qubitChain.sites) s) := by
  intro _
  exact ⟨(0 : Fin 2)⟩

/-- **Translation action** of `Multiplicative ℤ` on `qubitChain.sites = ℤ`.
The site action is the standard self-translation of `ℤ`, lifted from the
additive group `ℤ` to the multiplicative group `Multiplicative ℤ` via
`MulAction.toPermHom`.  Per-site identifications are the identity on
`Fin 2` (the local index type is constant), and the reference-basis
condition is reflexive thanks to the uniform `Nonempty` instance above. -/
noncomputable def qubitChainTranslationAction :
    LocalNetLike.HasGroupAction qubitChain.sites (Multiplicative ℤ) where
  siteAction := MulAction.toPermHom (Multiplicative ℤ) ℤ
  siteIdxEquiv _ _ := Equiv.refl _
  siteIdxEquiv_referenceBasis _ _ := rfl

/-- **Non-vacuous existence of a Haag–Kastler-axioms realisation.**  The
typeclass and `HasGroupAction` preconditions of the four axiom theorems
`LocalNetLike.HaagKastler.{isotony, locality, covariance, vacuum_invariance}`
are inhabited concretely by the spin-1/2 chain on `ℤ` with translation action.
Equivalently: the canonical Naaijkens 2012 quantum spin system satisfies all
four Haag–Kastler axioms simultaneously, witnessed by an axiom-free Lean
term. -/
theorem qubitChain_haag_kastler_axioms_realised :
    Nonempty
      (LocalNetLike.HasGroupAction qubitChain.sites (Multiplicative ℤ)) :=
  ⟨qubitChainTranslationAction⟩

/-! ### End-to-end sanity: the four axioms instantiate in the qubit-chain
setting. -/

example {Λ Λ' : Finset qubitChain.sites} (h : Λ ⊆ Λ') :
    LocalNetLike.localSubalgebra (L := qubitChain.sites) Λ
      ≤ LocalNetLike.localSubalgebra Λ' :=
  LocalNetLike.HaagKastler.isotony h

example {Λ₁ Λ₂ : Finset qubitChain.sites} (hd : Disjoint Λ₁ Λ₂)
    {T₁ T₂ : LocalNetLike.globalHilbert qubitChain.sites
              →L[ℂ] LocalNetLike.globalHilbert qubitChain.sites}
    (h₁ : T₁ ∈ LocalNetLike.localSubalgebra (L := qubitChain.sites) Λ₁)
    (h₂ : T₂ ∈ LocalNetLike.localSubalgebra (L := qubitChain.sites) Λ₂) :
    Commute T₁ T₂ :=
  LocalNetLike.HaagKastler.locality hd h₁ h₂

example (g : Multiplicative ℤ) :
    ∀ T ∈ LocalNetLike.quasiLocal qubitChain.sites,
      qubitChainTranslationAction.algebraAut g T
        ∈ LocalNetLike.quasiLocal qubitChain.sites :=
  LocalNetLike.HaagKastler.covariance _ qubitChainTranslationAction g

example (g : Multiplicative ℤ) :
    qubitChainTranslationAction.unitaryAction g
        (LocalNetLike.vacuumState qubitChain.sites)
      = LocalNetLike.vacuumState qubitChain.sites :=
  LocalNetLike.HaagKastler.vacuum_invariance _ qubitChainTranslationAction g
