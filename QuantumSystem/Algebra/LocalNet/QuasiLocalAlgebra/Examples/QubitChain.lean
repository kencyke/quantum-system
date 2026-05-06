module

public import QuantumSystem.Algebra.LocalNet.AsLocalNetLike
public import QuantumSystem.Algebra.LocalNet.QuasiLocalAlgebra.HaagKastler

/-!
# Spin-1/2 chain on `ℤ`: a concrete lattice Haag–Kastler example

This file is the canonical concrete instance of the abstract
`LocalNetLike.HaagKastler.{isotony, locality, covariance}` theorems, together
with the separate `vacuum_vector_invariance` reference-vector layer: the
**spin-1/2 chain on `ℤ` with translation action**, the canonical infinite-lattice
quantum spin system of Naaijkens 2012 §1.3.

The branch establishes that for any `[LocalNetLike L] [∀ s, Nonempty (localIdx s)]`
together with `(act : LocalNetLike.HasGroupAction L G)`, the lattice local-net
conditions and canonical reference-vector invariance hold simultaneously.  This file witnesses that the hypotheses are
**non-vacuously inhabited** by a non-trivial example, by constructing all three
pieces of data:

1. `qubitChain : LocalNet` — the lattice `ℤ` with a qubit (`Fin 2`) at every site,
2. an `instance` populating `[∀ s : ℤ, Nonempty (localIdx s)]`,
3. `qubitChainTranslationAction : LocalNetLike.HasGroupAction ℤ (Multiplicative ℤ)` —
   translation of `ℤ` on itself.

The mere existence of `qubitChainTranslationAction` as a proof-producing term
shows that the lattice local-net conditions and reference-vector invariance have
a non-vacuous common realisation.

This is a lattice/spin-system model: disjoint finite subsets of `ℤ` play the role
of independent regions.  It is not a continuous-spacetime double-cone model.

## References

* Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §1.3 (canonical
  spin-chain instance).
* Verch 2025 §1.2 for the general local-net and invariant-state framework.
-/

@[expose] public section

open scoped LocalNetLike

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

/-- Companion instance stated in the `LocalNet`-shape `qubitChain.localIdx s`.
This duplicates `instNonemptyQubitChainLocalIdx` with the type expression
required by the parameterised instances in `AsLocalNetLike` (which ask for
`[∀ s : L.sites, Nonempty (L.localIdx s)]` rather than the abstract
`LocalNetLike.localIdx` projection). -/
instance instNonemptyQubitChainLocalNetLocalIdx :
    ∀ s : qubitChain.sites, Nonempty (qubitChain.localIdx s) := fun _ => ⟨(0 : Fin 2)⟩

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

/-- **Concrete `HaagKastlerNet` witness.**  The spin-1/2 chain on `ℤ`
satisfies every component of the public Haag–Kastler bundle: full
functoriality and injectivity of isotony, a faithful local representation
on `regionHilbert Λ`, compatibility between that representation and the
abstract isotony embedding, and per-site nondegeneracy. -/
instance : LocalNetLike.HaagKastlerNet qubitChain.sites where
  nonempty_localIdx := instNonemptyQubitChainLocalIdx

/-! ### End-to-end sanity: the lattice local-net statements instantiate in the
qubit-chain setting. -/

example {Λ Λ' : Finset qubitChain.sites} (h : Λ ⊆ Λ') :
    𝔄(Λ) ≤ 𝔄(Λ') :=
  LocalNetLike.HaagKastler.isotony h

example {Λ₁ Λ₂ : Finset qubitChain.sites} (hd : Disjoint Λ₁ Λ₂)
    {T₁ T₂ : LocalNetLike.globalHilbert qubitChain.sites
              →L[ℂ] LocalNetLike.globalHilbert qubitChain.sites}
    (h₁ : T₁ ∈ 𝔄(Λ₁)) (h₂ : T₂ ∈ 𝔄(Λ₂)) :
    Commute T₁ T₂ :=
  LocalNetLike.HaagKastler.locality hd h₁ h₂

example (g : Multiplicative ℤ) :
    ∀ T ∈ LocalNetLike.quasiLocal qubitChain.sites,
      qubitChainTranslationAction.algebraAut g T
        ∈ LocalNetLike.quasiLocal qubitChain.sites :=
  LocalNetLike.HaagKastler.covariance _ qubitChainTranslationAction g

example (g : Multiplicative ℤ) :
    qubitChainTranslationAction.unitaryAction g Ω(qubitChain.sites)
      = Ω(qubitChain.sites) :=
  LocalNetLike.HaagKastler.vacuum_vector_invariance _ qubitChainTranslationAction g

example (g : Multiplicative ℤ)
    (T : ↥(LocalNetLike.quasiLocal qubitChain.sites)) :
    ω(qubitChain.sites) (qubitChainTranslationAction.quasiLocalEnd g T)
      = ω(qubitChain.sites) T :=
  LocalNetLike.HaagKastler.vacuum_state_invariance _ qubitChainTranslationAction g T

example (Λ : Finset qubitChain.sites)
    (a : LocalNetLike.localAlgebra (L := qubitChain.sites) Λ) :
    LocalNetLike.localAlgebraEmbed Λ a ∈ 𝔄(Λ) :=
  LocalNetLike.localAlgebraEmbed_mem_localSubalgebra Λ a

example (g : Multiplicative ℤ) (Λ : Finset qubitChain.sites)
    (a : LocalNetLike.localAlgebra (L := qubitChain.sites) Λ) :
    qubitChainTranslationAction.algebraAut g (LocalNetLike.localAlgebraEmbed Λ a)
      ∈ 𝔄(qubitChainTranslationAction.regionImage g Λ) :=
  LocalNetLike.HasGroupAction.algebraAut_localSubalgebra_le qubitChainTranslationAction g Λ _
    (LocalNetLike.localAlgebraEmbed_mem_localSubalgebra Λ a)

noncomputable example : LocalNetLike.IsFunctorial qubitChain.sites :=
  inferInstance

noncomputable example (Λ : Finset qubitChain.sites) :
    CStarAlgebra (qubitChain.localAlgebra Λ) :=
  inferInstance

/-- C⋆-algebra structure is also visible at the abstract `LocalNetLike.localAlgebra`
projection, confirming that downstream consumers can stay typeclass-polymorphic. -/
noncomputable example (Λ : Finset qubitChain.sites) :
    CStarAlgebra (LocalNetLike.localAlgebra (L := qubitChain.sites) Λ) :=
  inferInstance
