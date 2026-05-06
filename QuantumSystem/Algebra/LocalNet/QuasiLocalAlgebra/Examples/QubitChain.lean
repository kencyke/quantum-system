module

public import QuantumSystem.Algebra.LocalNet.QuasiLocalAlgebra.HaagKastler
public import QuantumSystem.Algebra.LocalNet.AsLocalNetLike
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Action.TypeTags

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

private lemma qubitChainTranslationAction_siteAction_one (t : ℤ) :
    qubitChainTranslationAction.siteAction (1 : Multiplicative ℤ) t = t := by
  change MulAction.toPerm (1 : Multiplicative ℤ) t = t
  exact one_smul (Multiplicative ℤ) t

private lemma qubitChainTranslationAction_siteAction_mul
    (g h : Multiplicative ℤ) (t : ℤ) :
    qubitChainTranslationAction.siteAction (g * h) t
      = qubitChainTranslationAction.siteAction g
          (qubitChainTranslationAction.siteAction h t) := by
  change MulAction.toPerm (g * h) t = MulAction.toPerm g (MulAction.toPerm h t)
  exact mul_smul g h t

/-- The qubit-chain translation action satisfies the dependent-index coherence
laws: the per-site identifications are `Equiv.refl`, so `piAction` reduces to
the bare permutation, which is multiplicative because `siteAction` is. -/
noncomputable instance qubitChainTranslationAction_isCoherent :
    LocalNetLike.HasGroupAction.IsCoherent qubitChainTranslationAction where
  piAction_one := by
    ext f t
    -- Rewrite t as (siteAction 1) t = t, then use piAction_apply_apply.
    have ht_eq : t = qubitChainTranslationAction.siteAction (1 : Multiplicative ℤ) t :=
      (qubitChainTranslationAction_siteAction_one t).symm
    conv_lhs => rw [ht_eq]
    rw [LocalNetLike.HasGroupAction.piAction_apply_apply]
    -- siteIdxEquiv 1 _ = Equiv.refl _, so `(refl) (f t) = f t = (Equiv.refl _) f t`.
    rfl
  piAction_mul g h := by
    ext f t
    -- Both sides equal f ((siteAction h).symm ((siteAction g).symm t)).
    -- LHS: piAction (g*h) f t.  Set s := (siteAction (g*h)).symm t.
    set s : ℤ := (qubitChainTranslationAction.siteAction (g * h)).symm t with hs_def
    have ht_eq_LHS : t = qubitChainTranslationAction.siteAction (g * h) s := by
      simp [hs_def]
    -- RHS: (piAction g (piAction h f)) t.  Set s' := (siteAction g).symm t.
    set s' : ℤ := (qubitChainTranslationAction.siteAction g).symm t with hs'_def
    have ht_eq_RHS : t = qubitChainTranslationAction.siteAction g s' := by
      simp [hs'_def]
    have hLHS : (qubitChainTranslationAction.piAction (g * h)) f t = f s := by
      conv_lhs => rw [ht_eq_LHS]
      rw [LocalNetLike.HasGroupAction.piAction_apply_apply]
      rfl
    have hRHS : ((qubitChainTranslationAction.piAction h).trans
            (qubitChainTranslationAction.piAction g)) f t
        = (qubitChainTranslationAction.piAction h f) s' := by
      change (qubitChainTranslationAction.piAction g
              (qubitChainTranslationAction.piAction h f)) t = _
      conv_lhs => rw [ht_eq_RHS]
      rw [LocalNetLike.HasGroupAction.piAction_apply_apply]
      rfl
    rw [hLHS, hRHS]
    -- Goal: f s = piAction h f s'
    -- piAction h f s' = f ((siteAction h).symm s'),
    -- and s = (siteAction (g*h)).symm t = (siteAction h).symm ((siteAction g).symm t)
    --                                   = (siteAction h).symm s'.
    set s'' : ℤ := (qubitChainTranslationAction.siteAction h).symm s' with hs''_def
    have hs'_eq : s' = qubitChainTranslationAction.siteAction h s'' := by
      simp [hs''_def]
    have hRHS2 : qubitChainTranslationAction.piAction h f s' = f s'' := by
      conv_lhs => rw [hs'_eq]
      rw [LocalNetLike.HasGroupAction.piAction_apply_apply]
      rfl
    rw [hRHS2]
    -- Goal: f s = f s''.  Need s = s''.
    congr 1
    rw [hs_def, hs''_def, hs'_def]
    -- Goal: (siteAction (g*h)).symm t = (siteAction h).symm ((siteAction g).symm t)
    apply (qubitChainTranslationAction.siteAction (g * h)).injective
    rw [Equiv.apply_symm_apply,
      qubitChainTranslationAction_siteAction_mul g h,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- **Non-vacuous existence of a lattice Haag–Kastler realisation.**  The
typeclass and `HasGroupAction` preconditions of the local-net theorems and the
reference-vector invariance theorem are inhabited concretely by the spin-1/2
chain on `ℤ` with translation action. -/
theorem qubitChain_haag_kastler_axioms_realised :
    Nonempty
      (LocalNetLike.HasGroupAction qubitChain.sites (Multiplicative ℤ)) :=
  ⟨qubitChainTranslationAction⟩

/-- **Concrete `HaagKastlerNet` witness.**  The spin-1/2 chain on `ℤ`
satisfies every component of the public Haag–Kastler bundle: full
functoriality and injectivity of isotony, a faithful local representation
on `regionHilbert Λ`, compatibility between that representation and the
abstract isotony embedding, and per-site nondegeneracy. -/
instance : LocalNetLike.HaagKastlerNet qubitChain.sites where
  nonempty_localIdx := instNonemptyQubitChainLocalIdx

/-- **Concrete `HaagKastlerCovariantNet` witness.**  The translation
action on the spin-1/2 chain is coherent, hence promotes the static
`HaagKastlerNet` data to a covariant Haag–Kastler net. -/
instance : LocalNetLike.HaagKastlerCovariantNet qubitChain.sites
    (Multiplicative ℤ) qubitChainTranslationAction where
  isCoherent := qubitChainTranslationAction_isCoherent

/-! ### End-to-end sanity: the lattice local-net statements instantiate in the
qubit-chain setting. -/

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
        (LocalNetLike.vacuumVector qubitChain.sites)
      = LocalNetLike.vacuumVector qubitChain.sites :=
  LocalNetLike.HaagKastler.vacuum_vector_invariance _ qubitChainTranslationAction g

example (g : Multiplicative ℤ)
    (T : ↥(LocalNetLike.quasiLocal qubitChain.sites)) :
    LocalNetLike.vacuumStateOnQuasiLocal qubitChain.sites
        (qubitChainTranslationAction.quasiLocalEnd g T)
      = LocalNetLike.vacuumStateOnQuasiLocal qubitChain.sites T :=
  LocalNetLike.HaagKastler.vacuum_state_invariance _ qubitChainTranslationAction g T

example (Λ : Finset qubitChain.sites)
    (a : LocalNetLike.localAlgebra (L := qubitChain.sites) Λ) :
    LocalNetLike.localAlgebraEmbed Λ a
      ∈ LocalNetLike.localSubalgebra (L := qubitChain.sites) Λ :=
  LocalNetLike.localAlgebraEmbed_mem_localSubalgebra Λ a

example (g : Multiplicative ℤ) (Λ : Finset qubitChain.sites)
    (a : LocalNetLike.localAlgebra (L := qubitChain.sites) Λ) :
    qubitChainTranslationAction.algebraAut g (LocalNetLike.localAlgebraEmbed Λ a)
      ∈ LocalNetLike.localSubalgebra (L := qubitChain.sites)
          (qubitChainTranslationAction.regionImage g Λ) :=
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
