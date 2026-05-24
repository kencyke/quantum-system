module

public import QuantumSystem.Algebra.LocalNet.AsLocalNetLike
public import QuantumSystem.Algebra.QuasiLocalAlgebra.HaagKastler

/-!
# Spin-1/2 chain on `ℤ`: a concrete lattice Haag–Kastler example

The **spin-1/2 chain on `ℤ` with translation action**, the canonical
infinite-lattice quantum spin system of Naaijkens 2012 §1.3.  This file
witnesses that the abstract `LocalNetLike.HaagKastler.{isotony, locality,
covariance}` theorems and the `vacuum_vector_invariance` reference-vector
layer admit a non-trivial common realisation, by constructing:

1. `qubitChain : LocalNet` — the lattice `ℤ` with a qubit (`Fin 2`) at every site;
2. `instNonemptyQubitChainLocalIdx` — the per-site nondegeneracy instance;
3. `qubitChainReferenceBasis` — the constant `0`-tuple as sector tuple `Ω`;
4. `qubitChainTranslationAction :
   LocalNetLike.HasGroupAction qubitChain.sites qubitChainReferenceBasis
     (Multiplicative ℤ)` — translation of `ℤ` on itself.

This is a lattice/spin-system model, not a continuous-spacetime double-cone
model: disjoint finite subsets of `ℤ` play the role of independent regions.

## References

* Naaijkens, *Anyons in Infinite Quantum Systems*, 2012, §1.3.
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

/-- The spin-1/2 chain has a `Nonempty` local index set at every site.  The
constant-function shape (`fun _ => ⟨0⟩`) is what lets the sector-compatibility
field `siteIdxEquiv_sectorVec := rfl` typecheck in
`qubitChainTranslationAction` below. -/
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

/-- The canonical sector tuple of `qubitChain` used in this example: the
constant `0`-tuple in `Fin 2`. -/
abbrev qubitChainReferenceBasis :
    (s : qubitChain.sites) → LocalNetLike.localIdx (L := qubitChain.sites) s :=
  fun _ => (0 : Fin 2)

/-- **Translation action** of `Multiplicative ℤ` on `qubitChain.sites = ℤ`:
self-translation of `ℤ` lifted via `MulAction.toPermHom`, with identity
per-site identifications.  Sector compatibility holds by `rfl` since `Ω`
is constant. -/
noncomputable def qubitChainTranslationAction :
    LocalNetLike.HasGroupAction qubitChain.sites
      qubitChainReferenceBasis (Multiplicative ℤ) where
  siteAction := MulAction.toPermHom (Multiplicative ℤ) ℤ
  siteIdxEquiv _ _ := Equiv.refl _
  siteIdxEquiv_sectorVec _ _ := rfl

private lemma qubitChain_piCongr_const_refl_apply
    (e : Equiv.Perm ℤ) (f : (s : ℤ) → Fin 2) (t : ℤ) :
    (Equiv.piCongr (W := fun _ : ℤ => Fin 2) (Z := fun _ : ℤ => Fin 2)
        e (fun _ : ℤ => Equiv.refl (Fin 2)) f) t = f (e.symm t) := by
  obtain ⟨s, rfl⟩ : ∃ s, e s = t := ⟨e.symm t, e.apply_symm_apply t⟩
  rw [Equiv.piCongr_apply_apply]
  simp

/-- The translation action on the spin chain promotes to a genuine `Multiplicative ℤ`-action
on dependent qubit-index tuples. -/
instance instQubitChainTranslationActionIsGenuineAction :
    qubitChainTranslationAction.IsGenuineAction where
  piAction_one := by
    ext f s
    change (Equiv.piCongr (W := fun _ : ℤ => Fin 2) (Z := fun _ : ℤ => Fin 2)
        ((MulAction.toPermHom (Multiplicative ℤ) ℤ) 1)
        (fun _ : ℤ => Equiv.refl (Fin 2)) (f : (s : ℤ) → Fin 2)) (show ℤ from s) =
      (f : (s : ℤ) → Fin 2) (show ℤ from s)
    rw [qubitChain_piCongr_const_refl_apply]
    exact congrArg (f : (s : ℤ) → Fin 2)
      (show ((1 : Multiplicative ℤ)⁻¹ • (show ℤ from s)) = (show ℤ from s) by
        rw [inv_one, one_smul])
  piAction_mul g h := by
    ext f s
    change (Equiv.piCongr (W := fun _ : ℤ => Fin 2) (Z := fun _ : ℤ => Fin 2)
        ((MulAction.toPermHom (Multiplicative ℤ) ℤ) (g * h))
        (fun _ : ℤ => Equiv.refl (Fin 2)) (f : (s : ℤ) → Fin 2)) (show ℤ from s) =
      ((Equiv.piCongr (W := fun _ : ℤ => Fin 2) (Z := fun _ : ℤ => Fin 2)
          ((MulAction.toPermHom (Multiplicative ℤ) ℤ) g)
          (fun _ : ℤ => Equiv.refl (Fin 2)))
        ((Equiv.piCongr (W := fun _ : ℤ => Fin 2) (Z := fun _ : ℤ => Fin 2)
          ((MulAction.toPermHom (Multiplicative ℤ) ℤ) h)
          (fun _ : ℤ => Equiv.refl (Fin 2))) (f : (s : ℤ) → Fin 2))) (show ℤ from s)
    rw [qubitChain_piCongr_const_refl_apply, qubitChain_piCongr_const_refl_apply,
      qubitChain_piCongr_const_refl_apply]
    exact congrArg (f : (s : ℤ) → Fin 2)
      (show ((g * h)⁻¹ • (show ℤ from s)) = h⁻¹ • g⁻¹ • (show ℤ from s) by
        rw [mul_inv_rev, mul_smul])

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
    (𝔄(Λ) : StarSubalgebra ℂ
        (LocalNetLike.globalHilbert qubitChain.sites qubitChainReferenceBasis
          →L[ℂ] LocalNetLike.globalHilbert qubitChain.sites qubitChainReferenceBasis))
      ≤ 𝔄(Λ') :=
  LocalNetLike.HaagKastler.isotony h

example {Λ₁ Λ₂ : Finset qubitChain.sites} (hd : Disjoint Λ₁ Λ₂)
    {T₁ T₂ : LocalNetLike.globalHilbert qubitChain.sites qubitChainReferenceBasis
              →L[ℂ] LocalNetLike.globalHilbert qubitChain.sites qubitChainReferenceBasis}
    (h₁ : T₁ ∈ (𝔄(Λ₁) : StarSubalgebra ℂ
        (LocalNetLike.globalHilbert qubitChain.sites qubitChainReferenceBasis
          →L[ℂ] LocalNetLike.globalHilbert qubitChain.sites qubitChainReferenceBasis)))
    (h₂ : T₂ ∈ (𝔄(Λ₂) : StarSubalgebra ℂ
        (LocalNetLike.globalHilbert qubitChain.sites qubitChainReferenceBasis
          →L[ℂ] LocalNetLike.globalHilbert qubitChain.sites qubitChainReferenceBasis))) :
    Commute T₁ T₂ :=
  LocalNetLike.HaagKastler.locality hd h₁ h₂

example (g : Multiplicative ℤ) :
    ∀ T ∈ LocalNetLike.quasiLocal qubitChain.sites qubitChainReferenceBasis,
      qubitChainTranslationAction.algebraAut g T
        ∈ LocalNetLike.quasiLocal qubitChain.sites qubitChainReferenceBasis :=
  LocalNetLike.HaagKastler.covariance _ _ qubitChainTranslationAction g

/-- The spin-1/2 chain on `ℤ` together with the translation action satisfies the
public bundled covariant Haag–Kastler interface. -/
instance : LocalNetLike.CovariantHaagKastlerNet qubitChain.sites
    qubitChainReferenceBasis (Multiplicative ℤ)
    qubitChainTranslationAction where

example (g h : Multiplicative ℤ)
    (T : ↥(LocalNetLike.quasiLocal qubitChain.sites qubitChainReferenceBasis)) :
    qubitChainTranslationAction.quasiLocalAut (g * h) T =
      qubitChainTranslationAction.quasiLocalAut g
        (qubitChainTranslationAction.quasiLocalAut h T) :=
  qubitChainTranslationAction.quasiLocalAut_mul_apply g h T

example (T : ↥(LocalNetLike.quasiLocal qubitChain.sites qubitChainReferenceBasis)) :
    qubitChainTranslationAction.quasiLocalAut 1 T = T :=
  qubitChainTranslationAction.quasiLocalAut_one_apply T

example (g : Multiplicative ℤ) :
    qubitChainTranslationAction.unitaryAction g (LocalNetLike.vacuumVector qubitChain.sites qubitChainReferenceBasis)
      = (LocalNetLike.vacuumVector qubitChain.sites qubitChainReferenceBasis) :=
  LocalNetLike.HaagKastler.vacuum_vector_invariance _ _ qubitChainTranslationAction g

example (g : Multiplicative ℤ)
    (T : ↥(LocalNetLike.quasiLocal qubitChain.sites qubitChainReferenceBasis)) :
    LocalNetLike.vacuumFunctionalOnQuasiLocal qubitChain.sites qubitChainReferenceBasis (qubitChainTranslationAction.quasiLocalEnd g T)
      = LocalNetLike.vacuumFunctionalOnQuasiLocal qubitChain.sites qubitChainReferenceBasis T :=
  LocalNetLike.HaagKastler.vacuum_functional_invariance _ _ qubitChainTranslationAction g T

example (g : Multiplicative ℤ)
    (T : ↥(LocalNetLike.quasiLocal qubitChain.sites qubitChainReferenceBasis)) :
    LocalNetLike.vacuumFunctionalOnQuasiLocal qubitChain.sites qubitChainReferenceBasis (qubitChainTranslationAction.quasiLocalAut g T)
      = LocalNetLike.vacuumFunctionalOnQuasiLocal qubitChain.sites qubitChainReferenceBasis T :=
  LocalNetLike.HaagKastler.vacuum_functional_invariance_aut _ _
    qubitChainTranslationAction g T

example (Λ : Finset qubitChain.sites)
    (a : LocalNetLike.localAlgebra (L := qubitChain.sites) Λ) :
    LocalNetLike.localAlgebraEmbed Λ a ∈
      (𝔄(Λ) : StarSubalgebra ℂ
        (LocalNetLike.globalHilbert qubitChain.sites qubitChainReferenceBasis
          →L[ℂ] LocalNetLike.globalHilbert qubitChain.sites qubitChainReferenceBasis)) :=
  LocalNetLike.localAlgebraEmbed_mem_localSubalgebra (Ω := qubitChainReferenceBasis) Λ a

example (g : Multiplicative ℤ) (Λ : Finset qubitChain.sites)
    (a : LocalNetLike.localAlgebra (L := qubitChain.sites) Λ) :
    qubitChainTranslationAction.algebraAut g (LocalNetLike.localAlgebraEmbed Λ a)
      ∈ (𝔄(qubitChainTranslationAction.regionImage g Λ) : StarSubalgebra ℂ
        (LocalNetLike.globalHilbert qubitChain.sites qubitChainReferenceBasis
          →L[ℂ] LocalNetLike.globalHilbert qubitChain.sites qubitChainReferenceBasis)) :=
  LocalNetLike.HasGroupAction.algebraAut_localSubalgebra_le qubitChainTranslationAction g Λ _
    (LocalNetLike.localAlgebraEmbed_mem_localSubalgebra (Ω := qubitChainReferenceBasis) Λ a)

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
