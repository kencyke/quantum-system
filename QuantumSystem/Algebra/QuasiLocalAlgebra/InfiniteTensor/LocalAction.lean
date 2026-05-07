module

public import QuantumSystem.Algebra.QuasiLocalAlgebra.InfiniteTensor.ReferenceBasis

/-!
# Operator-algebra action on the reference-basis sector

For the canonical reference-basis sector `globalHilbertOmega L Ω_referenceBasis`,
we transport the existing local-operator embedding
`LocalEmbed.lean : localEmbed Λ M : globalHilbert L →L[ℂ] globalHilbert L`
through the linear isometry equivalence `globalHilbertOmegaReferenceBasisEquiv`
(Phase 3) to obtain its incomplete-tensor-product counterpart.

This realises the "operator `M ⊗ 1_{complement}`" action on the abstract
reference-basis sector and makes the algebraic-colimit construction of
`globalHilbertOmega` interoperable with the operator algebra side already
formalised on `globalHilbert`.

A general-`Ω` operator-algebra action (where `Ω` is an arbitrary unit-vector
family rather than the canonical basis one) requires a fresh
basis-decomposition `regionIdx Λ' ≃ regionIdx Λ × regionIdx (Λ' \ Λ)` and is
left for follow-up work.

## Main definitions

* `LocalNetLike.localEmbedΩRef Λ M` — the continuous linear operator on
  the reference-basis incomplete tensor product
  `globalHilbertOmega L Ω_referenceBasis Ω_referenceBasis_norm` corresponding
  to a finite-region operator `M : ℋ(Λ) →L[ℂ] ℋ(Λ)`.

## Main results

* `LocalNetLike.localEmbedΩRef_one` — identity on the region maps to
  identity on the global sector.
* `LocalNetLike.localEmbedΩRef_zero` — zero maps to zero.
-/

@[expose] public section

open scoped LocalNetLike InnerProductSpace

namespace LocalNetLike

variable {L : Type*} [DecidableEq L] [LocalNetLike L]
    [hL : ∀ s : L, Nonempty (LocalNetLike.localIdx (L := L) s)]

/-- The transported local-operator embedding on the reference-basis
incomplete-tensor-product sector
`globalHilbertOmega L Ω_referenceBasis Ω_referenceBasis_norm`.

Defined by conjugating the basis-indexed `localEmbed Λ M` via the linear
isometry equivalence `globalHilbertOmegaReferenceBasisEquiv` of Phase 3:
`localEmbedΩRef Λ M = equiv.symm ∘L localEmbed Λ M ∘L equiv`. -/
noncomputable def localEmbedΩRef (Λ : Finset L)
    (M : ℋ(Λ) →L[ℂ] ℋ(Λ)) :
    globalHilbertOmega L (Ω_referenceBasis (L := L)) Ω_referenceBasis_norm
      →L[ℂ] globalHilbertOmega L (Ω_referenceBasis (L := L)) Ω_referenceBasis_norm :=
  let e :
      globalHilbertOmega L (Ω_referenceBasis (L := L)) Ω_referenceBasis_norm
        ≃ₗᵢ[ℂ] globalHilbert L := globalHilbertOmegaReferenceBasisEquiv
  e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((localEmbed (L := L) Λ M).comp e.toContinuousLinearEquiv.toContinuousLinearMap)

/-- Action on a vector, expressed in terms of the underlying basis-indexed
embedding `localEmbed`.  This is the defining identity, not a separate
property. -/
theorem localEmbedΩRef_apply (Λ : Finset L) (M : ℋ(Λ) →L[ℂ] ℋ(Λ))
    (x : globalHilbertOmega L (Ω_referenceBasis (L := L))
            Ω_referenceBasis_norm) :
    localEmbedΩRef Λ M x
      = (globalHilbertOmegaReferenceBasisEquiv (L := L)).symm
          ((localEmbed (L := L) Λ M)
            (globalHilbertOmegaReferenceBasisEquiv (L := L) x)) := rfl

/-- The action sends the zero operator to zero. -/
@[simp]
theorem localEmbedΩRef_zero (Λ : Finset L) :
    localEmbedΩRef (L := L) Λ 0 = 0 := by
  ext x
  rw [localEmbedΩRef_apply, localEmbed_zero]
  simp

/-- The action sends the identity to the identity. -/
@[simp]
theorem localEmbedΩRef_one (Λ : Finset L) :
    localEmbedΩRef (L := L) Λ (ContinuousLinearMap.id ℂ ℋ(Λ))
      = ContinuousLinearMap.id ℂ
          (globalHilbertOmega L (Ω_referenceBasis (L := L)) Ω_referenceBasis_norm) := by
  ext x
  rw [localEmbedΩRef_apply, localEmbed_one]
  simp

/-- The action is additive: `localEmbedΩRef Λ (M + N) = localEmbedΩRef Λ M
+ localEmbedΩRef Λ N`. -/
theorem localEmbedΩRef_add (Λ : Finset L) (M N : ℋ(Λ) →L[ℂ] ℋ(Λ)) :
    localEmbedΩRef (L := L) Λ (M + N)
      = localEmbedΩRef (L := L) Λ M + localEmbedΩRef (L := L) Λ N := by
  ext x
  rw [localEmbedΩRef_apply, localEmbed_add]
  simp [localEmbedΩRef_apply]

/-- The action is `ℂ`-linear in the operator: `localEmbedΩRef Λ (c • M)
= c • localEmbedΩRef Λ M`. -/
theorem localEmbedΩRef_smul (Λ : Finset L) (c : ℂ) (M : ℋ(Λ) →L[ℂ] ℋ(Λ)) :
    localEmbedΩRef (L := L) Λ (c • M) = c • localEmbedΩRef (L := L) Λ M := by
  ext x
  rw [localEmbedΩRef_apply, localEmbed_smul]
  simp [localEmbedΩRef_apply]

/-- The action is multiplicative: composition of finite-region operators
goes to composition of their lifts. -/
theorem localEmbedΩRef_mul (Λ : Finset L) (M N : ℋ(Λ) →L[ℂ] ℋ(Λ)) :
    localEmbedΩRef (L := L) Λ (M.comp N)
      = (localEmbedΩRef (L := L) Λ M).comp (localEmbedΩRef (L := L) Λ N) := by
  ext x
  rw [localEmbedΩRef_apply, localEmbed_mul]
  simp [localEmbedΩRef_apply]

end LocalNetLike
