module

public import QuantumSystem.Algebra.VonNeumannAlgebra.TypeI

/-!
# Split inclusions of von Neumann algebras

An inclusion `A ≤ B` of von Neumann algebras on a Hilbert space is **split** when some type I
factor `M` interpolates: `A ≤ M ≤ B`. This is the definition of Doplicher–Longo, *Standard and
split inclusions of von Neumann algebras* (Invent. Math. 75, 1984) §1; the notion originates in
the analysis of local algebras by Buchholz, *Product states for local algebras* (Comm. Math.
Phys. 36, 1974), where the interpolating type I factor is what produces normal product states
across a commuting pair. The AQFT *split property* — this predicate applied to the inclusions
`𝓡(O₁) ≤ 𝓡(O₂)` of local von Neumann algebras of properly contained regions — lives at the net
level in `QuantumSystem.Algebra.LocalNet.SplitProperty`.

The structural content of a split inclusion is the tensor decomposition
`IsSplitInclusion.exists_tensorDecomposition`: a spatial isomorphism `U : H ≃ₗᵢ ℓ²(F) ⊗̂ (eH)`
carrying `A` into the tensor factor `B(ℓ²(F)) ⊗̄ 1` and the commutant `B′` into `1 ⊗̄ B(eH)`. It
is inherited from the type I structure theorem
(`QuantumSystem.Algebra.VonNeumannAlgebra.StructureTheorem`).

## Main definitions and results

* `VonNeumannAlgebra.IsSplitInclusion A B` — some type I factor `M` satisfies `A ≤ M ≤ B`.
* `VonNeumannAlgebra.IsSplitInclusion.le` / `mono` — a split inclusion is an inclusion, and
  splitness survives shrinking `A` and enlarging `B`.
* `VonNeumannAlgebra.IsSplitInclusion.exists_tensorDecomposition` — the split tensor
  decomposition of the inclusion.
-/

@[expose] public section

namespace VonNeumannAlgebra

open HilbertTensor

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Split inclusion of von Neumann algebras** (Doplicher–Longo). An inclusion `A ≤ B` is
*split* when some type I factor `M` interpolates: `A ≤ M ≤ B`. The containment `A ≤ B` is not
part of the definition, since it follows (`IsSplitInclusion.le`). -/
def IsSplitInclusion (A B : VonNeumannAlgebra H) : Prop :=
  ∃ M : VonNeumannAlgebra H, IsTypeIFactor M ∧ A ≤ M ∧ M ≤ B

/-- A split inclusion is in particular an inclusion. -/
lemma IsSplitInclusion.le {A B : VonNeumannAlgebra H} (h : IsSplitInclusion A B) : A ≤ B :=
  let ⟨_, _, h₁, h₂⟩ := h
  h₁.trans h₂

/-- Splitness is preserved by shrinking the smaller algebra and enlarging the larger one. -/
lemma IsSplitInclusion.mono {A A' B B' : VonNeumannAlgebra H} (hA : A' ≤ A) (hB : B ≤ B')
    (h : IsSplitInclusion A B) : IsSplitInclusion A' B' :=
  let ⟨M, hM, h₁, h₂⟩ := h
  ⟨M, hM, hA.trans h₁, h₂.trans hB⟩

/-- Any inclusion sandwiching a type I factor is split. -/
lemma IsTypeIFactor.isSplitInclusion_of_le_of_le {M A B : VonNeumannAlgebra H}
    (hM : IsTypeIFactor M) (h₁ : A ≤ M) (h₂ : M ≤ B) : IsSplitInclusion A B :=
  ⟨M, hM, h₁, h₂⟩

/-- A type I factor splits in itself: `IsSplitInclusion M M`. Consequently the reflexive
instances of the AQFT split property (`O₁ = O₂`) require the local algebras themselves to be
type I factors. -/
lemma IsTypeIFactor.isSplitInclusion_self {M : VonNeumannAlgebra H} (hM : IsTypeIFactor M) :
    IsSplitInclusion M M :=
  hM.isSplitInclusion_of_le_of_le le_rfl le_rfl

/-- **Split tensor decomposition.** A split inclusion `A ≤ M ≤ B` is spatially tensor-split:
there is a linear isometric equivalence `U : H ≃ₗᵢ ℓ²(F) ⊗̂ (eH)` (with `e` a minimal projection
of the interpolating type I factor `M`) under which `M` becomes exactly the tensor factor
`B(ℓ²(F)) ⊗̄ 1` and `M′` the factor `1 ⊗̄ B(eH)`, so that `A` lands in the left factor and the
commutant `B′` in the right factor. This is the inclusion-form structural consequence of the
split property (Doplicher–Longo; Buchholz), inherited from
`IsFactor.exists_split_tensorDecomposition`. -/
theorem IsSplitInclusion.exists_tensorDecomposition {A B : VonNeumannAlgebra H}
    (h : IsSplitInclusion A B) :
    ∃ (M : VonNeumannAlgebra H) (e : H →L[ℂ] H) (F : Set (H →L[ℂ] H))
      (U : H ≃ₗᵢ[ℂ] HilbertTensor (lp (fun _ : F => ℂ) 2) (LinearMap.range (e : H →ₗ[ℂ] H))),
      IsMinimalProjection M e ∧ A ≤ M ∧ M ≤ B ∧
      VonNeumannAlgebra.conj U M = vnTensorLeft ∧
      VonNeumannAlgebra.conj U M′ = vnTensorRight ∧
      VonNeumannAlgebra.conj U A ≤ vnTensorLeft ∧
      VonNeumannAlgebra.conj U B′ ≤ vnTensorRight := by
  obtain ⟨M, ⟨hMf, e, he⟩, h₁, h₂⟩ := h
  obtain ⟨F, U, hM, hM', hA, hB⟩ := hMf.exists_split_tensorDecomposition he h₁ h₂
  exact ⟨M, e, F, U, he, h₁, h₂, hM, hM', hA, hB⟩

end VonNeumannAlgebra
