/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Algebra.VonNeumannAlgebra.TypeI.Basic
public import QuantumSystem.Algebra.VonNeumannAlgebra.Diagonal

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
`IsSplitInclusion.exists_tensor_decomposition`: a spatial isomorphism `U : H ≃ₗᵢ ℓ²(F) ⊗̂ (eH)`
carrying `A` into the tensor factor `𝓑(ℓ²(F)) ⊗̄ 1` and the commutant `B′` into `1 ⊗̄ 𝓑(eH)`. It
is inherited from the type I structure theorem
(`QuantumSystem.Algebra.VonNeumannAlgebra.TypeI.StructureTheorem`).

## Main definitions and results

* `VonNeumannAlgebra.IsSplitInclusion A B` — some type I factor `M` satisfies `A ≤ M ≤ B`.
* `VonNeumannAlgebra.IsSplitInclusion.le` / `mono` — a split inclusion is an inclusion, and
  splitness survives shrinking `A` and enlarging `B`.
* `VonNeumannAlgebra.IsTypeIFactor.isSplitInclusion_of_le_of_le` — any inclusion sandwiching a
  type I factor is split.
* `VonNeumannAlgebra.isSplitInclusion_self_iff` — the identity inclusion `M ≤ M` is split exactly
  when `M` is a type I factor; the two directions are
  `IsTypeIFactor.isSplitInclusion_self` and `IsSplitInclusion.isTypeIFactor_of_self`.
* `VonNeumannAlgebra.IsSplitInclusion.exists_tensor_decomposition` — the split tensor
  decomposition of the inclusion.
* `VonNeumannAlgebra.not_isSplitInclusion_diagonalAlgebra` — the negative control: the diagonal
  algebra `ℂ ⊕ ℂ = diagonalAlgebra (Fin 2)` on `ℂ²` is not a factor
  (`not_isFactor_diagonalAlgebra`), so its identity inclusion is *not* split. This is what keeps
  the predicate distinguishable from plain inclusion.

## Notation

`⊗̄` in the prose above is documentation shorthand for the von Neumann (spatial) tensor product of
algebras; that convention is stated in full in `QuantumSystem.Algebra.VonNeumannAlgebra.TensorFactor`,
where the algebras it names (`HilbertTensor.vnTensorLeft` / `vnTensorRight`) are defined.
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

/-- A type I factor splits in itself: `IsSplitInclusion M M`. -/
lemma IsTypeIFactor.isSplitInclusion_self {M : VonNeumannAlgebra H} (hM : IsTypeIFactor M) :
    IsSplitInclusion M M :=
  hM.isSplitInclusion_of_le_of_le le_rfl le_rfl

/-- **The identity inclusion splits only for type I factors.** An interpolating factor squeezed
between `M` and itself *is* `M`, by antisymmetry. This is why a reflexive proper-containment
relation would make the AQFT split property demand type I local algebras — the reason
`ProperContainment` is axiomatised to be irreflexive. -/
lemma IsSplitInclusion.isTypeIFactor_of_self {M : VonNeumannAlgebra H}
    (h : IsSplitInclusion M M) : IsTypeIFactor M :=
  let ⟨_, hN, h₁, h₂⟩ := h
  le_antisymm h₂ h₁ ▸ hN

/-- The identity inclusion `M ≤ M` is split exactly when `M` is a type I factor. -/
lemma isSplitInclusion_self_iff {M : VonNeumannAlgebra H} :
    IsSplitInclusion M M ↔ IsTypeIFactor M :=
  ⟨IsSplitInclusion.isTypeIFactor_of_self, IsTypeIFactor.isSplitInclusion_self⟩

/-- **Split tensor decomposition.** A split inclusion `A ≤ M ≤ B` is spatially tensor-split:
there is a linear isometric equivalence `U : H ≃ₗᵢ ℓ²(F) ⊗̂ (eH)` (with `e` a minimal projection
of the interpolating type I factor `M`) under which `M` becomes exactly the tensor factor
`𝓑(ℓ²(F)) ⊗̄ 1` and `M′` the factor `1 ⊗̄ 𝓑(eH)`, so that `A` lands in the left factor and the
commutant `B′` in the right factor. This is the inclusion-form structural consequence of the
split property (Doplicher–Longo; Buchholz), inherited from
`IsTypeIFactor.exists_split_tensor_decomposition`.

The interpolating factor is returned with its full type I factoriality and its minimal projection,
and the index set `F` with its nonemptiness, so that a consumer needs no reconstruction. -/
theorem IsSplitInclusion.exists_tensor_decomposition {A B : VonNeumannAlgebra H}
    (h : IsSplitInclusion A B) :
    ∃ (M : VonNeumannAlgebra H) (e : H →L[ℂ] H) (F : Set (H →L[ℂ] H))
      (U : H ≃ₗᵢ[ℂ] lp (fun _ : F => ℂ) 2 ⊗̂ LinearMap.range (e : H →ₗ[ℂ] H)),
      IsTypeIFactor M ∧ IsMinimalProjection M e ∧ Nonempty F ∧ A ≤ M ∧ M ≤ B ∧
      VonNeumannAlgebra.conj U M = vnTensorLeft ∧
      VonNeumannAlgebra.conj U M′ = vnTensorRight ∧
      VonNeumannAlgebra.conj U A ≤ vnTensorLeft ∧
      VonNeumannAlgebra.conj U B′ ≤ vnTensorRight := by
  obtain ⟨M, hMt, h₁, h₂⟩ := h
  obtain ⟨e, he, F, U, hF, hM, hM', hA, hB⟩ := hMt.exists_split_tensor_decomposition h₁ h₂
  exact ⟨M, e, F, U, hMt, he, hF, h₁, h₂, hM, hM', hA, hB⟩

/-! ### A non-split inclusion: the diagonal algebra on `ℂ²`

The negative control for `IsSplitInclusion`. Everything above inhabits the *positive* side of the
predicate; this section keeps the negations of `IsFactor`, `IsTypeIFactor` and `IsSplitInclusion`
inhabited, realizing the minimal non-split witness `ℂ⊕ℂ ⊆ ℂ⊕ℂ` (a commutative algebra is split in
itself only when it is `ℂ·1`). Without it nothing built in this repository would distinguish `IsSplitInclusion`
from plain inclusion, nor `IsFactor` from `True`.

It lives here, next to the predicate it refutes, rather than among the local-net witnesses: it
mentions no net, no index set and no representation. The algebra itself is the general diagonal
algebra `ℓ^∞(ι)` of `QuantumSystem.Algebra.VonNeumannAlgebra.Diagonal` at `ι = Fin 2`.
-/

section Diagonal

/-- **The diagonal algebra is not a factor**: the coordinate projection `P₀` lies in its centre
(`coordProjection_mem`, `coordProjection_mem_commutant`) and is not a scalar. The first refuted
`IsFactor` in the repository — without it nothing built here distinguishes `IsFactor` from `True`. -/
theorem not_isFactor_diagonalAlgebra : ¬ IsFactor (diagonalAlgebra (Fin 2)) := fun h =>
  let ⟨c, hc⟩ := h _ (coordProjection_mem 0) (coordProjection_mem_commutant 0)
  coordProjection_ne_smul_one (by decide : (0 : Fin 2) ≠ 1) c hc

/-- The diagonal algebra is not a type I factor, not being a factor at all. -/
theorem not_isTypeIFactor_diagonalAlgebra : ¬ IsTypeIFactor (diagonalAlgebra (Fin 2)) := fun h =>
  not_isFactor_diagonalAlgebra h.1

/-- **A non-split inclusion** — the minimal witness `ℂ⊕ℂ ⊆ ℂ⊕ℂ`: the identity
inclusion of the diagonal algebra on `ℂ²` is not split. An interpolating type I factor squeezed
between `diagonalAlgebra (Fin 2)` and itself would *be* `diagonalAlgebra (Fin 2)`
(`IsSplitInclusion.isTypeIFactor_of_self`), which is not a factor. This keeps the negation of
`IsSplitInclusion` inhabited: without it nothing built in the repository distinguishes the
predicate from plain inclusion. -/
theorem not_isSplitInclusion_diagonalAlgebra :
    ¬ IsSplitInclusion (diagonalAlgebra (Fin 2)) (diagonalAlgebra (Fin 2)) := fun h =>
  not_isTypeIFactor_diagonalAlgebra h.isTypeIFactor_of_self

end Diagonal

end VonNeumannAlgebra
