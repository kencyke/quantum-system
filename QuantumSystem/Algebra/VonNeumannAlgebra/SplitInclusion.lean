module

public import QuantumSystem.Algebra.VonNeumannAlgebra.TypeI
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2

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
(`QuantumSystem.Algebra.VonNeumannAlgebra.StructureTheorem`).

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
* `VonNeumannAlgebra.diagonalAlgebra` and `VonNeumannAlgebra.not_isSplitInclusion_diagonalAlgebra`
  — the negative control: the diagonal algebra `ℂ ⊕ ℂ` on `ℂ²` is not a factor
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
`IsFactor.exists_split_tensor_decomposition`.

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
  obtain ⟨hMf, e, he⟩ := hMt
  obtain ⟨F, U, hF, hM, hM', hA, hB⟩ := hMf.exists_split_tensor_decomposition he h₁ h₂
  exact ⟨M, e, F, U, ⟨hMf, e, he⟩, he, hF, h₁, h₂, hM, hM', hA, hB⟩

/-! ### A non-split inclusion: the diagonal algebra on `ℂ²`

The negative control for `IsSplitInclusion`. Everything above inhabits the *positive* side of the
predicate; this section keeps the negations of `IsFactor`, `IsTypeIFactor` and `IsSplitInclusion`
inhabited, realizing the minimal non-split witness `ℂ⊕ℂ ⊆ ℂ⊕ℂ` of the extraction note
`docs/math/split-inclusion.md` (degeneracy table: a commutative algebra is split in itself only
when it is `ℂ·1`). Without it nothing built in this repository would distinguish `IsSplitInclusion`
from plain inclusion, nor `IsFactor` from `True`.

It lives here, next to the predicate it refutes, rather than among the local-net witnesses: it
mentions no net, no index set and no representation.
-/

section Diagonal

open InnerProductSpace

/-- The rank-one projection `|e₀⟩⟨e₀|` onto the first coordinate of `ℂ²`: self-adjoint
(`star_diagonalProjection`) and not a scalar (`diagonalProjection_ne_smul_one`), it generates
the diagonal algebra below and witnesses its nontrivial centre. -/
noncomputable def diagonalProjection :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  rankOne ℂ (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1)

/-- The **diagonal algebra** `ℂ ⊕ ℂ` on `ℂ²`: the commutant of the rank-one projection onto the
first coordinate — concretely, the operators diagonal in the standard basis. The smallest
von Neumann algebra in the repository that is a counterexample rather than a witness. -/
noncomputable def diagonalAlgebra : VonNeumannAlgebra (EuclideanSpace ℂ (Fin 2)) :=
  commutantSet {diagonalProjection}

/-- The rank-one projection onto a coordinate is self-adjoint. -/
lemma star_diagonalProjection : star diagonalProjection = diagonalProjection := by
  rw [diagonalProjection, ContinuousLinearMap.star_eq_adjoint, adjoint_rankOne]

/-- The generating projection acts as `v ↦ v₀ • e₀`. -/
lemma diagonalProjection_apply (v : EuclideanSpace ℂ (Fin 2)) :
    diagonalProjection v = v 0 • EuclideanSpace.single 0 1 := by
  rw [diagonalProjection, rankOne_apply, EuclideanSpace.inner_single_left, map_one, one_mul]

/-- The generating projection lies in the diagonal algebra: it commutes with itself and, being
self-adjoint, with its own adjoint. -/
lemma diagonalProjection_mem : diagonalProjection ∈ diagonalAlgebra := by
  rw [diagonalAlgebra, mem_commutantSet_iff]
  rintro g rfl
  exact ⟨rfl, by rw [star_diagonalProjection]⟩

/-- The generating projection lies in the commutant of the diagonal algebra: every member of the
commutant of `{diagonalProjection}` commutes with it by definition. -/
lemma diagonalProjection_mem_commutant : diagonalProjection ∈ diagonalAlgebra.commutant := by
  rw [mem_commutant_iff]
  intro g hg
  rw [diagonalAlgebra, mem_commutantSet_iff] at hg
  exact (hg diagonalProjection rfl).1.symm

/-- The generating projection is not a scalar: it fixes `e₀` and kills `e₁`, so `c • 1` would
force `c = 1` and `c = 0` at once. This is the nontrivial centre of the diagonal algebra. -/
lemma diagonalProjection_ne_smul_one (c : ℂ) : diagonalProjection ≠ c • 1 := by
  intro h
  have h0 : diagonalProjection (EuclideanSpace.single 0 1) 0 = c := by
    rw [h]
    simp
  have h1 : diagonalProjection (EuclideanSpace.single 1 1) 1 = c := by
    rw [h]
    simp
  rw [diagonalProjection_apply] at h0 h1
  simp at h0 h1
  exact one_ne_zero (h0.trans h1.symm)

/-- **The diagonal algebra is not a factor**: its generating projection lies in its centre and is
not a scalar. The first refuted `IsFactor` in the repository — without it nothing built here
distinguishes `IsFactor` from `True`. -/
theorem not_isFactor_diagonalAlgebra : ¬ IsFactor diagonalAlgebra := fun h =>
  let ⟨c, hc⟩ := h diagonalProjection diagonalProjection_mem diagonalProjection_mem_commutant
  diagonalProjection_ne_smul_one c hc

/-- The diagonal algebra is not a type I factor, not being a factor at all. -/
theorem not_isTypeIFactor_diagonalAlgebra : ¬ IsTypeIFactor diagonalAlgebra := fun h =>
  not_isFactor_diagonalAlgebra h.1

/-- **A non-split inclusion** — the extraction note's minimal witness `ℂ⊕ℂ ⊆ ℂ⊕ℂ`: the identity
inclusion of the diagonal algebra on `ℂ²` is not split. An interpolating type I factor squeezed
between `diagonalAlgebra` and itself would *be* `diagonalAlgebra`
(`IsSplitInclusion.isTypeIFactor_of_self`), which is not a factor. This keeps the negation of
`IsSplitInclusion` inhabited: without it nothing built in the repository distinguishes the
predicate from plain inclusion. -/
theorem not_isSplitInclusion_diagonalAlgebra :
    ¬ IsSplitInclusion diagonalAlgebra diagonalAlgebra := fun h =>
  not_isTypeIFactor_diagonalAlgebra h.isTypeIFactor_of_self

end Diagonal

end VonNeumannAlgebra
