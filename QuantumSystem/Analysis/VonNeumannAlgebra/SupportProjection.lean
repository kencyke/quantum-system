/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import QuantumSystem.Analysis.VonNeumannAlgebra.MurrayVonNeumann
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.InvariantSubspace
public import QuantumSystem.ForMathlib.Analysis.VonNeumannAlgebra.Commutant

/-!
# Support projections of vectors

For a von Neumann algebra `M` on `H` and a vector `ξ`, the **support** of `ξ` in `M` is the
orthogonal projection `s(ξ)` onto the closed subspace `[M′ ξ]` generated from `ξ` by the commutant
(`InnerProductSpace.cyclicSubspace`). It lies in `M`, and it is the smallest projection of `M`
fixing `ξ`: for a projection `e ∈ M`, `s(ξ) ≤ e ↔ e ξ = ξ`. Equivalently, it is the support of the
vector functional `ω_ξ = ⟪ξ, (·) ξ⟫` on `M`, the smallest projection `e ∈ M` with
`ω_ξ (1 - e) = 0` (`VonNeumannAlgebra.supportProj_le_iff_inner_eq_zero`); in particular it depends
only on `ω_ξ`.

Conversely, if two vectors `ξ, η` induce the same vector functional on `M`,
`⟪ξ, x ξ⟫ = ⟪η, x η⟫` for all `x ∈ M`, then `x ξ ↦ x η` extends to a partial isometry `v′` of the
commutant `M′` with source projection `P_{[M ξ]}` and range projection `P_{[M η]}`, and
`η = v′ ξ`. This is the statement that a vector representative of a functional on `M` is unique up
to a partial isometry of `M′`. The partial isometry is the extension of the isometric
correspondence `x ξ ↦ x η` given by `exists_isPartialIsometry_mem_centralizer_of_norm_eq`, the
lemma that also produces the partial isometry of the polar decomposition.

## Main definitions

* `VonNeumannAlgebra.supportProj M ξ` — the support projection `s(ξ) = P_{[M′ ξ]}`.

## Main results

* `VonNeumannAlgebra.coe_cyclicSubspace` — for a von Neumann algebra, `[M ξ]` is the closure of
  the orbit `{x ξ | x ∈ M}`.
* `VonNeumannAlgebra.supportProj_mem` — `s(ξ) ∈ M`; `VonNeumannAlgebra.supportProj_apply_self` —
  `s(ξ) ξ = ξ`; `VonNeumannAlgebra.supportProj_commutant` — the support in `M′` is `P_{[M ξ]}`.
* `VonNeumannAlgebra.mul_supportProj_eq_zero_iff`, `VonNeumannAlgebra.supportProj_mul_eq_zero_iff`
  — for `x ∈ M`, `x s(ξ) = 0 ↔ x ξ = 0` and `s(ξ) x = 0 ↔ x⋆ ξ = 0`.
* `VonNeumannAlgebra.supportProj_le_iff`, `VonNeumannAlgebra.supportProj_le_iff_inner_eq_zero` —
  for a projection `e ∈ M`, `s(ξ) ≤ e ↔ e ξ = ξ ↔ ω_ξ (1 - e) = 0`.
* `VonNeumannAlgebra.supportProj_eq_of_inner_eq` — vectors with the same vector functional on `M`
  have the same support; `VonNeumannAlgebra.supportProj_apply_of_mem_commutant` — hence
  `s(v′ ξ) = s(ξ)` for `v′ ∈ M′` with `v′⋆ v′ ξ = ξ`.
* `VonNeumannAlgebra.supportProj_zero`, `VonNeumannAlgebra.supportProj_smul`,
  `VonNeumannAlgebra.supportProj_eq_one_iff` — `s(0) = 0`, `s(c ξ) = s(ξ)` for `c ≠ 0`, and
  `s(ξ) = 1` iff `ξ` is cyclic for `M′`.
* `VonNeumannAlgebra.commute_supportProj_supportProj_commutant` — `s(ξ)` commutes with the support
  `s′(η)` in `M′` of any vector.
* `VonNeumannAlgebra.inner_apply_eq_of_inner_eq`, `VonNeumannAlgebra.norm_apply_eq_of_inner_eq` —
  equal vector functionals give `⟪x η, y η⟫ = ⟪x ξ, y ξ⟫` and `‖x η‖ = ‖x ξ‖` on `M`.
* `VonNeumannAlgebra.exists_isPartialIsometry_mem_commutant_of_inner_eq` — the partial isometry
  `v′ ∈ M′` with `v′ ξ = η`, `v′⋆ v′ = s′(ξ)` and `v′ v′⋆ = s′(η)`, where `s′` is the support in
  `M′`, i.e. the projection onto `[M ξ]` (`VonNeumannAlgebra.supportProj_commutant`).
* `VonNeumannAlgebra.supportProj_commutant_mvNEquiv_of_inner_eq` — hence `s′(ξ) ∼ s′(η)` in `M′`.

The two-representation form of the uniqueness statement (vectors of two representations with the
same vector functional) is not formalised; only vectors of one Hilbert space are compared here.
-/

@[expose] public section

open scoped InnerProductSpace VonNeumannAlgebra
open InnerProductSpace (cyclicSubspace)

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (M : VonNeumannAlgebra H)

/-- The **support projection** `s(ξ)` of `ξ` in `M`: the orthogonal projection onto `[M′ ξ]`. -/
noncomputable def supportProj (ξ : H) : H →L[ℂ] H :=
  (cyclicSubspace M′ ξ).toSubmodule.starProjection

variable {M} {ξ v : H} {x : H →L[ℂ] H}

variable (M ξ) in
/-- For a von Neumann algebra, `[M ξ]` is the closure of the orbit `{x ξ | x ∈ M}`. -/
lemma coe_cyclicSubspace :
    (cyclicSubspace M ξ : Set H) =
      closure (Set.range fun x : M => (x : H →L[ℂ] H) ξ) :=
  InnerProductSpace.coe_cyclicSubspace_of_submodule M.toSubalgebra.toSubmodule ξ

variable (M ξ) in
/-- `ξ ∈ [M ξ]`, since `1 ∈ M`. -/
lemma self_mem_cyclicSubspace : ξ ∈ cyclicSubspace M ξ := by
  simpa using InnerProductSpace.apply_mem_cyclicSubspace ξ (one_mem M)

/-- `[M ξ]` is invariant under `M`. -/
lemma apply_mem_cyclicSubspace (hx : x ∈ M) (hv : v ∈ cyclicSubspace M ξ) :
    x v ∈ cyclicSubspace M ξ :=
  InnerProductSpace.apply_mem_cyclicSubspace_of_mem M.toSubalgebra.toNonUnitalSubalgebra hx hv

/-- Operators of `M′` commute with those of `M`: `w (y z) = y (w z)` for `w ∈ M′`, `y ∈ M`. -/
lemma apply_apply_of_mem_commutant {w y : H →L[ℂ] H} (hw : w ∈ M′) (hy : y ∈ M) (z : H) :
    w (y z) = y (w z) := by
  rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, mem_commutant_iff.mp hw y hy]

/-- A closed set containing the orbit `{x ξ | x ∈ M}` contains `[M ξ]`. -/
lemma cyclicSubspace_subset {s : Set H} (hs : IsClosed s) (h : ∀ x ∈ M, x ξ ∈ s) :
    (cyclicSubspace M ξ : Set H) ⊆ s :=
  InnerProductSpace.cyclicSubspace_subset_of_submodule M.toSubalgebra.toSubmodule hs h

variable (M) in
/-- `x ↦ x ζ` on `M`, as a linear map. -/
def applyₗ (ζ : H) : M →ₗ[ℂ] H where
  toFun x := (x : H →L[ℂ] H) ζ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `applyₗ M ζ x = x ζ`. -/
@[simp] lemma applyₗ_apply (ζ : H) (x : M) : M.applyₗ ζ x = (x : H →L[ℂ] H) ζ := rfl

variable (M ξ)

/-- The support projection is a star projection. -/
lemma isStarProjection_supportProj : IsStarProjection (M.supportProj ξ) :=
  isStarProjection_starProjection

/-- The support projection of `ξ` in the commutant is the projection onto `[M ξ]`. -/
lemma supportProj_commutant :
    M′.supportProj ξ = (cyclicSubspace M ξ).toSubmodule.starProjection := by
  simp only [supportProj, commutant_commutant]

/-- The support projection `s(ξ)` lies in `M`: its range `[M′ ξ]` is invariant under `M′`. -/
lemma supportProj_mem : M.supportProj ξ ∈ M := by
  rw [IsStarProjection.mem_iff (M.isStarProjection_supportProj ξ)]
  intro y hy
  rw [supportProj, Submodule.range_starProjection,
    Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
  exact fun v hv => apply_mem_cyclicSubspace hy hv

/-- `s(ξ) ξ = ξ`. -/
@[simp]
lemma supportProj_apply_self : M.supportProj ξ ξ = ξ :=
  Submodule.starProjection_eq_self_iff.mpr (self_mem_cyclicSubspace M′ ξ)

variable {M ξ}

/-- For `x ∈ M`, `x s(ξ) = 0 ↔ x ξ = 0`: `x` annihilates `[M′ ξ]` as soon as it annihilates `ξ`,
since it commutes with `M′`. -/
lemma mul_supportProj_eq_zero_iff (hx : x ∈ M) : x * M.supportProj ξ = 0 ↔ x ξ = 0 := by
  refine ⟨fun h => by simpa using congr($h ξ), fun h => ?_⟩
  have hK : (cyclicSubspace M′ ξ : Set H) ⊆ {v | x v = 0} :=
    cyclicSubspace_subset (isClosed_eq x.continuous continuous_const) fun y hy => by
      change x (y ξ) = 0
      rw [← mul_apply_eq_comp, mem_commutant_iff.mp hy x hx, mul_apply_eq_comp, h, map_zero]
  ext w
  exact hK (Submodule.starProjection_apply_mem _ w)

/-- For `x ∈ M`, `s(ξ) x = 0 ↔ x⋆ ξ = 0`: the adjoint form of
`VonNeumannAlgebra.mul_supportProj_eq_zero_iff`. -/
lemma supportProj_mul_eq_zero_iff (hx : x ∈ M) : M.supportProj ξ * x = 0 ↔ star x ξ = 0 := by
  rw [← mul_supportProj_eq_zero_iff (star_mem hx), ← star_eq_zero, star_mul,
    (M.isStarProjection_supportProj ξ).isSelfAdjoint.star_eq]

/-- The support projection is the smallest projection of `M` fixing `ξ`: for a star projection
`e ∈ M`, `s(ξ) ≤ e ↔ e ξ = ξ`. -/
lemma supportProj_le_iff {e : H →L[ℂ] H} (he : IsStarProjection e) (heM : e ∈ M) :
    M.supportProj ξ ≤ e ↔ e ξ = ξ := by
  obtain ⟨_, he'⟩ := isStarProjection_iff_eq_starProjection_range.mp he
  have hfix : ∀ {v}, v ∈ e.range ↔ e v = v := fun {v} =>
    ⟨fun ⟨w, hw⟩ => by
      rw [← hw]
      change e (e w) = e w
      rw [← mul_apply_eq_comp, he.isIdempotentElem.eq],
      fun hv => ⟨v, hv⟩⟩
  conv_lhs => rw [he', supportProj]
  rw [Submodule.starProjection_le_starProjection_iff]
  refine ⟨fun h => hfix.mp (h (self_mem_cyclicSubspace M′ ξ)), fun h v hv => hfix.mpr ?_⟩
  refine cyclicSubspace_subset (s := {v | e v = v})
    (isClosed_eq e.continuous continuous_id) (fun y hy => ?_) hv
  change e (y ξ) = y ξ
  rw [← mul_apply_eq_comp, mem_commutant_iff.mp hy e heM, mul_apply_eq_comp, h]

/-- For a star projection `e`, `e ξ = ξ` iff `⟪ξ, (1 - e) ξ⟫ = 0`, since
`⟪ξ, (1 - e) ξ⟫ = ‖(1 - e) ξ‖²`. -/
private lemma apply_eq_self_iff_inner_eq_zero {e : H →L[ℂ] H} (he : IsStarProjection e) :
    e ξ = ξ ↔ ⟪ξ, (1 - e) ξ⟫_ℂ = 0 := by
  have hq : IsStarProjection (1 - e) := he.one_sub
  have : ⟪(1 - e) ξ, (1 - e) ξ⟫_ℂ = ⟪ξ, (1 - e) ξ⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
      hq.isSelfAdjoint.star_eq, ← mul_apply_eq_comp, hq.isIdempotentElem.eq]
  rw [← this, inner_self_eq_zero, sub_apply, one_apply_eq_self, sub_eq_zero, eq_comm]

/-- The support projection is the support of the vector functional `ω_ξ = ⟪ξ, (·) ξ⟫`: for a star
projection `e ∈ M`, `s(ξ) ≤ e ↔ ω_ξ (1 - e) = 0`. -/
lemma supportProj_le_iff_inner_eq_zero {e : H →L[ℂ] H} (he : IsStarProjection e)
    (heM : e ∈ M) : M.supportProj ξ ≤ e ↔ ⟪ξ, (1 - e) ξ⟫_ℂ = 0 := by
  rw [supportProj_le_iff he heM, apply_eq_self_iff_inner_eq_zero he]

/-- **The support depends only on the vector functional.** If `⟪ξ, x ξ⟫ = ⟪η, x η⟫` for all
`x ∈ M`, then `s(ξ) = s(η)`. -/
theorem supportProj_eq_of_inner_eq {η : H} (h : ∀ x ∈ M, ⟪ξ, x ξ⟫_ℂ = ⟪η, x η⟫_ℂ) :
    M.supportProj ξ = M.supportProj η := by
  have key : ∀ {a b : H}, (∀ x ∈ M, ⟪a, x a⟫_ℂ = ⟪b, x b⟫_ℂ) →
      M.supportProj b ≤ M.supportProj a := fun {a b} hab => by
    have hs := M.isStarProjection_supportProj a
    rw [supportProj_le_iff_inner_eq_zero hs (M.supportProj_mem a),
      ← hab _ (sub_mem (one_mem M) (M.supportProj_mem a)), ← apply_eq_self_iff_inner_eq_zero hs,
      supportProj_apply_self]
  exact le_antisymm (key fun x hx => (h x hx).symm) (key h)

/-- A vector `v′ ξ` with `v′ ∈ M′` and `v′⋆ v′ ξ = ξ` has the same vector functional on `M` as
`ξ`: `⟪v′ ξ, x v′ ξ⟫ = ⟪ξ, x ξ⟫`. -/
lemma inner_apply_eq_of_mem_commutant {w : H →L[ℂ] H} (hw : w ∈ M′)
    (hwξ : star w (w ξ) = ξ) (hx : x ∈ M) : ⟪w ξ, x (w ξ)⟫_ℂ = ⟪ξ, x ξ⟫_ℂ := by
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
    ← mul_apply_eq_comp x w, ← mul_apply_eq_comp (star w), ← mul_assoc,
    ← mem_commutant_iff.mp (star_mem hw) x hx, mul_assoc, mul_apply_eq_comp, mul_apply_eq_comp,
    hwξ]

/-- For `v′ ∈ M′` with `v′⋆ v′ ξ = ξ` (for instance `ξ` in the source space of a partial
isometry `v′`), `s(v′ ξ) = s(ξ)`. -/
lemma supportProj_apply_of_mem_commutant {w : H →L[ℂ] H} (hw : w ∈ M′)
    (hwξ : star w (w ξ) = ξ) : M.supportProj (w ξ) = M.supportProj ξ :=
  supportProj_eq_of_inner_eq fun _ hx => inner_apply_eq_of_mem_commutant hw hwξ hx

variable (M) in
/-- `s(0) = 0`. -/
@[simp]
lemma supportProj_zero : M.supportProj 0 = 0 :=
  le_antisymm ((supportProj_le_iff (IsStarProjection.zero _) (zero_mem M)).mpr (map_zero _))
    (ContinuousLinearMap.nonneg_iff_isPositive.mpr
      (.of_isStarProjection (M.isStarProjection_supportProj 0)))

/-- `s(c ξ) = s(ξ)` for `c ≠ 0`. -/
lemma supportProj_smul {c : ℂ} (hc : c ≠ 0) : M.supportProj (c • ξ) = M.supportProj ξ := by
  refine le_antisymm ?_ ?_
  · rw [supportProj_le_iff (M.isStarProjection_supportProj ξ) (M.supportProj_mem ξ), map_smul,
      supportProj_apply_self]
  · rw [supportProj_le_iff (M.isStarProjection_supportProj _) (M.supportProj_mem _)]
    have := M.supportProj_apply_self (c • ξ)
    rw [map_smul] at this
    exact smul_right_injective H hc this

/-- `s(ξ) = 1` iff `ξ` is cyclic for the commutant, `[M′ ξ] = H`. -/
lemma supportProj_eq_one_iff :
    M.supportProj ξ = 1 ↔ InnerProductSpace.IsCyclicVector M′ ξ := by
  rw [supportProj, ← Submodule.starProjection_top', Submodule.starProjection_inj,
    ← ClosedSubmodule.toSubmodule_top, ClosedSubmodule.toSubmodule_injective.eq_iff]
  exact InnerProductSpace.isCyclicVector_iff.symm

variable (M) in
/-- The support `s(ξ) ∈ M` commutes with the support `s′(η) ∈ M′` of any vector `η` in the
commutant. -/
lemma commute_supportProj_supportProj_commutant (ξ η : H) :
    Commute (M.supportProj ξ) (M′.supportProj η) :=
  mem_commutant_iff.mp (M′.supportProj_mem η) _ (M.supportProj_mem ξ)

/-! ### Vectors with the same vector functional -/

section SameVectorFunctional

variable {η : H}

/-- For vectors with the same vector functional on `M`, `⟪x η, y η⟫ = ⟪x ξ, y ξ⟫` on `M`. -/
lemma inner_apply_eq_of_inner_eq (h : ∀ x ∈ M, ⟪ξ, x ξ⟫_ℂ = ⟪η, x η⟫_ℂ) {x y : H →L[ℂ] H}
    (hx : x ∈ M) (hy : y ∈ M) : ⟪x η, y η⟫_ℂ = ⟪x ξ, y ξ⟫_ℂ := by
  simp only [← ContinuousLinearMap.adjoint_inner_right, ← mul_apply_eq_comp,
    ← ContinuousLinearMap.star_eq_adjoint]
  exact (h _ (mul_mem (star_mem hx) hy)).symm

/-- For vectors with the same vector functional on `M`, `‖x η‖ = ‖x ξ‖` on `M`. -/
lemma norm_apply_eq_of_inner_eq (h : ∀ x ∈ M, ⟪ξ, x ξ⟫_ℂ = ⟪η, x η⟫_ℂ) {x : H →L[ℂ] H}
    (hx : x ∈ M) : ‖x η‖ = ‖x ξ‖ := by
  have := inner_apply_eq_of_inner_eq h hx hx
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at this
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by exact_mod_cast this)

/-- `[M ζ]` is the closure of the range of `x ↦ x ζ` on `M`: `coe_cyclicSubspace` restated as an
equality of submodules, the form in which the partial isometry lemma reports its projections. -/
private lemma topologicalClosure_range_applyₗ (ζ : H) :
    (LinearMap.range (M.applyₗ ζ)).topologicalClosure = (cyclicSubspace M ζ).toSubmodule :=
  SetLike.coe_injective <| by
    rw [Submodule.topologicalClosure_coe, LinearMap.coe_range]
    exact (coe_cyclicSubspace M ζ).symm

/-- **Uniqueness of vector representatives.** If `⟪ξ, x ξ⟫ = ⟪η, x η⟫` for all `x ∈ M`, there is a
partial isometry `v′ ∈ M′` with `v′ ξ = η`, source projection `v′⋆ v′ = s′(ξ) = P_{[M ξ]}` and
range projection `v′ v′⋆ = s′(η) = P_{[M η]}`. It extends the isometric correspondence
`x ξ ↦ x η` on `M` (`exists_isPartialIsometry_mem_centralizer_of_norm_eq`), which every `a ∈ M`
intertwines: `a (x ξ) = (a x) ξ`. -/
theorem exists_isPartialIsometry_mem_commutant_of_inner_eq
    (h : ∀ x ∈ M, ⟪ξ, x ξ⟫_ℂ = ⟪η, x η⟫_ℂ) :
    ∃ v ∈ M′, IsPartialIsometry v ∧ v ξ = η ∧ star v * v = M′.supportProj ξ ∧
      v * star v = M′.supportProj η := by
  obtain ⟨v, hvM, hv, hvx, hsrc, hrng⟩ := exists_isPartialIsometry_mem_centralizer_of_norm_eq
    (M.applyₗ ξ) (M.applyₗ η) (fun x => (norm_apply_eq_of_inner_eq h x.2).symm)
    (S := (M : Set (H →L[ℂ] H))) (fun _ ha => star_mem (s := M) ha)
    fun a ha x => ⟨⟨a * x, mul_mem ha x.2⟩, rfl, rfl⟩
  refine ⟨v, mem_commutant_iff.mpr hvM, hv, by simpa using hvx 1, ?_, ?_⟩
  · simp only [supportProj_commutant, hsrc, topologicalClosure_range_applyₗ]
  · simp only [supportProj_commutant, hrng, topologicalClosure_range_applyₗ]

/-- Vectors with the same vector functional on `M` have Murray–von Neumann equivalent supports in
the commutant: `s′(ξ) ∼ s′(η)` in `M′`. -/
lemma supportProj_commutant_mvNEquiv_of_inner_eq (h : ∀ x ∈ M, ⟪ξ, x ξ⟫_ℂ = ⟪η, x η⟫_ℂ) :
    M′.supportProj ξ ∼[M′] M′.supportProj η :=
  let ⟨v, hv, hpi, _, h₁, h₂⟩ := exists_isPartialIsometry_mem_commutant_of_inner_eq h
  ⟨v, hv, hpi, h₁, h₂⟩

end SameVectorFunctional

end VonNeumannAlgebra
