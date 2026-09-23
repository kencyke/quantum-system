/-
Copyright (c) 2025 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.WeakOperatorTopology

/-!
# ForMathlib: weak-operator-topology closedness of commutants

This file shows that commutants (`Set.centralizer`) and double commutants are WOT-closed, and
provides a finite-coordinate Hahn–Banach separation lemma for WOT-closed submodules. The
WOT type-copy is Mathlib's `H →WOT[ℂ] H`, with `ContinuousLinearMapWOT.ofCLM` /
`ContinuousLinearMapWOT.toCLM` as the identifications with `H →L[ℂ] H`; separate continuity of
multiplication comes from Mathlib's `IsSemitopologicalRing` instance on it.

## Main definitions

* `Set.toWOT`: view a subset of operators inside the WOT type-copy.
* `IsWOTClosed`: a predicate for subsets closed in the WOT.
* `submoduleToWOT`: transport a `Submodule` of bounded operators to the WOT type-copy.
* `inducingFnCLM`: the `inducingFn` defining the WOT, as a continuous linear map.
* `restrictPiCLM`: restrict a function `ι → ℂ` to a finite subset (as a CLM).
* `inducingFnRestrictCLM`: the finite-coordinate evaluation map for WOT.

## Main results

* `Set.toWOT_eq_image`: `Set.toWOT` is the image of the subset under `ContinuousLinearMapWOT.ofCLM`.
* `Set.toWOT_centralizer`: `Set.toWOT` commutes with taking commutants.
* `isWOTClosed_iff_isClosed_image`: WOT-closedness as closedness of the image under the canonical
  inclusion `ContinuousLinearMap.WOTofCLM`.
* `isWOTClosed_centralizer`: the commutant of any set is WOT-closed.
* `isWOTClosed_centralizer_centralizer`: double commutants are WOT-closed.
* `exists_wotCLM_sep_of_isClosed_submodule`: a finite-coordinate separation lemma for WOT-closed
  submodules.
* `exists_wotCLM_sep_of_isClosed_submodule_sum`: the separation functional as an explicit finite
  sum of coordinate projections (matrix coefficients).

## Notes

This is the "easy" half of the von Neumann double commutant theorem (double commutants are
WOT-closed). The converse implication (WOT-closed *-subalgebra equals its double commutant) is
substantially harder and is proved in `DoubleCommutant/WOTClosedSubAlgebra.lean`.
-/

@[expose] public section

namespace WeakOperatorTopology

open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

local notation "B" => (H →L[ℂ] H)
local notation "BWOT" => (H →WOT[ℂ] H)
local notation "H⋆" => StrongDual ℂ H

open ContinuousLinearMapWOT (ofCLM toCLM)

/-- View a subset of operators inside the WOT type-copy. -/
def Set.toWOT (S : Set B) : Set BWOT :=
  toCLM ⁻¹' S

lemma Set.mem_toWOT_iff {S : Set B} {T : BWOT} :
    T ∈ Set.toWOT (H := H) S ↔ toCLM T ∈ S :=
  Iff.rfl

/-- `Set.toWOT` is the image of the subset under `ContinuousLinearMapWOT.ofCLM`. -/
lemma Set.toWOT_eq_image (S : Set B) :
    Set.toWOT (H := H) S = ofCLM '' S := by
  ext T
  exact ⟨fun h => ⟨_, h, rfl⟩, by rintro ⟨x, hx, rfl⟩; exact hx⟩

/-- `Set.toWOT` commutes with taking commutants, since `ofCLM` and `toCLM` are mutually inverse
ring isomorphisms. -/
lemma Set.toWOT_centralizer (S : Set B) :
    Set.toWOT (H := H) (Set.centralizer S) = Set.centralizer (Set.toWOT (H := H) S) := by
  ext T
  simp only [Set.mem_toWOT_iff, Set.mem_centralizer_iff]
  constructor
  · intro h a ha
    exact ContinuousLinearMapWOT.toCLM_injective (by simpa using h (toCLM a) ha)
  · intro h a ha
    simpa using congrArg toCLM (h (ofCLM a) ha)

/-- A subset of operators is WOT-closed if its image in the WOT type-copy is closed. -/
def IsWOTClosed (S : Set B) : Prop :=
  IsClosed (Set.toWOT (H := H) S)

/-- WOT-closedness stated as closedness of the image under the canonical inclusion, the form in
which the weak operator topology is usually phrased. -/
lemma isWOTClosed_iff_isClosed_image (S : Set B) :
    IsWOTClosed (H := H) S ↔
      IsClosed (ContinuousLinearMap.WOTofCLM (σ := RingHom.id ℂ) (E := H) (F := H) '' S) := by
  rw [IsWOTClosed, Set.toWOT_eq_image]
  rfl

/-- The commutant `Set.centralizer S` is WOT-closed. -/
lemma isWOTClosed_centralizer (S : Set B) : IsWOTClosed (H := H) (Set.centralizer S) := by
  rw [IsWOTClosed, Set.toWOT_centralizer]
  exact Set.isClosed_centralizer _

/-- Any double commutant is WOT-closed. -/
theorem isWOTClosed_centralizer_centralizer (S : Set B) :
    IsWOTClosed (H := H) (Set.centralizer (Set.centralizer S)) :=
  isWOTClosed_centralizer (H := H) (S := Set.centralizer S)

/-- Transport a `Submodule` of bounded operators to the WOT type-copy, as the preimage under the
linear equivalence `ContinuousLinearMapWOT.linearEquiv`. Its carrier is `Set.toWOT A`.

We deliberately avoid the dot-notation name `Submodule.toWOT` because `.toWOT` is already used
elsewhere in this development for sets (`Set.toWOT`).
-/
noncomputable def submoduleToWOT (A : Submodule ℂ B) : Submodule ℂ BWOT :=
  A.comap (ContinuousLinearMapWOT.linearEquiv (σ := RingHom.id ℂ) (E := H) (F := H) ℂ).toLinearMap

@[simp]
lemma mem_submoduleToWOT_iff (A : Submodule ℂ B) (T : BWOT) :
    T ∈ submoduleToWOT (H := H) A ↔ toCLM T ∈ A :=
  Iff.rfl

lemma coe_submoduleToWOT (A : Submodule ℂ B) :
    (submoduleToWOT (H := H) A : Set BWOT) = Set.toWOT (H := H) (A : Set B) :=
  rfl

/-- The `inducingFn` defining the weak operator topology, as a continuous linear map. -/
noncomputable def inducingFnCLM : BWOT →L[ℂ] (H × H⋆ → ℂ) :=
  ⟨ContinuousLinearMapWOT.inducingFn (RingHom.id ℂ) H H,
    ContinuousLinearMapWOT.continuous_inducingFn (σ := RingHom.id ℂ) (E := H) (F := H)⟩

@[simp]
lemma inducingFnCLM_apply (T : BWOT) :
    inducingFnCLM (H := H) T = ContinuousLinearMapWOT.inducingFn (RingHom.id ℂ) H H T :=
  rfl

/-- Restrict a function `ι → ℂ` to a finite subset `I : Finset ι` (as a continuous linear map). -/
noncomputable def restrictPiCLM {ι : Type*} (I : Finset ι) : (ι → ℂ) →L[ℂ] (↥I → ℂ) := by
  classical
  refine
    ⟨{ toFun := fun f i => f i
       map_add' := by
        intro f g
        ext i
        rfl
       map_smul' := by
        intro c f
        ext i
        rfl }, ?_⟩
  refine continuous_pi ?_
  intro i
  simpa using (continuous_apply (i := (i : ι)))

/-- The finite-coordinate evaluation map `BWOT → (I → ℂ)` coming from `inducingFn`. -/
noncomputable def inducingFnRestrictCLM (I : Finset (H × H⋆)) : BWOT →L[ℂ] (↥I → ℂ) :=
  restrictPiCLM (ι := (H × H⋆)) I ∘L inducingFnCLM (H := H)

/-- A basic separation lemma: for a WOT-closed submodule `A` and `T ∉ A`,
there exists a WOT-continuous linear functional factoring through finitely many
matrix-coefficient coordinates which vanishes on `A` but not on `T`.

This is a “finite-coordinate” version of Hahn–Banach separation tailored to the WOT definition.
-/
lemma exists_wotCLM_sep_of_isClosed_submodule {A : Submodule ℂ BWOT}
    (hA : IsClosed (A : Set BWOT)) {T : BWOT} (hT : T ∉ (A : Set BWOT)) :
    ∃ I : Finset (H × H⋆), ∃ g : (↥I → ℂ) →L[ℂ] ℂ,
      let f : BWOT →L[ℂ] ℂ := g ∘L inducingFnRestrictCLM (H := H) I
      (∀ S : BWOT, S ∈ (A : Set BWOT) → f S = 0) ∧ f T ≠ 0 := by
  classical
  have hopen : IsOpen ((A : Set BWOT)ᶜ) := hA.isOpen_compl
  have hnhds : (A : Set BWOT)ᶜ ∈ 𝓝 T := hopen.mem_nhds hT
  have hind : Topology.IsInducing (ContinuousLinearMapWOT.inducingFn (RingHom.id ℂ) H H) :=
    ContinuousLinearMapWOT.isInducing_inducingFn (σ := RingHom.id ℂ) (E := H) (F := H)
  have hcomap_mem : (A : Set BWOT)ᶜ ∈
      Filter.comap (ContinuousLinearMapWOT.inducingFn (RingHom.id ℂ) H H)
        (𝓝 ((ContinuousLinearMapWOT.inducingFn (RingHom.id ℂ) H H) T)) := by
    simpa [hind.nhds_eq_comap] using hnhds
  rcases (Filter.mem_comap.1 hcomap_mem) with ⟨V, hVnhds, hVsub⟩
  have hVbasic : ∃ I : Finset (H × H⋆), ∃ t : (H × H⋆) → Set ℂ,
      (∀ i, t i ∈ 𝓝 ((ContinuousLinearMapWOT.inducingFn (RingHom.id ℂ) H H) T i)) ∧
        ((↑I : Set (H × H⋆)).pi t) ⊆ V := by
    simpa [nhds_pi, Filter.mem_pi'] using hVnhds
  rcases hVbasic with ⟨I, t, ht0, hIt⟩
  let Φ : BWOT →ₗ[ℂ] (↥I → ℂ) := (restrictPiCLM (ι := (H × H⋆)) I).toLinearMap.comp
    (ContinuousLinearMapWOT.inducingFn (RingHom.id ℂ) H H)
  let p : Submodule ℂ (↥I → ℂ) := A.map Φ
  have hnot : Φ T ∉ (p : Set (↥I → ℂ)) := by
    intro hmem
    rcases (Submodule.mem_map).1 hmem with ⟨S, hSA, hST⟩
    have hSIn : (ContinuousLinearMapWOT.inducingFn (RingHom.id ℂ) H H) S ∈
        ((↑I : Set (H × H⋆)).pi t) := by
      change
        ∀ i, i ∈ (↑I : Set (H × H⋆)) →
          (ContinuousLinearMapWOT.inducingFn (RingHom.id ℂ) H H) S i ∈ t i
      intro i hi
      have : (ContinuousLinearMapWOT.inducingFn (RingHom.id ℂ) H H) S i =
          (ContinuousLinearMapWOT.inducingFn (RingHom.id ℂ) H H) T i := by
        have := congrArg (fun f => f ⟨i, hi⟩) hST
        simpa [Φ, restrictPiCLM] using this
      have ht : t i ∈ 𝓝 ((ContinuousLinearMapWOT.inducingFn (RingHom.id ℂ) H H) T i) := ht0 i
      exact mem_of_mem_nhds (by simpa [this] using ht)
    have hSInV : (ContinuousLinearMapWOT.inducingFn (RingHom.id ℂ) H H) S ∈ V := hIt hSIn
    have hSInCompl : S ∈ (A : Set BWOT)ᶜ := by
      have : S ∈ (ContinuousLinearMapWOT.inducingFn (RingHom.id ℂ) H H) ⁻¹' V := hSInV
      exact hVsub this
    exact hSInCompl (show S ∈ (A : Set BWOT) from hSA)
  obtain ⟨g, hgT, hgmap⟩ :=
    (Submodule.exists_dual_map_eq_bot_of_notMem (p := p) (x := Φ T) hnot (by infer_instance))
  have _hfd : FiniteDimensional ℂ (↥I → ℂ) := by infer_instance
  let gCLM : (↥I → ℂ) →L[ℂ] ℂ :=
    ⟨g, LinearMap.continuous_of_finiteDimensional g⟩
  refine ⟨I, gCLM, ?_⟩
  dsimp
  refine And.intro ?_ ?_
  · intro S hSA
    have : Φ S ∈ (p : Set (↥I → ℂ)) := by
      exact (Submodule.mem_map).2 ⟨S, hSA, rfl⟩
    have hgzero : ∀ z : (↥I → ℂ), z ∈ (p : Set (↥I → ℂ)) → g z = 0 := by
      intro z hz
      have : g z ∈ (p.map g : Submodule ℂ ℂ) := by
        exact (Submodule.mem_map).2 ⟨z, hz, rfl⟩
      simpa [hgmap] using this
    have : g (Φ S) = 0 := hgzero (Φ S) this
    simpa [gCLM, inducingFnRestrictCLM, Φ] using this
  · intro hf0
    have : g (Φ T) = 0 := by
      have : (gCLM ∘L inducingFnRestrictCLM (H := H) I) T = 0 := hf0
      simpa [gCLM, inducingFnRestrictCLM, Φ] using this
    exact hgT this


/-- Explicit finite-sum form of the finite-coordinate WOT separation lemma.

This refines `exists_wotCLM_sep_of_isClosed_submodule` by expanding the intermediate functional
`g : (I → ℂ) →L[ℂ] ℂ` in coordinates. Concretely, for a WOT-closed submodule `A` and `T ∉ A`, it
produces a finite index set `I : Finset (H × H⋆)` and coefficients `coeff : I → ℂ` such that the
separating functional

`f = ∑ i : I, coeff i • (proj i) ∘ inducingFnRestrictCLM I`

vanishes on `A` but satisfies `f T ≠ 0`.

In the intended application, the coordinates of `inducingFnRestrictCLM` are matrix coefficients
`(x, y) ↦ y (T x)` defining basic WOT functionals.
-/
lemma exists_wotCLM_sep_of_isClosed_submodule_sum {A : Submodule ℂ BWOT}
    (hA : IsClosed (A : Set BWOT)) {T : BWOT} (hT : T ∉ (A : Set BWOT)) :
    ∃ I : Finset (H × H⋆),
      ∃ coeff : (↥I → ℂ),
        let f : BWOT →L[ℂ] ℂ :=
          ∑ i : ↥I, (coeff i) • (ContinuousLinearMap.proj i ∘L inducingFnRestrictCLM (H := H) I)
        (∀ S : BWOT, S ∈ (A : Set BWOT) → f S = 0) ∧ f T ≠ 0 := by
  classical
  rcases exists_wotCLM_sep_of_isClosed_submodule (H := H) (A := A) hA (T := T) hT with
    ⟨I, g, hg⟩
  let coeff : ↥I → ℂ := fun i => g (fun j => if i = j then (1 : ℂ) else 0)
  have hg_sum : ∀ z : (↥I → ℂ), g z = ∑ i : ↥I, z i • coeff i := by
    intro z
    simpa [coeff] using (LinearMap.pi_apply_eq_sum_univ (R := ℂ)
      (f := (g : (↥I → ℂ) →L[ℂ] ℂ).toLinearMap) (x := z))
  refine ⟨I, coeff, ?_⟩
  have hvan : ∀ S : BWOT, S ∈ (A : Set BWOT) →
      (∑ i : ↥I,
        (coeff i) • (inducingFnRestrictCLM (H := H) I S i)) = 0 := by
    intro S hSA
    have := (hg.1 S hSA)
    simpa [hg_sum, mul_comm, mul_left_comm, mul_assoc] using this
  have hneq : (∑ i : ↥I, (inducingFnRestrictCLM (H := H) I T i) • coeff i) ≠ 0 := by
    intro h0
    have : (g ∘L inducingFnRestrictCLM (H := H) I) T = 0 := by
      simpa [hg_sum] using h0
    exact hg.2 this
  refine And.intro ?_ ?_
  · intro S hSA
    have : (∑ i : ↥I, (coeff i) • (inducingFnRestrictCLM (H := H) I S i)) = 0 := hvan S hSA
    simpa [sum_apply, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, this]
  · intro hf
    have : (∑ i : ↥I, (coeff i) • (inducingFnRestrictCLM (H := H) I T i)) = 0 := by
      simpa [sum_apply, smul_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] using hf
    exact hneq (by simpa [mul_comm, mul_left_comm, mul_assoc, Algebra.smul_mul_assoc] using this)

end WeakOperatorTopology
