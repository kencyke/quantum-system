/-
Copyright (c) 2025 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.WeakOperatorTopology

import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# ForMathlib: weak-operator-topology closedness of commutants

This file shows that commutants (`Set.centralizer`) and double commutants are WOT-closed, and
provides a finite-coordinate Hahn–Banach separation lemma for WOT-closed submodules. The
WOT type-copy is Mathlib's `H →WOT[𝕜] H`, for a normed space `H` over `𝕜 = ℝ` or `ℂ`, with
`ContinuousLinearMapWOT.ofCLM` / `ContinuousLinearMapWOT.toCLM` as the identifications with
`H →L[𝕜] H`; separate continuity of
multiplication comes from Mathlib's `IsSemitopologicalRing` instance on it. A set `S` of operators
is carried into the type-copy as its image `ContinuousLinearMapWOT.ofCLM '' S`, and a submodule as
its `Submodule.map` along the inverse of `ContinuousLinearMapWOT.linearEquiv`; every result about
WOT-closedness and WOT-closures is stated in this image form.

## Main definitions

* `IsWOTClosed`: a set `S` of operators on a normed space is WOT-closed if
  `ContinuousLinearMapWOT.ofCLM '' S` is closed.
* `inducingFnCLM`: the `inducingFn` defining the WOT, as a continuous linear map.
* `inducingFnRestrictCLM`: the finite-coordinate evaluation map for WOT.

## Main results

* `isWOTClosed_centralizer`: the commutant of any set is WOT-closed.
* `isWOTClosed_centralizer_centralizer`: double commutants are WOT-closed.
* `exists_wotCLM_sep_of_isClosed_submodule`: a finite-coordinate separation lemma for WOT-closed
  submodules.
* `exists_wotCLM_sep_of_isClosed_submodule_sum`: the separation functional as an explicit finite
  sum of coordinate projections (matrix coefficients).

## Notes

This is the "easy" half of the von Neumann double commutant theorem (double commutants are
WOT-closed). The converse implication (WOT-closed *-subalgebra equals its double commutant) is
substantially harder and is proved in `DoubleCommutant/WOTClosedSubalgebra.lean`.
-/

@[expose] public section

namespace WeakOperatorTopology

open scoped Topology

open ContinuousLinearMapWOT (ofCLM)

section IsWOTClosed

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- A set `S` of operators on `H` is WOT-closed if its image `ofCLM '' S` in the WOT type-copy is
closed. It is a reducible abbreviation of that closedness, the one spelling of WOT-closedness. -/
abbrev IsWOTClosed (S : Set (H →L[𝕜] H)) : Prop :=
  IsClosed (ofCLM '' S : Set (H →WOT[𝕜] H))

/-- The commutant `Set.centralizer S` is WOT-closed. -/
lemma isWOTClosed_centralizer (S : Set (H →L[𝕜] H)) : IsWOTClosed (H := H) (Set.centralizer S) := by
  have h : (ofCLM '' Set.centralizer S : Set (H →WOT[𝕜] H)) = Set.centralizer (ofCLM '' S) := by
    ext T
    obtain ⟨T, rfl⟩ := ContinuousLinearMapWOT.ofCLM_surjective T
    rw [ContinuousLinearMapWOT.ofCLM_injective.mem_set_image, Set.mem_centralizer_iff,
      Set.mem_centralizer_iff]
    refine ⟨?_, fun h m hm =>
      congrArg ContinuousLinearMapWOT.toCLM (h (ofCLM m) ⟨m, hm, rfl⟩)⟩
    rintro h _ ⟨m, hm, rfl⟩
    exact congrArg ofCLM (h m hm)
  rw [IsWOTClosed, h]
  exact Set.isClosed_centralizer _

/-- Any double commutant is WOT-closed. -/
lemma isWOTClosed_centralizer_centralizer (S : Set (H →L[𝕜] H)) :
    IsWOTClosed (H := H) (Set.centralizer (Set.centralizer S)) :=
  isWOTClosed_centralizer (H := H) (S := Set.centralizer S)

end IsWOTClosed

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [NormedSpace 𝕜 H]

local notation "B" => (H →L[𝕜] H)
local notation "BWOT" => (H →WOT[𝕜] H)
local notation "H⋆" => StrongDual 𝕜 H

/-- The `inducingFn` defining the weak operator topology, as a continuous linear map. -/
noncomputable def inducingFnCLM : BWOT →L[𝕜] (H × H⋆ → 𝕜) :=
  ⟨ContinuousLinearMapWOT.inducingFn (RingHom.id 𝕜) H H,
    ContinuousLinearMapWOT.continuous_inducingFn (σ := RingHom.id 𝕜) (E := H) (F := H)⟩

/-- `inducingFnCLM` evaluates as `ContinuousLinearMapWOT.inducingFn`. -/
@[simp]
lemma inducingFnCLM_apply (T : BWOT) :
    inducingFnCLM (H := H) T = ContinuousLinearMapWOT.inducingFn (RingHom.id 𝕜) H H T :=
  rfl

/-- The finite-coordinate evaluation map `BWOT → (I → 𝕜)` coming from `inducingFn`. -/
noncomputable def inducingFnRestrictCLM (I : Finset (H × H⋆)) : BWOT →L[𝕜] (↥I → 𝕜) :=
  ContinuousLinearMap.pi (fun i : I => ContinuousLinearMap.proj (i : H × H⋆)) ∘L
    inducingFnCLM (H := H)

/-- A basic separation lemma: for a WOT-closed submodule `A` and `T ∉ A`,
there exists a WOT-continuous linear functional factoring through finitely many
matrix-coefficient coordinates which vanishes on `A` but not on `T`.

This is a “finite-coordinate” version of Hahn–Banach separation tailored to the WOT definition.
-/
lemma exists_wotCLM_sep_of_isClosed_submodule {A : Submodule 𝕜 BWOT}
    (hA : IsClosed (A : Set BWOT)) {T : BWOT} (hT : T ∉ (A : Set BWOT)) :
    ∃ I : Finset (H × H⋆), ∃ g : (↥I → 𝕜) →L[𝕜] 𝕜,
      let f : BWOT →L[𝕜] 𝕜 := g ∘L inducingFnRestrictCLM (H := H) I
      (∀ S : BWOT, S ∈ (A : Set BWOT) → f S = 0) ∧ f T ≠ 0 := by
  classical
  have hopen : IsOpen ((A : Set BWOT)ᶜ) := hA.isOpen_compl
  have hnhds : (A : Set BWOT)ᶜ ∈ 𝓝 T := hopen.mem_nhds hT
  have hind : Topology.IsInducing (ContinuousLinearMapWOT.inducingFn (RingHom.id 𝕜) H H) :=
    ContinuousLinearMapWOT.isInducing_inducingFn (σ := RingHom.id 𝕜) (E := H) (F := H)
  have hcomap_mem : (A : Set BWOT)ᶜ ∈
      Filter.comap (ContinuousLinearMapWOT.inducingFn (RingHom.id 𝕜) H H)
        (𝓝 ((ContinuousLinearMapWOT.inducingFn (RingHom.id 𝕜) H H) T)) := by
    simpa [hind.nhds_eq_comap] using hnhds
  rcases (Filter.mem_comap.1 hcomap_mem) with ⟨V, hVnhds, hVsub⟩
  have hVbasic : ∃ I : Finset (H × H⋆), ∃ t : (H × H⋆) → Set 𝕜,
      (∀ i, t i ∈ 𝓝 ((ContinuousLinearMapWOT.inducingFn (RingHom.id 𝕜) H H) T i)) ∧
        ((↑I : Set (H × H⋆)).pi t) ⊆ V := by
    simpa [nhds_pi, Filter.mem_pi'] using hVnhds
  rcases hVbasic with ⟨I, t, ht0, hIt⟩
  let Φ : BWOT →ₗ[𝕜] (↥I → 𝕜) :=
    (ContinuousLinearMap.pi fun i : I => ContinuousLinearMap.proj (i : H × H⋆)).toLinearMap.comp
    (ContinuousLinearMapWOT.inducingFn (RingHom.id 𝕜) H H)
  let p : Submodule 𝕜 (↥I → 𝕜) := A.map Φ
  have hnot : Φ T ∉ (p : Set (↥I → 𝕜)) := by
    intro hmem
    rcases (Submodule.mem_map).1 hmem with ⟨S, hSA, hST⟩
    have hSIn : (ContinuousLinearMapWOT.inducingFn (RingHom.id 𝕜) H H) S ∈
        ((↑I : Set (H × H⋆)).pi t) := by
      change
        ∀ i, i ∈ (↑I : Set (H × H⋆)) →
          (ContinuousLinearMapWOT.inducingFn (RingHom.id 𝕜) H H) S i ∈ t i
      intro i hi
      have : (ContinuousLinearMapWOT.inducingFn (RingHom.id 𝕜) H H) S i =
          (ContinuousLinearMapWOT.inducingFn (RingHom.id 𝕜) H H) T i := by
        have := congrArg (fun f => f ⟨i, hi⟩) hST
        simpa [Φ] using this
      have ht : t i ∈ 𝓝 ((ContinuousLinearMapWOT.inducingFn (RingHom.id 𝕜) H H) T i) := ht0 i
      exact mem_of_mem_nhds (by simpa [this] using ht)
    have hSInV : (ContinuousLinearMapWOT.inducingFn (RingHom.id 𝕜) H H) S ∈ V := hIt hSIn
    have hSInCompl : S ∈ (A : Set BWOT)ᶜ := by
      have : S ∈ (ContinuousLinearMapWOT.inducingFn (RingHom.id 𝕜) H H) ⁻¹' V := hSInV
      exact hVsub this
    exact hSInCompl (show S ∈ (A : Set BWOT) from hSA)
  obtain ⟨g, hgT, hgmap⟩ :=
    (Submodule.exists_dual_map_eq_bot_of_notMem (p := p) (x := Φ T) hnot (by infer_instance))
  have _hfd : FiniteDimensional 𝕜 (↥I → 𝕜) := by infer_instance
  let gCLM : (↥I → 𝕜) →L[𝕜] 𝕜 :=
    ⟨g, LinearMap.continuous_of_finiteDimensional g⟩
  refine ⟨I, gCLM, ?_⟩
  dsimp
  refine And.intro ?_ ?_
  · intro S hSA
    have : Φ S ∈ (p : Set (↥I → 𝕜)) := by
      exact (Submodule.mem_map).2 ⟨S, hSA, rfl⟩
    have hgzero : ∀ z : (↥I → 𝕜), z ∈ (p : Set (↥I → 𝕜)) → g z = 0 := by
      intro z hz
      have : g z ∈ (p.map g : Submodule 𝕜 𝕜) := by
        exact (Submodule.mem_map).2 ⟨z, hz, rfl⟩
      simpa [hgmap] using this
    exact hgzero (Φ S) this
  · exact hgT


/-- Explicit finite-sum form of the finite-coordinate WOT separation lemma.

This refines `exists_wotCLM_sep_of_isClosed_submodule` by expanding the intermediate functional
`g : (I → 𝕜) →L[𝕜] 𝕜` in coordinates. Concretely, for a WOT-closed submodule `A` and `T ∉ A`, it
produces a finite index set `I : Finset (H × H⋆)` and coefficients `coeff : I → 𝕜` such that the
separating functional

`f = ∑ i : I, coeff i • (proj i) ∘ inducingFnRestrictCLM I`

vanishes on `A` but satisfies `f T ≠ 0`.

In the intended application, the coordinates of `inducingFnRestrictCLM` are matrix coefficients
`(x, y) ↦ y (T x)` defining basic WOT functionals.
-/
lemma exists_wotCLM_sep_of_isClosed_submodule_sum {A : Submodule 𝕜 BWOT}
    (hA : IsClosed (A : Set BWOT)) {T : BWOT} (hT : T ∉ (A : Set BWOT)) :
    ∃ I : Finset (H × H⋆),
      ∃ coeff : (↥I → 𝕜),
        let f : BWOT →L[𝕜] 𝕜 :=
          ∑ i : ↥I, (coeff i) • (ContinuousLinearMap.proj i ∘L inducingFnRestrictCLM (H := H) I)
        (∀ S : BWOT, S ∈ (A : Set BWOT) → f S = 0) ∧ f T ≠ 0 := by
  classical
  rcases exists_wotCLM_sep_of_isClosed_submodule (H := H) (A := A) hA (T := T) hT with
    ⟨I, g, hg⟩
  let coeff : ↥I → 𝕜 := fun i => g (fun j => if i = j then (1 : 𝕜) else 0)
  have hg_sum : ∀ z : (↥I → 𝕜), g z = ∑ i : ↥I, z i • coeff i := by
    intro z
    simpa [coeff] using (LinearMap.pi_apply_eq_sum_univ (R := 𝕜)
      (f := (g : (↥I → 𝕜) →L[𝕜] 𝕜).toLinearMap) (x := z))
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
