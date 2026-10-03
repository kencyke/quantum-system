/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# The trace dual of a linear map between operator algebras

Let `H` and `K` be finite-dimensional inner product spaces over `𝕜 = ℝ` or `ℂ`. The **trace
pairing** `(A, X) ↦ tr(A ∘ X)` on `B(H) = H →L[𝕜] H` is nondegenerate
(`ContinuousLinearMap.traceForm_nondegenerate`): testing against the rank-one operators,
`tr(A ∘ |x⟩⟨y|) = ⟪y, A x⟫` (`ContinuousLinearMap.trace_comp_rankOne`). It therefore identifies
`B(H)` with its dual, and every linear map `Φ : B(H) → B(K)` has a unique **trace dual**
`Φ* = ContinuousLinearMap.traceDual Φ : B(K) → B(H)` with `tr(Φ(A) ∘ B) = tr(A ∘ Φ*(B))`
(`ContinuousLinearMap.trace_comp_traceDual`). No basis is chosen. The trace is Mathlib's
`LinearMap.trace 𝕜 H`, applied to the underlying linear map of an operator.

`Φ*` is the transpose of `Φ` for the *bilinear* trace pairing `(A, B) ↦ tr(A ∘ B)`, so it is
`𝕜`-linear in `Φ`. It is not in general the adjoint for the Hilbert–Schmidt inner product
`⟪A, B⟫ = tr(A† ∘ B)`, which is conjugate-linear in `Φ` (for `Φ = i • id`, `Φ* = i • id` while the
Hilbert–Schmidt adjoint is `-i • id`). The two agree exactly when `Φ` preserves self-adjointness,
`Φ(A†) = Φ(A)†`, in particular for positive maps; for a quantum channel `Φ*` is the Heisenberg
picture of `Φ`.

The map `Φ` is taken from any type `F` with `FunLike` and `LinearMapClass` instances, so that
bundled linear maps and completely positive maps are covered alike.

## Main definitions

* `ContinuousLinearMap.traceForm 𝕜 H` — the trace form `(A, X) ↦ tr(A ∘ X)` on `B(H)`.
* `ContinuousLinearMap.traceDual Φ` — the trace dual `Φ* : B(K) →ₗ B(H)` of `Φ : B(H) → B(K)`.

## Main statements

* `ContinuousLinearMap.ext_iff_trace_comp_left`, `ContinuousLinearMap.ext_iff_trace_comp_right` —
  operators are separated by the trace pairing.
* `ContinuousLinearMap.trace_comp_traceDual` — the defining duality
  `tr(Φ(A) ∘ B) = tr(A ∘ Φ*(B))`; `ContinuousLinearMap.eq_traceDual_iff` — it characterises `Φ*`.
* `ContinuousLinearMap.traceDual_congr` — the trace dual depends only on the values of `Φ`.
* `ContinuousLinearMap.inner_traceDual_apply` — `⟪x, Φ*(B) y⟫ = tr(Φ(|y⟩⟨x|) ∘ B)`.
* `ContinuousLinearMap.traceDual_traceDual` — the trace dual is an involution, `Φ** = Φ`.
* `ContinuousLinearMap.traceDual_one_iff` — `Φ` is trace preserving iff `Φ*` is unital.
* `ContinuousLinearMap.traceDual_eq_sum_of_kraus` — the trace dual of the Kraus map
  `A ↦ Σₐ Tₐ A Tₐ†` is `B ↦ Σₐ Tₐ† B Tₐ`.
-/

@[expose] public section

open scoped InnerProductSpace
open InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 H K : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [FiniteDimensional 𝕜 H]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]

/-! ### The trace pairing -/

/-- Cyclicity of the trace for operators between two spaces: `tr(B ∘ A) = tr(A ∘ B)`. -/
lemma trace_comp_comm' [FiniteDimensional 𝕜 K] (A : H →L[𝕜] K) (B : K →L[𝕜] H) :
    LinearMap.trace 𝕜 H (B ∘L A) = LinearMap.trace 𝕜 K (A ∘L B) := by
  rw [toLinearMap_comp, LinearMap.trace_comp_comm', ← toLinearMap_comp]

/-- Pairing with a rank-one operator evaluates a matrix coefficient: `tr(A ∘ |x⟩⟨y|) = ⟪y, A x⟫`. -/
lemma trace_comp_rankOne (A : H →L[𝕜] H) (x y : H) :
    LinearMap.trace 𝕜 H (A ∘L rankOne 𝕜 x y) = ⟪y, A x⟫_𝕜 := by
  rw [comp_rankOne, trace_rankOne]

/-- Pairing with a rank-one operator evaluates a matrix coefficient: `tr(|x⟩⟨y| ∘ A) = ⟪y, A x⟫`. -/
lemma trace_rankOne_comp (A : H →L[𝕜] H) (x y : H) :
    LinearMap.trace 𝕜 H (rankOne 𝕜 x y ∘L A) = ⟪y, A x⟫_𝕜 := by
  rw [trace_comp_comm', trace_comp_rankOne]

/-- Operators are separated by the trace pairing: `X = Y` iff `tr(X ∘ A) = tr(Y ∘ A)` for all `A`,
already for the rank-one `A` (`ContinuousLinearMap.trace_comp_rankOne`). -/
theorem ext_iff_trace_comp_right {X Y : H →L[𝕜] H} :
    X = Y ↔ ∀ A : H →L[𝕜] H, LinearMap.trace 𝕜 H (X ∘L A) = LinearMap.trace 𝕜 H (Y ∘L A) := by
  refine ⟨fun h _ => h ▸ rfl, fun h => ext fun x => ext_inner_left 𝕜 fun y => ?_⟩
  rw [← trace_comp_rankOne, ← trace_comp_rankOne, h]

/-- Operators are separated by the trace pairing: `X = Y` iff `tr(A ∘ X) = tr(A ∘ Y)` for
all `A`. -/
theorem ext_iff_trace_comp_left {X Y : H →L[𝕜] H} :
    X = Y ↔ ∀ A : H →L[𝕜] H, LinearMap.trace 𝕜 H (A ∘L X) = LinearMap.trace 𝕜 H (A ∘L Y) := by
  rw [ext_iff_trace_comp_right]
  exact forall_congr' fun A => by rw [trace_comp_comm' A X, trace_comp_comm' A Y]

variable (𝕜 H) in
/-- The **trace form** `(A, X) ↦ tr(A ∘ X)` on `B(H)`. -/
noncomputable def traceForm : LinearMap.BilinForm 𝕜 (H →L[𝕜] H) :=
  (LinearMap.mul 𝕜 (H →L[𝕜] H)).compr₂ (LinearMap.trace 𝕜 H ∘ₗ coeLM 𝕜)

omit [FiniteDimensional 𝕜 H] in
/-- The trace form is `(A, X) ↦ tr(A ∘ X)`. -/
@[simp] lemma traceForm_apply (A X : H →L[𝕜] H) :
    traceForm 𝕜 H A X = LinearMap.trace 𝕜 H (A ∘L X) :=
  rfl

/-- The trace form is nondegenerate (`ContinuousLinearMap.ext_iff_trace_comp_right`,
`ContinuousLinearMap.ext_iff_trace_comp_left`). -/
theorem traceForm_nondegenerate : (traceForm 𝕜 H).Nondegenerate :=
  ⟨fun A h => ext_iff_trace_comp_right.2 fun X => by simpa using h X,
    fun X h => ext_iff_trace_comp_left.2 fun A => by simpa using h A⟩

/-! ### The trace dual -/

variable {F : Type*} [FunLike F (H →L[𝕜] H) (K →L[𝕜] K)]
  [LinearMapClass F 𝕜 (H →L[𝕜] H) (K →L[𝕜] K)]

/-- The **trace dual** `Φ* : B(K) →ₗ B(H)` of a linear map `Φ : B(H) → B(K)`, its transpose for
the bilinear trace pairing, characterised by `tr(Φ(A) ∘ B) = tr(A ∘ Φ*(B))`
(`ContinuousLinearMap.trace_comp_traceDual`): `Φ*(B)` is the operator that the nondegenerate trace
form `ContinuousLinearMap.traceForm` identifies with the functional `A ↦ tr(Φ(A) ∘ B)`. Both
spaces are finite-dimensional, where the trace is the trace; Mathlib's `LinearMap.trace` is `0`
on infinite-dimensional spaces. -/
noncomputable def traceDual [FiniteDimensional 𝕜 K] (Φ : F) : (K →L[𝕜] K) →ₗ[𝕜] (H →L[𝕜] H) :=
  ((traceForm 𝕜 H).toDual traceForm_nondegenerate).symm.toLinearMap ∘ₗ
    LinearMap.lcomp 𝕜 𝕜 (Φ : (H →L[𝕜] H) →ₗ[𝕜] (K →L[𝕜] K)) ∘ₗ (traceForm 𝕜 K).flip

variable [FiniteDimensional 𝕜 K]

/-- **The defining duality** of the trace dual: `tr(Φ(A) ∘ B) = tr(A ∘ Φ*(B))`. -/
theorem trace_comp_traceDual (Φ : F) (A : H →L[𝕜] H) (B : K →L[𝕜] K) :
    LinearMap.trace 𝕜 K (Φ A ∘L B) = LinearMap.trace 𝕜 H (A ∘L traceDual Φ B) := by
  have h := LinearMap.BilinForm.apply_toDual_symm_apply (hB := traceForm_nondegenerate)
    ((LinearMap.lcomp 𝕜 𝕜 (Φ : (H →L[𝕜] H) →ₗ[𝕜] (K →L[𝕜] K)) ∘ₗ (traceForm 𝕜 K).flip) B) A
  rw [trace_comp_comm' (traceDual Φ B) A]
  exact h.symm

/-- The trace dual is characterised by the trace duality: `Y = Φ*(B)` iff
`tr(A ∘ Y) = tr(Φ(A) ∘ B)` for all `A`. -/
theorem eq_traceDual_iff (Φ : F) (B : K →L[𝕜] K) (Y : H →L[𝕜] H) :
    Y = traceDual Φ B ↔
      ∀ A : H →L[𝕜] H, LinearMap.trace 𝕜 H (A ∘L Y) = LinearMap.trace 𝕜 K (Φ A ∘L B) := by
  simp_rw [ext_iff_trace_comp_left (X := Y), trace_comp_traceDual]

/-- The trace dual depends only on the values of the map: if `Φ A = Ψ A` for all `A`, then
`Φ* = Ψ*`. -/
theorem traceDual_congr {G : Type*} [FunLike G (H →L[𝕜] H) (K →L[𝕜] K)]
    [LinearMapClass G 𝕜 (H →L[𝕜] H) (K →L[𝕜] K)] {Φ : F} {Ψ : G} (h : ∀ A, Φ A = Ψ A) :
    traceDual Φ = traceDual Ψ :=
  LinearMap.ext fun B => (eq_traceDual_iff Ψ B _).2 fun A => by
    rw [← h, ← trace_comp_traceDual]

/-- The matrix coefficients of the trace dual: `⟪x, Φ*(B) y⟫ = tr(Φ(|y⟩⟨x|) ∘ B)`. -/
theorem inner_traceDual_apply (Φ : F) (B : K →L[𝕜] K) (x y : H) :
    ⟪x, traceDual Φ B y⟫_𝕜 = LinearMap.trace 𝕜 K (Φ (rankOne 𝕜 y x) ∘L B) := by
  rw [trace_comp_traceDual, trace_rankOne_comp]

/-- The trace dual is an involution, `Φ** = Φ`: by the defining duality applied twice,
`tr(B ∘ Φ**(A)) = tr(Φ*(B) ∘ A) = tr(A ∘ Φ*(B)) = tr(Φ(A) ∘ B) = tr(B ∘ Φ(A))`. -/
theorem traceDual_traceDual (Φ : F) (A : H →L[𝕜] H) : traceDual (traceDual Φ) A = Φ A := by
  refine ext_iff_trace_comp_left.2 fun B => ?_
  rw [← trace_comp_traceDual, trace_comp_comm', ← trace_comp_traceDual, trace_comp_comm']

/-- A linear map is trace preserving iff its trace dual is unital:
`tr(Φ(A)) = tr(Φ(A) ∘ 1) = tr(A ∘ Φ*(1))`. -/
theorem traceDual_one_iff {Φ : F} :
    traceDual Φ 1 = 1 ↔ ∀ A, LinearMap.trace 𝕜 K (Φ A) = LinearMap.trace 𝕜 H A := by
  rw [eq_comm, eq_traceDual_iff]
  exact forall_congr' fun A => by rw [← mul_def, ← mul_def, mul_one, mul_one, eq_comm]

/-- The trace dual of the Kraus map `A ↦ Σₐ Tₐ A Tₐ†` is `B ↦ Σₐ Tₐ† B Tₐ`, by cyclicity of the
trace, `tr(Tₐ A Tₐ† B) = tr(A Tₐ† B Tₐ)`. -/
theorem traceDual_eq_sum_of_kraus [CompleteSpace H] [CompleteSpace K] {Φ : F} {ι : Type*}
    [Fintype ι] {T : ι → H →L[𝕜] K} (hT : ∀ A, Φ A = ∑ a, T a ∘L A ∘L adjoint (T a))
    (B : K →L[𝕜] K) : traceDual Φ B = ∑ a, adjoint (T a) ∘L B ∘L T a := by
  rw [eq_comm, eq_traceDual_iff]
  intro A
  simp only [hT, comp_finsetSum, finsetSum_comp, toLinearMap_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show A ∘L adjoint (T a) ∘L B ∘L T a = (A ∘L adjoint (T a) ∘L B) ∘L T a by
    simp only [comp_assoc], trace_comp_comm']
  simp only [comp_assoc]

end ContinuousLinearMap
