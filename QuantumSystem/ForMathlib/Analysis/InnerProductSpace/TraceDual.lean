/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

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

The same nondegeneracy represents every linear functional `f` on `B(H)` by its **density**
`ρ_f = ContinuousLinearMap.density f`, the operator with `f(A) = tr(ρ_f ∘ A)`
(`ContinuousLinearMap.trace_density_comp`); for a state on `B(H)` this is its density operator. A
positive functional has a positive density (`ContinuousLinearMap.density_nonneg`), the trace has
density `1`, and composing with a map `Φ` transforms the density by the trace dual,
`ρ_{f ∘ Φ} = Φ*(ρ_f)` (`ContinuousLinearMap.density_eq_traceDual`).

The maps `Φ` and the functionals `f` are taken from any type with `FunLike` and `LinearMapClass`
instances, so that bundled linear maps, completely positive maps, positive functionals and states
are covered alike.

## Main definitions

* `ContinuousLinearMap.traceForm 𝕜 H` — the trace form `(A, X) ↦ tr(A ∘ X)` on `B(H)`.
* `ContinuousLinearMap.traceDual Φ` — the trace dual `Φ* : B(K) →ₗ B(H)` of `Φ : B(H) → B(K)`.
* `ContinuousLinearMap.density f` — the density `ρ_f` of a functional, `f(A) = tr(ρ_f ∘ A)`.
* `ContinuousLinearMap.tracePositiveLinearMap 𝕜 H` — the trace on `B(H)` as a positive functional.

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
* `ContinuousLinearMap.trace_map` — algebra isomorphisms `B(H) ≃ B(K)` preserve the trace.
* `ContinuousLinearMap.trace_density_comp`, `ContinuousLinearMap.eq_density_iff` — the density is
  characterised by `f(A) = tr(ρ_f ∘ A)`; `ContinuousLinearMap.density_eq_density_iff` — two
  functionals have the same density iff they agree.
* `ContinuousLinearMap.density_eq_traceDual`, `ContinuousLinearMap.density_eq_apply_density` —
  `ρ_{f ∘ Φ} = Φ*(ρ_f)` and `ρ_{f ∘ Φ*} = Φ(ρ_f)`.
* `ContinuousLinearMap.apply_eq_zero_of_inner_apply_self_eq_zero` — a positive operator vanishes
  where its quadratic form does; `ContinuousLinearMap.trace_star_mul_self_eq_zero_iff` — the trace
  is faithful, `tr(A⋆ A) = 0 ↔ A = 0`; `ContinuousLinearMap.trace_comp_nonneg` — `0 ≤ tr(A B)`
  for positive `A` and `B`.
* `ContinuousLinearMap.density_nonneg` — a positive functional has a positive density;
  `ContinuousLinearMap.density_tracePositiveLinearMap` — the trace has density `1`.
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

/-- Algebra isomorphisms `B(H) ≃ B(K)` preserve the trace: transported to the endomorphism
algebras, this is `LinearMap.trace_map`. -/
theorem trace_map [FiniteDimensional 𝕜 K] {F' : Type*} [EquivLike F' (H →L[𝕜] H) (K →L[𝕜] K)]
    [AlgEquivClass F' 𝕜 (H →L[𝕜] H) (K →L[𝕜] K)] (φ : F') (A : H →L[𝕜] H) :
    LinearMap.trace 𝕜 K (φ A) = LinearMap.trace 𝕜 H A := by
  have h₁ : Module.End.toContinuousLinearMap H (A : H →ₗ[𝕜] H) = A := by ext; rfl
  have h₂ : (Module.End.toContinuousLinearMap K).symm (φ A) = (φ A : K →ₗ[𝕜] K) := by
    rw [AlgEquiv.symm_apply_eq]; ext; rfl
  have h := LinearMap.trace_map (((Module.End.toContinuousLinearMap H).trans
    (AlgEquiv.ofClass φ)).trans (Module.End.toContinuousLinearMap K).symm) (A : H →ₗ[𝕜] H)
  rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, h₁] at h
  exact (congrArg _ h₂).symm.trans h

open scoped ComplexOrder in
variable (𝕜 H) in
/-- The trace `A ↦ tr A` on `B(H)` as a positive linear functional: `tr A ≥ 0` for `A ≥ 0`
(`LinearMap.IsPositive.trace_nonneg`). -/
noncomputable def tracePositiveLinearMap : (H →L[𝕜] H) →ₚ[𝕜] 𝕜 :=
  .mk₀ (LinearMap.trace 𝕜 H ∘ₗ coeLM 𝕜) fun _ hA =>
    (nonneg_iff_isPositive.1 hA).toLinearMap.trace_nonneg

open scoped ComplexOrder in
omit [FiniteDimensional 𝕜 H] in
/-- The trace functional evaluates as the trace. -/
@[simp] lemma tracePositiveLinearMap_apply (A : H →L[𝕜] H) :
    tracePositiveLinearMap 𝕜 H A = LinearMap.trace 𝕜 H A :=
  rfl

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

/-! ### The density of a functional -/

section Density

variable {G : Type*} [FunLike G (H →L[𝕜] H) 𝕜] [LinearMapClass G 𝕜 (H →L[𝕜] H) 𝕜]

/-- The **density** `ρ_f` of a linear functional `f` on `B(H)`: the operator that the
nondegenerate trace form `ContinuousLinearMap.traceForm` identifies with `f`, so that
`f(A) = tr(ρ_f ∘ A)` (`ContinuousLinearMap.trace_density_comp`). For a state on `B(H)` this is its
density operator. No basis is chosen. -/
noncomputable def density (f : G) : H →L[𝕜] H :=
  ((traceForm 𝕜 H).toDual traceForm_nondegenerate).symm (f : (H →L[𝕜] H) →ₗ[𝕜] 𝕜)

/-- **The defining property** of the density: `tr(ρ_f ∘ A) = f(A)`. -/
theorem trace_density_comp (f : G) (A : H →L[𝕜] H) :
    LinearMap.trace 𝕜 H (density f ∘L A) = f A :=
  LinearMap.BilinForm.apply_toDual_symm_apply (hB := traceForm_nondegenerate) _ A

/-- The density is characterised by its defining property: `Y = ρ_f` iff `tr(Y ∘ A) = f(A)` for
all `A`. -/
theorem eq_density_iff (f : G) (Y : H →L[𝕜] H) :
    Y = density f ↔ ∀ A : H →L[𝕜] H, LinearMap.trace 𝕜 H (Y ∘L A) = f A := by
  simp_rw [ext_iff_trace_comp_right (Y := density f), trace_density_comp]

/-- Two functionals have the same density iff they agree. -/
theorem density_eq_density_iff {G' : Type*} [FunLike G' (H →L[𝕜] H) 𝕜]
    [LinearMapClass G' 𝕜 (H →L[𝕜] H) 𝕜] {f : G} {g : G'} :
    density f = density g ↔ ∀ A, f A = g A := by
  rw [eq_density_iff]
  simp_rw [trace_density_comp]

/-- The matrix coefficients of the density: `⟪x, ρ_f x⟫ = f(|x⟩⟨x|)`. -/
theorem inner_density_apply (f : G) (x : H) : ⟪x, density f x⟫_𝕜 = f (rankOne 𝕜 x x) := by
  rw [← trace_density_comp, trace_comp_rankOne]

open scoped ComplexOrder in
/-- The trace has density `1`. -/
@[simp] theorem density_tracePositiveLinearMap : density (tracePositiveLinearMap 𝕜 H) = 1 := by
  rw [eq_comm, eq_density_iff]
  intro A
  rw [← mul_def, one_mul, tracePositiveLinearMap_apply]

variable {F : Type*} [FunLike F (H →L[𝕜] H) (K →L[𝕜] K)]
  [LinearMapClass F 𝕜 (H →L[𝕜] H) (K →L[𝕜] K)]

/-- **Pulling back a functional transforms its density by the trace dual**: if `f = g ∘ Φ`, then
`ρ_f = Φ*(ρ_g)`, since `tr(Φ*(ρ_g) ∘ A) = tr(ρ_g ∘ Φ(A)) = g(Φ(A))`. -/
theorem density_eq_traceDual {G' : Type*} [FunLike G' (K →L[𝕜] K) 𝕜]
    [LinearMapClass G' 𝕜 (K →L[𝕜] K) 𝕜] (Φ : F) {f : G} {g : G'} (h : ∀ A, f A = g (Φ A)) :
    density f = traceDual Φ (density g) := by
  rw [eq_comm, eq_density_iff]
  intro A
  rw [trace_comp_comm', ← trace_comp_traceDual, trace_comp_comm', trace_density_comp, h]

/-- **The Schrödinger picture**: if `f = g ∘ Φ*` for the trace dual `Φ*` of `Φ : B(H) → B(K)`,
then `ρ_f = Φ(ρ_g)`; for a quantum channel `Φ`, the state `g ∘ Φ*` has density `Φ(ρ_g)`. -/
theorem density_eq_apply_density {G' : Type*} [FunLike G' (K →L[𝕜] K) 𝕜]
    [LinearMapClass G' 𝕜 (K →L[𝕜] K) 𝕜] (Φ : F) {f : G'} {g : G}
    (h : ∀ B, f B = g (traceDual Φ B)) : density f = Φ (density g) := by
  rw [density_eq_traceDual (traceDual Φ) h, traceDual_traceDual]

end Density

end ContinuousLinearMap

/-! ### Positivity of the density -/

section DensityNonneg

open scoped ComplexOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {G : Type*} [FunLike G (E →L[ℂ] E) ℂ] [LinearMapClass G ℂ (E →L[ℂ] E) ℂ]

/-- **A positive functional has a positive density**: `⟪x, ρ_f x⟫ = f(|x⟩⟨x|) ≥ 0`
(`ContinuousLinearMap.inner_density_apply`). -/
theorem ContinuousLinearMap.density_nonneg [OrderHomClass G (E →L[ℂ] E) ℂ] (f : G) :
    0 ≤ density f := by
  rw [nonneg_iff_isPositive, isPositive_iff_complex]
  intro x
  have h := map_nonneg f (nonneg_iff_isPositive.2 (isPositive_rankOne_self (𝕜 := ℂ) x))
  rw [← inner_density_apply] at h
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp h
  have hre' : RCLike.re ⟪density f x, x⟫_ℂ = (⟪x, density f x⟫_ℂ).re := inner_re_symm _ _
  have him' : (⟪density f x, x⟫_ℂ).im = 0 := by
    have := inner_im_symm (𝕜 := ℂ) (density f x) x
    simp only [RCLike.im_to_complex] at this
    rw [this, ← him, neg_zero]
  exact ⟨Complex.ext (by simp) (by simp [him']), hre' ▸ hre⟩

/-- A positive operator vanishes on the vectors where its quadratic form vanishes: with
`ρ = a⋆ a`, `⟪x, ρ x⟫ = ‖a x‖²`. -/
theorem ContinuousLinearMap.apply_eq_zero_of_inner_apply_self_eq_zero {ρ : E →L[ℂ] E}
    (hρ : 0 ≤ ρ) {x : E} (hx : ⟪x, ρ x⟫_ℂ = 0) : ρ x = 0 := by
  obtain ⟨a, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hρ
  have h : ⟪x, (star a * a) x⟫_ℂ = ((‖a x‖ ^ 2 : ℝ) : ℂ) := by
    change ⟪x, adjoint a (a x)⟫_ℂ = _
    rw [adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  rw [h, Complex.ofReal_eq_zero] at hx
  have hax : a x = 0 := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hx)
  change adjoint a (a x) = 0
  rw [hax, map_zero]

/-- The trace vanishes on `A⋆ A` only at `A = 0`: `tr(A⋆ A) = Σᵢ ‖A bᵢ‖²`. -/
theorem ContinuousLinearMap.trace_star_mul_self_eq_zero_iff (A : E →L[ℂ] E) :
    LinearMap.trace ℂ E ((star A * A : E →L[ℂ] E) : E →ₗ[ℂ] E) = 0 ↔ A = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  set b := stdOrthonormalBasis ℂ E
  have hterm : ∀ i, ⟪b i, ((star A * A : E →L[ℂ] E) : E →ₗ[ℂ] E) (b i)⟫_ℂ =
      ((‖A (b i)‖ ^ 2 : ℝ) : ℂ) := fun i => by
    change ⟪b i, adjoint A (A (b i))⟫_ℂ = _
    rw [adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  rw [LinearMap.trace_eq_sum_inner _ b, Finset.sum_congr rfl fun i _ => hterm i,
    ← Complex.ofReal_sum, Complex.ofReal_eq_zero] at h
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg ‖A (b i)‖).mp h
  refine ContinuousLinearMap.coe_injective (b.toBasis.ext fun i => ?_)
  rw [OrthonormalBasis.coe_toBasis, coe_coe, ContinuousLinearMap.toLinearMap_zero, LinearMap.zero_apply]
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (hzero i (Finset.mem_univ i)))

/-- The trace of a product of positive operators is nonnegative: for `A = R† R`,
`tr(A B) = tr(R B R†)` and `R B R† ≥ 0`. -/
theorem ContinuousLinearMap.trace_comp_nonneg {A B : E →L[ℂ] E} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ LinearMap.trace ℂ E (A ∘L B) := by
  obtain ⟨R, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA
  have h : 0 ≤ R * B * star R := star_right_conjugate_nonneg hB R
  have h' := LinearMap.IsPositive.trace_nonneg
    ((ContinuousLinearMap.isPositive_toLinearMap_iff _).2
      (ContinuousLinearMap.nonneg_iff_isPositive.1 h))
  rwa [ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def,
    ← ContinuousLinearMap.trace_comp_comm' (R ∘L B) (star R), ← ContinuousLinearMap.comp_assoc,
    ← ContinuousLinearMap.mul_def] at h'

end DensityNonneg
