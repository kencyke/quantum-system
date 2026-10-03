/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Analysis.CStarAlgebra.QuantumChannel.Dual
public import QuantumSystem.Analysis.Matrix.QuantumChannel.Choi
public import QuantumSystem.ForMathlib.LinearAlgebra.Matrix.Trace

/-!
# The dual of a quantum channel as a Schwarz map

Let `φ : Mₙ(ℂ) → Mₘ(ℂ)` be a `2`-positive, in particular a completely positive, map that is trace
non-increasing on positive semidefinite matrices, equivalently `Matrix.traceDual φ 1 ≤ 1`
(`Matrix.traceDual_one_le_one_iff`). Its trace dual `Matrix.traceDual φ : Mₘ(ℂ) → Mₙ(ℂ)`,
read on operators through the ⋆-isomorphisms `Matrix.toEuclideanCLM`, is a normal Schwarz map
`Matrix.dualSchwarzMap φ hφ : B(ℂᵐ) → B(ℂⁿ)`, unital when `φ` is trace preserving, as a
quantum channel is. The trace dual is `2`-positive by self-duality of the positive semidefinite
cone (`KPositiveMap.matrixTraceDual`) and sub-unital, hence a Schwarz map by the Kadison–Schwarz
inequality (`KPositiveMapClass.toSchwarzMap`); the ⋆-isomorphisms are Schwarz maps
(`NonUnitalStarAlgHomClass.instSchwarzMapClass`). No Kraus representation of `φ` is chosen. It is
the Heisenberg-picture channel along which the data-processing inequality for Araki's relative
entropy (`VonNeumannAlgebra.arakiEntropy_comp_le`) applies, and it transports the normal functional
`Tr (ρ ·)` to `Tr (φ(ρ) ·)`: `Tr (ρ (Matrix.traceDual φ B)) = Tr (φ(ρ) B)`
(`Matrix.trace_mul_traceDual`).

The Schwarz map is bundled with `SchwarzMap.onBoundedLinearOperators`
(`QuantumSystem/Analysis/CStarAlgebra/QuantumChannel/Dual.lean`). The construction is stated for
any type `F` of `2`-positive linear maps (`KPositiveMapClass F 2`), so that completely positive
maps (`CompletelyPositiveMap`, through
`CompletelyPositiveMapClass.instKPositiveMapClass`) and `2`-positive maps (`KPositiveMap 2`) enter
directly.

## Main definitions

* `Matrix.dualSchwarzMap φ hφ : SchwarzMap 𝓑(ℂᵐ) 𝓑(ℂⁿ)` — the trace dual of a
  `2`-positive map `φ` with `Matrix.traceDual φ 1 ≤ 1`; `Matrix.QuantumChannel.dualSchwarzMap Φ`
  for a quantum channel `Φ`.

## Main results

* `Matrix.traceDual_one_le_one_iff` — `Matrix.traceDual φ 1 ≤ 1` iff `φ` is trace
  non-increasing on positive semidefinite matrices.
* `Matrix.dualSchwarzMap_apply`, `Matrix.QuantumChannel.dualSchwarzMap_apply` — on the
  operator of `B ∈ Mₘ(ℂ)` it is the operator of `Matrix.traceDual φ B`.
* `Matrix.dualSchwarzMap_one`, `Matrix.QuantumChannel.dualSchwarzMap_one` — it is
  unital when `φ` is trace preserving.
* `Matrix.isNormalMap_dualSchwarzMap`, `Matrix.QuantumChannel.isNormalMap_dualSchwarzMap`
  — it is normal.
-/

@[expose] public section

open ContinuousLinearMap
open scoped VonNeumannAlgebra ComplexOrder

/-! ### The dual of a `2`-positive trace non-increasing map -/

namespace Matrix

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
  {F : Type*} [FunLike F (Matrix n n ℂ) (Matrix m m ℂ)]

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- The trace dual of a positive map is sub-unital, `Matrix.traceDual φ 1 ≤ 1`, iff the map is
**trace non-increasing** on positive semidefinite matrices, `Re Tr φ(ρ) ≤ Re Tr ρ`:
`Tr φ(ρ) = Tr (ρ (Matrix.traceDual φ 1))` (`Matrix.trace_mul_traceDual`), and the positive
semidefinite cone is self-dual, tested here on the rank-one matrices `x x†`. -/
theorem traceDual_one_le_one_iff [OrderHomClass F (Matrix n n ℂ) (Matrix m m ℂ)]
    [LinearMapClass F ℂ (Matrix n n ℂ) (Matrix m m ℂ)] (φ : F) :
    Matrix.traceDual φ 1 ≤ 1 ↔
      ∀ ρ : Matrix n n ℂ, ρ.PosSemidef → (φ ρ).trace.re ≤ ρ.trace.re := by
  have key (ρ : Matrix n n ℂ) : (φ ρ).trace = (ρ * Matrix.traceDual φ 1).trace := by
    rw [← trace_mul_traceDual, Matrix.mul_one]
  refine ⟨fun h ρ hρ => ?_, fun h => ?_⟩
  · have h' := (Complex.le_def.1 (hρ.trace_mul_nonneg (Matrix.le_iff.1 h))).1
    rwa [Matrix.mul_sub, trace_sub, Matrix.mul_one, ← key, Complex.sub_re, Complex.zero_re,
      sub_nonneg] at h'
  · rw [Matrix.le_iff, posSemidef_iff_dotProduct_mulVec_complex]
    intro x
    have hρ := posSemidef_vecMulVec_self_star x
    rw [← trace_mul_vecMulVec, Matrix.sub_mul, Matrix.one_mul, trace_sub,
      Matrix.trace_mul_comm (Matrix.traceDual φ 1), ← key]
    have h₁ := Complex.le_def.1 hρ.trace_nonneg
    have h₂ := Complex.le_def.1 (hρ.map φ).trace_nonneg
    refine Complex.le_def.2 ⟨?_, ?_⟩
    · simpa [sub_nonneg] using h _ hρ
    · rw [Complex.sub_im, ← h₁.2, ← h₂.2, sub_self, Complex.zero_im]

open scoped Matrix.Norms.L2Operator MatrixOrder CStarAlgebra in
/-- The **dual** `B(ℂᵐ) → B(ℂⁿ)` of a `2`-positive map `φ : M_n(ℂ) → M_m(ℂ)` with
`Matrix.traceDual φ 1 ≤ 1`, that is, a trace non-increasing one
(`Matrix.traceDual_one_le_one_iff`), as a Schwarz map: the trace dual of `φ`
(`Matrix.dualSchwarzMap_apply`) read on operators,
`Matrix.toEuclideanCLM ∘ Matrix.traceDual φ ∘ Matrix.toEuclideanCLM⁻¹`. The trace dual is
`2`-positive (`KPositiveMap.matrixTraceDual`) and sub-unital, hence a Schwarz map
(`KPositiveMapClass.toSchwarzMap`), and the ⋆-isomorphisms are Schwarz maps. For a trace-preserving
`φ` the hypothesis is `(Matrix.traceDual_one hφ).le` and the dual is unital
(`Matrix.dualSchwarzMap_one`). -/
noncomputable def dualSchwarzMap [LinearMapClass F ℂ (Matrix n n ℂ) (Matrix m m ℂ)]
    [KPositiveMapClass F 2 (Matrix n n ℂ) (Matrix m m ℂ)] (φ : F)
    (hφ : Matrix.traceDual φ 1 ≤ 1) : SchwarzMap 𝓑(EuclideanSpace ℂ m) 𝓑(EuclideanSpace ℂ n) :=
  SchwarzMap.onBoundedLinearOperators <|
    (SchwarzMapClass.toSchwarzMap (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ))).comp <|
      (KPositiveMapClass.toSchwarzMap (KPositiveMap.matrixTraceDual 2 φ) hφ).comp
        (SchwarzMapClass.toSchwarzMap (Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ)).symm)

open scoped Matrix.Norms.L2Operator MatrixOrder CStarAlgebra in
/-- On the operator of a matrix `B`, the dual `Matrix.dualSchwarzMap φ hφ` is the
operator of the trace dual `Matrix.traceDual φ B`. -/
theorem dualSchwarzMap_apply [LinearMapClass F ℂ (Matrix n n ℂ) (Matrix m m ℂ)]
    [KPositiveMapClass F 2 (Matrix n n ℂ) (Matrix m m ℂ)] (φ : F)
    (hφ : Matrix.traceDual φ 1 ≤ 1) (B : Matrix m m ℂ) :
    (dualSchwarzMap φ hφ) B.toBoundedLinearOperators =
      (Matrix.traceDual φ B).toBoundedLinearOperators := by
  apply Subtype.ext
  change Matrix.toEuclideanCLM (𝕜 := ℂ) (Matrix.traceDual φ
    ((Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ)).symm (Matrix.toEuclideanCLM (𝕜 := ℂ) B))) = _
  rw [StarAlgEquiv.symm_apply_apply]
  rfl

open scoped Matrix.Norms.L2Operator MatrixOrder CStarAlgebra in
/-- The dual of a trace-preserving map is unital. -/
theorem dualSchwarzMap_one [LinearMapClass F ℂ (Matrix n n ℂ) (Matrix m m ℂ)]
    [KPositiveMapClass F 2 (Matrix n n ℂ) (Matrix m m ℂ)] (φ : F) (hφ : IsTracePreserving φ) :
    (dualSchwarzMap φ (traceDual_one hφ).le) 1 = 1 := by
  apply Subtype.ext
  change Matrix.toEuclideanCLM (𝕜 := ℂ)
    (Matrix.traceDual φ ((Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ)).symm 1)) = 1
  rw [map_one, traceDual_one hφ, map_one]

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- The dual of a `2`-positive trace non-increasing map is normal (finite dimensions). -/
theorem isNormalMap_dualSchwarzMap [LinearMapClass F ℂ (Matrix n n ℂ) (Matrix m m ℂ)]
    [KPositiveMapClass F 2 (Matrix n n ℂ) (Matrix m m ℂ)] (φ : F)
    (hφ : Matrix.traceDual φ 1 ≤ 1) : VonNeumannAlgebra.IsNormalMap (dualSchwarzMap φ hφ) :=
  VonNeumannAlgebra.isNormalMap_of_finiteDimensional _

namespace QuantumChannel

open scoped Matrix.Norms.L2Operator MatrixOrder CStarAlgebra in
/-- The **dual channel** `Φ* : B(ℂᵐ) → B(ℂⁿ)` of a quantum channel as a Schwarz map
(`Matrix.dualSchwarzMap`); no Kraus representation of `Φ` is chosen. -/
noncomputable def dualSchwarzMap (Φ : QuantumChannel n m) :
    SchwarzMap 𝓑(EuclideanSpace ℂ m) 𝓑(EuclideanSpace ℂ n) :=
  Matrix.dualSchwarzMap Φ (traceDual_one Φ.isTracePreserving).le

open scoped Matrix.Norms.L2Operator MatrixOrder CStarAlgebra in
/-- On the operator of a matrix `B`, the dual channel is the operator of `Matrix.traceDual Φ B`. -/
theorem dualSchwarzMap_apply (Φ : QuantumChannel n m) (B : Matrix m m ℂ) :
    (dualSchwarzMap Φ) B.toBoundedLinearOperators =
      (Matrix.traceDual Φ B).toBoundedLinearOperators :=
  Matrix.dualSchwarzMap_apply Φ (traceDual_one Φ.isTracePreserving).le B

open scoped Matrix.Norms.L2Operator MatrixOrder CStarAlgebra in
/-- The dual of a (trace-preserving) channel is unital. -/
theorem dualSchwarzMap_one (Φ : QuantumChannel n m) : (dualSchwarzMap Φ) 1 = 1 :=
  Matrix.dualSchwarzMap_one Φ Φ.isTracePreserving

/-- The dual of a channel is normal (finite dimensions). -/
theorem isNormalMap_dualSchwarzMap (Φ : QuantumChannel n m) :
    VonNeumannAlgebra.IsNormalMap (dualSchwarzMap Φ) :=
  VonNeumannAlgebra.isNormalMap_of_finiteDimensional _

end QuantumChannel

end Matrix
