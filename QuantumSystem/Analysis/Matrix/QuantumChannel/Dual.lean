/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Algebra.VonNeumannAlgebra.Normal
public import QuantumSystem.Analysis.Matrix.QuantumChannel.Choi
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.SchwarzMap
public import QuantumSystem.ForMathlib.LinearAlgebra.Matrix.Trace

/-!
# The dual of a quantum channel as a Schwarz map

For a `2`-positive, in particular a completely positive, trace-preserving map
`Φ : Mₙ(ℂ) → Mₘ(ℂ)`, such as a quantum channel, the trace dual `Φ*` (`Matrix.traceDual`) is, as a
map `B(ℂᵐ) → B(ℂⁿ)`, a unital normal Schwarz map. It is `2`-positive by self-duality of the
positive semidefinite cone (`KPositiveMap.traceDual`), unital since `Φ` is trace preserving
(`Matrix.traceDual_one`), and hence a Schwarz map by the Kadison–Schwarz inequality
(`KPositiveMapClass.le_map_star_mul`); no Kraus representation of `Φ` is chosen. It is the
Heisenberg-picture channel along which the data-processing inequality for Araki's relative entropy
(`VonNeumannAlgebra.arakiEntropy_comp_le`) applies, and it transports the normal functional
`Tr (ρ ·)` to `Tr (Φ(ρ) ·)`: `Tr (ρ Φ*(B)) = Tr (Φ(ρ) B)` (`Matrix.trace_mul_traceDual`).

## Main definitions

* `KPositiveMap.dualSchwarzMap φ hφ : SchwarzMap 𝓑(ℂᵐ) 𝓑(ℂⁿ)` — the trace dual of a `2`-positive
  trace-preserving map `φ`; `Matrix.QuantumChannel.dualSchwarzMap Φ` for a quantum channel `Φ`.

## Main results

* `KPositiveMap.dualSchwarzMap_apply`, `Matrix.QuantumChannel.dualSchwarzMap_apply` — on
  `B ∈ Mₘ(ℂ)` it is `Matrix.traceDual Φ B`.
* `KPositiveMap.dualSchwarzMap_one`, `Matrix.QuantumChannel.dualSchwarzMap_one` — it is unital, as
  `Φ` is trace preserving.
* `KPositiveMap.isNormalMap_dualSchwarzMap`, `Matrix.QuantumChannel.isNormalMap_dualSchwarzMap` —
  it is normal.
-/

@[expose] public section

open ContinuousLinearMap
open scoped VonNeumannAlgebra ComplexOrder

namespace SchwarzMap

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A Schwarz map `B(K) → B(H)` between operator algebras, as a Schwarz map between the bundled
von Neumann algebras `𝓑(K) → 𝓑(H)`. Stated over variable Hilbert spaces, so that the order and
`⋆`-structure of `↥𝓑(K)` are found generically. -/
noncomputable def onBoundedLinearOperators (T : SchwarzMap (K →L[ℂ] K) (H →L[ℂ] H)) :
    SchwarzMap 𝓑(K) 𝓑(H) where
  toFun x := ⟨T x, VonNeumannAlgebra.mem_boundedLinearOperators _⟩
  map_add' x y := Subtype.ext (map_add T (x : K →L[ℂ] K) y)
  map_smul' c x := Subtype.ext (map_smul T c (x : K →L[ℂ] K))
  le_map_star_mul' x := by
    rw [← Subtype.coe_le_coe]
    exact T.le_map_star_mul' (x : K →L[ℂ] K)

/-- `T.onBoundedLinearOperators` acts as `T` on the underlying operators. -/
@[simp] lemma coe_onBoundedLinearOperators_apply (T : SchwarzMap (K →L[ℂ] K) (H →L[ℂ] H))
    (x : 𝓑(K)) : (T.onBoundedLinearOperators x : H →L[ℂ] H) = T x := rfl

end SchwarzMap

namespace Matrix

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-! ### The inverse of `Matrix.toEuclideanCLM`

The algebraic properties of `Matrix.toEuclideanCLM.symm` used below, stated once with the default
structure on matrices. -/

omit [DecidableEq n] in
/-- `Matrix.toEuclideanCLM⁻¹` is additive. -/
lemma toEuclideanCLM_symm_add (S T : EuclideanSpace ℂ m →L[ℂ] EuclideanSpace ℂ m) :
    (Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ)).symm (S + T) =
      (Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ)).symm S +
        (Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ)).symm T :=
  map_add _ S T

omit [DecidableEq n] in
/-- `Matrix.toEuclideanCLM⁻¹` is ℂ-linear. -/
lemma toEuclideanCLM_symm_smul (c : ℂ) (S : EuclideanSpace ℂ m →L[ℂ] EuclideanSpace ℂ m) :
    (Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ)).symm (c • S) =
      c • (Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ)).symm S :=
  map_smul _ c S

omit [DecidableEq n] in
/-- `Matrix.toEuclideanCLM⁻¹` is unital. -/
lemma toEuclideanCLM_symm_one :
    (Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ)).symm 1 = 1 :=
  map_one _

omit [DecidableEq n] in
/-- `Matrix.toEuclideanCLM⁻¹` sends `S⋆ T` to `S⋆ T` of the matrices. -/
lemma toEuclideanCLM_symm_star_mul (S T : EuclideanSpace ℂ m →L[ℂ] EuclideanSpace ℂ m) :
    (Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ)).symm (star S * T) =
      star ((Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ)).symm S) *
        (Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ)).symm T := by
  have hstar : (Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ)).symm (star S) =
      star ((Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ)).symm S) :=
    EquivLike.injective (Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ)) <| by
      rw [StarAlgEquiv.apply_symm_apply, map_star, StarAlgEquiv.apply_symm_apply]
  rw [map_mul, hstar]

omit [DecidableEq m] in
/-- `Matrix.toEuclideanCLM` sends `X⋆ Y` to `X⋆ Y` of the operators. -/
lemma toEuclideanCLM_star_mul (X Y : Matrix n n ℂ) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (star X * Y) =
      star (Matrix.toEuclideanCLM (𝕜 := ℂ) X) * Matrix.toEuclideanCLM (𝕜 := ℂ) Y := by
  classical
  rw [map_mul, map_star]

end Matrix

/-! ### The dual of a `2`-positive trace-preserving map -/

namespace KPositiveMap

open Matrix

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

open scoped Matrix.Norms.L2Operator MatrixOrder CStarAlgebra in
/-- The **dual** `φ* : B(ℂᵐ) → B(ℂⁿ)` of a `2`-positive trace-preserving map
`φ : M_n(ℂ) → M_m(ℂ)` as a Schwarz map: `T ↦ φ*(T)`, the trace dual of `φ`
(`KPositiveMap.dualSchwarzMap_apply`) read on operators through `Matrix.toEuclideanCLM`. The trace
dual is `2`-positive (`KPositiveMap.traceDual`) and unital (`Matrix.traceDual_one`), hence
satisfies the Kadison–Schwarz inequality (`KPositiveMapClass.le_map_star_mul`). -/
noncomputable def dualSchwarzMap (φ : KPositiveMap 2 (Matrix n n ℂ) (Matrix m m ℂ))
    (hφ : IsTracePreserving φ) : SchwarzMap 𝓑(EuclideanSpace ℂ m) 𝓑(EuclideanSpace ℂ n) :=
  SchwarzMap.onBoundedLinearOperators
    { toFun T := Matrix.toEuclideanCLM (𝕜 := ℂ)
        (φ.traceDual ((Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ)).symm T))
      map_add' S T := by rw [toEuclideanCLM_symm_add, map_add, map_add]
      map_smul' c T := by rw [toEuclideanCLM_symm_smul, map_smul, map_smul, RingHom.id_apply]
      le_map_star_mul' T := by
        rw [toEuclideanCLM_symm_star_mul, ← toEuclideanCLM_star_mul]
        exact OrderHomClass.mono (CompletelyPositiveMap.id (Matrix n n ℂ)).toEuclidean
          (KPositiveMapClass.le_map_star_mul φ.traceDual (traceDual_one hφ).le _) }

open scoped Matrix.Norms.L2Operator MatrixOrder CStarAlgebra in
/-- `φ*(B) = Matrix.traceDual φ B` for a matrix `B`. -/
theorem dualSchwarzMap_apply (φ : KPositiveMap 2 (Matrix n n ℂ) (Matrix m m ℂ))
    (hφ : IsTracePreserving φ) (B : Matrix m m ℂ) :
    (dualSchwarzMap φ hφ) B.toBoundedLinearOperators =
      (Matrix.traceDual φ B).toBoundedLinearOperators := by
  apply Subtype.ext
  change Matrix.toEuclideanCLM (𝕜 := ℂ)
    (φ.traceDual ((Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ)).symm (Matrix.toEuclideanCLM (𝕜 := ℂ) B))) = _
  rw [StarAlgEquiv.symm_apply_apply]
  rfl

open scoped Matrix.Norms.L2Operator MatrixOrder CStarAlgebra in
/-- The dual of a trace-preserving map is unital. -/
theorem dualSchwarzMap_one (φ : KPositiveMap 2 (Matrix n n ℂ) (Matrix m m ℂ))
    (hφ : IsTracePreserving φ) : (dualSchwarzMap φ hφ) 1 = 1 := by
  apply Subtype.ext
  change Matrix.toEuclideanCLM (𝕜 := ℂ)
    (φ.traceDual ((Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ)).symm 1)) = 1
  rw [toEuclideanCLM_symm_one, KPositiveMap.coe_traceDual, traceDual_one hφ, map_one]

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- The dual of a `2`-positive trace-preserving map is normal (finite dimensions). -/
theorem isNormalMap_dualSchwarzMap (φ : KPositiveMap 2 (Matrix n n ℂ) (Matrix m m ℂ))
    (hφ : IsTracePreserving φ) : VonNeumannAlgebra.IsNormalMap (dualSchwarzMap φ hφ) :=
  VonNeumannAlgebra.isNormalMap_of_finiteDimensional _

end KPositiveMap

namespace Matrix

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

namespace QuantumChannel

open scoped Matrix.Norms.L2Operator MatrixOrder CStarAlgebra in
/-- A quantum channel as a `2`-positive map. -/
noncomputable def toKPositiveMap₂ (Φ : QuantumChannel n m) :
    KPositiveMap 2 (Matrix n n ℂ) (Matrix m m ℂ) :=
  ⟨Φ.val.toLinearMap, Φ.val.map_cstarMatrix_nonneg' 2⟩

open scoped Matrix.Norms.L2Operator MatrixOrder CStarAlgebra in
/-- `Φ.toKPositiveMap₂` is `Φ` as a function. -/
@[simp] lemma coe_toKPositiveMap₂ (Φ : QuantumChannel n m) : ⇑Φ.toKPositiveMap₂ = Φ.val :=
  rfl

/-- The **dual channel** `Φ* : B(ℂᵐ) → B(ℂⁿ)` of a quantum channel as a Schwarz map
(`KPositiveMap.dualSchwarzMap`); no Kraus representation of `Φ` is chosen. -/
noncomputable def dualSchwarzMap (Φ : QuantumChannel n m) :
    SchwarzMap 𝓑(EuclideanSpace ℂ m) 𝓑(EuclideanSpace ℂ n) :=
  Φ.toKPositiveMap₂.dualSchwarzMap Φ.property

/-- `Φ*(B) = Matrix.traceDual Φ B` for a matrix `B`. -/
theorem dualSchwarzMap_apply (Φ : QuantumChannel n m) (B : Matrix m m ℂ) :
    (dualSchwarzMap Φ) B.toBoundedLinearOperators =
      (Matrix.traceDual Φ.val B).toBoundedLinearOperators :=
  Φ.toKPositiveMap₂.dualSchwarzMap_apply Φ.property B

/-- The dual of a (trace-preserving) channel is unital. -/
theorem dualSchwarzMap_one (Φ : QuantumChannel n m) : (dualSchwarzMap Φ) 1 = 1 :=
  Φ.toKPositiveMap₂.dualSchwarzMap_one Φ.property

/-- The dual of a channel is normal (finite dimensions). -/
theorem isNormalMap_dualSchwarzMap (Φ : QuantumChannel n m) :
    VonNeumannAlgebra.IsNormalMap (dualSchwarzMap Φ) :=
  VonNeumannAlgebra.isNormalMap_of_finiteDimensional _

end QuantumChannel

end Matrix
