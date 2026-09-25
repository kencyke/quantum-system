/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Algebra.VonNeumannAlgebra.Normal
public import QuantumSystem.Analysis.Matrix.Channel
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.SchwarzMap

/-!
# The dual of a quantum channel as a Schwarz map

For a quantum channel `Φ : Mₙ(ℂ) → Mₘ(ℂ)` with Kraus operators `Kᵢ`, the trace dual
`Φ* B = Σᵢ Kᵢᴴ B Kᵢ` (`Matrix.traceDual`) is, as a map `B(ℂᵐ) → B(ℂⁿ)`, a unital normal Schwarz
map. It is the Heisenberg-picture channel along which the data-processing inequality for Araki's
relative entropy (`VonNeumannAlgebra.arakiEntropy_comp_le`) applies, and it transports the normal
functional `Tr (ρ ·)` to `Tr (Φ(ρ) ·)`: `Tr (ρ Φ*(B)) = Tr (Φ(ρ) B)`.

## Main definitions

* `Matrix.QuantumChannel.dualSchwarzMap Φ : SchwarzMap 𝓑(ℂᵐ) 𝓑(ℂⁿ)` — the trace dual of `Φ`.

## Main results

* `Matrix.QuantumChannel.dualSchwarzMap_apply` — on `B ∈ Mₘ(ℂ)` it is `Matrix.traceDual Φ B`.
* `Matrix.QuantumChannel.dualSchwarzMap_one` — it is unital, as `Φ` is trace preserving.
* `Matrix.QuantumChannel.isNormalMap_dualSchwarzMap` — it is normal.
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

@[simp] lemma coe_onBoundedLinearOperators_apply (T : SchwarzMap (K →L[ℂ] K) (H →L[ℂ] H))
    (x : 𝓑(K)) : (T.onBoundedLinearOperators x : H →L[ℂ] H) = T x := rfl

end SchwarzMap

namespace Matrix

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-- A rectangular matrix `K ∈ M_{m×n}(ℂ)` as the bounded operator `ℂⁿ → ℂᵐ`. -/
noncomputable def toEuclideanL (K : Matrix m n ℂ) : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ m :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin K)

omit [DecidableEq m] in
@[simp] lemma toEuclideanL_apply (K : Matrix m n ℂ) (v : EuclideanSpace ℂ n) :
    toEuclideanL K v = WithLp.toLp 2 (K *ᵥ WithLp.ofLp v) := rfl

/-- The adjoint of `K : ℂⁿ → ℂᵐ` is `Kᴴ`. -/
lemma adjoint_toEuclideanL (K : Matrix m n ℂ) : adjoint (toEuclideanL K) = toEuclideanL Kᴴ := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  change inner ℂ (Matrix.toEuclideanLin Kᴴ x) y = inner ℂ x (Matrix.toEuclideanLin K y)
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_left]

/-- Conjugating a square matrix by a rectangular one: `Kᴴ B K` is `K† ∘ B ∘ K` as operators. -/
lemma toEuclideanCLM_conjTranspose_mul_mul (K : Matrix m n ℂ) (B : Matrix m m ℂ) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (Kᴴ * B * K) =
      adjoint (toEuclideanL K) ∘L Matrix.toEuclideanCLM (𝕜 := ℂ) B ∘L toEuclideanL K := by
  ext1 v
  rw [adjoint_toEuclideanL]
  apply (WithLp.equiv 2 _).injective
  simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]

namespace QuantumChannel

/-- The Kraus rank chosen for `Φ`. -/
noncomputable def krausRank (Φ : QuantumChannel n m) : ℕ := Φ.2.completelyPositive.choose

/-- Kraus operators chosen for `Φ`: `Φ(A) = Σᵢ Kᵢ A Kᵢᴴ` (`kraus_spec`). -/
noncomputable def kraus (Φ : QuantumChannel n m) : Fin (krausRank Φ) → Matrix m n ℂ :=
  Φ.2.completelyPositive.choose_spec.choose

omit [DecidableEq n] [DecidableEq m] in
lemma kraus_spec (Φ : QuantumChannel n m) (A : Matrix n n ℂ) :
    Φ.val A = ∑ i, (kraus Φ) i * A * ((kraus Φ) i)ᴴ :=
  Φ.2.completelyPositive.choose_spec.choose_spec A

omit [DecidableEq m] in
/-- The Kraus operators as bounded operators satisfy `Σᵢ Kᵢ† Kᵢ = 1`. -/
lemma sum_adjoint_toEuclideanL_kraus (Φ : QuantumChannel n m) :
    ∑ i, adjoint (toEuclideanL ((kraus Φ) i)) ∘L toEuclideanL ((kraus Φ) i) = 1 := by
  classical
  have h (i : Fin (krausRank Φ)) : adjoint (toEuclideanL ((kraus Φ) i)) ∘L toEuclideanL ((kraus Φ) i) =
      Matrix.toEuclideanCLM (𝕜 := ℂ) (((kraus Φ) i)ᴴ * (1 : Matrix m m ℂ) * (kraus Φ) i) := by
    rw [toEuclideanCLM_conjTranspose_mul_mul, map_one, one_def, ContinuousLinearMap.id_comp]
  simp_rw [h, Matrix.mul_one, ← map_sum, QuantumChannel.kraus_sum_eq_one Φ (kraus_spec Φ), map_one]

/-- The **dual channel** `Φ* : B(ℂᵐ) → B(ℂⁿ)`, `B ↦ Σᵢ Kᵢᴴ B Kᵢ`, as a Schwarz map
(`SchwarzMap.ofKraus`). Its values do not depend on the chosen Kraus operators: it is the trace dual
`Matrix.traceDual Φ` (`dualSchwarzMap_apply`). -/
noncomputable def dualSchwarzMap (Φ : QuantumChannel n m) :
    SchwarzMap 𝓑(EuclideanSpace ℂ m) 𝓑(EuclideanSpace ℂ n) :=
  (SchwarzMap.ofKraus _ (sum_adjoint_toEuclideanL_kraus Φ).le).onBoundedLinearOperators

omit [DecidableEq m] in
@[simp] lemma coe_dualSchwarzMap (Φ : QuantumChannel n m) (x : 𝓑(EuclideanSpace ℂ m)) :
    ((dualSchwarzMap Φ) x : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) =
      ∑ i, adjoint (toEuclideanL ((kraus Φ) i)) ∘L (x : _ →L[ℂ] _) ∘L toEuclideanL ((kraus Φ) i) :=
  rfl

/-- `Φ*(B) = Matrix.traceDual Φ B` for a matrix `B`. -/
theorem dualSchwarzMap_apply (Φ : QuantumChannel n m) (B : Matrix m m ℂ) :
    (dualSchwarzMap Φ) B.toBoundedLinearOperators = (Matrix.traceDual Φ.val B).toBoundedLinearOperators := by
  apply Subtype.ext
  rw [coe_dualSchwarzMap, coe_toBoundedLinearOperators, coe_toBoundedLinearOperators,
    Matrix.traceDual_eq_of_kraus (kraus_spec Φ), map_sum]
  simp_rw [toEuclideanCLM_conjTranspose_mul_mul]

omit [DecidableEq m] in
/-- The dual of a (trace-preserving) channel is unital. -/
theorem dualSchwarzMap_one (Φ : QuantumChannel n m) : (dualSchwarzMap Φ) 1 = 1 := by
  apply Subtype.ext
  rw [coe_dualSchwarzMap]
  change ∑ i, adjoint (toEuclideanL ((kraus Φ) i)) ∘L (1 : _ →L[ℂ] _) ∘L toEuclideanL ((kraus Φ) i) =
    (1 : EuclideanSpace ℂ n →L[ℂ] _)
  simp_rw [one_def, ContinuousLinearMap.id_comp]
  exact (sum_adjoint_toEuclideanL_kraus Φ)

omit [DecidableEq m] in
/-- The dual of a channel is normal (finite dimensions). -/
theorem isNormalMap_dualSchwarzMap (Φ : QuantumChannel n m) :
    VonNeumannAlgebra.IsNormalMap (dualSchwarzMap Φ) :=
  VonNeumannAlgebra.isNormalMap_of_finiteDimensional _

end QuantumChannel

end Matrix
