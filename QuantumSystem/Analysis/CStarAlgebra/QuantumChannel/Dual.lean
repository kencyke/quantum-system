/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.Algebra.VonNeumannAlgebra.Normal
public import QuantumSystem.Analysis.CStarAlgebra.KadisonSchwarz
public import QuantumSystem.Analysis.CStarAlgebra.QuantumChannel.Basic
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.Stinespring
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.LinearMap
public import QuantumSystem.Notation

/-!
# The trace dual of a completely positive map

Let `H` and `K` be finite-dimensional complex Hilbert spaces. The trace dual
`φ* = ContinuousLinearMap.traceDual φ : B(K) → B(H)` of a linear map `φ : B(H) → B(K)`, defined by
`tr(φ(A) B) = tr(A φ*(B))`, is `k`-positive whenever `φ` is (`KPositiveMap.traceDual`), and
completely positive whenever `φ` is (`CompletelyPositiveMap.traceDual`). This is the
**self-duality of the positive cone** for the trace pairing
(`CStarMatrix.sum_trace_comp_nonneg`): the quadratic form of `id_k ⊗ φ*` at `ξ ∈ Hᵏ` is the
pairing `Σᵢⱼ tr(Qⱼᵢ Mᵢⱼ)` of the nonnegative block matrices `Q = (φ(|ξᵢ⟩⟨ξⱼ|))ᵢⱼ` and `M`.

The trace dual of a `2`-positive map `φ` that is trace non-increasing on positive operators,
equivalently `φ*(1) ≤ 1` (`ContinuousLinearMap.traceDual_one_le_one_iff`), is therefore a Schwarz
map (`KPositiveMapClass.toSchwarzMap` applied to `KPositiveMap.traceDual 2 φ`), unital when `φ` is
trace preserving (`isTracePreserving_iff_traceDual_one`). Transported to the bundled von Neumann
algebras by `SchwarzMap.onBoundedLinearOperators`, it is normal
(`VonNeumannAlgebra.isNormalMap_of_finiteDimensional`). For a quantum channel it is the Heisenberg
picture of `Φ`, to which the data-processing inequality for Araki's relative entropy
(`VonNeumannAlgebra.arakiEntropy_comp_le`) applies
(`QuantumChannel.umegakiEntropy_comp_traceDual_le`).
No Kraus representation is chosen.

## Main definitions

* `KPositiveMap.traceDual k φ`, `CompletelyPositiveMap.traceDual φ`: the trace dual of a
  `k`-positive, respectively completely positive, map, again `k`-positive, respectively completely
  positive.
* `SchwarzMap.onBoundedLinearOperators T : SchwarzMap 𝓑(K) 𝓑(H)` — a Schwarz map `B(K) → B(H)`
  between the bundled von Neumann algebras.

## Main statements

* `CStarMatrix.sum_trace_comp_nonneg`: `0 ≤ Σᵢⱼ tr(Qⱼᵢ Mᵢⱼ)` for nonnegative block operator
  matrices `Q` and `M`.
* `ContinuousLinearMap.traceDual_one_le_one_iff`: `φ*(1) ≤ 1` iff `φ` is trace non-increasing on
  positive operators.
-/

@[expose] public section

open ContinuousLinearMap InnerProductSpace
open scoped InnerProductSpace ComplexOrder CStarAlgebra VonNeumannAlgebra

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

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]

/-! ### Self-duality of the positive cone -/

namespace CStarMatrix

/-- **Self-duality of the positive cone** for block operator matrices: for nonnegative
`Q, M ∈ M_n(B(K))`, the trace of `QM` on `Kⁿ` is nonnegative, `0 ≤ Σᵢⱼ tr(Qⱼᵢ Mᵢⱼ)`. Writing
`Q = R⋆ R`, the sum is `Σₗ tr((R M R⋆)ₗₗ)` by cyclicity of the trace, a sum of traces of the
nonnegative diagonal entries of the nonnegative matrix `R M R⋆`. -/
theorem sum_trace_comp_nonneg {n : Type*} [Fintype n] {Q M : CStarMatrix n n (K →L[ℂ] K)}
    (hQ : 0 ≤ Q) (hM : 0 ≤ M) :
    0 ≤ ∑ i, ∑ j, Tr (Q j i ∘L M i j) := by
  obtain ⟨P, hP, rfl⟩ := (StarOrderedRing.le_iff 0 Q).mp hQ
  clear hQ
  rw [zero_add]
  induction hP using AddSubmonoid.closure_induction with
  | mem _ h =>
    obtain ⟨R, rfl⟩ := h
    have hRMR : 0 ≤ R * M * star R := star_right_conjugate_nonneg hM R
    have key : ∑ i, ∑ j, Tr ((star R * R) j i ∘L M i j) =
        ∑ l, Tr ((R * M * star R) l l) := by
      simp only [mul_apply, star_apply, Finset.sum_mul, mul_def, star_eq_adjoint, finsetSum_comp,
        toLinearMap_sum, map_sum]
      have h (i j l : n) : Tr ((adjoint (R l j) ∘L R l i) ∘L M i j) =
          Tr ((R l i ∘L M i j) ∘L adjoint (R l j)) := by
        rw [comp_assoc, trace_comp_comm']
      simp only [h]
      rw [Finset.sum_comm]
      exact (Finset.sum_congr rfl fun j _ => Finset.sum_comm).trans Finset.sum_comm
    rw [key]
    refine Finset.sum_nonneg fun l _ => ?_
    exact LinearMap.IsPositive.trace_nonneg ((isPositive_toLinearMap_iff _).2
      (nonneg_iff_isPositive.1 (CStarMatrix.diag_nonneg hRMR)))
  | zero => simp [zero_apply]
  | add P P' _ _ hP hP' =>
    simpa [add_apply, add_comp, toLinearMap_add, map_add, Finset.sum_add_distrib] using
      add_nonneg hP hP'

end CStarMatrix

/-! ### The trace dual of a positive map -/

variable {F : Type*} [FunLike F (H →L[ℂ] H) (K →L[ℂ] K)]
  [LinearMapClass F ℂ (H →L[ℂ] H) (K →L[ℂ] K)]

namespace KPositiveMap

/-- The trace dual `φ* : B(K) → B(H)` of a `k`-positive map `φ : B(H) → B(K)`, characterised by
`tr(φ(A) B) = tr(A φ*(B))` (`ContinuousLinearMap.trace_comp_traceDual`), is `k`-positive: the
quadratic form of `id_k ⊗ φ*` at `M` and `ξ ∈ Hᵏ` is
`Σᵢⱼ ⟪ξᵢ, φ*(Mᵢⱼ) ξⱼ⟫ = Σᵢⱼ tr(φ(|ξⱼ⟩⟨ξᵢ|) Mᵢⱼ)` (`ContinuousLinearMap.inner_traceDual_apply`),
nonnegative by self-duality of the positive cone (`CStarMatrix.sum_trace_comp_nonneg`) since the
block matrix `(|ξᵢ⟩⟨ξⱼ|)` is nonnegative (`CStarMatrix.rankOne_nonneg`). The block size `k` is
explicit, since `φ` may be `k`-positive for several `k`. -/
noncomputable def traceDual (k : ℕ) [KPositiveMapClass F k (H →L[ℂ] H) (K →L[ℂ] K)] (φ : F) :
    KPositiveMap k (K →L[ℂ] K) (H →L[ℂ] H) where
  toLinearMap := ContinuousLinearMap.traceDual φ
  map_cstarMatrix_nonneg' M hM := by
    rw [CStarMatrix.nonneg_iff_sum_inner_apply_nonneg]
    intro ξ
    have hQ := KPositiveMapClass.map_cstarMatrix_nonneg' φ _ (CStarMatrix.rankOne_nonneg ξ)
    refine (CStarMatrix.sum_trace_comp_nonneg hQ hM).trans_eq ?_
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    change _ = ⟪ξ i, ContinuousLinearMap.traceDual φ (M i j) (ξ j)⟫_ℂ
    rw [inner_traceDual_apply]
    rfl

/-- The `k`-positive map `KPositiveMap.traceDual k φ` is the trace dual of `φ` as a function. -/
@[simp] lemma coe_traceDual (k : ℕ) [KPositiveMapClass F k (H →L[ℂ] H) (K →L[ℂ] K)] (φ : F) :
    ⇑(traceDual k φ) = ContinuousLinearMap.traceDual φ :=
  rfl

end KPositiveMap

namespace CompletelyPositiveMap

/-- The trace dual `φ* : B(K) → B(H)` of a completely positive map `φ : B(H) → B(K)`,
characterised by `tr(φ(A) B) = tr(A φ*(B))` (`ContinuousLinearMap.trace_comp_traceDual`), is
completely positive: it is `k`-positive for every `k` (`KPositiveMap.traceDual`). -/
noncomputable def traceDual [CompletelyPositiveMapClass F (H →L[ℂ] H) (K →L[ℂ] K)] (φ : F) :
    (K →L[ℂ] K) →CP (H →L[ℂ] H) where
  toLinearMap := ContinuousLinearMap.traceDual φ
  map_cstarMatrix_nonneg' k := (KPositiveMap.traceDual k φ).map_cstarMatrix_nonneg'

/-- The completely positive map `CompletelyPositiveMap.traceDual φ` is the trace dual of `φ` as a
function. -/
@[simp] lemma coe_traceDual [CompletelyPositiveMapClass F (H →L[ℂ] H) (K →L[ℂ] K)] (φ : F) :
    ⇑(traceDual φ) = ContinuousLinearMap.traceDual φ :=
  rfl

end CompletelyPositiveMap

/-! ### The dual of a `2`-positive trace non-increasing map -/

namespace ContinuousLinearMap

/-- The trace dual of a positive map is sub-unital, `φ*(1) ≤ 1`, iff the map is **trace
non-increasing** on positive operators, `Re tr φ(A) ≤ Re tr A`: `tr φ(A) = tr(A φ*(1))`
(`ContinuousLinearMap.trace_comp_traceDual`), and the positive cone is self-dual, tested here on
the rank-one operators `|x⟩⟨x|`. -/
theorem traceDual_one_le_one_iff [OrderHomClass F (H →L[ℂ] H) (K →L[ℂ] K)] (φ : F) :
    traceDual φ 1 ≤ 1 ↔ ∀ A : H →L[ℂ] H, 0 ≤ A →
      (Tr (φ A)).re ≤ (Tr A).re := by
  have key (A : H →L[ℂ] H) :
      Tr (φ A) = Tr (A ∘L traceDual φ 1) := by
    rw [← trace_comp_traceDual, ← mul_def, mul_one]
  refine ⟨fun h A hA => ?_, fun h => ?_⟩
  · have h' := (Complex.nonneg_iff.1 (trace_comp_nonneg hA (sub_nonneg.2 h))).1
    rwa [comp_sub, ← mul_def A 1, mul_one, toLinearMap_sub, map_sub, ← key, Complex.sub_re,
      sub_nonneg] at h'
  · rw [← sub_nonneg, nonneg_iff_inner_nonneg]
    intro x
    have hP : 0 ≤ rankOne ℂ x x := nonneg_iff_isPositive.2 (isPositive_rankOne_self x)
    have h1 : ⟪x, (1 - traceDual φ 1) x⟫_ℂ =
        Tr (rankOne ℂ x x) - Tr (φ (rankOne ℂ x x)) := by
      rw [sub_apply, one_apply_eq_self, inner_sub_right, inner_traceDual_apply, ← mul_def,
        mul_one, trace_rankOne]
    have h₁ := Complex.nonneg_iff.1 ((nonneg_iff_isPositive.1 hP).toLinearMap.trace_nonneg)
    have h₂ := Complex.nonneg_iff.1
      ((nonneg_iff_isPositive.1 (map_nonneg φ hP)).toLinearMap.trace_nonneg)
    rw [h1, Complex.nonneg_iff, Complex.sub_re, Complex.sub_im, ← h₁.2, ← h₂.2, sub_self]
    exact ⟨sub_nonneg.2 (h _ hP), rfl⟩

end ContinuousLinearMap

