/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import QuantumSystem.Analysis.CStarAlgebra.CompletelyPositiveMap.Kraus
public import QuantumSystem.Analysis.CStarAlgebra.CompletelyPositiveMap.TraceDual
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.RankOne
public import QuantumSystem.ForMathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# The Choi–Kraus theorem for bounded operators

Let `H` and `K` be finite-dimensional complex Hilbert spaces and `b` an orthonormal basis of `H`.
For a linear map `Φ : B(H) → B(K)` the following are equivalent:
1. `Φ` is completely positive;
2. `Φ` is `k`-positive (`KPositiveMap`) for some `k ≥ min(dim H, dim K)`: `id_k ⊗ Φ` is positive,
   for the single block size `k`;
3. its **Choi operator** `J_b(Φ) = Σᵢⱼ |bᵢ⟩⟨bⱼ| ⊗ Φ(|bᵢ⟩⟨bⱼ|)` on `H ⊗ K` is positive;
4. `Φ` has a Kraus representation `Φ(A) = Σₐ Tₐ A Tₐ†`.

The rank `rank J(Φ)` of `J_b(Φ)` does not depend on `b`. Every Kraus representation has at least
`rank J(Φ)` operators, with equality iff its Kraus operators are linearly independent. That the
minimum is attained is proved from Stinespring's theorem
(`QuantumSystem/Analysis/CStarAlgebra/CompletelyPositiveMap/Stinespring.lean`).

## Main definitions

* `ContinuousLinearMap.choi b Φ`: the Choi operator `J_b(Φ)`.
* `ContinuousLinearMap.choiRank Φ`: its rank `rank J(Φ)`, the same for every orthonormal basis.
* `CompletelyPositiveMap.ofKPositiveMap φ hk`: a `k`-positive map with `k ≥ min(dim H, dim K)` as a
  completely positive map.

## Main statements

* `ContinuousLinearMap.adjoint_mkL_comp_choi_comp_mkL`: the blocks of the Choi operator,
  `ιᵢ† J_b(Φ) ιⱼ = Φ(|bᵢ⟩⟨bⱼ|)` for the insertions `ιᵢ = mkL ℂ H K (bᵢ) : y ↦ bᵢ ⊗ y`.
* `ContinuousLinearMap.choi_nonneg`: the Choi operator of a `dim H`-positive map is positive.
* `ContinuousLinearMap.exists_kraus_of_choi_nonneg`: a map with positive Choi operator has a Kraus
  representation.
* `ContinuousLinearMap.choi_eq_sum_rankOne_of_kraus`: for Kraus operators `Tₐ`,
  `J_b(Φ) = Σₐ |vₐ⟩⟨vₐ|` with `vₐ = Σᵢ bᵢ ⊗ Tₐ bᵢ`.
* `ContinuousLinearMap.choiRank_le_card`,
  `ContinuousLinearMap.choiRank_eq_card_iff_linearIndependent`: every Kraus
  representation has at least `rank J(Φ)` operators, exactly that many iff they are linearly
  independent.
* `ContinuousLinearMap.choi_eq_conj_choiBasisChange`: a change of the orthonormal basis conjugates
  the Choi operator by a unitary, `J_b(Φ) = (W ⊗ 1) J_{b'}(Φ) (W ⊗ 1)†`;
  `ContinuousLinearMap.finrank_range_choi`: hence its rank does not depend on the basis.
* `ContinuousLinearMap.exists_kraus_of_kPositive`: a `k`-positive map with
  `k ≥ min(dim H, dim K)` has a Kraus representation; for `k ≥ dim K` through the trace dual.
* `CompletelyPositiveMap.exists_coe_eq_iff_choi_nonneg`: **Choi's theorem**, `Φ` is completely
  positive iff `J_b(Φ) ≥ 0`.

## Implementation notes

The Choi operator puts the input space `H` on the left, `J_b(Φ) ∈ B(H ⊗ K)`, as Choi (1975) and
the matrix Choi matrix `Matrix.choiMatrix` do. It depends on the orthonormal basis `b` only up to
the unitary conjugation `ContinuousLinearMap.choi_eq_conj_choiBasisChange`, so neither its
positivity (`CompletelyPositiveMap.exists_coe_eq_iff_choi_nonneg`) nor its rank
(`ContinuousLinearMap.finrank_range_choi`), which for completely positive maps is the minimal number
of Kraus operators, depends on `b`; `ContinuousLinearMap.choiRank` is therefore defined through the
standard orthonormal basis `stdOrthonormalBasis ℂ H`. No basis of `K` is chosen.

## References

* M.-D. Choi, *Completely positive linear maps on complex matrices*, Linear Algebra Appl. 10
  (1975) 285–290
* Watrous, *The Theory of Quantum Information*, Theorem 2.22 (with the output factor first,
  `J(Φ) = Σ Φ(Eᵢⱼ) ⊗ Eᵢⱼ`; the two orders differ by the swap of the tensor factors)
-/

@[expose] public section

open TensorProduct InnerProductSpace ContinuousLinearMap
open scoped TensorProduct InnerProductSpace InnerProduct ComplexOrder CStarAlgebra

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]
  {ι : Type*} [Fintype ι]
  {F : Type*} [FunLike F (H →L[ℂ] H) (K →L[ℂ] K)]

namespace ContinuousLinearMap

/-! ### The Choi operator -/

/-- The **Choi operator** `J_b(Φ) = Σᵢⱼ |bᵢ⟩⟨bⱼ| ⊗ Φ(|bᵢ⟩⟨bⱼ|)` on `H ⊗ K` of a map
`Φ : B(H) → B(K)`, for an orthonormal basis `b` of `H`. -/
noncomputable def choi (b : OrthonormalBasis ι ℂ H) (Φ : F) : H ⊗[ℂ] K →L[ℂ] H ⊗[ℂ] K :=
  ∑ i, ∑ j, mapL (rankOne ℂ (b i) (b j)) (Φ (rankOne ℂ (b i) (b j)))

/-- The rank `rank J(Φ)` of the Choi operator of `Φ : B(H) → B(K)`: the dimension of its range,
the same for every orthonormal basis of `H` (`ContinuousLinearMap.finrank_range_choi`). -/
noncomputable def choiRank (Φ : F) : ℕ :=
  Module.finrank ℂ (choi (stdOrthonormalBasis ℂ H) Φ).range

/-- The Choi operator through the insertions `ιᵢ = mkL ℂ H K (bᵢ) : y ↦ bᵢ ⊗ y`:
`J_b(Φ) = Σᵢⱼ ιᵢ Φ(|bᵢ⟩⟨bⱼ|) ιⱼ†` (`TensorProduct.mapL_rankOne_left`). -/
lemma choi_eq_sum_mkL (b : OrthonormalBasis ι ℂ H) (Φ : F) :
    choi b Φ = ∑ i, ∑ j,
      mkL ℂ H K (b i) ∘L Φ (rankOne ℂ (b i) (b j)) ∘L (mkL ℂ H K (b j))† := by
  simp only [choi, mapL_rankOne_left]

/-- The blocks of the Choi operator: `ιᵢ† J_b(Φ) ιⱼ = Φ(|bᵢ⟩⟨bⱼ|)`. -/
lemma adjoint_mkL_comp_choi_comp_mkL (b : OrthonormalBasis ι ℂ H) (Φ : F) (i j : ι) :
    (mkL ℂ H K (b i))† ∘L choi b Φ ∘L mkL ℂ H K (b j) = Φ (rankOne ℂ (b i) (b j)) := by
  classical
  ext y
  simp [choi, b.inner_eq_ite, adjoint_mkL_apply_tmul, apply_ite, ite_smul]

/-- The quadratic form of the Choi operator is the quadratic form of the block matrix
`(Φ(|bᵢ⟩⟨bⱼ|))ᵢⱼ` at the components `ιᵢ† z` of `z`: `⟪z, J_b(Φ) z⟫ = Σᵢⱼ ⟪ιᵢ† z, Φ(|bᵢ⟩⟨bⱼ|) ιⱼ† z⟫`. -/
lemma inner_choi_apply (b : OrthonormalBasis ι ℂ H) (Φ : F) (z : H ⊗[ℂ] K) :
    ⟪z, choi b Φ z⟫_ℂ = ∑ i, ∑ j,
      ⟪((mkL ℂ H K (b i))†) z, Φ (rankOne ℂ (b i) (b j)) (((mkL ℂ H K (b j))†) z)⟫_ℂ := by
  simp only [choi_eq_sum_mkL, sum_apply, comp_apply, inner_sum, adjoint_inner_left]

/-- The Choi operator of a `k`-positive map with `k ≥ dim H` is positive: its quadratic form is that
of the block matrix `(Φ(|bᵢ⟩⟨bⱼ|))ᵢⱼ` (`ContinuousLinearMap.inner_choi_apply`), the image under
`id_{dim H} ⊗ Φ` of the nonnegative block matrix `(|bᵢ⟩⟨bⱼ|)ᵢⱼ` (`CStarMatrix.rankOne_nonneg`). -/
lemma choi_nonneg {k : ℕ} [KPositiveMapClass F k (H →L[ℂ] H) (K →L[ℂ] K)]
    (hk : Module.finrank ℂ H ≤ k) (b : OrthonormalBasis ι ℂ H) (Φ : F) : 0 ≤ choi b Φ := by
  have hι : Fintype.card ι ≤ k := by rwa [← Module.finrank_eq_card_basis b.toBasis]
  have hQ := KPositiveMapClass.map_nonneg_of_card_le Φ hι (CStarMatrix.rankOne_nonneg b)
  refine nonneg_iff_inner_nonneg.2 fun z => ?_
  rw [inner_choi_apply]
  exact CStarMatrix.sum_inner_apply_nonneg hQ fun i => ((mkL ℂ H K (b i))†) z

/-! ### Kraus representations -/

/-- A map whose Choi operator is positive has a Kraus representation `Φ(A) = Σₐ Tₐ A Tₐ†`: writing
`J_b(Φ) = Σₐ |uₐ⟩⟨uₐ|` (`ContinuousLinearMap.isPositive_iff_eq_sum_rankOne`), the blocks are
`Φ(|bᵢ⟩⟨bⱼ|) = Σₐ |ιᵢ† uₐ⟩⟨ιⱼ† uₐ|`, so `Tₐ = Σᵢ |ιᵢ† uₐ⟩⟨bᵢ|` works on the `|bᵢ⟩⟨bⱼ|`, and by
linearity everywhere (`ContinuousLinearMap.eq_sum_inner_smul_rankOne`). -/
lemma exists_kraus_of_choi_nonneg [LinearMapClass F ℂ (H →L[ℂ] H) (K →L[ℂ] K)]
    (b : OrthonormalBasis ι ℂ H) {Φ : F} (h : 0 ≤ choi b Φ) :
    ∃ (m : ℕ) (T : Fin m → H →L[ℂ] K), ∀ A, Φ A = ∑ a, T a ∘L A ∘L (T a)† := by
  classical
  obtain ⟨m, u, hu⟩ := isPositive_iff_eq_sum_rankOne.1 (nonneg_iff_isPositive.1 h)
  set w : Fin m → ι → K := fun a i => ((mkL ℂ H K (b i))†) (u a) with hw
  set T : Fin m → H →L[ℂ] K := fun a => ∑ i, rankOne ℂ (w a i) (b i) with hTdef
  refine ⟨m, T, fun A => ?_⟩
  have hE (i j : ι) : Φ (rankOne ℂ (b i) (b j)) = ∑ a, rankOne ℂ (w a i) (w a j) := by
    rw [← adjoint_mkL_comp_choi_comp_mkL b Φ i j, hu]
    simp [comp_finsetSum, finsetSum_comp, comp_rankOne, rankOne_comp, w]
  have hT (a : Fin m) (i : ι) : T a (b i) = w a i := by
    simp [T, rankOne_apply, b.inner_eq_ite]
  have hTE (a : Fin m) (i j : ι) :
      T a ∘L rankOne ℂ (b i) (b j) ∘L (T a)† = rankOne ℂ (w a i) (w a j) := by
    rw [rankOne_comp, adjoint_adjoint, comp_rankOne, hT, hT]
  conv_lhs => rw [eq_sum_inner_smul_rankOne b A]
  conv_rhs => rw [eq_sum_inner_smul_rankOne b A]
  simp only [map_sum, map_smul, hE, comp_finsetSum, finsetSum_comp, smul_comp, comp_smul, hTE,
    Finset.smul_sum]
  exact (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans Finset.sum_comm

/-- The Choi operator of a Kraus map `Φ(A) = Σₐ Tₐ A Tₐ†` is `J_b(Φ) = Σₐ |vₐ⟩⟨vₐ|` with the
vectorised Kraus operators `vₐ = Σᵢ bᵢ ⊗ Tₐ bᵢ`. -/
lemma choi_eq_sum_rankOne_of_kraus (b : OrthonormalBasis ι ℂ H) {Φ : F} {κ : Type*} [Fintype κ]
    {T : κ → H →L[ℂ] K} (hT : ∀ A, Φ A = ∑ a, T a ∘L A ∘L (T a)†) :
    choi b Φ = ∑ a, rankOne ℂ (∑ i, b i ⊗ₜ[ℂ] T a (b i)) (∑ i, b i ⊗ₜ[ℂ] T a (b i)) := by
  have hE (i j : ι) : Φ (rankOne ℂ (b i) (b j)) = ∑ a, rankOne ℂ (T a (b i)) (T a (b j)) := by
    rw [hT]
    simp only [rankOne_comp, adjoint_adjoint, comp_rankOne]
  rw [choi_eq_sum_mkL]
  simp only [hE, comp_finsetSum, finsetSum_comp, rankOne_comp, adjoint_adjoint, comp_rankOne,
    mkL_apply_apply]
  refine ((Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans Finset.sum_comm).trans
    (Finset.sum_congr rfl fun a _ => ?_)
  rw [map_sum, Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => by rw [map_sum, sum_apply]

/-- Every Kraus representation `Φ(A) = Σₐ Tₐ A Tₐ†` has at least `rank J(Φ)` operators: the range
of `J_b(Φ) = Σₐ |vₐ⟩⟨vₐ|` is spanned by the `|κ|` vectors `vₐ`. -/
lemma choiRank_le_card {Φ : F} {κ : Type*} [Fintype κ]
    {T : κ → H →L[ℂ] K} (hT : ∀ A, Φ A = ∑ a, T a ∘L A ∘L (T a)†) :
    choiRank Φ ≤ Fintype.card κ := by
  rw [choiRank, choi_eq_sum_rankOne_of_kraus _ hT, range_sum_rankOne_self]
  exact finrank_range_le_card _

/-- A Kraus representation `Φ(A) = Σₐ Tₐ A Tₐ†` has exactly `rank J(Φ)` operators iff its Kraus
operators are linearly independent: the range of `J_b(Φ)` is spanned by the vectorised Kraus
operators `vₐ = Σᵢ bᵢ ⊗ Tₐ bᵢ`, and vectorisation `T ↦ Σᵢ bᵢ ⊗ T bᵢ` is injective. -/
lemma choiRank_eq_card_iff_linearIndependent
    {Φ : F} {κ : Type*} [Fintype κ] {T : κ → H →L[ℂ] K}
    (hT : ∀ A, Φ A = ∑ a, T a ∘L A ∘L (T a)†) :
    choiRank Φ = Fintype.card κ ↔
      LinearIndependent ℂ T := by
  classical
  set b := stdOrthonormalBasis ℂ H
  rw [choiRank, choi_eq_sum_rankOne_of_kraus b hT, range_sum_rankOne_self, eq_comm]
  refine (linearIndependent_iff_card_eq_finrank_span (R := ℂ)).symm.trans ?_
  let L : (H →L[ℂ] K) →ₗ[ℂ] H ⊗[ℂ] K := ∑ i, (mkL ℂ H K (b i) : K →ₗ[ℂ] H ⊗[ℂ] K) ∘ₗ
    (ContinuousLinearMap.apply ℂ K (b i) : (H →L[ℂ] K) →ₗ[ℂ] K)
  have hL (S : H →L[ℂ] K) : L S = ∑ i, b i ⊗ₜ[ℂ] S (b i) := by simp [L]
  have hker : LinearMap.ker L = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun S hS => ?_
    have h (j) : S (b j) = 0 := by
      have := congrArg ((mkL ℂ H K (b j))†) (hL S ▸ hS)
      simpa [map_sum, adjoint_mkL_apply_tmul, b.inner_eq_ite] using this
    exact ContinuousLinearMap.coe_injective (b.toBasis.ext fun j => by simp [h j])
  rw [← LinearMap.linearIndependent_iff L hker]
  have hv : (fun a => ∑ i, b i ⊗ₜ[ℂ] T a (b i)) = ⇑L ∘ T := funext fun a => (hL (T a)).symm
  rw [hv]

/-- **Choi's theorem**, `min(dim H, dim K)`-positivity form: a `k`-positive map
`φ : B(H) → B(K)` with `k ≥ min(dim H, dim K)` has a Kraus representation. For `k ≥ dim H` its
Choi operator is positive (`ContinuousLinearMap.choi_nonneg`). For `k ≥ dim K` its trace dual
`φ* : B(K) → B(H)` is `k`-positive (`KPositiveMap.traceDual`), hence a Kraus map
`B ↦ Σₐ Sₐ B Sₐ†`, and `φ = φ** = Σₐ Sₐ† · Sₐ` (`ContinuousLinearMap.traceDual_eq_sum_of_kraus`). -/
theorem exists_kraus_of_kPositive [LinearMapClass F ℂ (H →L[ℂ] H) (K →L[ℂ] K)] {k : ℕ}
    [KPositiveMapClass F k (H →L[ℂ] H) (K →L[ℂ] K)]
    (hk : min (Module.finrank ℂ H) (Module.finrank ℂ K) ≤ k) (φ : F) :
    ∃ (m : ℕ) (T : Fin m → H →L[ℂ] K), ∀ A, φ A = ∑ a, T a ∘L A ∘L (T a)† := by
  rcases min_le_iff.1 hk with h | h
  · exact exists_kraus_of_choi_nonneg (stdOrthonormalBasis ℂ H) (choi_nonneg h _ φ)
  · obtain ⟨m, S, hS⟩ := exists_kraus_of_choi_nonneg (stdOrthonormalBasis ℂ K)
      (choi_nonneg h _ (KPositiveMap.traceDual k φ))
    refine ⟨m, fun a => (S a)†, fun A => ?_⟩
    rw [← traceDual_traceDual φ A,
      traceDual_congr (Φ := traceDual φ) (Ψ := KPositiveMap.traceDual k φ) fun _ => rfl,
      traceDual_eq_sum_of_kraus hS]
    simp only [adjoint_adjoint]

/-! ### Basis independence of the Choi rank -/

section FinrankRangeChoi

variable {ι' : Type*} [Fintype ι']

omit [FiniteDimensional ℂ H] in
private lemma rankOne_sum_sum {κ : Type*} [Fintype κ] (e : κ → H) (c d : κ → ℂ) :
    rankOne ℂ (∑ k, c k • e k) (∑ l, d l • e l) =
      ∑ k, ∑ l, (c k * starRingEnd ℂ (d l)) • rankOne ℂ (e k) (e l) := by
  simp only [map_sum, map_smul, map_smulₛₗ, sum_apply, smul_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

/-- The Choi operator in a second orthonormal basis `b'`: expanding `|bᵢ⟩⟨bⱼ|` in `b'` inside the
linear `Φ` gives `J_b(Φ) = Σₖₗ |wₖ⟩⟨wₗ| ⊗ Φ(|b'ₖ⟩⟨b'ₗ|)` with `wₖ = Σᵢ ⟪b'ₖ, bᵢ⟫ bᵢ`. -/
private lemma choi_eq_sum_of_orthonormalBasis [LinearMapClass F ℂ (H →L[ℂ] H) (K →L[ℂ] K)]
    (b : OrthonormalBasis ι ℂ H) (b' : OrthonormalBasis ι' ℂ H) (Φ : F) :
    choi b Φ = ∑ k, ∑ l, mapL (rankOne ℂ (∑ i, ⟪b' k, b i⟫_ℂ • b i) (∑ j, ⟪b' l, b j⟫_ℂ • b j))
      (Φ (rankOne ℂ (b' k) (b' l))) := by
  have hE (i j : ι) : Φ (rankOne ℂ (b i) (b j)) =
      ∑ k, ∑ l, (⟪b' k, b i⟫_ℂ * starRingEnd ℂ ⟪b' l, b j⟫_ℂ) • Φ (rankOne ℂ (b' k) (b' l)) := by
    conv_lhs => rw [← b'.sum_repr' (b i), ← b'.sum_repr' (b j)]
    rw [rankOne_sum_sum]
    simp only [map_sum, map_smul]
  simp only [rankOne_sum_sum]
  simp only [choi, hE, ← mapLEquiv_tmul, sum_tmul, tmul_sum, ← smul_tmul', tmul_smul, map_sum,
    map_smul]
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  conv_lhs => enter [2, i, 2, k]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, k]; rw [Finset.sum_comm]

/-- The unitary `W : b'ₖ ↦ Σᵢ ⟪b'ₖ, bᵢ⟫ bᵢ` relating the Choi operators of two orthonormal bases
`b`, `b'` of `H` (`ContinuousLinearMap.choi_eq_conj_choiBasisChange`): `W = C_b ∘ C_{b'}` for the
antiunitary complex conjugations `C_b : Σᵢ cᵢ bᵢ ↦ Σᵢ c̄ᵢ bᵢ` along the two bases. -/
noncomputable def choiBasisChange (b : OrthonormalBasis ι ℂ H) (b' : OrthonormalBasis ι' ℂ H) :
    H →L[ℂ] H :=
  ∑ m, rankOne ℂ (∑ i, ⟪b' m, b i⟫_ℂ • b i) (b' m)

/-- `W b'ₖ = Σᵢ ⟪b'ₖ, bᵢ⟫ bᵢ`. -/
lemma choiBasisChange_apply (b : OrthonormalBasis ι ℂ H) (b' : OrthonormalBasis ι' ℂ H) (k : ι') :
    choiBasisChange b b' (b' k) = ∑ i, ⟪b' k, b i⟫_ℂ • b i := by
  classical
  simp [choiBasisChange, sum_apply, rankOne_apply, b'.inner_eq_ite]

/-- `W x = Σₖ ⟪b'ₖ, x⟫ W b'ₖ`. -/
lemma choiBasisChange_apply_eq_sum (b : OrthonormalBasis ι ℂ H) (b' : OrthonormalBasis ι' ℂ H)
    (x : H) : choiBasisChange b b' x = ∑ k, ⟪b' k, x⟫_ℂ • ∑ i, ⟪b' k, b i⟫_ℂ • b i := by
  simp [choiBasisChange, sum_apply, rankOne_apply, Finset.smul_sum, smul_smul, mul_comm]

/-- The vectors `W b'ₖ = Σᵢ ⟪b'ₖ, bᵢ⟫ bᵢ` are orthonormal: `⟪W b'ₖ, W b'ₗ⟫ = ⟪b'ₗ, b'ₖ⟫`, by Parseval's
identity in `b`. -/
lemma inner_choiBasisChange_apply (b : OrthonormalBasis ι ℂ H) (b' : OrthonormalBasis ι' ℂ H)
    (k l : ι') :
    ⟪choiBasisChange b b' (b' k), choiBasisChange b b' (b' l)⟫_ℂ = ⟪b' l, b' k⟫_ℂ := by
  classical
  rw [choiBasisChange_apply, choiBasisChange_apply, ← b.sum_inner_mul_inner (b' l) (b' k)]
  simp [b.inner_eq_ite, mul_comm]

/-- `W` preserves inner products: `⟪W x, W y⟫ = ⟪x, y⟫`, by Parseval's identity in `b'`. -/
lemma inner_choiBasisChange_choiBasisChange (b : OrthonormalBasis ι ℂ H)
    (b' : OrthonormalBasis ι' ℂ H) (x y : H) :
    ⟪choiBasisChange b b' x, choiBasisChange b b' y⟫_ℂ = ⟪x, y⟫_ℂ := by
  classical
  rw [choiBasisChange_apply_eq_sum, choiBasisChange_apply_eq_sum, ← b'.sum_inner_mul_inner x y]
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, ← choiBasisChange_apply,
    inner_choiBasisChange_apply, b'.inner_eq_ite]
  simp [mul_comm]

/-- `W† W = 1`: `W` is an isometry, hence unitary on the finite-dimensional `H`. -/
lemma adjoint_comp_choiBasisChange (b : OrthonormalBasis ι ℂ H) (b' : OrthonormalBasis ι' ℂ H) :
    (choiBasisChange b b')† ∘L choiBasisChange b b' = 1 := by
  ext x
  refine ext_inner_left ℂ fun y => ?_
  simp [adjoint_inner_right, inner_choiBasisChange_choiBasisChange]

/-- **Changing the orthonormal basis conjugates the Choi operator**:
`J_b(Φ) = (W ⊗ 1) J_{b'}(Φ) (W ⊗ 1)†` for the unitary `W = ContinuousLinearMap.choiBasisChange b b'`,
`W b'ₖ = Σᵢ ⟪b'ₖ, bᵢ⟫ bᵢ`: expanding `|bᵢ⟩⟨bⱼ|` in `b'` inside the linear `Φ` gives
`J_b(Φ) = Σₖₗ |W b'ₖ⟩⟨W b'ₗ| ⊗ Φ(|b'ₖ⟩⟨b'ₗ|)`. -/
lemma choi_eq_conj_choiBasisChange [LinearMapClass F ℂ (H →L[ℂ] H) (K →L[ℂ] K)]
    (b : OrthonormalBasis ι ℂ H) (b' : OrthonormalBasis ι' ℂ H) (Φ : F) :
    choi b Φ = mapL (choiBasisChange b b') 1 ∘L choi b' Φ ∘L mapL ((choiBasisChange b b')†) 1 := by
  classical
  set W := choiBasisChange b b'
  have hW (k : ι') : W (b' k) = ∑ i, ⟪b' k, b i⟫_ℂ • b i := choiBasisChange_apply b b' k
  have hconj (x y : H) : W ∘L rankOne ℂ x y ∘L (W†) = rankOne ℂ (W x) (W y) := by
    ext z
    simp [rankOne_apply, adjoint_inner_right]
  rw [choi_eq_sum_of_orthonormalBasis b b' Φ, choi]
  simp only [comp_finsetSum, finsetSum_comp, ← mapL_comp, one_def, id_comp, comp_id, hconj, hW]

/-- Conjugation by `W ⊗ 1` does not increase the rank of the Choi operator. -/
private lemma finrank_range_choi_le [LinearMapClass F ℂ (H →L[ℂ] H) (K →L[ℂ] K)]
    (b : OrthonormalBasis ι ℂ H) (b' : OrthonormalBasis ι' ℂ H) (Φ : F) :
    Module.finrank ℂ (choi b Φ).range ≤ Module.finrank ℂ (choi b' Φ).range := by
  rw [choi_eq_conj_choiBasisChange b b' Φ]
  set A := mapL (choiBasisChange b b') (1 : K →L[ℂ] K)
  set B := mapL ((choiBasisChange b b')†) (1 : K →L[ℂ] K)
  have hle : (A ∘L choi b' Φ ∘L B).range ≤ (choi b' Φ).range.map A.toLinearMap := by
    rintro _ ⟨z, rfl⟩
    exact ⟨_, ⟨_, rfl⟩, rfl⟩
  exact (Submodule.finrank_mono hle).trans (Submodule.finrank_map_le _ _)

/-- **The rank of the Choi operator does not depend on the orthonormal basis**, for every linear
`Φ : B(H) → B(K)`: `rank J_b(Φ) = rank J(Φ)`. A change of basis conjugates `J_b(Φ)` by the unitary
`W ⊗ 1` (`ContinuousLinearMap.choi_eq_conj_choiBasisChange`), which bounds each rank by the
other. -/
lemma finrank_range_choi [LinearMapClass F ℂ (H →L[ℂ] H) (K →L[ℂ] K)] (b : OrthonormalBasis ι ℂ H)
    (Φ : F) : Module.finrank ℂ (choi b Φ).range = choiRank Φ :=
  (finrank_range_choi_le b _ Φ).antisymm (finrank_range_choi_le _ b Φ)

end FinrankRangeChoi

end ContinuousLinearMap

namespace CompletelyPositiveMap

/-- **Choi's theorem**, `min(dim H, dim K)`-positivity form: a `k`-positive map
`φ : B(H) → B(K)` with `k ≥ min(dim H, dim K)`, i.e. one for which `id_k ⊗ φ` is positive for the
single block size `k`, is completely positive: it is a Kraus map
(`ContinuousLinearMap.exists_kraus_of_kPositive`). Conversely a completely positive map is
`k`-positive for every `k` (`CompletelyPositiveMapClass.instKPositiveMapClass`). -/
noncomputable def ofKPositiveMap [LinearMapClass F ℂ (H →L[ℂ] H) (K →L[ℂ] K)] {k : ℕ}
    [KPositiveMapClass F k (H →L[ℂ] H) (K →L[ℂ] K)] (φ : F)
    (hk : min (Module.finrank ℂ H) (Module.finrank ℂ K) ≤ k) : (H →L[ℂ] H) →CP (K →L[ℂ] K) where
  toLinearMap := (φ : (H →L[ℂ] H) →ₗ[ℂ] (K →L[ℂ] K))
  map_cstarMatrix_nonneg' n M hM := by
    obtain ⟨m, T, hT⟩ := exists_kraus_of_kPositive hk φ
    convert (ofKraus T).map_cstarMatrix_nonneg' n M hM using 2
    exact funext hT

/-- The completely positive map `CompletelyPositiveMap.ofKPositiveMap φ hk` is `φ` as a
function. -/
@[simp] lemma coe_ofKPositiveMap [LinearMapClass F ℂ (H →L[ℂ] H) (K →L[ℂ] K)] {k : ℕ}
    [KPositiveMapClass F k (H →L[ℂ] H) (K →L[ℂ] K)] (φ : F)
    (hk : min (Module.finrank ℂ H) (Module.finrank ℂ K) ≤ k) : ⇑(ofKPositiveMap φ hk) = φ :=
  rfl

/-- **Choi's theorem**: a linear map `Φ : B(H) → B(K)` is completely positive, i.e. it is the
linear map of some `φ : B(H) →CP B(K)`, iff its Choi operator `J_b(Φ)` is positive, for any
orthonormal basis `b` of `H` (the positivity of `J_b(Φ)` does not depend on `b`, as the bases are
related by the unitary conjugation `ContinuousLinearMap.choi_eq_conj_choiBasisChange`). -/
theorem exists_coe_eq_iff_choi_nonneg (b : OrthonormalBasis ι ℂ H)
    (Φ : (H →L[ℂ] H) →ₗ[ℂ] (K →L[ℂ] K)) :
    (∃ φ : (H →L[ℂ] H) →CP (K →L[ℂ] K), (φ : (H →L[ℂ] H) →ₗ[ℂ] (K →L[ℂ] K)) = Φ) ↔
      0 ≤ ContinuousLinearMap.choi b Φ := by
  refine ⟨fun ⟨φ, hφ⟩ => hφ ▸ ContinuousLinearMap.choi_nonneg le_rfl b φ, fun h => ?_⟩
  obtain ⟨m, T, hT⟩ := ContinuousLinearMap.exists_kraus_of_choi_nonneg b h
  exact ⟨ofKraus T, LinearMap.ext fun A => (hT A).symm⟩

end CompletelyPositiveMap
