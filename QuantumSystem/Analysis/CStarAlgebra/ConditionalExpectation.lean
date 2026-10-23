/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.ContractiveProjection
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.SchwarzMap
public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.Stinespring
import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.KPositiveMap
import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.UnitalContraction

/-!
# Contractive projections onto C⋆-subalgebras are conditional expectations

Let `φ` be a linear projection of a C⋆-algebra `A` onto a ⋆-subalgebra `S`
(`LinearMap.IsProj S.toSubmodule φ`), with `‖φ x‖ ≤ ‖x‖` for every `x`. Besides being `S`-linear
on both sides (`LinearMap.IsProj.map_mul_left_of_norm_apply_le`,
`LinearMap.IsProj.map_mul_right_of_norm_apply_le`), `φ` is positive and satisfies the
Kadison–Schwarz inequality; these three properties are Tomiyama's theorem
(`LinearMap.IsProj.tomiyama_of_norm_apply_le`). Moreover, `φ` is completely positive.

* **Positivity.** The map `Ê : λ + x ↦ λ + φ(x)` from `A⁺¹` to `S⁺¹` is unital, and contractive:
  `‖(λ + φ(x)) s‖ = ‖φ((λ + x) s)‖ ≤ ‖λ + x‖ ‖s‖` for `s ∈ S` by right `S`-linearity. A unital
  contraction is positive (`map_nonneg_of_map_one_of_norm_apply_le`), and so is `φ`; in particular
  `φ` preserves the involution.
* **The Kadison–Schwarz inequality** `φ(x)⋆ φ(x) ≤ φ(x⋆ x)`: by `S`-linearity,
  `φ((x - φ x)⋆ (x - φ x)) = φ(x⋆ x) - φ(x)⋆ φ(x)`. So `φ` is a Schwarz map whose multiplicative
  domain contains `S`, and the Choi–Effros product on its range (`ChoiEffros`) is the product of `A`
  (`ChoiEffros.val_mul_of_isProj`).
* **Complete positivity.** For `M = Y⋆ Y ≥ 0` in `Mₖ(A)` and `c ∈ Sᵏ`,
  `Σᵢⱼ cᵢ⋆ φ(Mᵢⱼ) cⱼ = φ(Σₘ zₘ⋆ zₘ) ≥ 0` with `zₘ = Σⱼ Yₘⱼ cⱼ`. A self-adjoint matrix `T` with
  entries in `S` and this property is positive: the columns of `N = T⁻`, whose entries lie in `S`,
  give the diagonal of `N T N = -N³`, so `N³ ≥ 0` has zero diagonal and vanishes, and `N = 0`.

## Main definitions

* `LinearMap.IsProj.toPositiveLinearMap`, `LinearMap.IsProj.toSchwarzMap`,
  `LinearMap.IsProj.toCompletelyPositiveMap` — a contractive projection onto a C⋆-subalgebra as a
  positive, Schwarz, and completely positive map.

## Main results

* `LinearMap.IsProj.tomiyama_of_norm_apply_le` — **Tomiyama's theorem**: such `φ` is order
  preserving, `S`-bimodular, and satisfies the Kadison–Schwarz inequality.
* `LinearMap.IsProj.map_nonneg_of_norm_apply_le` — **a contractive projection onto a
  C⋆-subalgebra is positive**; `LinearMap.IsProj.map_star_of_norm_apply_le` — it preserves `star`.
* `LinearMap.IsProj.star_map_mul_map_le_of_norm_apply_le` — **the Kadison–Schwarz inequality**;
  `LinearMap.IsProj.le_multiplicativeDomain_of_norm_apply_le` — `S` lies in the multiplicative
  domain.
* `LinearMap.IsProj.map_cstarMatrix_nonneg_of_norm_apply_le` — **a contractive projection onto a
  C⋆-subalgebra is completely positive**.

## References

* J. Tomiyama, *On the projection of norm one in W⋆-algebras*, Proc. Japan Acad. 33 (1957),
  608–612, Theorem 1.
-/

@[expose] public section

open scoped CStarAlgebra

section Matrix

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {n : Type*} [Fintype n]

/-- The matrices over `A` with entries in `S`. -/
private def matrixSubalgebra (n : Type*) [Fintype n] (S : NonUnitalStarSubalgebra ℂ A) :
    NonUnitalStarSubalgebra ℂ (CStarMatrix n n A) where
  carrier := {M | ∀ i j, M i j ∈ S}
  add_mem' hM hN i j := add_mem (hM i j) (hN i j)
  zero_mem' _ _ := zero_mem S
  mul_mem' {M N} hM hN i j := by
    change (M * N) i j ∈ S
    rw [CStarMatrix.mul_apply]
    exact sum_mem fun l _ => mul_mem (hM i l) (hN l j)
  smul_mem' r _ hM i j := SMulMemClass.smul_mem r (hM i j)
  star_mem' {M} hM i j := by
    rw [CStarMatrix.star_apply]
    exact star_mem (hM j i)

private instance {S : NonUnitalStarSubalgebra ℂ A} [hS : IsClosed (S : Set A)] :
    IsClosed (matrixSubalgebra n S : Set (CStarMatrix n n A)) := by
  change IsClosed {M : CStarMatrix n n A | ∀ i j, M i j ∈ S}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    hS.preimage ((continuous_apply j).comp (continuous_apply i))

/-- A positive matrix with zero diagonal is zero: `X = Y⋆ Y` has `X i i = Σₖ (Y k i)⋆ Y k i`. -/
private lemma eq_zero_of_nonneg_of_diag_eq_zero {X : CStarMatrix n n A} (hX : 0 ≤ X)
    (hd : ∀ i, X i i = 0) : X = 0 := by
  obtain ⟨Y, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hX
  have hY : Y = 0 := CStarMatrix.ext fun k i => by
    have h := hd i
    rw [CStarMatrix.mul_apply] at h
    simp only [CStarMatrix.star_apply] at h
    have := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => star_mul_self_nonneg (Y k i)).mp h k
      (Finset.mem_univ k)
    exact star_mul_self_eq_zero.mp this
  rw [hY, mul_zero]

/-- A self-adjoint matrix `T` over `A` with entries in a closed ⋆-subalgebra `S` is positive if
`Σᵢⱼ cᵢ⋆ Tᵢⱼ cⱼ ≥ 0` for every `c` with entries in `S`. For `N = T⁻`, whose entries lie in `S`, the
columns of `N` give the diagonal of `N T N = -N³`, so `N³ ≥ 0` has zero diagonal; hence `N³ = 0`,
`N = 0` and `T = T⁺`. -/
private lemma nonneg_of_forall_sum_star_mul_mul_nonneg {S : NonUnitalStarSubalgebra ℂ A}
    [IsClosed (S : Set A)] {T : CStarMatrix n n A} (hT : IsSelfAdjoint T)
    (hTS : ∀ i j, T i j ∈ S)
    (h : ∀ c : n → A, (∀ i, c i ∈ S) → 0 ≤ ∑ i, ∑ j, star (c i) * T i j * c j) : 0 ≤ T := by
  set N := T⁻
  have hN : 0 ≤ N := CFC.negPart_nonneg T
  have hNS : N ∈ matrixSubalgebra n S := by
    change T⁻ ∈ _
    rw [CFC.negPart_def]
    exact cfcₙ_mem _ (show T ∈ matrixSubalgebra n S from hTS)
  have hNTN : star N * T * N = -(N * N * N) := by
    conv_lhs => rw [← CFC.posPart_sub_negPart T hT]
    rw [hN.isSelfAdjoint.star_eq, mul_sub, sub_mul, CFC.negPart_mul_posPart, zero_mul, zero_sub]
  have hX : 0 ≤ N * N * N := by
    simpa [hN.isSelfAdjoint.star_eq, mul_assoc] using star_left_conjugate_nonneg hN N
  have hdiag (i : n) : (N * N * N) i i = 0 := by
    refine le_antisymm ?_ (CStarMatrix.diag_nonneg hX)
    have hc := h (fun j => N j i) fun j => hNS j i
    have e : (star N * T * N) i i = ∑ j, ∑ l, star (N j i) * T j l * N l i := by
      simp only [CStarMatrix.mul_apply, CStarMatrix.star_apply, Finset.sum_mul]
      exact Finset.sum_comm
    rw [← e, hNTN] at hc
    exact neg_nonneg.mp hc
  have hN3 : N * N * N = 0 := eq_zero_of_nonneg_of_diag_eq_zero hX hdiag
  have hN0 : N = 0 := by
    have hNs : star N = N := hN.isSelfAdjoint.star_eq
    have h₁ : ‖N * N‖ = ‖N‖ * ‖N‖ := by rw [← CStarRing.norm_star_mul_self, hNs]
    have h₂ : ‖(N * N) * (N * N)‖ = ‖N * N‖ * ‖N * N‖ := by
      rw [← CStarRing.norm_star_mul_self (x := N * N), star_mul, hNs]
    have h₃ : (N * N) * (N * N) = 0 := by
      rw [show (N * N) * (N * N) = (N * N * N) * N by simp only [mul_assoc], hN3, zero_mul]
    rw [h₃, norm_zero, h₁] at h₂
    exact norm_eq_zero.mp (mul_self_eq_zero.mp (mul_self_eq_zero.mp h₂.symm))
  rw [← CFC.posPart_sub_negPart T hT]
  change 0 ≤ T⁺ - N
  rw [hN0, sub_zero]
  exact CFC.posPart_nonneg T

omit [PartialOrder A] [StarOrderedRing A] [Fintype n] in
/-- A self-adjoint matrix stays self-adjoint under an entrywise map commuting with `star`. -/
private lemma isSelfAdjoint_cstarMatrix_map {M : CStarMatrix n n A} (hM : IsSelfAdjoint M) {f : A → A}
    (hf : ∀ x, f (star x) = star (f x)) : IsSelfAdjoint (M.map f) :=
  isSelfAdjoint_iff.mpr <| CStarMatrix.ext fun i j => by
    rw [CStarMatrix.star_apply, CStarMatrix.map_apply, CStarMatrix.map_apply, ← hf,
      ← CStarMatrix.star_apply, hM.star_eq]

omit [PartialOrder A] [StarOrderedRing A] in
/-- `Σᵢⱼ cᵢ⋆ (Y⋆ Y)ᵢⱼ cⱼ = Σₘ zₘ⋆ zₘ` with `zₘ = Σⱼ Yₘⱼ cⱼ`. -/
private lemma sum_star_mul_star_mul_self_mul (Y : CStarMatrix n n A) (c : n → A) :
    ∑ i, ∑ j, star (c i) * (star Y * Y) i j * c j =
      ∑ m, star (∑ j, Y m j * c j) * ∑ j, Y m j * c j := by
  simp only [CStarMatrix.mul_apply, CStarMatrix.star_apply, star_sum, star_mul, Finset.sum_mul,
    Finset.mul_sum, mul_assoc]
  refine (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_comm)

end Matrix

namespace LinearMap.IsProj

variable {F A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [FunLike F A A] [LinearMapClass F ℂ A A] {φ : F} {S : NonUnitalStarSubalgebra ℂ A}
  (hφ : IsProj S.toSubmodule φ) (hn : ∀ x, ‖φ x‖ ≤ ‖x‖)

include hφ hn

/-- **A contractive projection onto a C⋆-subalgebra is positive.** The map
`Ê : λ + x ↦ λ + φ(x)` from `A⁺¹` to `S⁺¹` is unital, and contractive because
`‖(λ + φ(x)) s‖ = ‖φ((λ + x) s)‖ ≤ ‖λ + x‖ ‖s‖` for `s ∈ S` by right `S`-linearity; a unital
contraction is positive (`map_nonneg_of_map_one_of_norm_apply_le`). -/
theorem map_nonneg_of_norm_apply_le {a : A} (ha : 0 ≤ a) : 0 ≤ φ a := by
  have := hφ.isClosed (AddMonoidHomClass.continuous_of_bound φ 1 fun x => by simpa using hn x)
  let : PartialOrder S := CStarAlgebra.spectralOrder S
  let : StarOrderedRing S := CStarAlgebra.spectralOrderedRing S
  let ψ : A →ₗ[ℂ] S := (φ : A →ₗ[ℂ] A).codRestrict S.toSubmodule hφ.map_mem
  have hψ (x : A) : (ψ x : A) = φ x := rfl
  let Ê : A⁺¹ →ₗ[ℂ] S⁺¹ :=
    { toFun := fun y => Unitization.inl y.fst + (ψ y.snd : S⁺¹)
      map_add' := fun y z => by
        simp only [Unitization.fst_add, Unitization.snd_add, map_add, Unitization.inl_add,
          Unitization.inr_add]
        abel
      map_smul' := fun r y => by
        simp only [Unitization.fst_smul, Unitization.snd_smul, map_smul, Unitization.inl_smul,
          Unitization.inr_smul, RingHom.id_apply, smul_add] }
  have hÊ (y : A⁺¹) : Ê y = Unitization.inl y.fst + (ψ y.snd : S⁺¹) := rfl
  have h₁ : Ê 1 = 1 := by simp [hÊ]
  have hnorm (y : A⁺¹) : ‖Ê y‖ ≤ ‖y‖ := by
    rw [Unitization.norm_eq_sup (Ê y), Unitization.norm_eq_sup y]
    simp only [hÊ, Unitization.fst_add, Unitization.snd_add, Unitization.fst_inl,
      Unitization.snd_inl, Unitization.fst_inr, Unitization.snd_inr, add_zero, zero_add]
    refine sup_le_sup_left (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun s => ?_) _
    have hs : (s : A) ∈ S := s.2
    have e₁ : (((algebraMap ℂ (S →L[ℂ] S) y.fst + ContinuousLinearMap.mul ℂ S (ψ y.snd)) s : S) :
        A) = φ ((algebraMap ℂ (A →L[ℂ] A) y.fst + ContinuousLinearMap.mul ℂ A y.snd) s) := by
      simp [Algebra.algebraMap_eq_smul_one, hψ, map_add, map_smul,
        hφ.map_id _ hs, map_mul_right_of_norm_apply_le hφ hn hs]
    calc ‖(algebraMap ℂ (S →L[ℂ] S) y.fst + ContinuousLinearMap.mul ℂ S (ψ y.snd)) s‖
        = ‖φ ((algebraMap ℂ (A →L[ℂ] A) y.fst + ContinuousLinearMap.mul ℂ A y.snd) s)‖ := by
          rw [← e₁]; rfl
      _ ≤ ‖(algebraMap ℂ (A →L[ℂ] A) y.fst + ContinuousLinearMap.mul ℂ A y.snd) s‖ := hn _
      _ ≤ ‖algebraMap ℂ (A →L[ℂ] A) y.fst + ContinuousLinearMap.mul ℂ A y.snd‖ * ‖(s : A)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = _ := rfl
  have h := map_nonneg_of_map_one_of_norm_apply_le Ê h₁ hnorm
    (Unitization.inr_nonneg_iff.mpr ha)
  rw [show Ê a = (ψ a : S⁺¹) by simp [hÊ], Unitization.inr_nonneg_iff,
    CStarAlgebra.nonneg_iff_eq_star_mul_self] at h
  obtain ⟨y, hy⟩ := h
  rw [← hψ, hy]
  exact star_mul_self_nonneg (y : A)

/-- A contractive projection onto a C⋆-subalgebra, as a positive linear map. -/
noncomputable def toPositiveLinearMap : A →ₚ[ℂ] A :=
  PositiveLinearMap.mk₀ (φ : A →ₗ[ℂ] A) fun _ ha => map_nonneg_of_norm_apply_le hφ hn ha

@[simp]
lemma toPositiveLinearMap_apply (x : A) : toPositiveLinearMap hφ hn x = φ x :=
  rfl

omit [PartialOrder A] [StarOrderedRing A] in
/-- A contractive projection onto a C⋆-subalgebra preserves the involution, being positive. -/
lemma map_star_of_norm_apply_le (x : A) : φ (star x) = star (φ x) := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  exact map_star (toPositiveLinearMap hφ hn) x

/-- **The Kadison–Schwarz inequality for a contractive projection onto a C⋆-subalgebra.**
`φ(x)⋆ φ(x) ≤ φ(x⋆ x)`: `S`-linearity turns `0 ≤ φ((x - φ x)⋆ (x - φ x))` into
`0 ≤ φ(x⋆ x) - φ(x)⋆ φ(x)`. -/
theorem star_map_mul_map_le_of_norm_apply_le (x : A) :
    star (φ x) * φ x ≤ φ (star x * x) := by
  have hy : φ x ∈ S := hφ.map_mem x
  have h := map_nonneg_of_norm_apply_le hφ hn (star_mul_self_nonneg (x - φ x))
  have e : φ (star (x - φ x) * (x - φ x)) =
      φ (star x * x) - star (φ x) * φ x := by
    rw [star_sub, sub_mul, mul_sub, mul_sub, map_sub, map_sub, map_sub,
      map_mul_right_of_norm_apply_le hφ hn hy, map_star_of_norm_apply_le hφ hn,
      map_mul_left_of_norm_apply_le hφ hn (star_mem hy),
      hφ.map_id _ (show _ ∈ S from mul_mem (star_mem hy) hy)]
    abel
  rwa [e, sub_nonneg] at h

/-- **Tomiyama's theorem** (Tomiyama 1957, Theorem 1). A linear projection `φ` of a C⋆-algebra
`A` onto a ⋆-subalgebra `S` with `‖φ x‖ ≤ ‖x‖` is order preserving, satisfies
`φ (a * x * b) = a * φ x * b` for `a, b ∈ S`, and satisfies the Kadison–Schwarz inequality
`φ(x)⋆ φ(x) ≤ φ(x⋆ x)`. Tomiyama assumes `A` unital and passes to the bidual; here `A` need not be
unital, and the proof works in `A` and its unitization. -/
theorem tomiyama_of_norm_apply_le :
    Monotone φ ∧ (∀ a ∈ S, ∀ b ∈ S, ∀ x, φ (a * x * b) = a * φ x * b) ∧
      ∀ x, star (φ x) * φ x ≤ φ (star x * x) :=
  ⟨fun x y hxy => sub_nonneg.mp <| by
      rw [← map_sub]; exact map_nonneg_of_norm_apply_le hφ hn (sub_nonneg.mpr hxy),
    fun _ ha _ hb x => hφ.map_mul_mul_of_norm_apply_le hn ha hb x,
    star_map_mul_map_le_of_norm_apply_le hφ hn⟩

/-- A contractive projection onto a C⋆-subalgebra, as a Schwarz map. -/
noncomputable def toSchwarzMap : SchwarzMap A A :=
  { (φ : A →ₗ[ℂ] A) with le_map_star_mul' := star_map_mul_map_le_of_norm_apply_le hφ hn }

@[simp]
lemma toSchwarzMap_apply (x : A) : toSchwarzMap hφ hn x = φ x :=
  rfl

/-- The range `S` of a contractive projection lies in its multiplicative domain. -/
lemma le_multiplicativeDomain_of_norm_apply_le :
    S ≤ LinearMap.multiplicativeDomain (toSchwarzMap hφ hn) := fun s hs b => by
  simp only [toSchwarzMap_apply, hφ.map_id _ hs]
  exact ⟨map_mul_left_of_norm_apply_le hφ hn hs b, map_mul_right_of_norm_apply_le hφ hn hs b⟩

/-- **A contractive projection onto a C⋆-subalgebra is completely positive.**
For `M = Y⋆ Y ≥ 0` and `c` with entries in `S`, `S`-linearity gives
`Σᵢⱼ cᵢ⋆ φ(Mᵢⱼ) cⱼ = φ(Σₘ zₘ⋆ zₘ) ≥ 0` with `zₘ = Σⱼ Yₘⱼ cⱼ`, and a self-adjoint matrix over `S`
with this property is positive. -/
theorem map_cstarMatrix_nonneg_of_norm_apply_le {k : ℕ} {M : CStarMatrix (Fin k) (Fin k) A}
    (hM : 0 ≤ M) : 0 ≤ M.map φ := by
  have := hφ.isClosed (AddMonoidHomClass.continuous_of_bound φ 1 fun x => by simpa using hn x)
  obtain ⟨Y, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM
  refine nonneg_of_forall_sum_star_mul_mul_nonneg (S := S)
    (isSelfAdjoint_cstarMatrix_map (IsSelfAdjoint.star_mul_self Y)
      (map_star_of_norm_apply_le hφ hn))
    (fun i j => hφ.map_mem _) fun c hc => ?_
  have h := map_nonneg_of_norm_apply_le hφ hn
    (Finset.sum_nonneg (s := Finset.univ) fun m _ => star_mul_self_nonneg (∑ j, Y m j * c j))
  rw [← sum_star_mul_star_mul_self_mul, map_sum] at h
  convert h using 2 with i _
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [CStarMatrix.map_apply, map_mul_right_of_norm_apply_le hφ hn (hc j),
    map_mul_left_of_norm_apply_le hφ hn (star_mem (hc i))]

/-- A contractive projection onto a C⋆-subalgebra, as a completely positive map. -/
noncomputable def toCompletelyPositiveMap : A →CP A :=
  { (φ : A →ₗ[ℂ] A) with
    map_cstarMatrix_nonneg' := fun _ _ hM => map_cstarMatrix_nonneg_of_norm_apply_le hφ hn hM }

@[simp]
lemma toCompletelyPositiveMap_apply (x : A) : toCompletelyPositiveMap hφ hn x = φ x :=
  rfl

end LinearMap.IsProj
