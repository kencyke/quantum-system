/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.ContractiveProjection
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.SchwarzMap
public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap

import QuantumSystem.Analysis.CStarAlgebra.ChoiEffros
import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.Stinespring
import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.KPositiveMap
import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.UnitalContraction

/-!
# Contractive projections onto C⋆-subalgebras are conditional expectations

Let `φ` be a linear projection of a C⋆-algebra `A` onto a ⋆-subalgebra `S`
(`LinearMap.IsProj S.toSubmodule φ`), with `‖φ x‖ ≤ ‖x‖` for every `x`. The subalgebra `S` is not
assumed closed: it is the range of the bounded idempotent `φ`, hence closed
(`LinearMap.IsProj.isClosed`), so it is a C⋆-subalgebra. Besides being `S`-linear
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
* **Complete positivity.** For `M ≥ 0` in `Mₖ(A)` and `c ∈ Sᵏ`, `S`-linearity gives
  `Σᵢⱼ cᵢ⋆ φ(Mᵢⱼ) cⱼ = φ(Σᵢⱼ cᵢ⋆ Mᵢⱼ cⱼ) ≥ 0` (`CStarMatrix.sum_star_mul_mul_nonneg`). A matrix
  with entries in `S` and this property is positive
  (`CStarMatrix.nonneg_of_forall_sum_star_mul_mul_nonneg`).

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

/-- `toPositiveLinearMap hφ hn` evaluates as `φ`. -/
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

/-- `toSchwarzMap hφ hn` evaluates as `φ`. -/
@[simp]
lemma toSchwarzMap_apply (x : A) : toSchwarzMap hφ hn x = φ x :=
  rfl

/-- A projection is idempotent, so that `ChoiEffros (toSchwarzMap hφ hn)` is a C⋆-algebra. -/
instance : Fact (IsIdempotentElem (toSchwarzMap hφ hn : A →ₗ[ℂ] A)) :=
  ⟨LinearMap.ext fun a => hφ.map_id _ (hφ.map_mem a)⟩

/-- `toSchwarzMap hφ hn` is the projection `φ` onto `S`, so that `ChoiEffros.val_mul_of_isProj`
applies to it. -/
lemma isProj_toSchwarzMap : IsProj S.toSubmodule (toSchwarzMap hφ hn) :=
  ⟨hφ.map_mem, hφ.map_id⟩

noncomputable example : NonUnitalCStarAlgebra (ChoiEffros (toSchwarzMap hφ hn)) :=
  inferInstance

example (x y : ChoiEffros (toSchwarzMap hφ hn)) : (x * y).val = x.val * y.val :=
  ChoiEffros.val_mul_of_isProj (isProj_toSchwarzMap hφ hn) x y

/-- The range `S` of a contractive projection lies in its multiplicative domain. -/
lemma le_multiplicativeDomain_of_norm_apply_le :
    S ≤ LinearMap.multiplicativeDomain (toSchwarzMap hφ hn) := fun s hs b => by
  simp only [toSchwarzMap_apply, hφ.map_id _ hs]
  exact ⟨map_mul_left_of_norm_apply_le hφ hn hs b, map_mul_right_of_norm_apply_le hφ hn hs b⟩

/-- **A contractive projection onto a C⋆-subalgebra is completely positive.**
For `M ≥ 0` and `c` with entries in `S`, `S`-linearity gives
`Σᵢⱼ cᵢ⋆ φ(Mᵢⱼ) cⱼ = φ(Σᵢⱼ cᵢ⋆ Mᵢⱼ cⱼ) ≥ 0`, and a matrix over `S` with this property is
positive (`CStarMatrix.nonneg_of_forall_sum_star_mul_mul_nonneg`). -/
theorem map_cstarMatrix_nonneg_of_norm_apply_le {k : ℕ} {M : CStarMatrix (Fin k) (Fin k) A}
    (hM : 0 ≤ M) : 0 ≤ M.map φ := by
  refine CStarMatrix.nonneg_of_forall_sum_star_mul_mul_nonneg (S := S) (fun i j => hφ.map_mem _)
    fun c hc => ?_
  have h := map_nonneg_of_norm_apply_le hφ hn (CStarMatrix.sum_star_mul_mul_nonneg hM c)
  rw [map_sum] at h
  convert h using 2 with i _
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [CStarMatrix.map_apply, map_mul_right_of_norm_apply_le hφ hn (hc j),
    map_mul_left_of_norm_apply_le hφ hn (star_mem (hc i))]

/-- A contractive projection onto a C⋆-subalgebra, as a completely positive map. -/
noncomputable def toCompletelyPositiveMap : A →CP A :=
  { (φ : A →ₗ[ℂ] A) with
    map_cstarMatrix_nonneg' := fun _ _ hM => map_cstarMatrix_nonneg_of_norm_apply_le hφ hn hM }

/-- `toCompletelyPositiveMap hφ hn` evaluates as `φ`. -/
@[simp]
lemma toCompletelyPositiveMap_apply (x : A) : toCompletelyPositiveMap hφ hn x = φ x :=
  rfl

end LinearMap.IsProj
