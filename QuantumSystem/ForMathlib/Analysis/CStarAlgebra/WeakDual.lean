import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.GroupTheory.MonoidLocalization.Basic
import Mathlib.Topology.Algebra.Module.WeakDual


section IsPositive

open NNReal

variable (A : Type*) [NonUnitalCStarAlgebra A]

/-- A linear functional is positive if it sends every element of the form `star a * a`
to a nonnegative real number (viewed in `ℂ`). -/
def IsPositive (φ : WeakDual ℂ A) : Prop :=
  ∀ a : A, ∃ r : ℝ≥0, φ (star a * a) = RCLike.ofReal (r : ℝ)

namespace IsPositive

lemma zero : IsPositive A 0 := by
  intro a
  use 0
  show (0 : A →L[ℂ] ℂ) (star a * a) = _
  simp only [ContinuousLinearMap.zero_apply]
  rfl

lemma add {φ ψ : WeakDual ℂ A} (hφ : IsPositive A φ) (hψ : IsPositive A ψ) :
    IsPositive A (φ + ψ) := by
  intro a
  obtain ⟨r, hr⟩ := hφ a
  obtain ⟨s, hs⟩ := hψ a
  use r + s
  show (φ + ψ : A →L[ℂ] ℂ) (star a * a) = _
  erw [ContinuousLinearMap.add_apply]
  rw [hr, hs]
  simp only [RCLike.ofReal_add, NNReal.coe_add]

lemma smul {φ : WeakDual ℂ A} (hφ : IsPositive A φ) {c : ℝ≥0} :
    IsPositive A (c • φ) := by
  intro a
  obtain ⟨r, hr⟩ := hφ a
  use c * r
  show (c • φ : A →L[ℂ] ℂ) (star a * a) = _
  erw [ContinuousLinearMap.smul_apply]
  rw [hr]
  simp only [RCLike.ofReal_mul, NNReal.coe_mul]
  rw [Algebra.smul_def]
  rfl

lemma isClosed : IsClosed { φ : WeakDual ℂ A | IsPositive A φ } := by
  rw [show { φ : WeakDual ℂ A | IsPositive A φ } =
      ⋂ a : A, { φ : WeakDual ℂ A | ∃ r : ℝ≥0, φ (star a * a) = r } by
        ext φ; simp [IsPositive]]
  apply isClosed_iInter
  intro a
  -- Evaluation functional is continuous in weak* topology
  let ev : (WeakDual ℂ A) →L[ℂ] ℂ :=
    { toFun := fun φ => φ (star a * a)
      map_add' := fun φ ψ => rfl
      map_smul' := fun c φ => rfl
      cont := WeakDual.eval_continuous (star a * a) }
  have : { φ : WeakDual ℂ A | ∃ r : ℝ≥0, φ (star a * a) = r } =
         ev ⁻¹' { z : ℂ | 0 ≤ z.re ∧ z.im = 0 } := by
    ext φ
    constructor
    · rintro ⟨r, hr⟩
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      dsimp [ev]
      rw [hr]
      change 0 ≤ RCLike.re (RCLike.ofReal (r : ℝ) : ℂ) ∧ RCLike.im (RCLike.ofReal (r : ℝ) : ℂ) = 0
      rw [RCLike.ofReal_re, RCLike.ofReal_im]
      exact ⟨r.2, rfl⟩
    · rintro ⟨hre, him⟩
      lift (ev φ) to ℝ using him with val hval
      have h_nonneg : 0 ≤ val := by
        rw [Complex.ofReal_re] at hre
        exact hre
      use ⟨val, h_nonneg⟩
      exact hval.symm
  rw [this]
  apply IsClosed.preimage
  · exact ev.continuous
  · apply IsClosed.inter
    · exact isClosed_le continuous_const Complex.continuous_re
    · exact isClosed_eq Complex.continuous_im continuous_const

end IsPositive

end IsPositive
