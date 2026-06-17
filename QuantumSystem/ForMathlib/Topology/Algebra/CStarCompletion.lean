module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Module.Completion

/-!
# C⋆-algebra structure on a completion

The completion of a normed `*`-algebra is again a normed `*`-algebra, and the completion of a
(possibly incomplete) C⋆-normed algebra is a `CStarAlgebra`. Mathlib already provides the
`NormedRing`, `NormedAlgebra` and `CompleteSpace` instances on `UniformSpace.Completion`; this
file adds the missing `Star`, `StarRing`, `NormedStarGroup`, `CStarRing` and `StarModule`
instances, obtained by extending the operations on the dense image by continuity, and assembles
them into a `CStarAlgebra` instance.

These are general facts about completions and are candidates for upstreaming to Mathlib.
-/

@[expose] public section

namespace UniformSpace.Completion

variable {A : Type*}

section StarRing

variable [NormedRing A] [StarRing A] [NormedStarGroup A]

theorem uniformContinuous_star : UniformContinuous (star : A → A) := by
  have h : Isometry (star : A → A) :=
    AddMonoidHomClass.isometry_of_norm (starAddEquiv (R := A)) fun x => norm_star x
  exact h.uniformContinuous

/-- Involution on a completion, the continuous extension of the involution on the dense image. -/
noncomputable instance : Star (Completion A) := ⟨Completion.map star⟩

@[simp] theorem star_coe (a : A) : star (↑a : Completion A) = (↑(star a) : Completion A) :=
  map_coe uniformContinuous_star a

instance : ContinuousStar (Completion A) := ⟨continuous_map⟩

noncomputable instance : InvolutiveStar (Completion A) where
  star_involutive a := by
    refine induction_on a (isClosed_eq (continuous_id.star.star) continuous_id) ?_
    intro a
    rw [star_coe, star_coe, star_star]

noncomputable instance : StarMul (Completion A) where
  star_mul a b := by
    refine induction_on₂ a b
      (isClosed_eq continuous_mul.star ((continuous_snd.star).mul (continuous_fst.star))) ?_
    intro a b
    rw [← coe_mul, star_coe, star_coe, star_coe, ← coe_mul, star_mul]

noncomputable instance : StarRing (Completion A) where
  star_add a b := by
    refine induction_on₂ a b
      (isClosed_eq continuous_add.star ((continuous_fst.star).add (continuous_snd.star))) ?_
    intro a b
    rw [← coe_add, star_coe, star_coe, star_coe, ← coe_add, star_add]

instance : NormedStarGroup (Completion A) where
  norm_star_le a := by
    refine induction_on a (isClosed_le continuous_id.star.norm continuous_norm) ?_
    intro a
    rw [star_coe, norm_coe, norm_coe]
    exact (norm_star a).le

end StarRing

section CStarRing

variable [NormedRing A] [StarRing A] [NormedStarGroup A] [CStarRing A]

instance : CStarRing (Completion A) where
  norm_mul_self_le a := by
    refine induction_on a
      (isClosed_le (continuous_norm.mul continuous_norm) (continuous_id.star.mul continuous_id).norm)
      ?_
    intro a
    rw [star_coe, ← coe_mul, norm_coe, norm_coe]
    exact CStarRing.norm_mul_self_le a

end CStarRing

section StarModule

variable {𝕜 : Type*} [NormedField 𝕜] [StarRing 𝕜] [NormedRing A] [StarRing A]
  [NormedStarGroup A] [NormedAlgebra 𝕜 A] [StarModule 𝕜 A]

noncomputable instance : StarModule 𝕜 (Completion A) where
  star_smul c a := by
    refine induction_on a
      (isClosed_eq (continuous_const_smul c).star (continuous_id.star.const_smul (star c))) ?_
    intro a
    rw [← coe_smul, star_coe, star_coe, ← coe_smul, star_smul]

end StarModule

/-- The completion of a normed algebra over a normed field is a normed algebra. (Mathlib only
    provides this for commutative base rings; here `A` may be non-commutative.) -/
noncomputable instance instNormedAlgebraOfNormedRing {𝕜 : Type*} [NormedField 𝕜] [NormedRing A]
    [NormedAlgebra 𝕜 A] : NormedAlgebra 𝕜 (Completion A) :=
  { Completion.algebra A 𝕜 with
    norm_smul_le := fun c x => by
      refine induction_on x (isClosed_le ?_ ?_) ?_
      · exact (continuous_const_smul c).norm
      · exact continuous_const.mul continuous_norm
      · intro a
        rw [← coe_smul, norm_coe, norm_coe]
        exact norm_smul_le c a }

/-- The completion of a (possibly incomplete) C⋆-normed `ℂ`-algebra is a `CStarAlgebra`. -/
noncomputable instance instCStarAlgebra [NormedRing A] [StarRing A] [NormedStarGroup A]
    [CStarRing A] [NormedAlgebra ℂ A] [StarModule ℂ A] : CStarAlgebra (Completion A) where

end UniformSpace.Completion
