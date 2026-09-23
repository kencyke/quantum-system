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
them into a `CStarAlgebra` instance. It also records the **functoriality** of the completion for
`*`-algebra equivalences (`mapStarAlgEquiv`): a uniformly continuous `*`-isomorphism with uniformly
continuous inverse extends to a `*`-isomorphism of the completions.

These are general facts about completions and are candidates for upstreaming to Mathlib.
-/

@[expose] public section

namespace UniformSpace.Completion

variable {A : Type*}

section StarRing

variable [NormedRing A] [StarRing A] [NormedStarGroup A]

lemma uniformContinuous_star : UniformContinuous (star : A → A) := by
  have h : Isometry (star : A → A) :=
    AddMonoidHomClass.isometry_of_norm (starAddEquiv (R := A)) fun x => norm_star x
  exact h.uniformContinuous

/-- Involution on a completion, the continuous extension of the involution on the dense image. -/
noncomputable instance : Star (Completion A) := ⟨Completion.map star⟩

@[simp] lemma star_coe (a : A) : star (↑a : Completion A) = (↑(star a) : Completion A) :=
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
      (isClosed_le (continuous_norm.mul continuous_norm)
        (continuous_id.star.mul continuous_id).norm) ?_
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

section MapStarAlgEquiv

variable {𝕜 A B : Type*} [NormedField 𝕜]
  [NormedRing A] [NormedAlgebra 𝕜 A] [StarRing A] [NormedStarGroup A]
  [NormedRing B] [NormedAlgebra 𝕜 B] [StarRing B] [NormedStarGroup B]

/-- **Functoriality of the completion for star algebra equivalences**: a uniformly continuous
`*`-algebra equivalence whose inverse is also uniformly continuous extends, by continuity on the
dense image, to a `*`-algebra equivalence of the completions. (In particular every `*`-isomorphism
of C⋆-normed algebras, being isometric, extends to the completions.) -/
noncomputable def mapStarAlgEquiv (e : A ≃⋆ₐ[𝕜] B) (he : UniformContinuous e)
    (he' : UniformContinuous e.symm) : Completion A ≃⋆ₐ[𝕜] Completion B where
  toFun := Completion.map e
  invFun := Completion.map e.symm
  left_inv x := by
    refine induction_on x (isClosed_eq (continuous_map.comp continuous_map) continuous_id) ?_
    intro a
    rw [map_coe he, map_coe he', StarAlgEquiv.symm_apply_apply]
  right_inv x := by
    refine induction_on x (isClosed_eq (continuous_map.comp continuous_map) continuous_id) ?_
    intro a
    rw [map_coe he', map_coe he, StarAlgEquiv.apply_symm_apply]
  map_mul' x y := by
    refine induction_on₂ x y
      (isClosed_eq ((continuous_map (f := ⇑e)).comp continuous_mul)
        (((continuous_map (f := ⇑e)).comp continuous_fst).mul
          ((continuous_map (f := ⇑e)).comp continuous_snd))) ?_
    intro a b
    rw [← coe_mul, map_coe he, map_coe he, map_coe he, ← coe_mul, map_mul]
  map_add' x y := by
    refine induction_on₂ x y
      (isClosed_eq ((continuous_map (f := ⇑e)).comp continuous_add)
        (((continuous_map (f := ⇑e)).comp continuous_fst).add
          ((continuous_map (f := ⇑e)).comp continuous_snd))) ?_
    intro a b
    rw [← coe_add, map_coe he, map_coe he, map_coe he, ← coe_add, map_add]
  map_smul' c x := by
    refine induction_on x
      (isClosed_eq (continuous_map.comp (continuous_const_smul c))
        ((continuous_const_smul c).comp continuous_map)) ?_
    intro a
    rw [← coe_smul, map_coe he, map_coe he, ← coe_smul, map_smul]
  map_star' x := by
    refine induction_on x
      (isClosed_eq (continuous_map.comp continuous_star) (continuous_star.comp continuous_map)) ?_
    intro a
    rw [star_coe, map_coe he, map_coe he, star_coe, map_star]

@[simp] lemma mapStarAlgEquiv_coe (e : A ≃⋆ₐ[𝕜] B) (he : UniformContinuous e)
    (he' : UniformContinuous e.symm) (a : A) :
    mapStarAlgEquiv e he he' (↑a : Completion A) = (↑(e a) : Completion B) :=
  map_coe he a

lemma coe_mapStarAlgEquiv (e : A ≃⋆ₐ[𝕜] B) (he : UniformContinuous e)
    (he' : UniformContinuous e.symm) :
    ⇑(mapStarAlgEquiv e he he') = Completion.map e :=
  rfl

end MapStarAlgEquiv

end UniformSpace.Completion
