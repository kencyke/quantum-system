/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Module.Completion

/-!
# C⋆-algebra structure on a completion

The completion of a normed `⋆`-algebra is again a normed `⋆`-algebra, and the completion of a
(possibly incomplete) C⋆-normed algebra is a `CStarAlgebra`, or a `NonUnitalCStarAlgebra` when it
has no unit. Mathlib defines the multiplication of `UniformSpace.Completion α` for a unital ring
`α` only; this file drafts it for non-unital rings (`UniformSpace.Completion.nonUnitalRing`),
agreeing with Mathlib's for unital ones, and the non-unital instances are given low priority so that
Mathlib's are found first for a unital ring. Mathlib already provides the `NormedRing` and
`CompleteSpace` instances on `UniformSpace.Completion`, and the `NormedAlgebra` instance for a
commutative ring only; this file adds the `NormedAlgebra` instance for a ring that need not be
commutative and the missing `Star`, `StarRing`, `NormedStarGroup`, `CStarRing` and `StarModule`
instances, obtained by extending the operations on the dense image by continuity and stated for
non-unital seminormed `⋆`-rings, so that one star structure serves the unital and the non-unital
case, and assembles them into a `CStarAlgebra` or `NonUnitalCStarAlgebra` instance. It also
records the **functoriality** of the completion for `⋆`-algebra equivalences (`mapStarAlgEquiv`): a
uniformly continuous `⋆`-isomorphism with uniformly continuous inverse extends to a `⋆`-isomorphism
of the completions.

These are general facts about completions and are candidates for upstreaming to Mathlib.

## TODO

Generalizing `UniformSpace.Completion.mul` and `UniformSpace.Completion.ring` upstream to
non-unital rings retires the draft of the non-unital ring structure.
-/

@[expose] public section

namespace UniformSpace.Completion

/-! ### Draft: the completion of a non-unital ring -/

open Function

noncomputable section NonUnital

variable (α : Type*) [NonUnitalRing α] [UniformSpace α]

/-- The multiplication of the completion of a non-unital ring, extended from `α` by continuity.
For a unital ring it is `UniformSpace.Completion.mul`. -/
instance (priority := 50) mul' : Mul (Completion α) :=
  ⟨curry <| (isDenseInducing_coe.prodMap isDenseInducing_coe).extend ((↑) ∘ uncurry (· * ·))⟩

variable {α} [IsTopologicalRing α]

/-- The coercion of a non-unital topological ring to its completion is multiplicative. -/
lemma coe_mul' (a b : α) : ((a * b : α) : Completion α) = a * b :=
  ((isDenseInducing_coe.prodMap isDenseInducing_coe).extend_eq
      ((continuous_coe α).comp (@continuous_mul α _ _ _)) (a, b)).symm

variable [IsUniformAddGroup α]

/-- The multiplication of the completion of a non-unital topological ring is continuous. -/
instance (priority := 50) continuousMul' : ContinuousMul (Completion α) where
  continuous_mul := by
    let m := (AddMonoidHom.mul : α →+ α →+ α).compr₂ toCompl
    have : Continuous fun p : α × α => m p.1 p.2 := (continuous_coe α).comp continuous_mul
    have di : IsDenseInducing (toCompl : α → Completion α) := isDenseInducing_coe
    exact (di.extend_Z_bilin di this :)

/-- The completion of a non-unital topological ring is a non-unital ring. -/
instance (priority := 50) nonUnitalRing : NonUnitalRing (Completion α) :=
  { (inferInstance : AddCommGroup (Completion α)), (mul' α : Mul (Completion α)) with
    zero_mul a :=
      Completion.induction_on a (isClosed_eq (by fun_prop) continuous_const)
        fun a => by rw [← coe_zero, ← coe_mul', zero_mul]
    mul_zero a :=
      Completion.induction_on a (isClosed_eq (by fun_prop) continuous_const)
        fun a => by rw [← coe_zero, ← coe_mul', mul_zero]
    mul_assoc a b c :=
      Completion.induction_on₃ a b c (isClosed_eq (by fun_prop) (by fun_prop))
        fun a b c => by rw [← coe_mul', ← coe_mul', ← coe_mul', ← coe_mul', mul_assoc]
    left_distrib a b c :=
      Completion.induction_on₃ a b c (isClosed_eq (by fun_prop) (by fun_prop))
        fun a b c => by rw [← coe_add, ← coe_mul', ← coe_mul', ← coe_mul', ← coe_add, mul_add]
    right_distrib a b c :=
      Completion.induction_on₃ a b c (isClosed_eq (by fun_prop) (by fun_prop))
        fun a b c => by rw [← coe_add, ← coe_mul', ← coe_mul', ← coe_mul', ← coe_add, add_mul] }

/-- The completion of a non-unital topological ring is a topological ring. -/
instance (priority := 50) isTopologicalRing' : IsTopologicalRing (Completion α) where
  continuous_add := continuous_add
  continuous_mul := continuous_mul

/-- In the completion of a non-unital ring, scalars associate with the multiplication:
`(r • x) * y = r • (x * y)`. -/
private lemma smul_mul_assoc' {R : Type*} [SMul R α] [UniformContinuousConstSMul R α]
    [IsScalarTower R α α] (r : R) (x y : Completion α) : (r • x) * y = r • (x * y) := by
  induction x, y using induction_on₂ with
  | hp =>
    exact isClosed_eq ((continuous_fst.const_smul r).mul continuous_snd)
      ((continuous_fst.mul continuous_snd).const_smul r)
  | ih x y => rw [← coe_smul, ← coe_mul', ← coe_mul', ← coe_smul, smul_mul_assoc]

/-- In the completion of a non-unital ring, scalars commute with the multiplication:
`x * (r • y) = r • (x * y)`. -/
private lemma mul_smul_comm' {R : Type*} [SMul R α] [UniformContinuousConstSMul R α]
    [SMulCommClass R α α] (r : R) (x y : Completion α) : x * (r • y) = r • (x * y) := by
  induction x, y using induction_on₂ with
  | hp =>
    exact isClosed_eq (continuous_fst.mul (continuous_snd.const_smul r))
      ((continuous_fst.mul continuous_snd).const_smul r)
  | ih x y => rw [← coe_smul, ← coe_mul', ← coe_mul', ← coe_smul, mul_smul_comm]

/-- The scalar action on the completion of a non-unital ring is compatible with left
multiplication. -/
instance isScalarTower' {R : Type*} [SMul R α] [UniformContinuousConstSMul R α]
    [IsScalarTower R α α] : IsScalarTower R (Completion α) (Completion α) where
  smul_assoc r x y := smul_mul_assoc' r x y

/-- The scalar action on the completion of a non-unital ring is compatible with right
multiplication. -/
instance smulCommClass' {R : Type*} [SMul R α] [UniformContinuousConstSMul R α]
    [SMulCommClass R α α] : SMulCommClass R (Completion α) (Completion α) where
  smul_comm r x y := (mul_smul_comm' r x y).symm

end NonUnital

/-- The completion of a non-unital seminormed ring is a non-unital normed ring. -/
noncomputable instance (priority := 50) nonUnitalNormedRing (A : Type*) [NonUnitalSeminormedRing A] :
    NonUnitalNormedRing (Completion A) where
  __ : NormedAddCommGroup (Completion A) := inferInstance
  __ : NonUnitalRing (Completion A) := inferInstance
  norm_mul_le x y := by
    induction x, y using induction_on₂ with
    | hp => apply isClosed_le <;> fun_prop
    | ih x y => simpa only [← coe_mul', norm_coe] using norm_mul_le x y

variable {A : Type*}

section StarRing

variable [NonUnitalSeminormedRing A] [StarRing A] [NormedStarGroup A]

private lemma uniformContinuous_star : UniformContinuous (star : A → A) :=
  (AddMonoidHomClass.isometry_of_norm (starAddEquiv (R := A)) fun x => norm_star x).uniformContinuous

/-- Involution on a completion, the continuous extension of the involution on the dense image. -/
noncomputable instance instStar : Star (Completion A) := ⟨Completion.map star⟩

/-- The involution on the completion extends that of `A`: `star ↑a = ↑(star a)`. -/
@[simp] lemma star_coe (a : A) : star (↑a : Completion A) = (↑(star a) : Completion A) :=
  map_coe uniformContinuous_star a

/-- The involution on a completion is continuous. -/
instance instContinuousStar : ContinuousStar (Completion A) := ⟨continuous_map⟩

/-- The completion of a seminormed `⋆`-ring is a `⋆`-ring. -/
noncomputable instance instStarRing : StarRing (Completion A) where
  star_involutive a := by
    refine induction_on a (isClosed_eq (continuous_id.star.star) continuous_id) fun a => ?_
    rw [star_coe, star_coe, star_star]
  star_mul a b := by
    refine induction_on₂ a b
      (isClosed_eq continuous_mul.star ((continuous_snd.star).mul (continuous_fst.star))) ?_
    intro a b
    rw [← coe_mul', star_coe, star_coe, star_coe, ← coe_mul', star_mul]
  star_add a b := by
    refine induction_on₂ a b
      (isClosed_eq continuous_add.star ((continuous_fst.star).add (continuous_snd.star))) ?_
    intro a b
    rw [← coe_add, star_coe, star_coe, star_coe, ← coe_add, star_add]

/-- The involution on a completion is isometric: `‖star a‖ = ‖a‖`. -/
instance instNormedStarGroup : NormedStarGroup (Completion A) where
  norm_star_le a := by
    refine induction_on a (isClosed_le continuous_id.star.norm continuous_norm) fun a => ?_
    rw [star_coe, norm_coe, norm_coe]
    exact (norm_star a).le

/-- The completion of a seminormed `⋆`-ring whose seminorm satisfies the C⋆-identity
`‖a‖ * ‖a‖ ≤ ‖star a * a‖` satisfies it; the seminorm need not be a norm. -/
lemma cstarRing_of_norm_mul_self_le (h : ∀ a : A, ‖a‖ * ‖a‖ ≤ ‖star a * a‖) :
    CStarRing (Completion A) where
  norm_mul_self_le a := by
    refine induction_on a
      (isClosed_le (continuous_norm.mul continuous_norm)
        (continuous_id.star.mul continuous_id).norm) fun a => ?_
    rw [star_coe, ← coe_mul', norm_coe, norm_coe]
    exact h a

/-- The completion of a C⋆-normed ring satisfies the C⋆-identity `‖star a * a‖ = ‖a‖ * ‖a‖`. -/
instance instCStarRing {A : Type*} [NonUnitalNormedRing A] [StarRing A] [NormedStarGroup A]
    [CStarRing A] : CStarRing (Completion A) :=
  cstarRing_of_norm_mul_self_le CStarRing.norm_mul_self_le

/-- The involution on the completion of a star module over `𝕜` is conjugate-linear:
`star (c • a) = star c • star a`. -/
instance instStarModule {𝕜 : Type*} [NormedField 𝕜] [StarRing 𝕜] [NormedSpace 𝕜 A]
    [StarModule 𝕜 A] : StarModule 𝕜 (Completion A) where
  star_smul c a := by
    refine induction_on a
      (isClosed_eq (continuous_const_smul c).star (continuous_id.star.const_smul (star c))) ?_
    intro a
    rw [← coe_smul, star_coe, star_coe, ← coe_smul, star_smul]

end StarRing

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

/-- The completion of a (possibly incomplete) non-unital C⋆-normed `ℂ`-algebra is a
`NonUnitalCStarAlgebra`. -/
noncomputable instance (priority := 50) instNonUnitalCStarAlgebra [NonUnitalNormedRing A]
    [StarRing A] [NormedStarGroup A] [CStarRing A] [NormedSpace ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] [StarModule ℂ A] : NonUnitalCStarAlgebra (Completion A) where

section MapStarAlgEquiv

variable {𝕜 A B : Type*} [NormedField 𝕜]
  [NormedRing A] [NormedAlgebra 𝕜 A] [StarRing A] [NormedStarGroup A]
  [NormedRing B] [NormedAlgebra 𝕜 B] [StarRing B] [NormedStarGroup B]

/-- **Functoriality of the completion for star algebra equivalences**: a uniformly continuous
`⋆`-algebra equivalence whose inverse is also uniformly continuous extends, by continuity on the
dense image, to a `⋆`-algebra equivalence of the completions. In particular an isometric
`⋆`-isomorphism extends to the completions. -/
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

/-- `mapStarAlgEquiv e he he'` extends `e` on the image of the completion embedding
`A → Completion A`. -/
@[simp] lemma mapStarAlgEquiv_coe (e : A ≃⋆ₐ[𝕜] B) (he : UniformContinuous e)
    (he' : UniformContinuous e.symm) (a : A) :
    mapStarAlgEquiv e he he' (↑a : Completion A) = (↑(e a) : Completion B) :=
  map_coe he a

/-- As a function, `mapStarAlgEquiv e he he'` is the completion map `Completion.map e`. -/
lemma coe_mapStarAlgEquiv (e : A ≃⋆ₐ[𝕜] B) (he : UniformContinuous e)
    (he' : UniformContinuous e.symm) :
    ⇑(mapStarAlgEquiv e he he') = Completion.map e :=
  rfl

end MapStarAlgEquiv

end UniformSpace.Completion
