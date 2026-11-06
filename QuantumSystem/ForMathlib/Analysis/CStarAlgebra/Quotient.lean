/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.Hom
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Topology.Algebra.Module.Basic

/-!
# Two-sided ideals as submodules, and quotient C⋆-algebras

A two-sided ideal of a (possibly non-unital) algebra `A` over `R` is spelled here as an
`R`-submodule `I : Submodule R A` that absorbs multiplication on both sides, the `Prop`-valued class
`Submodule.IsTwoSidedIdeal`. In this spelling the quotient `A ⧸ I` is Mathlib's quotient module
`Submodule.Quotient`, and the closure of an ideal is Mathlib's `Submodule.topologicalClosure`; the
multiplication, the ring structure, and the submultiplicativity of the quotient norm are what this
file adds. The quotient norm `‖a + I‖ = infDist a I`, its completeness and its scalar action are
Mathlib's (`Submodule.Quotient.seminormedAddCommGroup`, `Submodule.Quotient.completeSpace`,
`Submodule.Quotient.normedSpace`). The ring structure is obtained as Mathlib obtains
`Ideal.Quotient.ring`: through a ring congruence extending `QuotientAddGroup.con`. Throughout the
file, and in every docstring, a two-sided ideal of an `R`-algebra `A` means such a submodule
`I : Submodule R A` with `[I.IsTwoSidedIdeal]`.

For a non-unital C⋆-algebra `A` the spelling loses nothing: a closed two-sided ideal in the
ring-theoretic sense, a `TwoSidedIdeal A`, is automatically a complex subspace
(`TwoSidedIdeal.smul_mem_of_isClosed`, so that `TwoSidedIdeal.toSubmodule` lands in the present
spelling), and a closed two-sided ideal given as a submodule is automatically self-adjoint
(`Submodule.star_mem_of_isClosed`). Every statement below about a closed two-sided ideal
`I : Submodule ℂ A` therefore holds for a closed `J : TwoSidedIdeal A`, applied to
`J.toSubmodule`; the examples at the end of the file check this for self-adjointness and for the
quotient C⋆-algebra. Both follow from closedness through approximate units: `c • x`
is the limit of `(c • e) * x` along an approximate unit `e` of `A`, and `x⋆` is the limit of
`x⋆ * u ∈ I` along an approximate unit `u` of the C⋆-algebra `I ∩ I⋆`. A closed ideal is therefore
a closed ⋆-subalgebra, and a C⋆-algebra in its own right.

The quotient `A ⧸ I` by a closed two-sided ideal, with the quotient norm, is a C⋆-algebra, unital
when `A` is. The C⋆-identity rests on an approximate unit `u` of `I`, positive contractions of the
C⋆-algebra `I`: in the unitization, `‖1 - u‖ ≤ 1`, and for every `b ∈ I`,
`‖a + I‖² ≤ ‖a - a u‖² = ‖(1 - u) a⋆a (1 - u)‖ ≤ ‖a⋆a + b‖ + ‖b - b u‖`, whose last term tends to
zero along `u`. Taking the infimum over `b` gives `‖a + I‖² ≤ ‖a⋆a + I‖`.

Mathlib's `Ideal.IsTwoSided` is the same predicate for `Ideal A = Submodule A A`, which needs `A`
unital; `Submodule.IsTwoSidedIdeal` applies to any scalars, in particular to non-unital algebras.

## Implementation notes

On an `Ideal` of a unital ring, Mathlib's `Ideal.Quotient.ring` and its normed counterparts also
apply. They agree with the instances here by `rfl`, but not at reducible transparency, so the ring
and normed-ring instances on the quotient have priority `100` and Mathlib's are found first.

## Main definitions

* `Submodule.IsTwoSidedIdeal`: a submodule of a non-unital algebra absorbing multiplication on both
  sides.
* `Submodule.Quotient.mkₙₐ`, `Submodule.Quotient.liftₙₐ`, and their unital (`mkₐ`) and involutive
  (`mkStarₙₐ`, `liftStarₙₐ`, `mkStarₐ`) versions: the quotient map and the universal property.
* `Submodule.toNonUnitalStarSubalgebra`: a closed two-sided ideal `I : Submodule ℂ A` of a
  C⋆-algebra as a ⋆-subalgebra.
* `TwoSidedIdeal.toSubmodule`: a closed ring-theoretic two-sided ideal of a C⋆-algebra, as a
  submodule that is a two-sided ideal.
* `NonUnitalStarAlgHom.quotientKerEquivRange`: a ⋆-homomorphism of C⋆-algebras induces a
  ⋆-isomorphism from the quotient by its kernel onto its range.

## Main results

* For a two-sided ideal `I` of a non-unital normed `𝕜`-algebra `A`, the quotient `A ⧸ I` is a
  non-unital normed `𝕜`-algebra: `NonUnitalSeminormedRing`, normed when `I` is closed, with the
  `NormedSpace 𝕜`, `IsScalarTower` and `SMulCommClass` structure of a non-unital algebra; when `A`
  is unital it is a `NormedAlgebra 𝕜`.
* **`Submodule.star_mem_of_isClosed`**: a closed two-sided ideal `I : Submodule ℂ A` of a
  C⋆-algebra is self-adjoint; through `TwoSidedIdeal.toSubmodule`, so is every closed ring-theoretic
  two-sided ideal.
* **`Submodule.Quotient.instCStarRing`**: the quotient norm satisfies the C⋆-identity, so the quotient
  by a closed two-sided ideal `I : Submodule ℂ A` is a `NonUnitalCStarAlgebra`, and a `CStarAlgebra`
  when `A` is unital; through `TwoSidedIdeal.toSubmodule`, the same holds for the quotient by a
  closed ring-theoretic two-sided ideal.
* **`NonUnitalStarAlgHom.isClosed_range`**: the range of a ⋆-homomorphism of C⋆-algebras is closed;
  hence a ⋆-homomorphism with dense range is surjective.
-/

@[expose] public section

open CStarAlgebra Filter Metric Topology Unitization

namespace Submodule

/-! ### Two-sided ideals as submodules -/

section IsTwoSidedIdeal

variable {R A : Type*} [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]

/-- A submodule of a non-unital algebra that absorbs multiplication on both sides: a two-sided ideal
that is also a submodule. For a unital algebra and `R = A` this is `Ideal.IsTwoSided`. -/
class IsTwoSidedIdeal (I : Submodule R A) : Prop where
  /-- A two-sided ideal absorbs multiplication on the left. -/
  mul_mem_left (a : A) {x : A} : x ∈ I → a * x ∈ I
  /-- A two-sided ideal absorbs multiplication on the right. -/
  mul_mem_right (a : A) {x : A} : x ∈ I → x * a ∈ I

/-- The zero submodule is a two-sided ideal. -/
instance : (⊥ : Submodule R A).IsTwoSidedIdeal where
  mul_mem_left a x hx := by rw [mem_bot] at hx ⊢; rw [hx, mul_zero]
  mul_mem_right a x hx := by rw [mem_bot] at hx ⊢; rw [hx, zero_mul]

/-- The whole algebra is a two-sided ideal. -/
instance : (⊤ : Submodule R A).IsTwoSidedIdeal where
  mul_mem_left _ _ _ := trivial
  mul_mem_right _ _ _ := trivial

/-- The intersection of two two-sided ideals is a two-sided ideal. -/
instance (I J : Submodule R A) [I.IsTwoSidedIdeal] [J.IsTwoSidedIdeal] :
    (I ⊓ J).IsTwoSidedIdeal where
  mul_mem_left a _ hx := ⟨IsTwoSidedIdeal.mul_mem_left a hx.1, IsTwoSidedIdeal.mul_mem_left a hx.2⟩
  mul_mem_right a _ hx :=
    ⟨IsTwoSidedIdeal.mul_mem_right a hx.1, IsTwoSidedIdeal.mul_mem_right a hx.2⟩

end IsTwoSidedIdeal

end Submodule

namespace NonUnitalAlgHom

variable (R : Type*) {A B F : Type*} [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [NonUnitalNonAssocSemiring B] [Module R B] [FunLike F A B] [NonUnitalAlgHomClass F R A B]

/-- The kernel of a homomorphism of non-unital `R`-algebras, as a submodule of the domain. -/
def ker (φ : F) : Submodule R A :=
  LinearMap.ker (φ : A →ₗ[R] B)

variable {R}

/-- Membership in the kernel. -/
@[simp]
lemma mem_ker {φ : F} {x : A} : x ∈ ker R φ ↔ φ x = 0 :=
  LinearMap.mem_ker

/-- The kernel of a homomorphism of non-unital algebras is a two-sided ideal. -/
instance (φ : F) : (ker R φ).IsTwoSidedIdeal where
  mul_mem_left a x hx := by
    rw [mem_ker] at hx ⊢
    rw [map_mul, hx, mul_zero]
  mul_mem_right a x hx := by
    rw [mem_ker] at hx ⊢
    rw [map_mul, hx, zero_mul]

end NonUnitalAlgHom

namespace Submodule

/-! ### The quotient ring -/

section Quotient

variable {R A : Type*} [Ring R] [NonUnitalRing A] [Module R A] (I : Submodule R A)
  [I.IsTwoSidedIdeal]

namespace Quotient

/-- `I.quotientRel` is a ring congruence when `I` is a two-sided ideal; it is the congruence
`QuotientAddGroup.con` of the additive subgroup `I`. -/
protected def ringCon : RingCon A where
  __ := QuotientAddGroup.con I.toAddSubgroup
  mul' {a₁ b₁ a₂ b₂} h₁ h₂ := by
    have h₁' : -a₁ + b₁ ∈ I := QuotientAddGroup.leftRel_apply.mp h₁
    have h₂' : -a₂ + b₂ ∈ I := QuotientAddGroup.leftRel_apply.mp h₂
    refine QuotientAddGroup.leftRel_apply.mpr ?_
    have : -(a₁ * a₂) + b₁ * b₂ = b₁ * (-a₂ + b₂) + (-a₁ + b₁) * a₂ := by noncomm_ring
    change -(a₁ * a₂) + b₁ * b₂ ∈ I
    rw [this]
    exact I.add_mem (IsTwoSidedIdeal.mul_mem_left b₁ h₂') (IsTwoSidedIdeal.mul_mem_right a₂ h₁')

/-- The quotient of a non-unital ring by a two-sided ideal is a non-unital ring. -/
instance (priority := 100) instNonUnitalRing : NonUnitalRing (A ⧸ I) :=
  inferInstanceAs <| NonUnitalRing (Quotient.ringCon I).Quotient

-- The ring structure extends the additive group of the quotient module.
example : (instNonUnitalRing I).toAddCommGroup = Submodule.Quotient.addCommGroup I := by
  with_reducible_and_instances rfl

/-- The quotient map is multiplicative. -/
@[simp]
lemma mk_mul (a b : A) : (mk (a * b) : A ⧸ I) = mk a * mk b :=
  rfl

/-- Scalars pass through products on the quotient. -/
instance [IsScalarTower R A A] : IsScalarTower R (A ⧸ I) (A ⧸ I) where
  smul_assoc c x y := by
    induction x using Submodule.Quotient.induction_on with | H a => ?_
    induction y using Submodule.Quotient.induction_on with | H b => ?_
    exact congr_arg mk (smul_mul_assoc c a b)

/-- Scalars commute with products on the quotient. -/
instance [SMulCommClass R A A] : SMulCommClass R (A ⧸ I) (A ⧸ I) where
  smul_comm c x y := by
    induction x using Submodule.Quotient.induction_on with | H a => ?_
    induction y using Submodule.Quotient.induction_on with | H b => ?_
    exact congr_arg mk (mul_smul_comm c a b).symm

/-- The quotient map onto the quotient by a two-sided ideal, as a homomorphism of non-unital
algebras. -/
def mkₙₐ : A →ₙₐ[R] A ⧸ I where
  toFun := mk
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- The quotient map sends `a` to its class. -/
@[simp]
lemma mkₙₐ_apply (a : A) : mkₙₐ I a = mk a :=
  rfl

/-- The quotient map is surjective. -/
lemma mkₙₐ_surjective : Function.Surjective (mkₙₐ I) :=
  mk_surjective I

/-- The kernel of the quotient map is the ideal. -/
@[simp]
lemma ker_mkₙₐ : NonUnitalAlgHom.ker R (mkₙₐ I) = I :=
  Submodule.ext fun _ ↦ by rw [NonUnitalAlgHom.mem_ker, mkₙₐ_apply, mk_eq_zero]

section Lift

variable {B : Type*} [NonUnitalRing B] [Module R B] (φ : A →ₙₐ[R] B)

/-- A homomorphism vanishing on `I` factors through the quotient by `I`. -/
def liftₙₐ (hφ : I ≤ NonUnitalAlgHom.ker R φ) : A ⧸ I →ₙₐ[R] B where
  toFun := Quotient.lift φ fun a b h ↦ by
    have hab : a - b ∈ I := (Submodule.Quotient.eq I).mp (Quotient.sound h)
    rw [← sub_eq_zero, ← map_sub]
    exact NonUnitalAlgHom.mem_ker.mp (hφ hab)
  map_smul' c x := by
    induction x using Submodule.Quotient.induction_on with | H a => ?_
    exact map_smul φ c a
  map_zero' := map_zero φ
  map_add' x y := by
    induction x using Submodule.Quotient.induction_on with | H a => ?_
    induction y using Submodule.Quotient.induction_on with | H b => ?_
    exact map_add φ a b
  map_mul' x y := by
    induction x using Submodule.Quotient.induction_on with | H a => ?_
    induction y using Submodule.Quotient.induction_on with | H b => ?_
    exact map_mul φ a b

/-- The induced map sends the class of `a` to `φ a`. -/
@[simp]
lemma liftₙₐ_mk (hφ : I ≤ NonUnitalAlgHom.ker R φ) (a : A) : liftₙₐ I φ hφ (mk a) = φ a :=
  rfl

/-- The induced map composed with the quotient map is `φ`. -/
@[simp]
lemma liftₙₐ_comp_mkₙₐ (hφ : I ≤ NonUnitalAlgHom.ker R φ) : (liftₙₐ I φ hφ).comp (mkₙₐ I) = φ :=
  rfl

end Lift

end Quotient

end Quotient

section QuotientUnital

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (I : Submodule R A) [I.IsTwoSidedIdeal]

namespace Quotient

/-- The quotient of a ring by a two-sided ideal is a ring. -/
instance (priority := 100) instRing : Ring (A ⧸ I) :=
  inferInstanceAs <| Ring (Quotient.ringCon I).Quotient

-- No diamond with the non-unital structure.
example : (instRing I).toNonUnitalRing = instNonUnitalRing I := by
  with_reducible_and_instances rfl

/-- The quotient map sends `1` to `1`. -/
@[simp]
lemma mk_one : (mk 1 : A ⧸ I) = 1 :=
  rfl

/-- The quotient map onto the quotient by a two-sided ideal, as a ring homomorphism. -/
def mkRingHom : A →+* A ⧸ I where
  __ := mkₙₐ I
  map_one' := rfl

/-- The ring homomorphism sends `a` to its class. -/
@[simp]
lemma mkRingHom_apply (a : A) : mkRingHom I a = mk a :=
  rfl

/-- The quotient of an `R`-algebra by a two-sided ideal is an `R`-algebra, with the scalar action
of the quotient module. -/
instance (priority := 100) instAlgebra : Algebra R (A ⧸ I) where
  algebraMap := (mkRingHom I).comp (algebraMap R A)
  commutes' c x := by
    induction x using Submodule.Quotient.induction_on with | H a => ?_
    exact congr_arg mk (Algebra.commutes c a)
  smul_def' c x := by
    induction x using Submodule.Quotient.induction_on with | H a => ?_
    exact congr_arg mk (Algebra.smul_def c a)

-- The algebra's scalar action is that of the quotient module.
example : (instAlgebra I).toSMul = Submodule.Quotient.instSMul I := by
  with_reducible_and_instances rfl

/-- The quotient map onto the quotient by a two-sided ideal, as an algebra homomorphism. -/
def mkₐ : A →ₐ[R] A ⧸ I where
  __ := mkRingHom I
  commutes' _ := rfl

/-- The algebra homomorphism sends `a` to its class. -/
@[simp]
lemma mkₐ_apply (a : A) : mkₐ I a = mk a :=
  rfl

end Quotient

end QuotientUnital

/-! ### The closure of a two-sided ideal -/

section Closure

variable {R A : Type*} [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] [TopologicalSpace A]
  [ContinuousAdd A] [ContinuousMul A] [ContinuousConstSMul R A]

/-- The closure of a two-sided ideal is a two-sided ideal. -/
instance (I : Submodule R A) [I.IsTwoSidedIdeal] : I.topologicalClosure.IsTwoSidedIdeal where
  mul_mem_left a x hx := by
    rw [← SetLike.mem_coe, topologicalClosure_coe] at hx ⊢
    exact map_mem_closure (f := (a * ·)) (continuous_const_mul a) hx fun _ h ↦
      IsTwoSidedIdeal.mul_mem_left a h
  mul_mem_right a x hx := by
    rw [← SetLike.mem_coe, topologicalClosure_coe] at hx ⊢
    exact map_mem_closure (f := (· * a)) (continuous_mul_const a) hx fun _ h ↦
      IsTwoSidedIdeal.mul_mem_right a h

/-- The whole algebra is a closed submodule. -/
instance : IsClosed ((⊤ : Submodule R A) : Set A) := by
  rw [top_coe]
  exact isClosed_univ

/-- The zero submodule of a `T1` space is closed. -/
instance [T1Space A] : IsClosed ((⊥ : Submodule R A) : Set A) := by
  rw [bot_coe]
  exact isClosed_singleton

end Closure

/-! ### The quotient norm -/

section Seminormed

variable {R A : Type*} [Ring R] [NonUnitalSeminormedRing A] [Module R A] (I : Submodule R A)
  [I.IsTwoSidedIdeal]

namespace Quotient

omit [I.IsTwoSidedIdeal] in
/-- The norm of `a + I` is at most the norm of any representative `a + b`, `b ∈ I`. -/
lemma norm_mk_le_norm_add (a : A) {b : A} (hb : b ∈ I) : ‖(mk a : A ⧸ I)‖ ≤ ‖a + b‖ := by
  have : (mk (a + b) : A ⧸ I) = mk a := (Submodule.Quotient.eq I).mpr (by simpa using hb)
  exact this ▸ Submodule.Quotient.norm_mk_le I (a + b)

/-- The quotient norm is submultiplicative. -/
noncomputable instance (priority := 100) instNonUnitalSeminormedRing : NonUnitalSeminormedRing (A ⧸ I) :=
  { Submodule.Quotient.seminormedAddCommGroup I, instNonUnitalRing I with
  norm_mul_le x y := le_of_forall_pos_le_add fun ε hε ↦ by
    have := ((nhds_basis_ball.prod_nhds nhds_basis_ball).tendsto_iff nhds_basis_ball).mp
      (continuous_mul.tendsto (‖x‖, ‖y‖)) ε hε
    simp only [Set.mem_prod, Metric.mem_ball, and_imp, Prod.forall, Prod.exists] at this
    obtain ⟨ε₁, ε₂, ⟨h₁, h₂⟩, h⟩ := this
    obtain ⟨⟨a, rfl, ha⟩, ⟨b, rfl, hb⟩⟩ :=
      Submodule.Quotient.norm_mk_lt x h₁, Submodule.Quotient.norm_mk_lt y h₂
    simp only [dist, abs_sub_lt_iff] at h
    specialize h ‖a‖ ‖b‖ ⟨by linarith, by linarith [Submodule.Quotient.norm_mk_le I a]⟩
      ⟨by linarith, by linarith [Submodule.Quotient.norm_mk_le I b]⟩
    calc
      _ ≤ ‖a‖ * ‖b‖ := by
        rw [← mk_mul]
        exact (Submodule.Quotient.norm_mk_le I (a * b)).trans (norm_mul_le a b)
      _ ≤ _ := (sub_lt_iff_lt_add'.mp h.1).le }

-- The quotient norm is that of the quotient module.
example : (instNonUnitalSeminormedRing I).toSeminormedAddCommGroup =
    Submodule.Quotient.seminormedAddCommGroup I := by
  with_reducible_and_instances rfl

/-- The quotient by a closed two-sided ideal `I : Submodule R A` is a non-unital normed ring. -/
noncomputable instance (priority := 100) instNonUnitalNormedRing [IsClosed (I : Set A)] :
    NonUnitalNormedRing (A ⧸ I) :=
  { instNonUnitalSeminormedRing I, Submodule.Quotient.normedAddCommGroup I with }

/-- `‖a + I‖ = 0` exactly when `a ∈ I`, for a closed ideal `I`. -/
lemma norm_mk_eq_zero [IsClosed (I : Set A)] (a : A) : ‖(mk a : A ⧸ I)‖ = 0 ↔ a ∈ I := by
  rw [norm_eq_zero, mk_eq_zero]

end Quotient

end Seminormed

section SeminormedUnital

variable {𝕜 A : Type*} [NormedField 𝕜] [SeminormedRing A] [NormedAlgebra 𝕜 A] (I : Submodule 𝕜 A)
  [I.IsTwoSidedIdeal]

namespace Quotient

/-- The quotient of a seminormed algebra by a two-sided ideal is a seminormed ring. -/
noncomputable instance (priority := 100) instSeminormedRing : SeminormedRing (A ⧸ I) :=
  { instNonUnitalSeminormedRing I, instRing I with }

/-- The quotient of a normed algebra by a closed two-sided ideal `I : Submodule 𝕜 A` is a normed
ring. -/
noncomputable instance (priority := 100) instNormedRing [IsClosed (I : Set A)] : NormedRing (A ⧸ I) :=
  { instSeminormedRing I, Submodule.Quotient.normedAddCommGroup I with }

/-- The quotient of a normed algebra by a two-sided ideal is a normed algebra. -/
noncomputable instance (priority := 100) instNormedAlgebra : NormedAlgebra 𝕜 (A ⧸ I) :=
  { Submodule.Quotient.normedSpace I 𝕜, instAlgebra I with }

end Quotient

end SeminormedUnital

/-! ### Closed two-sided ideals of C⋆-algebras -/

section CStarIdeal

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- `‖a⋆ - a⋆ u‖² ≤ 2 ‖a a⋆ - a a⋆ u‖` for a self-adjoint contraction `u`. -/
private lemma norm_star_sub_star_mul_sq_le (a u : A) (hu : star u = u) (hu₁ : ‖u‖ ≤ 1) :
    ‖star a - star a * u‖ ^ 2 ≤ 2 * ‖a * star a - a * star a * u‖ := by
  set d := a * star a - a * star a * u
  have h : star (star a - star a * u) * (star a - star a * u) = d - u * d := by
    simp only [star_sub, star_mul, star_star, hu, d]
    noncomm_ring
  rw [sq, ← CStarRing.norm_star_mul_self, h]
  calc
    ‖d - u * d‖ ≤ ‖d‖ + ‖u‖ * ‖d‖ := (norm_sub_le _ _).trans (by gcongr; exact norm_mul_le _ _)
    _ ≤ ‖d‖ + 1 * ‖d‖ := by gcongr
    _ = 2 * ‖d‖ := by ring

variable (I : Submodule ℂ A) [I.IsTwoSidedIdeal] [hI : IsClosed (I : Set A)]

/-- The elements `x` of a closed two-sided ideal `I` with `x⋆ ∈ I`, as a ⋆-subalgebra. -/
private def interStar : NonUnitalStarSubalgebra ℂ A where
  carrier := {x | x ∈ I ∧ star x ∈ I}
  add_mem' hx hy := ⟨I.add_mem hx.1 hy.1, by rw [star_add]; exact I.add_mem hx.2 hy.2⟩
  zero_mem' := ⟨I.zero_mem, by rw [star_zero]; exact I.zero_mem⟩
  mul_mem' {_ y} hx hy :=
    ⟨IsTwoSidedIdeal.mul_mem_right y hx.1, by rw [star_mul]; exact IsTwoSidedIdeal.mul_mem_right _ hy.2⟩
  smul_mem' c _ hx := ⟨I.smul_mem c hx.1, by rw [star_smul]; exact I.smul_mem _ hx.2⟩
  star_mem' hx := ⟨hx.2, by rw [star_star]; exact hx.1⟩

omit hI in
private lemma mem_interStar {x : A} : x ∈ interStar I ↔ x ∈ I ∧ star x ∈ I :=
  Iff.rfl

/-- A closed two-sided ideal `I : Submodule ℂ A` of a C⋆-algebra is self-adjoint. For a closed
`J : TwoSidedIdeal A`, apply this to `J.toSubmodule`. -/
theorem star_mem_of_isClosed {a : A} (ha : a ∈ I) : star a ∈ I := by
  set B := interStar I
  have : IsClosed (B : Set A) := by
    have : (B : Set A) = (I : Set A) ∩ star ⁻¹' (I : Set A) := Set.ext fun _ ↦ mem_interStar I
    rw [this]
    exact hI.inter (hI.preimage continuous_star)
  let _ := CStarAlgebra.spectralOrder B
  have _ := CStarAlgebra.spectralOrderedRing B
  have hl := CStarAlgebra.increasingApproximateUnit B
  let y : B := ⟨a * star a, (mem_interStar I).2 ⟨IsTwoSidedIdeal.mul_mem_right _ ha,
    by simpa using IsTwoSidedIdeal.mul_mem_right (star a) ha⟩⟩
  -- `y u → y` along the approximate unit, so `a⋆ u → a⋆`
  have hy : Tendsto (fun u : B ↦ ‖a * star a - a * star a * u‖) (CStarAlgebra.approximateUnit B)
      (𝓝 0) := by
    have := (continuous_subtype_val.tendsto y).comp (hl.tendsto_mul_left y)
    simpa [Function.comp_def, ← dist_eq_norm', ← tendsto_iff_dist_tendsto_zero] using this
  have h : Tendsto (fun u : B ↦ star a * (u : A)) (CStarAlgebra.approximateUnit B)
      (𝓝 (star a)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hy₂ := (hy.const_mul 2).sqrt
    rw [mul_zero, Real.sqrt_zero] at hy₂
    refine squeeze_zero' (.of_forall fun _ ↦ norm_nonneg _) ?_ hy₂
    filter_upwards [hl.eventually_star_eq, hl.eventually_norm] with u hu hu₁
    rw [norm_sub_rev]
    exact Real.le_sqrt_of_sq_le <| norm_star_sub_star_mul_sq_le a u (congr_arg Subtype.val hu) hu₁
  exact hI.mem_of_tendsto h (.of_forall fun u ↦
    IsTwoSidedIdeal.mul_mem_left _ ((mem_interStar I).1 u.2).1)

/-- A closed two-sided ideal `I : Submodule ℂ A` of a C⋆-algebra contains `a⋆` exactly when it
contains `a`. -/
lemma star_mem_iff_of_isClosed {a : A} : star a ∈ I ↔ a ∈ I :=
  ⟨fun h ↦ star_star a ▸ star_mem_of_isClosed I h, star_mem_of_isClosed I⟩

/-- A closed two-sided ideal `I : Submodule ℂ A` of a C⋆-algebra, as a ⋆-subalgebra. -/
def toNonUnitalStarSubalgebra : NonUnitalStarSubalgebra ℂ A where
  __ := I
  mul_mem' {_ y} hx _ := IsTwoSidedIdeal.mul_mem_right y hx
  star_mem' hx := star_mem_of_isClosed I hx

/-- The ⋆-subalgebra of a closed ideal has the ideal as its carrier. -/
@[simp]
lemma coe_toNonUnitalStarSubalgebra : (I.toNonUnitalStarSubalgebra : Set A) = I :=
  rfl

/-- Membership in the ⋆-subalgebra of a closed ideal is membership in the ideal. -/
@[simp]
lemma mem_toNonUnitalStarSubalgebra {x : A} : x ∈ I.toNonUnitalStarSubalgebra ↔ x ∈ I :=
  Iff.rfl

/-- The ⋆-subalgebra of a closed ideal is closed. -/
instance : IsClosed (I.toNonUnitalStarSubalgebra : Set A) :=
  hI

end CStarIdeal

end Submodule

namespace TwoSidedIdeal

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- A closed ring-theoretic two-sided ideal `I : TwoSidedIdeal A` of a C⋆-algebra is closed under
any continuous scalar action
compatible with the multiplication, in particular under complex scalars. -/
lemma smul_mem_of_isClosed {𝕜 : Type*} [SMul 𝕜 A] [ContinuousConstSMul 𝕜 A]
    [IsScalarTower 𝕜 A A] {I : TwoSidedIdeal A} (hI : IsClosed (I : Set A)) {y : A} (hy : y ∈ I)
    (r : 𝕜) : r • y ∈ I := by
  let _ := CStarAlgebra.spectralOrder A
  have _ := CStarAlgebra.spectralOrderedRing A
  have h := ((CStarAlgebra.increasingApproximateUnit A).tendsto_mul_right y).const_smul r
  refine hI.mem_of_tendsto h (.of_forall fun e ↦ ?_)
  rw [SetLike.mem_coe, ← smul_mul_assoc]
  exact I.mul_mem_left _ _ hy

variable (I : TwoSidedIdeal A) [hI : IsClosed (I : Set A)]

/-- A closed ring-theoretic two-sided ideal of a C⋆-algebra, as a complex subspace absorbing
multiplication on both sides. -/
def toSubmodule : Submodule ℂ A where
  carrier := I
  add_mem' := I.add_mem
  zero_mem' := I.zero_mem
  smul_mem' c _ hx := smul_mem_of_isClosed hI hx c

/-- The submodule of a closed ideal has the ideal as its carrier. -/
@[simp]
lemma coe_toSubmodule : (I.toSubmodule : Set A) = I :=
  rfl

/-- Membership in the submodule of a closed ideal is membership in the ideal. -/
@[simp]
lemma mem_toSubmodule {x : A} : x ∈ I.toSubmodule ↔ x ∈ I :=
  Iff.rfl

/-- The submodule of a closed ideal is a two-sided ideal. -/
instance : I.toSubmodule.IsTwoSidedIdeal where
  mul_mem_left a _ hx := I.mul_mem_left a _ hx
  mul_mem_right a _ hx := I.mul_mem_right _ a hx

/-- The submodule of a closed ideal is closed. -/
instance : IsClosed (I.toSubmodule : Set A) :=
  hI

end TwoSidedIdeal

namespace NonUnitalStarAlgHom

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- The kernel of a ⋆-homomorphism of C⋆-algebras is closed. -/
instance isClosed_ker (φ : A →⋆ₙₐ[ℂ] B) : IsClosed (NonUnitalAlgHom.ker ℂ φ : Set A) := by
  have : (NonUnitalAlgHom.ker ℂ φ : Set A) = φ ⁻¹' {0} := Set.ext fun _ ↦ NonUnitalAlgHom.mem_ker
  rw [this]
  exact isClosed_singleton.preimage (map_continuous φ)

end NonUnitalStarAlgHom

/-! ### Quotient C⋆-algebras -/

namespace Submodule

section CStarQuotient

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- `‖1 - u‖ ≤ 1` in the unitization for a positive contraction `u`. -/
private lemma norm_one_sub_inr_le_one {u : A} (hu : 0 ≤ (u : A⁺¹)) (hu₁ : ‖u‖ ≤ 1) :
    ‖(1 : A⁺¹) - u‖ ≤ 1 := by
  have h : (u : A⁺¹) ∈ Set.Icc 0 1 :=
    mem_Icc_iff_norm_le_one.mpr ⟨hu, by rwa [norm_inr]⟩
  have : (1 : A⁺¹) - u ∈ Set.Icc 0 1 := ⟨sub_nonneg.mpr h.2, sub_le_self _ h.1⟩
  exact (mem_Icc_iff_norm_le_one.mp this).2

/-- `‖a - a u‖² ≤ ‖a⋆a + b‖ + ‖b - b u‖` for a positive contraction `u`. -/
private lemma sq_norm_sub_mul_le (a b : A) {u : A} (hu : 0 ≤ (u : A⁺¹)) (hu₁ : ‖u‖ ≤ 1) :
    ‖a - a * u‖ ^ 2 ≤ ‖star a * a + b‖ + ‖b - b * u‖ := by
  set v : A⁺¹ := 1 - u
  have hv : ‖v‖ ≤ 1 := norm_one_sub_inr_le_one hu hu₁
  have hvs : star v = v := by simp [v, hu.isSelfAdjoint.star_eq, -inr_star]
  have ha : ((a - a * u : A) : A⁺¹) = (a : A⁺¹) * v := by simp [v, mul_sub]
  have hb : ((b - b * u : A) : A⁺¹) = (b : A⁺¹) * v := by simp [v, mul_sub]
  have key : star ((a : A⁺¹) * v) * ((a : A⁺¹) * v) =
      v * ((star a * a + b : A) : A⁺¹) * v - v * ((b : A⁺¹) * v) := by
    simp only [star_mul, hvs, inr_add, inr_mul, inr_star]
    noncomm_ring
  rw [sq, ← norm_inr (𝕜 := ℂ), ha, ← CStarRing.norm_star_mul_self, key,
    ← norm_inr (𝕜 := ℂ) (b - b * u), hb, ← norm_inr (𝕜 := ℂ) (star a * a + b)]
  calc
    _ ≤ ‖v * ((star a * a + b : A) : A⁺¹) * v‖ + ‖v * ((b : A⁺¹) * v)‖ := norm_sub_le _ _
    _ ≤ ‖v‖ * ‖((star a * a + b : A) : A⁺¹)‖ * ‖v‖ + ‖v‖ * ‖(b : A⁺¹) * v‖ := by
      gcongr
      · exact norm_mul₃_le
      · exact norm_mul_le _ _
    _ ≤ 1 * ‖((star a * a + b : A) : A⁺¹)‖ * 1 + 1 * ‖(b : A⁺¹) * v‖ := by gcongr
    _ = _ := by ring

variable (I : Submodule ℂ A) [I.IsTwoSidedIdeal] [hI : IsClosed (I : Set A)]

namespace Quotient

/-- The involution on the quotient by a closed two-sided ideal `I : Submodule ℂ A`. -/
noncomputable instance instStar : Star (A ⧸ I) where
  star := Quotient.map' star fun a b h ↦ by
    have hab : a - b ∈ I := (Submodule.Quotient.eq I).mp (Quotient.sound h)
    exact Quotient.exact <| (Submodule.Quotient.eq I).mpr <| by
      rw [← star_sub]
      exact star_mem_of_isClosed I hab

/-- The involution commutes with the quotient map. -/
@[simp]
lemma mk_star (a : A) : (mk (star a) : A ⧸ I) = star (mk a) :=
  rfl

/-- The involution descended from `A` makes the quotient a ⋆-ring. -/
noncomputable instance instStarRing : StarRing (A ⧸ I) where
  star_involutive x := by
    induction x using Submodule.Quotient.induction_on with | H a => ?_
    exact congr_arg mk (star_star a)
  star_mul x y := by
    induction x using Submodule.Quotient.induction_on with | H a => ?_
    induction y using Submodule.Quotient.induction_on with | H b => ?_
    exact congr_arg mk (star_mul a b)
  star_add x y := by
    induction x using Submodule.Quotient.induction_on with | H a => ?_
    induction y using Submodule.Quotient.induction_on with | H b => ?_
    exact congr_arg mk (star_add a b)

/-- The involution on the quotient is conjugate-linear. -/
instance : StarModule ℂ (A ⧸ I) where
  star_smul c x := by
    induction x using Submodule.Quotient.induction_on with | H a => ?_
    exact congr_arg mk (star_smul c a)

/-- `‖a + I‖² ≤ ‖a⋆a + b‖` for every `b ∈ I`. -/
private lemma sq_norm_mk_le (a : A) {b : A} (hb : b ∈ I) :
    ‖(mk a : A ⧸ I)‖ ^ 2 ≤ ‖star a * a + b‖ := by
  set J := I.toNonUnitalStarSubalgebra
  let _ := CStarAlgebra.spectralOrder J
  have _ := CStarAlgebra.spectralOrderedRing J
  have hl := CStarAlgebra.increasingApproximateUnit J
  let b' : J := ⟨b, hb⟩
  have h : Tendsto (fun u : J ↦ ‖star a * a + b‖ + ‖b - b * u‖) (CStarAlgebra.approximateUnit J)
      (𝓝 (‖star a * a + b‖ + 0)) := by
    refine tendsto_const_nhds.add ?_
    have := (continuous_subtype_val.tendsto b').comp (hl.tendsto_mul_left b')
    simpa [Function.comp_def, ← dist_eq_norm', ← tendsto_iff_dist_tendsto_zero] using this
  rw [add_zero] at h
  refine ge_of_tendsto h ?_
  filter_upwards [hl.eventually_nonneg, hl.eventually_norm] with u hu hu₁
  have hu' : 0 ≤ ((u : A) : A⁺¹) := by
    simpa using OrderHomClass.mono
      ((inrNonUnitalStarAlgHom ℂ A).comp (NonUnitalStarSubalgebraClass.subtype J)) hu
  calc
    _ ≤ ‖a - a * u‖ ^ 2 := by
      gcongr
      simpa [sub_eq_add_neg] using
        norm_mk_le_norm_add I a (I.neg_mem (IsTwoSidedIdeal.mul_mem_left a u.2))
    _ ≤ _ := sq_norm_sub_mul_le a b hu' hu₁

/-- The quotient norm by a closed two-sided ideal `I : Submodule ℂ A` of a C⋆-algebra satisfies the
C⋆-identity. For a closed `J : TwoSidedIdeal A`, the quotient is `A ⧸ J.toSubmodule`. -/
instance instCStarRing : CStarRing (A ⧸ I) where
  norm_mul_self_le x := by
    induction x using Submodule.Quotient.induction_on with | H a => ?_
    rw [← mk_star, ← mk_mul, ← sq]
    refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
    obtain ⟨c, hc, hcε⟩ := Submodule.Quotient.norm_mk_lt (mk (star a * a) : A ⧸ I) hε
    have hb : c - star a * a ∈ I := (Submodule.Quotient.eq I).mp hc
    calc
      _ ≤ ‖star a * a + (c - star a * a)‖ := sq_norm_mk_le I a hb
      _ = ‖c‖ := by rw [add_sub_cancel]
      _ < _ := hcε

/-- The quotient of a C⋆-algebra by a closed two-sided ideal `I : Submodule ℂ A` is a C⋆-algebra.
For a closed `J : TwoSidedIdeal A`, the quotient is `A ⧸ J.toSubmodule`. -/
noncomputable instance instNonUnitalCStarAlgebra : NonUnitalCStarAlgebra (A ⧸ I) where

/-- The quotient of a commutative C⋆-algebra by a closed two-sided ideal `I : Submodule ℂ A` is a
commutative C⋆-algebra. -/
noncomputable instance instNonUnitalCommCStarAlgebra {A : Type*} [NonUnitalCommCStarAlgebra A]
    (I : Submodule ℂ A) [I.IsTwoSidedIdeal] [IsClosed (I : Set A)] :
    NonUnitalCommCStarAlgebra (A ⧸ I) where
  mul_comm x y := by
    induction x using Submodule.Quotient.induction_on with | H a => ?_
    induction y using Submodule.Quotient.induction_on with | H b => ?_
    exact congr_arg mk (mul_comm a b)

/-- The quotient map onto the quotient by a closed two-sided ideal `I : Submodule ℂ A`, as a
⋆-homomorphism. -/
noncomputable def mkStarₙₐ : A →⋆ₙₐ[ℂ] A ⧸ I where
  __ := mkₙₐ I
  map_star' _ := rfl

/-- The ⋆-homomorphism sends `a` to its class. -/
@[simp]
lemma mkStarₙₐ_apply (a : A) : mkStarₙₐ I a = mk a :=
  rfl

/-- The quotient ⋆-homomorphism is surjective. -/
lemma mkStarₙₐ_surjective : Function.Surjective (mkStarₙₐ I) :=
  mk_surjective I

/-- The kernel of the quotient ⋆-homomorphism is the ideal. -/
@[simp]
lemma ker_mkStarₙₐ : NonUnitalAlgHom.ker ℂ (mkStarₙₐ I) = I :=
  ker_mkₙₐ I

section Lift

variable {B : Type*} [NonUnitalRing B] [Module ℂ B] [Star B] (φ : A →⋆ₙₐ[ℂ] B)

/-- A ⋆-homomorphism vanishing on `I` factors through the quotient by `I`. -/
noncomputable def liftStarₙₐ (hφ : I ≤ NonUnitalAlgHom.ker ℂ φ) : A ⧸ I →⋆ₙₐ[ℂ] B where
  __ := liftₙₐ I (φ : A →ₙₐ[ℂ] B) hφ
  map_star' x := by
    induction x using Submodule.Quotient.induction_on with | H a => ?_
    exact map_star φ a

/-- The induced ⋆-homomorphism sends the class of `a` to `φ a`. -/
@[simp]
lemma liftStarₙₐ_mk (hφ : I ≤ NonUnitalAlgHom.ker ℂ φ) (a : A) : liftStarₙₐ I φ hφ (mk a) = φ a :=
  rfl

/-- The induced ⋆-homomorphism composed with the quotient map is `φ`. -/
@[simp]
lemma liftStarₙₐ_comp_mkStarₙₐ (hφ : I ≤ NonUnitalAlgHom.ker ℂ φ) :
    (liftStarₙₐ I φ hφ).comp (mkStarₙₐ I) = φ :=
  rfl

end Lift

end Quotient

end CStarQuotient

section CStarQuotientUnital

variable {A : Type*} [CStarAlgebra A] (I : Submodule ℂ A) [I.IsTwoSidedIdeal] [IsClosed (I : Set A)]

namespace Quotient

/-- The quotient of a unital C⋆-algebra by a closed two-sided ideal `I : Submodule ℂ A` is a unital
C⋆-algebra. For a closed `J : TwoSidedIdeal A`, the quotient is `A ⧸ J.toSubmodule`. -/
noncomputable instance instCStarAlgebra : CStarAlgebra (A ⧸ I) where

-- No diamond with the non-unital structure.
example : (instCStarAlgebra I).toNonUnitalCStarAlgebra = instNonUnitalCStarAlgebra I := by
  with_reducible_and_instances rfl

/-- The quotient of a commutative unital C⋆-algebra by a closed two-sided ideal `I : Submodule ℂ A`
is a commutative unital C⋆-algebra. -/
noncomputable instance instCommCStarAlgebra {A : Type*} [CommCStarAlgebra A] (I : Submodule ℂ A)
    [I.IsTwoSidedIdeal] [IsClosed (I : Set A)] : CommCStarAlgebra (A ⧸ I) where
  mul_comm x y := by
    induction x using Submodule.Quotient.induction_on with | H a => ?_
    induction y using Submodule.Quotient.induction_on with | H b => ?_
    exact congr_arg mk (mul_comm a b)

/-- The quotient map onto the quotient by a closed two-sided ideal `I : Submodule ℂ A`, as a unital
⋆-homomorphism. -/
noncomputable def mkStarₐ : A →⋆ₐ[ℂ] A ⧸ I where
  __ := mkₐ I
  map_star' _ := rfl

/-- The unital ⋆-homomorphism sends `a` to its class. -/
@[simp]
lemma mkStarₐ_apply (a : A) : mkStarₐ I a = mk a :=
  rfl

end Quotient

end CStarQuotientUnital

end Submodule

/-! ### The first isomorphism theorem -/

namespace NonUnitalStarAlgHom

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] (φ : A →⋆ₙₐ[ℂ] B)

/-- The ⋆-homomorphism out of the quotient by the kernel induced by `φ`. -/
noncomputable def kerLift : A ⧸ NonUnitalAlgHom.ker ℂ φ →⋆ₙₐ[ℂ] B :=
  Submodule.Quotient.liftStarₙₐ (NonUnitalAlgHom.ker ℂ φ) φ le_rfl

/-- The map induced on the quotient by the kernel sends the class of `a` to `φ a`. -/
@[simp]
lemma kerLift_mk (a : A) : kerLift φ (Submodule.Quotient.mk a) = φ a :=
  rfl

/-- The map induced on the quotient by the kernel is injective. -/
lemma kerLift_injective : Function.Injective (kerLift φ) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using Submodule.Quotient.induction_on with | H a => ?_
  rw [Submodule.Quotient.mk_eq_zero, NonUnitalAlgHom.mem_ker]
  exact hx

/-- **First isomorphism theorem** for C⋆-algebras: a ⋆-homomorphism induces a ⋆-isomorphism from
the quotient by its kernel onto its range. -/
noncomputable def quotientKerEquivRange : A ⧸ NonUnitalAlgHom.ker ℂ φ ≃⋆ₐ[ℂ] φ.range :=
  StarAlgEquiv.ofBijective ((kerLift φ).codRestrict φ.range fun x ↦ by
    induction x using Submodule.Quotient.induction_on with | H a => ?_
    exact ⟨a, rfl⟩)
    ⟨fun x y h ↦ kerLift_injective φ (congr_arg Subtype.val h), by
      rintro ⟨_, a, rfl⟩
      exact ⟨Submodule.Quotient.mk a, rfl⟩⟩

/-- The isomorphism onto the range sends the class of `a` to `φ a`. -/
@[simp]
lemma quotientKerEquivRange_mk (a : A) : (quotientKerEquivRange φ (Submodule.Quotient.mk a) : B) = φ a :=
  rfl

/-- The ⋆-isomorphism from the quotient by the kernel onto the range is isometric. -/
lemma norm_quotientKerEquivRange (x : A ⧸ NonUnitalAlgHom.ker ℂ φ) :
    ‖(quotientKerEquivRange φ x : B)‖ = ‖x‖ :=
  NonUnitalStarAlgHom.norm_map (kerLift φ) (kerLift_injective φ) x

/-- The range of a ⋆-homomorphism of C⋆-algebras is closed. -/
theorem isClosed_range : IsClosed (φ.range : Set B) := by
  have hiso : Isometry (kerLift φ) :=
    (AddMonoidHomClass.isometry_iff_norm _).mpr (norm_quotientKerEquivRange φ)
  have : Set.range (kerLift φ) = φ.range := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      induction x using Submodule.Quotient.induction_on with | H a => ?_
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨Submodule.Quotient.mk a, rfl⟩
  rw [← this]
  exact hiso.isUniformInducing.isComplete_range.isClosed

/-- A ⋆-homomorphism of C⋆-algebras with dense range is surjective. -/
lemma surjective_of_denseRange (hφ : DenseRange φ) : Function.Surjective φ := by
  rw [← Set.range_eq_univ, ← NonUnitalStarAlgHom.coe_range, ← (isClosed_range φ).closure_eq]
  exact hφ.closure_eq

end NonUnitalStarAlgHom

section Examples

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

noncomputable example : CStarAlgebra (A ⧸ (⊥ : Submodule ℂ A)) :=
  inferInstance

noncomputable example : CStarAlgebra (A ⧸ (⊤ : Submodule ℂ A)) :=
  inferInstance

noncomputable example (φ : A →⋆ₙₐ[ℂ] B) : CStarAlgebra (A ⧸ NonUnitalAlgHom.ker ℂ φ) :=
  inferInstance

noncomputable example (I : TwoSidedIdeal A) [IsClosed (I : Set A)] : CStarAlgebra (A ⧸ I.toSubmodule) :=
  inferInstance

-- The statements for a closed ring-theoretic two-sided ideal, through `TwoSidedIdeal.toSubmodule`.
example {C : Type*} [NonUnitalCStarAlgebra C] (I : TwoSidedIdeal C) [IsClosed (I : Set C)] {a : C}
    (ha : a ∈ I) : star a ∈ I :=
  Submodule.star_mem_of_isClosed I.toSubmodule ha

noncomputable example {C : Type*} [NonUnitalCStarAlgebra C] (I : TwoSidedIdeal C)
    [IsClosed (I : Set C)] : NonUnitalCStarAlgebra (C ⧸ I.toSubmodule) :=
  inferInstance

-- Where Mathlib's quotient by an `Ideal` applies, its instances are the ones found.
example {R : Type*} [NormedCommRing R] :
    (inferInstance : Ring (R ⧸ (⊥ : Ideal R))) = Ideal.Quotient.ring ⊥ := by
  with_reducible_and_instances rfl

example {R : Type*} [NormedCommRing R] :
    (inferInstance : NonUnitalSeminormedRing (R ⧸ (⊥ : Ideal R))) =
      (Ideal.Quotient.semiNormedCommRing ⊥).toNonUnitalSeminormedRing := by
  with_reducible_and_instances rfl

end Examples
