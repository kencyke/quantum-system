/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Analysis.CStarAlgebra.Hom
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Normed.Algebra.Basic
public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Topology.MetricSpace.Completion

/-!
# Direct limits of normed groups along isometries

For a directed system `f` of seminormed groups `G i` whose maps preserve the norm
(`DirectLimit.IsometricSystem f`), the norm of an element of the direct limit is the norm of any
representative in a component. This makes the direct limit a seminormed group, a normed group when
the components are, and a normed space, a seminormed or normed ring, with or without a unit, a
normed algebra, a normed `⋆`-group, a C⋆-ring or an inner product space when the components and the
maps are; each component embeds isometrically. In the completion of the direct limit the union of
the components is dense, and the component at a greatest index is all of it. The maps of a directed
system of C⋆-algebras along injective `⋆`-homomorphisms are isometric
(`DirectLimit.IsometricSystem.of_injective`), so its completion is the C⋆-inductive limit, of
algebras that need not have a unit.

The instances for rings without a unit have a low priority: a system of unital rings along unital
homomorphisms finds its structure through the unital instances first.

Mathlib's `DirectLimit G f` is a quotient and carries the quotient topology, which is not the
topology of this norm, so the normed direct limit is the type synonym `NormedDirectLimit G f`, with
the algebraic structure of `DirectLimit G f`.

## Main definitions

* `DirectLimit.IsometricSystem f` — the maps of the directed system `f` preserve the norm.
* `NormedDirectLimit G f` — the direct limit of an isometric directed system, with its norm.
* `NormedDirectLimit.mk i x` — the class of `x : G i`.
* `NormedDirectLimit.ofₗᵢ 𝕜 i`, `NormedDirectLimit.ofAlgHom 𝕜 i` — the canonical map of the
  component `G i`, as a linear isometry and as an algebra homomorphism.

## Main results

* `NormedDirectLimit.norm_mk` — the norm of the class of `x : G i` is `‖x‖`.
* `NormedDirectLimit.inner_mk` — the inner product of the classes of `x y : G i` is `⟪x, y⟫`.
* `DirectLimit.IsometricSystem.of_injective` — injective `⋆`-homomorphisms of C⋆-algebras form an
  isometric system.
* `NormedDirectLimit.dense_iUnion_range_coe_mk` — the components are dense in the completion;
  `NormedDirectLimit.completion_map_mk_surjective` — the completion of a component at a greatest
  index is the whole completion.
-/

@[expose] public section

open scoped InnerProductSpace
open UniformSpace

variable {ι : Type*} [Preorder ι] {G : ι → Type*} {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*}
  {f : ∀ i j (h : i ≤ j), T h} [∀ i j (h : i ≤ j), FunLike (T h) (G i) (G j)]

/-- The maps of a directed system of normed groups **preserve the norm**. -/
class DirectLimit.IsometricSystem [∀ i, Norm (G i)] (f : ∀ i j (h : i ≤ j), T h) : Prop where
  /-- Each map of the system preserves the norm. -/
  norm_map (i j : ι) (h : i ≤ j) (x : G i) : ‖f i j h x‖ = ‖x‖

namespace DirectLimit.IsometricSystem

/-- **Injective `⋆`-homomorphisms of C⋆-algebras form an isometric system**: an injective
`⋆`-homomorphism of C⋆-algebras is isometric. -/
theorem of_injective [∀ i, NonUnitalCStarAlgebra (G i)]
    [∀ i j h, NonUnitalAlgHomClass (T h) ℂ (G i) (G j)] [∀ i j h, StarHomClass (T h) (G i) (G j)]
    (hf : ∀ i j (h : i ≤ j), Function.Injective (f i j h)) : IsometricSystem f :=
  ⟨fun i j h x => NonUnitalStarAlgHom.norm_map (f i j h) (hf i j h) x⟩

/-- The maps of an isometric directed system of inner product spaces along linear maps preserve the
inner product. -/
lemma inner_map {𝕜 : Type*} [RCLike 𝕜] [∀ i, SeminormedAddCommGroup (G i)]
    [∀ i, InnerProductSpace 𝕜 (G i)] [∀ i j h, LinearMapClass (T h) 𝕜 (G i) (G j)]
    [IsometricSystem f] (i j : ι) (h : i ≤ j) (x y : G i) :
    ⟪f i j h x, f i j h y⟫_𝕜 = ⟪x, y⟫_𝕜 :=
  LinearIsometry.inner_map_map
    (⟨(f i j h : G i →ₗ[𝕜] G j), IsometricSystem.norm_map i j h⟩ : G i →ₗᵢ[𝕜] G j) x y

end DirectLimit.IsometricSystem

variable [DirectedSystem G (f · · ·)] [IsDirectedOrder ι]

variable (G f) in
/-- The direct limit of a directed system, to be given the norm of an isometric system: a type
synonym of `DirectLimit G f`, whose quotient topology is not that of the norm. -/
def NormedDirectLimit : Type _ :=
  DirectLimit G f

namespace NormedDirectLimit

/-- The class of `x : G i` in the direct limit. -/
def mk (i : ι) (x : G i) : NormedDirectLimit G f :=
  (⟦⟨i, x⟩⟧ : DirectLimit G f)

/-- The class of `f i j h x` is that of `x`. -/
lemma mk_map (i j : ι) (h : i ≤ j) (x : G i) :
    (mk j (f i j h x) : NormedDirectLimit G f) = mk i x :=
  DirectLimit.mk_apply i j x h

/-- Every element of the direct limit is the class of an element of a component. -/
@[elab_as_elim] protected lemma induction {C : NormedDirectLimit G f → Prop}
    (ih : ∀ i x, C (mk i x)) (z : NormedDirectLimit G f) : C z :=
  DirectLimit.induction (C := C) f ih z

/-- Two elements of the direct limit are classes of elements of a common component. -/
lemma exists_eq_mk₂ (z w : NormedDirectLimit G f) : ∃ i x y, z = mk i x ∧ w = mk i y :=
  DirectLimit.exists_eq_mk₂ f z w

/-- Three elements of the direct limit are classes of elements of a common component. -/
lemma exists_eq_mk₃ (z w u : NormedDirectLimit G f) :
    ∃ i x y v, z = mk i x ∧ w = mk i y ∧ u = mk i v :=
  DirectLimit.exists_eq_mk₃ f z w u

variable [Nonempty ι]

/-! ### Algebraic structure -/

section Group

variable [∀ i, AddCommGroup (G i)] [∀ i j h, AddMonoidHomClass (T h) (G i) (G j)]

/-- The additive group structure of the direct limit of additive groups. -/
noncomputable instance : AddCommGroup (NormedDirectLimit G f) :=
  inferInstanceAs (AddCommGroup (DirectLimit G f))

/-- The class of `0` is `0`. -/
lemma mk_zero (i : ι) : (mk i 0 : NormedDirectLimit G f) = 0 :=
  (DirectLimit.zero_def i).symm

/-- Taking classes is additive. -/
lemma mk_add (i : ι) (x y : G i) : (mk i (x + y) : NormedDirectLimit G f) = mk i x + mk i y :=
  (DirectLimit.add_def i x y).symm

/-- Taking classes commutes with negation. -/
lemma mk_neg (i : ι) (x : G i) : (mk i (-x) : NormedDirectLimit G f) = -mk i x :=
  (DirectLimit.neg_def i x).symm

/-- Taking classes commutes with subtraction. -/
lemma mk_sub (i : ι) (x y : G i) : (mk i (x - y) : NormedDirectLimit G f) = mk i x - mk i y := by
  rw [sub_eq_add_neg, mk_add, mk_neg, ← sub_eq_add_neg]

end Group

section Module

variable {R : Type*} [Semiring R] [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
  [∀ i j h, LinearMapClass (T h) R (G i) (G j)]

/-- The module structure of the direct limit of modules along linear maps. -/
noncomputable instance : Module R (NormedDirectLimit G f) :=
  inferInstanceAs (Module R (DirectLimit G f))

/-- Taking classes commutes with the scalar action. -/
lemma mk_smul (i : ι) (r : R) (x : G i) : (mk i (r • x) : NormedDirectLimit G f) = r • mk i x :=
  (DirectLimit.smul_def i x r).symm

end Module

section NonUnitalRing

variable [∀ i, NonUnitalRing (G i)] [∀ i j h, NonUnitalRingHomClass (T h) (G i) (G j)]

/-- The direct limit of rings, which need not have a unit, along ring homomorphisms is a ring. -/
noncomputable instance (priority := 50) : NonUnitalRing (NormedDirectLimit G f) :=
  inferInstanceAs (NonUnitalRing (DirectLimit G f))

/-- Taking classes is multiplicative. -/
lemma mk_mul (i : ι) (x y : G i) : (mk i (x * y) : NormedDirectLimit G f) = mk i x * mk i y :=
  (DirectLimit.mul_def i x y).symm

end NonUnitalRing

section NonUnitalAlgebra

variable {R : Type*} [Semiring R] [∀ i, NonUnitalRing (G i)] [∀ i, Module R (G i)]
  [∀ i j h, NonUnitalAlgHomClass (T h) R (G i) (G j)]

/-- The scalar action on a direct limit of algebras is compatible with left multiplication. -/
instance (priority := 50) [∀ i, IsScalarTower R (G i) (G i)] :
    IsScalarTower R (NormedDirectLimit G f) (NormedDirectLimit G f) where
  smul_assoc r z w := by
    obtain ⟨i, x, y, rfl, rfl⟩ := exists_eq_mk₂ z w
    rw [← mk_smul, smul_eq_mul, smul_eq_mul, ← mk_mul, ← mk_mul, ← mk_smul, smul_mul_assoc]

/-- The scalar action on a direct limit of algebras is compatible with right multiplication. -/
instance (priority := 50) [∀ i, SMulCommClass R (G i) (G i)] :
    SMulCommClass R (NormedDirectLimit G f) (NormedDirectLimit G f) where
  smul_comm r z w := by
    obtain ⟨i, x, y, rfl, rfl⟩ := exists_eq_mk₂ z w
    rw [smul_eq_mul, smul_eq_mul, ← mk_smul, ← mk_mul, ← mk_mul, ← mk_smul, mul_smul_comm]

end NonUnitalAlgebra

section Ring

variable [∀ i, Ring (G i)] [∀ i j h, RingHomClass (T h) (G i) (G j)]

/-- The direct limit of rings along ring homomorphisms is a ring. -/
noncomputable instance : Ring (NormedDirectLimit G f) :=
  inferInstanceAs (Ring (DirectLimit G f))

/-- The class of `1` is `1`. -/
lemma mk_one (i : ι) : (mk i 1 : NormedDirectLimit G f) = 1 :=
  (DirectLimit.one_def i).symm

/-- The universal property of the direct limit of rings: compatible ring homomorphisms out of the
components give a ring homomorphism out of the direct limit. -/
noncomputable def liftRingHom {P : Type*} [NonAssocSemiring P] (g : ∀ i, G i →+* P)
    (Hg : ∀ i j h x, g j (f i j h x) = g i x) : NormedDirectLimit G f →+* P :=
  DirectLimit.Ring.lift G f P g Hg

/-- `NormedDirectLimit.liftRingHom g Hg` restricts to `g i` on the component `G i`. -/
@[simp] lemma liftRingHom_mk {P : Type*} [NonAssocSemiring P] (g : ∀ i, G i →+* P)
    (Hg : ∀ i j h x, g j (f i j h x) = g i x) (i : ι) (x : G i) :
    liftRingHom g Hg (mk i x) = g i x :=
  rfl

end Ring

section Algebra

variable {R : Type*} [CommSemiring R] [∀ i, Ring (G i)] [∀ i, Algebra R (G i)]
  [∀ i j h, AlgHomClass (T h) R (G i) (G j)]

/-- The direct limit of algebras along algebra homomorphisms is an algebra. -/
noncomputable instance : Algebra R (NormedDirectLimit G f) :=
  inferInstanceAs (Algebra R (DirectLimit G f))

variable (R) in
/-- The canonical map of a component into the direct limit, as an algebra homomorphism. -/
noncomputable def ofAlgHom (i : ι) : G i →ₐ[R] NormedDirectLimit G f :=
  DirectLimit.Algebra.of G f i

/-- `NormedDirectLimit.ofAlgHom R i` takes classes. -/
@[simp] lemma ofAlgHom_apply (i : ι) (x : G i) :
    ofAlgHom R i x = (mk i x : NormedDirectLimit G f) :=
  rfl

/-- The universal property of the direct limit of algebras: compatible algebra homomorphisms out of
the components give an algebra homomorphism out of the direct limit. -/
noncomputable def liftAlgHom {P : Type*} [Semiring P] [Algebra R P] (g : ∀ i, G i →ₐ[R] P)
    (Hg : ∀ i j h x, g j (f i j h x) = g i x) : NormedDirectLimit G f →ₐ[R] P :=
  DirectLimit.Algebra.lift G f P g Hg

/-- `NormedDirectLimit.liftAlgHom g Hg` restricts to `g i` on the component `G i`. -/
@[simp] lemma liftAlgHom_mk {P : Type*} [Semiring P] [Algebra R P] (g : ∀ i, G i →ₐ[R] P)
    (Hg : ∀ i j h x, g j (f i j h x) = g i x) (i : ι) (x : G i) :
    liftAlgHom g Hg (mk i x) = g i x :=
  rfl

end Algebra

section Star

variable [∀ i, Star (G i)] [∀ i j h, StarHomClass (T h) (G i) (G j)]

/-- The involution of the direct limit along `⋆`-maps: that of a representative. -/
noncomputable instance : Star (NormedDirectLimit G f) :=
  inferInstanceAs (Star (DirectLimit G f))

omit [Nonempty ι] in
/-- Taking classes commutes with the involution. -/
lemma mk_star (i : ι) (x : G i) : (mk i (star x) : NormedDirectLimit G f) = star (mk i x) :=
  (DirectLimit.star_def i x).symm

end Star

/-- The direct limit of `⋆`-additive groups along additive `⋆`-maps is a `⋆`-additive monoid. -/
noncomputable instance [∀ i, AddCommGroup (G i)] [∀ i j h, AddMonoidHomClass (T h) (G i) (G j)]
    [∀ i, StarAddMonoid (G i)] [∀ i j h, StarHomClass (T h) (G i) (G j)] :
    StarAddMonoid (NormedDirectLimit G f) :=
  inferInstanceAs (StarAddMonoid (DirectLimit G f))

/-- The direct limit of `⋆`-rings along `⋆`-homomorphisms is a `⋆`-ring. -/
noncomputable instance [∀ i, Ring (G i)] [∀ i j h, RingHomClass (T h) (G i) (G j)]
    [∀ i, StarRing (G i)] [∀ i j h, StarHomClass (T h) (G i) (G j)] :
    StarRing (NormedDirectLimit G f) :=
  inferInstanceAs (StarRing (DirectLimit G f))

/-- The direct limit of `⋆`-rings, which need not have a unit, along `⋆`-homomorphisms is a
`⋆`-ring. -/
noncomputable instance (priority := 50) [∀ i, NonUnitalRing (G i)]
    [∀ i j h, NonUnitalRingHomClass (T h) (G i) (G j)] [∀ i, StarRing (G i)]
    [∀ i j h, StarHomClass (T h) (G i) (G j)] : StarRing (NormedDirectLimit G f) :=
  inferInstanceAs (StarRing (DirectLimit G f))

/-- The involution of the direct limit of `⋆`-modules is conjugate-linear. -/
instance {R : Type*} [Semiring R] [Star R] [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
    [∀ i j h, LinearMapClass (T h) R (G i) (G j)] [∀ i, Star (G i)]
    [∀ i j h, StarHomClass (T h) (G i) (G j)] [∀ i, StarModule R (G i)] :
    StarModule R (NormedDirectLimit G f) :=
  inferInstanceAs (StarModule R (DirectLimit G f))

/-! ### Norm -/

section Seminormed

variable [∀ i, SeminormedAddCommGroup (G i)] [∀ i j h, AddMonoidHomClass (T h) (G i) (G j)]
  [DirectLimit.IsometricSystem f]

variable (G f) in
/-- The seminorm of the direct limit along isometries: the norm of a representative. -/
noncomputable def seminorm : AddGroupSeminorm (NormedDirectLimit G f) where
  toFun := DirectLimit.lift f (fun _ x => ‖x‖) fun i j h x =>
    (DirectLimit.IsometricSystem.norm_map i j h x).symm
  map_zero' := by
    rw [← mk_zero (Classical.arbitrary ι)]
    exact norm_zero
  add_le' z w := by
    obtain ⟨i, x, y, rfl, rfl⟩ := exists_eq_mk₂ z w
    rw [← mk_add]
    exact norm_add_le x y
  neg' z := by
    induction z using NormedDirectLimit.induction with | _ i x
    rw [← mk_neg]
    exact norm_neg x

/-- The direct limit of seminormed groups along isometries is a seminormed group. -/
noncomputable instance seminormedAddCommGroup : SeminormedAddCommGroup (NormedDirectLimit G f) :=
  (seminorm G f).toSeminormedAddCommGroup

/-- The norm of the class of `x : G i` in the direct limit is `‖x‖`. -/
@[simp] lemma norm_mk (i : ι) (x : G i) : ‖(mk i x : NormedDirectLimit G f)‖ = ‖x‖ :=
  rfl

/-- Taking classes is isometric. -/
lemma isometry_mk (i : ι) : Isometry (mk i : G i → NormedDirectLimit G f) :=
  Isometry.of_dist_eq fun x y => by rw [dist_eq_norm, dist_eq_norm, ← mk_sub, norm_mk]

/-- **The components are dense in the completion** of the direct limit. -/
theorem dense_iUnion_range_coe_mk :
    Dense (⋃ i, Set.range fun x : G i =>
      ((mk i x : NormedDirectLimit G f) : Completion (NormedDirectLimit G f))) := by
  refine Completion.denseRange_coe.mono ?_
  rintro _ ⟨z, rfl⟩
  induction z using NormedDirectLimit.induction with | _ i x
  exact Set.mem_iUnion.2 ⟨i, x, rfl⟩

/-- **The completion of a component at a greatest index is the whole completion** of the direct
limit: its range is complete, hence closed, and contains every class. -/
theorem completion_map_mk_surjective (i : ι) (hi : IsTop i) :
    Function.Surjective (Completion.map (mk i : G i → NormedDirectLimit G f)) := by
  have hclosed : IsClosed (Set.range (Completion.map (mk i : G i → NormedDirectLimit G f))) :=
    (isometry_mk i).completion_map.isUniformInducing.isComplete_range.isClosed
  have hdense : Dense (Set.range (Completion.map (mk i : G i → NormedDirectLimit G f))) := by
    refine Completion.denseRange_coe.mono ?_
    rintro _ ⟨z, rfl⟩
    induction z using NormedDirectLimit.induction with | _ j x
    exact ⟨(f j i (hi j) x : G i), by
      rw [Completion.map_coe (isometry_mk i).uniformContinuous, mk_map]⟩
  exact Set.range_eq_univ.1 (hclosed.closure_eq.symm.trans hdense.closure_eq)

/-- The involution of a direct limit of normed `⋆`-groups along isometric `⋆`-maps is isometric. -/
instance (priority := 50) normedStarGroup [∀ i, StarAddMonoid (G i)] [∀ i, NormedStarGroup (G i)]
    [∀ i j h, StarHomClass (T h) (G i) (G j)] : NormedStarGroup (NormedDirectLimit G f) where
  norm_star_le z := by
    induction z using NormedDirectLimit.induction with | _ i x
    rw [← mk_star, norm_mk, norm_mk]
    exact (norm_star x).le

end Seminormed

section Normed

variable [∀ i, NormedAddCommGroup (G i)] [∀ i j h, AddMonoidHomClass (T h) (G i) (G j)]
  [DirectLimit.IsometricSystem f]

/-- The direct limit of normed groups along isometries is a normed group. -/
noncomputable instance normedAddCommGroup : NormedAddCommGroup (NormedDirectLimit G f) :=
  NormedAddCommGroup.ofSeparation fun z hz => by
    induction z using NormedDirectLimit.induction with | _ i x
    rw [norm_mk, norm_eq_zero] at hz
    rw [hz, mk_zero]

end Normed

section NormedSpace

variable {𝕜 : Type*} [NormedField 𝕜] [∀ i, SeminormedAddCommGroup (G i)]
  [∀ i, NormedSpace 𝕜 (G i)] [∀ i j h, LinearMapClass (T h) 𝕜 (G i) (G j)]
  [DirectLimit.IsometricSystem f]

/-- The direct limit of normed spaces along linear isometries is a normed space. -/
noncomputable instance normedSpace : NormedSpace 𝕜 (NormedDirectLimit G f) where
  norm_smul_le r z := by
    induction z using NormedDirectLimit.induction with | _ i x
    rw [← mk_smul, norm_mk, norm_mk]
    exact norm_smul_le r x

variable (𝕜) in
/-- The canonical map of a component into the direct limit along linear isometries, as a linear
isometry. -/
noncomputable def ofₗᵢ (i : ι) : G i →ₗᵢ[𝕜] NormedDirectLimit G f where
  toFun := mk i
  map_add' := mk_add i
  map_smul' r x := mk_smul i r x
  norm_map' _ := rfl

/-- `NormedDirectLimit.ofₗᵢ 𝕜 i` takes classes. -/
@[simp] lemma ofₗᵢ_apply (i : ι) (x : G i) : ofₗᵢ 𝕜 i x = (mk i x : NormedDirectLimit G f) :=
  rfl

end NormedSpace

section NonUnitalSeminormedRing

variable [∀ i, NonUnitalSeminormedRing (G i)] [∀ i j h, NonUnitalRingHomClass (T h) (G i) (G j)]
  [DirectLimit.IsometricSystem f]

/-- The direct limit of seminormed rings, which need not have a unit, along isometric ring
homomorphisms is a seminormed ring. -/
noncomputable instance (priority := 50) nonUnitalSeminormedRing :
    NonUnitalSeminormedRing (NormedDirectLimit G f) where
  __ : SeminormedAddCommGroup (NormedDirectLimit G f) := inferInstance
  __ : NonUnitalRing (NormedDirectLimit G f) := inferInstance
  norm_mul_le z w := by
    obtain ⟨i, x, y, rfl, rfl⟩ := exists_eq_mk₂ z w
    rw [← mk_mul, norm_mk, norm_mk, norm_mk]
    exact norm_mul_le x y

end NonUnitalSeminormedRing

section NonUnitalNormedRing

variable [∀ i, NonUnitalNormedRing (G i)] [∀ i j h, NonUnitalRingHomClass (T h) (G i) (G j)]
  [DirectLimit.IsometricSystem f]

/-- The direct limit of normed rings, which need not have a unit, along isometric ring
homomorphisms is a normed ring. -/
noncomputable instance (priority := 50) nonUnitalNormedRing :
    NonUnitalNormedRing (NormedDirectLimit G f) where
  __ : NonUnitalSeminormedRing (NormedDirectLimit G f) := inferInstance
  __ : NormedAddCommGroup (NormedDirectLimit G f) := inferInstance

/-- A direct limit of C⋆-rings, which need not have a unit, along isometric `⋆`-homomorphisms is a
C⋆-ring. -/
instance (priority := 50) nonUnitalCStarRing [∀ i, StarRing (G i)] [∀ i, CStarRing (G i)]
    [∀ i j h, StarHomClass (T h) (G i) (G j)] : CStarRing (NormedDirectLimit G f) where
  norm_mul_self_le z := by
    induction z using NormedDirectLimit.induction with | _ i x
    rw [← mk_star, ← mk_mul, norm_mk, norm_mk]
    exact CStarRing.norm_mul_self_le x

end NonUnitalNormedRing

section SeminormedRing

variable [∀ i, SeminormedRing (G i)] [∀ i j h, RingHomClass (T h) (G i) (G j)]
  [DirectLimit.IsometricSystem f]

/-- The direct limit of seminormed rings along isometric ring homomorphisms is a seminormed
ring. -/
noncomputable instance seminormedRing : SeminormedRing (NormedDirectLimit G f) where
  __ : SeminormedAddCommGroup (NormedDirectLimit G f) := inferInstance
  __ : Ring (NormedDirectLimit G f) := inferInstance
  norm_mul_le z w := by
    obtain ⟨i, x, y, rfl, rfl⟩ := exists_eq_mk₂ z w
    rw [← mk_mul, norm_mk, norm_mk, norm_mk]
    exact norm_mul_le x y

end SeminormedRing

section NormedRing

variable [∀ i, NormedRing (G i)] [∀ i j h, RingHomClass (T h) (G i) (G j)]
  [DirectLimit.IsometricSystem f]

/-- The direct limit of normed rings along isometric ring homomorphisms is a normed ring. -/
noncomputable instance normedRing : NormedRing (NormedDirectLimit G f) where
  __ : SeminormedRing (NormedDirectLimit G f) := inferInstance
  __ : NormedAddCommGroup (NormedDirectLimit G f) := inferInstance

/-- The involution of a direct limit of normed `⋆`-rings along isometric `⋆`-homomorphisms is
isometric. -/
instance normedStarGroupOfNormedRing [∀ i, StarRing (G i)] [∀ i, NormedStarGroup (G i)]
    [∀ i j h, StarHomClass (T h) (G i) (G j)] : NormedStarGroup (NormedDirectLimit G f) where
  norm_star_le z := by
    induction z using NormedDirectLimit.induction with | _ i x
    rw [← mk_star, norm_mk, norm_mk]
    exact (norm_star x).le

/-- A direct limit of unital C⋆-rings along isometric unital `⋆`-homomorphisms is a C⋆-ring. -/
instance cstarRing [∀ i, StarRing (G i)] [∀ i, CStarRing (G i)]
    [∀ i j h, StarHomClass (T h) (G i) (G j)] : CStarRing (NormedDirectLimit G f) where
  norm_mul_self_le z := by
    induction z using NormedDirectLimit.induction with | _ i x
    rw [← mk_star, ← mk_mul, norm_mk, norm_mk]
    exact CStarRing.norm_mul_self_le x

end NormedRing

section NormedAlgebra

variable {𝕜 : Type*} [NormedField 𝕜] [∀ i, SeminormedRing (G i)] [∀ i, NormedAlgebra 𝕜 (G i)]
  [∀ i j h, AlgHomClass (T h) 𝕜 (G i) (G j)] [DirectLimit.IsometricSystem f]

/-- The direct limit of normed algebras along isometric algebra homomorphisms is a normed
algebra. -/
noncomputable instance normedAlgebra : NormedAlgebra 𝕜 (NormedDirectLimit G f) where
  norm_smul_le r z := by
    induction z using NormedDirectLimit.induction with | _ i x
    rw [← mk_smul, norm_mk, norm_mk]
    exact norm_smul_le r x

end NormedAlgebra

section Inner

variable {𝕜 : Type*} [RCLike 𝕜] [∀ i, SeminormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace 𝕜 (G i)] [∀ i j h, LinearMapClass (T h) 𝕜 (G i) (G j)]
  [DirectLimit.IsometricSystem f]

omit [Nonempty ι] in
/-- The inner product of the direct limit: that of representatives in a common component. -/
noncomputable instance instInner : Inner 𝕜 (NormedDirectLimit G f) where
  inner := DirectLimit.lift₂ f f (fun _ x y => ⟪x, y⟫_𝕜) fun i j h x y =>
    (DirectLimit.IsometricSystem.inner_map i j h x y).symm

omit [Nonempty ι] in
/-- The inner product of the classes of `x y : G i` in the direct limit is `⟪x, y⟫`. -/
lemma inner_mk (i : ι) (x y : G i) :
    ⟪(mk i x : NormedDirectLimit G f), mk i y⟫_𝕜 = ⟪x, y⟫_𝕜 :=
  DirectLimit.lift₂_def _ _ _ _ _ _ _

/-- The direct limit of inner product spaces along linear isometries is an inner product space. -/
noncomputable instance innerProductSpace : InnerProductSpace 𝕜 (NormedDirectLimit G f) where
  norm_sq_eq_re_inner z := by
    induction z using NormedDirectLimit.induction with | _ i x
    rw [norm_mk, inner_mk]
    exact norm_sq_eq_re_inner x
  conj_inner_symm z w := by
    obtain ⟨i, x, y, rfl, rfl⟩ := exists_eq_mk₂ z w
    rw [inner_mk, inner_mk]
    exact inner_conj_symm x y
  add_left z w u := by
    obtain ⟨i, x, y, u, rfl, rfl, rfl⟩ := exists_eq_mk₃ z w u
    rw [← mk_add, inner_mk, inner_mk, inner_mk]
    exact inner_add_left x y u
  smul_left z w r := by
    obtain ⟨i, x, y, rfl, rfl⟩ := exists_eq_mk₂ z w
    rw [← mk_smul, inner_mk, inner_mk]
    exact inner_smul_left x y r

end Inner

end NormedDirectLimit
