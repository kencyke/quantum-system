/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import QuantumSystem.ForMathlib.Analysis.CStarAlgebra.Completion

/-!
# C⋆-seminorms

A **C⋆-seminorm** on a `⋆`-algebra `X` over `ℂ` is a submultiplicative seminorm `p` with
`p (x⋆ x) = p x ²`. The seminorm `x ↦ ‖Φ x‖` of a `⋆`-homomorphism `Φ` into a C⋆-algebra is one
(`CStarSeminorm.ofStarAlgHom`), and every C⋆-seminorm arises in this way: the completion of `X` for
`p`, in which the vectors of seminorm `0` are identified with `0`, is a C⋆-algebra, and the canonical
map `p.toCompletion : X → Completion p.Carrier` is a `⋆`-homomorphism whose seminorm is `p`
(`CStarSeminorm.ofStarAlgHom_toCompletion`). What holds for the seminorms of `⋆`-homomorphisms into
C⋆-algebras therefore holds for every C⋆-seminorm. A `⋆`-homomorphism of `X` into a C⋆-algebra
bounded by `p` extends to the completion (`CStarSeminorm.lift`), and uniquely when the completion
is a C⋆-algebra (`CStarSeminorm.lift_unique`).

When the C⋆-seminorms of `X` are bounded at each point, their supremum is a C⋆-seminorm, the
greatest one (`CStarSeminorm.greatest`).

The algebra `X` is not assumed unital. The definitions ask only for a non-unital `⋆`-ring with a
`ℂ`-module structure; the completion is a `NonUnitalCStarAlgebra` when the scalars are compatible
with the multiplication and the involution (`IsScalarTower ℂ X X`, `SMulCommClass ℂ X X`,
`StarModule ℂ X`).

## Main definitions

* `CStarSeminorm X` — the C⋆-seminorms on `X`.
* `CStarSeminorm.ofStarAlgHom Φ` — the C⋆-seminorm `x ↦ ‖Φ x‖`.
* `CStarSeminorm.Carrier p` — `X` with the seminorm `p`, a seminormed `⋆`-algebra; its completion is
  a `NonUnitalCStarAlgebra`.
* `CStarSeminorm.toCompletion p` — the `⋆`-homomorphism `X →⋆ₙₐ[ℂ] Completion p.Carrier`.
* `CStarSeminorm.lift p Φ h` — the extension to `Completion p.Carrier` of a `⋆`-homomorphism `Φ`
  with `‖Φ x‖ ≤ p x`.
* `CStarSeminorm.greatest hb` — the supremum of the C⋆-seminorms of `X`, when they are bounded at each
  point.

## Main results

* `CStarSeminorm.apply_star` — a C⋆-seminorm is invariant under the involution.
* `CStarSeminorm.norm_toCompletion` — `‖p.toCompletion x‖ = p x`;
  `CStarSeminorm.ofStarAlgHom_toCompletion` — `p` is the seminorm of `p.toCompletion`.
* `CStarSeminorm.lift_toCompletion`, `CStarSeminorm.lift_unique` — `p.lift Φ h` is the extension
  of `Φ`, and the only one when the completion is a C⋆-algebra.
* `CStarSeminorm.le_greatest`, `CStarSeminorm.greatest_le` — the supremum is the greatest C⋆-seminorm.
-/

@[expose] public section

open UniformSpace

/-- A **C⋆-seminorm** on a `⋆`-algebra `X` over `ℂ`: a submultiplicative seminorm (`RingSeminorm`)
with `p (c • x) = ‖c‖ p x` and `p (x⋆ x) = p x ²`. -/
structure CStarSeminorm (X : Type*) [NonUnitalRing X] [StarRing X] [Module ℂ X] extends
    RingSeminorm X where
  /-- The seminorm is absolutely homogeneous. -/
  map_smul' : ∀ (c : ℂ) x, toFun (c • x) = ‖c‖ * toFun x
  /-- The C⋆-identity `p (x⋆ x) = p x ²`. -/
  map_star_mul_self' : ∀ x, toFun (star x * x) = toFun x ^ 2

namespace CStarSeminorm

variable {X : Type*} [NonUnitalRing X] [StarRing X] [Module ℂ X]

/-- A C⋆-seminorm is a function on `X`. -/
instance instFunLike : FunLike (CStarSeminorm X) X ℝ where
  coe p := p.toFun
  coe_injective p q h := by
    cases p
    cases q
    congr
    exact DFunLike.coe_injective h

/-- A C⋆-seminorm is a submultiplicative seminorm. -/
instance instRingSeminormClass : RingSeminormClass (CStarSeminorm X) X ℝ where
  map_zero p := p.map_zero'
  map_add_le_add p := p.add_le'
  map_mul_le_mul p := p.mul_le'
  map_neg_eq_map p := p.neg'

/-- Two C⋆-seminorms with the same values are equal. -/
@[ext] lemma ext {p q : CStarSeminorm X} (h : ∀ x, p x = q x) : p = q :=
  DFunLike.ext p q h

variable (p : CStarSeminorm X)

/-- A C⋆-seminorm is absolutely homogeneous. -/
lemma apply_smul (c : ℂ) (x : X) : p (c • x) = ‖c‖ * p x := p.map_smul' c x

/-- A C⋆-seminorm satisfies the C⋆-identity `p (x⋆ x) = p x ²`. -/
lemma apply_star_mul_self (x : X) : p (star x * x) = p x ^ 2 := p.map_star_mul_self' x

/-- A C⋆-seminorm is subadditive on finite sums. -/
lemma apply_sum_le {ι : Type*} (s : Finset ι) (f : ι → X) :
    p (∑ i ∈ s, f i) ≤ ∑ i ∈ s, p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, map_zero]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (map_add_le_add p _ _).trans (add_le_add le_rfl ih)

/-- **A C⋆-seminorm is invariant under the involution**: `p x ² = p (x⋆ x) ≤ p x⋆ p x`. -/
theorem apply_star (x : X) : p (star x) = p x := by
  have key (y : X) : p y ≤ p (star y) := by
    have h : p y ^ 2 ≤ p (star y) * p y := by
      rw [← p.apply_star_mul_self]
      exact map_mul_le_mul p _ _
    by_cases hy : p y = 0
    · rw [hy]
      exact apply_nonneg p _
    · have hpos : 0 < p y := lt_of_le_of_ne (apply_nonneg p y) (Ne.symm hy)
      nlinarith
  exact le_antisymm (by simpa using key (star x)) (key x)

/-- The C⋆-seminorm `x ↦ ‖Φ x‖` of a `⋆`-homomorphism into a C⋆-normed algebra, in any universe;
the target need not be complete. -/
def ofStarAlgHom {C : Type*} [NonUnitalNormedRing C] [StarRing C] [CStarRing C] [NormedSpace ℂ C]
    (Φ : X →⋆ₙₐ[ℂ] C) : CStarSeminorm X where
  toFun x := ‖Φ x‖
  map_zero' := by rw [map_zero, norm_zero]
  add_le' x y := by rw [map_add]; exact norm_add_le _ _
  neg' x := by rw [map_neg, norm_neg]
  mul_le' x y := by rw [map_mul]; exact norm_mul_le _ _
  map_smul' c x := by rw [map_smul, norm_smul]
  map_star_mul_self' x := by rw [map_mul, map_star, CStarRing.norm_star_mul_self, sq]

/-- `CStarSeminorm.ofStarAlgHom Φ` is `x ↦ ‖Φ x‖`. -/
@[simp] lemma ofStarAlgHom_apply {C : Type*} [NonUnitalNormedRing C] [StarRing C] [CStarRing C]
    [NormedSpace ℂ C] (Φ : X →⋆ₙₐ[ℂ] C) (x : X) : ofStarAlgHom Φ x = ‖Φ x‖ :=
  rfl

/-- The zero seminorm is a C⋆-seminorm. -/
noncomputable instance instInhabited : Inhabited (CStarSeminorm X) :=
  ⟨ofStarAlgHom (0 : X →⋆ₙₐ[ℂ] ℂ)⟩

/-! ### The C⋆-algebra of a C⋆-seminorm -/

/-- The `⋆`-algebra `X` with the C⋆-seminorm `p`, a seminormed `⋆`-algebra satisfying the
C⋆-identity; its completion is a C⋆-algebra. -/
def Carrier (_p : CStarSeminorm X) : Type _ :=
  X

namespace Carrier

/-- The non-unital ring structure of `p.Carrier`. -/
noncomputable instance instNonUnitalRing : NonUnitalRing p.Carrier :=
  inferInstanceAs (NonUnitalRing X)

/-- The complex vector space structure of `p.Carrier`. -/
noncomputable instance instModule : Module ℂ p.Carrier :=
  inferInstanceAs (Module ℂ X)

/-- The star ring structure of `p.Carrier`. -/
noncomputable instance instStarRing : StarRing p.Carrier :=
  inferInstanceAs (StarRing X)

/-- The star of `p.Carrier` is conjugate-linear. -/
instance instStarModule [StarModule ℂ X] : StarModule ℂ p.Carrier :=
  inferInstanceAs (StarModule ℂ X)

/-- Scalars pass through a product from its left factor in `p.Carrier`: `(c • x) * y = c • (x * y)`. -/
instance instIsScalarTower [IsScalarTower ℂ X X] : IsScalarTower ℂ p.Carrier p.Carrier :=
  inferInstanceAs (IsScalarTower ℂ X X)

/-- Scalars pass through a product from its right factor in `p.Carrier`: `x * (c • y) = c • (x * y)`. -/
instance instSMulCommClass [SMulCommClass ℂ X X] : SMulCommClass ℂ p.Carrier p.Carrier :=
  inferInstanceAs (SMulCommClass ℂ X X)

/-- The C⋆-seminorm, as an additive group seminorm of `p.Carrier`. -/
def addGroupSeminorm : AddGroupSeminorm p.Carrier where
  toFun := p
  map_zero' := map_zero p
  add_le' := map_add_le_add p
  neg' := map_neg_eq_map p

/-- With the seminorm `p`, `p.Carrier` is a non-unital seminormed ring. The seminormed group
structure is not a separate instance, so that it is reached through this one only. -/
noncomputable instance instNonUnitalSeminormedRing : NonUnitalSeminormedRing p.Carrier :=
  letI : SeminormedAddCommGroup p.Carrier := (addGroupSeminorm p).toSeminormedAddCommGroup
  { (inferInstance : SeminormedAddCommGroup p.Carrier), Carrier.instNonUnitalRing p with
    norm_mul_le := map_mul_le_mul p }

/-- The seminorm of `p.Carrier` is `p`. -/
lemma norm_def (x : p.Carrier) : ‖x‖ = p x :=
  rfl

/-- With the seminorm `p`, `p.Carrier` is a seminormed space. -/
noncomputable instance instNormedSpace : NormedSpace ℂ p.Carrier where
  norm_smul_le c x := by
    rw [norm_def, norm_def]
    exact (p.apply_smul c x).le

/-- The star of `p.Carrier` is isometric for `p`. -/
instance instNormedStarGroup : NormedStarGroup p.Carrier where
  norm_star_le x := by
    rw [norm_def, norm_def]
    exact (p.apply_star x).le

end Carrier

/-- The completion of `p.Carrier` satisfies the C⋆-identity. -/
instance instCStarRing : CStarRing (Completion p.Carrier) :=
  Completion.cstarRing_of_norm_mul_self_le fun a => by
    rw [Carrier.norm_def, Carrier.norm_def, ← sq]
    exact (p.apply_star_mul_self a).ge

/-- **The completion of a `⋆`-algebra for a C⋆-seminorm is a C⋆-algebra.** -/
noncomputable instance instNonUnitalCStarAlgebra [StarModule ℂ X] [IsScalarTower ℂ X X]
    [SMulCommClass ℂ X X] : NonUnitalCStarAlgebra (Completion p.Carrier) where

/-- The canonical `⋆`-homomorphism of `X` into its completion for the C⋆-seminorm `p`. -/
noncomputable def toCompletion : X →⋆ₙₐ[ℂ] Completion p.Carrier where
  toFun x := ((show p.Carrier from x) : Completion p.Carrier)
  map_smul' c x := Completion.coe_smul c (show p.Carrier from x)
  map_zero' := Completion.coe_zero
  map_add' x y := Completion.coe_add (show p.Carrier from x) (show p.Carrier from y)
  map_mul' x y := Completion.coe_mul' (show p.Carrier from x) (show p.Carrier from y)
  map_star' x := (Completion.star_coe (show p.Carrier from x)).symm

/-- The norm of the completion on the image of `X` is `p`: `‖p.toCompletion x‖ = p x`. -/
lemma norm_toCompletion (x : X) : ‖p.toCompletion x‖ = p x :=
  (Completion.norm_coe (show p.Carrier from x)).trans (Carrier.norm_def p x)

/-- **Every C⋆-seminorm is the seminorm of a `⋆`-homomorphism into a C⋆-algebra**: `p` is the
seminorm of `p.toCompletion`. -/
theorem ofStarAlgHom_toCompletion [StarModule ℂ X] [IsScalarTower ℂ X X] [SMulCommClass ℂ X X] :
    ofStarAlgHom p.toCompletion = p :=
  ext p.norm_toCompletion

/-- The image of `X` is dense in its completion for `p`. -/
lemma denseRange_toCompletion : DenseRange p.toCompletion :=
  Completion.denseRange_coe (α := p.Carrier)

/-! ### Extending `⋆`-homomorphisms to the completion -/

section Lift

variable {C : Type*} [NonUnitalCStarAlgebra C] (Φ : X →⋆ₙₐ[ℂ] C) (h : ∀ x, ‖Φ x‖ ≤ p x)

/-- A `⋆`-homomorphism of `X`, read on `p.Carrier`. -/
def homOf : p.Carrier →⋆ₙₐ[ℂ] C :=
  Φ

include h in
/-- A `⋆`-homomorphism bounded by `p` is uniformly continuous on `p.Carrier`. -/
lemma uniformContinuous_homOf : UniformContinuous (homOf p Φ) :=
  AddMonoidHomClass.uniformContinuous_of_bound (homOf p Φ) 1 fun x => by
    rw [one_mul, Carrier.norm_def]
    exact h x

/-- The extension to the completion for `p` of a `⋆`-homomorphism `Φ` into a C⋆-algebra with
`‖Φ x‖ ≤ p x`, by continuity. -/
noncomputable def lift : Completion p.Carrier →⋆ₙₐ[ℂ] C where
  toFun := Completion.extension (homOf p Φ)
  map_smul' c x := by
    refine Completion.induction_on (α := p.Carrier) x
      (isClosed_eq (Completion.continuous_extension.comp (continuous_const_smul c))
        (Completion.continuous_extension.const_smul c)) fun a => ?_
    rw [← Completion.coe_smul, Completion.extension_coe (uniformContinuous_homOf p Φ h),
      Completion.extension_coe (uniformContinuous_homOf p Φ h)]
    exact map_smul (homOf p Φ) c a
  map_zero' := by
    rw [← Completion.coe_zero, Completion.extension_coe (uniformContinuous_homOf p Φ h)]
    exact map_zero (homOf p Φ)
  map_add' x y := by
    refine Completion.induction_on₂ (α := p.Carrier) (β := p.Carrier) x y
      (isClosed_eq (Completion.continuous_extension.comp continuous_add)
        ((Completion.continuous_extension.comp continuous_fst).add
          (Completion.continuous_extension.comp continuous_snd))) fun a b => ?_
    rw [← Completion.coe_add, Completion.extension_coe (uniformContinuous_homOf p Φ h),
      Completion.extension_coe (uniformContinuous_homOf p Φ h),
      Completion.extension_coe (uniformContinuous_homOf p Φ h)]
    exact map_add (homOf p Φ) a b
  map_mul' x y := by
    refine Completion.induction_on₂ (α := p.Carrier) (β := p.Carrier) x y
      (isClosed_eq (Completion.continuous_extension.comp continuous_mul)
        ((Completion.continuous_extension.comp continuous_fst).mul
          (Completion.continuous_extension.comp continuous_snd))) fun a b => ?_
    rw [← Completion.coe_mul', Completion.extension_coe (uniformContinuous_homOf p Φ h),
      Completion.extension_coe (uniformContinuous_homOf p Φ h),
      Completion.extension_coe (uniformContinuous_homOf p Φ h)]
    exact map_mul (homOf p Φ) a b
  map_star' x := by
    refine Completion.induction_on (α := p.Carrier) x
      (isClosed_eq (Completion.continuous_extension.comp continuous_star)
        (Completion.continuous_extension.star)) fun a => ?_
    rw [Completion.star_coe, Completion.extension_coe (uniformContinuous_homOf p Φ h),
      Completion.extension_coe (uniformContinuous_homOf p Φ h)]
    exact map_star (homOf p Φ) a

/-- `CStarSeminorm.lift p Φ h` extends `Φ`. -/
@[simp] lemma lift_toCompletion (x : X) : p.lift Φ h (p.toCompletion x) = Φ x :=
  Completion.extension_coe (uniformContinuous_homOf p Φ h) (show p.Carrier from x)

section Unique

open scoped CStarAlgebra

variable [StarModule ℂ X] [IsScalarTower ℂ X X] [SMulCommClass ℂ X X]

/-- Two `⋆`-homomorphisms of the completion for `p` into a C⋆-algebra that agree on the image of
`X` are equal: they are continuous, and the image of `X` is dense. -/
lemma nonUnitalStarAlgHom_ext {ψ₁ ψ₂ : Completion p.Carrier →⋆ₙₐ[ℂ] C}
    (hψ : ∀ x, ψ₁ (p.toCompletion x) = ψ₂ (p.toCompletion x)) : ψ₁ = ψ₂ :=
  DFunLike.ext _ _ fun T => congrFun (p.denseRange_toCompletion.equalizer (map_continuous ψ₁)
    (map_continuous ψ₂) (funext hψ)) T

/-- **`CStarSeminorm.lift p Φ h` is the only extension of `Φ`** to the completion for `p`, when the
completion is a C⋆-algebra. -/
theorem lift_unique {ψ : Completion p.Carrier →⋆ₙₐ[ℂ] C} (hψ : ∀ x, ψ (p.toCompletion x) = Φ x) :
    ψ = p.lift Φ h :=
  p.nonUnitalStarAlgHom_ext fun x => by rw [hψ, lift_toCompletion]

end Unique

end Lift

/-! ### The greatest C⋆-seminorm -/

section Sup

variable (hb : ∀ x : X, BddAbove (Set.range fun p : CStarSeminorm X => p x))

/-- The pointwise supremum of the C⋆-seminorms is nonnegative. -/
lemma iSup_apply_nonneg (x : X) : 0 ≤ ⨆ q : CStarSeminorm X, q x :=
  Real.iSup_nonneg fun q => apply_nonneg q x

/-- **The supremum of the C⋆-seminorms** of `X`, when they are bounded at each point: the greatest
C⋆-seminorm on `X`. -/
noncomputable def greatest : CStarSeminorm X where
  toFun x := ⨆ p : CStarSeminorm X, p x
  map_zero' := by simp only [map_zero, ciSup_const]
  add_le' x y := ciSup_le fun p =>
    (map_add_le_add p x y).trans (add_le_add (le_ciSup (hb x) p) (le_ciSup (hb y) p))
  neg' x := by simp only [map_neg_eq_map]
  mul_le' x y := ciSup_le fun p => (map_mul_le_mul p x y).trans
    (mul_le_mul (le_ciSup (hb x) p) (le_ciSup (hb y) p) (apply_nonneg p y) (iSup_apply_nonneg x))
  map_smul' c x := by
    simp only [apply_smul]
    exact (Real.mul_iSup_of_nonneg (norm_nonneg c) _).symm
  map_star_mul_self' x := by
    refine le_antisymm (ciSup_le fun p => ?_) ?_
    · rw [p.apply_star_mul_self]
      exact pow_le_pow_left₀ (apply_nonneg p x) (le_ciSup (hb x) p) 2
    · rw [← Real.le_sqrt (iSup_apply_nonneg x) (iSup_apply_nonneg _)]
      refine ciSup_le fun p => ?_
      rw [← Real.sqrt_sq (apply_nonneg p x), ← p.apply_star_mul_self]
      exact Real.sqrt_le_sqrt (le_ciSup (hb _) p)

/-- The supremum of the C⋆-seminorms is their pointwise supremum. -/
lemma greatest_apply (x : X) : greatest hb x = ⨆ p : CStarSeminorm X, p x :=
  rfl

/-- Every C⋆-seminorm is at most the supremum. -/
lemma le_greatest (p : CStarSeminorm X) (x : X) : p x ≤ greatest hb x :=
  le_ciSup (hb x) p

/-- The supremum is the least bound of the C⋆-seminorms. -/
lemma greatest_le {x : X} {c : ℝ} (h : ∀ p : CStarSeminorm X, p x ≤ c) : greatest hb x ≤ c :=
  ciSup_le h

end Sup

end CStarSeminorm
