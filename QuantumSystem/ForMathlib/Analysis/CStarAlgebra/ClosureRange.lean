/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Hom
public import Mathlib.Topology.Algebra.NonUnitalStarAlgebra

/-!
# The closure of the range of a `⋆`-homomorphism into a C⋆-algebra

A `⋆`-homomorphism `φ : D → C` of a `⋆`-algebra `D` into a C⋆-algebra `C` gives the C⋆-seminorm
`x ↦ ‖φ x‖` on `D`, a norm when `φ` is injective. The completion of `D` for it is the norm closure
of `φ(D)` in `C`, a C⋆-subalgebra of `C`. This is how a C⋆-norm on an algebraic tensor product
`A ⊗[ℂ] B` gives a C⋆-tensor product; the minimal tensor product is the case of the tensor product of
two faithful representations.

The closure of the range, the corestriction and their algebraic and topological properties are
stated for a `⋆`-homomorphism into a topological `⋆`-algebra over a commutative semiring, the
setting of Mathlib's `NonUnitalStarSubalgebra.topologicalClosure`; the comparison of two seminorms
`‖φ x‖` and `‖ψ x‖` is stated for normed `⋆`-algebras over a normed field, the target of the
comparison map complete, and uses no C⋆-identity.

## Main definitions

* `NonUnitalStarAlgHom.closureRange φ` — the closure of the range of `φ`, a
  `NonUnitalStarSubalgebra` of `C`; it is closed, hence a `NonUnitalCStarAlgebra` when `C` is one.
* `NonUnitalStarAlgHom.closureRangeRestrict φ` — `φ` as a `⋆`-homomorphism of `D` into
  `φ.closureRange`.
* `NonUnitalStarAlgHom.closureRangeMap h` — for `‖ψ x‖ ≤ ‖φ x‖`, the `⋆`-homomorphism
  `φ.closureRange → ψ.closureRange` extending `φ x ↦ ψ x`.
* `NonUnitalStarAlgHom.closureRangeEquiv h` — for `‖φ x‖ = ‖ψ x‖`, the isometric `⋆`-isomorphism
  `φ.closureRange ≃⋆ₐ[𝕜] ψ.closureRange`.
* `NonUnitalStarAlgHom.equivOfDenseRange hφ hψ h` — for `‖φ x‖ = ‖ψ x‖` and dense ranges, the
  isometric `⋆`-isomorphism `C₁ ≃⋆ₐ[𝕜] C₂` that sends `φ x` to `ψ x`.
* `NonUnitalStarSubalgebra.equivOfEq S T h` — equal `⋆`-subalgebras are `⋆`-isomorphic.

## Main results

* `NonUnitalStarAlgHom.norm_closureRangeRestrict` — `‖φ.closureRangeRestrict x‖ = ‖φ x‖`.
* `NonUnitalStarAlgHom.denseRange_closureRangeRestrict` — `D` has dense image in `φ.closureRange`.
* `NonUnitalStarAlgHom.closureRangeRestrict_injective` — it is injective when `φ` is.
* `NonUnitalStarAlgHom.closureRangeRestrict_surjective_of_isClosed` — it is surjective when the range of
  `φ` is closed.
* `NonUnitalStarAlgHom.closureRange_comp_of_surjective` — composing `φ` with a surjective
  `⋆`-homomorphism does not change the closure of its range.
* `NonUnitalStarAlgHom.closureRangeMap_closureRangeRestrict`,
  `NonUnitalStarAlgHom.norm_closureRangeMap_le` — `closureRangeMap h` sends `φ x` to `ψ x` and is
  contractive.
* `NonUnitalStarAlgHom.norm_closureRangeEquiv` — `closureRangeEquiv h` is isometric.

These are general facts and are candidates for upstreaming to Mathlib.
-/

@[expose] public section

namespace NonUnitalStarSubalgebra

variable {R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Star A]

/-- Equal `⋆`-subalgebras are `⋆`-isomorphic, by the identity on the elements. -/
def equivOfEq (S T : NonUnitalStarSubalgebra R A) (h : S = T) : S ≃⋆ₐ[R] T where
  toFun x := ⟨x, h ▸ x.2⟩
  invFun x := ⟨x, h.symm ▸ x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_star' _ := rfl
  map_smul' _ _ := rfl

/-- `NonUnitalStarSubalgebra.equivOfEq` is the identity on the elements. -/
@[simp] lemma coe_equivOfEq (S T : NonUnitalStarSubalgebra R A) (h : S = T) (x : S) :
    (equivOfEq S T h x : A) = x :=
  rfl

end NonUnitalStarSubalgebra

namespace NonUnitalStarAlgHom

section Topological

variable {R D C : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring D] [Module R D] [Star D]
  [TopologicalSpace C] [Star C] [NonUnitalSemiring C] [Module R C] [ContinuousStar C]
  [ContinuousConstSMul R C] [IsSemitopologicalSemiring C]

/-- The closure of the range of a `⋆`-homomorphism `φ : D → C` into a topological `⋆`-algebra, as a
`⋆`-subalgebra of `C`. For a C⋆-algebra `C` it is the completion of `D` for the C⋆-seminorm
`x ↦ ‖φ x‖`. -/
def closureRange (φ : D →⋆ₙₐ[R] C) : NonUnitalStarSubalgebra R C :=
  (NonUnitalStarAlgHom.range φ).topologicalClosure

/-- The closure of the range of `φ` is the closure of the set `Set.range φ`. -/
lemma coe_closureRange (φ : D →⋆ₙₐ[R] C) : (φ.closureRange : Set C) = closure (Set.range φ) := rfl

/-- The closure of the range of `φ` is closed. -/
lemma isClosed_closureRange (φ : D →⋆ₙₐ[R] C) : IsClosed (φ.closureRange : Set C) :=
  (NonUnitalStarAlgHom.range φ).isClosed_topologicalClosure

/-- The closure of the range of `φ` is closed, so it is a C⋆-algebra when `C` is one
(`NonUnitalStarSubalgebra.nonUnitalCStarAlgebra`). -/
instance instIsClosedClosureRange (φ : D →⋆ₙₐ[R] C) : IsClosed (φ.closureRange : Set C) :=
  isClosed_closureRange φ

/-- A `⋆`-homomorphism `φ : D → C` into a topological `⋆`-algebra, as a `⋆`-homomorphism of `D`
into the closure of its range. -/
noncomputable def closureRangeRestrict (φ : D →⋆ₙₐ[R] C) : D →⋆ₙₐ[R] φ.closureRange :=
  NonUnitalStarAlgHom.codRestrict φ φ.closureRange
    fun x => NonUnitalStarSubalgebra.le_topologicalClosure _ ⟨x, rfl⟩

/-- `φ.closureRangeRestrict x` is `φ x`, as an element of `C`. -/
@[simp] lemma coe_closureRangeRestrict (φ : D →⋆ₙₐ[R] C) (x : D) : (φ.closureRangeRestrict x : C) = φ x := rfl

/-- `φ.closureRangeRestrict` is injective when `φ` is. -/
lemma closureRangeRestrict_injective {φ : D →⋆ₙₐ[R] C} (h : Function.Injective φ) :
    Function.Injective φ.closureRangeRestrict := fun _ _ hxy =>
  h (congrArg Subtype.val hxy)

/-- The image of `D` is dense in the closure of the range of `φ`. -/
lemma denseRange_closureRangeRestrict (φ : D →⋆ₙₐ[R] C) : DenseRange φ.closureRangeRestrict := by
  refine Topology.IsInducing.subtypeVal.dense_iff.2 fun T => ?_
  refine closure_mono ?_ T.2
  rintro _ ⟨x, rfl⟩
  exact ⟨φ.closureRangeRestrict x, ⟨x, rfl⟩, rfl⟩

/-- An element of a space in which `φ` has dense range lies in the closure of the range of `φ`. -/
lemma mem_closureRange_of_denseRange {φ : D →⋆ₙₐ[R] C} (hφ : DenseRange φ) (T : C) :
    T ∈ φ.closureRange := by
  rw [← SetLike.mem_coe, coe_closureRange, hφ.closure_eq]
  trivial

/-- `φ.closureRangeRestrict` is surjective when the range of `φ` is closed. -/
lemma closureRangeRestrict_surjective_of_isClosed {φ : D →⋆ₙₐ[R] C} (h : IsClosed (Set.range φ)) :
    Function.Surjective φ.closureRangeRestrict := fun T => by
  have hT : (T : C) ∈ closure (Set.range φ) := T.2
  rw [h.closure_eq] at hT
  obtain ⟨x, hx⟩ := hT
  exact ⟨x, Subtype.ext hx⟩

/-- Composing with a surjective `⋆`-homomorphism does not change the closure of the range. -/
lemma closureRange_comp_of_surjective {D' : Type*} [NonUnitalNonAssocSemiring D'] [Module R D']
    [Star D'] (φ : D →⋆ₙₐ[R] C) {e : D' →⋆ₙₐ[R] D} (he : Function.Surjective e) :
    (φ.comp e).closureRange = φ.closureRange :=
  SetLike.coe_injective <| by
    rw [coe_closureRange, coe_closureRange, NonUnitalStarAlgHom.coe_comp, he.range_comp]

variable {C₁ C₂ : Type*}
  [TopologicalSpace C₁] [Star C₁] [NonUnitalSemiring C₁] [Module R C₁] [ContinuousStar C₁]
  [ContinuousConstSMul R C₁] [IsSemitopologicalSemiring C₁]
  [TopologicalSpace C₂] [Star C₂] [NonUnitalSemiring C₂] [Module R C₂] [ContinuousStar C₂]
  [ContinuousConstSMul R C₂] [IsSemitopologicalSemiring C₂]

/-- The first projection, from the closure of the range of `x ↦ (φ x, ψ x)` to the closure of the
range of `φ`. -/
noncomputable def closureRangeProdFst (φ : D →⋆ₙₐ[R] C₁) (ψ : D →⋆ₙₐ[R] C₂) :
    (φ.prod ψ).closureRange →⋆ₙₐ[R] φ.closureRange :=
  NonUnitalStarAlgHom.codRestrict
    ((NonUnitalStarAlgHom.fst R C₁ C₂).comp
      (NonUnitalStarSubalgebraClass.subtype (φ.prod ψ).closureRange))
    φ.closureRange fun z => map_mem_closure (f := Prod.fst) (t := Set.range φ) continuous_fst z.2
      (by rintro _ ⟨x, rfl⟩; exact ⟨x, rfl⟩)

/-- The second projection, from the closure of the range of `x ↦ (φ x, ψ x)` to the closure of the
range of `ψ`. -/
noncomputable def closureRangeProdSnd (φ : D →⋆ₙₐ[R] C₁) (ψ : D →⋆ₙₐ[R] C₂) :
    (φ.prod ψ).closureRange →⋆ₙₐ[R] ψ.closureRange :=
  NonUnitalStarAlgHom.codRestrict
    ((NonUnitalStarAlgHom.snd R C₁ C₂).comp
      (NonUnitalStarSubalgebraClass.subtype (φ.prod ψ).closureRange))
    ψ.closureRange fun z => map_mem_closure (f := Prod.snd) (t := Set.range ψ) continuous_snd z.2
      (by rintro _ ⟨x, rfl⟩; exact ⟨x, rfl⟩)

end Topological

section Norm

variable {𝕜 D C : Type*} [NormedField 𝕜] [NonUnitalNonAssocSemiring D] [Module 𝕜 D] [Star D]
  [NonUnitalNormedRing C] [StarRing C] [NormedSpace 𝕜 C] [ContinuousStar C]

/-- The norm of `φ.closureRangeRestrict x` in the closure of the range is `‖φ x‖`. -/
lemma norm_closureRangeRestrict (φ : D →⋆ₙₐ[𝕜] C) (x : D) : ‖φ.closureRangeRestrict x‖ = ‖φ x‖ := rfl

end Norm

/-! ### Comparing two seminorms

For `⋆`-homomorphisms `φ : D → C₁` and `ψ : D → C₂` into normed `⋆`-algebras with
`‖ψ x‖ ≤ ‖φ x‖` and `C₂` complete, the map `φ x ↦ ψ x` extends to a contractive `⋆`-homomorphism of
the closure of the range of `φ` into that of `ψ`. It is obtained from the closure of the range of
`x ↦ (φ x, ψ x)` in `C₁ × C₂`, on which the first projection is isometric and onto the closure of
the range of `φ`. -/

section Normed

variable {𝕜 D C₁ C₂ : Type*} [NormedField 𝕜] [NonUnitalNonAssocSemiring D] [Module 𝕜 D] [Star D]
  [NonUnitalNormedRing C₁] [StarRing C₁] [NormedSpace 𝕜 C₁] [ContinuousStar C₁]
  [NonUnitalNormedRing C₂] [StarRing C₂] [NormedSpace 𝕜 C₂] [ContinuousStar C₂]
  {φ : D →⋆ₙₐ[𝕜] C₁} {ψ : D →⋆ₙₐ[𝕜] C₂}

/-- If `‖ψ x‖ ≤ ‖φ x‖` on `D`, the same holds for the two components of every element of the closure
of the range of `x ↦ (φ x, ψ x)`. -/
lemma norm_snd_le_norm_fst_of_mem_closureRange_prod (h : ∀ x, ‖ψ x‖ ≤ ‖φ x‖)
    (z : (φ.prod ψ).closureRange) : ‖(z : C₁ × C₂).2‖ ≤ ‖(z : C₁ × C₂).1‖ := by
  have hz : (z : C₁ × C₂) ∈ closure (Set.range (φ.prod ψ)) := z.2
  refine closure_minimal ?_
    (isClosed_le (continuous_norm.comp continuous_snd) (continuous_norm.comp continuous_fst)) hz
  rintro _ ⟨x, rfl⟩
  exact h x

/-- If `‖ψ x‖ ≤ ‖φ x‖` on `D`, the first projection of the closure of the range of
`x ↦ (φ x, ψ x)` is isometric. -/
lemma norm_closureRangeProdFst (h : ∀ x, ‖ψ x‖ ≤ ‖φ x‖) (z : (φ.prod ψ).closureRange) :
    ‖closureRangeProdFst φ ψ z‖ = ‖z‖ := by
  change ‖(z : C₁ × C₂).1‖ = ‖(z : C₁ × C₂)‖
  rw [Prod.norm_def, max_eq_left (norm_snd_le_norm_fst_of_mem_closureRange_prod h z)]

variable [CompleteSpace C₂]

/-- If `‖ψ x‖ ≤ ‖φ x‖` on `D` and `C₂` is complete, the first projection of the closure of the range
of `x ↦ (φ x, ψ x)` is a bijection onto the closure of the range of `φ`: it is isometric, and for a
limit `T` of values `φ xₙ` the values `ψ xₙ` form a Cauchy sequence, whose limit `v` gives the point
`(T, v)` over `T`. -/
lemma closureRangeProdFst_bijective (h : ∀ x, ‖ψ x‖ ≤ ‖φ x‖) :
    Function.Bijective (closureRangeProdFst φ ψ) := by
  have hiso : Isometry (closureRangeProdFst φ ψ) :=
    AddMonoidHomClass.isometry_of_norm _ (norm_closureRangeProdFst h)
  refine ⟨hiso.injective, fun T => ?_⟩
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 (T.2 : (T : C₁) ∈ closure (Set.range φ))
  choose x hx using hu
  have hlim' : Filter.Tendsto (fun n => φ (x n)) Filter.atTop (nhds (T : C₁)) :=
    hlim.congr fun n => (hx n).symm
  have hsub (χ : D →⋆ₙₐ[𝕜] C₂) (m n : ℕ) : χ (x m) - χ (x n) = χ (x m + (-1 : 𝕜) • x n) := by
    rw [map_add, map_smul, neg_one_smul, sub_eq_add_neg]
  have hsub' (m n : ℕ) : φ (x m) - φ (x n) = φ (x m + (-1 : 𝕜) • x n) := by
    rw [map_add, map_smul, neg_one_smul, sub_eq_add_neg]
  have hcauchy : CauchySeq fun n => ψ (x n) := by
    have hφ := hlim'.cauchySeq
    rw [Metric.cauchySeq_iff] at hφ ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hφ ε hε
    refine ⟨N, fun m hm n hn => lt_of_le_of_lt ?_ (hN m hm n hn)⟩
    rw [dist_eq_norm, dist_eq_norm, hsub ψ, hsub']
    exact h _
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hmem : ((T : C₁), v) ∈ closure (Set.range (φ.prod ψ)) :=
    mem_closure_of_tendsto (hlim'.prodMk_nhds hv) (Filter.Eventually.of_forall fun n => ⟨x n, rfl⟩)
  exact ⟨⟨_, hmem⟩, Subtype.ext rfl⟩

/-- For `⋆`-homomorphisms `φ` and `ψ` of `D` into normed `⋆`-algebras with `‖ψ x‖ ≤ ‖φ x‖`, the
second one complete, the `⋆`-homomorphism of the closure of the range of `φ` into the closure of the
range of `ψ` that sends `φ x` to `ψ x` (`NonUnitalStarAlgHom.closureRangeMap_closureRangeRestrict`). -/
noncomputable def closureRangeMap (h : ∀ x, ‖ψ x‖ ≤ ‖φ x‖) :
    φ.closureRange →⋆ₙₐ[𝕜] ψ.closureRange where
  toFun T := closureRangeProdSnd φ ψ
    ((StarAlgEquiv.ofBijective (closureRangeProdFst φ ψ) (closureRangeProdFst_bijective h)).symm T)
  map_smul' c T := by simp only [MonoidHom.id_apply, map_smul]
  map_zero' := by simp only [map_zero]
  map_add' T T' := by simp only [map_add]
  map_mul' T T' := by simp only [map_mul]
  map_star' T := by simp only [map_star]

/-- `closureRangeMap h` sends `φ x` to `ψ x`. -/
@[simp] lemma closureRangeMap_closureRangeRestrict (h : ∀ x, ‖ψ x‖ ≤ ‖φ x‖) (x : D) :
    closureRangeMap h (φ.closureRangeRestrict x) = ψ.closureRangeRestrict x := by
  have hx : (StarAlgEquiv.ofBijective (closureRangeProdFst φ ψ)
      (closureRangeProdFst_bijective h)).symm (φ.closureRangeRestrict x) =
        (φ.prod ψ).closureRangeRestrict x :=
    (StarAlgEquiv.symm_apply_eq _).2 rfl
  change closureRangeProdSnd φ ψ _ = _
  rw [hx]
  rfl

/-- `closureRangeMap h` is contractive. -/
lemma norm_closureRangeMap_le (h : ∀ x, ‖ψ x‖ ≤ ‖φ x‖) (T : φ.closureRange) :
    ‖closureRangeMap h T‖ ≤ ‖T‖ := by
  set z := (StarAlgEquiv.ofBijective (closureRangeProdFst φ ψ)
    (closureRangeProdFst_bijective h)).symm T with hz
  have hT : closureRangeProdFst φ ψ z = T :=
    StarAlgEquiv.apply_symm_apply
      (StarAlgEquiv.ofBijective (closureRangeProdFst φ ψ) (closureRangeProdFst_bijective h)) T
  calc ‖closureRangeMap h T‖ = ‖(z : C₁ × C₂).2‖ := rfl
    _ ≤ ‖(z : C₁ × C₂).1‖ := norm_snd_le_norm_fst_of_mem_closureRange_prod h z
    _ = ‖closureRangeProdFst φ ψ z‖ := rfl
    _ = ‖T‖ := by rw [hT]

/-- `closureRangeMap h` is continuous. -/
lemma continuous_closureRangeMap (h : ∀ x, ‖ψ x‖ ≤ ‖φ x‖) : Continuous (closureRangeMap h) :=
  AddMonoidHomClass.continuous_of_bound (closureRangeMap h) 1 fun T => by
    rw [one_mul]
    exact norm_closureRangeMap_le h T

variable [CompleteSpace C₁]

/-- For `⋆`-homomorphisms `φ` and `ψ` of `D` into Banach `⋆`-algebras with `‖φ x‖ = ‖ψ x‖`, the
closures of their ranges are `⋆`-isomorphic, by the isomorphism that sends `φ x` to `ψ x`: the
completion of `D` for such a seminorm depends on the seminorm only. The isomorphism is isometric
(`NonUnitalStarAlgHom.norm_closureRangeEquiv`). -/
noncomputable def closureRangeEquiv (h : ∀ x, ‖φ x‖ = ‖ψ x‖) :
    φ.closureRange ≃⋆ₐ[𝕜] ψ.closureRange where
  toFun := closureRangeMap fun x => (h x).ge
  invFun := closureRangeMap fun x => (h x).le
  left_inv T := congrFun ((denseRange_closureRangeRestrict φ).equalizer
    ((continuous_closureRangeMap fun x => (h x).le).comp
      (continuous_closureRangeMap fun x => (h x).ge)) continuous_id
    (funext fun x => by simp)) T
  right_inv T := congrFun ((denseRange_closureRangeRestrict ψ).equalizer
    ((continuous_closureRangeMap fun x => (h x).ge).comp
      (continuous_closureRangeMap fun x => (h x).le)) continuous_id
    (funext fun x => by simp)) T
  map_mul' := map_mul _
  map_add' := map_add _
  map_star' := map_star _
  map_smul' := map_smul _

/-- `closureRangeEquiv h` sends `φ x` to `ψ x`. -/
@[simp] lemma closureRangeEquiv_closureRangeRestrict (h : ∀ x, ‖φ x‖ = ‖ψ x‖) (x : D) :
    closureRangeEquiv h (φ.closureRangeRestrict x) = ψ.closureRangeRestrict x :=
  closureRangeMap_closureRangeRestrict (fun x => (h x).ge) x

/-- `closureRangeEquiv h` is isometric: it and its inverse are contractive. -/
lemma norm_closureRangeEquiv (h : ∀ x, ‖φ x‖ = ‖ψ x‖) (T : φ.closureRange) :
    ‖closureRangeEquiv h T‖ = ‖T‖ := by
  refine le_antisymm (norm_closureRangeMap_le (fun x => (h x).ge) T) ?_
  have hinv := norm_closureRangeMap_le (fun x => (h x).le) (closureRangeEquiv h T)
  have hT : closureRangeMap (fun x => (h x).le) (closureRangeEquiv h T) = T :=
    (closureRangeEquiv h).symm_apply_apply T
  rwa [hT] at hinv

/-- For `⋆`-homomorphisms `φ` and `ψ` of `D` with dense ranges in Banach `⋆`-algebras and
`‖φ x‖ = ‖ψ x‖`, the `⋆`-isomorphism `C₁ ≃⋆ₐ[𝕜] C₂` that sends `φ x` to `ψ x`: both algebras are
the completion of `D` for the same seminorm. It is `NonUnitalStarAlgHom.closureRangeEquiv h`, the
closures of the ranges being the whole algebras. -/
noncomputable def equivOfDenseRange (hφ : DenseRange φ) (hψ : DenseRange ψ)
    (h : ∀ x, ‖φ x‖ = ‖ψ x‖) : C₁ ≃⋆ₐ[𝕜] C₂ where
  toFun T := closureRangeEquiv h ⟨T, mem_closureRange_of_denseRange hφ T⟩
  invFun T := (closureRangeEquiv h).symm ⟨T, mem_closureRange_of_denseRange hψ T⟩
  left_inv _ := congrArg Subtype.val ((closureRangeEquiv h).symm_apply_apply _)
  right_inv _ := congrArg Subtype.val ((closureRangeEquiv h).apply_symm_apply _)
  map_mul' T T' := congrArg Subtype.val (map_mul (closureRangeEquiv h)
    ⟨T, mem_closureRange_of_denseRange hφ T⟩ ⟨T', mem_closureRange_of_denseRange hφ T'⟩)
  map_add' T T' := congrArg Subtype.val (map_add (closureRangeEquiv h)
    ⟨T, mem_closureRange_of_denseRange hφ T⟩ ⟨T', mem_closureRange_of_denseRange hφ T'⟩)
  map_star' T := congrArg Subtype.val (map_star (closureRangeEquiv h)
    ⟨T, mem_closureRange_of_denseRange hφ T⟩)
  map_smul' c T := congrArg Subtype.val (map_smul (closureRangeEquiv h) c
    ⟨T, mem_closureRange_of_denseRange hφ T⟩)

/-- `equivOfDenseRange hφ hψ h` sends `φ x` to `ψ x`. -/
@[simp] lemma equivOfDenseRange_apply (hφ : DenseRange φ) (hψ : DenseRange ψ)
    (h : ∀ x, ‖φ x‖ = ‖ψ x‖) (x : D) : equivOfDenseRange hφ hψ h (φ x) = ψ x :=
  congrArg Subtype.val (closureRangeEquiv_closureRangeRestrict h x)

/-- `equivOfDenseRange hφ hψ h` is isometric. -/
lemma norm_equivOfDenseRange (hφ : DenseRange φ) (hψ : DenseRange ψ) (h : ∀ x, ‖φ x‖ = ‖ψ x‖)
    (T : C₁) : ‖equivOfDenseRange hφ hψ h T‖ = ‖T‖ :=
  norm_closureRangeEquiv h ⟨T, mem_closureRange_of_denseRange hφ T⟩

end Normed

end NonUnitalStarAlgHom
