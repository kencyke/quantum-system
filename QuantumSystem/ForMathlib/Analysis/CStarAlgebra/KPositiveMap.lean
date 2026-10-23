/-
Copyright (c) 2026 Keisuke Suzuki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keisuke Suzuki
-/
module

public import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import Mathlib.Analysis.CStarAlgebra.Hom
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Positive

/-!
# `k`-positive maps

A ℂ-linear map `φ` between C⋆-algebras is **`k`-positive** if applying it entrywise to a `k × k`
matrix over its domain preserves nonnegativity. Mathlib's completely positive maps
(`CompletelyPositiveMap`) are the maps that are `k`-positive for every `k`; this file adds the
notion at a single matrix size `k`, mirroring Mathlib's structure and morphism class. A
`k`-positive map is `j`-positive for every `j ≤ k` (`KPositiveMapClass.of_le`), and, when linear,
positive for `k ≥ 1` (`KPositiveMapClass.orderHomClass`).

The main result is the **Kadison–Schwarz inequality** for `2`-positive, in particular
completely positive, maps between possibly non-unital C⋆-algebras. Its source is the
Cauchy–Schwarz inequality `φ(x⋆ y)⋆ φ(x⋆ y) ≤ ‖φ(x⋆ x)‖ • φ(y⋆ y)`, read off the positive matrix
`(φ(xᵢ⋆ xⱼ))ᵢⱼ`. With `x = 1` it is `φ(a)⋆ φ(a) ≤ ‖φ 1‖ • φ(a⋆ a)` on a unital domain, normalised
to `φ(a)⋆ φ(a) ≤ φ(a⋆ a)` under `φ 1 ≤ 1`; with `x` running through an approximate unit it is
`φ(a)⋆ φ(a) ≤ ‖φ‖ • φ(a⋆ a)` on a non-unital domain. Here `φ : F` is a `FunLike` map with
`LinearMapClass F ℂ A₁ A₂`, and `‖φ‖` is the operator norm of the bounded positive map
`PositiveContinuousLinearMap.ofClass φ : A₁ →L[ℂ] A₂`, which exists since a `2`-positive linear map
is positive (`KPositiveMapClass.instOrderHomClass`) and positive maps between C⋆-algebras are
bounded.

For merely positive maps the Kadison–Schwarz inequality still holds at normal elements, and a
positive map on a unital domain attains its norm at the unit, `‖φ‖ = ‖φ 1‖` (Russo–Dye 1966;
Paulsen, Corollary 2.9). Both follow from the `2`-positive case
treated here, through Stinespring's theorem that a positive map on a commutative C⋆-algebra is
completely positive and through the Russo–Dye theorem, and are proved not here but in the module
`QuantumSystem.Analysis.CStarAlgebra.PositiveMap`, which lies outside `ForMathlib/` because it
combines this file with the Russo–Dye theorem and Stinespring's theorem for commutative domains,
while a `ForMathlib` file imports Mathlib only.

## Main definitions

* `KPositiveMap k A₁ A₂` — `k`-positive ℂ-linear maps.
* `KPositiveMapClass F k A₁ A₂` — the corresponding morphism class. As
  `CompletelyPositiveMapClass`, it records only the order property and is meant to be used
  together with `LinearMapClass`; unlike that class, `A₁` and `A₂` are `outParam`s, so that
  `KPositiveMapClass.le_map_star_mul φ hφ a` elaborates without an expected type.
* `KPositiveMap.ofLE` — a `k`-positive map as a `j`-positive map, `j ≤ k`.
* `KPositiveMap.arrowCongr` — the transport `φ ↦ e₂ ∘ φ ∘ e₁⁻¹` of `k`-positive maps along
  ⋆-isomorphisms `e₁`, `e₂`.
* `CStarMatrix.ofScalar C n` — the scalar matrices `α ↦ (αᵢⱼ • 1)ᵢⱼ` in the matrices over a unital
  C⋆-algebra `C`, as a unital ⋆-homomorphism.

## Main results

* `CStarMatrix.diag_nonneg`, `CStarMatrix.submatrix_nonneg` — the diagonal entries, and more
  generally every reindexing `(M (f i) (f j))ᵢⱼ`, of a nonnegative `CStarMatrix` are nonnegative.
* `CStarMatrix.star_mul_le_norm_smul_of_nonneg` — if `!![p, b; b⋆, q]` is nonnegative, then
  `b⋆ b ≤ ‖p‖ • q`.
* `CStarMatrix.norm_sq_le_of_nonneg` — if `!![p, b; b⋆, q]` is nonnegative, then
  `‖b‖² ≤ ‖p‖ ‖q‖`.
* `CStarMatrix.nonneg_one_star_one_iff` — in a unital C⋆-algebra, `!![1, y; y⋆, 1]` is nonnegative
  exactly when `‖y‖ ≤ 1`.
* `CStarMatrix.nonneg_star_mul_self_block_iff` — for units `s`, `t` of a unital C⋆-algebra,
  `!![s⋆ s, x; x⋆, t⋆ t]` is nonnegative exactly when `‖(s⁻¹)⋆ x t⁻¹‖ ≤ 1`.
* `CStarMatrix.norm_ofMatrix_zero_one_le` — `‖!![0, x; 0, 0]‖ ≤ ‖x‖`.
* `CompletelyPositiveMapClass.instKPositiveMapClass` — completely positive maps, of any
  `CompletelyPositiveMapClass`, are `k`-positive.
* `KPositiveMapClass.of_le`, `KPositiveMapClass.orderHomClass` — a `k`-positive map is
  `j`-positive for `j ≤ k`, and positive for `k ≥ 1`; for `k = 2` this is the instance
  `KPositiveMapClass.instOrderHomClass`.
* `KPositiveMapClass.map_nonneg_of_card_le` — a `k`-positive map preserves the nonnegativity of
  block matrices indexed by any finite type with at most `k` elements.
* `KPositiveMapClass.star_map_mul_le_norm_smul` — the Cauchy–Schwarz inequality
  `φ(x⋆ y)⋆ φ(x⋆ y) ≤ ‖φ(x⋆ x)‖ • φ(y⋆ y)` for `2`-positive maps.
* `KPositiveMapClass.le_norm_smul_map_star_mul` — the Kadison–Schwarz inequality
  `φ(a)⋆ φ(a) ≤ ‖φ 1‖ • φ(a⋆ a)` for `2`-positive maps on a unital domain;
  `KPositiveMapClass.le_map_star_mul` — its normalised form `φ(a)⋆ φ(a) ≤ φ(a⋆ a)` under
  `φ 1 ≤ 1`.
* `KPositiveMapClass.le_smul_map_star_mul_of_norm_le`, `KPositiveMapClass.le_opNorm_smul_map_star_mul`
  — the Kadison–Schwarz inequality `φ(a)⋆ φ(a) ≤ ‖φ‖ • φ(a⋆ a)` for `2`-positive maps on a
  possibly non-unital domain.
* `OrderHomClass.norm_map_one_le_one` — a positive map between unital C⋆-algebras with
  `φ 1 ≤ 1` has `‖φ 1‖ ≤ 1`.

## References

* M.-D. Choi, *A Schwarz inequality for positive linear maps on C⋆-algebras*, Illinois J. Math.
  18 (1974), 565–574.
* R. V. Kadison, *A generalized Schwarz inequality and algebraic invariants for operator
  algebras*, Ann. of Math. 56 (1952), 494–503.
* E. C. Lance, *Hilbert C⋆-Modules*, London Math. Soc. Lecture Note Ser. 210 (1995).
* V. Paulsen, *Completely Bounded Maps and Operator Algebras*, Cambridge Stud. Adv. Math. 78
  (2002), Corollary 2.9.
* B. Russo, H. A. Dye, *A note on unitary operators in C⋆-algebras*, Duke Math. J. 33 (1966),
  413–416.
-/

@[expose] public section

open scoped CStarAlgebra
open Filter Topology

namespace CStarMatrix

variable {n A : Type*} [Fintype n] [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The diagonal entries of a nonnegative `CStarMatrix` are nonnegative. The positive matrices are the
additive closure of the `X⋆ X` (`StarOrderedRing.le_iff`), and `(X⋆ X) i i = ∑ₖ (X k i)⋆ (X k i)`. -/
lemma diag_nonneg {M : CStarMatrix n n A} (hM : 0 ≤ M) {i : n} : 0 ≤ M i i := by
  obtain ⟨P, hP, rfl⟩ := (StarOrderedRing.le_iff 0 M).mp hM
  clear hM
  rw [zero_add]
  induction hP using AddSubmonoid.closure_induction with
  | mem _ h =>
    obtain ⟨X, rfl⟩ := h
    change 0 ≤ (star X * X) i i
    rw [mul_apply]
    exact Finset.sum_nonneg fun k _ => by rw [star_apply]; exact star_mul_self_nonneg _
  | zero => exact le_rfl
  | add _ _ _ _ h₁ h₂ => exact add_nonneg h₁ h₂

/-- Reindexing a nonnegative `CStarMatrix` along any map `f : m → n`, not necessarily injective,
gives a nonnegative matrix `(M (f i) (f j))ᵢⱼ`. The positive matrices are the additive closure of
the `X⋆ X`, and `(X⋆ X) (f a) (f b) = Σ_c (X c (f a))⋆ X c (f b)` is the sum over `c` of `Z_c⋆ Z_c`
for the matrix `Z_c` whose only nonzero row is `(X c (f b))_b`. No unit of `A` is used. -/
lemma submatrix_nonneg {m : Type*} [Fintype m] {M : CStarMatrix n n A} (hM : 0 ≤ M) (f : m → n) :
    0 ≤ ofMatrix ((ofMatrix.symm M).submatrix f f) := by
  classical
  cases isEmpty_or_nonempty m with
  | inl _ =>
    rw [show ofMatrix ((ofMatrix.symm M).submatrix f f) = 0 from ext fun i => isEmptyElim i]
  | inr hm =>
    obtain ⟨r₀⟩ := hm
    obtain ⟨P, hP, rfl⟩ := (StarOrderedRing.le_iff 0 M).mp hM
    clear hM
    rw [zero_add]
    induction hP using AddSubmonoid.closure_induction with
    | mem _ h =>
      obtain ⟨X, rfl⟩ := h
      let Z : n → CStarMatrix m m A := fun c =>
        ofMatrix (Matrix.of fun r b => if r = r₀ then X c (f b) else 0)
      have hZ : ofMatrix ((ofMatrix.symm (star X * X)).submatrix f f) = ∑ c, star (Z c) * Z c := by
        ext a b
        refine Eq.trans ?_ (map_sum (AddMonoidHom.mk' (fun M : CStarMatrix m m A => M a b)
          (fun _ _ => rfl)) _ _).symm
        change ∑ c, star (X c (f a)) * X c (f b) = ∑ c, ∑ r, star (Z c r a) * Z c r b
        refine Finset.sum_congr rfl fun c _ => ?_
        simp [Z, ofMatrix_apply]
      rw [hZ]
      exact Finset.sum_nonneg fun c _ => star_mul_self_nonneg _
    | zero => exact le_of_eq (ext fun i j => rfl)
    | add x y _ _ hx hy =>
      exact (add_nonneg hx hy).trans_eq (ext fun i j => rfl)

/-- The `2 × 2` estimate behind the Kadison–Schwarz inequality, in a unital C⋆-algebra:
`CStarMatrix.star_mul_le_norm_smul_of_nonneg` for unital `A`. For `μ : ℝ` the lower-right entry of
`Y⋆ N Y`, `Y = !![1, -μ b; 0, 1]`, is `q - 2μ b⋆ b + μ² b⋆ p b ≥ 0`, and `b⋆ p b ≤ ‖p‖ • b⋆ b`. Take
`μ = ‖p‖⁻¹` when `p ≠ 0`; when `p = 0` let `μ → ∞` to get `b⋆ b = 0`. -/
private lemma star_mul_le_norm_smul_of_nonneg_of_unital {A : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {p b q : A} (hN : 0 ≤ ofMatrix !![p, b; star b, q]) :
    star b * b ≤ ‖p‖ • q := by
  have hp : 0 ≤ p := by simpa using diag_nonneg hN (i := 0)
  have hX : 0 ≤ star b * b := star_mul_self_nonneg b
  set l := ‖p‖
  have key (μ : ℝ) : (2 * μ - μ ^ 2 * l) • (star b * b) ≤ q := by
    let Y : CStarMatrix (Fin 2) (Fin 2) A := ofMatrix !![1, -(μ • b); 0, 1]
    have h₁ := diag_nonneg (star_left_conjugate_nonneg hN Y) (i := 1)
    have h₂ : (star Y * ofMatrix !![p, b; star b, q] * Y) 1 1 =
        q - (2 * μ) • (star b * b) + μ ^ 2 • (star b * p * b) := by
      simp only [Fin.isValue, CStarMatrix.mul_apply, CStarMatrix.star_apply, CStarMatrix.ofMatrix_apply,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Fin.sum_univ_two, Matrix.cons_val_zero, star_neg, star_one, one_mul, mul_one, Y, star_smul,
        star_trivial, mul_neg, neg_mul, smul_mul_assoc, mul_smul_comm]
      rw [add_mul, neg_mul, smul_mul_assoc]
      module
    have hconj := CStarAlgebra.star_left_conjugate_le_norm_smul b p (IsSelfAdjoint.of_nonneg hp)
    rw [h₂] at h₁
    have h' := add_nonneg h₁ (sub_nonneg.2 (smul_le_smul_of_nonneg_left hconj (sq_nonneg μ)))
    rw [← sub_nonneg]
    convert h' using 1
    module
  rcases (norm_nonneg p).eq_or_lt with hl | hl
  · -- `p = 0`: `2 μ ‖b⋆ b‖ ≤ ‖q‖` for every `μ ≥ 0` forces `b⋆ b = 0`.
    have hl0 : l = 0 := hl.symm
    suffices hb : star b * b = 0 by rw [hb, hl0, zero_smul]
    by_contra hne
    have hpos : 0 < ‖star b * b‖ := norm_pos_iff.2 hne
    set μ := ‖q‖ / ‖star b * b‖ + 1
    have hμ : 0 < μ := by positivity
    have hk := key μ
    rw [hl0, mul_zero, sub_zero] at hk
    have h := CStarAlgebra.norm_le_norm_of_le_of_nonneg hk (smul_nonneg (by positivity) hX)
    rw [norm_smul, Real.norm_of_nonneg (by positivity)] at h
    have : μ * ‖star b * b‖ = ‖q‖ + ‖star b * b‖ := by
      simp only [μ]; field_simp
    nlinarith [norm_nonneg q]
  · -- `p ≠ 0`: take `μ = ‖p‖⁻¹` and multiply by `‖p‖`.
    have hl' : l ≠ 0 := hl.ne'
    have h := smul_le_smul_of_nonneg_left (key l⁻¹) hl.le
    rw [smul_smul] at h
    have e₁ : l * (2 * l⁻¹ - l⁻¹ ^ 2 * l) = 1 := by field_simp; ring
    rwa [e₁, one_smul] at h

/-- The `2 × 2` estimate behind the Kadison–Schwarz inequality: if `!![p, b; b⋆, q]` is
nonnegative, then `b⋆ b ≤ ‖p‖ • q`. No unit of `A` is needed: the matrix stays nonnegative in the
unitization `A⁺¹`, which is order-embedded in `A` (`Unitization.inr_le_inr_iff`), and there the
estimate is proved by conjugating with `!![1, -μ b; 0, 1]`. -/
lemma star_mul_le_norm_smul_of_nonneg {p b q : A} (hN : 0 ≤ ofMatrix !![p, b; star b, q]) :
    star b * b ≤ ‖p‖ • q := by
  let ι : A →CP Unitization ℂ A :=
    CompletelyPositiveMapClass.toCompletelyPositiveLinearMap (Unitization.inrNonUnitalStarAlgHom ℂ A)
  have h := ι.map_cstarMatrix_nonneg _ hN
  have h' : (ofMatrix !![p, b; star b, q]).map ι =
      ofMatrix !![(p : Unitization ℂ A), (b : Unitization ℂ A); star (b : Unitization ℂ A),
        (q : Unitization ℂ A)] := by
    refine CStarMatrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j
    all_goals first | rfl | exact Unitization.inr_star b
  rw [h'] at h
  have := star_mul_le_norm_smul_of_nonneg_of_unital h
  rw [← Unitization.inr_le_inr_iff (A := A)]
  rw [Unitization.norm_inr] at this
  convert this using 1
  · simp [Unitization.inr_mul, Unitization.inr_star]
  · rw [← Complex.coe_smul, Unitization.inr_smul, Complex.coe_smul]

/-- If `!![p, b; b⋆, q]` is nonnegative, then `‖b‖² ≤ ‖p‖ ‖q‖`: take norms in `b⋆ b ≤ ‖p‖ • q`
(`CStarMatrix.star_mul_le_norm_smul_of_nonneg`). -/
lemma norm_sq_le_of_nonneg {p b q : A} (hN : 0 ≤ ofMatrix !![p, b; star b, q]) :
    ‖b‖ ^ 2 ≤ ‖p‖ * ‖q‖ := by
  have h := star_mul_le_norm_smul_of_nonneg hN
  rw [sq, ← CStarRing.norm_star_mul_self, ← norm_smul_of_nonneg (norm_nonneg p)]
  exact CStarAlgebra.norm_le_norm_of_le_of_nonneg h (star_mul_self_nonneg b)

section Single

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The embedding `a ↦ Eᵢᵢ a` of `A` as the `(i, i)` corner of `CStarMatrix n n A`, a
⋆-homomorphism. -/
def singleNonUnitalStarAlgHom (i : n) : A →⋆ₙₐ[ℂ] CStarMatrix n n A where
  toFun a := ofMatrix (Matrix.single i i a)
  map_smul' c a := by ext; simp [Matrix.single_apply]
  map_zero' := by ext; simp
  map_add' a b := by ext; simp [Matrix.single_add]
  map_mul' a b := by
    change _ = ofMatrix (Matrix.single i i a * Matrix.single i i b)
    rw [Matrix.single_mul_single_same]
  map_star' a := by
    change _ = ofMatrix (Matrix.single i i a).conjTranspose
    rw [Matrix.conjTranspose_single]

end Single

/-- The off-diagonal matrix `!![0, x; 0, 0]` has norm at most `‖x‖`: by the C⋆-identity its square
norm is that of `!![0, 0; 0, x⋆ x]`, the image of `x⋆ x` under an injective ⋆-homomorphism. -/
lemma norm_ofMatrix_zero_one_le (x : A) :
    ‖(ofMatrix !![0, x; 0, 0] : CStarMatrix (Fin 2) (Fin 2) A)‖ ≤ ‖x‖ := by
  have hinj : Function.Injective (singleNonUnitalStarAlgHom (A := A) (1 : Fin 2)) := by
    intro a b h
    have := congrFun (congrFun (congrArg (fun M : CStarMatrix (Fin 2) (Fin 2) A =>
      (M : Matrix _ _ A)) h) 1) 1
    simpa [singleNonUnitalStarAlgHom] using this
  have h : star (ofMatrix !![0, x; 0, 0] : CStarMatrix (Fin 2) (Fin 2) A) * ofMatrix !![0, x; 0, 0] =
      singleNonUnitalStarAlgHom 1 (star x * x) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [singleNonUnitalStarAlgHom, CStarMatrix.mul_apply, CStarMatrix.star_apply,
        ofMatrix_apply, Fin.sum_univ_two]
  have := congrArg norm h
  rw [CStarRing.norm_star_mul_self, NonUnitalStarAlgHom.norm_map _ hinj,
    CStarRing.norm_star_mul_self] at this
  nlinarith [norm_nonneg x, norm_nonneg (ofMatrix !![0, x; 0, 0] : CStarMatrix (Fin 2) (Fin 2) A)]

section Unital

variable {C : Type*} [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

/-- **Contractions as positive `2 × 2` matrices.** In a unital C⋆-algebra, `!![1, y; y⋆, 1]` is
nonnegative exactly when `‖y‖ ≤ 1`. If `‖y‖ ≤ 1`, then `1 - y⋆ y ≥ 0` has a square root `s` and
`!![1, y; y⋆, 1] = E⋆ E` for `E = !![1, y; 0, s]`; conversely `‖y‖² ≤ ‖1‖²`
(`CStarMatrix.norm_sq_le_of_nonneg`). -/
lemma nonneg_one_star_one_iff {y : C} :
    0 ≤ (ofMatrix !![1, y; star y, 1] : CStarMatrix (Fin 2) (Fin 2) C) ↔ ‖y‖ ≤ 1 := by
  rcases subsingleton_or_nontrivial C with hC | hC
  · simp [Subsingleton.elim y 0]
  constructor
  · intro h
    have := norm_sq_le_of_nonneg h
    rw [norm_one, mul_one] at this
    nlinarith [norm_nonneg y]
  · intro hy
    have hle : star y * y ≤ 1 := by
      refine (CStarAlgebra.star_mul_le_algebraMap_norm_sq (a := y)).trans ?_
      rw [← sub_nonneg, ← map_one (algebraMap ℝ C), ← map_sub]
      exact algebraMap_nonneg C (by nlinarith [norm_nonneg y])
    set s := CFC.sqrt (1 - star y * y)
    have hs : star s * s = 1 - star y * y := by
      rw [(CFC.sqrt_nonneg _).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self _ (sub_nonneg.mpr hle)]
    let E : CStarMatrix (Fin 2) (Fin 2) C := ofMatrix !![1, y; 0, s]
    have : (ofMatrix !![1, y; star y, 1] : CStarMatrix (Fin 2) (Fin 2) C) = star E * E := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [E, CStarMatrix.mul_apply, CStarMatrix.star_apply, ofMatrix_apply, Fin.sum_univ_two, hs]
    rw [this]
    exact star_mul_self_nonneg E

end Unital

end CStarMatrix

/-- A ℂ-linear map `φ : A₁ →ₗ[ℂ] A₂` between C⋆-algebras is **`k`-positive** if applying it
entrywise to a `k × k` matrix over `A₁` preserves nonnegativity. The completely positive maps
(`CompletelyPositiveMap`) are the maps that are `k`-positive for every `k`. -/
structure KPositiveMap (k : ℕ) (A₁ : Type*) (A₂ : Type*) [NonUnitalCStarAlgebra A₁]
    [NonUnitalCStarAlgebra A₂] [PartialOrder A₁] [PartialOrder A₂] [StarOrderedRing A₁]
    [StarOrderedRing A₂] extends A₁ →ₗ[ℂ] A₂ where
  /-- Applying the map entrywise to a nonnegative `k × k` matrix over `A₁` gives a nonnegative
  matrix over `A₂`. -/
  map_cstarMatrix_nonneg' (M : CStarMatrix (Fin k) (Fin k) A₁) (hM : 0 ≤ M) :
    0 ≤ M.map toLinearMap

/-- The morphism class of `k`-positive maps. As `CompletelyPositiveMapClass`, it records only the
order property and is meant to be used together with `LinearMapClass`. Unlike that class, `A₁` and
`A₂` are `outParam`s, determined by `F`, so that lemmas about `φ : F` elaborate without an expected
type. -/
class KPositiveMapClass (F : Type*) (k : ℕ) (A₁ A₂ : outParam Type*)
    [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂] [PartialOrder A₁] [PartialOrder A₂]
    [StarOrderedRing A₁] [StarOrderedRing A₂] [FunLike F A₁ A₂] : Prop where
  /-- Applying `φ` entrywise to a nonnegative `k × k` matrix over `A₁` gives a nonnegative
  matrix over `A₂`. -/
  map_cstarMatrix_nonneg' (φ : F) (M : CStarMatrix (Fin k) (Fin k) A₁) (hM : 0 ≤ M) :
    0 ≤ M.map φ

namespace KPositiveMap

variable {k : ℕ} {A₁ A₂ : Type*} [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂]
  [PartialOrder A₁] [PartialOrder A₂] [StarOrderedRing A₁] [StarOrderedRing A₂]

instance : FunLike (KPositiveMap k A₁ A₂) A₁ A₂ where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective
    exact h

/-- A `k`-positive map is `ℂ`-linear. -/
instance : LinearMapClass (KPositiveMap k A₁ A₂) ℂ A₁ A₂ where
  map_add f := map_add f.toLinearMap
  map_smulₛₗ f := map_smulₛₗ f.toLinearMap

/-- A bundled `k`-positive map is `k`-positive in the sense of `KPositiveMapClass`. -/
instance : KPositiveMapClass (KPositiveMap k A₁ A₂) k A₁ A₂ where
  map_cstarMatrix_nonneg' f := f.map_cstarMatrix_nonneg'

end KPositiveMap

/-- A completely positive map is `k`-positive for every `k`. This covers the bundled maps
`A₁ →CP A₂` and every other `CompletelyPositiveMapClass`, such as ⋆-homomorphisms
(`NonUnitalStarAlgHomClass.instCompletelyPositiveMapClass`). -/
instance CompletelyPositiveMapClass.instKPositiveMapClass {k : ℕ} {F A₁ A₂ : Type*}
    [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂] [PartialOrder A₁] [PartialOrder A₂]
    [StarOrderedRing A₁] [StarOrderedRing A₂] [FunLike F A₁ A₂]
    [CompletelyPositiveMapClass F A₁ A₂] : KPositiveMapClass F k A₁ A₂ where
  map_cstarMatrix_nonneg' φ := CompletelyPositiveMapClass.map_cstarMatrix_nonneg' φ k

namespace KPositiveMapClass

/-! ### Changing the matrix size -/

section NonUnital

variable {F A₁ A₂ : Type*} [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂] [PartialOrder A₁]
  [PartialOrder A₂] [StarOrderedRing A₁] [StarOrderedRing A₂] [FunLike F A₁ A₂]

/-- A `k`-positive map is `j`-positive for every `j ≤ k`. A nonnegative `j × j` matrix `M` is the
compression of the nonnegative `k × k` matrix `(M (g a) (g b))_{ab}` along `Fin.castLE`, where
`g : Fin k → Fin j` is a retraction of `Fin.castLE` (`CStarMatrix.submatrix_nonneg`); applying `φ`
entrywise commutes with both reindexings. -/
lemma of_le {k j : ℕ} [KPositiveMapClass F k A₁ A₂] (hjk : j ≤ k) :
    KPositiveMapClass F j A₁ A₂ where
  map_cstarMatrix_nonneg' φ M hM := by
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · exact le_of_eq (CStarMatrix.ext fun i => i.elim0)
    let g : Fin k → Fin j := fun i => if h : i.val < j then ⟨i, h⟩ else ⟨0, hj⟩
    have hg : ∀ a : Fin j, g (Fin.castLE hjk a) = a := fun a => by simp [g]
    have h := CStarMatrix.submatrix_nonneg
      (map_cstarMatrix_nonneg' φ _ (CStarMatrix.submatrix_nonneg hM g)) (Fin.castLE hjk)
    convert h using 1
    refine CStarMatrix.ext fun a b => ?_
    simp [CStarMatrix.map_apply, CStarMatrix.ofMatrix_apply, hg]

/-- A `k`-positive map preserves the nonnegativity of block matrices indexed by any finite type `ι`
with at most `k` elements: reindex along `ι ≃ Fin (card ι)` (`CStarMatrix.submatrix_nonneg`) and use
`card ι`-positivity (`KPositiveMapClass.of_le`). -/
lemma map_nonneg_of_card_le {k : ℕ} [KPositiveMapClass F k A₁ A₂] (φ : F) {ι : Type*}
    [Fintype ι] (hι : Fintype.card ι ≤ k) {M : CStarMatrix ι ι A₁} (hM : 0 ≤ M) :
    0 ≤ M.map φ := by
  have := of_le (F := F) hι
  let e := Fintype.equivFin ι
  have h := CStarMatrix.submatrix_nonneg
    (map_cstarMatrix_nonneg' φ _ (CStarMatrix.submatrix_nonneg hM e.symm)) e
  convert h using 1
  refine CStarMatrix.ext fun i j => ?_
  simp [CStarMatrix.map_apply, CStarMatrix.ofMatrix_apply]

/-- A `k`-positive map with `k ≥ 1` is positive: it is `1`-positive (`KPositiveMapClass.of_le`), and
a nonnegative `a = b⋆ b` is the entry of the nonnegative `1 × 1` matrix `[b]⋆ [b]`, whose image under
`φ` has the nonnegative entry `φ a` (`CStarMatrix.diag_nonneg`). -/
lemma orderHomClass {k : ℕ} [KPositiveMapClass F k A₁ A₂] [LinearMapClass F ℂ A₁ A₂]
    (hk : 1 ≤ k) : OrderHomClass F A₁ A₂ := by
  have := of_le (F := F) hk
  refine .of_addMonoidHom fun φ a ha => ?_
  obtain ⟨b, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha
  let X : CStarMatrix (Fin 1) (Fin 1) A₁ := CStarMatrix.ofMatrix fun _ _ => b
  have h := CStarMatrix.diag_nonneg (map_cstarMatrix_nonneg' φ _ (star_mul_self_nonneg X)) (i := 0)
  simp only [X, CStarMatrix.mul_apply, CStarMatrix.star_apply, CStarMatrix.map_apply,
    Finset.univ_unique, Finset.sum_singleton] at h
  exact h

/-- A `2`-positive linear map is positive (`KPositiveMapClass.orderHomClass`). The Kadison–Schwarz
inequalities are stated for `2`-positive maps, so their positivity is registered once here. Like
`SchwarzMapClass.instOrderHomClass`, it has low priority, so that cheaper instances are tried
first. -/
instance (priority := 100) instOrderHomClass [KPositiveMapClass F 2 A₁ A₂]
    [LinearMapClass F ℂ A₁ A₂] :
    OrderHomClass F A₁ A₂ :=
  orderHomClass (k := 2) (by norm_num)

end NonUnital

end KPositiveMapClass

namespace KPositiveMap

variable {k j : ℕ} {A₁ A₂ : Type*} [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂]
  [PartialOrder A₁] [PartialOrder A₂] [StarOrderedRing A₁] [StarOrderedRing A₂]

/-- A `k`-positive map as a `j`-positive map, for `j ≤ k` (`KPositiveMapClass.of_le`). -/
def ofLE (φ : KPositiveMap k A₁ A₂) (hjk : j ≤ k) : KPositiveMap j A₁ A₂ where
  toLinearMap := φ.toLinearMap
  map_cstarMatrix_nonneg' := (KPositiveMapClass.of_le (F := KPositiveMap k A₁ A₂) hjk).1 φ

/-- `KPositiveMap.ofLE φ hjk` is `φ` as a function. -/
@[simp] lemma coe_ofLE (φ : KPositiveMap k A₁ A₂) (hjk : j ≤ k) : ⇑(φ.ofLE hjk) = φ :=
  rfl

section ArrowCongr

variable {B₁ B₂ : Type*} [NonUnitalCStarAlgebra B₁] [NonUnitalCStarAlgebra B₂] [PartialOrder B₁]
  [PartialOrder B₂] [StarOrderedRing B₁] [StarOrderedRing B₂]

/-- `k`-positive maps transport along ⋆-isomorphisms `e₁ : A₁ ≃ B₁` of the domains and
`e₂ : A₂ ≃ B₂` of the codomains, `φ ↦ e₂ ∘ φ ∘ e₁⁻¹`: applying it entrywise to a `k × k` matrix
applies `e₁⁻¹`, `φ` and `e₂` in turn, and ⋆-homomorphisms are completely positive
(`NonUnitalStarAlgHomClass.instCompletelyPositiveMapClass`). -/
def arrowCongr (e₁ : A₁ ≃⋆ₐ[ℂ] B₁) (e₂ : A₂ ≃⋆ₐ[ℂ] B₂) :
    KPositiveMap k A₁ A₂ ≃ KPositiveMap k B₁ B₂ where
  toFun φ :=
    { toFun b := e₂ (φ (e₁.symm b))
      map_add' _ _ := by simp
      map_smul' _ _ := by simp
      map_cstarMatrix_nonneg' M hM :=
        CompletelyPositiveMapClass.map_cstarMatrix_nonneg' e₂ k _ (φ.map_cstarMatrix_nonneg' _
          (CompletelyPositiveMapClass.map_cstarMatrix_nonneg' e₁.symm k M hM)) }
  invFun ψ :=
    { toFun a := e₂.symm (ψ (e₁ a))
      map_add' _ _ := by simp
      map_smul' _ _ := by simp
      map_cstarMatrix_nonneg' M hM :=
        CompletelyPositiveMapClass.map_cstarMatrix_nonneg' e₂.symm k _ (ψ.map_cstarMatrix_nonneg' _
          (CompletelyPositiveMapClass.map_cstarMatrix_nonneg' e₁ k M hM)) }
  left_inv φ := DFunLike.ext _ _ fun a => by
    change e₂.symm (e₂ (φ (e₁.symm (e₁ a)))) = φ a
    simp
  right_inv ψ := DFunLike.ext _ _ fun b => by
    change e₂ (e₂.symm (ψ (e₁ (e₁.symm b)))) = ψ b
    simp

/-- The transported map `arrowCongr e₁ e₂ φ` sends `b` to `e₂ (φ (e₁⁻¹ b))`. -/
@[simp] lemma arrowCongr_apply (e₁ : A₁ ≃⋆ₐ[ℂ] B₁) (e₂ : A₂ ≃⋆ₐ[ℂ] B₂) (φ : KPositiveMap k A₁ A₂)
    (b : B₁) : arrowCongr e₁ e₂ φ b = e₂ (φ (e₁.symm b)) :=
  rfl

/-- The inverse transport `(arrowCongr e₁ e₂).symm ψ` sends `a` to `e₂⁻¹ (ψ (e₁ a))`. -/
@[simp] lemma arrowCongr_symm_apply (e₁ : A₁ ≃⋆ₐ[ℂ] B₁) (e₂ : A₂ ≃⋆ₐ[ℂ] B₂)
    (ψ : KPositiveMap k B₁ B₂) (a : A₁) : (arrowCongr e₁ e₂).symm ψ a = e₂.symm (ψ (e₁ a)) :=
  rfl

end ArrowCongr

end KPositiveMap

namespace KPositiveMapClass

/-! ### The Cauchy–Schwarz inequality -/

section NonUnital

variable {F A₁ A₂ : Type*} [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂] [PartialOrder A₁]
  [PartialOrder A₂] [StarOrderedRing A₁] [StarOrderedRing A₂] [FunLike F A₁ A₂]
  [KPositiveMapClass F 2 A₁ A₂]

/-- A `2`-positive map sends `y⋆ y` to a nonnegative element: it is the upper-left entry of the
image of `X⋆ X`, `X = !![y, 0; 0, 0]` (`CStarMatrix.diag_nonneg`). -/
lemma map_star_mul_self_nonneg (φ : F) (y : A₁) : 0 ≤ φ (star y * y) := by
  let X : CStarMatrix (Fin 2) (Fin 2) A₁ := CStarMatrix.ofMatrix !![y, 0; 0, 0]
  have h := CStarMatrix.diag_nonneg (map_cstarMatrix_nonneg' φ _ (star_mul_self_nonneg X)) (i := 0)
  simpa [X, CStarMatrix.mul_apply, CStarMatrix.star_apply, CStarMatrix.map_apply,
    Fin.sum_univ_two] using h

/-- The **Cauchy–Schwarz inequality** for a `2`-positive map:
`φ(x⋆ y)⋆ φ(x⋆ y) ≤ ‖φ(x⋆ x)‖ • φ(y⋆ y)`. The matrix `(φ(xᵢ⋆ xⱼ))ᵢⱼ` for `(x₁, x₂) = (x, y)` is the
image of `X⋆ X`, `X = !![x, y; 0, 0]`, hence nonnegative; being self-adjoint, it has
`φ(y⋆ x) = φ(x⋆ y)⋆`, and `CStarMatrix.star_mul_le_norm_smul_of_nonneg` applies. -/
lemma star_map_mul_le_norm_smul (φ : F) (x y : A₁) :
    star (φ (star x * y)) * φ (star x * y) ≤ ‖φ (star x * x)‖ • φ (star y * y) := by
  let X : CStarMatrix (Fin 2) (Fin 2) A₁ := CStarMatrix.ofMatrix !![x, y; 0, 0]
  have hN : 0 ≤ (star X * X).map φ := map_cstarMatrix_nonneg' φ _ (star_mul_self_nonneg X)
  have hentry : ∀ i j, ((star X * X).map φ) i j =
      φ (star (X 0 i) * X 0 j + star (X 1 i) * X 1 j) := fun i j => by
    simp [CStarMatrix.map_apply, CStarMatrix.mul_apply, CStarMatrix.star_apply, Fin.sum_univ_two]
  have hstar : φ (star y * x) = star (φ (star x * y)) := by
    have := congrArg (fun M : CStarMatrix (Fin 2) (Fin 2) A₂ => M 1 0)
      (IsSelfAdjoint.of_nonneg hN).star_eq
    simp only [CStarMatrix.star_apply, hentry] at this
    simpa [X, CStarMatrix.ofMatrix_apply] using this.symm
  have hM : (star X * X).map φ =
      CStarMatrix.ofMatrix !![φ (star x * x), φ (star x * y); star (φ (star x * y)),
        φ (star y * y)] := by
    refine CStarMatrix.ext fun i j => ?_
    rw [hentry]
    fin_cases i <;> fin_cases j <;> simp [X, CStarMatrix.ofMatrix_apply, hstar]
  rw [hM] at hN
  exact CStarMatrix.star_mul_le_norm_smul_of_nonneg hN

/-- The **Kadison–Schwarz inequality** for a `2`-positive map on a possibly non-unital
C⋆-algebra: if `‖φ x‖ ≤ C ‖x‖` for all `x`, then `φ(a)⋆ φ(a) ≤ C • φ(a⋆ a)`. Along an approximate
unit `e → 1` with `‖e‖ ≤ 1` and `e⋆ = e`, the Cauchy–Schwarz inequality
(`KPositiveMapClass.star_map_mul_le_norm_smul`) gives
`φ(e a)⋆ φ(e a) ≤ ‖φ(e⋆ e)‖ • φ(a⋆ a) ≤ C • φ(a⋆ a)`, and `φ(e a) → φ(a)`; the order is closed.
For the operator norm of `φ` see `KPositiveMapClass.le_opNorm_smul_map_star_mul`. -/
lemma le_smul_map_star_mul_of_norm_le [LinearMapClass F ℂ A₁ A₂] (φ : F) {C : ℝ}
    (hC : ∀ x, ‖φ x‖ ≤ C * ‖x‖) (a : A₁) : star (φ a) * φ a ≤ C • φ (star a * a) := by
  by_cases hC0 : 0 ≤ C
  swap
  · have h0 (x : A₁) : φ x = 0 :=
      norm_le_zero_iff.1 ((hC x).trans (mul_nonpos_of_nonpos_of_nonneg (not_le.1 hC0).le
        (norm_nonneg x)))
    simp [h0]
  have hl := CStarAlgebra.increasingApproximateUnit A₁
  have he : Tendsto (fun e => star e * a) (CStarAlgebra.approximateUnit A₁) (𝓝 a) :=
    (hl.tendsto_mul_right a).congr' (hl.eventually_star_eq.mono fun e he => by simp [he])
  have hφ : Tendsto (fun e => φ (star e * a)) (CStarAlgebra.approximateUnit A₁) (𝓝 (φ a)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero] at he ⊢
    refine squeeze_zero (fun _ => norm_nonneg _) (fun e => ?_) (by simpa using he.const_mul C)
    rw [← map_sub]
    exact hC _
  refine le_of_tendsto (hφ.star.mul hφ) ?_
  filter_upwards [hl.eventually_norm] with e he
  refine (star_map_mul_le_norm_smul φ e a).trans
    (smul_le_smul_of_nonneg_right ?_ (map_star_mul_self_nonneg φ a))
  calc ‖φ (star e * e)‖ ≤ C * ‖star e * e‖ := hC _
    _ ≤ C * 1 := by
      gcongr
      rw [CStarRing.norm_star_mul_self]
      nlinarith [norm_nonneg e]
    _ = C := mul_one C

/-- The **Kadison–Schwarz inequality** for a `2`-positive map on a possibly non-unital
C⋆-algebra, in terms of its operator norm: `φ(a)⋆ φ(a) ≤ ‖φ‖ • φ(a⋆ a)`. A `2`-positive map is
positive (`KPositiveMapClass.instOrderHomClass`), positive linear maps between C⋆-algebras are
bounded, and `‖φ‖` is the norm of `PositiveContinuousLinearMap.ofClass φ`. -/
lemma le_opNorm_smul_map_star_mul [LinearMapClass F ℂ A₁ A₂] (φ : F) (a : A₁) :
    star (φ a) * φ a ≤
      ‖(PositiveContinuousLinearMap.ofClass φ : A₁ →L[ℂ] A₂)‖ • φ (star a * a) :=
  le_smul_map_star_mul_of_norm_le φ (fun x => (PositiveContinuousLinearMap.ofClass φ :
    A₁ →L[ℂ] A₂).le_opNorm x) a

end NonUnital

/-! ### Unital domain -/

section Unital

variable {F A₁ A₂ : Type*} [CStarAlgebra A₁] [NonUnitalCStarAlgebra A₂] [PartialOrder A₁]
  [PartialOrder A₂] [StarOrderedRing A₁] [StarOrderedRing A₂] [FunLike F A₁ A₂]
  [KPositiveMapClass F 2 A₁ A₂]

/-- A `2`-positive map sends `1` to a nonnegative element. -/
lemma map_one_nonneg (φ : F) : 0 ≤ φ 1 := by
  simpa using map_star_mul_self_nonneg φ (1 : A₁)

/-- **Kadison–Schwarz inequality**, unnormalised form: every `2`-positive map on a
unital C⋆-algebra satisfies `φ(a)⋆ φ(a) ≤ ‖φ 1‖ • φ(a⋆ a)`. This is the Cauchy–Schwarz inequality
(`KPositiveMapClass.star_map_mul_le_norm_smul`) for `x = 1`, `y = a`. -/
theorem le_norm_smul_map_star_mul (φ : F) (a : A₁) :
    star (φ a) * φ a ≤ ‖φ 1‖ • φ (star a * a) := by
  simpa using star_map_mul_le_norm_smul φ 1 a

end Unital

/-! ### Unital domain and codomain -/

/-- A positive map between unital C⋆-algebras with `φ 1 ≤ 1` has `‖φ 1‖ ≤ 1`, since
`0 ≤ φ 1 ≤ 1`. A `2`-positive linear map is positive (`KPositiveMapClass.instOrderHomClass`). -/
lemma _root_.OrderHomClass.norm_map_one_le_one {F A₁ A₂ : Type*} [CStarAlgebra A₁]
    [CStarAlgebra A₂] [PartialOrder A₁] [PartialOrder A₂] [StarOrderedRing A₁] [StarOrderedRing A₂]
    [FunLike F A₁ A₂] [ZeroHomClass F A₁ A₂] [OrderHomClass F A₁ A₂] (φ : F) (hφ : φ 1 ≤ 1) :
    ‖φ 1‖ ≤ 1 :=
  (CStarAlgebra.norm_le_one_iff_of_nonneg _ (map_nonneg φ zero_le_one)).2 hφ

section Unital₂

variable {F A₁ A₂ : Type*} [CStarAlgebra A₁] [CStarAlgebra A₂] [PartialOrder A₁] [PartialOrder A₂]
  [StarOrderedRing A₁] [StarOrderedRing A₂] [FunLike F A₁ A₂] [KPositiveMapClass F 2 A₁ A₂]

/-- **Kadison–Schwarz inequality**: a `2`-positive map with `φ 1 ≤ 1` satisfies
`φ(a)⋆ φ(a) ≤ φ(a⋆ a)`: `‖φ 1‖ ≤ 1` since `0 ≤ φ 1 ≤ 1`, in
`KPositiveMapClass.le_norm_smul_map_star_mul`. -/
theorem le_map_star_mul (φ : F) (hφ : φ 1 ≤ 1) (a : A₁) :
    star (φ a) * φ a ≤ φ (star a * a) := by
  refine (le_norm_smul_map_star_mul φ a).trans ?_
  have hn : ‖φ 1‖ ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ (map_one_nonneg φ)).2 hφ
  calc ‖φ 1‖ • φ (star a * a) ≤ (1 : ℝ) • φ (star a * a) :=
        smul_le_smul_of_nonneg_right hn (map_star_mul_self_nonneg φ a)
    _ = φ (star a * a) := one_smul _ _

end Unital₂

end KPositiveMapClass

/-! ### Scalar matrices and positive `2 × 2` block matrices -/

open scoped ComplexOrder

namespace CStarMatrix

section Scalar

variable {C : Type*} [CStarAlgebra C] {n : ℕ}

variable (C n) in
/-- The scalar matrices inside the matrices over a unital C⋆-algebra `C`, `α ↦ (αᵢⱼ • 1)ᵢⱼ`, as a
unital ⋆-homomorphism. -/
noncomputable def ofScalar : CStarMatrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) C :=
  { mapₙₐ (StarAlgHom.ofId ℂ C).toNonUnitalStarAlgHom with
    map_one' := by
      ext i j
      change algebraMap ℂ C ((1 : CStarMatrix (Fin n) (Fin n) ℂ) i j) = (1 : CStarMatrix _ _ C) i j
      rw [CStarMatrix.one_apply, CStarMatrix.one_apply]
      split_ifs <;> simp
    commutes' := fun c => by
      ext i j
      change algebraMap ℂ C ((algebraMap ℂ (CStarMatrix (Fin n) (Fin n) ℂ) c) i j) =
        (algebraMap ℂ (CStarMatrix (Fin n) (Fin n) C) c) i j
      rw [algebraMap_apply, algebraMap_apply]
      split_ifs <;> simp }

/-- The entries `αᵢⱼ • 1` of `ofScalar C n α`. -/
lemma ofScalar_apply (α : CStarMatrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ofScalar C n α i j = algebraMap ℂ C (α i j) :=
  rfl

/-- Over a nontrivial unital C⋆-algebra, the scalar matrices embed injectively. -/
lemma ofScalar_injective [Nontrivial C] : Function.Injective (ofScalar C n) := fun α β h =>
  ext fun i j => (algebraMap ℂ C).injective (by
    rw [← ofScalar_apply, ← ofScalar_apply, h])

end Scalar

section TwoByTwo

variable {C : Type*} [CStarAlgebra C]

/-- Multiplying a `2 × 2` matrix by diagonal matrices on both sides. -/
lemma diag_mul_mul_diag (u v p x y q u' v' : C) :
    (ofMatrix !![u, 0; 0, v] : CStarMatrix (Fin 2) (Fin 2) C) * ofMatrix !![p, x; y, q] *
      ofMatrix !![u', 0; 0, v'] = ofMatrix !![u * p * u', u * x * v'; v * y * u', v * q * v'] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CStarMatrix.mul_apply, Fin.sum_univ_two, ofMatrix_apply]

/-- The adjoint of a diagonal `2 × 2` matrix. -/
lemma star_diag (u v : C) :
    star (ofMatrix !![u, 0; 0, v] : CStarMatrix (Fin 2) (Fin 2) C) =
      ofMatrix !![star u, 0; 0, star v] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CStarMatrix.star_apply, ofMatrix_apply]

variable [PartialOrder C] [StarOrderedRing C]

/-- **Positive `2 × 2` matrices with invertible diagonal.** For units `s`, `t`, the matrix
`!![s⋆ s, x; x⋆, t⋆ t]` is positive exactly when `‖(s⁻¹)⋆ x t⁻¹‖ ≤ 1`: conjugating by
`!![s⁻¹, 0; 0, t⁻¹]` turns it into `!![1, y; y⋆, 1]` with `y = (s⁻¹)⋆ x t⁻¹`
(`CStarMatrix.nonneg_one_star_one_iff`), and conjugating back by `!![s, 0; 0, t]` undoes this. -/
theorem nonneg_star_mul_self_block_iff (s t : Cˣ) (x : C) :
    0 ≤ (ofMatrix !![star (s : C) * s, x; star x, star (t : C) * t] : CStarMatrix (Fin 2) (Fin 2) C) ↔
      ‖star (↑s⁻¹ : C) * x * ↑t⁻¹‖ ≤ 1 := by
  set y := star (↑s⁻¹ : C) * x * ↑t⁻¹
  have h₁ : ∀ u : Cˣ, star (↑u⁻¹ : C) * (star (u : C) * u) * ↑u⁻¹ = 1 := fun u => by
    rw [← mul_assoc, ← star_mul, Units.mul_inv, star_one, one_mul, Units.mul_inv]
  have hy : star (s : C) * y * t = x := by
    rw [show star (s : C) * y * t = star (↑s⁻¹ * (s : C)) * x * (↑t⁻¹ * t) by
      simp only [y, star_mul, mul_assoc], Units.inv_mul, Units.inv_mul, star_one, one_mul, mul_one]
  have hy' : star (t : C) * star y * s = star x := by
    rw [← hy]
    simp only [star_mul, star_star, mul_assoc]
  have hD : star (ofMatrix !![(↑s⁻¹ : C), 0; 0, ↑t⁻¹] : CStarMatrix (Fin 2) (Fin 2) C) *
      ofMatrix !![star (s : C) * s, x; star x, star (t : C) * t] *
        ofMatrix !![(↑s⁻¹ : C), 0; 0, ↑t⁻¹] = ofMatrix !![1, y; star y, 1] := by
    rw [star_diag, diag_mul_mul_diag, h₁, h₁]
    congr 3
    simp only [y, star_mul, star_star, mul_assoc]
  have hD' : star (ofMatrix !![(s : C), 0; 0, t] : CStarMatrix (Fin 2) (Fin 2) C) *
      ofMatrix !![1, y; star y, 1] * ofMatrix !![(s : C), 0; 0, t] =
        ofMatrix !![star (s : C) * s, x; star x, star (t : C) * t] := by
    rw [star_diag, diag_mul_mul_diag, mul_one, mul_one, hy, hy']
  constructor
  · intro h
    have := star_left_conjugate_nonneg h (ofMatrix !![(↑s⁻¹ : C), 0; 0, ↑t⁻¹])
    rw [hD] at this
    exact nonneg_one_star_one_iff.mp this
  · intro h
    have := star_left_conjugate_nonneg (nonneg_one_star_one_iff.mpr h) (ofMatrix !![(s : C), 0; 0, t])
    rwa [hD'] at this

variable {n : ℕ}

/-- Adding `ε • 1` to `!![α 1, X; X⋆, β 1]` adds `ε` to `α` and `β`. -/
lemma ofScalar_block_add_smul_one (ε : ℝ) (a b : CStarMatrix (Fin n) (Fin n) ℂ)
    (x : CStarMatrix (Fin n) (Fin n) C) :
    (ofMatrix !![ofScalar C n a, x; star x, ofScalar C n b] :
      CStarMatrix (Fin 2) (Fin 2) (CStarMatrix (Fin n) (Fin n) C)) + (ε : ℂ) • 1 =
    ofMatrix !![ofScalar C n (a + (ε : ℂ) • 1), x; star x, ofScalar C n (b + (ε : ℂ) • 1)] := by
  rw [map_add, map_add, map_smul, map_one]
  refine CStarMatrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j
  · rfl
  · change x + (ε : ℂ) • (0 : CStarMatrix (Fin n) (Fin n) C) = x
    rw [smul_zero, add_zero]
  · change star x + (ε : ℂ) • (0 : CStarMatrix (Fin n) (Fin n) C) = star x
    rw [smul_zero, add_zero]
  · rfl

end TwoByTwo

end CStarMatrix

/-- In a unital C⋆-algebra, a positive element plus `ε • 1` with `ε > 0` is strictly positive. -/
lemma isStrictlyPositive_add_smul_one {D : Type*} [CStarAlgebra D] [PartialOrder D]
    [StarOrderedRing D] {a : D} (ha : 0 ≤ a) {ε : ℝ} (hε : 0 < ε) :
    IsStrictlyPositive (a + (ε : ℂ) • 1) := by
  refine IsStrictlyPositive.nonneg_add ha ?_
  have := isStrictlyPositive_algebraMap (A := D) hε
  convert this using 1
  rw [Algebra.algebraMap_eq_smul_one]
  exact Complex.coe_smul ε 1
